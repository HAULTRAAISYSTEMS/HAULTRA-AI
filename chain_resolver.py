"""Deterministic can-swap chain resolution (arbitrary-length, two-FK model).

One can rides the truck through a run of consecutive can-producing stops
(Pull / Pickup-and-Return / Swap): each stop boxes out its full, dumps it, and
the resulting empty is set off at the NEXT stop, whose full is then boxed out
and dumped, and so on. N stops = N dump trips, one can throughout. The head site
has no can from the moment the chain starts; by default the final empty returns
to the head.

There is no supplies/receives enum — a middle stop is BOTH. The chain is modelled
by two directional FKs per stop:

    chain_gives_to_stop_id    my dumped can becomes the empty set off HERE
    chain_takes_from_stop_id  my empty arrives FROM here

plus a 0-based ``chain_seq`` and, on the tail only, a ``chain_terminal`` of
'head' (default — return to head), 'yard', or 'none'.

Detection: the boss annotates ONE stop; the RUN itself is the chain. A single
swap signal anywhere in a run of can-producers extends across the whole run.
Signals come either from the AI parser's ``chain_hint`` or, for the manual
entry paths, from scanning the stop's note text — the SAME function, so every
path behaves identically.

The model never guesses a stop id and never normalizes an address for the boss;
address matching (explicit targets) is deterministic Python here, run against
the FINAL saved order. Precedence is manual > explicit > positional.
"""

import re
import uuid

# ── Address normalization / match key (unchanged recipe) ────────────────────
_SUFFIX_CANON = {
    "rd": "road", "road": "road",
    "blvd": "boulevard", "boulevard": "boulevard",
    "st": "street", "street": "street",
    "ave": "avenue", "av": "avenue", "avenue": "avenue",
    "dr": "drive", "drive": "drive",
    "ln": "lane", "lane": "lane",
    "hwy": "highway", "highway": "highway",
}
_HOUSE_RE = re.compile(r"^\d+[a-z]?$")


def _tokens(text):
    return re.sub(r"[^a-z0-9 ]+", " ", (text or "").lower()).split()


def address_key(text):
    """(house_number, first_street_token) or None. "5125 ballahack" and
    "5125 Ballahack Rd" both key to ("5125", "ballahack")."""
    toks = _tokens(text)
    house = idx = None
    for i, t in enumerate(toks):
        if _HOUSE_RE.match(t):
            house, idx = t, i
            break
    if house is None:
        return None
    rest = toks[idx + 1:]
    if not rest:
        return None
    first = rest[0]
    return (house, _SUFFIX_CANON.get(first, first))


def normalize_size(text):
    """Comparable container size — just the digit run ("30yd" -> "30"). Empty
    string when unknown, which never equals another size (can't validate a link
    against an unknown, so it's treated as a mismatch guard by the caller)."""
    m = re.search(r"\d+", str(text or ""))
    return m.group(0) if m else ""


# ── Note / hint detection ───────────────────────────────────────────────────
_TERMINAL_YARD_RE = re.compile(r"\b(back to (the )?yard|to the yard|return to yard)\b", re.I)
_TERMINAL_NONE_RE = re.compile(r"\b(no return|don'?t (bring|come) back|last one dumps|no can back|leave last)\b", re.I)
_RUN_RE = re.compile(r"\b(swap (till|til|until) (the )?end|keep swapping|swap all|swap the whole|swap everything|swap down the line)\b", re.I)
# "use to swap <target>" / "swap with <target>" / "use for <target>" / "take to <target>"
_EXPLICIT_RE = re.compile(
    r"\b(?:use to swap|swap with|swap w/|use (?:it )?for|use on|take (?:it )?to|this can goes to|empty for)\b\s*[:,-]?\s*(.+)",
    re.I)
_NEXT_RE = re.compile(r"\b(use to swap|swap w/? next|use (?:it )?for next|swap next|use to swap next)\b", re.I)
# The head's first empty comes FROM the yard (not delivered on-route yet).
_START_YARD_RE = re.compile(r"\b(start (?:from|at|with) (?:the )?yard|grab (?:one )?from (?:the )?yard(?: first)?|empty from (?:the )?yard(?: first)?|first can from (?:the )?yard)\b", re.I)

# Every regex that RECOGNIZES a chain phrase, ordered so an explicit target (which
# greedily consumes to end-of-line) is stripped last. strip_chain_phrases() removes
# exactly what detection matches, so a stored trigger phrase never renders raw while
# the boss's real note text ("gate code 1234") survives. Detection and stripping
# share this one list — they can never drift apart.
_CHAIN_PHRASE_RES = (_RUN_RE, _TERMINAL_YARD_RE, _TERMINAL_NONE_RE, _START_YARD_RE, _EXPLICIT_RE, _NEXT_RE)


def strip_chain_phrases(text):
    """Remove any recognized can-swap trigger phrase from a note so it is never
    shown to a user as raw text — the chain renders from FK state instead. Returns
    the note with only the human-meaningful remainder (empty string if the note was
    nothing but a swap phrase). Uses the SAME regexes as detection."""
    t = text or ""
    for rx in _CHAIN_PHRASE_RES:
        t = rx.sub(" ", t)
    # tidy leftover separators/space from the excision
    t = re.sub(r"\s{2,}", " ", t).strip(" \t\r\n.,;:-—–")
    return t


def hint_to_note(hint):
    """Canonical note phrase for a STRUCTURED chain_hint from the AI parser, so
    resolution stays note-driven and identical across every entry path — the model
    emits pure structure, Python writes the deterministic phrase (never prose, never
    a normalized address; an explicit target's verbatim text is passed through as-is).
    Returns "" for a null/unknown hint."""
    if not isinstance(hint, dict):
        return ""
    k = (hint.get("kind") or "").lower()
    if k == "run":
        return "swap till end"
    if k == "next":
        return "use to swap"
    if k == "explicit":
        target = (hint.get("target_text") or "").strip()
        return ("use to swap " + target) if target else "use to swap"
    if k == "terminal":
        term = (hint.get("terminal") or "").lower()
        if term == "yard":
            return "back to yard"
        if term == "none":
            return "no return"
        return ""
    if k == "start":
        if (hint.get("start") or "").lower() == "yard":
            return "start from yard"
        return ""
    return ""


def detect_start(text):
    """A 'head grabs its first empty from the yard' phrase -> 'yard' | None."""
    t = (text or "").strip()
    if t and _START_YARD_RE.search(t):
        return "yard"
    return None


def detect_chain_hint(text):
    """Scan free-text (a stop note or Quick-Add text) for a swap signal and
    return the same {kind, ...} shape the AI parser emits, or None.

    Precedence within a single note: terminal > run > explicit(with target) >
    next(bare). Terminal phrases are recognised even alongside a swap phrase so
    "swap till end back to yard" yields both a run intent and a yard terminal —
    the caller reads terminal separately."""
    t = (text or "").strip()
    if not t:
        return None
    if _RUN_RE.search(t):
        return {"kind": "run"}
    m = _EXPLICIT_RE.search(t)
    if m:
        target = m.group(1).strip(" .,-").strip()
        # An explicit target only counts when there's a real address after the
        # phrase (a house number + street). "use to swap" with nothing usable
        # after it falls through to the bare 'next' form below.
        if target and address_key(target) is not None:
            return {"kind": "explicit", "target_text": target}
    if _NEXT_RE.search(t):
        return {"kind": "next"}
    return None


def detect_terminal(text):
    """A terminal phrase in free text -> 'yard' | 'none' | None."""
    t = (text or "").strip()
    if not t:
        return None
    if _TERMINAL_YARD_RE.search(t):
        return "yard"
    if _TERMINAL_NONE_RE.search(t):
        return "none"
    return None


# ── FK-derived rendering (both sides, never prose) ──────────────────────────
def render_flows(stops):
    """Derive the human-readable can-swap lines for every stop PURELY from the two
    FK columns, so both ends of a link always render together (or neither). Input:
    a list of dicts carrying at least id, address, chain_gives_to_stop_id,
    chain_takes_from_stop_id, chain_terminal, chain_start, chain_seq.

    Returns {stop_id: {"takes","gives","start","integrity"}} where each value is a
    string or None. A stop with no chain link maps to all-None (render NOTHING).

    A link renders on BOTH stops: the giver gets ``gives`` ("Empty goes to <addr>")
    and the receiver gets ``takes`` ("Empty arrives from <addr>"). If a giver points
    at a receiver whose takes_from does NOT point back — a half-written link — the
    giver gets an ``integrity`` notice instead of a silent one-sided render."""
    addr = {}
    gives = {}
    takes = {}
    seq = {}
    for s in stops:
        sid = s.get("id")
        if sid is None:
            continue
        addr[sid] = (s.get("address") or "").strip()
        gives[sid] = s.get("chain_gives_to_stop_id")
        takes[sid] = s.get("chain_takes_from_stop_id")
        seq[sid] = s.get("chain_seq")

    def _addr(sid):
        return addr.get(sid) or "another stop"

    out = {}
    for s in stops:
        sid = s.get("id")
        if sid is None:
            continue
        g = s.get("chain_gives_to_stop_id")
        t = s.get("chain_takes_from_stop_id")
        term = (s.get("chain_terminal") or "")
        start = (s.get("chain_start") or "")
        line = {"takes": None, "gives": None, "start": None, "integrity": None}

        # incoming empty (reciprocal: the stop I take from must give to me)
        if t is not None:
            if gives.get(t) == sid:
                line["takes"] = "← Empty arrives from " + _addr(t)
            else:
                line["integrity"] = "Chain link to this stop is one-sided — re-link it in Edit Stop."
        elif start == "yard" and s.get("chain_group_id"):
            line["start"] = "← First empty grabbed from the yard"

        # outgoing empty. A normal link is reciprocal (my target takes from me); the
        # tail's terminal-head link is the return-home closure (the head starts the
        # chain, so its takes_from is legitimately null) — that is NOT one-sided.
        if g is not None:
            if takes.get(g) == sid:
                line["gives"] = "→ Empty goes to " + _addr(g)
            elif term == "head" and seq.get(g) == 0:
                line["gives"] = "→ Final empty returns to head " + _addr(g)
            else:
                line["integrity"] = "Chain link from this stop is one-sided — re-link it in Edit Stop."
        elif term == "yard":
            line["gives"] = "→ Final empty back to the yard"
        elif term == "none":
            line["gives"] = "→ Final empty just gets dumped (no return)"

        out[sid] = line
    return out


# ── Chain model ─────────────────────────────────────────────────────────────
CAN_PRODUCING = ("pickup and return", "pull", "swap")


def _is_can_producer(action):
    a = (action or "").strip().lower()
    if "delivery" in a or "drop" in a or "relocate" in a or a == "yard" or a == "vendor":
        return False
    return any(k in a for k in CAN_PRODUCING)


def _new_group_id():
    return uuid.uuid4().hex


def resolve_chain(stops):
    """Resolve can-swap chains over ``stops`` (list of dicts in FINAL saved
    order). Each stop dict may carry:

        id               real stop id (resolution runs against saved order)
        action, address, container_size, note
        chain_hint       optional {kind:...} from the AI parser
        manual_gives_to  optional stop id set by the boss's "Swaps with" picker

    Mutates each dict with resolved fields (None where not chained):

        _chain_group_id, _chain_seq, _chain_gives_to, _chain_takes_from,
        _chain_terminal, _chain_target_ref, _chain_source

    Returns {"errors": [...], "infos": [...], "needs_link": [...]} where errors
    are BLOCKING (container-size mismatch, bad guard) and must stop the save.
    """
    n = len(stops)
    for s in stops:
        s["_chain_group_id"] = None
        s["_chain_seq"] = None
        s["_chain_gives_to"] = None
        s["_chain_takes_from"] = None
        s["_chain_terminal"] = None
        s["_chain_target_ref"] = None
        s["_chain_source"] = None
        s["_chain_start"] = None

    id_by_index = [s.get("id") for s in stops]
    index_by_id = {sid: i for i, sid in enumerate(id_by_index) if sid is not None}
    producer = [_is_can_producer(s.get("action")) for s in stops]

    # Per-stop signal (manual > explicit > run/next) + terminal, from AI hint or note.
    kinds = [None] * n            # 'explicit' | 'run' | 'next'
    targets = [None] * n          # explicit target text
    terminals = [None] * n        # 'yard' | 'none'
    starts = [None] * n           # 'yard' (head grabs its first empty from the yard)
    for i, s in enumerate(stops):
        hint = s.get("chain_hint") if isinstance(s.get("chain_hint"), dict) else None
        note = s.get("note") or ""
        if not hint:
            hint = detect_chain_hint(note)
        if hint:
            k = (hint.get("kind") or "").lower()
            if k == "terminal":
                terminals[i] = hint.get("terminal") if hint.get("terminal") in ("yard", "none") else None
            elif k == "start":
                starts[i] = "yard" if (hint.get("start") or "").lower() == "yard" else None
            elif k in ("explicit", "run", "next"):
                kinds[i] = k
                if k == "explicit":
                    targets[i] = (hint.get("target_text") or "").strip()
        # A terminal / start phrase can co-exist with a swap phrase in the same note.
        if terminals[i] is None:
            terminals[i] = detect_terminal(note)
        if starts[i] is None:
            starts[i] = detect_start(note)

    errors, infos, needs_link = [], [], []

    # gives_to[i] = index this stop hands its dumped empty to; source tag.
    gives = [None] * n
    src = [None] * n
    claimed_giver = [False] * n   # already has an outgoing link (manual/explicit)
    claimed_taker = [False] * n   # already receives (prevents duplicate membership)

    def _set_link(gi, ri, source):
        gives[gi] = ri
        src[gi] = source
        claimed_giver[gi] = True
        claimed_taker[ri] = True

    # 1) MANUAL links (highest precedence) — the boss's explicit picker.
    for i, s in enumerate(stops):
        mid = s.get("manual_gives_to")
        if mid is None:
            continue
        if mid not in index_by_id:
            continue
        ri = index_by_id[mid]
        if ri == i:
            errors.append({"stop_id": id_by_index[i], "kind": "self", "msg": "A stop can't swap with itself."})
            continue
        if claimed_taker[ri]:
            errors.append({"stop_id": id_by_index[i], "kind": "double",
                           "msg": "That stop already receives a can from another stop in this chain."})
            continue
        _set_link(i, ri, "manual")

    # 2) EXPLICIT address targets (match within batch, may skip position).
    for i in range(n):
        if kinds[i] != "explicit" or claimed_giver[i]:
            continue
        tk = address_key(targets[i])
        match = None
        if tk is not None:
            for j in range(n):
                if j == i or claimed_taker[j]:
                    continue
                if address_key(stops[j].get("address")) == tk:
                    match = j
                    break
        if match is None:
            stops[i]["_chain_target_ref"] = targets[i]
            stops[i]["_chain_source"] = "explicit"
            needs_link.append({"stop_id": id_by_index[i], "target_text": targets[i]})
            continue
        _set_link(i, match, "explicit")
        stops[i]["_chain_target_ref"] = targets[i]

    # 3) POSITIONAL runs. A maximal block of consecutive can-producers is a run;
    #    a run/next signal anywhere in it chains the WHOLE run, and a 'run' signal
    #    propagates to every later run (each still its own chain). The run breaks
    #    on a non-producer, and — inside link creation — on a size mismatch, an
    #    already-claimed giver, or a member with a terminal signal (that member
    #    becomes the tail).
    runs = []
    i = 0
    while i < n:
        if producer[i]:
            j = i
            while j < n and producer[j]:
                j += 1
            runs.append(list(range(i, j)))
            i = j
        else:
            i += 1

    propagate_from = None
    for r_idx, run in enumerate(runs):
        if any(kinds[k] == "run" for k in run):
            propagate_from = r_idx if propagate_from is None else min(propagate_from, r_idx)

    for r_idx, run in enumerate(runs):
        has_signal = any(kinds[k] in ("run", "next") for k in run)
        propagated = propagate_from is not None and r_idx >= propagate_from
        if not (has_signal or propagated):
            continue
        # Link consecutive members, stopping at the tail (terminal signal, size
        # mismatch, or an already-claimed giver breaks the forward walk).
        prev = None
        for k in run:
            if prev is not None:
                if normalize_size(stops[prev].get("container_size")) != normalize_size(stops[k].get("container_size")):
                    # BLOCKING: a 30yd empty can't serve a 20yd site. Flag both,
                    # break the chain here; k may start a fresh same-size sub-chain.
                    errors.append({
                        "stop_id": id_by_index[prev], "kind": "size",
                        "msg": "Container size mismatch — a %s empty can't serve the %s site at %s. Chain broken here." % (
                            stops[prev].get("container_size") or "?", stops[k].get("container_size") or "?",
                            stops[k].get("address") or "this stop")})
                    errors.append({
                        "stop_id": id_by_index[k], "kind": "size",
                        "msg": "Container size mismatch — this %s site can't take the %s empty from %s. Chain broken here." % (
                            stops[k].get("container_size") or "?", stops[prev].get("container_size") or "?",
                            stops[prev].get("address") or "the prior stop")})
                    prev = None if terminals[k] else k
                    continue
                if not claimed_giver[prev] and not claimed_taker[k]:
                    _set_link(prev, k, "positional")
            # A terminal signal on this member ends the chain here (it's the tail).
            prev = None if terminals[k] else k

    # 4) Assemble chains from the gives graph, assign seq / takes_from / terminal.
    #    A chain starts at a HEAD: a claimed giver that nobody hands a can to
    #    (claimed_taker False), following gives forward.
    visited = [False] * n
    for start in range(n):
        if visited[start] or gives[start] is None or claimed_taker[start]:
            continue
        # walk the linear body
        seq_order = []
        cur = start
        guard = 0
        while cur is not None and not visited[cur] and guard <= n:
            visited[cur] = True
            seq_order.append(cur)
            cur = gives[cur]
            guard += 1
            if cur is not None and visited[cur]:
                break  # closes back (tail->head closure handled below) or a cycle
        if len(seq_order) < 2:
            # a lone giver whose target was consumed elsewhere — clear it
            for k in seq_order:
                gives[k] = None
            continue
        gid = _new_group_id()
        tail = seq_order[-1]
        # terminal: any member's terminal signal lands on the tail; default head.
        term = None
        for k in seq_order:
            if terminals[k]:
                term = terminals[k]
                break
        term = term or "head"
        # start: any member's start signal records where the HEAD's first empty
        # comes from ('yard'). Default None — the head starts can-less until a
        # delivery is scheduled (the existing INFO), unless told to grab from yard.
        start = None
        for k in seq_order:
            if starts[k]:
                start = starts[k]
                break
        for pos, k in enumerate(seq_order):
            s = stops[k]
            s["_chain_group_id"] = gid
            s["_chain_seq"] = pos
            if pos == 0:
                s["_chain_start"] = start
            s["_chain_takes_from"] = id_by_index[seq_order[pos - 1]] if pos > 0 else None
            if k == tail:
                s["_chain_terminal"] = term
                s["_chain_gives_to"] = id_by_index[seq_order[0]] if term == "head" else None
            else:
                s["_chain_gives_to"] = id_by_index[seq_order[pos + 1]]
            if s["_chain_source"] is None:
                s["_chain_source"] = src[k] or "positional"
        # INFO on the head when it is left without a can (yard/none terminal) AND
        # it wasn't told to grab its first empty from the yard.
        if term in ("yard", "none") and start != "yard":
            head = stops[seq_order[0]]
            infos.append({"stop_id": id_by_index[seq_order[0]],
                          "msg": "%s has no can until a delivery is scheduled." % (head.get("address") or "The head stop")})

    # 5) Guards. A gives-link that never got assembled into a chain (no head to
    #    start from) is an unintended cycle — reject it and clear the links.
    for i in range(n):
        if gives[i] is not None and stops[i]["_chain_group_id"] is None:
            errors.append({"stop_id": id_by_index[i], "kind": "loop",
                           "msg": "Swap links form a loop with no starting stop — break one link."})
            stops[i]["_chain_gives_to"] = None
            stops[i]["_chain_takes_from"] = None
    # Reject any leftover self-link (defensive).
    for i in range(n):
        if stops[i]["_chain_gives_to"] == id_by_index[i]:
            errors.append({"stop_id": id_by_index[i], "kind": "self", "msg": "A stop can't swap with itself."})
            stops[i]["_chain_gives_to"] = None

    return {"errors": errors, "infos": infos, "needs_link": needs_link}
