"""Deterministic can-swap chain resolution.

Roll-off reality: the full can pulled at one stop sometimes becomes the empty
that gets set off at another stop. The boss writes this as a free-text note
("use to swap 5125 ballahack rd"). The parser copies that target text VERBATIM
into a stop's ``chain_hint`` — it never guesses a stop id and never normalizes
the address, because an LLM hallucinates foreign keys. THIS module does the
matching, in plain Python: it links two stops in the SAME parse batch by
(house number, first street token), assigns a shared ``chain_group_id`` and the
``supplies``/``receives`` roles, and cross-links them.

It never fabricates a link. A hint whose target isn't in the batch keeps its raw
``chain_target_ref`` as a breadcrumb and leaves the partner NULL.

Kept deliberately free of Flask/SQLite so it is trivially unit-testable; the
caller resolves the temp partner index to a real stop id inside the insert
transaction (see ``_apply_chain_links`` in app.py).
"""

import re
import uuid

# Street-suffix canonicalization for the match key. Only the suffixes the
# dispatch texts actually vary on. Matching keys on the first street token means
# suffix spelling ("Rd" vs "Road" vs omitted) already can't split a match; this
# map is the belt-and-suspenders normalization the spec calls for.
_SUFFIX_CANON = {
    "rd": "road", "road": "road",
    "blvd": "boulevard", "boulevard": "boulevard",
    "st": "street", "street": "street",
    "ave": "avenue", "av": "avenue", "avenue": "avenue",
    "dr": "drive", "drive": "drive",
    "ln": "lane", "lane": "lane",
    "hwy": "highway", "highway": "highway",
}

_VALID_DIRECTIONS = ("supplies", "receives")
_HOUSE_RE = re.compile(r"^\d+[a-z]?$")


def _tokens(text):
    """Lowercase, drop punctuation, split on whitespace."""
    return re.sub(r"[^a-z0-9 ]+", " ", (text or "").lower()).split()


def normalize_address(text):
    """Whole-address normalization: lowercased, punctuation stripped, street
    suffixes canonicalized (rd->road, blvd->boulevard, ...). Exposed for tests
    and readability; matching itself uses address_key()."""
    return " ".join(_SUFFIX_CANON.get(t, t) for t in _tokens(text))


def address_key(text):
    """The deterministic in-batch match key: ``(house_number, first_street_token)``.

    "5125 ballahack" and "5125 Ballahack Rd" both key to ``("5125", "ballahack")``.
    Returns None when there's no leading house number or no street token after it —
    such an address can never anchor a match (and we never guess).
    """
    toks = _tokens(text)
    house = None
    house_idx = None
    for i, t in enumerate(toks):
        if _HOUSE_RE.match(t):
            house = t
            house_idx = i
            break
    if house is None:
        return None
    rest = toks[house_idx + 1:]
    if not rest:
        return None
    first = rest[0]
    return (house, _SUFFIX_CANON.get(first, first))


def _new_group_id():
    return uuid.uuid4().hex


def resolve_chains(stops):
    """Link can-swap chains within a single parse batch, in place.

    ``stops`` is a list of parse dicts, each optionally carrying::

        chain_hint = {"direction": "supplies"|"receives", "target_text": "<verbatim>"}

    On every stop this sets four private keys (the caller reads them, then maps
    the partner index to a real stop id at insert time):

        _chain_group_id      shared hex id across the linked pair, else None
        _chain_role          'supplies' | 'receives' | None
        _chain_target_ref    the verbatim target text (kept even when unmatched)
        _chain_partner_index index into ``stops`` of the partner, else None

    Returns a list of ``(supplier_index, receiver_index)`` links (order-independent,
    for logging/tests). Never fabricates: an unmatched hint yields only
    _chain_target_ref, with group/role/partner left None.
    """
    for s in stops:
        s["_chain_group_id"] = None
        s["_chain_role"] = None
        s["_chain_target_ref"] = None
        s["_chain_partner_index"] = None

    # Index every stop that has a usable address key, for O(1) in-batch lookup.
    by_key = {}
    for i, s in enumerate(stops):
        k = address_key(s.get("address"))
        if k:
            by_key.setdefault(k, []).append(i)

    links = []
    for i, s in enumerate(stops):
        hint = s.get("chain_hint")
        if not isinstance(hint, dict):
            continue
        if s["_chain_group_id"] is not None:
            continue  # already linked from the partner's side
        direction = (hint.get("direction") or "").strip().lower()
        target_text = (hint.get("target_text") or "").strip()
        if direction not in _VALID_DIRECTIONS or not target_text:
            continue

        # Breadcrumb + intended direction kept regardless of whether a partner is
        # found. The link (group_id + partner) is what "actually chained" hangs on;
        # readers gate on chain_group_id, so a role with no group is inert but lets
        # a later re-resolve (e.g. after an address edit) reconstruct the hint.
        s["_chain_target_ref"] = target_text
        s["_chain_role"] = direction

        tkey = address_key(target_text)
        partner = None
        if tkey is not None:
            for cand in by_key.get(tkey, ()):
                if cand == i:
                    continue
                if stops[cand]["_chain_group_id"] is not None:
                    continue  # already spoken for
                partner = cand
                break
        if partner is None:
            continue  # no match in batch -> never fabricate a link

        gid = _new_group_id()
        if direction == "supplies":
            sup_i, rec_i = i, partner
        else:  # 'receives' — the hint is on the receiving stop
            sup_i, rec_i = partner, i

        stops[sup_i]["_chain_group_id"] = gid
        stops[sup_i]["_chain_role"] = "supplies"
        stops[sup_i]["_chain_partner_index"] = rec_i
        stops[rec_i]["_chain_group_id"] = gid
        stops[rec_i]["_chain_role"] = "receives"
        stops[rec_i]["_chain_partner_index"] = sup_i
        links.append((sup_i, rec_i))

    return links
