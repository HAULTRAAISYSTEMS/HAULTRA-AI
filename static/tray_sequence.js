/*
 * Staging-tray sequencing — the ONE source of truth for the order of pending
 * (pre-insert) parser stops. Pure functions over an array of stop objects, each
 * carrying at least { id, seq, batch_id, source }. Order is driven strictly by
 * `seq` (a single counter shared by BOTH the AI and Quick-Add lanes), never by
 * source — a stop created third is third, whichever button made it.
 *
 * Loaded as a browser global (window.TraySeq) by parser.html AND required by a
 * Node test, so the ordering rules are verified independently of the DOM.
 */
(function (root) {
  'use strict';

  // Next integer seq for a stop appended at the END of the tray. Derived from the
  // current stops so a cleared tray (empty array) naturally restarts at 1 — that
  // is the "reset the counter" behavior after a successful insert.
  function nextSeqValue(stops) {
    var m = 0;
    (stops || []).forEach(function (s) {
      if (typeof s.seq === 'number' && s.seq > m) m = s.seq;
    });
    return m + 1;
  }

  // Append a fresh batch to the end, assigning contiguous seqs. Every stop in the
  // batch is tagged with batch_id so a later re-parse can find exactly this batch.
  function appendBatch(stops, batchStops, batchId) {
    stops = stops || [];
    var start = nextSeqValue(stops);
    (batchStops || []).forEach(function (s, i) {
      s.batch_id = batchId;
      s.seq = start + i;
    });
    return stops.concat(batchStops || []);
  }

  // Replace ALL stops of `batchId` with `newStops`, reusing the seq window the old
  // batch occupied so every surrounding stop stays exactly put. If the new batch
  // has a different count, the new stops are spread across the same window (they
  // renumber only WITHIN the batch's range) — outside seqs never shift. If the
  // batch isn't present yet, this is just an append.
  function replaceBatch(stops, batchId, newStops) {
    stops = stops || [];
    newStops = newStops || [];
    var old = stops.filter(function (s) { return s.batch_id === batchId; });
    var others = stops.filter(function (s) { return s.batch_id !== batchId; });
    if (!old.length) return appendBatch(stops, newStops, batchId);

    var oldSeqs = old.map(function (s) { return s.seq; });
    var lo = Math.min.apply(null, oldSeqs);
    var hi = Math.max.apply(null, oldSeqs);
    // the seqs of the stops immediately bracketing the old batch's window
    var prev = -Infinity, next = Infinity;
    others.forEach(function (s) {
      if (s.seq < lo && s.seq > prev) prev = s.seq;
      if (s.seq > hi && s.seq < next) next = s.seq;
    });
    var lower = (prev === -Infinity) ? (lo - 1) : prev;
    var upper = (next === Infinity) ? (hi + 1) : next;
    // spread the new stops strictly inside (lower, upper); fractional seqs keep the
    // outside integers untouched while preserving order for any batch count.
    newStops.forEach(function (s, i) {
      s.batch_id = batchId;
      s.seq = lower + (upper - lower) * (i + 1) / (newStops.length + 1);
    });
    return others.concat(newStops);
  }

  // Rewrite seq to a clean 1..N in the given id order (a drag-reorder result), so
  // the display order becomes the insert order. Any id not listed (defensive) is
  // appended in its prior seq order.
  function reorder(stops, orderedIds) {
    stops = stops || [];
    var byId = {};
    stops.forEach(function (s) { byId[s.id] = s; });
    var ordered = [];
    (orderedIds || []).forEach(function (id) {
      if (byId[id]) { ordered.push(byId[id]); delete byId[id]; }
    });
    var rest = stops.filter(function (s) { return byId[s.id]; })
                    .sort(function (a, b) { return a.seq - b.seq; });
    ordered = ordered.concat(rest);
    ordered.forEach(function (s, i) { s.seq = i + 1; });
    return ordered;
  }

  // A stable copy sorted by seq — what the tray renders and what the insert payload
  // iterates. Ties (shouldn't happen) fall back to insertion order via id compare.
  function sortBySeq(stops) {
    return (stops || []).slice().sort(function (a, b) {
      if (a.seq !== b.seq) return a.seq - b.seq;
      return String(a.id) < String(b.id) ? -1 : 1;
    });
  }

  var api = {
    nextSeqValue: nextSeqValue,
    appendBatch: appendBatch,
    replaceBatch: replaceBatch,
    reorder: reorder,
    sortBySeq: sortBySeq,
  };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  root.TraySeq = api;
})(typeof self !== 'undefined' ? self : this);
