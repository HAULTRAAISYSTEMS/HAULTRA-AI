// Unit tests for the staging-tray sequencing rules (pure JS, run with Node).
//   node tests/test_tray_sequence.mjs
// Verifies the ordering the Python suite can't: interleaved AI/Quick-Add entry,
// batch-scoped re-parse, and drag reorder.
import { createRequire } from 'module';
import { fileURLToPath } from 'url';
import path from 'path';
const require = createRequire(import.meta.url);
const T = require(path.join(path.dirname(fileURLToPath(import.meta.url)), '..', 'static', 'tray_sequence.js'));

let pass = 0;
function ok(cond, msg) {
  if (cond) { pass++; console.log('PASS - ' + msg); }
  else { console.log('FAIL - ' + msg); process.exit(1); }
}
const ids = (stops) => T.sortBySeq(stops).map((s) => s.id);
const mk = (id) => ({ id });

// Interleaved entry: AI(2) -> QuickAdd(3) -> AI(1) renders in exact entry order.
let tray = [];
tray = T.appendBatch(tray, [mk('a1'), mk('a2')], 'ai-1');            // AI batch
tray = T.appendBatch(tray, [mk('q1')], 'qa-1');                      // Quick Add
tray = T.appendBatch(tray, [mk('q2')], 'qa-2');
tray = T.appendBatch(tray, [mk('q3')], 'qa-3');
tray = T.appendBatch(tray, [mk('a3')], 'ai-2');                      // second AI batch
ok(JSON.stringify(ids(tray)) === JSON.stringify(['a1', 'a2', 'q1', 'q2', 'q3', 'a3']),
   'interleaved AI(2)->QuickAdd(3)->AI(1) renders in exact entry order, not grouped by source');

// Re-parse the FIRST AI batch -> Quick Add + later batch keep position and content.
let reparsed = T.replaceBatch(tray, 'ai-1', [mk('a1b'), mk('a2b')]);
ok(JSON.stringify(ids(reparsed)) === JSON.stringify(['a1b', 'a2b', 'q1', 'q2', 'q3', 'a3']),
   're-parse of a batch keeps every other stop in position');
const qSeqBefore = T.sortBySeq(tray).filter((s) => s.id[0] === 'q').map((s) => s.seq);
const qSeqAfter = T.sortBySeq(reparsed).filter((s) => s.id[0] === 'q').map((s) => s.seq);
ok(JSON.stringify(qSeqBefore) === JSON.stringify(qSeqAfter), 're-parse does not shift Quick-Add seq values');

// Re-parse returning MORE stops than the batch had -> renumber only within the
// batch's range, surrounding stops keep relative order.
let grown = T.replaceBatch(reparsed, 'ai-2', [mk('x1'), mk('x2'), mk('x3')]);  // ai-2 had 1, now 3
ok(JSON.stringify(ids(grown)) === JSON.stringify(['a1b', 'a2b', 'q1', 'q2', 'q3', 'x1', 'x2', 'x3']),
   're-parse 1 stop -> 3 stops: surrounding stops keep relative order, new stops fill the range');

// Re-parse a MIDDLE batch to a different count -> outside order preserved both sides.
let midGrow = T.replaceBatch(tray, 'qa-2', [mk('m1'), mk('m2')]);  // qa-2 (q2) had 1, now 2
ok(JSON.stringify(ids(midGrow)) === JSON.stringify(['a1', 'a2', 'q1', 'm1', 'm2', 'q3', 'a3']),
   're-parse a middle batch to 2 stops keeps both surrounding sides in order');

// Drag reorder: move the last stop to position 2 -> seq rewritten, order matches.
let dragged = T.reorder(tray, ['a1', 'a3', 'a2', 'q1', 'q2', 'q3']);
ok(JSON.stringify(ids(dragged)) === JSON.stringify(['a1', 'a3', 'a2', 'q1', 'q2', 'q3']),
   'drag reorder rewrites seq so display order becomes insert order');
ok(T.sortBySeq(dragged).every((s, i) => s.seq === i + 1), 'drag reorder produces clean 1..N seq');

// Reset behavior: a cleared tray restarts seq at 1.
ok(T.nextSeqValue([]) === 1, 'cleared tray restarts the seq counter at 1');

console.log('\nALL TRAY-SEQUENCE TESTS PASSED (' + pass + ')');
