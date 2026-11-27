// A faster drop-in for makefun-diff 1.0.0's diffPatch: the same patch, byte for byte, computed with integer
// line ids and typed-array Myers snapshots instead of string compares and per-path objects. The edit script
// is the reference's rule: common prefix, common suffix of what is left, then Myers's greedy search between
// them keeping on each diagonal the path furthest into the old text, the deletion's path when a deletion and
// an insertion reach the same point, no move past either end, no pruned diagonal, every equal run followed.

const FORMAT = 'makefun-diff/1';
const CONTEXT = 3;
const KEEP = 0;
const DELETE = 1;
const INSERT = 2;

/** A text's lines, each with its "\n" (the last one without, when the text does not end in one). */
function tokenize(text) {
  const lines = [];
  let start = 0;
  let idx = text.indexOf('\n', start);
  while (idx !== -1) {
    lines.push(text.slice(start, idx + 1));
    start = idx + 1;
    idx = text.indexOf('\n', start);
  }
  if (start < text.length) lines.push(text.slice(start));
  return lines;
}

/** The runs of the edit script of aIds[0..n) into bIds[0..m): parallel arrays of kind and count. */
function editRuns(aIds, n, bIds, m, kinds, counts) {
  if (n === 0) {
    if (m > 0) {
      kinds.push(INSERT);
      counts.push(m);
    }
    return;
  }
  if (m === 0) {
    kinds.push(DELETE);
    counts.push(n);
    return;
  }
  // Forward Myers. Level d holds x for diagonals k = -d..d step 2 at index j = (k + d) / 2, stored in one
  // growing Int32Array at offset d*(d+1)/2; -1 marks a diagonal no path reaches. x counts old lines consumed.
  let cap = 1 << 22;
  let snap = new Int32Array(cap);
  // d = 0: the opening snake.
  let x = 0;
  const lim0 = n < m ? n : m;
  while (x < lim0 && aIds[x] === bIds[x]) x++;
  snap[0] = x;
  let D = 0;
  if (x < n || x < m) {
    const maxEdit = n + m;
    outer:
    for (let d = 1; d <= maxEdit; d++) {
      const off = (d * (d + 1)) / 2;
      const prevOff = ((d - 1) * d) / 2;
      if (off + d + 1 > cap) {
        let next = cap;
        while (next < off + d + 1) next *= 2;
        const grown = new Int32Array(next);
        grown.set(snap);
        snap = grown;
        cap = next;
      }
      let prevXi = snap[prevOff];
      for (let j = 0; j <= d; j++) {
        const k = -d + 2 * j;
        // Deletion candidate from diagonal k - 1 (level d - 1 index j - 1): one more old line.
        // Insertion candidate from diagonal k + 1 (level d - 1 index j): one more new line.
        // prevXi carries level d - 1's index-j value across iterations (it is the next j's deletion read).
        const xi = j < d ? prevXi : -1;
        if (j < d) prevXi = snap[prevOff + j + 1];
        let best = -1;
        if (j > 0) {
          const xd = snap[prevOff + j - 1];
          if (xd >= 0 && xd < n) best = xd + 1;
        }
        if (xi >= 0 && xi - (k + 1) < m && xi > best) best = xi;
        if (best < 0) {
          snap[off + j] = -1;
          continue;
        }
        let cx = best;
        const lim = m + k < n ? m + k : n;
        while (cx < lim && aIds[cx] === bIds[cx - k]) cx++;
        snap[off + j] = cx;
        if (cx >= n && cx - k >= m) {
          D = d;
          break outer;
        }
      }
    }
  }
  // Backtrack from (n, m) at level D, reapplying the forward choice rule against the stored snapshots.
  // Ops are collected backwards: kind of each single step, with snakes as keep counts.
  const revKinds = [];
  const revCounts = [];
  let bx = n;
  let by = m;
  for (let d = D; d >= 1; d--) {
    const k = bx - by;
    const prevOff = ((d - 1) * d) / 2;
    const j = (k + d) / 2;
    let delX = -1;
    let insX = -1;
    if (j > 0) {
      const xd = snap[prevOff + j - 1];
      if (xd >= 0 && xd < n) delX = xd + 1;
    }
    if (j < d) {
      const xi = snap[prevOff + j];
      if (xi >= 0 && xi - (k + 1) < m) insX = xi;
    }
    const byDeletion = delX >= insX;
    const startX = byDeletion ? delX : insX;
    const snake = bx - startX;
    if (snake > 0) {
      revKinds.push(KEEP);
      revCounts.push(snake);
    }
    if (byDeletion) {
      revKinds.push(DELETE);
      revCounts.push(1);
      by = startX - k;
      bx = startX - 1;
    } else {
      revKinds.push(INSERT);
      revCounts.push(1);
      by = startX - k - 1;
      bx = startX;
    }
  }
  if (bx > 0) {
    revKinds.push(KEEP);
    revCounts.push(bx);
  }
  // Reverse into forward runs, coalescing neighbours of one kind.
  for (let i = revKinds.length - 1; i >= 0; i--) {
    const kind = revKinds[i];
    const last = kinds.length - 1;
    if (last >= 0 && kinds[last] === kind) counts[last] += revCounts[i];
    else {
      kinds.push(kind);
      counts.push(revCounts[i]);
    }
  }
}

/** A line as the patch writes it: its op, the line, a newline, and "%" on a line of its own when it had none. */
function written(op, line) {
  return line.endsWith('\n') ? op + line : op + line + '\n%\n';
}

/** makefun-diff 1.0.0's answer for one case's input. */
export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const a = tokenize(input.old);
  const b = tokenize(input.new);
  const n = a.length;
  const m = b.length;
  // One integer id per distinct line, shared by both texts.
  const ids = new Map();
  const aIds = new Int32Array(n);
  const bIds = new Int32Array(m);
  for (let i = 0; i < n; i++) {
    const line = a[i];
    let id = ids.get(line);
    if (id === undefined) {
      id = ids.size;
      ids.set(line, id);
    }
    aIds[i] = id;
  }
  for (let i = 0; i < m; i++) {
    const line = b[i];
    let id = ids.get(line);
    if (id === undefined) {
      id = ids.size;
      ids.set(line, id);
    }
    bIds[i] = id;
  }
  // The common prefix, then the common suffix of what is left.
  let prefix = 0;
  while (prefix < n && prefix < m && aIds[prefix] === bIds[prefix]) prefix++;
  let suffix = 0;
  while (suffix < n - prefix && suffix < m - prefix && aIds[n - 1 - suffix] === bIds[m - 1 - suffix]) suffix++;
  const kinds = [];
  const counts = [];
  if (prefix > 0) {
    kinds.push(KEEP);
    counts.push(prefix);
  }
  editRuns(
    aIds.subarray(prefix, n - suffix), n - suffix - prefix,
    bIds.subarray(prefix, m - suffix), m - suffix - prefix,
    kinds, counts,
  );
  if (suffix > 0) {
    const last = kinds.length - 1;
    if (last >= 0 && kinds[last] === KEEP) counts[last] += suffix;
    else {
      kinds.push(KEEP);
      counts.push(suffix);
    }
  }

  // The change runs: each a stretch of deletions and insertions between two kept lines.
  const changes = [];
  let o = 0;
  let p = 0;
  let deleted = 0;
  let inserted = 0;
  for (let i = 0; i < kinds.length; i++) {
    const kind = kinds[i];
    const count = counts[i];
    if (kind === KEEP) {
      o += count;
      p += count;
      continue;
    }
    let c = changes[changes.length - 1];
    if (c === undefined || c.o + c.dels !== o || c.p + c.ins !== p) {
      c = { o, p, dels: 0, ins: 0 };
      changes.push(c);
    }
    if (kind === DELETE) {
      c.dels += count;
      o += count;
      deleted += count;
    } else {
      c.ins += count;
      p += count;
      inserted += count;
    }
  }

  // The hunks: change runs at most 2 * CONTEXT kept lines apart share one.
  const hunks = [];
  for (const c of changes) {
    const h = hunks[hunks.length - 1];
    const prev = h === undefined ? undefined : h[h.length - 1];
    if (prev !== undefined && c.o - (prev.o + prev.dels) <= 2 * CONTEXT) h.push(c);
    else hunks.push([c]);
  }
  const out = [`${FORMAT} old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  for (const h of hunks) {
    const first = h[0];
    const last = h[h.length - 1];
    const oldStart = Math.max(0, first.o - CONTEXT);
    const newStart = first.p - (first.o - oldStart);
    const after = Math.min(CONTEXT, n - (last.o + last.dels));
    const oldEnd = last.o + last.dels + after;
    const newEnd = last.p + last.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      for (; at < c.o; at++) out.push(written('=', a[at]));
      for (let i = 0; i < c.dels; i++) out.push(written('-', a[c.o + i]));
      for (let i = 0; i < c.ins; i++) out.push(written('+', b[c.p + i]));
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) out.push(written('=', a[at]));
  }
  return out.join('');
}
