// main.ts is mend, the CLI SPEC.md specifies. Node 22+, the standard library alone; run it as
// `node main.ts [options] [PATCH]`.
//
// It reads a patch in one of four formats (unified diff, SEARCH/REPLACE blocks, V4A patches, JSON
// text-editor tool calls), finds the lines each edit names at the first of three matching tiers,
// and writes every change or none (atomic), printing what it changed or why it failed.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands
// over to runner.ts (the last lines below): keep that hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file as lines plus its own line break and whether it ends with one (SPEC.md section 3). */
interface FileState {
  lines: string[];
  br: '\r\n' | '\n';
  final: boolean;
}

function parseFile(text: string): FileState {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br: '\r\n' | '\n' = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const fin = text.endsWith(br);
  if (fin) parts.pop();
  return { lines: parts, br, final: fin };
}

function writeFile(st: FileState): string {
  if (st.lines.length === 0) return '';
  return st.lines.join(st.br) + (st.final ? st.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  /** Successful moves, in order, for the `R old -> new` output rows. */
  readonly moves: Array<[string, string]> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/* Matching lines (SPEC.md section 5). */

const rtrim = (s: string): string => s.replace(/[ \t]+$/, '');
const trimBoth = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadingOf = (s: string): string => /^[ \t]*/.exec(s)![0];

function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return rtrim(a) === rtrim(b);
  return trimBoth(a) === trimBoth(b);
}

/** Positions i >= from where pat matches lines[i, i+1, ...] at the tier. */
function findOccurrences(lines: string[], pat: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  const k = pat.length;
  if (k === 0) return out;
  for (let i = from; i + k <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < k; j++) {
      if (!lineEq(pat[j]!, lines[i + j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/**
 * The first tier at which pat occurs at least once (at or after `from`, and, for an end-of-file
 * chunk, only occurrences ending at the file's last line), with its occurrences.
 */
function firstTier(
  lines: string[],
  pat: string[],
  strict: boolean,
  from: number,
  eof: boolean,
): { tier: number; occ: number[] } | null {
  const maxTier = strict ? 0 : 2;
  for (let t = 0; t <= maxTier; t++) {
    let occ = findOccurrences(lines, pat, t, from);
    if (eof) occ = occ.filter((p) => p + pat.length === lines.length);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

interface OldNewLine {
  text: string;
  ctx: boolean;
}

/**
 * The lines N writes in place of the matched O at position pos. Context lines are written as the
 * file's own matched lines; at tier 2 every other line is re-indented from O's first line's
 * leading whitespace to the file's first matched line's.
 */
function buildReplacement(
  fileLines: string[],
  pos: number,
  o: OldNewLine[],
  n: OldNewLine[],
  tier: number,
): string[] {
  const out: string[] = [];
  const oCtxIdx: number[] = [];
  o.forEach((l, idx) => {
    if (l.ctx) oCtxIdx.push(idx);
  });
  let rank = 0;
  const f = leadingOf(fileLines[pos] ?? '');
  const p = o.length > 0 ? leadingOf(o[0]!.text) : '';
  for (const nl of n) {
    if (nl.ctx) {
      out.push(fileLines[pos + oCtxIdx[rank]!]!);
      rank++;
    } else if (tier === 2) {
      const t = nl.text;
      if (t !== '' && t.trim() !== '' && t.startsWith(p)) out.push(f + t.slice(p.length));
      else out.push(t);
    } else {
      out.push(nl.text);
    }
  }
  return out;
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* Unified diffs (SPEC.md section 6). */

interface HunkLine {
  kind: ' ' | '-' | '+';
  text: string;
  /** A `\` line followed this body line. */
  noNL: boolean;
  /** This body line came from an empty patch line. */
  fromEmpty: boolean;
}

interface Hunk {
  /** A from the `@@ -A[,B] +C[,D] @@` header. */
  a: number;
  lines: HunkLine[];
}

interface UniSection {
  /** null when the path is /dev/null (no file). */
  oldPath: string | null;
  newPath: string | null;
  creation: boolean;
  deletion: boolean;
  hunks: Hunk[];
  /** A `--- ` / `+++ ` pair named the paths (rename lines do not override it). */
  pair: boolean;
  renameFrom: string | null;
  renameTo: string | null;
}

/** The path of a `--- ` / `+++ ` header line, or null for /dev/null. */
function hhPath(line: string): string | null {
  let p = line.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: UniSection[] = [];
  const n = lines.length;
  let i = 0;
  let cur: UniSection | null = null;
  let inHeader = false;
  while (i < n) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(.+) b\/(.+)$/.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      cur = { oldPath: m[1]!.trim(), newPath: m[2]!.trim(), creation: false, deletion: false, hunks: [], pair: false, renameFrom: null, renameTo: null };
      sections.push(cur);
      inHeader = true;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && inHeader && cur.pair === false) {
        cur.oldPath = hhPath(line);
        cur.newPath = hhPath(lines[i + 1]!);
        cur.pair = true;
        i += 2;
        continue;
      }
      cur = { oldPath: hhPath(line), newPath: hhPath(lines[i + 1]!), creation: false, deletion: false, hunks: [], pair: true, renameFrom: null, renameTo: null };
      sections.push(cur);
      inHeader = true;
      i += 2;
      continue;
    }
    if (line.startsWith('--- ') && cur !== null && inHeader) {
      throw new Exit2(`error: parse ${i + 2}`);
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const hunk: Hunk = { a: parseInt(m[1]!, 10), lines: [] };
      i++;
      while (i < n) {
        const bl = lines[i]!;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (bl === '') {
          hunk.lines.push({ kind: ' ', text: '', noNL: false, fromEmpty: true });
          i++;
          continue;
        }
        const c = bl[0]!;
        if (c === ' ' || c === '-' || c === '+') {
          hunk.lines.push({ kind: c, text: bl.slice(1), noNL: false, fromEmpty: false });
          i++;
          continue;
        }
        if (c === '\\') {
          if (hunk.lines.length > 0) hunk.lines[hunk.lines.length - 1]!.noNL = true;
          i++;
          continue;
        }
        break;
      }
      while (hunk.lines.length > 0 && hunk.lines[hunk.lines.length - 1]!.fromEmpty) hunk.lines.pop();
      cur.hunks.push(hunk);
      inHeader = false;
      continue;
    }
    if (cur !== null && inHeader) {
      if (line.startsWith('rename from ')) cur.renameFrom = line.slice('rename from '.length).trim();
      else if (line === 'rename from') cur.renameFrom = '';
      else if (line.startsWith('rename to ')) cur.renameTo = line.slice('rename to '.length).trim();
      else if (line === 'rename to') cur.renameTo = '';
      else if (/^new file mode(\s|$)/.test(line)) cur.creation = true;
      else if (/^deleted file mode(\s|$)/.test(line)) cur.deletion = true;
    }
    i++;
  }
  for (const s of sections) {
    if (!s.pair) {
      if (s.renameFrom !== null) s.oldPath = s.renameFrom;
      if (s.renameTo !== null) s.newPath = s.renameTo;
    }
    if (s.oldPath === null) s.creation = true;
    if (s.newPath === null) s.deletion = true;
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((s) => unifiedSectionEdit(s, strict));
}

/** Whether a `\` line follows the hunk's last context or `+` line. */
function hunkNoNL(hunk: Hunk): boolean {
  for (let k = hunk.lines.length - 1; k >= 0; k--) {
    const l = hunk.lines[k]!;
    if (l.kind === ' ' || l.kind === '+') return l.noNL;
  }
  return false;
}

function hunkOldNew(hunk: Hunk): { o: OldNewLine[]; n: OldNewLine[] } {
  const o: OldNewLine[] = [];
  const n: OldNewLine[] = [];
  for (const l of hunk.lines) {
    if (l.kind !== '+') o.push({ text: l.text, ctx: l.kind === ' ' });
    if (l.kind !== '-') n.push({ text: l.text, ctx: l.kind === ' ' });
  }
  return { o, n };
}

function applyUnifiedHunk(state: FileState, hunk: Hunk, d: number, strict: boolean, path: string): FileState {
  const { o, n } = hunkOldNew(hunk);
  if (o.length === 0) {
    if (n.length === 0) return state;
    const at = Math.max(0, Math.min(hunk.a + d, state.lines.length));
    const lines = [...state.lines.slice(0, at), ...n.map((x) => x.text), ...state.lines.slice(at)];
    let fin = state.final;
    if (at === state.lines.length) fin = !hunkNoNL(hunk);
    return { lines, br: state.br, final: fin };
  }
  const found = firstTier(state.lines, o.map((x) => x.text), strict, 0, false);
  if (!found) throw new Fail('no-match', path);
  const target = hunk.a - 1 + d;
  let best = found.occ[0]!;
  for (const p of found.occ) {
    if (Math.abs(p - target) < Math.abs(best - target)) best = p;
  }
  const rep = buildReplacement(state.lines, best, o, n, found.tier);
  const lines = [...state.lines.slice(0, best), ...rep, ...state.lines.slice(best + o.length)];
  let fin = state.final;
  if (best + o.length === state.lines.length) fin = !hunkNoNL(hunk);
  return { lines, br: state.br, final: fin };
}

function unifiedSectionEdit(s: UniSection, strict: boolean): Edit {
  return (tree) => {
    const oldP = s.oldPath;
    const newP = s.newPath;
    if (oldP !== null && !safe(oldP)) throw new Fail('unsafe', oldP);
    if (newP !== null && !safe(newP)) throw new Fail('unsafe', newP);
    if (s.creation) {
      if (newP === null) return;
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const plus: string[] = [];
      let noNL = false;
      for (const h of s.hunks) {
        for (const l of h.lines) if (l.kind === '+') plus.push(l.text);
      }
      for (let hi = s.hunks.length - 1; hi >= 0; hi--) {
        const h = s.hunks[hi]!;
        let done = false;
        for (let k = h.lines.length - 1; k >= 0; k--) {
          if (h.lines[k]!.kind === '+') {
            noNL = h.lines[k]!.noNL;
            done = true;
            break;
          }
        }
        if (done) break;
      }
      tree.now.set(newP, plus.length === 0 ? '' : plus.join('\n') + (noNL ? '' : '\n'));
      return;
    }
    if (s.deletion) {
      if (oldP === null) return;
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      tree.now.set(oldP, null);
      return;
    }
    if (oldP !== null && newP !== null && oldP !== newP) {
      const text = tree.get(oldP);
      if (text === null) throw new Fail('missing', oldP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      let state = parseFile(text);
      let d = 0;
      for (const h of s.hunks) {
        const plus = h.lines.filter((l) => l.kind === '+').length;
        const minus = h.lines.filter((l) => l.kind === '-').length;
        state = applyUnifiedHunk(state, h, d, strict, oldP);
        d += plus - minus;
      }
      tree.now.set(newP, writeFile(state));
      tree.now.set(oldP, null);
      tree.moves.push([oldP, newP]);
      return;
    }
    const p = oldP ?? newP;
    if (p === null) return;
    const text = tree.get(p);
    if (text === null) throw new Fail('missing', p);
    let state = parseFile(text);
    let d = 0;
    for (const h of s.hunks) {
      const plus = h.lines.filter((l) => l.kind === '+').length;
      const minus = h.lines.filter((l) => l.kind === '-').length;
      state = applyUnifiedHunk(state, h, d, strict, p);
      d += plus - minus;
    }
    tree.now.set(p, writeFile(state));
  };
}

/* SEARCH/REPLACE blocks (SPEC.md section 7). */

interface SRBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const blocks: SRBlock[] = [];
  const n = lines.length;
  let prevReplaceEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < n) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchIdx = i;
    let path: string | null = null;
    for (let j = searchIdx - 1; j >= prevReplaceEnd; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      const t = l.trim();
      if (t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchIdx + 1}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = searchIdx + 1; j < n; j++) {
      const t = lines[j]!.trimEnd();
      if (t === '=======') {
        eq = j;
        break;
      }
      if (t === '>>>>>>> REPLACE' || t === '<<<<<<< SEARCH') break;
    }
    let rep = -1;
    if (eq >= 0) {
      for (let j = eq + 1; j < n; j++) {
        const t = lines[j]!.trimEnd();
        if (t === '>>>>>>> REPLACE') {
          rep = j;
          break;
        }
        if (t === '<<<<<<< SEARCH') break;
      }
    }
    if (eq < 0 || rep < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    blocks.push({ path, oldLines: lines.slice(searchIdx + 1, eq), newLines: lines.slice(eq + 1, rep) });
    prevPath = path;
    prevReplaceEnd = rep + 1;
    i = rep + 1;
  }
  if (blocks.length === 0) throw new Exit2('error: parse 1');
  return blocks.map((b) => searchReplaceEdit(b, strict));
}

function searchReplaceEdit(b: SRBlock, strict: boolean): Edit {
  return (tree) => {
    if (!safe(b.path)) throw new Fail('unsafe', b.path);
    if (b.oldLines.length === 0) {
      if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
      tree.now.set(b.path, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
      return;
    }
    const text = tree.get(b.path);
    if (text === null) throw new Fail('missing', b.path);
    const state = parseFile(text);
    const found = firstTier(state.lines, b.oldLines, strict, 0, false);
    if (!found) throw new Fail('no-match', b.path);
    if (found.occ.length > 1) throw new Fail('ambiguous', b.path);
    const pos = found.occ[0]!;
    const rep = buildReplacement(
      state.lines,
      pos,
      b.oldLines.map((t) => ({ text: t, ctx: false })),
      b.newLines.map((t) => ({ text: t, ctx: false })),
      found.tier,
    );
    const outLines = [...state.lines.slice(0, pos), ...rep, ...state.lines.slice(pos + b.oldLines.length)];
    tree.now.set(b.path, writeFile({ lines: outLines, br: state.br, final: state.final }));
  };
}

/* V4A patches (SPEC.md section 8). */

interface V4AChunk {
  /** null when the `@@` line carries no anchor. */
  anchor: string | null;
  body: { kind: ' ' | '-' | '+'; text: string }[];
  eof: boolean;
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  const end = last;
  let i = first + 1;
  const isSectionStart = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l === '*** Add File:' ||
    l.startsWith('*** Delete File: ') || l === '*** Delete File:' ||
    l.startsWith('*** Update File: ') || l === '*** Update File:';
  while (i < end) {
    while (i < end && blank(lines[i]!)) i++;
    if (i >= end) break;
    const line = lines[i]!;
    let kind: 'add' | 'del' | 'upd';
    let path: string;
    if (line.startsWith('*** Add File: ')) {
      kind = 'add';
      path = line.slice('*** Add File: '.length).trim();
    } else if (line === '*** Add File:') {
      kind = 'add';
      path = '';
    } else if (line.startsWith('*** Delete File: ')) {
      kind = 'del';
      path = line.slice('*** Delete File: '.length).trim();
    } else if (line === '*** Delete File:') {
      kind = 'del';
      path = '';
    } else if (line.startsWith('*** Update File: ')) {
      kind = 'upd';
      path = line.slice('*** Update File: '.length).trim();
    } else if (line === '*** Update File:') {
      kind = 'upd';
      path = '';
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    const secLineNo = i + 1;
    i++;
    const secLines: { text: string; no: number }[] = [];
    while (i < end && !isSectionStart(lines[i]!)) {
      secLines.push({ text: lines[i]!, no: i + 1 });
      i++;
    }
    while (secLines.length > 0 && blank(secLines[secLines.length - 1]!.text)) secLines.pop();
    edits.push(v4aSectionEdit(kind, path, secLineNo, secLines, strict));
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

function v4aSectionEdit(
  kind: 'add' | 'del' | 'upd',
  path: string,
  secLineNo: number,
  secLines: { text: string; no: number }[],
  strict: boolean,
): Edit {
  if (kind === 'add') {
    const fileLines: string[] = [];
    for (const l of secLines) {
      if (l.text.startsWith('+')) fileLines.push(l.text.slice(1));
      else if (l.text === '') fileLines.push('');
      else throw new Exit2(`error: parse ${l.no}`);
    }
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
    };
  }
  if (kind === 'del') {
    if (secLines.length > 0) throw new Exit2(`error: parse ${secLines[0]!.no}`);
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) === null) throw new Fail('missing', path);
      tree.now.set(path, null);
    };
  }
  let moveTo: string | null = null;
  let idx = 0;
  if (secLines.length > 0 && (secLines[0]!.text.startsWith('*** Move to: ') || secLines[0]!.text === '*** Move to:')) {
    moveTo = secLines[0]!.text.startsWith('*** Move to: ')
      ? secLines[0]!.text.slice('*** Move to: '.length).trim()
      : '';
    idx = 1;
  }
  const chunks: V4AChunk[] = [];
  let cur: V4AChunk | null = null;
  for (; idx < secLines.length; idx++) {
    const l = secLines[idx]!;
    const t = l.text;
    if (t.startsWith('@@')) {
      if (cur) chunks.push(cur);
      const a = t.slice(2).trim();
      cur = { anchor: a === '' ? null : a, body: [], eof: false };
    } else if (t === '*** End of File') {
      if (!cur) throw new Exit2(`error: parse ${l.no}`);
      cur.eof = true;
      chunks.push(cur);
      cur = null;
    } else if (t.startsWith(' ') || t.startsWith('-') || t.startsWith('+') || t === '') {
      if (!cur) {
        if (chunks.length === 0) cur = { anchor: null, body: [], eof: false };
        else throw new Exit2(`error: parse ${l.no}`);
      }
      cur.body.push({ kind: t === '' ? ' ' : (t[0] as ' ' | '-' | '+'), text: t === '' ? '' : t.slice(1) });
    } else {
      throw new Exit2(`error: parse ${l.no}`);
    }
  }
  if (cur) chunks.push(cur);
  if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${secLineNo}`);
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const text = tree.get(path);
    if (text === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    let state = parseFile(text);
    let cursor = 0;
    for (const chunk of chunks) {
      if (chunk.anchor !== null) {
        const at = findAnchor(state.lines, chunk.anchor, strict, cursor);
        if (at === null) throw new Fail('no-match', path);
        cursor = at + 1;
      }
      const o: OldNewLine[] = [];
      const n: OldNewLine[] = [];
      for (const l of chunk.body) {
        if (l.kind !== '+') o.push({ text: l.text, ctx: l.kind === ' ' });
        if (l.kind !== '-') n.push({ text: l.text, ctx: l.kind === ' ' });
      }
      if (o.length === 0) {
        const at = chunk.eof ? state.lines.length : cursor;
        const outLines = [...state.lines.slice(0, at), ...n.map((x) => x.text), ...state.lines.slice(at)];
        state = { lines: outLines, br: state.br, final: state.final };
        cursor = at + n.length;
        continue;
      }
      const found = firstTier(state.lines, o.map((x) => x.text), strict, cursor, chunk.eof);
      if (!found) throw new Fail('no-match', path);
      const pos = found.occ[0]!;
      const rep = buildReplacement(state.lines, pos, o, n, found.tier);
      const outLines = [...state.lines.slice(0, pos), ...rep, ...state.lines.slice(pos + o.length)];
      state = { lines: outLines, br: state.br, final: state.final };
      cursor = pos + rep.length;
    }
    const out = writeFile(state);
    if (moveTo !== null) {
      tree.now.set(moveTo, out);
      tree.now.set(path, null);
      tree.moves.push([path, moveTo]);
    } else {
      tree.now.set(path, out);
    }
  };
}

/** The first line at or after `from` equal to the anchor at the first tier where one is. */
function findAnchor(lines: string[], anchor: string, strict: boolean, from: number): number | null {
  const maxTier = strict ? 0 : 2;
  for (let t = 0; t <= maxTier; t++) {
    for (let k = from; k < lines.length; k++) {
      if (lineEq(anchor, lines[k]!, t)) return k;
    }
  }
  return null;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict)
          : kind === 'search-replace'
            ? searchReplaceEdits(lines, strict)
            : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesLen = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesLen;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const byteCmp = (a: string, b: string): number => Buffer.compare(Buffer.from(a), Buffer.from(b));
  const suppressed = new Set<string>();
  const rows: { key: string; text: string }[] = [];
  for (const [oldP, newP] of tree.moves) {
    if (tree.original(oldP) !== null && tree.get(oldP) === null && tree.original(newP) === null && tree.get(newP) !== null) {
      rows.push({ key: newP, text: `R ${oldP} -> ${newP}` });
      suppressed.add(oldP);
      suppressed.add(newP);
    }
  }
  for (const p of tree.now.keys()) {
    if (suppressed.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => byteCmp(a.key, b.key));
  if (!check) {
    for (const p of [...tree.now.keys()].sort(byteCmp)) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.text), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
