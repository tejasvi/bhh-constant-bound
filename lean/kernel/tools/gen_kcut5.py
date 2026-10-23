"""Emit the track-K modules of the coarse C_5 tree (k = 5, 2^22 initial boxes) from the output of `kcut3t`
(BHHCert/KCutGen3t.lean; boxes without leaves are not printed and count as 0).

usage: python3 gen_kcut5.py KCUT_OUTPUT... --out ROOT [--M 12] [--comb 1500] [--mod-leaves 1000] [--part 1000]

Every printed box is treated as a cut box (a WHOLE box, at most M leaves, becomes a cut tree with one external node:
top code 15, the whole tree as the external entry; its corners are recomputed here as `initBox 5 22 t`).
* boxes with at most --comb leaves: a core module BHH/KSub3/K5/C/B{t}.lean with the chunk data, `top` (cutOK) and the
  chunk theorems (subOK, at most M leaves each), and a glue module G/B{t}.lean with `subAll` and
  `rb (hL) : RangeBound 5 RNK3_5 t (t + 1) V` (built at assembly: it imports Mathlib through BHH.MainK);
* larger boxes: BHH/KSub3/K5/B{t}/{Data, S*, Box}.lean as in tools/gen_kcut.py;
* assembly: AsmP{i}.lean combine at most --part consecutive pieces (boxes and the zero gaps between them, by
  RangeBound.add / RangeBound.zero) into `part (hL) : RangeBound 5 RNK3_5 a b S`, Asm.lean combines the parts into
  `range (hL) : RangeBound 5 RNK3_5 0 (2 ^ RNK3_5) S`.
Nothing here is trusted: the kernel re-checks every claim.
"""
import argparse, os

ap = argparse.ArgumentParser()
ap.add_argument('inputs', nargs='*'); ap.add_argument('--out', required=True)
ap.add_argument('--M', type=int, default=12); ap.add_argument('--comb', type=int, default=1500)
ap.add_argument('--mod-leaves', type=int, default=1000); ap.add_argument('--part', type=int, default=1000)
ap.add_argument('--no-asm', action='store_true', help='emit only the box modules and pieces_k5.txt (t V glue-module), no AsmP/Asm')
ap.add_argument('--pieces', nargs='*', default=[], help='with --asm-only: pieces_k5.txt files of all parts')
ap.add_argument('--asm-only', action='store_true', help='emit only AsmP/Asm from --pieces files')
args = ap.parse_args()
k, M, R, NB = 5, args.M, 22, 2 ** 22
LEAF, RC, SHARD = 'LkKt', 'RNK3_5', 'BHHCert.ShardKt\nimport BHHCert.ShardK3'
NS = 'BHH.KSub3.K5'
DIR = os.path.join(args.out, 'BHH', 'KSub3', 'K5')
PR = 96; ONE = 2 ** PR

# ---- initBox (exact replica of BHHCert/Tree.lean: rootLo/rootHi, widest, midpoint, bit r of t)
def root(k):
    m = 2 * k - 3
    lo = [0 if d in (0, 2) else -(k - 2) * ONE for d in range(m)]
    hi = [(k - 2) * ONE for _ in range(m)]
    return lo, hi
def widest(lo, hi):
    best, bw = 0, -1
    for d in range(len(lo)):
        w = hi[d] - lo[d]
        if w > bw: best, bw = d, w
    return best
def initBox(t):
    lo, hi = root(k)
    for r in range(R - 1, -1, -1):
        d = widest(lo, hi); mid = (lo[d] + hi[d]) // 2
        if (t >> r) & 1: lo = lo[:]; lo[d] = mid
        else: hi = hi[:]; hi[d] = mid
    return lo, hi

# ---- parse
boxes = {}
next_ext = {}   # declared number of external entries per cut box (a killed run may leave a box incomplete)
for fn in args.inputs:
    cur = None
    for line in open(fn):
        f = line.split()
        if not f: continue
        if f[0] == 'WHOLE':
            t = int(f[2]); V = int(f[3]); lv = int(f[5]); code = f[6]
            lo, hi = initBox(t)
            boxes[t] = [V, '0xf', [(V, code, lv, ','.join(map(str, lo)), ','.join(map(str, hi)))]]
        elif f[0] == 'BOX':
            cur = int(f[2]); boxes[cur] = [int(f[3]), None, []]; next_ext[cur] = int(f[6])
        elif f[0] == 'TOP':
            boxes[cur][1] = f[1]
        elif f[0] == 'EXT':
            boxes[cur][2].append((int(f[1]), f[2], int(f[3]), f[4], f[5]))
for t, b in boxes.items():
    assert b[1] is not None and b[2], t
    assert t not in next_ext or len(b[2]) == next_ext[t], ('incomplete box', t, len(b[2]), next_ext[t])
if args.asm_only:
    boxes = {}

def ext_lit(e):
    v, code, _, lo, hi = e
    return '(%d, %s, [%s], [%s])' % (v, code, lo.replace(',', ', '), hi.replace(',', ', '))

def tree(n, leaf, var='i', ind='  ', hname='c'):
    out = []
    def go(lo, hi, ind, depth):
        if hi - lo == 1:
            out.append('%sobtain rfl : %s = %d := by omega\n%s%s\n' % (ind, var, lo, ind, leaf(lo)))
            return
        mid = (lo + hi) // 2
        out.append('%sby_cases %s%d : %s < %d\n' % (ind, hname, depth, var, mid))
        out.append('%s· ' % ind); go(lo, mid, ind + '  ', depth + 1)
        out.append('%s· ' % ind); go(mid, hi, ind + '  ', depth + 1)
    go(0, n, ind, 0)
    txt, i = '', 0
    while i < len(out):
        if out[i].endswith('· '):
            txt += out[i] + out[i + 1].lstrip(' '); i += 2
        else:
            txt += out[i]; i += 1
    return txt

def range_tree(pieces, ind='  '):
    def go(lo, hi):
        if hi - lo == 1:
            return pieces[lo][2]
        mid = (lo + hi) // 2
        return ('(RangeBound.add (by norm_num) (by norm_num) (by norm_num) (by decide)\n%s %s\n%s %s)'
                % (ind, go(lo, mid), ind, go(mid, hi)))
    return go(0, len(pieces))

def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as f:
        f.write(text)

def chunks_of(exts):
    chunks, curc, acc = [], [], 0
    for e in exts:
        if curc and acc + e[2] > M:
            chunks.append(curc); curc, acc = [], 0
        curc.append(e); acc += e[2]
    chunks.append(curc)
    return chunks

def data_text(t, V, top, chunks):
    out = []
    for i, ch in enumerate(chunks):
        out.append('/-- chunk %d (%d leaves) -/\nnoncomputable def x%d : List ExtEntry := [\n  %s]\n\n'
                   % (i, sum(e[2] for e in ch), i, ',\n  '.join(ext_lit(e) for e in ch)))
    out.append(('set_option maxRecDepth 100000 in\n' if len(chunks) > 3600 else '') +
               '/-- the chunks -/\nnoncomputable def xs : List (List ExtEntry) := [%s]\n\n' % ', '.join('x%d' % i for i in range(len(chunks))))
    out.append('/-- the top tree (external nodes: code 15) -/\nnoncomputable def ctop : Nat := %s\n\n'
               '/-- the value of the box -/\nnoncomputable def V : Int := %d\n\n' % (top, V))
    out.append('set_option maxRecDepth 100000 in\ntheorem top : cutOK %d (%s %d) ctop (initBox %d %s %d).1 (initBox %d %s %d).2 xs.flatten V = true := by\n'
               '  decide +kernel\n\n' % (k, LEAF, k, k, RC, t, k, RC, t))
    return ''.join(out)

def glue_text(t, V, nchunks):
    return ('set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n'
            'theorem subAll : ∀ i < xs.length, subOK %d (%s %d) (xs.getD i []) = true := by\n'
            '  intro i hi\n  have hl : xs.length = %d := rfl\n  rw [hl] at hi\n' % (k, LEAF, k, nchunks)
            + tree(nchunks, lambda a: 'exact s%d' % a)
            + '\ntheorem rb (hL : LeafSoundProp %d (%s %d)) : RangeBound %d %s %d %d %d :=\n'
              '  rangeBound_of_cut hL top (extOK_of_chunks xs subAll)\n\n' % (k, LEAF, k, k, RC, t, t + 1, V))

mods, pieces, units = [], [], []     # units: (module, estimated leaves) for the partitioner
modof = {}                           # box -> glue module
for t in sorted(boxes):
    V, top, exts = boxes[t]
    chunks = chunks_of(exts)
    leaves = sum(e[2] for e in exts)
    bns = '%s.B%07d' % (NS, t)
    if leaves <= args.comb:
        # core module (data, top, chunk theorems; no Mathlib) built by the fleet; glue module built at assembly
        body = ['/- track K sub-box checks, k = 5, initial box %d: %d leaves, %d chunks (generated by tools/gen_kcut5.py) -/\n'
                % (t, leaves, len(chunks)),
                'import BHHCert.TreeCut\nimport %s\n\nset_option Elab.async false\n\nnamespace %s\n\n'
                'open BHH.Cert\n\n' % (SHARD, bns), data_text(t, V, top, chunks)]
        for i in range(len(chunks)):
            body.append('theorem s%d : subOK %d (%s %d) (xs.getD %d []) = true := by\n  decide +kernel\n\n' % (i, k, LEAF, k, i))
        body.append('end %s\n' % bns)
        write(os.path.join(DIR, 'C', 'B%07d.lean' % t), ''.join(body))
        write(os.path.join(DIR, 'G', 'B%07d.lean' % t),
              '/- track K sub-box glue, k = 5, initial box %d (generated by tools/gen_kcut5.py) -/\n' % t
              + 'import %s.C.B%07d\nimport BHH.MainK\n\nnamespace %s\n\nopen BHH.Cert BHH.KC\n\n' % (NS, t, bns)
              + glue_text(t, V, len(chunks)) + 'end %s\n' % bns)
        units.append(('%s.C.B%07d' % (NS, t), leaves))
        mods.append('%s.G.B%07d' % (NS, t)); modof[t] = mods[-1]
        pieces.append((t, t + 1, '(%s.rb hL)' % bns, V))
    else:
        bdir = os.path.join(DIR, 'B%07d' % t)
        write(os.path.join(bdir, 'Data.lean'),
              '/- track K sub-box data, k = 5, initial box %d: %d external entries in %d chunks (generated by tools/gen_kcut5.py) -/\n'
              'import BHHCert.TreeCut\nimport %s\n\nset_option Elab.async false\n\nnamespace %s\n\nopen BHH.Cert\n\n%send %s\n'
              % (t, len(exts), len(chunks), SHARD, bns, data_text(t, V, top, chunks), bns))
        smods, j, i = [], 0, 0
        while i < len(chunks):
            lv, body = 0, []
            while i < len(chunks) and (not body or lv + sum(e[2] for e in chunks[i]) <= args.mod_leaves):
                lv += sum(e[2] for e in chunks[i])
                body.append('theorem s%d : subOK %d (%s %d) (xs.getD %d []) = true := by\n  decide +kernel\n\n' % (i, k, LEAF, k, i))
                i += 1
            write(os.path.join(bdir, 'S%03d.lean' % j),
                  '/- track K sub-box checks, k = 5, initial box %d (generated by tools/gen_kcut5.py) -/\n'
                  'import %s.Data\n\nset_option Elab.async false\n\nnamespace %s\n\nopen BHH.Cert\n\n%send %s\n'
                  % (t, bns, bns, ''.join(body), bns))
            smods.append('%s.S%03d' % (bns, j)); units.append(('%s.S%03d' % (bns, j), lv)); j += 1
        write(os.path.join(bdir, 'Box.lean'),
              '/- track K sub-box glue, k = 5, initial box %d (generated by tools/gen_kcut5.py) -/\n' % t
              + ''.join('import %s\n' % m for m in smods)
              + 'import BHH.MainK\n\nnamespace %s\n\nopen BHH.Cert BHH.KC\n\n' % bns + glue_text(t, V, len(chunks)) + 'end %s\n' % bns)
        mods.append('%s.Box' % bns); modof[t] = mods[-1]
        pieces.append((t, t + 1, '(%s.rb hL)' % bns, V))
if not args.asm_only:
    os.makedirs(args.out, exist_ok=True)
    with open(os.path.join(args.out, 'pieces_k5.txt'), 'w') as f:
        for t in sorted(modof):
            f.write('%d %d %s\n' % (t, boxes[t][0], modof[t]))
if args.no_asm:
    with open(os.path.join(args.out, 'units_k5.txt'), 'w') as f:
        for m, lv in units:
            f.write('%s %d\n' % (m, lv))
    print('boxes', len(boxes), 'units', len(units), 'leaves', sum(lv for _, lv in units))
    raise SystemExit(0)
if args.asm_only:
    for fn in args.pieces:
        for line in open(fn):
            t, V, m = line.split(); t = int(t); V = int(V)
            assert t not in modof, t
            modof[t] = m; mods.append(m)
            bns = m[:-len('.Box')] if m.endswith('.Box') else m.replace('.G.B', '.B')
            pieces.append((t, t + 1, '(%s.rb hL)' % bns, V))
    pieces.sort()
# zero gaps
full, prev = [], 0
for p in pieces:
    if p[0] > prev:
        full.append((prev, p[0], '(RangeBound.zero %d %s %d %d)' % (k, RC, prev, p[0]), 0))
    full.append(p); prev = p[1]
if prev < NB:
    full.append((prev, NB, '(RangeBound.zero %d %s %d %d)' % (k, RC, prev, NB), 0))
# parts
parts = [full[i:i + args.part] for i in range(0, len(full), args.part)]
pnames = []
for n, part in enumerate(parts):
    a, b = part[0][0], part[-1][1]
    S = sum(p[3] for p in part)
    used = sorted(set(modof[p[0]] for p in part if p[0] in modof and p[2].startswith('(%s.B' % NS)))
    write(os.path.join(DIR, 'AsmP%03d.lean' % n),
          '/- track K, k = 5: initial boxes [%d, %d) (generated by tools/gen_kcut5.py) -/\n' % (a, b)
          + ''.join('import %s\n' % m for m in used)
          + 'import BHH.MainK\nimport %s\n\nnamespace %s.P%03d\n\nopen BHH.Cert BHH.KC\n\n' % (SHARD, NS, n)
          + 'theorem part (hL : LeafSoundProp %d (%s %d)) : RangeBound %d %s %d %d %d := by\n'
            '  have h := %s\n  exact h.mono (by norm_num)\n\nend %s.P%03d\n' % (k, LEAF, k, k, RC, a, b, S, range_tree(part, '    '), NS, n))
    pnames.append((a, b, '(%s.P%03d.part hL)' % (NS, n), S, '%s.AsmP%03d' % (NS, n)))
S = sum(p[3] for p in pnames)
write(os.path.join(DIR, 'Asm.lean'),
      '/- track K, k = 5: all %d initial boxes (generated by tools/gen_kcut5.py) -/\n' % NB
      + ''.join('import %s\n' % p[4] for p in pnames)
      + 'import BHH.MainK\n\nnamespace %s\n\nopen BHH.Cert BHH.KC\n\n/-- the sum over all initial boxes -/\ndef S : Int := %d\n\n' % (NS, S)
      + 'theorem range (hL : LeafSoundProp %d (%s %d)) : RangeBound %d %s 0 (2 ^ %s) S := by\n'
        '  have h := %s\n  exact h.mono (by norm_num [S])\n\nend %s\n' % (k, LEAF, k, k, RC, RC, range_tree(pnames, '    '), NS))
if not args.asm_only:
    with open(os.path.join(args.out, 'units_k5.txt'), 'w') as f:
        for m, lv in units:
            f.write('%s %d\n' % (m, lv))
print('boxes', len(boxes), 'combined', sum(1 for m in mods if '.C.B' in m), 'big', sum(1 for m in mods if m.endswith('.Box')),
      'units', len(units), 'pieces', len(full), 'parts', len(parts), 'S =', S)
