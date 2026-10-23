"""Canonical C5 cut data: parse kcut3t outputs in the given order exactly as tools/gen_kcut5.py does (a later record of
a box replaces an earlier one) and write one record per box, in box order.  usage: canon_kc5.py OUT INPUT..."""
import sys
recs, cur = {}, None
for fn in sys.argv[2:]:
    for line in open(fn):
        f = line.split()
        if not f: continue
        if f[0] == 'WHOLE':
            recs[int(f[2])] = [line]
        elif f[0] == 'BOX':
            cur = int(f[2]); recs[cur] = [line]
        elif f[0] in ('TOP', 'EXT'):
            recs[cur].append(line)
with open(sys.argv[1], 'w') as out:
    for t in sorted(recs):
        out.writelines(recs[t])
print('boxes', len(recs))
