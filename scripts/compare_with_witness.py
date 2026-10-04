"""Check that the rays built in Lean (lean/out/lean_rays_d*.txt, written by
`lake exe dumprays`) give the same set of directions as the witness files.
Each ray is reduced to its primitive integer vector (divide by the gcd)."""
import sys
from math import gcd
from functools import reduce
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent

def prim(v):
    g = reduce(gcd, (abs(a) for a in v))
    return tuple(a // g for a in v)

def load(path, skip_norm=False):
    rows = []
    for line in open(path):
        if not line.strip() or line.startswith('#'):
            continue
        v = [int(t) for t in line.split()]
        rows.append(v[1:] if skip_norm else v)
    return rows

ok = True
for name, lean, wit, skip, n in [
    ('D19', 'lean/out/lean_rays_d19.txt', 'data/D19_12268_rays.txt', True, 12268),
    ('D21', 'lean/out/lean_rays_d21.txt', 'data/D21_30779_rays.txt', True, 30779),
]:
    a = load(HERE / lean)
    b = load(HERE / wit, skip)
    sa, sb = {prim(v) for v in a}, {prim(v) for v in b}
    same = len(a) == len(b) == len(sa) == len(sb) == n and sa == sb
    ok &= same
    print(f'{name}: lean {len(a)} rays ({len(sa)} directions), witness {len(b)} ({len(sb)}), equal: {same}')
print('PASS' if ok else 'FAIL')
sys.exit(0 if ok else 1)
