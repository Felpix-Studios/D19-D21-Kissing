#!/usr/bin/env python3
"""Structure facts about the 12276-point D19 configuration that the paper quotes (Section 3.5).

Usage: python3 scripts/d19_structure.py data/D19_12276_certificate.json

Builds the configuration with verify_d19_orbits.build (exact), then prints:
  * the group G: order, weights, relation to the 256 words of E that miss T,
    the tetrads, and the order-16 group of the 12270 version;
  * which additions of the 12268 construction conflict with the restored points;
  * per representative: type, tail factor, spread of head entries;
  * margins: smallest 1/4 - cos^2 (exact) and pairs near 1/2, base-new and new-new;
  * contacts involving restored points; largest cosine of each still-deleted point
    with a new point.
Floating point is used only for the printed decimals and the near-1/2 counts."""
import collections, itertools, json, math, sys
from fractions import Fraction
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_d19_orbits import build, span, mask, flip, dot, T, H, FIXED

data = json.loads(Path(sys.argv[1]).read_text())
b = build(data)
base, restored, reps, G, new = b['base'], b['restored'], b['reps'], b['G'], b['new']
Tm = b['Tm']
GEN = __import__('verify_d19_orbits').GEN
E = span([mask(g) for g in GEN])
E0 = [w for w in E if w & Tm == 0]
tets = [w for w in E0 if w.bit_count() == 4]
Gs = set(G)
print('G order', len(G), 'weights', dict(sorted(collections.Counter(g.bit_count() for g in G).items())))
print('words of E missing T:', len(E0), '; tetrads in H:', [[j + 1 for j in range(20) if t >> j & 1] for t in tets],
      '; tetrads in G:', sum(t in Gs for t in tets))
basis = []
for w in E0:
    if w not in span(basis): basis.append(w)
assert len(basis) == 8
def combine(k):  # the word with coordinates k (8 bits) in this basis
    x = 0
    for i in range(8):
        if k >> i & 1: x ^= basis[i]
    return x
cmap = {combine(k): k for k in range(256)}
subs = 0; is_G = 0
for f in range(1, 256):
    ker = {w for w in E0 if bin(cmap[w] & f).count('1') % 2 == 0}
    if not any(t in ker for t in tets):
        subs += 1; is_G += ker == Gs
print('index-2 subgroups of E0 containing no tetrad:', subs, '; G among them:', is_G == 1)
Gam = set(span([mask(s) for s in [[2,5,10,11,13,15],[2,5,10,16,17,20],[2,5,12,14,15,17],[2,10,13,14,16,18]]]))
print('12270 group inside G:', Gam <= Gs)
u = mask(FIXED)
print('restrictions of G to {3,6,8,19}:', len({g & u for g in G}), '(all even subsets)')

# conflicts of the restored points with the flat additions of Section 3.2 (alpha = 7/5 axis, 9/11 diagonal)
W = span([w for w in E if w.bit_count() == 4])
kept = [c for c in E if 1 <= (c & Tm).bit_count() <= 3 and (c ^ min(c ^ s for s in W)).bit_count() % 8 == 0]
R = ((1, 1, -1, -1), (1, -1, 1, -1), (1, -1, -1, 1))
def addition(c):
    q = [-1 if c >> j & 1 else 1 for j in range(20)]
    qT = [q[j - 1] for j in T]
    t0 = [sum(R[a][k] * qT[k] for k in range(4)) // 2 for a in range(3)]
    al = Fraction(7, 5) if (c & Tm).bit_count() == 2 else Fraction(9, 11)
    return [q[j - 1] for j in H] + [al * x for x in t0], t0
conf = collections.Counter()
for c in kept:
    a, t0 = addition(c)
    na = sum(x * x for x in a)
    k = sum(1 for r in restored if dot(a, r) > 0 and 4 * dot(a, r) ** 2 > na * 8)
    if k: conf[(tuple(t0), k)] += 1
print('flat additions conflicting with restored points (tail, number of restored points hit): count', dict(conf))

# representatives
Hidx = {j: k for k, j in enumerate(H)}
uk = [Hidx[j] for j in FIXED]
print('representatives (paper numbering):')
for i, r in enumerate(reps, 1):
    head, tail = r[:16], r[16:]
    rms = math.sqrt(sum(x * x for x in head) / 16)
    t2 = sum(x * x for x in tail)
    kind = 'axis' if max(abs(x) for x in tail) > 2 * sorted(abs(x) for x in tail)[1] + 1000 else 'diagonal'
    t0n = 2 if kind == 'axis' else math.sqrt(3)
    fac = math.sqrt(t2) / t0n / rms
    ha = [abs(x) for x in head]
    onu = [ha[k] for k in uk]; off = [ha[k] for k in range(16) if k not in uk]
    print(f'  r{i}: {kind:8s} tail {tail} factor {fac:.4f} head |entries| {min(ha)}..{max(ha)} '
          f'(ratio {max(ha)/min(ha):.4f}); on 3,6,8,19 mean {sum(onu)/4:.1f}, elsewhere {sum(off)/12:.1f}; norm {dot(r, r)}')

# margins
def gap(d, n1, n2):
    return Fraction(n1 * n2 - 4 * d * d, 4 * n1 * n2)
best = {}; near = collections.Counter()
def note(kind, d, n1, n2):
    if d <= 0: return
    g = gap(d, n1, n2)
    if kind not in best or g < best[kind][0]: best[kind] = (g, d / math.sqrt(n1 * n2))
    c = d / math.sqrt(n1 * n2)
    for e in (1e-5, 1e-4):
        if c > 0.5 - e: near[(kind, e)] += 1
norms = [dot(r, r) for r in reps]
# full counts over the configuration via orbits: base-new = sum over reps of base products (G preserves base);
# new-new pairs: product <S_g r_i, S_h r_j> = <r_i, S_{g+h} r_j>; each (i,j,g) with i<j stands for 128 pairs,
# each (i,i,g), g != 0, for 64 pairs.
for i, r in enumerate(reps):
    for x in base:
        d = dot(r, x)
        if d > 0:
            note('base-new', d, norms[i], 8)
            c = d / math.sqrt(norms[i] * 8)
            for e in (1e-5, 1e-4):
                if c > 0.5 - e: near[('base-new x128', e)] += 127
for i in range(14):
    for j in range(i, 14):
        for g in G:
            if i == j and g == 0: continue
            d = dot(reps[i], flip(g, reps[j]))
            mult = 128 if i < j else 64
            if d > 0:
                g_ = gap(d, norms[i], norms[j])
                if 'new-new' not in best or g_ < best['new-new'][0]: best['new-new'] = (g_, d / math.sqrt(norms[i] * norms[j]), (i + 1, j + 1, g, d, norms[i]))
                c = d / math.sqrt(norms[i] * norms[j])
                for e in (1e-5, 1e-4):
                    if c > 0.5 - e: near[('new-new', e)] += mult
for k, v in best.items():
    print(f'smallest 1/4 - cos^2, {k}: {v[0]} = {float(v[0]):.4g}, cos {v[1]:.10f}', v[2:] if len(v) > 2 else '')
bn = {e: near[('base-new', e)] + near[('base-new x128', e)] for e in (1e-5, 1e-4)}
print('pairs with cos within eps of 1/2: base-new', bn, 'new-new', {e: near[('new-new', e)] for e in (1e-5, 1e-4)})

# contacts
cont_r = sum(1 for r in restored for x in base if x != r and dot(r, x) == 4)
cont_rr = sum(1 for r, s in itertools.combinations(restored, 2) if dot(r, s) == 4)
print('contacts involving a restored point:', cont_r - cont_rr, '(among restored pairs:', cont_rr, ')')
print('inner products among the eight restored points:', sorted(collections.Counter(dot(r, s) for r, s in itertools.combinations(restored, 2)).items()))
# still-deleted points
fixed_octad = Tm | u
mx = collections.defaultdict(list)
for p in b['still']:
    tail = p[16:]
    m = max(dot(p, y) / math.sqrt(8 * dot(y, y)) for y in new)
    on_fixed = all(p[Hidx[j]] != 0 for j in FIXED)
    mx['fiber over T u {3,6,8,19}' if on_fixed else 'other fibers'].append(m)
for k, v in mx.items():
    print(f'still deleted, {k}: {len(v)} points, largest cosine with a new point {min(v):.4f} to {max(v):.4f}')
# a tetrad u in H with S_u in the group would pair x with S_u x: cosine 1 - 2 s/|x|^2, s = mass of x on u
worst = max(sum(r[Hidx[j]] ** 2 for j in range(1, 21) if t >> (j - 1) & 1) / dot(r, r) for r in reps for t in tets)
print(f'largest share of |r_i|^2 on a tetrad of H: {worst:.4f} (cosine of r_i with S_u r_i at least {1 - 2 * worst:.4f})')
