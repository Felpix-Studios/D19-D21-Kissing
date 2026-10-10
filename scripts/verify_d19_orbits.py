#!/usr/bin/env python3
"""Exact orbit-reduced check of the 12276-point D19 configuration, Python integers only.

Usage: python3 scripts/verify_d19_orbits.py data/D19_12276_certificate.json [--check-exports data/D19_12276_rays.txt]

No NumPy, optimizer or floating point. The code E (Ho's twelve generators with
coordinate 20), the octads, the 10668-point section and the 192 points on the
four octads containing T are rebuilt from the generators. The JSON supplies the
eight restored points, the generators of the sign group G and the 14
representatives, all in the paper's coordinates (T = {1,4,7,9}).

Checks:
  * the restored points are the eight deleted points on the octad T u {3,6,8,19}
    with v_T = (1,1,-1,-1), that is, with tail 2 f_1;
  * G has order 128, lies in E, vanishes on T, contains no tetrad, maps the base
    (10484 points) onto itself and the restored points onto themselves; all its
    orbits on the 192 deleted points have size 8, and the restored points are one orbit;
  * every new point has the sign word of a kept word of the 12268 construction
    (head signs, and the tail pattern nearest to its tail);
  * every product <r_i, b>, b in the base (14 x 10484), and every product
    <r_i, S_g r_j>, i <= j, excluding i = j and g = 0 (128 C(14,2) + 127 14 = 13426),
    satisfies cos <= 1/2 - 1/L, L = 50000 (the JSON's auxiliary_margin 24999/50000);
  * each of the 184 points still deleted has cosine above 1/2 with some new point.
With --check-exports, the ray file must equal the 12276 built rays as a multiset.
"""
from __future__ import annotations
import argparse, collections, itertools, json, math, time
from pathlib import Path

GEN = ((1,8,9,12,16,17,18,19),(2,10,11,14,15,17,18,20),(3,7,9,13,15,16,17,19),
       (4,7,8,10,12,15,16,19),(5,10,12,13,15,16,17,18),(6,7,8,9,10,13,16,18),
       (1,4,7,9),(1,5,6,18,20),(1,3,12,15,20),(1,10,13,19,20),
       (1,3,5,6,7,13,14,15,18,20),(2,4,6,7,8,13,14,16,17,18))
T = (1, 4, 7, 9)
H = tuple(j for j in range(1, 21) if j not in T)
FIXED = (3, 6, 8, 19)


def mask(s):
    return sum(1 << (j - 1) for j in s)


def span(gens):
    out = [0]
    for g in gens:
        out += [w ^ g for w in out]
    assert len(out) == len(set(out)), 'dependent generators'
    return out


def native(v):
    """(v_H, R v_T / 2) for v in R^20 with v_T summing to 0."""
    t = [v[j - 1] for j in T]
    assert sum(t) == 0
    z = (t[0]+t[1]-t[2]-t[3], t[0]-t[1]+t[2]-t[3], t[0]-t[1]-t[2]+t[3])
    assert all(a % 2 == 0 for a in z)
    return tuple([v[j - 1] for j in H] + [a // 2 for a in z])


def flip(g, y):
    """Change the signs of the paper coordinates in the 20-bit word g (all in H)."""
    return tuple(-a if k < 16 and g >> (H[k] - 1) & 1 else a for k, a in enumerate(y))


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def build(data):
    E = span([mask(g) for g in GEN])
    assert len(E) == 4096 and min(w.bit_count() for w in E if w) == 4
    octads = [w for w in range(1 << 20) if w.bit_count() == 8
              and all((w & mask(g)).bit_count() % 2 == 0 for g in GEN)]
    assert len(octads) == 130
    assert all((a & b).bit_count() <= 4 for a, b in itertools.combinations(octads, 2))
    Tm = mask(T)
    roots, fibers = [], {}
    for i, j in itertools.combinations(range(20), 2):
        for a, b in itertools.product((-2, 2), repeat=2):
            v = [0] * 20; v[i] = a; v[j] = b
            if sum(v[k - 1] for k in T) == 0:
                roots.append(native(v))
    for o in octads:
        pos = [j for j in range(20) if o >> j & 1]
        pts = []
        for m in range(256):
            if m.bit_count() % 2 == 0:
                continue
            v = [0] * 20
            for k, p in enumerate(pos):
                v[p] = -1 if m >> k & 1 else 1
            if sum(v[k - 1] for k in T) == 0:
                pts.append(native(v))
        fibers[o] = pts
    assert len(roots) == 492 and sum(map(len, fibers.values())) == 10176
    full = [o for o in octads if o & Tm == Tm]
    assert len(full) == 4 and all(len(fibers[o]) == 48 for o in full)
    core = roots + [p for o in octads if o not in full for p in fibers[o]]
    assert len(core) == 10476
    deleted = {p: o for o in full for p in fibers[o]}
    restored = [tuple(map(int, r)) for r in data['restored_base_points']]
    assert len(restored) == 8
    fixed_octad = Tm | mask(FIXED)
    assert fixed_octad in full
    for r in restored:
        assert len(r) == 20 and all(a in (-1, 0, 1) for a in r)
        assert native(r) in deleted and deleted[native(r)] == fixed_octad
    restored = [native(r) for r in restored]
    assert len(set(restored)) == 8
    assert set(restored) == {p for p, o in deleted.items() if o == fixed_octad and p[16:] == (2, 0, 0)}
    assert [list(r) for r in restored] == data['restored_base_points_native19']
    base = core + restored
    assert len(set(base)) == 10484
    gens = [mask(g) for g in data['group_generators']]
    G = span(gens)
    Eset = set(E)
    assert len(G) == 128 and all(g in Eset and g & Tm == 0 and g.bit_count() != 4 for g in G)
    bset = set(base)
    assert all(flip(g, b) in bset for g in G for b in base)
    assert {flip(g, restored[0]) for g in G} == set(restored)
    still = [p for p in deleted if p not in set(restored)]
    assert len(still) == 184
    orbit_sizes = collections.Counter()
    seen = set()
    for p in still:
        if p in seen:
            continue
        orb = {flip(g, p) for g in G}
        seen |= orb
        orbit_sizes[(deleted[p] == fixed_octad, len(orb))] += 1
    assert set(s for _, s in orbit_sizes) == {8}
    reps = [tuple(map(int, r)) for r in data['representatives']]
    assert len(reps) == 14 and all(len(r) == 19 for r in reps)
    assert all(type(a) is int for r in data['representatives'] for a in r)
    new = [flip(g, r) for r in reps for g in G]
    # sign words: the kept words of the 12268 construction
    W = span([w for w in E if w.bit_count() == 4])
    kept = {c for c in E if 1 <= (c & Tm).bit_count() <= 3
            and (c ^ min(c ^ s for s in W)).bit_count() % 8 == 0}
    assert len(kept) == 1792
    R = ((1, 1, -1, -1), (1, -1, 1, -1), (1, -1, -1, 1))
    pats = {}
    for m in range(16):
        if 1 <= m.bit_count() <= 3:
            q = [-1 if m >> b & 1 else 1 for b in range(4)]
            t0 = tuple(sum(R[a][b] * q[b] for b in range(4)) // 2 for a in range(3))
            pats[m] = t0
    def word(y):
        # nearest tail pattern: maximize <t0, t>/|t0|, compared exactly (|t0|^2 is 3 or 4)
        best = None
        for m, t0 in pats.items():
            d = dot(t0, y[16:])
            key = (1 if d > 0 else -1) * d * d * (12 // dot(t0, t0))   # sign(d) * 12 cos^2 |t|^2
            if best is None or key > best[0]:
                best = (key, m)
        m = best[1]
        return sum(1 << (H[k] - 1) for k in range(16) if y[k] < 0) | sum(1 << (T[b] - 1) for b in range(4) if m >> b & 1)
    words = [word(y) for y in new]
    assert set(words) == kept and len(words) == 1792
    return dict(base=base, core=core, restored=restored, G=G, gens=gens, reps=reps, new=new,
                still=still, orbit_sizes=orbit_sizes, words=words, Tm=Tm)


def verify(path, exports=None):
    begin = time.time()
    data = json.loads(Path(path).read_text())
    assert int(data['dimension']) == 19
    b = build(data)
    base, reps, G = b['base'], b['reps'], b['G']
    num, den = data['auxiliary_margin']['numerator'], data['auxiliary_margin']['denominator']
    assert 2 * num == den - 2, 'margin is 1/2 - 1/L with L = denominator'
    L = den
    norms = [dot(r, r) for r in reps]
    assert all(n > 0 for n in norms)
    weakest = {}
    def comparison(d, na, nb, kind, label):
        assert d <= math.isqrt(na * nb) // 2, ('kissing violation', label)
        if d > 0:
            assert (2 * L * d) ** 2 <= (L - 2) ** 2 * na * nb, ('margin violation', label)
            gap = (na * nb - 4 * d * d, 4 * na * nb)
            assert gap[0] > 0
            w = weakest.get(kind)
            if w is None or gap[0] * w[1] < w[0] * gap[1]:
                weakest[kind] = (gap[0], gap[1], label)
    nb = 0
    for i, (r, n) in enumerate(zip(reps, norms)):
        for k, x in enumerate(base):
            comparison(dot(r, x), n, 8, 'representative-base', (i, k))
            nb += 1
    no = 0
    for i, (r, na) in enumerate(zip(reps, norms)):
        for j in range(i, len(reps)):
            s = reps[j]
            prod = [a * c for a, c in zip(r, s)]
            for g in G:
                if i == j and g == 0:
                    continue
                d = sum(-v if k < 16 and g >> (H[k] - 1) & 1 else v for k, v in enumerate(prod))
                comparison(d, na, norms[j], 'representative-orbit', (i, j, g))
                no += 1
    assert nb == 14 * 10484 and no == 128 * math.comb(14, 2) + 127 * 14 == 13426
    # each point still deleted conflicts with some new point
    conflicts = 0
    for p in b['still']:
        if any(dot(p, y) > 0 and 4 * dot(p, y) ** 2 > 8 * dot(y, y) for y in b['new']):
            conflicts += 1
    assert conflicts == 184
    N = len(base) + len(b['new'])
    assert N == 12276 == int(data['population'])
    # The 492 roots of the base span R^19 (2e_i +- 2e_j for head pairs, and the tail roots).
    rejected = False
    try:
        comparison(norms[0], norms[0], norms[0], 'control', ('duplicate',))
    except AssertionError:
        rejected = True
    assert rejected
    out = {
        'verified': True, 'dimension': 19, 'population': N,
        'base': len(base), 'restored': 8, 'still_deleted': 184,
        'new_points': len(b['new']), 'representatives': len(reps), 'group_order': len(G),
        'group_generators': data['group_generators'],
        'G_orbits_on_deleted_points': {('fiber over T u {3,6,8,19}' if f else 'other fibers') + f', size {s}': c
                                       for (f, s), c in sorted(b['orbit_sizes'].items())},
        'new_point_sign_words': '1792 = the kept words of the 12268 construction',
        'representative_base_products': nb, 'representative_orbit_products': no,
        'pairs_covered': N * (N - 1) // 2, 'gap_L': L,
        'weakest_gap': {k: [v[0] // math.gcd(v[0], v[1]), v[1] // math.gcd(v[0], v[1]), str(v[2])]
                        for k, v in weakest.items()},
        'deleted_points_in_conflict': conflicts,
        'max_abs_entry': max(abs(a) for r in reps for a in r),
        'arithmetic': 'Python integers only; no floating point',
        'seconds': round(time.time() - begin, 1),
    }
    if exports:
        rows = []
        for line in open(exports):
            if line.strip():
                v = [int(t) for t in line.split()]
                assert len(v) == 20 and v[0] == dot(v[1:], v[1:])
                rows.append(tuple(v[1:]))
        assert collections.Counter(rows) == collections.Counter(base + b['new']), 'export differs'
        out['exports'] = f'{exports}: {len(rows)} rows, equal to the build as a multiset'
    print(json.dumps(out, indent=2))
    return out


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('certificate', type=Path)
    p.add_argument('--check-exports', type=Path)
    a = p.parse_args()
    verify(a.certificate, a.check_exports)
