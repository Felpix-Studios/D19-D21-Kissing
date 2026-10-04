"""Structural facts about the 30779-point configuration quoted in the paper.
Reads data/D21_30779_certificate.json only. Exact integer arithmetic except
where a float summary is printed."""
import json
from pathlib import Path
d = json.load(open(Path(__file__).resolve().parent.parent / 'data/D21_30779_certificate.json'))
reps = [tuple(r) for r in d['representatives']]
A = reps[:192]                      # half A; the JSON's other 192 are its w-images
w = 14723
pc = lambda x: bin(x).count('1')
flip = lambda r, g: tuple(-v if (g >> j) & 1 else v for j, v in enumerate(r))
assert reps[192:] == [flip(r, w) for r in A]
# Golay
gens = []
for j in range(12):
    x = sum(1 << (e + j) for e in [0, 1, 5, 6, 7, 9, 11])
    if pc(x) % 2: x |= 1 << 23
    gens.append(x)
G = {0}
for g in gens: G |= {x ^ g for x in G}
assert len(G) == 4096
M21 = (1 << 21) - 1
D = {x & M21 for x in G}            # punctured to 21 coordinates
print('|D| =', len(D), 'min wt', min(pc(x) for x in D if x))
O = [x for x in G if pc(x) == 8 and x >> 21 == 0]
print('octads', len(O))
T = sum(1 << (i - 1) for i in [3, 6, 10, 11, 16, 18, 20, 21])
print('T is an octad:', T in O)
lines = [x for x in D if pc(x) == 5]
print('lines', len(lines))
H = {0}
for g in d['generators']: H |= {x ^ g for x in H}
K = H | {h ^ w for h in H}
print('|H| =', len(H), '|K| =', len(K), 'w weight', pc(w), 'support', [j + 1 for j in range(21) if w >> j & 1])
print('w in D:', w in D, 'w zero on T:', w & T == 0, 'K even on every octad:', all(pc(k & o) % 2 == 0 for k in K for o in O),
      'K zero on T:', all(k & T == 0 for k in K))

print('\n--- the [21,9,6] code C ---')
Cg = [1559917, 15163, 774651, 1540761, 485602, 408336, 678478, 1748752, 1231514]
C = {0}
for g in Cg: C |= {x ^ g for x in C}
print('|C| =', len(C), 'min wt', min(pc(x) for x in C if x), 'all even:', all(pc(x) % 2 == 0 for x in C),
      'C in D:', C <= D, 'H in C:', H <= C, 'w in C:', w in C)
coset = lambda s: min(s ^ c for c in C)
allc = sorted({coset(x) for x in D})
print('cosets of C in D:', [(c, 'odd' if pc(c) % 2 else 'even', sum(1 for l in lines if coset(l) == c), 'lines') for c in allc])
print('w swaps the cosets:', {c: coset(c ^ w) for c in allc})

print('\n--- sign words of the new points ---')
sw = lambda r: sum(1 << k for k in range(21) if r[k] < 0)
SA = {sw(r) ^ h for r in A for h in H}
SK = {sw(r) ^ k for r in A for k in K}
print('half A:', len(SA), 'distinct sign words, all in D:', SA <= D)
print('all:', len(SK), 'distinct sign words')
from collections import Counter
print('half A per coset of C:', sorted(Counter(coset(s) for s in SA).items()))
print('all per coset of C:', sorted(Counter(coset(s) for s in SK).items()))
first = {}
for i, r in enumerate(A):
    first.setdefault(coset(sw(r)), i + 1)
print('first representative (1-based, JSON order) on each coset:', first)

print('\n--- weights ---')
ent = [abs(v) for r in A for v in r]
nr = [sum(v * v for v in r) for r in A]
print('entries', min(ent), max(ent), 'zero entries', sum(v == 0 for r in A for v in r), 'norms', min(nr), max(nr))
linemodel = {1993: [8, 15, 16, 18, 19], 2139: [1, 3, 5, 17, 18], 3370: [4, 5, 6, 8, 10]}
for c in [696, 1993, 2787, 1393, 2139, 3370]:
    rs = [r for r in A if coset(sw(r)) == c]
    rat = [[abs(x) / (sum(y * y for y in r) / 21) ** .5 for x in r] for r in rs]
    msg = f'coset {c}: {len(rs)} reps, entries/rms in [{min(min(q) for q in rat):.3f}, {max(max(q) for q in rat):.3f}]'
    if c in linemodel:
        L = set(linemodel[c]); dev = 0
        for r in rs:
            sc = (18 / sum(y * y for y in r)) ** .5
            for j, x in enumerate(r):
                dev = max(dev, abs(abs(x) * sc - ((2 / 5) ** .5 if j + 1 in L else 1.0)))
        msg += f'; line {sorted(L)} (a line of D: {sum(1 << (j - 1) for j in L) in lines}), max deviation from the line model at |lambda|^2 = 18: {dev:.2e}'
    print(msg)
