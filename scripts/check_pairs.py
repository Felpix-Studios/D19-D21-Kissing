#!/usr/bin/env python3
"""Exact all-pairs checker for integer-ray kissing configurations with large norms.

Input: a text file; lines starting with '#' are comments; every other line is a
squared norm followed by n integers.  Row x stands for the unit vector x/|x|.
The file passes iff
  * every data line has n+1 integer tokens and the stated norm equals the sum of squares > 0,
  * the rows give pairwise distinct directions (their primitive vectors differ),
  * n rows have a nonzero exact integer determinant (rank n),
  * every pair i<j has g <= floor(isqrt(n_i n_j)/2), where g = x_i . x_j.
The last test is exact: for integer g, 2g <= sqrt(nm) iff 2g <= isqrt(nm), so it is
the same as g <= 0 or 4g^2 <= nm, i.e. cos <= 1/2.

Overflow.  The fast path needs every stated norm < 2^62 (checked; larger norms stop the
run).  Then every |x_ik| < 2^31, so every product x_ik x_jk fits in int64.  G is summed
in int64 one coordinate at a time, so after k steps each entry is the dot product over
coordinates 1..k, and by Cauchy-Schwarz its absolute value is at most sqrt(n_i n_j) < 2^62.
No int64 overflow can happen.  The thresholds floor(isqrt(n_a n_b)/2) < 2^61 are computed
per pair of norm classes with Python integers and stored in int64.  Nothing is squared in
int64.  Cross-checks with Python integers: a random sample of pairs, every pair the float
screen marks as near 1/2 (cos > 0.49), sampled contacts, and every violation.

Also reported (pairs with at least one row whose norm is not --base-norm, "new" pairs):
  * the exact bound cos <= 1/2 - 1/L, tested as g <= floor(isqrt((L-2)^2 n m)/(2L));
  * the exact smallest gap (nm - 4g^2)/(4nm), overall and per pair type; a float screen
    picks every new pair and every base-base non-contact with gap < 1e-5 (float error
    < 1e-12), and the gap of every picked pair is computed exactly;
  * the exact number of pairs of each type with 0 < 1/2 - cos < 1e-6.

Usage: python3 scripts/check_pairs.py RAYS [--n 21] [--expect-rows N] [--expect-gap-L] [--json OUT]
Exit 0 and last line 'CHECK PASS' only if everything passes.
"""
import argparse
import hashlib
import json
import random
import re
import sys
import time
from fractions import Fraction
from math import gcd, isqrt

import numpy as np

INT = re.compile(r"^-?[0-9]+$")
FAST_LIMIT = 1 << 62


def die(msg):
    print("CHECK FAIL: " + msg)
    sys.exit(1)


def read_rays(path, n):
    norms, rows = [], []
    with open(path, "r", encoding="ascii") as fh:
        for ln, line in enumerate(fh, 1):
            if line.startswith("#"):
                continue
            tok = line.split()
            if len(tok) != n + 1:
                die(f"line {ln}: {len(tok)} tokens, expected {n + 1}")
            for t in tok:
                if not INT.match(t):
                    die(f"line {ln}: token {t!r} is not an integer")
            vals = [int(t) for t in tok]
            nn, x = vals[0], vals[1:]
            ss = sum(v * v for v in x)
            if nn != ss:
                die(f"line {ln}: stated norm {nn} != sum of squares {ss}")
            if nn <= 0:
                die(f"line {ln}: zero vector")
            norms.append(nn)
            rows.append(tuple(x))
    if not rows:
        die("no data rows")
    return norms, rows


def primitive(x):
    g = 0
    for v in x:
        g = gcd(g, v)
    return tuple(v // g for v in x)


def rank_rows(rows, n, p=(1 << 61) - 1):
    """Greedy elimination mod the prime p: indices of the first rows independent mod p.
    Only a candidate; the caller proves rank n by an exact nonzero determinant."""
    basis, picked = [], []
    for idx, x in enumerate(rows):
        v = [a % p for a in x]
        for b, piv in basis:
            if v[piv]:
                f = v[piv] * pow(b[piv], -1, p) % p
                v = [(a - f * c) % p for a, c in zip(v, b)]
        nz = [k for k in range(n) if v[k]]
        if nz:
            basis.append((v, nz[0]))
            picked.append(idx)
            if len(picked) == n:
                break
    return picked


def det_int(M):
    """Exact determinant of a square integer matrix by Bareiss elimination."""
    A = [list(r) for r in M]
    m, sign, prev = len(A), 1, 1
    for k in range(m - 1):
        if A[k][k] == 0:
            for r in range(k + 1, m):
                if A[r][k]:
                    A[k], A[r] = A[r], A[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, m):
            for j in range(k + 1, m):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[m - 1][m - 1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("rays")
    ap.add_argument("--n", type=int, default=21)
    ap.add_argument("--expect-rows", type=int, default=None)
    ap.add_argument("--base-norm", type=int, default=8)
    ap.add_argument("--gap-L", type=int, default=200000000)
    ap.add_argument("--expect-gap-L", action="store_true",
                    help="fail unless every new pair satisfies cos <= 1/2 - 1/L")
    ap.add_argument("--block", type=int, default=512)
    ap.add_argument("--sample", type=int, default=200000)
    ap.add_argument("--json", default=None)
    args = ap.parse_args()
    n, L = args.n, args.gap_L
    t0 = time.time()

    raw = open(args.rays, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    print(f"input {args.rays}\nsha256 {sha}")
    norms, rows = read_rays(args.rays, n)
    N = len(rows)
    print(f"rows {N}; every stated norm equals the sum of squares")
    if args.expect_rows is not None and N != args.expect_rows:
        die(f"{N} rows, expected {args.expect_rows}")

    # distinct directions
    first = {}
    for i, x in enumerate(rows):
        p = primitive(x)
        if p in first:
            die(f"repeated direction: data rows {first[p]} and {i} (0-based)")
        first[p] = i
    print(f"distinct directions {N}")

    # exact rank witness
    picked = rank_rows(rows, n)
    if len(picked) < n:
        die(f"rank {len(picked)} < {n} (mod 2^61-1; rank {n} not proved)")
    det = det_int([rows[i] for i in picked])
    if det == 0:
        die("rank witness has zero determinant")
    print(f"rank {n}: data rows {picked} have exact determinant {det}")

    # fast-path preconditions
    maxnorm = max(norms)
    if maxnorm >= FAST_LIMIT:
        die(f"max norm {maxnorm} >= 2^62: outside the proved-safe int64 path")
    X = np.array(rows, dtype=np.int64)
    if X.shape != (N, n) or X.tolist() != [list(r) for r in rows]:
        die("int64 copy of the rows differs from the parsed integers")
    classes = sorted(set(norms))
    cid = {v: k for k, v in enumerate(classes)}
    C = np.array([cid[v] for v in norms], dtype=np.int64)
    K = len(classes)
    thr = np.empty((K, K), dtype=np.int64)       # floor(isqrt(n m)/2): pass iff g <= thr
    con = np.empty((K, K), dtype=np.int64)       # g = con > 0 iff 4 g^2 = n m (contact)
    thrL = np.empty((K, K), dtype=np.int64)      # pass iff cos <= 1/2 - 1/L
    for a, na in enumerate(classes):
        for b, nb in enumerate(classes):
            nm = na * nb
            s = isqrt(nm)
            t = s // 2
            tl = isqrt((L - 2) ** 2 * nm) // (2 * L)
            assert 0 <= tl <= t < FAST_LIMIT
            thr[a, b] = t
            con[a, b] = s // 2 if (s * s == nm and s % 2 == 0) else -1
            thrL[a, b] = tl
    isnew = np.array([v != args.base_norm for v in norms])
    nrm = np.array(norms, dtype=np.int64)
    nrmf = np.array([float(v) for v in norms])
    print(f"norm classes {K}; max norm {maxnorm} (< 2^62); new rows (norm != {args.base_norm}) {int(isnew.sum())}")

    # random pairs for the Python-integer recheck, grouped by block of the first index
    rng = random.Random(20260929)
    sample = sorted({tuple(sorted(rng.sample(range(N), 2))) for _ in range(args.sample)}) if N > 1 else []
    by_block = {}
    for i, j in sample:
        by_block.setdefault(i // args.block, []).append((i, j))

    names = ["base-base", "base-new", "new-new"]
    stats = {k: {"pairs": 0, "violations": 0, "contacts": 0, "gapL_fail": 0, "within_1e-6": 0} for k in names}
    fast_seen = {}          # (i, j) -> (g, verdict) for every pair to recheck
    near = []               # pairs picked by the float screen: (i, j, g, type)
    viol_list = []
    best_noncontact = {}    # type -> (cos^2 float, i, j)
    D6 = 10 ** 6
    pairs_total = 0
    for i0 in range(0, N, args.block):
        i1 = min(N, i0 + args.block)
        m = i1 - i0
        cols = N - i0
        G = np.zeros((m, cols), dtype=np.int64)
        tmp = np.empty((m, cols), dtype=np.int64)
        Xi, Xj = X[i0:i1], X[i0:]
        for k in range(n):                        # partial sums over coordinates 1..k
            np.multiply(Xi[:, k:k + 1], Xj[None, :, k], out=tmp)
            G += tmp
        if not np.array_equal(G[np.arange(m), np.arange(m)], nrm[i0:i1]):
            die("int64 Gram diagonal differs from the stated norms")
        upper = np.triu(np.ones((m, cols), dtype=bool), k=1)
        ci, cj = C[i0:i1], C[i0:]
        T = thr[ci][:, cj]
        viol = (G > T) & upper
        tight = (G == con[ci][:, cj]) & (G > 0) & upper
        nw = isnew[i0:i1][:, None] | isnew[None, i0:]
        both = isnew[i0:i1][:, None] & isnew[None, i0:]
        typ = nw.astype(np.int8) + both.astype(np.int8)          # 0 base-base, 1 base-new, 2 new-new
        violL = (G > thrL[ci][:, cj]) & upper & nw
        Gf = G.astype(np.float64)
        c2 = np.where(G > 0, Gf * Gf / (nrmf[i0:i1, None] * nrmf[None, i0:]), 0.0)
        pick = upper & (nw | ~tight) & (c2 > 0.25 - 1e-5)     # new pairs, and base-base non-contacts
        for t, key in enumerate(names):
            sel = upper & (typ == t)
            st = stats[key]
            st["pairs"] += int(sel.sum())
            st["violations"] += int((viol & sel).sum())
            st["contacts"] += int((tight & sel).sum())
            st["gapL_fail"] += int((violL & sel).sum())
            loose = np.where(sel & ~tight & ~viol, c2, -1.0)
            if loose.size:
                a, b = np.unravel_index(np.argmax(loose), loose.shape)
                if loose[a, b] > best_noncontact.get(key, (-1.0,))[0]:
                    best_noncontact[key] = (float(loose[a, b]), i0 + int(a), i0 + int(b))
        pairs_total += int(upper.sum())
        for a, b in np.argwhere(viol):
            viol_list.append((i0 + int(a), i0 + int(b)))
        for a, b in np.argwhere(pick):
            near.append((i0 + int(a), i0 + int(b), int(G[a, b]), int(typ[a, b])))

        def verdict(a, b):
            return "viol" if viol[a, b] else ("contact" if tight[a, b] else "ok")

        for i, j in by_block.get(i0 // args.block, []):
            fast_seen[(i, j)] = (int(G[i - i0, j - i0]), verdict(i - i0, j - i0))
        for a, b in np.argwhere(pick | (upper & ~tight & (c2 > 0.2401))):
            fast_seen[(i0 + int(a), i0 + int(b))] = (int(G[a, b]), verdict(a, b))
        for a, b in np.argwhere(viol):
            fast_seen[(i0 + int(a), i0 + int(b))] = (int(G[a, b]), "viol")
        tz = np.argwhere(tight)
        if len(tz):
            for a, b in tz[np.random.default_rng(i0).integers(0, len(tz), size=min(len(tz), 50))]:
                fast_seen[(i0 + int(a), i0 + int(b))] = (int(G[a, b]), "contact")
        del G, tmp, T, Gf, c2

    expected = N * (N - 1) // 2
    if pairs_total != expected or sum(s["pairs"] for s in stats.values()) != expected:
        die(f"covered {pairs_total} pairs, expected {expected}")
    viol_total = sum(s["violations"] for s in stats.values())
    contact_total = sum(s["contacts"] for s in stats.values())
    print(f"pairs {pairs_total} (= N(N-1)/2), violations {viol_total}, contacts (cos = 1/2 exactly) {contact_total}")

    # Python-integer recheck of the fast path
    def exact(i, j):
        g = sum(a * b for a, b in zip(rows[i], rows[j]))
        lhs, rhs = 4 * g * g, norms[i] * norms[j]
        v = "ok" if g <= 0 or lhs < rhs else ("contact" if lhs == rhs else "viol")
        return g, v

    mism = 0
    classes_seen = {"ok": 0, "contact": 0, "viol": 0}
    for (i, j), (g, v) in fast_seen.items():
        ge, ve = exact(i, j)
        classes_seen[ve] += 1
        if ge != g or ve != v:
            mism += 1
    print(f"Python-int recheck of {len(fast_seen)} pairs ({len(sample)} random, the rest near 1/2, contacts "
          f"or violations): {classes_seen}, {mism} mismatches")
    if mism:
        die("int64 path disagrees with Python integers")

    # exact statistics on the pairs picked by the float screen
    best_gap, best_pair = None, None
    best_by_type = {}
    for i, j, g, t in near:
        nm = norms[i] * norms[j]
        gap = Fraction(nm - 4 * g * g, 4 * nm)
        key = names[t]
        if key not in best_by_type or gap < best_by_type[key][0]:
            best_by_type[key] = (gap, i, j)
        if t > 0 and (best_gap is None or gap < best_gap):
            best_gap, best_pair = gap, (i, j)
        if g > 0 and 4 * g * g < nm and 4 * D6 * D6 * g * g > (D6 - 2) ** 2 * nm:   # 0 < 1/2 - cos < 1e-6
            stats[key]["within_1e-6"] += 1
    for key in names:
        s = stats[key]
        print(f"  {key:9s} pairs {s['pairs']:>10d}  violations {s['violations']}  contacts {s['contacts']}  "
              f"fail cos<=1/2-1/L {s['gapL_fail']}  within 1e-6 of 1/2 {s['within_1e-6']}")
    report = {}
    for key, (c2f, i, j) in sorted(best_noncontact.items()):
        if c2f < 0:
            continue
        g = sum(a * b for a, b in zip(rows[i], rows[j]))
        cos2 = Fraction(g * g, norms[i] * norms[j])
        report[key] = {"rows": [i, j], "g": g, "gap": str(Fraction(1, 4) - cos2), "gap_float": float(Fraction(1, 4) - cos2)}
        print(f"  largest non-contact cosine {key:9s} {float(cos2) ** 0.5:.12f}  rows {i},{j}  gap {float(Fraction(1, 4) - cos2):.6e}")
    for key, (gap, i, j) in sorted(best_by_type.items()):
        report[key + " exact"] = {"rows": [i, j], "gap": str(gap)}
        print(f"  smallest exact gap {key:9s} {gap.numerator}/{gap.denominator} = {float(gap):.6e}  rows {i},{j}")
    new_pairs = stats["base-new"]["pairs"] + stats["new-new"]["pairs"]
    gapL_fail = stats["base-new"]["gapL_fail"] + stats["new-new"]["gapL_fail"]
    print(f"new pairs {new_pairs}: cos <= 1/2 - 1/{L} fails on {gapL_fail}")
    if best_gap is not None:
        i, j = best_pair
        print(f"smallest gap (nm-4g^2)/(4nm) over new pairs: {best_gap.numerator}/{best_gap.denominator} "
              f"= {float(best_gap):.6e}, data rows {i},{j}, norms {norms[i]}, {norms[j]}")
        if best_gap > Fraction(1, 10 ** 5) * Fraction(9, 10):
            die("float screen picked no pair with gap below 0.9e-5; the minimum is not certified")

    out = {"input": args.rays, "sha256": sha, "rows": N, "n": n, "pairs": pairs_total, "violations": viol_total,
           "contacts": contact_total, "distinct_directions": N, "rank_rows": picked, "rank_det": str(det),
           "norm_classes": K, "max_norm": str(maxnorm), "stats": stats, "largest_noncontact": report,
           "gap_L": L, "gapL_fail": gapL_fail,
           "smallest_new_gap": None if best_gap is None else [str(best_gap.numerator), str(best_gap.denominator)],
           "smallest_new_gap_rows": best_pair, "python_recheck": {"pairs": len(fast_seen), "random": len(sample),
                                                                  "classes": classes_seen, "mismatches": mism},
           "first_violation": viol_list[0] if viol_list else None, "seconds": round(time.time() - t0, 1)}
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(out, fh, indent=1)
    if viol_total:
        i, j = viol_list[0]
        die(f"{viol_total} pair violations; first data rows {i},{j} (0-based)")
    if args.expect_gap_L and gapL_fail:
        die(f"{gapL_fail} new pairs have cos > 1/2 - 1/{L}")
    print(f"time {time.time() - t0:.1f} s")
    print("CHECK PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
