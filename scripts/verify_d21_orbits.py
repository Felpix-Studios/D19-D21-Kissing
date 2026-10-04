#!/usr/bin/env python3
"""Exact orbit-reduced check of the 30779-point D21 configuration, Python integers only.

Usage: python3 scripts/verify_d21_orbits.py data/D21_30779_certificate.json

No NumPy, optimizer or floating point. The octads, odd fibers, removed points
and sign group are rebuilt from the certificate, and every pair that touches a
new point is checked through the sign-group reduction.

Names: H is the order-8 group Sigma_0 of the paper, K = <H, w> is Sigma, and T is
the octad Q. The JSON lists 384 representatives under H. The script checks that
the second 192 are the w-images (w = 14723) of the first 192, that w vanishes on T
and meets every octad evenly, and that K has order 16; the pair check then runs on
the 384 x H form, which is the same point set.
"""
from __future__ import annotations
import argparse, collections, itertools, json, math, time
from pathlib import Path

EXPONENTS=(0,1,5,6,7,9,11)
W=14723
T_ONE_BASED=(3,6,10,11,16,18,20,21)

def xor_span(rows):
    out=[0]
    for r in rows:out += [w^int(r) for w in out]
    assert len(set(out))==len(out), 'Dependent group generators'
    return sorted(out)

def shortened_octads():
    polynomial=sum(1<<j for j in EXPONENTS)
    rows=[]
    for j in range(12):
        w=polynomial<<j
        rows.append(w|((w.bit_count()&1)<<23))
    G=xor_span(rows)
    assert collections.Counter(w.bit_count() for w in G)=={0:1,8:759,12:2576,16:759,24:1}
    O=[w for w in G if w.bit_count()==8 and w<1<<21]
    assert len(O)==210
    assert all((u&v).bit_count()<=4 for i,u in enumerate(O) for v in O[i+1:])
    return O

def sign_change(r,g):
    return tuple(-v if (g>>j)&1 else v for j,v in enumerate(r))

def odd_patterns(support):
    for p in range(256):
        if p.bit_count()&1:
            v=[0]*21
            for k,j in enumerate(support):v[j]=-1 if (p>>k)&1 else 1
            yield tuple(v)

def verify(certificate:Path, output:Path|None=None):
    begin=time.time()
    data=json.loads(certificate.read_text())
    assert all(type(v) is int for r in data['representatives'] for v in r)
    reps=[tuple(map(int,r)) for r in data['representatives']]
    assert reps and all(len(r)==21 for r in reps)
    gens=list(map(int,data['generators']))
    assert all(0<=g<1<<21 for g in gens)
    C=xor_span(gens);O=shortened_octads()
    assert all((c&o).bit_count()%2==0 for c in C for o in O)
    supports={o:tuple(j for j in range(21) if (o>>j)&1) for o in O}
    removed=set()
    for r in data.get('removed_base_representatives',[]):
        r=tuple(map(int,r));assert len(r)==21
        support=sum(1<<j for j,v in enumerate(r) if v)
        assert support in supports and all(v in (-1,0,1) for v in r)
        assert sum(v==-1 for v in r)%2==1
        removed.update(sign_change(r,c) for c in C)
    # Complete odd fibers are invariant by binary orthogonality. The removed
    # set is a union of C-orbits, so the retained base is invariant as well.
    assert all(sign_change(r,c) in removed for r in removed for c in C)
    # The paper's form of the construction: 13 deletions on T, 192 reps x K.
    T=tuple(i-1 for i in T_ONE_BASED);Tmask=sum(1<<j for j in T)
    assert Tmask in supports and len(C)==8
    assert len(removed)==13 and all(sum(1<<j for j,v in enumerate(r) if v)==Tmask for r in removed)
    assert len(reps)==384 and reps[192:]==[sign_change(r,W) for r in reps[:192]]
    assert W&Tmask==0 and all((W&o).bit_count()%2==0 for o in O) and W not in C
    assert len(xor_span(gens+[W]))==16
    exception={sum(1<<j for j,v in enumerate(r) if v) for r in removed}
    remaining_patterns={o:[v for v in odd_patterns(supports[o]) if v not in removed] for o in exception}
    assert all(remaining_patterns[o] for o in exception)
    norms=[sum(v*v for v in r) for r in reps]
    assert all(n>0 for n in norms)
    L=int(data.get('certified_auxiliary_gap_denominator',200000000))
    assert L>2
    weakest=None
    def exact_comparison(dot,na,nb,label):
        nonlocal weakest
        assert dot<=math.isqrt(na*nb)//2, ('Kissing violation',label)
        if dot>0:
            assert (2*L*dot)**2<=(L-2)**2*na*nb, ('Strict gap violation',label)
            numerator=na*nb-4*dot*dot;denominator=4*na*nb
            assert numerator>0
            if weakest is None or numerator*weakest[1]<weakest[0]*denominator:
                d=math.gcd(numerator,denominator);weakest=(numerator//d,denominator//d,label)
    # A root max is 2*(the two largest coordinate magnitudes). For a complete
    # odd octad fiber the maximizing sign pattern follows r; if its parity is
    # even, flip a coordinate of minimum absolute value. A zero gives zero
    # flipping cost. Incomplete fibers are enumerated explicitly.
    for i,(r,n) in enumerate(zip(reps,norms)):
        magnitudes=sorted(map(abs,r))
        maximum=2*(magnitudes[-1]+magnitudes[-2])
        for o,positions in supports.items():
            if o in remaining_patterns:
                dot=max(sum(r[j]*v[j] for j in positions) for v in remaining_patterns[o])
            else:
                vals=[abs(r[j]) for j in positions]
                dot=sum(vals)
                if sum(r[j]<0 for j in positions)%2==0:dot-=2*min(vals)
            maximum=max(maximum,dot)
        exact_comparison(maximum,n,8,('representative-base',i))
    tested=0
    for i,(r,na) in enumerate(zip(reps,norms)):
        for j in range(i,len(reps)):
            s=reps[j];nb=norms[j]
            products=[a*b for a,b in zip(r,s)]
            best=None
            for c in C:
                if i==j and c==0:continue
                dot=sum(-v if (c>>k)&1 else v for k,v in enumerate(products))
                tested+=1
                if best is None or dot>best:best=dot
            if best is not None:exact_comparison(best,na,nb,('representative-orbit',i,j))
    base_count=840+210*128-len(removed)
    N=base_count+len(reps)*len(C)
    if 'population' in data:assert int(data['population'])==N
    if 'dimension'in data:assert int(data['dimension'])==21
    assert N==30779
    # All D21 roots remain. For i != j the roots 2e_i +/- 2e_j span e_i,
    # proving exactly dimension 21 without an approximate rank test.
    # All pair comparisons prove distinct normalized rays, including across
    # orbits and between the base and the auxiliary population.
    rejected=False
    try:exact_comparison(norms[0],norms[0],norms[0],('duplicate-negative-control',))
    except AssertionError:rejected=True
    assert rejected
    result={'verified':True,'dimension':21,'population':N,'original_base':27720,
            'retained_base':base_count,'removed_base_points':len(removed),
            'auxiliary_points':len(reps)*len(C),'representatives':len(reps),
            'sign_group_order':len(C),'sign_group_generators':gens,
            'k_form':{'representatives':192,'extra_generator':W,'group_order':16},
            'direct_representative_orbit_products_checked':tested,
            'complete_base_fibers':210-len(exception),'incomplete_base_fibers':len(exception),
            'pair_coverage_by_proof':N*(N-1)//2,'gap_denominator':L,
            'elementary_weakest_gap_fraction':list(weakest[:2]),
            'weakest_gap_comparison':weakest[2],
            'duplicate_negative_control_rejected':rejected,
            'arithmetic':'Python arbitrary-precision integers only; no floating point.',
            'seconds':time.time()-begin}
    if output:output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate',type=Path);p.add_argument('--output',type=Path)
    a=p.parse_args();verify(a.certificate,a.output)
