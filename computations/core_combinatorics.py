"""Independent finite checks of candidate PDF Section 5 convex combinatorics.

This is not a check of the huge reduction or program geometry.  All 6 orders
of three source vertices are checked, q=2, W=3, D=5.  D is deliberately small:
the counted identities hold for arbitrary D; forcing inequalities are not run.
Crossings are reconstructed from exact integer parabola coordinates.
"""
from itertools import combinations, permutations
from math import comb
import json
import time


def orient(p, q, r):
    return (q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0])


def crosses(e, f, pts):
    a, b = (pts[x] for x in e)
    c, d = (pts[x] for x in f)
    return orient(a,b,c)*orient(a,b,d)<0 and orient(c,d,a)*orient(c,d,b)<0


def run(late_order, n=3, q=2, W=3, D=5):
    S=n*q
    labels=[]
    for j in range(S):
        labels.extend(('p',j,r) for r in range(W))
    labels.extend(('d',None,r) for r in range(D))
    for v in late_order:
        for cp in reversed(range(q)):
            labels.extend(('q',v*q+cp,r) for r in range(W))
    pts=[(i,i*i) for i in range(len(labels))]
    edges=list(combinations(range(len(labels)),2))
    kind={}
    palette={}
    selected={}
    for e in edges:
        a,b=(labels[i] for i in e)
        if a[0]=='d' and b[0]=='d':
            kind[e]='D'
        elif a[0]==b[0] and a[1]==b[1]:
            kind[e]='U'
        elif a[0]=='p' and b[0]=='q' and a[1]==b[1]:
            kind[e]='S'
            selected[e]=(a[1],a[2],b[2])
        else:
            kind[e]='F'
            if b[0] in ('p','d'): palette[e]=0
            elif a[0] in ('q','d'): palette[e]=1
            else: palette[e]=int(a[1]<b[1])
    fields={e:0 for e in selected}
    local=0
    dummy_counts={e:[0,0] for e in edges if kind[e]=='D'}
    main_counts={}
    for quad in combinations(range(len(labels)),4):
        a,b,c,d=quad
        for e,f in [((a,b),(c,d)),((a,c),(b,d)),((a,d),(b,c))]:
            if not crosses(e,f,pts): continue
            ke,kf=kind[e],kind[f]
            if ke=='S' and kf=='F': fields[e]+=2*palette[f]-1
            if kf=='S' and ke=='F': fields[f]+=2*palette[e]-1
            if ke=='D':
                assert kf in ('F','D'), (e,f,ke,kf)
                if kf=='F': dummy_counts[e][palette[f]]+=1
            if kf=='D':
                assert ke in ('F','D'), (e,f,ke,kf)
                if ke=='F': dummy_counts[f][palette[e]]+=1
            if {ke,kf}=={'U','S'} or ke==kf=='U': local+=1
            if ke==kf=='S':
                j=selected[e][0]; k=selected[f][0]
                if j==k: local+=1
                else:
                    pair=tuple(sorted((j//q,k//q)))
                    main_counts[pair]=main_counts.get(pair,0)+1
    assert local==S*(comb(W,2)**2+2*W*comb(W,3)+2*comb(W,4))
    pos={v:i for i,v in enumerate(late_order)}
    expected={(v,w):(q*W*W)**2 for v,w in combinations(range(n),2) if pos[v]<pos[w]}
    assert main_counts==expected,(main_counts,expected)
    by_j={}
    for e,(j,r,t) in selected.items(): by_j.setdefault(j,{})[r,t]=fields[e]
    for j,values in by_j.items():
        beta=values[0,0]
        gammaL=values[1,0]-beta; gammaR=values[0,1]-beta
        assert -D-2*S*W<=gammaL<=-D+2*S*W
        assert -D-2*S*W<=gammaR<=-D+2*S*W
        assert all(v==beta+gammaL*r+gammaR*t for (r,t),v in values.items())
    for e,counts in dummy_counts.items():
        a,b=(labels[i][2] for i in e)
        assert counts==[S*W*(b-a-1)]*2
    assert sum(v[0] for v in dummy_counts.values())==S*W*comb(D,3)
    return {'late_order':late_order,'points':len(labels),'source_edges':len(selected),'local_constraints':local,'main_constraints':sum(main_counts.values()),'status':'PASS'}


if __name__=='__main__':
    start=time.process_time()
    results=[run(p) for p in permutations(range(3))]
    print(json.dumps({'scope':'Finite Section 5 combinatorics only; no program geometry, optimization, general theorem, or Lean claim','q':2,'W':3,'D':5,'results':results,'cpu_seconds':time.process_time()-start},indent=2))
