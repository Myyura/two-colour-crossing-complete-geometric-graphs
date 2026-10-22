"""Independent exact diagnostic for candidate PDF Sections 4 and 6.

Reduced counts test the geometric lemmas, not the full asymptotic reduction.
No source-archive checker is used. All final crossings use integer determinants.
"""
from fractions import Fraction as F
from itertools import combinations
from math import lcm
import json
import time


def orient(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])


def cross(a, b, c, d):
    return orient(a,b,c)*orient(a,b,d)<0 and orient(c,d,a)*orient(c,d,b)<0


def run(S, W, B, Dm, pairing):
    mu, tau = F(1,2**20), F(1,2**40)
    kap = F(1,100)
    P = lambda y: (-10-kap*y*y,y)
    A = lambda t: (1+kap*t*t,t)
    aa = [F(-3,4)+F(j,8*(S+1)) for j in range(1,S+1)]
    bb = [F(5,8)+F(j,8*(S+1)) for j in range(1,S+1)]
    theta = [F(2*r-W-1,2*(W-1)) for r in range(1,W+1)]
    orig, blocks, heights, macro = [], [], [], aa+bb
    for h,a in enumerate(aa):
        for v in theta:
            orig.append(P(a+tau*v)); blocks.append(h); heights.append(a+tau*v)
    for j in range(1,Dm+1):
        y=F(-1,2)+F(j,Dm+1)
        orig.append(P(y)); blocks.append(2*S+j-1); heights.append(y)
        macro.append(y)
    for h,b in enumerate(bb):
        for v in theta:
            orig.append(P(b+tau*v)); blocks.append(S+h); heights.append(b+tau*v)
    frame = [A(1-F(2*(i+1),B+1)) for i in range(B)]
    base = orig+frame
    assert all(orient(*triple) for triple in combinations(base,3))
    protos=[]
    for h,a in enumerate(aa+bb):
        p=P(a); r=((1+mu)*p[0]-mu,(1+mu)*p[1])
        protos.append(dict(kind='ordinary',parent=h,point=r))
    for h,partner in enumerate(pairing):
        a,b=aa[h],bb[partner]
        ac=[a+tau*v for v in theta]; bc=[b+tau*v for v in theta]
        support=lambda s,t,y: -10-kap*((ac[s]+bc[t])*y-ac[s]*bc[t])
        for side in ['left','right']:
            y=a+mu*(b-a) if side=='left' else b-mu*(b-a)
            for ell in range(1,W):
                if side=='left':
                    low,high=support(ell-1,0,y),support(ell,W-1,y)
                else:
                    low,high=support(W-1,ell,y),support(0,ell-1,y)
                assert high-low >= kap*tau*(b-a)/(2*W)
                r=((low+high)/2,y)
                protos.append(dict(kind=side,parent=h if side=='left' else S+partner,
                                   pair=(h,S+partner),ell=ell,point=r))
    # Check all one-program determinants used by the perturbation proof.
    determinants=[abs(orient(r['point'],u,v)) for r in protos for u,v in combinations(base,2)]
    assert all(determinants)
    eta=min(determinants)
    cap=lambda r:r[0]+10+kap*r[1]*r[1]
    assert all(cap(r['point'])<0 for r in protos)
    eta_cap=min(-cap(r['point']) for r in protos)
    L=1+max(abs(u[0]-v[0])+abs(u[1]-v[1]) for u,v in combinations(base,2))
    delta=F(1,1)
    while delta>min(eta/(8*L),eta_cap/8,F(1,4)):
        delta/=2
    # Two copies at every prototype, with a single global radius and grid.
    copies=[r.copy() for r in protos for _ in range(2)]
    M=len(base)+len(copies); m=M*(M-1)//2+M+2
    den=lcm(*[x.denominator for p in base for x in p],
            *[x.denominator for r in protos for x in r['point']],
            (delta/F(2*(m+1))).denominator)
    integer=lambda p:tuple(int(x*den) for x in p)
    ibase=[integer(p) for p in base]
    placed=ibase.copy(); search_checks=0
    step=int(delta*den/F(2*(m+1)))
    for r in copies:
        px,py=integer(r['point'])
        found=False
        for i in range(1,m+1):
            for j in range(1,m+1):
                q=(px+step*(2*i-m-1),py+step*(2*j-m-1))
                search_checks+=1
                if q in placed: continue
                if any(orient(u,v,q)==0 for u,v in combinations(placed,2)): continue
                r['index']=len(placed); placed.append(q); found=True; break
            if found: break
        assert found
    assert all(orient(*tri) for tri in combinations(placed,3))
    assert all(cap((F(placed[r['index']][0],den),F(placed[r['index']][1],den)))<0 for r in copies)
    o=len(orig)
    O=list(range(o)); Aids=list(range(o,o+B)); R=[r['index'] for r in copies]
    classes={
        'X':[(a,p) for a in Aids for p in O],
        'T':[(a,r) for a in Aids for r in R],
        'C':list(combinations(O,2)),
        'Y':[(r,p) for r in R for p in O]+list(combinations(R,2)),
        'I':list(combinations(Aids,2)),
    }
    checks=0
    def cr(e,f):
        nonlocal checks
        checks+=1
        return cross(placed[e[0]],placed[e[1]],placed[f[0]],placed[f[1]])
    # The exhaustive class exclusions needed by Section 7.
    for cn in ['C','Y','I']:
        assert not any(cr(x,y) for x in classes['X'] for y in classes[cn])
    for cn in ['T','C','Y']:
        assert not any(cr(x,y) for x in classes['I'] for y in classes[cn])
    for k in range(B):
        for i in range(B):
            for j in range(o):
                for l in range(o):
                    assert cr((o+k,j),(o+i,l)) == ((k-i)*(j-l)>0)
    # Exact parent table; virtual-column table; every selected and nonselected core edge.
    for r in copies:
        h=r['parent']; kind=r['kind']; ri=r['index']
        for k in range(B):
            rf=(ri,o+k)
            for j in O:
                for i in range(B):
                    if kind=='ordinary' and blocks[j]==h:
                        expect=(i<k and k<B//2) or (i>k and k>=B//2)
                    else:
                        precedes=(heights[j]<r['point'][1])
                        expect=(i<k and precedes) or (i>k and not precedes)
                    assert cr(rf,(j,o+i))==expect,(r,k,j,i)
            for u,v in classes['C']:
                bu,bv=blocks[u],blocks[v]
                if bu!=h and bv!=h:
                    expect=False
                elif bu==h and bv==h:
                    continue # Short parent costs are retained, not prescribed.
                else:
                    parent,other=(u,v) if bu==h else (v,u)
                    otherblock=blocks[other]
                    if kind=='ordinary':
                        expect=(k<B//2) if heights[other]>macro[h] else (k>=B//2)
                    elif otherblock in r['pair']:
                        rank=sorted(z for z in O if blocks[z]==h).index(parent)+1
                        expect=(rank>r['ell']) if kind=='left' else (rank<=r['ell'])
                    else:
                        a,b=(macro[z] for z in r['pair'])
                        expect=a<macro[otherblock]<b
                assert cr(rf,(u,v))==expect,(r,k,u,v,expect)
    return dict(S=S,W=W,B=B,Dm=Dm,pairing=pairing,points=M,originals=o,
                prototypes=len(protos),program_copies=len(copies),crossing_predicates=checks,
                insertion_candidates=search_checks,delta=str(delta),coordinate_common_den_bits=den.bit_length(),
                result='all exact checks passed')


if __name__=='__main__':
    start=time.process_time()
    out=[run(2,3,8,3,[1,0]),run(2,4,16,4,[0,1])]
    print(json.dumps(dict(cases=out,cpu_seconds=time.process_time()-start,
                         scope='Reduced geometric diagnostic; not full parameter construction or solver evidence'),indent=2))
