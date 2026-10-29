"""Run all checks for counterexample-insert.tex using only Python 3.

This additionally constructs A and B from the explicit ideals printed in the
LaTeX, rather than assuming their equivalence to the auxiliary weight cutoff.
"""
import contextlib
import io
import json
from pathlib import Path
from itertools import product

with contextlib.redirect_stdout(io.StringIO()):
    import check_manuscript_tables as tables
v=tables.v

# Independent finite commutative presentation: x^3=y^3=z^2=t^4=0.
# The t^4 cutoff is d-stable in characteristic two. All remaining explicit
# relations, including t^3 in B, are imposed and closed under d and products.
raw=[a for a in product(range(3),range(3),range(4),range(2)) if any(a)]
ri={a:i for i,a in enumerate(raw)}
def raw_vec(a): return 1<<ri[a] if a in ri else 0
def raw_product(u,w):
    r=0
    for i in v.bits(u):
        for j in v.bits(w):
            r ^= raw_vec(tuple(raw[i][k]+raw[j][k] for k in range(4)))
    return r
def raw_d(u):
    r=0
    for i in v.bits(u):
        x,y,t,z=raw[i]
        if t%2: r ^= raw_vec((x+1,y+1,t-1,z))
    return r
generators=[raw_vec(a) for a in [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]]
explicit={
 'A': [raw_vec((0,0,1,0)),raw_vec((1,1,0,0)),raw_vec((2,0,0,1)),raw_vec((0,1,0,1))],
 'B': [raw_vec((2,0,1,0)),raw_vec((0,2,1,0)),raw_vec((0,0,3,0)),
       raw_vec((0,0,2,0))^raw_vec((1,0,0,1)),raw_vec((0,0,1,1)),
       raw_vec((0,1,0,1)),raw_vec((2,0,0,1))]
}
for endpoint,rr in explicit.items():
    relations=v.Span()
    queue=[]
    def impose(r):
        r=relations.reduce(r)
        if relations.add(r): queue.append(r)
    for r in rr: impose(r)
    i=0
    while i<len(queue):
        r=queue[i]; i+=1
        impose(raw_d(r))
        for g in generators: impose(raw_product(g,r))
    free=[i for i in range(len(raw)) if i not in relations.pivots]
    assert len(free)==len(v.endpoint_bases[endpoint])
    ep_idx={a:i for i,a in enumerate(v.endpoint_bases[endpoint])}
    def convert(r):
        out=0
        for i in v.bits(r):
            a=v.normal(raw[i],endpoint)
            if a is not None: out ^= 1<<ep_idx[a]
        return out
    for r in relations.pivots.values(): assert convert(r)==0
    assert len(v.Span(convert(1<<i) for i in free))==len(free)
    for i in free:
        a=v.normal(raw[i],endpoint)
        aval=frozenset([a]) if a is not None else frozenset()
        expected=0
        for b in v.ep_d(aval,endpoint): expected ^= 1<<ep_idx[b]
        assert convert(raw_d(1<<i))==expected

# Cross-check each printed differential rank by a dense Gaussian elimination,
# independently of the sparse integer-span elimination used by the verifier.
def dense_rank(columns,nrows):
    a=[[(col>>r)&1 for col in columns] for r in range(nrows)]
    rank=0
    for j in range(len(columns)):
        p=next((r for r in range(rank,nrows) if a[r][j]),None)
        if p is None: continue
        a[rank],a[p]=a[p],a[rank]
        for r in range(nrows):
            if r!=rank and a[r][j]:
                a[r]=[u^w for u,w in zip(a[r],a[rank])]
        rank+=1
    return rank

expected_ranks={1:{2:0},2:{3:1,4:0},3:{4:4,5:2,6:0},4:{5:2,6:7,7:1,8:0}}
for length,rr in tables.tables.items():
    for degree,expected in expected_ranks[length].items():
        cols=[tables.coordinates(v.differential(a),rr) for name,a in rr
              if v.deg(v.trees[next(v.bits(a))])==degree]
        assert dense_rank(cols,len(rr))==expected

# Verify the map values exactly as stated in the insert's basis convention.
exceptional={
 'T':frozenset([(0,0,0,1)]),
 r'x\cup T':frozenset([(1,0,0,1)]),
 r'T\cup x':frozenset([(1,0,0,1)])
}
for rr in tables.tables.values():
    for name,a in rr:
        if r'\cup_1' in name or name in ('S','T') or r'\cup T' in name or r'T\cup' in name or r'S\cup' in name:
            assert v.eval_vector(a,'B')==exceptional.get(name,frozenset()),name

# Frobenius value and denominator, in the explicitly verified endpoint rings.
for ep in ('A','B'):
    basis=v.endpoint_bases[ep]
    ei={a:i for i,a in enumerate(basis)}
    def evec(terms):
        result=0
        for a in terms: result^=1<<ei[a]
        return result
    boundaries=v.Span(evec(v.ep_d(frozenset([a]),ep)) for a in basis)
    for exponent in [(3,0,0,0),(2,1,0,0),(1,2,0,0),(0,3,0,0)]:
        a=v.normal(exponent,ep)
        assert a is None or boundaries.reduce(evec([a]))==0
    degree3=[a for a in basis if sum(a[i]*[2,2,3,4][i] for i in range(4))==3]
    assert (not degree3 if ep=='A' else degree3==[(0,0,1,0)])
    if ep=='B':
        assert v.normal((0,0,2,0),ep)==(1,0,0,1)
        assert boundaries.reduce(evec([(1,0,0,1)]))!=0

summary=dict(v.summary)
summary.update({
 'explicit_endpoint_ideals':'passed',
 'all_four_manuscript_tables':'passed',
 'dense_differential_rank_cross_check':'passed',
 'manuscript_map_assignments':'passed',
 'frobenius_values_and_zero_denominator':'passed',
 'result':'ALL CHECKS PASSED',
})
out=Path(__file__).resolve().parent
(out/'verification-results.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
