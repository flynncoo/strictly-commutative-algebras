"""Exact exhaustive verification of the repaired characteristic-two counterexample.

No third-party dependencies. All vector spaces are over F_2; integers encode
vectors by their binary digits. The nonunital free two-operation algebra is
finite because both coordinates of the positive generator weights are <= 2.
"""
from functools import lru_cache
from itertools import product
from collections import Counter
import json

GEN = {'x': ((1, 0), 2), 'y': ((0, 1), 2),
       't': ((1, 1), 3), 'z': ((1, 2), 4)}

@lru_cache(None)
def wt(a):
    if isinstance(a, str): return GEN[a][0]
    u, v = wt(a[1]), wt(a[2])
    return (u[0]+v[0], u[1]+v[1])

@lru_cache(None)
def deg(a):
    if isinstance(a, str): return GEN[a][1]
    return deg(a[1])+deg(a[2])-(a[0]=='s')

def permitted(u, v):
    a, b = wt(u), wt(v)
    return a[0]+b[0] <= 2 and a[1]+b[1] <= 2

by_weight = {}
trees = []
for total in range(1, 5):
    for wx in range(3):
        wy = total-wx
        if not 0 <= wy <= 2: continue
        current = [g for g in GEN if GEN[g][0] == (wx, wy)]
        for (ax, ay), aa in list(by_weight.items()):
            bb = by_weight.get((wx-ax, wy-ay), [])
            for a,b in product(aa,bb):
                current.extend([('m',a,b), ('s',a,b)])
        by_weight[wx,wy] = current
        trees.extend(current)
idx = {a:i for i,a in enumerate(trees)}

def bits(v):
    while v:
        b = v & -v
        yield b.bit_length()-1
        v ^= b

def vec(*terms):
    r = 0
    for a in terms: r ^= 1 << idx[a]
    return r

def mul(op, u, v):
    r = 0
    for i in bits(u):
        for j in bits(v):
            a,b = trees[i],trees[j]
            if permitted(a,b): r ^= vec((op,a,b))
    return r

@lru_cache(None)
def dtree(a):
    if isinstance(a,str): return vec(('m','x','y')) if a=='t' else 0
    op,u,v = a
    r = mul(op,dtree(u),vec(v)) ^ mul(op,vec(u),dtree(v))
    if op=='s': r ^= vec(('m',u,v),('m',v,u))
    return r

def differential(v):
    r = 0
    for i in bits(v): r ^= dtree(trees[i])
    return r

class Span:
    def __init__(self, rows=()):
        self.pivots = {}
        for r in rows: self.add(r)
    def reduce(self,v):
        for i in sorted(self.pivots,reverse=True):
            if (v>>i)&1: v ^= self.pivots[i]
        return v
    def add(self,v):
        v = self.reduce(v)
        if not v: return False
        self.pivots[v.bit_length()-1] = v
        return True
    def __len__(self): return len(self.pivots)

relations = Span()
queue = []
def impose(r):
    # All relation rows must be homogeneous in degree and weight.
    if r:
        assert len({(deg(trees[i]),wt(trees[i])) for i in bits(r)}) == 1
    r = relations.reduce(r)
    if relations.add(r): queue.append(r)

# Both associativities and the one-sided Hirsch identity, on every admissible
# triple of arbitrary binary trees, not merely on the original generators.
triples = ((a,b,c) for a,b in product(trees,repeat=2)
           if permitted(a,b) for c in trees)
for a,b,c in triples:
    aw,bw,cw=wt(a),wt(b),wt(c)
    if any(aw[k]+bw[k]+cw[k] > 2 for k in (0,1)): continue
    for op in ('m','s'):
        impose(vec((op,(op,a,b),c),(op,a,(op,b,c))))
    impose(vec(('s',('m',a,b),c),
               ('m',a,('s',b,c)),('m',('s',a,c),b)))

@lru_cache(None)
def has_z(a):
    return a=='z' if isinstance(a,str) else has_z(a[1]) or has_z(a[2])
for a in trees:
    if has_z(a) and a not in ('z',('m','x','z'),('m','z','x')):
        impose(vec(a))
impose(vec(('m','x','y'),('m','y','x')))
impose(vec(('m','x','z'),('m','z','x')))
for a,b in product(('x','y'),repeat=2): impose(vec(('s',a,b)))
S=vec(('s','x','t'),('s','t','x'))
T=vec(('s','y','t'),('s','t','y'))
impose(vec(('m','t','t'),('s','t',('m','x','y')))
       ^mul('m',vec('x'),T)^mul('m',S,vec('y')))

# The three additional relations, whose differential ideal consequences matter.
impose(vec(('s','x',('m','y','y'))))
impose(vec(('s','y',('m','x','x'))))
impose(vec(('s','x',('s','t','y')),('s','y',('s','t','x'))))

# Close the relation space under d, and left and right applications of both
# operations with every tree in the finite free algebra.
pos = 0
while pos < len(queue):
    r = queue[pos]
    pos += 1
    impose(differential(r))
    rw=wt(trees[next(bits(r))])
    for a in trees:
        aw=wt(a)
        if any(rw[k]+aw[k]>2 for k in (0,1)): continue
        for op in ('m','s'):
            impose(mul(op,r,vec(a)))
            impose(mul(op,vec(a),r))

free = [i for i in range(len(trees)) if i not in relations.pivots]
q = relations.reduce
assert all(q(differential(r))==0 for r in relations.pivots.values())
assert all(q(differential(differential(1<<i)))==0 for i in free)

# Endpoints: nonunital commutative monomials in x,y,t,z; exponents encode them.
def monomial_weight(a):
    return (a[0]+a[2]+a[3], a[1]+a[2]+2*a[3])
def normal(a, endpoint):
    w=monomial_weight(a)
    if max(w)>2: return None
    x,y,t,z=a
    if endpoint=='A':
        if t or (x and y): return None
    else:
        x += t//2
        z += t//2
        t %= 2
    return (x,y,t,z)

endpoint_bases={}
for endpoint in ('A','B'):
    mm=set()
    for a in product(range(5),repeat=4):
        if not any(a): continue
        b=normal(a,endpoint)
        if b is not None: mm.add(b)
    endpoint_bases[endpoint]=sorted(mm)

def ep_mul(a,b,endpoint):
    out=set()
    for u,v in product(a,b):
        w=normal(tuple(u[i]+v[i] for i in range(4)),endpoint)
        if w is not None:
            out.symmetric_difference_update([w])
    return frozenset(out)
def ep_d(a,endpoint):
    out=set()
    for x,y,t,z in a:
        if t%2:
            w=normal((x+1,y+1,t-1,z),endpoint)
            if w is not None: out.symmetric_difference_update([w])
    return frozenset(out)
def ep_D(a):
    out=set()
    for x,y,t,z in a:
        if t%2:
            w=normal((x,y,t-1,z+1),'B')
            if w is not None: out.symmetric_difference_update([w])
    return frozenset(out)
def ep_star(a,b,endpoint):
    return ep_D(a) if endpoint=='B' and (0,1,0,0) in b else frozenset()

@lru_cache(None)
def evaluate(a,endpoint):
    if isinstance(a,str):
        if endpoint=='A' and a=='t': return frozenset()
        ex=[0]*4
        ex['xytz'.index(a)]=1
        return frozenset([tuple(ex)])
    op,u,v=a
    uu,vv=evaluate(u,endpoint),evaluate(v,endpoint)
    return ep_mul(uu,vv,endpoint) if op=='m' else ep_star(uu,vv,endpoint)

def eval_vector(v,endpoint):
    out=set()
    for i in bits(v): out.symmetric_difference_update(evaluate(trees[i],endpoint))
    return frozenset(out)

representatives=['x','y',('m','x','x'),('m','y','y'),'z',('m','x','z')]
dimensions=Counter(deg(trees[i]) for i in free)
image_by_degree={n:Span(q(differential(1<<i)) for i in free if deg(trees[i])==n)
                 for n in range(1,9)}
table=[]
for n in range(2,9):
    rank=len(image_by_degree[n])
    h=dimensions[n]-rank-len(image_by_degree[n-1])
    table.append([n,dimensions[n],rank,h])
    augmented=Span(image_by_degree[n-1].pivots.values())
    reps=[a for a in representatives if deg(a)==n]
    for a in reps:
        assert q(differential(vec(a)))==0
        assert augmented.add(q(vec(a)))
    assert len(reps)==h

# Exhaustively check endpoints' cup-1 axioms and the two evaluations, including
# every defining relation and every free expression's chain equation.
for endpoint,basis in endpoint_bases.items():
    vals=[frozenset([b]) for b in basis]
    for a,b in product(vals,repeat=2):
        ab=ep_mul(a,b,endpoint)
        assert ep_d(ab,endpoint)==ep_mul(ep_d(a,endpoint),b,endpoint)^ep_mul(a,ep_d(b,endpoint),endpoint)
        lhs=ep_d(ep_star(a,b,endpoint),endpoint)
        rhs=ep_star(ep_d(a,endpoint),b,endpoint)^ep_star(a,ep_d(b,endpoint),endpoint)^ab^ep_mul(b,a,endpoint)
        assert lhs==rhs
        for c in vals:
            assert ep_mul(ab,c,endpoint)==ep_mul(a,ep_mul(b,c,endpoint),endpoint)
            assert ep_star(ep_star(a,b,endpoint),c,endpoint)==ep_star(a,ep_star(b,c,endpoint),endpoint)
            assert ep_star(ab,c,endpoint)==ep_mul(a,ep_star(b,c,endpoint),endpoint)^ep_mul(ep_star(a,c,endpoint),b,endpoint)
    for r in relations.pivots.values(): assert not eval_vector(r,endpoint)
    for a in trees:
        assert ep_d(evaluate(a,endpoint),endpoint)==eval_vector(dtree(a),endpoint)
    ep_idx={a:i for i,a in enumerate(basis)}
    def ep_vec(a):
        out=0
        for b in a: out ^= 1<<ep_idx[b]
        return out
    boundaries=Span(ep_vec(ep_d(a,endpoint)) for a in vals)
    rank=len(boundaries)
    assert len(basis)-2*rank==len(representatives)
    for a in representatives:
        assert boundaries.add(ep_vec(evaluate(a,endpoint)))

summary={
    'field':'F_2', 'convention':'nonunital',
    'free_binary_expressions':len(trees),
    'relation_rank':len(relations), 'dimension_C':len(free),
    'dimension_A':len(endpoint_bases['A']), 'dimension_B':len(endpoint_bases['B']),
    'columns':['degree','dim C','rank d','dim H'], 'table':table,
    'positive_cohomology_representatives':['x','y','x^2','y^2','z','xz'],
    'checks':'differential ideal, d^2, endpoint axioms, all relations, chain maps, and cohomology isomorphisms passed',
}
print(json.dumps(summary,indent=2))

# An explicit vector-space decomposition into the six cohomology
# representatives and seventeen contractible pairs, for a short certificate.
def pretty(a):
    if isinstance(a,str): return a
    return '('+pretty(a[1])+(' * ' if a[0]=='s' else ' ')+pretty(a[2])+')'
def pretty_vector(v):
    return ' + '.join(pretty(trees[i]) for i in bits(v)) or '0'
pair_images=Span()
pairs=[]
for n in range(2,9):
    for i in free:
        if deg(trees[i]) != n: continue
        dv=q(differential(1<<i))
        if pair_images.add(dv): pairs.append((q(1<<i),dv))
decomposition=Span(q(vec(a)) for a in representatives)
for u,v in pairs:
    assert decomposition.add(u)
    assert decomposition.add(v)
assert len(decomposition)==len(free)

if __name__=='__main__':
    from pathlib import Path
    out=Path(__file__).resolve().parent
    (out/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
    certificate=['CONTRACTIBLE-PAIR CERTIFICATE OVER F_2',
                 'The symbol * denotes cup_1; juxtaposition denotes cup.',
                 'All equalities are in the repaired quotient C.',
                 'Together with x,y,x^2,y^2,z,xz, the following u and du form a basis.',
                 'Each displayed du is nonzero and d(du)=0.','']
    for u,v in pairs:
        certificate.append('d '+pretty_vector(u)+' = '+pretty_vector(v))
    (out/'contractible-pairs.txt').write_text('\n'.join(certificate)+'\n')
