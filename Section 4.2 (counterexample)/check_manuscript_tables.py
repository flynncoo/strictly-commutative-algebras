"""Choose a checked basis retaining the manuscript's first three tables."""
import contextlib
import io
from pathlib import Path
with contextlib.redirect_stdout(io.StringIO()):
    import verify_counterexample as v

x,y,t,z=[v.vec(a) for a in 'xytz']
def m(a,b): return v.mul('m',a,b)
def s(a,b): return v.mul('s',a,b)
S=s(x,t)^s(t,x)
T=s(y,t)^s(t,y)
xy=m(x,y)
tables={
 1:[('x',x),('y',y)],
 2:[('t',t),('x^2',m(x,x)),('xy',xy),('y^2',m(y,y))],
 3:[(r'x\cup_1 t',s(x,t)),(r'y\cup_1 t',s(y,t)),('T',T),('S',S),
    (r'x\cup t',m(x,t)),(r't\cup x',m(t,x)),
    (r'y\cup t',m(y,t)),(r't\cup y',m(t,y)),
    (r'x\cup_1(xy)',s(x,xy)),(r'y\cup_1(xy)',s(y,xy)),
    ('x^2y',m(x,xy)),('xy^2',m(xy,y))],
}
allbasis=v.Span([v.q(z),v.q(m(x,z))])
for length,rows in tables.items():
    for name,a in rows: assert allbasis.add(v.q(a)),name

preferred=[
 (r't\cup_1t',s(t,t)),
 (r'y\cup_1(t\cup_1x)',s(y,s(t,x))),
 (r'x\cup T',m(x,T)),(r'T\cup x',m(T,x)),(r'S\cup y',m(S,y)),
 (r'(x\cup_1t)\cup y',m(s(x,t),y)),
 (r'(y\cup_1t)\cup x',m(s(y,t),x)),
 (r'x\cup(y\cup_1t)',m(x,s(y,t))),
 (r't\cup_1(xy)',s(t,xy)),
 (r'y\cup_1(xt)',s(y,m(x,t))),
 (r'y\cup_1(tx)',s(y,m(t,x))),
 (r'x\cup_1(yt)',s(x,m(y,t))),
 (r'xy\cup t',m(xy,t)),(r't\cup xy',m(t,xy)),
 (r'x\cup t\cup y',m(m(x,t),y)),(r'y\cup t\cup x',m(m(y,t),x)),
 (r'x\cup(y\cup_1xy)',m(x,s(y,xy))),
 (r'(y\cup_1xy)\cup x',m(s(y,xy),x)),
 (r'(x\cup_1xy)\cup y',m(s(x,xy),y)),
 (r'y\cup_1(x^2y)',s(y,m(x,xy))),
 (r'x\cup_1(xy^2)',s(x,m(xy,y))),
 ('x^2y^2',m(xy,xy)),
]
rows=[]
for name,a in preferred:
    if allbasis.add(v.q(a)): rows.append((name,a))
assert len(rows)==20,len(rows)
assert len(allbasis)==40
tables[4]=rows

def coordinates(a,basis):
    pivots={}
    for j,(_,col) in enumerate(basis):
        c=1<<j
        col=v.q(col)
        for p,(u,w) in sorted(pivots.items(),reverse=True):
            if (col>>p)&1: col^=u; c^=w
        assert col
        pivots[col.bit_length()-1]=(col,c)
    col=v.q(a); c=0
    for p,(u,w) in sorted(pivots.items(),reverse=True):
        if (col>>p)&1: col^=u; c^=w
    assert not col
    return c

out=[]
for length,rr in tables.items():
    out.append('WORD LENGTH '+str(length))
    for n in range(2,9):
        atn=[(name,a) for name,a in rr if v.deg(v.trees[next(v.bits(a))])==n]
        if atn:
            out.append(str(n)+': '+', '.join(name for name,a in atn))
            out.append('rank d = '+str(len(v.Span(v.q(v.differential(a)) for name,a in atn))))
    out.append('DIFFERENTIALS')
    for name,a in rr:
        c=coordinates(v.differential(a),rr)
        if c: out.append('d('+name+') = '+' + '.join(rr[i][0] for i in v.bits(c)))
    out.append('NONZERO VALUES OF g')
    for name,a in rr:
        value=v.eval_vector(a,'B')
        if value: out.append(name+' -> '+str(sorted(value)))
    out.append('')
Path(__file__).with_name('close-presentation-check.txt').write_text('\n'.join(out))
print('\n'.join(out))
