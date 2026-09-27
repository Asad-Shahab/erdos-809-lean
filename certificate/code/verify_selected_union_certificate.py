"""Independent standard-library verification of the full selected-T certificate.

No producer import, no numerical solvers. Regenerates all allowed colored
five-position graphs and every local polynomial/flag contribution, then checks
exact rational PSD and coefficient identities.
"""
import gzip
import itertools as it
import json
import math
import time
from fractions import Fraction as F
from pathlib import Path

start=time.monotonic();BASE=Path(__file__).resolve().parents[1]
d=json.loads(gzip.decompress((BASE/'separation/triangle_selected_full_coefficients.json.gz').read_bytes()))
c=json.loads((BASE/'separation/triangle_selected_union_exact_certificate.json').read_text())
pairs={n:list(it.combinations(range(n),2)) for n in (3,4,5)}
perms={n:list(it.permutations(range(n))) for n in (3,4,5)}

def mat(code,n):
 a=[[0]*n for _ in range(n)]
 for (u,v),z in zip(pairs[n],code):a[u][v]=a[v][u]=z
 return a

def valid(a):
 return all(not(a[i][j]*a[i][k]*a[j][k] and 1 in (a[i][j],a[i][k],a[j][k])) for i,j,k in it.combinations(range(len(a)),3))

def encode(a,vs):return tuple(a[vs[i]][vs[j]] for i,j in pairs[len(vs)])

def canon(a,vs,root=False):
 orders=((vs[0],)+p for p in it.permutations(vs[1:])) if root else it.permutations(vs)
 return min(encode(a,p) for p in orders)

def edgecanon(a,vs):
 return min(encode(a,vs),encode(a,(vs[0],vs[1],vs[3],vs[2])))

ix={e:i for i,e in enumerate(pairs[5])}
tri_indices=[(ix[i,j],ix[i,k],ix[j,k]) for i,j,k in it.combinations(range(5),3)]
universe=set()
for z in it.product(range(4),repeat=10):
 if all(not(z[i] and z[j] and z[k] and 1 in (z[i],z[j],z[k])) for i,j,k in tri_indices):universe.add(z)
covered=set()
for z in d['codes']:
 a=mat(z,5);assert valid(a)
 orbit={encode(a,p) for p in perms[5]}
 assert not covered.intersection(orbit)
 covered.update(orbit)
assert covered==universe
print('Exact universe covered:',len(covered),'labeled graphs;',len(d['codes']),'orbits',flush=True)

flags=[tuple(z) for z in d['flags']];types=[tuple(z) for z in d['types']]
degree_flags=[tuple(z) for z in d['degree_flags']]
assert flags==sorted({canon(mat(z,3),tuple(range(3)),True) for z in it.product(range(4),repeat=3) if valid(mat(z,3))})
assert types==sorted({canon(mat(z,3),tuple(range(3))) for z in it.product(range(4),repeat=3) if valid(mat(z,3))})
assert degree_flags==sorted({canon(mat(z,4),tuple(range(4)),True) for z in it.product(range(4),repeat=6) if valid(mat(z,4))})
uf=sorted({edgecanon(mat(z,4),tuple(range(4))) for z in it.product(range(4),repeat=6) if z[0]==3 and valid(mat(z,4))})
union_data=json.loads((BASE/'separation/triangle_selected_union_coefficients.json').read_text())
assert uf==[tuple(z) for z in union_data['flags']]
fi={z:i for i,z in enumerate(flags)};ti={z:i for i,z in enumerate(types)};di={z:i for i,z in enumerate(degree_flags)};ui={z:i for i,z in enumerate(uf)}
attachments=[]
for typ,provided in zip(types,d['type_flags']):
 good=[]
 for att in it.product(range(4),repeat=3):
  a=mat(typ,3);a=[r+[att[i]] for i,r in enumerate(a)]+[list(att)+[0]]
  if valid(a):good.append(att)
 assert good==[tuple(z) for z in provided]
 attachments.append({z:i for i,z in enumerate(good)})

qs=[];pivot_count=0;block_dimensions=[]
assert len(c['bases'])==len(c['R'])==len(types)+1
for b,rr in zip(c['bases'],c['R']):
 r=[[F(z) for z in row] for row in rr];n=len(r);block_dimensions.append(n)
 assert all(len(row)==n for row in r)
 assert all(r[i][j]==r[j][i] for i in range(n) for j in range(n))
 rem=[row[:] for row in r]
 for k in range(n):
  v=rem[k][k];assert v>0;pivot_count+=1
  for i in range(k+1,n):
   for j in range(k+1,n):rem[i][j]-=rem[i][k]*rem[k][j]/v
 assert all(len(row)==n for row in b)
 sparse=[[(i,F(z)) for i,z in enumerate(row) if z] for row in b]
 qs.append([[sum((z*r[k][l]*zz for k,z in sparse[i] for l,zz in sparse[j]),F(0)) for j in range(len(b))] for i in range(len(b))])
assert len(qs[0])==len(flags)
assert all(len(qs[k+1])==len(attachments[k]) for k in range(len(types)))
alpha={name:{int(k):F(v) for k,v in vals.items()} for name,vals in c['alphas'].items()}
assert set(alpha)=={'density','degree','selected_root','union'}
assert all(v>=0 for vals in alpha.values() for v in vals.values())
limits={'density':len(types),'degree':len(degree_flags),'selected_root':len(flags),'union':len(uf)}
assert all(0<=k<limits[name] for name,vals in alpha.items() for k in vals)
# Use a common exact integer scale to keep 172320 local permutation checks fast.
scale=3*math.lcm(*(v.denominator for q in qs for row in q for v in row),*(v.denominator for vals in alpha.values() for v in vals.values()))
qi=[[[int(v*scale) for v in row] for row in q] for q in qs]
ai={name:{k:int(v*scale) for k,v in vals.items()} for name,vals in alpha.items()}
assert all(F(v*scale).denominator==1 for q in qs for row in q for v in row)
print('Exact PSD passed:',pivot_count,'positive pivots in',len(qs),'blocks; checking coefficients',flush=True)
slacks=[]
for index,z in enumerate(d['codes']):
 a=mat(z,5);target=0;rhs=0
 for p in perms[5]:
  tri=bool(a[p[0]][p[1]]*a[p[0]][p[2]]*a[p[1]][p[2]])
  ed=bool(a[p[3]][p[4]]);ef=a[p[3]][p[4]]==1;sel=a[p[3]][p[4]]==3
  target+=4*int(tri and a[p[0]][p[3]]>=2 and ef)+int(tri)-int(tri and ed)-2*int(tri and ef)-int(tri and sel)
  f=fi[canon(a,p[:3],True)];h=fi[canon(a,(p[0],p[3],p[4]),True)]
  rhs+=4*qi[0][f][h]
  typ=ti[canon(a,p[:3])]
  rhs+=ai['density'].get(typ,0)*(2*int(ed)-1)
  degflag=di[canon(a,p[:4],True)]
  rhs+=(4*ai['degree'].get(degflag,0)//3)*(3*int(a[p[0]][p[4]]>0)-1)
  if a[p[1]][p[2]]==3:
   rhs+=2*ai['selected_root'].get(h,0)*(1-int(a[p[0]][p[1]]>0)-int(a[p[0]][p[2]]>0))
  if a[p[0]][p[1]]==3:
   uflag=ui[edgecanon(a,p[:4])]
   rhs+=(4*ai['union'].get(uflag,0)//3)*(2-3*int(a[p[0]][p[4]]>0 or a[p[1]][p[4]]>0))
  literal=encode(a,p[:3])
  if literal in ti:
   k=ti[literal]
   f=attachments[k][tuple(a[p[i]][p[3]] for i in range(3))]
   h2=attachments[k][tuple(a[p[i]][p[4]] for i in range(3))]
   rhs+=4*qi[k+1][f][h2]
 assert target==d['p'][index]
 slack=F(target*scale-rhs,scale)
 assert slack==F(c['coefficient_slacks'][index]),(index,slack,c['coefficient_slacks'][index])
 assert slack>=0,(index,slack)
 slacks.append(slack)
 if (index+1)%300==0:print('Verified',index+1,'local coefficient identities',flush=True)
out={'status':'EXACTLY VERIFIED BY INDEPENDENT STANDARD-LIBRARY CHECKER','unlabeled_colored_graphs':len(d['codes']),'labeled_allowed_graphs':len(universe),'permutations_per_graph':120,'gram_matrices':len(qs),'reduced_dimensions':block_dimensions,'positive_LDL_pivots':pivot_count,'positive_coefficient_slacks':sum(v>0 for v in slacks),'zero_coefficient_slacks':sum(v==0 for v in slacks),'minimum_coefficient_slack':str(min(slacks)),'minimum_positive_coefficient_slack':str(min(v for v in slacks if v>0)),'maximum_density_multiplier':str(max(alpha['density'].values())),'seconds':time.monotonic()-start,'scope':'2A+(1/2-m-2f-M)Delta >= 0 for m>=1/4, minimum degree>=1/3, selected root constraints, selected-neighborhood-union<=2/3; actual one-matching M=2nu meets those hypotheses.'}
(BASE/'results/selected_union_independent_replay.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
