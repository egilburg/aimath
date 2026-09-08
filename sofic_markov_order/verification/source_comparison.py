"""Supplement the compiled comparison with a transparent source-level check.

Usage: python3 source_comparison.py OLD_LEAN_DIRECTORY NEW_LEAN_DIRECTORY
The old source is the previous public release, an external comparison input.
"""
from pathlib import Path
import sys,re,json,hashlib

old,new=map(Path,sys.argv[1:3])
renames=[('IndependentZeroBlocks','SoficMarkovOrder'),('digitShift','sequenceShift'),
 ('digitHead','sequenceHead'),('stationaryPrefix','orbitPrefix'),
 ('soficPairChain','pairChain'),('sourceSelectorWeights','selectorWeight')]
checks=[
 ('CanonicalHankelRepresentation','CanonicalHankel','stationary_process_markov_cutoff_of_finite_hankel','statement'),
 ('CanonicalHankelRepresentation','CanonicalHankel','stationary_process_markov_cutoff_of_representation','statement'),
 ('SoficSharpProcess','SharpProcess','exists_rational_sharp_sofic_process','statement'),
 ('SoficProcessMarkov','ProcessMarkov','processMarkov_iff_rankOne','statement'),
 ('StationarySourceBridge','SequenceSpace','digitShift','definition'),
 ('SoficProcessMarkov','ProcessMarkov','wordCylinder','definition'),
 ('SoficProcessMarkov','ProcessMarkov','ProcessMarkov','definition'),
 ('SoficHankel','HankelRankCriterion','wordHankelSpan','definition'),
 ('SoficHankel','HankelRankCriterion','WordReduced','definition'),
 ('SoficHankel','HankelRankCriterion','representedWord','definition'),
 ('ReachableSpanMortality','WordProducts','linearWord','definition'),
 ('ReachableSpanMortality','WordProducts','linearOrbit','definition'),
 ('ReachableSpanMortality','WordProducts','linearReachableSpan','definition'),
 ('SoficPositiveCompletion','PositiveCompletion','averageRow','definition'),
 ('SoficPositiveCompletion','PositiveCompletion','endEntry','definition'),
 ('SoficPositiveCompletion','PositiveCompletion','uniformMean','definition'),
 ('SoficRationalSharpness','RationalSharpness','RationalReal','definition')]

def remove_comments(text):
 # Lean block comments nest. Only comments and whitespace are normalized;
 # mathematical tokens, binders, hypotheses and bodies remain literal.
 result=[]; depth=0; i=0
 while i<len(text):
  if text[i:i+2]=='/-': depth+=1; i+=2
  elif text[i:i+2]=='-/' and depth: depth-=1; i+=2
  elif depth: i+=1
  elif text[i:i+2]=='--':
   j=text.find('\n',i); i=len(text) if j<0 else j
  else: result.append(text[i]); i+=1
 return ''.join(result)
def block(path,name):
 t=remove_comments(path.read_text())
 pat=r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem|structure) '+re.escape(name)+r'(?=\s|\(|:)'
 m=re.search(pat,t,re.M)
 if not m: raise RuntimeError((path,name))
 start=m.start(); rest=t[m.end():]
 end=re.search(r'^\s*(?:@\[|(?:def|theorem|lemma|structure|abbrev|instance|namespace|end|section|variable|omit|attribute)\s)',rest,re.M)
 return t[start:m.end()+(end.start() if end else len(rest))]
def normalized(text):
 for a,b in renames: text=text.replace(a,b)
 return re.sub(r'\s+','',text)
results=[]
for om,nm,n,kind in checks:
 op=old/'SierpinskiFormal'/f'{om}.lean'; np=new/'SoficMarkovOrder'/f'{nm}.lean'
 nn=n
 for a,b in renames: nn=nn.replace(a,b)
 a,b=block(op,n),block(np,nn)
 if kind=='statement': a,b=a.split(':=',1)[0],b.split(':=',1)[0]
 a,b=normalized(a),normalized(b)
 if a!=b: raise AssertionError((n,a,b))
 results.append({'old':f'IndependentZeroBlocks.{n}','new':f'SoficMarkovOrder.{nn}',
  'kind':kind,'result':'identical modulo explicit renaming, comments and whitespace',
  'normalized_sha256':hashlib.sha256(a.encode()).hexdigest()})
print(json.dumps({'status':'PASS','checks':results,'count':len(results)},indent=2))
