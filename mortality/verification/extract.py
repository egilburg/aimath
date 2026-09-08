from pathlib import Path
import re,json,hashlib,shutil,argparse
parser=argparse.ArgumentParser(description='Extract the paper-focused mortality proof from the original published Lean source.')
parser.add_argument('original_lean_root',type=Path)
parser.add_argument('output_lean_root',type=Path)
parser.add_argument('--report-dir',type=Path,required=True)
args=parser.parse_args()
src=args.original_lean_root.resolve()
dst=args.output_lean_root.resolve()
if src==dst: parser.error('Original and output roots must differ.')
dst.mkdir(parents=True,exist_ok=True)
args.report_dir.mkdir(parents=True,exist_ok=True)
ns='FiniteMonoidMortality'
(dst/ns).mkdir(exist_ok=True)
rename={'IndependentZeroBlocks':ns,'quadraticObservationDigit':'quadraticObservationLetter','linearWord_quadraticObservationDigit':'linearWord_quadraticObservationLetter','returnMatrix':'compressedReturn','returnMatrix_mul':'compressedReturn_mul','exists_invariant_quadraticForm_returnMatrix_of_finite':'exists_invariant_quadraticForm_compressedReturn_of_finite','rank_resetSandwich_lt_of_invariantTraceDefect_ne_zero':'rank_wordSandwich_lt_of_invariantTraceDefect_ne_zero'}
# Long names first, so the mapping is simultaneous and exact on identifiers.
pattern=re.compile(r'\b('+ '|'.join(re.escape(x) for x in sorted(rename,key=len,reverse=True))+r')\b')
def renamed(x): return pattern.sub(lambda m:rename[m[0]],x)
def read(name): return (src/'SierpinskiFormal'/f'{name}.lean').read_text()
def between(s,a,b): return s[s.index(a):s.index(b)]
def body(name):
 s=read(name)
 return s.split('namespace IndependentZeroBlocks\n',1)[1].rsplit('\nend IndependentZeroBlocks',1)[0].strip()
def remove_decl(s,name):
 # Scope individual declarations by the next declaration or comment.
 p=re.compile(r'(?m)^(?:@\[[^\n]*\] )?(?:private )?(?:theorem|def|abbrev) '+re.escape(name)+r'\b')
 m=p.search(s)
 if not m:return s
 start=m.start(); prior=s.rfind('/--',0,start)
 if prior>=0 and s[prior:start].strip().endswith('-/') and s[s.index('-/',prior)+2:start].strip()=='': start=prior
 nxt=re.search(r'(?m)^(?:/--|@\[|(?:private )?(?:theorem|def|abbrev) |end )',s[m.end():])
 end=m.end()+nxt.start() if nxt else len(s)
 return s[:start]+s[end:]
modules={}
words=between(body('MinimalRankCompression'),'/-- Chronological product','/-- Every square matrix')
# matrixWord's type context is kept exactly as in the original.
words='variable {F A ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]\n\n'+words
# Include scalar extension directly after word multiplication.
words+='\n'+body('MatrixWordScalarExtension')
modules['MatrixWords']=(['Mathlib.Data.Matrix.Mul','Mathlib.RingTheory.SimpleRing.Basic','Mathlib.Algebra.BigOperators.Group.List.Basic'], 'Matrix words and scalar extension', 'Word products multiply in written list order. Scalar extension preserves finite product range and reflects zero words.',words)
short=body('ReachableSpanMortality')
short=between(short,'section Semiring','theorem seed_mem_linearReachableSpan')+'end Semiring\n'
short=remove_decl(short,'linearWord_append')
short+='\nsection ShortOrbit\n\n'+between(body('FiniteDimensionDetection'),'variable {K V ι','/-- A reachable space has a basis')+'end ShortOrbit\n'
modules['ReachableSpans']=(['Mathlib.LinearAlgebra.FiniteDimensional.Lemmas','Mathlib.Algebra.BigOperators.Group.List.Basic'], 'Short spanning words for linear orbits','The ascending orbit spans stabilize before the ambient dimension. This is the linear witness lemma used by the quadratic observation.',short)
compression=body('MinimalRankCompression')
compression=between(compression,'/-- Every square matrix','/-- A positive lower rank')+between(compression,'/-- Return matrices multiply','/-- The word consisting')
compression='variable {F A ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]\n\n'+compression
modules['Compression']=(['FiniteMonoidMortality.MatrixWords','Mathlib.LinearAlgebra.Matrix.Rank','Mathlib.LinearAlgebra.Matrix.NonsingularInverse'],'Rank factorization and compressed returns','A rank-sized factorization H = U V turns a sandwich H Y H into U (V Y U) V. Only the rank and multiplication identities needed for mortality are included.',compression)
invariant=remove_decl(body('FiniteMortalityCompression'),'invariantTraceDefect_zero')
modules['InvariantForms']=(['Mathlib.Data.Real.Basic','FiniteMonoidMortality.Compression','Mathlib.GroupTheory.OrderOfElement','Mathlib.LinearAlgebra.Matrix.Trace','Mathlib.Tactic.NoncommRing'],'Invariant forms and a rank-drop certificate','Average g gᵀ over the invertible members of a finite matrix semigroup. The resulting positive-trace form detects rank loss through a scalar trace defect.',invariant)
quad=body('ShortQuadraticObservation')
for name in ['matrixOfSym2Coords_apply','sym2CoordsOfMatrix_mk']:
 quad=remove_decl(quad,name)
quad=quad.replace('/-- A digit fixes','/-- A generator fixes')
modules['QuadraticObservation']=(['Mathlib.Data.Real.Basic','FiniteMonoidMortality.MatrixWords','FiniteMonoidMortality.ReachableSpans','Mathlib.Data.Sym.Card','Mathlib.LinearAlgebra.Matrix.Symmetric','Mathlib.LinearAlgebra.Matrix.Trace'],'Short quadratic observations','Symmetric n-by-n matrices have n(n+1)/2 coordinates. Adjoining one constant coordinate makes the trace defect linear and yields a word witness of at most this length.',quad)
modules['Descent']=(['FiniteMonoidMortality.Compression','Mathlib.Tactic.Linarith'],'Quantitative sandwich rank descent','The word-length recurrence retains both outside words: L ↦ 2L + D. Starting from a singular generator saves one descent step.',body('FiniteMortalityDescent'))
modules['Main']=(['FiniteMonoidMortality.InvariantForms','FiniteMonoidMortality.QuadraticObservation','FiniteMonoidMortality.Descent'],'An exponential mortality bound for finite real matrix monoids','The entire word-product monoid is assumed finite and to contain zero. The generator indexing type need not be finite. The real theorem and rational specialization have the same explicit bound.',body('FiniteMortalityBound'))
entries=[]
for name,(imports,title,description,content) in modules.items():
 text='\n'.join('import '+i for i in imports)+'\n\nset_option autoImplicit false\n\n/-!\n# '+title+'\n\n'+description+'\n-/\n\nnoncomputable section\n\nopen scoped BigOperators\n\nnamespace '+ns+'\n\n'+renamed(content).strip()+'\n\nend '+ns+'\n'
 (dst/ns/f'{name}.lean').write_text(text)
 for match in re.finditer(r'(?m)^(?:@\[[^\n]*\] )?(?:private )?(?:def|abbrev|theorem) ([\w\u0080-\uffff]+)',content):
  old=match[1]
  entries.append({'old':'IndependentZeroBlocks.'+old,'new':ns+'.'+rename.get(old,old),'module':ns+'.'+name})
(dst/'Publication.lean').write_text('import FiniteMonoidMortality.Main\n')
(dst/'Audit.lean').write_text(renamed((src/'Audit.lean').read_text()))
for file in ['lean-toolchain','lake-manifest.json']:
 shutil.copy2(src/file,dst/file)
man=json.loads((dst/'lake-manifest.json').read_text());man['name']=ns;(dst/'lake-manifest.json').write_text(json.dumps(man,indent=2)+'\n')
(dst/'lakefile.toml').write_text('name = "FiniteMonoidMortality"\nversion = "1.1.0"\ndefaultTargets = ["Publication"]\n\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "v4.33.1"\n\n[[lean_lib]]\nname = "FiniteMonoidMortality"\n\n[[lean_lib]]\nname = "Publication"\n')
(args.report_dir/'declaration_map.json').write_text(json.dumps(entries,indent=2)+'\n')
print(json.dumps({'modules':len(modules),'declarations':len(entries),'lines':sum(len(p.read_text().splitlines()) for p in (dst/ns).glob('*.lean'))},indent=2))
