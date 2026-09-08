from pathlib import Path
import re,json,hashlib,argparse
parser=argparse.ArgumentParser(description='Reproduce the original mortality specifications for kernel-checked refactor compatibility.')
parser.add_argument('original_lean_root',type=Path)
parser.add_argument('refactored_lean_root',type=Path)
args=parser.parse_args()
old=args.original_lean_root/'SierpinskiFormal'
new=args.refactored_lean_root
s=(old/'FiniteMortalityBound.lean').read_text()
endpoints=['exists_short_zero_word_of_finite_real_monoid','exists_short_zero_word_of_finite_rational_monoid','exists_short_rank_decreasing_sandwich_of_finite']
text='''import Publication

set_option autoImplicit false

/-!
# Compatibility with the previously released claims

Each statement below is copied from the original paper package, with its
original matrix-word and bound definitions reproduced transparently here.
Lean checks that the refactored endpoint inhabits exactly that statement.
Only the namespace changes; no original proof modules are imported.
-/

namespace PublishedSpecification

variable {F A ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

def matrixWord (M : A → Matrix ι ι F) (w : List A) : Matrix ι ι F :=
  (w.map M).prod

def finiteMortalityBound (n : ℕ) : ℕ :=
  2 ^ (n - 1) + (2 ^ (n - 1) - 1) * (n * (n + 1) / 2)

'''
for name in endpoints:
 header=re.search(r'(?m)^theorem '+name+r'\b[\s\S]*?(?= := by)',s)[0]
 text+=header+' := by\n  exact FiniteMonoidMortality.'+name+' '+('hn M hfinite hzero' if name!=endpoints[-1] else 'M hfinite hzero h hh')+'\n\n'
text+='end PublishedSpecification\n\n'
for name in endpoints:
 text+='#print axioms PublishedSpecification.'+name+'\n'
(new/'Specification.lean').write_text(text)
print('Wrote original-statement compatibility checks for',len(endpoints),'endpoints.')
