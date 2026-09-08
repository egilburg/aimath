import SierpinskiFormal.CanonicalHankelRepresentation
import SierpinskiFormal.SoficSharpProcess
import SoficMarkovOrder.CanonicalHankel
import SoficMarkovOrder.SharpProcess
import Lean

/-!
Comparison-only audit; the old public package is an external input.
Build the old package and current package with their pinned Lean toolchain.
From the current lean/ directory, prepend OLD/lean/.lake/build/lib/lean to
LEAN_PATH and execute `lake env lean ../verification/SemanticComparison.lean`.
The imported old package is not required to build the current proof.

The four theorem types are compared after the explicit namespace/identifier
renaming. Every old-package constant in those types is traversed through its
type and definition body; constructors of inductive types are also checked.
Theorem proof bodies are not required to coincide: both developments are
independently kernel checked. Definition bodies are required to coincide.
-/

open Lean Elab Command

namespace RefactorComparison

def renamePart (s : String) : String :=
  s.replace "IndependentZeroBlocks" "SoficMarkovOrder"
   |>.replace "digitShift" "sequenceShift"
   |>.replace "digitHead" "sequenceHead"
   |>.replace "stationaryPrefix" "orbitPrefix"
   |>.replace "soficPairChain" "pairChain"
   |>.replace "sourceSelectorWeights" "selectorWeight"
   |>.replace "_digit_eq_ofFn" "_sequence_eq_ofFn"
   |>.replace "integral_comp_orbitPrefix_digit" "integral_comp_orbitPrefix_sequence"

def renameName : Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (renameName p) (renamePart s)
  | .num p n => .num (renameName p) n

partial def renameExpr (e : Expr) : Expr := e.replace fun
  | .const n us => some (.const (renameName n) us)
  | .proj n i v => some (.proj (renameName n) i (renameExpr v))
  | _ => none

def isOld (n : Name) : Bool := (`IndependentZeroBlocks).isPrefixOf n

partial def checkConstant (n : Name) (seen : NameSet) : CommandElabM NameSet := do
  if seen.contains n then return seen
  let mut seen := seen.insert n
  let old ← getConstInfo n
  let newName := renameName n
  let new ← getConstInfo newName
  unless renameExpr old.type == new.type do
    throwError "TYPE MISMATCH: {n} -> {newName}\nold renamed: {renameExpr old.type}\nnew: {new.type}"
  let mut dependencies := old.type.getUsedConstants
  match old.value? with
  | some v =>
    match new.value? with
    | some w =>
      unless renameExpr v == w do
        throwError "BODY MISMATCH: {n} -> {newName}\nold renamed: {renameExpr v}\nnew: {w}"
      dependencies := dependencies ++ v.getUsedConstants
    | none => throwError "Missing definition body: {newName}"
  | none => pure ()
  match old with
  | .inductInfo i => dependencies := dependencies ++ i.ctors.toArray
  | _ => pure ()
  logInfo m!"MATCH {n} -> {newName}: type; definition body when present"
  for d in dependencies do
    if isOld d then seen ← checkConstant d seen
  return seen

run_cmd do
  let roots := #[
    `IndependentZeroBlocks.stationary_process_markov_cutoff_of_finite_hankel,
    `IndependentZeroBlocks.stationary_process_markov_cutoff_of_representation,
    `IndependentZeroBlocks.exists_rational_sharp_sofic_process,
    `IndependentZeroBlocks.processMarkov_iff_rankOne]
  let mut seen : NameSet := {}
  for n in roots do seen ← checkConstant n seen
  logInfo m!"PASS: {roots.size} endpoint types and {seen.size} total custom declarations matched under explicit renaming."

end RefactorComparison
