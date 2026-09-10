import FiniteMonoidMortality.MatrixRankScalarExtension
import FiniteMonoidMortality.MatrixWordScalarExtension
import FiniteMonoidMortality.MinimalRankCompression
import FiniteMonoidMortality.MinimumRankBound
import FiniteMonoidMortality.MortalityBudget

set_option autoImplicit false

namespace FiniteMonoidMortality

inductive WordGate (A : Type*) where
  | empty
  | input (a : A)
  | append (i j : ℕ)
  deriving DecidableEq

def wordGateEval {A : Type*} (v : List (List A)) : WordGate A → List A
  | .empty => []
  | .input a => [a]
  | .append i j => v.getD i [] ++ v.getD j []

def wordProgramEval {A : Type*} : List (WordGate A) → List (List A)
  | [] => []
  | g::p => let v := wordProgramEval p; wordGateEval v g :: v

def wordProgramRoot {A : Type*} (p : List (WordGate A)) : List A :=
  (wordProgramEval p).getD 0 []

def wordGateValue {A R : Type*} [Monoid R] (M : A → R) (v : List R) : WordGate A → R
  | .empty => 1
  | .input a => M a
  | .append i j => v.getD i 1 * v.getD j 1

def wordProgramValues {A R : Type*} [Monoid R] (M : A → R) : List (WordGate A) → List R
  | [] => []
  | g::p => let v := wordProgramValues M p; wordGateValue M v g :: v

def wordProgramValue {A R : Type*} [Monoid R] (M : A → R) (p : List (WordGate A)) : R :=
  (wordProgramValues M p).getD 0 1

theorem getD_map_default {X Y : Type*} (f : X → Y) (v : List X) (i : ℕ) (d : X) :
    (v.map f).getD i (f d)=f (v.getD i d) := by
  induction v generalizing i with
  | nil => simp
  | cons a v ih => cases i <;> simp_all

theorem wordProgramValues_correct {A R : Type*} [Monoid R]
    (M : A → R) (p : List (WordGate A)) :
    wordProgramValues M p=(wordProgramEval p).map (fun w => (w.map M).prod) := by
  induction p with
  | nil => rfl
  | cons g p ih =>
    simp only [wordProgramValues,wordProgramEval,List.map_cons,ih]
    congr 1
    cases g with
    | empty => rfl
    | input a => simp [wordGateValue,wordGateEval]
    | append i j =>
      change ((wordProgramEval p).map (fun w => (w.map M).prod)).getD i
          (([].map M).prod) *
        ((wordProgramEval p).map (fun w => (w.map M).prod)).getD j
          (([].map M).prod) = _
      rw [getD_map_default,getD_map_default]
      simp [wordGateEval,List.map_append,List.prod_append]

theorem wordProgramValue_correct {A R : Type*} [Monoid R]
    (M : A → R) (p : List (WordGate A)) :
    wordProgramValue M p=((wordProgramRoot p).map M).prod := by
  rw [wordProgramValue,wordProgramValues_correct]
  exact getD_map_default (fun w => (w.map M).prod) (wordProgramEval p) 0 []

def wordGateValid {A : Type*} (n : ℕ) : WordGate A → Prop
  | .empty => True
  | .input _ => True
  | .append i j => i<n ∧ j<n

def wordProgramValid {A : Type*} : List (WordGate A) → Prop
  | [] => True
  | g::p => wordGateValid p.length g ∧ wordProgramValid p

def extendProgramLetter {A : Type*} (p : List (WordGate A)) (a : A) : List (WordGate A) :=
  .append 1 0 :: .input a :: p

def extendProgram {A : Type*} (p : List (WordGate A)) : List A → List (WordGate A)
  | [] => p
  | a::w => extendProgram (extendProgramLetter p a) w

@[simp] theorem extendProgramLetter_root {A : Type*} (p : List (WordGate A)) (a : A) :
    wordProgramRoot (extendProgramLetter p a)=wordProgramRoot p++[a] := by
  simp [wordProgramRoot,extendProgramLetter,wordProgramEval,wordGateEval]

@[simp] theorem extendProgram_length {A : Type*} (p : List (WordGate A)) (w : List A) :
    (extendProgram p w).length=2*w.length+p.length := by
  induction w generalizing p with
  | nil => simp [extendProgram]
  | cons a w ih => simp [extendProgram,ih,extendProgramLetter]; omega

@[simp] theorem extendProgram_root {A : Type*} (p : List (WordGate A)) (w : List A) :
    wordProgramRoot (extendProgram p w)=wordProgramRoot p++w := by
  induction w generalizing p with
  | nil => simp [extendProgram]
  | cons a w ih => simp [extendProgram,ih,List.append_assoc]

theorem extendProgram_valid {A : Type*} (p : List (WordGate A))
    (hp : wordProgramValid p) (hne : 0<p.length) (w : List A) :
    wordProgramValid (extendProgram p w) := by
  induction w generalizing p with
  | nil => exact hp
  | cons a w ih =>
    apply ih
    · simp [extendProgramLetter,wordProgramValid,wordGateValid,hp]; omega
    · simp [extendProgramLetter]

theorem extendProgram_old_value {A : Type*} (p : List (WordGate A)) (w : List A) (j : ℕ) :
    (wordProgramEval (extendProgram p w)).getD (2*w.length+j) []=
      (wordProgramEval p).getD j [] := by
  induction w generalizing p j with
  | nil => simp [extendProgram]
  | cons a w ih =>
    rw [show 2*(a::w).length+j=2*w.length+(j+2) by simp; omega]
    rw [extendProgram,ih]
    simp [extendProgramLetter,wordProgramEval,show j+2=(j+1)+1 from rfl]

def sandwichProgram {A : Type*} (p : List (WordGate A)) (w : List A) : List (WordGate A) :=
  .append 0 (2*w.length) :: extendProgram p w

@[simp] theorem sandwichProgram_root {A : Type*} (p : List (WordGate A)) (w : List A) :
    wordProgramRoot (sandwichProgram p w)=wordProgramRoot p++w++wordProgramRoot p := by
  change wordProgramRoot (extendProgram p w) ++
    (wordProgramEval (extendProgram p w)).getD (2*w.length) [] = _
  rw [extendProgram_root]
  simpa [wordProgramRoot] using congrArg (fun X => wordProgramRoot p++w++X)
    (extendProgram_old_value p w 0)

@[simp] theorem sandwichProgram_length {A : Type*} (p : List (WordGate A)) (w : List A) :
    (sandwichProgram p w).length=p.length+2*w.length+1 := by
  simp [sandwichProgram]; omega

theorem sandwichProgram_valid {A : Type*} (p : List (WordGate A))
    (hp : wordProgramValid p) (hne : 0<p.length) (w : List A) :
    wordProgramValid (sandwichProgram p w) := by
  constructor
  · change 0<(extendProgram p w).length ∧ 2*w.length<(extendProgram p w).length
    rw [extendProgram_length]; omega
  · exact extendProgram_valid p hp hne w

def mortalitySLPGateBound (n : ℕ) : ℕ := 1+n*(2*(1+n*(n+1)/2)+1)

theorem mortalitySLPGateBound_le_cubic (n : ℕ) :
    mortalitySLPGateBound n ≤ n^3+n^2+3*n+1 := by
  have hh := Nat.mul_div_le (n*(n+1)) 2
  unfold mortalitySLPGateBound
  nlinarith [Nat.mul_le_mul_left n hh]

theorem exists_minimum_rank_slp_real_of_finite
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hf : (Set.range (matrixWord M)).Finite) :
    ∃ p : List (WordGate A), wordProgramValid p ∧ 0<p.length ∧
      (∀ v, (matrixWord M (wordProgramRoot p)).rank ≤ (matrixWord M v).rank) ∧
      (wordProgramRoot p).length ≤ minimumRankBound n (matrixWord M (wordProgramRoot p)).rank ∧
      p.length ≤ mortalitySLPGateBound n := by
  classical
  obtain ⟨z,hmin,_⟩ := exists_minimum_rank_word_real_of_finite M hf
  let s := (matrixWord M z).rank
  let C := 2*(1+n*(n+1)/2)+1
  have aux : ∀ r, ∀ p : List (WordGate A), wordProgramValid p → 0<p.length →
      (matrixWord M (wordProgramRoot p)).rank=r →
      (wordProgramRoot p).length ≤ mortalityBudget n (n-r) →
      p.length ≤ 1+(n-r)*C →
      ∃ q : List (WordGate A), wordProgramValid q ∧ 0<q.length ∧
        (matrixWord M (wordProgramRoot q)).rank=s ∧
        (wordProgramRoot q).length ≤ mortalityBudget n (n-s) ∧
        q.length ≤ 1+(n-s)*C := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro p hp hne hr hl hg
      by_cases he : r=s
      · exact ⟨p,hp,hne,hr.trans he,by simpa [he] using hl,by simpa [he] using hg⟩
      · have hsr : s<r := by have := hmin (wordProgramRoot p); dsimp [s] at *; omega
        have hrn : r≤n := by simpa [hr] using Matrix.rank_le_card_width (matrixWord M (wordProgramRoot p))
        obtain ⟨w,hw,hd⟩ := exists_rank_sensitive_sandwich_below_word M hf (wordProgramRoot p)
          ⟨z,by simpa [hr] using hsr⟩
        let q := sandwichProgram p w
        let r' := (matrixWord M (wordProgramRoot q)).rank
        have hdrop : r'<r := by simpa [r',q,hr] using hd
        apply ih r' hdrop q (sandwichProgram_valid p hp hne w) (by simp [q]) rfl
        · have hs : (wordProgramRoot q).length ≤ mortalityBudget n (n-r+1) := by
            rw [mortalityBudget]
            rw [show n-(n-r)=r by omega,rankTriangle_eq,rankTriangle_eq]
            simp only [q,sandwichProgram_root,List.length_append]
            rw [hr] at hw
            omega
          exact hs.trans (mortalityBudget_mono n (by omega))
        · have hwc : 2*w.length+1 ≤ C := by dsimp [C]; omega
          have hg' : q.length ≤ 1+(n-r+1)*C := by
            simp only [q,sandwichProgram_length]
            rw [Nat.add_mul]
            omega
          exact hg'.trans (Nat.add_le_add_left
            (Nat.mul_le_mul_right C (by omega : n-r+1 ≤ n-r')) 1)
  obtain ⟨p,hp,hn,hr,hl,hg⟩ := aux n [.empty] (by trivial) (by simp)
    (by simp [wordProgramRoot,wordProgramEval,wordGateEval,matrixWord,Matrix.rank_one])
    (by simp [wordProgramRoot,wordProgramEval,wordGateEval,mortalityBudget]) (by simp)
  have hsn : s≤n := by simpa [s] using Matrix.rank_le_card_width (matrixWord M z)
  refine ⟨p,hp,hn,fun v => hr ▸ hmin v,?_,?_⟩
  · rw [hr]
    simpa [mortalityBudget_at_minimum n s hsn] using hl
  · exact hg.trans (Nat.add_le_add_left (Nat.mul_le_mul_right C (Nat.sub_le n s)) 1)

theorem exists_minimum_rank_slp_rational_of_finite
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℚ)
    (hf : (Set.range (matrixWord M)).Finite) :
    ∃ p : List (WordGate A), wordProgramValid p ∧ 0<p.length ∧
      (∀ v, (matrixWord M (wordProgramRoot p)).rank ≤ (matrixWord M v).rank) ∧
      (wordProgramRoot p).length ≤ minimumRankBound n (matrixWord M (wordProgramRoot p)).rank ∧
      p.length ≤ mortalitySLPGateBound n := by
  let f : ℚ →+* ℝ := Rat.castHom ℝ
  let MR := fun a => (M a).map f
  have hr (w : List A) : (matrixWord MR w).rank=(matrixWord M w).rank := by
    rw [matrixWord_map f M w]
    exact matrix_rank_map_field f _
  obtain ⟨p,hp,hn,hm,hl,hg⟩ := exists_minimum_rank_slp_real_of_finite MR
    (finite_matrixWord_range_map f M hf)
  exact ⟨p,hp,hn,fun v => by simpa [hr] using hm v,by simpa [hr] using hl,hg⟩

end FiniteMonoidMortality
