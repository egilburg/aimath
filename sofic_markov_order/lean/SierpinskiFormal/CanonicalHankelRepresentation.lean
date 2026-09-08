import SierpinskiFormal.SoficProcessMarkov

set_option autoImplicit false
noncomputable section
namespace IndependentZeroBlocks
open MeasureTheory

variable {K A : Type*} [Field K]

def hankelColumn (p : List A → K) (w : List A) : List A → K := fun u => p (u ++ w)

def contextShift (a : A) : Module.End K (List A → K) :=
  LinearMap.pi fun u => LinearMap.proj (u ++ [a])

theorem contextShift_column (p : List A → K) (a : A) (w : List A) :
    contextShift a (hankelColumn p w) = hankelColumn p (a :: w) := by
  ext u; simp [contextShift, hankelColumn, List.append_assoc]

theorem contextShift_invariant (p : List A → K) (a : A)
    (x : List A → K) (hx : x ∈ wordHankelSpan p) : contextShift a x ∈ wordHankelSpan p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      change contextShift a (hankelColumn p w) ∈ _
      rw [contextShift_column]
      exact Submodule.subset_span ⟨a :: w, rfl⟩
  | zero => simpa using (wordHankelSpan p).zero_mem
  | add x y hx hy ihx ihy => simpa using (wordHankelSpan p).add_mem ihx ihy
  | smul c x hx ih => simpa using (wordHankelSpan p).smul_mem c ih

def hankelLetter (p : List A → K) (a : A) : Module.End K (wordHankelSpan p) :=
  (contextShift a).restrict (contextShift_invariant p a)

def hankelInitial (p : List A → K) : wordHankelSpan p :=
  ⟨hankelColumn p [], Submodule.subset_span ⟨[], rfl⟩⟩

def hankelRow (p : List A → K) : Module.Dual K (wordHankelSpan p) :=
  (LinearMap.proj []).comp (wordHankelSpan p).subtype

theorem hankelWord_apply (p : List A → K) (w : List A) (x : wordHankelSpan p) (u : List A) :
    (linearWord (hankelLetter p) w x).val u = x.val (u ++ w) := by
  induction w generalizing x u with
  | nil => simp [linearWord]
  | cons a w ih =>
      change (linearWord (hankelLetter p) w x).val ((u ++ [a])) = _
      rw [ih]
      simp [List.append_assoc]

theorem hankel_represents (p : List A → K) :
    representedWord (hankelLetter p) (hankelRow p) (hankelInitial p) = p := by
  funext w
  change (linearWord (hankelLetter p) w (hankelInitial p)).val [] = p w
  rw [hankelWord_apply]
  simp [hankelInitial, hankelColumn]

theorem hankel_reduced (p : List A → K) :
    WordReduced (hankelLetter p) (hankelRow p) (hankelInitial p) := by
  constructor
  · have hword (w : List A) :
        (linearWord (hankelLetter p) w (hankelInitial p)).val = hankelColumn p w := by
      funext u
      rw [hankelWord_apply]
      simp [hankelInitial, hankelColumn]
    have he : (linearReachableSpan (hankelLetter p) (hankelInitial p)).map
        (wordHankelSpan p).subtype = wordHankelSpan p := by
      rw [linearReachableSpan, linearOrbit, Submodule.map_span, ← Set.range_comp]
      change Submodule.span K (Set.range (fun w =>
        (linearWord (hankelLetter p) w (hankelInitial p)).val)) = _
      simp_rw [hword]
      rfl
    apply top_unique
    intro x _
    have hx : x.val ∈ (linearReachableSpan (hankelLetter p) (hankelInitial p)).map
        (wordHankelSpan p).subtype := by rw [he]; exact x.property
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hx
    have hxy : y = x := Subtype.ext heq
    rwa [hxy] at hy
  · intro x hx
    apply Subtype.ext
    funext u
    have h := hx u
    change (linearWord (hankelLetter p) u x).val [] = 0 at h
    simpa [hankelWord_apply] using h

theorem wordHankelSpan_finiteDimensional_of_representation
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : A → Module.End K V) (l : Module.Dual K V) (g : V) :
    FiniteDimensional K (wordHankelSpan (representedWord T l g)) := by
  rw [wordHankelSpan_eq_map_reachable]
  infer_instance

/-- The upper bound needs only finite intrinsic Hankel dimension; a reduced
presentation is constructed internally from the actual cylinder probabilities. -/
theorem stationary_process_markov_cutoff_of_finite_hankel
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure (ℕ → A)) [IsProbabilityMeasure μ]
    (hstationary : MeasurePreserving digitShift μ μ)
    [FiniteDimensional ℝ (wordHankelSpan (fun w => μ.real (wordCylinder w)))]
    (hfinite : ∃ k, ProcessMarkov μ k) :
    ProcessMarkov μ ((Module.finrank ℝ
      (wordHankelSpan (fun w => μ.real (wordCylinder w)))).choose 2) := by
  let p := fun w => μ.real (wordCylinder w)
  exact stationary_process_markov_cutoff_hankel μ hstationary
    (hankelLetter p) (hankelRow p) (hankelInitial p)
    (fun w => congrFun (hankel_represents p).symm w) (hankel_reduced p) hfinite

/-- Any finite linear presentation supplies the finite-Hankel hypothesis; no
minimality hypothesis is left for the caller to prove. -/
theorem stationary_process_markov_cutoff_of_representation
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure (ℕ → A)) [IsProbabilityMeasure μ]
    (hstationary : MeasurePreserving digitShift μ μ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (T : A → Module.End ℝ V) (l : Module.Dual ℝ V) (g : V)
    (hrep : ∀ w, μ.real (wordCylinder w) = representedWord T l g w)
    (hfinite : ∃ k, ProcessMarkov μ k) :
    ProcessMarkov μ ((Module.finrank ℝ
      (wordHankelSpan (fun w => μ.real (wordCylinder w)))).choose 2) := by
  haveI : FiniteDimensional ℝ (wordHankelSpan (fun w => μ.real (wordCylinder w))) := by
    rw [funext hrep]
    exact wordHankelSpan_finiteDimensional_of_representation T l g
  exact stationary_process_markov_cutoff_of_finite_hankel μ hstationary hfinite

end IndependentZeroBlocks
