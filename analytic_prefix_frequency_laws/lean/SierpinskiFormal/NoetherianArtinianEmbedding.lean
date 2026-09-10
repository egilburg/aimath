import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! # A faithful Artinian target for finite Noetherian coefficient data

The primary quotients must precede localization. The resulting map is
injective, but no flatness or preservation of module images is asserted.
-/

noncomputable section
namespace IndependentZeroBlocks

theorem primaryQuotient_bot_isPrimary
    {R : Type*} [CommRing R] (Q : Ideal R) (hQ : Q.IsPrimary) :
    (⊥ : Ideal (R ⧸ Q)).IsPrimary := by
  rw [Ideal.isPrimary_iff]
  refine ⟨?_, ?_⟩
  · intro ht
    have h1 : (1 : R ⧸ Q) = 0 := by
      have : (1 : R ⧸ Q) ∈ (⊥ : Ideal (R ⧸ Q)) := by rw [ht]; trivial
      exact this
    have : (1 : R) ∈ Q := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      simpa using h1
    exact hQ.1 ((Ideal.eq_top_iff_one Q).mpr this)
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hab : a * b ∈ Q := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      simpa using hxy
    rcases (Ideal.isPrimary_iff.mp hQ).2 hab with ha | hb
    · left
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr ha
    · right
      obtain ⟨n, hn⟩ := hb
      exact ⟨n, by simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr hn⟩

theorem primaryZero_localization_injective
    {R : Type*} [CommRing R] (hR : (⊥ : Ideal R).IsPrimary) :
    letI : (nilradical R).IsPrime := Ideal.isPrime_radical hR
    Function.Injective (algebraMap R (Localization.AtPrime (nilradical R))) := by
  letI : (nilradical R).IsPrime := Ideal.isPrime_radical hR
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (nilradical R).primeCompl
    (Localization.AtPrime (nilradical R)) x).mp hx
  rcases (Ideal.isPrimary_iff.mp hR).2 (show x * (s : R) ∈ (⊥ : Ideal R) by
    simpa [mul_comm] using hs) with h | h
  · exact h
  · exact False.elim (s.property h)

theorem primaryZero_localization_isArtinian
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (hR : (⊥ : Ideal R).IsPrimary) :
    letI : (nilradical R).IsPrime := Ideal.isPrime_radical hR
    IsArtinianRing (Localization.AtPrime (nilradical R)) := by
  letI : (nilradical R).IsPrime := Ideal.isPrime_radical hR
  have hp : nilradical R ∈ minimalPrimes R := by
    refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
    intro J hJ _
    letI := hJ.1
    exact nilradical_le_prime J
  letI : IsNoetherianRing (Localization.AtPrime (nilradical R)) :=
    IsLocalization.isNoetherianRing (nilradical R).primeCompl _ inferInstance
  letI := Ring.KrullDimLE.of_isLocalization (nilradical R) hp
    (Localization.AtPrime (nilradical R))
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

universe u

/-- An injective map into an Artinian ring of the same universe. No assertion
about flatness, freeness of image modules, or effectivity is part of this data. -/
structure FaithfulArtinianTarget (R : Type u) [CommRing R] where
  Carrier : Type u
  [commRing : CommRing Carrier]
  [artinian : IsArtinianRing Carrier]
  toRingHom : R →+* Carrier
  injective : Function.Injective toRingHom

attribute [instance] FaithfulArtinianTarget.commRing FaithfulArtinianTarget.artinian

/-- The quotient by a primary ideal embeds in its localization at the
nilradical. Localizing the quotient preserves its nilpotents. -/
def primaryQuotientArtinianTarget
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (Q : Ideal R) (hQ : Q.IsPrimary) : FaithfulArtinianTarget (R ⧸ Q) := by
  have h := primaryQuotient_bot_isPrimary Q hQ
  letI : (nilradical (R ⧸ Q)).IsPrime := Ideal.isPrime_radical h
  letI := primaryZero_localization_isArtinian h
  exact ⟨Localization.AtPrime (nilradical (R ⧸ Q)),
    algebraMap (R ⧸ Q) _, primaryZero_localization_injective h⟩

/-- Every commutative Noetherian ring embeds in a finite product of
Artinian localizations of primary quotients. -/
theorem exists_faithfulArtinianTarget
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Nonempty (FaithfulArtinianTarget R) := by
  classical
  obtain ⟨s, hs, hprimary⟩ := Submodule.isLasker R R (⊥ : Ideal R)
  let T : (i : s) → FaithfulArtinianTarget (R ⧸ i.1) :=
    fun i ↦ primaryQuotientArtinianTarget i.1 (hprimary i.2)
  let φ : ∀ i : s, R →+* (T i).Carrier :=
    fun i ↦ (T i).toRingHom.comp (Ideal.Quotient.mk i.1)
  refine ⟨⟨(i : s) → (T i).Carrier, Pi.ringHom φ, ?_⟩⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hm : x ∈ s.inf id := by
    simp only [Finset.inf_eq_iInf, Ideal.mem_iInf]
    intro Q hQ
    let i : s := ⟨Q, hQ⟩
    have hi : φ i x = 0 := congrFun hx i
    have hz : Ideal.Quotient.mk Q x = 0 :=
      (T i).injective (by simpa [φ] using hi)
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hz
  rw [hs] at hm
  exact hm

end IndependentZeroBlocks
