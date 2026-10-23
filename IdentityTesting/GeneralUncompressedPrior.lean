import IdentityTesting.GeneralLowerSeparation
import IdentityTesting.SortedPairing
import IdentityTesting.DominantTilt
import IdentityTesting.FiniteCoupling

/-! The two displacement cases produce an actual common-form prior before
deletion and empirical compression. -/

noncomputable section
namespace IdentityTesting.GeneralLowerGeometry
open scoped BigOperators
open Classical
open FiniteTesting SortedPairing SignedDiagonalMoment DominantTilt

theorem exists_general_uncompressed_prior {k : ℕ}
    (q : Probability (Fin k)) (x : Fin k → ℝ) (T : ℝ)
    (hT : 0 < T) (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hcap : ∀ i, q.mass i ≤ (4 : ℝ) / 5)
    (hgeom : ∀ i j, q.mass i ≤ q.mass j → q.mass i * x i ≤ q.mass j * x j)
    (hbudget : T ^ 2 * (∑ i, (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * T) :
    ∃ (ν : (Fin (pairCount q.mass (lowCoords x)) → Bool) → Probability (Fin k)) (f : ℝ),
      1 ≤ f ∧ f ≤ 3 ∧
      (∀ σ i, i ∈ highCoords x → (ν σ).mass i = f * q.mass i) ∧
      (∀ σ, (∑ i ∈ lowCoords x, min ((ν σ).mass i) (q.mass i)) ≤
        (∑ i ∈ lowCoords x, q.mass i) - 2 * lowDisplacement q.mass x) ∧
      FiniteTesting.totalVariation
        (mixture (uniformSigns (pairCount q.mass (lowCoords x))) (fun σ => productLaw (ν σ) n))
        (productLaw q n) < 1 / (10 : ℝ) ^ 5 := by
  have hsmall : ∀ i ∈ lowCoords x, x i ≤ (1 : ℝ) / 8 :=
    fun i hi => (mem_lowCoords x i).mp hi
  by_cases hmax : ∀ i ∈ lowCoords x, q.mass i * x i ≤
      (∑ j ∈ lowCoords x, q.mass j * x j) / 2
  · let ν := sortedPairedLaw q x (lowCoords x) (fun i => (hx i).1) hsmall
    refine ⟨ν, 1, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro σ i hi
      simpa only [one_mul] using sortedPairedLaw_mass_outside q x (lowCoords x)
        (fun i => (hx i).1) hsmall σ i (Finset.mem_compl.mp hi)
    · intro σ
      have heq := overlap_on_changed_set (ν σ) q (lowCoords x)
        (sortedPairedLaw_mass_outside q x (lowCoords x) (fun i => (hx i).1) hsmall σ)
      have htv := sortedPairedLaw_totalVariation_ge q x (lowCoords x)
        (fun i => (hx i).1) hsmall hgeom hmax σ
      change 2 * lowDisplacement q.mass x ≤ _ at htv
      linarith
    · exact (sortedPairedLaw_sample_totalVariation_lt q x (lowCoords x)
        (fun i => (hx i).1) hsmall hT hq (fun i => (hx i).2) hbudget n hn).trans
          (by norm_num)
  · obtain ⟨i, ν, f, hi, hf1, hf3, _, _, hmass, hoverlap, _, htv⟩ :=
      exists_tilt_of_dominant_displacement q x (lowCoords x) hT hq hx hcap hsmall hbudget hmax
    refine ⟨fun _ => ν, f, hf1, hf3, ?_, ?_, ?_⟩
    · intro σ j hj
      apply hmass j
      intro hji
      subst j
      exact (Finset.mem_compl.mp hj) hi
    · intro σ
      exact hoverlap.le
    · simpa only [mixture_constant] using htv n hn

end IdentityTesting.GeneralLowerGeometry
