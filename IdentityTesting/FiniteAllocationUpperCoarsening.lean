import IdentityTesting.FiniteAllocationUpperOverlap
import IdentityTesting.CountablePooling

/-! The coarse reference test is obtained by an actual deterministic sample
map and the already constructed full-prefix test, retaining zero-mass labels. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteAllocationUpper
open FiniteTesting FiniteIID ProfileTesting

universe u v
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def collapseMap (H : Finset Ω) (i : Ω) : Option Ω := if i ∈ H then some i else none

def collapseLaw (p : Probability Ω) (H : Finset Ω) : Probability (Option Ω) :=
  mapLaw p (collapseMap H)

omit [Fintype Ω] in
theorem collapseMap_eq_some (H : Finset Ω) (i j : Ω) :
    collapseMap H i = some j ↔ i = j ∧ j ∈ H := by
  by_cases hi : i ∈ H
  · simp [collapseMap, hi]
    intro h
    simpa [h] using hi
  · simp only [collapseMap, if_neg hi, reduceCtorEq, false_iff, not_and]
    intro h
    simpa [h] using hi

theorem collapseLaw_mass_some (p : Probability Ω) (H : Finset Ω) (i : Ω) :
    (collapseLaw p H).mass (some i) = if i ∈ H then p.mass i else 0 := by
  classical
  rw [collapseLaw, mapLaw_mass]
  simp only [collapseMap_eq_some]
  by_cases hi : i ∈ H <;> simp [hi]

theorem collapseLaw_mass_none (p : Probability Ω) (H : Finset Ω) :
    (collapseLaw p H).mass none = ∑ i ∈ Finset.univ \ H, p.mass i := by
  classical
  rw [collapseLaw, mapLaw_mass]
  have heq : Finset.univ \ H = Finset.univ.filter (fun i => i ∉ H) := by
    ext i
    simp
  rw [heq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i ∈ H <;> simp [collapseMap, h]

def mappedTest {Ξ : Type v} (f : Ω → Ξ) (test : FiniteTesting.RandomizedTest Ξ) : FiniteTesting.RandomizedTest Ω where
  reject i := test.reject (f i)
  nonneg _ := test.nonneg _
  le_one _ := test.le_one _

omit [DecidableEq Ω] in
theorem expectation_mappedTest {Ξ : Type v} [Fintype Ξ] (p : Probability Ω)
    (f : Ω → Ξ) (test : FiniteTesting.RandomizedTest Ξ) :
    expectation p (mappedTest f test) = expectation (mapLaw p f) test := by
  classical
  rw [mapLaw, expectation_mixture]
  simp [expectation, pointLaw, mappedTest]

theorem expectation_collapse_sample (p : Probability Ω) (H : Finset Ω) (n : ℕ)
    (test : FiniteTesting.RandomizedTest (Fin n → Option Ω)) :
    expectation (productLaw p n) (mappedTest (fun sample => collapseMap H ∘ sample) test) =
      expectation (productLaw (collapseLaw p H) n) test := by
  rw [expectation_mappedTest, mapLaw_productLaw]
  rfl

theorem collapseLaw_weightSum (q : Probability Ω) (H : Finset Ω) :
    weightSum (collapseLaw q H) none = ∑ i ∈ H, q.mass i ^ ((2 : ℝ) / 3) := by
  classical
  have hs := Finset.sum_erase_add (s := (Finset.univ : Finset (Option Ω)))
    (f := fun i => (collapseLaw q H).mass i ^ ((2 : ℝ) / 3)) (Finset.mem_univ none)
  rw [Fintype.sum_option] at hs
  have heq : (∑ i : Ω, (collapseLaw q H).mass (some i) ^ ((2 : ℝ) / 3)) =
      ∑ i ∈ H, q.mass i ^ ((2 : ℝ) / 3) := by
    have hfun : ∀ i : Ω, (collapseLaw q H).mass (some i) ^ ((2 : ℝ) / 3) =
        if i ∈ H then q.mass i ^ ((2 : ℝ) / 3) else 0 := by
      intro i
      rw [collapseLaw_mass_some]
      split <;> norm_num
    simp_rw [hfun]
    simp
  unfold weightSum tailLabels powerWeight
  rw [heq] at hs
  linarith

theorem collapseLaw_overlap (p q : Probability Ω) (H : Finset Ω) :
    (∑ i : Option Ω, min ((collapseLaw p H).mass i) ((collapseLaw q H).mass i)) =
      min (∑ i ∈ Finset.univ \ H, p.mass i) (∑ i ∈ Finset.univ \ H, q.mass i) +
        localOverlap p q H := by
  rw [Fintype.sum_option, collapseLaw_mass_none, collapseLaw_mass_none]
  congr 1
  simp only [collapseLaw_mass_some]
  have hfun : (fun i => min (if i ∈ H then p.mass i else 0)
      (if i ∈ H then q.mass i else 0)) =
      (fun i => if i ∈ H then min (p.mass i) (q.mass i) else 0) := by
    funext i
    split <;> simp_all
  rw [hfun]
  simp [localOverlap]

theorem totalVariation_collapse_identity (p q : Probability Ω) (H : Finset Ω) :
    FiniteTesting.totalVariation p q = FiniteTesting.totalVariation (collapseLaw p H) (collapseLaw q H) +
      min (∑ i ∈ Finset.univ \ H, p.mass i) (∑ i ∈ Finset.univ \ H, q.mass i) -
        localOverlap p q (Finset.univ \ H) := by
  rw [finite_totalVariation_eq_one_sub_overlap, finite_totalVariation_eq_one_sub_overlap,
    collapseLaw_overlap]
  have hs := Finset.sum_sdiff (f := fun i => min (p.mass i) (q.mass i)) (Finset.subset_univ H)
  dsimp [localOverlap]
  linarith

theorem exists_coarse_test (q : Probability Ω) (H : Finset Ω) (N : ℕ) (hN : 1 ≤ N) :
    ∃ test : FiniteTesting.RandomizedTest (Fin N → Ω),
      expectation (productLaw q N) test ≤ 1 / 100 ∧
      ∀ p : Probability Ω,
        60000 * (1 / (N : ℝ) + (∑ i ∈ H, q.mass i ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 4) /
          Real.sqrt N) < FiniteTesting.totalVariation (collapseLaw p H) (collapseLaw q H) →
        1 - expectation (productLaw p N) test ≤ 1 / 100 := by
  obtain ⟨test, hnull, halt⟩ := fullPrefix_identity_test (collapseLaw q H) none N hN
  refine ⟨mappedTest (fun sample => collapseMap H ∘ sample) test, ?_, ?_⟩
  · rw [expectation_collapse_sample]
    exact hnull
  · intro p hp
    rw [expectation_collapse_sample]
    apply halt (collapseLaw p H)
    simpa only [profileRadius, collapseLaw_weightSum] using hp

end IdentityTesting.FiniteAllocationUpper
