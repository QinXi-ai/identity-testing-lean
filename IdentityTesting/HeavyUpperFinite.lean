import IdentityTesting.HeavyUpperAssembly
import IdentityTesting.HeavyUpperFiniteBridge
import IdentityTesting.HeavyUpperEmbedding
import IdentityTesting.HeavyRelabelingLowerBound

/-! Original-model heavy upper bound with internally constructed optimizer
coordinates, for a finite positive reference with its head in position zero. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyUpper
open Classical FiniteTesting FiniteAllocationUpper HeavySignedFamily

theorem finite_pooled_tail_mass_none {k : ℕ} (q : Probability (Fin k)) (a : Fin k) :
    (tailWeights (pooledLaw (extendFiniteLaw q) (Finset.range k))
      (some (rangeIndexEquiv k a))).mass none = 0 := by
  simp [tailWeights, finite_pooled_mass_none]

theorem finite_pooled_tail_mass_some {k : ℕ} (q : Probability (Fin k)) (a : Fin k)
    (i : {i : ℕ // i ∈ Finset.range k}) :
    (tailWeights (pooledLaw (extendFiniteLaw q) (Finset.range k))
      (some (rangeIndexEquiv k a))).mass (some i) =
      (tailWeights q a).mass ((rangeIndexEquiv k).symm i) := by
  simp only [tailWeights, Option.some.injEq, finite_pooled_mass_some, Equiv.symm_apply_eq]

theorem finite_pooled_tail_coordinate_sum {k : ℕ} (q : Probability (Fin k))
    (a : Fin k) (x : Fin k → ℝ) (f : ℝ → ℝ) :
    (∑ z : PoolLabel (Finset.range k),
      (tailWeights (pooledLaw (extendFiniteLaw q) (Finset.range k))
        (some (rangeIndexEquiv k a))).mass z * f (pooledCoordinate x z)) =
        ∑ i, (tailWeights q a).mass i * f (x i) := by
  rw [Fintype.sum_option, finite_pooled_tail_mass_none, zero_mul, zero_add]
  simp only [finite_pooled_tail_mass_some, pooledCoordinate]
  exact (rangeIndexEquiv k).symm.sum_comp (fun i => (tailWeights q a).mass i * f (x i))

theorem finite_heavy_upper_bound_of_kkt {k : ℕ} (q : Probability (Fin k))
    (a : Fin k) (x : Fin k → ℝ) (T β ε g : ℝ)
    (hT : 4 ≤ T) (hβ : 0 < β) (hg : 0 ≤ g) (hTg : 1 ≤ T * g)
    (hrscale : Real.sqrt (1 - q.mass a) ≤ g * Real.sqrt T)
    (ha : x a = 1) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, (tailWeights q a).mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, (tailWeights q a).mass i * x i * (1 - x i ^ 4))
    (hradius : (∑ i, (tailWeights q a).mass i * x i) + g = ε) :
    ∃ n : ℕ, HasIdentityTest (extendFiniteLaw q) ε n ∧
      (n : ℝ) ≤ (coarseSampleConstant + 10004) * T := by
  let Q := pooledLaw (extendFiniteLaw q) (Finset.range k)
  let A : PoolLabel (Finset.range k) := some (rangeIndexEquiv k a)
  let X := pooledCoordinate x
  have hhead : Q.mass A = q.mass a := by simp only [Q, A, finite_pooled_mass_some, Equiv.symm_apply_apply]
  have hXA : X A = 1 := by simpa only [X, A, pooledCoordinate, Equiv.symm_apply_apply] using ha
  have hX : ∀ z, 0 ≤ X z ∧ X z ≤ 1 := by
    intro z
    cases z with
    | none => norm_num [X, pooledCoordinate]
    | some i => exact hx ((rangeIndexEquiv k).symm i)
  have hk : ∀ z, (tailWeights Q A).mass z * X z ^ 3 = β * (1 - X z ^ 4) ^ 2 := by
    intro z
    cases z with
    | none => simp [Q, A, X, finite_pooled_tail_mass_none, pooledCoordinate]
    | some i => simpa only [Q, A, X, finite_pooled_tail_mass_some, pooledCoordinate] using hkkt ((rangeIndexEquiv k).symm i)
  have hb : 1 = T ^ 2 * β * ∑ z, (tailWeights Q A).mass z * X z * (1 - X z ^ 4) := by
    have hs := finite_pooled_tail_coordinate_sum q a x (fun y => y * (1 - y ^ 4))
    simp only [mul_assoc] at hbudget ⊢
    simpa only [Q, A, X, hs] using hbudget
  have hr : (∑ z, (tailWeights Q A).mass z * X z) + g = ε := by
    have hs := finite_pooled_tail_coordinate_sum q a x id
    simp only [id_eq] at hs
    simpa only [Q, A, X, hs] using hradius
  obtain ⟨n, test, hn, hnull, halt⟩ := finite_heavy_test_of_kkt Q A X T β ε g hT hβ hg hTg
    (by simpa only [hhead] using hrscale) hXA hX hk hb hr
  refine ⟨n, ?_, hn⟩
  apply hasIdentityTest_of_pooled_test (extendFiniteLaw q) (Finset.range k) ε n test hnull
  rw [finite_reference_residual_zero, sub_zero]
  exact halt

def fullHeavyCoordinate {k : ℕ} (x : Fin k → ℝ) : Fin (k + 1) → ℝ := Fin.cases 1 x

theorem fullHeavyCoordinate_tail_sum {k : ℕ} (q : Probability (Fin (k + 1)))
    (x : Fin k → ℝ) (f : ℝ → ℝ) :
    (∑ i, (tailWeights q 0).mass i * f (fullHeavyCoordinate x i)) =
      ∑ i, q.mass i.succ * f (x i) := by
  rw [Fin.sum_univ_succ]
  simp only [tailWeights, fullHeavyCoordinate, Fin.cases_zero, ite_true, zero_mul,
    Fin.succ_ne_zero, if_false, Fin.cases_succ, zero_add]

theorem finite_heavy_upper_bound {k : ℕ} (q : Probability (Fin (k + 1)))
    (hq : ∀ i, 0 < q.mass i) (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {ε : ℝ} (hε : 0 < ε) (hεR : ε ≤ tailTotal q) :
    ∃ n : ℕ, HasIdentityTest (extendFiniteLaw q) ε n ∧
      (n : ℝ) ≤ (coarseSampleConstant + 10004) * heavyRoot (extendFiniteLaw q) ε := by
  obtain ⟨hT, x, β, hx, hradius, hβ, hkkt, hbudget⟩ :=
    exists_heavy_upper_coordinates_at_root q hq hR0 hR hε
  let T := heavyRoot (extendFiniteLaw q) ε
  let g := Real.sqrt (tailTotal q / T)
  let X := fullHeavyCoordinate x
  have hsum0 : 0 ≤ ∑ i, q.mass i.succ * x i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (q.nonneg i.succ) (hx i).1.le)
  have hgR : g ≤ tailTotal q := by change (∑ i, q.mass i.succ * x i) + g = ε at hradius; linarith
  obtain ⟨hg, hT4, hTg, _⟩ := heavy_count_scale hR0 hR hT (rfl : g = Real.sqrt (tailTotal q / T)) hgR
  have hhead := reference_head_tail q
  have hRformula : 1 - q.mass 0 = tailTotal q := by linarith
  have hrscale : Real.sqrt (1 - q.mass 0) ≤ g * Real.sqrt T := by
    rw [hRformula]
    dsimp [g]
    rw [Real.sqrt_div hR0.le, div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.mpr hT))]
  have hX0 : X 0 = 1 := rfl
  have hX : ∀ i, 0 ≤ X i ∧ X i ≤ 1 := by
    intro i
    refine Fin.cases (by norm_num [X, fullHeavyCoordinate]) (fun j => ?_) i
    exact ⟨(hx j).1.le, (hx j).2.le⟩
  have hk : ∀ i, (tailWeights q 0).mass i * X i ^ 3 = β * (1 - X i ^ 4) ^ 2 := by
    intro i
    refine Fin.cases (by norm_num [tailWeights, X, fullHeavyCoordinate]) (fun j => ?_) i
    simpa only [tailWeights, Fin.succ_ne_zero, if_false, X, fullHeavyCoordinate, Fin.cases_succ] using hkkt j
  have hb : 1 = T ^ 2 * β * ∑ i, (tailWeights q 0).mass i * X i * (1 - X i ^ 4) := by
    have hs := fullHeavyCoordinate_tail_sum q x (fun y => y * (1 - y ^ 4))
    simp only [mul_assoc] at hbudget ⊢
    simpa only [X, hs] using hbudget
  have hr : (∑ i, (tailWeights q 0).mass i * X i) + g = ε := by
    have hs := fullHeavyCoordinate_tail_sum q x id
    simp only [id_eq] at hs
    simpa only [X, hs] using hradius
  exact finite_heavy_upper_bound_of_kkt q 0 X T β ε g hT4 hβ hg.le hTg hrscale hX0 hX hk hb hr

/-- The interior and boundary upper bound for every finite reference, including
zero masses and arbitrary placement of the largest atom. Alternatives still
range over the entire original countable alphabet. -/
theorem finite_heavy_upper_bound_with_zeros {l : ℕ} (q : Probability (Fin l))
    (hh : (3 : ℝ) / 4 ≤ largestMass (extendFiniteLaw q))
    (hh1 : largestMass (extendFiniteLaw q) < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hεR : ε ≤ 1 - largestMass (extendFiniteLaw q)) :
    ∃ n : ℕ, HasIdentityTest (extendFiniteLaw q) ε n ∧
      (n : ℝ) ≤ (coarseSampleConstant + 10004) * heavyRoot (extendFiniteLaw q) ε := by
  obtain ⟨k, r, a, ha, hr, hm, hz, hhead⟩ := exists_positive_heavy_representation q
  have ht := reference_head_tail r
  have hR0 : 0 < tailTotal r := by linarith only [ht, hhead, hh1]
  have hR : tailTotal r ≤ (1 : ℝ) / 4 := by linarith only [ht, hhead, hh]
  have heR : ε ≤ tailTotal r := by linarith only [ht, hhead, hεR]
  obtain ⟨n, htest, hn⟩ := finite_heavy_upper_bound r hr hR0 hR hε0 heR
  refine ⟨n, hasIdentityTest_of_finite_embedding_upper
    (extendFiniteLaw q) r a ha hm hz ε n htest, ?_⟩
  rwa [heavyRoot_of_heavy_finite_embedding (extendFiniteLaw q) r hr a ha hm hz hR ε]

end IdentityTesting.HeavyUpper
