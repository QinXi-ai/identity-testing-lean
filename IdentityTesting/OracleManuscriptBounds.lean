import IdentityTesting.RationalAllocationOracleBounds

/-! The min/max bracket and coordinate-error constants in the allocation oracle. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.RationalComputation

theorem manuscript_beta_lower_of_mass_bound {k : ℕ} (a : Fin k → ℝ)
    {t b M : ℝ} (ht : 0 < t) (hb : 0 < b) (hbM : b ≤ M)
    (hr : 0 < ∑ i, a i) (haM : ∀ i, a i ≤ M) :
    b / (1 + (k : ℝ) * t ^ 2 * M ^ 2) ≤ 1 / (t ^ 2 * ∑ i, a i) := by
  have hM : 0 < M := hb.trans_le hbM
  have hsum : (∑ i, a i) ≤ (k : ℝ) * M := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => haM i)
  have hprod : b * (∑ i, a i) ≤ (k : ℝ) * M ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hsum hb.le
    have h2 := mul_le_mul_of_nonneg_right hbM (mul_nonneg (Nat.cast_nonneg k) hM.le)
    nlinarith only [h1, h2]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hm := mul_le_mul_of_nonneg_left hprod (sq_nonneg t)
  nlinarith only [hm]

theorem exists_actual_oracle_optimizer_minmax {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) (t : ℝ) (ha : ∀ i, 0 < a i) (ht : 0 < t)
    (jmin jmax : Fin k) (hmin : ∀ i, a jmin ≤ a i) (hmax : ∀ i, a i ≤ a jmax) :
    ∃ (x : Fin k → ℝ) (β : ℝ), (∀ i, 0 < x i ∧ x i < 1) ∧ 0 < β ∧
      (∀ i, a i * (x i) ^ 3 = β * (1 - (x i) ^ 4) ^ 2) ∧
      (∑ i, allocationCost t (a i) (x i)) = 1 ∧
      allocationD (extendFiniteVector a) t = ∑ i, a i * x i ∧
      a jmin / (1 + (k : ℝ) * t ^ 2 * a jmax ^ 2) ≤ β ∧
      β ≤ (1 + t ^ 2 * a jmin ^ 2) ^ 2 / (t ^ 4 * a jmin ^ 3) := by
  obtain ⟨x, β, hx, hβ, hs, hc, hv, hl, hu⟩ := exists_actual_oracle_optimizer a t ha ht jmin
  refine ⟨x, β, hx, hβ, hs, hc, hv, ?_, hu⟩
  exact (manuscript_beta_lower_of_mass_bound a ht (ha jmin) (hmin jmax)
    (Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty) hmax).trans hl

theorem manuscript_coordinate_cost_error {t a M l u ρ ν : ℝ}
    (ha : 0 ≤ a) (haM : a ≤ M) (hl : 0 ≤ l) (hlu : l ≤ u)
    (hρ : 0 < ρ) (hu : u ≤ 1 - ρ / 2) (hwidth : u - l ≤ ν) :
    allocationCost t a u - allocationCost t a l ≤
      (16 * t ^ 2 * M ^ 2 / ρ ^ 2) * ν := by
  have h := allocationCost_lipschitz (t := t) (a := a) hl hlu (half_pos hρ) hu
  have heq : 4 * t ^ 2 * a ^ 2 / (ρ / 2) ^ 2 = 16 * t ^ 2 * a ^ 2 / ρ ^ 2 := by ring
  rw [heq] at h
  have hcoef : 16 * t ^ 2 * a ^ 2 / ρ ^ 2 ≤ 16 * t ^ 2 * M ^ 2 / ρ ^ 2 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha haM 2) (by positivity)) (sq_nonneg ρ)
  exact h.trans ((mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hlu)).trans
    (mul_le_mul_of_nonneg_left hwidth (by positivity)))

theorem manuscript_budget_objective_error {k : ℕ} (a l u : Fin k → ℝ)
    {t M ρ ν : ℝ} (ha : ∀ i, 0 ≤ a i) (haM : ∀ i, a i ≤ M)
    (hl : ∀ i, 0 ≤ l i) (hlu : ∀ i, l i ≤ u i) (hρ : 0 < ρ)
    (hu : ∀ i, u i ≤ 1 - ρ / 2) (hwidth : ∀ i, u i - l i ≤ ν) :
    (∑ i, allocationCost t (a i) (u i)) - (∑ i, allocationCost t (a i) (l i)) ≤
      (16 * (k : ℝ) * t ^ 2 * M ^ 2 / ρ ^ 2) * ν ∧
    (∑ i, a i * u i) - (∑ i, a i * l i) ≤ (∑ i, a i) * ν := by
  constructor
  · rw [← Finset.sum_sub_distrib]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      manuscript_coordinate_cost_error (t := t) (ha i) (haM i) (hl i) (hlu i) hρ (hu i) (hwidth i))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    convert h using 1 <;> ring
  · rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (hwidth i) (ha i)
    nlinarith only [h]

theorem manuscript_coordinate_pole_separation {b B a β y : ℝ}
    (hb : 0 < b) (hB : 0 < B) (hba : b ≤ a) (hβ : 0 < β) (hβB : β ≤ B)
    (hy : 0 ≤ y ∧ y < 1) (heq : a * y ^ 3 = β * (1 - y ^ 4) ^ 2) :
    let ρ := min (1 / 2 : ℝ) (b / (128 * B))
    0 < ρ ∧ y ≤ 1 - ρ := by
  let ρ := min (1 / 2 : ℝ) (b / (128 * B))
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  refine ⟨hρ, stationary_coordinate_pole_gap hb hba hβ hβB hρ
    (min_le_left _ _) ?_ hy.1 hy.2 heq⟩
  have h := (le_div_iff₀ (show 0 < 128 * B by positivity)).mp
    (min_le_right (1 / 2 : ℝ) (b / (128 * B)))
  nlinarith only [h]

end IdentityTesting.RationalComputation
