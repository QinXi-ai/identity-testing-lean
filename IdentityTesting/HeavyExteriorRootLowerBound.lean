import IdentityTesting.HeavyFiniteBridge
import IdentityTesting.HeavyNearExteriorLowerBound
import IdentityTesting.HeavyFarExteriorLowerBound

/-! # Complete exterior heavy lower bound at the original boundary root -/

noncomputable section
namespace IdentityTesting

open FiniteTesting HeavySignedFamily HeavyLowerGeometry HeavyFarExterior

theorem no_identityTest_of_finite_heavy_exterior {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {Δ : ℝ} (hΔ0 : 0 < Δ) (hε : tailTotal q + Δ < 1)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 11) *
      min (heavyRoot (extendFiniteLaw q) (tailTotal q))
        (tailTotal q / Δ ^ 2 + 1 / Δ)) :
    ¬ HasIdentityTest (extendFiniteLaw q) (tailTotal q + Δ) n := by
  have hc0 : (0 : ℝ) ≤ 1 / (10 : ℝ) ^ 11 := by norm_num
  have hnT := hn.trans (mul_le_mul_of_nonneg_left
    (min_le_left (heavyRoot (extendFiniteLaw q) (tailTotal q))
      (tailTotal q / Δ ^ 2 + 1 / Δ)) hc0)
  have hncount := hn.trans (mul_le_mul_of_nonneg_left
    (min_le_right (heavyRoot (extendFiniteLaw q) (tailTotal q))
      (tailTotal q / Δ ^ 2 + 1 / Δ)) hc0)
  by_cases hnear : Δ ≤ tailTotal q / 2
  · obtain ⟨hT, x, hx, hboundary, hbudget⟩ :=
      exists_finite_heavy_coordinates_at_root q hq hR0 hR hR0
    have hnT' : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) *
        heavyRoot (extendFiniteLaw q) (tailTotal q) := by
      exact hnT.trans (mul_le_mul_of_nonneg_right (by norm_num) hT.le)
    have hnΔ : (n : ℝ) * Δ ^ 2 / tailTotal q ≤ 1 / (10 : ℝ) ^ 10 := by
      have h := mul_le_mul_of_nonneg_right hncount (div_nonneg (sq_nonneg Δ) hR0.le)
      have heq : (1 / (10 : ℝ) ^ 11) * (tailTotal q / Δ ^ 2 + 1 / Δ) *
          (Δ ^ 2 / tailTotal q) = (1 / (10 : ℝ) ^ 11) * (1 + Δ / tailTotal q) := by
        field_simp [ne_of_gt hR0, ne_of_gt hΔ0]
        <;> ring
      rw [heq] at h
      have hratio : Δ / tailTotal q ≤ (1 : ℝ) / 2 :=
        (div_le_iff₀ hR0).2 (by linarith only [hnear])
      have hmul : (n : ℝ) * (Δ ^ 2 / tailTotal q) = (n : ℝ) * Δ ^ 2 / tailTotal q := by ring
      rw [hmul] at h
      norm_num at h
      linarith only [h, hratio]
    exact no_identityTest_of_heavy_boundary_coordinates q x
      (heavyRoot (extendFiniteLaw q) (tailTotal q)) Δ hT hq
      (fun i => ⟨(hx i).1.le, (hx i).2⟩) hR0 hR hbudget hboundary hΔ0 hnear n hnT' hnΔ
  · apply no_identityTest_of_far_exterior q hR0 (lt_of_not_ge hnear).le hε n
    have hRΔ : tailTotal q ≤ 2 * Δ := by linarith only [lt_of_not_ge hnear]
    have hscale : (tailTotal q / Δ ^ 2 + 1 / Δ) * Δ ≤ 3 := by
      have hformula : (tailTotal q / Δ ^ 2 + 1 / Δ) * Δ = tailTotal q / Δ + 1 := by
        field_simp [ne_of_gt hΔ0]
        <;> ring
      rw [hformula]
      have hratio : tailTotal q / Δ ≤ 2 := (div_le_iff₀ hΔ0).2 hRΔ
      linarith only [hratio]
    have h := mul_le_mul_of_nonneg_right hncount hΔ0.le
    have hbound := mul_le_mul_of_nonneg_left hscale hc0
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 36) hΔ0)).2
    norm_num at h hbound ⊢
    nlinarith only [h, hbound]

end IdentityTesting
