import IdentityTesting.CollisionVariance
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

/-! The numerical collision-detection bound, from actual IID moments. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.CollisionTesting
open FiniteTesting FiniteIID

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

theorem no_repeat_probability_le (p : Probability Ω) (L : Finset Ω) (n : ℕ)
    (hn : 2 ≤ n) (hp2 : 0 < collisionMass2 p L) :
    1 - expectation (productLaw p n) (repeatTest L n) ≤
      4 / ((n : ℝ) ^ 2 * collisionMass2 p L) +
        16 / ((n : ℝ) * Real.sqrt (collisionMass2 p L)) := by
  let N : ℝ := n
  let C : ℝ := n.choose 2
  let v := collisionMass2 p L
  let w := collisionMass3 p L
  let s := Real.sqrt v
  have hN2 : 2 ≤ N := Nat.cast_le.mpr hn
  have hN : 0 < N := by linarith
  have hC : 0 < C := Nat.cast_pos.mpr (Nat.choose_pos hn)
  have hv : 0 < v := hp2
  have hs : 0 < s := Real.sqrt_pos.2 hv
  have hsquare : s ^ 2 = v := Real.sq_sqrt hv.le
  have hchoose : N ^ 2 / 4 ≤ C := by
    have hprod := mul_nonneg hN.le (sub_nonneg.mpr hN2)
    have hcEq : C = N * (N - 1) / 2 := Nat.cast_choose_two ℝ n
    rw [hcEq]
    nlinarith only [hprod]
  have hb : 0 < N ^ 2 * v / 4 := by positivity
  have hbmu : N ^ 2 * v / 4 ≤ C * v := by
    have h := mul_le_mul_of_nonneg_right hchoose hv.le
    nlinarith only [h]
  have hden : (N ^ 2 * v / 4) ^ 2 ≤ (C * v) ^ 2 :=
    pow_le_pow_left₀ hb.le hbmu 2
  have hfirst : 1 / (C * v) ≤ 4 / (N ^ 2 * v) := by
    calc
      _ ≤ 1 / (N ^ 2 * v / 4) := div_le_div_of_nonneg_left (by norm_num) hb hbmu
      _ = _ := by field_simp [ne_of_gt hN, ne_of_gt hv]
  have hw : w ≤ v * s := collisionMass3_le_mass2_sqrt p L
  have hw0 : 0 ≤ w := collisionMass3_nonneg p L
  have hsecond : N ^ 3 * w / (C * v) ^ 2 ≤ 16 / (N * s) := by
    calc
      _ ≤ N ^ 3 * w / (N ^ 2 * v / 4) ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hN.le 3) hw0)
          (pow_pos hb 2) hden
      _ ≤ N ^ 3 * (v * s) / (N ^ 2 * v / 4) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (pow_nonneg hN.le 3))
          (sq_nonneg _)
      _ = 16 / (N * s) := by
        rw [← hsquare]
        field_simp [ne_of_gt hN, ne_of_gt hs]
        ring
  have hvar : collisionVariance p L n ≤ C * v + N ^ 3 * w := collisionVariance_le p L n
  calc
    1 - expectation (productLaw p n) (repeatTest L n) ≤ collisionVariance p L n / (C * v) ^ 2 :=
      no_repeat_probability_le_variance p L n hn hp2
    _ ≤ (C * v + N ^ 3 * w) / (C * v) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 1 / (C * v) + N ^ 3 * w / (C * v) ^ 2 := by
      rw [add_div]
      congr 1
      field_simp [ne_of_gt hC, ne_of_gt hv]
    _ ≤ 4 / (N ^ 2 * v) + 16 / (N * s) := add_le_add hfirst hsecond

end IdentityTesting.CollisionTesting
