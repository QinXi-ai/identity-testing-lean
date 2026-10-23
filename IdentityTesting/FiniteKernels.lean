import IdentityTesting.FiniteTesting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite stochastic kernels and actual TV contraction

Kernels are families of normalized finite probability laws. Their action is the
actual mixture, so the contraction and composition identities below concern
observation laws, including whole sample spaces.
-/

noncomputable section

namespace IdentityTesting.FiniteTesting

open scoped BigOperators
open Classical

universe u v w
variable {Ω : Type u} {Ξ : Type v} {I : Type w}
variable [Fintype Ω] [Fintype Ξ] [Fintype I]

theorem totalVariation_nonneg (p q : Probability Ω) : 0 ≤ totalVariation p q := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem totalVariation_triangle (p q r : Probability Ω) :
    totalVariation p r ≤ totalVariation p q + totalVariation q r := by
  unfold totalVariation
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro x _
  exact abs_sub_le _ _ _

theorem totalVariation_mixtures_same_weights (weights : Probability I)
    (p q : I → Probability Ω) :
    totalVariation (mixture weights p) (mixture weights q) ≤
      ∑ i, weights.mass i * totalVariation (p i) (q i) := by
  unfold totalVariation
  calc
    (1 / 2 : ℝ) * ∑ x, |(mixture weights p).mass x -
        (mixture weights q).mass x| ≤
        (1 / 2 : ℝ) * ∑ x, ∑ i, weights.mass i *
          |(p i).mass x - (q i).mass x| := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro x _
      simp only [mixture_mass, ← Finset.sum_sub_distrib, ← mul_sub]
      calc
        |∑ i, weights.mass i * ((p i).mass x - (q i).mass x)| ≤
            ∑ i, |weights.mass i * ((p i).mass x - (q i).mass x)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul, abs_of_nonneg (weights.nonneg _)]
    _ = ∑ i, weights.mass i * ((1 / 2 : ℝ) *
        ∑ x, |(p i).mass x - (q i).mass x|) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum]
      ring

/-- Applying the same actual stochastic kernel cannot increase TV. -/
theorem totalVariation_kernel_le (p q : Probability Ω) (K : Ω → Probability Ξ) :
    totalVariation (mixture p K) (mixture q K) ≤ totalVariation p q := by
  unfold totalVariation
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    (∑ y, |(mixture p K).mass y - (mixture q K).mass y|) ≤
        ∑ y, ∑ x, |p.mass x - q.mass x| * (K x).mass y := by
      apply Finset.sum_le_sum
      intro y _
      simp only [mixture_mass, ← Finset.sum_sub_distrib, ← sub_mul]
      calc
        |∑ x, (p.mass x - q.mass x) * (K x).mass y| ≤
            ∑ x, |(p.mass x - q.mass x) * (K x).mass y| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul, abs_of_nonneg ((K _).nonneg _)]
    _ = ∑ x, |p.mass x - q.mass x| := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, Probability.total, mul_one]

/-- Kernel action commutes with averaging an actual finite prior. -/
theorem mixture_kernel_mass (weights : Probability I) (laws : I → Probability Ω)
    (K : Ω → Probability Ξ) (y : Ξ) :
    (mixture (mixture weights laws) K).mass y =
      (mixture weights (fun i => mixture (laws i) K)).mass y := by
  simp only [mixture_mass, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Deterministic kernels are represented by actual normalized point masses. -/
def pointLaw (x : Ω) : Probability Ω := by
  classical
  exact {
    mass := fun y => if y = x then 1 else 0
    nonneg := fun y => by split_ifs <;> norm_num
    total := by simp
  }

@[simp] theorem pointLaw_mass (x y : Ω) :
    (pointLaw x).mass y = if y = x then 1 else 0 := by
  classical
  rfl

/-- Pushforward through a function, retaining all zero-mass output labels. -/
def mapLaw (p : Probability Ω) (f : Ω → Ξ) : Probability Ξ :=
  mixture p (fun x => pointLaw (f x))

theorem mapLaw_mass (p : Probability Ω) (f : Ω → Ξ) (y : Ξ) :
    (mapLaw p f).mass y = ∑ x, if f x = y then p.mass x else 0 := by
  classical
  simp only [mapLaw, mixture_mass, pointLaw_mass]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = y
  · simp [h]
  · simp [h, Ne.symm h]

theorem totalVariation_mapLaw_le (p q : Probability Ω) (f : Ω → Ξ) :
    totalVariation (mapLaw p f) (mapLaw q f) ≤ totalVariation p q :=
  totalVariation_kernel_le p q (fun x => pointLaw (f x))

@[simp] theorem mixture_pointLaw_mass (p : Probability Ω) (x : Ω) :
    (mixture p pointLaw).mass x = p.mass x := by
  classical
  simp [mixture_mass, pointLaw_mass]

theorem totalVariation_pointLaw (x y : Ω) :
    totalVariation (pointLaw x) (pointLaw y) = if x = y then 0 else 1 := by
  classical
  by_cases h : x = y
  · subst y
    simp [totalVariation]
  · have pointwise : ∀ z : Ω,
        |(pointLaw x).mass z - (pointLaw y).mass z| =
          (if z = x then (1 : ℝ) else 0) + (if z = y then 1 else 0) := by
      intro z
      by_cases hx : z = x
      · subst z
        simp [h]
      · by_cases hy : z = y
        · subst z
          simp [hx]
        · simp [hx, hy]
    simp only [totalVariation, pointwise, Finset.sum_add_distrib]
    norm_num [h]

/-- A deterministic modification costs at most the probability it changes the
observation. The observation can itself be an entire fixed-size sample tuple. -/
theorem totalVariation_mapLaw_self_le (p : Probability Ω) (f : Ω → Ω) :
    totalVariation (mapLaw p f) p ≤
      ∑ x, if f x ≠ x then p.mass x else 0 := by
  classical
  have h := totalVariation_mixtures_same_weights p (fun x => pointLaw (f x)) pointLaw
  have hid : totalVariation (mixture p (fun x => pointLaw (f x)))
      (mixture p pointLaw) = totalVariation (mapLaw p f) p := by
    simp only [totalVariation, mixture_pointLaw_mass, mapLaw]
  rw [hid] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro x _
  rw [totalVariation_pointLaw]
  by_cases hx : f x = x <;> simp [hx]

end IdentityTesting.FiniteTesting
