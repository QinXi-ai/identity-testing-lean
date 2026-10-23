import IdentityTesting.GeneralAllocationBounds
import IdentityTesting.HeavySignedFamily
import IdentityTesting.GeneralLowerSeparation
import IdentityTesting.DominantTilt

/-! # Scalar geometry for the actual heavy-head lower-bound assembly -/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.HeavyLowerGeometry

open HeavySignedFamily

variable {k : ℕ}

def lowTail (x : Fin k → ℝ) : Finset (Fin k) := Finset.univ.filter (fun i => x i ≤ (1 : ℝ) / 4)
def highTail (x : Fin k → ℝ) : Finset (Fin k) := (lowTail x)ᶜ
def seedSet (x : Fin k → ℝ) : Finset (Fin (k + 1)) := (highTail x).image Fin.succ
def lowDisplacement (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ) : ℝ :=
  ∑ i ∈ lowTail x, q.mass i.succ * x i
def highMass (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ) : ℝ :=
  ∑ i ∈ highTail x, q.mass i.succ
def highSlack (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ) : ℝ :=
  ∑ i ∈ highTail x, q.mass i.succ * (1 - x i)

theorem mem_highTail (x : Fin k → ℝ) (i : Fin k) : i ∈ highTail x ↔ (1 : ℝ) / 4 < x i := by
  simp only [highTail, lowTail, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
    true_and, not_le]

theorem head_not_seedSet (x : Fin k → ℝ) : (0 : Fin (k + 1)) ∉ seedSet x := by
  simp [seedSet, Fin.succ_ne_zero]

theorem sum_seedSet (x : Fin k → ℝ) (f : Fin (k + 1) → ℝ) :
    (∑ y ∈ seedSet x, f y) = ∑ i ∈ highTail x, f i.succ := by
  rw [seedSet, Finset.sum_image]
  exact fun a _ b _ hab => Fin.succ_injective _ hab

theorem radius_identity (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    {ε g : ℝ} (hε : (∑ i, q.mass i.succ * x i) + g = ε) :
    ε = lowDisplacement q x + highMass q x - highSlack q x + g := by
  have hsplit := Finset.sum_add_sum_compl (lowTail x) (fun i => q.mass i.succ * x i)
  have hslack : highSlack q x = highMass q x - ∑ i ∈ highTail x, q.mass i.succ * x i := by
    unfold highSlack highMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold highTail at hslack
  unfold lowDisplacement highMass highSlack highTail
  dsimp only [lowDisplacement, highMass, highSlack, highTail] at hslack
  linarith only [hsplit, hslack, hε]

theorem highSlack_nonneg (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, x i < 1) : 0 ≤ highSlack q x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (q.nonneg _) (sub_nonneg.mpr (hx i).le))

theorem lowDisplacement_nonneg (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ lowDisplacement q x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (q.nonneg _) (hx i))

theorem high_moment_bound (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) {T : ℝ}
    (hbudget : T ^ 2 * (∑ i, (q.mass i.succ) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1) :
    T ^ 2 * (∑ i ∈ highTail x, (q.mass i.succ) ^ ((3 : ℝ) / 2)) ^ 2 ≤
      16384 * highSlack q x := by
  exact allocation_high_subset_bound (highTail x) (fun i => q.mass i.succ) x
    (fun i => q.nonneg _) hx (fun i hi => by linarith only [(mem_highTail x i).mp hi]) hbudget

theorem tail_coordinate_bound (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) {T : ℝ}
    (hbudget : T ^ 2 * (∑ j, (q.mass j.succ) ^ 2 * (x j) ^ 4 / (1 - (x j) ^ 4)) = 1)
    (i : Fin k) : T * q.mass i.succ * (x i) ^ 2 ≤ 1 := by
  have hcost : ∀ j, 0 ≤ (q.mass j.succ) ^ 2 * (x j) ^ 4 / (1 - (x j) ^ 4) := by
    intro j
    exact div_nonneg (by positivity)
      (sub_nonneg.mpr (allocation_fourth_lt_one (hx j).1 (hx j).2).le)
  have hraw : (q.mass i.succ) ^ 2 * (x i) ^ 4 ≤
      (q.mass i.succ) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) := by
    apply (le_div_iff₀ (sub_pos.mpr (allocation_fourth_lt_one (hx i).1 (hx i).2))).2
    nlinarith only [mul_nonneg (sq_nonneg (q.mass i.succ)) (sq_nonneg ((x i) ^ 4))]
  have hsingle := Finset.single_le_sum (fun j _ => hcost j) (Finset.mem_univ i)
  have hrawT := mul_le_mul_of_nonneg_left (hraw.trans hsingle) (sq_nonneg T)
  rw [hbudget] at hrawT
  nlinarith only [hrawT, sq_nonneg (T * q.mass i.succ * (x i) ^ 2 - 1)]

theorem high_atom_bound (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1) {T : ℝ} (hT : 0 < T)
    (hbudget : T ^ 2 * (∑ j, (q.mass j.succ) ^ 2 * (x j) ^ 4 / (1 - (x j) ^ 4)) = 1)
    (i : Fin k) (hi : i ∈ highTail x) : q.mass i.succ ≤ 16 / T := by
  apply (le_div_iff₀ hT).2
  have hxi := (mem_highTail x i).mp hi
  have hsq : (1 : ℝ) / 16 < (x i) ^ 2 := by
    have h := mul_pos (sub_pos.mpr hxi) (show 0 < x i + 1 / 4 by linarith only [hxi])
    nlinarith only [h]
  have hm := mul_lt_mul_of_pos_left hsq (mul_pos hT (hq i.succ))
  have hc := tail_coordinate_bound q x hx hbudget i
  nlinarith only [hm, hc]

theorem large_scale_bounds {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hTR : (100000000 : ℝ) ≤ T * R) :
    0 < Real.sqrt (R / T) ∧
      Real.sqrt (R / T) ≤ R / 10000 ∧ 10000 ≤ T * Real.sqrt (R / T) := by
  let g := Real.sqrt (R / T)
  have hg : 0 < g := Real.sqrt_pos.mpr (div_pos hR hT)
  have hgsq : g ^ 2 = R / T := Real.sq_sqrt (div_nonneg hR.le hT.le)
  have hTgsq : (T * g) ^ 2 = T * R := by rw [mul_pow, hgsq]; field_simp
  have hTg : 10000 ≤ T * g :=
    (sq_le_sq₀ (by norm_num) (mul_nonneg hT.le hg.le)).mp (by nlinarith only [hTgsq, hTR])
  have hRgsq : (10000 * g) ^ 2 ≤ R ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hTR (sq_nonneg g)
    have heq : T * R * g ^ 2 = R ^ 2 := by rw [hgsq]; field_simp
    nlinarith only [h, heq]
  have hRg : 10000 * g ≤ R :=
    (sq_le_sq₀ (mul_nonneg (by norm_num) hg.le) hR.le).mp hRgsq
  exact ⟨hg, by change g ≤ R / 10000; linarith only [hRg], hTg⟩

theorem seed_overlap_lt_margin {A T E g : ℝ} (hT : 0 < T) (hE : 0 ≤ E) (hg : 0 < g)
    (hTg : 10000 ≤ T * g) (hmoment : T ^ 2 * A ^ 2 ≤ 16384 * E)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T) :
    2 * 1000 * (n : ℝ) ^ 2 * A ^ 2 + 32 / T < (E + g) / 100 := by
  have hn2 := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
  have hscaled := mul_le_mul_of_nonneg_right hn2 (sq_nonneg A)
  have hbudget := mul_le_mul_of_nonneg_left hmoment
    (by norm_num : (0 : ℝ) ≤ 1 / (10 : ℝ) ^ 20)
  have hbound : (n : ℝ) ^ 2 * A ^ 2 ≤ (16384 / (10 : ℝ) ^ 20) * E := by
    norm_num at hscaled hbudget ⊢
    nlinarith only [hscaled, hbudget]
  have hrem : 32 / T ≤ g / 250 := by
    apply (div_le_iff₀ hT).2
    nlinarith only [hTg]
  norm_num at hbound
  nlinarith only [hbound, hrem, hE, hg]

end IdentityTesting.HeavyLowerGeometry
