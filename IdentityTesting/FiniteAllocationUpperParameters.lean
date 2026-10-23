import IdentityTesting.FiniteAllocationUpperConcentrated
import IdentityTesting.FiniteAllocationUpperRounding

/-! Numerical conditions for the actual concentrated-coordinate test, derived
from KKT geometry and the original upper-branch mass bound. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteAllocationUpper
open FiniteTesting FiniteIID ProfileTesting CollisionTesting

def upperEta : ℝ := 1 / 10000000000000000

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

theorem concentrated_actual_parameters_with_geometry (q : Probability Ω) (x : Ω → ℝ) (T β ε : ℝ)
    (hT : (1 : ℝ) / 2 ≤ T) (hβ : 0 < β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hradius : (∑ i, q.mass i * x i) = ε)
    (hmax : ∀ i, q.mass i ≤ 2 * (1 - ε))
    (hD : coarseDisplacement q x upperEta ≤ 2 * concentratedResidual q x upperEta) :
    let L := concentratedLabels x upperEta
    let E := concentratedResidual q x upperEta
    let A := weightedMass q q L
    let m := ⌈10000 * T⌉₊
    2 ≤ m ∧ 0 < E ∧ 0 < A ∧ ∃ w : ℝ,
      0 ≤ w ∧ (∀ i ∈ L, Real.sqrt (q.mass i) ≤ w) ∧
      200 * w ≤ (m : ℝ) * A ∧ 8 * w * E ≤ A ∧
      (m : ℝ) ^ 2 * collisionMass2 q L ≤ 1 / 100 ∧
      32000000 * E ≤ (m : ℝ) ^ 2 * A ^ 2 ∧
      w ≤ 18 * T * A ∧ T ^ 2 * collisionMass2 q L ≤ 288 * upperEta := by
  dsimp only
  let L := concentratedLabels x upperEta
  let E := concentratedResidual q x upperEta
  let A := weightedMass q q L
  let m := ⌈10000 * T⌉₊
  have hT0 : 0 < T := by linarith
  have hη : 0 < upperEta := by norm_num [upperEta]
  have hηhalf : upperEta ≤ 1 / 2 := by norm_num [upperEta]
  have hE0 : 0 ≤ E := concentratedResidual_nonneg q x upperEta (fun i => (hx i).2)
  have hA0 : 0 ≤ A := weightedMass_nonneg q q L
  have hb := concentrated_beta_moment q x upperEta T β hηhalf hβ.le hx hbudget hD
  have hE : 0 < E := by
    by_contra hn
    have he : E = 0 := le_antisymm (le_of_not_gt hn) hE0
    have hb1 : (1 : ℝ) / 12 ≤ T ^ 2 * β * E := hb.1
    rw [he] at hb1
    norm_num at hb1
  have ha := concentrated_weighted_mass_bounds q x upperEta β hηhalf hβ.le
    (fun i => (hx i).2) hkkt
  have hAlower : 4 * Real.sqrt β * E ≤ A := ha.1
  have hAupper : A ≤ 12 * Real.sqrt β * E := ha.2
  have hA : 0 < A := (by positivity : 0 < 4 * Real.sqrt β * E).trans_le hAlower
  have hL : L.Nonempty := by
    by_contra hn
    have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz : E = 0 := by change (∑ i ∈ L, q.mass i * (1 - x i)) = 0; rw [he]; simp
    linarith
  obtain ⟨i, hi, hwi⟩ := Finset.exists_max_image L (fun j => Real.sqrt (q.mass j)) hL
  let w := Real.sqrt (q.mass i)
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw : ∀ j ∈ L, Real.sqrt (q.mass j) ≤ w := hwi
  have hwcap : w ≤ 12 * upperEta * Real.sqrt β :=
    concentrated_sqrt_mass_le q x upperEta β hηhalf hβ.le (fun j => (hx j).2) hkkt i hi
  have hm : 10000 * T ≤ (m : ℝ) := Nat.le_ceil _
  have hmupper : (m : ℝ) ≤ 10002 * T := by
    simpa only [show (10000 : ℝ) + 2 = 10002 by norm_num] using ceil_scale_le hT (by norm_num : (0 : ℝ) ≤ 10000)
  have hm2 : 2 ≤ m := by
    have h : (2 : ℝ) ≤ m := by linarith
    exact_mod_cast h
  have hscale := concentrated_moment_scale q x upperEta T β hηhalf hβ.le hx hkkt hbudget hD
  have hscale1 : (4 : ℝ) / 3 * E ≤ T ^ 2 * A ^ 2 := hscale.1
  have hwratio : w ≤ 18 * T * A := by
    by_cases hH : (coarseLabels x upperEta).Nonempty
    · have hrec := coarse_nonempty_reciprocal q x upperEta T β hη hT0 hβ.le hx hkkt hbudget hH
      have hG : upperGap q x upperEta ≤ 3 * E := by dsimp [upperGap, E]; linarith
      have hg := mul_le_mul_of_nonneg_left hG hT0.le
      have hTE : upperEta ≤ 6 * T * E := by linarith
      have he := mul_le_mul_of_nonneg_right hTE (by positivity : 0 ≤ 12 * Real.sqrt β)
      have hlow := mul_le_mul_of_nonneg_left hAlower (by positivity : 0 ≤ 18 * T)
      nlinarith only [hwcap, he, hlow]
    · have hH0 := Finset.not_nonempty_iff_eq_empty.mp hH
      have hLall : L = Finset.univ := by dsimp [L, concentratedLabels]; rw [hH0]; simp
      have hD0 : coarseDisplacement q x upperEta = 0 := by simp [coarseDisplacement, hH0]
      have hr := allocation_radius_split q x upperEta ε hradius
      have hδ : 1 - ε = E := by change ε = _ + (∑ j ∈ L, q.mass j) - E at hr; rw [hD0, hLall, q.total] at hr; linarith
      have hw2 : w ^ 2 ≤ 2 * E := by dsimp [w]; rw [Real.sq_sqrt (q.nonneg i)]; simpa only [hδ] using hmax i
      have h2 : w ≤ 2 * T * A := by nlinarith [mul_nonneg hT0.le hA0]
      nlinarith [mul_nonneg hT0.le hA0]
  have hmean : 200 * w ≤ (m : ℝ) * A := by
    have hma := mul_le_mul_of_nonneg_right hm hA0
    nlinarith [mul_nonneg hT0.le hA0]
  have hsmall : 8 * w * E ≤ A := by
    have hmE := mul_le_mul_of_nonneg_right hwcap hE0
    norm_num [upperEta] at hmE
    nlinarith [mul_nonneg (Real.sqrt_nonneg β) hE0]
  have hq2 : collisionMass2 q L ≤ w * A := by
    unfold collisionMass2
    dsimp [A, weightedMass]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have h1 := mul_le_mul_of_nonneg_left (hw j hj)
      (mul_nonneg (q.nonneg j) (Real.sqrt_nonneg (q.mass j)))
    have hs := Real.sq_sqrt (q.nonneg j)
    nlinarith only [h1, congrArg (fun z => q.mass j * z) hs]
  have hTq2 : T ^ 2 * collisionMass2 q L ≤ 288 * upperEta := by
    have hprod := mul_le_mul hwcap hAupper hA0 (by positivity : 0 ≤ 12 * upperEta * Real.sqrt β)
    have hs := Real.sq_sqrt hβ.le
    have heq : (12 * upperEta * Real.sqrt β) * (12 * Real.sqrt β * E) = 144 * upperEta * β * E := by nlinarith only [congrArg (fun z => 144 * upperEta * E * z) hs]
    rw [heq] at hprod
    have ht := mul_le_mul_of_nonneg_left (hq2.trans hprod) (sq_nonneg T)
    have hb' : T ^ 2 * β * E ≤ 2 := hb.2
    have hbmul := mul_le_mul_of_nonneg_left hb' (by positivity : 0 ≤ 144 * upperEta)
    nlinarith only [ht, hbmul]
  have hnull : (m : ℝ) ^ 2 * collisionMass2 q L ≤ 1 / 100 := by
    have hmSq := pow_le_pow_left₀ (Nat.cast_nonneg m) hmupper 2
    have hc0 : 0 ≤ collisionMass2 q L := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hmSig := mul_le_mul_of_nonneg_right hmSq hc0
    have hbound := mul_le_mul_of_nonneg_left hTq2 (by norm_num : (0 : ℝ) ≤ 10002 ^ 2)
    norm_num [upperEta] at hbound
    nlinarith only [hmSig, hbound]
  have hsignal : 32000000 * E ≤ (m : ℝ) ^ 2 * A ^ 2 := by
    have hmSq := pow_le_pow_left₀ (by positivity : 0 ≤ 10000 * T) hm 2
    have hmSig := mul_le_mul_of_nonneg_right hmSq (sq_nonneg A)
    have hbound := mul_le_mul_of_nonneg_left hscale1 (by norm_num : (0 : ℝ) ≤ 100000000)
    nlinarith only [hmSig, hbound, hE0]
  exact ⟨hm2, hE, hA, w, hw0, hw, hmean, hsmall, hnull, hsignal, hwratio, hTq2⟩

theorem concentrated_actual_parameters (q : Probability Ω) (x : Ω → ℝ) (T β ε : ℝ)
    (hT : (1 : ℝ) / 2 ≤ T) (hβ : 0 < β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hradius : (∑ i, q.mass i * x i) = ε)
    (hmax : ∀ i, q.mass i ≤ 2 * (1 - ε))
    (hD : coarseDisplacement q x upperEta ≤ 2 * concentratedResidual q x upperEta) :
    let L := concentratedLabels x upperEta
    let E := concentratedResidual q x upperEta
    let A := weightedMass q q L
    let m := ⌈10000 * T⌉₊
    2 ≤ m ∧ 0 < E ∧ 0 < A ∧ ∃ w : ℝ,
      0 ≤ w ∧ (∀ i ∈ L, Real.sqrt (q.mass i) ≤ w) ∧
      200 * w ≤ (m : ℝ) * A ∧ 8 * w * E ≤ A ∧
      (m : ℝ) ^ 2 * collisionMass2 q L ≤ 1 / 100 ∧
      32000000 * E ≤ (m : ℝ) ^ 2 * A ^ 2 := by
  obtain ⟨hm, hE, hA, w, hw, hcap, hmean, hsmall, hnull, hsignal, _⟩ :=
    concentrated_actual_parameters_with_geometry q x T β ε hT hβ hx hkkt hbudget hradius hmax hD
  exact ⟨hm, hE, hA, w, hw, hcap, hmean, hsmall, hnull, hsignal⟩

end IdentityTesting.FiniteAllocationUpper
