import IdentityTesting.HeavyUpperMask

/-! Numerical conditions for the actual heavy-tail weighted/repeat test. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyUpper
open FiniteTesting FiniteAllocationUpper CollisionTesting
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem heavy_actual_parameters_with_geometry (q : Probability Ω) (a : Ω) (x : Ω → ℝ) (T β g : ℝ)
    (hT : 4 ≤ T) (hβ : 0 < β) (hg : 0 ≤ g) (hTg : 1 ≤ T * g)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, (tailWeights q a).mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, (tailWeights q a).mass i * x i * (1 - x i ^ 4))
    (hcase : coarseDisplacement (tailWeights q a) x upperEta + g <
      2 * concentratedResidual (tailWeights q a) x upperEta) :
    let L := fineLabels a x upperEta
    let E := concentratedResidual (tailWeights q a) x upperEta
    let A := weightedMass q q L
    let m := ⌈10000 * T⌉₊
    2 ≤ m ∧ 0 < E ∧ 0 < A ∧ ∃ w : ℝ,
      0 ≤ w ∧ (∀ i ∈ L, Real.sqrt (q.mass i) ≤ w) ∧
      200 * w ≤ (m : ℝ) * A ∧ 8 * w * E ≤ A ∧
      (m : ℝ) ^ 2 * collisionMass2 q L ≤ 1 / 100 ∧
      32000000 * E ≤ (m : ℝ) ^ 2 * A ^ 2 ∧
      w ≤ 6 * upperEta * T * A ∧ T ^ 2 * collisionMass2 q L ≤ 288 * upperEta := by
  dsimp only
  let Q := tailWeights q a
  let L := fineLabels a x upperEta
  let E := concentratedResidual Q x upperEta
  let A := weightedMass q q L
  let m := ⌈10000 * T⌉₊
  have hT0 : 0 < T := by linarith
  have hηhalf : upperEta ≤ 1 / 2 := by norm_num [upperEta]
  have hD0 := coarseDisplacement_nonneg Q x upperEta (fun i => (hx i).1)
  have hE0 : 0 ≤ E := concentratedResidual_nonneg Q x upperEta (fun i => (hx i).2)
  have hE : 0 < E := by change coarseDisplacement Q x upperEta + g < 2 * E at hcase; linarith
  have hD : coarseDisplacement Q x upperEta ≤ 2 * E := by linarith
  have hTE : (1 : ℝ) / 2 ≤ T * E := by
    have hm := mul_le_mul_of_nonneg_left (show g ≤ 2 * E by linarith) hT0.le
    nlinarith only [hm, hTg]
  have hAm : weightedMoment Q (concentratedLabels x upperEta) = A :=
    tail_weightedMoment q a (concentratedLabels x upperEta)
  have ha := concentrated_weighted_mass_bounds Q x upperEta β hηhalf hβ.le
    (fun i => (hx i).2) hkkt
  rw [hAm] at ha
  have hAlower : 4 * Real.sqrt β * E ≤ A := ha.1
  have hAupper : A ≤ 12 * Real.sqrt β * E := ha.2
  have hA : 0 < A := (by positivity : 0 < 4 * Real.sqrt β * E).trans_le hAlower
  have hA0 := hA.le
  have hb := concentrated_beta_moment Q x upperEta T β hηhalf hβ.le hx hbudget hD
  let w := 12 * upperEta * Real.sqrt β
  have hw0 : 0 ≤ w := by dsimp [w]; norm_num [upperEta]
  have hw : ∀ i ∈ L, Real.sqrt (q.mass i) ≤ w := by
    intro i hi
    have hm := Finset.mem_erase.mp hi
    have hb := concentrated_sqrt_mass_le Q x upperEta β hηhalf hβ.le
      (fun j => (hx j).2) hkkt i hm.2
    simpa only [Q, tailWeights, if_neg hm.1] using hb
  have hm : 10000 * T ≤ (m : ℝ) := Nat.le_ceil _
  have hmupper : (m : ℝ) ≤ 10002 * T := by
    simpa only [show (10000 : ℝ) + 2 = 10002 by norm_num] using
      ceil_scale_le (by linarith : (1 : ℝ) / 2 ≤ T) (by norm_num : (0 : ℝ) ≤ 10000)
  have hm2 : 2 ≤ m := by
    have h : (2 : ℝ) ≤ m := by linarith
    exact_mod_cast h
  have hscale := concentrated_moment_scale Q x upperEta T β hηhalf hβ.le hx hkkt hbudget hD
  rw [hAm] at hscale
  have hscale1 : (4 : ℝ) / 3 * E ≤ T ^ 2 * A ^ 2 := hscale.1
  have hwratio : w ≤ 18 * T * A := by
    have hlow := mul_le_mul_of_nonneg_left hAlower (by positivity : 0 ≤ 18 * T)
    have he := mul_le_mul_of_nonneg_right hTE (by positivity : 0 ≤ 72 * Real.sqrt β)
    dsimp [w]
    norm_num [upperEta]
    nlinarith only [hlow, he, Real.sqrt_nonneg β]
  have hmean : 200 * w ≤ (m : ℝ) * A := by
    have hma := mul_le_mul_of_nonneg_right hm hA0
    nlinarith [mul_nonneg hT0.le hA0]
  have hsmall : 8 * w * E ≤ A := by
    dsimp [w]
    norm_num [upperEta]
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
    have hprod := mul_le_mul_of_nonneg_left hAupper hw0
    have hs := Real.sq_sqrt hβ.le
    have heq : w * (12 * Real.sqrt β * E) = 144 * upperEta * β * E := by
      dsimp [w]
      nlinarith only [congrArg (fun z => 144 * upperEta * E * z) hs]
    rw [heq] at hprod
    have ht := mul_le_mul_of_nonneg_left (hq2.trans hprod) (sq_nonneg T)
    have hb' : T ^ 2 * β * E ≤ 2 := hb.2
    have hbmul := mul_le_mul_of_nonneg_left hb' (by norm_num [upperEta] : 0 ≤ 144 * upperEta)
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
  have hwsharp : w ≤ 6 * upperEta * T * A := by
    have hη0 : 0 ≤ upperEta := by norm_num [upperEta]
    have he := mul_le_mul_of_nonneg_left hTE
      (by positivity : 0 ≤ 24 * upperEta * Real.sqrt β)
    have ha := mul_le_mul_of_nonneg_left hAlower
      (by positivity : 0 ≤ 6 * upperEta * T)
    dsimp [w]
    nlinarith only [he, ha]
  exact ⟨hm2, hE, hA, w, hw0, hw, hmean, hsmall, hnull, hsignal, hwsharp, hTq2⟩

theorem heavy_actual_parameters (q : Probability Ω) (a : Ω) (x : Ω → ℝ) (T β g : ℝ)
    (hT : 4 ≤ T) (hβ : 0 < β) (hg : 0 ≤ g) (hTg : 1 ≤ T * g)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, (tailWeights q a).mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, (tailWeights q a).mass i * x i * (1 - x i ^ 4))
    (hcase : coarseDisplacement (tailWeights q a) x upperEta + g <
      2 * concentratedResidual (tailWeights q a) x upperEta) :
    let L := fineLabels a x upperEta
    let E := concentratedResidual (tailWeights q a) x upperEta
    let A := weightedMass q q L
    let m := ⌈10000 * T⌉₊
    2 ≤ m ∧ 0 < E ∧ 0 < A ∧ ∃ w : ℝ,
      0 ≤ w ∧ (∀ i ∈ L, Real.sqrt (q.mass i) ≤ w) ∧
      200 * w ≤ (m : ℝ) * A ∧ 8 * w * E ≤ A ∧
      (m : ℝ) ^ 2 * collisionMass2 q L ≤ 1 / 100 ∧
      32000000 * E ≤ (m : ℝ) ^ 2 * A ^ 2 := by
  obtain ⟨hm, hE, hA, w, hw, hcap, hmean, hsmall, hnull, hsignal, _⟩ :=
    heavy_actual_parameters_with_geometry q a x T β g hT hβ hg hTg hx hkkt hbudget hcase
  exact ⟨hm, hE, hA, w, hw, hcap, hmean, hsmall, hnull, hsignal⟩

end IdentityTesting.HeavyUpper
