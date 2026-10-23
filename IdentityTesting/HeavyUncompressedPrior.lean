import IdentityTesting.HeavySignedLowerBound
import IdentityTesting.HeavyTilt

/-! # The actual common-form heavy prior before seed compression -/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.HeavyLowerGeometry

open FiniteTesting HeavySignedFamily HeavySignedLowerBound HeavyTilt SignedDiagonalMoment

variable {k : ℕ}

theorem complement_seed_mass (q : Probability (Fin (k + 1))) (x : Fin k → ℝ) :
    (∑ j ∈ (seedSet x)ᶜ, q.mass j) = 1 - highMass q x := by
  have h := (Finset.sum_add_sum_compl (seedSet x) q.mass).trans q.total
  rw [sum_seedSet] at h
  change _ + _ = 1 at h
  unfold highMass
  linarith only [h]

theorem exists_heavy_uncompressed_prior
    (q : Probability (Fin (k + 1))) (x : Fin k → ℝ) (T ε : ℝ)
    (hT : 0 < T) (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (hTR : (100000000 : ℝ) ≤ T * tailTotal q)
    (hbudget : T ^ 2 * (∑ i, (q.mass i.succ) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1)
    (hε : (∑ i, q.mass i.succ * x i) + Real.sqrt (tailTotal q / T) = ε)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T) :
    ∃ (ν : (Fin k → Bool) → Probability (Fin (k + 1))) (f : ℝ), 1 ≤ f ∧ f ≤ 2 ∧
      (∀ σ j, j ∈ seedSet x → (ν σ).mass j = f * q.mass j) ∧
      (∀ σ, (∑ j ∈ (seedSet x)ᶜ, min ((ν σ).mass j) (q.mass j)) ≤
        1 - ε - (highSlack q x + Real.sqrt (tailTotal q / T)) / 100) ∧
      FiniteTesting.totalVariation (mixture (uniformSigns k) (fun σ => productLaw (ν σ) n))
        (productLaw q n) < 1 / (10 : ℝ) ^ 3 := by
  let g := Real.sqrt (tailTotal q / T)
  have hg : 0 < g := Real.sqrt_pos.mpr (div_pos hR0 hT)
  have hE : 0 ≤ highSlack q x := highSlack_nonneg q x (fun i => (hx i).2)
  have hD : 0 ≤ lowDisplacement q x := lowDisplacement_nonneg q x (fun i => (hx i).1)
  have hradius := radius_identity q x hε
  have hmass := complement_seed_mass q x
  by_cases hcase : 2 * g ≤ lowDisplacement q x + highSlack q x
  · let ν := allocationHeavyLaw q x (fun i => (hx i).1) hR
    have hscale (σ : Fin k → Bool) (j : Fin (k + 1)) (hj : j ∈ seedSet x) :
        (ν σ).mass j = q.mass j := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact allocationHeavyLaw_mass_outside q x (fun i => (hx i).1) hR σ i ((mem_highTail x i).mp hi)
    refine ⟨ν, 1, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro σ j hj
      simpa only [one_mul] using hscale σ j hj
    · intro σ
      have hover := GeneralLowerGeometry.overlap_on_changed_set (ν σ) q (seedSet x)ᶜ
        (fun j hj => hscale σ j (Finset.notMem_compl.mp hj))
      have htv := allocationHeavyLaw_totalVariation_ge q x (fun i => (hx i).1) hR σ
      change 2 * lowDisplacement q x ≤ _ at htv
      rw [hmass] at hover
      change ε = lowDisplacement q x + highMass q x - highSlack q x + g at hradius
      change _ ≤ 1 - ε - (highSlack q x + g) / 100
      linarith only [hover, htv, hradius, hcase, hD, hg]
    · exact (allocationHeavyLaw_sample_totalVariation_lt q x hq hx hR hT hbudget n hn).trans (by norm_num)
  · obtain ⟨ν, f, hf1, hf2, _, _, htail, hover, _, htv⟩ :=
      exists_large_heavy_tilt q hq hR0 hR hT hTR
    refine ⟨fun _ => ν, f, hf1, hf2, ?_, ?_, ?_⟩
    · intro σ j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact htail i
    · intro σ
      have h := hover (seedSet x)ᶜ (Finset.mem_compl.mpr (head_not_seedSet x))
      rw [hmass] at h
      have hcase' := lt_of_not_ge hcase
      change ε = lowDisplacement q x + highMass q x - highSlack q x + g at hradius
      change _ ≤ 1 - ε - (highSlack q x + g) / 100
      change _ = _ - 4 * g at h
      linarith only [h, hradius, hcase', hE, hg]
    · simpa only [mixture_constant] using (htv n hn).trans (by norm_num : 1 / (10 : ℝ) ^ 4 < 1 / (10 : ℝ) ^ 3)

end IdentityTesting.HeavyLowerGeometry
