import IdentityTesting.EventCountMoments

/-! The two-sided event-count test, proved for actual finite IID observations. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.EventCounts
open FiniteTesting FiniteIID

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def countThreshold (n : ℕ) (u A : ℝ) : ℝ := A * (Real.sqrt (u / n) + 1 / n)

def countTest (E : Finset Ω) (n : ℕ) (u A : ℝ) : RandomizedTest (Fin n → Ω) where
  reject sample := if countThreshold n u A < |eventFrequency E n sample - u| then 1 else 0
  nonneg sample := by split <;> norm_num
  le_one sample := by split <;> norm_num

theorem countThreshold_pos (n : ℕ) (u A : ℝ) (hn : 0 < n) (hA : 0 < A) :
    0 < countThreshold n u A := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact mul_pos hA (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (one_div_pos.mpr hnR))

theorem countThreshold_floor (n : ℕ) (u A : ℝ) (hn : 0 < n) (hA : 0 < A) :
    A ≤ (n : ℝ) * countThreshold n u A := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := mul_nonneg (mul_nonneg hnR.le hA.le) (Real.sqrt_nonneg (u / n))
  unfold countThreshold
  have hN : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
  nlinarith

theorem countThreshold_mass_bound (n : ℕ) (u A : ℝ)
    (hn : 0 < n) (hu : 0 ≤ u) (hA : 0 < A) :
    u / ((n : ℝ) * countThreshold n u A ^ 2) ≤ 1 / A ^ 2 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hb := countThreshold_pos n u A hn hA
  have hs := Real.sqrt_nonneg (u / (n : ℝ))
  have hs2 := Real.sq_sqrt (div_nonneg hu hnR.le)
  have hNs : (n : ℝ) * Real.sqrt (u / (n : ℝ)) ^ 2 = u := by
    rw [hs2]
    field_simp
  have hlow : A * Real.sqrt (u / (n : ℝ)) ≤ countThreshold n u A := by
    unfold countThreshold
    have h := mul_nonneg hA.le (one_div_nonneg.mpr hnR.le)
    nlinarith
  have hsquare := mul_self_le_mul_self (mul_nonneg hA.le hs) hlow
  have hNsquare := mul_le_mul_of_nonneg_left hsquare hnR.le
  apply (div_le_div_iff₀ (mul_pos hnR (sq_pos_of_pos hb)) (sq_pos_of_pos hA)).2
  nlinarith [hNs]

theorem frequency_event_probability_le (p : Probability Ω) (E : Finset Ω)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (B : (Fin n → Ω) → Prop) [DecidablePred B]
    (hB : ∀ sample, B sample → t ≤ |eventFrequency E n sample - eventMass p E|) :
    mean (productLaw p n) (fun sample => if B sample then 1 else 0) ≤
      eventMass p E / ((n : ℝ) * t ^ 2) := by
  classical
  have hpoint : ∀ sample, (if B sample then (1 : ℝ) else 0) ≤
      (eventFrequency E n sample - eventMass p E) ^ 2 / t ^ 2 := by
    intro sample
    by_cases h : B sample
    · simp only [if_pos h]
      apply (le_div_iff₀ (sq_pos_of_pos ht)).2
      have hsq := mul_self_le_mul_self ht.le (hB sample h)
      simpa [sq_abs, ← pow_two] using hsq
    · simp only [if_neg h]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    _ ≤ mean (productLaw p n)
        (fun sample => (eventFrequency E n sample - eventMass p E) ^ 2 / t ^ 2) :=
      mean_mono _ hpoint
    _ = eventFrequencyVariance p E n / t ^ 2 := mean_div_const _ _ _
    _ ≤ (eventMass p E / n) / t ^ 2 :=
      div_le_div_of_nonneg_right (eventFrequencyVariance_le p E n hn) (sq_nonneg _)
    _ = _ := by ring

theorem countTest_null_error (q : Probability Ω) (E : Finset Ω)
    (n : ℕ) (A : ℝ) (hn : 0 < n) (hA : 0 < A) :
    expectation (productLaw q n) (countTest E n (eventMass q E) A) ≤ 1 / A ^ 2 := by
  have h := frequency_event_probability_le q E n hn (countThreshold n (eventMass q E) A)
    (countThreshold_pos n (eventMass q E) A hn hA)
    (fun sample => countThreshold n (eventMass q E) A < |eventFrequency E n sample - eventMass q E|)
    (fun sample h => h.le)
  exact h.trans (countThreshold_mass_bound n (eventMass q E) A hn (eventMass_nonneg q E) hA)

theorem countTest_alternative_error (q p : Probability Ω) (E : Finset Ω)
    (n : ℕ) (A : ℝ) (hn : 0 < n) (hA : 0 < A)
    (hsep : 2 * countThreshold n (eventMass q E) A ≤ |eventMass p E - eventMass q E|) :
    1 - expectation (productLaw p n) (countTest E n (eventMass q E) A) ≤
      1 / A ^ 2 + 2 / A := by
  let u := eventMass q E
  let v := eventMass p E
  let b := countThreshold n u A
  let d := |v - u|
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hu : 0 ≤ u := eventMass_nonneg q E
  have hb : 0 < b := countThreshold_pos n u A hn hA
  have hd : 0 < d := by dsimp [d]; linarith
  have hbd : b ≤ d / 2 := by linarith
  have hvu : v ≤ u + d := by
    have h := le_abs_self (v - u)
    dsimp [d]
    linarith
  have hB : ∀ sample : Fin n → Ω, |eventFrequency E n sample - u| ≤ b →
      d / 2 ≤ |eventFrequency E n sample - v| := by
    intro sample hs
    have htriangle := abs_sub_le v (eventFrequency E n sample) u
    rw [abs_sub_comm v (eventFrequency E n sample)] at htriangle
    dsimp [d] at hbd ⊢
    linarith
  have hmiss : 1 - expectation (productLaw p n) (countTest E n u A) =
      mean (productLaw p n) (fun sample => if |eventFrequency E n sample - u| ≤ b then 1 else 0) := by
    have hpoint : (fun sample => 1 - (countTest E n u A).reject sample) =
        (fun sample => if |eventFrequency E n sample - u| ≤ b then (1 : ℝ) else 0) := by
      funext sample
      change 1 - (if b < |eventFrequency E n sample - u| then 1 else 0) =
        (if |eventFrequency E n sample - u| ≤ b then 1 else 0)
      by_cases h : b < |eventFrequency E n sample - u|
      · rw [if_pos h, if_neg (not_le.mpr h)]
        norm_num
      · rw [if_neg h, if_pos (le_of_not_gt h)]
        norm_num
    rw [← hpoint, mean_sub, mean_const]
    rfl
  rw [hmiss]
  calc
    _ ≤ v / ((n : ℝ) * (d / 2) ^ 2) :=
      frequency_event_probability_le p E n hn (d / 2) (half_pos hd) _ hB
    _ ≤ (u + d) / ((n : ℝ) * (d / 2) ^ 2) :=
      div_le_div_of_nonneg_right hvu (mul_nonneg hnR.le (sq_nonneg _))
    _ = u / ((n : ℝ) * (d / 2) ^ 2) + 4 / ((n : ℝ) * d) := by
      field_simp
      ring
    _ ≤ u / ((n : ℝ) * b ^ 2) + 2 / ((n : ℝ) * b) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_left hu (mul_pos hnR (sq_pos_of_pos hb))
          (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (d / 2 - b)]) hnR.le)
      · apply (div_le_div_iff₀ (mul_pos hnR hd) (mul_pos hnR hb)).2
        nlinarith
    _ ≤ 1 / A ^ 2 + 2 / A := by
      apply add_le_add
      · exact countThreshold_mass_bound n u A hn hu hA
      · exact div_le_div_of_nonneg_left (by norm_num) hA (countThreshold_floor n u A hn hA)

end IdentityTesting.EventCounts
