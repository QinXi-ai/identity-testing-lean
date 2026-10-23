import IdentityTesting.AllocationTimeSeparation

/-! The time-decrease fraction and the constant 64 window in the rational-root proof. -/

noncomputable section
namespace IdentityTesting

theorem allocation_atom_gap_of_lower_bound {s t b a η : ℝ}
    (hb : 0 < b) (hba : b ≤ a) (hη : 0 ≤ η)
    (hg : 4 * η * (1 + t ^ 2 * b ^ 2) ≤ (t ^ 2 - s ^ 2) * b ^ 2) :
    4 * η * (1 + t ^ 2 * a ^ 2) ≤ (t ^ 2 - s ^ 2) * a ^ 2 := by
  have hc : 0 ≤ t ^ 2 - s ^ 2 - 4 * η * t ^ 2 := by
    by_contra h
    have hneg := mul_neg_of_neg_of_pos (lt_of_not_ge h) (sq_pos_of_pos hb)
    nlinarith only [hg, hη, hneg]
  have hsq := pow_le_pow_left₀ hb.le hba 2
  have hm := mul_le_mul_of_nonneg_left hsq hc
  nlinarith only [hg, hm]

theorem allocationD_finite_exact_time_decrease {k : ℕ} (a : Fin k → ℝ)
    {s t b : ℝ} (hs : 0 < s) (hst : s ≤ t) (hb : 0 < b)
    (ha : ∀ i, b ≤ a i) :
    allocationD (extendFiniteVector a) t ≤
      (1 - (t ^ 2 - s ^ 2) * b ^ 2 / (4 * (1 + t ^ 2 * b ^ 2))) *
        allocationD (extendFiniteVector a) s := by
  have ht : 0 < t := hs.trans_le hst
  have hsq := pow_le_pow_left₀ hs.le hst 2
  have hd : 0 < 4 * (1 + t ^ 2 * b ^ 2) := by positivity
  have heq : 4 * ((t ^ 2 - s ^ 2) * b ^ 2 / (4 * (1 + t ^ 2 * b ^ 2))) *
      (1 + t ^ 2 * b ^ 2) = (t ^ 2 - s ^ 2) * b ^ 2 := by field_simp
  apply allocationD_finite_time_contract a (fun i => hb.trans_le (ha i)) hs ht
  · exact div_nonneg (mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg b)) hd.le
  · apply (div_le_iff₀ hd).2
    nlinarith only [mul_nonneg (sq_nonneg s) (sq_nonneg b)]
  · intro i
    exact allocation_atom_gap_of_lower_bound hb (ha i)
      (div_nonneg (mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg b)) hd.le) heq.le

theorem allocationD_finite_exact_decrease_window {k : ℕ} (a : Fin k → ℝ)
    {t b : ℝ} (ht : 0 < t) (hb : 0 < b) (ha : ∀ i, b ≤ a i) :
    let η := t ^ 2 * b ^ 2 / (64 * (1 + t ^ 2 * b ^ 2))
    0 < η ∧ η < 1 ∧
    allocationD (extendFiniteVector a) t / (1 - η) ≤
      allocationD (extendFiniteVector a) (3 * t / 4) ∧
    allocationD (extendFiniteVector a) (3 * t / 2) ≤
      (1 - η) * allocationD (extendFiniteVector a) t := by
  dsimp only
  let η := t ^ 2 * b ^ 2 / (64 * (1 + t ^ 2 * b ^ 2))
  have heq : 64 * η * (1 + t ^ 2 * b ^ 2) = t ^ 2 * b ^ 2 := by
    dsimp only [η]; field_simp
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηq : η ≤ 1 / 4 := by
    dsimp only [η]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [mul_nonneg (sq_nonneg t) (sq_nonneg b)]
  have hη1 : η < 1 := by linarith
  have hfirst : allocationD (extendFiniteVector a) t ≤
      (1 - η) * allocationD (extendFiniteVector a) (3 * t / 4) := by
    apply allocationD_finite_time_contract a (fun i => hb.trans_le (ha i))
      (by positivity) ht hη.le hηq
    intro i
    apply allocation_atom_gap_of_lower_bound hb (ha i) hη.le
    nlinarith only [heq, mul_nonneg (sq_nonneg t) (sq_nonneg b)]
  have hsecond : allocationD (extendFiniteVector a) (3 * t / 2) ≤
      (1 - η) * allocationD (extendFiniteVector a) t := by
    apply allocationD_finite_time_contract a (fun i => hb.trans_le (ha i))
      ht (by positivity) hη.le hηq
    intro i
    apply allocation_atom_gap_of_lower_bound hb (ha i) hη.le
    have hm := mul_le_mul_of_nonneg_right hηq (mul_nonneg (sq_nonneg t) (sq_nonneg b))
    nlinarith only [heq, hm, mul_nonneg (sq_nonneg t) (sq_nonneg b)]
  exact ⟨hη, hη1, (div_le_iff₀ (sub_pos.mpr hη1)).2 (by nlinarith only [hfirst]), hsecond⟩

theorem allocationD_finite_exact_ambiguous_window {k : ℕ} (a : Fin k → ℝ)
    {t b e : ℝ} (ht : 0 < t) (hb : 0 < b) (he : 0 < e) (ha : ∀ i, b ≤ a i)
    (hl : e - (t ^ 2 * b ^ 2 / (64 * (1 + t ^ 2 * b ^ 2))) * e / 100 ≤
      allocationD (extendFiniteVector a) t)
    (hu : allocationD (extendFiniteVector a) t ≤
      e + (t ^ 2 * b ^ 2 / (64 * (1 + t ^ 2 * b ^ 2))) * e / 100) :
    e < allocationD (extendFiniteVector a) (3 * t / 4) ∧
      allocationD (extendFiniteVector a) (3 * t / 2) < e := by
  let η := t ^ 2 * b ^ 2 / (64 * (1 + t ^ 2 * b ^ 2))
  have h := allocationD_finite_exact_decrease_window a ht hb ha
  change 0 < η ∧ η < 1 ∧ _ ∧ _ at h
  have hfirst := (div_le_iff₀ (sub_pos.mpr h.2.1)).mp h.2.2.1
  have hp := mul_pos h.1 he
  constructor
  · by_contra hnot
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (sub_pos.mpr h.2.1).le
    change e - η * e / 100 ≤ _ at hl
    nlinarith only [hl, hfirst, hm, hp]
  · have hm := mul_le_mul_of_nonneg_left hu (sub_pos.mpr h.2.1).le
    change (1 - η) * allocationD (extendFiniteVector a) t ≤
      (1 - η) * (e + η * e / 100) at hm
    have hnonneg := mul_nonneg (sq_nonneg η) he.le
    nlinarith only [h.2.2.2, hm, hp, hnonneg]

end IdentityTesting
