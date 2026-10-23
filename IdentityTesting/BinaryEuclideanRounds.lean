import IdentityTesting.BinaryLongDivision

/-! The Euclidean schedule has linearly many division calls in binary length.
This module supplies the mathematical schedule, not a runtime claim for Lean's
native `Nat.gcd`. Actual stack execution is connected separately. -/
namespace IdentityTesting.BinaryEuclideanRounds

theorem remainder_double_lt (a b : ℕ) (hb : 0 < b) (hba : b ≤ a) :
    2 * (a % b) < a := by
  have hr := Nat.mod_lt a hb
  by_cases hhalf : 2 * b ≤ a
  · omega
  · rw [Nat.mod_eq_sub_mod hba, Nat.mod_eq_of_lt (by omega : a - b < b)]
    omega

theorem remainder_size_lt (a b : ℕ) (hb : 0 < b) (hba : b ≤ a) :
    (a % b).size < a.size := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hs : 0 < a.size := Nat.size_pos.mpr ha
  have hd := remainder_double_lt a b hb hba
  have hp := Nat.lt_size_self a
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a.size ≠ 0)
  rw [hk, pow_succ] at hp
  have hr : a % b < 2 ^ k := by omega
  have hsz := Nat.size_le.mpr hr
  omega

def rounds (a b : ℕ) : ℕ :=
  if hb : b = 0 then 0 else 1 + rounds b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero hb)

theorem rounds_zero (a : ℕ) : rounds a 0 = 0 := by rw [rounds]; simp

theorem rounds_step (a b : ℕ) (hb : 0 < b) : rounds a b = 1 + rounds b (a % b) := by
  rw [rounds]
  simp [Nat.ne_of_gt hb]

theorem ordered_rounds_bound (a b : ℕ) (hba : b ≤ a) : rounds a b ≤ a.size + b.size := by
  by_cases hb : b = 0
  · simp [hb, rounds_zero]
  · have hp : 0 < b := Nat.pos_of_ne_zero hb
    have hrem := Nat.mod_lt a hp
    have hs := remainder_size_lt a b hp hba
    have ih := ordered_rounds_bound b (a % b) (Nat.le_of_lt hrem)
    rw [rounds_step a b hp]
    omega
termination_by a.size + b.size
decreasing_by
  have hs := remainder_size_lt a b (Nat.pos_of_ne_zero hb) hba
  omega

theorem rounds_bound (a b : ℕ) : rounds a b ≤ a.size + b.size + 1 := by
  by_cases hba : b ≤ a
  · exact (ordered_rounds_bound a b hba).trans (by omega)
  · have hab : a < b := by omega
    rw [rounds_step a b (by omega), Nat.mod_eq_of_lt hab]
    have ih := ordered_rounds_bound b a (by omega)
    omega

theorem gcd_step (a b : ℕ) : Nat.gcd a b = Nat.gcd b (a % b) := by
  rw [Nat.gcd_comm a b, Nat.gcd_rec, Nat.gcd_comm (a % b) b]

end IdentityTesting.BinaryEuclideanRounds
