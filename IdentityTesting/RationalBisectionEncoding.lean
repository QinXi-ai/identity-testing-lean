import IdentityTesting.RationalEncodingBounds

/-! Binary encoding bounds for the actual rational coordinate bisection.
The dyadic grid invariant prevents an exponential bound from repeated generic
rational addition estimates. These are representation-size bounds; arithmetic
bit-operation costs are a separate obligation. -/

namespace IdentityTesting.RationalComputation

theorem bisect_add (p : ℚ → ℚ) (m n : ℕ) (l u : ℚ) :
    bisect p (m + n) l u =
      bisect p n (bisect p m l u).1 (bisect p m l u).2 := by
  induction m generalizing l u with
  | zero => simp [bisect]
  | succ m ih =>
    simp only [Nat.succ_add, bisect]
    split <;> exact ih _ _

theorem bisect_dyadic_grid (p : ℚ → ℚ) (n s k : ℕ) (hk : k < 2 ^ s) :
    ∃ j : ℕ, j < 2 ^ (s + n) ∧
      bisect p n ((k : ℚ) / 2 ^ s) (((k + 1 : ℕ) : ℚ) / 2 ^ s) =
        ((j : ℚ) / 2 ^ (s + n), (((j + 1 : ℕ) : ℚ) / 2 ^ (s + n))) := by
  induction n generalizing s k with
  | zero => exact ⟨k, by simpa using hk, by simp [bisect]⟩
  | succ n ih =>
    have hm : (((k : ℚ) / 2 ^ s) + (((k + 1 : ℕ) : ℚ) / 2 ^ s)) / 2 =
        ((2 * k + 1 : ℕ) : ℚ) / 2 ^ (s + 1) := by
      push_cast
      rw [pow_succ]
      ring
    have hl : (k : ℚ) / 2 ^ s = ((2 * k : ℕ) : ℚ) / 2 ^ (s + 1) := by
      push_cast
      rw [pow_succ]
      ring
    have hu : ((k + 1 : ℕ) : ℚ) / 2 ^ s =
        ((2 * k + 1 + 1 : ℕ) : ℚ) / 2 ^ (s + 1) := by
      push_cast
      rw [pow_succ]
      ring
    have hleft : 2 * k < 2 ^ (s + 1) := by rw [pow_succ]; omega
    have hright : 2 * k + 1 < 2 ^ (s + 1) := by rw [pow_succ]; omega
    simp only [bisect, hm]
    split
    · rw [hu]
      simpa only [show s + 1 + n = s + (n + 1) by omega] using
        ih (s + 1) (2 * k + 1) hright
    · rw [hl]
      simpa only [show s + 1 + n = s + (n + 1) by omega] using
        ih (s + 1) (2 * k) hleft

theorem coordinateInterval_dyadic_grid (a β : ℚ) (n : ℕ) :
    ∃ j : ℕ, j < 2 ^ n ∧ coordinateInterval a β n =
      ((j : ℚ) / 2 ^ n, (((j + 1 : ℕ) : ℚ) / 2 ^ n)) := by
  simpa [coordinateInterval] using
    bisect_dyadic_grid (coordinatePolynomial a β) n 0 0 (by norm_num)

theorem dyadic_encoding_le (n k : ℕ) (hk : k ≤ 2 ^ n) :
    rationalEncodingLength ((k : ℚ) / 2 ^ n) ≤ 2 * n + 3 := by
  have h := rational_fraction_reduction_bounds (k : ℤ) (2 ^ n) (by positivity)
  have hn : (((k : ℚ) / 2 ^ n).num).natAbs ≤ k := by simpa using h.1
  have hd : ((k : ℚ) / 2 ^ n).den ≤ 2 ^ n := by simpa using h.2
  have hnb := (Nat.size_le_size (hn.trans hk))
  have hdb := Nat.size_le_size hd
  rw [Nat.size_pow] at hnb hdb
  unfold rationalEncodingLength numeratorBits denominatorBits
  omega

theorem coordinateInterval_encoding_le (a β : ℚ) (n : ℕ) :
    rationalEncodingLength (coordinateInterval a β n).1 ≤ 2 * n + 3 ∧
      rationalEncodingLength (coordinateInterval a β n).2 ≤ 2 * n + 3 := by
  obtain ⟨j, hj, heq⟩ := coordinateInterval_dyadic_grid a β n
  rw [heq]
  exact ⟨dyadic_encoding_le n j hj.le, dyadic_encoding_le n (j + 1) (by omega)⟩

theorem coordinatePolynomial_encoding_le (a β x : ℚ) :
    rationalEncodingLength (coordinatePolynomial a β x) ≤
      2 * (rationalEncodingLength a + rationalEncodingLength β) +
        38 * rationalEncodingLength x + 65 := by
  have h3 := rational_pow_encoding x 3
  have h4 := rational_pow_encoding x 4
  have hsub := rational_sub_encoding 1 (x ^ 4)
  have hsq := rational_pow_encoding (1 - x ^ 4) 2
  have ha := rational_mul_encoding a (x ^ 3)
  have hb := rational_mul_encoding β ((1 - x ^ 4) ^ 2)
  have hfinal := rational_sub_encoding (a * x ^ 3) (β * (1 - x ^ 4) ^ 2)
  have hone : rationalEncodingLength 1 = 3 := by
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  unfold coordinatePolynomial
  omega

/-- The point queried after exactly `i` coordinate-bisection steps. -/
def coordinateQuery (a β : ℚ) (i : ℕ) : ℚ :=
  ((coordinateInterval a β i).1 + (coordinateInterval a β i).2) / 2

theorem coordinateInterval_step (a β : ℚ) (i : ℕ) :
    coordinateInterval a β (i + 1) =
      if coordinatePolynomial a β (coordinateQuery a β i) ≤ 0 then
        (coordinateQuery a β i, (coordinateInterval a β i).2)
      else ((coordinateInterval a β i).1, coordinateQuery a β i) := by
  rw [coordinateInterval, bisect_add]
  simp only [bisect, coordinateInterval, coordinateQuery]

theorem coordinateQuery_dyadic_grid (a β : ℚ) (i : ℕ) :
    ∃ j : ℕ, j < 2 ^ (i + 1) ∧ coordinateQuery a β i =
      (j : ℚ) / 2 ^ (i + 1) := by
  obtain ⟨k, hk, heq⟩ := coordinateInterval_dyadic_grid a β i
  refine ⟨2 * k + 1, ?_, ?_⟩
  · rw [pow_succ]
    omega
  · simp only [coordinateQuery, heq, Prod.fst, Prod.snd]
    push_cast
    rw [pow_succ]
    ring

theorem coordinateQuery_encoding_le (a β : ℚ) (i : ℕ) :
    rationalEncodingLength (coordinateQuery a β i) ≤ 2 * i + 5 := by
  obtain ⟨j, hj, heq⟩ := coordinateQuery_dyadic_grid a β i
  rw [heq]
  have h := dyadic_encoding_le (i + 1) j hj.le
  omega

theorem coordinateQuery_polynomial_encoding_le (a β : ℚ) (i : ℕ) :
    rationalEncodingLength (coordinatePolynomial a β (coordinateQuery a β i)) ≤
      2 * (rationalEncodingLength a + rationalEncodingLength β) + 76 * i + 255 := by
  have hx := coordinateQuery_encoding_le a β i
  have hp := coordinatePolynomial_encoding_le a β (coordinateQuery a β i)
  omega

theorem coordinateInterval_precision_encoding_le (a β C δ : ℚ) (hδ : 0 < δ) :
    rationalEncodingLength (coordinateInterval a β (oracleDyadicPrecision C δ)).1 ≤
        2 * (rationalEncodingLength C + rationalEncodingLength δ) + 5 ∧
      rationalEncodingLength (coordinateInterval a β (oracleDyadicPrecision C δ)).2 ≤
        2 * (rationalEncodingLength C + rationalEncodingLength δ) + 5 := by
  have hn := oracleDyadicPrecision_encoding_le C δ hδ
  obtain ⟨hl, hu⟩ := coordinateInterval_encoding_le a β (oracleDyadicPrecision C δ)
  constructor <;> omega

end IdentityTesting.RationalComputation
