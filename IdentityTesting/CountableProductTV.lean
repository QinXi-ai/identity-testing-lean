import IdentityTesting.Sampling
import IdentityTesting.NormalizedTruncation

/-! Product TV and expectation stability for the original countable IID model. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem totalVariation_triangle (p q r : DiscreteLaw) :
    totalVariation p r ≤ totalVariation p q + totalVariation q r := by
  have h := (p.summable_abs_sub r).tsum_le_tsum
    (fun i => abs_sub_le (p.mass i) (q.mass i) (r.mass i))
    ((p.summable_abs_sub q).add (q.summable_abs_sub r))
  rw [(p.summable_abs_sub q).tsum_add (q.summable_abs_sub r)] at h
  unfold totalVariation
  linarith

def sampleTotalVariation (p q : DiscreteLaw) (n : ℕ) : ℝ :=
  (∑' x : Sample n, |sampleMass p n x - sampleMass q n x|) / 2

theorem sample_abs_sub_summable (p q : DiscreteLaw) (n : ℕ) :
    Summable (fun x : Sample n => |sampleMass p n x - sampleMass q n x|) :=
  ((sampleMass_hasSum p n).summable.sub (sampleMass_hasSum q n).summable).abs

set_option maxHeartbeats 1200000 in
theorem sample_l1_succ_le (p q : DiscreteLaw) (n : ℕ) :
    (∑' x : Sample (n + 1), |sampleMass p (n + 1) x - sampleMass q (n + 1) x|) ≤
      (∑' x : Sample n, |sampleMass p n x - sampleMass q n x|) +
        ∑' i, |p.mass i - q.mass i| := by
  let e : ℕ × Sample n ≃ Sample (n + 1) := Fin.consEquiv (fun _ => ℕ)
  let f : ℕ × Sample n → ℝ := fun z =>
    p.mass z.1 * |sampleMass p n z.2 - sampleMass q n z.2|
  let g : ℕ × Sample n → ℝ := fun z =>
    |p.mass z.1 - q.mass z.1| * sampleMass q n z.2
  have hf : HasSum f (∑' x : Sample n, |sampleMass p n x - sampleMass q n x|) := by
    have h := HasSum.mul (f := p.mass)
      (g := fun x : Sample n => |sampleMass p n x - sampleMass q n x|)
      p.summable.hasSum (sample_abs_sub_summable p q n).hasSum
      (Summable.mul_of_nonneg p.summable (sample_abs_sub_summable p q n)
        p.nonneg (fun _ => abs_nonneg _))
    simpa [f, p.total] using h
  have hg : HasSum g (∑' i, |p.mass i - q.mass i|) := by
    have h := HasSum.mul (f := fun i => |p.mass i - q.mass i|) (g := sampleMass q n)
      (p.summable_abs_sub q).hasSum (sampleMass_hasSum q n)
      (Summable.mul_of_nonneg (p.summable_abs_sub q) (sampleMass_hasSum q n).summable
        (fun _ => abs_nonneg _) (sampleMass_nonneg q n))
    simpa [g] using h
  have hleft := (e.summable_iff).2 (sample_abs_sub_summable p q (n + 1))
  have hb : ∀ z : ℕ × Sample n,
      |sampleMass p (n + 1) (e z) - sampleMass q (n + 1) (e z)| ≤ f z + g z := by
    intro z
    simp only [sampleMass, e, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    change |p.mass z.1 * sampleMass p n z.2 - q.mass z.1 * sampleMass q n z.2| ≤ _
    calc
      _ = |p.mass z.1 * (sampleMass p n z.2 - sampleMass q n z.2) +
          (p.mass z.1 - q.mass z.1) * sampleMass q n z.2| := by congr 1; ring
      _ ≤ _ := by
        simpa [f, g, abs_mul, abs_of_nonneg (p.nonneg z.1),
          abs_of_nonneg (sampleMass_nonneg q n z.2)] using
            abs_add_le (p.mass z.1 * (sampleMass p n z.2 - sampleMass q n z.2))
              ((p.mass z.1 - q.mass z.1) * sampleMass q n z.2)
  have hh := hleft.tsum_le_tsum hb (hf.summable.add hg.summable)
  rw [e.tsum_eq (fun x : Sample (n + 1) => |sampleMass p (n + 1) x - sampleMass q (n + 1) x|),
    (hf.add hg).tsum_eq] at hh
  exact hh

/-- The product-coupling bound for arbitrary countable reference laws. -/
theorem sampleTotalVariation_le_mul (p q : DiscreteLaw) (n : ℕ) :
    sampleTotalVariation p q n ≤ (n : ℝ) * totalVariation p q := by
  induction n with
  | zero => simp [sampleTotalVariation, sampleMass]
  | succ n ih =>
    have h := sample_l1_succ_le p q n
    unfold sampleTotalVariation totalVariation at *
    push_cast
    nlinarith

theorem rejectionProbability_sub_le_sampleTotalVariation (p q : DiscreteLaw)
    {n : ℕ} (test : RandomizedTest n) :
    rejectionProbability p test - rejectionProbability q test ≤ sampleTotalVariation p q n := by
  let d : Sample n → ℝ := fun x => sampleMass p n x - sampleMass q n x
  have hd : Summable d := (sampleMass_hasSum p n).summable.sub (sampleMass_hasSum q n).summable
  have hbound : ∀ x,
      sampleMass p n x * test.reject x - sampleMass q n x * test.reject x ≤
        (|d x| + d x) / 2 := by
    intro x
    by_cases hdx : 0 ≤ d x
    · rw [abs_of_nonneg hdx]
      have h := mul_le_mul_of_nonneg_left (test.le_one x) hdx
      dsimp [d] at *
      nlinarith
    · rw [abs_of_nonpos (le_of_not_ge hdx)]
      have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hdx) (test.nonneg x)
      dsimp [d] at *
      nlinarith
  have h := ((rejection_summable p test).sub (rejection_summable q test)).tsum_le_tsum
    hbound ((hd.abs.add hd).div_const 2)
  rw [(rejection_summable p test).tsum_sub (rejection_summable q test),
    tsum_div_const, hd.abs.tsum_add hd] at h
  have hz : (∑' x, d x) = 0 := by
    dsimp [d]
    rw [(sampleMass_hasSum p n).summable.tsum_sub (sampleMass_hasSum q n).summable,
      (sampleMass_hasSum p n).tsum_eq, (sampleMass_hasSum q n).tsum_eq]
    ring
  rw [hz, add_zero] at h
  exact h

theorem normalized_sample_tv_le (q : DiscreteLaw) (m n : ℕ)
    (hr : residualMass q (Finset.range m) < 1) :
    sampleTotalVariation (prefixNormalizedLaw q m) q n ≤
      (n : ℝ) * residualMass q (Finset.range m) := by
  simpa only [totalVariation_prefixNormalized q m hr] using
    sampleTotalVariation_le_mul (prefixNormalizedLaw q m) q n

/-- The same original randomized test has errors 3/8 and 1/3 after truncation.
The strict alternative inequality includes the manuscript's extra r margin. -/
theorem normalized_test_errors (q : DiscreteLaw) (m n : ℕ) (ε : ℝ)
    (hr : residualMass q (Finset.range m) < 1)
    (hnr : (n : ℝ) * residualMass q (Finset.range m) ≤ 1 / 24)
    (test : RandomizedTest n) (htest : IsIdentityTest q ε test) :
    rejectionProbability (prefixNormalizedLaw q m) test ≤ 3 / 8 ∧
      ∀ p, ε + 2 * residualMass q (Finset.range m) <
        totalVariation p (prefixNormalizedLaw q m) → acceptanceProbability p test ≤ 1 / 3 := by
  constructor
  · have h := rejectionProbability_sub_le_sampleTotalVariation (prefixNormalizedLaw q m) q test
    have htv := normalized_sample_tv_le q m n hr
    linarith [htest.1]
  · intro p hp
    apply htest.2 p
    have hr0 : 0 ≤ residualMass q (Finset.range m) := tsum_nonneg (fun i => q.nonneg i)
    have htri := totalVariation_triangle p (prefixNormalizedLaw q m) q
    have htri' := totalVariation_triangle p q (prefixNormalizedLaw q m)
    have hsym : totalVariation q (prefixNormalizedLaw q m) =
        totalVariation (prefixNormalizedLaw q m) q := by
      unfold totalVariation
      congr 1
      apply tsum_congr
      intro i
      exact abs_sub_comm _ _
    rw [hsym, totalVariation_prefixNormalized q m hr] at htri'
    linarith

end IdentityTesting
