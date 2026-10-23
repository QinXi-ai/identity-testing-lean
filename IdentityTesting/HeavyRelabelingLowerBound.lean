import IdentityTesting.HeavyRelabelingRoots
import IdentityTesting.HeavyComplexityLowerBound
import IdentityTesting.FiniteTestingRelabeling

/-! # Original heavy lower bound for arbitrary finite references, zeros allowed -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

open Classical FiniteTesting EmpiricalSeeds HeavySignedFamily

theorem exists_positive_head_finite_embedding {m : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin m)) (hp : ∀ i, 0 < p.mass i)
    (e : Fin m → ℕ) (he : Function.Injective e)
    (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0) :
    ∃ (k : ℕ) (r : Probability (Fin (k + 1))) (a : Fin (k + 1) → ℕ),
      Function.Injective a ∧ (∀ i, 0 < r.mass i) ∧
      (∀ i, q.mass (a i) = r.mass i) ∧
      (∀ n, n ∉ Set.range a → q.mass n = 0) ∧ r.mass 0 = largestMass q := by
  cases m with
  | zero =>
      have ht := p.total
      norm_num at ht
  | succ k =>
      have hmem : largestIndex q ∈ Set.range e := by
        by_contra hn
        have hz := hoff (largestIndex q) hn
        rw [← largestMass_eq_selected] at hz
        exact (ne_of_gt (largestMass_pos q)) hz
      obtain ⟨j, hj⟩ := hmem
      let s : Fin (k + 1) ≃ Fin (k + 1) := Equiv.swap 0 j
      let r := mapLaw p s
      let a : Fin (k + 1) → ℕ := fun i => e (s.symm i)
      have hr (i : Fin (k + 1)) : r.mass i = p.mass (s.symm i) := by
        have h := mapLaw_mass_injective p s s.injective (s.symm i)
        simpa only [Equiv.apply_symm_apply] using h
      have hjmass : p.mass j = largestMass q := by
        rw [← hmass, hj, ← largestMass_eq_selected]
      refine ⟨k, r, a, he.comp s.symm.injective, ?_, ?_, ?_, ?_⟩
      · intro i
        rw [hr]
        exact hp _
      · intro i
        exact (hmass (s.symm i)).trans (hr i).symm
      · intro n hn
        apply hoff n
        rintro ⟨i, hi⟩
        apply hn
        refine ⟨s i, ?_⟩
        simpa only [a, Equiv.symm_apply_apply] using hi
      · rw [hr]
        have hswap : s.symm 0 = j := by simp [s]
        rw [hswap]
        exact hjmass

theorem exists_positive_heavy_representation {l : ℕ} (q : Probability (Fin l)) :
    ∃ (k : ℕ) (r : Probability (Fin (k + 1))) (a : Fin (k + 1) → ℕ),
      Function.Injective a ∧ (∀ i, 0 < r.mass i) ∧
      (∀ i, (extendFiniteLaw q).mass (a i) = r.mass i) ∧
      (∀ n, n ∉ Set.range a → (extendFiniteLaw q).mass n = 0) ∧
        r.mass 0 = largestMass (extendFiniteLaw q) := by
  obtain ⟨hm, hz⟩ := positiveFiniteLaw_countable_embedding q
  exact exists_positive_head_finite_embedding (extendFiniteLaw q) (positiveFiniteLaw q)
    (positiveFiniteLaw_pos q) (fun i => (positiveEnumeration q i).val)
    (Fin.val_injective.comp (positiveEnumeration_injective q)) hm hz

theorem no_identityTest_of_finite_heavy_complexityScale_with_zeros {l : ℕ}
    (q : Probability (Fin l))
    (hh : (3 : ℝ) / 4 < largestMass (extendFiniteLaw q))
    (hh1 : largestMass (extendFiniteLaw q) < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 11) * complexityScale (extendFiniteLaw q) ε) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  obtain ⟨k, r, a, ha, hr, hm, hz, hhead⟩ := exists_positive_heavy_representation q
  have ht := reference_head_tail r
  have hR0 : 0 < tailTotal r := by linarith only [ht, hhead, hh1]
  have hR : tailTotal r < (1 : ℝ) / 4 := by linarith only [ht, hhead, hh]
  have hscale := complexityScale_of_heavy_finite_embedding (extendFiniteLaw q) r hr a ha hm hz hR ε
  have hno := no_identityTest_of_finite_heavy_complexityScale r hr hR0 hR hε0 hε1 n (by rwa [← hscale])
  exact fun htest => hno (hasIdentityTest_of_finite_embedding (extendFiniteLaw q) r a ha hm hz ε n htest)

theorem finite_heavy_roundedScale_lower_with_zeros {l : ℕ}
    (q : Probability (Fin l))
    (hh : (3 : ℝ) / 4 < largestMass (extendFiniteLaw q))
    (hh1 : largestMass (extendFiniteLaw q) < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (htest : HasIdentityTest (extendFiniteLaw q) ε n) :
    (1 / (10 : ℝ) ^ 11) * (roundedScale (extendFiniteLaw q) ε : ℝ) ≤ n := by
  have hscale : (1 / (10 : ℝ) ^ 11) * complexityScale (extendFiniteLaw q) ε < (n : ℝ) := by
    apply lt_of_not_ge
    intro hn
    exact no_identityTest_of_finite_heavy_complexityScale_with_zeros q hh hh1 hε0 hε1 n hn htest
  have hceil : roundedScale (extendFiniteLaw q) ε ≤ 100000000000 * n := by
    apply Nat.ceil_le.mpr
    push_cast
    norm_num at hscale ⊢
    linarith only [hscale]
  have hreal : (roundedScale (extendFiniteLaw q) ε : ℝ) ≤ 100000000000 * (n : ℝ) := by
    exact_mod_cast hceil
  norm_num
  linarith only [hreal]

end IdentityTesting
