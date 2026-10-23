import IdentityTesting.Sampling

/-! Injective relabeling preserves the full countable testing experiment. -/
noncomputable section
namespace IdentityTesting
open scoped BigOperators
open Classical

def injectMass (f : ℕ → ℕ) (p : DiscreteLaw) (j : ℕ) : ℝ :=
  if h : j ∈ Set.range f then p.mass (Classical.choose h) else 0

theorem injectMass_apply (f : ℕ → ℕ) (hf : Function.Injective f)
    (p : DiscreteLaw) (i : ℕ) : injectMass f p (f i) = p.mass i := by
  unfold injectMass
  rw [dif_pos (Set.mem_range_self i)]
  exact congrArg p.mass (hf (Classical.choose_spec (Set.mem_range_self i)))

theorem injectMass_off (f : ℕ → ℕ) (p : DiscreteLaw) (j : ℕ)
    (hj : j ∉ Set.range f) : injectMass f p j = 0 := by
  exact dif_neg hj

theorem injectMass_hasSum (f : ℕ → ℕ) (hf : Function.Injective f)
    (p : DiscreteLaw) : HasSum (injectMass f p) 1 := by
  apply (hf.hasSum_iff (f := injectMass f p) (a := 1) (injectMass_off f p)).mp
  have hc : injectMass f p ∘ f = p.mass := by
    funext i
    exact injectMass_apply f hf p i
  rw [hc]
  simpa only [p.total] using p.summable.hasSum

def injectLaw (f : ℕ → ℕ) (hf : Function.Injective f) (p : DiscreteLaw) : DiscreteLaw where
  mass := injectMass f p
  nonneg j := by unfold injectMass; split; exact p.nonneg _; exact le_rfl
  summable := (injectMass_hasSum f hf p).summable
  total := (injectMass_hasSum f hf p).tsum_eq

theorem totalVariation_injectLaw (f : ℕ → ℕ) (hf : Function.Injective f)
    (p q : DiscreteLaw) : totalVariation (injectLaw f hf p) (injectLaw f hf q) =
      totalVariation p q := by
  have hz : ∀ j, j ∉ Set.range f → |injectMass f p j - injectMass f q j| = 0 := by
    intro j hj
    rw [injectMass_off f p j hj, injectMass_off f q j hj]
    simp
  have hc : (fun j => |injectMass f p j - injectMass f q j|) ∘ f =
      (fun i => |p.mass i - q.mass i|) := by
    funext i
    simp only [Function.comp_apply, injectMass_apply f hf]
  have hs := (hf.hasSum_iff (f := fun j => |injectMass f p j - injectMass f q j|)
    (a := ∑' i, |p.mass i - q.mass i|) hz).mp (by
      rw [hc]
      exact (p.summable_abs_sub q).hasSum)
  exact congrArg (fun x : ℝ => x / 2) hs.tsum_eq

def injectSample (f : ℕ → ℕ) {n : ℕ} (x : Sample n) : Sample n := f ∘ x

theorem injectSample_injective (f : ℕ → ℕ) (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (injectSample f (n := n)) := by
  intro x y h
  funext i
  exact hf (congrFun h i)

theorem sampleMass_injectLaw_apply (f : ℕ → ℕ) (hf : Function.Injective f)
    (p : DiscreteLaw) (n : ℕ) (x : Sample n) :
    sampleMass (injectLaw f hf p) n (injectSample f x) = sampleMass p n x := by
  simp only [sampleMass, injectLaw, injectSample, Function.comp_apply, injectMass_apply f hf]

theorem sampleMass_injectLaw_off (f : ℕ → ℕ) (hf : Function.Injective f)
    (p : DiscreteLaw) (n : ℕ) (x : Sample n)
    (hx : x ∉ Set.range (injectSample f (n := n))) :
    sampleMass (injectLaw f hf p) n x = 0 := by
  have hn : ¬ ∀ i, x i ∈ Set.range f := by
    intro h
    apply hx
    refine ⟨fun i => Classical.choose (h i), ?_⟩
    funext i
    exact Classical.choose_spec (h i)
  obtain ⟨i, hi⟩ := not_forall.mp hn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (injectMass_off f p (x i) hi)

def pullInjectTest (f : ℕ → ℕ) {n : ℕ} (test : RandomizedTest n) : RandomizedTest n where
  reject x := test.reject (injectSample f x)
  nonneg x := test.nonneg _
  le_one x := test.le_one _

theorem rejectionProbability_injectLaw (f : ℕ → ℕ) (hf : Function.Injective f)
    (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) :
    rejectionProbability (injectLaw f hf p) test = rejectionProbability p (pullInjectTest f test) := by
  let g := fun x => sampleMass (injectLaw f hf p) n x * test.reject x
  have hz : ∀ x, x ∉ Set.range (injectSample f (n := n)) → g x = 0 := by
    intro x hx
    simp only [g, sampleMass_injectLaw_off f hf p n x hx, zero_mul]
  have hc : g ∘ injectSample f =
      (fun x => sampleMass p n x * (pullInjectTest f test).reject x) := by
    funext x
    simp only [Function.comp_apply, g, sampleMass_injectLaw_apply, pullInjectTest]
  have hs := ((injectSample_injective f hf n).hasSum_iff
    (f := g) (a := rejectionProbability p (pullInjectTest f test)) hz).mp (by
      rw [hc]
      exact (rejection_summable p (pullInjectTest f test)).hasSum)
  exact hs.tsum_eq

theorem acceptanceProbability_injectLaw (f : ℕ → ℕ) (hf : Function.Injective f)
    (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) :
    acceptanceProbability (injectLaw f hf p) test = acceptanceProbability p (pullInjectTest f test) := by
  have h₁ := rejection_add_acceptance (injectLaw f hf p) test
  have h₂ := rejection_add_acceptance p (pullInjectTest f test)
  rw [rejectionProbability_injectLaw] at h₁
  linarith

theorem hasIdentityTest_of_injectLaw (f : ℕ → ℕ) (hf : Function.Injective f)
    (q : DiscreteLaw) (ε : ℝ) (n : ℕ) :
    HasIdentityTest (injectLaw f hf q) ε n → HasIdentityTest q ε n := by
  rintro ⟨test, hnull, halt⟩
  refine ⟨pullInjectTest f test, ?_, ?_⟩
  · rwa [← rejectionProbability_injectLaw]
  · intro p hp
    rw [← acceptanceProbability_injectLaw f hf p test]
    apply halt (injectLaw f hf p)
    rwa [totalVariation_injectLaw]

end IdentityTesting
