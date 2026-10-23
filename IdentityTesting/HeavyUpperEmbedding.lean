import IdentityTesting.FiniteTestingRelabeling
import Mathlib.Logic.Equiv.Fintype

/-! Finite injective placements extend to permutations of the whole countable
alphabet. This yields a lossless upper-test transfer for every alternative. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting
open Classical FiniteTesting

private theorem embedding_law_ext {p q : DiscreteLaw} (h : ∀ n, p.mass n = q.mass n) : p = q := by
  cases p
  cases q
  congr 1
  exact funext h

theorem exists_permutation_extension {k : ℕ} (e : Fin k → ℕ) (he : Function.Injective e) :
    ∃ f : Equiv.Perm ℕ, ∀ i : Fin k, f i.val = e i := by
  let M := k + (∑ i, e i) + 1
  have hkM : k ≤ M := by dsimp [M]; omega
  have heM : ∀ i, e i < M := by
    intro i
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (e j))
      (Finset.mem_univ i)
    dsimp [M]
    omega
  let l : Fin k ↪ Fin M := ⟨Fin.castLE hkM, Fin.castLE_injective hkM⟩
  let r : Fin k ↪ Fin M := ⟨(fun i => ⟨e i, heM i⟩), by
    intro i j h
    exact he (congrArg Fin.val h)⟩
  let s : Set.range l ≃ Set.range r := l.toEquivRange.symm.trans r.toEquivRange
  let g : Equiv.Perm (Fin M) := s.extendSubtype
  have hg : ∀ i, g (l i) = r i := by
    intro i
    rw [show g = s.extendSubtype from rfl, Equiv.extendSubtype_apply_of_mem s (l i) (Set.mem_range_self i)]
    simp only [s, Equiv.trans_apply, Function.Embedding.toEquivRange_symm_apply_self,
      Function.Embedding.toEquivRange_apply]
  let v : Fin M ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  refine ⟨g.viaFintypeEmbedding v, ?_⟩
  intro i
  have h := Equiv.Perm.viaFintypeEmbedding_apply_image g v (l i)
  rw [hg] at h
  exact h

theorem injectLaw_permutation_inverse (f : Equiv.Perm ℕ) (q : DiscreteLaw) :
    injectLaw f.symm f.symm.injective (injectLaw f f.injective q) = q := by
  have hm : ∀ n, (injectLaw f.symm f.symm.injective (injectLaw f f.injective q)).mass n = q.mass n := by
    intro n
    have hn : n = f.symm (f n) := (f.symm_apply_apply n).symm
    conv_lhs => rw [hn]
    change injectMass f.symm (injectLaw f f.injective q) (f.symm (f n)) = q.mass n
    rw [injectMass_apply f.symm f.symm.injective]
    change injectMass f q (f n) = q.mass n
    exact injectMass_apply f f.injective q n
  exact embedding_law_ext hm

theorem hasIdentityTest_of_finite_embedding_upper {k : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin k))
    (e : Fin k → ℕ) (he : Function.Injective e)
    (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0)
    (ε : ℝ) (n : ℕ) :
    HasIdentityTest (extendFiniteLaw p) ε n → HasIdentityTest q ε n := by
  obtain ⟨f, hf⟩ := exists_permutation_extension e he
  have heq := injectLaw_extendFiniteLaw_eq q p e hmass hoff f f.injective hf
  intro ht
  apply hasIdentityTest_of_injectLaw f.symm f.symm.injective q ε n
  rw [← heq, injectLaw_permutation_inverse]
  exact ht

end IdentityTesting
