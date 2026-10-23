import Mathlib.Data.Nat.Find

/-! A tail-recursive certified natural-number search. `Nat.find` appears only
in the termination proof, so its proof-producing recursion is never executed. -/
namespace IdentityTesting.RationalComputation

private theorem search_succ_le {p : ℕ → Prop} [DecidablePred p]
    (H : ∃ n, p n) (n : ℕ) (hn : n ≤ Nat.find H) (hp : ¬ p n) :
    n + 1 ≤ Nat.find H := by
  have hne : n ≠ Nat.find H := by
    intro heq
    exact hp (heq ▸ Nat.find_spec H)
  omega

def certifiedNatSearchFrom (p : ℕ → Prop) [DecidablePred p]
    (H : ∃ n, p n) (n : ℕ) (hn : n ≤ Nat.find H) : {m : ℕ // p m} :=
  if hp : p n then ⟨n, hp⟩ else
    certifiedNatSearchFrom p H (n + 1) (search_succ_le H n hn hp)
termination_by Nat.find H - n
decreasing_by
  have h := search_succ_le H n hn hp
  omega

def certifiedNatSearch (p : ℕ → Prop) [DecidablePred p]
    (H : ∃ n, p n) : {m : ℕ // p m} :=
  certifiedNatSearchFrom p H 0 (Nat.zero_le _)

theorem certifiedNatSearch_spec (p : ℕ → Prop) [DecidablePred p]
    (H : ∃ n, p n) : p (certifiedNatSearch p H).val :=
  (certifiedNatSearch p H).property

end IdentityTesting.RationalComputation
