import IdentityTesting.BinaryDivisionMachine
import IdentityTesting.BinaryLongDivision

namespace IdentityTesting.BinaryDivisionMachine
open BinaryArithmetic

theorem init_run (xs bs d : List Bool) (a : BinarySubtractorMachine.State)
    (q r : BinaryWordNormalization.State) :
    Runs ⟨.init, xs, bs, d, [], a, q, r⟩ (xs.length + 1)
      ⟨.scan, [], xs.reverse ++ bs, d, [], a, q, r⟩ := by
  induction xs generalizing bs with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.init, xs, b :: bs, d, [], a, q, r⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b :: bs)]
      simp [List.reverse_cons, List.append_assoc]

theorem dToTmp_run (bs d tmp q r : List Bool) (a : BinarySubtractorMachine.State) :
    Runs ⟨.dToTmp, [], bs, d, tmp, a, word q, word r⟩ (d.length + 1)
      ⟨.tmpToD, [], bs, [], d.reverse ++ tmp, a, word q, word r⟩ := by
  induction d generalizing tmp with
  | nil => rfl
  | cons b ds ih =>
      change advance (ds.length + 1 + 1) _ = _
      rw [advance]
      change advance (ds.length + 1) ⟨.dToTmp, [], bs, ds, b :: tmp, a, word q, word r⟩ = _
      rw [show advance (ds.length + 1) _ = _ from ih (b :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToD_run (bs d tmp q r : List Bool) (a : BinarySubtractorMachine.State) :
    Runs ⟨.tmpToD, [], bs, d, tmp, a, word q, word r⟩ (tmp.length + 1)
      ⟨.rToTmp, [], bs, tmp.reverse ++ d, [], { a with right := tmp.reverse ++ a.right }, word q, word r⟩ := by
  induction tmp generalizing d a with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1)
        ⟨.tmpToD, [], bs, b :: d, xs, { a with right := b :: a.right }, word q, word r⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b :: d) { a with right := b :: a.right }]
      simp [List.reverse_cons, List.append_assoc]

theorem rToTmp_run (bs d tmp q r : List Bool) (a : BinarySubtractorMachine.State) :
    Runs ⟨.rToTmp, [], bs, d, tmp, a, word q, word r⟩ (r.length + 1)
      ⟨.tmpToR, [], bs, d, r.reverse ++ tmp, a, word q, word []⟩ := by
  induction r generalizing tmp with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.rToTmp, [], bs, d, b :: tmp, a, word q, word xs⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToR_run (bs d tmp q r : List Bool) (a : BinarySubtractorMachine.State) :
    Runs ⟨.tmpToR, [], bs, d, tmp, a, word q, word r⟩ (tmp.length + 1)
      ⟨.startSub, [], bs, d, [], { a with left := tmp.reverse ++ a.left }, word q,
        word (tmp.reverse ++ r)⟩ := by
  induction tmp generalizing r a with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1)
        ⟨.tmpToR, [], bs, d, xs, { a with left := b :: a.left }, word q, word (b :: r)⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b :: r) { a with left := b :: a.left }]
      simp [List.reverse_cons, List.append_assoc]

theorem clearDiff_run (bs d q r out : List Bool) (a : BinarySubtractorMachine.State) :
    Runs ⟨.clearDiff, [], bs, d, [], { a with out := out }, word q, word r⟩ (out.length + 1)
      ⟨.scan, [], bs, d, [], { a with out := [] }, word q, word r⟩ := by
  induction out with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      exact ih

theorem clearRem_run (bs d q r : List Bool) (a : BinarySubtractorMachine.State) :
    Runs ⟨.clearRem, [], bs, d, [], a, word q, word r⟩ (r.length + 1)
      ⟨.diffToTmp, [], bs, d, [], a, word q, word []⟩ := by
  induction r with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      exact ih

theorem diffToTmp_run (bs d tmp q out : List Bool) (a : BinarySubtractorMachine.State) :
    Runs ⟨.diffToTmp, [], bs, d, tmp, { a with out := out }, word q, word []⟩ (out.length + 1)
      ⟨.tmpToRem, [], bs, d, out.reverse ++ tmp, { a with out := [] }, word q, word []⟩ := by
  induction out generalizing tmp with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1)
        ⟨.diffToTmp, [], bs, d, b :: tmp, { a with out := xs }, word q, word []⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToRem_run (bs d tmp q r : List Bool) (a : BinarySubtractorMachine.State) :
    Runs ⟨.tmpToRem, [], bs, d, tmp, a, word q, word r⟩ (tmp.length + 1)
      ⟨.scan, [], bs, d, [], a, word q, word (tmp.reverse ++ r)⟩ := by
  induction tmp generalizing r with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.tmpToRem, [], bs, d, xs, a, word q, word (b :: r)⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b :: r)]
      simp [List.reverse_cons, List.append_assoc]

private theorem sub_advance_halt (n : ℕ) (a : BinarySubtractorMachine.State) (h : a.phase = .halt) :
    BinarySubtractorMachine.advance n a = a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinarySubtractorMachine.advance, BinarySubtractorMachine.step,
      BinaryAdderMachine.step, h] using ih

theorem forward_sub (bs d q r : List Bool) (a : BinarySubtractorMachine.State) (n : ℕ)
    (h : (BinarySubtractorMachine.advance n a).phase = .halt) :
    ∃ k, k ≤ n + 1 ∧ Runs ⟨.subtracting, [], bs, d, [], a, word q, word r⟩ k
      ⟨.decide, [], bs, d, [], BinarySubtractorMachine.advance n a, word q, word r⟩ := by
  induction n generalizing a with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinarySubtractorMachine.advance] at h
      simp [Runs, advance, step, h, BinarySubtractorMachine.advance]
  | succ n ih =>
      by_cases hh : a.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [sub_advance_halt (n + 1) a hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨k, hk, he⟩ := ih (BinarySubtractorMachine.step a) h
        refine ⟨k + 1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinarySubtractorMachine.advance] using he

private theorem norm_advance_halt (n : ℕ) (a : BinaryWordNormalization.State) (h : a.phase = .halt) :
    BinaryWordNormalization.advance n a = a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryWordNormalization.advance, BinaryWordNormalization.step, h] using ih

theorem forward_normQ (d : List Bool) (a : BinarySubtractorMachine.State)
    (q r : BinaryWordNormalization.State) (n : ℕ)
    (h : (BinaryWordNormalization.advance n q).phase = .halt) :
    ∃ k, k ≤ n + 1 ∧ Runs ⟨.normQ, [], [], d, [], a, q, r⟩ k
      ⟨.normR, [], [], d, [], a, BinaryWordNormalization.advance n q, r⟩ := by
  induction n generalizing q with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinaryWordNormalization.advance] at h
      simp [Runs, advance, step, h, BinaryWordNormalization.advance]
  | succ n ih =>
      by_cases hh : q.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [norm_advance_halt (n + 1) q hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨k, hk, he⟩ := ih (BinaryWordNormalization.step q) h
        refine ⟨k + 1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinaryWordNormalization.advance] using he

theorem forward_normR (d : List Bool) (a : BinarySubtractorMachine.State)
    (q r : BinaryWordNormalization.State) (n : ℕ)
    (h : (BinaryWordNormalization.advance n r).phase = .halt) :
    ∃ k, k ≤ n + 1 ∧ Runs ⟨.normR, [], [], d, [], a, q, r⟩ k
      ⟨.halt, [], [], d, [], a, q, BinaryWordNormalization.advance n r⟩ := by
  induction n generalizing r with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinaryWordNormalization.advance] at h
      simp [Runs, advance, step, h, BinaryWordNormalization.advance]
  | succ n ih =>
      by_cases hh : r.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [norm_advance_halt (n + 1) r hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨k, hk, he⟩ := ih (BinaryWordNormalization.step r) h
        refine ⟨k + 1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinaryWordNormalization.advance] using he

def terminal (d q r : List Bool) (regs : BinarySubtractorMachine.Registers) : State :=
  ⟨.halt, [], [], d, [], BinarySubtractorMachine.haltState regs [],
    ⟨.halt, [], [], q⟩, ⟨.halt, [], [], r⟩⟩

theorem finish_run (d q r : List Bool) (regs : BinarySubtractorMachine.Registers) :
    ∃ n, n ≤ 2 * q.length + 2 * r.length + 7 ∧
      Runs (ready [] d q r regs) n
        (terminal d (BinaryWordNormalization.trim q) (BinaryWordNormalization.trim r) regs) := by
  let a := BinarySubtractorMachine.haltState regs []
  have hq := BinaryWordNormalization.normalization_run q
  have hr := BinaryWordNormalization.normalization_run r
  have hqh : (BinaryWordNormalization.advance (2 * q.length + 2) (word q)).phase = .halt := by
    rw [show word q = ⟨.collect, q, [], []⟩ from rfl, hq]
  obtain ⟨kq, hkq, hqr⟩ := forward_normQ d a (word q) (word r) _ hqh
  have hqr' : Runs ⟨.normQ, [], [], d, [], a, word q, word r⟩ kq
      ⟨.normR, [], [], d, [], a, ⟨.halt, [], [], BinaryWordNormalization.trim q⟩, word r⟩ := by
    simpa only [word, hq] using hqr
  have hrh : (BinaryWordNormalization.advance (2 * r.length + 2) (word r)).phase = .halt := by
    rw [show word r = ⟨.collect, r, [], []⟩ from rfl, hr]
  obtain ⟨kr, hkr, hrr⟩ := forward_normR d a ⟨.halt, [], [], BinaryWordNormalization.trim q⟩ (word r) _ hrh
  have hrr' : Runs ⟨.normR, [], [], d, [], a, ⟨.halt, [], [], BinaryWordNormalization.trim q⟩, word r⟩ kr
      (terminal d (BinaryWordNormalization.trim q) (BinaryWordNormalization.trim r) regs) := by
    simpa only [word, hr, terminal, a] using hrr
  have h0 : Runs (ready [] d q r regs) 1 ⟨.normQ, [], [], d, [], a, word q, word r⟩ := rfl
  exact ⟨_, by omega, (h0.trans hqr').trans hrr'⟩

end IdentityTesting.BinaryDivisionMachine
