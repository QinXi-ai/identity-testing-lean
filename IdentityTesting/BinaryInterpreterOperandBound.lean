import IdentityTesting.BinaryInterpreterOperandRuns

namespace IdentityTesting.BinaryInterpreterOperand
open BinaryInterpreterLayout BinaryRegisterMachine RationalComputation BinaryRationalRegisters
variable {L : Layout} (I : InputLocal L)
include I

/-- Both operand forms are read from the actual code tape, including their
discriminator. The validity hypothesis only bounds register addresses. -/
theorem operand_run (right : Bool) (c : L.Core) (s : RationalRegisters) (o : RationalOperand)
    (ho : o.slots ≤ s.length) (code history : List Symbol)
    (hc : L.input right c = BinaryInterpreterArithmetic.emptyWord) :
    ∃ n, n ≤ 20 * (rationalRegisterEncoding s + s.length + rationalEncodingLength (o.read s) + o.slots + 1) ∧
      Loaded right c (tape s) code ((RationalProgramCode.operand o).reverse ++ history)
        (BinaryRationalArithmetic.encode (o.read s))
        (advance right n (initial c (tape s) (RationalProgramCode.operand o ++ code) history)) := by
  cases o with
  | literal q =>
      obtain ⟨n, hn, hrun⟩ := literal_operand_run I right c (tape s) code history q hc
      refine ⟨n, ?_, hrun⟩
      change n ≤ 20 * (rationalRegisterEncoding s + s.length + rationalEncodingLength q + 0 + 1)
      omega
  | reg a =>
      have ha : a < s.length := by change a+1 ≤ s.length at ho; omega
      have hr : (RationalOperand.reg a).read s = s[a] := by
        simp [RationalOperand.read, List.getElem?_eq_getElem ha]
      obtain ⟨n, hn, hrun⟩ := register_operand_run I right c s a ha code history hc
      rw [tape_length] at hn
      refine ⟨n, ?_, ?_⟩
      · rw [hr]
        change n ≤ 20 * (rationalRegisterEncoding s + s.length + rationalEncodingLength s[a] + (a+1) + 1)
        omega
      · simpa only [hr] using hrun

theorem operand_load (right : Bool) (c : L.Core) (s : RationalRegisters) (o : RationalOperand)
    (ho : o.slots ≤ s.length) (code history : List Symbol)
    (hc : L.input right c = BinaryInterpreterArithmetic.emptyWord) :
    ∃ n,
      let start := initial c (tape s) (RationalProgramCode.operand o ++ code) history
      let final := advance right n start
      Loaded right c (tape s) code ((RationalProgramCode.operand o).reverse ++ history)
        (BinaryRationalArithmetic.encode (o.read s)) final ∧
      L.input right final.data.core = BinaryRationalArithmetic.encode (o.read s) ∧
      L.input (!right) final.data.core = L.input (!right) c ∧
      bitSteps right n start ≤
        300 * (rationalRegisterEncoding s + s.length + rationalEncodingLength (o.read s) + o.slots + 1) := by
  obtain ⟨n, hn, hrun⟩ := operand_run I right c s o ho code history hc
  refine ⟨n, hrun, ?_, ?_, ?_⟩
  · rw [hrun.2.1, I.get_set]
  · rw [hrun.2.1, I.other]
  · have h := bitSteps_le right n (initial c (tape s) (RationalProgramCode.operand o ++ code) history)
    omega

omit I in
def rearm (s : State L) : State L :=
  { s with
    phase := .kind
    data := {s.data with phase := .sign, fieldPhase := .reading}
    readPhase := .reading
    seekPhase := .seek
    splitPhase := .sign }

omit I in
theorem rearm_clean (s : State L) (h : Clean s) :
    rearm s = initial s.data.core s.tape s.data.code s.data.history := by
  rcases h with ⟨ht, ha, hs, hc, hr, hn, hd⟩
  cases s
  simp_all [rearm, initial, BinaryInterpreterLiteralInput.initial]

omit I in
theorem rearm_preserves_stacks (s : State L) :
    (rearm s).data.core = s.data.core ∧ (rearm s).data.code = s.data.code ∧
    (rearm s).data.history = s.data.history ∧ (rearm s).data.temp = s.data.temp ∧
    (rearm s).tape = s.tape ∧ (rearm s).address = s.address ∧ (rearm s).saved = s.saved ∧
    (rearm s).copyTemp = s.copyTemp ∧ (rearm s).record = s.record ∧
    (rearm s).numWork = s.numWork ∧ (rearm s).denWork = s.denWork := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end IdentityTesting.BinaryInterpreterOperand
