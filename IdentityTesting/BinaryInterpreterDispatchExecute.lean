import IdentityTesting.BinaryInterpreterDispatch

namespace IdentityTesting.BinaryInterpreterDispatch
open BinaryRegisterMachine RationalComputation BinaryInterpreterArithmetic

def execLift (frame : State) (op : RationalOp)
    (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) : State :=
  {setExec frame op e with phase := .running, selected := op}

theorem execView_lift (frame : State) (op : RationalOp)
    (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) :
    execView (execLift frame op e) op = e := execView_set frame op e

theorem step_execLift (frame : State) (op : RationalOp)
    (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) :
    step (execLift frame op e) = execLift frame op
      (BinaryInterpreterOperandExecute.step (arithmeticStorage op) e) := by
  change setExec (execLift frame op e) op
    (BinaryInterpreterOperandExecute.step (arithmeticStorage op) (execView (execLift frame op e) op)) = _
  rw [execView_lift]
  change {setExec (setExec frame op e) op
    (BinaryInterpreterOperandExecute.step (arithmeticStorage op) e) with phase := .running, selected := op} = _
  rw [setExec_set]
  rfl

theorem trace_execLift (frame : State) (op : RationalOp)
    (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) :
    transitionTrace (execLift frame op e) = BinaryInterpreterOperandExecute.transitionTrace (arithmeticStorage op) e := by
  change BinaryInterpreterOperandExecute.transitionTrace (arithmeticStorage op) (execView (execLift frame op e) op) = _
  rw [execView_lift]

theorem advance_execLift (frame : State) (op : RationalOp) (n : ℕ)
    (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) :
    advance n (execLift frame op e) = execLift frame op
      (BinaryInterpreterOperandExecute.advance (arithmeticStorage op) n e) := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
      simpa only [advance,step_execLift,BinaryInterpreterOperandExecute.advance] using
        (ih (BinaryInterpreterOperandExecute.step (arithmeticStorage op) e))

theorem bitSteps_execLift (frame : State) (op : RationalOp) (n : ℕ)
    (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) :
    bitSteps n (execLift frame op e) = BinaryInterpreterOperandExecute.bitSteps (arithmeticStorage op) n e := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih => simp only [bitSteps,trace_execLift,step_execLift,ih,BinaryInterpreterOperandExecute.bitSteps]

theorem execLift_self (s : State) (op : RationalOp) (hp : s.phase = .running) (hs : s.selected = op) :
    execLift s op (execView s op) = s := by
  simp only [execLift,setExec_view]
  cases s
  simp_all

theorem running_advance (s : State) (op : RationalOp) (hp : s.phase = .running) (hs : s.selected = op) (n : ℕ) :
    advance n s = execLift s op (BinaryInterpreterOperandExecute.advance (arithmeticStorage op) n (execView s op)) := by
  calc
    advance n s = advance n (execLift s op (execView s op)) := congrArg (advance n) (execLift_self s op hp hs).symm
    _ = _ := advance_execLift s op n (execView s op)

theorem running_bitSteps (s : State) (op : RationalOp) (hp : s.phase = .running) (hs : s.selected = op) (n : ℕ) :
    bitSteps n s = BinaryInterpreterOperandExecute.bitSteps (arithmeticStorage op) n (execView s op) := by
  calc
    bitSteps n s = bitSteps n (execLift s op (execView s op)) := congrArg (bitSteps n) (execLift_self s op hp hs).symm
    _ = _ := bitSteps_execLift s op n (execView s op)

theorem execLift_pool_clean (frame : State) (op : RationalOp)
    (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op))
    (hf : BinaryInterpreterPool.Clean frame.pool)
    (he : ∀ i, (arithmeticStorage op).tapes e.execution.core.core i = []) :
    BinaryInterpreterPool.Clean (execLift frame op e).pool := by
  intro other i
  by_cases h : other = op
  · subst other
    simpa only [execLift,setExec,BinaryInterpreterPool.get_set] using he i
  · simpa only [execLift,setExec,BinaryInterpreterPool.other_set _ op other _ h] using hf other i

theorem execLift_inactive (frame : State) (op other : RationalOp)
    (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) (h : other ≠ op) :
    (execLift frame op e).pool other = frame.pool other :=
  BinaryInterpreterPool.other_set frame.pool op other e.execution.core.core h

def CleanIO (io : IO) : Prop :=
  io.temp = [] ∧ io.leftAddress = [] ∧ io.rightAddress = [] ∧ io.destination = [] ∧
  io.saved = [] ∧ io.copyTemp = [] ∧ io.record = [] ∧ io.numWork = [] ∧ io.denWork = []

theorem cleanIO_ofExec {op : RationalOp} (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op))
    (ht : e.temp = []) (hi : BinaryInterpreterArithmetic.CleanIO e.execution.core) :
    CleanIO (IO.ofExec e) := ⟨ht,hi⟩

theorem initialIO_destination_view (op : RationalOp) (tape code history : List Symbol) (dst : List Bool) :
    ({initialIO tape code history with destination := dst} : IO).view op
      ((arithmeticLayout op).initial emptyWord emptyWord) ⟨(arithmeticStorage op).count,by omega⟩ =
      BinaryInterpreterOperandExecute.initial (arithmeticStorage op) tape dst code history := rfl

end IdentityTesting.BinaryInterpreterDispatch
