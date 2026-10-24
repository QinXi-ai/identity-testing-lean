import IdentityTesting.BinaryInterpreterDispatch

namespace IdentityTesting.BinaryInterpreterDispatch
open BinaryRegisterMachine RationalComputation BinaryInterpreterArithmetic

def opFirst : RationalOp → Bool
  | .copy | .sub | .div => false
  | .add | .mul | .le => true
def opSecond : RationalOp → Bool
  | .sub | .mul => true
  | _ => false
def opThird : RationalOp → Bool
  | .div | .le => true
  | _ => false

theorem decode_op (op : RationalOp) : decodeOp (opFirst op) (opSecond op) (opThird op) = some op := by
  cases op <;> rfl

def addressStart (pool : BinaryInterpreterPool.Pool) (tape : List Symbol)
    (op : RationalOp) (code history : List Symbol) : State :=
  select (setTag (initial pool tape code history)
    ⟨.halt,code,(RationalProgramCode.word (RationalProgramCode.opBits op)).reverse ++ history,
      opFirst op,opSecond op,opThird op⟩) op

theorem opcode_run (pool : BinaryInterpreterPool.Pool) (tape : List Symbol)
    (op : RationalOp) (code history : List Symbol) :
    advance 5 (initial pool tape (RationalProgramCode.word (RationalProgramCode.opBits op) ++ code) history) =
      addressStart pool tape op code history := by
  cases op <;>
    simp [advance,step,initial,initialIO,IO.ofExec,BinaryInterpreterOperandExecute.initial,
      BinaryInterpreterArithmeticClean.runningState,BinaryInterpreterArithmetic.operatingState,
      tagView,setTag,select,addressStart,RationalProgramCode.opBits,RationalProgramCode.word,
      BinaryCodeTagDecoder.step,decodeOp,opFirst,opSecond,opThird]

theorem opcode_cost (pool : BinaryInterpreterPool.Pool) (tape : List Symbol)
    (op : RationalOp) (code history : List Symbol) :
    bitSteps 5 (initial pool tape (RationalProgramCode.word (RationalProgramCode.opBits op) ++ code) history) = 33 := by
  cases op <;>
    simp [bitSteps,transitionTrace,step,initial,initialIO,IO.ofExec,BinaryInterpreterOperandExecute.initial,
      BinaryInterpreterArithmeticClean.runningState,BinaryInterpreterArithmetic.operatingState,
      tagView,setTag,select,RationalProgramCode.opBits,RationalProgramCode.word,
      BinaryCodeTagDecoder.step,BinaryCodeTagDecoder.transitionTrace,decodeOp]

def addressLift (frame : State) (a : BinaryCodeWordLoader.State) : State :=
  {setAddress frame a with phase := .address}

theorem address_lift_step (frame : State) (a : BinaryCodeWordLoader.State) (h : a.phase ≠ .halt) :
    step (addressLift frame a) = addressLift frame (BinaryCodeWordLoader.step a) := by
  simp only [step,addressLift,setAddress,h,if_false]
  rfl

theorem address_halt (n : ℕ) (a : BinaryCodeWordLoader.State) (h : a.phase = .halt) :
    BinaryCodeWordLoader.advance n a = a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryCodeWordLoader.advance,BinaryCodeWordLoader.step,h] using ih

theorem forward_address (frame : State) (a : BinaryCodeWordLoader.State) (n : ℕ)
    (h : (BinaryCodeWordLoader.advance n a).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance k (addressLift frame a) =
      enterExecution (addressLift frame (BinaryCodeWordLoader.advance n a)) ∧
      bitSteps k (addressLift frame a) ≤ 10*n+1 := by
  induction n generalizing a with
  | zero =>
    change a.phase = .halt at h
    refine ⟨1,by omega,?_,?_⟩
    · simp [advance,step,addressLift,setAddress,h,BinaryCodeWordLoader.advance]
    · simp [bitSteps,transitionTrace,addressLift,setAddress,h]
  | succ n ih =>
    by_cases hh : a.phase = .halt
    · rw [address_halt (n+1) a hh]
      refine ⟨1,by omega,?_,?_⟩
      · simp [advance,step,addressLift,setAddress,hh]
      · simp [bitSteps,transitionTrace,addressLift,setAddress,hh]
    · obtain ⟨k,hk,he,hc⟩ := ih (BinaryCodeWordLoader.step a) h
      refine ⟨k+1,by omega,?_,?_⟩
      · rw [advance,address_lift_step frame a hh]
        exact he
      · have ht := BinaryCodeWordLoader.transition_length a
        rw [bitSteps,address_lift_step frame a hh]
        have hv : addressView (addressLift frame a) = a := rfl
        simp only [transitionTrace,addressLift,setAddress,hh,if_false]
        change (BinaryCodeWordLoader.transitionTrace (addressView (addressLift frame a))).length + 1 +
          bitSteps k (addressLift frame (BinaryCodeWordLoader.step a)) ≤ _
        rw [hv]
        omega

/-- Read the actual operation tag and unary destination from the code tape.
No operation or destination is supplied to the machine's initial state. -/
theorem header_run (pool : BinaryInterpreterPool.Pool) (tape : List Symbol)
    (op : RationalOp) (dst : ℕ) (code history : List Symbol) :
    ∃ n, n ≤ 2*dst+12 ∧
      let start := initial pool tape
        ((RationalProgramCode.word (RationalProgramCode.opBits op) ++ RationalProgramCode.address dst) ++ code) history
      bitSteps n start ≤ 20*dst+100 ∧
      let f := advance n start
      f.phase = .running ∧ f.selected = op ∧ f.pool = BinaryInterpreterPool.rearm pool op ∧
      f.cursor op = ⟨(arithmeticStorage op).count,by omega⟩ ∧
      f.io = {initialIO tape code
        ((RationalProgramCode.word (RationalProgramCode.opBits op) ++ RationalProgramCode.address dst).reverse ++ history)
        with destination := List.replicate dst false} := by
  let hist := (RationalProgramCode.word (RationalProgramCode.opBits op)).reverse ++ history
  let frame := addressStart pool tape op code history
  let a : BinaryCodeWordLoader.State := ⟨.reading,RationalProgramCode.address dst ++ code,hist,[],[]⟩
  let af : BinaryCodeWordLoader.State :=
    ⟨.halt,code,(RationalProgramCode.address dst).reverse ++ hist,[],List.replicate dst false⟩
  have ha : BinaryCodeWordLoader.advance (2*dst+2) a = af :=
    (BinaryCodeMaterialization.materialize_address dst code hist).1
  have hah : (BinaryCodeWordLoader.advance (2*dst+2) a).phase = .halt := by rw [ha]
  obtain ⟨k,hk,he,hc⟩ := forward_address frame a (2*dst+2) hah
  rw [ha] at he
  have hstart : addressStart pool tape op (RationalProgramCode.address dst ++ code) history = addressLift frame a := rfl
  let start := initial pool tape
    ((RationalProgramCode.word (RationalProgramCode.opBits op) ++ RationalProgramCode.address dst) ++ code) history
  have htag : advance 5 start = addressLift frame a := by
    dsimp only [start]
    rw [List.append_assoc,opcode_run,hstart]
  have htotal : advance (5+k) start = enterExecution (addressLift frame af) := by
    rw [advance_add,htag,he]
  refine ⟨5+k,by omega,?_,?_,?_,?_,?_,?_⟩
  · change bitSteps (5+k) start ≤ _
    rw [bitSteps_add,htag]
    have ht : bitSteps 5 start = 33 := by
      dsimp only [start]
      rw [List.append_assoc,opcode_cost]
    rw [ht]
    omega
  · change (advance (5+k) start).phase = _
    rw [htotal]
    rfl
  · change (advance (5+k) start).selected = _
    rw [htotal]
    rfl
  · change (advance (5+k) start).pool = _
    rw [htotal]
    rfl
  · change (advance (5+k) start).cursor op = _
    rw [htotal]
    rfl
  · change (advance (5+k) start).io = _
    rw [htotal]
    simp [enterExecution,addressLift,setAddress,frame,addressStart,select,setTag,
      initial,initialIO,IO.ofExec,BinaryInterpreterOperandExecute.initial,
      BinaryInterpreterArithmeticClean.runningState,BinaryInterpreterArithmetic.operatingState,
      af,hist,List.reverse_append,List.append_assoc]

end IdentityTesting.BinaryInterpreterDispatch
