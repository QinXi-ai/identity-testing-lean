import IdentityTesting.BinaryWordNormalization

/-! A finite-control binary counter. Each input cell triggers a ripple-carry
increment; carried low bits are explicitly restored from a temporary stack.
No list length is evaluated by an executed instruction. -/
namespace IdentityTesting.BinaryRationalArithmeticBitCounter
open BinaryArithmetic

def increment : List Bool → List Bool
  | [] => [true]
  | false::xs => true::xs
  | true::xs => false::increment xs

theorem increment_value (xs : List Bool) : value (increment xs) = value xs+1 := by
  induction xs with
  | nil => simp [increment,value]
  | cons b xs ih => cases b <;> simp [increment,value,ih] <;> omega

theorem increment_length (xs : List Bool) : (increment xs).length ≤ xs.length+1 := by
  induction xs with
  | nil => simp [increment]
  | cons b xs ih => cases b <;> simp [increment] <;> omega

inductive Phase where
  | readInput | increment | restore | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  source : List Bool
  counter : List Bool
  temp : List Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .readInput => match s.source with
      | [] => {s with phase := .halt}
      | _::bs => {s with phase := .increment,source := bs}
  | .increment => match s.counter with
      | [] => {s with phase := .restore,counter := [true]}
      | false::bs => {s with phase := .restore,counter := true::bs}
      | true::bs => {s with counter := bs,temp := false::s.temp}
  | .restore => match s.temp with
      | [] => {s with phase := .readInput}
      | b::bs => {s with counter := b::s.counter,temp := bs}
  | .halt => s

def initial (xs : List Bool) : State := ⟨.readInput,xs,[],[]⟩

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)

def Runs (s : State) (n : ℕ) (t : State) : Prop := advance n s=t

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s=advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)

theorem Runs.trans {s t u : State} {m n : ℕ} (h : Runs s m t) (j : Runs t n u) :
    Runs s (m+n) u := by
  dsimp [Runs] at *
  rw [advance_add,h,j]

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .readInput => if s.source = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead]
  | .increment => if s.counter = [] then [.readCell,.branch,.writeCell,.moveHead]
      else [.readCell,.branch,.writeCell,.moveHead,.writeCell,.moveHead]
  | .restore => if s.temp = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 6 := by
  cases h:s.phase <;> simp only [transitionTrace,h]
  all_goals first | (split <;> simp) | simp

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 6*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

theorem restore_run (src cs tmp : List Bool) :
    Runs ⟨.restore,src,cs,tmp⟩ (tmp.length+1) ⟨.readInput,src,tmp.reverse++cs,[]⟩ := by
  induction tmp generalizing cs with
  | nil => rfl
  | cons b bs ih =>
      change advance (bs.length+1+1) _=_
      rw [advance]
      simpa [step,List.reverse_cons,List.append_assoc] using ih (b::cs)

theorem increment_run (src cs tmp : List Bool) :
    ∃ steps, steps ≤ 2*cs.length+tmp.length+2 ∧
      Runs ⟨.increment,src,cs,tmp⟩ steps ⟨.readInput,src,tmp.reverse++increment cs,[]⟩ := by
  induction cs generalizing tmp with
  | nil =>
      refine ⟨tmp.length+2,by omega,?_⟩
      change advance (tmp.length+1+1) _=_
      rw [advance]
      exact restore_run src [true] tmp
  | cons b bs ih =>
      cases b with
      | false =>
          refine ⟨tmp.length+2,by simp,?_⟩
          change advance (tmp.length+1+1) _=_
          rw [advance]
          exact restore_run src (true::bs) tmp
      | true =>
          obtain ⟨k,hk,hr⟩ := ih (false::tmp)
          refine ⟨k+1,by simp_all;omega,?_⟩
          change advance (k+1) _=_
          rw [advance]
          simpa [step,increment,List.reverse_cons,List.append_assoc] using hr

theorem count_run (src cs : List Bool) :
    ∃ steps out, steps ≤ 3*src.length*(cs.length+src.length+1)+1 ∧
      value out = value cs+src.length ∧ out.length ≤ cs.length+src.length ∧
      Runs ⟨.readInput,src,cs,[]⟩ steps ⟨.halt,[],out,[]⟩ := by
  induction src generalizing cs with
  | nil =>
      refine ⟨1,cs,by simp,by simp,by simp,?_⟩
      rfl
  | cons b bs ih =>
      obtain ⟨ki,hki,hkir⟩ := increment_run bs cs []
      simp only [List.length_nil,List.reverse_nil,List.nil_append,Nat.add_zero] at hki hkir
      obtain ⟨kr,out,hkr,hv,hl,hrr⟩ := ih (increment cs)
      have hc := increment_length cs
      have hfirst : Runs ⟨.readInput,b::bs,cs,[]⟩ 1 ⟨.increment,bs,cs,[]⟩ := rfl
      refine ⟨1+ki+kr,out,?_,?_,?_,(hfirst.trans hkir).trans hrr⟩
      · simp only [List.length_cons]
        have hp := Nat.mul_le_mul_left (3*bs.length) hc
        nlinarith only [hki,hkr,hp]
      · simp only [increment_value] at hv
        simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        omega

theorem binary_bit_count_machine (xs : List Bool) :
    ∃ steps out, (advance steps (initial xs)) = ⟨.halt,[],out,[]⟩ ∧
      value out=xs.length ∧ out.length≤xs.length ∧
      bitSteps steps (initial xs)≤18*xs.length*(xs.length+1)+6 := by
  obtain ⟨k,out,hk,hv,hl,hr⟩ := count_run xs []
  refine ⟨k,out,hr,?_,?_,?_⟩
  · simpa [value] using hv
  · simpa using hl
  · have hb := bitSteps_le k (initial xs)
    simp only [List.length_nil,Nat.zero_add] at hk
    nlinarith only [hb,hk]

end IdentityTesting.BinaryRationalArithmeticBitCounter
