import IdentityTesting.BinaryRationalArithmeticBitCounter

/-! A reusable two-stack natural counter. Zero testing reads only the end
marker. Predecessor uses ripple borrow and explicit restoration. The highest
one is removed when it is the last cell, so outputs remain canonical without
a whole-word normalization or a host-language natural-number operation. -/
namespace IdentityTesting.BinaryRationalArithmeticNatCounter
open BinaryArithmetic

def predecessor : List Bool → List Bool
  | [] => []
  | false::bs => true::predecessor bs
  | true::bs => if bs=[] then [] else false::bs

theorem predecessor_bits (n : ℕ) : predecessor n.bits=(n-1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [predecessor]
  | bit b n h ih =>
      rw [Nat.bits_append_bit n b h]
      cases b with
      | false =>
          have hn : n≠0 := by intro hn; have hf := h hn; cases hf
          simp only [predecessor,ih]
          have he : Nat.bit false n-1=2*(n-1)+1 := by simp [Nat.bit_val]; omega
          rw [he,Nat.bit1_bits]
      | true =>
          by_cases hn : n=0
          · subst n; simp [predecessor,Nat.bit_val]
          · have hb : n.bits≠[] := by
              intro hb
              have hv := congrArg value hb
              simp only [value_bits,value] at hv
              exact hn hv
            simp only [predecessor,if_neg hb]
            have he : Nat.bit true n-1=2*n := by simp [Nat.bit_val]
            rw [he,Nat.bit0_bits n hn]

inductive Phase where
  | check | pred | restore | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  counter : List Bool
  temp : List Bool
  zero : Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .check => {s with phase := .halt,zero := match s.counter with | [] => true | _::_ => false}
  | .pred => match s.counter with
      | [] => {s with phase := .restore}
      | false::bs => {s with counter := bs,temp := true::s.temp}
      | true::bs => {s with phase := .restore,counter := if bs=[] then [] else false::bs}
  | .restore => match s.temp with
      | [] => {s with phase := .halt}
      | b::bs => {s with counter := b::s.counter,temp := bs}
  | .halt => s

def initialPred (xs : List Bool) : State := ⟨.pred,xs,[],false⟩
def initialTest (xs : List Bool) : State := ⟨.check,xs,[],false⟩

def advance : ℕ → State → State
  | 0,s => s
  | k+1,s => advance k (step s)

def Runs (s : State) (n : ℕ) (t : State) : Prop := advance n s=t

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s=advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)

theorem Runs.trans {s t u : State} {m n : ℕ} (h : Runs s m t) (j : Runs t n u) : Runs s (m+n) u := by
  dsimp [Runs] at *
  rw [advance_add,h,j]

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .check => [.readCell,.branch]
  | .pred => match s.counter with
      | [] => [.readCell,.branch]
      | false::_ => [.readCell,.branch,.moveHead,.writeCell,.moveHead]
      | true::_ => [.readCell,.moveHead,.readCell,.branch,.writeCell,.moveHead]
  | .restore => if s.temp=[] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | k+1,s => (transitionTrace s).length+bitSteps k (step s)

theorem transition_length (s : State) : (transitionTrace s).length≤6 := by
  cases hp:s.phase <;> simp only [transitionTrace,hp]
  all_goals (repeat' first | split | simp_all)

theorem step_halt (s : State) (h : s.phase=.halt) : step s=s := by simp [step,h]

theorem transition_positive (s : State) (h : s.phase≠.halt) : 1≤(transitionTrace s).length := by
  cases hp:s.phase <;> simp only [transitionTrace,hp]
  all_goals (repeat' first | split | simp_all)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s≤6*n := by
  induction n generalizing s with
  | zero => simp [bitSteps]
  | succ n ih =>
      have hi := ih (step s)
      have ht := transition_length s
      simp only [bitSteps]
      omega

theorem restore_run (xs tmp : List Bool) (z : Bool) :
    Runs ⟨.restore,xs,tmp,z⟩ (tmp.length+1) ⟨.halt,tmp.reverse++xs,[],z⟩ := by
  induction tmp generalizing xs with
  | nil => rfl
  | cons b bs ih =>
      change advance (bs.length+1+1) _=_
      rw [advance]
      simpa [step,List.reverse_cons,List.append_assoc] using ih (b::xs)

theorem predecessor_run (xs tmp : List Bool) (z : Bool) :
    ∃ steps, steps≤2*xs.length+tmp.length+2 ∧
      Runs ⟨.pred,xs,tmp,z⟩ steps ⟨.halt,tmp.reverse++predecessor xs,[],z⟩ := by
  induction xs generalizing tmp with
  | nil =>
      refine ⟨tmp.length+2,by omega,?_⟩
      change advance (tmp.length+1+1) _=_
      rw [advance]
      exact restore_run [] tmp z
  | cons b bs ih =>
      cases b with
      | false =>
          obtain ⟨k,hk,hr⟩ := ih (true::tmp)
          refine ⟨k+1,by simp_all;omega,?_⟩
          change advance (k+1) _=_
          rw [advance]
          simpa [step,predecessor,List.reverse_cons,List.append_assoc] using hr
      | true =>
          refine ⟨tmp.length+2,by simp,?_⟩
          change advance (tmp.length+1+1) _=_
          rw [advance]
          exact restore_run (if bs=[] then [] else false::bs) tmp z

theorem binary_nat_counter_predecessor (n : ℕ) :
    ∃ steps, advance steps (initialPred n.bits)=⟨.halt,(n-1).bits,[],false⟩ ∧
      steps≤2*n.size+2 ∧ bitSteps steps (initialPred n.bits)≤12*(n.size+1) := by
  obtain ⟨k,hk,hr⟩ := predecessor_run n.bits [] false
  simp only [List.length_nil,List.reverse_nil,List.nil_append,Nat.add_zero,Nat.size_eq_bits_len,
    predecessor_bits] at hk hr
  refine ⟨k,hr,hk,?_⟩
  have hb := bitSteps_le k (initialPred n.bits)
  omega

theorem binary_nat_counter_test (n : ℕ) :
    advance 1 (initialTest n.bits)=⟨.halt,n.bits,[],decide (n=0)⟩ ∧
      bitSteps 1 (initialTest n.bits)=2 := by
  by_cases hn:n=0
  · simp [hn,initialTest,advance,step,bitSteps,transitionTrace]
  · have hb : n.bits≠[] := by
      intro hb
      have hv := congrArg value hb
      simp only [value_bits,value] at hv
      exact hn hv
    cases he:n.bits with
    | nil => exact (hb he).elim
    | cons b bs => simp [initialTest,advance,step,bitSteps,transitionTrace,he,hn]

end IdentityTesting.BinaryRationalArithmeticNatCounter
