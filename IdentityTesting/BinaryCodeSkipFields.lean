import IdentityTesting.BinaryCodeSkipActive

namespace IdentityTesting.BinaryCodeSkip
open BinaryRegisterMachine RationalComputation

/-- A compositional execution statement over the fixed task alphabet. The
machine itself contains no AST or copy of this specification. -/
def Parses (todo : List Task) (segment : List Symbol) : Prop :=
  ∀ (tasks : List Task) (code history : List Symbol),
    ∃ n, n ≤ 2*segment.length ∧
      advance n (ready (todo++tasks) (segment++code) history) =
        ready tasks code (segment.reverse++history)

theorem Parses.append {as bs : List Task} {a b : List Symbol}
    (ha : Parses as a) (hb : Parses bs b) : Parses (as++bs) (a++b) := by
  intro tasks code history
  obtain ⟨na,hna,hea⟩ := ha (bs++tasks) (b++code) history
  obtain ⟨nb,hnb,heb⟩ := hb tasks code (a.reverse++history)
  refine ⟨na+nb,?_,?_⟩
  · simp only [List.length_append]
    omega
  · simp only [List.append_assoc] at hea ⊢
    rw [advance_add,hea,heb]
    simp only [List.reverse_append,List.append_assoc]

def wordState (tasks : List Task) (code history : List Symbol) : State :=
  {ready tasks code history with phase := .word}

theorem word_read (bits : List Bool) (tasks : List Task) (code history : List Symbol) :
    advance (bits.length+1) (wordState tasks (RationalProgramCode.word bits++code) history) =
      ready tasks code ((RationalProgramCode.word bits).reverse++history) := by
  induction bits generalizing history with
  | nil => rfl
  | cons b bits ih =>
    change advance (bits.length+1+1) _ = _
    rw [advance]
    simpa [wordState,step,RationalProgramCode.word,List.reverse_cons,List.append_assoc] using
      ih (.cell (.bit b)::history)

theorem word_task (bits : List Bool) (tasks : List Task) (code history : List Symbol) :
    advance (bits.length+2) (ready (.word::tasks) (RationalProgramCode.word bits++code) history) =
      ready tasks code ((RationalProgramCode.word bits).reverse++history) := by
  change advance ((bits.length+1)+1) _ = _
  rw [advance]
  exact word_read bits tasks code history

theorem word_parses (bits : List Bool) : Parses [.word] (RationalProgramCode.word bits) := by
  intro tasks code history
  refine ⟨bits.length+2,?_,word_task bits tasks code history⟩
  rw [RationalProgramCode.word_length]
  omega

theorem operand_prefix (literal : Bool) (tasks : List Task) (code history : List Symbol) :
    advance 3 (ready (.operand::tasks) (RationalProgramCode.word [literal]++code) history) =
      ready ((if literal then [.word,.word,.word] else [.word])++tasks) code
        ((RationalProgramCode.word [literal]).reverse++history) := by
  cases literal <;> rfl

theorem operand_payload_parses (literal : Bool) (data : List Symbol)
    (h : Parses (if literal then [.word,.word,.word] else [.word]) data) :
    Parses [.operand] (RationalProgramCode.word [literal]++data) := by
  intro tasks code history
  obtain ⟨n,hn,he⟩ := h tasks code ((RationalProgramCode.word [literal]).reverse++history)
  refine ⟨3+n,?_,?_⟩
  · simp only [List.length_append,RationalProgramCode.word_length,List.length_cons,List.length_nil]
    omega
  · simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [advance_add,operand_prefix,he]
    simp only [List.reverse_append,List.append_assoc]

theorem operand_parses (o : RationalOperand) : Parses [.operand] (RationalProgramCode.operand o) := by
  cases o with
  | reg i => exact operand_payload_parses false (RationalProgramCode.address i) (word_parses (List.replicate i false))
  | literal q =>
    have h := ((word_parses [decide (q.num < 0)]).append (word_parses q.num.natAbs.bits)).append (word_parses q.den.bits)
    simpa only [RationalProgramCode.operand,List.append_assoc] using operand_payload_parses true _ h

theorem node_prefix (a b c : Bool) (todo tasks : List Task) (code history : List Symbol)
    (h : schedule a b c = some todo) :
    advance 6 (ready (.node::tasks) (RationalProgramCode.tag a b c++code) history) =
      ready (todo++tasks) code ((RationalProgramCode.tag a b c).reverse++history) := by
  cases a <;> cases b <;> cases c <;>
    simp_all [advance,step,ready,tagView,setTag,schedule,RationalProgramCode.tag,RationalProgramCode.word,
      BinaryCodeTagDecoder.step]

theorem node_payload_parses (a b c : Bool) (todo : List Task) (data : List Symbol)
    (hs : schedule a b c = some todo) (h : Parses todo data) :
    Parses [.node] (RationalProgramCode.tag a b c++data) := by
  intro tasks code history
  obtain ⟨n,hn,he⟩ := h tasks code ((RationalProgramCode.tag a b c).reverse++history)
  refine ⟨6+n,?_,?_⟩
  · simp only [List.length_append,RationalProgramCode.tag_length]
    omega
  · simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [advance_add,node_prefix a b c todo tasks (data++code) history hs,he]
    simp only [List.reverse_append,List.append_assoc]

theorem empty_parses : Parses [] [] := by
  intro tasks code history
  exact ⟨0,by simp,rfl⟩

theorem end_tag_run (tasks : List Task) (code history : List Symbol) :
    advance 6 (ready (.endTag::tasks) (RationalProgramCode.endTag++code) history) =
      ready tasks code (RationalProgramCode.endTag.reverse++history) := by
  simp [advance,step,ready,tagView,setTag,RationalProgramCode.endTag,RationalProgramCode.tag,
    RationalProgramCode.word,BinaryCodeTagDecoder.step]

theorem end_parses : Parses [.endTag] RationalProgramCode.endTag := by
  intro tasks code history
  exact ⟨6,by decide,end_tag_run tasks code history⟩

end IdentityTesting.BinaryCodeSkip
