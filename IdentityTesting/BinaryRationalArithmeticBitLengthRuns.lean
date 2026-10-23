import IdentityTesting.BinaryRationalArithmeticBitLength

namespace IdentityTesting.BinaryRationalArithmeticBitLength
open BinaryArithmetic

private theorem counter_halt (k : ℕ) (s : BinaryRationalArithmeticBitCounter.State) (h : s.phase = .halt) :
    BinaryRationalArithmeticBitCounter.advance k s=s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryRationalArithmeticBitCounter.advance,BinaryRationalArithmeticBitCounter.step,h] using ih

theorem forward_counter (s : State) (m : BinaryRationalArithmeticBitCounter.State) (k : ℕ)
    (h : (BinaryRationalArithmeticBitCounter.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs {s with phase := .counting,core := m} j
      {s with phase := .collect,core := BinaryRationalArithmeticBitCounter.advance k m} := by
  induction k generalizing m with
  | zero =>
      simp only [BinaryRationalArithmeticBitCounter.advance] at h
      refine ⟨1,by omega,?_⟩
      simp [Runs,advance,step,h,BinaryRationalArithmeticBitCounter.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [counter_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinaryRationalArithmeticBitCounter.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinaryRationalArithmeticBitCounter.advance] using he

private theorem normalizer_halt (k : ℕ) (s : BinaryWordNormalization.State) (h : s.phase = .halt) :
    BinaryWordNormalization.advance k s=s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryWordNormalization.advance,BinaryWordNormalization.step,h] using ih

theorem forward_normalizer (s : State) (m : BinaryWordNormalization.State) (k : ℕ)
    (h : (BinaryWordNormalization.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs {s with phase := .normalize,norm := m} j
      {s with phase := .halt,norm := BinaryWordNormalization.advance k m} := by
  induction k generalizing m with
  | zero =>
      simp only [BinaryWordNormalization.advance] at h
      refine ⟨1,by omega,?_⟩
      simp [Runs,advance,step,h,BinaryWordNormalization.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [normalizer_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinaryWordNormalization.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinaryWordNormalization.advance] using he

theorem collect_run (s : State) (xs : List Bool) :
    Runs {s with phase := .collect,core := {s.core with counter := xs}} (xs.length+1)
      {s with phase := .emit,core := {s.core with counter := []},temp := xs.reverse++s.temp} := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b bs ih =>
      change advance (bs.length+1+1) _=_
      rw [advance]
      change advance (bs.length+1)
        {s with phase := .collect,core := {s.core with counter := bs},temp := b::s.temp} = _
      rw [show advance _ _ = _ from ih {s with temp := b::s.temp}]
      simp [List.reverse_cons,List.append_assoc]

theorem emit_run (s : State) (xs : List Bool) :
    Runs {s with phase := .emit,temp := xs} (xs.length+1)
      {s with phase := .normalize,temp := [],norm := {s.norm with source := xs.reverse++s.norm.source}} := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b bs ih =>
      change advance (bs.length+1+1) _=_
      rw [advance]
      change advance (bs.length+1)
        {s with phase := .emit,temp := bs,norm := {s.norm with source := b::s.norm.source}} = _
      rw [show advance _ _ = _ from ih {s with norm := {s.norm with source := b::s.norm.source}}]
      simp [List.reverse_cons,List.append_assoc]

theorem transport (xs : List Bool) :
    Runs ⟨.collect,⟨.halt,[],xs,[]⟩,⟨.collect,[],[],[]⟩,[]⟩ (2*xs.length+2)
      ⟨.normalize,⟨.halt,[],[],[]⟩,⟨.collect,xs,[],[]⟩,[]⟩ := by
  have h1 := collect_run ⟨.collect,⟨.halt,[],[],[]⟩,⟨.collect,[],[],[]⟩,[]⟩ xs
  have h2 := emit_run ⟨.emit,⟨.halt,[],[],[]⟩,⟨.collect,[],[],[]⟩,[]⟩ xs.reverse
  simp only [List.append_nil,List.length_reverse,List.reverse_reverse] at h1 h2
  convert h1.trans h2 using 1 <;> omega

theorem bit_length_run (xs : List Bool) :
    ∃ steps, (advance steps (initial xs)).phase = .halt ∧
      output (advance steps (initial xs)) = xs.length.bits ∧
      steps ≤ 14*(xs.length+1)^2 := by
  obtain ⟨k,out,hk,hv,hl,hr⟩ := BinaryRationalArithmeticBitCounter.count_run xs []
  simp only [List.length_nil,Nat.zero_add,value] at hk hv hl
  let c := BinaryRationalArithmeticBitCounter.initial xs
  have hcore : BinaryRationalArithmeticBitCounter.advance k c = ⟨.halt,[],out,[]⟩ := hr
  have hhalt : (BinaryRationalArithmeticBitCounter.advance k c).phase = .halt := by rw [hcore]
  obtain ⟨j,hj,hjr⟩ := forward_counter (initial xs) c k hhalt
  rw [hcore] at hjr
  have h1 : Runs (initial xs) j ⟨.collect,⟨.halt,[],out,[]⟩,⟨.collect,[],[],[]⟩,[]⟩ := hjr
  have h2 := transport out
  let ni : BinaryWordNormalization.State := ⟨.collect,out,[],[]⟩
  let nf := BinaryWordNormalization.advance (2*out.length+2) ni
  obtain ⟨hnh,hno,hnv,hnl,hncost⟩ := BinaryWordNormalization.binary_normalization_machine out
  obtain ⟨jn,hjn,hjnr⟩ := forward_normalizer ⟨.normalize,⟨.halt,[],[],[]⟩,ni,[]⟩ ni (2*out.length+2) hnh
  have hall := (h1.trans h2).trans hjnr
  refine ⟨j+(2*out.length+2)+jn,?_,?_,?_⟩
  · rw [hall]
  · change (advance _ _).norm.out = _
    rw [hall]
    change nf.out=_
    rw [show nf.out=(value out).bits from hno,hv]
  · nlinarith only [hk,hl,hj,hjn]

theorem binary_bit_length_machine (xs : List Bool) :
    ∃ steps, (advance steps (initial xs)).phase = .halt ∧
      output (advance steps (initial xs)) = xs.length.bits ∧
      bitSteps steps (initial xs) ≤ 100*(xs.length+1)^2 := by
  obtain ⟨k,hh,ho,hk⟩ := bit_length_run xs
  refine ⟨k,hh,ho,?_⟩
  have hb := bitSteps_le k (initial xs)
  omega

end IdentityTesting.BinaryRationalArithmeticBitLength
