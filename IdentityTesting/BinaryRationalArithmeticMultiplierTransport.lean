import IdentityTesting.BinaryRationalArithmeticMultiplierRuns

namespace IdentityTesting.BinaryRationalArithmeticMultiplier
open BinaryArithmetic

theorem transport (n d : BinarySignedMultiplier.State) (sg : Bool) :
    Runs ⟨.numCollect,n,d,BinaryRationalNormalizationMachine.initial sg [] [],[]⟩
      (2*n.norm.out.length+2*d.norm.out.length+4)
      ⟨.normalize,{n with norm := {n.norm with out := []}},
        {d with norm := {d.norm with out := []}},
        BinaryRationalNormalizationMachine.initial sg n.norm.out d.norm.out,[]⟩ := by
  let r0 := BinaryRationalNormalizationMachine.initial sg [] []
  let n0 := {n with norm := {n.norm with out := []}}
  let d0 := {d with norm := {d.norm with out := []}}
  let s : State := ⟨.numCollect,n,d,r0,[]⟩
  have h1 : Runs s (n.norm.out.length+1) ⟨.numEmit,n0,d,r0,n.norm.out.reverse⟩ := by
    simpa [s,n0] using numCollect_run s n.norm.out
  have h2 : Runs ⟨.numEmit,n0,d,r0,n.norm.out.reverse⟩ (n.norm.out.length+1)
      ⟨.denCollect,n0,d,BinaryRationalNormalizationMachine.initial sg n.norm.out [],[]⟩ := by
    simpa [r0,BinaryRationalNormalizationMachine.initial,BinaryDivisionMachine.initial] using
      numEmit_run ⟨.numEmit,n0,d,r0,[]⟩ n.norm.out.reverse
  let r1 := BinaryRationalNormalizationMachine.initial sg n.norm.out []
  have h3 : Runs ⟨.denCollect,n0,d,r1,[]⟩ (d.norm.out.length+1)
      ⟨.denEmit,n0,d0,r1,d.norm.out.reverse⟩ := by
    simpa [d0] using denCollect_run ⟨.denCollect,n0,d,r1,[]⟩ d.norm.out
  have h4 : Runs ⟨.denEmit,n0,d0,r1,d.norm.out.reverse⟩ (d.norm.out.length+1)
      ⟨.normalize,n0,d0,BinaryRationalNormalizationMachine.initial sg n.norm.out d.norm.out,[]⟩ := by
    simpa [r1,BinaryRationalNormalizationMachine.initial,BinaryDivisionMachine.initial] using
      denEmit_run ⟨.denEmit,n0,d0,r1,[]⟩ d.norm.out.reverse
  convert ((h1.trans h2).trans h3).trans h4 using 1 <;> omega

theorem normalize_outputs (n d : BinarySignedMultiplier.State) (m v : ℕ)
    (hn : n.norm.out = m.bits) (hd : d.norm.out = v.bits) (hv : 0 < v) :
    ∃ steps rn rd, steps ≤ 2*m.size+2*v.size+1000*(m.size+v.size+1)^3+5 ∧
      Runs ⟨.numCollect,n,d,BinaryRationalNormalizationMachine.initial n.negative [] [],[]⟩ steps
        ⟨.halt,{n with norm := {n.norm with out := []}},
          {d with norm := {d.norm with out := []}},
          BinaryRationalNormalizationMachine.terminal n.negative (Nat.gcd m v).bits
            (m / Nat.gcd m v).bits (v / Nat.gcd m v).bits rn rd,[]⟩ := by
  obtain ⟨k,rn,rd,hk,hr⟩ := BinaryRationalNormalizationMachine.normalization_run n.negative m v hv
  let ni := BinaryRationalNormalizationMachine.initial n.negative m.bits v.bits
  let n0 := {n with norm := {n.norm with out := []}}
  let d0 := {d with norm := {d.norm with out := []}}
  have hh : (BinaryRationalNormalizationMachine.advance k ni).phase = .halt := by
    rw [show BinaryRationalNormalizationMachine.advance k ni = _ from hr]
    rfl
  obtain ⟨j,hj,hjr⟩ := forward_normalization ⟨.normalize,n0,d0,ni,[]⟩ ni k hh
  rw [show BinaryRationalNormalizationMachine.advance k ni = _ from hr] at hjr
  have ht := transport n d n.negative
  rw [hn,hd] at ht
  refine ⟨_,rn,rd,?_,ht.trans hjr⟩
  simp only [Nat.size_eq_bits_len]
  omega

end IdentityTesting.BinaryRationalArithmeticMultiplier
