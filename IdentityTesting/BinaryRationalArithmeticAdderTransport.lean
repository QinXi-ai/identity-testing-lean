import IdentityTesting.BinaryRationalArithmeticAdderPreparation

namespace IdentityTesting.BinaryRationalArithmeticAdder
open BinaryArithmetic

def emptied (n : BinarySignedMultiplier.State) : BinarySignedMultiplier.State :=
  { n with norm := { n.norm with out := [] } }

def sumReady (n r : BinarySignedMultiplier.State) : BinarySignedAdder.State :=
  BinarySignedAdder.initial ⟨n.negative,n.norm.out⟩ ⟨r.negative,r.norm.out⟩

theorem load_products (n d r : BinarySignedMultiplier.State) :
    Runs ⟨.leftCollect,
      ⟨.numCollect,n,d,BinaryRationalNormalizationMachine.initial false [] [],[]⟩,r,
      BinarySignedAdder.initial ⟨n.negative,[]⟩ ⟨r.negative,[]⟩,[]⟩
      (2*n.norm.out.length+2*r.norm.out.length+4)
      ⟨.add,
        ⟨.numCollect,emptied n,d,BinaryRationalNormalizationMachine.initial false [] [],[]⟩,
        emptied r,sumReady n r,[]⟩ := by
  let b : BinaryRationalArithmeticMultiplier.State :=
    ⟨.numCollect,n,d,BinaryRationalNormalizationMachine.initial false [] [],[]⟩
  let b0 : BinaryRationalArithmeticMultiplier.State :=
    ⟨.numCollect,emptied n,d,BinaryRationalNormalizationMachine.initial false [] [],[]⟩
  let a := BinarySignedAdder.initial ⟨n.negative,[]⟩ ⟨r.negative,[]⟩
  let a1 := BinarySignedAdder.initial ⟨n.negative,n.norm.out⟩ ⟨r.negative,[]⟩
  have h1 : Runs ⟨.leftCollect,b,r,a,[]⟩ (n.norm.out.length+1)
      ⟨.leftEmit,b0,r,a,n.norm.out.reverse⟩ := by
    simpa [b,b0,emptied] using leftCollect_run ⟨.leftCollect,b,r,a,[]⟩ n.norm.out
  have h2 : Runs ⟨.leftEmit,b0,r,a,n.norm.out.reverse⟩ (n.norm.out.length+1)
      ⟨.rightCollect,b0,r,a1,[]⟩ := by
    simpa [a,a1,BinarySignedAdder.initial] using leftEmit_run ⟨.leftEmit,b0,r,a,[]⟩ n.norm.out.reverse
  have h3 : Runs ⟨.rightCollect,b0,r,a1,[]⟩ (r.norm.out.length+1)
      ⟨.rightEmit,b0,emptied r,a1,r.norm.out.reverse⟩ := by
    simpa [emptied] using rightCollect_run ⟨.rightCollect,b0,r,a1,[]⟩ r.norm.out
  have h4 : Runs ⟨.rightEmit,b0,emptied r,a1,r.norm.out.reverse⟩ (r.norm.out.length+1)
      ⟨.add,b0,emptied r,sumReady n r,[]⟩ := by
    simpa [a1,sumReady,BinarySignedAdder.initial] using rightEmit_run ⟨.rightEmit,b0,emptied r,a1,[]⟩ r.norm.out.reverse
  convert ((h1.trans h2).trans h3).trans h4 using 1 <;> omega

def summed (n : BinarySignedMultiplier.State) (a : BinarySignedAdder.State) : BinarySignedMultiplier.State :=
  { n with negative := a.negative, norm := { n.norm with out := a.norm.out } }

theorem transport_sum (n d r : BinarySignedMultiplier.State) (a : BinarySignedAdder.State) :
    Runs ⟨.sumCollect,
      ⟨.numCollect,emptied n,d,BinaryRationalNormalizationMachine.initial false [] [],[]⟩,r,a,[]⟩
      (2*a.norm.out.length+2)
      ⟨.normalize,
        ⟨.numCollect,summed n a,d,BinaryRationalNormalizationMachine.initial a.negative [] [],[]⟩,
        r,{ a with norm := { a.norm with out := [] } },[]⟩ := by
  let b : BinaryRationalArithmeticMultiplier.State :=
    ⟨.numCollect,emptied n,d,BinaryRationalNormalizationMachine.initial false [] [],[]⟩
  let a0 := { a with norm := { a.norm with out := [] } }
  have h1 : Runs ⟨.sumCollect,b,r,a,[]⟩ (a.norm.out.length+1)
      ⟨.sumEmit,b,r,a0,a.norm.out.reverse⟩ := by
    simpa [a0] using sumCollect_run ⟨.sumCollect,b,r,a,[]⟩ a.norm.out
  have h2 : Runs ⟨.sumEmit,b,r,a0,a.norm.out.reverse⟩ (a.norm.out.length+1)
      ⟨.normalize,
        ⟨.numCollect,summed n a,d,BinaryRationalNormalizationMachine.initial a.negative [] [],[]⟩,
        r,a0,[]⟩ := by
    simpa [b,a0,emptied,summed,BinaryRationalNormalizationMachine.initial] using
      sumEmit_run ⟨.sumEmit,b,r,a0,[]⟩ a.norm.out.reverse
  convert h1.trans h2 using 1 <;> omega

end IdentityTesting.BinaryRationalArithmeticAdder
