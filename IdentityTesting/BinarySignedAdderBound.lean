import IdentityTesting.BinarySignedAdderCore

namespace IdentityTesting.BinarySignedAdder
open BinaryArithmetic BinarySignedWords

theorem finish_output (s : State) (out : List Bool)
    (ht : s.temp = []) (hn : s.norm = ⟨.collect, [], [], []⟩) :
    ∃ j, j ≤ 4 * out.length + 6 ∧
      (advance j { s with phase := .outCollect, arith := { s.arith with out := out } }).phase = .halt ∧
      (output (advance j { s with phase := .outCollect, arith := { s.arith with out := out } })).magnitude = (value out).bits ∧
      (output (advance j { s with phase := .outCollect, arith := { s.arith with out := out } })).value =
        signedValue s.negative (value out) := by
  let emptyArith := { s.arith with out := [] }
  have h1 : Runs { s with phase := .outCollect, arith := { s.arith with out := out } } (out.length + 1)
      { s with phase := .outEmit, arith := emptyArith, temp := out.reverse } := by
    simpa [ht, emptyArith] using outCollect_run s out
  have h2 : Runs { s with phase := .outEmit, arith := emptyArith, temp := out.reverse } (out.length + 1)
      { s with phase := .normalizing, arith := emptyArith, temp := [], norm := ⟨.collect,out,[],[]⟩ } := by
    simpa [hn] using outEmit_run { s with arith := emptyArith } out.reverse
  let s2 := { s with phase := .normalizing, arith := emptyArith, temp := [], norm := ⟨.collect,out,[],[]⟩ }
  have hnorm := BinaryWordNormalization.normalization_run out
  obtain ⟨j,hj,hr⟩ := forward_norm s2 ⟨.collect,out,[],[]⟩ (2*out.length+2) (by rw [hnorm])
  rw [hnorm] at hr
  have h3 : Runs s2 j { s2 with phase := .finish, norm := ⟨.halt,[],[],BinaryWordNormalization.trim out⟩ } := hr
  have h4 : Runs { s2 with phase := .finish, norm := ⟨.halt,[],[],BinaryWordNormalization.trim out⟩ } 1
      { s2 with phase := .halt, norm := ⟨.halt,[],[],BinaryWordNormalization.trim out⟩, negative := if BinaryWordNormalization.trim out = [] then false else s.negative } := rfl
  have hw := ((h1.trans h2).trans h3).trans h4
  refine ⟨(out.length+1)+(out.length+1)+j+1,by omega,?_,?_,?_⟩
  · rw [hw]
  · change (advance _ _).norm.out = _
    rw [hw]
    exact BinaryWordNormalization.trim_eq_bits out
  · change signedValue (advance _ _).negative (value (advance _ _).norm.out) = _
    rw [hw]
    simp only
    rw [clear_zero_sign, BinaryWordNormalization.trim_value]

theorem run_signed_sum (a b : Bool) (xs ys : List Bool) :
    ∃ steps, steps ≤ 4*(xs.length+ys.length)+15*max xs.length ys.length+26 ∧
      (advance steps (initial ⟨a,xs⟩ ⟨b,ys⟩)).phase = .halt ∧
      (output (advance steps (initial ⟨a,xs⟩ ⟨b,ys⟩))).value =
        signedValue a (value xs) + signedValue b (value ys) ∧
      (output (advance steps (initial ⟨a,xs⟩ ⟨b,ys⟩))).magnitude =
        (signedValue a (value xs) + signedValue b (value ys)).natAbs.bits := by
  obtain ⟨p,c,hp,hc,hpr⟩ := prepare a b xs ys
  obtain ⟨k,r,out,hk,hl,hv,hr⟩ := run_arithmetic a b xs ys c hc
  let s := { (arithmeticReady a b xs ys c) with phase := .outCollect, arith := BinaryAdderMachine.haltState r out }
  obtain ⟨j,hj,hh,hm,ho⟩ := finish_output s out rfl rfl
  have he : { s with phase := .outCollect, arith := { s.arith with out := out } } = s := rfl
  rw [he] at hh hm ho
  have hwhole : advance (p+k+j) (initial ⟨a,xs⟩ ⟨b,ys⟩) = advance j s := by
    rw [advance_add, advance_add, hpr, hr]
  refine ⟨p+k+j,by omega,?_,?_,?_⟩
  · rw [hwhole]
    exact hh
  · rw [hwhole,ho]
    exact hv
  · rw [hwhole,hm,← hv]
    cases hs : (arithmeticReady a b xs ys c).negative <;> simp [signedValue,hs]

theorem binary_signed_addition_machine (x y : ℤ) :
    ∃ steps, let s := initial (encode x) (encode y)
      (advance steps s).phase = .halt ∧ (output (advance steps s)).value = x+y ∧
      (output (advance steps s)).magnitude = (x+y).natAbs.bits ∧
      bitSteps steps s ≤ 400 * (x.natAbs.size+y.natAbs.size+1) := by
  obtain ⟨steps,hs,hh,hv,hm⟩ := run_signed_sum (encode x).negative (encode y).negative
    (encode x).magnitude (encode y).magnitude
  refine ⟨steps,hh,?_,?_,?_⟩
  · simpa [encode, signedValue_int] using hv
  · simpa [encode, signedValue_int] using hm
  · have hb := bitSteps_le steps (initial (encode x) (encode y))
    simp only [encode,Nat.size_eq_bits_len] at hs
    have hmax : max x.natAbs.size y.natAbs.size ≤ x.natAbs.size+y.natAbs.size := max_le (by omega) (by omega)
    omega

end IdentityTesting.BinarySignedAdder
