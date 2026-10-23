import IdentityTesting.BinaryRationalArithmeticAdderDispatch

namespace IdentityTesting.BinaryRationalArithmeticAdder
open BinaryArithmetic

theorem pdenCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .pdenCollect, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with factor := xs } } } } (xs.length+1)
      { s with phase := .pdenCopy, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with factor := [] } } }, temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .pdenCollect, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with factor := xs } } }, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons,List.append_assoc]

theorem qdenCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .qdenCollect, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with shifted := xs } } } } (xs.length+1)
      { s with phase := .qdenCopy, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with shifted := [] } } }, temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .qdenCollect, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with shifted := xs } } }, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons,List.append_assoc]

theorem leftCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .leftCollect, base := { s.base with num := { s.base.num with norm := { s.base.num.norm with out := xs } } } } (xs.length+1)
      { s with phase := .leftEmit, base := { s.base with num := { s.base.num with norm := { s.base.num.norm with out := [] } } }, temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .leftCollect, base := { s.base with num := { s.base.num with norm := { s.base.num.norm with out := xs } } }, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons,List.append_assoc]

theorem rightCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .rightCollect, right := { s.right with norm := { s.right.norm with out := xs } } } (xs.length+1)
      { s with phase := .rightEmit, right := { s.right with norm := { s.right.norm with out := [] } }, temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .rightCollect, right := { s.right with norm := { s.right.norm with out := xs } }, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons,List.append_assoc]

theorem sumCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .sumCollect, adder := { s.adder with norm := { s.adder.norm with out := xs } } } (xs.length+1)
      { s with phase := .sumEmit, adder := { s.adder with norm := { s.adder.norm with out := [] } }, temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .sumCollect, adder := { s.adder with norm := { s.adder.norm with out := xs } }, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons,List.append_assoc]

theorem pdenCopy_run (s : State) (xs : List Bool) :
    Runs { s with phase := .pdenCopy, temp := xs } (xs.length+1)
      { s with phase := .qdenCollect, temp := [], base := { s.base with den := { s.base.den with mul := { s.base.den.mul with factor := xs.reverse ++ s.base.den.mul.factor } } }, right := { s.right with mul := { s.right.mul with shifted := xs.reverse ++ s.right.mul.shifted } } } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .pdenCopy, temp := xs, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with factor := b :: s.base.den.mul.factor } } }, right := { s.right with mul := { s.right.mul with shifted := b :: s.right.mul.shifted } } } = _
      rw [show advance _ _ = _ from ih { s with base := { s.base with den := { s.base.den with mul := { s.base.den.mul with factor := b :: s.base.den.mul.factor } } }, right := { s.right with mul := { s.right.mul with shifted := b :: s.right.mul.shifted } } }]
      simp [List.reverse_cons,List.append_assoc]

theorem qdenCopy_run (s : State) (xs : List Bool) :
    Runs { s with phase := .qdenCopy, temp := xs } (xs.length+1)
      { s with phase := .leftProduct, temp := [], base := { s.base with den := { s.base.den with mul := { s.base.den.mul with shifted := xs.reverse ++ s.base.den.mul.shifted } }, num := { s.base.num with mul := { s.base.num.mul with shifted := xs.reverse ++ s.base.num.mul.shifted } } } } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .qdenCopy, temp := xs, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with shifted := b :: s.base.den.mul.shifted } }, num := { s.base.num with mul := { s.base.num.mul with shifted := b :: s.base.num.mul.shifted } } } } = _
      rw [show advance _ _ = _ from ih { s with base := { s.base with den := { s.base.den with mul := { s.base.den.mul with shifted := b :: s.base.den.mul.shifted } }, num := { s.base.num with mul := { s.base.num.mul with shifted := b :: s.base.num.mul.shifted } } } }]
      simp [List.reverse_cons,List.append_assoc]

theorem leftEmit_run (s : State) (xs : List Bool) :
    Runs { s with phase := .leftEmit, temp := xs } (xs.length+1)
      { s with phase := .rightCollect, temp := [], adder := { s.adder with left := xs.reverse ++ s.adder.left } } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .leftEmit, temp := xs, adder := { s.adder with left := b :: s.adder.left } } = _
      rw [show advance _ _ = _ from ih { s with adder := { s.adder with left := b :: s.adder.left } }]
      simp [List.reverse_cons,List.append_assoc]

theorem rightEmit_run (s : State) (xs : List Bool) :
    Runs { s with phase := .rightEmit, temp := xs } (xs.length+1)
      { s with phase := .add, temp := [], adder := { s.adder with right := xs.reverse ++ s.adder.right } } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .rightEmit, temp := xs, adder := { s.adder with right := b :: s.adder.right } } = _
      rw [show advance _ _ = _ from ih { s with adder := { s.adder with right := b :: s.adder.right } }]
      simp [List.reverse_cons,List.append_assoc]

theorem sumEmit_run (s : State) (xs : List Bool) :
    Runs { s with phase := .sumEmit, temp := xs } (xs.length+1)
      { s with phase := .normalize, temp := [], base := { s.base with num := { s.base.num with norm := { s.base.num.norm with out := xs.reverse ++ s.base.num.norm.out }, negative := s.adder.negative }, norm := { s.base.norm with negative := s.adder.negative } } } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .sumEmit, temp := xs, base := { s.base with num := { s.base.num with norm := { s.base.num.norm with out := b :: s.base.num.norm.out } } } } = _
      rw [show advance _ _ = _ from ih { s with base := { s.base with num := { s.base.num with norm := { s.base.num.norm with out := b :: s.base.num.norm.out } } } }]
      simp [List.reverse_cons,List.append_assoc]

end IdentityTesting.BinaryRationalArithmeticAdder
