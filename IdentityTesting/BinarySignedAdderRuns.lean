import IdentityTesting.BinarySignedAdder

namespace IdentityTesting.BinarySignedAdder
open BinaryArithmetic BinarySignedWords

theorem leftCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .leftCollect, left := xs } (xs.length + 1)
      { s with phase := .leftCopy, left := [], temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) { s with phase := .leftCollect, left := xs, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons, List.append_assoc]

theorem leftCopy_run (s : State) (xs : List Bool) :
    Runs { s with phase := .leftCopy, temp := xs } (xs.length + 1)
      { s with phase := .rightCollect, temp := [], left := xs.reverse ++ s.left, compare := { s.compare with left := xs.reverse ++ s.compare.left } } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) { s with phase := .leftCopy, temp := xs, left := b :: s.left, compare := { s.compare with left := b :: s.compare.left } } = _
      rw [show advance _ _ = _ from ih { s with left := b :: s.left, compare := { s.compare with left := b :: s.compare.left } }]
      simp [List.reverse_cons, List.append_assoc]

theorem rightCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .rightCollect, right := xs } (xs.length + 1)
      { s with phase := .rightCopy, right := [], temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) { s with phase := .rightCollect, right := xs, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons, List.append_assoc]

theorem rightCopy_run (s : State) (xs : List Bool) :
    Runs { s with phase := .rightCopy, temp := xs } (xs.length + 1)
      { s with phase := .comparing, temp := [], right := xs.reverse ++ s.right, compare := { s.compare with right := xs.reverse ++ s.compare.right } } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) { s with phase := .rightCopy, temp := xs, right := b :: s.right, compare := { s.compare with right := b :: s.compare.right } } = _
      rw [show advance _ _ = _ from ih { s with right := b :: s.right, compare := { s.compare with right := b :: s.compare.right } }]
      simp [List.reverse_cons, List.append_assoc]

theorem leftRouteCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .leftRouteCollect, left := xs } (xs.length + 1)
      { s with phase := .leftRouteEmit, left := [], temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) { s with phase := .leftRouteCollect, left := xs, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons, List.append_assoc]

theorem leftRouteEmit_run (s : State) (xs : List Bool) :
    Runs { s with phase := .leftRouteEmit, temp := xs } (xs.length + 1)
      { s with phase := .rightRouteCollect, temp := [], arith := if s.swap then
        { s.arith with right := xs.reverse ++ s.arith.right }
        else { s.arith with left := xs.reverse ++ s.arith.left } } := by
  induction xs generalizing s with
  | nil => cases hs : s.swap <;> cases s <;> simp_all [Runs, advance, step]
  | cons b xs ih =>
      cases hs : s.swap
      · change advance (xs.length + 1 + 1) _ = _
        rw [advance]
        simp only [step, hs, Bool.false_eq_true, ↓reduceIte]
        simpa [Runs, hs, List.reverse_cons, List.append_assoc] using
          ih { s with arith := { s.arith with left := b :: s.arith.left } }
      · change advance (xs.length + 1 + 1) _ = _
        rw [advance]
        simp only [step, hs, ↓reduceIte]
        simpa [Runs, hs, List.reverse_cons, List.append_assoc] using
          ih { s with arith := { s.arith with right := b :: s.arith.right } }

theorem rightRouteCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .rightRouteCollect, right := xs } (xs.length + 1)
      { s with phase := .rightRouteEmit, right := [], temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) { s with phase := .rightRouteCollect, right := xs, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons, List.append_assoc]

theorem rightRouteEmit_run (s : State) (xs : List Bool) :
    Runs { s with phase := .rightRouteEmit, temp := xs } (xs.length + 1)
      { s with phase := .arithmetic, temp := [], arith := if s.swap then
        { s.arith with left := xs.reverse ++ s.arith.left }
        else { s.arith with right := xs.reverse ++ s.arith.right } } := by
  induction xs generalizing s with
  | nil => cases hs : s.swap <;> cases s <;> simp_all [Runs, advance, step]
  | cons b xs ih =>
      cases hs : s.swap
      · change advance (xs.length + 1 + 1) _ = _
        rw [advance]
        simp only [step, hs, Bool.false_eq_true, ↓reduceIte]
        simpa [Runs, hs, List.reverse_cons, List.append_assoc] using
          ih { s with arith := { s.arith with right := b :: s.arith.right } }
      · change advance (xs.length + 1 + 1) _ = _
        rw [advance]
        simp only [step, hs, ↓reduceIte]
        simpa [Runs, hs, List.reverse_cons, List.append_assoc] using
          ih { s with arith := { s.arith with left := b :: s.arith.left } }

theorem outCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .outCollect, arith := { s.arith with out := xs } } (xs.length + 1)
      { s with phase := .outEmit, arith := { s.arith with out := [] }, temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) { s with phase := .outCollect, arith := { s.arith with out := xs }, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons, List.append_assoc]

theorem outEmit_run (s : State) (xs : List Bool) :
    Runs { s with phase := .outEmit, temp := xs } (xs.length + 1)
      { s with phase := .normalizing, temp := [], norm := { s.norm with source := xs.reverse ++ s.norm.source } } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) { s with phase := .outEmit, temp := xs, norm := { s.norm with source := b :: s.norm.source } } = _
      rw [show advance _ _ = _ from ih { s with norm := { s.norm with source := b :: s.norm.source } }]
      simp [List.reverse_cons, List.append_assoc]

end IdentityTesting.BinarySignedAdder
