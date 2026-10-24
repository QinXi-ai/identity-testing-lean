import IdentityTesting.BinaryRationalArithmeticCeilSizeDispatch

namespace IdentityTesting.BinaryRationalArithmeticCeilSize
open BinaryArithmetic

theorem quotient_collect (s : State) (xs : List Bool) :
    Runs {s with phase := .quotientCollect,div := {s.div with quot := {s.div.quot with out := xs}}} (xs.length+1)
      {s with phase := .quotientEmit,div := {s.div with quot := {s.div.quot with out := []}},temp := xs.reverse++s.temp} := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b bs ih =>
      change advance (bs.length+1+1) _=_
      rw [advance]
      change advance (bs.length+1) {s with phase := .quotientCollect,div := {s.div with quot := {s.div.quot with out := bs}},temp := b::s.temp} = _
      rw [show advance _ _ = _ from ih {s with temp := b::s.temp}]
      simp [List.reverse_cons,List.append_assoc]

theorem rounded_collect (s : State) (xs : List Bool) :
    Runs {s with phase := .roundedCollect,counter := {s.counter with counter := xs}} (xs.length+1)
      {s with phase := .roundedEmit,counter := {s.counter with counter := []},temp := xs.reverse++s.temp} := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b bs ih =>
      change advance (bs.length+1+1) _=_
      rw [advance]
      change advance (bs.length+1) {s with phase := .roundedCollect,counter := {s.counter with counter := bs},temp := b::s.temp} = _
      rw [show advance _ _ = _ from ih {s with temp := b::s.temp}]
      simp [List.reverse_cons,List.append_assoc]

theorem ceiling_collect (s : State) (xs : List Bool) :
    Runs {s with phase := .ceilingCollect,norm := {s.norm with out := xs}} (xs.length+1)
      {s with phase := .ceilingEmit,norm := {s.norm with out := []},temp := xs.reverse++s.temp} := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b bs ih =>
      change advance (bs.length+1+1) _=_
      rw [advance]
      change advance (bs.length+1) {s with phase := .ceilingCollect,norm := {s.norm with out := bs},temp := b::s.temp} = _
      rw [show advance _ _ = _ from ih {s with temp := b::s.temp}]
      simp [List.reverse_cons,List.append_assoc]

theorem quotient_emit (s : State) (xs : List Bool) :
    Runs {s with phase := .quotientEmit,temp := xs} (xs.length+1)
      {s with phase := .round,temp := [],counter := {s.counter with counter := xs.reverse++s.counter.counter}} := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b bs ih =>
      change advance (bs.length+1+1) _=_
      rw [advance]
      change advance (bs.length+1) {s with phase := .quotientEmit,temp := bs,counter := {s.counter with counter := b::s.counter.counter}} = _
      rw [show advance _ _ = _ from ih {s with counter := {s.counter with counter := b::s.counter.counter}}]
      simp [List.reverse_cons,List.append_assoc]

theorem rounded_emit (s : State) (xs : List Bool) :
    Runs {s with phase := .roundedEmit,temp := xs} (xs.length+1)
      {s with phase := .normalize,temp := [],norm := {s.norm with source := xs.reverse++s.norm.source}} := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b bs ih =>
      change advance (bs.length+1+1) _=_
      rw [advance]
      change advance (bs.length+1) {s with phase := .roundedEmit,temp := bs,norm := {s.norm with source := b::s.norm.source}} = _
      rw [show advance _ _ = _ from ih {s with norm := {s.norm with source := b::s.norm.source}}]
      simp [List.reverse_cons,List.append_assoc]

theorem ceiling_emit (s : State) (xs : List Bool) :
    Runs {s with phase := .ceilingEmit,temp := xs} (xs.length+1)
      {s with phase := .measuring,temp := [],measure := {s.measure with core := {s.measure.core with source := xs.reverse++s.measure.core.source}}} := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b bs ih =>
      change advance (bs.length+1+1) _=_
      rw [advance]
      change advance (bs.length+1) {s with phase := .ceilingEmit,temp := bs,measure := {s.measure with core := {s.measure.core with source := b::s.measure.core.source}}} = _
      rw [show advance _ _ = _ from ih {s with measure := {s.measure with core := {s.measure.core with source := b::s.measure.core.source}}}]
      simp [List.reverse_cons,List.append_assoc]

end IdentityTesting.BinaryRationalArithmeticCeilSize
