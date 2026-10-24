import IdentityTesting.BinaryInterpreterArithmeticInstances

namespace IdentityTesting.BinaryInterpreterLayout

/-- Physical input wiring laws, independent of the arithmetic result. -/
structure InputLocal (L : Layout) where
  get_set : ∀ right c w, L.input right (L.setInput right c w) = w
  set_self : ∀ right c, L.setInput right c (L.input right c) = c
  set_set : ∀ right c u v, L.setInput right (L.setInput right c u) v = L.setInput right c v
  other : ∀ right c w, L.input (!right) (L.setInput right c w) = L.input (!right) c

end IdentityTesting.BinaryInterpreterLayout

namespace IdentityTesting.BinaryInterpreterArithmetic
open BinaryInterpreterLayout RationalComputation

def arithmeticInputLocal (op : RationalOp) : InputLocal (arithmeticLayout op) where
  get_set := by cases op <;> intro right c w <;> cases right <;> rfl
  set_self := by cases op <;> intro right c <;> cases right <;> rfl
  set_set := by cases op <;> intro right c u v <;> cases right <;> rfl
  other := by cases op <;> intro right c w <;> cases right <;> rfl

end IdentityTesting.BinaryInterpreterArithmetic
