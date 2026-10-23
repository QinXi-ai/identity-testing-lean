import IdentityTesting.BinaryInterpreterCompositeStorage
import IdentityTesting.BinaryInterpreterArithmeticInstances

namespace IdentityTesting.BinaryInterpreterArithmetic
open BinaryInterpreterStorage BinaryInterpreterLayouts RationalComputation

def arithmeticStorage : (op : RationalOp) → Storage (arithmeticLayout op)
  | .copy => copyStorage
  | .add => additionStorage
  | .sub => subtractionStorage
  | .mul => multiplicationStorage
  | .div => divisionStorage
  | .le => comparisonStorage

theorem arithmeticStorage_count (op : RationalOp) : (arithmeticStorage op).count ≤ 96 := by
  cases op <;> decide

end IdentityTesting.BinaryInterpreterArithmetic
