import IdentityTesting.BinaryWorkspaceRationalAdder

namespace IdentityTesting.BinaryAdderStorage
open BinaryWorkspaceAdapters BinaryWorkspaceGrowth
open scoped BigOperators
set_option maxRecDepth 4096

def tapes (c : BinaryRationalArithmeticAdder.State) : Fin 94 → List Bool :=
  ![c.base.num.mul.factor,
    c.base.num.mul.shifted,
    c.base.num.mul.temp,
    c.base.num.mul.acc,
    c.base.num.mul.adder.left,
    c.base.num.mul.adder.right,
    c.base.num.mul.adder.work,
    c.base.num.mul.adder.out,
    c.base.num.norm.source,
    c.base.num.norm.work,
    c.base.num.norm.out,
    c.base.num.temp,
    c.base.den.mul.factor,
    c.base.den.mul.shifted,
    c.base.den.mul.temp,
    c.base.den.mul.acc,
    c.base.den.mul.adder.left,
    c.base.den.mul.adder.right,
    c.base.den.mul.adder.work,
    c.base.den.mul.adder.out,
    c.base.den.norm.source,
    c.base.den.norm.work,
    c.base.den.norm.out,
    c.base.den.temp,
    c.base.norm.gcd.div.source,
    c.base.norm.gcd.div.bits,
    c.base.norm.gcd.div.divisor,
    c.base.norm.gcd.div.temp,
    c.base.norm.gcd.div.sub.left,
    c.base.norm.gcd.div.sub.right,
    c.base.norm.gcd.div.sub.work,
    c.base.norm.gcd.div.sub.out,
    c.base.norm.gcd.div.quot.source,
    c.base.norm.gcd.div.quot.work,
    c.base.norm.gcd.div.quot.out,
    c.base.norm.gcd.div.rem.source,
    c.base.norm.gcd.div.rem.work,
    c.base.norm.gcd.div.rem.out,
    c.base.norm.gcd.temp,
    c.base.norm.num.source,
    c.base.norm.num.bits,
    c.base.norm.num.divisor,
    c.base.norm.num.temp,
    c.base.norm.num.sub.left,
    c.base.norm.num.sub.right,
    c.base.norm.num.sub.work,
    c.base.norm.num.sub.out,
    c.base.norm.num.quot.source,
    c.base.norm.num.quot.work,
    c.base.norm.num.rem.source,
    c.base.norm.num.rem.work,
    c.base.norm.num.rem.out,
    c.base.norm.den.source,
    c.base.norm.den.bits,
    c.base.norm.den.divisor,
    c.base.norm.den.temp,
    c.base.norm.den.sub.left,
    c.base.norm.den.sub.right,
    c.base.norm.den.sub.work,
    c.base.norm.den.sub.out,
    c.base.norm.den.quot.source,
    c.base.norm.den.quot.work,
    c.base.norm.den.rem.source,
    c.base.norm.den.rem.work,
    c.base.norm.den.rem.out,
    c.base.norm.temp,
    c.base.temp,
    c.base.norm.num.quot.out,
    c.base.norm.den.quot.out,
    c.right.mul.factor,
    c.right.mul.shifted,
    c.right.mul.temp,
    c.right.mul.acc,
    c.right.mul.adder.left,
    c.right.mul.adder.right,
    c.right.mul.adder.work,
    c.right.mul.adder.out,
    c.right.norm.source,
    c.right.norm.work,
    c.right.norm.out,
    c.right.temp,
    c.adder.left,
    c.adder.right,
    c.adder.temp,
    c.adder.compare.left,
    c.adder.compare.right,
    c.adder.arith.left,
    c.adder.arith.right,
    c.adder.arith.work,
    c.adder.arith.out,
    c.adder.norm.source,
    c.adder.norm.work,
    c.adder.norm.out,
    c.temp]

def setTapes (c : BinaryRationalArithmeticAdder.State) (f : Fin 94 → List Bool) :
    BinaryRationalArithmeticAdder.State :=
  {c with base := {c.base with num := {c.base.num with mul := {c.base.num.mul with factor := f 0, shifted := f 1, temp := f 2, acc := f 3, adder := {c.base.num.mul.adder with left := f 4, right := f 5, work := f 6, out := f 7}}, norm := {c.base.num.norm with source := f 8, work := f 9, out := f 10}, temp := f 11}, den := {c.base.den with mul := {c.base.den.mul with factor := f 12, shifted := f 13, temp := f 14, acc := f 15, adder := {c.base.den.mul.adder with left := f 16, right := f 17, work := f 18, out := f 19}}, norm := {c.base.den.norm with source := f 20, work := f 21, out := f 22}, temp := f 23}, norm := {c.base.norm with gcd := {c.base.norm.gcd with div := {c.base.norm.gcd.div with source := f 24, bits := f 25, divisor := f 26, temp := f 27, sub := {c.base.norm.gcd.div.sub with left := f 28, right := f 29, work := f 30, out := f 31}, quot := {c.base.norm.gcd.div.quot with source := f 32, work := f 33, out := f 34}, rem := {c.base.norm.gcd.div.rem with source := f 35, work := f 36, out := f 37}}, temp := f 38}, num := {c.base.norm.num with source := f 39, bits := f 40, divisor := f 41, temp := f 42, sub := {c.base.norm.num.sub with left := f 43, right := f 44, work := f 45, out := f 46}, quot := {c.base.norm.num.quot with source := f 47, work := f 48, out := f 67}, rem := {c.base.norm.num.rem with source := f 49, work := f 50, out := f 51}}, den := {c.base.norm.den with source := f 52, bits := f 53, divisor := f 54, temp := f 55, sub := {c.base.norm.den.sub with left := f 56, right := f 57, work := f 58, out := f 59}, quot := {c.base.norm.den.quot with source := f 60, work := f 61, out := f 68}, rem := {c.base.norm.den.rem with source := f 62, work := f 63, out := f 64}}, temp := f 65}, temp := f 66}, right := {c.right with mul := {c.right.mul with factor := f 69, shifted := f 70, temp := f 71, acc := f 72, adder := {c.right.mul.adder with left := f 73, right := f 74, work := f 75, out := f 76}}, norm := {c.right.norm with source := f 77, work := f 78, out := f 79}, temp := f 80}, adder := {c.adder with left := f 81, right := f 82, temp := f 83, compare := {c.adder.compare with left := f 84, right := f 85}, arith := {c.adder.arith with left := f 86, right := f 87, work := f 88, out := f 89}, norm := {c.adder.norm with source := f 90, work := f 91, out := f 92}}, temp := f 93}

theorem tapes_set (c : BinaryRationalArithmeticAdder.State) (f : Fin 94 → List Bool) :
    tapes (setTapes c f) = f := by
  funext i
  fin_cases i <;> rfl

theorem set_tapes (c : BinaryRationalArithmeticAdder.State) : setTapes c (tapes c) = c := by rfl

theorem set_set (c : BinaryRationalArithmeticAdder.State) (f g : Fin 94 → List Bool) :
    setTapes (setTapes c f) g = setTapes c g := by rfl

set_option maxHeartbeats 1200000 in
theorem tapes_cells (c : BinaryRationalArithmeticAdder.State) :
    (∑ i, (tapes c i).length) = rationalAdderCells c := by
  simp [tapes, Fin.sum_univ_succ, rationalAdderCells, rationalMultiplierCells,
    signedMultiplierCells, multiplierCells, normalizerCells, rationalNormalizationCells,
    gcdCells, divisionCells, adderCells, signedAdderCells, signedComparisonCells]
  omega

end IdentityTesting.BinaryAdderStorage
