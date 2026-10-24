# Identity testing in Lean

Lean 4 formalization of the core results of *Instance-Optimal Identity Testing
at the Original Total-Variation Radius: Resolving Canonne's 2024 Open Question 1*,
by Xi Qin (Wuhan University).

## Verified results

- **Statistical characterization.** For every probability distribution on the
  natural numbers and every radius `0 < ε ≤ 1`, the sample complexity is bounded
  above and below by universal constant multiples of the characterization scale.
  The model uses independent samples, randomized tests with both errors at most
  `1/3`, and strict alternatives `ε < totalVariation p q`. Alternative distributions
  may assign mass outside the reference support.
- **Certified rational evaluation.** For any nonempty finite list of positive
  rational probabilities summing to one and a rational radius `0 < ε ≤ 1`, an
  executable algorithm returns rational endpoints satisfying
  `0 ≤ L ≤ complexityScale(q, ε) ≤ U ≤ 2L`. The endpoints are positive when
  `ε < 1` and both zero when `ε = 1`.
- **Rational representation sizes.** Explicit bounds for reduced numerators and
  denominators, the coordinate-bisection endpoints and actual queries, and the
  allocation oracle's parameters, search queries, and returned intervals, all in
  terms of the original rational input length.
- **Continuity and relabeling.** Joint continuity of the overlap moment under
  arbitrary ℓ¹ convergence and positive limiting overlap targets; invariance of
  allocation, moment, roots, and characterization scales under countable
  permutations, including tied largest atoms.
- **Explicit examples.** Exact uniform allocation and root formulas, the
  near-endpoint scale `max(1, √(k(1−ε)))`, and the flat-tail boundary scale
  `k^(2/5)/R`, including its exterior minimum transition.
- **Minimum sample counts.** A natural-number minimum in the original test
  model, its universal scale comparison, and the exact point-mass formula;
  the finite `h ≤ 4/5` corollary and heavy-atom bounds including `R = 1/4`.
- **General roots and signed mixtures.** Existence and continuity of roots for
  arbitrary nonnegative summable mass vectors; the general signed-likelihood
  matrix total-variation bound and its explicit heavy-atom Frobenius constant.
- **Arbitrary probability priors.** The testing-error inequality holds for
  measurable probability-measure priors on laws on the natural numbers, with
  an integral mixture and an almost-everywhere strict-alternative condition.
- **Allocation analysis.** Strict concavity, explicit derivatives, the sharp
  finite-dimensional Hölder envelope, the original time-decrease window, and
  the real oracle family's continuity, monotonicity, range and elasticities,
  parameter-ratio bounds and certified stopping windows. The right derivative
  diverges at zero allocation.
  Feasible heavy-tail compression has the original `1024` and strict `16/T` bounds.
- **Explicit testing constants.** The concentrated-coordinate budget and moment
  bounds use `1/6` and `8/3`; the actual mean and collision tests satisfy the
  manuscript's `0.0576`, `0.0288`, `1.5e-6` and `0.006` error bounds, including
  the sharper heavy-tail mean bounds. The light-label moment branch has mean
  errors below `0.0032` and `0.0016`, null collision error below `0.000051`,
  and alternative collision miss probability below `0.013`. The combined test
  has null error below `0.003251` and miss probability below `0.013`.
- **Explicit prior bounds.** The constructed general allocation prior has
  sample-mixture total variation below `10^-4` and every positive-weight member
  is strictly separated. Deterministic general and heavy tilts satisfy the
  manuscript's square-root sample bounds. Dyadic seed compression permits
  arbitrary positive masses and zero exterior mass, with the exact ceiling counts.
  The small-scale heavy tilt has sample TV below `1/50`; feasible heavy
  compression has the original overlap bound below `(E+g)/100`.
- **Restricted-support lower bounds.** Heavy interior and near-exterior lower
  bounds remain valid when alternatives are restricted to the positive support.
- **Effective countable evaluation.** Rational atom approximations and certified
  vanishing tail bounds give executable interval algorithms for the allocation
  functional, both positive roots and the overlap moment. The root and moment
  endpoints converge to the original infinite-support quantities. The heavy
  evaluator retains the full tail mass.
- **Normalized truncation.** Exact total variation and scaling identities,
  the heavy-boundary limit, and transfer of tests through 100 independent
  randomized batches with error at most `exp(-25/8) < 1/3`.
- **Pooling loss.** The exact TV loss after pooling any finite set is half the
  tail absolute-difference loss, equivalently the smaller residual mass minus
  the residual overlap. In particular it lies between zero and that residual mass.
- **Binary arithmetic machines.** Fixed finite-control stack machines for
  addition, multiplication, subtraction, division, gcd and rational normalization,
  with proved termination, canonical outputs and polynomial primitive-action bounds.
  Signed addition, multiplication, comparison and negation include zero-sign handling.
  Signed addition uses at most `400(bits(|x|)+bits(|y|)+1)` primitive actions.
  Signed subtraction is linear, and an actual rational multiplication machine
  returns the reduced fraction within `20000(L(p)+L(q)+1)^3` primitive actions.
  Rational addition returns the canonical sum within
  `1300000(L(p)+L(q)+1)^3` primitive actions.
  Rational division, subtraction and comparison have canonical-output bounds of
  `50000`, `2700000` and `5500000` times `(L(p)+L(q)+1)^3`, respectively.
  Division includes the totalized zero-denominator case.
  A binary length machine reads the input cells, increments a binary counter,
  and returns the canonical binary length within `100(L+1)^2` primitive actions.
  A rational ceiling-size machine performs division, rounding, normalization and
  bit counting to return `size(ceil(q))` as a canonical rational record, within
  `8000(L(q)+1)^2` primitive actions. A separate scratch-cleanup bound gives
  `40000(L(q)+1)^2` in total.
- **Register and workspace operations.** Actual symbol machines read and write
  delimited registers, split and join rational records, and clear arithmetic
  scratch stacks while preserving an output frame. Rational multiplication and
  scratch cleanup together cost at most `100000(L(p)+L(q)+1)^3` primitive actions.
  Load and store use a shared physical record tape, with explicit costs in the
  register encoding size and the loaded or stored rational length.
  Register copying composes those actual machines, including coincident source
  and destination addresses. Addition and division include separate proved
  bounds for clearing every scratch cell while preserving the output.
  A multiplication instruction performs both loads, arithmetic, writeback and
  cleanup in one machine; all arithmetic and IO scratch stacks finish empty.
  Its source and destination addresses are supplied as unary tapes.
  One shared load/operate/store interpreter handles all six register operations
  (copy, addition, subtraction, multiplication, division and comparison), with
  exact instruction semantics and a uniform polynomial primitive-action bound.
  The same interpreter has a proved physical cleanup phase for all six operations:
  the result tape is preserved and every arithmetic and IO scratch stack is empty.
  The total bound is `3000*T + 100000000*S^3`, where `T` is the register-tape
  encoding size and `S` is the sum of operand lengths plus one. Whole-program
  dispatch remains to be assembled. Separate field loaders read unary addresses,
  rational literal bodies and tags from an existing code tape, preserving a
  history that a symbol-by-symbol rewind routine restores. Their costs include
  the field movements; initial code-tape generation is not yet implemented.
  Literal payloads can write directly into either physical input of each of the
  six arithmetic primitives, preserving the other input and emptying the loader
  temporary stack. Six fixed groups use 427 physical stacks; rearming preserves
  all their contents and resets only finite control.
  The ceiling-size control operation also uses the shared register interpreter:
  load, compute, writeback and physical cleanup cost at most
  `2400*T + 9000000*(L+1)^2`. It supports a source equal to its destination,
  clears all 31 core stacks and all IO stacks, and can be rearmed for reuse.
  This implementation counts a second source load into an auxiliary input word;
  its 31 stacks are separate from the six arithmetic groups above.
  A shared operand-code loader now consumes the reg/literal discriminators and
  both payloads, with all four operand combinations supported. It feeds the same
  arithmetic core used by operate/writeback/physical cleanup for all six operations.
  The result tape equals the corresponding register update, including destination
  aliases; the unread code suffix and complete reversed operand history are
  preserved, and all core, I/O and loader temporary stacks finish empty.
  Its bound is `5000*(T + lhs.slots + rhs.slots) + 100000000*S^3`, where
  `S = L(lhs.read registers) + L(rhs.read registers) + 1`.
  A fixed-pool single-instruction dispatcher also reads the operation code and
  destination from the instruction tape. Its entry takes only the pool, register
  tape, code and history. It selects the actual operation group at runtime,
  leaves all other groups unchanged, and returns exactly the source instruction's
  register update, with an empty workspace and the full consumed instruction in
  history. Its bound is `6000*(T + lhs.slots + rhs.slots + 1) + 100000000*S^3`.
  Rearming preserves every physical stack and supports the next instruction on
  the same pool. This covers `RationalProgramCode.instruction`; outer program-node
  tags and whole-program control remain to be connected. These costs count the
  defined transition traces; a general BitOp interpreter/simulation theorem is
  not yet supplied.
- **Actual rational instruction traces.** A finite-register program implements
  coordinate bisection and the complete finite-vector budget/objective evaluator.
  Its output equals the original interval evaluator, with at most `k(21n+45)`
  arithmetic/comparison calls and `17+k` registers. Every actual operand,
  including partial sums and scratch values, has a proved polynomial length bound.
  The outer search program also returns exactly the original allocation oracle's
  result. Its arithmetic/comparison call count is polynomial in the original
  input length, and its code size and register count have explicit bounds.
  A general trace theorem bounds every intermediate register and the entire
  register tape from the initial lengths and actual operand lengths.
  For the complete allocation search, every actual operand and every intermediate
  register tape has a polynomial bound directly in the original input length,
  including all stopping branches and exhaustion of the iteration budget.
  Initialization programs read the original rational inputs to compute the seven
  oracle parameters and precision ratios, with proved instruction, register and
  code-size bounds. The expression compiler preserves the input registers.
  Every actual initialization operand and intermediate register tape also has
  an explicit polynomial encoding bound in the original input length.
  A program depending only on the dimension now starts from the original
  `[t, sigma] ++ a` and zero scratch, computes its initialization fields and
  runtime precision/fuel, and returns exactly `allocationOracle`. Its dynamic
  arithmetic trace agrees with the proved search trace. The code tape has an
  explicit length bound. Separate binary-counter routines preserve the counter
  when testing zero and compute predecessor in at most `12*(bits(n)+1)` primitive
  actions. These components still need whole-program bit-machine assembly,
  including code generation, scratch allocation and nested counter storage.
  A register-to-counter component now reads natural-valued rational registers,
  uses the reader's numerator stack as the counter, and physically clears the
  denominator. Its cost is at most `45*T + 30*L(n) + 180`; zero testing and
  predecessor continue on the same counter stacks. The actual initializer's
  precision and fuel registers are proved natural and in bounds, so their
  counter loads need no supplied naturalness certificate. The input tape here
  encodes the source initializer's output; binary execution of that initializer,
  arbitrary rational floor conversion and nested loop control remain separate.
- **Gaussian calculations.** Exact linear and diagonal quadratic exponential
  integrals, orthogonal invariance of the standard Gaussian vector, and the
  finite-sign/Gaussian interchange used in the signed-matrix argument. Quadratic
  integration and integrability hold in an orthonormal eigenbasis. For a
  self-adjoint operator of norm below one, the spectral theorem constructs that
  basis and gives the exact product formula without a supplied eigenbasis.
  The actual Gram quadratic form and trace agree with the squared Euclidean and
  Frobenius norms, and the Euclidean operator norm is bounded by the Frobenius norm.
  The squared-matrix-norm exponential is integrable under the corresponding
  Frobenius bound. The exact integral also equals
  `1/sqrt(det(I-t^2 M^T M))`. For real symmetric `M` with `n*||M||F <= 1/2`,
  the signed average is bounded by `1/sqrt(det(I-n^2 M^2))`, which is at most
  `exp(n^2 ||M||F^2)`. The determinant is positive and the Gaussian integrand is
  integrable under these hypotheses.

The statistical proof constructs tests for the point-mass, allocation, moment,
and heavy-atom interior/exterior regimes, then transfers finite results to
countable references. The evaluation algorithm includes rational allocation
oracles, certified root searches, maximum-atom selection, and moment intervals.

**Scope:** a polynomial bit-operation bound for the complete evaluation algorithm
is not yet formalized. Executable definitions and proved termination alone do
not establish a polynomial-time bound.
Some auxiliary manuscript claims and the complete arithmetic/algorithm cost
composition remain unfinished.

### Representation-size bounds

Write `L(q) = 1 + bits(|q.num|) + bits(q.den)` and
`V(a) = k + ∑ᵢ L(aᵢ)`. The checked results include:

- After `n` coordinate-bisection steps, each endpoint has length at most `2n+3`.
- The actual query after `i` completed steps has length at most `2i+5`; its sign-polynomial
  value has length at most `2(L(a)+L(β))+76i+255`.
- For `B = 2n+2L(ρ)+7`, each pole-safe coordinate endpoint has length at most `B`.
  Each objective-interval endpoint has length at most `2V(a)+2kB+3`, and each
  budget-interval endpoint at most `4V(a)+2k(2L(t)+12B+22)+3`.
- The computed precision `n = oracleDyadicPrecision C δ` satisfies
  `n ≤ L(C)+L(δ)+1` whenever `δ > 0`.

For the actual allocation oracle, let `S = V(a)+L(t)+L(σ)`. Its chosen inner
precision is at most `33S+158`, and its outer fuel is at most `30S+126`.
An instrumented search returns the same interval and records at most `30S+128`
source-level budget/objective calls; every recorded parameter has length at most `180S+737`.
Each returned endpoint has length at most `368S²+1778S+25`.

For the full interval algorithm, put `T = V(q)+L(ε)`. Each returned endpoint has
length at most `288T²+2536T+5355`. Both root searches have linear bounds on
their source-level oracle-call counts, query lengths, and tolerances in their
own input lengths. Square-root and moment interval representations are bounded
as well.

These statements refer to the executable Lean definitions. The coordinate
routine bisects `[0,1]` and clips the upper endpoint to `1−ρ`; its correctness
is proved for this implementation. Composition of the remaining signed rational
arithmetic operations through the full algorithm must still be
proved before a polynomial bit-operation complexity theorem can be claimed.

The separate bit-stack machines add binary inputs `m,n` in at most
`50 max(bits(m),bits(n))+20` primitive actions and multiply them in at most
`140 bits(m)(bits(m)+bits(n)+1)+7`. Their transitions operate on individual
Boolean stack cells and finite registers. These bounds concern that explicit
machine model, not Lean's native integer runtime.

Long division costs at most `210(bits(m)+bits(n)+1)^2` actions and gcd at most
`400(bits(m)+bits(n)+1)^3`. For any integer `z` and positive denominator `d`,
fraction normalization returns the exact reduced numerator and denominator of
`z/d` in at most `9000(bits(|z|)+bits(d)+1)^3` actions.
Signed multiplication costs at most `200(bits(|x|)+bits(|y|)+1)^2` actions,
and signed comparison at most `11 max(bits(|x|),bits(|y|))+22`.

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/QinXi-ai/identity-testing-lean.git
cd identity-testing-lean
lake exe cache get
lake build +IdentityTesting:olean
lake env lean Verification.lean
```

Lean is pinned to **4.24.0** in `lean-toolchain`. Mathlib is pinned to commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; transitive dependencies are recorded
in `lake-manifest.json`. No local machine paths or external proof certificates
are required.

`Verification.lean` imports the public entry point, prints the main theorem
types and definitions, audits their transitive axioms, and evaluates examples
covering all branches and a reordered reference. The audited proofs use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Entry points

| File | Result |
|---|---|
| [IdentityTesting.lean](IdentityTesting.lean) | Public import |
| [CountableCharacterization.lean](IdentityTesting/CountableCharacterization.lean) | Full countable statistical theorem |
| [CountableCharacterizationRealScale.lean](IdentityTesting/CountableCharacterizationRealScale.lean) | Bounds directly in the real characterization scale |
| [RationalComplexityScale.lean](IdentityTesting/RationalComplexityScale.lean) | Executable interval algorithm and its specification |
| [RationalEncodingBounds.lean](IdentityTesting/RationalEncodingBounds.lean) | Reduced rational arithmetic and precision encoding bounds |
| [RationalBisectionEncoding.lean](IdentityTesting/RationalBisectionEncoding.lean) | Dyadic grid invariant and actual query encoding bounds |
| [RationalOracleEvaluationEncoding.lean](IdentityTesting/RationalOracleEvaluationEncoding.lean) | Pole-safe coordinate, budget, and objective encoding bounds |
| [RationalOracleResourceBounds.lean](IdentityTesting/RationalOracleResourceBounds.lean) | Actual oracle parameters, trace, and output sizes |
| [OverlapMomentJointContinuity.lean](IdentityTesting/OverlapMomentJointContinuity.lean) | General ℓ¹ and target joint continuity |
| [CountableRelabeling.lean](IdentityTesting/CountableRelabeling.lean) | Countable permutation invariance of the actual functionals |
| [AllocationScaling.lean](IdentityTesting/AllocationScaling.lean) | Exact mass scaling of the countable allocation functional |
| [EqualBlockAllocation.lean](IdentityTesting/EqualBlockAllocation.lean) | Exact equal-mass block optimization |
| [UniformExamples.lean](IdentityTesting/UniformExamples.lean) | Uniform root formulas and statistical scales |
| [FlatTailExamples.lean](IdentityTesting/FlatTailExamples.lean) | Flat-tail roots, quantitative bounds, and statistical scales |
| [MinimumSampleComplexity.lean](IdentityTesting/MinimumSampleComplexity.lean) | Literal minimum-sample characterization |
| [GeneralRootContinuity.lean](IdentityTesting/GeneralRootContinuity.lean) | General summable-vector roots and convergence |
| [GeneralSignedMatrixHeavy.lean](IdentityTesting/GeneralSignedMatrixHeavy.lean) | General signed-mixture TV theorem and heavy-atom constants |
| [RationalComplexityEncoding.lean](IdentityTesting/RationalComplexityEncoding.lean) | Full algorithm output-size bound |
| [BinaryAdderMachine.lean](IdentityTesting/BinaryAdderMachine.lean) | Fixed-stack addition machine |
| [BinaryMultiplierBound.lean](IdentityTesting/BinaryMultiplierBound.lean) | Fixed-stack multiplication machine and cost bound |
| [BinaryRationalNormalization.lean](IdentityTesting/BinaryRationalNormalization.lean) | Actual fraction reduction, canonical outputs and cubic bit cost |
| [BinaryInterpreterOperandExecuteInstances.lean](IdentityTesting/BinaryInterpreterOperandExecuteInstances.lean) | Encoded reg/literal operands through all six operations, writeback and physical cleanup |
| [BinaryInterpreterDispatchRuns.lean](IdentityTesting/BinaryInterpreterDispatchRuns.lean) | Runtime instruction decoding and fixed-pool execution with exact source instruction semantics |
| [BinaryInterpreterCounterInputPrepared.lean](IdentityTesting/BinaryInterpreterCounterInputPrepared.lean) | Actual initialized precision/fuel register loads into binary counters |
| [OracleExactStopping.lean](IdentityTesting/OracleExactStopping.lean) | Aggregate elasticities, parameter ratios and exact stopping windows |
| [HeavyRestrictedSupport.lean](IdentityTesting/HeavyRestrictedSupport.lean) | Lower bounds for alternatives on the positive support |
| [EffectiveCountableCertificates.lean](IdentityTesting/EffectiveCountableCertificates.lean) | Executable countable intervals and endpoint convergence |
| [MeasurePrior.lean](IdentityTesting/MeasurePrior.lean) | Arbitrary measurable-prior testing inequality on Nat samples |
| [NormalizedTruncationLowerBound.lean](IdentityTesting/NormalizedTruncationLowerBound.lean) | Original normalized truncation and 100-batch transfer |
| [AllocationBoundaryDerivative.lean](IdentityTesting/AllocationBoundaryDerivative.lean) | Infinite right derivative at zero allocation |
| [HeavySharpErrors.lean](IdentityTesting/HeavySharpErrors.lean) | Explicit error constants for the general and heavy mean/collision tests |
| [GeneralAllocationPrior.lean](IdentityTesting/GeneralAllocationPrior.lean) | Prior constructed from the reference and radius, with strict separation and sample-mixture TV below 10^-4 |
| [MomentSharpErrors.lean](IdentityTesting/MomentSharpErrors.lean) | Explicit errors for the actual light-label mean and collision tests |
| [HeavyTiltManuscriptBounds.lean](IdentityTesting/HeavyTiltManuscriptBounds.lean) | Exact square-root sample bound for interior heavy tilts |
| [HeavyExteriorManuscriptBounds.lean](IdentityTesting/HeavyExteriorManuscriptBounds.lean) | Exact square-root sample bound for near-exterior tilts |
| [DyadicMassSeedPrior.lean](IdentityTesting/DyadicMassSeedPrior.lean) | Arbitrary-mass seeds, exact bin counts and zero-exterior cases |
| [BinarySignedMultiplierRuns.lean](IdentityTesting/BinarySignedMultiplierRuns.lean) | Actual signed multiplication and its quadratic primitive cost |
| [BinarySignedComparison.lean](IdentityTesting/BinarySignedComparison.lean) | Actual signed comparison, including noncanonical zero words |
| [RationalAlgorithmTraceCoordinateBounds.lean](IdentityTesting/RationalAlgorithmTraceCoordinateBounds.lean) | Coordinate program correctness, instruction counts and operand lengths |
| [AllocationExplicitDerivatives.lean](IdentityTesting/AllocationExplicitDerivatives.lean) | Explicit first and second derivatives, with strict concavity on the simplex |
| [AllocationExactTimeDecrease.lean](IdentityTesting/AllocationExactTimeDecrease.lean) | Exact time-decrease fraction and the constant-64 root window |
| [OracleBudgetFamily.lean](IdentityTesting/OracleBudgetFamily.lean) | Full real parameter family, elasticities and unique optimizer |
| [OracleManuscriptBounds.lean](IdentityTesting/OracleManuscriptBounds.lean) | Min/max bracket, pole separation and coordinate-error constants |
| [HeavyCompressionPrior.lean](IdentityTesting/HeavyCompressionPrior.lean) | Actual compression prior with the original feasible-budget constants |
| [FiniteCapCorollary.lean](IdentityTesting/FiniteCapCorollary.lean) | Finite cap-4/5 corollary and boundary comparison |
| [HeavyClosedCharacterization.lean](IdentityTesting/HeavyClosedCharacterization.lean) | Closed-domain heavy-atom minimum sample bounds |
| [Target.lean](IdentityTesting/Target.lean) | Allocation, moment, root, and scale definitions |
| [CountableModel.lean](IdentityTesting/CountableModel.lean) | Statistical model |
| [Verification.lean](Verification.lean) | Type, axiom, and execution audit |

The main exports are:

```lean
IdentityTesting.countable_characterization
IdentityTesting.countable_characterization_realScale
IdentityTesting.RationalComputation.rationalComplexityInterval
IdentityTesting.RationalComputation.rationalComplexityInterval_spec
```

Additional verified results include exact point-mass and small-overlap endpoint
sample counts, allocation-root rounding bounds, finite Hölder bounds, and the
explicit moment upper bound `(5 * 10^13 + 1) / W`.
