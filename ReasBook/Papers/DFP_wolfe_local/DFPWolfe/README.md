# Paper correspondence

The numbering below follows the shared theorem counter in `main-new.tex`:
Theorems 1 and 3, Corollary 2, Proposition 4, and Lemmas 5–11.
The LaTeX labels identify statements independently of their printed numbers.
Import `DFPWolfe` (or `DFPWolfe.Paper`) to access all the results below.

Each numbered paper statement has its own `.lean` file directly in this
directory. The first column links to that file; the last column links to the
proof sources. Each navigation file records the paper label and mathematical
statement, then uses `#check` to locate its already-proved Lean declarations.
These checks are a navigation aid, not additional proofs or theorem aliases.

| Paper result and navigation file | LaTeX label | Proof source and principal declaration |
| --- | --- | --- |
| [Theorem 1: strong Wolfe counterexample with a one-half Hölder Hessian](Theorem_1_StrongWolfeCounterexample.lean) | `thm:main` | [HolderSharpness](../ReasLib/Optimization/DFP/WolfeCounterexample/HolderSharpness.lean): `DFP.existsStrongWolfeCounterexampleHolderSharp_of_dimension_ge_two` |
| [Corollary 2: identity initialization](Corollary_2_IdentityInitialization.lean) | `cor:identity-initialization` | [Holder](../ReasLib/Optimization/DFP/WolfeCounterexample/Holder.lean): `DFP.existsMatrixIdentityLiminfStrongWolfeHolder` |
| [Theorem 3: planar convergence under a locally Lipschitz Hessian](Theorem_3_PlanarConvergence.lean) | `thm:planar-convergence` | [Main](Main.lean): `DFP.main_planarWeakWolfeConvergence` and `DFP.main_planarStrongWolfeConvergence` |
| [Proposition 4: exact one-step map](Proposition_4_OneStepMap.lean) | `prop:one-step` | [AbstractSecantStep](../ReasLib/Optimization/DFP/AbstractSecantStep.lean): `DFP.AbstractSecantStep.nextGradient_formula`; [ExactUpdate](../ReasLib/Optimization/DFP/AbstractSecantStep/ExactUpdate.lean): `nextInverseHessian_formula` and `nextInverseHessian_tau_independent` |
| [Lemma 5: local invariant graph](Lemma_5_LocalInvariantGraph.lean) | `lem:graph-transform` | [LocalInvariantGraph](../ReasLib/Analysis/Calculus/LocalInvariantGraph.lean): `LocalInvariantGraph.existsOfComplexSpectralRadiusLtOne` |
| [Lemma 6: invariant center manifold](Lemma_6_CenterManifold.lean) | `lem:center-manifold` | [SlowCurve](../ReasLib/Optimization/DFP/TwoPhaseControls/SlowCurve.lean): `DFP.TwoLeg.exists_localForwardInvariantSlowCurve`; [StateMap](../ReasLib/Optimization/DFP/TwoPhaseControls/StateMap.lean) and [Linearization](../ReasLib/Optimization/DFP/TwoPhaseControls/StateMap/Linearization.lean) for analyticity and eigenvalues |
| [Lemma 7: two-step expansions](Lemma_7_TwoStepExpansions.lean) | `lem:two-step-expansions` | [AmplitudeJet](../ReasLib/Optimization/DFP/TwoPhaseControls/AmplitudeJet.lean), [FrameAngleDrift](../ReasLib/Optimization/DFP/TwoPhaseOrbit/FrameAngleDrift.lean), [CenterDisplacement](../ReasLib/Optimization/DFP/TwoPhaseOrbit/CenterDisplacement.lean), and [EndpointAngleRemainder](../ReasLib/Optimization/DFP/TwoPhaseOrbit/EndpointAngleRemainder.lean); components listed below |
| [Lemma 8: scalar asymptotics and limiting circle](Lemma_8_ScalarAsymptotics.lean) | `lem:scalar-asymptotics` | [ScalarAsymptotics](../ReasLib/Optimization/DFP/TwoPhaseOrbit/ScalarAsymptotics.lean): `DFP.TwoPhaseOrbit.slowCurveScalarAsymptotics` |
| [Lemma 9: uniform separation](Lemma_9_UniformSeparation.lean) | `lem:separation` | [EndpointSeparation](../ReasLib/Optimization/DFP/TwoPhaseOrbit/EndpointSeparation.lean): `DFP.TwoPhaseOrbit.slowCurveUniformEndpointSeparation` |
| [Lemma 10: disjoint interpolation](Lemma_10_DisjointInterpolation.lean) | `lem:disjoint-interpolation` | [SmoothExtension](../ReasLib/Optimization/DFP/TwoPhaseOrbit/Interpolation/SmoothExtension.lean), [HessianBound](../ReasLib/Optimization/DFP/TwoPhaseOrbit/Interpolation/HessianBound.lean), [Interpolation](../ReasLib/Optimization/DFP/TwoPhaseOrbit/EndpointBump/Interpolation.lean), and [Hölder regularity](../ReasLib/Optimization/DFP/PlanarConvergence.lean); components listed below |
| [Lemma 11: planar secant degeneration](Lemma_11_PlanarSecantDegeneration.lean) | `lem:planar-degeneration` | [SecantDegeneration](../ReasLib/Optimization/DFP/SecantDegeneration.lean): `DFP.SecantIteration.planarDegeneration` |

Proposition 4's navigation file also checks `preconditionedEnergy_pos` and
`secantImageEnergy_pos` in `DFP.AbstractSecantStep`, for positivity of its two
denominators. Lemma 6's file includes the recovered-map agreement, analytic
extension, derivative, and eigenvalues `1`, `-1 / 9`, and `0`, followed by the
invariant graph theorem containing both shape jets and the scale recurrence.

Lemma 7's `O(ε⁶)` amplitude remainder is
`DFP.TwoLeg.slowCurveAmplitudeDrift` in
[AmplitudeJet](../ReasLib/Optimization/DFP/TwoPhaseControls/AmplitudeJet.lean).
Its other components are `DFP.TwoPhaseOrbit.slowCurveFrameRotation`,
`slowCurveFullCenterDrift`, `slowCurveHalfCenterDisplacement`, and
`slowCurveEndpointAngleRemainderModulus` (all in the latter namespace).
These retain the amplitude, rotation, full- and
half-cycle center, and within-cycle angle estimates separately.

Lemma 10 combines `contDiff_two_slowCurveBumpCorrection`,
`slowCurveBumpCorrection_eqOn_zero`,
`slowCurveBumpCorrectionHessianBound`,
`DFP.TwoPhaseOrbit.bumpCorrection_endpoint`,
`DFP.TwoPhaseOrbit.bumpCorrection_gradient_endpoint`, and
`DFP.PlanarConvergence.bumpCorrectionHessianHolder`.
The statements expose the construction's small-scale and invariant-curve
hypotheses; the counterexample theorem assembles those hypotheses.

Theorem 1's exported statement also includes the proved failure of higher
Hölder exponents on the initial sublevel. Lemma 5 uses `C^ν` regularity,
which is weaker than the paper's `C^(ν+1)` assumption. Lemma 8 includes
equality of the complete endpoint cluster set with the limiting circle.
Theorem 3 represents finite termination by constant continuation after the
first stationary point. Lemma 11 uses the secant equation and positive
definiteness, without assuming the DFP matrix update. Its zero-based Lean
coefficient `lam k` corresponds to the paper's `λₖ₊₁`.

## Source organization

`Main.lean` contains the public convergence and nonconvergence interfaces.
`Paper.lean` imports all eleven numbered navigation files and preserves the
supporting orbit and interpolation exports. The proofs themselves live in
`ReasLib`, grouped by their mathematical objects rather than obsolete paper
numbers. In particular, `TwoPhaseOrbit/Interpolation/` contains the isolation,
support, jet, smoothness, and Hessian estimates used for Lemma 10.

The old `Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample`
directory and the obsolete numbered wrapper directory remain removed.
The eleven current paper navigation files are intentionally retained; generic
infrastructure checks are not. `ReasLib` imports canonical proof modules directly
and contains no navigation `#check` or audit `#print` commands.
Source paths have changed, so downstream docs,
theorem graphs, and manuscript GitHub links must be regenerated when this
snapshot is published to ReasBook.
