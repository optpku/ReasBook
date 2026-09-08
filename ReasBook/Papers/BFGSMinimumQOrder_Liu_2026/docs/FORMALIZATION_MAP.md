# Formalization map

This index connects the manuscript *The Minimum Q-Order of BFGS with Exact Line
Search Is One* to the stable Lean modules. The `Book/` files are concise
paper-facing interfaces; the substantive reusable proofs live under
`ReasLib/`.

| Manuscript item | Paper-facing module | Main implementation |
| --- | --- | --- |
| Q-order definitions | `Book.Definition_2_1` | `ReasLib.Analysis.Convergence.QOrder` |
| Exact-line-search quasi-Newton algorithm | `Book.Algorithm_2_1` | `Book.Algorithm_2_1_QuasiNewton` |
| Exact-line-search convergence bridge | `Book.Proposition_2_2` | `ReasLib.Optimization.LineSearchConvergence` |
| Identity-initialized BFGS realization | `Book.Lemma_2_3` | `ReasLib.Optimization.BFGS.PlanarRealization` |
| BFGS trajectory interface | `Book.Lemma_2_3_Trajectory` | `ReasLib.Optimization.BFGS.Trajectory` |
| Planar gradient recurrence | `Book.Lemma_3_1` | `ReasLib.Optimization.BFGS.PlanarGradient.Recurrence` |
| Alternating-scale construction | `Book.Lemma_3_2` | `ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.Construction` |
| Separation and step estimates | `Book.Derivation_3_1`, `Book.Derivation_3_2` | `ReasLib.Optimization.BFGS.PlanarGradient.SeparationBounds`, `ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.StepBounds` |
| Q-superlinear, order-one behavior | `Book.Remark_3_3` | `ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.Convergence` |
| Smooth localized interpolation | `Book.Lemma_4_1` | `ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.Interpolation` |
| Quadratic-tail and Hessian control | `Book.Lemma_4_2`, `Book.Lemma_4_2_Hessian` | `ReasLib.Analysis.QuadraticTail`, `ReasLib.Analysis.Hessian` |
| Scaling and localization | `Book.Lemma_4_3` | `ReasLib.Optimization.BFGS.Scaling` |
| Main minimum-Q-order theorem | `Book.Theorem_1_1` | `ReasLib.Optimization.BFGS.MinimumQOrder` |
| Convex Broyden extension | `Book.Corollary_5_1` | `ReasLib.Optimization.BFGS.MinimumQOrder.ConvexBroyden` |

## Principal declarations

- `BFGS.IsOrderOneExample` packages the objective, trajectory, localization,
  Hessian, nontermination, and rate properties of the constructed example.
- `BFGS.exists_orderOneExample` proves existence in every finite dimension
  `n ≥ 2`, for every positive perturbation tolerance and localization radius.
- `BFGS.IsTrajectory.one_le_order` supplies the universal lower bound.
- `BFGS.IsOrderOneExample.existsBroydenTrajectory` and
  `BFGS.IsOrderOneExample.broydenPoints_eq` implement Dixon-type trajectory
  equivalence for the convex Broyden class.
- `BFGS.IsOrderOneExample.broydenOrder_eq_one` exports the rate conclusion for
  every equally initialized convex Broyden trajectory.

## Public roots

- Import `BFGSMinimumQOrder` for the complete BFGS paper formalization.
- Import `Book` for all paper-facing modules.
- Import a specific `ReasLib` module when developing reusable infrastructure.
- Import `DFPWolfe` for the independently packaged DFP Wolfe counterexample.
