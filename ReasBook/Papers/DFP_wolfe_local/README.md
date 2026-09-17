# A Counterexample to Global Convergence of Classical DFP Under the Standard Strong Wolfe Conditions

- **Authors:** Benqi Liu, Zichen Wang, Zaiwen Wen, Liwei Zhang, and Yaxiang Yuan
- **Venue:** arXiv:2608.21708v1 (`math.OC`), 2026
- **Paper ID:** `DFP_wolfe_local`
- **Branch/toolchain:** `v4.32.0` / `leanprover/lean4:v4.32.0`
- **Paper:** [arXiv HTML](https://arxiv.org/html/2608.21708v1)
- **Source development:** [imathwy/DFP_wolfe_local](https://github.com/imathwy/DFP_wolfe_local)
- **Source snapshot:** [`75ba9f9aa9a190e23900503a5e9af6a377bddf6d`](https://github.com/imathwy/DFP_wolfe_local/commit/75ba9f9aa9a190e23900503a5e9af6a377bddf6d)

## Contributor

- Zichen Wang ([@imathwy](https://github.com/imathwy))

## Coverage

This paper formalization develops a uniformly convex, globally Hessian-bounded
counterexample for the classical inverse-form Davidon-Fletcher-Powell (DFP)
method. The public `DFPWolfe` surface covers:

- the planar and all-dimensional counterexamples;
- the standard weak-Wolfe and paper-range strong-Wolfe interfaces;
- the global and level-set formulations of the convergence predicate;
- the two-phase orbit, limiting-circle, separation, and bump-extension
  constructions;
- the identity-initialized operator and matrix `liminf` certificates;
- a global one-half Hölder Hessian bound for the same strong-Wolfe
  counterexample in every dimension at least two, preserved under identity
  initialization;
- failure of every Hölder exponent greater than one half on the counterexample's
  initial sublevel, including its higher-dimensional extensions;
- planar convergence under weak or strong Wolfe conditions from arbitrary
  initial positive-definite matrices, assuming local Hessian Lipschitz
  regularity near the initial sublevel, together with the `C³` corollary; and
- the general planar secant degeneration lemma, including the adjacent-step
  product bound, uniform matrix boundedness, and vanishing smallest eigenvalue.

This update includes the convergence and Hölder-regularity results from the
revised manuscript accompanying the source snapshot above; the arXiv link
identifies the original paper.

The development also includes the reusable `ReasLib` analysis, topology,
calculus, and DFP infrastructure needed by these statements. Numerical
experiments and manuscript presentation files are maintained in the source
development repository and are not part of this ReasBook Lean contribution.
The implementation roots remain under this project directory while dedicated
Lake libraries preserve their public `DFPWolfe` and `ReasLib` module names.

## Statistics

The counts below cover the project's tracked Lean source files, including the
`DFPWolfe` and `ReasLib` implementation roots, their aggregate roots, and the
`Paper.lean` wrapper.

- **Lean code:** 829 `.lean` files, 159,827 physical lines, 149,306 nonblank lines
- **Declarations:** 4,887 (theorem/lemma/example: 4,112; other: 775)
- **Declaration breakdown:** 3,728 theorems, 384 lemmas, 669 definitions,
  14 abbreviations, 87 structures, and 5 instances
- **Module split:** 205 `DFPWolfe` files and 621 `ReasLib` files
- **Proof completion:** 4,112 / 4,112 theorem and lemma declarations have no placeholders
- **Remaining placeholders:** `sorry`: 0; `admit`: 0
- **Project-defined axioms:** 0

These are source-level counts of declaration heads, including attributed, private, and
noncomputable declarations, after removing comments and string literals.
They do not count the imported mathlib environment. `Paper.lean` is the
validation root for the complete public surface.

## Main declarations

- `DFP.existsStrongWolfeCounterexample_of_parameterRange`
- `DFP.main_not_globalWeakWolfeConvergence_of_parameterRange`
- `DFP.main_not_levelSetGlobalWeakWolfeConvergence_of_parameterRange`
- `DFP.not_PaperRangeGlobalWeakWolfeConvergence`
- `DFP.not_PaperRangeLevelSetGlobalWeakWolfeConvergence`
- `DFP.existsMatrixIdentityLiminfStrongWolfe_of_parameterRange`
- `DFP.existsStrongWolfeCounterexampleHolderSharp_of_dimension_ge_two`
- `DFP.existsMatrixIdentityLiminfStrongWolfeHolder`
- `DFP.main_planarWeakWolfeConvergence`
- `DFP.main_planarStrongWolfeConvergence`
- `DFP.SecantIteration.planarDegeneration`

## Build and verification

From the `ReasBook` directory on branch `v4.32.0`:

```bash
lake lean Papers/DFP_wolfe_local/Paper.lean
lake env lean Papers/DFP_wolfe_local/Paper.lean
```

`lake lean` checks the root and prepares its imported modules. The direct
`lake env lean` command rechecks the root against those artifacts. Validation
is restricted to this paper; the repository-wide build, generated documentation,
and comparator are not included in these commands.

`Paper.lean` imports the complete public `DFPWolfe` surface. The project uses
the Apache License, Version 2.0, consistent with the source development
repository.
