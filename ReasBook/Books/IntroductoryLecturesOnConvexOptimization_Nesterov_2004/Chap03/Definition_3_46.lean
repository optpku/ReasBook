/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_45

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

namespace ApproximateLagrangeMultiplierSwitchingMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E m}

open scoped ApproximateLagrangeMultiplierSwitchingNotation

local notation "φ" => problem.toLagrangianProblem.dualFunction

/- Definition 3.46 lies in the chapter's approximate-multiplier primal-dual gap domain.

Sampled owner-style declarations:
- `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintIndices`,
  `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintCount`,
  `ApproximateLagrangeMultiplierSwitchingMethod.inverseSubgradientNormSum`, and
  `ApproximateLagrangeMultiplierSwitchingMethod.approximateDualMultiplier` in `Definition_3_45`,
  the source-facing owners of `A₀(t)`, `N(t)`, `S_t`, and `λ_t`;
- `ProjectedMultipleConstraintFirstOrderProblem.toLagrangianProblem` in `Algorithm_3_4`, the
  canonical bridge from the switching-method problem to the Chapter 1 Lagrangian owner on
  `Q = problem.feasibleSet`;
- `LagrangianProblem.dualFunction` in `Chap01/Definition_1_10_2`, the owner dual value `φ`;
- mathlib `Finset.centerMass`, the canonical normalized finite-average owner used for the primal
  average itself.

Best owner abstraction:
- a run `method : ApproximateLagrangeMultiplierSwitchingMethod problem`, viewed through
  Definition 3.45 for the source data `A₀(t)`, `N(t)`, `S_t`, and `λ_t`, through
  `Finset.centerMass` on `A₀(t)` itself for the normalized primal average, and through the
  feasible-set Lagrangian owner `problem.toLagrangianProblem` for the dual term.

Primitive data:
- the switching-method run `method`;
- the stage index `t`.

Derived API:
- the inactive index set `A₀(t)`;
- the source count `N(t) = |A₀(t)|`;
- the owner reciprocal weights, normalization sum, and multiplier from Definition 3.45;
- the source weighted primal term, obtained canonically as the `centerMass` over `A₀(t)` with
  those owner weights;
- the dual value of the corresponding approximate multiplier.

Source/core/bridge triage:
- source-facing: `primalDualGapQuantity`;
- core/canonical: the run `method` together with the Definition 3.45 owner data and the
  Lagrangian owner `problem.toLagrangianProblem`, plus `Finset.centerMass` for the normalized
  finite average in the primal term;
- bridge/view: the `Finset.centerMass` realization of the weighted primal term and the Chapter 1
  dual-value specialization at the source-facing multiplier `λ_t`.

Unlike the generic Chapter 3 weighted-gap owners, this source item is tied specifically to the
Algorithm 3.4 multiplier `λ_t` from Definition 3.45 and to the Chapter 1 extended-real dual
function. Its primal term is still expressed canonically using `Finset.centerMass`, and the
full denominator regime is inherited directly from Definition 3.45's source-facing owners rather
than through a parallel local copy. -/

/-- Definition 3.46: for the feasible-set Lagrangian bridge attached to a run of Algorithm 3.4,
the primal--dual gap quantity `δ[method](t; hdenom)` is the difference between the owner weighted
primal average over `A₀[method](t)` and the canonical dual value at the approximate multiplier
`λ[method](t; hdenom)`. Under the full denominator regime `hdenom` from Definition 3.45, this is
the textbook quantity
`S_t⁻¹ ∑_{k ∈ A₀[method](t)} f(x_k) / ‖g(x_k)‖ - φ(λ_t)`. The value is taken in `EReal` because
`LagrangianProblem.dualFunction` is extended-real-valued. -/
def primalDualGapQuantity
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t) : EReal :=
  (((A₀[method](t)).centerMass
      (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
      (fun k ↦ problem.objective (method k)) : ℝ) : EReal) -
    φ (λ[method](t; hdenom))

/- Source-facing Lean notation for the textbook primal--dual gap quantity `δ_t`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "δ[" method:arg "](" t:arg "; " hdenom:arg ")" =>
  primalDualGapQuantity method t hdenom

end ApproximateLagrangeMultiplierSwitchingNotation

end ApproximateLagrangeMultiplierSwitchingMethod
