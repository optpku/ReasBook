/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-
Definition 5.3.5.1 lies in the Chapter 5 self-concordant Newton-iteration domain.

Sampled owner declarations:
* `IsStandardSelfConcordantOn` in `Definition_5_1_1`, the chapter owner for the standard
  self-concordant regime `M_f = 1`;
* `DampedNewton.Method.IsSelfConcordant` in `Definition_5_2_1`, the Chapter 5 refinement of the
  recursive intermediate Newton iterates;
* `NewtonDecrement.ofDetNeZero` in `Definition_5_0_24`, the canonical Chapter 5 owner for the
  Newton decrement at a domain point with nondegenerate Hessian;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the barrier-specific downstream bridge
  showing how the analytic-center application supplies the standard self-concordant owner used
  here.

Best owner abstraction:
* `source-facing`: a stopped intermediate self-concordant Newton method, namely the recursive
  Newton owner together with the first-stop certificate for the tolerance `β`;
* `core/canonical`: `DampedNewton.Method.IsSelfConcordant dom 1 intermediate` together with its
  owner-level decrement API;
* `bridge/view`: the passage from a `ν`-self-concordant barrier to
  `IsStandardSelfConcordantOn dom F`, and the derived method-level decrement API.

Primitive data:
* the underlying Chapter 1 damped Newton method;
* its Chapter 5 intermediate self-concordant refinement;
* the stopping index and the first-stop inequalities.

Derived API:
* the iterate sequence, domain membership, Hessian nondegeneracy, and update rule, inherited
  from `DampedNewton.Method` and its Chapter 5 refinement;
* the Newton decrement at step `k`, derived canonically from
  `DampedNewton.Method.IsSelfConcordant.decrement`.

This file therefore keeps the source-facing stopped method at the Chapter 5 Newton level: it
extends the Chapter 1 damped Newton owner directly, records the Chapter 5 intermediate
self-concordant property as a separate field, and leaves the analytic-center/barrier hypotheses to
the downstream bridge files where they actually enter. -/

/-- Definition 5.3.5.1: a stopped intermediate self-concordant Newton method on a standard
self-concordant function `F` on `dom`, started at `y₀ ∈ dom` with stopping threshold `β`,
consists of the underlying intermediate self-concordant Newton iteration
`yₖ₊₁ = yₖ - [∇²F(yₖ)]⁻¹ ∇F(yₖ) / (1 + ξₖ)` with
`ξₖ = λₖ^2 / (1 + λₖ)` and `λₖ = ‖∇ F(yₖ)‖*_(yₖ)`, together with a stopping index where the
Newton decrement first drops below the tolerance `β`. In the analytic-center application, the
extra barrier data belongs in downstream assumptions rather than in this owner. -/
structure StoppedIntermediateSelfConcordantNewtonMethod
    {dom : Set E} (F : E → ℝ) [IsStandardSelfConcordantOn dom F] (y0 : dom) (β : ℝ)
    extends DampedNewton.Method F (y0 : E) where
  /-- The underlying Chapter 1 method is the intermediate self-concordant Newton method. -/
  isSelfConcordant :
    toMethod.IsSelfConcordant dom 1 SelfConcordantNewtonVariant.intermediate
  /-- The stopping index at which the Newton decrement meets the tolerance `β`. -/
  stopIndex : ℕ
  /-- Before the stopping index, the Newton decrement remains strictly above `β`. -/
  continue_condition :
    ∀ ⦃k : ℕ⦄, k < stopIndex → β < isSelfConcordant.decrement k
  /-- At the stopping index, the Newton decrement is at most `β`. -/
  stop_condition : isSelfConcordant.decrement stopIndex ≤ β

namespace StoppedIntermediateSelfConcordantNewtonMethod

variable {dom : Set E} {F : E → ℝ} [IsStandardSelfConcordantOn dom F] {y0 : dom} {β : ℝ}

/-- The Newton decrement of the stopped intermediate method at step `k`. -/
abbrev decrement (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 β) (k : ℕ) : ℝ :=
  method.isSelfConcordant.decrement k

/-- Before the stopping index, the stepwise Newton decrement stays above `β`. -/
theorem beta_lt_decrement_of_lt_stopIndex
    (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 β)
    {k : ℕ} (hk : k < method.stopIndex) :
    β < method.decrement k :=
  method.continue_condition hk

/-- At the stopping index, the stepwise Newton decrement is at most `β`. -/
theorem decrement_stopIndex_le
    (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 β) :
    method.decrement method.stopIndex ≤ β :=
  method.stop_condition

end StoppedIntermediateSelfConcordantNewtonMethod
