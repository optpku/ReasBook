/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 5.3.2 lies in the Chapter 5 self-concordant-barrier domain.

Sampled owner-style declarations in this domain:
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the chapter owner for standard
  self-concordance on an open convex domain;

Best owner abstraction:
* source-facing: `IsSelfConcordantBarrierOnWith dom ν F`;
* core/canonical ambient owner: `IsStandardSelfConcordantOn dom F`;
* bridge/view: the owner theorem `barrier_parameter_bound_of_mem`.

Primitive data:
* the standard self-concordance owner on `dom`;
* the pointwise barrier-parameter inequality.

Derived API:
* standard self-concordance as an inferable parent instance;
* the barrier-parameter inequality as a theorem-level owner consequence.

Source/core/bridge triage:
* source-facing: `IsSelfConcordantBarrierOnWith dom ν F`;
* core/canonical: `IsStandardSelfConcordantOn dom F`;
* bridge/view: `barrier_parameter_bound_of_mem`.

This file therefore keeps the source-facing barrier owner, but removes unused `Fact` wrappers
around derived consequences. The owner-level consequences are exposed directly as theorems instead
of parallel typeclass packaging. -/

/-- Definition 5.3.2: a standard self-concordant function `F` is a `ν`-self-concordant barrier
for `dom` when, for every `x ∈ dom`, every direction `u` satisfies the barrier inequality
`2 ⟪∇F(x), u⟫ - ⟪u, ∇²F(x)u⟫ ≤ ν`. The constant `ν` is the barrier parameter. -/
class IsSelfConcordantBarrierOnWith (dom : Set E) (ν : NNReal) (F : E → ℝ) : Prop where
  /-- A self-concordant barrier is standard self-concordant on its open convex domain. -/
  toIsStandardSelfConcordantOn : IsStandardSelfConcordantOn dom F
  /-- The barrier parameter bounds the gradient term by the Hessian quadratic form at each point
  of the domain. -/
  barrier_parameter_bound {x : E} (hx : x ∈ dom) (u : E) :
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)

attribute [instance] IsSelfConcordantBarrierOnWith.toIsStandardSelfConcordantOn

namespace IsSelfConcordantBarrierOnWith

/-- A self-concordant barrier instance canonically supplies the defining barrier-parameter
inequality at each point of its domain. -/
theorem barrier_parameter_bound_of_mem
    {dom : Set E} (ν : NNReal) {F : E → ℝ}
    [h : IsSelfConcordantBarrierOnWith dom ν F] {x : E} (hx : x ∈ dom) (u : E) :
    2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ) :=
  h.barrier_parameter_bound hx u

end IsSelfConcordantBarrierOnWith

end
