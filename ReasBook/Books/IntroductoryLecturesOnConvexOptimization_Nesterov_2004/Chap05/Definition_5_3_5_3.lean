/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-
Definition 5.3.5.3 lies in the Chapter 5 self-concordant-barrier / stopped intermediate-Newton
domain.

Sampled owner declarations:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier, which canonically supplies `IsStandardSelfConcordantOn dom F`;
* `StoppedIntermediateSelfConcordantNewtonMethod` in `Definition_5_3_5_1`, the source-facing
  owner for the recursive intermediate Newton iterates together with the first-stop certificate;
* `DampedNewton.Method.IsSelfConcordant.succ_eq_nextPoint` in `Definition_5_2_1`, the canonical
  recursion theorem identifying each successor iterate with
  `selfConcordantNewtonNextPoint F 1 .intermediate ...`;
* `StoppedIntermediateSelfConcordantNewtonMethod.decrement` in `Definition_5_3_5_1`, the
  canonical owner-level Newton decrement API.

Best owner abstraction:
* source-facing: the stopped intermediate Newton method for minimizing a `ν`-self-concordant
  barrier;
* core/canonical: `StoppedIntermediateSelfConcordantNewtonMethod F y0 β`;
* bridge/view: the inferable parent instance `IsStandardSelfConcordantOn dom F` supplied by the
  barrier owner.

Primitive data:
* the stopped intermediate Newton method itself.

Derived API:
* the recursive update
  `yₖ₊₁ = selfConcordantNewtonNextPoint F 1 SelfConcordantNewtonVariant.intermediate yₖ ...`;
* the stopping index and decrement bounds.

Definition 5.3.5.3 therefore does not introduce a second owner carrying auxiliary path-following
data. It is the barrier specialization of the existing stopped intermediate Newton owner from
Definition 5.3.5.1.
-/

section

variable {dom : Set E} {F : E → ℝ} {ν : NNReal} [IsSelfConcordantBarrierOnWith dom ν F]
variable {y0 : dom} {β : ℝ}

/- Definition 5.3.5.3: for a `ν`-self-concordant barrier `F` on `dom`, the stopped intermediate
Newton method started at `y₀` with tolerance `β` is exactly the chapter owner
`StoppedIntermediateSelfConcordantNewtonMethod F y0 β`. The barrier hypothesis contributes only
the inferable standard self-concordance needed by that owner. -/
#check (StoppedIntermediateSelfConcordantNewtonMethod F y0 β)

end

end
