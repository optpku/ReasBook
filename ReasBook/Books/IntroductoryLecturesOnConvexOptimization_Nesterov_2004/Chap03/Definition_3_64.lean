/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [PseudoMetricSpace E] [AddCommMonoid E] [Module ℝ E]
variable {Q : Set E} {M : NNReal} {f : E → ℝ}

/- Definition 3.64 lies in the constrained convex optimization domain.

Sampled owner-style declarations:
- `linftyLipschitzClass` in `Chap01/Definition_1_3_4`, the Chapter 1 source-facing fixed-parameter
  Lipschitz class on functions;
- `S0On` and the notation `𝒮^0_μ(Q)` in `Chap03/Definition_3_47`, the nearby chapter pattern for
  a fixed-parameter function class with small projection lemmas;
- mathlib `ConvexOn`, the canonical owner predicate for convexity on a feasible set;
- mathlib `LipschitzOnWith`, the canonical owner predicate for a fixed Lipschitz bound on a
  feasible set.

Best owner abstraction:
- source-facing: the textbook fixed-parameter function class `𝓕_M^{0,0}(Q)`, written on Lean
  theorem surfaces as `𝓕⁰⁰[M](Q)`;
- core/canonical: `ConvexOn ℝ Q f` and `LipschitzOnWith M f Q`;
- bridge/view: the membership/accessor lemmas exposing those two canonical predicates directly.

Primitive data:
- a feasible set `Q`;
- a Lipschitz parameter `M`;
- an objective `f : E → ℝ`.

Derived API:
- source-facing membership `f ∈ 𝓕⁰⁰[M](Q)`;
- the canonical convexity and Lipschitz owner predicates recovered from membership;
- the constructor theorem from the canonical pair back to the source-facing class.

Source/core/bridge triage:
- source-facing: `f ∈ 𝓕⁰⁰[M](Q)`;
- core/canonical: `ConvexOn ℝ Q f` and `LipschitzOnWith M f Q`;
- bridge/view: `mem_F00_iff`, `ConvexLipschitzOn.convexOn`,
  `ConvexLipschitzOn.lipschitzOnWith`, and `ConvexLipschitzOn.mem_F00`.

This refinement removes the bundled minimization-problem wrapper and restores the chapter's
source-facing fixed-parameter function class. Nonemptiness, closedness, and any chosen problem
packaging belong on downstream problem statements, not in Definition 3.64 itself. -/

/-- Definition 3.64: a function belongs to the source-facing class `𝓕_M^{0,0}(Q)`, written in
Lean as `𝓕⁰⁰[M](Q)`, when it is
convex on `Q` and `M`-Lipschitz on `Q`. -/
def ConvexLipschitzOn (Q : Set E) (M : NNReal) (f : E → ℝ) : Prop :=
  ConvexOn ℝ Q f ∧ LipschitzOnWith M f Q

scoped[ConvexLipschitz] notation "𝓕⁰⁰[" M "](" Q ")" =>
  setOf (ConvexLipschitzOn Q M)

open scoped ConvexLipschitz

/-- Membership in `𝓕⁰⁰[M](Q)` is exactly the canonical pair consisting of convexity on `Q`
and an `M`-Lipschitz bound on `Q`. -/
@[simp] theorem mem_F00_iff :
    f ∈ 𝓕⁰⁰[M](Q) ↔ ConvexLipschitzOn Q M f :=
  Iff.rfl

namespace ConvexLipschitzOn

/-- Membership in `𝓕⁰⁰[M](Q)` includes the canonical convexity owner on `Q`. -/
theorem convexOn (hf : f ∈ 𝓕⁰⁰[M](Q)) :
    ConvexOn ℝ Q f :=
  hf.1

/-- Membership in `𝓕⁰⁰[M](Q)` includes the canonical fixed-parameter Lipschitz owner on `Q`.
-/
theorem lipschitzOnWith (hf : f ∈ 𝓕⁰⁰[M](Q)) :
    LipschitzOnWith M f Q :=
  hf.2

/-- Membership in `𝓕⁰⁰[M](Q)` implies that the feasible set `Q` is convex. -/
theorem convex (hf : f ∈ 𝓕⁰⁰[M](Q)) :
    Convex ℝ Q :=
  (convexOn hf).1

/-- The canonical convexity and Lipschitz owners on `Q` give source-facing membership in
`𝓕⁰⁰[M](Q)`. -/
theorem mem_F00 (hconv : ConvexOn ℝ Q f) (hlip : LipschitzOnWith M f Q) :
    f ∈ 𝓕⁰⁰[M](Q) :=
  ⟨hconv, hlip⟩

end ConvexLipschitzOn

end
