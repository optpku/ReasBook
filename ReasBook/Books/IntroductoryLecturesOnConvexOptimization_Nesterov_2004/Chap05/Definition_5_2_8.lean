/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Definition 5.2.8 lies in the strongly convex smooth minimization domain.

Sampled owner-style declarations:
* `StrongConvexOn` from mathlib, the canonical owner for whole-space strong convexity;
* `HasLipschitzContinuousHessian` from `Chap04/Definition_4_2_7`, written on theorem surfaces as
  `f ∈ C22[L₃]`, the project owner for global Hessian-Lipschitz regularity;
* `HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le`, the canonical second-derivative estimate
  on normed spaces;
* `HasLipschitzContinuousHessian.norm_sub_le`, the Hilbert-space Hessian estimate derived from
  that owner;
* `IsStrongConvexSmoothObjective` with source-facing notation `f ∈ 𝓢[μ, L]¹¹` from
  `Chap02/Definition_2_17`, the chapter owner pattern for bundled optimization classes.

Source/core/bridge triage:
* source-facing: the bundled strongly convex `C³` Hessian-Lipschitz regime
  `f ∈ 𝓢[σ₂, L₃]²²`;
* core/canonical: `StrongConvexOn Set.univ σ₂ f` and `f ∈ C22[L₃]`;
* bridge/view: the companion projection to `f ∈ C22[L₃]` and the textbook Hessian-difference
  inequality.

Primitive data:
* the strong-convexity parameter `σ₂`;
* the Hessian-Lipschitz constant `L₃`;
* positivity of `σ₂`;
* whole-space strong convexity of `f`;
* the canonical smoothness owner `f ∈ C22[L₃]`;
* the extra `C³` regularity needed by the source regime.

Derived API:
* the inherited `HasLipschitzContinuousHessian L₃ f` instance;
* the source-facing theorem `objective_mem : f ∈ C22[L₃]`;
* on real Hilbert spaces, the textbook estimate `‖hessian f x - hessian f y‖ ≤ L₃ ‖x - y‖`.

This file keeps the source-facing bundled regime, but now places its primitive owner data on the
same normed-space layer as `HasLipschitzContinuousHessian`. It no longer stores a duplicate raw
field `LipschitzWith L₃ (fun x ↦ fderiv ℝ (∇ f) x)`: that data is owned upstream by
`HasLipschitzContinuousHessian`. The Hilbert-specific textbook Hessian estimate remains a derived
bridge theorem. Positivity, whole-space strong convexity, and `C³` regularity stay available
through the class projections rather than a global bundled `Fact` instance. -/

/-- Definition 5.2.8: a real-valued objective on a real normed space is in the
strongly convex `C³` minimization regime with parameters `σ₂` and `L₃` when `σ₂ > 0`, the
objective is `σ₂`-strongly convex on all of `E`, it belongs to the chapter smoothness class
`C22[L₃]`, and it is three-times continuously differentiable. -/
class IsStrongConvexC22C3Objective
    (σ2 : ℝ) (L3 : NNReal) (f : E → ℝ) : Prop
    extends HasLipschitzContinuousHessian L3 f where
  /-- The strong-convexity parameter `σ₂` is positive. -/
  sigma_pos : 0 < σ2
  /-- The objective is `σ₂`-strongly convex on the whole space. -/
  strongConvex : StrongConvexOn Set.univ σ2 f
  /-- The objective is three-times continuously differentiable. -/
  contDiffThree : ContDiff ℝ 3 f

scoped[StrongConvexC22] notation "𝓢[" σ2 ", " L3 "]²²" =>
  setOf (IsStrongConvexC22C3Objective σ2 L3)

open scoped StrongConvexC22

/-- The whole-space notation `𝓢[σ₂, L₃]²²` is the source-facing set view of the owner predicate
`IsStrongConvexC22C3Objective σ₂ L₃`. -/
theorem mem_S22_iff {σ2 : ℝ} {L3 : NNReal} {f : E → ℝ} :
    f ∈ 𝓢[σ2, L3]²² ↔ IsStrongConvexC22C3Objective σ2 L3 f :=
  Iff.rfl

/-- The canonical self-concordance constant induced by strong convexity parameter `σ₂` and
Hessian-Lipschitz constant `L₃`. This is the owner-level `M_f = L₃ / (2 σ₂^(3 / 2))` used in
Example 5.1.6 and the strongly convex Chapter 5 quadratic-region estimates. -/
def strongConvexSelfConcordanceConstant (σ2 : ℝ) (L3 : NNReal) : NNReal :=
  Real.toNNReal ((L3 : ℝ) / (2 * σ2 * Real.sqrt σ2))

/-- Under `0 < σ₂`, the owner `strongConvexSelfConcordanceConstant σ₂ L₃` has the expected real
value `L₃ / (2 σ₂^(3 / 2))`. -/
theorem coe_strongConvexSelfConcordanceConstant
    {σ2 : ℝ} {L3 : NNReal} (hσ2 : 0 < σ2) :
    (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) =
      (L3 : ℝ) / (2 * σ2 * Real.sqrt σ2) := by
  have hnonneg : 0 ≤ (L3 : ℝ) / (2 * σ2 * Real.sqrt σ2) := by
    positivity
  unfold strongConvexSelfConcordanceConstant Real.toNNReal
  change max ((L3 : ℝ) / (2 * σ2 * Real.sqrt σ2)) 0 =
    (L3 : ℝ) / (2 * σ2 * Real.sqrt σ2)
  exact max_eq_left hnonneg

/-- The doubled real value of the canonical strong-convexity-induced self-concordance constant is
`L₃ / (σ₂ √σ₂)`. This is the coefficient appearing in the operator inequality of
Example 5.1.6. -/
theorem two_mul_coe_strongConvexSelfConcordanceConstant
    {σ2 : ℝ} {L3 : NNReal} (hσ2 : 0 < σ2) :
    2 * (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) =
      (L3 : ℝ) / (σ2 * Real.sqrt σ2) := by
  rw [coe_strongConvexSelfConcordanceConstant hσ2]
  have hsqrt : Real.sqrt σ2 ≠ 0 := Real.sqrt_ne_zero'.2 hσ2
  field_simp [hσ2.ne', hsqrt]

namespace IsStrongConvexC22C3Objective

/-- A strongly convex `C³` objective in Definition 5.2.8 belongs to the canonical owner class
`C22[L₃]`. -/
theorem objective_mem {σ2 : ℝ} {L3 : NNReal} {f : E → ℝ}
    (hf : f ∈ 𝓢[σ2, L3]²²) :
    f ∈ C22[L3] :=
  hf.toHasLipschitzContinuousHessian

section Hilbert

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

-- Proof sketch: apply the `LipschitzWith` field of
-- `HasLipschitzContinuousHessian`, obtained from `hf.objective_mem`, to the pair `x, y`.
/-- On a real Hilbert space, the Hessian-Lipschitz field of `f ∈ 𝓢[σ₂, L₃]²²` is the textbook
estimate `‖∇² f(x) - ∇² f(y)‖ ≤ L₃ ‖x - y‖`. -/
theorem hessian_norm_sub_le
    {σ2 : ℝ} {L3 : NNReal} {f : X → ℝ}
    (hf : f ∈ 𝓢[σ2, L3]²²) (x y : X) :
    ‖hessian f x - hessian f y‖ ≤ (L3 : ℝ) * ‖x - y‖ :=
  HasLipschitzContinuousHessian.norm_sub_le
    (IsStrongConvexC22C3Objective.objective_mem hf) x y

end Hilbert

end IsStrongConvexC22C3Objective
