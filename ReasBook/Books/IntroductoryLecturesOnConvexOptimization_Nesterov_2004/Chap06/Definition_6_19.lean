/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Definition 6.19 lies in the chapter's primal-form smoothing / regularized-supremum domain.

Sampled owner-style declarations:
- `smoothedPrimalObjectiveMaximand` in `Definition_6_30`, the Chapter 6 owner of the regularized
  maximand `u ↦ ⟪A x, u⟫ - \hat φ(u) - μ d(u)`;
- `smoothedPrimalObjective` in `Definition_6_30`, the Chapter 6 owner of the corresponding
  supremum objective;
- `Definition_6_7`, which treats a source-facing smoothing definition as a direct specialization
  of `smoothedPrimalObjective` rather than introducing a parallel owner;
- `continuousLocationSmoothApproximation` in `Definition_6_16`, another thin source-facing
  specialization of the same owner.

Best owner abstraction:
- source-facing: the primal-form smoothed objective attached to the special dual penalty
  `u ↦ ⟪b, u⟫ + ⟪Bu, u⟫`;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: the specialization `hatf = 0` and `hatφ u = b u + B u u`.

Primitive data:
- `B : E →L[ℝ] StrongDual ℝ E`;
- `Q : Set E`;
- `b : StrongDual ℝ E`;
- `d : E → ℝ`;
- `μ : ℝ`.

Derived API:
- the source-facing specialization `primalFormSmoothedObjective`;
- its owner-level expansion through `smoothedPrimalObjective_apply`;
- the explicit textbook supremum formula for the specialized maximand.

Source/core/bridge triage:
- source-facing: `primalFormSmoothedObjective`;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: the companion theorems below expanding the specialization to the displayed formula.

The previous file introduced separate public owners for the linear term, the quadratic-linear
penalty, the maximand, and the final smoothed objective. Only the last object is source-facing
mathematics here; the others are just pieces of the chapter owner `smoothedPrimalObjective`.
This refinement deletes those duplicate wheels, keeps the source-facing specialization, and
derives the displayed formula directly from the canonical owner.
-/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 6.19: in the primal-form smoothing specialization with `E₁ = E₂ = E`,
`Q₁ = Q₂ = Q`, `d₁ = d₂ = d`, and `A = B`, the smoothed subproblem `f_μ` is the Chapter 6
regularized-supremum owner specialized to the dual penalty `\hat φ(u) = ⟪b, u⟫ + ⟪Bu, u⟫`. -/
abbrev primalFormSmoothedObjective
    (B : E →L[ℝ] StrongDual ℝ E) (Q : Set E) (b : StrongDual ℝ E) (d : E → ℝ) (μ : ℝ) :
    E → ℝ :=
  smoothedPrimalObjective B Q 0 (fun u ↦ b u + B u u) d μ

/-- Expanding `primalFormSmoothedObjective` through the chapter owner gives the supremum of the
specialized regularized maximand over `Q`. -/
@[simp] theorem primalFormSmoothedObjective_def
    (B : E →L[ℝ] StrongDual ℝ E) (Q : Set E) (b : StrongDual ℝ E) (d : E → ℝ) (μ : ℝ) (x : E) :
    primalFormSmoothedObjective B Q b d μ x =
      sSup ((fun u : E ↦ B x u - (b u + B u u) - μ * d u) '' Q) := by
  simpa [primalFormSmoothedObjective, smoothedPrimalObjectiveMaximand] using
    smoothedPrimalObjective_apply B Q (0 : E → ℝ) (fun u : E ↦ b u + B u u) d μ x

/-- Evaluating `primalFormSmoothedObjective` recovers the textbook maximization oracle
`max_{u ∈ Q} {⟪Bx, u⟫ - μ d(u) - ⟪b, u⟫ - ⟪Bu, u⟫}`, encoded in Lean as a supremum over `Q`. -/
theorem primalFormSmoothedObjective_apply
    (B : E →L[ℝ] StrongDual ℝ E) (Q : Set E) (b : StrongDual ℝ E) (d : E → ℝ) (μ : ℝ) (x : E) :
    primalFormSmoothedObjective B Q b d μ x =
      sSup ((fun u : E ↦ B x u - μ * d u - b u - B u u) '' Q) := by
  have hmaximand :
      (fun u : E ↦ B x u - (b u + B u u) - μ * d u) =
        fun u : E ↦ B x u - μ * d u - b u - B u u := by
    funext u
    ring_nf
  rw [primalFormSmoothedObjective_def, hmaximand]

end
