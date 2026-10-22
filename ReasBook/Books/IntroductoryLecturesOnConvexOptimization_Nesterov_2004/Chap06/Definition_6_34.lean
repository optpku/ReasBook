/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 6.34 lies in Chapter 6's scalar smoothing-parameter domain.

Mandatory domain-style sampling before drafting:
- `switching_parameters` in `Chap06/Definition_6_35`, which keeps the source-facing Chapter 6
  scalar update data as an explicit owner rather than packaging it into a new framework;
- `excessive_gap_alpha` and `alternating_excessive_gap_step_size` in `Chap06/Definition_6_36`,
  which likewise expose the chapter's scalar parameter formulas directly;
- `scaled_smoothing_parameter_product_eq` in `Chap06/Proposition_6_28`, the downstream scalar
  identity that consumes exactly the formulas introduced here.

Best owner abstraction:
- source-facing: the ordered pair `(μ₁, μ₂)` of smoothness parameters;
- core/canonical: an explicit pair-valued scalar definition;
- bridge/view: the projection theorems recovering the displayed formulas for `μ₁` and `μ₂`.

Primitive data:
- the positive-source scalars `D₁`, `D₂`, `λ₁`, `λ₂`, and `‖A‖_{1,2}`;
- the displayed formulas for `μ₁` and `μ₂`.

Derived API:
- the first and second projection identities for the pair-valued owner.

The source formulas depend only on the scalar quantity `‖A‖_{1,2}`, not on the operator `A`
itself. Exposing the operator and ambient normed spaces here would therefore add public API noise
without changing the mathematical content of this definition.
-/

/-- Definition 6.34 [Chapter6_2.json:73]: the smoothness parameters are the pair
`(μ₁, μ₂)` defined by
`μ₁ = λ₁ ‖A‖_{1,2} √(D₂ / D₁)` and `μ₂ = λ₂ ‖A‖_{1,2} √(D₁ / D₂)`. -/
def smoothness_parameters
    (D1 D2 opNorm12 lambda1 lambda2 : ℝ) : ℝ × ℝ :=
  ( lambda1 * opNorm12 * Real.sqrt (D2 / D1)
  , lambda2 * opNorm12 * Real.sqrt (D1 / D2) )

-- Proof sketch: unfold `smoothness_parameters`; the first projection of the defining pair is
-- exactly the displayed formula for `μ₁`.
/-- The first projection of `smoothness_parameters` is the parameter
`μ₁ = λ₁ ‖A‖_{1,2} √(D₂ / D₁)`. -/
theorem smoothness_parameters_fst
    (D1 D2 opNorm12 lambda1 lambda2 : ℝ) :
    (smoothness_parameters D1 D2 opNorm12 lambda1 lambda2).1 =
      lambda1 * opNorm12 * Real.sqrt (D2 / D1) := by
  -- Reduce the first projection of the defining pair.
  rfl

-- Proof sketch: unfold `smoothness_parameters`; the second projection of the defining pair is
-- exactly the displayed formula for `μ₂`.
/-- The second projection of `smoothness_parameters` is the parameter
`μ₂ = λ₂ ‖A‖_{1,2} √(D₁ / D₂)`. -/
theorem smoothness_parameters_snd
    (D1 D2 opNorm12 lambda1 lambda2 : ℝ) :
    (smoothness_parameters D1 D2 opNorm12 lambda1 lambda2).2 =
      lambda2 * opNorm12 * Real.sqrt (D1 / D2) := by
  -- Reduce the second projection of the defining pair.
  rfl

end
