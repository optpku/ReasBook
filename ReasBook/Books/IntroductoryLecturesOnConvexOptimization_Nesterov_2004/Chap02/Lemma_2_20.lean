/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_22
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Remark_2_35_1

open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 2.20 lies in the whole-space specialization of the simple-set estimating-sequence domain
on a complete real inner-product space. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`.

Owner declarations sampled for this refinement:
* `simpleSetEstimatingModel` in `Proposition_2_22`, the owner lower model over a closed convex
  feasible set;
* `simpleSetEstimatingFunction`, `simpleSetEstimatingCenter`, and `simpleSetEstimatingValue` in
  `Proposition_2_22`, the owner recursive estimating-sequence objects in canonical quadratic form;
* `simpleSetEstimatingFunction_eq_canonicalQuadratic` and
  `simpleSetEstimatingFunction_eq_canonicalQuadratic_apply` in `Proposition_2_22`, the owner
  centered-quadratic function identity and its pointwise companion;
* `gradientMapping_univ_eq_gradient_step` and `reducedGradient_univ_eq_gradient` in
  `Remark_2_35_1`, the chapter's canonical whole-space bridge from projected-gradient stage data
  to the unconstrained `gradientStep` / `∇ f` formulas.

Best owner abstraction:
* source-facing: the textbook whole-space formulas obtained by specializing the simple-set owners
  to `Q = Set.univ`;
* core/canonical: `simpleSetEstimatingModel`, `simpleSetEstimatingFunction`,
  `simpleSetEstimatingCenter`, `simpleSetEstimatingValue`, and
  `simpleSetEstimatingFunction_eq_canonicalQuadratic_apply`;
* bridge/view: the ordinary specialization `Q = Set.univ`, simplified through
  `gradientMapping_univ_eq_gradient_step` and `reducedGradient_univ_eq_gradient`.

Primitive data:
* the objective `f`, initial point `x0`, parameters `(μ, L, γ₀)`, and stage data `(y, α)`;
* the nonvanishing hypothesis on the owner curvature sequence.

Derived API:
* the whole-space lower-model formula rewritten to `gradientStep` / `∇ f`;
* the whole-space recursive estimating-function and scalar-value families;
* the whole-space centered-quadratic identity.

The previous file duplicated these declarations with separate `smoothEstimating...` names. Those
definitions were exact `Set.univ` specializations of the owner simple-set API, so this file now
keeps only the specialization layer and reuses the canonical owner declarations directly. -/

recall simpleSetEstimatingModel
recall simpleSetEstimatingModel_apply
recall simpleSetEstimatingFunction
recall simpleSetEstimatingCenter
recall simpleSetEstimatingValue
recall simpleSetEstimatingFunction_eq_canonicalQuadratic
recall simpleSetEstimatingFunction_eq_canonicalQuadratic_apply

section

variable
    (f : E → ℝ) (x0 : E)
    (μ : ℝ) (L : NNRealˣ) (gamma0 : ℝ)
    (y : ℕ → E) (alpha : ℕ → ℝ)
    (k : ℕ) (x : E)

local notation "univSet" => (Set.univ : Set E)

local notation "model" =>
  simpleSetEstimatingModel
    univSet Set.univ_nonempty isClosed_univ convex_univ
    f μ L y

local notation "phi" =>
  simpleSetEstimatingFunction
    univSet Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y alpha

local notation "center" =>
  simpleSetEstimatingCenter
    univSet Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y alpha

local notation "phiStar" =>
  simpleSetEstimatingValue
    univSet Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y alpha

#check (model k : E → ℝ)

#check (phi : ℕ → E → ℝ)

#check (center : ℕ → E)

#check (phiStar : ℕ → ℝ)

/-- Lemma 2.20: specializing the simple-set lower model to the whole space rewrites the projected
step data as the exact gradient step `gradientStep f (y k) L` and gradient `∇ f (y k)`. -/
theorem whole_space_simpleSetEstimatingModel_apply :
    model k x =
      let yk := y k
      f (gradientStep f yk L) +
        (1 / (2 * L)) * ‖∇ f yk‖ ^ (2 : ℕ) +
        inner ℝ (∇ f yk) (x - yk) +
        (μ / 2) * ‖x - yk‖ ^ (2 : ℕ) := by
  simp [simpleSetEstimatingModel_apply, gradientMapping_univ_eq_gradient_step,
    reducedGradient_univ_eq_gradient]

/-- Lemma 2.20: the whole-space estimating-sequence function keeps the canonical centered
quadratic form from Proposition 2.22. -/
theorem whole_space_simpleSetEstimatingFunction_eq_canonicalQuadratic_apply
    (hγ : ∀ k, estimatingSequenceCurvature μ gamma0 alpha (k + 1) ≠ 0) :
    phi k x =
      phiStar k +
        (estimatingSequenceCurvature μ gamma0 alpha k / 2) *
          ‖x - center k‖ ^ (2 : ℕ) :=
  simpleSetEstimatingFunction_eq_canonicalQuadratic_apply
    univSet Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y alpha hγ k x

end
