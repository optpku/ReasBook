/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_22

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap
open scoped ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 2.37 is a recall-only item in the projected-gradient estimating-sequence domain for
a simple feasible set in a complete real inner-product space.

Primary domain:
* projected-gradient estimating sequences over a closed convex feasible set

Sampled owner-style declarations:
* `simpleSetEstimatingModel`
* `simpleSetEstimatingModel_apply`
* `simpleSetEstimatingFunction`
* `simpleSetEstimatingFunction_succ`

Best owner abstraction:
* the source-facing owners `simpleSetEstimatingModel` and `simpleSetEstimatingFunction` already
  defined in `Proposition_2_22`

Primitive data:
* a feasible set `Q` with nonempty / closed / convex hypotheses
* an objective `f`, initial point `x0`, and parameters `μ`, `L`, `gamma0`
* the stage points `y` and weights `α`

Derived API:
* the displayed lower-model formula `simpleSetEstimatingModel_apply`
* the initial-value identity `simpleSetEstimatingFunction_zero`
* the affine-recursion identity `simpleSetEstimatingFunction_succ`

Source/core/bridge triage:
* source-facing: the simple-set lower model and recursive estimating sequence from the text
* core/canonical: the owner declarations in `Proposition_2_22`, together with
  `quadraticallyRegularizedObjective` and `lineMap`
* bridge/view: the `..._apply`, zero-stage, and successor-stage formulas

This file therefore uses direct canonical recall for the owners and their companion formulas,
without re-spelling those long interfaces as parallel local declarations. -/

recall simpleSetEstimatingModel
recall simpleSetEstimatingModel_apply
recall simpleSetEstimatingFunction
recall simpleSetEstimatingFunction_zero
recall simpleSetEstimatingFunction_succ

section

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (x0 : E)
    (μ : ℝ) (L : NNRealˣ) (gamma0 : ℝ)
    (y : ℕ → E) (α : ℕ → ℝ) (k : ℕ) (x : E)

local notation "model" =>
  simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k

local notation "phi" =>
  simpleSetEstimatingFunction Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α

#check
  (show
      model x =
        let xQk := x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](y k)
        let gQk := g_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](y k)
        f xQk +
          (1 / (2 * L)) * ‖gQk‖ ^ (2 : ℕ) +
          inner ℝ gQk (x - y k) +
          (μ / 2) * ‖x - y k‖ ^ (2 : ℕ) from
    simpleSetEstimatingModel_apply Q hQ_nonempty hQ_closed hQ_convex f μ L y k x)

#check
  (show
      phi 0 =
        quadraticallyRegularizedObjective (fun _ : E ↦ f x0) gamma0 x0 from
    simpleSetEstimatingFunction_zero
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α)

#check
  (show
      phi (k + 1) =
        lineMap (phi k) model (α k) from
    simpleSetEstimatingFunction_succ
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k)

end

end
