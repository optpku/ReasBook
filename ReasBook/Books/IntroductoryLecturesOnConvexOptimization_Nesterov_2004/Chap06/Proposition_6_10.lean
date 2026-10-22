/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-
Proposition 6.10 lies in the constrained smoothing / within-set differentiability domain.

Sampled owner-style declarations:
- `explicitModelSmoothedProblem` in `Chap06/Definition_6_9`, the chapter owner for the smoothed
  explicit-model objective on a feasible set;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the ambient owner reused by
  `explicitModelSmoothedProblem`;
- mathlib `HasFDerivWithinAt.add`, the canonical within-set derivative sum rule;
- mathlib `LipschitzOnWith`, the canonical set-restricted Lipschitz owner.

Best owner abstraction:
- source-facing: `explicitModelSmoothedProblem Q₁ hatF fμ`;
- core/canonical: `HasFDerivWithinAt` and `LipschitzOnWith`;
- bridge/view: the evaluation lemma `explicitModelSmoothedProblem_apply`.

Primitive data:
- the feasible set `Q₁`;
- the base term `hatF` and smoothing term `fμ`;
- chosen derivative fields `gradHatF` and `gradFμ`;
- the derivative and Lipschitz hypotheses for those fields.

Derived API:
- the within-set derivative of the smoothed objective, obtained by the additive derivative rule;
- the Lipschitz bound for the summed derivative field, obtained by the triangle inequality.

This proposition is source-facing but not a new owner. The earlier local pointwise-sum wrapper
duplicated the existing Chapter 6 owner `explicitModelSmoothedProblem`, so the theorem now talks
directly about that owner and derives the sum view only through the existing evaluation lemma.
-/

/-- Proposition 6.10: if `\hat f` has `M`-Lipschitz gradient on `Q₁` and `f_μ` has gradient
Lipschitz constant `Real.toNNReal ((1 / μ) * ‖A‖^2)` on `Q₁`, then the objective of the
explicit-model smoothed problem from Definition 6.9 has derivative selection `gradHatF + gradFμ`
on `Q₁`, hence is differentiable there, and this derivative selection is Lipschitz on `Q₁` with
constant `M + Real.toNNReal ((1 / μ) * ‖A‖^2)`. -/
theorem explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn
    {Q₁ : Set E} {hatF fμ : E → ℝ} {gradHatF gradFμ : E → StrongDual ℝ E}
    (A : E →L[ℝ] F) {μ : ℝ} {M : NNReal}
    (hhatF : ∀ x ∈ Q₁, HasFDerivWithinAt hatF (gradHatF x) Q₁ x)
    (hhatF_lipschitz : LipschitzOnWith M gradHatF Q₁)
    (hfμ : ∀ x ∈ Q₁, HasFDerivWithinAt fμ (gradFμ x) Q₁ x)
    (hfμ_lipschitz :
      LipschitzOnWith (Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ))) gradFμ Q₁) :
    (∀ x ∈ Q₁,
      HasFDerivWithinAt
        (explicitModelSmoothedProblem Q₁ hatF fμ)
        (gradHatF x + gradFμ x) Q₁ x) ∧
    LipschitzOnWith
      (M + Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ)))
      (fun x ↦ gradHatF x + gradFμ x) Q₁ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simpa [explicitModelSmoothedProblem] using (hhatF x hx).add (hfμ x hx)
  · intro x hx y hy
    calc
      edist (gradHatF x + gradFμ x) (gradHatF y + gradFμ y) ≤
          edist (gradHatF x) (gradHatF y) + edist (gradFμ x) (gradFμ y) :=
        edist_add_add_le _ _ _ _
      _ ≤
          (M + Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ))) * edist x y := by
        simpa [add_mul] using
          add_le_add (hhatF_lipschitz hx hy) (hfμ_lipschitz hx hy)

end
