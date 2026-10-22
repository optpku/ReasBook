/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Text 4.2.17 lies in the chapter's scalar inverse-power gap-estimate domain.

Sampled neighboring declarations:
* `false_acceleration_gap_at_two_thirds_index_le_three_cubed_bound` in `Text_4_2_15`, the
  immediate predecessor false-acceleration rate statement, already on the chapter-standard
  constants `L3 R : NNReal`;
* `acceleratedCubicRegularization_gap_le_inverse_cubic_rate` in `Theorem_4_2_3`, the chapter's
  canonical accelerated cubic-Newton inverse-power gap estimate, again using `L3 : NNReal`;
* `cubicNewton_gap_le_inverse_square_rate_of_bounded_sublevel` in `Theorem_4_2_2`, the nearby
  cubic-Newton rate theorem written directly with the chapter standard nonnegative constants.

Best owner abstraction:
* source-facing: the displayed inverse-eighth objective-gap estimate at `x_{N+1}`;
* core/canonical: the scalar eighth-power gap upper bound together with the inverse-linear
  distance decay, stated using the chapter-standard nonnegative parameters `L3` and `R`;
* bridge/view: only the ambient coercions `(L3 : ℝ)` and `(R : ℝ)` needed on the real-valued
  theorem surface.

Primitive data:
* the objective `f`, iterate sequence `x`, reference point `xStar`, strong-convexity modulus
  `σ₂`, chapter constants `L3` and `R`, and the index `N`;
* the local eighth-power gap estimate at `x_{N+1}`;
* the inverse-linear distance decay at `x_{N+1}`.

Derived API:
* nonnegativity of the scalar coefficient and right-hand side bound, now inherited from
  `L3 R : NNReal` and `σ₂ > 0`;
* monotonicity of the eighth power applied to the distance estimate.

The previous version carried `L₃` and `R` as raw real parameters even though the surrounding
Chapter 4 rate API already treats them as canonical nonnegative constants. This refinement aligns
the theorem with that owner layer and removes proof scaffolding whose only purpose was to recover
those missing sign facts.
-/

/-- Text 4.2.17 at the source-facing scalar consequence level: once the earlier convexity,
smoothness, and false-acceleration hypotheses have been condensed into the local gap estimate at
`x_{N+1}` and the inverse-linear distance decay `‖x_{N+1} - xStar‖ ≤ 3 R / N`, substituting the
distance bound into the eighth-power estimate yields the inverse-eighth decay of the objective
gap for every positive index `N`. -/
theorem false_acceleration_gap_le_inverse_eighth_rate
    (f : E → ℝ) (x : ℕ → E) (xStar : E) (σ₂ : ℝ) (L3 R : NNReal) (N : ℕ)
    (hσ₂ : 0 < σ₂)
    (hN : 0 < N)
    (hgap_upper :
      f (x (N + 1)) - f xStar ≤
        (((3 : ℝ) ^ (9 : ℕ)) * (L3 : ℝ) ^ (4 : ℕ) / (2 * σ₂ ^ (3 : ℕ))) *
          ‖x (N + 1) - xStar‖ ^ (8 : ℕ))
    (hdistance_decay :
      ‖x (N + 1) - xStar‖ ≤ 3 * (R : ℝ) / (N : ℝ)) :
    f (x (N + 1)) - f xStar ≤
      (((3 : ℝ) ^ (17 : ℕ)) * (L3 : ℝ) ^ (4 : ℕ) * (R : ℝ) ^ (8 : ℕ)) /
        (2 * σ₂ ^ (3 : ℕ) * (N : ℝ) ^ (8 : ℕ)) := by
  have hN_real : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_real
  let coeff : ℝ := (((3 : ℝ) ^ (9 : ℕ)) * (L3 : ℝ) ^ (4 : ℕ) / (2 * σ₂ ^ (3 : ℕ)))
  have hcoeff_nonneg : 0 ≤ coeff := by
    positivity
  have hpow :
      ‖x (N + 1) - xStar‖ ^ (8 : ℕ) ≤ (3 * (R : ℝ) / (N : ℝ)) ^ (8 : ℕ) := by
    gcongr
  calc
    f (x (N + 1)) - f xStar ≤
        coeff *
          ‖x (N + 1) - xStar‖ ^ (8 : ℕ) :=
      hgap_upper
    _ ≤
        coeff *
          (3 * (R : ℝ) / (N : ℝ)) ^ (8 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hpow hcoeff_nonneg
    _ = (((3 : ℝ) ^ (17 : ℕ)) * (L3 : ℝ) ^ (4 : ℕ) * (R : ℝ) ^ (8 : ℕ)) /
          (2 * σ₂ ^ (3 : ℕ) * (N : ℝ) ^ (8 : ℕ)) := by
      dsimp [coeff]
      rw [div_pow, mul_pow]
      field_simp [hN_ne]
