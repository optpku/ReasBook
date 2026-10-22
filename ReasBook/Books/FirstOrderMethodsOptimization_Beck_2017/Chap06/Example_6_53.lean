/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_25

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {α : Type u} (C : Set α)

/- Example 6.53 is `bridge/view` in the chapter's Moreau-envelope/projection domain. The owner
stack already lives upstream:

- `M[μ, f]` from Definition 6.7,
- `δ_ C` from Definition 2.2,
- `prox_extendedIndicator_eq_projection_mapping` from Theorem 6.24,
- `projection_mapping_eq_singleton_of_nonempty_closed_convex` from Theorem 6.25,
- `infDist_eq_dist_metricProjection` from Proposition 3.12.

Accordingly, this file keeps only the source-facing Moreau-envelope formulas and a minimal bridge
showing that positive scaling does not change `δ_ C`. -/

/-- Positive scaling does not change the indicator `δ_ C` of a set `C`. -/
theorem smul_extendedIndicator_eq (μ : PosReal) :
    (((μ : EReal) • δ_ C) : α → EReal) = δ_ C := by
  funext x
  by_cases hx : x ∈ C
  · simp [extendedIndicator, hx, Pi.smul_apply, smul_eq_mul]
  · simp [extendedIndicator, hx, Pi.smul_apply, smul_eq_mul, EReal.coe_mul_top_of_pos μ.2]

end

section ProjectionFormula

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (C : Set E)

/-- For a nonempty closed convex set, the proximal mapping of any positive scaling of `δ_ C` is
the singleton containing the metric projection `P_C(x)`. -/
theorem prox_scaledExtendedIndicator_eq_singleton_metricProjection
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (μ : PosReal) (x : E) :
    prox[((μ : EReal) • δ_ C)] x = {Pp[C, hC_nonempty, hC_closed, hC_convex] x} := by
  rw [smul_extendedIndicator_eq C μ, prox_extendedIndicator_eq_projection_mapping C hC_nonempty x,
    projection_mapping_eq_singleton_of_nonempty_closed_convex
      C hC_nonempty hC_closed hC_convex x]

/-- Helper for Example 6.53: the quadratic penalty at the metric projection is the scaled square
of the distance `infDist x C`. -/
lemma metricProjection_penalty_eq_quadratic_infDist
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (μ : PosReal) (x : E) :
    ((((1 / (2 * μ) : ℝ) * ‖x - Pp[C, hC_nonempty, hC_closed, hC_convex] x‖ ^ (2 : ℕ)) :
      ℝ) : EReal) =
      ((((1 / (2 * μ) : ℝ) * (Metric.infDist x C) ^ (2 : ℕ)) : ℝ) : EReal) := by
  calc
    ((((1 / (2 * μ) : ℝ) * ‖x - Pp[C, hC_nonempty, hC_closed, hC_convex] x‖ ^ (2 : ℕ)) :
      ℝ) : EReal) =
        ((((1 / (2 * μ) : ℝ) * dist x (Pp[C, hC_nonempty, hC_closed, hC_convex] x) ^
          (2 : ℕ)) : ℝ) : EReal) := by
          simp [dist_eq_norm]
    _ = ((((1 / (2 * μ) : ℝ) * (Metric.infDist x C) ^ (2 : ℕ)) : ℝ) : EReal) := by
          rw [← infDist_eq_dist_metricProjection C hC_nonempty hC_closed hC_convex x]

/-- Example 6.53 (1): in a complete real inner-product space, if `C` is nonempty, closed, and
convex, then the Moreau envelope of `δ_ C` can be written pointwise using the metric projection
`P_C`. -/
theorem moreau_envelope_extendedIndicator_eq_indicator_metricProjection_add_sq_dist
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (μ : PosReal) (x : E) :
    M[μ, δ_ C] x =
      (δ_ C) (Pp[C, hC_nonempty, hC_closed, hC_convex] x) +
        ((((1 / (2 * μ) : ℝ) * ‖x - Pp[C, hC_nonempty, hC_closed, hC_convex] x‖ ^
          (2 : ℕ)) : ℝ) : EReal) := by
  simpa using
    (moreau_envelope_eq_of_scaled_prox_eq_singleton
      (prox_scaledExtendedIndicator_eq_singleton_metricProjection
        C hC_nonempty hC_closed hC_convex μ x))

/-- Example 6.53 (2): under the same nonempty closed convex hypotheses, the Moreau envelope of
`δ_ C` is the scaled half squared distance to `C`. -/
theorem moreau_envelope_extendedIndicator_eq_half_sq_infDist
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (μ : PosReal) :
    M[μ, δ_ C] =
      fun x ↦ ((((1 / (2 * μ) : ℝ) * (Metric.infDist x C) ^ (2 : ℕ)) : ℝ) : EReal) := by
  funext x
  calc
    M[μ, δ_ C] x =
        (δ_ C) (Pp[C, hC_nonempty, hC_closed, hC_convex] x) +
          ((((1 / (2 * μ) : ℝ) *
            ‖x - Pp[C, hC_nonempty, hC_closed, hC_convex] x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
          simpa using
            moreau_envelope_extendedIndicator_eq_indicator_metricProjection_add_sq_dist
              C hC_nonempty hC_closed hC_convex μ x
    _ = ((((1 / (2 * μ) : ℝ) *
          ‖x - Pp[C, hC_nonempty, hC_closed, hC_convex] x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
          have hP : Pp[C, hC_nonempty, hC_closed, hC_convex] x ∈ C :=
            projectionPoint_mem C hC_nonempty hC_closed hC_convex x
          simp [extendedIndicator, hP]
    _ = ((((1 / (2 * μ) : ℝ) * (Metric.infDist x C) ^ (2 : ℕ)) : ℝ) : EReal) :=
          metricProjection_penalty_eq_quadratic_infDist C hC_nonempty hC_closed hC_convex μ x

end ProjectionFormula
