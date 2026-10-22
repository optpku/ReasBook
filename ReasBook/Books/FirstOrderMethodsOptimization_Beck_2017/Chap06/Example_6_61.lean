/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_25

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Example 6.61 is `bridge/view` in the chapter's distance/projection/proximal domain.
Domain sampling shows that the owner layer is already fixed upstream:

- `half_sq_infDist_is_l_smooth` from Proposition 5.3 is the canonical smoothness statement for
  the half squared distance,
- `gradient_half_sq_infDist_eq_sub_metricProjection` from Proposition 3.12 is the canonical
  point-valued gradient formula,
- `prox_extendedIndicator_eq_projection_mapping` from Theorem 6.24 and
  `projection_mapping_eq_singleton_of_nonempty_closed_convex` from Theorem 6.25 are the Chapter 6
  bridges from the source-facing proximal/projection notation to the canonical metric projection.

Accordingly, this file keeps only direct recall of the existing owner statements plus the small
derived bridge from `prox[extendedIndicator C]` to the singleton metric projection. -/

/- Example 6.61 (1): for a convex set `C`, the half squared distance function
`x ↦ (1 / 2) d_C(x)^2 = (infDist x C)^2 / 2` is globally `1`-smooth. -/
recall half_sq_infDist_is_l_smooth

-- Proof sketch: combine the indicator/projection identification
-- `prox_extendedIndicator_eq_projection_mapping` with the singleton projection theorem
-- `projection_mapping_eq_singleton_of_nonempty_closed_convex`.
/-- For a nonempty closed convex set, the proximal mapping of the indicator `δ_C` is the singleton
containing the metric projection `P_C(x)`. -/
theorem prox_extendedIndicator_eq_singleton_metricProjection
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (x : E) :
    prox[extendedIndicator C] x = {Pp[C, hC_nonempty, hC_closed, hC_convex] x} := by
    rw [prox_extendedIndicator_eq_projection_mapping C hC_nonempty x,
      projection_mapping_eq_singleton_of_nonempty_closed_convex
        C hC_nonempty hC_closed hC_convex x]

/- Example 6.61 (2): for a nonempty closed convex set `C`, the gradient of
`x ↦ (1 / 2) d_C(x)^2` is `x - P_C(x)`, where the chapter's source-facing proximal notation
identifies `prox_{δ_C}(x)` with the same singleton by
`prox_extendedIndicator_eq_singleton_metricProjection`. -/
recall gradient_half_sq_infDist_eq_sub_metricProjection

end
