/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open Metric
open scoped Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Proposition 5.3 is `source-facing`: its mathematical content is the differentiability of
`x ↦ (infDist x C)^2 / 2` for a nonempty closed convex set together with the explicit gradient
formula `x - P_C(x)`. Domain sampling identifies Proposition 3.12's
`hasGradientAt_half_sq_infDist` as the owner abstraction for that content, Theorem 5.4's firm
nonexpansiveness of `metricProjection` as the key Lipschitz input, and Definition 5.1's
`is_l_smooth_on` as a derived Chapter 5 bridge. The primitive data are only the set `C` and its
nonempty/closed/convex hypotheses; the gradient field is derived from the owner theorem rather
than stored through a parallel local wrapper. -/
recall hasGradientAt_half_sq_infDist

section

variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" => fun x ↦
  (metricProjection C hC_nonempty hC_closed hC_convex x : E)

-- Proof sketch: write the gradient difference as `(x - y) - (P x - P y)`, expand its squared
-- norm, and use firm nonexpansiveness of the metric projection to bound the cross term.
/-- Proposition 5.3 companion: for a nonempty closed convex set, the explicit gradient field
`x ↦ x - P_C(x)` is nonexpansive. -/
theorem half_sq_infDist_sub_metricProjection_nonexpansive (x y : E) :
    ‖(x - P x) - (y - P y)‖ ≤ ‖x - y‖ := by
  let p := P x - P y
  have hfirm : ‖p‖ ^ 2 ≤ inner ℝ p (x - y) := by
    simpa [p] using
      metricProjection_firmly_nonexpansive C hC_nonempty hC_closed hC_convex x y
  have hsq : ‖(x - y) - p‖ ^ 2 = ‖x - y‖ ^ 2 - 2 * inner ℝ (x - y) p + ‖p‖ ^ 2 :=
    norm_sub_sq_real (x - y) p
  have hsq_le : ‖(x - y) - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [real_inner_comm] at hfirm
    nlinarith [hsq, hfirm]
  have habs : |‖(x - y) - p‖| ≤ |‖x - y‖| := (sq_le_sq).1 hsq_le
  convert habs using 1 <;> simp [p, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end

-- Proof sketch: Proposition 3.12 gives differentiability everywhere and identifies the gradient as
-- `x - P_C(x)`. For the owner-level smoothness statement, it remains to show this gradient field is
-- `1`-Lipschitz. Writing the gradient difference as `(x - y) - (P_C(x) - P_C(y))`, expanding its
-- squared norm, and applying firm nonexpansiveness of the metric projection yields the estimate.
variable [FiniteDimensional ℝ E]

private theorem half_sq_infDist_is_l_smooth_of_nonempty_closed
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) :
    is_l_smooth_on (fun z ↦ (infDist z C) ^ 2 / 2) Set.univ 1 := by
  rw [is_l_smooth_on_iff_lipschitzOnWith_gradient]
  refine ⟨?_, ?_⟩
  · intro x _
    have hx :=
      hasGradientAt_half_sq_infDist C hC_nonempty hC_closed hC_convex x
    exact hx.differentiableAt
  · rw [lipschitzOnWith_iff_norm_sub_le]
    intro x _ y _
    rw [gradient_half_sq_infDist_eq_sub_metricProjection
        C hC_nonempty hC_closed hC_convex x,
      gradient_half_sq_infDist_eq_sub_metricProjection
        C hC_nonempty hC_closed hC_convex y]
    simpa using
      half_sq_infDist_sub_metricProjection_nonexpansive
        C hC_nonempty hC_closed hC_convex x y

-- Proof sketch: if `C = ∅`, then `Metric.infDist · C = 0`, so the function is constant. If
-- `C.Nonempty`, replace `C` by its closure; `Metric.infDist` is unchanged by closure, while
-- `closure C` is closed, nonempty, and convex, so the closed-case estimate applies.
/-- Proposition 5.3: in a finite-dimensional real inner product space, the half squared distance
to a convex set is globally `1`-smooth. -/
theorem half_sq_infDist_is_l_smooth (C : Set E) (hC_convex : Convex ℝ C) :
    is_l_smooth_on (fun z ↦ (infDist z C) ^ 2 / 2) Set.univ 1 := by
  by_cases hC_nonempty : C.Nonempty
  · simpa [Metric.infDist_closure] using
      half_sq_infDist_is_l_smooth_of_nonempty_closed (closure C) hC_nonempty.closure
        isClosed_closure hC_convex.closure
  · rw [Set.not_nonempty_iff_eq_empty.mp hC_nonempty]
    rw [is_l_smooth_on_iff_lipschitzOnWith_gradient]
    refine ⟨?_, ?_⟩
    · intro x _
      simp [Metric.infDist_empty]
    · rw [lipschitzOnWith_iff_norm_sub_le]
      intro x _ y _
      simp [Metric.infDist_empty]

end
