/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_21
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20_Core
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: apply Example 13.4 to the indicator of `C` with parameter `γ = 1`, then rewrite
-- the Moreau envelope term using the squared-distance formula for the indicator function.
/-- Example 13.5: if `C` is nonempty and `f = ι_C + ‖·‖² / 2`, then the Fenchel conjugate `f*`
is `u ↦ (‖u‖² - d(u, C)²) / 2`. -/
theorem fenchelConjugate_indicator_add_halfSquaredNorm_eq_sqNorm_sub_sqInfDist_div_two
    (C : Set H) (hC_nonempty : C.Nonempty) :
    ((ι[C] + halfSquaredNorm).asEReal)∗ =
      fun u : H ↦ ((((‖u‖ ^ 2 - Metric.infDist u C ^ 2) / 2 : ℝ) : EReal)) := by
  let γ : Set.Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.2 zero_lt_one⟩
  funext u
  have hmoreau := congrFun (indicator_moreauEnvelope_eq_scaled_sq_infEDist C γ) u
  have hdist_top : (Metric.infEDist u C : EReal) ≠ ⊤ := by
    intro h
    rcases hC_nonempty with ⟨y, hy⟩
    exact ne_top_of_le_ne_top (edist_ne_top u y) (Metric.infEDist_le_edist_of_mem hy)
      (by simpa using h)
  have hreg' :
      (((ι[C] + halfSquaredNorm).asEReal)∗) u =
        ((((‖u‖ ^ 2) / 2 : ℝ) : EReal) - {}^[γ] ι[C] u) := by
    have hreg0 :
        (((ι[C] + halfSquaredNorm).asEReal)∗) u =
          ((((1 / 2) * ‖u‖ ^ 2 : ℝ) : EReal) - {}^[γ] ι[C] u) := by
      simpa [γ, halfSquaredNorm, one_smul] using
        conjugate_regularized_value_eq_scaledQuadratic_sub_moreauEnvelope (ι[C]) γ u
    calc
      (((ι[C] + halfSquaredNorm).asEReal)∗) u
          = ((((1 / 2) * ‖u‖ ^ 2 : ℝ) : EReal) - {}^[γ] ι[C] u) := hreg0
      _ = ((((‖u‖ ^ 2) / 2 : ℝ) : EReal) - {}^[γ] ι[C] u) := by
            congr 1
            ring_nf
  have hmoreau' :
      {}^[γ] ι[C] u = (Metric.infEDist u C : EReal) ^ 2 / (2 : EReal) := by
    calc
      {}^[γ] ι[C] u = (Metric.infEDist u C : EReal) ^ 2 / (2 * (γ : ℝ) : EReal) := hmoreau
      _ = (Metric.infEDist u C : EReal) ^ 2 / (2 : EReal) := by
        norm_num [γ]
  have hsq :
      (Metric.infEDist u C : EReal) ^ 2 / (2 : EReal) =
        (((Metric.infDist u C ^ 2) / 2 : ℝ) : EReal) := by
    rw [pow_two, ← EReal.coe_toReal hdist_top (by simp : (Metric.infEDist u C : EReal) ≠ ⊥),
      ← EReal.coe_toReal hdist_top (by simp : (Metric.infEDist u C : EReal) ≠ ⊥),
      show (2 : EReal) = ((2 : ℝ) : EReal) by rfl, ← EReal.coe_mul, ← EReal.coe_div]
    simp [Metric.infDist, pow_two]
  calc
    (((ι[C] + halfSquaredNorm).asEReal)∗) u
        = ((((‖u‖ ^ 2) / 2 : ℝ) : EReal) -
            ((Metric.infEDist u C : EReal) ^ 2 / (2 : EReal))) := by
            rw [hreg', hmoreau']
    _ = ((((‖u‖ ^ 2) / 2 : ℝ) : EReal) -
          (((Metric.infDist u C ^ 2) / 2 : ℝ) : EReal)) := by
            rw [hsq]
    _ = (((((‖u‖ ^ 2) / 2) - (Metric.infDist u C ^ 2) / 2 : ℝ) : EReal)) := by
          rw [← EReal.coe_sub]
    _ = ((((‖u‖ ^ 2 - Metric.infDist u C ^ 2) / 2 : ℝ) : EReal)) := by
          congr 1
          ring_nf

end

end ERealFunction
