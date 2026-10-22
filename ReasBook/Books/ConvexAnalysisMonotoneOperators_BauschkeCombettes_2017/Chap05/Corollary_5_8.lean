/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_51
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section

variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

-- Proof sketch: apply Proposition 5.7 to obtain some `y ∈ C` such that the projection shadow
-- sequence `P_C (xₙ n)` converges strongly to `y`. Then combine the weak convergence `xₙ ⇀ x`, the
-- strong convergence `P_C (xₙ n) → y`, and the projection variational inequality to show
-- `‖x - y‖ ^ 2 = 0`, hence `x = y`.
/-- Corollary 5.8: if `C` is a nonempty closed convex subset of a real Hilbert space, `xₙ` is
Fejér monotone with respect to `C`, `x ∈ C`, and `xₙ` converges weakly to `x`, then the shadow
sequence of metric projections of `xₙ` onto `C` converges strongly to `x`. -/
theorem tendsto_projectionPoint_of_fejerMonotone_of_tendsto_weakly
    (xₙ : ℕ → H) (hxₙ : FejerMonotone C xₙ) {x : H} (hx : x ∈ C)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x))) :
    Tendsto (fun n ↦ P (xₙ n)) atTop (𝓝 x) := by
  obtain ⟨z, hzC, hz⟩ :=
    exists_shadowLimit_of_fejerMonotone hC_nonempty hC_closed hC_convex xₙ hxₙ
  have hPx : P x = x := by
    have hxproj : x = P x :=
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mpr <| by
          refine ⟨hx, ?_⟩
          intro y hy
          simp
    simpa using hxproj.symm
  have hweak_sub :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n - x)) atTop (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    have hconst :
        Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H x) atTop (𝓝 (toWeakSpace ℝ H x)) :=
      tendsto_const_nhds
    simpa [sub_eq_add_neg] using hweak.sub hconst
  have hstrong_sub : Tendsto (fun n ↦ P (xₙ n) - x) atTop (𝓝 (z - x)) := by
    simpa [sub_eq_add_neg] using
      hz.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x))
  have hsq_left :
      Tendsto (fun n ↦ ‖P (xₙ n) - x‖ ^ 2) atTop (𝓝 (‖z - x‖ ^ 2)) := by
    simpa using hstrong_sub.norm.pow 2
  have hinner_zero :
      Tendsto (fun n ↦ ⟪xₙ n - x, P (xₙ n) - x⟫_ℝ) atTop (𝓝 0) :=
    by
      simpa using
        tendsto_inner_of_tendsto_weakly_of_tendsto
          (fun n ↦ xₙ n - x) (fun n ↦ P (xₙ n) - x) 0 (z - x) hweak_sub hstrong_sub
  have hsq_right :
      Tendsto (fun n ↦ ⟪P (xₙ n) - x, xₙ n - x⟫_ℝ) atTop (𝓝 0) := by
    simpa [real_inner_comm] using hinner_zero
  have hineq :
      ∀ n, ‖P (xₙ n) - x‖ ^ 2 ≤ ⟪P (xₙ n) - x, xₙ n - x⟫_ℝ := by
    intro n
    simpa [hPx] using
      norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex (xₙ n) x
  have hsq_nonpos : ‖z - x‖ ^ 2 ≤ 0 := by
    exact le_of_tendsto_of_tendsto hsq_left hsq_right (Eventually.of_forall hineq)
  have hsq_zero : ‖z - x‖ ^ 2 = 0 := by
    exact le_antisymm hsq_nonpos (sq_nonneg ‖z - x‖)
  have hz_eq : z = x := by
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq_zero))
  simpa [hz_eq] using hz

end
