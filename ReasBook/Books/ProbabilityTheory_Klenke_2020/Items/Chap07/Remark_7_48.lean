/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- Remark 7.48: a continuous linear functional on a real normed space is bounded on a
neighborhood of `0`, hence admits a global linear bound and therefore has finite operator norm.
This is the canonical boundedness theorem `ContinuousLinearMap.bound`. -/
recall ContinuousLinearMap.bound

/-- Remark 7.48: for every `δ > 0`, a continuous linear functional admits some `ε > 0` such that
`‖F‖ ≤ δ / ε`; in particular, its operator norm is finite. We state this on the canonical dual
space `StrongDual ℝ V`. -/
theorem strongDual_exists_pos_opNorm_le_div (F : StrongDual ℝ V) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ‖F‖ ≤ δ / ε := by
  obtain ⟨C, hC, hC_bound⟩ := F.bound
  refine ⟨δ / C, div_pos hδ hC, ?_⟩
  calc
    ‖F‖ ≤ C := F.opNorm_le_bound hC.le hC_bound
    _ = δ / (δ / C) := by
      field_simp [hδ.ne', hC.ne']

end
