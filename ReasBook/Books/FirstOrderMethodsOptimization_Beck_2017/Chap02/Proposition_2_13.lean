/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Matrix

noncomputable section

-- Proof sketch: unfold `support_function` as the supremum of `dotProduct y x` over
-- `x ∈ stdSimplex ℝ (Fin n)`. Since every simplex point is a convex combination of the vertices,
-- each value `dotProduct y x` is bounded above by the largest coordinate of `y`; evaluating at the
-- vertex corresponding to `i : Fin n` gives the reverse inequality and hence the coordinate
-- supremum.
/-- Proposition 2.13: for the unit simplex `Δ_n = stdSimplex ℝ (Fin n)` in `ℝ^n`, the support
function at the Euclidean-dual vector corresponding to `y` is the supremum, equivalently the
maximum, of the coordinates of `y`. -/
theorem support_function_unit_simplex_eq_coordinate_max {n : ℕ} (y : Fin n → ℝ) :
    support_function (stdSimplex ℝ (Fin n)) (dotProductEquiv ℝ (Fin n) y) =
      ⨆ i : Fin n, (y i : EReal) := by
  by_cases h : Nonempty (Fin n)
  · letI := h
    obtain ⟨i0, hi0⟩ := Finite.exists_max y
    rw [support_function_apply]
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨x, hx, rfl⟩
      have hxy : dotProduct y x ≤ y i0 := by
        calc
          dotProduct y x = ∑ i, y i * x i := by simp [dotProduct]
          _ ≤ ∑ i, y i0 * x i := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            exact mul_le_mul_of_nonneg_right (hi0 i) (hx.1 i)
          _ = y i0 * ∑ i, x i := by
            rw [Finset.mul_sum]
          _ = y i0 := by rw [hx.2, mul_one]
      have hxy' : ((dotProduct y x : ℝ) : EReal) ≤ (y i0 : EReal) := by
        exact_mod_cast hxy
      exact hxy'.trans (le_iSup (fun i : Fin n ↦ (y i : EReal)) i0)
    · apply iSup_le
      intro i
      refine le_sSup ?_
      refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
      simp [dotProductEquiv]
  · letI : IsEmpty (Fin n) := not_nonempty_iff.mp h
    simp [support_function_apply, stdSimplex_of_isEmpty_index]

end
