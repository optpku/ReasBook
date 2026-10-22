/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition 2.48: if a sequence in a real Hilbert space is asymptotic in norm to an
orthonormal sequence, then it converges weakly to `0`. -/
-- Proof sketch: Example 2.32.1 gives weak convergence of the orthonormal comparison sequence to
-- `0`. The perturbation `x n - y n` converges strongly to `0` because its norm tends to `0`, so
-- its image in `WeakSpace ℝ H` also converges to `0`. Adding the two weakly null sequences yields
-- the result.
theorem tendsto_zero_weakly_of_orthonormal_of_norm_sub_tendsto_zero
    (x y : ℕ → H) (hy : Orthonormal ℝ y)
    (hxy : Tendsto (fun n ↦ ‖x n - y n‖) atTop (nhds (0 : ℝ))) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H)) := by
  have hyWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (y n)) atTop (nhds (0 : WeakSpace ℝ H)) :=
    orthonormal_sequence_tendsto_zero_weakly y hy
  have hsubStrong : Tendsto (fun n ↦ x n - y n) atTop (nhds (0 : H)) := by
    simpa using (tendsto_zero_iff_norm_tendsto_zero).2 hxy
  have hsubWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n - y n)) atTop (nhds (0 : WeakSpace ℝ H)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto 0).comp hsubStrong
  have hsum :
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n - y n) + toWeakSpace ℝ H (y n))
        atTop (nhds (0 + 0 : WeakSpace ℝ H)) :=
    hsubWeak.add hyWeak
  simpa [sub_add_cancel] using hsum
