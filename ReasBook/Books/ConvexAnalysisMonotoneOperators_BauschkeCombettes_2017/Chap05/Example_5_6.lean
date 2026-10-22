/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_32_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Example 5.6: an orthonormal sequence is Fejér monotone with respect to `{0}`. -/
-- Proof sketch: the only point of `{0}` is `0`, and orthonormality gives `‖x n‖ = 1` for every
-- `n`, so the one-step distance inequality to `0` is an equality.
theorem orthonormal_sequence_fejer_monotone_with_respect_to_singleton_zero
    (x : ℕ → H) (hx : Orthonormal ℝ x) :
    FejerMonotone ({0} : Set H) x := by
  intro z hz n
  rw [Set.mem_singleton_iff] at hz
  subst z
  simp [dist_eq_norm, hx.norm_eq_one]

/- Companion recall: the weak-convergence clause of Example 5.6 is exactly the earlier theorem
that an orthonormal sequence converges weakly to `0`. -/
recall orthonormal_sequence_tendsto_zero_weakly

/- Companion recall: the non-strong-convergence clause of Example 5.6 is exactly the earlier
theorem that an orthonormal sequence does not converge strongly to `0`. -/
recall orthonormal_sequence_not_tendsto_zero_strongly
