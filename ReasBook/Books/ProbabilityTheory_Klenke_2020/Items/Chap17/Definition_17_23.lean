/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

namespace ProbabilityTheory

variable {E : Type u}

/-- Definition 17.23: a matrix `q` on the state space `E` is a Q-matrix if each off-diagonal
entry is nonnegative and every row has total sum `0`. The diagonal entries are then automatically
nonpositive. This is the infinitesimal generator of the transition semigroup of the continuous-time
Markov process.
-/
class IsQMatrix (q : E → E → ℝ) : Prop where
  /-- The off-diagonal entries of a Q-matrix are nonnegative jump rates. -/
  offDiag_nonneg : ∀ ⦃x y : E⦄, x ≠ y → 0 ≤ q x y
  /-- Every row of a Q-matrix has total sum `0`. -/
  row_hasSum_zero : ∀ x : E, HasSum (q x) 0

-- Proof sketch: subtract the diagonal singleton series from the row sum. The remaining off-diagonal
-- series has nonnegative terms, so its sum `-q x x` is nonnegative.
/-- The diagonal entries of a Q-matrix are nonpositive. -/
theorem IsQMatrix.diag_nonpos {q : E → E → ℝ} (hq : IsQMatrix q) (x : E) : q x x ≤ 0 := by
  classical
  have hOffDiagHasSum : HasSum (fun y : E ↦ if y = x then 0 else q x y) (-q x x) := by
    convert (hq.row_hasSum_zero x).sub (hasSum_ite_eq x (q x x)) using 1
    · ext y
      by_cases hy : y = x <;> simp [hy]
    · ring
  have hOffDiagNonneg : 0 ≤ ∑' y : E, if y = x then 0 else q x y := by
    refine tsum_nonneg fun y ↦ ?_
    by_cases hy : y = x
    · simp [hy]
    · simpa [hy] using hq.offDiag_nonneg <| by simpa [eq_comm] using hy
  have hneg : 0 ≤ -q x x := by
    simpa [hOffDiagHasSum.tsum_eq] using hOffDiagNonneg
  linarith

-- Proof sketch: `HasSum` of a row at `0` is exactly the statement that its `tsum` exists and is
-- equal to `0`.
/-- Every row of a Q-matrix has `tsum` equal to `0`. -/
theorem IsQMatrix.row_tsum_eq_zero {q : E → E → ℝ} (hq : IsQMatrix q) (x : E) :
    ∑' y : E, q x y = 0 := by
  -- Pass from the rowwise `HasSum` statement directly to the corresponding `tsum` identity.
  simpa using (hq.row_hasSum_zero x).tsum_eq

-- Proof sketch: the zero matrix has nonnegative off-diagonal entries, and each row has `HasSum`
-- equal to `0`.
/-- The zero matrix is a Q-matrix. -/
instance instIsQMatrixZero : IsQMatrix (fun _ _ : E ↦ 0) where
  offDiag_nonneg := by
    -- Every off-diagonal entry of the zero matrix is literally `0`.
    intro x y hxy
    simp
  row_hasSum_zero := by
    -- Each row is the constant-zero series, whose sum is `0`.
    intro x
    simpa using (hasSum_zero : HasSum (fun _ : E ↦ (0 : ℝ)) 0)

end ProbabilityTheory
