/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

variable {I : Type u}

/- Example 2.2: in the Hilbert space `ℓ²(I, ℝ)`, the textbook standard unit vector at `i` is the
canonical element `lp.single 2 i 1`, i.e. the vector that is `1` at `i` and `0` elsewhere. -/
/- The canonical constructor for the textbook standard unit vector is `lp.single`. -/
recall lp.single

/-- The standard unit vector is `1` at its defining index and `0` at every other coordinate. -/
theorem standard_unit_vector_apply [DecidableEq I] (i j : I) :
    ((lp.single 2 i (1 : ℝ) : lp (fun _ : I ↦ ℝ) 2) j = if j = i then 1 else 0) := by
  simp [lp.single_apply, Pi.single_apply, eq_comm]

-- Proof sketch: apply the canonical formula `lp.inner_eq_tsum` for the Hilbert sum `ℓ²(I, ℝ)` and
-- simplify the real inner product on each coordinate to multiplication.
/-- In real `ℓ²(I)`, the inner product is the sum of the pointwise products of the coordinates. -/
theorem l2_inner_eq_tsum_mul (ξ η : lp (fun _ : I ↦ ℝ) 2) :
    inner ℝ ξ η = ∑' j, ξ j * η j := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun j ↦ ?_
  rw [mul_comm]
  rfl
