/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_23
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace ProbabilityTheory

/-- Example 17.24: the Q-matrix of the Poisson process on `ℕ` with rate `α` has jump rate `α`
from `x` to `x + 1`, diagonal entry `-α`, and all other entries `0`. -/
def poissonProcessQMatrix (α : NNReal) : ℕ → ℕ → ℝ :=
  fun x y ↦ if y = x + 1 then (α : ℝ) else if y = x then -(α : ℝ) else 0

-- Proof sketch: unfold `poissonProcessQMatrix` and split on the cases `y = x + 1` and `y = x`;
-- the three resulting values match the difference of the two indicator functions.
/-- The Poisson-process Q-matrix agrees with the textbook formula
`q(x,y) = α (𝟙_{ {y = x + 1} } - 𝟙_{ {y = x} })`. -/
theorem poissonProcessQMatrix_apply (α : NNReal) (x y : ℕ) :
    poissonProcessQMatrix α x y =
      (α : ℝ) * ((if y = x + 1 then (1 : ℝ) else 0) - (if y = x then (1 : ℝ) else 0)) := by
  by_cases hsucc : y = x + 1
  · simp [poissonProcessQMatrix, hsucc]
  · by_cases hself : y = x
    · simp [poissonProcessQMatrix, hself]
    · simp [poissonProcessQMatrix, hsucc, hself]

-- Proof sketch: unfold `poissonProcessQMatrix`; since `x ≠ x + 1`, only the diagonal branch
-- remains and gives `-α`.
/-- On the diagonal, the Poisson-process Q-matrix has value `-α`. -/
theorem poissonProcessQMatrix_self (α : NNReal) (x : ℕ) :
    poissonProcessQMatrix α x x = -(α : ℝ) := by
  simp [poissonProcessQMatrix]

-- Proof sketch: unfold `poissonProcessQMatrix`; at `y = x + 1` the first branch is active, so
-- the value is the jump rate `α`.
/-- The only nonzero off-diagonal entry in row `x` is the jump from `x` to `x + 1`, with value
`α`. -/
theorem poissonProcessQMatrix_succ (α : NNReal) (x : ℕ) :
    poissonProcessQMatrix α x (x + 1) = (α : ℝ) := by
  simp [poissonProcessQMatrix]

-- Proof sketch: the diagonal and successor formulas give the sign conditions, and the row sum is
-- the difference of two singleton indicator series with the same total mass.
/-- The Poisson-process generator is a Q-matrix. -/
instance instIsQMatrixPoissonProcessQMatrix (α : NNReal) :
    IsQMatrix (poissonProcessQMatrix α) where
  offDiag_nonneg := by
    intro x y hxy
    by_cases hsucc : y = x + 1
    · simp [poissonProcessQMatrix, hsucc]
    · have hself : y ≠ x := by
        simpa [eq_comm] using hxy
      simp [poissonProcessQMatrix, hsucc, hself]
  row_hasSum_zero := by
    intro x
    rw [show poissonProcessQMatrix α x =
      fun y ↦ (α : ℝ) * ((if y = x + 1 then (1 : ℝ) else 0) - (if y = x then (1 : ℝ) else 0)) by
      funext y
      exact poissonProcessQMatrix_apply α x y]
    convert HasSum.mul_left (α : ℝ)
      (HasSum.sub (hasSum_ite_eq (x + 1) (1 : ℝ)) (hasSum_ite_eq x (1 : ℝ))) using 1
    simp

end ProbabilityTheory
