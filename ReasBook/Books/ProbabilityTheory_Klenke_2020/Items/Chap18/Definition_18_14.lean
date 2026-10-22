/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u}

local instance : DecidableEq E := Classical.decEq E

/-- The off-diagonal Metropolis transition weight from `x` to `y`. It is zero on the diagonal and
vanishes whenever the proposal matrix has zero mass from `x` to `y`. -/
def metropolisOffDiagonalEntry (π : E → ℝ≥0∞) (q : E → E → ℝ≥0∞) (x y : E) : ℝ≥0∞ :=
  if x = y then
    0
  else if q x y = 0 then
    0
  else
    q x y * min 1 (π y * q y x / (π x * q x y))

/-- Definition 18.14: the Metropolis matrix of the proposal matrix `q` and weight function `π` is
obtained by assigning the off-diagonal transition weight
`q(x, y) * min (1, π(y) q(y, x) / (π(x) q(x, y)))` and putting the remaining row mass on the
diagonal. -/
def metropolisMatrix (π : E → ℝ≥0∞) (q : E → E → ℝ≥0∞) : E → E → ℝ≥0∞ :=
  fun x y ↦
    if x = y then
      1 - ∑' z : E, metropolisOffDiagonalEntry π q x z
    else
      metropolisOffDiagonalEntry π q x y

/-- Helper for Definition 18.14: away from the diagonal, `metropolisMatrix` is exactly the
off-diagonal Metropolis entry. -/
theorem metropolisMatrix_apply_offDiag
    (π : E → ℝ≥0∞) (q : E → E → ℝ≥0∞) {x y : E} (hxy : x ≠ y) :
    metropolisMatrix π q x y = metropolisOffDiagonalEntry π q x y := by
  -- Off the diagonal, the outer branch of `metropolisMatrix` immediately selects the
  -- off-diagonal Metropolis weight.
  simp [metropolisMatrix, hxy]

-- Proof sketch: unfold `metropolisMatrix`; off the diagonal the outer `if` chooses the
-- off-diagonal branch, and the hypothesis `q x y = 0` then forces the remaining branch of
-- `metropolisOffDiagonalEntry` to be `0`.
/-- If `x ≠ y` and the proposal matrix gives zero mass to `y`, then the Metropolis matrix also has
zero transition mass from `x` to `y`. -/
theorem metropolisMatrix_apply_offDiag_of_eq_zero
    (π : E → ℝ≥0∞) (q : E → E → ℝ≥0∞) {x y : E} (hxy : x ≠ y) (hq : q x y = 0) :
    metropolisMatrix π q x y = 0 := by
  -- First move to the stable off-diagonal API, then simplify the zero-proposal branch.
  rw [metropolisMatrix_apply_offDiag π q hxy]
  simp [metropolisOffDiagonalEntry, hxy, hq]

-- Proof sketch: unfold `metropolisMatrix`; off the diagonal the value is the off-diagonal
-- Metropolis entry, and the positivity hypothesis rules out the zero-proposal branch, leaving the
-- acceptance-factor formula.
/-- If `x ≠ y` and the proposal matrix gives positive mass to `y`, then the off-diagonal
Metropolis entry is the proposal mass times the usual acceptance factor. -/
theorem metropolisMatrix_apply_offDiag_of_pos
    (π : E → ℝ≥0∞) (q : E → E → ℝ≥0∞) {x y : E} (hxy : x ≠ y) (hq : 0 < q x y) :
    metropolisMatrix π q x y =
      q x y * min 1 (π y * q y x / (π x * q x y)) := by
  -- The positive proposal mass removes the zero branch in `metropolisOffDiagonalEntry`.
  rw [metropolisMatrix_apply_offDiag π q hxy]
  simp [metropolisOffDiagonalEntry, hxy, ne_of_gt hq]

-- Proof sketch: unfold `metropolisMatrix`; on the diagonal the outer `if` chooses the branch that
-- subtracts the total off-diagonal Metropolis mass from `1`.
/-- The diagonal entry of the Metropolis matrix is the remaining row mass after all off-diagonal
Metropolis transitions from `x` have been accounted for. -/
theorem metropolisMatrix_apply_diag
    (π : E → ℝ≥0∞) (q : E → E → ℝ≥0∞) (x : E) :
    metropolisMatrix π q x x = 1 - ∑' z : E, metropolisOffDiagonalEntry π q x z := by
  -- On the diagonal, `metropolisMatrix` is defined to be the remaining row mass.
  simp [metropolisMatrix]

/-- Helper for Definition 18.14: each off-diagonal Metropolis weight is bounded above by the
corresponding proposal mass. -/
theorem metropolisOffDiagonalEntry_le_proposal
    (π : E → ℝ≥0∞) (q : E → E → ℝ≥0∞) (x y : E) :
    metropolisOffDiagonalEntry π q x y ≤ q x y := by
  -- Split according to the diagonal case and the zero-proposal case; the only remaining branch
  -- uses `min 1 _ ≤ 1`.
  by_cases hxy : x = y
  · simp [metropolisOffDiagonalEntry, hxy]
  · by_cases hqxy : q x y = 0
    · simp [metropolisOffDiagonalEntry, hxy, hqxy]
    · rw [metropolisOffDiagonalEntry, if_neg hxy, if_neg hqxy]
      calc
        q x y * min 1 (π y * q y x / (π x * q x y)) ≤ q x y * 1 := by
          exact mul_le_mul_right (min_le_left _ _) (q x y)
        _ = q x y := by simp

-- Proof sketch: for each row `x`, every off-diagonal Metropolis weight is bounded by the
-- corresponding proposal weight `q x y`, so the off-diagonal row sum is at most `1` because `q`
-- is stochastic. The diagonal entry was defined as the remaining mass `1 - ∑' y,
-- metropolisOffDiagonalEntry π q x y`, hence the total row sum is exactly `1`.
/-- If the proposal matrix `q` is stochastic, then the Metropolis matrix built from `q` and `π`
is again stochastic. -/
theorem metropolisMatrix_isStochasticMatrix
    (π : E → ℝ≥0∞) (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) :
    IsStochasticMatrix (metropolisMatrix π q) := by
  intro x
  set S : ℝ≥0∞ := ∑' z : E, metropolisOffDiagonalEntry π q x z
  have hS_le_one : S ≤ 1 := by
    -- Compare the Metropolis row termwise with the proposal row and use stochasticity of `q`.
    calc
      S = ∑' z : E, metropolisOffDiagonalEntry π q x z := by rfl
      _ ≤ ∑' z : E, q x z := by
        refine ENNReal.tsum_le_tsum ?_
        intro z
        exact metropolisOffDiagonalEntry_le_proposal π q x z
      _ = 1 := hq x
  have hOffDiagSum :
      ∑' y : E, ite (y = x) 0 (metropolisMatrix π q x y) =
        ∑' y : E, metropolisOffDiagonalEntry π q x y := by
    -- After splitting off the diagonal term, the remaining `ite`-sum is exactly the
    -- off-diagonal Metropolis sum.
    refine tsum_congr fun y ↦ ?_
    by_cases hy : y = x
    · simp [hy, metropolisOffDiagonalEntry]
    · rw [if_neg hy]
      rw [metropolisMatrix_apply_offDiag
        (π := π) (q := q) (x := x) (y := y) (fun hxy ↦ hy hxy.symm)]
  -- Split the row sum at `x`, rewrite the diagonal and off-diagonal pieces, and then use
  -- `S ≤ 1` to cancel the truncated subtraction.
  calc
    ∑' y : E, metropolisMatrix π q x y
      = metropolisMatrix π q x x + ∑' y : E, ite (y = x) 0 (metropolisMatrix π q x y) := by
          rw [ENNReal.tsum_eq_add_tsum_ite x]
    _ = (1 - S) + ∑' y : E, ite (y = x) 0 (metropolisMatrix π q x y) := by
          simpa [S] using
            congrArg
              (fun t : ℝ≥0∞ ↦ t + ∑' y : E, ite (y = x) 0 (metropolisMatrix π q x y))
              (metropolisMatrix_apply_diag π q x)
    _ = (1 - S) + ∑' y : E, metropolisOffDiagonalEntry π q x y := by
          rw [hOffDiagSum]
    _ = (1 - S) + S := by simp [S]
    _ = 1 := by simpa [add_comm] using (tsub_add_cancel_of_le hS_le_one)

section DiscreteState

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- The discrete kernel associated to the Metropolis matrix built from the target distribution `π`
and proposal matrix `q`. The matrix entries use the singleton masses of `π` as the target
weights. -/
def metropolisKernel (π : ProbabilityMeasure E) (q : E → E → ℝ≥0∞) : Kernel E E :=
  discreteMatrixKernel (metropolisMatrix (fun x : E ↦ (π : Measure E) ({x} : Set E)) q)

-- Proof sketch: unfold `metropolisKernel`; it is defined by applying `discreteMatrixKernel` to
-- the Metropolis matrix whose weights are the singleton masses of `π`.
/-- The defining formula for `metropolisKernel`. -/
theorem metropolisKernel_def (π : ProbabilityMeasure E) (q : E → E → ℝ≥0∞) :
    metropolisKernel π q =
      discreteMatrixKernel
        (metropolisMatrix (fun x : E ↦ (π : Measure E) ({x} : Set E)) q) := by
  -- This is the defining equation obtained by unfolding `metropolisKernel`.
  rfl

/-- If the proposal matrix is stochastic, then the discrete kernel associated with the Metropolis
matrix is a Markov kernel. -/
theorem metropolisKernel_isMarkovKernel
    (π : ProbabilityMeasure E) (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) :
    IsMarkovKernel (metropolisKernel π q) := by
  simpa [metropolisKernel_def] using
    (discreteMatrixKernel_isMarkovKernel
      (metropolisMatrix (fun x : E ↦ (π : Measure E) ({x} : Set E)) q)
      (metropolisMatrix_isStochasticMatrix
        (fun x : E ↦ (π : Measure E) ({x} : Set E)) q hq))

end DiscreteState

end ProbabilityTheory
