/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

local instance example18_6DecidableEq : DecidableEq E := Classical.decEq E

/-- Example 18.6: the independent coalescent transition matrix on `E × E`; away from the diagonal
the two coordinates evolve independently with transition matrix `p`, and once the two coordinates
meet they move together along the diagonal. -/
def independentCoalescentMatrix (p : E → E → ℝ≥0∞) : (E × E) → (E × E) → ℝ≥0∞
  | (x₁, y₁), (x₂, y₂) =>
      if x₁ = y₁ then
        if x₂ = y₂ then p x₁ x₂ else 0
      else
        p x₁ x₂ * p y₁ y₂

-- Proof sketch: unfold `independentCoalescentMatrix`; when the starting coordinates are distinct,
-- the definition immediately reduces to the product of the two one-step transition probabilities.
/-- Off the diagonal, the independent coalescent uses the product transition law of two
independent copies of the chain with transition matrix `p`. -/
theorem independentCoalescentMatrix_apply_of_ne
    (p : E → E → ℝ≥0∞) {x₁ y₁ x₂ y₂ : E} (h : x₁ ≠ y₁) :
    independentCoalescentMatrix p (x₁, y₁) (x₂, y₂) = p x₁ x₂ * p y₁ y₂ := by
  -- The off-diagonal hypothesis selects the independent-product branch of the definition.
  simp [independentCoalescentMatrix, h]

-- Proof sketch: unfold `independentCoalescentMatrix`; on the diagonal the outer `if` uses
-- `x = x`, and the inner `if` reduces the diagonal-to-diagonal transition to `p x z`.
/-- Once the two coordinates have coalesced at `x`, a diagonal transition to `(z, z)` has
probability `p x z`. -/
theorem independentCoalescentMatrix_apply_diag
    (p : E → E → ℝ≥0∞) (x z : E) :
    independentCoalescentMatrix p (x, x) (z, z) = p x z := by
  -- On the diagonal, both `if` tests reduce to equality and the entry becomes `p x z`.
  simp [independentCoalescentMatrix]

-- Proof sketch: unfold `independentCoalescentMatrix`; on the diagonal the inner `if` forces every
-- transition to a non-diagonal state to have probability `0`.
/-- Once the two coordinates have coalesced, the independent coalescent cannot leave the diagonal.
-/
theorem independentCoalescentMatrix_apply_diag_of_ne
    (p : E → E → ℝ≥0∞) {x x₂ y₂ : E} (h : x₂ ≠ y₂) :
    independentCoalescentMatrix p (x, x) (x₂, y₂) = 0 := by
  -- A diagonal state can only transition to another diagonal state.
  simp [independentCoalescentMatrix, h]

-- Proof sketch: split the row indexed by `(x, y)` into the off-diagonal case `x ≠ y`, where the
-- row sum factors as the product of two stochastic row sums, and the diagonal case `x = y`, where
-- only the diagonal states `(z, z)` contribute and the row sum is the single stochastic row sum
-- of `p`.
/-- The independent coalescent matrix is stochastic whenever `p` is stochastic. -/
theorem independentCoalescentMatrix_isStochasticMatrix
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) :
    IsStochasticMatrix (independentCoalescentMatrix p) := by
  classical
  rintro ⟨x, y⟩
  by_cases hxy : x = y
  · subst hxy
    -- On the diagonal, each slice over the second coordinate has a single surviving term.
    have hslice : ∀ z : E, ∑' w : E, independentCoalescentMatrix p (x, x) (z, w) = p x z := by
      intro z
      rw [tsum_eq_single z]
      · rw [independentCoalescentMatrix_apply_diag]
      · intro w hw
        rw [independentCoalescentMatrix_apply_diag_of_ne (p := p)]
        exact fun hzw => hw hzw.symm
    -- Rewrite the product-state row sum as iterated sums and collapse the diagonal slices.
    calc
      ∑' s : E × E, independentCoalescentMatrix p (x, x) s =
          ∑' z : E, ∑' w : E, independentCoalescentMatrix p (x, x) (z, w) := by
            simpa using
              (ENNReal.tsum_prod' (f := fun s : E × E => independentCoalescentMatrix p (x, x) s))
      _ = ∑' z : E, p x z := by
            refine tsum_congr hslice
      _ = 1 := hp x
  · -- Off the diagonal, the row factorizes as the product of the two original rows.
    calc
      ∑' s : E × E, independentCoalescentMatrix p (x, y) s =
          ∑' z : E, ∑' w : E, independentCoalescentMatrix p (x, y) (z, w) := by
            simpa using
              (ENNReal.tsum_prod' (f := fun s : E × E => independentCoalescentMatrix p (x, y) s))
      _ = ∑' z : E, ∑' w : E, p x z * p y w := by
            refine tsum_congr fun z => ?_
            refine tsum_congr fun w => ?_
            rw [independentCoalescentMatrix_apply_of_ne (p := p) hxy]
      _ = ∑' z : E, p x z * ∑' w : E, p y w := by
            refine tsum_congr fun z => ?_
            rw [ENNReal.tsum_mul_left]
      _ = ∑' z : E, p x z * 1 := by simp [hp y]
      _ = (∑' z : E, p x z) * 1 := by rw [ENNReal.tsum_mul_right]
      _ = 1 := by simp [hp x]

end ProbabilityTheory
