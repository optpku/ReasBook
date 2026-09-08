module

public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

open scoped Matrix

universe u

namespace Matrix.PosDef

/-- Cauchy–Schwarz for the weighted inner product induced by a real positive-definite matrix. -/
theorem dotProduct_mulVec_sq_le {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} (hH : H.PosDef) (x y : n → ℝ) :
    (x ⬝ᵥ (H *ᵥ y)) ^ 2 ≤
      (x ⬝ᵥ (H *ᵥ x)) * (y ⬝ᵥ (H *ᵥ y)) := by
  classical
  have hnonneg : ∀ z : n → ℝ, 0 ≤ Matrix.toBilin' H z z := by
    intro z
    by_cases hz : z = 0
    · subst z
      simp
    · rw [Matrix.toBilin'_apply']
      have hpos : 0 < z ⬝ᵥ (H *ᵥ z) := by
        simpa using hH.dotProduct_mulVec_pos hz
      exact hpos.le
  have hsymm : LinearMap.IsSymm (Matrix.toBilin' H) := by
    apply LinearMap.BilinForm.isSymm_iff.mp
    exact Matrix.isSymm_toBilin'_iff_isSymm.mpr
      (Matrix.isHermitian_iff_isSymm.mp hH.isHermitian)
  simpa only [Matrix.toBilin'_apply'] using
    (Matrix.toBilin' H).apply_sq_le_of_symm hnonneg hsymm x y

end Matrix.PosDef
