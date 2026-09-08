module

public import ReasLib.Analysis.Seminorm.Contracting
public import ReasLib.Analysis.Seminorm.Equivalence
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi

public section

namespace DFPStable

open scoped Matrix

/-- The stable `2 × 2` matrix with entries `-1 / 9`, `2 / 3`, `0`, and `0`. -/
noncomputable def matrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(1 / 9 : ℝ), 2 / 3; 0, 0]

/-- The endomorphism of real coordinate pairs induced by `matrix`. -/
noncomputable def map : Module.End ℝ (Fin 2 → ℝ) :=
  matrix.mulVecLin

/-- The weighted coordinate-sum seminorm `x ↦ ‖x 0‖ + 2 * ‖x 1‖`. -/
noncomputable def weightedSum : Seminorm ℝ (Fin 2 → ℝ) :=
  (normSeminorm ℝ ℝ).comp (LinearMap.proj 0) +
    (2 : NNReal) • (normSeminorm ℝ ℝ).comp (LinearMap.proj 1)

/-- Multiplication by `matrix` in coordinates. -/
theorem matrix_mulVec (x : Fin 2 → ℝ) :
    matrix *ᵥ x = ![-(1 / 9 : ℝ) * x 0 + (2 / 3) * x 1, 0] := by
  -- Evaluate each of the two rows against the two coordinates of `x`.
  ext i
  fin_cases i
  · simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The bundled endomorphism `map` acts by matrix-vector multiplication. -/
theorem map_apply (x : Fin 2 → ℝ) :
    map x = matrix *ᵥ x := by
  -- Pass from the bundled linear endomorphism to its matrix action.
  rw [map, Matrix.mulVecLin_apply]

/-- Evaluation of the explicit weighted coordinate-sum seminorm. -/
theorem weightedSum_apply (x : Fin 2 → ℝ) :
    weightedSum x = ‖x 0‖ + 2 * ‖x 1‖ := by
  -- Evaluate the two coordinate projections and the nonnegative scalar action.
  simp [weightedSum, NNReal.smul_def]

/-- The weighted coordinate-sum seminorm is equivalent to the standard norm seminorm. -/
theorem weightedSum_isEquivalent :
    weightedSum.IsEquivalent (normSeminorm ℝ (Fin 2 → ℝ)) := by
  -- Use constants `1` and `3` for the lower and upper comparisons.
  rw [Seminorm.isEquivalent_iff]
  refine ⟨1, 3, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro x
    rw [weightedSum_apply]
    simp only [NNReal.coe_one, one_mul, NNReal.coe_ofNat, coe_normSeminorm]
    constructor
    · -- Each coordinate norm is bounded by the weighted sum.
      refine (pi_norm_le_iff_of_nonneg ?_).2 ?_
      · positivity
      · intro i
        have hx0 := norm_nonneg (x 0)
        have hx1 := norm_nonneg (x 1)
        have htwo : (0 : ℝ) ≤ 2 := by norm_num
        have hone : ‖x 1‖ ≤ ‖x 0‖ + 2 * ‖x 1‖ := by nlinarith
        fin_cases i
        · exact le_add_of_nonneg_right (mul_nonneg htwo hx1)
        · exact hone
    · -- Both coordinate norms are bounded by the ambient sup norm.
      have hx0 := norm_le_pi_norm x 0
      have hx1 := norm_le_pi_norm x 1
      linarith

/-- The stable endomorphism contracts `weightedSum` at the rational rate `1 / 3 < 1`. -/
theorem weightedSum_contracts :
    (∀ x, weightedSum (map x) ≤ (1 / 3 : ℝ) * weightedSum x) ∧
      (1 / 3 : ℝ) < 1 := by
  constructor
  · intro x
    -- Reduce the contraction estimate to the first coordinate of the matrix product.
    rw [map_apply, matrix_mulVec, weightedSum_apply, weightedSum_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_zero, mul_zero, add_zero]
    calc
      ‖-(1 / 9 : ℝ) * x 0 + (2 / 3) * x 1‖ ≤
          ‖-(1 / 9 : ℝ) * x 0‖ + ‖(2 / 3 : ℝ) * x 1‖ := norm_add_le _ _
      _ = (1 / 9 : ℝ) * ‖x 0‖ + (2 / 3 : ℝ) * ‖x 1‖ := by
        rw [norm_mul, norm_mul]
        norm_num
      _ ≤ (1 / 3 : ℝ) * (‖x 0‖ + 2 * ‖x 1‖) := by
        nlinarith [norm_nonneg (x 0), norm_nonneg (x 1)]
  · -- The displayed rational coefficient is strictly below one.
    norm_num

/-- The explicit contraction bound as an inequality of seminorms. -/
theorem weightedSum_comp_le :
    weightedSum.comp map ≤ (1 / 3 : NNReal) • weightedSum := by
  -- Evaluate the seminorm order pointwise and reuse the coordinate contraction.
  rw [Seminorm.le_def]
  intro x
  simpa only [Seminorm.comp_apply, smul_apply, NNReal.smul_def, smul_eq_mul,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using weightedSum_contracts.1 x

/-- The explicit weighted coordinate-sum seminorm makes `map` contracting below one. -/
theorem weightedSum_isContracting :
    weightedSum.IsContracting map 1 := by
  -- Package the explicit coefficient and the seminorm-order estimate.
  rw [Seminorm.isContracting_iff]
  refine ⟨1 / 3, ?_, ?_⟩
  · norm_num
  · intro x
    simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      weightedSum_contracts.1 x

end DFPStable
