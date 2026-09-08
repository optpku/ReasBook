module

public import ReasLib.Optimization.DFP.InverseUpdate.QuadraticForm

public section

open scoped Matrix

universe u

namespace Matrix

/-- Simultaneously scaling both vectors in a secant pair scales the quadratic
denominator involving the base matrix by the square of the scalar. -/
theorem inverseDFPUpdate_metric_denominator_smul {n : Type u} [Fintype n]
    (H : Matrix n n ℝ) (y : n → ℝ) (c : ℝ) :
    (c • y) ⬝ᵥ (H *ᵥ (c • y)) = c ^ 2 * (y ⬝ᵥ (H *ᵥ y)) := by
  -- Pull both scalar factors through the matrix action and dot product.
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
  ring

/-- Simultaneously scaling both vectors in a secant pair scales its curvature
denominator by the square of the scalar. -/
theorem inverseDFPUpdate_secant_denominator_smul {n : Type u} [Fintype n]
    (s y : n → ℝ) (c : ℝ) :
    (c • s) ⬝ᵥ (c • y) = c ^ 2 * (s ⬝ᵥ y) := by
  -- Pull both scalar factors out of the secant curvature pairing.
  rw [smul_dotProduct, dotProduct_smul]
  ring

/-- The inverse-form DFP update is unchanged when both vectors of the secant
pair are multiplied by the same nonzero scalar. -/
theorem inverseDFPUpdate_smul_pair {n : Type u} [Fintype n]
    (H : Matrix n n ℝ) (s y : n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    inverseDFPUpdate H (c • s) (c • y) = inverseDFPUpdate H s y := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  -- Cancel the common square without assuming that the remaining factor is nonzero.
  have hscale (a b : ℝ) : (c ^ 2 * a)⁻¹ * (c ^ 2 * b) = a⁻¹ * b := by
    by_cases ha : a = 0
    · simp [ha]
    · field_simp [hc2, ha]
  -- Apply the cancellation separately to the two rank-one corrections.
  ext i j
  rw [inverseDFPUpdate_apply, inverseDFPUpdate_apply,
    inverseDFPUpdate_metric_denominator_smul,
    inverseDFPUpdate_secant_denominator_smul]
  simp only [mulVec_smul, smul_vecMul, Pi.smul_apply, smul_eq_mul]
  have hmetric :
      (c ^ 2 * (y ⬝ᵥ (H *ᵥ y)))⁻¹ *
          ((c * (H *ᵥ y) i) * (c * (y ᵥ* H) j)) =
        (y ⬝ᵥ (H *ᵥ y))⁻¹ * ((H *ᵥ y) i * (y ᵥ* H) j) := by
    calc
      (c ^ 2 * (y ⬝ᵥ (H *ᵥ y)))⁻¹ *
          ((c * (H *ᵥ y) i) * (c * (y ᵥ* H) j)) =
        (c ^ 2 * (y ⬝ᵥ (H *ᵥ y)))⁻¹ *
          (c ^ 2 * ((H *ᵥ y) i * (y ᵥ* H) j)) := by ring
      _ = (y ⬝ᵥ (H *ᵥ y))⁻¹ * ((H *ᵥ y) i * (y ᵥ* H) j) :=
        hscale _ _
  have hsecant :
      (c ^ 2 * (s ⬝ᵥ y))⁻¹ * ((c * s i) * (c * s j)) =
        (s ⬝ᵥ y)⁻¹ * (s i * s j) := by
    calc
      (c ^ 2 * (s ⬝ᵥ y))⁻¹ * ((c * s i) * (c * s j)) =
          (c ^ 2 * (s ⬝ᵥ y))⁻¹ * (c ^ 2 * (s i * s j)) := by ring
      _ = (s ⬝ᵥ y)⁻¹ * (s i * s j) := hscale _ _
  rw [hmetric, hsecant]

/-- A common nonzero scale preserves exactly the two nonvanishing denominator
conditions used by the inverse-form DFP update. -/
theorem inverseDFPUpdate_denominators_ne_zero_smul_iff {n : Type u} [Fintype n]
    (H : Matrix n n ℝ) (s y : n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    ((c • y) ⬝ᵥ (H *ᵥ (c • y)) ≠ 0 ∧ (c • s) ⬝ᵥ (c • y) ≠ 0) ↔
      (y ⬝ᵥ (H *ᵥ y) ≠ 0 ∧ s ⬝ᵥ y ≠ 0) := by
  -- Rewrite both scaled denominators and cancel the nonzero square factor.
  rw [inverseDFPUpdate_metric_denominator_smul,
    inverseDFPUpdate_secant_denominator_smul]
  simp [pow_ne_zero 2 hc]

/-- A common nonzero scale preserves positivity of the secant curvature. -/
theorem inverseDFPUpdate_secant_denominator_pos_smul_iff {n : Type u} [Fintype n]
    (s y : n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    0 < (c • s) ⬝ᵥ (c • y) ↔ 0 < s ⬝ᵥ y := by
  -- The common square factor is strictly positive.
  rw [inverseDFPUpdate_secant_denominator_smul]
  exact mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hc)

/-- Under the original nonvanishing denominator hypotheses, the update formed
from a scaled secant pair sends `c • y` to `c • s`. -/
theorem inverseDFPUpdate_mulVec_smul_secant {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} {s y : n → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hHy : y ⬝ᵥ (H *ᵥ y) ≠ 0) (hsy : s ⬝ᵥ y ≠ 0) :
    inverseDFPUpdate H (c • s) (c • y) *ᵥ (c • y) = c • s := by
  -- Replace the scaled update and pull the scalar through its matrix action.
  rw [inverseDFPUpdate_smul_pair H s y hc, mulVec_smul,
    inverseDFPUpdate_mulVec_secant hHy hsy]

namespace PosDef

/-- Positive definiteness and positive original curvature give positive
denominators for every common nonzero scaling of the secant pair. -/
theorem inverseDFPUpdate_denominators_pos_smul {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} {s y : n → ℝ} (hH : H.PosDef) (hsy : 0 < s ⬝ᵥ y)
    {c : ℝ} (hc : c ≠ 0) :
    0 < (c • y) ⬝ᵥ (H *ᵥ (c • y)) ∧ 0 < (c • s) ⬝ᵥ (c • y) := by
  have hc2pos : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  -- Each original positive denominator remains positive after multiplication by `c²`.
  rw [inverseDFPUpdate_metric_denominator_smul,
    inverseDFPUpdate_secant_denominator_smul]
  exact ⟨mul_pos hc2pos (hH.inverseDFPUpdate_denominator_pos hsy),
    mul_pos hc2pos hsy⟩

/-- Positive definiteness of an inverse-form DFP update is invariant under a
common nonzero scaling of its secant pair. -/
theorem inverseDFPUpdate_smul_pair {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} {s y : n → ℝ} (hH : H.PosDef) (hsy : 0 < s ⬝ᵥ y)
    {c : ℝ} (hc : c ≠ 0) :
    (Matrix.inverseDFPUpdate H (c • s) (c • y)).PosDef := by
  -- Transport positive definiteness across invariance of the scaled update.
  rw [Matrix.inverseDFPUpdate_smul_pair H s y hc]
  exact hH.inverseDFPUpdate hsy

end PosDef

end Matrix
