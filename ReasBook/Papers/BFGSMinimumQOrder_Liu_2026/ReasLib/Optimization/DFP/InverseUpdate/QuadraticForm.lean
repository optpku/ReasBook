module

public import ReasLib.Optimization.DFP.InverseUpdate
public import ReasLib.LinearAlgebra.Matrix.PosDef.CauchySchwarz

public section

open scoped Matrix

universe u

namespace Matrix

/-- The public entrywise formula recovers the opaque inverse-form DFP definition. -/
private theorem inverseDFPUpdate_eq_formula {n : Type u} [Fintype n]
    (H : Matrix n n ℝ) (s y : n → ℝ) :
    inverseDFPUpdate H s y =
      H - (y ⬝ᵥ (H *ᵥ y))⁻¹ • vecMulVec (H *ᵥ y) (y ᵥ* H) +
        (s ⬝ᵥ y)⁻¹ • vecMulVec s s := by
  ext i j
  simp [inverseDFPUpdate_apply, vecMulVec_apply]

/-- The action of the inverse-form DFP update on a vector, expanded at one coordinate. -/
theorem inverseDFPUpdate_mulVec_apply {n : Type u} [Fintype n] (H : Matrix n n ℝ)
    (s y x : n → ℝ) (i : n) :
    (inverseDFPUpdate H s y *ᵥ x) i =
      (H *ᵥ x) i - (y ⬝ᵥ (H *ᵥ y))⁻¹ *
        ((H *ᵥ y) i * ((y ᵥ* H) ⬝ᵥ x)) +
        (s ⬝ᵥ y)⁻¹ * (s i * (s ⬝ᵥ x)) := by
  -- Expand the update action and evaluate each rank-one matrix on `x`.
  simp only [inverseDFPUpdate_eq_formula, add_mulVec, sub_mulVec, smul_mulVec,
    vecMulVec_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    op_smul_eq_mul, smul_eq_mul]

/-- The quadratic form of an inverse-form DFP update, before using symmetry of the
base matrix. -/
theorem inverseDFPUpdate_dotProduct_mulVec {n : Type u} [Fintype n]
    (H : Matrix n n ℝ) (s y x : n → ℝ) :
    x ⬝ᵥ (inverseDFPUpdate H s y *ᵥ x) =
      x ⬝ᵥ (H *ᵥ x) - (y ⬝ᵥ (H *ᵥ y))⁻¹ *
        ((x ⬝ᵥ (H *ᵥ y)) * ((y ᵥ* H) ⬝ᵥ x)) +
        (s ⬝ᵥ y)⁻¹ * ((x ⬝ᵥ s) * (s ⬝ᵥ x)) := by
  -- Matrix and dot-product linearity separate the three quadratic contributions.
  simp only [inverseDFPUpdate_eq_formula, add_mulVec, sub_mulVec, smul_mulVec,
    vecMulVec_mulVec, dotProduct_add, dotProduct_sub, dotProduct_smul,
    op_smul_eq_mul, smul_eq_mul]

/-- For a Hermitian real base matrix, the quadratic form of the inverse-form DFP
update is the usual difference and sum of two scalar squares. -/
theorem inverseDFPUpdate_dotProduct_mulVec_of_isHermitian {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} (hH : H.IsHermitian) (s y x : n → ℝ) :
    x ⬝ᵥ (inverseDFPUpdate H s y *ᵥ x) =
      x ⬝ᵥ (H *ᵥ x) - (y ⬝ᵥ (H *ᵥ y))⁻¹ * (x ⬝ᵥ (H *ᵥ y)) ^ 2 +
        (s ⬝ᵥ y)⁻¹ * (x ⬝ᵥ s) ^ 2 := by
  -- Hermitian symmetry identifies the row factor with `H *ᵥ y`.
  have hyH : y ᵥ* H = H *ᵥ y := by
    have hstar := Matrix.star_mulVec H y
    rw [hH.eq] at hstar
    simpa using hstar.symm
  -- Substitute the row identity and commute the remaining real dot products.
  rw [inverseDFPUpdate_dotProduct_mulVec, hyH,
    dotProduct_comm (H *ᵥ y) x, dotProduct_comm s x]
  ring

/-- If both update denominators are nonzero, the inverse-form DFP update sends
the secant vector `y` to the displacement vector `s`. -/
theorem inverseDFPUpdate_mulVec_secant {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} {s y : n → ℝ} (hHy : y ⬝ᵥ (H *ᵥ y) ≠ 0)
    (hsy : s ⬝ᵥ y ≠ 0) :
    inverseDFPUpdate H s y *ᵥ y = s := by
  -- Check the secant equation coordinatewise using the expanded update action.
  funext i
  rw [inverseDFPUpdate_mulVec_apply, ← dotProduct_mulVec]
  field_simp [hHy, hsy]
  ring

/-- An inverse-form DFP update of a Hermitian real matrix is Hermitian. -/
theorem inverseDFPUpdate_isHermitian {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} (hH : H.IsHermitian) (s y : n → ℝ) :
    (inverseDFPUpdate H s y).IsHermitian := by
  -- Symmetry turns the metric correction into a scaled self outer product.
  have hyH : y ᵥ* H = H *ᵥ y := by
    have hstar := Matrix.star_mulVec H y
    rw [hH.eq] at hstar
    simpa using hstar.symm
  have hmetricOuter : (vecMulVec (H *ᵥ y) (y ᵥ* H)).IsHermitian := by
    rw [hyH]
    simp [Matrix.IsHermitian]
  have hsecantOuter : (vecMulVec s s).IsHermitian := by
    simp [Matrix.IsHermitian]
  -- Hermitian matrices are closed under real scaling, subtraction, and addition.
  rw [inverseDFPUpdate_eq_formula]
  exact (hH.sub (hmetricOuter.smul (IsSelfAdjoint.all _))).add
    (hsecantOuter.smul (IsSelfAdjoint.all _))

namespace PosDef

/-- Positive definiteness and positive secant curvature make both scalar
denominators of the inverse-form DFP update positive. -/
theorem inverseDFPUpdate_denominators_pos {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} {s y : n → ℝ} (hH : H.PosDef) (hsy : 0 < s ⬝ᵥ y) :
    0 < y ⬝ᵥ (H *ᵥ y) ∧ 0 < s ⬝ᵥ y := by
  exact ⟨hH.inverseDFPUpdate_denominator_pos hsy, hsy⟩

/-- Removing the rank-one component in the `H *ᵥ y` direction leaves a
nonnegative quadratic form. -/
theorem inverseDFPUpdate_projectedQuadratic_nonneg {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} (hH : H.PosDef) {y : n → ℝ} (hy : y ≠ 0) (x : n → ℝ) :
    0 ≤ x ⬝ᵥ (H *ᵥ x) -
      (y ⬝ᵥ (H *ᵥ y))⁻¹ * (x ⬝ᵥ (H *ᵥ y)) ^ 2 := by
  apply sub_nonneg.mpr
  apply (inv_mul_le_iff₀ (by simpa using hH.dotProduct_mulVec_pos hy)).2
  simpa only [mul_comm] using hH.dotProduct_mulVec_sq_le x y

/-- The pointwise quadratic-form positivity needed to construct
`Matrix.PosDef.inverseDFPUpdate`. -/
theorem inverseDFPUpdate_dotProduct_mulVec_pos {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} {s y x : n → ℝ} (hH : H.PosDef)
    (hsy : 0 < s ⬝ᵥ y) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (Matrix.inverseDFPUpdate H s y *ᵥ x) := by
  simpa using (hH.inverseDFPUpdate hsy).dotProduct_mulVec_pos hx

end PosDef

end Matrix
