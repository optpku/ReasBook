module

public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

open scoped Matrix

namespace Matrix

/-- The inverse-form DFP rank-two update determined by a matrix and a secant pair. -/
noncomputable def inverseDFPUpdate {n : Type u} [Fintype n] (H : Matrix n n ℝ) (s y : n → ℝ) :
    Matrix n n ℝ :=
  H - (y ⬝ᵥ (H *ᵥ y))⁻¹ • vecMulVec (H *ᵥ y) (y ᵥ* H) +
    (s ⬝ᵥ y)⁻¹ • vecMulVec s s

/-- The inverse-form DFP update is the sum of its base matrix and the two
rank-one correction terms. -/
theorem inverseDFPUpdate_def {n : Type u} [Fintype n]
    (H : Matrix n n ℝ) (s y : n → ℝ) :
    inverseDFPUpdate H s y =
      H - (y ⬝ᵥ (H *ᵥ y))⁻¹ • vecMulVec (H *ᵥ y) (y ᵥ* H) +
        (s ⬝ᵥ y)⁻¹ • vecMulVec s s := by
  rfl

/-- The entrywise formula for the inverse-form DFP update. -/
theorem inverseDFPUpdate_apply {n : Type u} [Fintype n] (H : Matrix n n ℝ)
    (s y : n → ℝ) (i j : n) :
    inverseDFPUpdate H s y i j =
      H i j - (y ⬝ᵥ (H *ᵥ y))⁻¹ * ((H *ᵥ y) i * (y ᵥ* H) j) +
        (s ⬝ᵥ y)⁻¹ * (s i * s j) := by
  -- Evaluate the two rank-one matrices and their scalar multiples at `(i, j)`.
  simp [inverseDFPUpdate, vecMulVec_apply]

namespace PosDef

/-- Positive definiteness and positive curvature make the quadratic denominator positive. -/
theorem inverseDFPUpdate_denominator_pos {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} {s y : n → ℝ} (hH : H.PosDef) (hsy : 0 < s ⬝ᵥ y) :
    0 < y ⬝ᵥ (H *ᵥ y) := by
  -- Positive secant curvature rules out the zero secant vector.
  have hy : y ≠ 0 := by
    intro hy
    subst y
    simp at hsy
  -- Positive definiteness is strict on that nonzero vector.
  simpa using hH.dotProduct_mulVec_pos hy

/-- Both scalar denominators in the inverse-form DFP update are nonzero. -/
theorem inverseDFPUpdate_denominators_ne_zero {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} {s y : n → ℝ} (hH : H.PosDef) (hsy : 0 < s ⬝ᵥ y) :
    y ⬝ᵥ (H *ᵥ y) ≠ 0 ∧ s ⬝ᵥ y ≠ 0 := by
  -- Each denominator is nonzero because its corresponding curvature is positive.
  exact ⟨ne_of_gt (inverseDFPUpdate_denominator_pos hH hsy), ne_of_gt hsy⟩

/-- Left multiplication by a vector agrees with right multiplication for a real
Hermitian matrix. -/
private lemma vecMul_eq_mulVec_of_isHermitian {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} (hH : H.IsHermitian) (y : n → ℝ) :
    y ᵥ* H = H *ᵥ y := by
  -- Conjugate-transpose the matrix-vector product, then remove the two real stars.
  have hstar := Matrix.star_mulVec H y
  rw [hH.eq] at hstar
  simpa using hstar.symm

/-- The quadratic form of a DFP update is the base form minus and plus its two
rank-one scalar contributions. -/
private lemma inverseDFPUpdate_quadraticForm {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} (hH : H.IsHermitian) (s y x : n → ℝ) :
    x ⬝ᵥ (Matrix.inverseDFPUpdate H s y *ᵥ x) =
      x ⬝ᵥ (H *ᵥ x) - (y ⬝ᵥ (H *ᵥ y))⁻¹ * (x ⬝ᵥ (H *ᵥ y)) ^ 2 +
        (s ⬝ᵥ y)⁻¹ * (x ⬝ᵥ s) ^ 2 := by
  -- Hermitian symmetry identifies the row factor in the update with `H *ᵥ y`.
  have hyH := vecMul_eq_mulVec_of_isHermitian hH y
  -- Matrix and dot-product linearity reduce the formula to scalar ring arithmetic.
  simp only [Matrix.inverseDFPUpdate, add_mulVec, sub_mulVec, smul_mulVec,
    vecMulVec_mulVec, dotProduct_add, dotProduct_sub, dotProduct_smul,
    op_smul_eq_mul, smul_eq_mul]
  rw [hyH]
  rw [dotProduct_comm (H *ᵥ y) x, dotProduct_comm s x]
  ring

/-- Removing the `H *ᵥ y` component of a vector completes the corresponding
quadratic form to a square. -/
private lemma quadraticForm_sub_projection {n : Type u} [Fintype n]
    {H : Matrix n n ℝ} (hH : H.IsHermitian) (y x : n → ℝ)
    (hq : y ⬝ᵥ (H *ᵥ y) ≠ 0) :
    x ⬝ᵥ (H *ᵥ x) - (y ⬝ᵥ (H *ᵥ y))⁻¹ * (x ⬝ᵥ (H *ᵥ y)) ^ 2 =
      (x - ((x ⬝ᵥ (H *ᵥ y)) / (y ⬝ᵥ (H *ᵥ y))) • y) ⬝ᵥ
        (H *ᵥ (x - ((x ⬝ᵥ (H *ᵥ y)) / (y ⬝ᵥ (H *ᵥ y))) • y)) := by
  -- Symmetry also identifies the two mixed terms in the expanded residual form.
  have hyH := vecMul_eq_mulVec_of_isHermitian hH y
  have hmixed : y ⬝ᵥ (H *ᵥ x) = x ⬝ᵥ (H *ᵥ y) := by
    calc
      y ⬝ᵥ (H *ᵥ x) = (y ᵥ* H) ⬝ᵥ x := by
        rw [dotProduct_mulVec]
      _ = (H *ᵥ y) ⬝ᵥ x := by rw [hyH]
      _ = x ⬝ᵥ (H *ᵥ y) := dotProduct_comm _ _
  -- Expand the projected vector, substitute the mixed-term identity, and normalize.
  simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hmixed]
  field_simp [hq]
  ring

/-- The inverse-form DFP update preserves positive definiteness. -/
theorem inverseDFPUpdate {n : Type u} [Fintype n] {H : Matrix n n ℝ}
    {s y : n → ℝ} (hH : H.PosDef) (hsy : 0 < s ⬝ᵥ y) :
    (Matrix.inverseDFPUpdate H s y).PosDef := by
  classical
  have hqpos : 0 < y ⬝ᵥ (H *ᵥ y) := inverseDFPUpdate_denominator_pos hH hsy
  have hq : y ⬝ᵥ (H *ᵥ y) ≠ 0 := ne_of_gt hqpos
  -- Hermitian symmetry turns both update summands into scaled self outer products.
  have hyH := vecMul_eq_mulVec_of_isHermitian hH.isHermitian y
  have hmetricOuter : (vecMulVec (H *ᵥ y) (y ᵥ* H)).IsHermitian := by
    rw [hyH]
    simp [Matrix.IsHermitian]
  have hsecantOuter : (vecMulVec s s).IsHermitian := by
    simp [Matrix.IsHermitian]
  have hmetricScaled :
      ((y ⬝ᵥ (H *ᵥ y))⁻¹ • vecMulVec (H *ᵥ y) (y ᵥ* H)).IsHermitian :=
    hmetricOuter.smul (IsSelfAdjoint.all _)
  have hsecantScaled : ((s ⬝ᵥ y)⁻¹ • vecMulVec s s).IsHermitian :=
    hsecantOuter.smul (IsSelfAdjoint.all _)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · -- The base Hermitian matrix remains Hermitian after subtracting and adding the two terms.
    rw [Matrix.inverseDFPUpdate]
    exact (hH.isHermitian.sub hmetricScaled).add hsecantScaled
  · intro x hx
    -- Rewrite the quadratic form as a positive base residual plus a secant square.
    have hform := inverseDFPUpdate_quadraticForm hH.isHermitian s y x
    rw [quadraticForm_sub_projection hH.isHermitian y x hq] at hform
    have hpositive : 0 < x ⬝ᵥ (Matrix.inverseDFPUpdate H s y *ᵥ x) := by
      by_cases hresidual :
          x - ((x ⬝ᵥ (H *ᵥ y)) / (y ⬝ᵥ (H *ᵥ y))) • y = 0
      · -- If the residual vanishes, nonzero `x` forces a nonzero secant square.
        have hxproj :
            x = ((x ⬝ᵥ (H *ᵥ y)) / (y ⬝ᵥ (H *ᵥ y))) • y :=
          sub_eq_zero.mp hresidual
        have hcoeff : (x ⬝ᵥ (H *ᵥ y)) / (y ⬝ᵥ (H *ᵥ y)) ≠ 0 := by
          intro hcoeff
          apply hx
          rw [hxproj, hcoeff]
          simp
        have hys : y ⬝ᵥ s ≠ 0 := by
          rw [dotProduct_comm]
          exact ne_of_gt hsy
        have hxs : x ⬝ᵥ s ≠ 0 := by
          rw [hxproj, smul_dotProduct, smul_eq_mul]
          exact mul_ne_zero hcoeff hys
        have hsecantPos : 0 < (s ⬝ᵥ y)⁻¹ * (x ⬝ᵥ s) ^ 2 :=
          mul_pos (inv_pos.mpr hsy) (sq_pos_of_ne_zero hxs)
        rw [hform, hresidual]
        simpa using hsecantPos
      · -- Otherwise positive definiteness makes the base residual strictly positive.
        have hresidualPos :
            0 < (x - ((x ⬝ᵥ (H *ᵥ y)) / (y ⬝ᵥ (H *ᵥ y))) • y) ⬝ᵥ
              (H *ᵥ (x - ((x ⬝ᵥ (H *ᵥ y)) / (y ⬝ᵥ (H *ᵥ y))) • y)) := by
          simpa using hH.dotProduct_mulVec_pos hresidual
        have hsecantNonneg : 0 ≤ (s ⬝ᵥ y)⁻¹ * (x ⬝ᵥ s) ^ 2 :=
          mul_nonneg (inv_nonneg.mpr hsy.le) (sq_nonneg _)
        rw [hform]
        exact add_pos_of_pos_of_nonneg hresidualPos hsecantNonneg
    -- Over `ℝ`, the star on the test vector is definitionally trivial.
    simpa using hpositive

end PosDef

end Matrix
