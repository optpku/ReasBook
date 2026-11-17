module

public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2
public import ReasLib.Optimization.DFP.Polar.Hermitian
public import ReasLib.Optimization.DFP.Polar.Recurrence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# General canceled polar stage

The scale and the angular coefficient are independent inputs. Substituting the
paper's coefficient δ * F(v) gives an analytic map in the independent scale and
inverse-index variables. Every occurrence of the scale is even in the canceled
stage, which supplies the quadratic scale remainder without assigning an analytic
extension to a fractional power at zero. The matrix transport reuses the raw
polar update and its exact DFP bracket.
-/

public section

noncomputable section

open scoped Matrix Topology

namespace DFP.Polar.General.Normalized

/-- Helper for lem:polar-continuation: the angle with independent scale and coefficient. -/
def stageAngle (a t : ℝ) : ℝ :=
  a * t

/-- Helper for lem:polar-continuation: the product formula defining a stage angle. -/
theorem stageAngle_def (a t : ℝ) : stageAngle a t = a * t := by
  rfl

/-- Helper for lem:polar-continuation: the regularized sine quotient. -/
def sinFactor (a t : ℝ) : ℝ :=
  a * Real.sinc (stageAngle a t)

/-- Helper for lem:polar-continuation: the removable-singularity formula for the sine factor. -/
theorem sinFactor_def (a t : ℝ) : sinFactor a t = a * Real.sinc (stageAngle a t) := by
  rfl

/-- Helper for lem:polar-continuation: the regularized cotangent multiplier. -/
def cotFactor (a t : ℝ) : ℝ :=
  Real.cos (stageAngle a t) / sinFactor a t

/-- Helper for lem:polar-continuation: the quotient defining the cotangent multiplier. -/
theorem cotFactor_def (a t : ℝ) :
    cotFactor a t = Real.cos (stageAngle a t) / sinFactor a t := by
  rfl

/-- Helper for lem:polar-continuation: the regularized sine agrees with its quotient at every
positive scale, including a zero angular coefficient. -/
theorem sinFactor_eq_sin_div (a t : ℝ) (ht : 0 < t) :
    sinFactor a t = Real.sin (stageAngle a t) / t := by
  by_cases ha : a = 0
  · simp [ha, sinFactor_def, stageAngle_def]
  · rw [sinFactor_def, stageAngle_def,
      Real.sinc_of_ne_zero (mul_ne_zero ha ht.ne')]
    field_simp

/-- Helper for lem:polar-continuation: the canceled cotangent agrees with scale times the ordinary
cotangent at positive scales. -/
theorem cotFactor_eq_mul_cot (a t : ℝ) (ht : 0 < t) :
    cotFactor a t = t * Real.cot (stageAngle a t) := by
  rw [cotFactor_def, sinFactor_eq_sin_div a t ht, Real.cot_eq_cos_div_sin,
    div_eq_mul_inv, inv_div]
  ring

/-- Helper for lem:polar-continuation: the diagonal normalization matrix `S_t = diag(t, 1)`. -/
def scaleMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![t, 0; 0, 1]

/-- Helper for lem:polar-continuation: the diagonal formula defining `scaleMatrix`. -/
theorem scaleMatrix_def (t : ℝ) :
    scaleMatrix t = !![t, 0; 0, 1] := by
  -- The displayed matrix is the definition of the normalization map.
  rfl

/-- Helper for lem:polar-continuation: the pointwise inverse of `scaleMatrix t` when `t ≠ 0`. -/
def invScaleMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![t⁻¹, 0; 0, 1]

/-- Helper for lem:polar-continuation: the diagonal formula defining `invScaleMatrix`. -/
theorem invScaleMatrix_def (t : ℝ) :
    invScaleMatrix t = !![t⁻¹, 0; 0, 1] := by
  -- The inverse-scale matrix is defined by its diagonal entries.
  rfl

/-- Helper for lem:polar-continuation: the normalization matrix and its inverse multiply to the
identity at every nonzero scale. -/
private lemma scaleMatrix_mul_invScaleMatrix (t : ℝ) (ht : t ≠ 0) :
    scaleMatrix t * invScaleMatrix t = 1 := by
  -- Evaluate the four finite matrix entries and cancel the nonzero scale.
  ext i j
  fin_cases i
  all_goals fin_cases j
  · simp [scaleMatrix, invScaleMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      ht]
  · simp [scaleMatrix, invScaleMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [scaleMatrix, invScaleMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [scaleMatrix, invScaleMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Helper for lem:polar-continuation: the diagonal normalization matrix is symmetric. -/
private lemma scaleMatrix_transpose (t : ℝ) :
    (scaleMatrix t).transpose = scaleMatrix t := by
  -- A diagonal matrix is unchanged by exchanging its two indices.
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals rfl

/-- Helper for lem:polar-continuation: the diagonal inverse-normalization matrix is symmetric. -/
private lemma invScaleMatrix_transpose (t : ℝ) :
    (invScaleMatrix t).transpose = invScaleMatrix t := by
  -- The inverse-scale matrix has the same diagonal form.
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals rfl

/-- Helper for lem:polar-continuation: the coordinates `(t ^ 2 * Z₀₀, t * Z₀₁, Z₁₁)` of `S_t Z
S_t`. -/
def coordinates (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) : ℝ × ℝ × ℝ :=
  (t ^ 2 * Z 0 0, t * Z 0 1, Z 1 1)

/-- Helper for lem:polar-continuation: the entry formula defining the normalized coordinates. -/
theorem coordinates_apply (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    coordinates t Z = (t ^ 2 * Z 0 0, t * Z 0 1, Z 1 1) := by
  -- Unfold the three normalized coordinates.
  rfl

/-- Helper for lem:polar-continuation: the normalized quotient `Q = V / C`. -/
def slope (x : ℝ × ℝ × ℝ) : ℝ :=
  x.2.2 / x.2.1

/-- Helper for lem:polar-continuation: the entry quotient defining `slope`. -/
theorem slope_def (x : ℝ × ℝ × ℝ) :
    slope x = x.2.2 / x.2.1 := by
  -- The slope is the totalized quotient of the last two coordinates.
  rfl

/-- Helper for lem:polar-continuation: the normalized displacement vector `S_t⁻¹ v = (-Q, 1)`. -/
def stepV (x : ℝ × ℝ × ℝ) : Fin 2 → ℝ :=
  ![-slope x, 1]

/-- Helper for lem:polar-continuation: the coordinate formula defining the normalized displacement
vector. -/
theorem stepV_def (x : ℝ × ℝ × ℝ) :
    stepV x = ![-slope x, 1] := by
  -- The normalized displacement vector is defined componentwise.
  rfl

/-- Helper for lem:polar-continuation: the canceled normalized gradient-change vector `S_t w`. -/
def stepW (a : ℝ) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) : Fin 2 → ℝ :=
  ![(ζNext - ζ) * cotFactor a t - ζ * t ^ 2 * slope x, ζNext]

/-- Helper for lem:polar-continuation: the canceled coordinate formula defining the normalized
gradient change. -/
theorem stepW_def (a : ℝ) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ) :
    stepW a t x ζ ζNext =
      ![(ζNext - ζ) * cotFactor a t - ζ * t ^ 2 * slope x, ζNext] := by
  -- The canceled gradient-change vector is its displayed two-entry vector.
  rfl

/-- Helper for lem:polar-continuation: the canceled matrix representing `S_t R(stageAngle a t)ᵀ
S_t⁻¹`. -/
def rotation (a : ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (stageAngle a t), t ^ 2 * sinFactor a t;
    -sinFactor a t, Real.cos (stageAngle a t)]

/-- Helper for lem:polar-continuation: the canceled coordinate formula defining the normalized
rotation matrix. -/
theorem rotation_def (a : ℝ) (t : ℝ) :
    rotation a t =
      !![Real.cos (stageAngle a t), t ^ 2 * sinFactor a t;
        -sinFactor a t, Real.cos (stageAngle a t)] := by
  -- The normalized rotation is defined by this explicit matrix.
  rfl

/-- Helper for lem:polar-continuation: the normalized secant scalar `bar vᵀ bar w`. -/
def stageSigma (a : ℝ) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ) : ℝ :=
  stepV x ⬝ᵥ stepW a t x ζ ζNext

/-- Helper for lem:polar-continuation: the dot-product formula defining `stageSigma`. -/
theorem stageSigma_def (a : ℝ) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) :
    stageSigma a t x ζ ζNext = stepV x ⬝ᵥ stepW a t x ζ ζNext := by
  -- Expose the dot-product definition of the secant scalar.
  rfl

/-- Helper for lem:polar-continuation: one exact normalized DFP matrix update with canceled
rotation factors. -/
def stageMatrix (a : ℝ) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let X := RealSymmetric2.matrix x.1 x.2.1 x.2.2
  let v := stepV x
  let w := stepW a t x ζ ζNext
  let σ := stageSigma a t x ζ ζNext
  let P := rotation a t
  P *
    ((1 - σ⁻¹ • Matrix.vecMulVec w v) * X *
      (1 - σ⁻¹ • Matrix.vecMulVec v w) + σ⁻¹ • Matrix.vecMulVec w w) *
    P.transpose

/-- Helper for lem:polar-continuation: the exact normalized bracket formula defining
`stageMatrix`. -/
theorem stageMatrix_def (a : ℝ) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) :
    stageMatrix a t x ζ ζNext =
      let X := RealSymmetric2.matrix x.1 x.2.1 x.2.2
      let v := stepV x
      let w := stepW a t x ζ ζNext
      let σ := stageSigma a t x ζ ζNext
      let P := rotation a t
      P *
        ((1 - σ⁻¹ • Matrix.vecMulVec w v) * X *
          (1 - σ⁻¹ • Matrix.vecMulVec v w) + σ⁻¹ • Matrix.vecMulVec w w) *
        P.transpose := by
  -- Unfold only the named components of the normalized stage.
  rfl

/-- Helper for lem:polar-continuation: the factored DFP bracket built from a matrix, two vectors,
and a secant scalar. -/
private def dfpBracket (X : Matrix (Fin 2) (Fin 2) ℝ)
    (v w : Fin 2 → ℝ) (σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 - σ⁻¹ • Matrix.vecMulVec w v) * X *
      (1 - σ⁻¹ • Matrix.vecMulVec v w) +
    σ⁻¹ • Matrix.vecMulVec w w

/-- Helper for lem:polar-continuation: the normalized stage is a rotation congruence of its
factored DFP bracket. -/
private lemma stageMatrixBracketFormula (a : ℝ) (t : ℝ)
    (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ) :
    stageMatrix a t x ζ ζNext =
      rotation a t *
        dfpBracket (RealSymmetric2.matrix x.1 x.2.1 x.2.2)
          (stepV x) (stepW a t x ζ ζNext) (stageSigma a t x ζ ζNext) *
        (rotation a t).transpose := by
  -- Expose the bracket without expanding any of its rank-one terms.
  rfl

/-- Helper for lem:polar-continuation: the raw polar update is a rotation congruence of the
factored DFP bracket. -/
private lemma matrixStepBracketFormula
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ ζ ζNext : ℝ) :
    DFP.Polar.matrixStep Z δ ζ ζNext =
      (DFP.Polar.rotationMatrix δ).transpose *
        dfpBracket Z (DFP.Polar.stepVOf Z)
          (DFP.Polar.stepWOf Z δ ζ ζNext) (DFP.Polar.sigmaOf Z δ ζ ζNext) *
        DFP.Polar.rotationMatrix δ := by
  -- Use the raw update's public formula to identify its bracket.
  rw [DFP.Polar.matrixStep_def]
  rfl

/-- Helper for lem:polar-continuation: the factored DFP bracket is Hermitian whenever its base
matrix is Hermitian. -/
private theorem dfpBracket_isHermitian
    (X : Matrix (Fin 2) (Fin 2) ℝ) (v w : Fin 2 → ℝ) (σ : ℝ)
    (hX : X.IsHermitian) :
    (dfpBracket X v w σ).IsHermitian := by
  -- Pair the two rank-one factors by conjugate transpose.
  let A : Matrix (Fin 2) (Fin 2) ℝ := 1 - σ⁻¹ • Matrix.vecMulVec w v
  let B : Matrix (Fin 2) (Fin 2) ℝ := 1 - σ⁻¹ • Matrix.vecMulVec v w
  have hAB : Aᴴ = B := by
    dsimp [A, B]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec]
    simp
  have hleft : (A * X * B).IsHermitian := by
    rw [← hAB]
    exact Matrix.isHermitian_mul_mul_conjTranspose A hX
  -- The rank-one correction is self-adjoint over the real scalars.
  have houter : (σ⁻¹ • Matrix.vecMulVec w w).IsHermitian := by
    apply Matrix.IsHermitian.smul
    · refine Matrix.IsHermitian.ext ?_
      intro i j
      simp [Matrix.vecMulVec_apply, mul_comm]
    · exact IsSelfAdjoint.all _
  change (A * X * B + σ⁻¹ • Matrix.vecMulVec w w).IsHermitian
  exact hleft.add houter

/-- Helper for lem:polar-continuation: the factored DFP bracket is covariant under symmetric
mutually inverse changes of coordinates. -/
private theorem dfpBracket_transport
    (S T X : Matrix (Fin 2) (Fin 2) ℝ) (v w : Fin 2 → ℝ) (σ : ℝ)
    (hST : S * T = 1) (hTS : T * S = 1)
    (hS : S.transpose = S) (hT : T.transpose = T) :
    dfpBracket (S * X * S) (T *ᵥ v) (S *ᵥ w) σ =
      S * dfpBracket X v w σ * S := by
  -- Transport each rank-one term through the two matrix actions.
  have hwv :
      Matrix.vecMulVec (S *ᵥ w) (T *ᵥ v) =
        S * Matrix.vecMulVec w v * T := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [← Matrix.vecMul_transpose T v, hT]
  have hvw :
      Matrix.vecMulVec (T *ᵥ v) (S *ᵥ w) =
        T * Matrix.vecMulVec v w * S := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [← Matrix.vecMul_transpose S w, hS]
  have hww :
      Matrix.vecMulVec (S *ᵥ w) (S *ᵥ w) =
        S * Matrix.vecMulVec w w * S := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [← Matrix.vecMul_transpose S w, hS]
  -- Factor each transformed rank-one correction before cancelling S and T.
  have hfactor (A : Matrix (Fin 2) (Fin 2) ℝ) :
      1 - σ⁻¹ • (S * A * T) =
        S * (1 - σ⁻¹ • A) * T := by
    calc
      1 - σ⁻¹ • (S * A * T) =
          S * T - σ⁻¹ • (S * A * T) := by rw [hST]
      _ = S * (1 - σ⁻¹ • A) * T := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, one_smul]
  have hfactor' (A : Matrix (Fin 2) (Fin 2) ℝ) :
      1 - σ⁻¹ • (T * A * S) =
        T * (1 - σ⁻¹ • A) * S := by
    calc
      1 - σ⁻¹ • (T * A * S) =
          T * S - σ⁻¹ • (T * A * S) := by rw [hTS]
      _ = T * (1 - σ⁻¹ • A) * S := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, one_smul]
  rw [dfpBracket, dfpBracket, hwv, hvw, hww, hfactor, hfactor']
  simp only [Matrix.mul_assoc, Matrix.mul_add, smul_add,
    Matrix.mul_smul, Matrix.smul_mul]
  simp only [← Matrix.mul_assoc, hTS, hST, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.add_mul, Matrix.smul_mul]

/-- Helper for lem:polar-continuation: a normalized stage matrix is Hermitian. -/
theorem stageMatrix_isHermitian (a : ℝ) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) :
    (stageMatrix a t x ζ ζNext).IsHermitian := by
  -- First expose the stage's named base matrix, vectors, scalar, and rotation.
  rw [stageMatrix_def]
  dsimp
  let X := RealSymmetric2.matrix x.1 x.2.1 x.2.2
  let v := stepV x
  let w := stepW a t x ζ ζNext
  let σ := stageSigma a t x ζ ζNext
  let P := rotation a t
  have hBracket : (dfpBracket X v w σ).IsHermitian :=
    dfpBracket_isHermitian X v w σ
      (RealSymmetric2.matrix_isHermitian x.1 x.2.1 x.2.2)
  have hStage := Matrix.isHermitian_mul_mul_conjTranspose P hBracket
  -- The real conjugate transpose is ordinary transpose, matching the definition.
  change (P * dfpBracket X v w σ * P.transpose).IsHermitian
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hStage

/-- Helper for lem:polar-continuation: the coordinate triple produced by one normalized matrix
stage. -/
def stage (a : ℝ) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) : ℝ × ℝ × ℝ :=
  let X := stageMatrix a t x ζ ζNext
  (X 0 0, X 0 1, X 1 1)

/-- Helper for lem:polar-continuation: the selected entries of `stageMatrix` form the output of
`stage`. -/
theorem stage_apply (a : ℝ) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ) :
    stage a t x ζ ζNext =
      let X := stageMatrix a t x ζ ζNext
      (X 0 0, X 0 1, X 1 1) := by
  -- The stage output is the selected matrix-entry triple.
  rfl

/-- Helper for lem:polar-continuation: the limiting one-stage coordinate update with angular
coefficient `c`. -/
def leadingStage (c : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.1, x.1 * (slope x - c), 1 + x.1 * (slope x - c) ^ 2)

/-- Helper for lem:polar-continuation: the three coordinate formulas defining the limiting stage
map. -/
theorem leadingStage_apply (c : ℝ) (x : ℝ × ℝ × ℝ) :
    leadingStage c x =
      (x.1, x.1 * (x.2.2 / x.2.1 - c),
        1 + x.1 * (x.2.2 / x.2.1 - c) ^ 2) := by
  -- Replace the named slope by its quotient definition.
  rfl

/-- Helper for lem:polar-continuation: Hermitian coordinate reconstruction is conjugation by
`scaleMatrix t`. -/
theorem coordinates_eq_scaleMatrix_mul (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (hZ : Z.IsHermitian) :
    RealSymmetric2.matrix (coordinates t Z).1 (coordinates t Z).2.1
        (coordinates t Z).2.2 =
      scaleMatrix t * Z * scaleMatrix t := by
  -- Hermitian symmetry supplies the sole off-diagonal identification.
  have hsymm : Z 1 0 = Z 0 1 := by
    simpa using hZ.apply 0 1
  rw [RealSymmetric2.matrix_eq]
  ext i j
  fin_cases i
  all_goals fin_cases j
  -- Expand the two diagonal scale factors and normalize the finite sums.
  all_goals simp [coordinates, scaleMatrix, Matrix.mul_apply,
    Matrix.of_apply, Matrix.vecMul, Matrix.mulVec, Fin.sum_univ_two,
    Matrix.cons_dotProduct_cons, Matrix.dotProduct_cons, Matrix.cons_dotProduct,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, hsymm]
  all_goals ring

/-- Helper for lem:polar-continuation: at positive scale, normalized displacement is inverse-scale
transport of `stepVOf`. -/
theorem stepV_eq_invScaleMatrix_mulVec (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ht : 0 < t) :
    stepV (coordinates t Z) = invScaleMatrix t *ᵥ DFP.Polar.stepVOf Z := by
  -- Evaluate the two vector entries; only powers of the positive scale are
  -- cancelled, while the matrix quotient remains totalized.
  rw [stepV_def, DFP.Polar.stepVOf_def, DFP.Polar.omegaOf_def]
  funext i
  fin_cases i
  · simp [coordinates, slope, invScaleMatrix,
      Matrix.mulVec, Matrix.mul_apply,
      Matrix.of_apply, Matrix.cons_dotProduct_cons, Matrix.dotProduct_cons,
      Matrix.cons_dotProduct, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.sum_univ_two]
    field_simp [ht.ne']
  · simp [coordinates, invScaleMatrix, Matrix.mulVec, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Helper for lem:polar-continuation: at positive scale, normalized gradient change is scale
transport of `stepWOf`. -/
theorem stepW_eq_scaleMatrix_mulVec (a : ℝ) (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ζ ζNext : ℝ) (ht : 0 < t) :
    stepW a t (coordinates t Z) ζ ζNext =
      scaleMatrix t *ᵥ
        DFP.Polar.stepWOf Z (stageAngle a t) ζ ζNext := by
  -- The normalized slope and cotangent each contribute one scale factor.
  have hSlope :
      t ^ 2 * slope (coordinates t Z) = t * DFP.Polar.omegaOf Z := by
    rw [DFP.Polar.omegaOf_def]
    simp [coordinates, slope, div_eq_mul_inv, mul_inv_rev]
    field_simp [ht.ne']
  rw [stepW_def, DFP.Polar.stepWOf_def, cotFactor_eq_mul_cot a t ht]
  funext j
  fin_cases j
  · -- Evaluate the radial coordinate before applying the scaled slope identity.
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero, Matrix.mulVec, scaleMatrix, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.dotProduct_cons,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, zero_mul, Matrix.dotProduct_of_isEmpty, add_zero]
    have hterm :
        ζ * t ^ 2 * slope (coordinates t Z) =
          ζ * (t * DFP.Polar.omegaOf Z) := by
      calc
        ζ * t ^ 2 * slope (coordinates t Z) =
            ζ * (t ^ 2 * slope (coordinates t Z)) := by ring
        _ = ζ * (t * DFP.Polar.omegaOf Z) := by rw [hSlope]
    rw [hterm]
    ring
  · simp [scaleMatrix, Matrix.mulVec, Matrix.of_apply, Matrix.dotProduct_cons,
      Matrix.cons_dotProduct, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

/-- Helper for lem:polar-continuation: at positive scale, the canceled rotation is the exact
scaled rotation transport. -/
theorem rotation_eq_scaleMatrix_mul (a : ℝ) (t : ℝ) (ht : 0 < t) :
    rotation a t =
      scaleMatrix t * (DFP.Polar.rotationMatrix (stageAngle a t)).transpose *
        invScaleMatrix t := by
  -- Recover the ordinary sine quotient on the positive branch, then
  -- evaluate the diagonal conjugation entrywise.
  rw [rotation_def, DFP.Polar.rotationMatrix_def,
    sinFactor_eq_sin_div a t ht]
  ext r c
  fin_cases r
  all_goals fin_cases c
  all_goals simp [scaleMatrix, invScaleMatrix, Matrix.mul_apply, Matrix.of_apply,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.sum_univ_two]
  all_goals field_simp [ht.ne']

/-- Helper for lem:polar-continuation: inverse scaling of the displacement and scaling of the
gradient change preserve the secant scalar. -/
theorem stageSigma_eq_sigmaOf (a : ℝ) (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ζ ζNext : ℝ) (ht : 0 < t) :
    stageSigma a t (coordinates t Z) ζ ζNext =
      DFP.Polar.sigmaOf Z (stageAngle a t) ζ ζNext := by
  -- Move the two matrix actions next to each other inside the dot product.
  have hTS : invScaleMatrix t * scaleMatrix t = 1 :=
    mul_eq_one_comm.mp (scaleMatrix_mul_invScaleMatrix t ht.ne')
  rw [stageSigma_def, stepV_eq_invScaleMatrix_mulVec t Z ht,
    stepW_eq_scaleMatrix_mulVec a t Z ζ ζNext ht,
    Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    invScaleMatrix_transpose, hTS, Matrix.vecMul_one,
    DFP.Polar.sigmaOf_def]

/-- Helper for lem:polar-continuation: a scaled rotation congruence cancels mutually inverse
symmetric coordinate changes. -/
private lemma scaledRotationCongruence
    (S T R B : Matrix (Fin 2) (Fin 2) ℝ)
    (hST : S * T = 1) (hTS : T * S = 1)
    (hS : S.transpose = S) (hT : T.transpose = T) :
    (S * R.transpose * T) * (S * B * S) *
        (S * R.transpose * T).transpose =
      S * (R.transpose * B * R) * S := by
  -- Cancel the inverse scale separately on the two sides of the bracket.
  have hleft : (S * R.transpose * T) * S = S * R.transpose := by
    simp only [Matrix.mul_assoc, hTS, Matrix.mul_one]
  have hright : S * (S * R.transpose * T).transpose = R * S := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hT,
      Matrix.transpose_transpose, hS, ← Matrix.mul_assoc, hST,
      Matrix.one_mul]
  calc
    (S * R.transpose * T) * (S * B * S) *
        (S * R.transpose * T).transpose =
        ((S * R.transpose * T) * S) * B *
          (S * (S * R.transpose * T).transpose) := by
      simp only [Matrix.mul_assoc]
    _ = (S * R.transpose) * B * (R * S) := by rw [hleft, hright]
    _ = S * (R.transpose * B * R) * S := by
      simp only [Matrix.mul_assoc]

/-- Helper for lem:polar-continuation: at positive scale, one normalized stage is the exact scaled
raw polar update. -/
theorem stageMatrix_eq_scaleMatrix_mul (a : ℝ) (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ζ ζNext : ℝ)
    (hZ : Z.IsHermitian) (ht : 0 < t) :
    stageMatrix a t (coordinates t Z) ζ ζNext =
      scaleMatrix t *
        DFP.Polar.matrixStep Z (stageAngle a t) ζ ζNext * scaleMatrix t := by
  -- Identify the normalized matrix, vectors, and secant scalar before
  -- transporting the complete factored bracket.
  have hST := scaleMatrix_mul_invScaleMatrix t ht.ne'
  have hTS : invScaleMatrix t * scaleMatrix t = 1 := mul_eq_one_comm.mp hST
  rw [stageMatrixBracketFormula, coordinates_eq_scaleMatrix_mul t Z hZ,
    stepV_eq_invScaleMatrix_mulVec t Z ht,
    stepW_eq_scaleMatrix_mulVec a t Z ζ ζNext ht,
    stageSigma_eq_sigmaOf a t Z ζ ζNext ht,
    dfpBracket_transport _ _ _ _ _ _ hST hTS
      (scaleMatrix_transpose t) (invScaleMatrix_transpose t),
    rotation_eq_scaleMatrix_mul a t ht]
  -- Rotation conjugation cancels the inverse scales left after bracket transport.
  rw [scaledRotationCongruence _ _ _ _ hST hTS
    (scaleMatrix_transpose t) (invScaleMatrix_transpose t),
    matrixStepBracketFormula]

/-- Helper for lem:polar-continuation: a tangential unit gradient change removes the old
tangential and off-diagonal bracket data. -/
private lemma dfpBracketTangentialUnit (A C V Q : ℝ) :
    dfpBracket (RealSymmetric2.matrix A C V) ![-Q, 1] ![0, 1] 1 =
      RealSymmetric2.matrix A (A * Q) (1 + A * Q ^ 2) := by
  -- Evaluate the rank-one factors and normalize their polynomial entries.
  rw [dfpBracket, RealSymmetric2.matrix_eq, RealSymmetric2.matrix_eq]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- Helper for lem:polar-continuation: the canceled rotation at zero scale is the shear with the
prescribed angular coefficient. -/
private lemma rotation_zero (a : ℝ) :
    rotation a 0 = !![1, 0; -a, 1] := by
  simp [rotation_def, stageAngle_def, sinFactor_def]

/-- Helper for lem:polar-continuation: at zero scale, the unit-multiplier update is the matrix of
the limiting stage. -/
theorem stageMatrix_zero (a : ℝ) (x : ℝ × ℝ × ℝ) :
    stageMatrix a 0 x 1 1 =
      RealSymmetric2.matrix (leadingStage a x).1
        (leadingStage a x).2.1
        (leadingStage a x).2.2 := by
  -- The canceled gradient change and its secant scalar have unit limits.
  have hW : stepW a 0 x 1 1 = ![0, 1] := by
    simp [stepW_def]
  have hSigma : stageSigma a 0 x 1 1 = 1 := by
    rw [stageSigma_def, hW, stepV_def]
    simp
  rw [stageMatrixBracketFormula, hW, hSigma, stepV_def,
    dfpBracketTangentialUnit, rotation_zero]
  -- Conjugation by the limiting shear replaces Q by Q - a.
  simp only [leadingStage, RealSymmetric2.matrix_eq]
  ext r c
  fin_cases r
  all_goals fin_cases c
  all_goals simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  all_goals ring

/-- Helper for lem:polar-continuation: the unit-multiplier stage at zero scale is the source's
limiting one-stage map for every angular coefficient. -/
theorem stage_zero (a : ℝ) (x : ℝ × ℝ × ℝ) :
    stage a 0 x 1 1 = leadingStage a x := by
  rw [stage_apply, stageMatrix_zero]
  simp only [RealSymmetric2.matrix_eq, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Prod.mk.eta]

/-- Helper for lem:polar-continuation: A two-entry vector is analytic when both scalar coordinates
are analytic. -/
private lemma analyticAtFin2Vec {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {f : E → Fin 2 → ℝ} {z : E}
    (h0 : AnalyticAt ℝ (fun y : E ↦ f y 0) z)
    (h1 : AnalyticAt ℝ (fun y : E ↦ f y 1) z) :
    AnalyticAt ℝ f z := by
  -- Reduce the finite vector to its two coordinate germs.
  rw [analyticAt_pi_iff]
  intro j
  fin_cases j
  · simpa using h0
  · simpa using h1

/-- Helper for lem:polar-continuation: The coordinate update as a function of its normalized
gradient change and rotation matrix. -/
private def stageFromFactors (x : ℝ × ℝ × ℝ)
    (d : (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)) : ℝ × ℝ × ℝ :=
  let X := RealSymmetric2.matrix x.1 x.2.1 x.2.2
  let v := stepV x
  let w := d.1
  let σ := v ⬝ᵥ w
  let P := Matrix.of d.2
  let Y := P * ((1 - σ⁻¹ • Matrix.vecMulVec w v) * X *
      (1 - σ⁻¹ • Matrix.vecMulVec v w) + σ⁻¹ • Matrix.vecMulVec w w) * P.transpose
  (Y 0 0, Y 0 1, Y 1 1)

/-- Helper for lem:polar-continuation: The normalized stage equals the update formed from its
gradient change and rotation matrix. -/
private lemma stage_eq_fromFactors (a : ℝ) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    stage a t x ζ η =
      stageFromFactors x (stepW a t x ζ η, fun r c ↦ rotation a t r c) := by
  -- The interface uses exactly the source's factored bracket and rotation congruence.
  simp only [stage_apply, stageMatrix_def, stageSigma_def, stageFromFactors]
  rfl

/-- Helper for lem:polar-continuation: The factorized coordinate update preserves analytic state
and factor paths with a nonzero secant scalar. -/
private lemma stageFromFactorsAlong_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : E → ℝ × ℝ × ℝ}
    {d : E → (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)} {z : E}
    (hX : AnalyticAt ℝ X z) (hd : AnalyticAt ℝ d z)
    (hSlope : AnalyticAt ℝ (fun y ↦ slope (X y)) z)
    (hσ0 : stepV (X z) ⬝ᵥ (d z).1 ≠ 0) :
    AnalyticAt ℝ (fun y ↦ stageFromFactors (X y) (d y)) z := by
  -- Expose each state coordinate through analytic projections.
  have hA : AnalyticAt ℝ (fun y ↦ (X y).1) z :=
    AnalyticAt.comp (f := X) analyticAt_fst hX
  have hCV : AnalyticAt ℝ (fun y ↦ (X y).2) z :=
    AnalyticAt.comp (f := X) analyticAt_snd hX
  have hC : AnalyticAt ℝ (fun y ↦ (X y).2.1) z :=
    AnalyticAt.comp (f := fun y ↦ (X y).2) analyticAt_fst hCV
  have hV : AnalyticAt ℝ (fun y ↦ (X y).2.2) z :=
    AnalyticAt.comp (f := fun y ↦ (X y).2) analyticAt_snd hCV
  -- The finite factor coordinates supply the vector and rotation entries.
  have hW : AnalyticAt ℝ (fun y ↦ (d y).1) z :=
    AnalyticAt.comp (f := d) analyticAt_fst hd
  have hP : AnalyticAt ℝ (fun y ↦ (d y).2) z :=
    AnalyticAt.comp (f := d) analyticAt_snd hd
  have hW0 := analyticAt_pi_iff.mp hW 0
  have hW1 := analyticAt_pi_iff.mp hW 1
  have hP0 := analyticAt_pi_iff.mp hP 0
  have hP1 := analyticAt_pi_iff.mp hP 1
  have hP00 := analyticAt_pi_iff.mp hP0 0
  have hP01 := analyticAt_pi_iff.mp hP0 1
  have hP10 := analyticAt_pi_iff.mp hP1 0
  have hP11 := analyticAt_pi_iff.mp hP1 1
  have hV0 : AnalyticAt ℝ (fun y ↦ stepV (X y) 0) z := by
    simp only [stepV_def, Fin.isValue, Matrix.cons_val_zero]
    exact hSlope.neg
  have hV1 : AnalyticAt ℝ (fun y ↦ stepV (X y) 1) z := by
    simp only [stepV_def, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact analyticAt_const
  have hσ : AnalyticAt ℝ (fun y ↦ stepV (X y) ⬝ᵥ (d y).1) z := by
    simp only [dotProduct, Fin.sum_univ_two]
    exact (hV0.mul hW0).add (hV1.mul hW1)
  have hσinv := hσ.inv hσ0
  -- The inverse secant is the only nonpolynomial operation in the factored bracket.
  simp only [stageFromFactors, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.of_apply,
    smul_eq_mul, RealSymmetric2.matrix_eq, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  fun_prop


/-- Helper for lem:polar-continuation: the sine quotient has an analytic removable singularity at
zero. -/
theorem analyticAt_sinc_zero : AnalyticAt ℝ Real.sinc 0 := by
  obtain ⟨p, hp⟩ := (Real.analyticAt_sin : AnalyticAt ℝ Real.sin 0)
  rw [Real.sinc_eq_dslope]
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- Helper for lem:polar-continuation: the canceled stage is analytic along independent analytic
angle, scale, state and gradient-factor paths at zero scale. -/
theorem stageAlong_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a t : E → ℝ} {X : E → ℝ × ℝ × ℝ} {ζ η : E → ℝ} {z : E}
    (ha : AnalyticAt ℝ a z) (ht : AnalyticAt ℝ t z)
    (hX : AnalyticAt ℝ X z) (hζ : AnalyticAt ℝ ζ z) (hη : AnalyticAt ℝ η z)
    (ha0 : a z ≠ 0) (ht0 : t z = 0) (hC : (X z).2.1 ≠ 0)
    (hσ : stageSigma (a z) (t z) (X z) (ζ z) (η z) ≠ 0) :
    AnalyticAt ℝ (fun y ↦ stage (a y) (t y) (X y) (ζ y) (η y)) z := by
  have hAngle : AnalyticAt ℝ (fun y ↦ stageAngle (a y) (t y)) z := ha.mul ht
  have hAngle0 : stageAngle (a z) (t z) = 0 := by
    simp only [stageAngle_def, ht0, mul_zero]
  have hSinc : AnalyticAt ℝ (fun y ↦ Real.sinc (stageAngle (a y) (t y))) z :=
    analyticAt_sinc_zero.comp_of_eq hAngle hAngle0
  have hSin : AnalyticAt ℝ (fun y ↦ sinFactor (a y) (t y)) z := ha.mul hSinc
  have hCos : AnalyticAt ℝ (fun y ↦ Real.cos (stageAngle (a y) (t y))) z :=
    Real.analyticAt_cos.comp hAngle
  have hSin0 : sinFactor (a z) (t z) ≠ 0 := by
    simpa only [sinFactor_def, hAngle0, Real.sinc_zero, mul_one] using ha0
  have hCot : AnalyticAt ℝ (fun y ↦ cotFactor (a y) (t y)) z := hCos.div hSin hSin0
  have hCV : AnalyticAt ℝ (fun y ↦ (X y).2) z := analyticAt_snd.comp hX
  have hSlope : AnalyticAt ℝ (fun y ↦ slope (X y)) z :=
    (analyticAt_snd.comp hCV).div (analyticAt_fst.comp hCV) hC
  have hW : AnalyticAt ℝ (fun y ↦ stepW (a y) (t y) (X y) (ζ y) (η y)) z := by
    apply analyticAtFin2Vec
    · simp only [stepW_def, Fin.isValue, Matrix.cons_val_zero]
      exact ((hη.sub hζ).mul hCot).sub ((hζ.mul (ht.pow 2)).mul hSlope)
    · simpa only [stepW_def, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using hη
  have hP : AnalyticAt ℝ (fun y ↦ fun r c : Fin 2 ↦ rotation (a y) (t y) r c) z := by
    refine analyticAt_pi_iff.mpr ?_
    intro r
    refine analyticAt_pi_iff.mpr ?_
    intro c
    fin_cases r
    all_goals fin_cases c
    all_goals simp only [rotation_def, Matrix.of_apply, Fin.zero_eta, Fin.mk_one,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    · exact hCos
    · exact (ht.pow 2).mul hSin
    · exact hSin.neg
    · exact hCos
  simp only [stage_eq_fromFactors]
  exact stageFromFactorsAlong_analyticAt hX (hW.prod hP) hSlope hσ

/-- Helper for lem:polar-continuation: each regularized sine factor is even in the scale variable. -/
theorem sinFactor_neg (a t : ℝ) : sinFactor a (-t) = sinFactor a t := by
  simp only [sinFactor_def, stageAngle_def, mul_neg, Real.sinc_neg]

/-- Helper for lem:polar-continuation: each regularized cotangent factor is even in the scale
variable. -/
theorem cotFactor_neg (a t : ℝ) : cotFactor a (-t) = cotFactor a t := by
  simp only [cotFactor_def, stageAngle_def, mul_neg, Real.cos_neg, sinFactor_neg]

/-- Helper for lem:polar-continuation: the canceled secant-vector factor is even in scale for
independent gradient multipliers. -/
theorem stepW_neg (a t : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    stepW a (-t) x ζ η = stepW a t x ζ η := by
  simp only [stepW_def, cotFactor_neg, neg_sq]

/-- Helper for lem:polar-continuation: the canceled rotation factor is even in scale. -/
theorem rotation_neg (a t : ℝ) : rotation a (-t) = rotation a t := by
  simp only [rotation_def, stageAngle_def, mul_neg, Real.cos_neg, neg_sq,
    sinFactor_neg]

/-- Helper for lem:polar-continuation: the complete normalized stage is even in scale, which
removes its first scale derivative. -/
theorem stage_neg (a t : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    stage a (-t) x ζ η = stage a t x ζ η := by
  simp only [stage_apply, stageMatrix_def, stageSigma_def, stepW_neg, rotation_neg]


/-- Helper for lem:polar-continuation: the source exponential odd-stage feedback, using the first
diagonal entry at the beginning of both stages. -/
def feedback (φ : ℝ → ℝ) (v γ : ℝ) : ℝ :=
  Real.exp (-φ γ * v)

/-- Helper for lem:polar-continuation: the source feedback equals one at zero inverse index. -/
theorem feedback_zero (φ : ℝ → ℝ) (γ : ℝ) : feedback φ 0 γ = 1 := by
  simp [feedback]

/-- Helper for lem:polar-continuation: exponential feedback is always positive. -/
theorem feedback_pos (φ : ℝ → ℝ) (v γ : ℝ) : 0 < feedback φ v γ := by
  exact Real.exp_pos _

/-- Helper for lem:polar-continuation: a canceled stage with independent inverse index, scale and
analytic angular coefficient paths. -/
def cycleStage (aE aO φ : ℝ → ℝ) (i : Fin 2) (t v : ℝ)
    (x₀ x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let ζ := feedback φ v x₀.1
  stage ((![aE, aO] : Fin 2 → ℝ → ℝ) i v) t x
    (![1, ζ] i) (![ζ, 1] i)

/-- Helper for lem:polar-continuation: the first stage uses the even angular coefficient and
decreases its gradient factor from one to the shared feedback. -/
theorem cycleStage_even (aE aO φ : ℝ → ℝ) (t v : ℝ)
    (x₀ x : ℝ × ℝ × ℝ) :
    cycleStage aE aO φ 0 t v x₀ x =
      stage (aE v) t x 1 (feedback φ v x₀.1) := by
  rfl

/-- Helper for lem:polar-continuation: the second stage returns the gradient factor to one and
retains feedback evaluated at the original boundary state. -/
theorem cycleStage_odd (aE aO φ : ℝ → ℝ) (t v : ℝ)
    (x₀ x : ℝ × ℝ × ℝ) :
    cycleStage aE aO φ 1 t v x₀ x =
      stage (aO v) t x (feedback φ v x₀.1) 1 := by
  rfl

/-- Helper for lem:polar-continuation: the complete two-stage map before changing the boundary
scale. -/
def twoStep (aE aO φ : ℝ → ℝ) (t v : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let y := cycleStage aE aO φ 0 t v x x
  cycleStage aE aO φ 1 t v x y

/-- Helper for lem:polar-continuation: the two-parameter map at zero parameters is exactly the
composition of the two source limiting stages. -/
theorem twoStep_zero (aE aO φ : ℝ → ℝ) (x : ℝ × ℝ × ℝ) :
    twoStep aE aO φ 0 0 x = leadingStage (aO 0) (leadingStage (aE 0) x) := by
  simp only [twoStep, cycleStage_even, cycleStage_odd, feedback_zero, stage_zero]

/-- Helper for lem:polar-continuation: the two-stage canceled map is even in scale independently
of the inverse index. -/
theorem twoStep_neg (aE aO φ : ℝ → ℝ) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    twoStep aE aO φ (-t) v x = twoStep aE aO φ t v x := by
  simp only [twoStep, cycleStage_even, cycleStage_odd, stage_neg]

/-- Helper for lem:polar-continuation: the analytic successor scale ratio, with inverse index
retained as an independent input. -/
def scaleRatio (β v : ℝ) : ℝ :=
  Real.exp (-Real.log (1 + v) / (1 + β))

/-- Helper for lem:polar-continuation: changing the boundary scale acts by congruence with a
diagonal matrix. -/
def rescale (β v : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (scaleRatio β v ^ 2 * x.1, scaleRatio β v * x.2.1, x.2.2)

/-- Helper for lem:polar-continuation: the boundary scale ratio is one at zero inverse index for
every prescribed exponent. -/
theorem scaleRatio_zero (β : ℝ) : scaleRatio β 0 = 1 := by
  simp [scaleRatio]

/-- Helper for lem:polar-continuation: rescaling at zero inverse index is the identity on
normalized states. -/
theorem rescale_zero (β : ℝ) (x : ℝ × ℝ × ℝ) : rescale β 0 x = x := by
  simp only [rescale, scaleRatio_zero, one_pow, one_mul, Prod.mk.eta]

/-- Helper for lem:polar-continuation: the actual source order of the canceled cycle map is two
shared-feedback stages followed by the change of scale. -/
def map (β : ℝ) (aE aO φ : ℝ → ℝ) (t v : ℝ)
    (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  rescale β v (twoStep aE aO φ t v x)

/-- Helper for lem:polar-continuation: the limiting cycle preserves its first diagonal coordinate
for every state, including states off the reference family. -/
theorem map_zero_first (β : ℝ) (aE aO φ : ℝ → ℝ) (x : ℝ × ℝ × ℝ) :
    (map β aE aO φ 0 0 x).1 = x.1 := by
  simp only [map, rescale_zero, twoStep_zero, leadingStage]

/-- Helper for lem:polar-continuation: the complete two-parameter cycle map is even in its scale
input. -/
theorem map_neg (β : ℝ) (aE aO φ : ℝ → ℝ) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    map β aE aO φ (-t) v x = map β aE aO φ t v x := by
  simp only [map, twoStep_neg]

/-- Helper for lem:polar-continuation: the shared feedback preserves analytic parameter and
boundary-state paths. -/
theorem feedbackAlong_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {φ : ℝ → ℝ} {v γ : E → ℝ} {z : E}
    (hφ : AnalyticAt ℝ φ (γ z)) (hv : AnalyticAt ℝ v z)
    (hγ : AnalyticAt ℝ γ z) :
    AnalyticAt ℝ (fun y ↦ feedback φ (v y) (γ y)) z := by
  exact (((hφ.comp hγ).neg).mul hv).rexp'

/-- Helper for lem:polar-continuation: the scale ratio is analytic near zero inverse index,
without requiring analyticity of a fractional scale power at zero. -/
theorem scaleRatio_analyticAt (β : ℝ) : AnalyticAt ℝ (scaleRatio β) 0 := by
  have hbase : (0 : ℝ) < 1 + 0 := by norm_num
  have hlog : AnalyticAt ℝ (fun v : ℝ ↦ Real.log (1 + v)) 0 :=
    (analyticAt_const.add analyticAt_id).log hbase
  exact (hlog.neg.div_const).rexp'

/-- Helper for lem:polar-continuation: one even stage is jointly analytic in the independent
scale, inverse index and current state. -/
theorem evenStage_analyticAt (aE aO φ : ℝ → ℝ) (x : ℝ × ℝ × ℝ)
    (haE : AnalyticAt ℝ aE 0) (hφ : AnalyticAt ℝ φ x.1)
    (ha0 : aE 0 ≠ 0) (hC : x.2.1 ≠ 0) :
    AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦
      cycleStage aE aO φ 0 z.1.1 z.1.2 z.2 z.2) ((0, 0), x) := by
  have ht : AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.1)
      ((0, 0), x) := analyticAt_fst.comp analyticAt_fst
  have hv : AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.2)
      ((0, 0), x) := analyticAt_snd.comp analyticAt_fst
  have hX : AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.2)
      ((0, 0), x) := analyticAt_snd
  have hγ : AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.2.1)
      ((0, 0), x) := analyticAt_fst.comp analyticAt_snd
  have hfeedback := feedbackAlong_analyticAt
    (γ := fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.2.1)
    (z := ((0, 0), x)) hφ hv hγ
  have hσ : stageSigma (aE 0) 0 x 1 (feedback φ 0 x.1) ≠ 0 := by
    simp [feedback_zero, stageSigma_def, stepV_def, stepW_def]
  simp only [cycleStage_even]
  exact stageAlong_analyticAt (haE.comp_of_eq hv rfl) ht hX analyticAt_const hfeedback
    ha0 rfl hC hσ


/-- Helper for lem:polar-continuation: the full two-stage map is jointly analytic in its two
independent parameters and state at a regular limiting cycle. -/
theorem twoStep_analyticAt (aE aO φ : ℝ → ℝ) (x : ℝ × ℝ × ℝ)
    (haE : AnalyticAt ℝ aE 0) (haO : AnalyticAt ℝ aO 0)
    (hφ : AnalyticAt ℝ φ x.1) (ha0 : aE 0 ≠ 0) (hb0 : aO 0 ≠ 0)
    (hC : x.2.1 ≠ 0) (hCNext : (leadingStage (aE 0) x).2.1 ≠ 0) :
    AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦
      twoStep aE aO φ z.1.1 z.1.2 z.2) ((0, 0), x) := by
  have ht : AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.1)
      ((0, 0), x) := analyticAt_fst.comp analyticAt_fst
  have hv : AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.2)
      ((0, 0), x) := analyticAt_snd.comp analyticAt_fst
  have hγ : AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.2.1)
      ((0, 0), x) := analyticAt_fst.comp analyticAt_snd
  let y : (ℝ × ℝ) × (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ :=
    fun z ↦ cycleStage aE aO φ 0 z.1.1 z.1.2 z.2 z.2
  have hy : AnalyticAt ℝ y ((0, 0), x) :=
    evenStage_analyticAt aE aO φ x haE hφ ha0 hC
  have hyzero : y ((0, 0), x) = leadingStage (aE 0) x := by
    simp only [y, cycleStage_even, feedback_zero, stage_zero]
  have hyC : (y ((0, 0), x)).2.1 ≠ 0 := by
    rwa [hyzero]
  have hfeedback := feedbackAlong_analyticAt
    (γ := fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.2.1)
    (z := ((0, 0), x)) hφ hv hγ
  have hσ : stageSigma (aO 0) 0 (y ((0, 0), x)) (feedback φ 0 x.1) 1 ≠ 0 := by
    simp [feedback_zero, stageSigma_def, stepV_def, stepW_def]
  exact stageAlong_analyticAt (haO.comp_of_eq hv rfl) ht hy hfeedback analyticAt_const
    hb0 rfl hyC hσ

/-- Helper for lem:polar-continuation: the normalized cycle followed by its source scale change
has joint analyticity in the independent small parameters. -/
theorem map_analyticAt (β : ℝ) (aE aO φ : ℝ → ℝ) (x : ℝ × ℝ × ℝ)
    (haE : AnalyticAt ℝ aE 0) (haO : AnalyticAt ℝ aO 0)
    (hφ : AnalyticAt ℝ φ x.1) (ha0 : aE 0 ≠ 0) (hb0 : aO 0 ≠ 0)
    (hC : x.2.1 ≠ 0) (hCNext : (leadingStage (aE 0) x).2.1 ≠ 0) :
    AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦
      map β aE aO φ z.1.1 z.1.2 z.2) ((0, 0), x) := by
  have hv : AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.2)
      ((0, 0), x) := analyticAt_snd.comp analyticAt_fst
  have htwo := twoStep_analyticAt aE aO φ x haE haO hφ ha0 hb0 hC hCNext
  have hρ := (scaleRatio_analyticAt β).comp_of_eq hv rfl
  have hA := analyticAt_fst.comp htwo
  have hCV := analyticAt_snd.comp htwo
  have hC' := analyticAt_fst.comp hCV
  have hV := analyticAt_snd.comp hCV
  exact ((hρ.pow 2).mul hA).prod ((hρ.mul hC').prod hV)


/-- Helper for lem:polar-continuation: an even vector-valued function has zero
derivative at the origin. This is the differential form of scale cancellation. -/
theorem deriv_zero_of_even {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (heven : ∀ t, f (-t) = f t) : deriv f 0 = 0 := by
  have heq := congrArg (fun g : ℝ → F ↦ deriv g 0) (funext heven)
  rw [deriv_comp_neg, neg_zero] at heq
  have hdouble : (2 : ℝ) • deriv f 0 = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp heq
  exact (smul_eq_zero.mp hdouble).resolve_left two_ne_zero

/-- Helper for lem:polar-continuation: analyticity and zero first derivative
give a quadratic scale remainder for a vector-valued map. -/
theorem analytic_sub_value_isBigO_sq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : ℝ → F}
    (hf : AnalyticAt ℝ f 0) (hderiv : deriv f 0 = 0) :
    (fun t : ℝ ↦ f t - f 0) =O[𝓝 0] (fun t : ℝ ↦ t ^ 2) := by
  obtain ⟨q, hq, hformula⟩ := hf.exists_eq_sum_add_pow_mul 2
  have hfactor (t : ℝ) : f t - f 0 = t ^ 2 • q t := by
    have hvalue : f t = f 0 + t ^ 2 • q t := by
      simpa [Finset.sum_range_succ, hderiv, iteratedDeriv_zero] using hformula t
    rw [hvalue]
    abel
  have hbound := (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 2) (𝓝 0)).smul
    (hq.continuousAt.isBigO_one ℝ)
  simpa only [hfactor, smul_eq_mul, mul_one] using hbound

/-- Helper for lem:polar-continuation: the scale slice of the actual two-parameter
map has quadratic variation, while the independent inverse index is fixed at zero. -/
theorem map_scale_sub_zero_isBigO_sq (β : ℝ) (aE aO φ : ℝ → ℝ)
    (x : ℝ × ℝ × ℝ) (haE : AnalyticAt ℝ aE 0) (haO : AnalyticAt ℝ aO 0)
    (hφ : AnalyticAt ℝ φ x.1) (ha0 : aE 0 ≠ 0) (hb0 : aO 0 ≠ 0)
    (hC : x.2.1 ≠ 0) (hCNext : (leadingStage (aE 0) x).2.1 ≠ 0) :
    (fun t : ℝ ↦ map β aE aO φ t 0 x - map β aE aO φ 0 0 x)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 2) := by
  have hjoint := map_analyticAt β aE aO φ x haE haO hφ ha0 hb0 hC hCNext
  have hpath : AnalyticAt ℝ (fun t : ℝ ↦ ((t, (0 : ℝ)), x)) 0 :=
    (analyticAt_id.prod analyticAt_const).prod analyticAt_const
  have hslice : AnalyticAt ℝ (fun t : ℝ ↦ map β aE aO φ t 0 x) 0 :=
    hjoint.comp_of_eq hpath rfl
  have hderiv : deriv (fun t : ℝ ↦ map β aE aO φ t 0 x) 0 = 0 :=
    deriv_zero_of_even (fun t ↦ map_neg β aE aO φ t 0 x)
  exact analytic_sub_value_isBigO_sq hslice hderiv


/-- Helper for eq:polar-feedback: the exponential formula for the shared feedback. -/
theorem feedback_def (φ : ℝ → ℝ) (v γ : ℝ) :
    feedback φ v γ = Real.exp (-φ γ * v) := by
  rfl

/-- Helper for lem:polar-continuation: the two consecutive shared-feedback stages. -/
theorem twoStep_apply (aE aO φ : ℝ → ℝ) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    twoStep aE aO φ t v x =
      cycleStage aE aO φ 1 t v x (cycleStage aE aO φ 0 t v x x) := by
  rfl

/-- Helper for lem:polar-continuation: the analytic successor scale ratio. -/
theorem scaleRatio_def (β v : ℝ) :
    scaleRatio β v = Real.exp (-Real.log (1 + v) / (1 + β)) := by
  rfl

/-- Helper for lem:polar-continuation: the coordinate formula for source rescaling. -/
theorem rescale_apply (β v : ℝ) (x : ℝ × ℝ × ℝ) :
    rescale β v x =
      (scaleRatio β v ^ 2 * x.1, scaleRatio β v * x.2.1, x.2.2) := by
  rfl

/-- Helper for lem:polar-continuation: the complete cycle composition interface. -/
theorem map_apply (β : ℝ) (aE aO φ : ℝ → ℝ) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    map β aE aO φ t v x = rescale β v (twoStep aE aO φ t v x) := by
  rfl

end DFP.Polar.General.Normalized
