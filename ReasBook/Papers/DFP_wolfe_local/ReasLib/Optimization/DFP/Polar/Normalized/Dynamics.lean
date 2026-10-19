module

public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2
public import ReasLib.Optimization.DFP.Polar.Hermitian
public import ReasLib.Optimization.DFP.Polar.Normalized.Regularization

public section

noncomputable section

open scoped Matrix

namespace DFP.Polar.Normalized

/-- The diagonal normalization matrix `S_t = diag(t ^ 2, 1)`. -/
def scaleMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![t ^ 2, 0; 0, 1]

/-- The diagonal formula defining `scaleMatrix`. -/
theorem scaleMatrix_def (t : ℝ) :
    scaleMatrix t = !![t ^ 2, 0; 0, 1] := by
  -- The displayed matrix is the definition of the normalization map.
  rfl

/-- The pointwise inverse of `scaleMatrix t` when `t ≠ 0`. -/
def invScaleMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(t ^ 2)⁻¹, 0; 0, 1]

/-- The diagonal formula defining `invScaleMatrix`. -/
theorem invScaleMatrix_def (t : ℝ) :
    invScaleMatrix t = !![(t ^ 2)⁻¹, 0; 0, 1] := by
  -- The inverse-scale matrix is defined by its diagonal entries.
  rfl

/-- The normalization matrix and its inverse multiply to the identity at every
   nonzero scale. -/
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

/-- The diagonal normalization matrix is symmetric. -/
private lemma scaleMatrix_transpose (t : ℝ) :
    (scaleMatrix t).transpose = scaleMatrix t := by
  -- A diagonal matrix is unchanged by exchanging its two indices.
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals rfl

/-- The diagonal inverse-normalization matrix is symmetric. -/
private lemma invScaleMatrix_transpose (t : ℝ) :
    (invScaleMatrix t).transpose = invScaleMatrix t := by
  -- The inverse-scale matrix has the same diagonal form.
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals rfl

/-- The coordinates `(t ^ 4 * Z₀₀, t ^ 2 * Z₀₁, Z₁₁)` of `S_t Z S_t`. -/
def coordinates (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) : ℝ × ℝ × ℝ :=
  (t ^ 4 * Z 0 0, t ^ 2 * Z 0 1, Z 1 1)

/-- The entry formula defining the normalized coordinates. -/
theorem coordinates_apply (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    coordinates t Z = (t ^ 4 * Z 0 0, t ^ 2 * Z 0 1, Z 1 1) := by
  -- Unfold the three normalized coordinates.
  rfl

/-- The normalized quotient `Q = V / C`. -/
def slope (x : ℝ × ℝ × ℝ) : ℝ :=
  x.2.2 / x.2.1

/-- The entry quotient defining `slope`. -/
theorem slope_def (x : ℝ × ℝ × ℝ) :
    slope x = x.2.2 / x.2.1 := by
  -- The slope is the totalized quotient of the last two coordinates.
  rfl

/-- The normalized displacement vector `S_t⁻¹ v = (-Q, 1)`. -/
def stepV (x : ℝ × ℝ × ℝ) : Fin 2 → ℝ :=
  ![-slope x, 1]

/-- The coordinate formula defining the normalized displacement vector. -/
theorem stepV_def (x : ℝ × ℝ × ℝ) :
    stepV x = ![-slope x, 1] := by
  -- The normalized displacement vector is defined componentwise.
  rfl

/-- The canceled normalized gradient-change vector `S_t w`. -/
def stepW (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) : Fin 2 → ℝ :=
  ![(ζNext - ζ) * cotFactor i t - ζ * t ^ 4 * slope x, ζNext]

/-- The canceled coordinate formula defining the normalized gradient change. -/
theorem stepW_def (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ) :
    stepW i t x ζ ζNext =
      ![(ζNext - ζ) * cotFactor i t - ζ * t ^ 4 * slope x, ζNext] := by
  -- The canceled gradient-change vector is its displayed two-entry vector.
  rfl

/-- The canceled matrix representing `S_t R(stageAngle i t)ᵀ S_t⁻¹`. -/
def rotation (i : Fin 2) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (stageAngle i t), t ^ 4 * sinFactor i t;
    -sinFactor i t, Real.cos (stageAngle i t)]

/-- The canceled coordinate formula defining the normalized rotation matrix. -/
theorem rotation_def (i : Fin 2) (t : ℝ) :
    rotation i t =
      !![Real.cos (stageAngle i t), t ^ 4 * sinFactor i t;
        -sinFactor i t, Real.cos (stageAngle i t)] := by
  -- The normalized rotation is defined by this explicit matrix.
  rfl

/-- The normalized secant scalar `bar vᵀ bar w`. -/
def stageSigma (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ) : ℝ :=
  stepV x ⬝ᵥ stepW i t x ζ ζNext

/-- The dot-product formula defining `stageSigma`. -/
theorem stageSigma_def (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) :
    stageSigma i t x ζ ζNext = stepV x ⬝ᵥ stepW i t x ζ ζNext := by
  -- Expose the dot-product definition of the secant scalar.
  rfl

/-- One exact normalized DFP matrix update with canceled rotation factors. -/
def stageMatrix (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let X := RealSymmetric2.matrix x.1 x.2.1 x.2.2
  let v := stepV x
  let w := stepW i t x ζ ζNext
  let σ := stageSigma i t x ζ ζNext
  let P := rotation i t
  P *
    ((1 - σ⁻¹ • Matrix.vecMulVec w v) * X *
      (1 - σ⁻¹ • Matrix.vecMulVec v w) + σ⁻¹ • Matrix.vecMulVec w w) *
    P.transpose

/-- The exact normalized bracket formula defining `stageMatrix`. -/
theorem stageMatrix_def (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) :
    stageMatrix i t x ζ ζNext =
      let X := RealSymmetric2.matrix x.1 x.2.1 x.2.2
      let v := stepV x
      let w := stepW i t x ζ ζNext
      let σ := stageSigma i t x ζ ζNext
      let P := rotation i t
      P *
        ((1 - σ⁻¹ • Matrix.vecMulVec w v) * X *
          (1 - σ⁻¹ • Matrix.vecMulVec v w) + σ⁻¹ • Matrix.vecMulVec w w) *
        P.transpose := by
  -- Unfold only the named components of the normalized stage.
  rfl

/-- The factored DFP bracket built from a matrix, two vectors, and a secant
   scalar. -/
private def dfpBracket (X : Matrix (Fin 2) (Fin 2) ℝ)
    (v w : Fin 2 → ℝ) (σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 - σ⁻¹ • Matrix.vecMulVec w v) * X *
      (1 - σ⁻¹ • Matrix.vecMulVec v w) +
    σ⁻¹ • Matrix.vecMulVec w w

/-- The normalized stage is a rotation congruence of its factored DFP bracket. -/
private lemma stageMatrixBracketFormula (i : Fin 2) (t : ℝ)
    (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ) :
    stageMatrix i t x ζ ζNext =
      rotation i t *
        dfpBracket (RealSymmetric2.matrix x.1 x.2.1 x.2.2)
          (stepV x) (stepW i t x ζ ζNext) (stageSigma i t x ζ ζNext) *
        (rotation i t).transpose := by
  -- Expose the bracket without expanding any of its rank-one terms.
  rfl

/-- The raw polar update is a rotation congruence of the factored DFP bracket. -/
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

/-- The factored DFP bracket is Hermitian whenever its base matrix is Hermitian. -/
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

/-- The factored DFP bracket is covariant under symmetric mutually inverse
   changes of coordinates. -/
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

/-- A normalized stage matrix is Hermitian. -/
theorem stageMatrix_isHermitian (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) :
    (stageMatrix i t x ζ ζNext).IsHermitian := by
  -- First expose the stage's named base matrix, vectors, scalar, and rotation.
  rw [stageMatrix_def]
  dsimp
  let X := RealSymmetric2.matrix x.1 x.2.1 x.2.2
  let v := stepV x
  let w := stepW i t x ζ ζNext
  let σ := stageSigma i t x ζ ζNext
  let P := rotation i t
  have hBracket : (dfpBracket X v w σ).IsHermitian :=
    dfpBracket_isHermitian X v w σ
      (RealSymmetric2.matrix_isHermitian x.1 x.2.1 x.2.2)
  have hStage := Matrix.isHermitian_mul_mul_conjTranspose P hBracket
  -- The real conjugate transpose is ordinary transpose, matching the definition.
  change (P * dfpBracket X v w σ * P.transpose).IsHermitian
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hStage

/-- The coordinate triple produced by one normalized matrix stage. -/
def stage (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ ζNext : ℝ) : ℝ × ℝ × ℝ :=
  let X := stageMatrix i t x ζ ζNext
  (X 0 0, X 0 1, X 1 1)

/-- The selected entries of `stageMatrix` form the output of `stage`. -/
theorem stage_apply (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ) :
    stage i t x ζ ζNext =
      let X := stageMatrix i t x ζ ζNext
      (X 0 0, X 0 1, X 1 1) := by
  -- The stage output is the selected matrix-entry triple.
  rfl

/-- The shared odd-stage radial multiplier determined at a cycle boundary. -/
def feedback (L κ t : ℝ) (x₀ : ℝ × ℝ × ℝ) : ℝ :=
  Real.exp (-L * (κ / x₀.1) ^ 2 * t ^ 3)

/-- The cubic formula defining the feedback multiplier. -/
theorem feedback_def (L κ t : ℝ) (x₀ : ℝ × ℝ × ℝ) :
    feedback L κ t x₀ = Real.exp (-L * (κ / x₀.1) ^ 2 * t ^ 3) := by
  -- The feedback multiplier is defined by the cubic exponential formula.
  rfl

/-- A selected cycle stage using the same boundary feedback in both phases. -/
def cycleStage (L κ : ℝ) (i : Fin 2) (t : ℝ)
    (x₀ x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let ζOdd := feedback L κ t x₀
  stage i t x (![1, ζOdd] i) (![ζOdd, 1] i)

/-- The phase-selected formula defining `cycleStage`. -/
theorem cycleStage_apply (L κ : ℝ) (i : Fin 2) (t : ℝ)
    (x₀ x : ℝ × ℝ × ℝ) :
    cycleStage L κ i t x₀ x =
      let ζOdd := feedback L κ t x₀
      stage i t x (![1, ζOdd] i) (![ζOdd, 1] i) := by
  -- Unfold the shared odd-stage feedback parameter.
  rfl

/-- The two consecutive normalized stages before changing the boundary scale. -/
def twoStep (L κ t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let x₁ := cycleStage L κ 0 t x x
  cycleStage L κ 1 t x x₁

/-- The two-phase composition formula defining `twoStep`. -/
theorem twoStep_def (L κ t : ℝ) (x : ℝ × ℝ × ℝ) :
    twoStep L κ t x =
      cycleStage L κ 1 t x (cycleStage L κ 0 t x x) := by
  -- The two-step map is the stated composition of its two phases.
  rfl

/-- Change normalized coordinates from scale `t` to scale `nextScale t`. -/
def rescale (t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let ρ := rescaleFactor t
  (ρ ^ 2 * x.1, ρ * x.2.1, x.2.2)

/-- The coordinate formula defining the boundary rescaling. -/
theorem rescale_apply (t : ℝ) (x : ℝ × ℝ × ℝ) :
    rescale t x =
      (rescaleFactor t ^ 2 * x.1, rescaleFactor t * x.2.1, x.2.2) := by
  -- Unfold the boundary rescaling coordinates.
  rfl

/-- The normalized two-stage map followed by boundary rescaling. -/
def map (L κ t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  rescale t (twoStep L κ t x)

/-- The defining composition of the normalized map. -/
theorem map_def (L κ t : ℝ) (x : ℝ × ℝ × ℝ) :
    map L κ t x = rescale t (twoStep L κ t x) := by
  -- The normalized map is defined as rescaling after two stages.
  rfl

/-- The limiting one-stage coordinate update with angular coefficient `c`. -/
def leadingStage (c : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.1, x.1 * (slope x - c), 1 + x.1 * (slope x - c) ^ 2)

/-- The three coordinate formulas defining the limiting stage map. -/
theorem leadingStage_apply (c : ℝ) (x : ℝ × ℝ × ℝ) :
    leadingStage c x =
      (x.1, x.1 * (x.2.2 / x.2.1 - c),
        1 + x.1 * (x.2.2 / x.2.1 - c) ^ 2) := by
  -- Replace the named slope by its quotient definition.
  rfl

/-- Hermitian coordinate reconstruction is conjugation by `scaleMatrix t`. -/
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
  fin_cases i <;> fin_cases j
  -- Expand the two diagonal scale factors and normalize the finite sums.
  all_goals simp [coordinates, scaleMatrix, Matrix.mul_apply,
    Matrix.of_apply, Matrix.vecMul, Matrix.mulVec, Fin.sum_univ_two,
    Matrix.cons_dotProduct_cons, Matrix.dotProduct_cons, Matrix.cons_dotProduct,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, hsymm] <;> ring

/-- At positive scale, normalized displacement is inverse-scale transport of `stepVOf`. -/
theorem stepV_eq_invScaleMatrix_mulVec (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ht : 0 < t) :
    stepV (coordinates t Z) = invScaleMatrix t *ᵥ DFP.Polar.stepVOf Z := by
  -- Evaluate the two vector entries; only powers of the positive scale are
  -- cancelled, while the matrix quotient remains totalized.
  rw [stepV_def, DFP.Polar.stepVOf_def, DFP.Polar.omegaOf_def]
  funext i
  fin_cases i
  · simp [coordinates, DFP.Polar.Normalized.slope, invScaleMatrix,
      Matrix.mulVec, Matrix.mul_apply,
      Matrix.of_apply, Matrix.cons_dotProduct_cons, Matrix.dotProduct_cons,
      Matrix.cons_dotProduct, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.sum_univ_two]
    field_simp [ht.ne']
  · simp [coordinates, invScaleMatrix, Matrix.mulVec, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- At positive scale, normalized gradient change is scale transport of `stepWOf`. -/
theorem stepW_eq_scaleMatrix_mulVec (i : Fin 2) (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ζ ζNext : ℝ) (ht : 0 < t) :
    stepW i t (coordinates t Z) ζ ζNext =
      scaleMatrix t *ᵥ
        DFP.Polar.stepWOf Z (stageAngle i t) ζ ζNext := by
  -- The normalized slope and cotangent each contribute one scale factor.
  have hSlope :
      t ^ 4 * slope (coordinates t Z) = t ^ 2 * DFP.Polar.omegaOf Z := by
    rw [DFP.Polar.omegaOf_def]
    simp [coordinates, DFP.Polar.Normalized.slope, div_eq_mul_inv, mul_inv_rev]
    field_simp [ht.ne']
  rw [stepW_def, DFP.Polar.stepWOf_def, cotFactor_eq_mul_cot i t ht]
  funext j
  fin_cases j
  · -- Evaluate the radial coordinate before applying the scaled slope identity.
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero, Matrix.mulVec, scaleMatrix, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.dotProduct_cons,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, zero_mul, Matrix.dotProduct_of_isEmpty, add_zero]
    have hterm :
        ζ * t ^ 4 * slope (coordinates t Z) =
          ζ * (t ^ 2 * DFP.Polar.omegaOf Z) := by
      calc
        ζ * t ^ 4 * slope (coordinates t Z) =
            ζ * (t ^ 4 * slope (coordinates t Z)) := by ring
        _ = ζ * (t ^ 2 * DFP.Polar.omegaOf Z) := by rw [hSlope]
    rw [hterm]
    ring
  · simp [scaleMatrix, Matrix.mulVec, Matrix.of_apply, Matrix.dotProduct_cons,
      Matrix.cons_dotProduct, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

/-- At positive scale, the canceled rotation is the exact scaled rotation transport. -/
theorem rotation_eq_scaleMatrix_mul (i : Fin 2) (t : ℝ) (ht : 0 < t) :
    rotation i t =
      scaleMatrix t * (DFP.Polar.rotationMatrix (stageAngle i t)).transpose *
        invScaleMatrix t := by
  -- Recover the ordinary sine quotient on the positive branch, then
  -- evaluate the diagonal conjugation entrywise.
  rw [rotation_def, DFP.Polar.rotationMatrix_def,
    sinFactor_eq_sin_div i t ht]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [scaleMatrix, invScaleMatrix, Matrix.mul_apply, Matrix.of_apply,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.sum_univ_two]
  all_goals field_simp [ht.ne']

/-- Inverse scaling of the displacement and scaling of the gradient change
   preserve the secant scalar. -/
private lemma stageSigma_eq_sigmaOf (i : Fin 2) (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ζ ζNext : ℝ) (ht : 0 < t) :
    stageSigma i t (coordinates t Z) ζ ζNext =
      DFP.Polar.sigmaOf Z (stageAngle i t) ζ ζNext := by
  -- Move the two matrix actions next to each other inside the dot product.
  have hTS : invScaleMatrix t * scaleMatrix t = 1 :=
    mul_eq_one_comm.mp (scaleMatrix_mul_invScaleMatrix t ht.ne')
  rw [stageSigma_def, stepV_eq_invScaleMatrix_mulVec t Z ht,
    stepW_eq_scaleMatrix_mulVec i t Z ζ ζNext ht,
    Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    invScaleMatrix_transpose, hTS, Matrix.vecMul_one,
    DFP.Polar.sigmaOf_def]

/-- A scaled rotation congruence cancels mutually inverse symmetric coordinate
   changes. -/
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

/-- At positive scale, one normalized stage is the exact scaled raw polar update. -/
theorem stageMatrix_eq_scaleMatrix_mul (i : Fin 2) (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ζ ζNext : ℝ)
    (hZ : Z.IsHermitian) (ht : 0 < t) :
    stageMatrix i t (coordinates t Z) ζ ζNext =
      scaleMatrix t *
        DFP.Polar.matrixStep Z (stageAngle i t) ζ ζNext * scaleMatrix t := by
  -- Identify the normalized matrix, vectors, and secant scalar before
  -- transporting the complete factored bracket.
  have hST := scaleMatrix_mul_invScaleMatrix t ht.ne'
  have hTS : invScaleMatrix t * scaleMatrix t = 1 := mul_eq_one_comm.mp hST
  rw [stageMatrixBracketFormula, coordinates_eq_scaleMatrix_mul t Z hZ,
    stepV_eq_invScaleMatrix_mulVec t Z ht,
    stepW_eq_scaleMatrix_mulVec i t Z ζ ζNext ht,
    stageSigma_eq_sigmaOf i t Z ζ ζNext ht,
    dfpBracket_transport _ _ _ _ _ _ hST hTS
      (scaleMatrix_transpose t) (invScaleMatrix_transpose t),
    rotation_eq_scaleMatrix_mul i t ht]
  -- Rotation conjugation cancels the inverse scales left after bracket transport.
  rw [scaledRotationCongruence _ _ _ _ hST hTS
    (scaleMatrix_transpose t) (invScaleMatrix_transpose t),
    matrixStepBracketFormula]

/-- A tangential unit gradient change removes the old tangential and
   off-diagonal bracket data. -/
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

/-- At zero scale, the canceled rotation is the shear with coefficient
   `limitAngle i`. -/
private lemma rotation_zero (i : Fin 2) :
    rotation i 0 = !![1, 0; -limitAngle i, 1] := by
  -- Evaluate the analytic sinc regularization, rather than the singular quotient.
  have hAngle : stageAngle i 0 = 0 := by
    simp only [stageAngle_def, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_mul]
  have hSin : sinFactor i 0 = limitAngle i := by
    rw [sinFactor_def, hAngle, Real.sinc_zero, mul_one,
      stageAngleFactor_def, angleFactor_def, unitRoot_def]
    fin_cases i
    all_goals norm_num [stageWeight_zero, stageWeight_one,
      limitAngle_zero, limitAngle_one]
    all_goals ring
  rw [rotation_def, hAngle, hSin]
  simp only [Real.cos_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_mul]

/-- At zero scale, the unit-multiplier update is the matrix of the limiting
   stage. -/
private lemma stageMatrix_zero (i : Fin 2) (x : ℝ × ℝ × ℝ) :
    stageMatrix i 0 x 1 1 =
      RealSymmetric2.matrix (leadingStage (limitAngle i) x).1
        (leadingStage (limitAngle i) x).2.1
        (leadingStage (limitAngle i) x).2.2 := by
  -- The canceled gradient change and its secant scalar have unit limits.
  have hW : stepW i 0 x 1 1 = ![0, 1] := by
    simp [stepW_def]
  have hSigma : stageSigma i 0 x 1 1 = 1 := by
    rw [stageSigma_def, hW, stepV_def]
    simp
  rw [stageMatrixBracketFormula, hW, hSigma, stepV_def,
    dfpBracketTangentialUnit, rotation_zero]
  -- Conjugation by the limiting shear replaces Q by Q - limitAngle i.
  simp only [leadingStage, RealSymmetric2.matrix_eq]
  ext r c
  fin_cases r
  all_goals fin_cases c
  all_goals simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  all_goals ring

/-- At zero scale, either feedback-controlled stage is its limiting stage map. -/
theorem cycleStage_zero (L κ : ℝ) (i : Fin 2)
    (x₀ x : ℝ × ℝ × ℝ) :
    cycleStage L κ i 0 x₀ x = leadingStage (limitAngle i) x := by
  -- Cubic feedback is one at zero, so both phases use the unit multipliers.
  have hFeedback : feedback L κ 0 x₀ = 1 := by
    simp [feedback_def]
  have hUnit : (![1, 1] : Fin 2 → ℝ) i = 1 := by
    fin_cases i
    all_goals rfl
  rw [cycleStage_apply]
  dsimp only
  rw [hFeedback, hUnit, stage_apply, stageMatrix_zero]
  -- Read off the three coordinates of the limiting symmetric matrix.
  simp only [RealSymmetric2.matrix_eq, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Prod.mk.eta]

end DFP.Polar.Normalized
