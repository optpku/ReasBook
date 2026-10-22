/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ReasLib.Geometry.Euclidean.Plane.Rotation
public import ReasLib.Optimization.DFP.Iteration
public import ReasLib.Optimization.DFP.Polar.CycleFamily

public section

noncomputable section

open scoped Matrix

namespace DFP.Polar

/-- The starting index and cycle parameter of a prescribed polar recurrence. -/
structure Parameters where
  startIndex : ℕ
  cycleParameter : ℝ

namespace Parameters

/-- Construct polar recurrence parameters from a starting index and cycle parameter. -/
def of (j₀ : ℕ) (νStar : ℝ) : Parameters where
  startIndex := j₀
  cycleParameter := νStar

/-- The starting index stored by `Parameters.of`. -/
@[simp]
theorem of_startIndex (j₀ : ℕ) (νStar : ℝ) :
    (of j₀ νStar).startIndex = j₀ := by
  -- Reduce the constructor projection to the prescribed starting index.
  rfl

/-- The cycle parameter stored by `Parameters.of`. -/
@[simp]
theorem of_cycleParameter (j₀ : ℕ) (νStar : ℝ) :
    (of j₀ νStar).cycleParameter = νStar := by
  -- Reduce the constructor projection to the prescribed cycle parameter.
  rfl

end Parameters

/-- The unit vector with unreduced real polar angle `θ`. -/
def polarUnit (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos θ, Real.sin θ]

/-- The radial coordinate of `polarUnit`. -/
@[simp]
theorem polarUnit_apply_zero (θ : ℝ) :
    polarUnit θ 0 = Real.cos θ := by
  -- Evaluate the first coordinate of the explicit polar vector.
  rfl

/-- The tangential coordinate of `polarUnit`. -/
@[simp]
theorem polarUnit_apply_one (θ : ℝ) :
    polarUnit θ 1 = Real.sin θ := by
  -- Evaluate the second coordinate of the explicit polar vector.
  rfl

/-- The explicit rotation matrix for an unreduced real angle. -/
def rotationMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The cosine-sine formula for the real-angle rotation matrix. -/
theorem rotationMatrix_def (θ : ℝ) :
    rotationMatrix θ = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  -- Expose the four entries of the prescribed rotation matrix.
  rfl

/-- The real-angle rotation matrix agrees with the oriented-angle rotation matrix after
coercion, while its input remains an unreduced real angle. -/
theorem rotationMatrix_eq_euclideanPlane (θ : ℝ) :
    rotationMatrix θ = EuclideanPlane.rotationMatrix (θ : Real.Angle) := by
  -- Replace the opaque imported matrix by the matrix of its bundled rotation.
  rw [rotationMatrix_def, ← EuclideanPlane.toMatrix_rotation]
  -- Compute the four entries through the public rotation and perpendicular-vector formulas.
  ext i j
  fin_cases i
  · fin_cases j
    · simp [LinearMap.toMatrix_apply, EuclideanPlane.rotation_apply,
        EuclideanPlane.perp_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
    · simp [LinearMap.toMatrix_apply, EuclideanPlane.rotation_apply,
        EuclideanPlane.perp_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
  · fin_cases j
    · simp [LinearMap.toMatrix_apply, EuclideanPlane.rotation_apply,
        EuclideanPlane.perp_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
    · simp [LinearMap.toMatrix_apply, EuclideanPlane.rotation_apply,
        EuclideanPlane.perp_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]

namespace Parameters

/-- The cubic scale `t_j = (j₀ + j)^(-1/3)`. -/
def scale (p : Parameters) (j : ℕ) : ℝ :=
  ((p.startIndex + j : ℕ) : ℝ) ^ (-(1 : ℝ) / 3)

/-- The formula defining the cubic scale. -/
theorem scale_def (p : Parameters) (j : ℕ) :
    p.scale j = ((p.startIndex + j : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  -- Unfold the prescribed cubic scale at cycle `j`.
  rfl

/-- The prescribed even unreduced polar angle. -/
def evenAngle (p : Parameters) (j : ℕ) : ℝ :=
  2 * Real.pi * ((p.startIndex + j : ℕ) : ℝ) ^ ((1 : ℝ) / 3)

/-- The formula defining the prescribed even angle. -/
theorem evenAngle_def (p : Parameters) (j : ℕ) :
    p.evenAngle j =
      2 * Real.pi * ((p.startIndex + j : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
  -- Unfold the prescribed unreduced angle at an even iterate.
  rfl

/-- The prescribed odd angle with weights `1/3` and `2/3` on consecutive even angles. -/
def oddAngle (p : Parameters) (j : ℕ) : ℝ :=
  (p.evenAngle j + 2 * p.evenAngle (j + 1)) / 3

/-- The weighted formula defining the prescribed odd angle. -/
theorem oddAngle_def (p : Parameters) (j : ℕ) :
    p.oddAngle j = (p.evenAngle j + 2 * p.evenAngle (j + 1)) / 3 := by
  -- Unfold the weighted interpolation between consecutive even angles.
  rfl

/-- The full unreduced angle sequence interleaving the even and odd angles. -/
def angle (p : Parameters) : ℕ → ℝ :=
  DFP.twoStepSequence p.evenAngle p.oddAngle

/-- The even terms of the prescribed angle sequence. -/
@[simp]
theorem angle_even (p : Parameters) (j : ℕ) :
    p.angle (2 * j) = p.evenAngle j := by
  -- Select the boundary term of the interleaved angle sequence.
  simpa only [angle] using DFP.twoStepSequence_even p.evenAngle p.oddAngle j

/-- The odd terms of the prescribed angle sequence. -/
@[simp]
theorem angle_odd (p : Parameters) (j : ℕ) :
    p.angle (2 * j + 1) = p.oddAngle j := by
  -- Select the intermediate term of the interleaved angle sequence.
  simpa only [angle] using DFP.twoStepSequence_odd p.evenAngle p.oddAngle j

/-- The selected normalization factor `K_*`. -/
def kStar (p : Parameters) : ℝ :=
  cycleK p.cycleParameter

/-- The selected normalization factor is `cycleK` at the cycle parameter. -/
theorem kStar_def (p : Parameters) :
    p.kStar = cycleK p.cycleParameter := by
  -- Reduce the selected normalization factor to the rational cycle family.
  rfl

/-- The selected limiting-cycle coordinate `w_*`. -/
def wStar (p : Parameters) : ℝ :=
  cycleW p.cycleParameter

/-- The selected limiting-cycle coordinate is `cycleW` at the cycle parameter. -/
theorem wStar_def (p : Parameters) :
    p.wStar = cycleW p.cycleParameter := by
  -- Reduce the selected cycle coordinate to the rational cycle family.
  rfl

/-- The cubic feedback rate `L = 4a / (9ν_*)`. -/
def feedbackRate (p : Parameters) : ℝ :=
  4 * baseAngle / (9 * p.cycleParameter)

/-- The formula defining the cubic feedback rate. -/
theorem feedbackRate_def (p : Parameters) :
    p.feedbackRate = 4 * baseAngle / (9 * p.cycleParameter) := by
  -- Unfold the cubic feedback rate selected from the cycle parameter.
  rfl

/-- The initial local inverse-Hessian matrix of the polar recurrence. -/
def initialMatrix (p : Parameters) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.kStar / p.scale 0 ^ 4, p.kStar * p.wStar / p.scale 0 ^ 2;
    p.kStar * p.wStar / p.scale 0 ^ 2, 1 + p.kStar * p.wStar ^ 2]

/-- The explicit formula for the initial local inverse-Hessian matrix. -/
theorem initialMatrix_def (p : Parameters) :
    p.initialMatrix =
      !![p.kStar / p.scale 0 ^ 4, p.kStar * p.wStar / p.scale 0 ^ 2;
        p.kStar * p.wStar / p.scale 0 ^ 2, 1 + p.kStar * p.wStar ^ 2] := by
  -- Expose the four entries of the prescribed initial matrix.
  rfl

end Parameters

/-- The local ratio `ω = Z₂₂ / Z₁₂`, using zero-based `Fin 2` indices. -/
def omegaOf (Z : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Z 1 1 / Z 0 1

/-- The matrix-entry formula defining `omegaOf`. -/
theorem omegaOf_def (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    omegaOf Z = Z 1 1 / Z 0 1 := by
  -- Unfold the ratio of the tangential and off-diagonal entries.
  rfl

/-- The radius factor determined by a local matrix and angle increment. -/
def radiusRatioOf (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ : ℝ) : ℝ :=
  Real.cos δ + omegaOf Z * Real.sin δ

/-- The formula defining the local radius factor. -/
theorem radiusRatioOf_def (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ : ℝ) :
    radiusRatioOf Z δ = Real.cos δ + omegaOf Z * Real.sin δ := by
  -- Unfold the radius ratio determined by the local matrix and angle increment.
  rfl

/-- The normalized local displacement vector associated with a matrix. -/
def stepVOf (Z : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → ℝ :=
  ![-omegaOf Z, 1]

/-- The coordinate formula for the normalized local displacement vector. -/
theorem stepVOf_def (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    stepVOf Z = ![-omegaOf Z, 1] := by
  -- Expose the two coordinates of the normalized displacement vector.
  rfl

/-- The normalized local gradient-change vector for one polar stage. -/
def stepWOf (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ ζ ζNext : ℝ) : Fin 2 → ℝ :=
  ![(ζNext - ζ) * Real.cot δ - ζ * omegaOf Z, ζNext]

/-- The coordinate formula for the normalized local gradient-change vector. -/
theorem stepWOf_def (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ ζ ζNext : ℝ) :
    stepWOf Z δ ζ ζNext =
      ![(ζNext - ζ) * Real.cot δ - ζ * omegaOf Z, ζNext] := by
  -- Expose the two coordinates of the normalized gradient change.
  rfl

/-- The local secant scalar `σ = vᵀw` for one polar stage. -/
def sigmaOf (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ ζ ζNext : ℝ) : ℝ :=
  stepVOf Z ⬝ᵥ stepWOf Z δ ζ ζNext

/-- The dot-product formula defining the local secant scalar. -/
theorem sigmaOf_def (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ ζ ζNext : ℝ) :
    sigmaOf Z δ ζ ζNext = stepVOf Z ⬝ᵥ stepWOf Z δ ζ ζNext := by
  -- Unfold the secant scalar as the dot product of the stage vectors.
  rfl

/-- The factored and rotated local matrix update for one polar stage. -/
def matrixStep (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ ζ ζNext : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  let R := rotationMatrix δ
  let v := stepVOf Z
  let w := stepWOf Z δ ζ ζNext
  let σ := sigmaOf Z δ ζ ζNext
  R.transpose *
    ((1 - σ⁻¹ • Matrix.vecMulVec w v) * Z *
      (1 - σ⁻¹ • Matrix.vecMulVec v w) + σ⁻¹ • Matrix.vecMulVec w w) * R

/-- The factored formula defining `matrixStep`. -/
theorem matrixStep_def (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ ζ ζNext : ℝ) :
    matrixStep Z δ ζ ζNext =
      let R := rotationMatrix δ
      let v := stepVOf Z
      let w := stepWOf Z δ ζ ζNext
      let σ := sigmaOf Z δ ζ ζNext
      R.transpose *
        ((1 - σ⁻¹ • Matrix.vecMulVec w v) * Z *
          (1 - σ⁻¹ • Matrix.vecMulVec v w) + σ⁻¹ • Matrix.vecMulVec w w) * R := by
  -- Reveal the named stage data while retaining the factored matrix update.
  rfl

namespace Parameters

/-- The even-cycle amplitude computed from a cycle index and current even matrix. -/
def amplitudeOf (p : Parameters) (j : ℕ) (Z : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  p.scale j ^ 4 * Z 0 0

/-- The formula defining the even-cycle amplitude. -/
theorem amplitudeOf_def (p : Parameters) (j : ℕ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    p.amplitudeOf j Z = p.scale j ^ 4 * Z 0 0 := by
  -- Unfold the normalized radial entry at the cycle boundary.
  rfl

/-- The odd radial multiplier computed from the even-cycle amplitude. -/
def oddMultiplierOf (p : Parameters) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.exp
    (-p.feedbackRate * (p.kStar / p.amplitudeOf j Z) ^ 2 * p.scale j ^ 3)

/-- The cubic-feedback formula defining the odd radial multiplier. -/
theorem oddMultiplierOf_def (p : Parameters) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    p.oddMultiplierOf j Z =
      Real.exp
        (-p.feedbackRate * (p.kStar / p.amplitudeOf j Z) ^ 2 * p.scale j ^ 3) := by
  -- Unfold the cubic restoring feedback computed from this even matrix.
  rfl

/-- The first matrix stage of a cycle, using feedback from its even matrix. -/
def firstStageMatrix (p : Parameters) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  matrixStep Z (p.oddAngle j - p.evenAngle j) 1 (p.oddMultiplierOf j Z)

/-- The formula defining the first matrix stage of a cycle. -/
theorem firstStageMatrix_def (p : Parameters) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    p.firstStageMatrix j Z =
      matrixStep Z (p.oddAngle j - p.evenAngle j) 1 (p.oddMultiplierOf j Z) := by
  -- Unfold the first stage using feedback computed from its even input matrix.
  rfl

/-- The next even matrix after two stages sharing feedback from the same even matrix. -/
def nextEvenMatrix (p : Parameters) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let ζOdd := p.oddMultiplierOf j Z
  let ZOdd := matrixStep Z (p.oddAngle j - p.evenAngle j) 1 ζOdd
  matrixStep ZOdd (p.evenAngle (j + 1) - p.oddAngle j) ζOdd 1

/-- The two-stage formula for the next even matrix, with one shared feedback multiplier. -/
theorem nextEvenMatrix_def (p : Parameters) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    p.nextEvenMatrix j Z =
      let ζOdd := p.oddMultiplierOf j Z
      let ZOdd := matrixStep Z (p.oddAngle j - p.evenAngle j) 1 ζOdd
      matrixStep ZOdd (p.evenAngle (j + 1) - p.oddAngle j) ζOdd 1 := by
  -- Expose both stages while preserving their one shared odd multiplier.
  rfl

/-- The recursively prescribed matrices at even iteration indices. -/
def evenMatrix (p : Parameters) : ℕ → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => p.initialMatrix
  | j + 1 => p.nextEvenMatrix j (evenMatrix p j)

/-- The initial value of the recursive even-matrix sequence. -/
@[simp]
theorem evenMatrix_zero (p : Parameters) :
    p.evenMatrix 0 = p.initialMatrix := by
  -- Reduce the recursive even-matrix sequence at its initial index.
  rfl

/-- The successor equation for the recursive even-matrix sequence. -/
theorem evenMatrix_succ (p : Parameters) (j : ℕ) :
    p.evenMatrix (j + 1) = p.nextEvenMatrix j (p.evenMatrix j) := by
  -- Reduce one recursive cycle of the even-matrix sequence.
  rfl

/-- The prescribed matrix at the intermediate odd index of a cycle. -/
def oddMatrix (p : Parameters) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  p.firstStageMatrix j (p.evenMatrix j)

/-- The first-stage formula defining the odd matrix. -/
theorem oddMatrix_def (p : Parameters) (j : ℕ) :
    p.oddMatrix j = p.firstStageMatrix j (p.evenMatrix j) := by
  -- Unfold the intermediate matrix as the first stage of its cycle.
  rfl

/-- The full local-matrix sequence interleaving cycle boundaries and intermediate states. -/
def matrix (p : Parameters) : ℕ → Matrix (Fin 2) (Fin 2) ℝ :=
  DFP.twoStepSequence p.evenMatrix p.oddMatrix

/-- The prescribed matrix at iteration zero. -/
@[simp]
theorem matrix_zero (p : Parameters) :
    p.matrix 0 = p.initialMatrix := by
  -- Select the zeroth boundary term without using the later parity interface.
  calc
    p.matrix 0 = p.evenMatrix 0 := by
      simpa only [matrix, Nat.mul_zero] using
        DFP.twoStepSequence_even p.evenMatrix p.oddMatrix 0
    -- Reduce the boundary recursion at its initial index.
    _ = p.initialMatrix := evenMatrix_zero p

/-- The even terms of the prescribed matrix sequence. -/
@[simp]
theorem matrix_even (p : Parameters) (j : ℕ) :
    p.matrix (2 * j) = p.evenMatrix j := by
  -- Select the boundary matrix from the interleaved matrix sequence.
  simpa only [matrix] using DFP.twoStepSequence_even p.evenMatrix p.oddMatrix j

/-- The odd terms of the prescribed matrix sequence. -/
@[simp]
theorem matrix_odd (p : Parameters) (j : ℕ) :
    p.matrix (2 * j + 1) = p.oddMatrix j := by
  -- Select the intermediate matrix from the interleaved matrix sequence.
  simpa only [matrix] using DFP.twoStepSequence_odd p.evenMatrix p.oddMatrix j

/-- The prescribed amplitude sequence at cycle boundaries. -/
def amplitude (p : Parameters) (j : ℕ) : ℝ :=
  p.amplitudeOf j (p.evenMatrix j)

/-- The formula defining the prescribed amplitude sequence. -/
theorem amplitude_def (p : Parameters) (j : ℕ) :
    p.amplitude j = p.amplitudeOf j (p.evenMatrix j) := by
  -- Unfold the amplitude sequence at a cycle boundary.
  rfl

/-- The radial-gradient multiplier sequence with unit even terms and feedback odd terms. -/
def zeta (p : Parameters) : ℕ → ℝ :=
  DFP.twoStepSequence (fun _ ↦ 1) (fun j ↦ p.oddMultiplierOf j (p.evenMatrix j))

/-- The even radial-gradient multipliers equal one. -/
@[simp]
theorem zeta_even (p : Parameters) (j : ℕ) :
    p.zeta (2 * j) = 1 := by
  -- Select the unit boundary multiplier from the interleaved sequence.
  simpa only [zeta] using DFP.twoStepSequence_even
    (fun _ : ℕ ↦ (1 : ℝ)) (fun i ↦ p.oddMultiplierOf i (p.evenMatrix i)) j

/-- The odd radial-gradient multiplier uses the amplitude of the same even cycle. -/
@[simp]
theorem zeta_odd (p : Parameters) (j : ℕ) :
    p.zeta (2 * j + 1) = p.oddMultiplierOf j (p.evenMatrix j) := by
  -- Select the feedback multiplier from the intermediate sequence.
  simpa only [zeta] using DFP.twoStepSequence_odd
    (fun _ : ℕ ↦ (1 : ℝ)) (fun i ↦ p.oddMultiplierOf i (p.evenMatrix i)) j

/-- The unreduced angular increment `δ_k = θ_(k+1) - θ_k`. -/
def angleIncrement (p : Parameters) (k : ℕ) : ℝ :=
  p.angle (k + 1) - p.angle k

/-- The difference formula defining the angular increment. -/
theorem angleIncrement_def (p : Parameters) (k : ℕ) :
    p.angleIncrement k = p.angle (k + 1) - p.angle k := by
  -- Unfold the difference of consecutive unreduced angles.
  rfl

/-- The full local ratio sequence `ω_k`. -/
def omega (p : Parameters) (k : ℕ) : ℝ :=
  omegaOf (p.matrix k)

/-- The matrix-entry formula for the full local ratio sequence. -/
theorem omega_def (p : Parameters) (k : ℕ) :
    p.omega k = omegaOf (p.matrix k) := by
  -- Unfold the local matrix ratio at iteration `k`.
  rfl

/-- The full radius-factor sequence `W_k`, determined before the radii. -/
def radiusRatio (p : Parameters) (k : ℕ) : ℝ :=
  radiusRatioOf (p.matrix k) (p.angleIncrement k)

/-- The formula defining the full radius-factor sequence. -/
theorem radiusRatio_def (p : Parameters) (k : ℕ) :
    p.radiusRatio k = radiusRatioOf (p.matrix k) (p.angleIncrement k) := by
  -- Unfold the radius ratio from the matrix and angular increment sequences.
  rfl

/-- The full normalized displacement-vector sequence `v_k`. -/
def stepV (p : Parameters) (k : ℕ) : Fin 2 → ℝ :=
  stepVOf (p.matrix k)

/-- The formula defining the full normalized displacement-vector sequence. -/
theorem stepV_def (p : Parameters) (k : ℕ) :
    p.stepV k = stepVOf (p.matrix k) := by
  -- Unfold the normalized displacement vector at iteration `k`.
  rfl

/-- The full normalized gradient-change-vector sequence `w_k`. -/
def stepW (p : Parameters) (k : ℕ) : Fin 2 → ℝ :=
  stepWOf (p.matrix k) (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1))

/-- The formula defining the full normalized gradient-change-vector sequence. -/
theorem stepW_def (p : Parameters) (k : ℕ) :
    p.stepW k =
      stepWOf (p.matrix k) (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1)) := by
  -- Unfold the normalized gradient-change vector at iteration `k`.
  rfl

/-- The full local secant-scalar sequence `σ_k`. -/
def sigma (p : Parameters) (k : ℕ) : ℝ :=
  sigmaOf (p.matrix k) (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1))

/-- The formula defining the full local secant-scalar sequence. -/
theorem sigma_def (p : Parameters) (k : ℕ) :
    p.sigma k =
      sigmaOf (p.matrix k) (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1)) := by
  -- Unfold the secant scalar at iteration `k`.
  rfl

/-- Every successor matrix is obtained by the prescribed factored update. -/
theorem matrix_succ (p : Parameters) (k : ℕ) :
    p.matrix (k + 1) =
      matrixStep (p.matrix k) (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1)) := by
  -- Split the flattened sequence into the first and second stages of each cycle.
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · -- At an even index, the successor is exactly the prescribed first stage.
    rw [matrix_odd, matrix_even, angleIncrement_def, angle_odd, angle_even,
      zeta_even, zeta_odd, oddMatrix_def, firstStageMatrix_def]
  · -- At an odd index, normalize the successor to the next cycle boundary.
    have hnext : 2 * j + 1 + 1 = 2 * (j + 1) := by
      omega
    rw [angleIncrement_def, hnext, matrix_even, evenMatrix_succ, nextEvenMatrix_def,
      matrix_odd, oddMatrix_def, firstStageMatrix_def, angle_even, angle_odd,
      zeta_even, zeta_odd]

end Parameters

end DFP.Polar
