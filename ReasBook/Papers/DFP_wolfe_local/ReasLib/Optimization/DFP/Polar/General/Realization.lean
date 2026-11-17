module

public import ReasLib.Optimization.DFP.Polar.General.PhysicalRecurrence
public import ReasLib.Optimization.DFP.Polar.General.Geometry
public import ReasLib.Optimization.DFP.Orbit

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.Polar.General.Parameters

/-- Helper for eq:polar-radii: the paired tail product fixes the limiting
radius at one and divides the even radius by its first factor at odd indices. -/
def radius (p : Parameters) : ℕ → ℝ :=
  Geometry.pairedRadius (fun j ↦ p.radiusRatio (2 * j))
    (fun j ↦ p.radiusRatio (2 * j + 1))

/-- Helper for eq:polar-step-data: the actual source points combine the tail
product radii and prescribed unreduced angles. -/
def point (p : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  p.radius k • DFP.Polar.polarUnit (p.angle k)

/-- Helper for eq:polar-endpoint-data: the prescribed gradients use the same
points and shared exponential feedback as the matrix recurrence. -/
def gradients (p : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  p.zeta k • p.point k

/-- Helper for eq:polar-physical-step: the physical inverse Hessian is the
rotated inverse of the actual source local matrix. -/
def inverseHessian (p : Parameters) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  DFP.Polar.rotationMatrix (p.angle k) * (p.matrix k)⁻¹ *
    (DFP.Polar.rotationMatrix (p.angle k)).transpose

/-- Helper for eq:polar-physical-step: the actual positive step length formula
required by the radial DFP direction calculation. -/
def stepLength (p : Parameters) (k : ℕ) : ℝ :=
  (p.matrix k).det * Real.sin (p.angleIncrement k) /
    (p.zeta k * p.matrix k 0 1 * p.radiusRatio k)

/-- Helper for eq:polar-corrections: the gradient correction is exactly the
prescribed gradient minus the base quadratic gradient. -/
def correction (p : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  (p.zeta k - 1) • p.point k

/-- Helper for eq:polar-support-radii: interpolation radii retain the same
positive scale through both stages of a cycle. -/
def supportRadius (p : Parameters) (κ : ℝ) (k : ℕ) : ℝ :=
  κ * General.scale p.beta p.startIndex (k / 2)

/-- Helper for eq:polar-objective: the source objective is the exact explicit
cutoff sum for these points and gradient corrections. -/
def objective (p : Parameters) (κ : ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  DFP.Polar.InterpolationSum.objective p.point (p.supportRadius κ) p.correction

/-- Helper for eq:polar-radii: the finite paired-radius interface to the
infinite source tail product. -/
theorem radius_def (p : Parameters) :
    p.radius = Geometry.pairedRadius (fun j ↦ p.radiusRatio (2 * j))
      (fun j ↦ p.radiusRatio (2 * j + 1)) := by
  rfl

/-- Helper for eq:polar-step-data: the point formula is the prescribed polar vector. -/
theorem point_def (p : Parameters) (k : ℕ) :
    p.point k = p.radius k • DFP.Polar.polarUnit (p.angle k) := by
  rfl

/-- Helper for eq:polar-endpoint-data: the exact prescribed gradient formula. -/
theorem gradients_def (p : Parameters) (k : ℕ) : p.gradients k = p.zeta k • p.point k := by
  rfl

/-- Helper for eq:polar-corrections: the exact coefficient formula. -/
theorem correction_def (p : Parameters) (k : ℕ) :
    p.correction k = (p.zeta k - 1) • p.point k := by
  rfl

/-- Helper for eq:polar-support-radii: the exact scale of the explicit support ball. -/
theorem supportRadius_def (p : Parameters) (κ : ℝ) (k : ℕ) :
    p.supportRadius κ k = κ * General.scale p.beta p.startIndex (k / 2) := by
  rfl

/-- Helper for eq:polar-objective: the objective uses the same interpolation
data as every geometric and sharpness estimate. -/
theorem objective_def (p : Parameters) (κ : ℝ) :
    p.objective κ = DFP.Polar.InterpolationSum.objective p.point (p.supportRadius κ)
      p.correction := by
  rfl

/-- Helper for eq:polar-radii: interleaving the two actual factor subsequences
recovers the complete source factor sequence. -/
theorem radiusRatio_eq_interleaving (p : Parameters) :
    DFP.twoStepSequence (fun j ↦ p.radiusRatio (2 * j))
      (fun j ↦ p.radiusRatio (2 * j + 1)) = p.radiusRatio := by
  funext k
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [DFP.twoStepSequence_even]
  · rw [DFP.twoStepSequence_odd]

/-- Helper for eq:polar-radii: the actual paired-tail radius satisfies the
source multiplicative recurrence at both phases. -/
theorem radius_recurrence (p : Parameters) (hr : ∀ k, 0 < p.radiusRatio k)
    (hlog : Summable (fun j ↦ Real.log (p.radiusRatio (2 * j) * p.radiusRatio (2 * j + 1))))
    (k : ℕ) : p.radius k = p.radiusRatio k * p.radius (k + 1) := by
  rw [radius_def, Geometry.pairedRadius_recurrence
    (fun j ↦ hr (2 * j)) (fun j ↦ hr (2 * j + 1)) hlog,
    radiusRatio_eq_interleaving]

/-- Helper for lem:polar-geometry: factors greater than one make every actual
radius strictly greater than its limiting unit radius. -/
theorem radius_gt_one (p : Parameters) (hr : ∀ k, 1 < p.radiusRatio k)
    (hlog : Summable (fun j ↦ Real.log (p.radiusRatio (2 * j) * p.radiusRatio (2 * j + 1))))
    (k : ℕ) : 1 < p.radius k := by
  exact Geometry.pairedRadius_gt_one (fun j ↦ hr (2 * j)) (fun j ↦ hr (2 * j + 1)) hlog k

/-- Helper for lem:polar-geometry: the complete actual radius sequence
strictly decreases to its limiting value. -/
theorem radius_strictAnti (p : Parameters) (hr : ∀ k, 1 < p.radiusRatio k)
    (hlog : Summable (fun j ↦ Real.log (p.radiusRatio (2 * j) * p.radiusRatio (2 * j + 1)))) :
    StrictAnti p.radius := by
  exact Geometry.pairedRadius_strictAnti
    (fun j ↦ hr (2 * j)) (fun j ↦ hr (2 * j + 1)) hlog

/-- Helper for lem:polar-geometry: summable cycle logarithms and positive
radial decrements yield convergence of the same actual radii to one. -/
theorem radius_tendsto_one (p : Parameters) (hr : ∀ k, 1 < p.radiusRatio k)
    (hlog : Summable (fun j ↦ Real.log (p.radiusRatio (2 * j) * p.radiusRatio (2 * j + 1)))) :
    Tendsto p.radius atTop (𝓝 1) := by
  exact Geometry.pairedRadius_tendsto_one
    (fun j ↦ hr (2 * j)) (fun j ↦ hr (2 * j + 1)) hlog

/-- Helper for eq:polar-corrections: the same actual correction is zero at
every even point. -/
@[simp]
theorem correction_even (p : Parameters) (j : ℕ) : p.correction (2 * j) = 0 := by
  rw [correction_def, zeta_even, sub_self, zero_smul]


/-- Helper for eq:polar-physical-step: the exact rotated inverse matrix formula. -/
theorem inverseHessian_def (p : Parameters) (k : ℕ) :
    p.inverseHessian k = DFP.Polar.rotationMatrix (p.angle k) * (p.matrix k)⁻¹ *
      (DFP.Polar.rotationMatrix (p.angle k)).transpose := by
  rfl

/-- Helper for eq:polar-physical-step: the exact prescribed step length formula. -/
theorem stepLength_def (p : Parameters) (k : ℕ) :
    p.stepLength k = (p.matrix k).det * Real.sin (p.angleIncrement k) /
      (p.zeta k * p.matrix k 0 1 * p.radiusRatio k) := by
  rfl

/-- Helper for eq:polar-angles: the next unreduced angle is its source increment
added to the current angle. -/
theorem angle_succ (p : Parameters) (k : ℕ) :
    p.angle (k + 1) = p.angle k + p.angleIncrement k := by
  rw [angleIncrement_def]
  ring

/-- Helper for lem:polar-geometry: a nonnegative radius is the norm of the
actual polar point. -/
theorem point_norm (p : Parameters) (k : ℕ) (hr : 0 ≤ p.radius k) :
    ‖p.point k‖ = p.radius k := by
  rw [point_def, norm_smul, DFP.Polar.PointGeometry.polarUnit_norm, Real.norm_eq_abs,
    abs_of_nonneg hr, mul_one]

/-- Helper for eq:polar-physical-step: every physical inverse Hessian is
positive definite when its actual local matrix is positive definite. -/
theorem inverseHessian_posDef (p : Parameters) (k : ℕ)
    (hZ : (p.matrix k).PosDef) : (p.inverseHessian k).PosDef := by
  rw [inverseHessian_def]
  exact DFP.Polar.PhysicalRealization.conjugate_posDef _ _
    (DFP.Polar.PhysicalRealization.rotation_orthogonal _) hZ.inv

/-- Helper for eq:polar-physical-step: the prescribed step length is positive
under the proved source local feasibility conditions. -/
theorem stepLength_pos (p : Parameters) (k : ℕ)
    (hZ : (p.matrix k).PosDef) (hC : 0 < p.matrix k 0 1)
    (hsin : 0 < Real.sin (p.angleIncrement k)) (hr : 0 < p.radiusRatio k) :
    0 < p.stepLength k := by
  rw [stepLength_def]
  exact div_pos (mul_pos hZ.det_pos hsin) (mul_pos (mul_pos (p.zeta_pos k) hC) hr)

/-- Helper for eq:polar-physical-step: the exact actual chord satisfies the
source DFP search equation with the prescribed step length and gradient. -/
theorem chord_search (p : Parameters) (k : ℕ)
    (hZ : (p.matrix k).PosDef) (hC : 0 < p.matrix k 0 1) (hr : 0 < p.radiusRatio k)
    (hbalance : p.radius k = p.radiusRatio k * p.radius (k + 1)) :
    WithLp.ofLp (p.point (k + 1) - p.point k) =
      (-p.stepLength k) • (p.inverseHessian k *ᵥ WithLp.ofLp (p.gradients k)) := by
  have hb : p.radius (k + 1) *
      DFP.Polar.radiusRatioOf (p.matrix k) (p.angleIncrement k) = p.radius k := by
    rw [← radiusRatio_def, mul_comm]
    exact hbalance.symm
  have hrOf : DFP.Polar.radiusRatioOf (p.matrix k) (p.angleIncrement k) ≠ 0 := by
    simpa only [radiusRatio_def] using hr.ne'
  rw [point_def, point_def, angle_succ, stepLength_def, inverseHessian_def,
    gradients_def, point_def, radiusRatio_def]
  exact DFP.Polar.PhysicalRealization.search_step _ _ _ _ _ _ hb hZ.isHermitian
    hC.ne' hZ.det_pos.ne' (p.zeta_pos k).ne' hrOf

/-- Helper for eq:polar-physical-step: the actual chord and actual gradient
change have positive curvature whenever the local source scalar is positive. -/
theorem secant_pairing_pos (p : Parameters) (k : ℕ)
    (hbalance : p.radius k = p.radiusRatio k * p.radius (k + 1))
    (hr : 0 < p.radius (k + 1)) (hsin : 0 < Real.sin (p.angleIncrement k))
    (hσ : 0 < DFP.Polar.sigmaOf (p.matrix k) (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1))) :
    0 < WithLp.ofLp (p.point (k + 1) - p.point k) ⬝ᵥ
      WithLp.ofLp (p.gradients (k + 1) - p.gradients k) := by
  have hb : p.radius (k + 1) *
      DFP.Polar.radiusRatioOf (p.matrix k) (p.angleIncrement k) = p.radius k := by
    rw [← radiusRatio_def, mul_comm]
    exact hbalance.symm
  rw [point_def, point_def, gradients_def, gradients_def, point_def, point_def, angle_succ]
  exact DFP.Polar.PhysicalRealization.secant_pairing_pos _ _ _ _ _ _ _ hb hr hsin hσ

/-- Helper for eq:polar-physical-step: the actual rotated inverse matrices
satisfy the inverse DFP update for the same physical chord and secant pair. -/
theorem inverseHessian_step (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (k : ℕ)
    (hbalance : p.radius k = p.radiusRatio k * p.radius (k + 1))
    (hZ : (p.matrix k).PosDef) (hr : 0 < p.radius (k + 1))
    (hsin : 0 < Real.sin (p.angleIncrement k))
    (hσ : 0 < DFP.Polar.sigmaOf (p.matrix k) (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1))) :
    p.inverseHessian (k + 1) = Matrix.inverseDFPUpdate (p.inverseHessian k)
      (WithLp.ofLp (p.point (k + 1) - p.point k))
      (WithLp.ofLp (p.gradients (k + 1) - p.gradients k)) := by
  have hb : p.radius (k + 1) *
      DFP.Polar.radiusRatioOf (p.matrix k) (p.angleIncrement k) = p.radius k := by
    rw [← radiusRatio_def, mul_comm]
    exact hbalance.symm
  rw [inverseHessian_def, matrix_step p hβ hstart k, angle_succ,
    inverseHessian_def, point_def, point_def, gradients_def, gradients_def,
    point_def, point_def, angle_succ]
  exact DFP.Polar.PhysicalRealization.physicalInverseHessian_step _ _ _ _ _ _ _
    hb hZ hr hsin hσ

/-- Helper for eq:polar-endpoint-data: interpolation recovers the exact
prescribed actual gradients at every source point. -/
theorem gradient_objective_center (p : Parameters) (κ : ℝ)
    (h : DFP.Polar.InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction) (k : ℕ) :
    gradient (p.objective κ) (p.point k) = p.gradients k := by
  rw [objective_def, DFP.Polar.InterpolationSum.gradient_objective_center h k,
    correction_def, gradients_def, sub_smul, one_smul]
  abel

/-- Helper for eq:polar-physical-step: the canonical scaled direction equals
the actual source chord. -/
theorem steps_eq_chord (p : Parameters) (k : ℕ)
    (hsearch : WithLp.ofLp (p.point (k + 1) - p.point k) =
      (-p.stepLength k) • (p.inverseHessian k *ᵥ WithLp.ofLp (p.gradients k))) :
    DFP.steps p.stepLength (DFP.directions p.inverseHessian p.gradients) k =
      p.point (k + 1) - p.point k := by
  apply WithLp.ofLp_injective
  simpa only [DFP.steps_apply, DFP.directions_apply, WithLp.ofLp_smul,
    WithLp.ofLp_neg, WithLp.ofLp_toLp, neg_smul, smul_neg] using hsearch.symm


/-- Helper for eq:polar-endpoint-data: the prescribed gradient equals the
base gradient plus the exact interpolation coefficient. -/
theorem point_add_correction (p : Parameters) (k : ℕ) :
    p.point k + p.correction k = p.gradients k := by
  rw [correction_def, gradients_def, sub_smul, one_smul]
  abel

/-- Helper for eq:polar-endpoint-data: the explicit interpolated objective
has the actual prescribed source gradient, with a differentiability certificate. -/
theorem hasGradientAt_objective_center (p : Parameters) (κ : ℝ)
    (h : DFP.Polar.InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction) (k : ℕ) :
    HasGradientAt (p.objective κ) (p.gradients k) (p.point k) := by
  rw [objective_def, ← point_add_correction]
  exact DFP.Polar.InterpolationSum.hasGradientAt_objective_center h k

/-- Helper for thm:main: the exact source sequences form a certified classical
DFP orbit after interpolation. All geometric regularity comes from the explicit
cutoff construction and every update comes from the original raw recurrence. -/
theorem sourceOrbit (p : Parameters) (κ : ℝ) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex)
    (hGeometry : DFP.Polar.InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction)
    (hZ : ∀ k, (p.matrix k).PosDef) (hC : ∀ k, 0 < p.matrix k 0 1)
    (hSin : ∀ k, 0 < Real.sin (p.angleIncrement k))
    (hFactor : ∀ k, 1 < p.radiusRatio k)
    (hSigma : ∀ k, 0 < DFP.Polar.sigmaOf (p.matrix k) (p.angleIncrement k)
      (p.zeta k) (p.zeta (k + 1)))
    (hLog : Summable (fun j ↦ Real.log (p.radiusRatio (2 * j) * p.radiusRatio (2 * j + 1)))) :
    DFP.IsOrbit (p.objective κ) p.stepLength p.point p.gradients p.inverseHessian := by
  have hr : ∀ k, 0 < p.radiusRatio k := fun k ↦ zero_lt_one.trans (hFactor k)
  have hbalance := p.radius_recurrence hr hLog
  have hsearch (k : ℕ) := p.chord_search k (hZ k) (hC k) (hr k) (hbalance k)
  have hstep (k : ℕ) := p.steps_eq_chord k (hsearch k)
  constructor
  · intro k
    exact p.stepLength_pos k (hZ k) (hC k) (hSin k) (hr k)
  · exact p.hasGradientAt_objective_center κ hGeometry
  · intro k
    rw [hstep k]
    abel
  · intro k
    rw [hstep k, DFP.gradientChanges_apply]
    exact p.inverseHessian_step hβ hstart k (hbalance k) (hZ k)
      (zero_lt_one.trans (p.radius_gt_one hFactor hLog (k + 1))) (hSin k) (hSigma k)

/-- Helper for thm:main: the canonical source secant denominators are nonzero,
using the actual chord and actual prescribed gradients. -/
theorem sourceSecantDenominator_ne (p : Parameters)
    (hZ : ∀ k, (p.matrix k).PosDef) (hC : ∀ k, 0 < p.matrix k 0 1)
    (hSin : ∀ k, 0 < Real.sin (p.angleIncrement k))
    (hFactor : ∀ k, 1 < p.radiusRatio k)
    (hSigma : ∀ k, 0 < DFP.Polar.sigmaOf (p.matrix k) (p.angleIncrement k)
      (p.zeta k) (p.zeta (k + 1)))
    (hLog : Summable (fun j ↦ Real.log (p.radiusRatio (2 * j) * p.radiusRatio (2 * j + 1))))
    (k : ℕ) :
    WithLp.ofLp (DFP.steps p.stepLength (DFP.directions p.inverseHessian p.gradients) k) ⬝ᵥ
      WithLp.ofLp (DFP.gradientChanges p.gradients k) ≠ 0 := by
  have hr : ∀ k, 0 < p.radiusRatio k := fun k ↦ zero_lt_one.trans (hFactor k)
  have hbalance := p.radius_recurrence hr hLog
  rw [p.steps_eq_chord k (p.chord_search k (hZ k) (hC k) (hr k) (hbalance k)),
    DFP.gradientChanges_apply]
  exact (p.secant_pairing_pos k (hbalance k)
    (zero_lt_one.trans (p.radius_gt_one hFactor hLog (k + 1))) (hSin k) (hSigma k)).ne'


/-- Helper for thm:main: the actual source gradient norm is the same
positive radial multiplier times the same tail-product radius. -/
theorem gradients_norm (p : Parameters) (k : ℕ) (hr : 0 ≤ p.radius k) :
    ‖p.gradients k‖ = p.zeta k * p.radius k := by
  rw [gradients_def, norm_smul, point_norm p k hr, Real.norm_eq_abs,
    abs_of_nonneg (p.zeta_pos k).le]

/-- Helper for thm:main: the source radius and multiplier limits give the
exact actual gradient-norm limit one. -/
theorem gradients_norm_tendsto_one (p : Parameters) (hr : ∀ k, 0 ≤ p.radius k)
    (hradius : Tendsto p.radius atTop (𝓝 1)) (hzeta : Tendsto p.zeta atTop (𝓝 1)) :
    Tendsto (fun k ↦ ‖p.gradients k‖) atTop (𝓝 1) := by
  simpa only [gradients_norm p _ (hr _), one_mul] using hzeta.mul hradius

/-- Helper for eq:polar-endpoint-data: the same explicit objective has the
source prescribed half squared radius values at every interpolation center. -/
theorem objective_center_value (p : Parameters) (κ : ℝ)
    (hGeometry : DFP.Polar.InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction)
    (k : ℕ) (hr : 0 ≤ p.radius k) :
    p.objective κ (p.point k) = (1 / 2 : ℝ) * p.radius k ^ 2 := by
  rw [objective_def, DFP.Polar.InterpolationSum.objective_center hGeometry, point_norm p k hr]

end DFP.Polar.General.Parameters
