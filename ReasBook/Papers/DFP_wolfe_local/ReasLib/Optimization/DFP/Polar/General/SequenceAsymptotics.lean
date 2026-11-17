module

public import ReasLib.Optimization.DFP.Polar.General.Realization
public import ReasLib.Optimization.DFP.Polar.General.Continuation
public import ReasLib.Optimization.DFP.Polar.General.RadiusProducts
public import ReasLib.Optimization.DFP.Polar.General.PlanarCounterexample
public import ReasLib.Optimization.DFP.Polar.General.ActualGeometry
public import ReasLib.Optimization.DFP.Polar.General.WolfeRatios
public import ReasLib.Optimization.DFP.Polar.General.GradientOscillation
public import ReasLib.Optimization.DFP.Polar.SequenceAsymptotics

public section

noncomputable section

open Filter
open scoped Matrix Topology BigOperators Asymptotics

namespace DFP.Polar.General.SequenceAsymptotics

open DFP.Polar.General.WolfeRatios
  (omega_phase_eq angleIncrement_phase_eq phaseMultipliers_eq_zeta)

/-- Helper for sec:known-results: the actual physical step of the same polar trajectory. -/
def step (p : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) := p.point (k + 1) - p.point k

/-- Helper for sec:known-results: the exact source physical gradient change. -/
def secant (p : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  p.gradients (k + 1) - p.gradients k

/-- Helper for sec:known-results: the source secant pairing uses the same step and gradients. -/
def secantPairing (p : Parameters) (k : ℕ) : ℝ := inner ℝ (step p k) (secant p k)

/-- Helper for sec:known-results: Xu's scalar uses the actual same accepted step length. -/
def xuScalar (p : Parameters) (k : ℕ) : ℝ := secantPairing p k / p.stepLength k

/-- Helper for eq:planar-scalar-definition: the actual source secant curvature. -/
def curvature (p : Parameters) (k : ℕ) : ℝ := secantPairing p k / ‖step p k‖ ^ 2

/-- Helper for eq:planar-scalar-definition: the source free coefficient uses
the previous curvature and the current physical inverse Hessian. -/
def freeCoefficient (p : Parameters) (k : ℕ) : ℝ :=
  curvature p (k - 1) * (p.inverseHessian k).det

/-- Helper for sec:known-results: the source consecutive gradient-norm ratio. -/
def gradientRatio (p : Parameters) (k : ℕ) : ℝ :=
  ‖p.gradients (k + 1)‖ / ‖p.gradients k‖

/-- Helper for sec:known-results: each normalized phase is the actual recursively
constructed matrix state, with the shared scale for both phases. -/
def phaseState (p : Parameters) (j : ℕ) (i : Fin 2) : ℝ × ℝ × ℝ :=
  ![p.normalizedEvenState j, p.normalizedOddState j] i

/-- Helper for sec:known-results: the even phase is the actual boundary state. -/
theorem phaseState_zero (p : Parameters) (j : ℕ) :
    phaseState p j 0 = p.normalizedEvenState j := by
  rfl

/-- Helper for sec:known-results: the odd phase is the actual intermediate state. -/
theorem phaseState_one (p : Parameters) (j : ℕ) :
    phaseState p j 1 = p.normalizedOddState j := by
  rfl

/-- Helper for sec:known-results: the actual step is the original point
displacement. This is the reusable source step interface. -/
theorem step_def (p : Parameters) (k : ℕ) : step p k = p.point (k + 1) - p.point k := by
  rfl

/-- Helper for sec:known-results: the actual secant is the original gradient
difference. This is the reusable source secant interface. -/
theorem secant_def (p : Parameters) (k : ℕ) :
    secant p k = p.gradients (k + 1) - p.gradients k := by
  rfl

/-- Helper for sec:known-results: the scalar source secant pairing.
This is its reusable definition interface. -/
theorem secantPairing_def (p : Parameters) (k : ℕ) :
    secantPairing p k = inner ℝ (step p k) (secant p k) := by
  rfl

/-- Helper for sec:known-results: Xu's scalar is the original source secant
pairing divided by the original source step length. -/
theorem xuScalar_def (p : Parameters) (k : ℕ) :
    xuScalar p k = secantPairing p k / p.stepLength k := by
  rfl

/-- Helper for eq:planar-scalar-definition: the exact source secant curvature
is the pairing divided by the squared step norm. -/
theorem curvature_def (p : Parameters) (k : ℕ) :
    curvature p k = secantPairing p k / ‖step p k‖ ^ 2 := by
  rfl

/-- Helper for eq:planar-scalar-definition: the source free coefficient has
the previous curvature and the current inverse Hessian determinant. -/
theorem freeCoefficient_def (p : Parameters) (k : ℕ) :
    freeCoefficient p k = curvature p (k - 1) * (p.inverseHessian k).det := by
  rfl

/-- Helper for sec:known-results: the exact source gradient-norm quotient.
This is its reusable scalar definition interface. -/
theorem gradientRatio_def (p : Parameters) (k : ℕ) :
    gradientRatio p k = ‖p.gradients (k + 1)‖ / ‖p.gradients k‖ := by
  rfl

/-- Helper for sec:known-results: a source-scale lower step bound forces
infinite total length for the actual same trajectory. -/
theorem stepNorm_not_summable_of_lower (p : Parameters) (hβ : 0 < p.beta)
    {lower : ℝ} (hlower : 0 < lower)
    (hbound : ∀ k, lower * scale p.beta p.startIndex (k / 2) ≤ ‖step p k‖) :
    ¬ Summable (fun k ↦ ‖step p k‖) := by
  intro hsum
  have hinjective : Function.Injective (fun j : ℕ ↦ 2 * j) := by
    intro a b hab
    dsimp only at hab
    omega
  have heven := hsum.comp_injective hinjective
  have hcomparison (j : ℕ) : scale p.beta p.startIndex j ≤ lower⁻¹ * ‖step p (2 * j)‖ := by
    have hhalf : 2 * j / 2 = j := by omega
    have h := hbound (2 * j)
    rw [hhalf] at h
    calc
      scale p.beta p.startIndex j =
          lower⁻¹ * (lower * scale p.beta p.startIndex j) := by
        rw [← mul_assoc, inv_mul_cancel₀ hlower.ne', one_mul]
      _ ≤ lower⁻¹ * ‖step p (2 * j)‖ :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hlower.le)
  exact not_summable_scale hβ p.startIndex
    (Summable.of_nonneg_of_le (scale_nonneg p.beta p.startIndex) hcomparison
      (heven.mul_left lower⁻¹))

/-- Helper for sec:known-results: the exact even-to-odd Xu leading coefficient
exceeds the odd coefficient for every selected stable Wolfe base. -/
theorem xuLeadingCoefficient_difference (p : Parameters) :
    p.deltaEven * p.ell - p.deltaOdd = (p.ell - 1) * (p.ell + 1) := by
  rw [p.deltaEven_def, p.deltaOdd_def, baseDeltaEven_def, baseDeltaOdd_def]
  ring

/-- Helper for sec:known-results: the cross-phase Xu limit is strictly larger
than one for every Wolfe pair, with no special fixed numerical threshold. -/
theorem xuJumpLimit_gt_one (p : Parameters) : 1 < p.deltaEven * p.ell / p.deltaOdd := by
  apply (one_lt_div p.deltaOdd_pos).mpr
  have hpositive : 0 < p.ell + 1 := by linarith [p.base.one_lt_ell]
  have hgap : 0 < (p.ell - 1) * (p.ell + 1) :=
    mul_pos (sub_pos.mpr p.base.one_lt_ell) hpositive
  linarith [xuLeadingCoefficient_difference p]

/-- Helper for lem:planar-degeneration: undoing the source diagonal
normalization multiplies determinants by `τ⁻²`. -/
theorem recoverMatrix_det (t : ℝ) (x : ℝ × ℝ × ℝ) :
    (PhysicalRecurrence.recoverMatrix t x).det =
      t⁻¹ ^ 2 * (PhysicalRecurrence.stateMatrix x).det := by
  rw [PhysicalRecurrence.recoverMatrix_apply, PhysicalRecurrence.stateMatrix_def,
    RealSymmetric2.matrix_eq]
  simp [Matrix.det_fin_two]
  ring

/-- Helper for lem:planar-degeneration: the physical inverse Hessian determinant
is the reciprocal of the actual local source determinant. -/
theorem inverseHessian_det (p : Parameters) (k : ℕ) :
    (p.inverseHessian k).det = (p.matrix k).det⁻¹ := by
  rw [p.inverseHessian_def, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    DFP.Polar.SequenceAsymptotics.rotation_det, one_mul, mul_one, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv]

/-- Helper for lem:planar-degeneration: each raw source phase recovers its
actual normalized state using the common cycle scale. -/
theorem matrix_phase_eq_recoverMatrix (p : Parameters) (j : ℕ) (i : Fin 2) :
    p.matrix (2 * j + (i : ℕ)) =
      PhysicalRecurrence.recoverMatrix (p.scale j) (phaseState p j i) := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simp only [Fin.val_zero, add_zero,
      p.matrix_even, phaseState_zero]
    exact p.evenMatrix_eq_recoverMatrix j
  · simp only [Fin.val_one,
      p.matrix_odd, phaseState_one]
    exact p.oddMatrix_eq_recoverMatrix j

/-- Helper for lem:planar-degeneration: the normalized determinant identity
has exactly the source quadratic scale, before any limit is taken. -/
theorem inverseHessian_det_phase (p : Parameters) (j : ℕ) (i : Fin 2) :
    (p.inverseHessian (2 * j + (i : ℕ))).det =
      p.scale j ^ 2 / (PhysicalRecurrence.stateMatrix (phaseState p j i)).det := by
  rw [inverseHessian_det, matrix_phase_eq_recoverMatrix, recoverMatrix_det,
    mul_inv_rev, inv_pow, inv_inv, div_eq_mul_inv]
  ring

/-- Helper for sec:known-results: the actual source phase state is the same
phase input used in the canceled radius and Wolfe observables.
This is a reusable same-trajectory interface. -/
theorem phaseState_eq_phaseInput (p : Parameters) (j : ℕ) (i : Fin 2) :
    phaseState p j i = RadiusBounds.phaseInput p i (p.scale j) (p.inverseIndex j)
      (p.normalizedEvenState j) := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [phaseState_zero, RadiusBounds.phaseInput_zero]
  · rw [phaseState_one, RadiusBounds.phaseInput_one, p.normalizedOddState_apply]

/-- Helper for eq:planar-scalar-definition and sec:known-results: the actual
physical secant pairing is the square of the common chord factor times the
original local normalized secant scalar. This is a reusable source identity. -/
theorem secantPairing_eq (p : Parameters) (k : ℕ)
    (hbalance : p.radius k = p.radiusRatio k * p.radius (k + 1))
    (hsin : Real.sin (p.angleIncrement k) ≠ 0) :
    secantPairing p k = (p.radius (k + 1) * Real.sin (p.angleIncrement k)) ^ 2 *
      DFP.Polar.sigmaOf (p.matrix k) (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1)) := by
  have hb : p.radius (k + 1) * DFP.Polar.radiusRatioOf (p.matrix k) (p.angleIncrement k) =
      p.radius k := by
    rw [← p.radiusRatio_def, mul_comm]
    exact hbalance.symm
  simpa only [secantPairing_def, step_def, secant_def, DFP.Polar.WolfeRatios.inner_eq_dot,
    p.gradients_def, p.point_def, p.angle_succ] using
    DFP.Polar.PhysicalRealization.secant_pairing (p.matrix k) (p.angle k)
      (p.angleIncrement k) (p.radius k) (p.radius (k + 1)) (p.zeta k) (p.zeta (k + 1)) hb hsin

/-- Helper for eq:planar-scalar-definition: the actual squared step norm
uses the same chord factor as the secant pairing and the factor `1+ω²`.
This is a reusable exact source identity. -/
theorem step_norm_sq (p : Parameters) (k : ℕ)
    (hbalance : p.radius k = p.radiusRatio k * p.radius (k + 1)) :
    ‖step p k‖ ^ 2 = (p.radius (k + 1) * Real.sin (p.angleIncrement k)) ^ 2 *
      (1 + DFP.Polar.omegaOf (p.matrix k) ^ 2) := by
  have hb : p.radius (k + 1) * DFP.Polar.radiusRatioOf (p.matrix k) (p.angleIncrement k) =
      p.radius k := by
    rw [← p.radiusRatio_def, mul_comm]
    exact hbalance.symm
  have hcoordinates : WithLp.ofLp (step p k) = DFP.Polar.rotationMatrix (p.angle k) *ᵥ
      ((p.radius (k + 1) * Real.sin (p.angleIncrement k)) • DFP.Polar.stepVOf (p.matrix k)) := by
    rw [step_def, p.point_def, p.point_def, p.angle_succ]
    exact DFP.Polar.PhysicalRealization.chord_eq _ _ _ _ _ hb
  have hnorm : ‖step p k‖ =
      ‖(WithLp.toLp 2 ((p.radius (k + 1) * Real.sin (p.angleIncrement k)) •
        DFP.Polar.stepVOf (p.matrix k)) : EuclideanSpace ℝ (Fin 2))‖ := by
    have h := congrArg (fun v : Fin 2 → ℝ ↦
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖) hcoordinates
    simpa only [WithLp.toLp_ofLp, Matrix.norm_toLp_mulVec_eq_of_mem_orthogonalGroup _
      (DFP.Polar.PhysicalRealization.rotation_orthogonal (p.angle k))] using h
  rw [hnorm, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, DFP.Polar.stepVOf_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- Helper for eq:planar-scalar-definition: exact cancellation of the common
chord factor gives the actual source curvature `σ/(1+ω²)`.
This is a reusable finite identity preceding the asymptotic limit. -/
theorem curvature_eq_sigma_div (p : Parameters) (k : ℕ)
    (hbalance : p.radius k = p.radiusRatio k * p.radius (k + 1))
    (hr : 0 < p.radius (k + 1)) (hsin : Real.sin (p.angleIncrement k) ≠ 0) :
    curvature p k = DFP.Polar.sigmaOf (p.matrix k) (p.angleIncrement k)
      (p.zeta k) (p.zeta (k + 1)) / (1 + DFP.Polar.omegaOf (p.matrix k) ^ 2) := by
  have hfactor : (p.radius (k + 1) * Real.sin (p.angleIncrement k)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero hr.ne' hsin)
  rw [curvature_def, secantPairing_eq p k hbalance hsin, step_norm_sq p k hbalance]
  exact mul_div_mul_left _ _ hfactor

/-- Helper for eq:planar-scalar-definition: the canceled local secant scalar
at the actual input of either source phase.
This is a reusable same-trajectory analytic observable. -/
def phaseSigma (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  Normalized.stageSigma (RadiusBounds.phaseAngle p i v) t
    (RadiusBounds.phaseInput p i t v x) (RadiusBounds.phaseMultipliers p i v x).1
      (RadiusBounds.phaseMultipliers p i v x).2

/-- Helper for eq:planar-scalar-definition: the canceled phase secant scalar
has a scalar formula in the actual slope, cotangent factor, and original
gradient multipliers. This is its reusable finite proof interface. -/
theorem phaseSigma_formula (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseSigma p i t v x =
      -RadiusBounds.phaseSlope p i t v x *
        (((RadiusBounds.phaseMultipliers p i v x).2 -
          (RadiusBounds.phaseMultipliers p i v x).1) *
          Normalized.cotFactor (RadiusBounds.phaseAngle p i v) t -
            (RadiusBounds.phaseMultipliers p i v x).1 * t ^ 2 *
              RadiusBounds.phaseSlope p i t v x) + (RadiusBounds.phaseMultipliers p i v x).2 := by
  simp only [phaseSigma, Normalized.stageSigma_def, Normalized.stepV_def,
    Normalized.stepW_def, RadiusBounds.phaseSlope_def, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul]

/-- Helper for eq:planar-scalar-definition: the exact source canceled secant
scalar equals one at the selected zero-parameter equilibrium.
This is a reusable normalization identity. -/
theorem phaseSigma_at_base (p : Parameters) (i : Fin 2) :
    phaseSigma p i 0 0 p.initialState = 1 := by
  simp only [phaseSigma_formula, RadiusBounds.phaseMultipliers_at_zero, sub_self,
    zero_mul, mul_zero, zero_pow two_ne_zero, zero_add]

/-- Helper for eq:planar-scalar-definition: the canceled source secant scalar
is jointly analytic at zero independent parameters and the actual equilibrium.
This is a reusable analytic interface for its physical limit. -/
theorem phaseSigma_joint_analyticAt (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseSigma p i z.1.1 z.1.2 z.2)
      ((0, 0), p.initialState) := by
  have ht : AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.1) ((0, 0), p.initialState) :=
    analyticAt_fst.comp analyticAt_fst
  have hv : AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.2) ((0, 0), p.initialState) :=
    analyticAt_snd.comp analyticAt_fst
  have ha := (RadiusBounds.phaseAngle_analyticAt p i).comp_of_eq hv rfl
  have hQ := RadiusBounds.phaseSlope_joint_analyticAt p hβ i
  have hmult := RadiusBounds.phaseMultipliers_joint_analyticAt p hβ i
  have hζ := analyticAt_fst.comp hmult
  have hη := analyticAt_snd.comp hmult
  have hzero : RadiusBounds.phaseAngle p i 0 * 0 = 0 := mul_zero _
  have hsinc := Normalized.analyticAt_sinc_zero.comp_of_eq (ha.mul ht) hzero
  have hden : RadiusBounds.phaseAngle p i 0 *
      Real.sinc (RadiusBounds.phaseAngle p i 0 * 0) ≠ 0 := by
    simp only [mul_zero, Real.sinc_zero, mul_one]
    exact (RadiusBounds.phaseAngle_base_pos p hβ i).ne'
  have hcot : AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦
        Normalized.cotFactor (RadiusBounds.phaseAngle p i z.1.2) z.1.1)
      ((0, 0), p.initialState) := by
    simp only [Normalized.cotFactor_def, Normalized.sinFactor_def, Normalized.stageAngle_def]
    exact (Real.analyticAt_cos.comp (ha.mul ht)).div (ha.mul hsinc) hden
  simp only [phaseSigma_formula]
  exact (hQ.neg.mul (((hη.sub hζ).mul hcot).sub ((hζ.mul (ht.pow 2)).mul hQ))).add hη

/-- Helper for eq:planar-scalar-definition: the actual raw secant scalar at
either phase is the canceled scalar on the same recursively constructed
source state. This is a reusable physical normalization bridge. -/
theorem sigma_phase_eq (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) (i : Fin 2) :
    DFP.Polar.sigmaOf (p.matrix (2 * j + (i : ℕ))) (p.angleIncrement (2 * j + (i : ℕ)))
        (p.zeta (2 * j + (i : ℕ))) (p.zeta (2 * j + (i : ℕ) + 1)) =
      phaseSigma p i (p.scale j) (p.inverseIndex j) (p.normalizedEvenState j) := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simpa only [Fin.val_zero, Nat.add_zero, phaseSigma, RadiusBounds.phaseAngle_zero,
      RadiusBounds.phaseInput_zero, RadiusBounds.phaseMultipliers_zero,
      ← p.oddMultiplier_def] using p.sigma_even_eq_normalized hβ hstart j
  · simpa only [Fin.val_one, phaseSigma, RadiusBounds.phaseAngle_one,
      RadiusBounds.phaseInput_one, RadiusBounds.phaseMultipliers_one,
      ← p.normalizedOddState_apply, ← p.oddMultiplier_def] using
      p.sigma_odd_eq_normalized hβ hstart j

/-- Helper for eq:planar-scalar-definition: the canceled source secant scalar
is unchanged when the starting index is increased.
This is a reusable uniformity bridge for the actual trajectory. -/
theorem phaseSigma_withStartIndex (p : Parameters) (j0 : ℕ) (i : Fin 2)
    (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseSigma (p.withStartIndex j0) i t v x = phaseSigma p i t v x := by
  simp only [phaseSigma, RadiusBounds.phaseAngle_withStartIndex,
    RadiusBounds.phaseInput_withStartIndex, RadiusBounds.phaseMultipliers_withStartIndex]

/-- Helper for sec:known-results: the complete independent-parameter input
of the actual chosen recursive source trajectory tends to its genuine base.
This is a reusable same-orbit limit derived from the proved tube. -/
theorem actualInput_tendsto {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    Tendsto (fun j ↦ (((p.withStartIndex j0).scale j, (p.withStartIndex j0).inverseIndex j),
      (p.withStartIndex j0).normalizedEvenState j)) atTop (𝓝 ((0, 0), p.initialState)) := by
  have hlimit := (Continuation.smallParameters_tendsto_zero p hβ j0).prodMk_nhds
    (h.evenState_tendsto hβ hβone)
  simpa only [Parameters.scale_def, Parameters.inverseIndex_def,
    Parameters.withStartIndex_beta, Parameters.withStartIndex_startIndex,
    Continuation.stateAt_def] using hlimit

/-- Helper for eq:planar-scalar-definition: the actual source raw normalized
secant scalar tends to one along either phase, with the original matrices,
angles, and multipliers. This is a reusable same-orbit asymptotic theorem. -/
theorem sigma_phase_tendsto_one {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (hstart : 0 < j0) (i : Fin 2) :
    Tendsto (fun j ↦ DFP.Polar.sigmaOf ((p.withStartIndex j0).matrix (2 * j + (i : ℕ)))
      ((p.withStartIndex j0).angleIncrement (2 * j + (i : ℕ)))
      ((p.withStartIndex j0).zeta (2 * j + (i : ℕ)))
      ((p.withStartIndex j0).zeta (2 * j + (i : ℕ) + 1))) atTop (𝓝 1) := by
  have hlimit := (phaseSigma_joint_analyticAt p hβ i).continuousAt.tendsto.comp
    (actualInput_tendsto h hβ hβone)
  have hβq : 0 < (p.withStartIndex j0).beta := by
    simpa only [p.withStartIndex_beta] using hβ
  have hstartq : 0 < (p.withStartIndex j0).startIndex := by
    simpa only [p.withStartIndex_startIndex] using hstart
  simpa only [Function.comp_def, sigma_phase_eq _ hβq hstartq,
    phaseSigma_withStartIndex, phaseSigma_at_base] using hlimit

/-- Helper for sec:known-results: the phase slope is fixed before increasing
the starting index. This is a reusable same-trajectory uniformity interface. -/
theorem phaseSlope_withStartIndex (p : Parameters) (j0 : ℕ) (i : Fin 2)
    (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    RadiusBounds.phaseSlope (p.withStartIndex j0) i t v x = RadiusBounds.phaseSlope p i t v x := by
  rw [RadiusBounds.phaseSlope_def, RadiusBounds.phaseSlope_def,
    RadiusBounds.phaseInput_withStartIndex]

/-- Helper for eq:planar-scalar-definition: the actual raw source slope
tends to zero along each phase as its common cycle scale tends to zero.
This is a reusable same-orbit limit derived from the actual continuation. -/
theorem omega_phase_tendsto_zero {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (i : Fin 2) :
    Tendsto (fun j ↦ DFP.Polar.omegaOf ((p.withStartIndex j0).matrix (2 * j + (i : ℕ))))
      atTop (𝓝 0) := by
  have hinput := actualInput_tendsto h hβ hβone
  have hQ := (RadiusBounds.phaseSlope_joint_analyticAt p hβ i).continuousAt.tendsto.comp hinput
  have hscale : Tendsto (fun j ↦ (p.withStartIndex j0).scale j) atTop (𝓝 0) := by
    simpa only [RadiusBounds.scale_withStartIndex] using scale_tendsto_zero hβ j0
  have hproduct := hscale.mul hQ
  simpa only [omega_phase_eq, phaseSlope_withStartIndex, Function.comp_def, zero_mul] using hproduct

/-- Helper for lem:planar-degeneration: the genuine limiting normalized
state at either phase, using the same source base point as continuation.
This is a reusable reference-state interface. -/
def referencePhase (p : Parameters) (i : Fin 2) : ℝ × ℝ × ℝ :=
  RadiusBounds.phaseInput p i 0 0 p.initialState

/-- Helper for lem:planar-degeneration: the limiting even state is the exact
source initial matrix state. This is its reusable phase projection. -/
theorem referencePhase_zero (p : Parameters) : referencePhase p 0 = p.initialState := by
  rw [referencePhase, RadiusBounds.phaseInput_zero]

/-- Helper for lem:planar-degeneration: the limiting odd state is the exact
source odd reference at equilibrium. This is its reusable phase projection. -/
theorem referencePhase_one (p : Parameters) (hβ : 0 < p.beta) :
    referencePhase p 1 = p.oddReference p.gammaStar := by
  rw [referencePhase, RadiusBounds.phaseInput_one_at_base p hβ]

/-- Helper for lem:planar-degeneration: the actual normalized phase states
converge to their original source base states.
This is a reusable same-orbit consequence of the actual continuation tube. -/
theorem phaseState_tendsto {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (i : Fin 2) :
    Tendsto (fun j ↦ phaseState (p.withStartIndex j0) j i) atTop (𝓝 (referencePhase p i)) := by
  have hlimit := (RadiusBounds.phaseInput_joint_analyticAt p hβ i).continuousAt.tendsto.comp
    (actualInput_tendsto h hβ hβone)
  simpa only [Function.comp_def, phaseState_eq_phaseInput,
    RadiusBounds.phaseInput_withStartIndex, referencePhase] using hlimit

/-- Helper for lem:planar-degeneration: the determinant of a normalized
symmetric state is its coordinate discriminant.
This is a reusable algebraic interface for determinant limits. -/
theorem stateMatrix_det_formula (x : ℝ × ℝ × ℝ) :
    (PhysicalRecurrence.stateMatrix x).det = x.1 * x.2.2 - x.2.1 ^ 2 := by
  rw [PhysicalRecurrence.stateMatrix_def, RealSymmetric2.matrix_eq]
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- Helper for lem:planar-degeneration: every source normalized cycle state
has determinant equal to its normalization coordinate, independently of the
cycle coefficient. This is a reusable algebraic source identity. -/
theorem stateMatrix_cycleState_det (γ lam : ℝ) :
    (PhysicalRecurrence.stateMatrix (cycleState γ lam)).det = γ := by
  rw [stateMatrix_det_formula, cycleState_apply]
  dsimp only
  ring

/-- Helper for lem:planar-degeneration: both genuine normalized source
limits have the same positive determinant `γ*`.
This is a reusable base determinant identity. -/
theorem referencePhase_det (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    (PhysicalRecurrence.stateMatrix (referencePhase p i)).det = p.gammaStar := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [referencePhase_zero, p.initialState_def, stateMatrix_cycleState_det]
  · rw [referencePhase_one p hβ, p.oddReference_gammaStar, stateMatrix_cycleState_det]

/-- Helper for lem:planar-degeneration: the actual normalized phase
determinants tend to the source normalization `γ*`.
This is a reusable same-orbit determinant limit. -/
theorem phaseState_det_tendsto {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (i : Fin 2) :
    Tendsto (fun j ↦ (PhysicalRecurrence.stateMatrix (phaseState (p.withStartIndex j0) j i)).det)
      atTop (𝓝 p.gammaStar) := by
  have hcontinuous : Continuous (fun x : ℝ × ℝ × ℝ ↦ (PhysicalRecurrence.stateMatrix x).det) := by
    simp only [stateMatrix_det_formula]
    fun_prop
  have hlimit := hcontinuous.continuousAt.tendsto.comp (phaseState_tendsto h hβ hβone i)
  simpa only [Function.comp_def, referencePhase_det p hβ] using hlimit

/-- Helper for lem:planar-degeneration: the actual normalized phase matrices
are positive definite because the same trajectory remains in its proved
continuation tube. This is a reusable source-feasibility consequence. -/
theorem phaseState_posDef {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (j : ℕ) (i : Fin 2) :
    (PhysicalRecurrence.stateMatrix (phaseState (p.withStartIndex j0) j i)).PosDef := by
  have hregular := h.normalized_regular j
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [phaseState_zero, Continuation.stateMatrix_eq_legacy]
    exact (DFP.Polar.StageFeasibility.regularState_posDef _ hregular.1).1
  · rw [phaseState_one, Continuation.stateMatrix_eq_legacy]
    exact (DFP.Polar.StageFeasibility.regularState_posDef _ hregular.2).1

/-- Helper for lem:planar-degeneration: the determinant of the actual
physical source inverse Hessian has normalized limit `1/γ*` at the exact
quadratic scale `τ²`, including both source phases.
This is a reusable same-orbit quantitative limit. -/
theorem inverseHessian_det_normalized_tendsto {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (hstart : 0 < j0) :
    Tendsto (fun k ↦ ((p.withStartIndex j0).inverseHessian k).det /
      scale p.beta j0 (k / 2) ^ 2) atTop (𝓝 (1 / p.gammaStar)) := by
  have hnormalized (j : ℕ) (i : Fin 2) :
      ((p.withStartIndex j0).inverseHessian (2 * j + (i : ℕ))).det /
        scale p.beta j0 j ^ 2 =
          1 / (PhysicalRecurrence.stateMatrix (phaseState (p.withStartIndex j0) j i)).det := by
    rw [inverseHessian_det_phase, RadiusBounds.scale_withStartIndex]
    field_simp [(scale_pos p.beta hstart j).ne', (phaseState_posDef h j i).det_pos.ne']
  have hphase (i : Fin 2) :
      Tendsto (fun j ↦ ((p.withStartIndex j0).inverseHessian (2 * j + (i : ℕ))).det /
        scale p.beta j0 j ^ 2) atTop (𝓝 (1 / p.gammaStar)) := by
    have hlimit := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).div
      (phaseState_det_tendsto h hβ hβone i) p.gammaStar_pos.ne'
    simpa only [hnormalized, Pi.div_def] using hlimit
  have hhalfEven (j : ℕ) : 2 * j / 2 = j := by
    omega
  have hhalfOdd (j : ℕ) : (2 * j + 1) / 2 = j := by
    omega
  apply tendsto_of_tendsto_even_odd
  · simpa only [Fin.val_zero, Nat.add_zero, hhalfEven] using hphase 0
  · simpa only [Fin.val_one, hhalfOdd] using hphase 1

/-- Helper for lem:planar-degeneration: the actual physical inverse Hessian
determinant is asymptotic to the source expression `τ²/γ*`.
This is a reusable same-orbit asymptotic equivalent. -/
theorem inverseHessian_det_equivalent {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (hstart : 0 < j0) :
    (fun k ↦ ((p.withStartIndex j0).inverseHessian k).det) ~[atTop]
      (fun k ↦ scale p.beta j0 (k / 2) ^ 2 / p.gammaStar) := by
  have hscale (k : ℕ) : 0 < scale p.beta j0 (k / 2) ^ 2 :=
    sq_pos_of_pos (scale_pos p.beta hstart (k / 2))
  have h := DFP.Polar.SequenceAsymptotics.equivalent_of_normalized_limit hscale
    (one_div_pos.mpr p.gammaStar_pos).ne' (inverseHessian_det_normalized_tendsto h hβ hβone hstart)
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using h

/-- Helper for eq:planar-scalar-definition: interleaving the two actual
source phase limits gives the original full normalized secant limit one.
This is a reusable same-orbit convergence theorem. -/
theorem sigma_tendsto_one {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (hstart : 0 < j0) :
    Tendsto (fun k ↦ DFP.Polar.sigmaOf ((p.withStartIndex j0).matrix k)
      ((p.withStartIndex j0).angleIncrement k) ((p.withStartIndex j0).zeta k)
        ((p.withStartIndex j0).zeta (k + 1))) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_even_odd
  · simpa only [Fin.val_zero, Nat.add_zero] using sigma_phase_tendsto_one h hβ hβone hstart 0
  · simpa only [Fin.val_one] using sigma_phase_tendsto_one h hβ hβone hstart 1

/-- Helper for eq:planar-scalar-definition: the original full raw slope
sequence tends to zero along the same chosen source trajectory.
This is a reusable interleaved source limit. -/
theorem omega_tendsto_zero {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    Tendsto (fun k ↦ DFP.Polar.omegaOf ((p.withStartIndex j0).matrix k)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_even_odd
  · simpa only [Fin.val_zero, Nat.add_zero] using omega_phase_tendsto_zero h hβ hβone 0
  · simpa only [Fin.val_one] using omega_phase_tendsto_zero h hβ hβone 1

/-- Helper for sec:known-results: the exact unreduced source angle
increments tend to zero along each actual phase.
This is a reusable consequence of the prescribed source scales. -/
theorem angleIncrement_phase_tendsto_zero {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (hstart : 0 < j0) (i : Fin 2) :
    Tendsto (fun j ↦ (p.withStartIndex j0).angleIncrement (2 * j + (i : ℕ)))
      atTop (𝓝 0) := by
  have hinput := actualInput_tendsto h hβ hβone
  have hA := (RadiusBounds.phaseAngle_analyticAt p i).continuousAt.tendsto.comp
    hinput.fst_nhds.snd_nhds
  have hscale : Tendsto (fun j ↦ (p.withStartIndex j0).scale j) atTop (𝓝 0) := by
    simpa only [RadiusBounds.scale_withStartIndex] using scale_tendsto_zero hβ j0
  have hproduct := hA.mul hscale
  have hβq : 0 < (p.withStartIndex j0).beta := by
    simpa only [p.withStartIndex_beta] using hβ
  have hstartq : 0 < (p.withStartIndex j0).startIndex := by
    simpa only [p.withStartIndex_startIndex] using hstart
  simpa only [angleIncrement_phase_eq _ hβq hstartq,
    RadiusBounds.phaseAngle_withStartIndex, Function.comp_def, mul_zero] using hproduct

/-- Helper for sec:known-results: the actual unreduced source angle
increments tend to zero on the complete interleaved trajectory.
This is a reusable source angular limit. -/
theorem angleIncrement_tendsto_zero {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (hstart : 0 < j0) : Tendsto (p.withStartIndex j0).angleIncrement atTop (𝓝 0) := by
  apply tendsto_of_tendsto_even_odd
  · simpa only [Fin.val_zero, Nat.add_zero] using
      angleIncrement_phase_tendsto_zero h hβ hβone hstart 0
  · simpa only [Fin.val_one] using angleIncrement_phase_tendsto_zero h hβ hβone hstart 1

/-- Helper for sec:known-results: feasibility and vanishing angular
increments give positive sines at every sufficiently late actual source step.
This is reusable support for finite secant normalization identities. -/
theorem eventually_angle_sin_pos {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (hstart : 0 < j0) :
    ∀ᶠ k in atTop, 0 < Real.sin ((p.withStartIndex j0).angleIncrement k) := by
  have hangle := angleIncrement_tendsto_zero h hβ hβone hstart
  filter_upwards [hangle.eventually (Iio_mem_nhds Real.pi_pos)] with k hk
  exact Real.sin_pos_of_pos_of_lt_pi (h.rawFeasible hβ hstart k).angle_pos hk

/-- Helper for eq:planar-scalar-definition: the actual source secant
curvature tends to one, as the exact quotient `σ/(1+ω²)`.
This is a reusable same-orbit limit from the concrete radial and continuation data. -/
theorem curvature_tendsto_one {p : Parameters} {j0 : ℕ} {N M B K c U : ℝ}
    (h : RadiusProducts.SourceRadialData p j0 N M B K c U)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) :
    Tendsto (curvature (p.withStartIndex j0)) atTop (𝓝 1) := by
  have homega := omega_tendsto_zero h.trajectory hβ hβone
  have hden : Tendsto (fun k ↦ 1 + DFP.Polar.omegaOf ((p.withStartIndex j0).matrix k) ^ 2)
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).add
      (homega.pow 2)
    simpa only [zero_pow two_ne_zero, add_zero] using h
  have hquotient := (sigma_tendsto_one h.trajectory hβ hβone hstart).div hden one_ne_zero
  have hidentity : (curvature (p.withStartIndex j0)) =ᶠ[atTop]
      (fun k ↦ DFP.Polar.sigmaOf ((p.withStartIndex j0).matrix k)
        ((p.withStartIndex j0).angleIncrement k) ((p.withStartIndex j0).zeta k)
        ((p.withStartIndex j0).zeta (k + 1)) /
          (1 + DFP.Polar.omegaOf ((p.withStartIndex j0).matrix k) ^ 2)) := by
    filter_upwards [eventually_angle_sin_pos h.trajectory hβ hβone hstart] with k hk
    exact curvature_eq_sigma_div _ k
      ((p.withStartIndex j0).radius_recurrence (fun k ↦ zero_lt_one.trans (h.factors k))
        h.logarithms k) (zero_lt_one.trans (h.radii.above_one (k + 1))) hk.ne'
  apply (tendsto_congr' hidentity).mpr
  simpa only [Pi.div_def, div_one] using hquotient

/-- Helper for lem:planar-degeneration: the original free coefficient with
previous curvature has the same normalized limit as the current physical
inverse Hessian determinant, on the same chosen source trajectory. -/
theorem freeCoefficient_normalized_tendsto {p : Parameters} {j0 : ℕ} {N M B K c U : ℝ}
    (h : RadiusProducts.SourceRadialData p j0 N M B K c U)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) :
    Tendsto (fun k ↦ freeCoefficient (p.withStartIndex j0) k /
      scale p.beta j0 (k / 2) ^ 2) atTop (𝓝 (1 / p.gammaStar)) := by
  have hcurvature := curvature_tendsto_one h hβ hβone hstart
  have hshift : Tendsto (fun k ↦ curvature (p.withStartIndex j0) (k + 1 - 1))
      atTop (𝓝 1) := by
    simpa only [Nat.add_sub_cancel] using hcurvature
  have hprevious : Tendsto (fun k ↦ curvature (p.withStartIndex j0) (k - 1))
      atTop (𝓝 1) := (tendsto_add_atTop_iff_nat 1).mp hshift
  have hproduct := hprevious.mul
    (inverseHessian_det_normalized_tendsto h.trajectory hβ hβone hstart)
  simpa only [freeCoefficient_def, mul_div_assoc, one_mul] using hproduct

/-- Helper for lem:planar-degeneration: the actual original free coefficient
is asymptotic to `τ²/γ*`, with the previous-curvature index retained.
This is a reusable same-orbit asymptotic equivalent. -/
theorem freeCoefficient_equivalent {p : Parameters} {j0 : ℕ} {N M B K c U : ℝ}
    (h : RadiusProducts.SourceRadialData p j0 N M B K c U)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) :
    freeCoefficient (p.withStartIndex j0) ~[atTop]
      (fun k ↦ scale p.beta j0 (k / 2) ^ 2 / p.gammaStar) := by
  have hscale (k : ℕ) : 0 < scale p.beta j0 (k / 2) ^ 2 :=
    sq_pos_of_pos (scale_pos p.beta hstart (k / 2))
  have hequiv := DFP.Polar.SequenceAsymptotics.equivalent_of_normalized_limit hscale
    (one_div_pos.mpr p.gammaStar_pos).ne' (freeCoefficient_normalized_tendsto h hβ hβone hstart)
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hequiv

/-- Helper for sec:known-results: the raw source off-diagonal matrix entry
has its exact inverse-scale coordinate formula at each phase.
This is a reusable finite normalization identity. -/
theorem matrix_phase_offDiagonal (p : Parameters) (j : ℕ) (i : Fin 2) :
    p.matrix (2 * j + (i : ℕ)) 0 1 = (p.scale j)⁻¹ * (phaseState p j i).2.1 := by
  rw [matrix_phase_eq_recoverMatrix, PhysicalRecurrence.recoverMatrix_apply]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

/-- Helper for sec:known-results: the source sine factor has exactly one
power of the common cycle scale, with its analytic sinc factor retained.
This is a reusable finite source identity. -/
theorem sin_angleIncrement_phase (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) (i : Fin 2) :
    Real.sin (p.angleIncrement (2 * j + (i : ℕ))) = p.scale j *
      Normalized.sinFactor (RadiusBounds.phaseAngle p i (p.inverseIndex j)) (p.scale j) := by
  rw [angleIncrement_phase_eq p hβ hstart, Normalized.sinFactor_def, Normalized.stageAngle_def]
  have h := RadiusBounds.mul_sinc_eq_sin
    (RadiusBounds.phaseAngle p i (p.inverseIndex j) * p.scale j)
  calc
    Real.sin (RadiusBounds.phaseAngle p i (p.inverseIndex j) * p.scale j) =
        (RadiusBounds.phaseAngle p i (p.inverseIndex j) * p.scale j) *
          Real.sinc (RadiusBounds.phaseAngle p i (p.inverseIndex j) * p.scale j) := h.symm
    _ = _ := by
      ring

/-- Helper for sec:known-results: exact cancellation of the original source
step length in Xu's scalar retains the actual radii and local matrix data.
This is a reusable finite physical identity. -/
theorem xuScalar_eq (p : Parameters) (k : ℕ)
    (hbalance : p.radius k = p.radiusRatio k * p.radius (k + 1))
    (hZ : (p.matrix k).PosDef) (hC : p.matrix k 0 1 ≠ 0) (hW : p.radiusRatio k ≠ 0)
    (hsin : Real.sin (p.angleIncrement k) ≠ 0) :
    xuScalar p k = p.zeta k * p.radius k * p.radius (k + 1) *
      Real.sin (p.angleIncrement k) * DFP.Polar.sigmaOf (p.matrix k) (p.angleIncrement k)
        (p.zeta k) (p.zeta (k + 1)) * p.matrix k 0 1 / (p.matrix k).det := by
  rw [xuScalar_def, secantPairing_eq p k hbalance hsin, p.stepLength_def, hbalance]
  field_simp [hZ.det_pos.ne', hC, hW, hsin, (p.zeta_pos k).ne']

/-- Helper for sec:known-results: Xu's actual source scalar divided by the
quadratic scale equals the product of its normalized phase quantities.
This is a reusable exact normalization identity on the same trajectory. -/
theorem xuScalar_phase_normalization (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) (i : Fin 2)
    (hbalance : p.radius (2 * j + (i : ℕ)) =
      p.radiusRatio (2 * j + (i : ℕ)) * p.radius (2 * j + (i : ℕ) + 1))
    (hZ : (p.matrix (2 * j + (i : ℕ))).PosDef)
    (hC : p.matrix (2 * j + (i : ℕ)) 0 1 ≠ 0)
    (hW : p.radiusRatio (2 * j + (i : ℕ)) ≠ 0)
    (hsin : Real.sin (p.angleIncrement (2 * j + (i : ℕ))) ≠ 0) :
    xuScalar p (2 * j + (i : ℕ)) / p.scale j ^ 2 =
      p.zeta (2 * j + (i : ℕ)) * p.radius (2 * j + (i : ℕ)) *
        p.radius (2 * j + (i : ℕ) + 1) *
        Normalized.sinFactor (RadiusBounds.phaseAngle p i (p.inverseIndex j)) (p.scale j) *
        DFP.Polar.sigmaOf (p.matrix (2 * j + (i : ℕ))) (p.angleIncrement (2 * j + (i : ℕ)))
          (p.zeta (2 * j + (i : ℕ))) (p.zeta (2 * j + (i : ℕ) + 1)) *
        ((phaseState p j i).2.1 / (PhysicalRecurrence.stateMatrix (phaseState p j i)).det) := by
  have ht : 0 < p.scale j := by
    rw [p.scale_def]
    exact scale_pos p.beta hstart j
  have hdet : (PhysicalRecurrence.stateMatrix (phaseState p j i)).det ≠ 0 := by
    intro hz
    have hpositive := hZ.det_pos
    rw [matrix_phase_eq_recoverMatrix, recoverMatrix_det, hz, mul_zero] at hpositive
    exact (lt_irrefl 0) hpositive
  rw [xuScalar_eq p _ hbalance hZ hC hW hsin, matrix_phase_offDiagonal,
    matrix_phase_eq_recoverMatrix, recoverMatrix_det, sin_angleIncrement_phase p hβ hstart]
  field_simp [ht.ne', hdet]

/-- Helper for sec:known-results: the exact source leading coefficients of
Xu's scalar are `δE ell` and `δO` at the selected two-cycle normalization.
This is a reusable fixed-before-index scalar datum. -/
def xuLeadingCoefficient (p : Parameters) : Fin 2 → ℝ := ![p.deltaEven * p.ell, p.deltaOdd]

/-- Helper for sec:known-results: both Xu leading coefficients are positive
at every selected general strict Wolfe base.
This is a reusable scalar positivity theorem. -/
theorem xuLeadingCoefficient_pos (p : Parameters) (i : Fin 2) :
    0 < xuLeadingCoefficient p i := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · exact mul_pos p.deltaEven_pos (zero_lt_one.trans p.base.one_lt_ell)
  · exact p.deltaOdd_pos

/-- Helper for sec:known-results: the limiting normalized source coordinate
quotient identifies the exact selected Xu coefficient.
This is a reusable base-state identity. -/
theorem xuLeadingCoefficient_formula (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    RadiusBounds.phaseAngle p i 0 * ((referencePhase p i).2.1 / p.gammaStar) =
      xuLeadingCoefficient p i := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [RadiusBounds.phaseAngle_zero, p.evenAngleFactor_zero hβ, referencePhase_zero,
      p.initialState_def, cycleState_apply]
    simp only [xuLeadingCoefficient, Matrix.cons_val_zero]
    field_simp [p.gammaStar_pos.ne']
  · rw [RadiusBounds.phaseAngle_one, p.oddAngleFactor_zero hβ, referencePhase_one p hβ,
      p.oddReference_gammaStar, cycleState_apply]
    simp only [xuLeadingCoefficient, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp [p.gammaStar_pos.ne']

/-- Helper for sec:known-results: the analytic sine quotient of the actual
source angle tends to the selected phase angle coefficient.
This is a reusable same-orbit normalized trigonometric limit. -/
theorem sinFactor_phase_tendsto {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (i : Fin 2) :
    Tendsto (fun j ↦ Normalized.sinFactor
      (RadiusBounds.phaseAngle (p.withStartIndex j0) i ((p.withStartIndex j0).inverseIndex j))
      ((p.withStartIndex j0).scale j)) atTop (𝓝 (RadiusBounds.phaseAngle p i 0)) := by
  have hinput := actualInput_tendsto h hβ hβone
  have hA := (RadiusBounds.phaseAngle_analyticAt p i).continuousAt.tendsto.comp
    hinput.fst_nhds.snd_nhds
  have hT := hinput.fst_nhds.fst_nhds
  have hsinc := Real.continuous_sinc.continuousAt.tendsto.comp (hA.mul hT)
  have hproduct := hA.mul hsinc
  simpa only [Normalized.sinFactor_def, Normalized.stageAngle_def,
    RadiusBounds.phaseAngle_withStartIndex, Function.comp_def, mul_zero, Real.sinc_zero,
    mul_one] using hproduct

/-- Helper for sec:known-results: the actual same-orbit Xu scalar has the
source normalized phase limits `δE ell` and `δO` at the quadratic scale.
This is a reusable quantitative theorem from the proved source geometry. -/
theorem xuScalar_phase_tendsto {p : Parameters} {j0 : ℕ} {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) (i : Fin 2) :
    Tendsto (fun j ↦ xuScalar (p.withStartIndex j0) (2 * j + (i : ℕ)) /
      scale p.beta j0 j ^ 2) atTop (𝓝 (xuLeadingCoefficient p i)) := by
  have hβq : 0 < (p.withStartIndex j0).beta := by
    simpa only [p.withStartIndex_beta] using hβ
  have hstartq : 0 < (p.withStartIndex j0).startIndex := by
    simpa only [p.withStartIndex_startIndex] using hstart
  have hphase := phaseState_tendsto h.radial.trajectory hβ hβone i
  have hζ := (h.radial.trajectory.zeta_tendsto_one hβ hβone).comp
    (DFP.Polar.SequenceAsymptotics.phaseIndices_tendsto (i : ℕ))
  have hR := h.radial.radii.tendsto_one.comp
    (DFP.Polar.SequenceAsymptotics.phaseIndices_tendsto (i : ℕ))
  have hRnext : Tendsto (fun j ↦ (p.withStartIndex j0).radius (2 * j + (i : ℕ) + 1))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Nat.add_assoc] using h.radial.radii.tendsto_one.comp
      (DFP.Polar.SequenceAsymptotics.phaseIndices_tendsto ((i : ℕ) + 1))
  have hsin := sinFactor_phase_tendsto h.radial.trajectory hβ hβone i
  have hσ := sigma_phase_tendsto_one h.radial.trajectory hβ hβone hstart i
  have hratio := hphase.snd_nhds.fst_nhds.div
    (phaseState_det_tendsto h.radial.trajectory hβ hβone i) p.gammaStar_pos.ne'
  have hproduct := ((((hζ.mul hR).mul hRnext).mul hsin).mul hσ).mul hratio
  have hnormalized (j : ℕ) := xuScalar_phase_normalization (p.withStartIndex j0)
    hβq hstartq j i
    ((p.withStartIndex j0).radius_recurrence
      (fun k ↦ zero_lt_one.trans (h.radial.factors k)) h.radial.logarithms _)
    (h.radial.feasible _).posDef (h.radial.feasible _).offDiagonal_pos.ne'
    (h.radial.feasible _).radius_pos.ne' (h.sine_pos _).ne'
  simpa only [← RadiusBounds.scale_withStartIndex p j0, hnormalized, Pi.div_def,
    Function.comp_def, one_mul, mul_one, xuLeadingCoefficient_formula p hβ] using hproduct

/-- Helper for sec:known-results: the actual source Xu scalar is positive
at every step by the proved physical feasibility and positive secant pairing.
This is a reusable same-orbit positivity theorem. -/
theorem xuScalar_pos_of_geometry {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V) (k : ℕ) :
    0 < xuScalar (p.withStartIndex j0) k := by
  have hbalance := (p.withStartIndex j0).radius_recurrence
    (fun k ↦ zero_lt_one.trans (h.radial.factors k)) h.radial.logarithms k
  have hpair : 0 < secantPairing (p.withStartIndex j0) k := by
    rw [secantPairing_eq _ k hbalance (h.sine_pos k).ne']
    exact mul_pos (sq_pos_of_pos (mul_pos (zero_lt_one.trans (h.radial.radii.above_one (k + 1)))
      (h.sine_pos k))) (h.radial.feasible k).secant_pos
  rw [xuScalar_def]
  exact div_pos hpair ((p.withStartIndex j0).stepLength_pos k (h.radial.feasible k).posDef
    (h.radial.feasible k).offDiagonal_pos (h.sine_pos k) (h.radial.feasible k).radius_pos)

/-- Helper for sec:known-results: the actual phase Xu scalars have the
source asymptotic equivalents `δE ell τ²` and `δO τ²`.
This is a reusable same-orbit quantitative theorem. -/
theorem xuScalar_phase_equivalent {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) (i : Fin 2) :
    (fun j ↦ xuScalar (p.withStartIndex j0) (2 * j + (i : ℕ))) ~[atTop]
      (fun j ↦ xuLeadingCoefficient p i * scale p.beta j0 j ^ 2) := by
  exact DFP.Polar.SequenceAsymptotics.equivalent_of_normalized_limit
    (fun j ↦ sq_pos_of_pos (scale_pos p.beta hstart j))
    (xuLeadingCoefficient_pos p i).ne' (xuScalar_phase_tendsto h hβ hβone hstart i)

/-- Helper for sec:known-results: consecutive quadratic source scales have
ratio tending to one, using their exact analytic successor scaling.
This is a reusable power-law scale quotient limit. -/
theorem scaleSquareQuotient_tendsto_one (p : Parameters) (hstart : 0 < p.startIndex) :
    Tendsto (fun j ↦ p.scale (j + 1) ^ 2 / p.scale j ^ 2) atTop (𝓝 1) := by
  have hv : Tendsto p.inverseIndex atTop (𝓝 0) := by
    rw [funext p.inverseIndex_def]
    exact tendsto_inv_atTop_zero.comp (Continuation.index_tendsto_atTop p.startIndex)
  have hratio := (Normalized.scaleRatio_analyticAt p.beta).continuousAt.tendsto.comp hv
  have hid (j : ℕ) : p.scale (j + 1) ^ 2 / p.scale j ^ 2 =
      Normalized.scaleRatio p.beta (p.inverseIndex j) ^ 2 := by
    have ht : 0 < p.scale j := by
      rw [p.scale_def]
      exact scale_pos p.beta hstart j
    rw [p.scale_succ hstart j, mul_pow]
    field_simp [ht.ne']
  simpa only [hid, Function.comp_def, Normalized.scaleRatio_zero, one_pow] using hratio.pow 2

/-- Helper for sec:known-results: normalized even and odd limits and a unit
successor-scale ratio determine the ratio of the next even value to the
current odd value. This is a reusable abstract two-phase scalar theorem. -/
theorem phaseRatio_jump_tendsto {u t : ℕ → ℝ} {A B : ℝ}
    (ht : ∀ j, t j ≠ 0) (hB : B ≠ 0) (hodd : ∀ j, u (2 * j + 1) ≠ 0)
    (hevenLimit : Tendsto (fun j ↦ u (2 * j) / t j) atTop (𝓝 A))
    (hoddLimit : Tendsto (fun j ↦ u (2 * j + 1) / t j) atTop (𝓝 B))
    (hscale : Tendsto (fun j ↦ t (j + 1) / t j) atTop (𝓝 1)) :
    Tendsto (fun j ↦ u (2 * j + 2) / u (2 * j + 1)) atTop (𝓝 (A / B)) := by
  have hshift := hevenLimit.comp (tendsto_add_atTop_nat 1)
  have hproduct := (hshift.div hoddLimit hB).mul hscale
  have hid (j : ℕ) : u (2 * j + 2) / u (2 * j + 1) =
      ((u (2 * (j + 1)) / t (j + 1)) / (u (2 * j + 1) / t j)) * (t (j + 1) / t j) := by
    have hindex : 2 * (j + 1) = 2 * j + 2 := by
      omega
    rw [hindex]
    field_simp [ht j, ht (j + 1), hodd j]
  simpa only [hid, Pi.div_def, Function.comp_def, mul_one] using hproduct

/-- Helper for sec:known-results: the same actual source Xu sequence has
the next-even/current-odd ratio tending to `δE ell/δO`, which exceeds one.
This is a reusable same-orbit jump limit. -/
theorem xuScalar_jump_tendsto {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) :
    Tendsto (fun j ↦ xuScalar (p.withStartIndex j0) (2 * j + 2) /
      xuScalar (p.withStartIndex j0) (2 * j + 1)) atTop (𝓝 (p.deltaEven * p.ell / p.deltaOdd)) := by
  have hstartq : 0 < (p.withStartIndex j0).startIndex := by
    simpa only [p.withStartIndex_startIndex] using hstart
  have ht (j : ℕ) : (p.withStartIndex j0).scale j ^ 2 ≠ 0 := by
    rw [RadiusBounds.scale_withStartIndex]
    exact (sq_pos_of_pos (scale_pos p.beta hstart j)).ne'
  have heven : Tendsto (fun j ↦ xuScalar (p.withStartIndex j0) (2 * j) /
      (p.withStartIndex j0).scale j ^ 2) atTop (𝓝 (p.deltaEven * p.ell)) := by
    simpa only [Fin.val_zero, Nat.add_zero, RadiusBounds.scale_withStartIndex,
      xuLeadingCoefficient, Matrix.cons_val_zero] using xuScalar_phase_tendsto h hβ hβone hstart 0
  have hodd : Tendsto (fun j ↦ xuScalar (p.withStartIndex j0) (2 * j + 1) /
      (p.withStartIndex j0).scale j ^ 2) atTop (𝓝 p.deltaOdd) := by
    simpa only [Fin.val_one, RadiusBounds.scale_withStartIndex,
      xuLeadingCoefficient, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
      xuScalar_phase_tendsto h hβ hβone hstart 1
  exact phaseRatio_jump_tendsto ht p.deltaOdd_pos.ne'
    (fun j ↦ (xuScalar_pos_of_geometry h (2 * j + 1)).ne') heven hodd
    (scaleSquareQuotient_tendsto_one _ hstartq)

/-- Helper for sec:known-results: the actual Xu sequence is not eventually
nonincreasing because its original cross-phase quotient tends to a number
strictly greater than one. This is a reusable same-orbit conclusion. -/
theorem xuScalar_not_eventually_nonincreasing {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) :
    ¬ ∀ᶠ k in atTop, xuScalar (p.withStartIndex j0) (k + 1) ≤
      xuScalar (p.withStartIndex j0) k := by
  have hlarge := (xuScalar_jump_tendsto h hβ hβone hstart).eventually
    (eventually_gt_nhds (xuJumpLimit_gt_one p))
  have hphase : ∀ᶠ j in atTop, xuScalar (p.withStartIndex j0) (2 * j + 1) <
      xuScalar (p.withStartIndex j0) (2 * j + 2) := by
    filter_upwards [hlarge] with j hj
    exact (one_lt_div (xuScalar_pos_of_geometry h (2 * j + 1))).mp hj
  exact DFP.Polar.SequenceAsymptotics.not_eventually_nonincreasing_of_odd_increases
    (xuScalar (p.withStartIndex j0)) hphase

/-- Helper for sec:known-results: the same actual source step lengths have
divergent total Euclidean length, by the positive global source step envelope.
This is a reusable same-orbit conclusion. -/
theorem stepNorm_not_summable_of_geometry {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hs : 0 < s) :
    ¬ Summable (fun k ↦ ‖step (p.withStartIndex j0) k‖) := by
  have hβq : 0 < (p.withStartIndex j0).beta := by
    simpa only [p.withStartIndex_beta] using hβ
  apply stepNorm_not_summable_of_lower _ hβq hs
  intro k
  simpa only [step_def, Parameters.withStartIndex_beta,
    Parameters.withStartIndex_startIndex] using (h.steps k).1

/-- Helper for sec:known-results: the original selected curvature ratio limit
is positive at each phase. This is reusable positivity for excluding exact
line-search endpoints on the same source orbit. -/
theorem curvatureLimit_pos (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    0 < RadiusBounds.curvatureLimit p i := by
  rw [RadiusBounds.curvatureLimit_def]
  exact sub_pos.mpr ((div_lt_one (RadiusBounds.referenceSlope_pos p hβ i)).mpr
    (RadiusBounds.referenceSlope_gt_angle p hβ i))

/-- Helper for sec:known-results: the actual raw source endpoint curvature
quotient tends to its positive selected phase limit on the same trajectory.
This is a reusable same-orbit endpoint-ratio limit. -/
theorem sourceCurvatureQuotient_phase_tendsto {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : Continuation.TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (hstart : 0 < j0) (i : Fin 2) :
    Tendsto (fun j ↦ WolfeRatios.sourceCurvatureQuotient (p.withStartIndex j0)
      (2 * j + (i : ℕ))) atTop (𝓝 (RadiusBounds.curvatureLimit p i)) := by
  have hβq : 0 < (p.withStartIndex j0).beta := by
    simpa only [p.withStartIndex_beta] using hβ
  have hstartq : 0 < (p.withStartIndex j0).startIndex := by
    simpa only [p.withStartIndex_startIndex] using hstart
  have hlimit := (RadiusBounds.phaseCurvature_joint_continuousAt p hβ i).tendsto.comp
    (actualInput_tendsto h hβ hβone)
  have hid (j : ℕ) : WolfeRatios.sourceCurvatureQuotient (p.withStartIndex j0)
      (2 * j + (i : ℕ)) = RadiusBounds.phaseCurvature p i ((p.withStartIndex j0).scale j)
        ((p.withStartIndex j0).inverseIndex j) ((p.withStartIndex j0).normalizedEvenState j) := by
    rw [(WolfeRatios.sourceQuotients_eq_phase _ hβq hstartq j i).2,
      RadiusBounds.phaseCurvature_withStartIndex]
  simpa only [hid, Function.comp_def, RadiusBounds.phaseCurvature_at_base p hβ] using hlimit

/-- Helper for sec:known-results: every sufficiently late endpoint in either
actual source phase has a nonzero directional derivative. The proof uses
the positive limiting endpoint curvature ratio and its exact physical pairing.
This is a reusable same-orbit exclusion of exact line search. -/
theorem sourceEndSlope_phase_eventually_ne_zero {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) (i : Fin 2) :
    ∀ᶠ j in atTop, WolfeRatios.sourceEndSlope (p.withStartIndex j0) (2 * j + (i : ℕ)) ≠ 0 := by
  have hlimit := sourceCurvatureQuotient_phase_tendsto h.radial.trajectory hβ hβone hstart i
  have hpositive := hlimit.eventually (Ioi_mem_nhds (curvatureLimit_pos p hβ i))
  filter_upwards [hpositive] with j hj
  intro hz
  have hratio := (WolfeRatios.sourceSlope_ratios (p.withStartIndex j0) (2 * j + (i : ℕ))
    ((p.withStartIndex j0).radius_recurrence
      (fun k ↦ zero_lt_one.trans (h.radial.factors k)) h.radial.logarithms _)
    (h.radial.feasible _).posDef (h.radial.feasible _).offDiagonal_pos
    (h.sine_pos _) (h.radial.feasible _).radius_pos
    (zero_lt_one.trans (h.radial.radii.above_one _))).2
  rw [hz, abs_zero, zero_div] at hratio
  linarith

/-- Helper for sec:known-results: the accepted endpoint derivative is
nonzero at every sufficiently late actual source step, on the complete
interleaved sequence. This is a reusable same-orbit conclusion. -/
theorem sourceEndSlope_eventually_ne_zero {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) :
    ∀ᶠ k in atTop, WolfeRatios.sourceEndSlope (p.withStartIndex j0) k ≠ 0 := by
  obtain ⟨JE, hJE⟩ := eventually_atTop.mp
    (sourceEndSlope_phase_eventually_ne_zero h hβ hβone hstart 0)
  obtain ⟨JO, hJO⟩ := eventually_atTop.mp
    (sourceEndSlope_phase_eventually_ne_zero h hβ hβone hstart 1)
  refine eventually_atTop.mpr ⟨2 * max JE JO, ?_⟩
  intro k hk
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hj : JE ≤ j := by
      have h := le_max_left JE JO
      omega
    simpa only [Fin.val_zero, Nat.add_zero] using hJE j hj
  · have hj : JO ≤ j := by
      have h := le_max_right JE JO
      omega
    simpa only [Fin.val_one] using hJO j hj

/-- Helper for sec:known-results: the eventual endpoint nonvanishing is
stated directly as the original physical gradient-displacement pairing.
This is a reusable same-orbit directional-derivative conclusion. -/
theorem acceptedEndpoint_eventually_ne_zero {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) :
    ∀ᶠ k in atTop, inner ℝ ((p.withStartIndex j0).gradients (k + 1))
      ((p.withStartIndex j0).point (k + 1) - (p.withStartIndex j0).point k) ≠ 0 := by
  simpa only [WolfeRatios.sourceEndSlope_def] using
    sourceEndSlope_eventually_ne_zero h hβ hβone hstart

/-- Helper for sec:known-results: the norm of an actual prescribed radial
gradient is its positive multiplier times the original nonnegative radius.
This is a reusable same-orbit scalar identity. -/
theorem gradient_norm (p : Parameters) (k : ℕ) (hr : 0 ≤ p.radius k) :
    ‖p.gradients k‖ = p.zeta k * p.radius k := by
  rw [p.gradients_def, norm_smul, Real.norm_eq_abs, abs_of_pos (p.zeta_pos k), p.point_norm k hr]

/-- Helper for sec:known-results: the actual prescribed gradient norms tend
to one along the same continuation and radial source construction.
This is a reusable same-orbit nonstationarity limit. -/
theorem gradientNorm_tendsto_one {p : Parameters} {j0 : ℕ} {N M B K c U : ℝ}
    (h : RadiusProducts.SourceRadialData p j0 N M B K c U)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    Tendsto (fun k ↦ ‖(p.withStartIndex j0).gradients k‖) atTop (𝓝 1) := by
  have hproduct := (h.trajectory.zeta_tendsto_one hβ hβone).mul h.radii.tendsto_one
  simpa only [gradient_norm _ _ (zero_lt_one.trans (h.radii.above_one _)).le,
    one_mul] using hproduct

/-- Helper for lem:planar-degeneration: consecutive physical step products
are comparable to the current quadratic source scale whenever both step
norms have the source linear-scale bounds. This is a reusable scalar comparison. -/
theorem stepProduct_bounds (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) {lower upper : ℝ} (hlower : 0 < lower)
    (hupper : 0 < upper)
    (hsteps : ∀ k, lower * p.scale (k / 2) ≤ ‖step p k‖ ∧
      ‖step p k‖ ≤ upper * p.scale (k / 2)) (k : ℕ) :
    lower ^ 2 * p.scale (k / 2) ^ 2 ≤ ‖step p (k - 1)‖ * ‖step p k‖ ∧
      ‖step p (k - 1)‖ * ‖step p k‖ ≤ 2 * upper ^ 2 * p.scale (k / 2) ^ 2 := by
  have hindex : (k - 1) / 2 ≤ k / 2 := Nat.div_le_div_right (Nat.sub_le k 1)
  have hscale : p.scale (k / 2) ≤ p.scale ((k - 1) / 2) := by
    simpa only [p.scale_def] using scale_antitone hβ hstart hindex
  have hindices : p.startIndex + k / 2 ≤ 2 * (p.startIndex + (k - 1) / 2) := by omega
  have hhalf : (1 / 2 : ℝ) * p.scale ((k - 1) / 2) ≤ p.scale (k / 2) := by
    simpa only [p.scale_def] using
      Geometry.scale_lower_of_index_le_two hβ hstart ((k - 1) / 2) (k / 2) hindices
  have hprevious : p.scale ((k - 1) / 2) ≤ 2 * p.scale (k / 2) := by linarith
  have hpreviousLower : lower * p.scale (k / 2) ≤ ‖step p (k - 1)‖ :=
    (mul_le_mul_of_nonneg_left hscale hlower.le).trans (hsteps (k - 1)).1
  have hpreviousUpper : ‖step p (k - 1)‖ ≤ (2 * upper) * p.scale (k / 2) := by
    have h := (hsteps (k - 1)).2.trans
      (mul_le_mul_of_nonneg_left hprevious hupper.le)
    nlinarith
  have ht : 0 ≤ p.scale (k / 2) := by
    simpa only [p.scale_def] using scale_nonneg p.beta p.startIndex (k / 2)
  have hproductLower := mul_le_mul hpreviousLower (hsteps k).1
    (mul_nonneg hlower.le ht) (norm_nonneg _)
  have hproductUpper := mul_le_mul hpreviousUpper (hsteps k).2
    (norm_nonneg _) (mul_nonneg (mul_nonneg zero_le_two hupper.le) ht)
  constructor
  · nlinarith
  · nlinarith

/-- Helper for lem:planar-degeneration: the original free coefficient is
eventually bounded by fixed positive multiples of consecutive physical step
products. The constants depend only on the source step envelopes and `γ*`. -/
theorem freeCoefficient_stepProduct_bounds (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) {lower upper : ℝ} (hlower : 0 < lower)
    (hupper : 0 < upper)
    (hsteps : ∀ k, lower * p.scale (k / 2) ≤ ‖step p k‖ ∧
      ‖step p k‖ ≤ upper * p.scale (k / 2))
    (hfree : freeCoefficient p ~[atTop]
      (fun k ↦ p.scale (k / 2) ^ 2 / p.gammaStar)) :
    ∀ᶠ k in atTop,
      (1 / (4 * upper ^ 2 * p.gammaStar)) *
          (‖step p (k - 1)‖ * ‖step p k‖) ≤ freeCoefficient p k ∧
        freeCoefficient p k ≤ (2 / (lower ^ 2 * p.gammaStar)) *
          (‖step p (k - 1)‖ * ‖step p k‖) := by
  have hpositive (k : ℕ) : 0 < p.scale (k / 2) ^ 2 / p.gammaStar := by
    rw [p.scale_def]
    exact div_pos (sq_pos_of_pos (scale_pos p.beta hstart _)) p.gammaStar_pos
  have hbounds := DFP.Polar.SequenceAsymptotics.eventual_factor_bounds_of_equivalent
    hpositive hfree
  have hgamma := p.gammaStar_pos
  have ha : 0 ≤ 1 / (4 * upper ^ 2 * p.gammaStar) := by positivity
  have hb : 0 ≤ 2 / (lower ^ 2 * p.gammaStar) := by positivity
  filter_upwards [hbounds] with k hk
  have hproduct := stepProduct_bounds p hβ hstart hlower hupper hsteps k
  constructor
  · calc
      (1 / (4 * upper ^ 2 * p.gammaStar)) *
          (‖step p (k - 1)‖ * ‖step p k‖) ≤
          (1 / (4 * upper ^ 2 * p.gammaStar)) *
            (2 * upper ^ 2 * p.scale (k / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hproduct.2 ha
      _ = (p.scale (k / 2) ^ 2 / p.gammaStar) / 2 := by
        field_simp [p.gammaStar_pos.ne', hupper.ne']
        ring
      _ ≤ freeCoefficient p k := hk.1
  · calc
      freeCoefficient p k ≤ 2 * (p.scale (k / 2) ^ 2 / p.gammaStar) := hk.2
      _ = (2 / (lower ^ 2 * p.gammaStar)) * (lower ^ 2 * p.scale (k / 2) ^ 2) := by
        field_simp [p.gammaStar_pos.ne', hlower.ne']
      _ ≤ (2 / (lower ^ 2 * p.gammaStar)) *
          (‖step p (k - 1)‖ * ‖step p k‖) :=
        mul_le_mul_of_nonneg_left hproduct.1 hb

/-- Helper for lem:planar-degeneration: the actual original free coefficient
has the order of consecutive source step products on the same geometric
trajectory, with the previous curvature index preserved. -/
theorem freeCoefficient_stepProduct_order_of_geometry {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) (hs : 0 < s) :
    ∃ lower > 0, ∃ upper > 0, ∀ᶠ k in atTop,
      lower * (‖step (p.withStartIndex j0) (k - 1)‖ *
        ‖step (p.withStartIndex j0) k‖) ≤ freeCoefficient (p.withStartIndex j0) k ∧
      freeCoefficient (p.withStartIndex j0) k ≤ upper *
        (‖step (p.withStartIndex j0) (k - 1)‖ * ‖step (p.withStartIndex j0) k‖) := by
  have hβq : 0 < (p.withStartIndex j0).beta := by
    simpa only [p.withStartIndex_beta] using hβ
  have hstartq : 0 < (p.withStartIndex j0).startIndex := by
    simpa only [p.withStartIndex_startIndex] using hstart
  have hV : 0 < V := by
    have hsteps := h.steps 0
    have ht := scale_pos p.beta hstart (0 / 2)
    have hproduct : 0 < V * scale p.beta j0 (0 / 2) :=
      (mul_pos hs ht).trans_le (hsteps.1.trans hsteps.2)
    exact (mul_pos_iff_of_pos_right ht).mp hproduct
  have hsteps (k : ℕ) :
      s * (p.withStartIndex j0).scale (k / 2) ≤ ‖step (p.withStartIndex j0) k‖ ∧
        ‖step (p.withStartIndex j0) k‖ ≤ V * (p.withStartIndex j0).scale (k / 2) := by
    simpa only [step_def, RadiusBounds.scale_withStartIndex] using h.steps k
  have hfree : freeCoefficient (p.withStartIndex j0) ~[atTop]
      (fun k ↦ (p.withStartIndex j0).scale (k / 2) ^ 2 /
        (p.withStartIndex j0).gammaStar) := by
    simpa only [RadiusBounds.scale_withStartIndex, p.withStartIndex_gammaStar] using
      freeCoefficient_equivalent h.radial hβ hβone hstart
  have hgamma := (p.withStartIndex j0).gammaStar_pos
  refine ⟨1 / (4 * V ^ 2 * (p.withStartIndex j0).gammaStar), ?_,
    2 / (s ^ 2 * (p.withStartIndex j0).gammaStar), ?_, ?_⟩
  · positivity
  · positivity
  · exact freeCoefficient_stepProduct_bounds _ hβq hstartq hs hV hsteps hfree

/-- Helper for sec:known-results and lem:planar-degeneration: quantitative
scalar and matrix conclusions for one original source trajectory. Every
field refers to its actual points, gradients, steps, and inverse Hessians.
The proof below derives this certificate from the same geometric witness. -/
structure ScalarSequenceProperties (p : Parameters) : Prop where
  /-- Helper for sec:known-results: the source gradient norm tends to one. -/
  gradientNorm_limit : Tendsto (fun k ↦ ‖p.gradients k‖) atTop (𝓝 1)
  /-- Helper for sec:known-results: total source step length is infinite. -/
  stepNorm_not_summable : ¬ Summable (fun k ↦ ‖step p k‖)
  /-- Helper for sec:known-results: partial total source lengths diverge to infinity. -/
  length_tendsto_atTop : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ‖step p k‖) atTop atTop
  /-- Helper for eq:polar-step-data: the physical angular increments tend to zero. -/
  angleIncrement_limit : Tendsto p.angleIncrement atTop (𝓝 0)
  /-- Helper for eq:polar-step-data: the physical source slopes tend to zero. -/
  omega_limit : Tendsto (fun k ↦ DFP.Polar.omegaOf (p.matrix k)) atTop (𝓝 0)
  /-- Helper for eq:planar-scalar-definition: the normalized secant pairing tends to one. -/
  sigma_limit : Tendsto (fun k ↦ DFP.Polar.sigmaOf (p.matrix k)
    (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1))) atTop (𝓝 1)
  /-- Helper for eq:planar-scalar-definition: exact source curvature formula. -/
  curvature_formula : ∀ k, curvature p k = DFP.Polar.sigmaOf (p.matrix k)
    (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1)) / (1 + DFP.Polar.omegaOf (p.matrix k) ^ 2)
  /-- Helper for eq:planar-scalar-definition: the source curvature tends to one. -/
  curvature_limit : Tendsto (curvature p) atTop (𝓝 1)
  /-- Helper for lem:planar-degeneration: the source determinant has normalized limit `1/γ*`. -/
  determinant_normalized : Tendsto (fun k ↦ (p.inverseHessian k).det / p.scale (k / 2) ^ 2)
    atTop (𝓝 (1 / p.gammaStar))
  /-- Helper for lem:planar-degeneration: the exact source determinant equivalent. -/
  determinant_equivalent : (fun k ↦ (p.inverseHessian k).det) ~[atTop]
    (fun k ↦ p.scale (k / 2) ^ 2 / p.gammaStar)
  /-- Helper for lem:planar-degeneration: the original free coefficient has normalized limit. -/
  free_normalized : Tendsto (fun k ↦ freeCoefficient p k / p.scale (k / 2) ^ 2)
    atTop (𝓝 (1 / p.gammaStar))
  /-- Helper for lem:planar-degeneration: the original free coefficient equivalent. -/
  free_equivalent : freeCoefficient p ~[atTop] (fun k ↦ p.scale (k / 2) ^ 2 / p.gammaStar)
  /-- Helper for lem:planar-degeneration: the original free coefficient has
  the order of consecutive physical step products. -/
  free_stepProduct_order : ∃ lower > 0, ∃ upper > 0, ∀ᶠ k in atTop,
    lower * (‖step p (k - 1)‖ * ‖step p k‖) ≤ freeCoefficient p k ∧
      freeCoefficient p k ≤ upper * (‖step p (k - 1)‖ * ‖step p k‖)
  /-- Helper for sec:known-results: both original Xu normalized phase limits. -/
  xu_normalized : ∀ i : Fin 2,
    Tendsto (fun j ↦ xuScalar p (2 * j + (i : ℕ)) / p.scale j ^ 2)
      atTop (𝓝 (xuLeadingCoefficient p i))
  /-- Helper for sec:known-results: both original Xu asymptotic equivalents. -/
  xu_equivalent : ∀ i : Fin 2, (fun j ↦ xuScalar p (2 * j + (i : ℕ))) ~[atTop]
    (fun j ↦ xuLeadingCoefficient p i * p.scale j ^ 2)
  /-- Helper for sec:known-results: the source cross-phase Xu quotient limit. -/
  xu_jump : Tendsto (fun j ↦ xuScalar p (2 * j + 2) / xuScalar p (2 * j + 1))
    atTop (𝓝 (p.deltaEven * p.ell / p.deltaOdd))
  /-- Helper for sec:known-results: the source cross-phase Xu limit exceeds one. -/
  xu_jump_gt_one : 1 < p.deltaEven * p.ell / p.deltaOdd
  /-- Helper for sec:known-results: the source Xu scalar is not eventually nonincreasing. -/
  xu_not_eventually_nonincreasing : ¬ ∀ᶠ k in atTop, xuScalar p (k + 1) ≤ xuScalar p k
  /-- Helper for sec:known-results: the original accepted endpoint pairing is eventually nonzero. -/
  endpoint_eventually_ne_zero : ∀ᶠ k in atTop,
    inner ℝ (p.gradients (k + 1)) (p.point (k + 1) - p.point k) ≠ 0

/-- Helper for sec:known-results and lem:planar-degeneration: the actual
chosen geometric source witness satisfies the complete scalar and matrix
comparison package. No sequence asymptotic, positivity, or monotonicity
conclusion is a premise. This theorem uses the same original trajectory. -/
theorem scalarSequenceProperties_of_geometry {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) (hs : 0 < s) :
    ScalarSequenceProperties (p.withStartIndex j0) := by
  have hdiverge := stepNorm_not_summable_of_geometry h hβ hs
  constructor
  · exact gradientNorm_tendsto_one h.radial hβ hβone
  · exact hdiverge
  · exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun k ↦ norm_nonneg (step (p.withStartIndex j0) k))).mp hdiverge
  · exact angleIncrement_tendsto_zero h.radial.trajectory hβ hβone hstart
  · exact omega_tendsto_zero h.radial.trajectory hβ hβone
  · exact sigma_tendsto_one h.radial.trajectory hβ hβone hstart
  · intro k
    exact curvature_eq_sigma_div _ k
      ((p.withStartIndex j0).radius_recurrence
        (fun k ↦ zero_lt_one.trans (h.radial.factors k)) h.radial.logarithms k)
      (zero_lt_one.trans (h.radial.radii.above_one (k + 1))) (h.sine_pos k).ne'
  · exact curvature_tendsto_one h.radial hβ hβone hstart
  · simpa only [RadiusBounds.scale_withStartIndex, p.withStartIndex_gammaStar] using
      inverseHessian_det_normalized_tendsto h.radial.trajectory hβ hβone hstart
  · simpa only [RadiusBounds.scale_withStartIndex, p.withStartIndex_gammaStar] using
      inverseHessian_det_equivalent h.radial.trajectory hβ hβone hstart
  · simpa only [RadiusBounds.scale_withStartIndex, p.withStartIndex_gammaStar] using
      freeCoefficient_normalized_tendsto h.radial hβ hβone hstart
  · simpa only [RadiusBounds.scale_withStartIndex, p.withStartIndex_gammaStar] using
      freeCoefficient_equivalent h.radial hβ hβone hstart
  · exact freeCoefficient_stepProduct_order_of_geometry h hβ hβone hstart hs
  · intro i
    simpa only [RadiusBounds.scale_withStartIndex, xuLeadingCoefficient,
      p.withStartIndex_deltaEven, p.withStartIndex_ell, p.withStartIndex_deltaOdd] using
      xuScalar_phase_tendsto h hβ hβone hstart i
  · intro i
    simpa only [RadiusBounds.scale_withStartIndex, xuLeadingCoefficient,
      p.withStartIndex_deltaEven, p.withStartIndex_ell, p.withStartIndex_deltaOdd] using
      xuScalar_phase_equivalent h hβ hβone hstart i
  · simpa only [p.withStartIndex_deltaEven, p.withStartIndex_ell, p.withStartIndex_deltaOdd] using
      xuScalar_jump_tendsto h hβ hβone hstart
  · exact xuJumpLimit_gt_one _
  · exact xuScalar_not_eventually_nonincreasing h hβ hβone hstart
  · exact acceptedEndpoint_eventually_ne_zero h hβ hβone hstart

/-- Helper for sec:known-results: the physical displacement in a canonical
DFP inverse iteration. This is a reusable iteration-level scalar interface. -/
def iterationStep {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι) (k : ℕ) :
    EuclideanSpace ℝ ι := it.point (k + 1) - it.point k

/-- Helper for sec:known-results: the displacement formula for the canonical
iteration step. This is its reusable definition interface. -/
theorem iterationStep_def {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι) (k : ℕ) :
    iterationStep it k = it.point (k + 1) - it.point k := by
  rfl

/-- Helper for sec:known-results: the canonical displacement is exactly the
scaled DFP search step stored in the same inverse iteration.
This is a reusable link to the algorithmic iteration laws. -/
theorem iterationStep_eq_steps {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι) (k : ℕ) :
    iterationStep it k = DFP.steps it.stepLength
      (DFP.directions it.inverseHessian (DFP.gradients it.objective it.point)) k := by
  rw [iterationStep_def, it.pointSucc k, add_sub_cancel_left]

/-- Helper for sec:known-results: the gradient secant in the canonical DFP
inverse iteration. This is a reusable quantity on the same objective and points. -/
def iterationSecant {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι) (k : ℕ) :
    EuclideanSpace ℝ ι := DFP.gradientChanges (DFP.gradients it.objective it.point) k

/-- Helper for sec:known-results: the original gradient difference in the
canonical DFP iteration. This is its reusable evaluation interface. -/
theorem iterationSecant_def {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι) (k : ℕ) :
    iterationSecant it k = DFP.gradients it.objective it.point (k + 1) -
      DFP.gradients it.objective it.point k := by
  rw [iterationSecant, DFP.gradientChanges_apply]

/-- Helper for sec:known-results: Xu's scalar evaluated on a canonical DFP
iteration using its own steps, gradients, and accepted step lengths.
This is a reusable iteration-level quantity. -/
def iterationXuScalar {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι) (k : ℕ) : ℝ :=
  inner ℝ (iterationStep it k) (iterationSecant it k) / it.stepLength k

/-- Helper for sec:known-results: the exact canonical Xu scalar formula.
This is its reusable definition interface. -/
theorem iterationXuScalar_def {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι) (k : ℕ) :
    iterationXuScalar it k = inner ℝ (iterationStep it k) (iterationSecant it k) /
      it.stepLength k := by
  rfl

/-- Helper for eq:planar-scalar-definition: the canonical source secant
curvature uses the same iteration's physical step and gradient change.
This is a reusable iteration-level quantity. -/
def iterationCurvature {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι) (k : ℕ) : ℝ :=
  inner ℝ (iterationStep it k) (iterationSecant it k) / ‖iterationStep it k‖ ^ 2

/-- Helper for eq:planar-scalar-definition: the exact canonical secant
curvature formula. This is its reusable definition interface. -/
theorem iterationCurvature_def {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι) (k : ℕ) :
    iterationCurvature it k = inner ℝ (iterationStep it k) (iterationSecant it k) /
      ‖iterationStep it k‖ ^ 2 := by
  rfl

/-- Helper for lem:planar-degeneration: the original planar free coefficient
on a canonical DFP iteration retains the previous-curvature index and the
current physical inverse Hessian determinant. -/
def iterationFreeCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (it : DFP.InverseIteration ι) (k : ℕ) : ℝ :=
  iterationCurvature it (k - 1) * (it.inverseHessian k).det

/-- Helper for lem:planar-degeneration: the exact canonical original free
coefficient formula. This is its reusable definition interface. -/
theorem iterationFreeCoefficient_def {ι : Type*} [Fintype ι] [DecidableEq ι]
    (it : DFP.InverseIteration ι) (k : ℕ) :
    iterationFreeCoefficient it k = iterationCurvature it (k - 1) *
      (it.inverseHessian k).det := by
  rfl

/-- Helper for sec:known-results: the canonical certificate's displacement
is the same original source step retained by `SourceIdentity`.
This is a reusable source-to-certificate comparison bridge. -/
theorem iterationStep_eq_source {p : Parameters} {κ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (h : PlanarCounterexample.SourceIdentity p κ w) (k : ℕ) :
    iterationStep w.iteration k = step p k := by
  rw [iterationStep_def, h.point, step_def]

/-- Helper for sec:known-results: the canonical certificate's gradient
change is the same original source secant retained by `SourceIdentity`.
This is a reusable source-to-certificate comparison bridge. -/
theorem iterationSecant_eq_source {p : Parameters} {κ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (h : PlanarCounterexample.SourceIdentity p κ w) (k : ℕ) :
    iterationSecant w.iteration k = secant p k := by
  rw [iterationSecant_def, h.gradients, secant_def]

/-- Helper for sec:known-results: Xu's scalar of the canonical certificate
is exactly the actual source Xu scalar at every index.
This is a reusable source-to-certificate quantitative identity. -/
theorem iterationXuScalar_eq_source {p : Parameters} {κ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (h : PlanarCounterexample.SourceIdentity p κ w) (k : ℕ) :
    iterationXuScalar w.iteration k = xuScalar p k := by
  rw [iterationXuScalar_def, iterationStep_eq_source h, iterationSecant_eq_source h,
    h.stepLength, xuScalar_def, secantPairing_def]

/-- Helper for eq:planar-scalar-definition: the canonical certificate's
secant curvature is exactly the original source curvature at every index.
This is a reusable source-to-certificate identity. -/
theorem iterationCurvature_eq_source {p : Parameters} {κ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (h : PlanarCounterexample.SourceIdentity p κ w) (k : ℕ) :
    iterationCurvature w.iteration k = curvature p k := by
  rw [iterationCurvature_def, iterationStep_eq_source h, iterationSecant_eq_source h,
    curvature_def, secantPairing_def]

/-- Helper for lem:planar-degeneration: the original free coefficient of the
canonical certificate is exactly that of the same source construction.
This is a reusable source-to-certificate identity. -/
theorem iterationFreeCoefficient_eq_source {p : Parameters} {κ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (h : PlanarCounterexample.SourceIdentity p κ w) (k : ℕ) :
    iterationFreeCoefficient w.iteration k = freeCoefficient p k := by
  rw [iterationFreeCoefficient_def, iterationCurvature_eq_source h, h.inverseHessian,
    freeCoefficient_def]

/-- Helper for sec:known-results and lem:planar-degeneration: the scalar
comparison conclusions on the canonical counterexample certificate itself.
The source scales are retained to state the original quantitative equivalents. -/
structure CanonicalScalarProperties (p : Parameters)
    (w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2) : Prop where
  /-- Helper for sec:known-results: canonical gradient norms tend to one. -/
  gradientNorm_limit : Tendsto (fun k ↦ ‖DFP.gradients w.iteration.objective w.iteration.point k‖)
    atTop (𝓝 1)
  /-- Helper for sec:known-results: the canonical DFP steps have infinite total length. -/
  stepNorm_not_summable : ¬ Summable (fun k ↦ ‖iterationStep w.iteration k‖)
  /-- Helper for sec:known-results: canonical partial path lengths diverge to infinity. -/
  length_tendsto_atTop : Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
    ‖iterationStep w.iteration k‖) atTop atTop
  /-- Helper for eq:planar-scalar-definition: the canonical curvature retains
  the original exact physical source quotient. -/
  curvature_formula : ∀ k, iterationCurvature w.iteration k = DFP.Polar.sigmaOf (p.matrix k)
    (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1)) / (1 + DFP.Polar.omegaOf (p.matrix k) ^ 2)
  /-- Helper for eq:planar-scalar-definition: canonical secant curvature tends to one. -/
  curvature_limit : Tendsto (iterationCurvature w.iteration) atTop (𝓝 1)
  /-- Helper for lem:planar-degeneration: the canonical normalized determinant limit. -/
  determinant_normalized : Tendsto (fun k ↦ (w.iteration.inverseHessian k).det /
    p.scale (k / 2) ^ 2) atTop (𝓝 (1 / p.gammaStar))
  /-- Helper for lem:planar-degeneration: the canonical determinant has the source equivalent. -/
  determinant_equivalent : (fun k ↦ (w.iteration.inverseHessian k).det) ~[atTop]
    (fun k ↦ p.scale (k / 2) ^ 2 / p.gammaStar)
  /-- Helper for lem:planar-degeneration: the canonical normalized free coefficient limit. -/
  free_normalized : Tendsto (fun k ↦ iterationFreeCoefficient w.iteration k /
    p.scale (k / 2) ^ 2) atTop (𝓝 (1 / p.gammaStar))
  /-- Helper for lem:planar-degeneration: the canonical original free coefficient equivalent. -/
  free_equivalent : iterationFreeCoefficient w.iteration ~[atTop]
    (fun k ↦ p.scale (k / 2) ^ 2 / p.gammaStar)
  /-- Helper for lem:planar-degeneration: the canonical free coefficient has
  the order of consecutive canonical physical step products. -/
  free_stepProduct_order : ∃ lower > 0, ∃ upper > 0, ∀ᶠ k in atTop,
    lower * (‖iterationStep w.iteration (k - 1)‖ * ‖iterationStep w.iteration k‖) ≤
        iterationFreeCoefficient w.iteration k ∧
      iterationFreeCoefficient w.iteration k ≤ upper *
        (‖iterationStep w.iteration (k - 1)‖ * ‖iterationStep w.iteration k‖)
  /-- Helper for sec:known-results: both canonical Xu scalar normalized phase limits. -/
  xu_normalized : ∀ i : Fin 2,
    Tendsto (fun j ↦ iterationXuScalar w.iteration (2 * j + (i : ℕ)) / p.scale j ^ 2)
      atTop (𝓝 (xuLeadingCoefficient p i))
  /-- Helper for sec:known-results: both canonical Xu scalar phase equivalents. -/
  xu_equivalent : ∀ i : Fin 2,
    (fun j ↦ iterationXuScalar w.iteration (2 * j + (i : ℕ))) ~[atTop]
      (fun j ↦ xuLeadingCoefficient p i * p.scale j ^ 2)
  /-- Helper for sec:known-results: the canonical cross-phase Xu ratio limit. -/
  xu_jump : Tendsto (fun j ↦ iterationXuScalar w.iteration (2 * j + 2) /
    iterationXuScalar w.iteration (2 * j + 1)) atTop (𝓝 (p.deltaEven * p.ell / p.deltaOdd))
  /-- Helper for sec:known-results: the canonical cross-phase Xu limit exceeds one. -/
  xu_jump_gt_one : 1 < p.deltaEven * p.ell / p.deltaOdd
  /-- Helper for sec:known-results: the canonical Xu scalar is not eventually nonincreasing. -/
  xu_not_eventually_nonincreasing : ¬ ∀ᶠ k in atTop,
    iterationXuScalar w.iteration (k + 1) ≤ iterationXuScalar w.iteration k
  /-- Helper for sec:known-results: accepted canonical endpoint derivatives
  are eventually nonzero. -/
  endpoint_eventually_ne_zero : ∀ᶠ k in atTop,
    inner ℝ (DFP.gradients w.iteration.objective w.iteration.point (k + 1))
      (w.iteration.point (k + 1) - w.iteration.point k) ≠ 0

/-- Helper for sec:known-results and lem:planar-degeneration: `SourceIdentity`
transfers every scalar comparison conclusion to the same canonical DFP
counterexample, retaining the original scales and physical inverse matrices. -/
theorem canonicalScalarProperties_of_source {p : Parameters} {κ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (hsource : PlanarCounterexample.SourceIdentity p κ w) (h : ScalarSequenceProperties p) :
    CanonicalScalarProperties p w := by
  constructor
  · simpa only [hsource.gradients] using h.gradientNorm_limit
  · simpa only [iterationStep_eq_source hsource] using h.stepNorm_not_summable
  · simpa only [iterationStep_eq_source hsource] using h.length_tendsto_atTop
  · simpa only [iterationCurvature_eq_source hsource] using h.curvature_formula
  · rw [funext (iterationCurvature_eq_source hsource)]
    exact h.curvature_limit
  · simpa only [hsource.inverseHessian] using h.determinant_normalized
  · simpa only [hsource.inverseHessian] using h.determinant_equivalent
  · simpa only [iterationFreeCoefficient_eq_source hsource] using h.free_normalized
  · rw [funext (iterationFreeCoefficient_eq_source hsource)]
    exact h.free_equivalent
  · simpa only [iterationStep_eq_source hsource, iterationFreeCoefficient_eq_source hsource]
      using h.free_stepProduct_order
  · intro i
    simpa only [iterationXuScalar_eq_source hsource] using h.xu_normalized i
  · intro i
    simpa only [iterationXuScalar_eq_source hsource] using h.xu_equivalent i
  · simpa only [iterationXuScalar_eq_source hsource] using h.xu_jump
  · exact h.xu_jump_gt_one
  · simpa only [iterationXuScalar_eq_source hsource] using h.xu_not_eventually_nonincreasing
  · rw [hsource.gradients, hsource.point]
    exact h.endpoint_eventually_ne_zero

/-- Helper for sec:known-results and lem:planar-degeneration: one actual
geometric source witness and its exact canonical certificate jointly satisfy
the scalar comparison package. All conclusions belong to that same witness. -/
theorem sameOrbitScalarProperties_of_geometry {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V κ : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) (hs : 0 < s)
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2)
      (p.withStartIndex j0).c1 (p.withStartIndex j0).c2}
    (hsource : PlanarCounterexample.SourceIdentity (p.withStartIndex j0) κ w) :
    ScalarSequenceProperties (p.withStartIndex j0) ∧
      CanonicalScalarProperties (p.withStartIndex j0) w := by
  have hscalar := scalarSequenceProperties_of_geometry h hβ hβone hstart hs
  exact ⟨hscalar, canonicalScalarProperties_of_source hsource hscalar⟩

/-- Helper for sec:known-results: both original gradient-norm quotient
expansions, their strict phase signs, and the resulting failures of eventual
monotonicity on one source trajectory. -/
structure GradientSequenceProperties (p : Parameters) : Prop where
  /-- Helper for sec:known-results: the common feedback leading coefficient is positive. -/
  feedback_pos : 0 < p.feedbackPotential p.gammaStar
  /-- Helper for sec:known-results: both gradient quotient remainders have
  one common positive quadratic error constant. -/
  ratio_errors : ∃ C > 0, ∀ᶠ j in atTop,
    |‖p.gradients (2 * j + 1)‖ / ‖p.gradients (2 * j)‖ - 1 +
        p.feedbackPotential p.gammaStar * p.scale j ^ (1 + p.beta)| ≤ C * p.scale j ^ 2 ∧
      |‖p.gradients (2 * j + 2)‖ / ‖p.gradients (2 * j + 1)‖ - 1 -
        p.feedbackPotential p.gammaStar * p.scale j ^ (1 + p.beta)| ≤ C * p.scale j ^ 2
  /-- Helper for sec:known-results: the two source quotient expansions in
  asymptotic notation, with one common quadratic error constant. -/
  ratio_isBigOWith : ∃ C > 0,
    Asymptotics.IsBigOWith C atTop
        (fun j ↦ ‖p.gradients (2 * j + 1)‖ / ‖p.gradients (2 * j)‖ - 1 +
          p.feedbackPotential p.gammaStar * p.scale j ^ (1 + p.beta))
        (fun j ↦ p.scale j ^ 2) ∧
      Asymptotics.IsBigOWith C atTop
        (fun j ↦ ‖p.gradients (2 * j + 2)‖ / ‖p.gradients (2 * j + 1)‖ - 1 -
          p.feedbackPotential p.gammaStar * p.scale j ^ (1 + p.beta))
        (fun j ↦ p.scale j ^ 2)
  /-- Helper for sec:known-results: gradient norms strictly decrease from
  even to odd indices and strictly increase from odd to even indices. -/
  phase_signs : ∀ᶠ j in atTop,
    ‖p.gradients (2 * j + 1)‖ < ‖p.gradients (2 * j)‖ ∧
      ‖p.gradients (2 * j + 1)‖ < ‖p.gradients (2 * j + 2)‖
  /-- Helper for sec:known-results: the gradient norms are not eventually nonincreasing. -/
  not_eventually_nonincreasing : ¬ ∀ᶠ k in atTop, ‖p.gradients (k + 1)‖ ≤ ‖p.gradients k‖
  /-- Helper for sec:known-results: the gradient norms are not eventually nondecreasing. -/
  not_eventually_nondecreasing : ¬ ∀ᶠ k in atTop, ‖p.gradients k‖ ≤ ‖p.gradients (k + 1)‖

/-- Helper for sec:known-results: the actual geometric source witness
satisfies both gradient quotient expansions and both eventual monotonicity
failures, with no added asymptotic or sign hypothesis. -/
theorem gradientSequenceProperties_of_geometry {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) :
    GradientSequenceProperties (p.withStartIndex j0) := by
  have hM : 0 ≤ M := by
    have hbound := h.radial.trajectory.slow_bound 0
    exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans hbound)
      (Real.rpow_pos_of_pos (scale_pos p.beta hstart 0) _)
  have hU : 0 ≤ U := by
    have hdecrease := h.radial.radii.strictAnti (Nat.zero_lt_succ 0)
    have hbound := h.radial.radii.drop_upper 0
    have hproduct : 0 ≤ U * scale p.beta j0 (0 / 2) ^ 2 := by linarith
    exact nonneg_of_mul_nonneg_left hproduct (sq_pos_of_pos (scale_pos p.beta hstart _))
  have hfeedback := (p.withStartIndex_analyticData j0).2.2
  obtain ⟨C, hC, herrors⟩ := GradientOscillation.existsGradientRatioErrors p hβ hβone hM hU
  obtain ⟨D, hD, hbigO⟩ := GradientOscillation.existsGradientRatioBigOWith p hβ hβone hM hU
  have hmonotone := GradientOscillation.gradientNorm_not_eventually_monotone
    p hβ hβone hstart hM hU h.radial
  constructor
  · rw [hfeedback, p.withStartIndex_gammaStar]
    exact GradientOscillation.feedbackPotential_base_pos p hβ
  · refine ⟨C, hC, ?_⟩
    simpa only [hfeedback, p.withStartIndex_gammaStar, RadiusBounds.scale_withStartIndex,
      p.withStartIndex_beta] using herrors j0 hstart N B K c h.radial
  · refine ⟨D, hD, ?_⟩
    simpa only [hfeedback, p.withStartIndex_gammaStar, RadiusBounds.scale_withStartIndex,
      p.withStartIndex_beta] using hbigO j0 hstart N B K c h.radial
  · exact GradientOscillation.gradientPhaseSigns p hβ hβone hstart hM hU h.radial
  · exact hmonotone.1
  · exact hmonotone.2

/-- Helper for sec:known-results: a source sequence whose complete cluster
set is the unit circle cannot converge to any point. The argument retains
the two distinct antipodal source cluster points. -/
theorem point_not_tendsto_of_circleCluster {p : Parameters}
    (hcluster : ∀ x : EuclideanSpace ℝ (Fin 2), MapClusterPt x atTop p.point ↔ ‖x‖ = 1)
    (x : EuclideanSpace ℝ (Fin 2)) : ¬ Tendsto p.point atTop (𝓝 x) := by
  intro hlimit
  have hunit (θ : ℝ) : DFP.Polar.polarUnit θ = x := by
    obtain ⟨j, hstrict, hsubsequence⟩ :=
      ((hcluster _).mpr (DFP.Polar.PointGeometry.polarUnit_norm θ)).tendsto_subseq
    exact tendsto_nhds_unique hsubsequence (hlimit.comp hstrict.tendsto_atTop)
  have hantipodal := (hunit 0).trans (hunit Real.pi).symm
  have hcoordinate := congrArg (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0) hantipodal
  norm_num only [DFP.Polar.polarUnit_apply_zero, Real.cos_zero, Real.cos_pi] at hcoordinate

/-- Helper for sec:known-results and lem:planar-degeneration: the complete
source sequence conclusions, including the full cluster set, scalar and matrix
asymptotics, gradient oscillation and failure of iterate convergence. -/
structure SequenceProperties (p : Parameters) : Prop where
  /-- Helper for sec:known-results: original scalar and physical matrix conclusions. -/
  scalar : ScalarSequenceProperties p
  /-- Helper for sec:known-results: original gradient quotient expansions and phase signs. -/
  gradient : GradientSequenceProperties p
  /-- Helper for sec:known-results: the source accumulation set is the complete unit circle. -/
  cluster : ∀ x : EuclideanSpace ℝ (Fin 2), MapClusterPt x atTop p.point ↔ ‖x‖ = 1
  /-- Helper for sec:known-results: the original source iterates do not converge. -/
  point_not_tendsto : ∀ x : EuclideanSpace ℝ (Fin 2), ¬ Tendsto p.point atTop (𝓝 x)

/-- Helper for sec:known-results and lem:planar-degeneration: all source
sequence conclusions follow from the same actual chosen geometric witness.
No sequence comparison conclusion is assumed. -/
theorem sequenceProperties_of_geometry {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) (hs : 0 < s) :
    SequenceProperties (p.withStartIndex j0) := by
  exact ⟨scalarSequenceProperties_of_geometry h hβ hβone hstart hs,
    gradientSequenceProperties_of_geometry h hβ hβone hstart, h.cluster,
    point_not_tendsto_of_circleCluster h.cluster⟩

/-- Helper for sec:known-results: the two gradient quotient expansions and
oscillation statements on the canonical DFP certificate itself. -/
structure CanonicalGradientProperties (p : Parameters)
    (w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2) : Prop where
  /-- Helper for sec:known-results: both actual canonical gradient quotient error bounds. -/
  ratio_errors : ∃ C > 0, ∀ᶠ j in atTop,
    |‖DFP.gradients w.iteration.objective w.iteration.point (2 * j + 1)‖ /
          ‖DFP.gradients w.iteration.objective w.iteration.point (2 * j)‖ - 1 +
        p.feedbackPotential p.gammaStar * p.scale j ^ (1 + p.beta)| ≤ C * p.scale j ^ 2 ∧
      |‖DFP.gradients w.iteration.objective w.iteration.point (2 * j + 2)‖ /
          ‖DFP.gradients w.iteration.objective w.iteration.point (2 * j + 1)‖ - 1 -
        p.feedbackPotential p.gammaStar * p.scale j ^ (1 + p.beta)| ≤ C * p.scale j ^ 2
  /-- Helper for sec:known-results: the two canonical quotient expansions
  in asymptotic notation with one common quadratic error constant. -/
  ratio_isBigOWith : ∃ C > 0,
    Asymptotics.IsBigOWith C atTop
        (fun j ↦ ‖DFP.gradients w.iteration.objective w.iteration.point (2 * j + 1)‖ /
            ‖DFP.gradients w.iteration.objective w.iteration.point (2 * j)‖ - 1 +
          p.feedbackPotential p.gammaStar * p.scale j ^ (1 + p.beta))
        (fun j ↦ p.scale j ^ 2) ∧
      Asymptotics.IsBigOWith C atTop
        (fun j ↦ ‖DFP.gradients w.iteration.objective w.iteration.point (2 * j + 2)‖ /
            ‖DFP.gradients w.iteration.objective w.iteration.point (2 * j + 1)‖ - 1 -
          p.feedbackPotential p.gammaStar * p.scale j ^ (1 + p.beta))
        (fun j ↦ p.scale j ^ 2)
  /-- Helper for sec:known-results: the canonical gradient norms have strict
  opposite signs on successive phases. -/
  phase_signs : ∀ᶠ j in atTop,
    ‖DFP.gradients w.iteration.objective w.iteration.point (2 * j + 1)‖ <
        ‖DFP.gradients w.iteration.objective w.iteration.point (2 * j)‖ ∧
      ‖DFP.gradients w.iteration.objective w.iteration.point (2 * j + 1)‖ <
        ‖DFP.gradients w.iteration.objective w.iteration.point (2 * j + 2)‖
  /-- Helper for sec:known-results: canonical gradient norms are not eventually nonincreasing. -/
  not_eventually_nonincreasing : ¬ ∀ᶠ k in atTop,
    ‖DFP.gradients w.iteration.objective w.iteration.point (k + 1)‖ ≤
      ‖DFP.gradients w.iteration.objective w.iteration.point k‖
  /-- Helper for sec:known-results: canonical gradient norms are not eventually nondecreasing. -/
  not_eventually_nondecreasing : ¬ ∀ᶠ k in atTop,
    ‖DFP.gradients w.iteration.objective w.iteration.point k‖ ≤
      ‖DFP.gradients w.iteration.objective w.iteration.point (k + 1)‖

/-- Helper for sec:known-results: the exact source identity transfers both
gradient quotient expansions and all strict oscillation conclusions to the
same canonical DFP certificate. -/
theorem canonicalGradientProperties_of_source {p : Parameters} {κ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (hsource : PlanarCounterexample.SourceIdentity p κ w) (h : GradientSequenceProperties p) :
    CanonicalGradientProperties p w := by
  constructor
  · simpa only [hsource.gradients] using h.ratio_errors
  · simpa only [hsource.gradients] using h.ratio_isBigOWith
  · simpa only [hsource.gradients] using h.phase_signs
  · simpa only [hsource.gradients] using h.not_eventually_nonincreasing
  · simpa only [hsource.gradients] using h.not_eventually_nondecreasing

/-- Helper for sec:known-results and lem:planar-degeneration: all quantitative
sequence conclusions concern the canonical certificate's own points, gradients,
physical steps, accepted lengths and inverse Hessians. -/
structure CanonicalSequenceProperties (p : Parameters)
    (w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2) : Prop where
  /-- Helper for sec:known-results: canonical scalar, matrix and endpoint conclusions. -/
  scalar : CanonicalScalarProperties p w
  /-- Helper for sec:known-results: canonical gradient ratio expansions and oscillation. -/
  gradient : CanonicalGradientProperties p w
  /-- Helper for sec:known-results: the canonical accumulation set is the complete unit circle. -/
  cluster : ∀ x : EuclideanSpace ℝ (Fin 2),
    MapClusterPt x atTop w.iteration.point ↔ ‖x‖ = 1
  /-- Helper for sec:known-results: the canonical DFP iterates do not converge. -/
  point_not_tendsto : ∀ x : EuclideanSpace ℝ (Fin 2),
    ¬ Tendsto w.iteration.point atTop (𝓝 x)

/-- Helper for sec:known-results and lem:planar-degeneration: the full source
sequence package transfers through the retained exact same-orbit identity. -/
theorem canonicalSequenceProperties_of_source {p : Parameters} {κ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (hsource : PlanarCounterexample.SourceIdentity p κ w) (h : SequenceProperties p) :
    CanonicalSequenceProperties p w := by
  constructor
  · exact canonicalScalarProperties_of_source hsource h.scalar
  · exact canonicalGradientProperties_of_source hsource h.gradient
  · simpa only [hsource.point] using h.cluster
  · simpa only [hsource.point] using h.point_not_tendsto

/-- Helper for sec:known-results and lem:planar-degeneration: one actual
chosen source geometry and its exact canonical certificate jointly satisfy all
gradient, length, Xu, endpoint, curvature, determinant and free-coefficient
conclusions. Every assertion refers to that same chosen source orbit. -/
theorem sameOrbitSequenceProperties_of_geometry {p : Parameters} {j0 : ℕ}
    {N M B K c U a b s V κ : ℝ}
    (h : ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) (hs : 0 < s)
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2)
      (p.withStartIndex j0).c1 (p.withStartIndex j0).c2}
    (hsource : PlanarCounterexample.SourceIdentity (p.withStartIndex j0) κ w) :
    SequenceProperties (p.withStartIndex j0) ∧
      CanonicalSequenceProperties (p.withStartIndex j0) w := by
  have hsequence := sequenceProperties_of_geometry h hβ hβone hstart hs
  exact ⟨hsequence, canonicalSequenceProperties_of_source hsource hsequence⟩

end DFP.Polar.General.SequenceAsymptotics
