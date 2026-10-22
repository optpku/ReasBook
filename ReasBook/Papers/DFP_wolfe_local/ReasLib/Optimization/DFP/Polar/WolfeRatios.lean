/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.PhysicalRealization
public import ReasLib.Optimization.DFP.Polar.RadiusExpansions
public import ReasLib.Optimization.LineSearch.Wolfe.Gradient

public section

noncomputable section

open Filter
open scoped Matrix Topology ContDiff

namespace DFP.Polar.WolfeRatios

/-- Helper for eq:polar-wolfe-ratios: the half-radius-squared model endpoint value. -/
def modelValue (p : Parameters) (k : ℕ) : ℝ := p.radius k ^ 2 / 2

/-- Helper for eq:polar-wolfe-ratios: the original model endpoint formula. -/
theorem modelValue_def (p : Parameters) (k : ℕ) :
    modelValue p k = p.radius k ^ 2 / 2 := by
  rfl

/-- Helper for eq:polar-wolfe-ratios: the original half-radius model value
is exactly the quadratic endpoint value in the original Euclidean coordinates. -/
theorem modelValue_eq_half_norm_sq (p : Parameters) (k : ℕ) :
    modelValue p k = ‖p.point k‖ ^ 2 / 2 := by
  rw [modelValue_def, Parameters.point_def, norm_smul, PhysicalRealization.polarUnit_norm,
    mul_one, Real.norm_eq_abs, sq_abs]

/-- Helper for eq:polar-wolfe-ratios: the original initial directional pairing. -/
def startSlope (p : Parameters) (k : ℕ) : ℝ :=
  inner ℝ (p.gradient k) (p.point (k + 1) - p.point k)

/-- Helper for eq:polar-wolfe-ratios: the initial physical slope formula. -/
theorem startSlope_def (p : Parameters) (k : ℕ) :
    startSlope p k = inner ℝ (p.gradient k) (p.point (k + 1) - p.point k) := by
  rfl

/-- Helper for eq:polar-wolfe-ratios: the original next-endpoint directional pairing. -/
def endSlope (p : Parameters) (k : ℕ) : ℝ :=
  inner ℝ (p.gradient (k + 1)) (p.point (k + 1) - p.point k)

/-- Helper for eq:polar-wolfe-ratios: the next physical slope formula. -/
theorem endSlope_def (p : Parameters) (k : ℕ) :
    endSlope p k = inner ℝ (p.gradient (k + 1)) (p.point (k + 1) - p.point k) := by
  rfl

/-- Helper for eq:polar-wolfe-ratios: the source Armijo model ratio on original endpoints. -/
def armijoRatio (p : Parameters) (k : ℕ) : ℝ :=
  (modelValue p k - modelValue p (k + 1)) / (-startSlope p k)

/-- Helper for eq:polar-wolfe-ratios: the original normalized model decrease. -/
theorem armijoRatio_def (p : Parameters) (k : ℕ) :
    armijoRatio p k = (modelValue p k - modelValue p (k + 1)) / (-startSlope p k) := by
  rfl

/-- Helper for eq:polar-wolfe-ratios: the source absolute-curvature ratio. -/
def curvatureRatio (p : Parameters) (k : ℕ) : ℝ := |endSlope p k| / |startSlope p k|

/-- Helper for eq:polar-wolfe-ratios: the original absolute directional-pairing quotient. -/
theorem curvatureRatio_def (p : Parameters) (k : ℕ) :
    curvatureRatio p k = |endSlope p k| / |startSlope p k| := by
  rfl

/-- Helper for eq:polar-wolfe-ratios: real Euclidean inner products are coordinate pairings. -/
theorem inner_eq_dot (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ x y = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- Helper for eq:polar-wolfe-ratios: a next radial gradient in the current polar frame. -/
theorem next_radial_eq (θ δ r ζ : ℝ) :
    WithLp.ofLp (ζ • (r • polarUnit (θ + δ))) =
      rotationMatrix θ *ᵥ ((ζ * r) • ![Real.cos δ, Real.sin δ]) := by
  rw [rotationMatrix_def]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.cos_add]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.sin_add]
    ring

/-- Helper for eq:polar-wolfe-ratios: the exact initial chord pairing before radial division. -/
theorem radial_start_pairing (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (θ δ r rNext ζ : ℝ) (hr : rNext * radiusRatioOf Z δ = r) :
    inner ℝ (ζ • (r • polarUnit θ))
      (rNext • polarUnit (θ + δ) - r • polarUnit θ) =
        -(ζ * r * rNext * omegaOf Z * Real.sin δ) := by
  rw [inner_eq_dot, smul_smul, PhysicalRealization.radial_eq,
    PhysicalRealization.chord_eq Z θ δ r rNext hr,
    Matrix.dotProduct_mulVec_eq_of_mem_orthogonalGroup _
      (PhysicalRealization.rotation_orthogonal θ), stepVOf_def]
  simp [dotProduct, Fin.sum_univ_two]
  ring

/-- Helper for eq:polar-wolfe-ratios: the exact next chord pairing before radial division. -/
theorem radial_end_pairing (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (θ δ r rNext ζNext : ℝ) (hr : rNext * radiusRatioOf Z δ = r) :
    inner ℝ (ζNext • (rNext • polarUnit (θ + δ)))
      (rNext • polarUnit (θ + δ) - r • polarUnit θ) =
        ζNext * rNext ^ 2 * Real.sin δ * (Real.sin δ - omegaOf Z * Real.cos δ) := by
  rw [inner_eq_dot, next_radial_eq,
    PhysicalRealization.chord_eq Z θ δ r rNext hr,
    Matrix.dotProduct_mulVec_eq_of_mem_orthogonalGroup _
      (PhysicalRealization.rotation_orthogonal θ), stepVOf_def]
  simp [dotProduct, Fin.sum_univ_two]
  ring

/-- Helper for eq:polar-wolfe-ratios: the source exact initial scalar-product formula. -/
theorem startSlope_eq (p : Parameters) (k : ℕ)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) (hW : p.radiusRatio k ≠ 0) :
    -startSlope p k = p.zeta k * p.radius k ^ 2 * p.omega k *
      Real.sin (p.angleIncrement k) / p.radiusRatio k := by
  rw [startSlope_def, Parameters.gradient_def, Parameters.point_def,
    Parameters.point_def, PhysicalRealization.angle_succ,
    radial_start_pairing _ _ _ _ _ _ (PhysicalRealization.radius_balance p k hr hW),
    ← Parameters.omega_def, hr]
  field_simp

/-- Helper for eq:polar-wolfe-ratios: the source exact next scalar-product formula. -/
theorem endSlope_eq (p : Parameters) (k : ℕ)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) (hW : p.radiusRatio k ≠ 0) :
    endSlope p k = p.zeta (k + 1) * p.radius k ^ 2 * Real.sin (p.angleIncrement k) /
      p.radiusRatio k ^ 2 * (Real.sin (p.angleIncrement k) -
        p.omega k * Real.cos (p.angleIncrement k)) := by
  rw [endSlope_def, Parameters.gradient_def, Parameters.point_def,
    Parameters.point_def, PhysicalRealization.angle_succ,
    radial_end_pairing _ _ _ _ _ _ (PhysicalRealization.radius_balance p k hr hW),
    ← Parameters.omega_def, hr]
  field_simp

/-- Helper for eq:polar-wolfe-ratios: source radius, multiplier, slope and angle positivity
make the physical initial slope strictly negative. -/
theorem startSlope_neg (p : Parameters) (k : ℕ) (hstart : 0 < p.startIndex)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k)
    (hradius : 0 < p.radius k) (hω : 0 < p.omega k) (hW : 0 < p.radiusRatio k) :
    startSlope p k < 0 := by
  have hζ := PhysicalRealization.zeta_pos p k
  have hsin := PhysicalRealization.angleIncrement_sin_pos p hstart k
  have hpositive : 0 < -startSlope p k := by
    rw [startSlope_eq p k hr (ne_of_gt hW)]
    exact div_pos (mul_pos (mul_pos (mul_pos hζ (sq_pos_of_pos hradius)) hω) hsin) hW
  exact neg_pos.mp hpositive

/-- Helper for eq:polar-wolfe-ratios: exact scalar cancellation in the Armijo model quotient. -/
theorem armijo_scalar (r q δ ζ W : ℝ) (hr : r ≠ 0) (hω : q ≠ 0)
    (hζ : ζ ≠ 0) (hsin : Real.sin δ ≠ 0) (hW : W ≠ 0) :
    (r ^ 2 / 2 - (r / W) ^ 2 / 2) / (ζ * r ^ 2 * q * Real.sin δ / W) =
      (W ^ 2 - 1) / (2 * ζ * q * Real.sin δ * W) := by
  field_simp

/-- Helper for eq:polar-wolfe-ratios: exact scalar cancellation in the absolute-curvature
quotient. -/
theorem curvature_scalar (r q δ ζ ζNext W : ℝ) (hr : 0 < r) (hω : 0 < q)
    (hζ : 0 < ζ) (hζNext : 0 < ζNext) (hsin : 0 < Real.sin δ) (hW : 0 < W) :
    |ζNext * r ^ 2 * Real.sin δ / W ^ 2 * (Real.sin δ - q * Real.cos δ)| /
        |-(ζ * r ^ 2 * q * Real.sin δ / W)| =
      (ζNext / ζ) * |q * Real.cos δ - Real.sin δ| / (q * W) := by
  simp only [abs_mul, abs_div, abs_neg, abs_pow, abs_of_pos hr, abs_of_pos hω,
    abs_of_pos hζ, abs_of_pos hζNext, abs_of_pos hsin, abs_of_pos hW]
  rw [abs_sub_comm (Real.sin δ) (q * Real.cos δ)]
  field_simp

/-- Helper for eq:polar-wolfe-ratios: the exact Armijo quotient for the original model endpoints. -/
theorem armijoRatio_eq (p : Parameters) (k : ℕ) (hstart : 0 < p.startIndex)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k)
    (hradius : 0 < p.radius k) (hω : 0 < p.omega k) (hW : 0 < p.radiusRatio k) :
    armijoRatio p k = (p.radiusRatio k ^ 2 - 1) /
      (2 * p.zeta k * p.omega k * Real.sin (p.angleIncrement k) * p.radiusRatio k) := by
  rw [armijoRatio_def, modelValue_def, modelValue_def,
    startSlope_eq p k hr (ne_of_gt hW), hr]
  exact armijo_scalar _ _ _ _ _ (ne_of_gt hradius) (ne_of_gt hω)
    (ne_of_gt (PhysicalRealization.zeta_pos p k))
    (ne_of_gt (PhysicalRealization.angleIncrement_sin_pos p hstart k)) (ne_of_gt hW)

/-- Helper for eq:polar-wolfe-ratios: the exact source absolute-curvature quotient on original
gradients. -/
theorem curvatureRatio_eq (p : Parameters) (k : ℕ) (hstart : 0 < p.startIndex)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k)
    (hradius : 0 < p.radius k) (hω : 0 < p.omega k) (hW : 0 < p.radiusRatio k) :
    curvatureRatio p k = (p.zeta (k + 1) / p.zeta k) *
      |p.omega k * Real.cos (p.angleIncrement k) - Real.sin (p.angleIncrement k)| /
        (p.omega k * p.radiusRatio k) := by
  have hstartEq : startSlope p k = -(p.zeta k * p.radius k ^ 2 * p.omega k *
      Real.sin (p.angleIncrement k) / p.radiusRatio k) := by
    linarith [startSlope_eq p k hr (ne_of_gt hW)]
  rw [curvatureRatio_def, hstartEq, endSlope_eq p k hr (ne_of_gt hW)]
  exact curvature_scalar _ _ _ _ _ _ hradius hω (PhysicalRealization.zeta_pos p k)
    (PhysicalRealization.zeta_pos p (k + 1))
    (PhysicalRealization.angleIncrement_sin_pos p hstart k) hW

/-- Helper for eq:polar-wolfe-asymptotics: the positive limiting angular coefficient. -/
theorem limitAngle_pos (i : Fin 2) : 0 < Normalized.limitAngle i := by
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue, Normalized.limitAngle_zero] using
      mul_pos zero_lt_two AngularGeometry.baseAngle_pos
  · simpa only [Fin.mk_one, Fin.isValue, Normalized.limitAngle_one] using
      AngularGeometry.baseAngle_pos

/-- Helper for eq:polar-wolfe-asymptotics: the analytic sine quotient has the source zero-scale
value. -/
theorem sinFactor_zero (i : Fin 2) : Normalized.sinFactor i 0 = Normalized.limitAngle i := by
  rw [Normalized.sinFactor_def, Normalized.stageAngle_def,
    Normalized.stageAngleFactor_def, Normalized.angleFactor_def, Normalized.unitRoot_def]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [Normalized.stageWeight_zero, Normalized.limitAngle_zero]
    norm_num
    ring
  · simp only [Fin.mk_one, Fin.isValue]
    rw [Normalized.stageWeight_one, Normalized.limitAngle_one]
    norm_num
    ring

/-- Helper for eq:polar-wolfe-asymptotics: the source Armijo limit for either phase. -/
def armijoLimit (ν : ℝ) (i : Fin 2) : ℝ :=
  1 - Normalized.limitAngle i / (2 * RadiusExpansions.referenceSlope ν i)

/-- Helper for eq:polar-wolfe-asymptotics: the explicit phase Armijo limit. -/
theorem armijoLimit_def (ν : ℝ) (i : Fin 2) :
    armijoLimit ν i = 1 - Normalized.limitAngle i / (2 * RadiusExpansions.referenceSlope ν i) := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the source strong-curvature limit for either phase. -/
def curvatureLimit (ν : ℝ) (i : Fin 2) : ℝ :=
  1 - Normalized.limitAngle i / RadiusExpansions.referenceSlope ν i

/-- Helper for eq:polar-wolfe-asymptotics: the explicit phase curvature limit. -/
theorem curvatureLimit_def (ν : ℝ) (i : Fin 2) :
    curvatureLimit ν i = 1 - Normalized.limitAngle i / RadiusExpansions.referenceSlope ν i := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: either continued stage angle vanishes at zero scale. -/
theorem stageAngle_zero (i : Fin 2) : Normalized.stageAngle i 0 = 0 := by
  rw [Normalized.stageAngle_def]
  simp

/-- Helper for eq:polar-wolfe-asymptotics: the original radius factor in normalized slope
coordinates. -/
def regularRadius (i : Fin 2) (t q : ℝ) : ℝ :=
  Real.cos (Normalized.stageAngle i t) + t ^ 4 * q * Normalized.sinFactor i t

/-- Helper for eq:polar-wolfe-asymptotics: the canceled source radius-factor formula. -/
theorem regularRadius_def (i : Fin 2) (t q : ℝ) :
    regularRadius i t q =
      Real.cos (Normalized.stageAngle i t) + t ^ 4 * q * Normalized.sinFactor i t := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: normalized radius equals one at zero scale. -/
theorem regularRadius_zero (i : Fin 2) (q : ℝ) : regularRadius i 0 q = 1 := by
  rw [regularRadius_def, stageAngle_zero]
  simp

/-- Helper for eq:polar-wolfe-asymptotics: the Armijo quotient after exact trigonometric
cancellation. -/
def regularArmijo (i : Fin 2) (z : Fin 4 → ℝ) : ℝ :=
  (2 * z 1 * Real.cos (Normalized.stageAngle i (z 0)) - Normalized.sinFactor i (z 0) +
    z 1 ^ 2 * z 0 ^ 4 * Normalized.sinFactor i (z 0)) /
      (2 * z 2 * z 1 * regularRadius i (z 0) (z 1))

/-- Helper for eq:polar-wolfe-asymptotics: the regular Armijo quotient formula. -/
theorem regularArmijo_def (i : Fin 2) (z : Fin 4 → ℝ) :
    regularArmijo i z =
      (2 * z 1 * Real.cos (Normalized.stageAngle i (z 0)) - Normalized.sinFactor i (z 0) +
        z 1 ^ 2 * z 0 ^ 4 * Normalized.sinFactor i (z 0)) /
          (2 * z 2 * z 1 * regularRadius i (z 0) (z 1)) := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the signed curvature quotient after quadratic
cancellation. -/
def regularCurvature (i : Fin 2) (z : Fin 4 → ℝ) : ℝ :=
  (z 3 / z 2) * (z 1 * Real.cos (Normalized.stageAngle i (z 0)) -
    Normalized.sinFactor i (z 0)) / (z 1 * regularRadius i (z 0) (z 1))

/-- Helper for eq:polar-wolfe-asymptotics: the regular signed curvature formula. -/
theorem regularCurvature_def (i : Fin 2) (z : Fin 4 → ℝ) :
    regularCurvature i z = (z 3 / z 2) *
      (z 1 * Real.cos (Normalized.stageAngle i (z 0)) - Normalized.sinFactor i (z 0)) /
        (z 1 * regularRadius i (z 0) (z 1)) := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the four actual scalar inputs of a regular ratio. -/
def ratioData (t q ζ ζNext : ℝ) : Fin 4 → ℝ := ![t, q, ζ, ζNext]

/-- Helper for eq:polar-wolfe-asymptotics: the public regular-ratio input formula. -/
theorem ratioData_def (t q ζ ζNext : ℝ) : ratioData t q ζ ζNext = ![t, q, ζ, ζNext] := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the first input coordinate is the original scale. -/
theorem ratioData_zero (t q ζ ζNext : ℝ) : ratioData t q ζ ζNext 0 = t := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the second input coordinate is the normalized source
slope. -/
theorem ratioData_one (t q ζ ζNext : ℝ) : ratioData t q ζ ζNext 1 = q := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the third input coordinate is the current multiplier. -/
theorem ratioData_two (t q ζ ζNext : ℝ) : ratioData t q ζ ζNext 2 = ζ := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the fourth input coordinate is the next multiplier. -/
theorem ratioData_three (t q ζ ζNext : ℝ) : ratioData t q ζ ζNext 3 = ζNext := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: every normalized scalar input
is one of its four named source coordinates. -/
theorem ratioData_apply (t q ζ ζNext : ℝ) (r : Fin 4) :
    ratioData t q ζ ζNext r =
      if (r : ℕ) = 0 then t else if (r : ℕ) = 1 then q else
        if (r : ℕ) = 2 then ζ else ζNext := by
  fin_cases r
  all_goals rfl

/-- Helper for eq:polar-wolfe-asymptotics: the source zero-scale regular-ratio input. -/
def referenceData (ν : ℝ) (i : Fin 2) : Fin 4 → ℝ :=
  ratioData 0 (RadiusExpansions.referenceSlope ν i) 1 1

/-- Helper for eq:polar-wolfe-asymptotics: the original reference slope and unit multipliers. -/
theorem referenceData_def (ν : ℝ) (i : Fin 2) :
    referenceData ν i = ratioData 0 (RadiusExpansions.referenceSlope ν i) 1 1 := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the regular quotients are jointly analytic
in scale, normalized source slope, and the two original feedback multipliers. -/
theorem regularRatios_analyticAt (ν : ℝ) (i : Fin 2)
    (hQ : RadiusExpansions.referenceSlope ν i ≠ 0) :
    AnalyticAt ℝ (fun z : Fin 4 → ℝ ↦ (regularArmijo i z, regularCurvature i z))
      (referenceData ν i) := by
  have hzero : referenceData ν i 0 = 0 := by simp [referenceData_def, ratioData_zero]
  have hcoord (j : Fin 4) : AnalyticAt ℝ (fun z : Fin 4 → ℝ ↦ z j)
      (referenceData ν i) :=
    (ContinuousLinearMap.proj j : (Fin 4 → ℝ) →L[ℝ] ℝ).analyticAt _
  have hconst (c : ℝ) : AnalyticAt ℝ (fun _ : Fin 4 → ℝ ↦ c) (referenceData ν i) :=
    analyticAt_const
  have hS : AnalyticAt ℝ (fun z : Fin 4 → ℝ ↦ Normalized.sinFactor i (z 0))
      (referenceData ν i) :=
    (Normalized.sinFactor_analyticAt i).comp_of_eq (hcoord 0) hzero
  have hδ : AnalyticAt ℝ (fun z : Fin 4 → ℝ ↦ Normalized.stageAngle i (z 0))
      (referenceData ν i) :=
    (Normalized.stageAngle_analyticAt i).comp_of_eq (hcoord 0) hzero
  have hcos : AnalyticAt ℝ (fun z : Fin 4 → ℝ ↦ Real.cos (Normalized.stageAngle i (z 0)))
      (referenceData ν i) := Real.analyticAt_cos.comp hδ
  have hWanalytic : AnalyticAt ℝ (fun z : Fin 4 → ℝ ↦ regularRadius i (z 0) (z 1))
      (referenceData ν i) := by
    simpa only [regularRadius_def] using
      hcos.fun_add ((((hcoord 0).fun_pow 4).fun_mul (hcoord 1)).fun_mul hS)
  have hq : referenceData ν i 1 ≠ 0 := by
    simpa [referenceData_def, ratioData_def] using hQ
  have hzeta : referenceData ν i 2 ≠ 0 := by
    simp [referenceData_def, ratioData_two]
  have hW : regularRadius i (referenceData ν i 0) (referenceData ν i 1) ≠ 0 := by
    rw [hzero, regularRadius_zero]
    exact one_ne_zero
  have hden : 2 * referenceData ν i 2 * referenceData ν i 1 *
      regularRadius i (referenceData ν i 0) (referenceData ν i 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hzeta) hq) hW
  have hdenCurv : referenceData ν i 1 *
      regularRadius i (referenceData ν i 0) (referenceData ν i 1) ≠ 0 := mul_ne_zero hq hW
  have hnumA := (((hconst 2).fun_mul (hcoord 1)).fun_mul hcos |>.fun_sub hS).add
    ((((hcoord 1).fun_pow 2).fun_mul ((hcoord 0).fun_pow 4)).fun_mul hS)
  have hdenA := (((hconst 2).fun_mul (hcoord 2)).fun_mul (hcoord 1)).fun_mul hWanalytic
  have hnumC := ((hcoord 3).fun_div (hcoord 2) hzeta).fun_mul (((hcoord 1).fun_mul hcos).fun_sub hS)
  have hdenC := (hcoord 1).fun_mul hWanalytic
  simp only [regularArmijo_def, regularCurvature_def]
  exact (hnumA.fun_div hdenA hden).prod (hnumC.fun_div hdenC hdenCurv)

/-- Helper for eq:polar-wolfe-asymptotics: exact quadratic-angle cancellation gives the Armijo
limit. -/
theorem regularArmijo_reference (ν : ℝ) (i : Fin 2)
    (hQ : RadiusExpansions.referenceSlope ν i ≠ 0) :
    regularArmijo i (referenceData ν i) = armijoLimit ν i := by
  rw [regularArmijo_def, referenceData_def, armijoLimit_def]
  simp only [ratioData_zero, ratioData_one, ratioData_two, stageAngle_zero, Real.cos_zero,
    sinFactor_zero, regularRadius_zero, mul_one]
  field_simp
  ring

/-- Helper for eq:polar-wolfe-asymptotics: the signed regular curvature has the source limit. -/
theorem regularCurvature_reference (ν : ℝ) (i : Fin 2)
    (hQ : RadiusExpansions.referenceSlope ν i ≠ 0) :
    regularCurvature i (referenceData ν i) = curvatureLimit ν i := by
  rw [regularCurvature_def, referenceData_def, curvatureLimit_def]
  simp only [ratioData_zero, ratioData_one, ratioData_two, ratioData_three, stageAngle_zero,
    Real.cos_zero, sinFactor_zero, regularRadius_zero, mul_one, div_self one_ne_zero, one_mul]
  field_simp

/-- Helper for eq:polar-wolfe-asymptotics: an analytic map sends a uniformly linear
input error to a uniformly linear output error on a fixed neighborhood. -/
theorem analyticErrorOfLinearInput {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (x₀ : E) (hf : AnalyticAt ℝ f x₀) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ → ∀ x : E,
      ‖x - x₀‖ ≤ B * t → ‖f x - f x₀‖ ≤ C * t := by
  obtain ⟨K, s, hs, hLip⟩ := hf.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hbase : x₀ ∈ s := mem_of_mem_nhds hs
  have hBOne : 0 < B + 1 := by linarith
  have hKOne : 0 < (K : ℝ) + 1 := by positivity
  refine ⟨((K : ℝ) + 1) * (B + 1), mul_pos hKOne hBOne,
    ε / (B + 1), div_pos hε hBOne, ?_⟩
  intro t ht htδ x hx
  have hsmall : (B + 1) * t < ε := by
    nlinarith [(lt_div_iff₀ hBOne).mp htδ]
  have hin : x ∈ s := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hBt : B * t ≤ (B + 1) * t := by nlinarith
    exact hx.trans_lt (hBt.trans_lt hsmall)
  calc
    ‖f x - f x₀‖ ≤ (K : ℝ) * ‖x - x₀‖ :=
      (lipschitzOnWith_iff_norm_sub_le.mp hLip) hin hbase
    _ ≤ (K : ℝ) * (B * t) := mul_le_mul_of_nonneg_left hx K.coe_nonneg
    _ ≤ (((K : ℝ) + 1) * (B + 1)) * t := by
      nlinarith [mul_nonneg K.coe_nonneg ht]

/-- Helper for eq:polar-wolfe-asymptotics: the actual shared cubic feedback
is jointly analytic near a nonzero boundary amplitude. -/
theorem feedback_analyticAt (L κ : ℝ) (x₀ : ℝ × ℝ × ℝ) (hA : x₀.1 ≠ 0) :
    AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ Normalized.feedback L κ z.1 z.2) (0, x₀) := by
  have hfirst : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.1) (0, x₀) := analyticAt_fst
  have hstate : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2) (0, x₀) := analyticAt_snd
  have hAmp : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2.1) (0, x₀) :=
    analyticAt_fst.comp hstate
  simp only [Normalized.feedback_def]
  fun_prop (disch := assumption)

/-- Helper for eq:polar-wolfe-asymptotics: scale and state each have a linear bound
in the ordinary product norm around the zero-scale source state. -/
theorem scaleState_norm_le (t B : ℝ) (x x₀ : ℝ × ℝ × ℝ)
    (ht : 0 ≤ t) (hB : 0 ≤ B) (hx : ‖x - x₀‖ ≤ B * t) :
    ‖(t, x) - (0, x₀)‖ ≤ (B + 1) * t := by
  have hdist : dist (t, x) (0, x₀) ≤ (B + 1) * t := by
    rw [Prod.dist_eq]
    apply max_le
    · rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht]
      nlinarith
    · rw [dist_eq_norm]
      nlinarith
  simpa only [dist_eq_norm] using hdist

/-- Helper for eq:polar-wolfe-asymptotics: source feedback differs from one
by a uniform linear error on the proved linear state neighborhood. -/
theorem feedbackErrorOfStateBound (L κ : ℝ) (x₀ : ℝ × ℝ × ℝ)
    (hA : x₀.1 ≠ 0) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ → ∀ x : ℝ × ℝ × ℝ,
      ‖x - x₀‖ ≤ B * t → |Normalized.feedback L κ t x - 1| ≤ C * t := by
  have hBOne : 0 ≤ B + 1 := by linarith
  obtain ⟨C, hC, δ, hδ, hbound⟩ := analyticErrorOfLinearInput
    (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ Normalized.feedback L κ z.1 z.2)
    (0, x₀) (feedback_analyticAt L κ x₀ hA) (B + 1) hBOne
  have hzero : Normalized.feedback L κ 0 x₀ = 1 := by simp [Normalized.feedback_def]
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro t ht htδ x hx
  have h := hbound t ht htδ (t, x) (scaleState_norm_le t B x x₀ ht hB hx)
  simpa only [hzero, Real.norm_eq_abs] using h

/-- Helper for eq:polar-wolfe-asymptotics: normalized shared feedback is the original odd
multiplier. -/
theorem feedback_prescribed (p : Parameters) (j : ℕ) :
    Normalized.feedback p.feedbackRate p.kStar (p.scale j) (p.normalizedEvenState j) =
      p.zeta (2 * j + 1) := by
  rw [StageFeasibility.normalizedEvenState_eq_coordinates,
    StageFeasibility.feedback_coordinates_prescribed, Parameters.zeta_odd]

/-- Helper for eq:polar-wolfe-asymptotics: one feedback bound controls the current
and next original multipliers in both phases of the same cycle. -/
theorem zeta_phase_errors (p : Parameters) (j : ℕ) (C : ℝ)
    (hfb : |p.zeta (2 * j + 1) - 1| ≤ C * p.scale j) (i : Fin 2) :
    |p.zeta (2 * j + (i : ℕ)) - 1| ≤ C * p.scale j ∧
      |p.zeta (2 * j + (i : ℕ) + 1) - 1| ≤ C * p.scale j := by
  have hnonneg : 0 ≤ C * p.scale j := (abs_nonneg _).trans hfb
  fin_cases i
  · simp only [Nat.add_zero, Parameters.zeta_even, sub_self, abs_zero]
    exact ⟨hnonneg, hfb⟩
  · have hnext : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
    simp only [hnext, Parameters.zeta_even, sub_self, abs_zero]
    exact ⟨hfb, hnonneg⟩

/-- Helper for eq:polar-wolfe-asymptotics: the actual original feedback multipliers
have uniform linear errors for every subsequently larger freshly initialized start index. -/
theorem actualFeedbackEstimates :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ C > 0, ∃ J : ℕ, 0 < J ∧
        ∀ j₀ ≥ J, ∀ j : ℕ, ∀ i : Fin 2,
          let p := Parameters.of j₀ νStar
          |p.zeta (2 * j + (i : ℕ)) - 1| ≤ C * p.scale j ∧
            |p.zeta (2 * j + (i : ℕ) + 1) - 1| ≤ C * p.scale j := by
  obtain ⟨η, hη, hTube⟩ := Continuation.actualTube
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, hbranch, N, hN, M, hM, J₀, hJ₀, htube⟩ := hTube νStar hnear
  obtain ⟨B, hB, δs, hδs, hstate⟩ :=
    RadiusExpansions.stateBoundOfTube νStar M N hparameter hbranch hM.le hN.le
  have hK := TwoCycle.cycleK_bijOn_parameterSet.mapsTo hparameter
  have hE := (StageFeasibility.regularState_def _).mp
    (StageFeasibility.regularState_evenState (cycleK νStar) hK)
  obtain ⟨C, hC, δf, hδf, hfeedback⟩ := feedbackErrorOfStateBound
    (4 * baseAngle / (9 * νStar)) (cycleK νStar)
    (TwoCycle.evenState (cycleK νStar)) hE.1.ne' B hB.le
  obtain ⟨J₁, _, hscale⟩ := Continuation.existsStartThreshold
    (min δs δf) (lt_min hδs hδf)
  refine ⟨hparameter, C, hC, max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀ j i
  let p := Parameters.of j₀ νStar
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using
      hJ₀.trans_le ((le_max_left J₀ J₁).trans hj₀)
  have ht := ScaleTails.scale_pos p hstart j
  have hsmall : p.scale j < min δs δf :=
    (ScaleTails.scale_antitone p hstart (Nat.zero_le j)).trans_lt
      (hscale νStar j₀ ((le_max_right J₀ J₁).trans hj₀))
  have hactual := htube j₀ ((le_max_left J₀ J₁).trans hj₀) j
  have hslow : |(p.normalizedEvenState j).1 - cycleK νStar| ≤ M * p.scale j := by
    simpa only [p, Parameters.kStar_def, Parameters.of_cycleParameter] using hactual.1
  have hx := hstate (p.scale j) ht.le (hsmall.trans_le (min_le_left _ _))
    (p.normalizedEvenState j) hslow hactual.2.1
  have hfb := hfeedback (p.scale j) ht.le (hsmall.trans_le (min_le_right _ _))
    (p.normalizedEvenState j) hx
  have hL : p.feedbackRate = 4 * baseAngle / (9 * νStar) := by
    simp only [p, Parameters.feedbackRate_def, Parameters.of_cycleParameter]
  have hκ : p.kStar = cycleK νStar := by
    simp only [p, Parameters.kStar_def, Parameters.of_cycleParameter]
  rw [← hL, ← hκ, feedback_prescribed] at hfb
  exact zeta_phase_errors p j C hfb i

/-- Helper for eq:polar-wolfe-asymptotics: the normalized radius is the original radius at slope
`t²q`. -/
theorem regularRadius_eq (i : Fin 2) (t q : ℝ) (ht : 0 < t) :
    regularRadius i t q = Real.cos (Normalized.stageAngle i t) +
      t ^ 2 * q * Real.sin (Normalized.stageAngle i t) := by
  rw [regularRadius_def, Normalized.sinFactor_eq_sin_div i t ht]
  field_simp

/-- Helper for eq:polar-wolfe-asymptotics: the source sine factor retains its exact quadratic
power. -/
theorem sin_stageAngle_eq (i : Fin 2) (t : ℝ) (ht : 0 < t) :
    Real.sin (Normalized.stageAngle i t) = t ^ 2 * Normalized.sinFactor i t := by
  rw [Normalized.sinFactor_eq_sin_div i t ht]
  field_simp

/-- Helper for eq:polar-wolfe-asymptotics: the identity `cos²+sin²=1` cancels
the fourth-order numerator in the original Armijo ratio exactly. -/
theorem radius_square_sub_one (i : Fin 2) (t q : ℝ) (ht : 0 < t) :
    regularRadius i t q ^ 2 - 1 = t ^ 4 * Normalized.sinFactor i t *
      (2 * q * Real.cos (Normalized.stageAngle i t) - Normalized.sinFactor i t +
        q ^ 2 * t ^ 4 * Normalized.sinFactor i t) := by
  have htrig := Real.cos_sq_add_sin_sq (Normalized.stageAngle i t)
  rw [sin_stageAngle_eq i t ht] at htrig
  rw [regularRadius_def]
  nlinarith

/-- Helper for eq:polar-wolfe-asymptotics: exact common-factor cancellation gives the regular
Armijo quotient. -/
theorem armijo_normalization (i : Fin 2) (t q ζ ζNext : ℝ) (ht : 0 < t)
    (hq : q ≠ 0) (hζ : ζ ≠ 0) (hS : Normalized.sinFactor i t ≠ 0)
    (hW : regularRadius i t q ≠ 0) :
    (regularRadius i t q ^ 2 - 1) /
        (2 * ζ * (t ^ 2 * q) * Real.sin (Normalized.stageAngle i t) * regularRadius i t q) =
      regularArmijo i (ratioData t q ζ ζNext) := by
  rw [radius_square_sub_one i t q ht, sin_stageAngle_eq i t ht,
    regularArmijo_def]
  simp only [ratioData_zero, ratioData_one, ratioData_two]
  field_simp

/-- Helper for eq:polar-wolfe-asymptotics: the signed source curvature quotient
has exact cancellation of its common quadratic factor. -/
theorem curvature_normalization (i : Fin 2) (t q ζ ζNext : ℝ) (ht : 0 < t)
    (hq : q ≠ 0) (hζ : ζ ≠ 0) (hW : regularRadius i t q ≠ 0) :
    (ζNext / ζ) * ((t ^ 2 * q) * Real.cos (Normalized.stageAngle i t) -
        Real.sin (Normalized.stageAngle i t)) / ((t ^ 2 * q) * regularRadius i t q) =
      regularCurvature i (ratioData t q ζ ζNext) := by
  rw [sin_stageAngle_eq i t ht, regularCurvature_def]
  simp only [ratioData_zero, ratioData_one, ratioData_two, ratioData_three]
  field_simp

/-- Helper for eq:polar-wolfe-asymptotics: the original source slope exceeds the limiting angle. -/
theorem referenceSlope_gt_angle (ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet) (i : Fin 2) :
    Normalized.limitAngle i < RadiusExpansions.referenceSlope ν i := by
  have h := RadiusExpansions.referenceSlopes_gt ν hν
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue, Normalized.limitAngle_zero] using h.1
  · simpa only [Fin.mk_one, Fin.isValue, Normalized.limitAngle_one] using h.2

/-- Helper for eq:polar-wolfe-asymptotics: the original phase slopes are strictly positive. -/
theorem referenceSlope_pos (ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet) (i : Fin 2) :
    0 < RadiusExpansions.referenceSlope ν i :=
  (limitAngle_pos i).trans (referenceSlope_gt_angle ν hν i)

/-- Helper for eq:polar-wolfe-asymptotics: the signed source curvature limit is positive. -/
theorem curvatureLimit_pos (ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet) (i : Fin 2) :
    0 < curvatureLimit ν i := by
  rw [curvatureLimit_def]
  exact sub_pos.mpr ((div_lt_one (referenceSlope_pos ν hν i)).2
    (referenceSlope_gt_angle ν hν i))

/-- Helper for eq:polar-wolfe-asymptotics: the two regular ratios have uniform linear
errors for every input with a proved linear deviation from the source reference data. -/
theorem ratioErrorsOfLinearInput (ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet)
    (i : Fin 2) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ → ∀ z : Fin 4 → ℝ,
      ‖z - referenceData ν i‖ ≤ B * t →
        |regularArmijo i z - armijoLimit ν i| ≤ C * t ∧
          |abs (regularCurvature i z) - curvatureLimit ν i| ≤ C * t := by
  have hQ := ne_of_gt (referenceSlope_pos ν hν i)
  obtain ⟨C, hC, δ, hδ, hbound⟩ := analyticErrorOfLinearInput
    (fun z : Fin 4 → ℝ ↦ (regularArmijo i z, regularCurvature i z))
    (referenceData ν i) (regularRatios_analyticAt ν i hQ) B hB
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro t ht htδ z hz
  have hfull := hbound t ht htδ z hz
  have hA := (norm_fst_le
    ((regularArmijo i z, regularCurvature i z) -
      (regularArmijo i (referenceData ν i), regularCurvature i (referenceData ν i)))).trans hfull
  have hC := (norm_snd_le
    ((regularArmijo i z, regularCurvature i z) -
      (regularArmijo i (referenceData ν i), regularCurvature i (referenceData ν i)))).trans hfull
  simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs,
    regularArmijo_reference ν i hQ, regularCurvature_reference ν i hQ] at hA hC
  have habs : |abs (regularCurvature i z) - curvatureLimit ν i| ≤
      |regularCurvature i z - curvatureLimit ν i| := by
    simpa only [abs_of_pos (curvatureLimit_pos ν hν i)] using
      abs_abs_sub_abs_le_abs_sub (regularCurvature i z) (curvatureLimit ν i)
  exact ⟨hA, habs.trans hC⟩

/-- Helper for eq:polar-wolfe-asymptotics: the source slopes have the strict
right-sided bounds `2a<QE<3a` and `a<QO<3a` on the original parameter interval. -/
theorem referenceSlope_bounds (ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet)
    (hright : baseAngle < ν) :
    2 * baseAngle < RadiusExpansions.referenceSlope ν 0 ∧
      RadiusExpansions.referenceSlope ν 0 < 3 * baseAngle ∧
      baseAngle < RadiusExpansions.referenceSlope ν 1 ∧
      RadiusExpansions.referenceSlope ν 1 < 3 * baseAngle := by
  have ha := AngularGeometry.baseAngle_pos
  have hinterval := hν
  rw [TwoCycle.parameterSet_def] at hinterval
  have hden : 0 < 2 * ν - baseAngle := by linarith
  have hνupper : ν < 2 * baseAngle := by linarith [hinterval.2]
  have hsum : 0 < ν + baseAngle := by linarith
  have hprod := mul_pos (sub_pos.mpr hright) hsum
  have hprodW := mul_neg_of_pos_of_neg (sub_pos.mpr hright) (sub_neg.mpr hνupper)
  have hz : cycleZ ν < baseAngle := by
    rw [cycleZ_def]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hw : cycleW ν < 2 * baseAngle := by
    rw [cycleW_def]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hlow := RadiusExpansions.referenceSlopes_gt ν hν
  refine ⟨hlow.1, ?_, hlow.2, ?_⟩
  · rw [RadiusExpansions.referenceSlope_even]
    linarith
  · rw [RadiusExpansions.referenceSlope_odd]
    linarith

/-- Helper for eq:polar-wolfe-asymptotics: both source curvature limits lie
strictly below two thirds for every right-sided source parameter sufficiently near the base. -/
theorem curvatureLimit_lt_two_thirds (ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet)
    (hright : baseAngle < ν) (i : Fin 2) : curvatureLimit ν i < 2 / 3 := by
  have hbounds := referenceSlope_bounds ν hν hright
  have hQ := referenceSlope_pos ν hν i
  have hangle := limitAngle_pos i
  have hupper : RadiusExpansions.referenceSlope ν i < 3 * Normalized.limitAngle i := by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Normalized.limitAngle_zero]
      nlinarith [AngularGeometry.baseAngle_pos, hbounds.2.1]
    · simpa only [Fin.mk_one, Fin.isValue, Normalized.limitAngle_one] using hbounds.2.2.2
  have hratio : (1 / 3 : ℝ) < Normalized.limitAngle i / RadiusExpansions.referenceSlope ν i := by
    apply (lt_div_iff₀ hQ).2
    linarith
  rw [curvatureLimit_def]
  linarith

/-- Helper for eq:polar-wolfe-asymptotics: dividing the proved cubic source slope
error by the positive squared scale gives a linear normalized error. -/
theorem normalizedSlope_error (t q Q C : ℝ) (ht : 0 < t)
    (herror : |q - Q * t ^ 2| ≤ C * t ^ 3) : |q / t ^ 2 - Q| ≤ C * t := by
  have hden := sq_pos_of_pos ht
  have heq : q / t ^ 2 - Q = (q - Q * t ^ 2) / t ^ 2 := by field_simp
  rw [heq, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |q - Q * t ^ 2| ≤ C * t ^ 3 := herror
    _ = C * t * t ^ 2 := by ring

/-- Helper for eq:polar-wolfe-asymptotics: componentwise source errors control
the ordinary norm of the four regular-ratio inputs. -/
theorem ratioData_norm_le (ν : ℝ) (i : Fin 2) (t q ζ ζNext B : ℝ)
    (ht : 0 ≤ t) (htB : t ≤ B * t)
    (hq : |q - RadiusExpansions.referenceSlope ν i| ≤ B * t)
    (hζ : |ζ - 1| ≤ B * t) (hζNext : |ζNext - 1| ≤ B * t) :
    ‖ratioData t q ζ ζNext - referenceData ν i‖ ≤ B * t := by
  apply (pi_norm_le_iff_of_nonneg (ht.trans htB)).2
  intro r
  fin_cases r
  all_goals norm_num only [Pi.sub_apply, referenceData_def, ratioData_apply,
    Fin.val_mk, Real.norm_eq_abs, ite_true, ite_false]
  · simpa only [sub_zero, abs_of_nonneg ht] using htB
  · exact hq
  · exact hζ
  · exact hζNext

/-- Helper for eq:polar-wolfe-asymptotics: the normalized scalar inputs retain
the original physical slope and current/next multipliers of the chosen phase. -/
def actualRatioData (p : Parameters) (j : ℕ) (i : Fin 2) : Fin 4 → ℝ :=
  ratioData (p.scale j) (p.omega (2 * j + (i : ℕ)) / p.scale j ^ 2)
    (p.zeta (2 * j + (i : ℕ))) (p.zeta (2 * j + (i : ℕ) + 1))

/-- Helper for eq:polar-wolfe-asymptotics: the actual four-input normalization formula. -/
theorem actualRatioData_def (p : Parameters) (j : ℕ) (i : Fin 2) :
    actualRatioData p j i =
      ratioData (p.scale j) (p.omega (2 * j + (i : ℕ)) / p.scale j ^ 2)
        (p.zeta (2 * j + (i : ℕ))) (p.zeta (2 * j + (i : ℕ) + 1)) := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the regular normalized radius is
exactly the original prescribed radius factor at every positive source scale. -/
theorem regularRadius_prescribed (p : Parameters) (j : ℕ) (i : Fin 2)
    (hstart : 0 < p.startIndex) :
    regularRadius i (p.scale j) (p.omega (2 * j + (i : ℕ)) / p.scale j ^ 2) =
      p.radiusRatio (2 * j + (i : ℕ)) := by
  have ht := ScaleTails.scale_pos p hstart j
  rw [regularRadius_eq i _ _ ht, Normalized.stageAngle_scale p i j hstart,
    Parameters.radiusRatio_def, radiusRatioOf_def, ← Parameters.omega_def]
  field_simp

/-- Helper for eq:polar-wolfe-asymptotics: the original physical ratios equal
the regular scalar quotients, after exact cancellation of the true source scale. -/
theorem actualRatios_eq (p : Parameters) (j : ℕ) (i : Fin 2) (hstart : 0 < p.startIndex)
    (hr : p.radius (2 * j + (i : ℕ) + 1) =
      p.radius (2 * j + (i : ℕ)) / p.radiusRatio (2 * j + (i : ℕ)))
    (hradius : 0 < p.radius (2 * j + (i : ℕ)))
    (hω : 0 < p.omega (2 * j + (i : ℕ))) (hW : 0 < p.radiusRatio (2 * j + (i : ℕ))) :
    armijoRatio p (2 * j + (i : ℕ)) = regularArmijo i (actualRatioData p j i) ∧
      curvatureRatio p (2 * j + (i : ℕ)) = |regularCurvature i (actualRatioData p j i)| := by
  have ht := ScaleTails.scale_pos p hstart j
  have hq : 0 < p.omega (2 * j + (i : ℕ)) / p.scale j ^ 2 :=
    div_pos hω (sq_pos_of_pos ht)
  have hζ := PhysicalRealization.zeta_pos p (2 * j + (i : ℕ))
  have hζNext := PhysicalRealization.zeta_pos p (2 * j + (i : ℕ) + 1)
  have hsin : Normalized.sinFactor i (p.scale j) ≠ 0 := by
    rw [Normalized.sinFactor_eq_sin_div i _ ht,
      Normalized.stageAngle_scale p i j hstart]
    exact ne_of_gt (div_pos (PhysicalRealization.angleIncrement_sin_pos p hstart _)
      (sq_pos_of_pos ht))
  have hWregular : regularRadius i (p.scale j)
      (p.omega (2 * j + (i : ℕ)) / p.scale j ^ 2) ≠ 0 := by
    rw [regularRadius_prescribed p j i hstart]
    exact ne_of_gt hW
  have hqcancel : p.scale j ^ 2 *
      (p.omega (2 * j + (i : ℕ)) / p.scale j ^ 2) = p.omega (2 * j + (i : ℕ)) := by
    field_simp
  have hA := armijo_normalization i (p.scale j)
    (p.omega (2 * j + (i : ℕ)) / p.scale j ^ 2)
    (p.zeta (2 * j + (i : ℕ))) (p.zeta (2 * j + (i : ℕ) + 1)) ht
    (ne_of_gt hq) (ne_of_gt hζ) hsin hWregular
  have hC := curvature_normalization i (p.scale j)
    (p.omega (2 * j + (i : ℕ)) / p.scale j ^ 2)
    (p.zeta (2 * j + (i : ℕ))) (p.zeta (2 * j + (i : ℕ) + 1)) ht
    (ne_of_gt hq) (ne_of_gt hζ) hWregular
  rw [regularRadius_prescribed p j i hstart, Normalized.stageAngle_scale p i j hstart,
    hqcancel] at hA hC
  constructor
  · rw [armijoRatio_eq p _ hstart hr hradius hω hW, actualRatioData_def]
    exact hA
  · rw [curvatureRatio_eq p _ hstart hr hradius hω hW, actualRatioData_def, ← hC]
    simp only [abs_div, abs_mul, abs_of_pos hζ, abs_of_pos hζNext, abs_of_pos hω,
      abs_of_pos hW]

/-- Helper for eq:polar-wolfe-asymptotics: the actual normalized ratio inputs
satisfy a fixed linear error bound, with positive original scalar data and exact
radius recurrence, uniformly before all larger freshly initialized starting indices. -/
theorem actualRatioInputEstimates :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ B > 0, ∃ J : ℕ, 0 < J ∧
        ∀ j₀ ≥ J, ∀ j : ℕ, ∀ i : Fin 2,
          let p := Parameters.of j₀ νStar
          0 < p.radius (2 * j + (i : ℕ)) ∧
            0 < p.omega (2 * j + (i : ℕ)) ∧
            0 < p.radiusRatio (2 * j + (i : ℕ)) ∧
            p.radius (2 * j + (i : ℕ) + 1) =
              p.radius (2 * j + (i : ℕ)) / p.radiusRatio (2 * j + (i : ℕ)) ∧
            ‖actualRatioData p j i - referenceData νStar i‖ ≤ B * p.scale j := by
  obtain ⟨ηs, hηs, hslope⟩ := RadiusExpansions.actualSlopeAndRadiusEstimates
  obtain ⟨ηf, hηf, hfeedback⟩ := actualFeedbackEstimates
  obtain ⟨ηr, hηr, hradii⟩ := RadiusProducts.polarRadiusProducts
  refine ⟨min ηs (min ηf ηr), lt_min hηs (lt_min hηf hηr), ?_⟩
  intro νStar hnear
  have hnearS : νStar ∈ Set.Ioo baseAngle (baseAngle + ηs) :=
    Set.Ioo_subset_Ioo_right (add_le_add le_rfl (min_le_left ηs (min ηf ηr))) hnear
  have hnearF : νStar ∈ Set.Ioo baseAngle (baseAngle + ηf) :=
    Set.Ioo_subset_Ioo_right (add_le_add le_rfl
      ((min_le_right ηs (min ηf ηr)).trans (min_le_left ηf ηr))) hnear
  have hnearR : νStar ∈ Set.Ioo baseAngle (baseAngle + ηr) :=
    Set.Ioo_subset_Ioo_right (add_le_add le_rfl
      ((min_le_right ηs (min ηf ηr)).trans (min_le_right ηf ηr))) hnear
  obtain ⟨hparameter, Cs, hCs, Js, hJs, hS⟩ := hslope νStar hnearS
  obtain ⟨_, Cf, hCf, Jf, _, hF⟩ := hfeedback νStar hnearF
  obtain ⟨_, K, _, c, _, R, _, Jr, _, hR⟩ := hradii νStar hnearR
  let qmin := min (RadiusExpansions.referenceSlope νStar 0)
    (RadiusExpansions.referenceSlope νStar 1)
  have hqmin : 0 < qmin := lt_min (referenceSlope_pos νStar hparameter 0)
    (referenceSlope_pos νStar hparameter 1)
  have hcutoff : 0 < qmin / (2 * Cs) := div_pos hqmin (mul_pos zero_lt_two hCs)
  obtain ⟨Jq, _, hscale⟩ := Continuation.existsStartThreshold _ hcutoff
  have hB : 0 < 1 + Cs + Cf := by linarith
  refine ⟨hparameter, 1 + Cs + Cf, hB, max Js (max Jf (max Jr Jq)),
    hJs.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀ j i
  let p := Parameters.of j₀ νStar
  have hjS : Js ≤ j₀ := (le_max_left Js _).trans hj₀
  have hjF : Jf ≤ j₀ := (le_max_left Jf _).trans ((le_max_right Js _).trans hj₀)
  have hjR : Jr ≤ j₀ := (le_max_left Jr Jq).trans
    ((le_max_right Jf _).trans ((le_max_right Js _).trans hj₀))
  have hjq : Jq ≤ j₀ := (le_max_right Jr Jq).trans
    ((le_max_right Jf _).trans ((le_max_right Js _).trans hj₀))
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJs.trans_le hjS
  have ht := ScaleTails.scale_pos p hstart j
  have hsmall : p.scale j < qmin / (2 * Cs) :=
    (ScaleTails.scale_antitone p hstart (Nat.zero_le j)).trans_lt (hscale νStar j₀ hjq)
  have hCt : Cs * p.scale j < qmin / 2 := by
    nlinarith [(lt_div_iff₀ (mul_pos zero_lt_two hCs)).mp hsmall]
  have hsource := hS j₀ hjS j i
  have hqerror := normalizedSlope_error (p.scale j)
    (p.omega (2 * j + (i : ℕ))) (RadiusExpansions.referenceSlope νStar i) Cs ht hsource.2.1
  have hqminLe : qmin ≤ RadiusExpansions.referenceSlope νStar i :=
    (RadiusProducts.phaseCoefficient_bounds (RadiusExpansions.referenceSlope νStar) i).1
  have hqpositive : 0 < p.omega (2 * j + (i : ℕ)) / p.scale j ^ 2 := by
    linarith [(abs_le.mp hqerror).1]
  have hω : 0 < p.omega (2 * j + (i : ℕ)) :=
    (div_pos_iff_of_pos_right (sq_pos_of_pos ht)).mp hqpositive
  have hrad := hR j₀ hjR
  have hrPos : ∀ k, 0 < p.radius k := fun k ↦ zero_lt_one.trans (hrad.above_one k)
  have hW := PhysicalRealization.radiusRatio_pos_of_radiusRecurrence p
    (2 * j + (i : ℕ)) (hrPos _) (hrPos _) (hrad.recurrence _)
  have hfb := hF j₀ hjF j i
  have hCsB : Cs ≤ 1 + Cs + Cf := by linarith
  have hCfB : Cf ≤ 1 + Cs + Cf := by linarith
  have htB : p.scale j ≤ (1 + Cs + Cf) * p.scale j := by nlinarith
  refine ⟨hrPos _, hω, hW, hrad.recurrence _, ?_⟩
  rw [actualRatioData_def]
  exact ratioData_norm_le νStar i _ _ _ _ _ ht.le htB
    (hqerror.trans (mul_le_mul_of_nonneg_right hCsB ht.le))
    (hfb.1.trans (mul_le_mul_of_nonneg_right hCfB ht.le))
    (hfb.2.trans (mul_le_mul_of_nonneg_right hCfB ht.le))

/-- Helper for eq:polar-wolfe-asymptotics: the finite alternating phases
share one positive error constant and one positive scale neighborhood. -/
theorem uniformPhaseRatioErrors (ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ → ∀ i : Fin 2,
      ∀ z : Fin 4 → ℝ, ‖z - referenceData ν i‖ ≤ B * t →
        |regularArmijo i z - armijoLimit ν i| ≤ C * t ∧
          |abs (regularCurvature i z) - curvatureLimit ν i| ≤ C * t := by
  obtain ⟨C₀, hC₀, δ₀, hδ₀, hzero⟩ := ratioErrorsOfLinearInput ν hν 0 B hB
  obtain ⟨C₁, hC₁, δ₁, hδ₁, hone⟩ := ratioErrorsOfLinearInput ν hν 1 B hB
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro t ht htδ
  rw [Fin.forall_fin_two]
  constructor
  · intro z hz
    have h := hzero t ht (htδ.trans_le (min_le_left _ _)) z hz
    have hconstant : C₀ * t ≤ (C₀ + C₁) * t :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₁.le) ht
    exact ⟨h.1.trans hconstant, h.2.trans hconstant⟩
  · intro z hz
    have h := hone t ht (htδ.trans_le (min_le_right _ _)) z hz
    have hconstant : C₁ * t ≤ (C₀ + C₁) * t :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀.le) ht
    exact ⟨h.1.trans hconstant, h.2.trans hconstant⟩

/-- eq:polar-wolfe-asymptotics: the original actual model Armijo and absolute
curvature ratios have the manuscript's phase limits with a common linear
scale error, uniformly for all later freshly initialized natural starting indices. -/
theorem polarWolfeAsymptotics :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ C > 0, ∃ J : ℕ, 0 < J ∧
        ∀ j₀ ≥ J, ∀ j : ℕ, ∀ i : Fin 2,
          let p := Parameters.of j₀ νStar
          startSlope p (2 * j + (i : ℕ)) < 0 ∧
            |armijoRatio p (2 * j + (i : ℕ)) - armijoLimit νStar i| ≤ C * p.scale j ∧
            |curvatureRatio p (2 * j + (i : ℕ)) - curvatureLimit νStar i| ≤ C * p.scale j := by
  obtain ⟨η, hη, hinputs⟩ := actualRatioInputEstimates
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, B, hB, J₀, hJ₀, hinput⟩ := hinputs νStar hnear
  obtain ⟨C, hC, δ, hδ, hlocal⟩ := uniformPhaseRatioErrors νStar hparameter B hB.le
  obtain ⟨J₁, _, hscale⟩ := Continuation.existsStartThreshold δ hδ
  refine ⟨hparameter, C, hC, max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀ j i
  let p := Parameters.of j₀ νStar
  have hjInput : J₀ ≤ j₀ := (le_max_left J₀ J₁).trans hj₀
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJ₀.trans_le hjInput
  have ht := ScaleTails.scale_pos p hstart j
  have hsmall : p.scale j < δ :=
    (ScaleTails.scale_antitone p hstart (Nat.zero_le j)).trans_lt
      (hscale νStar j₀ ((le_max_right J₀ J₁).trans hj₀))
  obtain ⟨hradius, hω, hW, hr, hnorm⟩ := hinput j₀ hjInput j i
  have herror := hlocal (p.scale j) ht.le hsmall i (actualRatioData p j i) hnorm
  have hratios := actualRatios_eq p j i hstart hr hradius hω hW
  refine ⟨startSlope_neg p _ hstart hr hradius hω hW, ?_, ?_⟩
  · simpa only [← hratios.1] using herror.1
  · simpa only [← hratios.2] using herror.2

/-- eq:polar-wolfe-ratios: direct scalar products give both exact ratios for
the original prescribed point and gradient data and half-radius-squared endpoint values.
Every scalar feasibility premise is discharged uniformly before the choice of j0. -/
theorem polarWolfeRatios :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ J : ℕ, 0 < J ∧
        ∀ j₀ ≥ J, ∀ k : ℕ,
          let p := Parameters.of j₀ νStar
          startSlope p k < 0 ∧
            armijoRatio p k = (p.radiusRatio k ^ 2 - 1) /
              (2 * p.zeta k * p.omega k * Real.sin (p.angleIncrement k) * p.radiusRatio k) ∧
            curvatureRatio p k = (p.zeta (k + 1) / p.zeta k) *
              |p.omega k * Real.cos (p.angleIncrement k) - Real.sin (p.angleIncrement k)| /
                (p.omega k * p.radiusRatio k) := by
  obtain ⟨η, hη, hinputs⟩ := actualRatioInputEstimates
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, B, _, J, hJ, hinput⟩ := hinputs νStar hnear
  refine ⟨hparameter, J, hJ, ?_⟩
  intro j₀ hj₀ k
  let p := Parameters.of j₀ νStar
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJ.trans_le hj₀
  have h := hinput j₀ hj₀ (k / 2) (RadiusExpansions.phaseIndex k)
  rw [RadiusExpansions.phaseIndex_identity] at h
  obtain ⟨hradius, hω, hW, hr, _⟩ := h
  exact ⟨startSlope_neg p k hstart hr hradius hω hW,
    armijoRatio_eq p k hstart hr hradius hω hW,
    curvatureRatio_eq p k hstart hr hradius hω hW⟩

/-- Helper for eq:polar-wolfe-asymptotics: the even Armijo limit is the exact source formula. -/
theorem armijoLimit_even (ν : ℝ) :
    armijoLimit ν 0 = 1 - baseAngle / RadiusExpansions.referenceSlope ν 0 := by
  rw [armijoLimit_def, Normalized.limitAngle_zero]
  by_cases hQ : RadiusExpansions.referenceSlope ν 0 = 0
  · simp [hQ]
  · field_simp

/-- Helper for eq:polar-wolfe-asymptotics: the odd Armijo limit is the exact source formula. -/
theorem armijoLimit_odd (ν : ℝ) :
    armijoLimit ν 1 = 1 - baseAngle / (2 * RadiusExpansions.referenceSlope ν 1) := by
  rw [armijoLimit_def, Normalized.limitAngle_one]

/-- Helper for eq:polar-wolfe-asymptotics: the even curvature limit is the exact source formula. -/
theorem curvatureLimit_even (ν : ℝ) :
    curvatureLimit ν 0 = 1 - 2 * baseAngle / RadiusExpansions.referenceSlope ν 0 := by
  rw [curvatureLimit_def, Normalized.limitAngle_zero]

/-- Helper for eq:polar-wolfe-asymptotics: the odd curvature limit is the exact source formula. -/
theorem curvatureLimit_odd (ν : ℝ) :
    curvatureLimit ν 1 = 1 - baseAngle / RadiusExpansions.referenceSlope ν 1 := by
  rw [curvatureLimit_def, Normalized.limitAngle_one]

/-- Helper for thm:main and eq:polar-wolfe-asymptotics: both original phase slopes
have the base value `3a`, evaluated from the exact rational source family. -/
theorem referenceSlope_base (i : Fin 2) :
    RadiusExpansions.referenceSlope baseAngle i = 3 * baseAngle := by
  have ha := ne_of_gt AngularGeometry.baseAngle_pos
  have hz : cycleZ baseAngle = baseAngle := by
    rw [cycleZ_def]
    field_simp
  have hw : cycleW baseAngle = 2 * baseAngle := by
    rw [cycleW_def]
    field_simp
    ring
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, RadiusExpansions.referenceSlope_even, hz]
    ring
  · simp only [Fin.mk_one, Fin.isValue, RadiusExpansions.referenceSlope_odd, hw]
    ring

/-- Helper for thm:main and eq:polar-wolfe-asymptotics: the phase Armijo limits
are continuous at the source base parameter. -/
theorem armijoLimit_continuousAt_base (i : Fin 2) :
    ContinuousAt (fun ν : ℝ ↦ armijoLimit ν i) baseAngle := by
  have ha := AngularGeometry.baseAngle_pos
  have hden : 2 * baseAngle - baseAngle ≠ 0 := by linarith
  have hQ : ContinuousAt (fun ν : ℝ ↦ RadiusExpansions.referenceSlope ν i) baseAngle := by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, RadiusExpansions.referenceSlope_even, cycleZ_def]
      fun_prop (disch := assumption)
    · simp only [Fin.mk_one, Fin.isValue, RadiusExpansions.referenceSlope_odd, cycleW_def]
      fun_prop (disch := assumption)
  have hnonzero : 2 * RadiusExpansions.referenceSlope baseAngle i ≠ 0 := by
    rw [referenceSlope_base]
    positivity
  have hquot : ContinuousAt (fun ν : ℝ ↦ Normalized.limitAngle i /
      (2 * RadiusExpansions.referenceSlope ν i)) baseAngle :=
    continuousAt_const.div (continuousAt_const.mul hQ) hnonzero
  simp only [armijoLimit_def]
  exact continuousAt_const.sub hquot

/-- Helper for thm:main and eq:polar-wolfe-asymptotics: the even Armijo limit at the base is two
thirds. -/
theorem armijoLimit_base_even : armijoLimit baseAngle 0 = 2 / 3 := by
  have ha := ne_of_gt AngularGeometry.baseAngle_pos
  rw [armijoLimit_even, referenceSlope_base]
  field_simp
  ring

/-- Helper for thm:main and eq:polar-wolfe-asymptotics: the odd Armijo limit at the base is five
sixths. -/
theorem armijoLimit_base_odd : armijoLimit baseAngle 1 = 5 / 6 := by
  have ha := ne_of_gt AngularGeometry.baseAngle_pos
  rw [armijoLimit_odd, referenceSlope_base]
  field_simp
  ring

/-- Helper for thm:main and eq:polar-wolfe-asymptotics: strict source Armijo
and curvature margins hold throughout a fixed small right parameter interval. -/
theorem existsStrictLimitMargins (c₁ : ℝ) (hc₁ : c₁ < 2 / 3) :
    ∃ η > 0, ∀ ν ∈ Set.Ioo baseAngle (baseAngle + η),
      ν ∈ TwoCycle.parameterSet ∧ ∀ i : Fin 2,
        c₁ < armijoLimit ν i ∧ curvatureLimit ν i < 2 / 3 := by
  have hzero : c₁ < armijoLimit baseAngle 0 := by
    rw [armijoLimit_base_even]
    exact hc₁
  have hone : c₁ < armijoLimit baseAngle 1 := by
    rw [armijoLimit_base_odd]
    linarith
  have hnearZero : ∀ᶠ ν in 𝓝 baseAngle, c₁ < armijoLimit ν 0 :=
    (armijoLimit_continuousAt_base 0).eventually (Ioi_mem_nhds hzero)
  have hnearOne : ∀ᶠ ν in 𝓝 baseAngle, c₁ < armijoLimit ν 1 :=
    (armijoLimit_continuousAt_base 1).eventually (Ioi_mem_nhds hone)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hnearZero.and hnearOne)
  have hfour : (0 : ℝ) < 4 := by norm_num
  have hquarter : 0 < baseAngle / 4 := div_pos AngularGeometry.baseAngle_pos hfour
  refine ⟨min δ (baseAngle / 4), lt_min hδ hquarter, ?_⟩
  intro ν hν
  have hin : ν ∈ Metric.ball baseAngle δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hν.1)]
    linarith [hν.2, min_le_left δ (baseAngle / 4)]
  have hboth := hball hin
  have hparameter : ν ∈ TwoCycle.parameterSet := by
    rw [TwoCycle.parameterSet_def]
    constructor
    · linarith [hν.1, AngularGeometry.baseAngle_pos]
    · linarith [hν.2, min_le_right δ (baseAngle / 4)]
  refine ⟨hparameter, ?_⟩
  intro i
  have hArmijo : c₁ < armijoLimit ν i := by
    fin_cases i
    · simpa only [Fin.zero_eta, Fin.isValue] using hboth.1
    · simpa only [Fin.mk_one, Fin.isValue] using hboth.2
  exact ⟨hArmijo, curvatureLimit_lt_two_thirds ν hparameter hν.1 i⟩

/-- Helper for thm:main and eq:polar-wolfe-asymptotics: one positive margin
works for both limiting model Armijo decreases and both curvature limits. -/
theorem existsCommonLimitMargin (ν c₁ : ℝ)
    (hlimits : ∀ i : Fin 2, c₁ < armijoLimit ν i ∧ curvatureLimit ν i < 2 / 3) :
    ∃ m > 0, ∀ i : Fin 2,
      c₁ + m ≤ armijoLimit ν i ∧ curvatureLimit ν i + m ≤ 2 / 3 := by
  let a : Fin 2 → ℝ := fun i ↦ armijoLimit ν i - c₁
  let w : Fin 2 → ℝ := fun i ↦ 2 / 3 - curvatureLimit ν i
  let m := min (min (a 0) (a 1)) (min (w 0) (w 1))
  have ha : ∀ i, 0 < a i := fun i ↦ sub_pos.mpr (hlimits i).1
  have hw : ∀ i, 0 < w i := fun i ↦ sub_pos.mpr (hlimits i).2
  have hm : 0 < m := lt_min (lt_min (ha 0) (ha 1)) (lt_min (hw 0) (hw 1))
  have hmA (i : Fin 2) : m ≤ a i :=
    (min_le_left _ _).trans (RadiusProducts.phaseCoefficient_bounds a i).1
  have hmW (i : Fin 2) : m ≤ w i :=
    (min_le_right _ _).trans (RadiusProducts.phaseCoefficient_bounds w i).1
  refine ⟨m, hm, ?_⟩
  intro i
  have hA := hmA i
  have hW := hmW i
  dsimp only [a] at hA
  dsimp only [w] at hW
  constructor
  · linarith
  · linarith

/-- Helper for thm:main and eq:polar-wolfe-ratios: the actual original
model endpoints and gradient pairings satisfy scalar strong Wolfe at one step. -/
structure ModelStrongWolfe (p : Parameters) (k : ℕ) (c₁ c₂ : ℝ) : Prop where
  /-- Helper for thm:main: the prescribed coefficients are admissible. -/
  coefficients : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1
  /-- Helper for eq:polar-wolfe-ratios: the original chord has strictly negative initial pairing. -/
  descent : startSlope p k < 0
  /-- Helper for eq:polar-wolfe-ratios: the half-radius-squared model satisfies Armijo. -/
  armijo : LineSearch.Wolfe.IsArmijo c₁ (modelValue p k) (modelValue p (k + 1)) (startSlope p k)
  /-- Helper for eq:polar-wolfe-ratios: the original endpoint pairings satisfy strong curvature. -/
  curvature : LineSearch.Wolfe.IsStrongCurvature c₂ (startSlope p k) (endSlope p k)
  /-- Helper for eq:polar-wolfe-ratios: the original Armijo ratio meets the prescribed
  coefficient. -/
  armijoRatio_ge : c₁ ≤ armijoRatio p k
  /-- Helper for eq:polar-wolfe-ratios: the original curvature ratio is at most two thirds. -/
  curvatureRatio_le : curvatureRatio p k ≤ 2 / 3

/-- Helper for thm:main and eq:polar-wolfe-ratios: source ratio bounds with
negative actual initial pairing imply the standard scalar strong-Wolfe inequalities. -/
theorem modelStrongWolfe_of_ratios (p : Parameters) (k : ℕ) (c₁ c₂ : ℝ)
    (hcoeff : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (hc₂ : 2 / 3 ≤ c₂)
    (hdescent : startSlope p k < 0) (hA : c₁ ≤ armijoRatio p k)
    (hC : curvatureRatio p k ≤ 2 / 3) : ModelStrongWolfe p k c₁ c₂ := by
  have hdecrease : c₁ ≤ (modelValue p k - modelValue p (k + 1)) / (-startSlope p k) := by
    simpa only [armijoRatio_def] using hA
  have hArmijo := LineSearch.Wolfe.IsArmijo.of_decreaseRatio hdescent hdecrease
  have hden : 0 < |startSlope p k| := abs_pos.mpr (ne_of_lt hdescent)
  have hratio : |endSlope p k| / |startSlope p k| ≤ c₂ := by
    simpa only [curvatureRatio_def] using hC.trans hc₂
  have hcurvature := LineSearch.Wolfe.isStrongCurvature_iff.mpr ((div_le_iff₀ hden).mp hratio)
  exact ⟨hcoeff, hdescent, hArmijo, hcurvature, hA, hC⟩

/-- Helper for thm:main and eq:polar-wolfe-asymptotics: choose the source
parameter inside any additional positive right-neighborhood cap, then choose
one natural threshold before every later fresh j0. All original model steps
satisfy the prescribed strong Wolfe inequalities, with curvature ratio at most two thirds. -/
theorem existsUniformModelWolfe (c₁ c₂ ηcap : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1)
    (hcap : 0 < ηcap) :
    ∃ νStar ∈ Set.Ioo baseAngle (baseAngle + ηcap),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ J : ℕ, 0 < J ∧
        ∀ j₀ ≥ J, ∀ k : ℕ, ModelStrongWolfe (Parameters.of j₀ νStar) k c₁ c₂ := by
  obtain ⟨ηa, hηa, hactual⟩ := polarWolfeAsymptotics
  obtain ⟨ηm, hηm, hmargins⟩ := existsStrictLimitMargins c₁ hc₁lim
  let d := min ηcap (min ηa ηm)
  have hd : 0 < d := lt_min hcap (lt_min hηa hηm)
  let νStar := baseAngle + d / 2
  have hnear : νStar ∈ Set.Ioo baseAngle (baseAngle + d) := by
    dsimp only [νStar]
    constructor
    · linarith
    · linarith
  have hcapν : νStar ∈ Set.Ioo baseAngle (baseAngle + ηcap) :=
    Set.Ioo_subset_Ioo_right (add_le_add le_rfl (min_le_left _ _)) hnear
  have hnearA : νStar ∈ Set.Ioo baseAngle (baseAngle + ηa) :=
    Set.Ioo_subset_Ioo_right (add_le_add le_rfl
      ((min_le_right ηcap (min ηa ηm)).trans (min_le_left ηa ηm))) hnear
  have hnearM : νStar ∈ Set.Ioo baseAngle (baseAngle + ηm) :=
    Set.Ioo_subset_Ioo_right (add_le_add le_rfl
      ((min_le_right ηcap (min ηa ηm)).trans (min_le_right ηa ηm))) hnear
  obtain ⟨hparameter, hlimits⟩ := hmargins νStar hnearM
  obtain ⟨_, C, hC, J₀, hJ₀, huniform⟩ := hactual νStar hnearA
  obtain ⟨m, hm, hmargin⟩ := existsCommonLimitMargin νStar c₁ hlimits
  have htwoC : 0 < 2 * C := mul_pos zero_lt_two hC
  obtain ⟨J₁, _, hscale⟩ := Continuation.existsStartThreshold
    (m / (2 * C)) (div_pos hm htwoC)
  have hcoeff : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 := ⟨hc₁, hc₁lim.trans_le hc₂lim, hc₂⟩
  refine ⟨νStar, hcapν, hparameter, max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀ k
  let p := Parameters.of j₀ νStar
  have hjOld : J₀ ≤ j₀ := (le_max_left J₀ J₁).trans hj₀
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJ₀.trans_le hjOld
  have hsmall : p.scale (k / 2) < m / (2 * C) :=
    (ScaleTails.scale_antitone p hstart (Nat.zero_le (k / 2))).trans_lt
      (hscale νStar j₀ ((le_max_right J₀ J₁).trans hj₀))
  have hCt : C * p.scale (k / 2) < m / 2 := by
    nlinarith [(lt_div_iff₀ htwoC).mp hsmall]
  have hactualStep := huniform j₀ hjOld (k / 2) (RadiusExpansions.phaseIndex k)
  rw [RadiusExpansions.phaseIndex_identity] at hactualStep
  have hlimit := hmargin (RadiusExpansions.phaseIndex k)
  have hA : c₁ ≤ armijoRatio p k := by
    have herror := (abs_le.mp hactualStep.2.1).1
    linarith [hlimit.1]
  have hCurvature : curvatureRatio p k ≤ 2 / 3 := by
    have herror := (abs_le.mp hactualStep.2.2).2
    linarith [hlimit.2]
  exact modelStrongWolfe_of_ratios p k c₁ c₂ hcoeff hc₂lim hactualStep.1 hA hCurvature

/-- Helper for thm:main and eq:polar-wolfe-ratios: any function with the certified
model endpoint values and original prescribed endpoint gradients inherits the
standard strong-Wolfe conditions for the original physical chord. -/
theorem strongWolfe_of_endpointData (p : Parameters) (k : ℕ)
    (coeff : LineSearch.Wolfe.Coefficients) (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hmodel : ModelStrongWolfe p k coeff.c₁ coeff.c₂)
    (hvalue : f (p.point k) = modelValue p k)
    (hvalueNext : f (p.point (k + 1)) = modelValue p (k + 1))
    (hgradient : HasGradientAt f (p.gradient k) (p.point k))
    (hgradientNext : HasGradientAt f (p.gradient (k + 1)) (p.point (k + 1))) :
    LineSearch.Wolfe.IsStrong coeff f (p.point k) (p.point (k + 1) - p.point k) := by
  have hnext : p.point k + (p.point (k + 1) - p.point k) = p.point (k + 1) := by abel
  have hgradientAtNext : HasGradientAt f (p.gradient (k + 1))
      (p.point k + (p.point (k + 1) - p.point k)) := by
    simpa only [hnext] using hgradientNext
  have hArmijo : LineSearch.Wolfe.IsArmijo coeff.c₁ (f (p.point k))
      (f (p.point k + (p.point (k + 1) - p.point k)))
      (inner ℝ (p.gradient k) (p.point (k + 1) - p.point k)) := by
    rw [hnext, hvalue, hvalueNext, ← startSlope_def]
    exact hmodel.armijo
  have hCurvature : LineSearch.Wolfe.IsStrongCurvature coeff.c₂
      (inner ℝ (p.gradient k) (p.point (k + 1) - p.point k))
      (inner ℝ (p.gradient (k + 1)) (p.point (k + 1) - p.point k)) := by
    rw [← startSlope_def, ← endSlope_def]
    exact hmodel.curvature
  exact LineSearch.Wolfe.IsStrong.ofHasGradientAt hgradient hgradientAtNext hArmijo hCurvature

end DFP.Polar.WolfeRatios
