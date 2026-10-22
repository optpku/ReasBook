/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.Recurrence
public import ReasLib.Optimization.DFP.Polar.Realization

open scoped Matrix

/-
v21 Section 3.1: polar data
-/
#check (DFP.Polar.Parameters.scale_def :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ),
    p.scale j = ((p.startIndex + j : ℕ) : ℝ) ^ (-(1 : ℝ) / 3))
#check (DFP.Polar.Parameters.evenAngle_def :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ),
    p.evenAngle j =
      2 * Real.pi * ((p.startIndex + j : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
#check (DFP.Polar.Parameters.oddAngle_def :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ),
    p.oddAngle j = (p.evenAngle j + 2 * p.evenAngle (j + 1)) / 3)
#check (DFP.Polar.Parameters.angle_even :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ), p.angle (2 * j) = p.evenAngle j)
#check (DFP.Polar.Parameters.angle_odd :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ), p.angle (2 * j + 1) = p.oddAngle j)
#check (DFP.Polar.polarUnit_apply_zero :
  ∀ θ : ℝ, DFP.Polar.polarUnit θ 0 = Real.cos θ)
#check (DFP.Polar.polarUnit_apply_one :
  ∀ θ : ℝ, DFP.Polar.polarUnit θ 1 = Real.sin θ)
#check (DFP.Polar.rotationMatrix_def :
  ∀ θ : ℝ,
    DFP.Polar.rotationMatrix θ =
      !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ])
#check (DFP.Polar.baseAngle_def :
  DFP.Polar.baseAngle = 2 * Real.pi / 9)
#check (DFP.Polar.cycleZ_def :
  ∀ ν : ℝ,
    DFP.Polar.cycleZ ν =
      ν * (2 * DFP.Polar.baseAngle - ν) / (2 * ν - DFP.Polar.baseAngle))
#check (DFP.Polar.cycleW_def :
  ∀ ν : ℝ,
    DFP.Polar.cycleW ν =
      ν * (DFP.Polar.baseAngle + ν) / (2 * ν - DFP.Polar.baseAngle))
#check (DFP.Polar.cycleK_def :
  ∀ ν : ℝ,
    DFP.Polar.cycleK ν =
      (2 * ν - DFP.Polar.baseAngle) /
        (ν * (2 * DFP.Polar.baseAngle - ν) * (DFP.Polar.baseAngle + ν)))
#check (DFP.Polar.Parameters.initialMatrix_def :
  ∀ p : DFP.Polar.Parameters,
    p.initialMatrix =
      !![p.kStar / p.scale 0 ^ 4, p.kStar * p.wStar / p.scale 0 ^ 2;
        p.kStar * p.wStar / p.scale 0 ^ 2, 1 + p.kStar * p.wStar ^ 2])
#check (DFP.Polar.Parameters.amplitude_def :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ),
    p.amplitude j = p.amplitudeOf j (p.evenMatrix j))
#check (DFP.Polar.Parameters.oddMultiplierOf_def :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ) (Z : Matrix (Fin 2) (Fin 2) ℝ),
    p.oddMultiplierOf j Z =
      Real.exp
        (-p.feedbackRate * (p.kStar / p.amplitudeOf j Z) ^ 2 * p.scale j ^ 3))
#check (DFP.Polar.Parameters.zeta_even :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ), p.zeta (2 * j) = 1)
#check (DFP.Polar.Parameters.zeta_odd :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ),
    p.zeta (2 * j + 1) = p.oddMultiplierOf j (p.evenMatrix j))
#check (DFP.Polar.Parameters.omega_def :
  ∀ (p : DFP.Polar.Parameters) (k : ℕ),
    p.omega k = DFP.Polar.omegaOf (p.matrix k))
#check (DFP.Polar.Parameters.radiusRatio_def :
  ∀ (p : DFP.Polar.Parameters) (k : ℕ),
    p.radiusRatio k = DFP.Polar.radiusRatioOf (p.matrix k) (p.angleIncrement k))
#check (DFP.Polar.Parameters.stepV_def :
  ∀ (p : DFP.Polar.Parameters) (k : ℕ),
    p.stepV k = DFP.Polar.stepVOf (p.matrix k))
#check (DFP.Polar.Parameters.stepW_def :
  ∀ (p : DFP.Polar.Parameters) (k : ℕ),
    p.stepW k =
      DFP.Polar.stepWOf (p.matrix k) (p.angleIncrement k)
        (p.zeta k) (p.zeta (k + 1)))
#check (DFP.Polar.Parameters.sigma_def :
  ∀ (p : DFP.Polar.Parameters) (k : ℕ),
    p.sigma k =
      DFP.Polar.sigmaOf (p.matrix k) (p.angleIncrement k)
        (p.zeta k) (p.zeta (k + 1)))
#check (DFP.Polar.Parameters.nextEvenMatrix_def :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ) (Z : Matrix (Fin 2) (Fin 2) ℝ),
    p.nextEvenMatrix j Z =
      let ζOdd := p.oddMultiplierOf j Z
      let ZOdd := DFP.Polar.matrixStep Z (p.oddAngle j - p.evenAngle j) 1 ζOdd
      DFP.Polar.matrixStep ZOdd (p.evenAngle (j + 1) - p.oddAngle j) ζOdd 1)
#check (DFP.Polar.Parameters.matrix_succ :
  ∀ (p : DFP.Polar.Parameters) (k : ℕ),
    p.matrix (k + 1) =
      DFP.Polar.matrixStep (p.matrix k) (p.angleIncrement k)
        (p.zeta k) (p.zeta (k + 1)))
#check (DFP.Polar.Parameters.evenRadius_def :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ),
    p.evenRadius j =
      ∏' n : ℕ, p.radiusRatio (2 * (j + n)) * p.radiusRatio (2 * (j + n) + 1))
#check (DFP.Polar.Parameters.oddRadius_def :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ),
    p.oddRadius j = p.evenRadius j / p.radiusRatio (2 * j))
#check (DFP.Polar.Parameters.radius_even :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ), p.radius (2 * j) = p.evenRadius j)
#check (DFP.Polar.Parameters.radius_odd :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ), p.radius (2 * j + 1) = p.oddRadius j)
#check (DFP.Polar.Parameters.point_def :
  ∀ (p : DFP.Polar.Parameters) (k : ℕ),
    p.point k = p.radius k • DFP.Polar.polarUnit (p.angle k))
#check (DFP.Polar.Parameters.gradient_def :
  ∀ (p : DFP.Polar.Parameters) (k : ℕ), p.gradient k = p.zeta k • p.point k)
#check (DFP.Polar.Parameters.inverseHessian_def :
  ∀ (p : DFP.Polar.Parameters) (k : ℕ),
    p.inverseHessian k =
      DFP.Polar.rotationMatrix (p.angle k) * (p.matrix k)⁻¹ *
        (DFP.Polar.rotationMatrix (p.angle k)).transpose)
