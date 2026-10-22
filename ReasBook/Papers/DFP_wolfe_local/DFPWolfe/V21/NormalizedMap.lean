/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.Normalized.Recurrence
public import ReasLib.Optimization.DFP.Polar.Normalized.Regularity

open Filter
open scoped Matrix Topology

/- v21 Section 3.2: normalized map
The first check identifies the source map `Φ` with the canonical rescaled two-stage
map; the remaining checks cover its canceled stages, exact coordinate transports,
and fixed-compact regularity interface.
-/
#check (DFP.Polar.Normalized.map :
  ℝ → ℝ → ℝ → (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ)

#check (DFP.Polar.Normalized.unitRoot : ℝ → ℝ)
#check (DFP.Polar.Normalized.unitRoot_def :
  ∀ t : ℝ, DFP.Polar.Normalized.unitRoot t =
    Real.exp (Real.log (1 + t ^ 3) / 3))
#check (DFP.Polar.Normalized.nextScale : ℝ → ℝ)
#check (DFP.Polar.Normalized.nextScale_def :
  ∀ t : ℝ, DFP.Polar.Normalized.nextScale t =
    t / DFP.Polar.Normalized.unitRoot t)
#check (DFP.Polar.Normalized.angleFactor : ℝ → ℝ)
#check (DFP.Polar.Normalized.angleFactor_def :
  ∀ t : ℝ, DFP.Polar.Normalized.angleFactor t =
    9 * DFP.Polar.baseAngle /
      (DFP.Polar.Normalized.unitRoot t ^ 2 +
        DFP.Polar.Normalized.unitRoot t + 1))
#check (DFP.Polar.Normalized.stageWeight : Fin 2 → ℝ)
#check (DFP.Polar.Normalized.stageWeight_zero :
  DFP.Polar.Normalized.stageWeight 0 = (2 : ℝ) / 3)
#check (DFP.Polar.Normalized.stageWeight_one :
  DFP.Polar.Normalized.stageWeight 1 = (1 : ℝ) / 3)
#check (DFP.Polar.Normalized.limitAngle : Fin 2 → ℝ)
#check (DFP.Polar.Normalized.limitAngle_zero :
  DFP.Polar.Normalized.limitAngle 0 = 2 * DFP.Polar.baseAngle)
#check (DFP.Polar.Normalized.limitAngle_one :
  DFP.Polar.Normalized.limitAngle 1 = DFP.Polar.baseAngle)
#check (DFP.Polar.Normalized.stageAngleFactor : Fin 2 → ℝ → ℝ)
#check (DFP.Polar.Normalized.stageAngleFactor_def :
  ∀ (i : Fin 2) (t : ℝ), DFP.Polar.Normalized.stageAngleFactor i t =
    DFP.Polar.Normalized.stageWeight i * DFP.Polar.Normalized.angleFactor t)
#check (DFP.Polar.Normalized.stageAngle : Fin 2 → ℝ → ℝ)
#check (DFP.Polar.Normalized.stageAngle_def :
  ∀ (i : Fin 2) (t : ℝ), DFP.Polar.Normalized.stageAngle i t =
    t ^ 2 * DFP.Polar.Normalized.stageAngleFactor i t)
#check (DFP.Polar.Normalized.sinFactor : Fin 2 → ℝ → ℝ)
#check (DFP.Polar.Normalized.sinFactor_def :
  ∀ (i : Fin 2) (t : ℝ), DFP.Polar.Normalized.sinFactor i t =
    DFP.Polar.Normalized.stageAngleFactor i t *
      Real.sinc (DFP.Polar.Normalized.stageAngle i t))
#check (DFP.Polar.Normalized.cotFactor : Fin 2 → ℝ → ℝ)
#check (DFP.Polar.Normalized.cotFactor_def :
  ∀ (i : Fin 2) (t : ℝ), DFP.Polar.Normalized.cotFactor i t =
    Real.cos (DFP.Polar.Normalized.stageAngle i t) /
      DFP.Polar.Normalized.sinFactor i t)
#check (DFP.Polar.Normalized.rescaleFactor : ℝ → ℝ)
#check (DFP.Polar.Normalized.rescaleFactor_def :
  ∀ t : ℝ, DFP.Polar.Normalized.rescaleFactor t =
    (DFP.Polar.Normalized.unitRoot t)⁻¹ ^ 2)

#check (DFP.Polar.Normalized.nextScale_eq_rpow :
  ∀ (t : ℝ), 0 < t → DFP.Polar.Normalized.nextScale t =
    t * (1 + t ^ 3) ^ (-(1 : ℝ) / 3))
#check (DFP.Polar.Normalized.stageAngle_eq_rpow :
  ∀ (i : Fin 2) (t : ℝ), 0 < t →
    DFP.Polar.Normalized.stageAngle i t =
      DFP.Polar.Normalized.stageWeight i *
        ((9 * DFP.Polar.baseAngle / t) *
          ((1 + t ^ 3) ^ ((1 : ℝ) / 3) - 1)))
#check (DFP.Polar.Normalized.nextScale_analyticAt :
  AnalyticAt ℝ DFP.Polar.Normalized.nextScale 0)
#check (DFP.Polar.Normalized.stageAngle_analyticAt :
  ∀ i : Fin 2, AnalyticAt ℝ (DFP.Polar.Normalized.stageAngle i) 0)
#check (DFP.Polar.Normalized.sinFactor_eq_sin_div :
  ∀ (i : Fin 2) (t : ℝ), 0 < t →
    DFP.Polar.Normalized.sinFactor i t =
      Real.sin (DFP.Polar.Normalized.stageAngle i t) / t ^ 2)
#check (DFP.Polar.Normalized.cotFactor_eq_mul_cot :
  ∀ (i : Fin 2) (t : ℝ), 0 < t →
    DFP.Polar.Normalized.cotFactor i t =
      t ^ 2 * Real.cot (DFP.Polar.Normalized.stageAngle i t))
#check (DFP.Polar.Normalized.rescaleFactor_eq_div_sq :
  ∀ (t : ℝ), 0 < t → DFP.Polar.Normalized.rescaleFactor t =
    (DFP.Polar.Normalized.nextScale t / t) ^ 2)
#check (DFP.Polar.Normalized.sinFactor_analyticAt :
  ∀ i : Fin 2, AnalyticAt ℝ (DFP.Polar.Normalized.sinFactor i) 0)
#check (DFP.Polar.Normalized.cotFactor_analyticAt :
  ∀ i : Fin 2, AnalyticAt ℝ (DFP.Polar.Normalized.cotFactor i) 0)
#check (DFP.Polar.Normalized.nextScale_expansion :
  (fun t : ℝ ↦ DFP.Polar.Normalized.nextScale t -
      (t - (1 / 3 : ℝ) * t ^ 4)) =O[𝓝 0] fun t : ℝ ↦ t ^ 7)
#check (DFP.Polar.Normalized.stageAngle_expansion :
  ∀ i : Fin 2,
    (fun t : ℝ ↦ DFP.Polar.Normalized.stageAngle i t -
      DFP.Polar.Normalized.limitAngle i * t ^ 2) =O[𝓝 0]
        fun t : ℝ ↦ t ^ 5)
#check (DFP.Polar.Normalized.rescaleFactor_analyticAt :
  AnalyticAt ℝ DFP.Polar.Normalized.rescaleFactor 0)
#check (DFP.Polar.Normalized.rescaleFactor_firstIteratedFDeriv_eq_zero :
  iteratedFDeriv ℝ 1 DFP.Polar.Normalized.rescaleFactor 0 = 0)
#check (DFP.Polar.Normalized.rescaleFactor_secondIteratedFDeriv_eq_zero :
  iteratedFDeriv ℝ 2 DFP.Polar.Normalized.rescaleFactor 0 = 0)

#check (DFP.Polar.Normalized.scaleMatrix :
  ℝ → Matrix (Fin 2) (Fin 2) ℝ)
#check (DFP.Polar.Normalized.scaleMatrix_def :
  ∀ t : ℝ, DFP.Polar.Normalized.scaleMatrix t = !![t ^ 2, 0; 0, 1])
#check (DFP.Polar.Normalized.invScaleMatrix :
  ℝ → Matrix (Fin 2) (Fin 2) ℝ)
#check (DFP.Polar.Normalized.invScaleMatrix_def :
  ∀ t : ℝ, DFP.Polar.Normalized.invScaleMatrix t = !![(t ^ 2)⁻¹, 0; 0, 1])
#check (DFP.Polar.Normalized.coordinates :
  ℝ → Matrix (Fin 2) (Fin 2) ℝ → ℝ × ℝ × ℝ)
#check (DFP.Polar.Normalized.coordinates_apply :
  ∀ (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ),
    DFP.Polar.Normalized.coordinates t Z =
      (t ^ 4 * Z 0 0, t ^ 2 * Z 0 1, Z 1 1))
#check (DFP.Polar.Normalized.slope : (ℝ × ℝ × ℝ) → ℝ)
#check (DFP.Polar.Normalized.slope_def :
  ∀ x : ℝ × ℝ × ℝ, DFP.Polar.Normalized.slope x = x.2.2 / x.2.1)
#check (DFP.Polar.Normalized.stepV : (ℝ × ℝ × ℝ) → Fin 2 → ℝ)
#check (DFP.Polar.Normalized.stepV_def :
  ∀ x : ℝ × ℝ × ℝ,
    DFP.Polar.Normalized.stepV x = ![-DFP.Polar.Normalized.slope x, 1])
#check (DFP.Polar.Normalized.stepW :
  Fin 2 → ℝ → (ℝ × ℝ × ℝ) → ℝ → ℝ → Fin 2 → ℝ)
#check (DFP.Polar.Normalized.stepW_def :
  ∀ (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ),
    DFP.Polar.Normalized.stepW i t x ζ ζNext =
      ![(ζNext - ζ) * DFP.Polar.Normalized.cotFactor i t -
          ζ * t ^ 4 * DFP.Polar.Normalized.slope x, ζNext])
#check (DFP.Polar.Normalized.rotation :
  Fin 2 → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
#check (DFP.Polar.Normalized.rotation_def :
  ∀ (i : Fin 2) (t : ℝ), DFP.Polar.Normalized.rotation i t =
    !![Real.cos (DFP.Polar.Normalized.stageAngle i t),
        t ^ 4 * DFP.Polar.Normalized.sinFactor i t;
      -DFP.Polar.Normalized.sinFactor i t,
        Real.cos (DFP.Polar.Normalized.stageAngle i t)])
#check (DFP.Polar.Normalized.stageSigma :
  Fin 2 → ℝ → (ℝ × ℝ × ℝ) → ℝ → ℝ → ℝ)
#check (DFP.Polar.Normalized.stageSigma_def :
  ∀ (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ),
    DFP.Polar.Normalized.stageSigma i t x ζ ζNext =
      DFP.Polar.Normalized.stepV x ⬝ᵥ
        DFP.Polar.Normalized.stepW i t x ζ ζNext)
#check (DFP.Polar.Normalized.stageMatrix :
  Fin 2 → ℝ → (ℝ × ℝ × ℝ) → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
#check (DFP.Polar.Normalized.stageMatrix_def :
  ∀ (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ),
    DFP.Polar.Normalized.stageMatrix i t x ζ ζNext =
      let X := RealSymmetric2.matrix x.1 x.2.1 x.2.2
      let v := DFP.Polar.Normalized.stepV x
      let w := DFP.Polar.Normalized.stepW i t x ζ ζNext
      let σ := DFP.Polar.Normalized.stageSigma i t x ζ ζNext
      let P := DFP.Polar.Normalized.rotation i t
      P *
        ((1 - σ⁻¹ • Matrix.vecMulVec w v) * X *
          (1 - σ⁻¹ • Matrix.vecMulVec v w) +
            σ⁻¹ • Matrix.vecMulVec w w) * P.transpose)
#check (DFP.Polar.Normalized.stageMatrix_isHermitian :
  ∀ (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ),
    (DFP.Polar.Normalized.stageMatrix i t x ζ ζNext).IsHermitian)
#check (DFP.Polar.Normalized.stage :
  Fin 2 → ℝ → (ℝ × ℝ × ℝ) → ℝ → ℝ → ℝ × ℝ × ℝ)
#check (DFP.Polar.Normalized.stage_apply :
  ∀ (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ ζNext : ℝ),
    DFP.Polar.Normalized.stage i t x ζ ζNext =
      let X := DFP.Polar.Normalized.stageMatrix i t x ζ ζNext
      (X 0 0, X 0 1, X 1 1))
#check (DFP.Polar.Normalized.feedback :
  ℝ → ℝ → ℝ → (ℝ × ℝ × ℝ) → ℝ)
#check (DFP.Polar.Normalized.feedback_def :
  ∀ (L κ t : ℝ) (x₀ : ℝ × ℝ × ℝ),
    DFP.Polar.Normalized.feedback L κ t x₀ =
      Real.exp (-L * (κ / x₀.1) ^ 2 * t ^ 3))
#check (DFP.Polar.Normalized.cycleStage :
  ℝ → ℝ → Fin 2 → ℝ → (ℝ × ℝ × ℝ) →
    (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ)
#check (DFP.Polar.Normalized.cycleStage_apply :
  ∀ (L κ : ℝ) (i : Fin 2) (t : ℝ) (x₀ x : ℝ × ℝ × ℝ),
    DFP.Polar.Normalized.cycleStage L κ i t x₀ x =
      let ζOdd := DFP.Polar.Normalized.feedback L κ t x₀
      DFP.Polar.Normalized.stage i t x (![1, ζOdd] i) (![ζOdd, 1] i))
#check (DFP.Polar.Normalized.twoStep :
  ℝ → ℝ → ℝ → (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ)
#check (DFP.Polar.Normalized.twoStep_def :
  ∀ (L κ t : ℝ) (x : ℝ × ℝ × ℝ),
    DFP.Polar.Normalized.twoStep L κ t x =
      DFP.Polar.Normalized.cycleStage L κ 1 t x
        (DFP.Polar.Normalized.cycleStage L κ 0 t x x))
#check (DFP.Polar.Normalized.rescale :
  ℝ → (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ)
#check (DFP.Polar.Normalized.rescale_apply :
  ∀ (t : ℝ) (x : ℝ × ℝ × ℝ), DFP.Polar.Normalized.rescale t x =
    (DFP.Polar.Normalized.rescaleFactor t ^ 2 * x.1,
      DFP.Polar.Normalized.rescaleFactor t * x.2.1, x.2.2))
#check (DFP.Polar.Normalized.map_def :
  ∀ (L κ t : ℝ) (x : ℝ × ℝ × ℝ),
    DFP.Polar.Normalized.map L κ t x =
      DFP.Polar.Normalized.rescale t (DFP.Polar.Normalized.twoStep L κ t x))
#check (DFP.Polar.Normalized.leadingStage :
  ℝ → (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ)
#check (DFP.Polar.Normalized.leadingStage_apply :
  ∀ (c : ℝ) (x : ℝ × ℝ × ℝ), DFP.Polar.Normalized.leadingStage c x =
    (x.1, x.1 * (x.2.2 / x.2.1 - c),
      1 + x.1 * (x.2.2 / x.2.1 - c) ^ 2))

#check (DFP.Polar.matrixStep_isHermitian :
  ∀ (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ ζ ζNext : ℝ), Z.IsHermitian →
    (DFP.Polar.matrixStep Z δ ζ ζNext).IsHermitian)
#check (DFP.Polar.Parameters.evenMatrix_isHermitian :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ), (p.evenMatrix j).IsHermitian)
#check (DFP.Polar.Normalized.coordinates_eq_scaleMatrix_mul :
  ∀ (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ), Z.IsHermitian →
    RealSymmetric2.matrix (DFP.Polar.Normalized.coordinates t Z).1
        (DFP.Polar.Normalized.coordinates t Z).2.1
        (DFP.Polar.Normalized.coordinates t Z).2.2 =
      DFP.Polar.Normalized.scaleMatrix t * Z *
        DFP.Polar.Normalized.scaleMatrix t)
#check (DFP.Polar.Normalized.stepV_eq_invScaleMatrix_mulVec :
  ∀ (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ), 0 < t →
    DFP.Polar.Normalized.stepV (DFP.Polar.Normalized.coordinates t Z) =
      DFP.Polar.Normalized.invScaleMatrix t *ᵥ DFP.Polar.stepVOf Z)
#check (DFP.Polar.Normalized.stepW_eq_scaleMatrix_mulVec :
  ∀ (i : Fin 2) (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) (ζ ζNext : ℝ),
    0 < t →
      DFP.Polar.Normalized.stepW i t (DFP.Polar.Normalized.coordinates t Z)
          ζ ζNext =
        DFP.Polar.Normalized.scaleMatrix t *ᵥ
          DFP.Polar.stepWOf Z (DFP.Polar.Normalized.stageAngle i t) ζ ζNext)
#check (DFP.Polar.Normalized.rotation_eq_scaleMatrix_mul :
  ∀ (i : Fin 2) (t : ℝ), 0 < t → DFP.Polar.Normalized.rotation i t =
    DFP.Polar.Normalized.scaleMatrix t *
      (DFP.Polar.rotationMatrix (DFP.Polar.Normalized.stageAngle i t)).transpose *
        DFP.Polar.Normalized.invScaleMatrix t)
#check (DFP.Polar.Normalized.stageMatrix_eq_scaleMatrix_mul :
  ∀ (i : Fin 2) (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) (ζ ζNext : ℝ),
    Z.IsHermitian → 0 < t →
      DFP.Polar.Normalized.stageMatrix i t
          (DFP.Polar.Normalized.coordinates t Z) ζ ζNext =
        DFP.Polar.Normalized.scaleMatrix t *
          DFP.Polar.matrixStep Z (DFP.Polar.Normalized.stageAngle i t) ζ ζNext *
            DFP.Polar.Normalized.scaleMatrix t)
#check (DFP.Polar.Normalized.cycleStage_zero :
  ∀ (L κ : ℝ) (i : Fin 2) (x₀ x : ℝ × ℝ × ℝ),
    DFP.Polar.Normalized.cycleStage L κ i 0 x₀ x =
      DFP.Polar.Normalized.leadingStage (DFP.Polar.Normalized.limitAngle i) x)

#check (DFP.Polar.Normalized.denominators :
  ℝ → ℝ → ℝ → (ℝ × ℝ × ℝ) → Fin 9 → ℝ)
#check (DFP.Polar.Normalized.denominators_apply :
  ∀ (L κ t : ℝ) (x : ℝ × ℝ × ℝ),
    DFP.Polar.Normalized.denominators L κ t x =
      let ζOdd := DFP.Polar.Normalized.feedback L κ t x
      let x₁ := DFP.Polar.Normalized.cycleStage L κ 0 t x x
      ![DFP.Polar.Normalized.unitRoot t,
        DFP.Polar.Normalized.unitRoot t ^ 2 + DFP.Polar.Normalized.unitRoot t + 1,
        DFP.Polar.Normalized.sinFactor 0 t, DFP.Polar.Normalized.sinFactor 1 t,
        x.1, x.2.1, DFP.Polar.Normalized.stageSigma 0 t x 1 ζOdd, x₁.2.1,
        DFP.Polar.Normalized.stageSigma 1 t x₁ ζOdd 1])
#check (DFP.Polar.Normalized.denominators_uniformOn :
  ∀ (L κ : ℝ) (𝒦 : Set (ℝ × ℝ × ℝ)), IsCompact 𝒦 →
    (∀ x ∈ 𝒦, 0 < x.1) → (∀ x ∈ 𝒦, 0 < x.2.1) →
    (∀ x ∈ 𝒦,
      0 < (DFP.Polar.Normalized.leadingStage
        (DFP.Polar.Normalized.limitAngle 0) x).2.1) →
    ∃ ε > 0, ∃ d > 0, ∀ t ∈ Set.Icc (-ε) ε,
      ∀ x ∈ 𝒦, ∀ i : Fin 9,
        d ≤ |DFP.Polar.Normalized.denominators L κ t x i|)
#check (DFP.Polar.Normalized.map_analyticAt_zero :
  ∀ (L κ : ℝ) (x : ℝ × ℝ × ℝ), 0 < x.1 → 0 < x.2.1 →
    0 < (DFP.Polar.Normalized.leadingStage
      (DFP.Polar.Normalized.limitAngle 0) x).2.1 →
    AnalyticAt ℝ (Function.uncurry (DFP.Polar.Normalized.map L κ)) (0, x))
#check (DFP.Polar.Normalized.map_uniformJets :
  ∀ (L κ : ℝ) (m : ℕ) (𝒦 : Set (ℝ × ℝ × ℝ)), IsCompact 𝒦 →
    (∀ x ∈ 𝒦, 0 < x.1) → (∀ x ∈ 𝒦, 0 < x.2.1) →
    (∀ x ∈ 𝒦,
      0 < (DFP.Polar.Normalized.leadingStage
        (DFP.Polar.Normalized.limitAngle 0) x).2.1) →
    FiniteTaylorJet.IsUniformOn
      (fun x : ℝ × ℝ × ℝ ↦ fun t : ℝ ↦ DFP.Polar.Normalized.map L κ t x)
      (fun x ↦ FiniteTaylorJet.ofFunction ℝ m
        (fun t ↦ DFP.Polar.Normalized.map L κ t x) 0) 0 𝒦)
#check (DFP.Polar.Normalized.cycleStage_analyticAt_zero :
  ∀ (L κ : ℝ) (i : Fin 2) (x₀ x : ℝ × ℝ × ℝ),
    AnalyticAt ℝ (fun t ↦ DFP.Polar.Normalized.cycleStage L κ i t x₀ x) 0)
#check (DFP.Polar.Normalized.cycleStage_firstIteratedFDeriv_eq_zero :
  ∀ (L κ : ℝ) (i : Fin 2) (x₀ x : ℝ × ℝ × ℝ),
    iteratedFDeriv ℝ 1
      (fun t ↦ DFP.Polar.Normalized.cycleStage L κ i t x₀ x) 0 = 0)
#check (DFP.Polar.Normalized.cycleStage_secondIteratedFDeriv_eq_zero :
  ∀ (L κ : ℝ) (i : Fin 2) (x₀ x : ℝ × ℝ × ℝ),
    iteratedFDeriv ℝ 2
      (fun t ↦ DFP.Polar.Normalized.cycleStage L κ i t x₀ x) 0 = 0)

#check (DFP.Polar.Normalized.nextScale_scale :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ), 0 < p.startIndex →
    DFP.Polar.Normalized.nextScale (p.scale j) = p.scale (j + 1))
#check (DFP.Polar.Normalized.stageAngle_scale :
  ∀ (p : DFP.Polar.Parameters) (i : Fin 2) (j : ℕ), 0 < p.startIndex →
    DFP.Polar.Normalized.stageAngle i (p.scale j) =
      p.angleIncrement (2 * j + (i : ℕ)))
#check (DFP.Polar.Parameters.normalizedEvenState :
  DFP.Polar.Parameters → ℕ → ℝ × ℝ × ℝ)
#check (DFP.Polar.Parameters.normalizedEvenState_apply :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ), p.normalizedEvenState j =
    (p.scale j ^ 4 * p.evenMatrix j 0 0,
      p.scale j ^ 2 * p.evenMatrix j 0 1, p.evenMatrix j 1 1))
#check (DFP.Polar.Parameters.normalizedEvenState_matrix :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ),
    RealSymmetric2.matrix (p.normalizedEvenState j).1
        (p.normalizedEvenState j).2.1 (p.normalizedEvenState j).2.2 =
      DFP.Polar.Normalized.scaleMatrix (p.scale j) * p.evenMatrix j *
        DFP.Polar.Normalized.scaleMatrix (p.scale j))
#check (DFP.Polar.Parameters.normalizedEvenState_succ :
  ∀ (p : DFP.Polar.Parameters) (j : ℕ), 0 < p.startIndex →
    p.normalizedEvenState (j + 1) =
      DFP.Polar.Normalized.map p.feedbackRate p.kStar (p.scale j)
        (p.normalizedEvenState j))
