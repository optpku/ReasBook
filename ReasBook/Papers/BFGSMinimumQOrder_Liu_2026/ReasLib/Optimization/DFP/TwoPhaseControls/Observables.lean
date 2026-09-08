module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
public import ReasLib.Geometry.Euclidean.Plane.SignedAngle

public section

noncomputable section

open scoped EuclideanSpace Matrix

namespace DFP.TwoLeg

/-- The normalized observables attached to one exact planar two-leg DFP cycle. -/
structure CompleteTwoLegObservables where
  amplitudeRatio : ℝ
  frameAngleIncrement : ℝ
  halfCenterDisplacement : EuclideanSpace ℝ (Fin 2)
  fullCenterDisplacement : EuclideanSpace ℝ (Fin 2)
  firstEndpointAngleIncrement : Real.Angle
  secondEndpointAngleIncrement : Real.Angle
  firstStepNorm : ℝ
  secondStepNorm : ℝ
  initialGradientNorm : ℝ
  intermediateGradientNorm : ℝ
  finalGradientNorm : ℝ

/-- Evaluate the complete normalized observable family from the signed two-leg state
`(ε, p, h)`. The frame increment uses `EuclideanPlane.SignedAngle.coordinate`, the
identity-centered local coordinate, while endpoint increments remain quotient-valued
`Real.Angle`s. -/
def observableMap : (ℝ × ℝ × ℝ) → CompleteTwoLegObservables := fun x ↦
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let g₀Raw : Fin 2 → ℝ := ![(1 : ℝ), p * ε ^ 2]
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * ε ^ 4, h]
  let Hg₀ := H₀ *ᵥ g₀Raw
  let A₀ := (TwoPhaseControls.first ε).matrix
  let alpha₀ := (TwoPhaseControls.first ε).tau * (g₀Raw ⬝ᵥ Hg₀) /
    (Hg₀ ⬝ᵥ (A₀ *ᵥ Hg₀))
  let s₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (-(alpha₀ • Hg₀))
  let F₁ := DFP.FirstLeg.frame ε p h
  let spectral₁ := DFP.FirstLeg.spectralFactors ε p h
  let gradient₁ := DFP.FirstLeg.gradientFactors ε p h
  let H₁ : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal ![ε ^ 4 * spectral₁.1, spectral₁.2]
  let g₁Raw : Fin 2 → ℝ := ![gradient₁.1, ε ^ 2 * gradient₁.2]
  let Hg₁ := H₁ *ᵥ g₁Raw
  let A₁ := (TwoPhaseControls.second ε).matrix
  let alpha₁ := (TwoPhaseControls.second ε).tau * (g₁Raw ⬝ᵥ Hg₁) /
    (Hg₁ ⬝ᵥ (A₁ *ᵥ Hg₁))
  let s₁Raw : Fin 2 → ℝ := -(alpha₁ • Hg₁)
  let s₁ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (F₁ *ᵥ s₁Raw)
  let g₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 g₀Raw
  let g₁ : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (DFP.FirstLeg.outputGradient ε p h)
  let g₂ : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (F₁ *ᵥ DFP.SecondLeg.outputGradient ε p h)
  { amplitudeRatio := (DFP.SecondLeg.coordinates ε p h).1
    frameAngleIncrement := EuclideanPlane.SignedAngle.coordinate
      (F₁ * DFP.SecondLeg.frame ε p h)
    halfCenterDisplacement := s₀ - (g₁ - g₀)
    fullCenterDisplacement := s₀ + s₁ - (g₂ - g₀)
    firstEndpointAngleIncrement := EuclideanPlane.orientation.oangle g₀ g₁
    secondEndpointAngleIncrement := EuclideanPlane.orientation.oangle g₁ g₂
    firstStepNorm := ‖s₀‖
    secondStepNorm := ‖s₁‖
    initialGradientNorm := ‖g₀‖
    intermediateGradientNorm := ‖g₁‖
    finalGradientNorm := ‖g₂‖ }

/-- The observable amplitude ratio is the low final gradient coordinate. -/
theorem observableMap_amplitudeRatio (ε p h : ℝ) :
    (observableMap (ε, p, h)).amplitudeRatio =
      (DFP.SecondLeg.coordinates ε p h).1 := by
  rfl

/-- The observable frame increment is the local signed coordinate of the relative
two-leg frame product. -/
theorem observableMap_frameAngleIncrement (ε p h : ℝ) :
    (observableMap (ε, p, h)).frameAngleIncrement =
      EuclideanPlane.SignedAngle.coordinate
        (DFP.FirstLeg.frame ε p h * DFP.SecondLeg.frame ε p h) := by
  rfl

/-- The two center-displacement projections are the normalized half- and full-cycle
changes of `x - g` in the incoming oriented frame. -/
theorem observableMap_centerDisplacements (ε p h : ℝ) :
    let g₀Raw : Fin 2 → ℝ := ![(1 : ℝ), p * ε ^ 2]
    let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * ε ^ 4, h]
    let Hg₀ := H₀ *ᵥ g₀Raw
    let A₀ := (TwoPhaseControls.first ε).matrix
    let alpha₀ := (TwoPhaseControls.first ε).tau * (g₀Raw ⬝ᵥ Hg₀) /
      (Hg₀ ⬝ᵥ (A₀ *ᵥ Hg₀))
    let s₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (-(alpha₀ • Hg₀))
    let F₁ := DFP.FirstLeg.frame ε p h
    let spectral₁ := DFP.FirstLeg.spectralFactors ε p h
    let gradient₁ := DFP.FirstLeg.gradientFactors ε p h
    let H₁ : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal ![ε ^ 4 * spectral₁.1, spectral₁.2]
    let g₁Raw : Fin 2 → ℝ := ![gradient₁.1, ε ^ 2 * gradient₁.2]
    let Hg₁ := H₁ *ᵥ g₁Raw
    let A₁ := (TwoPhaseControls.second ε).matrix
    let alpha₁ := (TwoPhaseControls.second ε).tau * (g₁Raw ⬝ᵥ Hg₁) /
      (Hg₁ ⬝ᵥ (A₁ *ᵥ Hg₁))
    let s₁Raw : Fin 2 → ℝ := -(alpha₁ • Hg₁)
    let s₁ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (F₁ *ᵥ s₁Raw)
    let g₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 g₀Raw
    let g₁ : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (DFP.FirstLeg.outputGradient ε p h)
    let g₂ : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (F₁ *ᵥ DFP.SecondLeg.outputGradient ε p h)
    ((observableMap (ε, p, h)).halfCenterDisplacement,
        (observableMap (ε, p, h)).fullCenterDisplacement) =
      (s₀ - (g₁ - g₀), s₀ + s₁ - (g₂ - g₀)) := by
  rfl

/-- The endpoint-direction projections are canonical oriented angles, with no chosen
real representatives. -/
theorem observableMap_endpointAngleIncrements (ε p h : ℝ) :
    let F₁ := DFP.FirstLeg.frame ε p h
    let g₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(1 : ℝ), p * ε ^ 2]
    let g₁ : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (DFP.FirstLeg.outputGradient ε p h)
    let g₂ : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (F₁ *ᵥ DFP.SecondLeg.outputGradient ε p h)
    ((observableMap (ε, p, h)).firstEndpointAngleIncrement,
        (observableMap (ε, p, h)).secondEndpointAngleIncrement) =
      (EuclideanPlane.orientation.oangle g₀ g₁,
        EuclideanPlane.orientation.oangle g₁ g₂) := by
  rfl

/-- The step-norm projections are the norms of the two exact normalized displacements. -/
theorem observableMap_stepNorms (ε p h : ℝ) :
    let g₀Raw : Fin 2 → ℝ := ![(1 : ℝ), p * ε ^ 2]
    let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * ε ^ 4, h]
    let Hg₀ := H₀ *ᵥ g₀Raw
    let A₀ := (TwoPhaseControls.first ε).matrix
    let alpha₀ := (TwoPhaseControls.first ε).tau * (g₀Raw ⬝ᵥ Hg₀) /
      (Hg₀ ⬝ᵥ (A₀ *ᵥ Hg₀))
    let s₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (-(alpha₀ • Hg₀))
    let F₁ := DFP.FirstLeg.frame ε p h
    let spectral₁ := DFP.FirstLeg.spectralFactors ε p h
    let gradient₁ := DFP.FirstLeg.gradientFactors ε p h
    let H₁ : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal ![ε ^ 4 * spectral₁.1, spectral₁.2]
    let g₁Raw : Fin 2 → ℝ := ![gradient₁.1, ε ^ 2 * gradient₁.2]
    let Hg₁ := H₁ *ᵥ g₁Raw
    let A₁ := (TwoPhaseControls.second ε).matrix
    let alpha₁ := (TwoPhaseControls.second ε).tau * (g₁Raw ⬝ᵥ Hg₁) /
      (Hg₁ ⬝ᵥ (A₁ *ᵥ Hg₁))
    let s₁Raw : Fin 2 → ℝ := -(alpha₁ • Hg₁)
    let s₁ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (F₁ *ᵥ s₁Raw)
    ((observableMap (ε, p, h)).firstStepNorm,
        (observableMap (ε, p, h)).secondStepNorm) = (‖s₀‖, ‖s₁‖) := by
  rfl

/-- The gradient-norm projections are the norms at the initial, intermediate, and
final normalized cycle endpoints. -/
theorem observableMap_gradientNorms (ε p h : ℝ) :
    let F₁ := DFP.FirstLeg.frame ε p h
    let g₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(1 : ℝ), p * ε ^ 2]
    let g₁ : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (DFP.FirstLeg.outputGradient ε p h)
    let g₂ : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (F₁ *ᵥ DFP.SecondLeg.outputGradient ε p h)
    ((observableMap (ε, p, h)).initialGradientNorm,
        (observableMap (ε, p, h)).intermediateGradientNorm,
        (observableMap (ε, p, h)).finalGradientNorm) =
      (‖g₀‖, ‖g₁‖, ‖g₂‖) := by
  rfl

end DFP.TwoLeg
