/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

public section

open scoped ContDiff Gradient NNReal

namespace EqualityConstrained

variable {n m : ℕ}

/-- The constraint-gradient operator, represented as the adjoint of the Fréchet derivative. -/
noncomputable abbrev constraintGradient
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.adjoint (fderiv ℝ c x)

/-- The constraint-gradient operator is the adjoint of the Fréchet derivative. -/
theorem constraintGradient_def
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    constraintGradient c x = ContinuousLinearMap.adjoint (fderiv ℝ c x) := rfl

/-- A nonempty open region and strictly positive uniform regularity bounds for a
smooth equality-constrained problem. -/
structure Regularity
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) where
  /-- The region on which the uniform estimates hold. -/
  region : Set (EuclideanSpace ℝ (Fin n))
  /-- A uniform lower bound for the objective. -/
  objectiveLower : ℝ
  /-- A uniform bound for the norm of the objective gradient. -/
  gradientBound : ℝ≥0
  /-- A Lipschitz constant for the objective gradient. -/
  gradientLipschitz : ℝ≥0
  /-- A uniform operator-norm bound for the constraint gradient. -/
  constraintGradientBound : ℝ≥0
  /-- A Lipschitz constant for the constraint gradient. -/
  constraintGradientLipschitz : ℝ≥0
  /-- A uniform positive lower modulus for the constraint gradient. -/
  licqModulus : NNRealˣ
  /-- The chosen region is nonempty. -/
  nonempty_region : region.Nonempty
  /-- The chosen region is open. -/
  isOpen_region : IsOpen region
  /-- The objective-gradient norm bound is strictly positive. -/
  gradientBound_pos : 0 < gradientBound
  /-- The objective-gradient Lipschitz bound is strictly positive. -/
  gradientLipschitz_pos : 0 < gradientLipschitz
  /-- The constraint-gradient norm bound is strictly positive. -/
  constraintGradientBound_pos : 0 < constraintGradientBound
  /-- The constraint-gradient Lipschitz bound is strictly positive. -/
  constraintGradientLipschitz_pos : 0 < constraintGradientLipschitz
  /-- The objective is differentiable throughout the chosen region. -/
  differentiableOn_objective : DifferentiableOn ℝ f region
  /-- The constraint map is differentiable throughout the chosen region. -/
  differentiableOn_constraint : DifferentiableOn ℝ c region
  /-- The objective is bounded below on the chosen region. -/
  objectiveLower_le (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) : objectiveLower ≤ f x
  /-- The objective gradient is uniformly bounded on the chosen region. -/
  norm_gradient_le (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) :
    ‖∇ f x‖ ≤ gradientBound
  /-- The objective gradient is Lipschitz on the chosen region. -/
  lipschitzOn_gradient : LipschitzOnWith gradientLipschitz (∇ f) region
  /-- The constraint gradient is uniformly bounded in operator norm on the chosen region. -/
  norm_constraintGradient_le (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) :
    ‖constraintGradient c x‖ ≤ constraintGradientBound
  /-- The constraint gradient is Lipschitz on the chosen region. -/
  lipschitzOn_constraintGradient :
    LipschitzOnWith constraintGradientLipschitz (constraintGradient c) region
  /-- The constraint gradient has the stated uniform lower norm bound. -/
  licqLowerBound (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region)
      (u : EuclideanSpace ℝ (Fin m)) :
    licqModulus * ‖u‖ ≤ ‖constraintGradient c x u‖

namespace Regularity

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- Construct a regularity certificate from explicit witnesses for all uniform bounds. -/
def ofBounds
    (region : Set (EuclideanSpace ℝ (Fin n))) (objectiveLower : ℝ)
    (gradientBound gradientLipschitz constraintGradientBound
      constraintGradientLipschitz : ℝ≥0) (licqModulus : NNRealˣ)
    (nonempty_region : region.Nonempty) (isOpen_region : IsOpen region)
    (gradientBound_pos : 0 < gradientBound)
    (gradientLipschitz_pos : 0 < gradientLipschitz)
    (constraintGradientBound_pos : 0 < constraintGradientBound)
    (constraintGradientLipschitz_pos : 0 < constraintGradientLipschitz)
    (differentiableOn_objective : DifferentiableOn ℝ f region)
    (differentiableOn_constraint : DifferentiableOn ℝ c region)
    (objectiveLower_le : ∀ x ∈ region, objectiveLower ≤ f x)
    (norm_gradient_le : ∀ x ∈ region, ‖∇ f x‖ ≤ gradientBound)
    (lipschitzOn_gradient : LipschitzOnWith gradientLipschitz (∇ f) region)
    (norm_constraintGradient_le :
      ∀ x ∈ region, ‖constraintGradient c x‖ ≤ constraintGradientBound)
    (lipschitzOn_constraintGradient :
      LipschitzOnWith constraintGradientLipschitz (constraintGradient c) region)
    (licqLowerBound : ∀ x ∈ region, ∀ u : EuclideanSpace ℝ (Fin m),
      licqModulus * ‖u‖ ≤ ‖constraintGradient c x u‖) :
    Regularity f c :=
  { region
    objectiveLower
    gradientBound
    gradientLipschitz
    constraintGradientBound
    constraintGradientLipschitz
    licqModulus
    nonempty_region
    isOpen_region
    gradientBound_pos
    gradientLipschitz_pos
    constraintGradientBound_pos
    constraintGradientLipschitz_pos
    differentiableOn_objective
    differentiableOn_constraint
    objectiveLower_le
    norm_gradient_le
    lipschitzOn_gradient
    norm_constraintGradient_le
    lipschitzOn_constraintGradient
    licqLowerBound }

/-- The structured LICQ modulus is strictly positive. -/
theorem licqModulus_pos (h : Regularity f c) : 0 < h.licqModulus.val :=
  pos_iff_ne_zero.2 h.licqModulus.ne_zero

/-- A regularity certificate exposes the nonempty open region, local differentiability,
strictly positive constants, and uniform estimates of Assumption 2.1. -/
theorem spec (h : Regularity f c) :
    h.region.Nonempty ∧ IsOpen h.region ∧
      (DifferentiableOn ℝ f h.region ∧ DifferentiableOn ℝ c h.region) ∧
      ((0 : ℝ) < h.gradientBound ∧ (0 : ℝ) < h.gradientLipschitz ∧
        (0 : ℝ) < h.constraintGradientBound ∧
        (0 : ℝ) < h.constraintGradientLipschitz ∧
        0 < h.licqModulus.val) ∧
      ((∀ x ∈ h.region, h.objectiveLower ≤ f x) ∧
        (∀ x ∈ h.region, ‖∇ f x‖ ≤ h.gradientBound) ∧
        LipschitzOnWith h.gradientLipschitz (∇ f) h.region ∧
        (∀ x ∈ h.region, ‖constraintGradient c x‖ ≤ h.constraintGradientBound) ∧
        LipschitzOnWith h.constraintGradientLipschitz (constraintGradient c) h.region ∧
        ∀ x ∈ h.region, ∀ u : EuclideanSpace ℝ (Fin m),
          h.licqModulus * ‖u‖ ≤ ‖constraintGradient c x u‖) :=
  ⟨h.nonempty_region, h.isOpen_region,
    ⟨h.differentiableOn_objective, h.differentiableOn_constraint⟩,
    ⟨NNReal.coe_pos.2 h.gradientBound_pos,
      NNReal.coe_pos.2 h.gradientLipschitz_pos,
      NNReal.coe_pos.2 h.constraintGradientBound_pos,
      NNReal.coe_pos.2 h.constraintGradientLipschitz_pos,
      h.licqModulus_pos⟩,
    ⟨h.objectiveLower_le, h.norm_gradient_le, h.lipschitzOn_gradient,
      h.norm_constraintGradient_le, h.lipschitzOn_constraintGradient, h.licqLowerBound⟩⟩

/-- Every point of the open regularity region is a differentiability point of the objective. -/
theorem differentiableAt_objective (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) :
    DifferentiableAt ℝ f x :=
  (h.differentiableOn_objective x hx).differentiableAt (h.isOpen_region.mem_nhds hx)

/-- Every point of the open regularity region is a differentiability point of the constraint map. -/
theorem differentiableAt_constraint (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) :
    DifferentiableAt ℝ c x :=
  (h.differentiableOn_constraint x hx).differentiableAt (h.isOpen_region.mem_nhds hx)

/-- On the regularity region, `fderiv ℝ f x` is the derivative of the objective at `x`. -/
theorem hasFDerivAt_objective (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) :
    HasFDerivAt f (fderiv ℝ f x) x :=
  (h.differentiableAt_objective hx).hasFDerivAt

/-- On the regularity region, `fderiv ℝ c x` is the derivative of the constraint map at `x`. -/
theorem hasFDerivAt_constraint (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) :
    HasFDerivAt c (fderiv ℝ c x) x :=
  (h.differentiableAt_constraint hx).hasFDerivAt

/-- The objective is continuous on the regularity region. -/
theorem continuousOn_objective (h : Regularity f c) : ContinuousOn f h.region :=
  h.differentiableOn_objective.continuousOn

/-- The constraint map is continuous on the regularity region. -/
theorem continuousOn_constraint (h : Regularity f c) : ContinuousOn c h.region :=
  h.differentiableOn_constraint.continuousOn

/-- The objective is continuous at every point of the open regularity region. -/
theorem continuousAt_objective (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) : ContinuousAt f x :=
  (h.differentiableAt_objective hx).continuousAt

/-- The constraint map is continuous at every point of the open regularity region. -/
theorem continuousAt_constraint (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) : ContinuousAt c x :=
  (h.differentiableAt_constraint hx).continuousAt

/-- The objective gradient is continuous on the regularity region. -/
theorem continuousOn_gradient (h : Regularity f c) : ContinuousOn (∇ f) h.region :=
  h.lipschitzOn_gradient.continuousOn

/-- The constraint-gradient operator is continuous on the regularity region. -/
theorem continuousOn_constraintGradient (h : Regularity f c) :
    ContinuousOn (constraintGradient c) h.region :=
  h.lipschitzOn_constraintGradient.continuousOn

/-- The objective gradient is continuous at every point of the open regularity region. -/
theorem continuousAt_gradient (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) : ContinuousAt (∇ f) x :=
  h.continuousOn_gradient.continuousAt (h.isOpen_region.mem_nhds hx)

/-- The constraint-gradient operator is continuous at every point of the open regularity region. -/
theorem continuousAt_constraintGradient (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) :
    ContinuousAt (constraintGradient c) x :=
  h.continuousOn_constraintGradient.continuousAt (h.isOpen_region.mem_nhds hx)

/-- The objective derivative is Lipschitz on the regularity region. -/
theorem lipschitzOn_objectiveFDeriv (h : Regularity f c) :
    LipschitzOnWith h.gradientLipschitz (fderiv ℝ f) h.region := by
  intro x hx y hy
  simpa only [← toDual_gradient, LinearIsometryEquiv.edist_map] using
    h.lipschitzOn_gradient hx hy

/-- The constraint derivative is Lipschitz on the regularity region. -/
theorem lipschitzOn_constraintFDeriv (h : Regularity f c) :
    LipschitzOnWith h.constraintGradientLipschitz (fderiv ℝ c) h.region := by
  intro x hx y hy
  simpa only [constraintGradient_def, LinearIsometryEquiv.edist_map] using
    h.lipschitzOn_constraintGradient hx hy

/-- The objective derivative is continuous on the regularity region. -/
theorem continuousOn_objectiveFDeriv (h : Regularity f c) :
    ContinuousOn (fderiv ℝ f) h.region :=
  h.lipschitzOn_objectiveFDeriv.continuousOn

/-- The constraint derivative is continuous on the regularity region. -/
theorem continuousOn_constraintFDeriv (h : Regularity f c) :
    ContinuousOn (fderiv ℝ c) h.region :=
  h.lipschitzOn_constraintFDeriv.continuousOn

/-- The objective gradient extended by zero outside the regularity region. -/
noncomputable def objectiveGradientExtension (h : Regularity f c) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  @Set.piecewise _ _ h.region (gradient f) (fun _ ↦ 0)
    (fun x ↦ Classical.propDecidable (x ∈ h.region))

/-- The objective-gradient extension agrees with the true gradient in the regularity region. -/
theorem objectiveGradientExtension_eq (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) :
    h.objectiveGradientExtension x = gradient f x := by
  classical
  simp only [objectiveGradientExtension, Set.piecewise, if_pos hx]

/-- The zero extension of the objective gradient is globally measurable. -/
theorem measurable_objectiveGradientExtension (h : Regularity f c) :
    Measurable h.objectiveGradientExtension := by
  classical
  simpa only [objectiveGradientExtension] using
    h.continuousOn_gradient.measurable_piecewise
      continuous_const.continuousOn h.isOpen_region.measurableSet

/-- The constraint map extended by zero outside the regularity region. -/
noncomputable def constraintExtension (h : Regularity f c) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) :=
  @Set.piecewise _ _ h.region c (fun _ ↦ 0)
    (fun x ↦ Classical.propDecidable (x ∈ h.region))

/-- The constraint extension agrees with the true constraint in the regularity region. -/
theorem constraintExtension_eq (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) :
    h.constraintExtension x = c x := by
  classical
  simp only [constraintExtension, Set.piecewise, if_pos hx]

/-- The zero extension of the constraint map is globally measurable. -/
theorem measurable_constraintExtension (h : Regularity f c) :
    Measurable h.constraintExtension := by
  classical
  simpa only [constraintExtension] using
    h.continuousOn_constraint.measurable_piecewise
      continuous_const.continuousOn h.isOpen_region.measurableSet

/-- The constraint derivative extended by zero outside the regularity region. -/
noncomputable def constraintFDerivExtension (h : Regularity f c) :
    EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
  @Set.piecewise _ _ h.region (fderiv ℝ c) (fun _ ↦ 0)
    (fun x ↦ Classical.propDecidable (x ∈ h.region))

/-- The constraint-derivative extension agrees with `fderiv ℝ c` in the regularity region. -/
theorem constraintFDerivExtension_eq (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) :
    h.constraintFDerivExtension x = fderiv ℝ c x := by
  classical
  simp only [constraintFDerivExtension, Set.piecewise, if_pos hx]

/-- The zero extension of the constraint derivative is globally measurable. -/
theorem measurable_constraintFDerivExtension (h : Regularity f c) :
    Measurable h.constraintFDerivExtension := by
  classical
  simpa only [constraintFDerivExtension] using
    h.continuousOn_constraintFDeriv.measurable_piecewise
      continuous_const.continuousOn h.isOpen_region.measurableSet

/-- The constraint-gradient operator extended by zero outside the regularity region. -/
noncomputable def constraintGradientExtension (h : Regularity f c) :
    EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  @Set.piecewise _ _ h.region (constraintGradient c) (fun _ ↦ 0)
    (fun x ↦ Classical.propDecidable (x ∈ h.region))

/-- The constraint-gradient extension agrees with the true operator in the regularity region. -/
theorem constraintGradientExtension_eq (h : Regularity f c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.region) :
    h.constraintGradientExtension x = constraintGradient c x := by
  classical
  simp only [constraintGradientExtension, Set.piecewise, if_pos hx]

/-- The zero extension of the constraint-gradient operator is globally measurable. -/
theorem measurable_constraintGradientExtension (h : Regularity f c) :
    Measurable h.constraintGradientExtension := by
  classical
  simpa only [constraintGradientExtension] using
    h.continuousOn_constraintGradient.measurable_piecewise
      continuous_const.continuousOn h.isOpen_region.measurableSet

/-- The uniform lower norm bound gives the canonical antilipschitz estimate. -/
theorem constraintGradientAntilipschitz
    (h : Regularity f c) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ h.region) :
    AntilipschitzWith h.licqModulus⁻¹ (constraintGradient c x) := by
  refine (constraintGradient c x).antilipschitz_of_bound fun u ↦ ?_
  rw [NNReal.coe_inv]
  have hInverseNonnegative : 0 ≤ (h.licqModulus : ℝ)⁻¹ := by
    positivity
  calc
    ‖u‖ = (h.licqModulus : ℝ)⁻¹ * ((h.licqModulus : ℝ) * ‖u‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ (NNReal.coe_pos.2 h.licqModulus_pos).ne', one_mul]
    _ ≤ (h.licqModulus : ℝ)⁻¹ * ‖constraintGradient c x u‖ :=
      mul_le_mul_of_nonneg_left (h.licqLowerBound x hx u) hInverseNonnegative

/-- The uniform LICQ bound makes every constraint-gradient operator injective. -/
theorem constraintGradientInjective
    (h : Regularity f c) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ h.region) :
    Function.Injective (constraintGradient c x) :=
  (constraintGradientAntilipschitz h x hx).injective

end Regularity

end EqualityConstrained

end
