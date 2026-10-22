/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Topology.MetricSpace.Thickening
public import TR_LALM_theory.Proposition_4_1.Parameters

public section

namespace LALM.Correction

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The corrected localization radius `χᶜᵒʳ * Δ`. -/
noncomputable def localizationRadius (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  displacementFactor h params.delta * params.delta

/-- The corrected localization radius is the displacement factor times the step radius. -/
theorem localizationRadius_def (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    localizationRadius h params = displacementFactor h params.delta * params.delta := by
  -- Expose the two factors stored by the localization-radius definition.
  rfl

/-- The corrected initial-potential bound `Φ̄₁ᶜᵒʳ`. -/
noncomputable def initialPotentialBound (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  f x₀ + h.gradientBound * displacementFactor h params.delta * params.delta +
    4 * params.multiplierBound ^ 2 / params.rho +
    (multiplierPrimalConstant h params.delta params.beta params.rho
      params.multiplierBound / params.rho) * params.delta ^ 2

/-- The corrected initial-potential bound has the displayed source formula. -/
theorem initialPotentialBound_def (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    initialPotentialBound h params =
      f x₀ + h.gradientBound * displacementFactor h params.delta * params.delta +
        4 * params.multiplierBound ^ 2 / params.rho +
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * params.delta ^ 2 := by
  -- Unfold the corrected initial-potential constant to its source formula.
  rfl

/-- The corrected deterministic objective threshold `Hdetᶜᵒʳ`. -/
noncomputable def deterministicObjectiveBound
    (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  initialPotentialBound h params + params.multiplierBound ^ 2 / (2 * params.rho)

/-- The corrected deterministic objective threshold has its displayed formula. -/
theorem deterministicObjectiveBound_def
    (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    deterministicObjectiveBound h params =
      initialPotentialBound h params + params.multiplierBound ^ 2 / (2 * params.rho) := by
  -- Expose the objective threshold as the initial potential plus its correction.
  rfl

/-- The corrected deterministic objective--feasibility localization set. -/
def deterministicSublevel (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | f x ≤ deterministicObjectiveBound h params ∧
    ‖c x‖ ≤ 2 * params.multiplierBound / params.rho}

/-- Membership in the corrected deterministic localization set is the
conjunction of its objective and feasibility bounds. -/
theorem mem_deterministicSublevel (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ deterministicSublevel h params ↔
      f x ≤ deterministicObjectiveBound h params ∧
        ‖c x‖ ≤ 2 * params.multiplierBound / params.rho := by
  rfl

/-- The corrected localization buffer around the corrected deterministic sublevel
lies in the regularity region. -/
def DeterministicRegionCondition (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : Prop :=
  Metric.cthickening (localizationRadius h params) (deterministicSublevel h params) ⊆
    h.region

/-- The corrected region condition exposes the exact closed localization buffer. -/
theorem deterministicRegionCondition_iff
    (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    DeterministicRegionCondition h params ↔
      Metric.cthickening (localizationRadius h params)
        (deterministicSublevel h params) ⊆ h.region := by
  -- Unfold the region condition to its closed-thickening containment.
  rfl

/-- The lower bound used by the corrected deterministic and stochastic Lyapunov analyses. -/
noncomputable def lyapunovLowerBound (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  h.objectiveLower - params.multiplierBound ^ 2 / (2 * params.rho)

/-- The corrected Lyapunov lower bound has the standard multiplier correction. -/
theorem lyapunovLowerBound_def (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    lyapunovLowerBound h params =
      h.objectiveLower - params.multiplierBound ^ 2 / (2 * params.rho) := by
  -- Expose the objective lower bound and multiplier correction.
  rfl

end LALM.Correction

end
