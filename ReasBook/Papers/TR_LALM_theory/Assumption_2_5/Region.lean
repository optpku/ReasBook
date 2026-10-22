/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Topology.MetricSpace.Thickening
public import TR_LALM_theory.Assumption_2_3.Parameters

public section

namespace LALM

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The deterministic initial-potential bound determined by the regularity data and
chosen NR-LALM parameters. -/
@[expose] noncomputable def initialPotentialBound (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  f x₀ + h.gradientBound * params.delta +
    4 * params.multiplierBound ^ 2 / params.rho +
    (multiplierPrimalConstant h params.delta params.beta params.rho
      params.multiplierBound / params.rho) * params.delta ^ 2

/-- The initial-potential bound has the explicit source formula for `Φ̄₁`. -/
theorem initialPotentialBound_def (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    initialPotentialBound h params =
      f x₀ + h.gradientBound * params.delta +
        4 * params.multiplierBound ^ 2 / params.rho +
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * params.delta ^ 2 := rfl

/-- The deterministic objective threshold `Hdet` obtained from the initial-potential
bound and the multiplier correction. -/
@[expose] noncomputable def deterministicObjectiveBound
    (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  initialPotentialBound h params +
    params.multiplierBound ^ 2 / (2 * params.rho)

/-- The deterministic objective threshold has its defining explicit formula. -/
theorem deterministicObjectiveBound_def
    (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    deterministicObjectiveBound h params =
      initialPotentialBound h params +
        params.multiplierBound ^ 2 / (2 * params.rho) := rfl

/-- The deterministic objective--feasibility localization set. -/
@[expose] def deterministicSublevel (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | f x ≤ deterministicObjectiveBound h params ∧
    ‖c x‖ ≤ 2 * params.multiplierBound / params.rho}

/-- Membership in the deterministic localization set is the conjunction of
the objective and feasibility bounds. -/
@[simp] theorem mem_deterministicSublevel (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ deterministicSublevel h params ↔
      f x ≤ deterministicObjectiveBound h params ∧
        ‖c x‖ ≤ 2 * params.multiplierBound / params.rho := Iff.rfl

/-- The exact-gradient deterministic sublevel, enlarged by the chosen step radius,
lies inside the regularity region. -/
@[expose] def DeterministicRegionCondition (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : Prop :=
  Metric.cthickening params.delta (deterministicSublevel h params) ⊆ h.region

/-- The deterministic region condition is exactly the closed-neighborhood
containment required by the source assumption. -/
theorem deterministicRegionCondition_iff
    (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    DeterministicRegionCondition h params ↔
      Metric.cthickening params.delta (deterministicSublevel h params) ⊆
        h.region := Iff.rfl

end LALM

end
