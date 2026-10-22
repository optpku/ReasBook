/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Topology.MetricSpace.Thickening
public import TR_LALM_theory.Theorem_3_6.Complexity

public section

open MeasureTheory

namespace LALM.StochasticRun.Localization

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀} {Q B b : ℕ+}
variable {confidence : ℝ}

/-- The stochastic objective threshold
`H_st = H_det + 2 * C_eˢ * Aₑ / confidence`. -/
@[expose] noncomputable def objectiveBound
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (confidence : ℝ) : ℝ :=
  LALM.deterministicObjectiveBound h params +
    2 * lyapunovErrorConstant h params * errorAverageConstant h oracle params / confidence

/-- The stochastic objective threshold has the source's explicit formula. -/
theorem objectiveBound_def
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (confidence : ℝ) :
    objectiveBound h oracle params confidence =
      LALM.deterministicObjectiveBound h params +
        2 * lyapunovErrorConstant h params * errorAverageConstant h oracle params /
          confidence := rfl

/-- The stochastic objective--feasibility localization set at the
confidence-dependent threshold. -/
@[expose] def sublevel
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (confidence : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | f x ≤ objectiveBound h oracle params confidence ∧
    ‖c x‖ ≤ 2 * params.multiplierBound / params.rho}

/-- Membership in the stochastic localization set is the conjunction of the
confidence-dependent objective and feasibility bounds. -/
@[simp] theorem mem_sublevel
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (confidence : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ sublevel h oracle params confidence ↔
      f x ≤ objectiveBound h oracle params confidence ∧
        ‖c x‖ ≤ 2 * params.multiplierBound / params.rho := Iff.rfl

/-- The source's two geometric conditions on a stochastic localization set. -/
@[expose] def RegionCondition
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  sublevel h oracle params confidence ⊆ X ∧
    Metric.cthickening params.delta X ⊆ h.region

/-- The stochastic region condition is exactly sublevel containment together
with containment of the closed `params.delta`-neighborhood in `h.region`. -/
theorem regionCondition_iff
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) :
    RegionCondition h oracle params confidence X ↔
      sublevel h oracle params confidence ⊆ X ∧
        Metric.cthickening params.delta X ⊆ h.region := Iff.rfl

/-- Construct the stochastic region condition from its two source clauses. -/
theorem RegionCondition.of
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (h_sublevel : sublevel h oracle params confidence ⊆ X)
    (h_thickening : Metric.cthickening params.delta X ⊆ h.region) :
    RegionCondition h oracle params confidence X :=
  ⟨h_sublevel, h_thickening⟩

/-- A stochastic localization region contains the confidence-dependent sublevel. -/
theorem RegionCondition.sublevel_subset
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (h_region : RegionCondition h oracle params confidence X) :
    sublevel h oracle params confidence ⊆ X := h_region.1

/-- The closed step-neighborhood of a stochastic localization region lies in
the regularity region. -/
theorem RegionCondition.thickening_subset
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (h_region : RegionCondition h oracle params confidence X) :
    Metric.cthickening params.delta X ⊆ h.region := h_region.2

/-- The first time at or after iteration `1` when a stochastic run leaves `X`. -/
@[expose] noncomputable def exitTime
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) : Ω → WithTop ℕ :=
  MeasureTheory.hittingAfter run.point Xᶜ 1

/-- The localization exit time is the canonical hitting time of the complement of `X`. -/
theorem exitTime_def
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) :
    exitTime run X = MeasureTheory.hittingAfter run.point Xᶜ 1 := rfl

/-- Exiting by `K` is equivalent to leaving `X` at some index from `1` through `K`. -/
theorem exitTime_le_iff
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (ω : Ω) (K : ℕ) :
    exitTime run X ω ≤ K ↔
      ∃ j ∈ Set.Icc 1 K, run.point j ω ∉ X := by
  rw [exitTime_def]
  constructor
  · intro h_exit
    obtain ⟨j, hj, hpoint⟩ :=
      (MeasureTheory.hittingAfter_le_iff
        (u := run.point) (s := Xᶜ) (n := 1) (i := K) (ω := ω)).mp h_exit
    exact ⟨j, hj, hpoint⟩
  · rintro ⟨j, hj, hpoint⟩
    exact (MeasureTheory.hittingAfter_le_iff
      (u := run.point) (s := Xᶜ) (n := 1) (i := K) (ω := ω)).mpr
        ⟨j, hj, hpoint⟩

/-- The event that the stochastic run does not leave `X` by iteration `K`. -/
def survivalEvent
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) : Set Ω :=
  {ω | (K : WithTop ℕ) < exitTime run X ω}

/-- Survival through `K` is equivalent to membership in `X` at every index `1, …, K`. -/
theorem mem_survivalEvent
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (ω : Ω) :
    ω ∈ survivalEvent run X K ↔
      ∀ j ∈ Set.Icc 1 K, run.point j ω ∈ X := by
  rw [survivalEvent, Set.mem_setOf_eq, ← not_le, exitTime_le_iff]
  simp

end LALM.StochasticRun.Localization

end

open LALM.StochasticRun
