/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import TR_LALM_theory.Assumption_2_1.Regularity

public section

open scoped NNReal

namespace LALM.Restoration

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The constraint-residual energy `h(x) = (1 / 2) * ‖c x‖ ^ 2`. -/
@[expose] noncomputable def energy
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / 2) * ‖c x‖ ^ 2

/-- The constraint-residual energy has the explicit source formula. -/
theorem energy_def
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    energy c x = (1 / 2) * ‖c x‖ ^ 2 := rfl

/-- The sublevel set of the constraint-residual energy through `z₀`. -/
@[expose] def sublevel
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (z₀ : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | energy c x ≤ energy c z₀}

/-- Membership in the restoration sublevel is the corresponding energy inequality. -/
@[simp] theorem mem_sublevel
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (z₀ x : EuclideanSpace ℝ (Fin n)) :
    x ∈ sublevel c z₀ ↔ energy c x ≤ energy c z₀ := Iff.rfl

/-- The closed-neighborhood radius `M * ‖c z₀‖ / barL` used by restoration. -/
@[expose] noncomputable def radius (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ) : ℝ :=
  hreg.constraintGradientBound * ‖c z₀‖ / barL

/-- The restoration radius has the explicit source formula. -/
theorem radius_def (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ) :
    radius hreg z₀ barL = hreg.constraintGradientBound * ‖c z₀‖ / barL := rfl

/-- One constraint-residual gradient restoration step. -/
@[expose] noncomputable def next
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (barL : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - barL⁻¹ • gradient (energy c) x

/-- A restoration step is the source gradient update. -/
theorem next_apply
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (barL : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    next c barL x = x - barL⁻¹ • gradient (energy c) x := rfl

/-- The restoration sequence obtained by iterating `next`. -/
@[expose] noncomputable def iterate
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (barL : ℝ) (z₀ : EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  (next c barL)^[t] z₀

/-- The restoration sequence starts at `z₀`. -/
@[simp] theorem iterate_zero
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (barL : ℝ) (z₀ : EuclideanSpace ℝ (Fin n)) :
    iterate c barL z₀ 0 = z₀ := rfl

/-- The restoration sequence obeys the source recurrence. -/
@[simp] theorem iterate_succ
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (barL : ℝ) (z₀ : EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    iterate c barL z₀ (t + 1) = next c barL (iterate c barL z₀ t) :=
  Function.iterate_succ_apply' (next c barL) t z₀

/-- The geometric contraction factor for restoration with step parameter `barL`. -/
@[expose] noncomputable def contractionFactor
    (hreg : EqualityConstrained.Regularity f c) (barL : ℝ) : ℝ :=
  1 - hreg.licqModulus ^ 2 / barL

/-- The restoration contraction factor has the explicit source formula. -/
theorem contractionFactor_def (hreg : EqualityConstrained.Regularity f c) (barL : ℝ) :
    contractionFactor hreg barL = 1 - hreg.licqModulus ^ 2 / barL := rfl

/-- The source lower bound imposed on the restoration step parameter. -/
@[expose] def StepSizeCondition (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ) : Prop :=
  max ((hreg.licqModulus : ℝ) ^ 2)
    ((hreg.constraintGradientBound : ℝ) ^ 2 +
      hreg.constraintGradientLipschitz * ‖c z₀‖ *
        (1 + hreg.constraintGradientBound ^ 2 / hreg.licqModulus ^ 2)) < barL

/-- The restoration step-size condition is exactly the source lower bound. -/
theorem stepSizeCondition_iff (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ) :
    StepSizeCondition hreg z₀ barL ↔
      max ((hreg.licqModulus : ℝ) ^ 2)
        ((hreg.constraintGradientBound : ℝ) ^ 2 +
          hreg.constraintGradientLipschitz * ‖c z₀‖ *
            (1 + hreg.constraintGradientBound ^ 2 / hreg.licqModulus ^ 2)) < barL :=
  Iff.rfl

/-- The closed restoration neighborhood lies in the regularity region. -/
@[expose] def RegionCondition (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ) : Prop :=
  Metric.cthickening (radius hreg z₀ barL) (sublevel c z₀) ⊆ hreg.region

/-- The restoration region condition is exactly the source neighborhood inclusion. -/
theorem regionCondition_iff (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ) :
    RegionCondition hreg z₀ barL ↔
      Metric.cthickening (radius hreg z₀ barL) (sublevel c z₀) ⊆ hreg.region :=
  Iff.rfl

/-- The explicit number of restoration steps required by the geometric energy bound. -/
@[expose] noncomputable def stepCount (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (rho multiplierBound : NNRealˣ) : ℕ :=
  Nat.ceil
    (Real.log (max 1 (2 * rho ^ 2 * energy c z₀ / multiplierBound ^ 2)) /
      (-Real.log (contractionFactor hreg barL)))

/-- The restoration step count has the explicit geometric-bound formula. -/
theorem stepCount_def (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (rho multiplierBound : NNRealˣ) :
    stepCount hreg z₀ barL rho multiplierBound =
      Nat.ceil
        (Real.log (max 1 (2 * rho ^ 2 * energy c z₀ / multiplierBound ^ 2)) /
          (-Real.log (contractionFactor hreg barL))) := rfl

end LALM.Restoration

end
