/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

universe u

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Exercise 21.1.2: for a real-valued process on nonnegative time with measurable time slices and
continuous sample paths, the sample-path interval integral over `[(a : ℝ), (b : ℝ)] ⊆ [0, ∞)` is a
measurable function of the sample point. -/
-- Proof sketch: first use
-- `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` to show that
-- `(t, ω) ↦ X (Real.toNNReal t) ω` is strongly measurable on `ℝ × Ω`; then apply measurability of
-- the Bochner integral in one variable over the restricted Lebesgue measure on `Ι a b`, and
-- rewrite the interval integral by `intervalIntegral.integral_of_le`.
theorem measurable_intervalIntegral_of_continuous_paths
    {X : NNReal → Ω → ℝ}
    (hX_meas : ∀ t, Measurable (X t))
    (hX_cont : ∀ ω, Continuous fun t ↦ X t ω)
    {a b : NNReal} (hab : a < b) :
    Measurable (fun ω ↦ ∫ t in (a : ℝ)..(b : ℝ), X (Real.toNNReal t) ω) := by
  let ν : Measure ℝ := volume.restrict (Set.uIoc (a : ℝ) (b : ℝ))
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have h_cont : ∀ ω, Continuous fun t ↦ X (Real.toNNReal t) ω := fun ω ↦
    (hX_cont ω).comp continuous_real_toNNReal
  have h_uncurry : StronglyMeasurable (Function.uncurry fun t ω ↦ X (Real.toNNReal t) ω) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable h_cont
      (fun t ↦ (hX_meas (Real.toNNReal t)).stronglyMeasurable)
  have h_swap : StronglyMeasurable (Function.uncurry fun ω t ↦ X (Real.toNNReal t) ω) := by
    simpa [Function.uncurry] using h_uncurry.comp_measurable measurable_swap
  have h_integral : StronglyMeasurable (fun ω ↦ ∫ t, X (Real.toNNReal t) ω ∂ν) :=
    h_swap.integral_prod_right
  have h_eq :
      (fun ω ↦ ∫ t in (a : ℝ)..(b : ℝ), X (Real.toNNReal t) ω) =
        fun ω ↦ ∫ t, X (Real.toNNReal t) ω ∂ν := by
    ext ω
    simpa [ν, Set.uIoc_of_le habR] using
      (intervalIntegral.integral_of_le hab.le :
        ∫ t in (a : ℝ)..(b : ℝ), X (Real.toNNReal t) ω =
          ∫ t in Set.Ioc (a : ℝ) (b : ℝ), X (Real.toNNReal t) ω ∂volume)
  rw [h_eq]
  exact h_integral.measurable

end MeasureTheory
