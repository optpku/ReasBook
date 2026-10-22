/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

universe u

namespace MeasureTheory
namespace ProbabilityMeasure

variable {E : Type u} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

/-- Definition 2.32: The convolution of two probability measures is the probability measure whose
underlying measure is the canonical additive convolution of their underlying measures; equivalently,
it is the push-forward of `μ.prod ν` under addition. -/
noncomputable def conv (μ ν : ProbabilityMeasure E) : ProbabilityMeasure E :=
  ⟨μ.toMeasure ∗ ν.toMeasure, by infer_instance⟩

/-- The convolution of probability measures is the push-forward of their product measure under
addition. -/
theorem conv_eq_map (μ ν : ProbabilityMeasure E) :
    μ.conv ν = (μ.prod ν).map measurable_add.aemeasurable := by
  apply Subtype.ext
  rfl

/-- Probability measures form a monoid under additive convolution, with unit given by the Dirac
probability measure at `0`. Convolution powers are the ordinary monoid powers. -/
noncomputable instance : Monoid (ProbabilityMeasure E) where
  one := diracProba 0
  mul := conv
  mul_assoc μ ν ρ := by
    apply ProbabilityMeasure.toMeasure_injective
    change (((μ : Measure E) ∗ (ν : Measure E)) ∗ (ρ : Measure E)) =
        ((μ : Measure E) ∗ ((ν : Measure E) ∗ (ρ : Measure E)))
    simpa using Measure.conv_assoc (μ : Measure E) (ν : Measure E) (ρ : Measure E)
  one_mul μ := by
    apply ProbabilityMeasure.toMeasure_injective
    change (Measure.dirac 0 ∗ (μ : Measure E)) = (μ : Measure E)
    simp
  mul_one μ := by
    apply ProbabilityMeasure.toMeasure_injective
    change ((μ : Measure E) ∗ Measure.dirac 0) = (μ : Measure E)
    simp
  npow := fun n μ ↦ Nat.recOn n (diracProba 0) fun _ ν ↦ conv ν μ
  npow_zero μ := by
    rfl
  npow_succ n μ := by
    rfl

/-- The unit for probability-measure convolution is the Dirac probability measure at `0`. -/
@[simp]
theorem one_eq_diracProba : (1 : ProbabilityMeasure E) = diracProba 0 := rfl

/-- The underlying measure of the convolution product is the canonical additive convolution of the
underlying measures. -/
@[simp]
theorem toMeasure_mul (μ ν : ProbabilityMeasure E) :
    (μ * ν).toMeasure = μ.toMeasure ∗ ν.toMeasure := rfl

/-- The underlying measure of the convolution of two probability measures is the canonical additive
convolution of their underlying measures. -/
@[simp]
theorem toMeasure_conv (μ ν : ProbabilityMeasure E) :
    (μ.conv ν).toMeasure = μ.toMeasure ∗ ν.toMeasure :=
  toMeasure_mul μ ν

end ProbabilityMeasure
end MeasureTheory
