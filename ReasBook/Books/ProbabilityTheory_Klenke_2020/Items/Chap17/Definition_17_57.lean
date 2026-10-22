/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

noncomputable section

namespace ProbabilityTheory

variable {d : ℕ}

/-- Definition 17.57 (1): `μ₁` is below `μ₂` in stochastic order if every bounded measurable
coordinatewise monotone increasing test function has smaller `μ₁`-integral than `μ₂`-integral. -/
def StochasticLE (μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)) : Prop :=
  ∀ ⦃f : (Fin d → ℝ) → ℝ⦄, Monotone f →
    Bornology.IsBounded (Set.range f) →
    Measurable f →
    ∫ x, f x ∂(μ1 : Measure (Fin d → ℝ)) ≤ ∫ x, f x ∂(μ2 : Measure (Fin d → ℝ))

-- Proof sketch: for every admissible test function `f`, both sides of the defining inequality are
-- the same integral when `μ₁ = μ₂`.
/-- Stochastic order is reflexive. -/
theorem stochasticLE_refl (μ : ProbabilityMeasure (Fin d → ℝ)) :
    StochasticLE μ μ := by
  -- Unfold the order and test against an arbitrary admissible function.
  intro f _ _ _
  -- Both sides are the same integral because both measures are `μ`.
  exact le_rfl

/-- Definition 17.57 (2): the lower orthant order compares probability measures by reversing the
pointwise order of their values on the closed lower orthants `Set.Iic x`. -/
def LowerOrthantLE (μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)) : Prop :=
  ∀ x : Fin d → ℝ, (μ2 : Measure (Fin d → ℝ)) (Iic x) ≤ (μ1 : Measure (Fin d → ℝ)) (Iic x)

-- Proof sketch: for each `x`, the two measures give the same mass to the closed lower orthant
-- `Set.Iic x`.
/-- Lower orthant order is reflexive. -/
theorem lowerOrthantLE_refl (μ : ProbabilityMeasure (Fin d → ℝ)) :
    LowerOrthantLE μ μ := by
  -- Unfold the pointwise order on lower orthants.
  intro x
  -- The same measure assigns the same mass to `Iic x` on both sides.
  exact le_rfl

end ProbabilityTheory
