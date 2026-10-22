/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

open MeasureTheory intervalIntegral
open scoped MeasureTheory InnerProductSpace

noncomputable section

universe u

section IntegralCriterion

attribute [local instance] Measure.Subtype.measureSpace

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {T : Set.Ioi (0 : ℝ)}
/-- An `L²` derivative witness for a function `x : [0,T] → H` is an `L²([0,T]; H)` class whose
representatives satisfy the textbook integral criterion from Example 2.10. -/
def HasL2DerivativeOnIcc (T : Set.Ioi (0 : ℝ)) (x : Set.Icc (0 : ℝ) (T : ℝ) → H)
    (x' : MeasureTheory.Lp H 2 (volume : Measure (Set.Icc (0 : ℝ) (T : ℝ)))) : Prop :=
  ∃ g : Set.Icc (0 : ℝ) (T : ℝ) → H,
    ∃ hg : MemLp g 2 (volume : Measure (Set.Icc (0 : ℝ) (T : ℝ))),
    hg.toLp g = x' ∧
      ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
        x t = x ⟨0, ⟨le_rfl, le_of_lt T.2⟩⟩ + ∫ s in 0..(t : ℝ), Set.IccExtend
          (le_of_lt T.2) g s

end IntegralCriterion

section Sobolev

attribute [local instance] Measure.Subtype.measureSpace

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {T : Set.Ioi (0 : ℝ)}

/-- Example 2.10: `W^{1,2}([0,T]; H)` consists of a continuous function on `[0,T]` together with a
canonical `L²([0,T]; H)` derivative class satisfying the textbook integral criterion through some
`L²` representative of that class. -/
structure SobolevW12 (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : Set.Ioi (0 : ℝ)) where
  toContinuousMap : C(Set.Icc (0 : ℝ) (T : ℝ), H)
  deriv : MeasureTheory.Lp H 2 (volume : Measure (Set.Icc (0 : ℝ) (T : ℝ)))
  hasL2DerivativeOnIcc : HasL2DerivativeOnIcc T toContinuousMap deriv

local notation "I" => Set.Icc (0 : ℝ) (T : ℝ)

local instance : IsFiniteMeasure (volume : Measure I) := by
  refine ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩

namespace SobolevW12

/-- The canonical `L²([0,T]; H)` class of the continuous part of a Sobolev function. -/
abbrev toLp (x : SobolevW12 H T) :
    MeasureTheory.Lp H 2 (volume : Measure I) :=
  x.toContinuousMap.toLp 2 (volume : Measure I) ℝ

/-- The integral criterion in Example 2.10 is witnessed by some representative of the derivative
class. -/
theorem exists_eq_leftEndpoint_add_intervalIntegral (x : SobolevW12 H T) :
    ∃ g : I → H, ∃ hg : MemLp g 2 (volume : Measure I),
      hg.toLp g = x.deriv ∧
        ∀ t : I,
          x.toContinuousMap t = x.toContinuousMap ⟨0, ⟨le_rfl, le_of_lt T.2⟩⟩ +
            ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) g s := by
  simpa [HasL2DerivativeOnIcc] using x.hasL2DerivativeOnIcc

end SobolevW12

end Sobolev

section SobolevInner

attribute [local instance] Measure.Subtype.measureSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {T : Set.Ioi (0 : ℝ)}

local notation "I" => Set.Icc (0 : ℝ) (T : ℝ)

local instance : IsFiniteMeasure (volume : Measure I) := by
  refine ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩

namespace SobolevW12

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- Example 2.10 equips `W^{1,2}([0,T]; H)` with the scalar product given by the sum of the
canonical `L²` inner products of the function part and of the derivative class. -/
instance : Inner ℝ (SobolevW12 H T) where
  inner x y := inner ℝ x.toLp y.toLp + inner ℝ x.deriv y.deriv

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The textbook scalar product is the sum of the canonical `L²` inner products of the continuous
part and of the derivative class. -/
theorem inner_eq_L2_inner_add_L2_inner (x y : SobolevW12 H T) :
    inner ℝ x y = inner ℝ x.toLp y.toLp + inner ℝ x.deriv y.deriv :=
  rfl

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The continuous part contributes the integral of the pointwise inner product over `[0,T]`. -/
theorem inner_eq_integral_add_L2_inner (x y : SobolevW12 H T) :
    inner ℝ x y =
      (∫ t : I, inner ℝ (x.toContinuousMap t) (y.toContinuousMap t)) +
        inner ℝ x.deriv y.deriv := by
  rw [inner_eq_L2_inner_add_L2_inner, L2.inner_def]
  congr 1
  apply MeasureTheory.integral_congr_ae
  have hx :
      ((x.toLp : MeasureTheory.Lp H 2 (volume : Measure I)) : I → H) =ᵐ[volume] x.toContinuousMap :=
    by
    exact AEEqFun.coeFn_mk x.toContinuousMap _
  have hy :
      ((y.toLp : MeasureTheory.Lp H 2 (volume : Measure I)) : I → H) =ᵐ[volume] y.toContinuousMap :=
    by
    exact AEEqFun.coeFn_mk y.toContinuousMap _
  filter_upwards [hx, hy] with t hxt hyt
  simpa using congrArg₂ (inner ℝ) hxt hyt

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The textbook scalar product is the sum of the pointwise inner-product integrals of the
continuous part and of the derivative class. -/
theorem inner_eq_integral_add_derivative (x y : SobolevW12 H T) :
    inner ℝ x y =
      (∫ t : I, inner ℝ (x.toContinuousMap t) (y.toContinuousMap t)) +
        ∫ t : I, inner ℝ (x.deriv t) (y.deriv t) := by
  rw [inner_eq_integral_add_L2_inner, L2.inner_def]

end SobolevW12

end SobolevInner
