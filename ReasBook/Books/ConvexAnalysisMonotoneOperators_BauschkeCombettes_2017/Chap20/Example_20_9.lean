/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory InnerProductSpace

noncomputable section

universe u

namespace SetValuedOperator

attribute [local instance] Measure.Subtype.measureSpace

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (T : Set.Ioi (0 : ℝ))

local notation "IccT" => Set.Icc (0 : ℝ) (T : ℝ)
local notation "L2T" => MeasureTheory.Lp H 2 (volume : Measure IccT)
local notation "W12T" => SobolevW12 H T

/-- The left endpoint `0` of the interval `[0,T]` as a point of `Set.Icc (0 : ℝ) T`. -/
def leftEndpoint : IccT :=
  ⟨0, Set.left_mem_Icc.2 (le_of_lt T.2)⟩

/-- The right endpoint `T` of the interval `[0,T]` as a point of `Set.Icc (0 : ℝ) T`. -/
def rightEndpoint : IccT :=
  ⟨(T : ℝ), Set.right_mem_Icc.2 (le_of_lt T.2)⟩

local instance : IsFiniteMeasure (volume : Measure IccT) := by
  refine ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩

/-- Boundary conditions from Example 20.9 for the time-derivative operator on `L²([0,T]; H)`. -/
inductive TimeDerivativeBoundaryCondition (H : Type u) where
  /-- The Sobolev representative has prescribed initial value `x0`. -/
  | initial (x0 : H)
  /-- The Sobolev representative is periodic on `[0,T]`. -/
  | periodic

namespace TimeDerivativeBoundaryCondition

variable {T : Set.Ioi (0 : ℝ)}

/-- The boundary condition from Example 20.9 imposed on a Sobolev representative on `[0,T]`. -/
def Holds (bc : TimeDerivativeBoundaryCondition H) (f : SobolevW12 H T) : Prop :=
  match bc with
  | .initial x0 => f.toContinuousMap (leftEndpoint T) = x0
  | .periodic => f.toContinuousMap (leftEndpoint T) = f.toContinuousMap (rightEndpoint T)

@[simp] theorem holds_initial_iff (x0 : H) (f : SobolevW12 H T) :
    (.initial x0 : TimeDerivativeBoundaryCondition H).Holds f ↔
      f.toContinuousMap (leftEndpoint T) = x0 :=
  Iff.rfl

@[simp] theorem holds_periodic_iff (f : SobolevW12 H T) :
    (TimeDerivativeBoundaryCondition.periodic : TimeDerivativeBoundaryCondition H).Holds f ↔
      f.toContinuousMap (leftEndpoint T) = f.toContinuousMap (rightEndpoint T) :=
  Iff.rfl

end TimeDerivativeBoundaryCondition

/-- The source domain `D` from Example 20.9: the `L²([0,T]; H)` classes that admit a
`W^{1,2}` representative satisfying the chosen boundary condition. -/
def timeDerivativeDomain (bc : TimeDerivativeBoundaryCondition H) : Set L2T :=
  {x | ∃ f : W12T, f.toLp = x ∧ bc.Holds f}

@[simp] theorem mem_timeDerivativeDomain_iff
    (bc : TimeDerivativeBoundaryCondition H) (x : L2T) :
    x ∈ timeDerivativeDomain T bc ↔ ∃ f : W12T, f.toLp = x ∧ bc.Holds f :=
  Iff.rfl

/-- On the source domain from Example 20.9, the derivative class is uniquely determined by the
`L²` class together with the boundary condition. -/
theorem existsUnique_deriv_of_mem_timeDerivativeDomain
    (bc : TimeDerivativeBoundaryCondition H) {x : L2T} (hx : x ∈ timeDerivativeDomain T bc) :
    ∃! x' : L2T, ∃ f : W12T, f.toLp = x ∧ bc.Holds f ∧ f.deriv = x' := sorry

/-- The canonical derivative class attached to an element of the source domain from Example 20.9. -/
def timeDerivative (bc : TimeDerivativeBoundaryCondition H) : timeDerivativeDomain T bc → L2T :=
  fun x ↦ Classical.choose
    (existsUnique_deriv_of_mem_timeDerivativeDomain T bc x.2)

/-- The canonical derivative on the source domain is realized by a Sobolev representative with the
chosen boundary condition. -/
theorem timeDerivative_spec (bc : TimeDerivativeBoundaryCondition H)
    (x : timeDerivativeDomain T bc) :
    ∃ f : W12T,
      f.toLp = (x : L2T) ∧ bc.Holds f ∧ f.deriv = timeDerivative T bc x := by
  rcases Classical.choose_spec
      (existsUnique_deriv_of_mem_timeDerivativeDomain T bc x.2) with
    ⟨hmem, _⟩
  exact hmem

/-- Any Sobolev representative of a point in the source domain has derivative equal to the
canonical derivative attached to that domain point. -/
theorem deriv_eq_timeDerivative_of_exists
    (bc : TimeDerivativeBoundaryCondition H) (x : timeDerivativeDomain T bc) {x' : L2T}
    (hx' : ∃ f : W12T, f.toLp = (x : L2T) ∧ bc.Holds f ∧ f.deriv = x') :
    x' = timeDerivative T bc x := by
  rcases Classical.choose_spec
      (existsUnique_deriv_of_mem_timeDerivativeDomain T bc x.2) with
    ⟨_, huniq⟩
  exact huniq x' hx'

/-- Example 20.9: the time-derivative operator sends `x` to the singleton `{x'}` on the source
domain `D`, where `x'` is the canonical derivative class, and to `∅` outside `D`. -/
def timeDerivativeOperator (bc : TimeDerivativeBoundaryCondition H) : SetValuedOperator L2T L2T :=
  SetValuedOperator.ofFunction (timeDerivativeDomain T bc) (timeDerivative T bc)

@[simp] theorem timeDerivativeOperator_apply_of_mem
    (bc : TimeDerivativeBoundaryCondition H) {x : L2T} (hx : x ∈ timeDerivativeDomain T bc) :
    timeDerivativeOperator T bc x = ({timeDerivative T bc ⟨x, hx⟩} : Set L2T) := by
  simpa [timeDerivativeOperator] using
    SetValuedOperator.ofFunction_apply_of_mem (timeDerivativeDomain T bc) (timeDerivative T bc) hx

@[simp] theorem timeDerivativeOperator_apply_of_not_mem
    (bc : TimeDerivativeBoundaryCondition H) {x : L2T} (hx : x ∉ timeDerivativeDomain T bc) :
    timeDerivativeOperator T bc x = (∅ : Set L2T) := by
  simpa [timeDerivativeOperator] using
    SetValuedOperator.ofFunction_apply_of_not_mem
      (timeDerivativeDomain T bc) (timeDerivative T bc) hx

/-- The source domain `D` is exactly the domain of the time-derivative operator from
Example 20.9. -/
@[simp] theorem mem_dom_timeDerivativeOperator_iff
    (bc : TimeDerivativeBoundaryCondition H) (x : L2T) :
    x ∈ (timeDerivativeOperator T bc).dom ↔ x ∈ timeDerivativeDomain T bc := by
  by_cases hx : x ∈ timeDerivativeDomain T bc
  · constructor
    · intro _
      exact hx
    · intro _
      rw [SetValuedOperator.mem_dom_iff, timeDerivativeOperator_apply_of_mem T bc hx]
      exact Set.singleton_nonempty _
  · constructor
    · intro hdom
      rw [SetValuedOperator.mem_dom_iff, timeDerivativeOperator_apply_of_not_mem T bc hx]
        at hdom
      simp at hdom
    · intro hmem
      exact (hx hmem).elim

-- Proof sketch: split on whether `x` lies in the source domain `D`; on `D`, the operator is the
-- singleton `{timeDerivative x}`, and the specification theorem identifies that canonical
-- derivative with the existential graph description from the Sobolev representative.
/-- Bridge lemma: membership in the time-derivative operator is exactly the existential graph
description in terms of Sobolev representatives satisfying the chosen boundary condition. -/
@[simp] theorem mem_timeDerivativeOperator_iff
    (bc : TimeDerivativeBoundaryCondition H) (x x' : L2T) :
    x' ∈ timeDerivativeOperator T bc x ↔
      ∃ f : W12T, f.toLp = x ∧ bc.Holds f ∧ f.deriv = x' := by
  by_cases hx : x ∈ timeDerivativeDomain T bc
  · rw [timeDerivativeOperator_apply_of_mem T bc hx, Set.mem_singleton_iff]
    constructor
    · intro hx'
      subst hx'
      exact timeDerivative_spec T bc ⟨x, hx⟩
    · intro hx'
      exact deriv_eq_timeDerivative_of_exists T bc ⟨x, hx⟩ hx'
  · rw [timeDerivativeOperator_apply_of_not_mem T bc hx]
    constructor
    · intro hx'
      exact False.elim (Set.notMem_empty x' hx')
    · rintro ⟨f, rfl, hbc, _⟩
      exact (hx ⟨f, rfl, hbc⟩).elim

-- Proof sketch: unfold `timeDerivativeOperator`; in the initial-value branch the value set is
-- exactly the derivatives of Sobolev representatives with left endpoint `x0`.
/-- Membership in the initial-value time-derivative operator means being the derivative class of a
Sobolev representative with the prescribed left endpoint. -/
theorem mem_timeDerivativeOperator_initial_iff (x0 : H) (x x' : L2T) :
    x' ∈ timeDerivativeOperator T (.initial x0) x ↔
      ∃ f : W12T,
        f.toLp = x ∧ f.toContinuousMap (leftEndpoint T) = x0 ∧ f.deriv = x' :=
  by
    rw [mem_timeDerivativeOperator_iff]
    simp

-- Proof sketch: unfold `timeDerivativeOperator`; in the periodic branch the value set is exactly
-- the derivatives of Sobolev representatives whose two endpoint values agree.
/-- Membership in the periodic time-derivative operator means being the derivative class of a
Sobolev representative whose endpoint values on `[0,T]` coincide. -/
theorem mem_timeDerivativeOperator_periodic_iff (x x' : L2T) :
    x' ∈ timeDerivativeOperator T .periodic x ↔
      ∃ f : W12T,
        f.toLp = x ∧ f.toContinuousMap (leftEndpoint T) = f.toContinuousMap (rightEndpoint T) ∧
          f.deriv = x' := by
  rw [mem_timeDerivativeOperator_iff]
  simp

-- Proof sketch: pick Sobolev representatives witnessing `x' ∈ A x` and `y' ∈ A y`, rewrite the
-- monotonicity pairing in `L²([0,T]; H)` as the integral of `⟪f - g, f' - g'⟫`, and use the
-- integration-by-parts identity from the textbook. The boundary term vanishes in the fixed-initial
-- case and is nonnegative in the periodic case because the endpoint differences agree.
section Monotonicity

variable [InnerProductSpace ℝ H]

/-- Example 20.9: for either a prescribed initial value or the periodic boundary condition, the
time-derivative operator on `L²([0,T]; H)` is monotone. -/
theorem timeDerivativeOperator_isMonotone (bc : TimeDerivativeBoundaryCondition H) :
    (timeDerivativeOperator T bc).IsMonotone := sorry

end Monotonicity

end SetValuedOperator
