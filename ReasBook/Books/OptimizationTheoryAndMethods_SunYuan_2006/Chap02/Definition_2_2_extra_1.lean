/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Order.Bounds.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1

universe u

section ExactLineSearch

variable {E : Type u} [Add E] [SMul ℝ E]

/- Chapter02 Definition 2.2-extra-1 (1): the line-search function along `d` from `x`
is `lineSearchObjective f x d`, with value at `0` recovered by
`lineSearchObjective_zero`. This file reuses those canonical owners directly below rather than
introducing a parallel local alias. -/

/-- Chapter02 Definition 2.2-extra-1 (2): an exact line-search step along `d` from `x`
is a point `αk ∈ Set.Ici 0` where `lineSearchObjective f x d` attains its minimum on
the nonnegative ray. This uses the canonical minimizer owner `IsMinOn`, with the domain
condition recorded as membership in `Set.Ici 0`. -/
class IsExactLineSearchStepOnNonnegativeRay (f : E → ℝ) (x d : E) (αk : ℝ) : Prop where
  mem_Ici : αk ∈ Set.Ici 0
  isMinOn : IsMinOn (lineSearchObjective f x d) (Set.Ici 0) αk

/-- Every exact line-search step on `Set.Ioi 0` is also exact on the nonnegative ray `Set.Ici 0`. -/
theorem IsExactLineSearchStep.toIsExactLineSearchStepOnNonnegativeRay
    {f : E → ℝ} {x d : E} {αk : ℝ}
    (h : IsExactLineSearchStep f x d αk) :
    IsExactLineSearchStepOnNonnegativeRay f x d αk := by
  refine ⟨le_of_lt h.toIsLineSearchStep.step_pos, ?_⟩
  refine isMinOn_iff.mpr ?_
  intro α hα
  have hα0 : 0 ≤ α := hα
  rcases lt_or_eq_of_le hα0 with hα' | rfl
  · exact (isMinOn_iff.mp h.isMinOn) α hα'
  · exact le_of_lt h.toIsLineSearchStep.strictDescent

/-- Every exact line-search step on `Set.Ioi 0` is, in particular, exact on `Set.Ici 0`. -/
instance isExactLineSearchStepOnNonnegativeRayOfIsExactLineSearchStep
    {f : E → ℝ} {x d : E} {αk : ℝ} [h : IsExactLineSearchStep f x d αk] :
    IsExactLineSearchStepOnNonnegativeRay f x d αk :=
  h.toIsExactLineSearchStepOnNonnegativeRay

/-- Exact line-search step witnesses are proposition-valued, hence subsingleton. -/
instance isExactLineSearchStepOnNonnegativeRaySubsingleton
    (f : E → ℝ) (x d : E) (αk : ℝ) :
    Subsingleton (IsExactLineSearchStepOnNonnegativeRay f x d αk) := inferInstance

/-- Unfolding specification for `IsExactLineSearchStepOnNonnegativeRay`. -/
theorem isExactLineSearchStepOnNonnegativeRay_iff
    (f : E → ℝ) (x d : E) (αk : ℝ) :
    IsExactLineSearchStepOnNonnegativeRay f x d αk ↔
      0 ≤ αk ∧
        ∀ ⦃α : ℝ⦄, 0 ≤ α →
          lineSearchObjective f x d αk ≤ lineSearchObjective f x d α := by
  constructor
  · intro h
    refine ⟨by simpa [Set.mem_Ici] using h.mem_Ici, ?_⟩
    intro α hα
    exact (isMinOn_iff.mp h.isMinOn) α (by simpa [Set.mem_Ici] using hα)
  · rintro ⟨hαk, hmin⟩
    refine ⟨by simpa [Set.mem_Ici] using hαk, ?_⟩
    exact isMinOn_iff.mpr (fun α hα ↦ hmin (by simpa [Set.mem_Ici] using hα))

/-- A source-facing exact line-search step is nonnegative. -/
theorem IsExactLineSearchStepOnNonnegativeRay.nonneg
    {f : E → ℝ} {x d : E} {αk : ℝ}
    (h : IsExactLineSearchStepOnNonnegativeRay f x d αk) :
    0 ≤ αk :=
  by simpa [Set.mem_Ici] using h.mem_Ici

/-- The exact line-search objective at a source-facing exact step is minimal on `Set.Ici 0`. -/
theorem IsExactLineSearchStepOnNonnegativeRay.optimal
    {f : E → ℝ} {x d : E} {αk : ℝ}
    (h : IsExactLineSearchStepOnNonnegativeRay f x d αk) {α : ℝ} (hα : 0 ≤ α) :
    lineSearchObjective f x d αk ≤ lineSearchObjective f x d α :=
  (isMinOn_iff.mp h.isMinOn) α (by simpa [Set.mem_Ici] using hα)

/-- If `αk` is an exact line-search step, then the line-search objective at `αk` does not
exceed its value at `0`. -/
theorem lineSearchObjective_le_zero_of_isExactLineSearchStepOnNonnegativeRay
    {f : E → ℝ} {x d : E} {αk : ℝ}
    (h : IsExactLineSearchStepOnNonnegativeRay f x d αk) :
    lineSearchObjective f x d αk ≤ lineSearchObjective f x d 0 :=
  h.optimal (by simp)

end ExactLineSearch

section FirstStationary

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Chapter02 Definition 2.2-extra-1 (3): a first stationary exact line-search step along
`d` from `x` is the least nonnegative `α` at which `f` is differentiable and
`inner ℝ (gradient f (x + α • d)) d = 0`. -/
def IsFirstStationaryLineSearchStep (f : E → ℝ) (x d : E) (αk : ℝ) : Prop :=
  IsLeast
    {α : ℝ |
      0 ≤ α ∧
        DifferentiableAt ℝ f (x + α • d) ∧
          inner ℝ (gradient f (x + α • d)) d = 0}
    αk

/-- First stationary exact line-search step witnesses are proposition-valued, hence
subsingleton. -/
instance isFirstStationaryLineSearchStepSubsingleton
    (f : E → ℝ) (x d : E) (αk : ℝ) :
    Subsingleton (IsFirstStationaryLineSearchStep f x d αk) := inferInstance

/-- Unfolding specification for `IsFirstStationaryLineSearchStep`. -/
theorem isFirstStationaryLineSearchStep_iff
    (f : E → ℝ) (x d : E) (αk : ℝ) :
    IsFirstStationaryLineSearchStep f x d αk ↔
      IsLeast
        {α : ℝ |
          0 ≤ α ∧
            DifferentiableAt ℝ f (x + α • d) ∧
              inner ℝ (gradient f (x + α • d)) d = 0}
        αk :=
  Iff.rfl

/-- A first stationary line-search step is nonnegative. -/
theorem IsFirstStationaryLineSearchStep.nonneg
    {f : E → ℝ} {x d : E} {αk : ℝ}
    (h : IsFirstStationaryLineSearchStep f x d αk) :
    0 ≤ αk :=
  h.1.1

/-- A first stationary line-search step occurs where `f` is differentiable along the search
ray. -/
theorem IsFirstStationaryLineSearchStep.differentiableAt_step
    {f : E → ℝ} {x d : E} {αk : ℝ}
    (h : IsFirstStationaryLineSearchStep f x d αk) :
    DifferentiableAt ℝ f (x + αk • d) :=
  h.1.2.1

/-- A first stationary line-search step satisfies the stationarity equation. -/
theorem IsFirstStationaryLineSearchStep.stationary
    {f : E → ℝ} {x d : E} {αk : ℝ}
    (h : IsFirstStationaryLineSearchStep f x d αk) :
    inner ℝ (gradient f (x + αk • d)) d = 0 :=
  h.1.2.2

/-- A first stationary line-search step is the least nonnegative stationary point on the search
ray. -/
theorem IsFirstStationaryLineSearchStep.minimal
    {f : E → ℝ} {x d : E} {αk α : ℝ}
    (h : IsFirstStationaryLineSearchStep f x d αk)
    (hα : 0 ≤ α)
    (hDiff : DifferentiableAt ℝ f (x + α • d))
    (hStat : inner ℝ (gradient f (x + α • d)) d = 0) :
    αk ≤ α :=
  h.2 ⟨hα, hDiff, hStat⟩

/-- Chapter02 Definition 2.2-extra-1 (4): the cosine of the angle between `d` and
`-gradient f x` is the canonical `InnerProductGeometry.cos_angle` formula specialized to the
negative gradient. -/
theorem cos_angle_searchDirection_negGradient (f : E → ℝ) (x d : E) :
    Real.cos (InnerProductGeometry.angle d (-gradient f x)) =
      -(inner ℝ d (gradient f x)) / (‖d‖ * ‖gradient f x‖) := by
  simpa using InnerProductGeometry.cos_angle d (-gradient f x)

/-- Multiplying `cos_angle_searchDirection_negGradient` by `‖gradient f x‖` rewrites the
source-facing cosine factor as the negative normalized directional derivative. -/
theorem gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm
    (f : E → ℝ) (x d : E) :
    ‖gradient f x‖ * Real.cos (InnerProductGeometry.angle d (-gradient f x)) =
      -(inner ℝ (gradient f x) d / ‖d‖) := by
  rw [cos_angle_searchDirection_negGradient]
  calc
    ‖gradient f x‖ * (-(inner ℝ d (gradient f x)) / (‖d‖ * ‖gradient f x‖)) =
        -((‖gradient f x‖ * inner ℝ d (gradient f x)) / (‖d‖ * ‖gradient f x‖)) := by
          ring
    _ = -(inner ℝ d (gradient f x) / ‖d‖) := by
      by_cases hgrad : ‖gradient f x‖ = 0
      · have hgrad' : gradient f x = 0 := norm_eq_zero.mp hgrad
        simp [hgrad']
      · field_simp [hgrad]
    _ = -(inner ℝ (gradient f x) d / ‖d‖) := by rw [real_inner_comm]

end FirstStationary
