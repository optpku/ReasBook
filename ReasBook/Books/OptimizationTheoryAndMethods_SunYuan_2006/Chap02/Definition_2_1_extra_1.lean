/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3

universe u

-- `IsMinOn` is the canonical mathlib minimizer owner for line-search subproblems.
-- For the search ray itself, the source-facing Chapter 2 owner stays at the weaker
-- `Add`/`SMul` level rather than specializing to an affine-map API that would
-- require stronger subtraction data.

variable {E : Type u}

/-- Chapter02 Definition 2.1-extra-1 (1): the one-dimensional objective associated to the
search ray from `x` in direction `d` is the function `α ↦ f (x + α • d)`. -/
def lineSearchObjective [Add E] [SMul ℝ E] (f : E → ℝ) (x d : E) : ℝ → ℝ :=
  fun α ↦ f (x + α • d)

/-- Evaluating `lineSearchObjective f x d` at `α` gives `f (x + α • d)`. -/
theorem lineSearchObjective_apply [Add E] [SMul ℝ E] (f : E → ℝ) (x d : E) (α : ℝ) :
    lineSearchObjective f x d α = f (x + α • d) :=
  rfl

/-- A local gradient witness for `f` at the ray point `x + t • d` computes the derivative of the
line-search objective as the gradient pairing with the search direction. -/
theorem HasGradientAt.deriv_lineSearchObjective_apply
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g x d : E} {t : ℝ} (hGrad : HasGradientAt f g (x + t • d)) :
    deriv (lineSearchObjective f x d) t = inner ℝ g d := by
  change deriv (f ∘ fun s : ℝ ↦ x + s • d) t = inner ℝ g d
  have hRay : HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
    simpa [one_smul] using ((hasDerivAt_id' t).smul_const d).const_add x
  simpa [InnerProductSpace.toDual_apply_apply] using
    (hGrad.hasFDerivAt.comp_hasDerivAt t hRay).deriv

/-- At a point where `f` is differentiable along the search ray, the derivative of the
line-search objective is the gradient pairing with the search direction. -/
theorem deriv_lineSearchObjective_apply
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x d : E) (t : ℝ) (hDiff : DifferentiableAt ℝ f (x + t • d)) :
    deriv (lineSearchObjective f x d) t =
      inner ℝ (gradient f (x + t • d)) d := by
  simpa using hDiff.hasGradientAt.deriv_lineSearchObjective_apply

/-- A Chapter 1 descent direction yields strict local decrease for the canonical Chapter 2
line-search objective. -/
theorem IsDescentDirectionAt.exists_localDecrease_lineSearchObjective
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {x d : E} (h : IsDescentDirectionAt f x d) :
    ∃ δ > 0, ∀ α : ℝ, 0 < α → α < δ →
      lineSearchObjective f x d α < lineSearchObjective f x d 0 := by
  rcases h.exists_localDecrease with ⟨δ, hδ, hDecrease⟩
  refine ⟨δ, hδ, ?_⟩
  intro α hα hαδ
  simpa [lineSearchObjective] using hDecrease α hα hαδ

/-- Evaluating `lineSearchObjective f x d` at `0` recovers the base value `f x`. -/
theorem lineSearchObjective_zero [AddZeroClass E] [SMulWithZero ℝ E] (f : E → ℝ) (x d : E) :
    lineSearchObjective f x d 0 = f x := by
  simp [lineSearchObjective]

/-- Chapter02 Definition 2.1-extra-1 (2): a line-search step from `x` along the
direction `d` is a step size `α` whose one-dimensional objective value strictly
decreases from `α = 0` to `α`. -/
class IsLineSearchStep [Add E] [SMul ℝ E] (f : E → ℝ) (x d : E) (α : ℝ) : Prop where
  step_pos : 0 < α
  strictDescent : lineSearchObjective f x d α < lineSearchObjective f x d 0

/-- The predicate `IsLineSearchStep` is proposition-valued, hence subsingleton. -/
instance isLineSearchStepSubsingleton [Add E] [SMul ℝ E] (f : E → ℝ) (x d : E) (α : ℝ) :
    Subsingleton (IsLineSearchStep f x d α) := inferInstance

/-- Unfolding specification for `IsLineSearchStep`. -/
theorem isLineSearchStep_iff [Add E] [SMul ℝ E] (f : E → ℝ) (x d : E) (α : ℝ) :
    IsLineSearchStep f x d α ↔
      0 < α ∧ lineSearchObjective f x d α < lineSearchObjective f x d 0 := by
  constructor
  · intro hStep
    exact ⟨hStep.step_pos, hStep.strictDescent⟩
  · rintro ⟨hα, hdesc⟩
    exact ⟨hα, hdesc⟩

/-- Chapter02 Definition 2.1-extra-1 (3): an exact line-search step from `x`
along `d` is a step size `α` at which `lineSearchObjective f x d`
attains its minimum on `Set.Ioi 0`, while still being a genuine line-search
step with strict descent from `α = 0`. -/
class IsExactLineSearchStep [Add E] [SMul ℝ E] (f : E → ℝ) (x d : E) (α : ℝ) : Prop where
  toIsLineSearchStep : IsLineSearchStep f x d α
  isMinOn : IsMinOn (lineSearchObjective f x d) (Set.Ioi (0 : ℝ)) α

/-- Every exact line-search step is, in particular, a line-search step. -/
instance isLineSearchStepOfIsExactLineSearchStep [Add E] [SMul ℝ E]
    {f : E → ℝ} {x d : E} {α : ℝ} [hExact : IsExactLineSearchStep f x d α] :
    IsLineSearchStep f x d α :=
  hExact.toIsLineSearchStep

/-- An exact line-search witness is proposition-valued, hence subsingleton. -/
instance isExactLineSearchStepSubsingleton [Add E] [SMul ℝ E] (f : E → ℝ) (x d : E) (α : ℝ) :
    Subsingleton (IsExactLineSearchStep f x d α) := inferInstance

/-- Unfolding specification for `IsExactLineSearchStep`. -/
theorem isExactLineSearchStep_iff [Add E] [SMul ℝ E] (f : E → ℝ) (x d : E) (α : ℝ) :
    IsExactLineSearchStep f x d α ↔
      IsLineSearchStep f x d α ∧ IsMinOn (lineSearchObjective f x d) (Set.Ioi (0 : ℝ)) α := by
  constructor
  · intro hStep
    exact ⟨hStep.toIsLineSearchStep, hStep.isMinOn⟩
  · rintro ⟨hStep, hMin⟩
    exact ⟨hStep, hMin⟩

/-- Chapter02 Definition 2.1-extra-1 (4): an inexact line-search step from `x`
along `d` is a positive step size `α` whose achieved descent amount is accepted
by a user-supplied predicate `acceptable`, after requiring actual strict descent
from `α = 0`. -/
class IsInexactLineSearchStep [Add E] [SMul ℝ E] (acceptable : ℝ → Prop) (f : E → ℝ)
    (x d : E) (α : ℝ) : Prop extends IsLineSearchStep f x d α where
  acceptedDescent : acceptable (lineSearchObjective f x d 0 - lineSearchObjective f x d α)

/-- Every inexact line-search step is, in particular, a line-search step. -/
theorem IsInexactLineSearchStep.isLineSearchStep [Add E] [SMul ℝ E]
    {acceptable : ℝ → Prop} {f : E → ℝ} {x d : E} {α : ℝ}
    (hInexact : IsInexactLineSearchStep acceptable f x d α) :
    IsLineSearchStep f x d α :=
  hInexact.toIsLineSearchStep

/-- The predicate `IsInexactLineSearchStep` is proposition-valued, hence subsingleton. -/
instance isInexactLineSearchStepSubsingleton [Add E] [SMul ℝ E]
    (acceptable : ℝ → Prop) (f : E → ℝ) (x d : E) (α : ℝ) :
    Subsingleton (IsInexactLineSearchStep acceptable f x d α) := inferInstance

/-- Unfolding specification for `IsInexactLineSearchStep`. -/
theorem isInexactLineSearchStep_iff [Add E] [SMul ℝ E]
    (acceptable : ℝ → Prop) (f : E → ℝ) (x d : E) (α : ℝ) :
    IsInexactLineSearchStep acceptable f x d α ↔
      IsLineSearchStep f x d α ∧
        acceptable (lineSearchObjective f x d 0 - lineSearchObjective f x d α) := by
  constructor
  · intro hStep
    exact ⟨hStep.toIsLineSearchStep, hStep.acceptedDescent⟩
  · rintro ⟨hStep, hAccept⟩
    exact { toIsLineSearchStep := hStep, acceptedDescent := hAccept }
