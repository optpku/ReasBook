/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

universe u

-- Polynomial interpolation adds a source-facing bridge between the existing
-- line-search objective owner `lineSearchObjective` and the canonical
-- polynomial/minimizer APIs. The minimizer surface itself remains the
-- canonical `IsMinOn` owner from mathlib.

variable {E : Type u}

/- Chapter02 Definition 2.4-extra-1.
Interpolation methods for line search approximate `lineSearchObjective f x d` on the current
bracketing interval by fitting a quadratic or cubic `Polynomial ℝ` to known sampled data,
choose a new `α` that minimizes the polynomial model on that bracket, and then reduce the
bracketing interval by comparing the new `α` with the previously known points.

The source does not define one single algorithmic owner, but it does use a reusable notion:
a polynomial model whose values agree with the line-search objective at finitely many sampled
step sizes. Choosing a minimizer of that model on the current bracket then remains the canonical
surface `IsMinOn (fun t ↦ p.eval t) (Set.Icc a b) α`.
-/
/-- Chapter02 Definition 2.4-extra-1: a polynomial `p` interpolates the line-search objective
at the sampled step sizes `samplePoints` when `p.eval α = lineSearchObjective f x d α` for every
sampled `α`. -/
def InterpolatesLineSearchOn [Add E] [SMul ℝ E] (f : E → ℝ) (x d : E)
    (p : Polynomial ℝ) (samplePoints : Finset ℝ) : Prop :=
  ∀ ⦃α : ℝ⦄, α ∈ samplePoints → p.eval α = lineSearchObjective f x d α

/-- Helper for Chapter02 Definition 2.4-extra-1: evaluating an interpolating polynomial at a
sampled step size recovers the corresponding line-search objective value. -/
theorem InterpolatesLineSearchOn.eval_eq [Add E] [SMul ℝ E]
    {f : E → ℝ} {x d : E} {p : Polynomial ℝ} {samplePoints : Finset ℝ}
    (h : InterpolatesLineSearchOn f x d p samplePoints) {α : ℝ}
    (hα : α ∈ samplePoints) :
    p.eval α = lineSearchObjective f x d α :=
  -- This is the direct elimination step from the interpolation hypothesis to one sampled value.
  h hα

/-- Helper for Chapter02 Definition 2.4-extra-1: unfolding `InterpolatesLineSearchOn` gives the
source-facing interpolation equations `p.eval α = f (x + α • d)` at each sampled step size. -/
theorem interpolatesLineSearchOn_iff [Add E] [SMul ℝ E] (f : E → ℝ) (x d : E)
    (p : Polynomial ℝ) (samplePoints : Finset ℝ) :
    InterpolatesLineSearchOn f x d p samplePoints ↔
      ∀ ⦃α : ℝ⦄, α ∈ samplePoints → p.eval α = f (x + α • d) := by
  -- Unfold the canonical owner and the ray objective to recover the textbook equation.
  simp [InterpolatesLineSearchOn, lineSearchObjective]
