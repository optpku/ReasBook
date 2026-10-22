/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_3_15
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_14
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_16

-- Semantic recall: `lean_leansearch` surfaced the canonical `gradient` and `iteratedFDeriv`
-- APIs; local Chapter 1 now packages gradient monotonicity through Definition 1.3.15 and keeps
-- the Hessian side in the explicit quadratic-form language `(iteratedFDeriv ℝ 2 f x) ![u, u]`.

open scoped Gradient

section Theorem1317

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {S : Set E} {f : E → ℝ}

-- The textbook states these criteria for nonempty open convex sets, but nonemptiness is
-- redundant for the Lean statements below.

/-- Chapter01 Theorem 1.3.17 (1). The source states this on `ℝ^n`; the canonical Lean statement
uses an arbitrary real complete inner product space. If `S` is open and convex and
`f : E → ℝ` is twice continuously differentiable on `S`, then `∇ f` is monotone on `S`
if and only if the Hessian quadratic form, formalized by `iteratedFDeriv ℝ 2 f`, is
nonnegative in every direction at each point of `S`. -/
theorem gradientMonotoneOn_iff_iteratedFDeriv_nonneg
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hC2 : ContDiffOn ℝ 2 f S) :
    monotoneOperatorOn (fun x : S ↦ ∇ f x) Set.univ ↔
      ∀ x ∈ S, ∀ u : E, 0 ≤ (iteratedFDeriv ℝ 2 f x) ![u, u] := by
  have hDiff : DifferentiableOn ℝ f S := hC2.differentiableOn two_ne_zero
  -- First pass through convexity, which is the common interface between Theorems 1.3.14 and 1.3.16.
  calc
    monotoneOperatorOn (fun x : S ↦ ∇ f x) Set.univ ↔ ConvexOn ℝ S f := by
      simpa using
        (convexOn_iff_gradient_monotoneOn (D := S) (S := S) (f := f)
          hS_open (by intro x hx; exact hx) hS_convex hDiff).symm
    _ ↔ ∀ x ∈ S, ∀ u : E, 0 ≤ (iteratedFDeriv ℝ 2 f x) ![u, u] := by
      exact convexOn_iff_iteratedFDeriv_nonneg hS_open hS_convex hC2

/-- Chapter01 Theorem 1.3.17 (2). The source states this on `ℝ^n`; the canonical Lean statement
uses an arbitrary real complete inner product space. If `S` is open and convex and
`f : E → ℝ` is twice continuously differentiable on `S`, and if the Hessian quadratic form,
formalized by `iteratedFDeriv ℝ 2 f`, is positive in every nonzero direction at each point of
`S`, then `∇ f` is strictly monotone on `S`. -/
theorem gradientStrictMonotoneOn_of_iteratedFDeriv_pos
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hC2 : ContDiffOn ℝ 2 f S)
    (hPos :
      ∀ x ∈ S, ∀ u : E, u ≠ 0 → 0 < (iteratedFDeriv ℝ 2 f x) ![u, u]) :
    strictlyMonotoneOperatorOn (fun x : S ↦ ∇ f x) Set.univ := by
  have hDiff : DifferentiableOn ℝ f S := hC2.differentiableOn two_ne_zero
  -- Convert Hessian positivity into strict convexity before applying the gradient criterion.
  have hStrictConvex : StrictConvexOn ℝ S f :=
    strictConvexOn_of_iteratedFDeriv_pos hS_open hS_convex hC2 hPos
  -- The first-order strict monotonicity criterion now closes the target directly.
  simpa using
    (strictConvexOn_iff_gradient_strictMonotoneOn (D := S) (S := S) (f := f)
      hS_open (by intro x hx; exact hx) hS_convex hDiff).1 hStrictConvex

/-- Chapter01 Theorem 1.3.17 (3). The source states this on `ℝ^n`; the canonical Lean statement
uses an arbitrary real complete inner product space. If `S` is open and convex and
`f : E → ℝ` is twice continuously differentiable on `S`, then `∇ f` is uniformly, or
strongly, monotone on `S` if and only if the Hessian quadratic form, formalized by
`iteratedFDeriv ℝ 2 f`, is uniformly positive definite on `S`, i.e. there exists `c > 0`
such that `c * ‖u‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![u, u]` for all `x ∈ S` and
`u : E`. -/
theorem gradientStrongMonotoneOn_iff_iteratedFDeriv_uniformly_pos
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hC2 : ContDiffOn ℝ 2 f S) :
    stronglyMonotoneOperatorOn (fun x : S ↦ ∇ f x) Set.univ ↔
      ∃ c > 0, ∀ x ∈ S, ∀ u : E,
        c * ‖u‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![u, u] := by
  have hDiff : DifferentiableOn ℝ f S := hC2.differentiableOn two_ne_zero
  -- Again use strong convexity as the shared middle statement for the two imported equivalences.
  calc
    stronglyMonotoneOperatorOn (fun x : S ↦ ∇ f x) Set.univ ↔
        ∃ c > 0, StrongConvexOn S c f := by
      simpa using
        (exists_strongConvexOn_iff_gradient_strongMonotoneOn (D := S) (S := S) (f := f)
          hS_open (by intro x hx; exact hx) hS_convex hDiff).symm
    _ ↔ ∃ c > 0, ∀ x ∈ S, ∀ u : E,
        c * ‖u‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![u, u] := by
      exact exists_strongConvexOn_iff_iteratedFDeriv_uniformly_pos hS_open hS_convex hC2

end Theorem1317
