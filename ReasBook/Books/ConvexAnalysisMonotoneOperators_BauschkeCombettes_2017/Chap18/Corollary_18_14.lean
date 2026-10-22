/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section StrongerDifferentiabilityBounds

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: specialize Theorem 18.13 (1) to `φ(s) = β * |s|^(p+1)`. The Cauchy--Schwarz
-- reduction built into Theorem 18.13 then gives the stated bound
-- `⟪x - y, ∇f(x) - ∇f(y)⟫ ≤ β ‖x - y‖^(p+1)`.
/-- Corollary 18.14 (1): if the gradient of a convex Fréchet differentiable function is
`β`-Hölder of order `p`, then
`⟪x - y, ∇f(x) - ∇f(y)⟫ ≤ β ‖x - y‖^(p+1)`. -/
theorem gradient_inner_le_power_bound_of_gradient_norm_le_power_bound
    (f : H → ℝ) (gradf : H → H) (β p : ℝ)
    (hgrad : ∀ x : H, HasFDerivAt f (toDual ℝ H (gradf x)) x)
    (hconv : ConvexOn ℝ (Set.univ : Set H) f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hi : ∀ x y : H, ‖gradf x - gradf y‖ ≤ β * ‖x - y‖ ^ p) :
    ∀ x y : H, ⟪x - y, gradf x - gradf y⟫_ℝ ≤ β * ‖x - y‖ ^ (p + 1) := sorry

-- Proof sketch: specialize Theorem 18.13 (2) to the same power control
-- `φ(s) = β * |s|^(p+1)`. Its integral remainder `θ` simplifies to
-- `β / (p + 1) * ‖x - y‖^(p+1)`.
/-- Corollary 18.14 (2): the bound
`⟪x - y, ∇f(x) - ∇f(y)⟫ ≤ β ‖x - y‖^(p+1)` implies the descent estimate
`f(y) ≤ f(x) + ⟪y - x, ∇f(x)⟫ + β/(p+1) ‖x - y‖^(p+1)`. -/
theorem descent_le_linearization_add_power_bound_of_gradient_inner_le_power_bound
    (f : H → ℝ) (gradf : H → H) (β p : ℝ)
    (hgrad : ∀ x : H, HasFDerivAt f (toDual ℝ H (gradf x)) x)
    (hconv : ConvexOn ℝ (Set.univ : Set H) f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hii : ∀ x y : H, ⟪x - y, gradf x - gradf y⟫_ℝ ≤ β * ‖x - y‖ ^ (p + 1)) :
    ∀ x y : H, f y ≤ f x + ⟪y - x, gradf x⟫_ℝ + β / (p + 1) * ‖x - y‖ ^ (p + 1) := sorry

-- Proof sketch: specialize Theorem 18.13 (3) and then compute the scalar conjugate of
-- `t ↦ β * |t|^(p+1) / (p + 1)` using Example 13.2(i) together with the positive-scaling formula
-- from Proposition 13.23(i).
/-- Corollary 18.14 (3): the descent estimate with remainder
`β/(p+1) ‖x - y‖^(p+1)` implies the lower bound for the Fenchel conjugate
`f*` along the gradient image, with conjugate power exponent `1 + 1/p`. -/
theorem conjugate_gradient_ge_affine_add_conjugate_power_bound_of_descent_le_linearization_add_power_bound
    (f : H → ℝ) (gradf : H → H) (β p : ℝ)
    (hgrad : ∀ x : H, HasFDerivAt f (toDual ℝ H (gradf x)) x)
    (hconv : ConvexOn ℝ (Set.univ : Set H) f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hiii :
      ∀ x y : H,
        f y ≤ f x + ⟪y - x, gradf x⟫_ℝ + β / (p + 1) * ‖x - y‖ ^ (p + 1)) :
    ∀ x y : H,
      conjugate (fun z : H ↦ ((f z : ℝ) : EReal)) (gradf y) ≥
        conjugate (fun z : H ↦ ((f z : ℝ) : EReal)) (gradf x) +
          ((⟪x, gradf y - gradf x⟫_ℝ : ℝ) : EReal) +
            (((β ^ (-1 / p) * p / (p + 1) * ‖gradf x - gradf y‖ ^ (1 + 1 / p) : ℝ) : EReal)) :=
  sorry

-- Proof sketch: apply Theorem 18.13 (4) to the hypothesis from clause (iv) and simplify the
-- specialized scalar conjugate term to
-- `β^(-1/p) * p / (p + 1) * ‖∇f(x) - ∇f(y)‖^(1 + 1/p)`.
/-- Corollary 18.14 (4): the Fenchel-conjugate lower bound from clause (iv) implies the lower
coercivity estimate
`⟪x - y, ∇f(x) - ∇f(y)⟫ ≥ 2 β^(-1/p) p/(p+1) ‖∇f(x) - ∇f(y)‖^(1 + 1/p)`. -/
theorem gradient_inner_ge_two_conjugate_power_bound_of_conjugate_gradient_ge_affine_add_conjugate_power_bound
    (f : H → ℝ) (gradf : H → H) (β p : ℝ)
    (hgrad : ∀ x : H, HasFDerivAt f (toDual ℝ H (gradf x)) x)
    (hconv : ConvexOn ℝ (Set.univ : Set H) f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hiv :
      ∀ x y : H,
        conjugate (fun z : H ↦ ((f z : ℝ) : EReal)) (gradf y) ≥
          conjugate (fun z : H ↦ ((f z : ℝ) : EReal)) (gradf x) +
            ((⟪x, gradf y - gradf x⟫_ℝ : ℝ) : EReal) +
              (((β ^ (-1 / p) * p / (p + 1) * ‖gradf x - gradf y‖ ^ (1 + 1 / p) : ℝ) :
                EReal))) :
    ∀ x y : H,
      ⟪x - y, gradf x - gradf y⟫_ℝ ≥
        2 * β ^ (-1 / p) * p / (p + 1) * ‖gradf x - gradf y‖ ^ (1 + 1 / p) := sorry

-- Proof sketch: combine the lower bound from clause (v) with Cauchy--Schwarz and solve the
-- resulting scalar inequality for `‖∇f(x) - ∇f(y)‖`, which yields the explicit Hölder constant
-- `β * ((p + 1) / (2p))^p`.
/-- Corollary 18.14 (5): the coercivity estimate from clause (v) implies the Hölder bound
`‖∇f(x) - ∇f(y)‖ ≤ β ((p+1)/(2p))^p ‖x - y‖^p`. -/
theorem gradient_norm_le_scaled_power_bound_of_gradient_inner_ge_two_conjugate_power_bound
    (f : H → ℝ) (gradf : H → H) (β p : ℝ)
    (hgrad : ∀ x : H, HasFDerivAt f (toDual ℝ H (gradf x)) x)
    (hconv : ConvexOn ℝ (Set.univ : Set H) f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hv :
      ∀ x y : H,
        ⟪x - y, gradf x - gradf y⟫_ℝ ≥
          2 * β ^ (-1 / p) * p / (p + 1) * ‖gradf x - gradf y‖ ^ (1 + 1 / p)) :
    ∀ x y : H,
      ‖gradf x - gradf y‖ ≤ β * ((p + 1) / (2 * p)) ^ p * ‖x - y‖ ^ p := sorry

end StrongerDifferentiabilityBounds

end ERealFunction
