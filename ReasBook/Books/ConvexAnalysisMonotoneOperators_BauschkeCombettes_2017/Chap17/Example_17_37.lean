/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Example_16_73
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section RadialSubdifferential

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: Example 16.73(1) yields `ρ` with `(∂ φ.toEReal) 0 = [-ρ, ρ]`, and
-- Example 16.73(3) turns that scalar interval into the zero-branch radial formula
-- `(∂ (fun y ↦ φ ‖y‖).toEReal) 0 = B(0; ρ)`. For `x ≠ 0`, Example 16.73(2) rewrites the radial
-- subdifferential as `((∂ φ.toEReal) ‖x‖) • {‖x‖⁻¹ • x}`, while Proposition 17.31(i) makes the
-- scalar owner `(∂ φ.toEReal) ‖x‖` the singleton `{deriv φ ‖x‖}` because `φ` is differentiable
-- off `0`.
/-- Example 17.37: if `φ : ℝ → ℝ` is convex, even, and differentiable on `ℝ \ {0}`, then there
exists `ρ ∈ ℝ₊` such that the scalar subdifferential of `φ` at `0` is `[-ρ, ρ]`, and the
subdifferential of the radial function `x ↦ φ ‖x‖` is the closed ball `B(0; ρ)` at the origin
and the singleton `{(φ'(‖x‖) / ‖x‖) • x}` away from the origin. -/
theorem exists_subdifferential_comp_norm_eq_closedBall_at_zero_and_singleton_of_ne
    (φ : ℝ → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ φ) (heven : Function.Even φ)
    (hφdiff : DifferentiableOn ℝ φ (({0} : Set ℝ)ᶜ)) :
    ∃ ρ : NNReal,
      (∂ φ.toEReal) 0 = Set.Icc (-(ρ : ℝ)) (ρ : ℝ) ∧
      (∂ (fun y : H ↦ φ ‖y‖).toEReal) 0 = Metric.closedBall (0 : H) (ρ : ℝ) ∧
      ∀ x : H, x ≠ 0 →
        (∂ (fun y : H ↦ φ ‖y‖).toEReal) x = ({(deriv φ ‖x‖ / ‖x‖) • x} : Set H) := by
  sorry

end RadialSubdifferential

end

end ERealFunction
