/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section RadialSubdifferential

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: Theorem 16.29 rewrites membership in the subdifferential of `x ↦ φ ‖x‖` as
-- Fenchel--Young equality. Example 13.8 identifies the conjugate of this radial function with
-- `u ↦ φ^*(‖u‖)`, Proposition 13.15 gives the scalar Fenchel--Young inequality
-- `φ(‖x‖) + φ^*(‖u‖) ≥ ‖x‖ * ‖u‖`, and Fact 2.11 bounds `⟪x, u⟫` by `‖x‖ * ‖u‖`. Equality in
-- both inequalities is equivalent to `‖u‖ ∈ ∂φ(‖x‖)` and to `x` and `u` lying on the same
-- nonnegative ray.
/-- Example 16.31: for an even function `φ ∈ Γ₀(ℝ)`, a vector `u` belongs to the subdifferential
of the radial function `x ↦ φ ‖x‖` at `x` exactly when `‖u‖` belongs to the subdifferential of
`φ` at `‖x‖` and `x` and `u` lie on the same nonnegative ray. -/
theorem mem_subdifferential_comp_norm_iff_norm_mem_subdifferential_and_same_ray
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ) (x u : H) :
    u ∈ (∂ (fun y : H ↦ φ ‖y‖)) x ↔
      ‖u‖ ∈ (∂ φ) ‖x‖ ∧ SameRay ℝ x u := sorry

end RadialSubdifferential

end ERealFunction
