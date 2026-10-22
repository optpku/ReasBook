/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_40
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Example_16_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Example_16_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section ScalarAndRadialSubdifferential

variable (φ : ℝ → ℝ)

/- Source/core/bridge triage:
- `source-facing`: Example 16.73 records the scalar subdifferential formula for `φ` at `0` and
  the radial subdifferential formulas for `y ↦ φ ‖y‖`.
- `core/canonical`: clause `(1)` is governed by the scalar owner `∂` on `ℝ`, together with the
  one-dimensional monotonicity API of Proposition 17.16 and the continuity/subdifferential owner
  of Proposition 16.17. Clauses `(2)` and `(3)` are governed by the radial membership criterion of
  Example 16.31 and the norm subdifferential formula of Example 16.32.
- `bridge/view`: clause `(2)` packages the owner membership description as a pointwise scalar
  action on the normalized ray, while clause `(3)` specializes the zero branch to the closed ball
  determined by clause `(1)`.
-/

-- Proof sketch: view the real-valued scalar function `φ` through `φ.toEReal`. Corollary
-- 8.40 makes `φ` continuous, so `φ.toEReal ∈ Γ₀(ℝ)`. Proposition 16.17(ii) identifies
-- `(∂ φ.toEReal) 0` as a nonempty weakly compact interval, evenness makes it symmetric,
-- and Proposition 11.7(ii) gives monotonicity on `ℝ₊`, yielding the radius `ρ`.
/-- Example 16.73 (1): if `φ : ℝ → ℝ` is convex and even, then the scalar subdifferential at `0`
is a symmetric interval `[-ρ, ρ]` for some `ρ ∈ ℝ₊`. -/
theorem exists_symmetric_subdifferential_zero_eq_interval
    (hconv : _root_.ConvexOn ℝ Set.univ φ) (heven : Function.Even φ) :
    ∃ ρ : NNReal, (∂ φ.toEReal) 0 = Set.Icc (-(ρ : ℝ)) (ρ : ℝ) := sorry

end ScalarAndRadialSubdifferential

section RadialSubdifferential

open scoped Pointwise

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (φ : ℝ → ℝ)

-- Proof sketch: apply the owner membership theorem of Example 16.31 to `φ.toEReal`, then rewrite
-- `SameRay ℝ x u` with `x ≠ 0` as membership in the pointwise scalar action of the singleton
-- `{‖x‖⁻¹ • x}`. This eliminates the local image wrapper and exposes the canonical set action.
/-- Example 16.73 (2): for every nonzero `x`, the subdifferential of the radial function
`y ↦ φ ‖y‖` at `x` is the scalar subdifferential at `‖x‖` acting on the normalized ray through
`x`. -/
theorem subdifferential_comp_norm_eq_scaled_ray_image_of_ne
    (hconv : _root_.ConvexOn ℝ Set.univ φ) (heven : Function.Even φ)
    (x : H) (hx : x ≠ 0) :
    (∂ (fun y : H ↦ φ ‖y‖).toEReal) x =
      ((∂ φ.toEReal) ‖x‖) • ({‖x‖⁻¹ • x} : Set H) := sorry

-- Proof sketch: combine the explicit scalar interval input `hρ` with the convex radial
-- subdifferential owner at `0`. Example 16.32 identifies the norm subdifferential with the closed
-- unit ball, so scaling by the scalar interval `[-ρ, ρ]` yields `B(0; ρ)`.
/-- Example 16.73 (3): if `ρ` realizes the symmetric scalar subdifferential description from
clause `(1)`, then the subdifferential of `y ↦ φ ‖y‖` at `0` is the closed ball `B(0; ρ)`. -/
theorem subdifferential_comp_norm_zero_eq_closedBall_of_subdifferential_zero_eq_interval
    (hconv : _root_.ConvexOn ℝ Set.univ φ)
    {ρ : NNReal} (hρ : (∂ φ.toEReal) 0 = Set.Icc (-(ρ : ℝ)) (ρ : ℝ)) :
    (∂ (fun y : H ↦ φ ‖y‖).toEReal) 0 =
      Metric.closedBall (0 : H) (ρ : ℝ) := sorry

end RadialSubdifferential

end ERealFunction
