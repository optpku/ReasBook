/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_42

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

/- Internal seed for Example 17.13: the scalar square map on `[0, +∞)`, extended by `+∞` on
`(-∞, 0)`. The public owner of the example remains the bivariate function below; this seed only
supports the canonical closed-perspective implementation. -/
private noncomputable def nonnegativeSquare (t : ℝ) : Set.Ioi (⊥ : EReal) :=
  if ht : 0 ≤ t then
    ⟨((t ^ 2 : ℝ) : EReal), EReal.bot_lt_coe _⟩
  else
    ⟨⊤, by simp⟩

private theorem nonnegativeSquare_effectiveDomain_nonempty :
    (effectiveDomain nonnegativeSquare).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_effectiveDomain_iff]
  simp [nonnegativeSquare]

-- Proof sketch: `nonnegativeSquare` is the lower-semicontinuous convex extension of `t ↦ t^2`
-- from `Set.Ici (0 : ℝ)` to `ℝ`, so it is a member of `Γ₀(ℝ)`.
private theorem nonnegativeSquare_mem_gammaZero :
    nonnegativeSquare ∈ Γ₀(ℝ) := sorry

/-- Example 17.13: the counterexample function on `ℝ²` is
`f(ξ,η)=η^2+η^2/ξ` for `ξ > 0` and `η ≥ 0`, `f(0,0)=0`, and `f=+∞` otherwise. -/
noncomputable def quadraticPerspectivePlusSquare : ℝ × ℝ → Set.Ioi (⊥ : EReal) :=
  closedPerspective nonnegativeSquare nonnegativeSquare_effectiveDomain_nonempty +
    (fun p : ℝ × ℝ ↦ p.2 ^ 2).toEReal

-- Proof sketch: unfold the canonical pointwise sum. The closed perspective of
-- `nonnegativeSquare` supplies the `η^2 / ξ` branch on `ξ > 0`, the recession-value branch at
-- `ξ = 0`, and `+∞` elsewhere; the added `toEReal` quadratic contributes the extra `η^2` term.
/-- Coercing the Example 17.13 function to `EReal` recovers its explicit piecewise formula. -/
@[simp] theorem quadraticPerspectivePlusSquare_apply (p : ℝ × ℝ) :
    (quadraticPerspectivePlusSquare p : EReal) =
      if 0 < p.1 ∧ 0 ≤ p.2 then
        ((p.2 ^ 2 + p.2 ^ 2 / p.1 : ℝ) : EReal)
      else if p = ((0 : ℝ), (0 : ℝ)) then
        0
      else
        ⊤ := sorry

-- Proof sketch: on the open positive orthant, the formula is the rational-polynomial map
-- `(ξ,η) ↦ η^2 + η^2 / ξ`; standard Fréchet calculus on products shows this map is twice
-- differentiable there because division by `ξ` is smooth on `ξ > 0`.
/-- The open-domain formula `h(ξ,η)=η^2+η^2/ξ` is twice Fréchet differentiable on
`ℝ_{++}^2 = ]0,+∞[ × ]0,+∞[`. -/
theorem quadraticPerspective_openFormula_contDiffOn :
    ContDiffOn ℝ 2
      (fun p : ℝ × ℝ ↦ p.2 ^ 2 + p.2 ^ 2 / p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := sorry

-- Proof sketch: `nonnegativeSquare_mem_gammaZero` packages the one-sided quadratic seed in
-- `Γ₀(ℝ)`, so `closedPerspective_mem_gammaZero` puts its closed perspective in `Γ₀(ℝ × ℝ)`. The
-- everywhere-finite second-coordinate square is another `Γ₀(ℝ × ℝ)` member, and
-- `pointwiseAdd_mem_gammaZero` applies because the two effective domains intersect at `(0, 0)`.
/-- The Example 17.13 counterexample belongs to `Γ₀(ℝ × ℝ)`. -/
theorem quadraticPerspectivePlusSquare_mem_gammaZero :
    quadraticPerspectivePlusSquare ∈ Γ₀(ℝ × ℝ) := sorry

-- Proof sketch: the function vanishes on the ray `{(ξ,0) | ξ ≥ 0}` inside its effective domain.
-- Evaluating the strict Jensen inequality on two distinct points of that ray gives equality
-- instead of strict inequality, so strict convexity fails.
/-- The Example 17.13 counterexample is not strictly convex. -/
theorem quadraticPerspectivePlusSquare_not_strictlyConvex :
    ¬ StrictlyConvex quadraticPerspectivePlusSquare := sorry

end ERealFunction
