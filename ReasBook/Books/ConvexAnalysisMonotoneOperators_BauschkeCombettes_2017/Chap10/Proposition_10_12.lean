/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))

-- Proof sketch: use `hconv.nonempty` to pick a point of the effective domain, then evaluate the
-- defining infimum at the diagonal pair `x = y`; convexity gives the opposite inequality for every
-- normalized Jensen gap, so the infimum at radius `0` is exactly `0`.
/-- Proposition 10.12 (1): for a proper convex `]-∞,+∞]`-valued function, the exact modulus of
convexity vanishes at `0`. -/
theorem exactModulusOfConvexity_zero
    :
    exactModulusOfConvexity f 0 = 0 := sorry

-- Proof sketch: rewrite convexity through the Jensen-on-domain inequality from Chapter 8, then
-- follow the textbook two-case argument. For `1 < γ < 2`, rescale an admissible pair for `γ * t`
-- and compare the corresponding normalized gaps; for `γ ≥ 2`, factor `γ` into finitely many terms
-- in `(1,2)` and iterate the first step.
/-- Proposition 10.12 (2): for a proper convex `]-∞,+∞]`-valued function, the exact modulus of
convexity satisfies `φ (γ t) ≥ γ^2 φ t` for every `t ∈ ℝ_+` and every `γ ≥ 1`. -/
theorem exactModulusOfConvexity_mul_ge_sq_mul
    (t γ : NNReal) (hγ : 1 ≤ γ) :
    exactModulusOfConvexity f (γ * t) ≥
      (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t := sorry

-- Proof sketch: if `s ≤ t`, write `t = γ * s` with `γ ≥ 1`; then apply the quadratic-scaling
-- inequality and use that the exact modulus takes values in `[0,+∞]` to conclude `φ s ≤ φ t`.
/-- Proposition 10.12 (3): for a proper convex `]-∞,+∞]`-valued function, the exact modulus of
convexity is increasing on `ℝ_+`. -/
theorem exactModulusOfConvexity_monotone
    :
    Monotone (exactModulusOfConvexity f) := sorry

end ERealFunction
