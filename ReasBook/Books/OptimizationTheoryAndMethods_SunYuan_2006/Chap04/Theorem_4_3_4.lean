/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_extra_1

open scoped BigOperators

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ}

-- Domain sampling pass:
-- * source-facing owner for the Fletcher-Reeves recurrence:
--   `ConjugateGradientIterativeScheme E` from `Algorithm_4_2_extra_1`
-- * core/canonical owners reused here:
--   `ConjugateGradientRun E` for the generic nonlinear conjugate-gradient run data,
--   `lineSearchObjective` together with `deriv_lineSearchObjective_apply` for the accepted
--   one-dimensional profile and its canonical derivative, and
--   `StrongWolfeCondition`, `WolfePowellCondition`, and `WolfePowellParameters` from Chapter 2
--   for the accepted inexact-line-search rules
-- * bridge/view added here: `ConjugateGradientRun.WolfePowell` and
--   `ConjugateGradientRun.StrongWolfePowell`, which record the weak and strong
--   Wolfe-Powell rules on a generic run together with the iterate update, leaving the
--   Fletcher-Reeves-specific `β` recurrence in `ConjugateGradientIterativeScheme`
-- Primitive run data remain the iterate, gradient, direction, and step-size sequences together
-- with `HasGradientAt`; the weak- and strong-Wolfe acceptance data are run-level bridges built
-- on the canonical derivative of `lineSearchObjective`, while the
-- normalized direction-ratio API below remains theorem-specific derived data.

namespace ConjugateGradientRun

/-- The derivative of the canonical line-search profile at `0` is the current directional
derivative `⟪g_k, d_k⟫_ℝ`. -/
theorem deriv_lineSearchObjective_zero (method : ConjugateGradientRun E f) (k : ℕ) :
    deriv (lineSearchObjective f (method.x k) (method.d k)) 0 =
      inner ℝ (method.g k) (method.d k) := by
  simpa [zero_smul, add_zero, (method.hasGradientAt k).gradient] using
    deriv_lineSearchObjective_apply f (method.x k) (method.d k) 0
      (by simpa using (method.hasGradientAt k).differentiableAt)

/-- If the accepted step realizes the next recorded iterate, the derivative of the canonical
line-search profile at `α k` is the next directional derivative `⟪g_(k+1), d_k⟫_ℝ`. -/
theorem deriv_lineSearchObjective_step
    (method : ConjugateGradientRun E f) (k : ℕ)
    (hUpdate : method.x (k + 1) = method.x k + method.α k • method.d k) :
    deriv (lineSearchObjective f (method.x k) (method.d k)) (method.α k) =
      inner ℝ (method.g (k + 1)) (method.d k) := by
  have hGrad :
      HasGradientAt f (method.g (k + 1)) (method.x k + method.α k • method.d k) := by
    simpa [hUpdate] using method.hasGradientAt (k + 1)
  simpa using hGrad.deriv_lineSearchObjective_apply

/-- A nonlinear conjugate-gradient run satisfies the Wolfe-Powell rule with parameters `ρ` and
`σ` when each nonstationary step follows the recorded iterate update and satisfies the Chapter 2
weak-Wolfe condition on the canonical line-search profile `lineSearchObjective f (x_k) d_k`.
This is the reusable run-level Wolfe bridge for Chapter 4 methods. -/
structure WolfePowell (f : E → ℝ) (method : ConjugateGradientRun E f) where
  ρ : ℝ
  σ : ℝ
  wolfeParameters : WolfePowellParameters ρ σ
  update (k : ℕ) :
    method.g k ≠ 0 →
      method.x (k + 1) = method.x k + method.α k • method.d k
  wolfe (k : ℕ) :
    method.g k ≠ 0 →
      WolfePowellCondition
        (lineSearchObjective f (method.x k) (method.d k))
        (deriv (lineSearchObjective f (method.x k) (method.d k)))
        ρ σ (method.α k)

namespace WolfePowell

variable {method : ConjugateGradientRun E f}

/-- A Wolfe-Powell run carries the admissible Wolfe-Powell parameter inequalities. -/
instance (hWolfe : WolfePowell f method) : WolfePowellParameters hWolfe.ρ hWolfe.σ :=
  hWolfe.wolfeParameters

/-- Any nonstationary accepted Wolfe-Powell step is positive. -/
theorem alpha_pos
    (hWolfe : WolfePowell f method) (k : ℕ) (hk : method.g k ≠ 0) :
    0 < method.α k :=
  (hWolfe.wolfe k hk).step_pos

/-- Any nonstationary accepted Wolfe-Powell step satisfies the Armijo inequality on the recorded
search ray. -/
theorem armijo
    (hWolfe : WolfePowell f method) (k : ℕ) (hk : method.g k ≠ 0) :
    f (method.x k + method.α k • method.d k) ≤
      f (method.x k) + hWolfe.ρ * method.α k * inner ℝ (method.g k) (method.d k) := by
  let _ := hk
  simpa [lineSearchObjective_apply, lineSearchObjective_zero,
    method.deriv_lineSearchObjective_zero k] using
    (hWolfe.wolfe k hk).sufficientDecrease

/-- Any nonstationary accepted Wolfe-Powell step satisfies the curvature inequality in the
run-level directional-derivative form used in Chapter 4. -/
theorem curvature
    (hWolfe : WolfePowell f method) (k : ℕ) (hk : method.g k ≠ 0) :
    hWolfe.σ * inner ℝ (method.g k) (method.d k) ≤
      inner ℝ (method.g (k + 1)) (method.d k) := by
  let _ := hk
  simpa [method.deriv_lineSearchObjective_zero k,
    method.deriv_lineSearchObjective_step k (hWolfe.update k hk)] using
    (hWolfe.wolfe k hk).curvature

end WolfePowell

/-- A nonlinear conjugate-gradient run satisfies the strong Wolfe-Powell rule with parameters
`ρ` and `σ` when each nonstationary step follows the recorded iterate update and satisfies the
Chapter 2 strong-Wolfe condition on the canonical line-search profile
`lineSearchObjective f (x_k) d_k`, together with the sharper restriction `σ < 1 / 2` used in
Chapter 4.3. This keeps the source-facing strong-Wolfe rule separate from the weaker
Wolfe-Powell curvature inequality. -/
structure StrongWolfePowell (f : E → ℝ) (method : ConjugateGradientRun E f)
    where
  ρ : ℝ
  σ : ℝ
  wolfeParameters : WolfePowellParameters ρ σ
  update (k : ℕ) :
    method.g k ≠ 0 →
      method.x (k + 1) = method.x k + method.α k • method.d k
  sigma_lt_half : σ < 1 / 2
  strongWolfe (k : ℕ) :
    method.g k ≠ 0 →
      StrongWolfeCondition
        (lineSearchObjective f (method.x k) (method.d k))
        (deriv (lineSearchObjective f (method.x k) (method.d k)))
        ρ σ (method.α k)

namespace StrongWolfePowell

variable {method : ConjugateGradientRun E f}

/-- A strong-Wolfe-Powell run carries the admissible Wolfe-Powell parameter inequalities. -/
instance (hWolfe : StrongWolfePowell f method) : WolfePowellParameters hWolfe.ρ hWolfe.σ :=
  hWolfe.wolfeParameters

/-- Any nonstationary accepted strong-Wolfe-Powell step is positive. -/
theorem alpha_pos
    (hWolfe : StrongWolfePowell f method) (k : ℕ) (hk : method.g k ≠ 0) :
    0 < method.α k :=
  (hWolfe.strongWolfe k hk).step_pos

/-- Any nonstationary accepted strong-Wolfe-Powell step satisfies the Armijo inequality on the
recorded search ray. -/
theorem armijo
    (hWolfe : StrongWolfePowell f method) (k : ℕ) (hk : method.g k ≠ 0) :
    f (method.x k + method.α k • method.d k) ≤
      f (method.x k) + hWolfe.ρ * method.α k * inner ℝ (method.g k) (method.d k) := by
  let _ := hk
  simpa [lineSearchObjective_apply, lineSearchObjective_zero,
    method.deriv_lineSearchObjective_zero k] using
    (hWolfe.strongWolfe k hk).sufficientDecrease

/-- Any nonstationary accepted strong-Wolfe-Powell step satisfies the strong curvature
inequality in the run-level directional-derivative form used in Chapter 4. -/
theorem strongCurvature
    (hWolfe : StrongWolfePowell f method) (k : ℕ)
    (hk : method.g k ≠ 0) :
    |inner ℝ (method.g (k + 1)) (method.d k)| ≤
      -hWolfe.σ * inner ℝ (method.g k) (method.d k) := by
  let _ := hk
  simpa [method.deriv_lineSearchObjective_zero k,
    method.deriv_lineSearchObjective_step k (hWolfe.update k hk)] using
    (hWolfe.strongWolfe k hk).strongCurvature

end StrongWolfePowell

/-- The normalized directional derivative `⟪g_k, d_k⟫ / ‖g_k‖²`
appearing in the Fletcher-Reeves descent estimate. -/
def directionRatio (method : ConjugateGradientRun E f) (k : ℕ) : ℝ :=
  inner ℝ (method.g k) (method.d k) / ‖method.g k‖ ^ (2 : ℕ)

end ConjugateGradientRun

/-- Chapter04 Theorem 4.3.4 (1): for a Fletcher-Reeves conjugate-gradient run whose step sizes
satisfy the strong Wolfe-Powell rule, the estimate
`-∑ j in Finset.range (k + 1), hWolfe.σ ^ j ≤ method.directionRatio k ≤
  -2 + ∑ j in Finset.range (k + 1), hWolfe.σ ^ j`
holds at each nonterminated stage `k`; the nontermination side condition is made explicit
because `method.directionRatio k` uses `‖method.g k‖²` in the denominator. -/
theorem fletcherReeves_directionRatio_bounds
    (method : ConjugateGradientIterativeScheme E f)
    (hWolfe : ConjugateGradientRun.StrongWolfePowell f method.toConjugateGradientRun) (k : ℕ)
    (hk : ¬ method.terminatedAt k) :
    -(Finset.sum (Finset.range (k + 1)) fun j ↦ hWolfe.σ ^ j) ≤
      method.toConjugateGradientRun.directionRatio k ∧
      method.toConjugateGradientRun.directionRatio k ≤
        -2 + Finset.sum (Finset.range (k + 1)) (fun j ↦ hWolfe.σ ^ j) := sorry

/-- The lower bound from `fletcherReeves_directionRatio_bounds`, exposed separately for later
rewriting and monotonicity arguments. -/
theorem fletcherReeves_directionRatio_lowerBound
    (method : ConjugateGradientIterativeScheme E f)
    (hWolfe : ConjugateGradientRun.StrongWolfePowell f method.toConjugateGradientRun) (k : ℕ)
    (hk : ¬ method.terminatedAt k) :
    -(Finset.sum (Finset.range (k + 1)) fun j ↦ hWolfe.σ ^ j) ≤
      method.toConjugateGradientRun.directionRatio k :=
  (fletcherReeves_directionRatio_bounds method hWolfe k hk).1

/-- The upper bound from `fletcherReeves_directionRatio_bounds`, exposed separately for later
rewriting and comparison arguments. -/
theorem fletcherReeves_directionRatio_upperBound
    (method : ConjugateGradientIterativeScheme E f)
    (hWolfe : ConjugateGradientRun.StrongWolfePowell f method.toConjugateGradientRun) (k : ℕ)
    (hk : ¬ method.terminatedAt k) :
    method.toConjugateGradientRun.directionRatio k ≤
      -2 + Finset.sum (Finset.range (k + 1)) (fun j ↦ hWolfe.σ ^ j) :=
  (fletcherReeves_directionRatio_bounds method hWolfe k hk).2

/-- Chapter04 Theorem 4.3.4 (2): under the same strong Wolfe-Powell hypotheses, every
nonterminated Fletcher-Reeves search direction is a descent direction, expressed through the
canonical owner `IsDescentDirectionAt f (method.x k) (method.d k)`. -/
theorem fletcherReeves_descentDirection
    (method : ConjugateGradientIterativeScheme E f)
    (hWolfe : ConjugateGradientRun.StrongWolfePowell f method.toConjugateGradientRun) (k : ℕ)
    (hk : ¬ method.terminatedAt k) :
    IsDescentDirectionAt f (method.x k) (method.d k) := sorry

/-- Under the strong Wolfe-Powell hypotheses, every nonterminated Fletcher-Reeves search
direction has negative gradient pairing with the current gradient data. -/
theorem fletcherReeves_descentDirection_inner_neg
    (method : ConjugateGradientIterativeScheme E f)
    (hWolfe : ConjugateGradientRun.StrongWolfePowell f method.toConjugateGradientRun) (k : ℕ)
    (hk : ¬ method.terminatedAt k) :
    inner ℝ (method.g k) (method.d k) < 0 := by
  have hDescent : IsDescentDirectionAt f (method.x k) (method.d k) :=
    fletcherReeves_descentDirection method hWolfe k hk
  simpa [IsDescentDirectionAt, method.gradient_eq k] using hDescent

end
