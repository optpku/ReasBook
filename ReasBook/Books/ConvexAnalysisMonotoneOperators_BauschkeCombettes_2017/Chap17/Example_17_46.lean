/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open InnerProductSpace
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private noncomputable def affineInnerSupremumEReal (u : ℕ → H) (α : ℕ → ℝ) : H → EReal :=
  fun x ↦ ⨆ n : ℕ, ((⟪x, u n⟫_ℝ - α n : ℝ) : EReal)

-- Proof sketch: every affine term is a finite real number, hence strictly above `⊥`; the supremum
-- of such terms is again strictly above `⊥`.
private theorem affineInnerSupremum_value_mem_Ioi_bot (u : ℕ → H) (α : ℕ → ℝ) (x : H) :
    affineInnerSupremumEReal u α x ∈ Set.Ioi (⊥ : EReal) := sorry

/-- Example 17.46: the function `x ↦ supₙ (⟪x, uₙ⟫_ℝ - αₙ)` associated with a sequence of vectors
and real offsets. -/
noncomputable def affineInnerSupremum (u : ℕ → H) (α : ℕ → ℝ) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨affineInnerSupremumEReal u α x, affineInnerSupremum_value_mem_Ioi_bot u α x⟩

/-- Coercing `affineInnerSupremum u α` to `EReal` recovers the defining supremum formula. -/
@[simp] theorem affineInnerSupremum_apply (u : ℕ → H) (α : ℕ → ℝ) (x : H) :
    (affineInnerSupremum u α x : EReal) = ⨆ n : ℕ, ((⟪x, u n⟫_ℝ - α n : ℝ) : EReal) :=
  rfl

-- Proof sketch: each map `x ↦ ⟪x, uₙ⟫ - αₙ` is continuous and convex, so Proposition 9.3 applies
-- to their pointwise supremum. Positivity of the offsets gives a finite value at `0`, hence
-- properness.
/-- The supremum of the affine functionals `x ↦ ⟪x, uₙ⟫_ℝ - αₙ` belongs to `Γ₀(H)` when all
offsets are strictly positive. -/
theorem affineInnerSupremum_mem_gammaZero (u : ℕ → H) (α : ℕ → ℝ)
    (hα_pos : ∀ n : ℕ, 0 < α n) :
    affineInnerSupremum u α ∈ Γ₀(H) := sorry

-- Proof sketch: the unit-ball bound gives
-- `⟪x, uₙ⟫_ℝ - αₙ ≤ ‖x‖ * ‖uₙ‖ < ‖x‖` for every `n`, while positivity of `αₙ` keeps the value at
-- `0` finite. Hence the supremum is finite at every point.
/-- If every `uₙ` lies in the open unit ball and every `αₙ` is positive, then the affine supremum
is finite everywhere. -/
theorem affineInnerSupremum_effectiveDomain_eq_univ (u : ℕ → H) (α : ℕ → ℝ)
    (hu_ball : ∀ n : ℕ, ‖u n‖ < 1) (hα_pos : ∀ n : ℕ, 0 < α n) :
    effectiveDomain (affineInnerSupremum u α) = Set.univ := sorry

-- Proof sketch: for each `n`, the increment
-- `⟪x, uₙ⟫_ℝ - αₙ - (⟪y, uₙ⟫_ℝ - αₙ) = ⟪x - y, uₙ⟫_ℝ` is bounded by `‖x - y‖ ‖uₙ‖ ≤ ‖x - y‖`.
-- Taking suprema in both directions gives the `1`-Lipschitz estimate.
/-- If every `uₙ` lies in the open unit ball and every `αₙ` is positive, then the real-valued
representative of the affine supremum is `1`-Lipschitz. -/
theorem affineInnerSupremum_lipschitz (u : ℕ → H) (α : ℕ → ℝ)
    (hu_ball : ∀ n : ℕ, ‖u n‖ < 1) (hα_pos : ∀ n : ℕ, 0 < α n) :
    LipschitzWith 1 (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal) := sorry

-- Proof sketch: at `x = 0`, positivity gives `-αₙ ≤ 0` for every `n`, while `αₙ → 0` shows that
-- the supremum of the values `-αₙ` is at least `0`.
/-- Positive offsets tending to `0` force the affine supremum to vanish at the origin. -/
theorem affineInnerSupremum_zero (u : ℕ → H) (α : ℕ → ℝ)
    (hα_pos : ∀ n : ℕ, 0 < α n) (hα_zero : Tendsto α atTop (𝓝 0)) :
    (affineInnerSupremum u α 0 : EReal) = 0 := sorry

-- Proof sketch: weak convergence of `uₙ` to `0` gives
-- `⟪x, uₙ⟫_ℝ - αₙ → 0` whenever `αₙ → 0`, so the supremum is at least this limit.
/-- If `uₙ ⇀ 0` and `αₙ → 0`, then the affine supremum is nonnegative everywhere. -/
theorem affineInnerSupremum_nonneg (u : ℕ → H) (α : ℕ → ℝ)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_zero : Tendsto α atTop (𝓝 0)) :
    ∀ x : H, 0 ≤ (affineInnerSupremum u α x : EReal) := sorry

-- Proof sketch: positivity of the offsets makes the finitely many low-index terms eventually
-- negative in every fixed direction, the null-sequence hypothesis forces those offsets to vanish
-- along the weakly controlled tail, and weak convergence controls the corresponding inner
-- products. This forces every directional derivative at `0` to vanish.
/-- If `uₙ` lies in the open unit ball, `uₙ ⇀ 0`, and `αₙ` is a positive null sequence, then the
affine supremum is Gâteaux differentiable at `0` with derivative `0`. -/
theorem affineInnerSupremum_hasGateauxDerivativeAt_zero (u : ℕ → H) (α : ℕ → ℝ)
    (hu_ball : ∀ n : ℕ, ‖u n‖ < 1)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_pos : ∀ n : ℕ, 0 < α n) (hα_zero : Tendsto α atTop (𝓝 0)) :
    HasGateauxDerivativeAt
      (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal)
      (0 : H →L[ℝ] ℝ) (0 : H) := sorry

-- Proof sketch: if `uₙ` does not converge strongly to `0`, choose a subsequence with norms bounded
-- away from `0` and test the affine supremum on the normalized vectors
-- `√(α_{kₙ}) • u_{kₙ} / ‖u_{kₙ}‖` to violate the little-o criterion. Conversely, if `uₙ → 0`,
-- split the supremum into finitely many initial terms and a small tail to obtain
-- `f(y) = o(‖y‖)` at the origin.
/-- If `uₙ` lies in the open unit ball, `uₙ ⇀ 0`, and `αₙ` is a positive null sequence, then the
affine supremum is Fréchet differentiable at `0` exactly when `uₙ → 0` strongly. -/
theorem affineInnerSupremum_differentiableAt_zero_iff (u : ℕ → H) (α : ℕ → ℝ)
    (hu_ball : ∀ n : ℕ, ‖u n‖ < 1)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_pos : ∀ n : ℕ, 0 < α n)
    (hα_zero : Tendsto α atTop (𝓝 0)) :
    DifferentiableAt ℝ (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal) (0 : H) ↔
      Tendsto u atTop (𝓝 (0 : H)) := sorry

/-- Companion zero-derivative formulation of Example 17.46 (iii): under the same weak-convergence
hypothesis, Fréchet differentiability at `0` is equivalent to having Fréchet derivative `0`, hence
to strong convergence of `uₙ`. -/
theorem affineInnerSupremum_hasFDerivAt_zero_iff (u : ℕ → H) (α : ℕ → ℝ)
    (hu_ball : ∀ n : ℕ, ‖u n‖ < 1)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_pos : ∀ n : ℕ, 0 < α n)
    (hα_zero : Tendsto α atTop (𝓝 0)) :
    HasFDerivAt (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal)
      (0 : H →L[ℝ] ℝ) (0 : H) ↔
      Tendsto u atTop (𝓝 (0 : H)) := sorry

end ERealFunction
