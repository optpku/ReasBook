/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u ι

variable {E : Type u}
variable [NormedAddCommGroup E]

variable {I : Type ι} [Fintype I]
variable [NormedSpace ℝ E]
variable {D : Set E}

/-- The operator obtained by taking the finite weighted average of a family of maps on a subset. -/
def weightedOperatorAverage (ω : I → ℝ) (T : I → D → E) : D → E :=
  fun x ↦ ∑ i : I, ω i • T i x

-- Proof sketch: evaluate the definition of `weightedOperatorAverage` at a point of the domain.
/-- The weighted average operator acts pointwise by the corresponding finite weighted sum. -/
@[simp] theorem weightedOperatorAverage_apply (ω : I → ℝ) (T : I → D → E) (x : D) :
    weightedOperatorAverage ω T x = ∑ i : I, ω i • T i x := rfl

variable [InnerProductSpace ℝ E] [CompleteSpace E] [Nonempty I]

-- Proof sketch: apply the weighted variance identity in a real Hilbert space to the family of
-- vectors `T i x - T i y`.
/-- Proposition 4.6 (1): the squared norm of the weighted average difference equals the weighted
sum of squared norms minus the pairwise variance term. -/
theorem weightedOperatorAverage_norm_sq_eq_weighted_norm_sq_sub_pairwise
    (ω : I → ℝ) (T : I → D → E) (hT : ∀ i, IsFirmlyNonexpansiveOn (T i))
    (hω_mem : ∀ i, ω i ∈ Set.Ioc (0 : ℝ) 1) (hω_sum : ∑ i : I, ω i = 1) (x y : D) :
    ‖weightedOperatorAverage ω T x - weightedOperatorAverage ω T y‖ ^ 2 =
      ∑ i : I, ω i * ‖T i x - T i y‖ ^ 2 -
        (1 / 2 : ℝ) * ∑ i : I, ∑ j : I, ω i * ω j * ‖(T i x - T i y) - (T j x - T j y)‖ ^ 2 := sorry

-- Proof sketch: combine the weighted variance identity with the firm nonexpansive bound for each
-- `T i` written in residual norm form.
/-- Proposition 4.6 (2): the squared norm of the weighted average difference is bounded by the
weighted firm nonexpansive estimates together with the same pairwise variance correction. -/
theorem weightedOperatorAverage_norm_sq_le_weighted_residual_sub_pairwise
    (ω : I → ℝ) (T : I → D → E) (hT : ∀ i, IsFirmlyNonexpansiveOn (T i))
    (hω_mem : ∀ i, ω i ∈ Set.Ioc (0 : ℝ) 1) (hω_sum : ∑ i : I, ω i = 1) (x y : D) :
    ‖weightedOperatorAverage ω T x - weightedOperatorAverage ω T y‖ ^ 2 ≤
      ∑ i : I, ω i *
          (‖(x : E) - y‖ ^ 2 - ‖((x : E) - T i x) - ((y : E) - T i y)‖ ^ 2) -
        (1 / 2 : ℝ) * ∑ i : I, ∑ j : I, ω i * ω j * ‖(T i x - T i y) - (T j x - T j y)‖ ^ 2 := sorry

-- Proof sketch: rewrite the residual of the weighted average, expand the Hilbert-space norm
-- identity, and combine it with the previous estimate to obtain the exact formula.
/-- Proposition 4.6 (3): the weighted average satisfies the firm nonexpansive identity with an
additional pairwise correction term. -/
theorem weightedOperatorAverage_norm_sq_eq_sub_residual_sub_pairwise
    (ω : I → ℝ) (T : I → D → E) (hT : ∀ i, IsFirmlyNonexpansiveOn (T i))
    (hω_mem : ∀ i, ω i ∈ Set.Ioc (0 : ℝ) 1) (hω_sum : ∑ i : I, ω i = 1) (x y : D) :
    ‖weightedOperatorAverage ω T x - weightedOperatorAverage ω T y‖ ^ 2 =
      ‖(x : E) - y‖ ^ 2 -
        ‖((x : E) - weightedOperatorAverage ω T x) -
          ((y : E) - weightedOperatorAverage ω T y)‖ ^ 2 -
        ∑ i : I, ∑ j : I, ω i * ω j * ‖(T i x - T i y) - (T j x - T j y)‖ ^ 2 := sorry

-- Proof sketch: drop the nonnegative double-sum correction term from the preceding identity.
/-- Companion bridge: the firm nonexpansiveness conclusion of Proposition 4.6 (4) unfolds to the
displayed residual inequality. -/
theorem weightedOperatorAverage_norm_sq_le_sub_residual
    (ω : I → ℝ) (T : I → D → E) (hT : ∀ i, IsFirmlyNonexpansiveOn (T i))
    (hω_mem : ∀ i, ω i ∈ Set.Ioc (0 : ℝ) 1) (hω_sum : ∑ i : I, ω i = 1) (x y : D) :
    ‖weightedOperatorAverage ω T x - weightedOperatorAverage ω T y‖ ^ 2 ≤
      ‖(x : E) - y‖ ^ 2 -
        ‖((x : E) - weightedOperatorAverage ω T x) -
          ((y : E) - weightedOperatorAverage ω T y)‖ ^ 2 := sorry

/-- Proposition 4.6 (4): the weighted average of firmly nonexpansive operators is firmly
nonexpansive. -/
theorem weightedOperatorAverage_isFirmlyNonexpansiveOn
    (ω : I → ℝ) (T : I → D → E) (hT : ∀ i, IsFirmlyNonexpansiveOn (T i))
    (hω_mem : ∀ i, ω i ∈ Set.Ioc (0 : ℝ) 1) (hω_sum : ∑ i : I, ω i = 1) :
    IsFirmlyNonexpansiveOn (weightedOperatorAverage ω T) := by
  intro x y
  exact weightedOperatorAverage_norm_sq_le_sub_residual ω T hT hω_mem hω_sum x y
