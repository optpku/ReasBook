/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

namespace ERealFunction

/-- The `Γ₀`-valued representative of the alternating-minimization counterexample. -/
noncomputable def example11_28Function : (ℝ × ℝ) → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    if h : 0 ≤ x.1 ∧ 0 ≤ x.2 then
      ⟨((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal), EReal.bot_lt_coe _⟩
    else
      ⟨⊤, by simp⟩

/-- Coercing the `Γ₀`-valued representative back to `EReal` recovers the explicit formula. -/
@[simp] theorem example11_28Function_apply (x : ℝ × ℝ) :
    (example11_28Function x : EReal) =
      if 0 ≤ x.1 ∧ 0 ≤ x.2 then
        ((max (2 * x.1 - x.2) (2 * x.2 - x.1) : ℝ) : EReal)
      else
        ⊤ :=
  by
    by_cases h : 0 ≤ x.1 ∧ 0 ≤ x.2 <;> simp [example11_28Function, h]

/-- The first coordinate update in Example 11.28: minimize the slice `ξ₁ ↦ f (ξ₁, ξ₂)` while
keeping the second coordinate fixed. -/
def example11_28MinimizeFirst (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, x.2)

/-- The second coordinate update in Example 11.28: minimize the slice `ξ₂ ↦ f (ξ₁, ξ₂)` while
keeping the first coordinate fixed. -/
def example11_28MinimizeSecond (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1, x.1)

/-- One alternating-minimization cycle in Example 11.28 consists of the first-coordinate update
followed by the second-coordinate update. -/
def example11_28AlternatingMinimizationStep (x : ℝ × ℝ) : ℝ × ℝ :=
  example11_28MinimizeSecond (example11_28MinimizeFirst x)

/-- Iterating the alternating-minimization cycle from the initial point `x0`. -/
def example11_28Recurrence (x0 : ℝ × ℝ) : ℕ → ℝ × ℝ :=
  fun n ↦ (example11_28AlternatingMinimizationStep^[n]) x0

local notation "f" => example11_28Function.asEReal

-- Proof sketch: write the function as the sum of the positive-orthant indicator and the maximum
-- of two affine forms. Lower semicontinuity and convexity come from these two pieces, while the
-- explicit formula shows the function is proper.
/-- The explicit function from the counterexample belongs to `Γ₀(ℝ × ℝ)`. -/
theorem example11_28Function_mem_gammaZero :
    example11_28Function ∈ Γ₀(ℝ × ℝ) := sorry

-- Proof sketch: outside the positive orthant the function is `+∞`, while on the orthant the
-- maximum of `2 ξ₁ - ξ₂` and `2 ξ₂ - ξ₁` dominates `(ξ₁ + ξ₂) / 2`; since
-- `(ξ₁ + ξ₂) / 2 → +∞` whenever `‖(ξ₁, ξ₂)‖ → +∞` inside the orthant, the whole function is
-- coercive.
/-- The Example 11.28 function is coercive. -/
theorem example11_28Function_coercive :
    Coercive f := sorry

-- Proof sketch: on the positive orthant the formula is nonnegative and vanishes only at the
-- origin, while outside the orthant the value is `+∞`. This identifies the unique global
-- minimizer.
/-- The minimizer set of the counterexample is the singleton `{(0, 0)}`. -/
theorem example11_28Argmin_eq :
    Argmin f =
      ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) := sorry

-- Proof sketch: evaluate the function at the origin to get the upper bound `0`, and use the
-- explicit positive-orthant formula to show every value is at least `0`.
/-- The infimum of the function values in the counterexample is `0`. -/
theorem example11_28Function_sInf_eq_zero :
    sInf (Set.range f) = 0 := sorry

-- Proof sketch: when `t ≥ 0`, the point `(t, t)` lies in the positive orthant and both affine
-- branches take the common value `t`.
/-- On the nonnegative diagonal, the counterexample function takes the value `t`. -/
theorem example11_28Function_value_on_diagonal {t : ℝ} (ht : 0 ≤ t) :
    f (t, t) = t := sorry

-- Proof sketch: if `ξ₂ < 0`, every slice value is `+∞`, so `x.2` is still a minimizer. If
-- `ξ₂ ≥ 0`, the slice is the maximum of the decreasing affine map `ξ₁ ↦ 2 ξ₂ - ξ₁` and the
-- increasing affine map `ξ₁ ↦ 2 ξ₁ - ξ₂`, whose common minimizer is `ξ₁ = ξ₂`.
/-- The first coordinate update realizes the minimum of the first-coordinate slice. -/
theorem example11_28MinimizeFirst_isMinOn (x : ℝ × ℝ) :
    IsMinOn (fun ξ₁ : ℝ ↦ f (ξ₁, x.2)) Set.univ (example11_28MinimizeFirst x).1 := sorry

-- Proof sketch: if `ξ₁ < 0`, the whole slice is `+∞`, so every point is a minimizer. If
-- `ξ₁ ≥ 0`, the same affine-maximum argument shows that the unique finite minimizer of
-- `ξ₂ ↦ f (ξ₁, ξ₂)` is `ξ₂ = ξ₁`.
/-- The second coordinate update realizes the minimum of the second-coordinate slice. -/
theorem example11_28MinimizeSecond_isMinOn (x : ℝ × ℝ) :
    IsMinOn (fun ξ₂ : ℝ ↦ f (x.1, ξ₂)) Set.univ (example11_28MinimizeSecond x).2 := sorry

-- Proof sketch: unfold the two coordinate updates and simplify the resulting diagonal point.
/-- One alternating-minimization cycle sends `(ξ₁, ξ₂)` to the diagonal point `(ξ₂, ξ₂)`. -/
@[simp] theorem example11_28AlternatingMinimizationStep_eq_diagonal (x : ℝ × ℝ) :
    example11_28AlternatingMinimizationStep x = (x.2, x.2) := by
  rfl

-- Proof sketch: `example11_28MinimizeFirst_isMinOn` identifies the first coordinate update as the
-- relevant slice minimization, and `example11_28MinimizeSecond_isMinOn` does the same for the
-- second coordinate update. After one full cycle the orbit reaches `(ξ₂, ξ₂)`, which is fixed by
-- the same cycle. Induct on `n` through the iterate description.
/-- Every alternating-minimization iterate after the initial one is the diagonal point determined
by the second initial coordinate. -/
theorem example11_28Recurrence_eq_diagonal (x0 : ℝ × ℝ) {n : ℕ} (hn : 1 ≤ n) :
    example11_28Recurrence x0 n = (x0.2, x0.2) := sorry

-- Proof sketch: combine `example11_28Recurrence_eq_diagonal` with
-- `example11_28Function_value_on_diagonal`, using `0 < x0.2` to place the diagonal point inside
-- the positive orthant.
/-- Example 11.28: for every iterate after the initial one, alternating minimization produces the
diagonal point `(ξ₂,₀, ξ₂,₀)` and the function value there is exactly `ξ₂,₀`. -/
theorem alternatingMinimization_eq_diagonal_and_value (x0 : ℝ × ℝ) (hx0_2 : 0 < x0.2)
    {n : ℕ} (hn : 1 ≤ n) :
    example11_28Recurrence x0 n = (x0.2, x0.2) ∧
      f (example11_28Recurrence x0 n) = x0.2 := sorry

-- Proof sketch: use `example11_28Recurrence_eq_diagonal` to show the recurrence is eventually
-- constant with value `(x0.2, x0.2)`, then apply the standard criterion for convergence of
-- eventually constant sequences.
/-- The explicit Example 11.28 recurrence converges to the diagonal point fixed after the first
step. -/
theorem example11_28Recurrence_tendsto (x0 : ℝ × ℝ) :
    Tendsto (example11_28Recurrence x0) atTop (nhds (x0.2, x0.2)) := sorry

-- Proof sketch: the labeled theorem shows that every tail value of the sequence is the positive
-- constant `x0.2`, whereas `example11_28Function_sInf_eq_zero` identifies the infimum with `0`.
-- Hence the function values do not converge to the infimum.
/-- If the second initial coordinate is positive, the Example 11.28 recurrence is not a minimizing
sequence for the counterexample function. -/
theorem example11_28Recurrence_not_isMinimizing (x0 : ℝ × ℝ) (hx0_2 : 0 < x0.2) :
    ¬ IsMinimizingSequence f (example11_28Recurrence x0) := sorry

-- Proof sketch: `example11_28Argmin_eq` identifies the unique minimizer with the origin, while
-- `0 < x0.2` shows the limit point `(x0.2, x0.2)` is not the origin.
/-- If the second initial coordinate is positive, the limit of the Example 11.28 recurrence is not
a minimizer of the counterexample function. -/
theorem example11_28Recurrence_limit_not_mem_argmin (x0 : ℝ × ℝ) (hx0_2 : 0 < x0.2) :
    (x0.2, x0.2) ∉ Argmin f := sorry

end ERealFunction
