/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic

noncomputable section

-- This file owns the textbook quadratic-interpolation update `(2.4.25)`, the recursively
-- generated three-point sequence attached to an initial triple, and Algorithm 2.4.2's
-- source-facing bracket update data. `Theorem_2_4_3` is the bridge from this recursive owner to
-- the Chapter 1 convergence-rate owner `HasQOrderConvergenceTo`.

/-- The denominator in the three-point quadratic interpolation update `(2.4.25)`. -/
def quadraticInterpolationStepDenominator (φ : ℝ → ℝ) (a₁ a₂ a₃ : ℝ) : ℝ :=
  φ a₁ / ((a₁ - a₂) * (a₁ - a₃)) +
    φ a₂ / ((a₂ - a₃) * (a₂ - a₁)) +
    φ a₃ / ((a₃ - a₁) * (a₃ - a₂))

/-- The numerator in the three-point quadratic interpolation update `(2.4.25)`. -/
def quadraticInterpolationStepNumerator (φ : ℝ → ℝ) (a₁ a₂ a₃ : ℝ) : ℝ :=
  φ a₁ * (a₂ + a₃) / ((a₁ - a₂) * (a₁ - a₃)) +
    φ a₂ * (a₃ + a₁) / ((a₂ - a₃) * (a₂ - a₁)) +
    φ a₃ * (a₁ + a₂) / ((a₃ - a₁) * (a₃ - a₂))

/-- The three-point quadratic interpolation update `(2.4.25)`. -/
def quadraticInterpolationStep (φ : ℝ → ℝ) (a₁ a₂ a₃ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * quadraticInterpolationStepNumerator φ a₁ a₂ a₃ /
    quadraticInterpolationStepDenominator φ a₁ a₂ a₃

private structure QuadraticInterpolationWindow where
  left : ℝ
  middle : ℝ
  right : ℝ

/-- The sliding interpolation window generated from `(a₀, a₁, a₂)`. Its `n`th value stores
`(αₙ, αₙ₊₁, αₙ₊₂)`. -/
private def quadraticInterpolationWindow
    (φ : ℝ → ℝ) (a₀ a₁ a₂ : ℝ) : ℕ → QuadraticInterpolationWindow
  | 0 => ⟨a₀, a₁, a₂⟩
  | n + 1 =>
      let window := quadraticInterpolationWindow φ a₀ a₁ a₂ n
      ⟨window.middle, window.right,
        quadraticInterpolationStep φ window.left window.middle window.right⟩

/-- The recursively generated three-point quadratic-interpolation sequence from Algorithm 2.4.2
with initial values `a₀`, `a₁`, `a₂`. -/
def quadraticInterpolationSequence (φ : ℝ → ℝ) (a₀ a₁ a₂ : ℝ) : ℕ → ℝ
  | 0 => a₀
  | 1 => a₁
  | n + 2 => (quadraticInterpolationWindow φ a₀ a₁ a₂ n).right

@[simp] theorem quadraticInterpolationSequence_zero
    (φ : ℝ → ℝ) (a₀ a₁ a₂ : ℝ) :
    quadraticInterpolationSequence φ a₀ a₁ a₂ 0 = a₀ := rfl

@[simp] theorem quadraticInterpolationSequence_one
    (φ : ℝ → ℝ) (a₀ a₁ a₂ : ℝ) :
    quadraticInterpolationSequence φ a₀ a₁ a₂ 1 = a₁ := rfl

@[simp] theorem quadraticInterpolationSequence_two
    (φ : ℝ → ℝ) (a₀ a₁ a₂ : ℝ) :
    quadraticInterpolationSequence φ a₀ a₁ a₂ 2 = a₂ := rfl

private theorem quadraticInterpolationWindow_right_eq
    (φ : ℝ → ℝ) (a₀ a₁ a₂ : ℝ) (n : ℕ) :
    (quadraticInterpolationWindow φ a₀ a₁ a₂ n).right =
      quadraticInterpolationSequence φ a₀ a₁ a₂ (n + 2) :=
  rfl

private theorem quadraticInterpolationWindow_middle_eq
    (φ : ℝ → ℝ) (a₀ a₁ a₂ : ℝ) (n : ℕ) :
    (quadraticInterpolationWindow φ a₀ a₁ a₂ n).middle =
      quadraticInterpolationSequence φ a₀ a₁ a₂ (n + 1) := by
  cases n with
  | zero => rfl
  | succ n =>
      exact quadraticInterpolationWindow_right_eq φ a₀ a₁ a₂ n

private theorem quadraticInterpolationWindow_left_eq
    (φ : ℝ → ℝ) (a₀ a₁ a₂ : ℝ) (n : ℕ) :
    (quadraticInterpolationWindow φ a₀ a₁ a₂ n).left =
      quadraticInterpolationSequence φ a₀ a₁ a₂ n := by
  cases n with
  | zero => rfl
  | succ n =>
      exact quadraticInterpolationWindow_middle_eq φ a₀ a₁ a₂ n

/-- The recursive step relation for `quadraticInterpolationSequence`. -/
theorem quadraticInterpolationSequence_step_eq
    (φ : ℝ → ℝ) (a₀ a₁ a₂ : ℝ) (n : ℕ) :
    quadraticInterpolationSequence φ a₀ a₁ a₂ (n + 3) =
      quadraticInterpolationStep φ
        (quadraticInterpolationSequence φ a₀ a₁ a₂ n)
        (quadraticInterpolationSequence φ a₀ a₁ a₂ (n + 1))
        (quadraticInterpolationSequence φ a₀ a₁ a₂ (n + 2)) := by
  calc
    quadraticInterpolationSequence φ a₀ a₁ a₂ (n + 3)
        = (quadraticInterpolationWindow φ a₀ a₁ a₂ (n + 1)).right := by
            rfl
    _ = quadraticInterpolationStep φ
          (quadraticInterpolationWindow φ a₀ a₁ a₂ n).left
          (quadraticInterpolationWindow φ a₀ a₁ a₂ n).middle
          (quadraticInterpolationWindow φ a₀ a₁ a₂ n).right := by
            simp [quadraticInterpolationWindow]
    _ = quadraticInterpolationStep φ
          (quadraticInterpolationSequence φ a₀ a₁ a₂ n)
          (quadraticInterpolationSequence φ a₀ a₁ a₂ (n + 1))
          (quadraticInterpolationSequence φ a₀ a₁ a₂ (n + 2)) := by
            rw [quadraticInterpolationWindow_left_eq, quadraticInterpolationWindow_middle_eq,
              quadraticInterpolationWindow_right_eq]

/-- A valid three-point bracket for quadratic-interpolation line search, with ordered sample
points `α1 < α2 < α3` and the textbook middle-point comparison data
`φ α2 ≤ φ α1`, `φ α2 ≤ φ α3`. The source-side condition that a target minimizer lies in
`[α1, α3]` is expressed directly as `αStar ∈ Set.Icc bracket.α1 bracket.α3`. -/
structure QuadraticInterpolationThreePointBracket (φ : ℝ → ℝ) where
  α1 : ℝ
  α2 : ℝ
  α3 : ℝ
  α1_lt_α2 : α1 < α2
  α2_lt_α3 : α2 < α3
  middle_le_left : φ α2 ≤ φ α1
  middle_le_right : φ α2 ≤ φ α3

/-- The quadratic-interpolation point `αbar` attached to the current bracket by the textbook
formula `(2.4.25)`. -/
noncomputable def QuadraticInterpolationThreePointBracket.interpolationPoint
    (bracket : QuadraticInterpolationThreePointBracket φ) : ℝ :=
  quadraticInterpolationStep φ bracket.α1 bracket.α2 bracket.α3

/-- The sample points of a three-point bracket satisfy `α1 < α3`. -/
theorem QuadraticInterpolationThreePointBracket.α1_lt_α3
    (bracket : QuadraticInterpolationThreePointBracket φ) :
    bracket.α1 < bracket.α3 :=
  lt_trans bracket.α1_lt_α2 bracket.α2_lt_α3

private theorem left_lt_of_negative_secantProduct
    {α1 α3 αbar : ℝ} (hα1_lt_α3 : α1 < α3)
    (hprod : (αbar - α1) * (αbar - α3) < 0) :
    α1 < αbar := by
  by_contra hα1_lt_αbar
  have hαbar_le_α1 : αbar ≤ α1 := not_lt.mp hα1_lt_αbar
  have hαbar_le_α3 : αbar ≤ α3 := le_trans hαbar_le_α1 hα1_lt_α3.le
  have hnonneg : 0 ≤ (αbar - α1) * (αbar - α3) :=
    mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hαbar_le_α1) (sub_nonpos.mpr hαbar_le_α3)
  exact not_lt_of_ge hnonneg hprod

private theorem right_lt_of_negative_secantProduct
    {α1 α3 αbar : ℝ} (hα1_lt_α3 : α1 < α3)
    (hprod : (αbar - α1) * (αbar - α3) < 0) :
    αbar < α3 := by
  by_contra hαbar_lt_α3
  have hα3_le_αbar : α3 ≤ αbar := not_lt.mp hαbar_lt_α3
  have hα1_le_αbar : α1 ≤ αbar := le_trans hα1_lt_α3.le hα3_le_αbar
  have hnonneg : 0 ≤ (αbar - α1) * (αbar - α3) :=
    mul_nonneg (sub_nonneg.mpr hα1_le_αbar) (sub_nonneg.mpr hα3_le_αbar)
  exact not_lt_of_ge hnonneg hprod

namespace QuadraticInterpolationThreePointBracket

def rightKeepMiddle
    (bracket : QuadraticInterpolationThreePointBracket φ) (αbar : ℝ)
    (hα2_lt_αbar : bracket.α2 < αbar) (hφ : φ bracket.α2 ≤ φ αbar) :
    QuadraticInterpolationThreePointBracket φ where
  α1 := bracket.α1
  α2 := bracket.α2
  α3 := αbar
  α1_lt_α2 := bracket.α1_lt_α2
  α2_lt_α3 := hα2_lt_αbar
  middle_le_left := bracket.middle_le_left
  middle_le_right := hφ

def rightUseInterpolationPoint
    (bracket : QuadraticInterpolationThreePointBracket φ) (αbar : ℝ)
    (hα2_lt_αbar : bracket.α2 < αbar) (hαbar_lt_α3 : αbar < bracket.α3)
    (hφ : φ αbar < φ bracket.α2) :
    QuadraticInterpolationThreePointBracket φ where
  α1 := bracket.α2
  α2 := αbar
  α3 := bracket.α3
  α1_lt_α2 := hα2_lt_αbar
  α2_lt_α3 := hαbar_lt_α3
  middle_le_left := hφ.le
  middle_le_right := le_trans hφ.le bracket.middle_le_right

def leftKeepMiddle
    (bracket : QuadraticInterpolationThreePointBracket φ) (αbar : ℝ)
    (hαbar_lt_α2 : αbar < bracket.α2) (hφ : φ bracket.α2 ≤ φ αbar) :
    QuadraticInterpolationThreePointBracket φ where
  α1 := αbar
  α2 := bracket.α2
  α3 := bracket.α3
  α1_lt_α2 := hαbar_lt_α2
  α2_lt_α3 := bracket.α2_lt_α3
  middle_le_left := hφ
  middle_le_right := bracket.middle_le_right

def leftUseInterpolationPoint
    (bracket : QuadraticInterpolationThreePointBracket φ) (αbar : ℝ)
    (hα1_lt_αbar : bracket.α1 < αbar) (hαbar_lt_α2 : αbar < bracket.α2)
    (hφ : φ αbar < φ bracket.α2) :
    QuadraticInterpolationThreePointBracket φ where
  α1 := bracket.α1
  α2 := αbar
  α3 := bracket.α2
  α1_lt_α2 := hα1_lt_αbar
  α2_lt_α3 := hαbar_lt_α2
  middle_le_left := le_trans hφ.le bracket.middle_le_left
  middle_le_right := hφ.le

end QuadraticInterpolationThreePointBracket

/-- The source-facing Step 3 bracket-update rule for Algorithm 2.4.2.

When the interpolation point `αbar` lies to the right of `α2`, the next bracket is either
`(α1, α2, αbar)` or `(α2, αbar, α3)` according to whether `φ αbar` is no smaller than
`φ α2`. When `αbar` lies to the left of `α2`, the next bracket is either `(αbar, α2, α3)` or
`(α1, αbar, α2)` by the same comparison. Any target-containment invariant is tracked
separately by direct interval membership `αStar ∈ Set.Icc bracket.α1 bracket.α3`. -/
inductive QuadraticInterpolationThreePointBracketUpdate
    (bracket : QuadraticInterpolationThreePointBracket φ) (αbar : ℝ) :
    QuadraticInterpolationThreePointBracket φ → Prop where
  | rightKeepMiddle
      (hα2_lt_αbar : bracket.α2 < αbar)
      (hαbar_lt_α3 : αbar < bracket.α3)
      (hφ : φ bracket.α2 ≤ φ αbar) :
      QuadraticInterpolationThreePointBracketUpdate bracket αbar
        (bracket.rightKeepMiddle αbar hα2_lt_αbar hφ)
  | rightUseInterpolationPoint
      (hα2_lt_αbar : bracket.α2 < αbar)
      (hαbar_lt_α3 : αbar < bracket.α3)
      (hφ : φ αbar < φ bracket.α2) :
      QuadraticInterpolationThreePointBracketUpdate bracket αbar
        (bracket.rightUseInterpolationPoint αbar hα2_lt_αbar hαbar_lt_α3 hφ)
  | leftKeepMiddle
      (hα1_lt_αbar : bracket.α1 < αbar)
      (hαbar_lt_α2 : αbar < bracket.α2)
      (hφ : φ bracket.α2 ≤ φ αbar) :
      QuadraticInterpolationThreePointBracketUpdate bracket αbar
        (bracket.leftKeepMiddle αbar hαbar_lt_α2 hφ)
  | leftUseInterpolationPoint
      (hα1_lt_αbar : bracket.α1 < αbar)
      (hαbar_lt_α2 : αbar < bracket.α2)
      (hφ : φ αbar < φ bracket.α2) :
      QuadraticInterpolationThreePointBracketUpdate bracket αbar
        (bracket.leftUseInterpolationPoint αbar hα1_lt_αbar hαbar_lt_α2 hφ)

/-- The outcome of one quadratic-interpolation line-search iteration with three bracket points. -/
inductive QuadraticInterpolationThreePointStepResult (φ : ℝ → ℝ) where
  | retry
  | stop
  | continueWith (nextBracket : QuadraticInterpolationThreePointBracket φ)

private theorem quadraticInterpolationThreePointStepResult_stop_ne_retry
    {φ : ℝ → ℝ} :
    (QuadraticInterpolationThreePointStepResult.stop :
      QuadraticInterpolationThreePointStepResult φ) ≠ .retry := by
  intro h
  cases h

private theorem quadraticInterpolationThreePointStepResult_continueWith_ne_retry
    {φ : ℝ → ℝ} (nextBracket : QuadraticInterpolationThreePointBracket φ) :
    (QuadraticInterpolationThreePointStepResult.continueWith nextBracket :
      QuadraticInterpolationThreePointStepResult φ) ≠ .retry := by
  intro h
  cases h

private theorem quadraticInterpolationThreePointStepResult_continueWith_ne_stop
    {φ : ℝ → ℝ} (nextBracket : QuadraticInterpolationThreePointBracket φ) :
    (QuadraticInterpolationThreePointStepResult.continueWith nextBracket :
      QuadraticInterpolationThreePointStepResult φ) ≠ .stop := by
  intro h
  cases h

private theorem quadraticInterpolationThreePointStepResult_continueWith_injective
    {φ : ℝ → ℝ}
    {bracket₁ bracket₂ : QuadraticInterpolationThreePointBracket φ}
    (h :
      QuadraticInterpolationThreePointStepResult.continueWith bracket₁ =
        QuadraticInterpolationThreePointStepResult.continueWith bracket₂) :
    bracket₁ = bracket₂ := by
  cases h
  rfl

namespace QuadraticInterpolationThreePointBracket

/-- Chapter02 Algorithm 2.4.2 (Line Search Employing Quadratic Interpolation with Three Points).
Given a positive tolerance `ε > 0`, a line-search objective `φ`, and a valid current bracket
`{α1, α2, α3}`, Step 1 produces `αbar = bracket.interpolationPoint` by the
quadratic-interpolation formula `(2.4.25)`. If one also tracks a target minimizer `αStar`,
the source hypothesis that it lies in the current bracket is
`αStar ∈ Set.Icc bracket.α1 bracket.α3`.
One textbook iteration:

* retries when `(αbar - α1) * (αbar - α3) ≥ 0`,
* stops when `αbar` lies between `α1` and `α3` and `|αbar - α2| < ε`,
* otherwise continues with the Step 3 bracket computed from `α1`, `α2`, `α3`, and `αbar`. -/
noncomputable def step
    (bracket : QuadraticInterpolationThreePointBracket φ) (ε : ℝ)
    (hε : 0 < ε) : QuadraticInterpolationThreePointStepResult φ :=
  let αbar := bracket.interpolationPoint
  if houtside : 0 ≤ (αbar - bracket.α1) * (αbar - bracket.α3) then
    .retry
  else if htol : |αbar - bracket.α2| < ε then
    .stop
  else
    let hinside : (αbar - bracket.α1) * (αbar - bracket.α3) < 0 := lt_of_not_ge houtside
    let hα1_lt_αbar :=
      left_lt_of_negative_secantProduct bracket.α1_lt_α3 hinside
    let hαbar_lt_α3 :=
      right_lt_of_negative_secantProduct bracket.α1_lt_α3 hinside
    if hα2_lt_αbar : bracket.α2 < αbar then
      if hφ : φ bracket.α2 ≤ φ αbar then
        .continueWith (bracket.rightKeepMiddle αbar hα2_lt_αbar hφ)
      else
        .continueWith
          (bracket.rightUseInterpolationPoint αbar hα2_lt_αbar hαbar_lt_α3
            (lt_of_not_ge hφ))
    else if hαbar_lt_α2 : αbar < bracket.α2 then
      if hφ : φ bracket.α2 ≤ φ αbar then
        .continueWith (bracket.leftKeepMiddle αbar hαbar_lt_α2 hφ)
      else
        .continueWith
          (bracket.leftUseInterpolationPoint αbar hα1_lt_αbar hαbar_lt_α2
            (lt_of_not_ge hφ))
    else
      have hαbar_eq_α2 : αbar = bracket.α2 :=
        le_antisymm (le_of_not_gt hα2_lt_αbar) (le_of_not_gt hαbar_lt_α2)
      have htol' : |αbar - bracket.α2| < ε := by
        rw [hαbar_eq_α2, sub_self, abs_zero]
        exact hε
      False.elim (htol htol')

/-- `bracket.step ε hε` retries exactly when the interpolation point fails
the textbook interval test `(αbar - α1) * (αbar - α3) < 0`. -/
theorem step_eq_retry_iff
    (bracket : QuadraticInterpolationThreePointBracket φ) (ε : ℝ) (hε : 0 < ε) :
    bracket.step ε hε = .retry ↔
      0 ≤
        (bracket.interpolationPoint - bracket.α1) *
          (bracket.interpolationPoint - bracket.α3) := by
  let s := bracket.interpolationPoint
  by_cases ht : 0 ≤ (s - bracket.α1) * (s - bracket.α3)
  · simp only [step, s, dif_pos ht]
    simpa [s] using ht
  · have hnotRetry : bracket.step ε hε ≠ .retry := by
      by_cases htol : |s - bracket.α2| < ε
      · simpa only [step, s, dif_neg ht, dif_pos htol] using
          (quadraticInterpolationThreePointStepResult_stop_ne_retry : _)
      · by_cases hα2_lt_s : bracket.α2 < s
        · by_cases hφ : φ bracket.α2 ≤ φ s
          · simpa only [step, s, dif_neg ht, dif_neg htol,
              dif_pos hα2_lt_s, dif_pos hφ] using
              quadraticInterpolationThreePointStepResult_continueWith_ne_retry
                (bracket.rightKeepMiddle s hα2_lt_s hφ)
          · simpa only [step, s, dif_neg ht, dif_neg htol,
              dif_pos hα2_lt_s, dif_neg hφ] using
              quadraticInterpolationThreePointStepResult_continueWith_ne_retry
                (bracket.rightUseInterpolationPoint s hα2_lt_s
                  (right_lt_of_negative_secantProduct bracket.α1_lt_α3 (lt_of_not_ge ht))
                  (lt_of_not_ge hφ))
        · by_cases hs_lt_α2 : s < bracket.α2
          · by_cases hφ : φ bracket.α2 ≤ φ s
            · simpa only [step, s, dif_neg ht, dif_neg htol,
                dif_neg hα2_lt_s, dif_pos hs_lt_α2, dif_pos hφ] using
                quadraticInterpolationThreePointStepResult_continueWith_ne_retry
                  (bracket.leftKeepMiddle s hs_lt_α2 hφ)
            · simpa only [step, s, dif_neg ht, dif_neg htol,
                dif_neg hα2_lt_s, dif_pos hs_lt_α2, dif_neg hφ] using
                quadraticInterpolationThreePointStepResult_continueWith_ne_retry
                  (bracket.leftUseInterpolationPoint s
                    (left_lt_of_negative_secantProduct bracket.α1_lt_α3 (lt_of_not_ge ht))
                    hs_lt_α2 (lt_of_not_ge hφ))
          · have hs_eq_α2 : s = bracket.α2 :=
              le_antisymm (le_of_not_gt hα2_lt_s) (le_of_not_gt hs_lt_α2)
            have htol' : |s - bracket.α2| < ε := by
              rw [hs_eq_α2, sub_self, abs_zero]
              exact hε
            exact False.elim (htol htol')
    constructor
    · intro hretry
      exact False.elim (hnotRetry hretry)
    · intro hge
      exact False.elim (ht hge)

/-- `bracket.step ε hε` stops exactly when the interpolation point lies
strictly between `α1` and `α3` in the sense that
`(bracket.interpolationPoint - α1) * (bracket.interpolationPoint - α3) < 0`, and the tolerance
test `|bracket.interpolationPoint - α2| < ε` succeeds. -/
theorem step_eq_stop_iff
    (bracket : QuadraticInterpolationThreePointBracket φ) (ε : ℝ) (hε : 0 < ε) :
    bracket.step ε hε = .stop ↔
      (bracket.interpolationPoint - bracket.α1) *
          (bracket.interpolationPoint - bracket.α3) < 0 ∧
        |bracket.interpolationPoint - bracket.α2| < ε := by
  let s := bracket.interpolationPoint
  by_cases ht : 0 ≤ (s - bracket.α1) * (s - bracket.α3)
  · have hnot : ¬ (s - bracket.α1) * (s - bracket.α3) < 0 := not_lt_of_ge ht
    simp only [step, s, dif_pos ht]
    simp [s, hnot]
  · have ht' : (s - bracket.α1) * (s - bracket.α3) < 0 := lt_of_not_ge ht
    by_cases htol : |s - bracket.α2| < ε
    · simp only [step, s, dif_neg ht, dif_pos htol]
      simp [s, ht', htol]
    · have hnotStop : bracket.step ε hε ≠ .stop := by
        by_cases hα2_lt_s : bracket.α2 < s
        · by_cases hφ : φ bracket.α2 ≤ φ s
          · simpa only [step, s, dif_neg ht, dif_neg htol,
              dif_pos hα2_lt_s, dif_pos hφ] using
              quadraticInterpolationThreePointStepResult_continueWith_ne_stop
                (bracket.rightKeepMiddle s hα2_lt_s hφ)
          · simpa only [step, s, dif_neg ht, dif_neg htol,
              dif_pos hα2_lt_s, dif_neg hφ] using
              quadraticInterpolationThreePointStepResult_continueWith_ne_stop
                (bracket.rightUseInterpolationPoint s hα2_lt_s
                  (right_lt_of_negative_secantProduct bracket.α1_lt_α3 ht')
                  (lt_of_not_ge hφ))
        · by_cases hs_lt_α2 : s < bracket.α2
          · by_cases hφ : φ bracket.α2 ≤ φ s
            · simpa only [step, s, dif_neg ht, dif_neg htol,
                dif_neg hα2_lt_s, dif_pos hs_lt_α2, dif_pos hφ] using
                quadraticInterpolationThreePointStepResult_continueWith_ne_stop
                  (bracket.leftKeepMiddle s hs_lt_α2 hφ)
            · simpa only [step, s, dif_neg ht, dif_neg htol,
                dif_neg hα2_lt_s, dif_pos hs_lt_α2, dif_neg hφ] using
                quadraticInterpolationThreePointStepResult_continueWith_ne_stop
                  (bracket.leftUseInterpolationPoint s
                    (left_lt_of_negative_secantProduct bracket.α1_lt_α3 ht')
                    hs_lt_α2 (lt_of_not_ge hφ))
          · have hs_eq_α2 : s = bracket.α2 :=
              le_antisymm (le_of_not_gt hα2_lt_s) (le_of_not_gt hs_lt_α2)
            have htol' : |s - bracket.α2| < ε := by
              rw [hs_eq_α2, sub_self, abs_zero]
              exact hε
            exact False.elim (htol htol')
      constructor
      · intro hstop
        exact False.elim (hnotStop hstop)
      · intro h
        exact False.elim (htol h.2)

/-- `bracket.step ε hε` continues exactly when the interpolation point lies
strictly between `α1` and `α3`, fails the tolerance test `|αbar - α2| < ε`, and the resulting
next bracket is one of the four textbook Step 3 updates. -/
theorem step_eq_continueWith_iff
    (bracket : QuadraticInterpolationThreePointBracket φ) (ε : ℝ) (hε : 0 < ε)
    (nextBracket : QuadraticInterpolationThreePointBracket φ) :
    bracket.step ε hε = .continueWith nextBracket ↔
      (bracket.interpolationPoint - bracket.α1) *
          (bracket.interpolationPoint - bracket.α3) < 0 ∧
        ¬ (|bracket.interpolationPoint - bracket.α2| < ε) ∧
        QuadraticInterpolationThreePointBracketUpdate
          bracket bracket.interpolationPoint nextBracket := by
  let s := bracket.interpolationPoint
  constructor
  · intro hStep
    have hinside :
        (s - bracket.α1) * (s - bracket.α3) < 0 := by
      refine lt_of_not_ge ?_
      intro hge
      have hretry : bracket.step ε hε = .retry :=
        (bracket.step_eq_retry_iff ε hε).2
          (by simpa [s] using hge)
      rw [hStep] at hretry
      cases hretry
    have hnotTol : ¬ |s - bracket.α2| < ε := by
      intro htol
      have hstop : bracket.step ε hε = .stop :=
        (bracket.step_eq_stop_iff ε hε).2
          ⟨by simpa [s] using hinside, by simpa [s] using htol⟩
      rw [hStep] at hstop
      cases hstop
    have hα1_lt_s : bracket.α1 < s :=
      left_lt_of_negative_secantProduct bracket.α1_lt_α3 hinside
    have hs_lt_α3 : s < bracket.α3 :=
      right_lt_of_negative_secantProduct bracket.α1_lt_α3 hinside
    have hUpdate : QuadraticInterpolationThreePointBracketUpdate bracket s nextBracket := by
      by_cases hα2_lt_s : bracket.α2 < s
      · by_cases hφ : φ bracket.α2 ≤ φ s
        · have hEq : bracket.rightKeepMiddle s hα2_lt_s hφ = nextBracket := by
            have hStep' :
                QuadraticInterpolationThreePointStepResult.continueWith
                    (bracket.rightKeepMiddle s hα2_lt_s hφ) =
                  QuadraticInterpolationThreePointStepResult.continueWith nextBracket := by
              simpa only [step, s,
                dif_neg (not_le_of_gt hinside), dif_neg hnotTol, dif_pos hα2_lt_s,
                dif_pos hφ] using hStep
            exact quadraticInterpolationThreePointStepResult_continueWith_injective hStep'
          cases hEq
          exact .rightKeepMiddle hα2_lt_s hs_lt_α3 hφ
        · have hEq : bracket.rightUseInterpolationPoint s hα2_lt_s hs_lt_α3 (lt_of_not_ge hφ) =
              nextBracket := by
            have hStep' :
                QuadraticInterpolationThreePointStepResult.continueWith
                    (bracket.rightUseInterpolationPoint s hα2_lt_s hs_lt_α3 (lt_of_not_ge hφ)) =
                  QuadraticInterpolationThreePointStepResult.continueWith nextBracket := by
              simpa only [step, s,
                dif_neg (not_le_of_gt hinside), dif_neg hnotTol, dif_pos hα2_lt_s,
                dif_neg hφ] using hStep
            exact quadraticInterpolationThreePointStepResult_continueWith_injective hStep'
          cases hEq
          exact .rightUseInterpolationPoint hα2_lt_s hs_lt_α3 (lt_of_not_ge hφ)
      · by_cases hs_lt_α2 : s < bracket.α2
        · by_cases hφ : φ bracket.α2 ≤ φ s
          · have hEq : bracket.leftKeepMiddle s hs_lt_α2 hφ = nextBracket := by
              have hStep' :
                  QuadraticInterpolationThreePointStepResult.continueWith
                      (bracket.leftKeepMiddle s hs_lt_α2 hφ) =
                    QuadraticInterpolationThreePointStepResult.continueWith nextBracket := by
                simpa only [step, s,
                  dif_neg (not_le_of_gt hinside), dif_neg hnotTol, dif_neg hα2_lt_s,
                  dif_pos hs_lt_α2, dif_pos hφ] using hStep
              exact quadraticInterpolationThreePointStepResult_continueWith_injective hStep'
            cases hEq
            exact .leftKeepMiddle hα1_lt_s hs_lt_α2 hφ
          · have hEq : bracket.leftUseInterpolationPoint s hα1_lt_s hs_lt_α2 (lt_of_not_ge hφ) =
                nextBracket := by
              have hStep' :
                  QuadraticInterpolationThreePointStepResult.continueWith
                      (bracket.leftUseInterpolationPoint s hα1_lt_s hs_lt_α2
                        (lt_of_not_ge hφ)) =
                    QuadraticInterpolationThreePointStepResult.continueWith nextBracket := by
                simpa only [step, s,
                  dif_neg (not_le_of_gt hinside), dif_neg hnotTol, dif_neg hα2_lt_s,
                  dif_pos hs_lt_α2, dif_neg hφ] using hStep
              exact quadraticInterpolationThreePointStepResult_continueWith_injective hStep'
            cases hEq
            exact .leftUseInterpolationPoint hα1_lt_s hs_lt_α2 (lt_of_not_ge hφ)
        · have hs_eq_α2 : s = bracket.α2 :=
            le_antisymm (le_of_not_gt hα2_lt_s) (le_of_not_gt hs_lt_α2)
          have htol : |s - bracket.α2| < ε := by
            rw [hs_eq_α2, sub_self, abs_zero]
            exact hε
          exact False.elim (hnotTol htol)
    exact ⟨by simpa [s] using hinside, by simpa [s] using hnotTol, by simpa [s] using hUpdate⟩
  · rintro ⟨hinside, hnotTol, hUpdate⟩
    have hUpdate' : QuadraticInterpolationThreePointBracketUpdate bracket s nextBracket := by
      simpa [s] using hUpdate
    cases hUpdate' with
    | rightKeepMiddle hα2_lt_αbar hαbar_lt_α3 hφ =>
        simp only [step, s, dif_neg (not_le_of_gt hinside),
          dif_neg hnotTol, dif_pos hα2_lt_αbar, dif_pos hφ]
    | rightUseInterpolationPoint hα2_lt_αbar hαbar_lt_α3 hφ =>
        simp only [step, s, dif_neg (not_le_of_gt hinside),
          dif_neg hnotTol, dif_pos hα2_lt_αbar, dif_neg (not_le_of_gt hφ)]
    | leftKeepMiddle hα1_lt_αbar hαbar_lt_α2 hφ =>
        simp only [step, s, dif_neg (not_le_of_gt hinside),
          dif_neg hnotTol, dif_neg (not_lt_of_ge hαbar_lt_α2.le), dif_pos hαbar_lt_α2,
          dif_pos hφ]
    | leftUseInterpolationPoint hα1_lt_αbar hαbar_lt_α2 hφ =>
        simp only [step, s, dif_neg (not_le_of_gt hinside),
          dif_neg hnotTol, dif_neg (not_lt_of_ge hαbar_lt_α2.le), dif_pos hαbar_lt_α2,
          dif_neg (not_le_of_gt hφ)]

end QuadraticInterpolationThreePointBracket
