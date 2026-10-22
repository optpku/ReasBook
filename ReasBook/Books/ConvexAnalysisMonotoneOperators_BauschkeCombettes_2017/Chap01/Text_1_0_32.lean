/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

namespace EReal

variable {X : Type u}

/-- Text 1.0.32: addition on `EReal` with the textbook convention that the indeterminate sums
`+∞ + -∞` and `-∞ + +∞` are assigned the value `+∞`. -/
def sumWithTopBotAsTop : EReal → EReal → EReal
  | ⊤, ⊥ => ⊤
  | ⊥, ⊤ => ⊤
  | x, y => x + y

/-- Text 1.0.32: the textbook pointwise sum of two extended-real-valued functions is obtained by
applying the textbook extended-real addition convention pointwise. -/
abbrev pointwiseSum (f g : X → EReal) : X → EReal :=
  fun x ↦ sumWithTopBotAsTop (f x) (g x)

/-- Evaluating the textbook pointwise sum amounts to applying the textbook extended-real
addition convention at the chosen point. -/
@[simp] theorem pointwiseSum_apply (f g : X → EReal) (x : X) :
    pointwiseSum f g x = sumWithTopBotAsTop (f x) (g x) :=
  rfl

/-- The textbook addition convention is finite exactly when both inputs are finite real values. -/
theorem exists_real_eq_sumWithTopBotAsTop_iff {a b : EReal} :
    (∃ r : ℝ, sumWithTopBotAsTop a b = (r : EReal)) ↔
      (∃ s : ℝ, a = (s : EReal)) ∧ ∃ t : ℝ, b = (t : EReal) := by
  cases a <;> cases b
  case bot.bot =>
    change (∃ r : ℝ, (⊥ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊥ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊥ : EReal) = (t : EReal)
    simp
  case bot.coe b =>
    change (∃ r : ℝ, (⊥ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊥ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (b : EReal) = (t : EReal)
    simp
  case bot.top =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊥ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊤ : EReal) = (t : EReal)
    simp
  case coe.bot a =>
    change (∃ r : ℝ, (⊥ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (a : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊥ : EReal) = (t : EReal)
    simp
  case coe.coe a b =>
    change (∃ r : ℝ, (a : EReal) + (b : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (a : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (b : EReal) = (t : EReal)
    constructor
    · intro _
      exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    · intro _
      refine ⟨a + b, ?_⟩
      exact (EReal.coe_add a b).symm
  case coe.top a =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (a : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊤ : EReal) = (t : EReal)
    simp
  case top.bot =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊤ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊥ : EReal) = (t : EReal)
    simp
  case top.coe b =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊤ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (b : EReal) = (t : EReal)
    simp
  case top.top =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊤ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊤ : EReal) = (t : EReal)
    simp

end EReal
