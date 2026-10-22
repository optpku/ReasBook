/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

/-- Multiplying a `]-∞,+∞]`-value by a positive real again yields a `]-∞,+∞]`-value. -/
-- Proof sketch: use `EReal.mul_ne_bot` for the product `(ξ : EReal) * x`, combining that real
-- coercions are neither `⊥` nor `⊤`, that `x` is not `⊥` by membership in `Set.Ioi ⊥`, and that a
-- positive real is nonnegative.
theorem adjoint_mul_mem_Ioi_bot (ξ : ℝ) (hξ : 0 < ξ) (x : Set.Ioi (⊥ : EReal)) :
    (⊥ : EReal) < (ξ : EReal) * (x : EReal) := by
  -- Turn the membership goal into the statement that the product is not `⊥`.
  rw [bot_lt_iff_ne_bot]
  -- Apply the characterization of when a product in `EReal` avoids the value `⊥`.
  exact (EReal.mul_ne_bot _ _).2
    ⟨Or.inl (EReal.coe_ne_bot ξ), Or.inr x.property.ne', Or.inl (EReal.coe_ne_top ξ),
      Or.inl (EReal.coe_nonneg.2 hξ.le)⟩

/-- The value `+∞` belongs to `]-∞,+∞]`. -/
-- Proof sketch: rewrite membership in `Set.Ioi (⊥ : EReal)` as the inequality `⊥ < ⊤`.
theorem top_mem_Ioi_bot : (⊤ : EReal) ∈ Set.Ioi (⊥ : EReal) := by
  -- Membership in `Set.Ioi (⊥ : EReal)` is exactly the strict inequality `⊥ < ⊤`.
  simp

/-- Text 8.0.1: the adjoint of `φ : ℝ → ]-∞,+∞]` is the function `φ*` defined by
`φ*(ξ) = ξ φ(1 / ξ)` for `ξ > 0` and `φ*(ξ) = +∞` otherwise. -/
noncomputable def adjoint (φ : ℝ → Set.Ioi (⊥ : EReal)) : ℝ → Set.Ioi (⊥ : EReal) :=
  fun ξ ↦
    if hξ : 0 < ξ then
      ⟨(ξ : EReal) * (φ (1 / ξ) : EReal), adjoint_mul_mem_Ioi_bot ξ hξ (φ (1 / ξ))⟩
    else
      ⟨(⊤ : EReal), top_mem_Ioi_bot⟩

/-- The positive branch of the adjoint definition evaluates to `ξ φ(1 / ξ)`. -/
-- Proof sketch: unfold `adjoint` and simplify the defining `if` using the hypothesis `0 < ξ`.
@[simp] theorem adjoint_apply_of_pos (φ : ℝ → Set.Ioi (⊥ : EReal)) {ξ : ℝ} (hξ : 0 < ξ) :
    (adjoint φ ξ : EReal) = (ξ : EReal) * (φ (1 / ξ) : EReal) := by
  -- Select the positive branch in the defining case split of `adjoint`.
  simp [adjoint, hξ]

/-- The nonpositive branch of the adjoint definition evaluates to `+∞`. -/
-- Proof sketch: unfold `adjoint` and simplify the defining `if` using `¬ 0 < ξ`, obtained from
-- the assumption `ξ ≤ 0`.
@[simp] theorem adjoint_apply_of_nonpos (φ : ℝ → Set.Ioi (⊥ : EReal)) {ξ : ℝ} (hξ : ξ ≤ 0) :
    (adjoint φ ξ : EReal) = ⊤ := by
  -- Select the nonpositive branch in the defining case split of `adjoint`.
  simp [adjoint, not_lt.mpr hξ]

end ERealFunction
