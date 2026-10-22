/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H]

/-- Helper for Definition 9.28: subtracting a finite effective-domain value from any value of `f`
still stays strictly above `-∞`. -/
private lemma recession_increment_gt_bot_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H} (hx : x ∈ effectiveDomain f) :
    ⊥ < ((f (x + y) : EReal) - (f x : EReal)) := by
  -- The denominator is finite because `x` lies in the effective domain.
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hxy_bot : (f (x + y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + y) : EReal) from (f (x + y)).2)
  by_cases hxy_top : (f (x + y) : EReal) = ⊤
  · -- If the translated value is `⊤`, then the increment is `⊤`.
    rw [hxy_top, EReal.top_sub hx_top]
    simp
  · -- Otherwise both terms are finite, so the increment is a real cast.
    rw [← EReal.coe_toReal hxy_top hxy_bot, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_sub]
    exact EReal.bot_lt_coe _

/-- The supremum defining the recession function is still strictly above `-∞` when the effective
domain is nonempty. -/
-- Proof sketch: use a point of the nonempty effective domain to obtain one finite increment
-- `f (x + y) - f x`, then compare that increment with the defining supremum.
theorem recessionFunction_sup_gt_bot (f : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty) (y : H) :
    ⊥ < sSup ((fun x : H ↦ (f (x + y) : EReal) - (f x : EReal)) '' effectiveDomain f) := by
  rcases hdom with ⟨x, hx⟩
  -- The witness `x` contributes one increment that is already above `-∞`.
  have hinc : ⊥ < ((f (x + y) : EReal) - (f x : EReal)) :=
    recession_increment_gt_bot_of_mem_effectiveDomain f hx
  have hle :
      ((f (x + y) : EReal) - (f x : EReal)) ≤
        sSup ((fun x : H ↦ (f (x + y) : EReal) - (f x : EReal)) '' effectiveDomain f) := by
    -- Realizing one image point gives a lower bound for the defining supremum.
    exact (isLUB_sSup _).1 ⟨x, hx, rfl⟩
  -- Comparing the witness with the supremum shows that the supremum is also above `-∞`.
  exact lt_of_lt_of_le hinc hle

/-- Definition 9.28: the recession function sends `y` to the supremum of the translated increments
`f (x + y) - f x` over the effective domain of `f`. -/
noncomputable def recessionFunction (f : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty) : H → Set.Ioi (⊥ : EReal) :=
  fun y ↦
    ⟨sSup ((fun x : H ↦ (f (x + y) : EReal) - (f x : EReal)) '' effectiveDomain f),
      recessionFunction_sup_gt_bot f hdom y⟩

/-- The value of the recession function is the supremum of the translated increments over the
effective domain. -/
-- Proof sketch: unfold `recessionFunction`; the coercion to `EReal` forgets only the proof that the
-- defining supremum is strictly above `-∞`.
@[simp] theorem recessionFunction_apply (f : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty) (y : H) :
    (recessionFunction f hdom y : EReal) =
      sSup ((fun x : H ↦ (f (x + y) : EReal) - (f x : EReal)) '' effectiveDomain f) := by
  -- Unfolding the subtype-valued definition leaves exactly the stored supremum.
  rfl

end ERealFunction
