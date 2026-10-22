/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section RealVectorSpace

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

-- Proof sketch: if `x` is a global minimizer, then every positive directional difference quotient
-- at `x` is nonnegative, so their infimum is nonnegative. Conversely, if every directional
-- derivative at `x` is nonnegative, apply Proposition 17.2 (2) with direction `y - x` to get
-- `f x ≤ f y` for every `y`.
/-- Proposition 17.3: for a convex `]-∞,+∞]`-valued function, an effective-domain point `x` is a
global minimizer exactly when every directional derivative at `x` is nonnegative. -/
theorem mem_argmin_iff_nonneg_directionalDerivative
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    x ∈ Argmin f.asEReal ↔ ∀ y : H, 0 ≤ f′(x; y) := by
  constructor
  · intro hxmin y
    rw [mem_argmin_iff, isMinOn_univ_iff] at hxmin
    have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hfx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    rw [directionalDerivative]
    refine le_sInf ?_
    rintro _ ⟨α, rfl⟩
    dsimp [directionalDifferenceQuotient]
    have hnum : (0 : EReal) ≤ (f (x + (α : ℝ) • y) : EReal) - (f x : EReal) := by
      rw [EReal.sub_nonneg (Or.inr hfx_top) (Or.inr hfx_bot)]
      exact hxmin (x + (α : ℝ) • y)
    have hinv : (0 : EReal) ≤ (((α : ℝ)⁻¹ : ℝ) : EReal) := by
      exact_mod_cast inv_nonneg.mpr (le_of_lt α.2)
    rw [div_eq_mul_inv]
    exact mul_nonneg hnum hinv
  · intro hdir
    rw [mem_argmin_iff, isMinOn_univ_iff]
    intro y
    have hnonneg : (f x : EReal) ≤ f′(x; y - x) + (f x : EReal) := by
      simpa [add_comm, zero_add] using add_le_add_right (hdir (y - x)) (f x : EReal)
    exact hnonneg.trans (directionalDerivative_add_value_le f hconv hx y)

end RealVectorSpace

end ERealFunction
