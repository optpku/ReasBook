/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {X : Type u}

/-- Text 1.0.31: the effective domain of an extended-real-valued function is the set of points
at which the function takes a finite value. Equivalently, it is the preimage of the open interval
`Ioo ⊥ ⊤`, i.e. the points where the value is neither `+∞` nor `-∞`. -/
def effectiveDom (f : X → EReal) : Set X :=
  f ⁻¹' Set.Ioo (⊥ : EReal) ⊤

/-- A point lies in the effective domain exactly when the function value there is finite, i.e. it
is neither `+∞` nor `-∞`. -/
@[simp] theorem mem_effectiveDom_iff (f : X → EReal) (x : X) :
    x ∈ effectiveDom f ↔ f x ≠ ⊤ ∧ f x ≠ ⊥ := by
  rw [effectiveDom, Set.mem_preimage, Set.mem_Ioo, bot_lt_iff_ne_bot, lt_top_iff_ne_top]
  constructor
  · intro hx
    exact ⟨hx.2, hx.1⟩
  · intro hx
    exact ⟨hx.2, hx.1⟩

/-- A point lies in the effective domain exactly when the function value there comes from a real
number via the canonical coercion `ℝ → EReal`. -/
theorem mem_effectiveDom_iff_exists_real (f : X → EReal) (x : X) :
    x ∈ effectiveDom f ↔ ∃ r : ℝ, f x = (r : EReal) := by
  constructor
  · intro hx
    rcases (mem_effectiveDom_iff f x).1 hx with ⟨h_top, h_bot⟩
    exact ⟨(f x).toReal, (EReal.coe_toReal h_top h_bot).symm⟩
  · rintro ⟨r, hr⟩
    simp [mem_effectiveDom_iff, hr]

/-- The effective domain is the part of the ordinary domain where the function also avoids
`-∞`. -/
theorem effectiveDom_eq_dom_inter_neBot (f : X → EReal) :
    effectiveDom f = dom f ∩ {x | f x ≠ ⊥} := by
  ext x
  rw [Set.mem_inter_iff, Set.mem_setOf_eq, mem_effectiveDom_iff, mem_dom_iff, lt_top_iff_ne_top]

end ERealFunction
