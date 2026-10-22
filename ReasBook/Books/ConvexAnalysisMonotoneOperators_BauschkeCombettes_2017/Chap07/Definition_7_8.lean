/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_49

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/- Definition 7.8: for a subset `C` of a real Hilbert space, the support function `σ_C` is the
canonical `EReal`-valued functional `u ↦ sup ⟪C | u⟫`, formalized in this project by
`innerSupremumOn C`. -/
recall innerSupremumOn {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
  (C : Set 𝓗) (u : 𝓗) : EReal

notation "σ[" C "]" => innerSupremumOn C

-- Proof sketch: this is exactly `innerSupremumOn_eq_sSup_image`, restated using the textbook
-- notation `σ[C]`.
/-- The support function `σ[C]` is the supremum of the image of `C` under the functional
`x ↦ ⟪x, u⟫`. -/
theorem supportFunction_eq_sSup_image (C : Set 𝓗) (u : 𝓗) :
    σ[C] u = sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) := by
  simp [innerSupremumOn_eq_sSup_image]

namespace ERealFunction

/-- The support function of a nonempty set never takes the value `-∞`. -/
theorem bot_lt_supportFunction_of_nonempty (C : Set 𝓗) (hC_nonempty : C.Nonempty) (u : 𝓗) :
    (⊥ : EReal) < σ[C] u := by
  rcases hC_nonempty with ⟨x, hx⟩
  rw [supportFunction_eq_sSup_image]
  exact lt_of_lt_of_le (EReal.bot_lt_coe _) <| (isLUB_sSup _).1 ⟨x, hx, rfl⟩

/-- The support function of a nonempty set is proper as an `EReal`-valued function. -/
theorem isProper_supportFunction_of_nonempty (C : Set 𝓗) (hC_nonempty : C.Nonempty) :
    IsProper (σ[C]) := by
  refine ⟨fun u ↦ ne_of_gt (bot_lt_supportFunction_of_nonempty C hC_nonempty u), ?_⟩
  refine ⟨0, ?_⟩
  simp [ERealFunction.dom, supportFunction_eq_sSup_image, hC_nonempty]

end ERealFunction
