/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Data.EReal.Basic
import Mathlib.LinearAlgebra.Dual.Defs

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Definition 2.9: the support function of a set `C ⊆ E` is the extended-real-valued function on
the dual space `E* = Module.Dual ℝ E` sending `y` to the supremum of the pairings `y x` for
`x ∈ C`. For nonempty `C`, this realizes the textbook codomain `(-∞, ∞]`. -/
noncomputable def support_function (C : Set E) : Module.Dual ℝ E → EReal :=
  fun y ↦ sSup ((fun x : E ↦ (y x : EReal)) '' C)

/-- Textbook notation for the dual-space support function `σ_C`. -/
notation "σ_ " C:arg => support_function C

/-- Evaluating the support function at `y` gives the supremum of the dual pairings `y x` over
`x ∈ C`. -/
@[simp]
lemma support_function_apply (C : Set E) (y : Module.Dual ℝ E) :
    support_function C y = sSup ((fun x : E ↦ (y x : EReal)) '' C) :=
  rfl

/-- Every point of `C` gives a lower bound on the support function of `C`. -/
theorem le_support_function_of_mem {C : Set E} {x : E} (hx : x ∈ C) (y : Module.Dual ℝ E) :
    (y x : EReal) ≤ support_function C y := by
  rw [support_function_apply]
  exact le_sSup ⟨x, hx, rfl⟩

/-- For a nonempty set `C`, the support function is strictly above `-∞`. -/
theorem bot_lt_support_function (C : Set E) (hC : C.Nonempty) (y : Module.Dual ℝ E) :
    ⊥ < support_function C y := by
  rcases hC with ⟨x, hx⟩
  rw [bot_lt_iff_ne_bot]
  intro hbot
  have hle : (y x : EReal) ≤ support_function C y := le_support_function_of_mem hx y
  rw [hbot] at hle
  exact EReal.coe_ne_bot (y x) (le_bot_iff.mp hle)

-- Proof sketch: choose `x ∈ C`; then `(y x : EReal)` belongs to the image set whose supremum
-- defines `support_function C y`, so `⊥ < (y x : EReal) ≤ support_function C y`, ruling out
-- the value `⊥`.
/-- For a nonempty set `C`, the support function never takes the value `-∞`. -/
theorem support_function_ne_bot (C : Set E) (hC : C.Nonempty) (y : Module.Dual ℝ E) :
    support_function C y ≠ ⊥ :=
  ne_of_gt (bot_lt_support_function C hC y)

/-- If the pairing image `y '' C` has greatest element `a`, then the support function of `C` at
`y` is exactly `a`. -/
theorem support_function_eq_of_isGreatest_image (C : Set E) (y : Module.Dual ℝ E) {a : EReal}
    (hmax : IsGreatest ((fun x : E ↦ (y x : EReal)) '' C) a) :
    support_function C y = a := by
  rw [support_function_apply]
  exact hmax.csSup_eq

end
