/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/-- Example 20.9: the rotation `x ↦ x + r (mod 1)` on `[0,1)` is ergodic exactly when `r` is
irrational; equivalently, translation by `r` on `AddCircle 1` is ergodic exactly when `r` is
irrational. -/
-- Proof sketch: rewrite the system on `[0,1)` as translation on `AddCircle 1`, then combine
-- `AddCircle.ergodic_add_right` with the characterization of infinite additive order on the
-- additive circle by irrationality of the translation parameter.
theorem mod_one_rotation_ergodic_iff_irrational (r : ℝ) :
    Ergodic ((· + (r : AddCircle (1 : ℝ)))) volume ↔ Irrational r := by
  simpa [AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div, Irrational] using
    (show Ergodic ((· + (r : AddCircle (1 : ℝ)))) ↔ addOrderOf (r : AddCircle (1 : ℝ)) = 0 from
      AddCircle.ergodic_add_right)
