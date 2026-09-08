module

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact decrease ratios for translated quadratics

The identity in this file separates the quadratic part of an objective
decrease from a prescribed correction to its gradient.  It is independent of
any particular DFP orbit or interpolation construction.
-/

public section

universe u

namespace DFP

/-- If an objective agrees with a translated half squared norm at two points
and its reference gradient splits into the quadratic displacement plus a
correction, then its exact decrease ratio has the corresponding quadratic and
correction terms. -/
theorem decreaseRatio_eq_one_sub_normSq_add_correction
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (C x xnext g correction : E)
    (hvalue : f x = (1 / 2 : ℝ) * ‖x - C‖ ^ 2)
    (hvalueNext : f xnext = (1 / 2 : ℝ) * ‖xnext - C‖ ^ 2)
    (hgradient : x - C = g - correction) :
    let s := xnext - x
    let q := -inner ℝ g s
    0 < q →
      (f x - f xnext) / q =
        1 - ‖s‖ ^ 2 / (2 * q) + inner ℝ correction s / q := by
  dsimp only
  intro hq
  have hinnerNe : inner ℝ g (xnext - x) ≠ 0 := by
    intro hzero
    rw [hzero] at hq
    norm_num at hq
  have hnextTranslated : xnext - C = (x - C) + (xnext - x) := by
    abel
  rw [hvalue, hvalueNext, hnextTranslated, norm_add_sq_real,
    hgradient, inner_sub_left]
  field_simp [hinnerNe]
  ring

end DFP
