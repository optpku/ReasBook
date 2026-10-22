/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SignType

section

variable {α : Type*} [Ring α] [LinearOrder α]

/- Definition 6.2 is `source-facing`: domain sampling against
`Mathlib.Data.Sign.Defs`, `Mathlib.Data.Sign.Basic`, and
`Mathlib.Algebra.Order.Group.PosPart` shows that the primitive scalar ingredients are already the
canonical upstream owners `sign` and `(·)⁺`. The new owner here is therefore only the
soft-thresholding map built from those generic ordered-ring primitives, while its piecewise
description remains derived API. -/

/-- Definition 6.2: the soft thresholding function with parameter `λ` is the map
`y ↦ (|y| - λ)⁺ * sign y`. -/
def soft_thresholding (lam : α) : α → α :=
  fun y ↦ (|y| - lam)⁺ * sign y

/-- Textbook notation for the soft thresholding operator. -/
notation "𝒯[" l "]" => soft_thresholding l

-- Proof sketch: unfold `soft_thresholding`; the statement is exactly the defining positive-part
-- and sign formula, so it follows by definitional reduction.
/-- Evaluating the soft-thresholding operator gives its defining positive-part/sign formula. -/
@[simp] theorem soft_thresholding_apply (lam y : α) :
    𝒯[lam] y = (|y| - lam)⁺ * sign y := rfl

end

section

variable {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]

-- Proof sketch: assume `0 ≤ λ` and split into the three regimes `λ ≤ y`, `|y| < λ`, and
-- `y ≤ -λ`. In each regime, simplify `( |y| - λ )⁺` and `sign y` to obtain the displayed
-- branch value.
/-- For a nonnegative threshold, soft thresholding has the usual three-branch piecewise
presentation. -/
theorem soft_thresholding_eq_piecewise {lam : α} (hlam : 0 ≤ lam) (y : α) :
    𝒯[lam] y =
      if lam ≤ y then y - lam else if |y| < lam then 0 else y + lam := by
  by_cases hly : lam ≤ y
  · have hy : 0 ≤ y := le_trans hlam hly
    by_cases hy0 : y = 0
    · have hlam0 : lam = 0 := le_antisymm (hy0 ▸ hly) hlam
      simp [soft_thresholding, hy0, hlam0]
    · have hyne : 0 ≠ y := by
        intro h0
        exact hy0 h0.symm
      have hypos : 0 < y := lt_of_le_of_ne hy hyne
      simp [soft_thresholding, hly, abs_of_nonneg hy, sign_pos hypos]
  · by_cases habs : |y| < lam
    · simp [soft_thresholding, hly, habs, posPart_of_nonpos (sub_nonpos.mpr habs.le)]
    · have hlamabs : lam ≤ |y| := le_of_not_gt habs
      have hyneg : y < 0 := by
        by_contra hy_nonneg
        exact hly (by simpa [abs_of_nonneg (le_of_not_gt hy_nonneg)] using hlamabs)
      have hyabs : |y| = -y := abs_of_neg hyneg
      have hneg : lam ≤ -y := by simpa [hyabs] using hlamabs
      calc
        𝒯[lam] y = (-y - lam) * (-1 : α) := by
          simp [soft_thresholding, hyabs, sign_neg hyneg,
            posPart_of_nonneg (sub_nonneg.mpr hneg)]
        _ = -(-y - lam) := by simp
        _ = y + lam := by abel_nf
        _ = if lam ≤ y then y - lam else if |y| < lam then 0 else y + lam := by
          simp [hly, habs]

end
