/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {α : Type*} [AddGroup α] [LinearOrder α]

/- Definition 6.4 is `source-facing`: domain sampling against Chapter 6's generic scalar
`soft_thresholding` owner in `Definition_6_2`, its coordinatewise lift in `Definition_6_3`, and
mathlib's generic absolute-value API shows that the primitive data here is only an ordered additive
group with `0`, `|·|`, and singleton sets. The owner abstraction is therefore the thresholding map
itself at that generic ordered layer, while the three branch formulas remain derived API. -/

/-- Definition 6.4: the hard-thresholding operator with threshold `a` sends `s` to `{0}` when
`|s| < a`, to `{s}` when `a < |s|`, and to `{0, s}` on the threshold `|s| = a`. -/
def hard_thresholding (a : α) : α → Set α :=
  fun s ↦
    if |s| < a then
      {0}
    else if a < |s| then
      {s}
    else
      {0, s}

end

@[inherit_doc] notation "𝓗[" a "]" => hard_thresholding a

section

variable {α : Type*} [AddGroup α] [LinearOrder α]

-- Proof sketch: evaluating `𝓗[a]` at `s` is exactly the defining three-branch formula.
/-- Evaluating the hard-thresholding operator gives its defining three-branch set-valued formula. -/
@[simp] theorem hard_thresholding_apply (a s : α) :
    𝓗[a] s = if |s| < a then {0} else if a < |s| then {s} else {0, s} :=
  rfl

-- Proof sketch: Unfold `hard_thresholding` and simplify the outer `if` using `h`.
/-- Hard thresholding returns only `0` below the threshold. -/
theorem hard_thresholding_of_abs_lt {a s : α} (h : |s| < a) :
    𝓗[a] s = {0} := by
  simp [hard_thresholding, h]

-- Proof sketch: Unfold `hard_thresholding`, use that the first branch is false by `h`, and then
-- simplify the second `if`.
/-- Hard thresholding returns only `s` above the threshold. -/
theorem hard_thresholding_of_lt_abs {a s : α} (h : a < |s|) :
    𝓗[a] s = {s} := by
  simp [hard_thresholding, h, not_lt_of_gt h]

-- Proof sketch: Unfold `hard_thresholding` and use the equality `|s| = a` to rule out the strict
-- inequality branches.
/-- Hard thresholding returns both `0` and `s` exactly on the threshold. -/
theorem hard_thresholding_of_abs_eq {a s : α} (h : |s| = a) :
    𝓗[a] s = {0, s} := by
  simp [hard_thresholding, h]

end
