/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_1

public section

/-!
Exercise 1.7 as source-facing canonical reuse.
-/

/- Exercise 1.7. Main labeled source-facing entry.

The local Chapter 1 theorem `tsvdSourceCondition_truncationErrorSq_le` is the
verified repository owner whose docstring explicitly identifies it with the
TSVD truncation estimate `(1.26)`. This exercise adds no new mathematical
owner beyond that theorem, so the `#check` below keeps the source-facing item
as a thin bridge to the existing canonical repository API instead of
introducing a redundant wrapper theorem.
-/
#check tsvdSourceCondition_truncationErrorSq_le
