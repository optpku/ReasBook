/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_3.LICQ

public section

/-
Definition 9.3. For a feasible point `f` of `(9.9)`, the linear independence
constraint qualification at the source-facing textbook layer is formalized by
`ConstraintQualification.IsRegularPoint c f`, which expands to
`ConstraintQualification.SatisfiesLICQ c (ActiveSet.active c) f`. The core owner
`ConstraintQualification.SatisfiesLICQ c active f` remains available for a
general active-index selector `active`.
-/
#check ConstraintQualification.IsRegularPoint

/-
Companion checks for the generalized LICQ owner and the source-facing bridge to
the active-set formulation.
-/
#check ConstraintQualification.SatisfiesLICQ
#check ConstraintQualification.isRegularPoint_iff_satisfiesLICQ
