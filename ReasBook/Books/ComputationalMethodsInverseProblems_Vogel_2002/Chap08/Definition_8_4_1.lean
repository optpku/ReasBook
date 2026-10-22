/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4_1.Approximation

public section

open scoped VariationalRegularization.Approximation

/-!
Definition 8.4-extra-2. Statement-stage check-only bridge.

This item is owned by the reusable Chapter 8 foundation module
`Book.Ch8.Definition_8_4_1.Approximation`, which introduces the generic dual
approximation functional `(8.76)` and the two concrete perturbations `(8.77)`
and `(8.78)` on the existing `L¹(Ω)` and admissible-test-field surfaces.

The current target file keeps only the labeled source-facing `#check` block so
later files can import the primitive API directly without redundant aliases.
-/

/- Definition 8.4-extra-2. Main labeled source-facing entry.

The reusable foundation module provides the three public owners for the generic
dual approximation and its `J_β` and `J_ε` specializations, together with their
defining formulas and specialization bridges. The `#check` commands below
record that source-facing API, including the reusable notation surface
`J_β` and `J_ε`, without adding wrapper declarations here. -/

#check VariationalRegularization.approximateTotalVariation
#check VariationalRegularization.approximateTotalVariation_def
#check J_β
#check VariationalRegularization.smoothNormApproxTotalVariation_def
#check VariationalRegularization.smoothNormApproxTotalVariation_eq_approximateTotalVariation
#check J_ε
#check VariationalRegularization.huberApproxTotalVariation_def
#check VariationalRegularization.huberApproxTotalVariation_eq_approximateTotalVariation
