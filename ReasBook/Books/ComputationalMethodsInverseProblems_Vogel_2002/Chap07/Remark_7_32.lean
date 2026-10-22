/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_10.Filters
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Order.Filter.Extr

public section

/-!
Remark 7.32 (TSVD L-curve blocker).

This source item is qualitative. It explains that the usual derivative-based
L-curve method does not directly apply to TSVD because the scalar filter
`SpectralFilter.tsvd` has jump discontinuities. It then says that one may
replace derivatives by discrete differences, derive TSVD analogues of the
auxiliary quantities `R`, `S`, and `S'`, and under assumptions analogous to
`(7.109)`-`(7.112)` prove either that the TSVD L-curve becomes very flat or
that the corner choice `m_L` does not yield mean square convergence.

A source-faithful Lean theorem is blocked in the current repo snapshot: there
is no verified Chapter 7 owner here for the TSVD L-curve objective, its
discrete-difference curvature replacement, the auxiliary quantities `R`, `S`,
and `S'`, or the corner index `m_L` together with its source-specific expected
squared estimation-error sequence. Introducing surrogate local definitions or a
generic theorem about arbitrary discontinuous filters would drift from the
source semantics. This file therefore records only the verified backend anchors
already present in the project and mathlib: the base and discrete TSVD filter
owners, the generic forward-difference operator, maximizer language, and the
Chapter 7 mean-square convergence predicate.
-/

/- Remark 7.32. The source-faithful TSVD L-curve statement is not yet ready to
formalize in this repo snapshot because the Chapter 7 owners for the
discrete-difference TSVD curvature setup, the analogous quantities `R`, `S`,
and `S'`, and the corner index `m_L` with its induced expected-error sequence
are still missing. The `#check` block below records only the canonical anchors
that a later precise formulation should reuse. -/

#check SpectralFilter.tsvd
#check SpectralFilter.discreteTsvd
#check fwdDiff
#check IsMaxOn
#check ParameterChoice.IsMeanSquareConvergent
