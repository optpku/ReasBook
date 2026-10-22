/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_14.BV
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_18.Comparison
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_19.Objective
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_20.Minimizer

public section

noncomputable section

/-!
Theorem 8.21. Statement-stage blocker.

The source theorem is organized around equation `(8.74)` and its transport
between the Chapter 8 `L^p(Ω)` surface and the `L¹(Ω)`/`BV(Ω)` total-
variation surface.

In the current repository snapshot, the exact Lean owner of `(8.74)` has not
yet been anchored, and the required `L^p(Ω) → L¹(Ω) → BV(Ω)` passage is only
available through reusable helper constructions rather than a verified
source-facing theorem statement. Promoting this item to a concrete theorem
over `tvRegularizedLeastSquaresFunctional K g α`, together with a surrogate
hypothesis such as `K 1 ≠ 0`, would therefore drift from the source semantics
and from the recorded statement-stage blocker state.

Accordingly, this file remains a labeled check-only blocker entry until the
exact owner of `(8.74)` and its inherited parameter surface are recovered.
-/

namespace VariationalRegularization

variable {d : ℕ}

/- Theorem 8.21. Main labeled source-facing blocker entry.

The exact Lean owner of equation `(8.74)` is still unresolved in this repair
scope. What is already verified in the current repository is the surrounding
transport surface:
`lpToL1 : L^p(Ω) → L¹(Ω)`, the Chapter 8 bounded-variation owner `BV(Ω)` with
its constructor `BV.ofLp`, the identity `BV.ofLp_toL1`, and the nearby
TV-regularized minimizer predicates built over the provisional helper
`tvRegularizedLeastSquaresFunctional`.

These `#check` commands therefore record only the reusable backend anchors for
that unresolved source-facing theorem surface. They do not identify
`tvRegularizedLeastSquaresFunctional K g α` as the exact source owner of
`(8.74)`, and they do not replace the missing inherited parameter/nullspace
surface by a guessed hypothesis such as `K 1 ≠ 0`. -/

#check lpToL1
#check BV
#check BV.ofLp
#check BV.ofLp_toL1
#check tvRegularizedLeastSquaresFunctional
#check IsTvRegularizedMinimizer
#check IsUniqueTvRegularizedMinimizer

end VariationalRegularization
