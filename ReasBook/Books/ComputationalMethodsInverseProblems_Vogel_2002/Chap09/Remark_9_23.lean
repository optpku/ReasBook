/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_30
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_5_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_5_1.Iteration
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_6.Projection

public section

/-! Statement-stage canonical anchors for Remark 9.23.

The source remark compares variational and iterative regularization only at the
level of qualitative tradeoffs. The current repository snapshot does not yet
contain verified Lean theorems for the full cost comparison, the modeling
flexibility claim, or the Richardson-Lucy/MRNSD zero-component persistence
statements. This file therefore records only checked backend anchors already
present in the repository or mathlib, without introducing a comparison theorem
or wrapper.
-/

/-
Remark 9.23.

In comparing variational and iterative regularization, the source poses a
qualitative question rather than a single theorem. The file therefore keeps the
remark as a clause-by-clause blocker/check surface, preserving the source
semantics while reusing only existing backend owners.
-/

/-
Source overview for Remark 9.23.

Clause `(1)` remains a qualitative blocker: Chapter 7 provides precise
parameter-choice owners, but the computational-cost comparison between solving
several variational problems and stopping an iteration is not itself a current
theorem surface.

Clause `(2)` also remains qualitative blocker prose. The source's flexibility
comparison about prior information, constraints, and likelihood-based
fit-to-data modeling is broader than any single existing owner in the current
repository snapshot.

Clause `(3)` is recorded only through a stronger/backend analogue for convex
minimizer uniqueness together with the existing Chapter 9 owners for the
Richardson-Lucy and MRNSD iteration surfaces, not as a verbatim formalization
of the source sentence.
-/

/- Remark 9.23 (1). Backend anchor for the Chapter 7 a posteriori
regularization-parameter selection language mentioned in the source. The
computational-cost comparison itself remains qualitative and is not formalized
here. -/
#check ParameterChoice.IsOrderOptimal

/- Remark 9.23 (2). Backend anchor for the constraint-handling side of the
source's flexibility comparison. The broader claim about prior information,
constraints, and likelihood-based fit-to-data modeling remains qualitative and
is not packaged by a single current owner. -/
#check EuclideanProjection.proj

/- Remark 9.23 (3). Stronger backend analogue: under strict convexity on a
convex feasible set, a variational minimizer is unique. This is stronger than,
and not identical to, the source's prose claim about independence from the
initial guess. -/
#check StrictConvexOn.eq_of_isMinOn

/-
Remark 9.23 (3), iterative side.

The repository already has canonical Chapter 9 owners for the Richardson-Lucy
one-step update and the recursive MRNSD iterate family. What is still missing
is the source-facing zero-component persistence theorem for those owners, so
the file records only the existing iterative surfaces rather than a guessed
persistence statement.
-/
#check RichardsonLucy.update

/- Backend recursive iterate owner for the MRNSD side of the same warning. -/
#check Mrnsd.iterates

/- Companion validity predicate for MRNSD boundary-minimum and step-size data. -/
#check Mrnsd.IsIterateSequence
