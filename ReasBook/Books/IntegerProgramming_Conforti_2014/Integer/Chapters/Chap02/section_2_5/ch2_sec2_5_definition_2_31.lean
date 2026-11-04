/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_definition_2_29.SAT
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_definition_2_31.ZeroOneILP

/-!
Satisfiability problem data and its `0/1` linear-feasibility translation.
-/

/- Definition 2.31 (1) [Satisfiability problem (SAT)]: the SAT problem on a finite clause family is
formalized by the decision-problem surface `SAT.Instance.decisionProblem`. -/

#check SAT.Instance.decisionProblem

/- Definition 2.31 (2) [Satisfiability problem (SAT)]: the equivalent `0/1` linear-feasibility
view `A x ≥ 1 - n(A)` is formalized by the translation `SAT.Instance.toZeroOneILP` together with
the satisfiability/feasibility equivalence theorem. -/

#check SAT.Instance.toZeroOneILP
#check SAT.Instance.satisfiable_iff_zeroOneILP_feasible
