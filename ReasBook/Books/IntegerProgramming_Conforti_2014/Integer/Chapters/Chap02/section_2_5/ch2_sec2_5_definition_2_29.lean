/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_definition_2_29.SAT

public section

/-!
Primitive SAT/CNF vocabulary reused from the item-owned `SAT` owner.
-/

/- Definition 2.29 (1) [Clauses and CNF]: literals in the variables `x_1, ..., x_n` are
formalized by `SAT.Literal`. -/

#check SAT.Literal

/- Definition 2.29 (2) [Clauses and CNF]: a clause is formalized by `SAT.Clause`, the finite
family of literals used by the local SAT API. -/

#check SAT.Clause

/- Definition 2.29 (3) [Clauses and CNF]: truth assignments are represented by
`τ : Fin n → Bool`, and clause satisfaction by such an assignment is formalized by
`SAT.Clause.satisfiedBy`. -/

#check SAT.Clause.satisfiedBy

/- Definition 2.29 (4) [Clauses and CNF]: a CNF formula, viewed as a finite conjunction/family of
clauses, is formalized by `SAT.Instance`. -/

#check SAT.Instance
