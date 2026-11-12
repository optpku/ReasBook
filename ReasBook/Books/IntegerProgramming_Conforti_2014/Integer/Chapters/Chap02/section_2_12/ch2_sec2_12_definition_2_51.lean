/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_12.ch2_sec2_12_definition_2_51.Problem

public section

/-!
`0`--`1` polynomial programming.

Definition 2.51 is formalized by the reusable owner `ZeroOnePolynomialProgram`, together with its
canonical constructor, feasible-set predicate, polynomial objective evaluation, and attained-value
set in the item-local foundation module.
-/

/- Definition 2.51 (0--1 polynomial program): the optimization data consisting of one objective
polynomial `f`, equality-constraint polynomials `g_i`, and binary variables `x_j ∈ {0, 1}` is
formalized by the declarations below. -/
#check ZeroOnePolynomialProgram
#check ZeroOnePolynomialProgram.ofPolynomials
#check ZeroOnePolynomialProgram.feasibleSet
#check ZeroOnePolynomialProgram.mem_feasibleSet_iff
#check ZeroOnePolynomialProgram.objectiveValue
#check ZeroOnePolynomialProgram.objectiveValue_def
#check ZeroOnePolynomialProgram.objectiveValues
#check ZeroOnePolynomialProgram.mem_objectiveValues_iff

end
