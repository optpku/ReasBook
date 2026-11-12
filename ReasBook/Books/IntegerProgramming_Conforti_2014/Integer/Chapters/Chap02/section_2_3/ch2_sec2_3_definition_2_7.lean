/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_3.ch2_sec2_3_definition_2_7.Model
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_3.ch2_sec2_3_definition_2_7.Patterns

public section

/-!
Definition 2.7 is formalized by the reusable owner `CuttingStock.patterns`, the named
pattern-count carrier `CuttingStock.Assignment`, feasibility predicate `CuttingStock.feasible`,
feasible set `CuttingStock.feasibleSet`, and objective `CuttingStock.objective` in the item-local
foundation modules.
-/

/- Definition 2.7: define the cutting-pattern set `S`, the integer pattern-count variables indexed
by `S`, and the pattern-based cutting-stock feasibility/objective via the declarations below. -/
#check CuttingStock.patterns
#check CuttingStock.mem_patterns_iff
#check CuttingStock.Assignment
#check CuttingStock.feasible
#check CuttingStock.feasible_iff
#check CuttingStock.feasibleSet
#check CuttingStock.mem_feasibleSet_iff
#check CuttingStock.objective
#check CuttingStock.objective_eq_sum

end
