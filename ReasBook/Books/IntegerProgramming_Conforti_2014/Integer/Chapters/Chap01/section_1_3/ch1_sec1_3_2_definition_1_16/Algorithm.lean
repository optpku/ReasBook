/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_11.Problem

@[expose] public section

namespace Problem

/-- A deterministic algorithm for `P` consists of an explicit correct-output procedure on every
valid instance of `P` together with an explicit finite step-count witness for each instance. -/
structure Algorithm (P : Problem) where
  solve : (i : P.instanceOf) → P.answers i
  runTime : P.instanceOf → Nat

namespace Algorithm

variable {P : Problem}

/-- Build an algorithm for `P` from an explicit solver and an explicit running-time function. -/
def ofSolver
    (solve : (i : P.instanceOf) → P.answers i)
    (runTime : P.instanceOf → Nat) :
    Algorithm P where
  solve := solve
  runTime := runTime

/-- `ofSolver` returns the solver used to build the algorithm. -/
@[simp] theorem ofSolver_solve
    (solve : (i : P.instanceOf) → P.answers i)
    (runTime : P.instanceOf → Nat)
    (i : P.instanceOf) :
    (ofSolver solve runTime).solve i = solve i :=
  rfl

/-- `ofSolver` returns the running-time function used to build the algorithm. -/
@[simp] theorem ofSolver_runTime
    (solve : (i : P.instanceOf) → P.answers i)
    (runTime : P.instanceOf → Nat)
    (i : P.instanceOf) :
    (ofSolver solve runTime).runTime i = runTime i :=
  rfl

/-- Every admissible instance of `P` has a correct answer whenever `P` is equipped with an
algorithm. -/
theorem exists_output
    (algorithm : Algorithm P)
    (i : P.instanceOf) :
    Nonempty (P.answers i) :=
  ⟨algorithm.solve i⟩

end Algorithm

end Problem

end
