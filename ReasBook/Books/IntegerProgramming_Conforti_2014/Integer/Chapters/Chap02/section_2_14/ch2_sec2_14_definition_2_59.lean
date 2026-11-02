module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_59.BinaryConstraint

namespace Definition_2_59

/-- The eight projects used in the source-specific specialization of Definition 2.59. -/
public inductive Project
  | A | B | C | D | E | F | G | H
deriving DecidableEq

/-- The full project set `{A, ..., H}` from Definition 2.59. -/
public def allProjects : Finset Project :=
  [Project.A, Project.B, Project.C, Project.D, Project.E, Project.F, Project.G, Project.H].toFinset

/-- The project set `{B, C}` used in Definition 2.59 (10). -/
public def projectsBC : Finset Project :=
  [Project.B, Project.C].toFinset

/-- The project set `{B, C, D, E}` used in Definition 2.59 (11). -/
public def projectsBCDE : Finset Project :=
  [Project.B, Project.C, Project.D, Project.E].toFinset

/-- The project set `{B, ..., H}` used in Definition 2.59 (12). -/
public def projectsBCDEFGH : Finset Project :=
  [Project.B, Project.C, Project.D, Project.E, Project.F, Project.G, Project.H].toFinset

section Definition_2_59

variable (x : Project → ℝ) (m : ℕ)

/-!
Definition 2.59 (Linear constraints for binary logical conditions).

The twelve textbook formulas for projects `A, ..., H` are specialized instances of the reusable
predicates in `BinaryConstraint`.
-/

/- Definition 2.59 (1): at most one of `A, ..., H`. -/
#check BinaryConstraint.atMostOne allProjects x

/- Definition 2.59 (2): exactly two of `A, ..., H`. -/
#check BinaryConstraint.exactly allProjects 2 x

/- Definition 2.59 (3): if `A`, then `B`. -/
#check BinaryConstraint.implies Project.A Project.B x

/- Definition 2.59 (4): if `A`, then not `B`. -/
#check BinaryConstraint.impliesNot Project.A Project.B x

/- Definition 2.59 (5): if not `A`, then `B`. -/
#check BinaryConstraint.notImplies Project.A Project.B x

/- Definition 2.59 (6): `A ↔ B`. -/
#check BinaryConstraint.equivalent Project.A Project.B x

/- Definition 2.59 (7): if `A`, then `B` and `C`. -/
#check BinaryConstraint.impliesBoth Project.A Project.B Project.C x

/- Definition 2.59 (8): if `A`, then `B` or `C`. -/
#check BinaryConstraint.impliesOneOf Project.A Project.B Project.C x

/- Definition 2.59 (9): if `B` or `C`, then `A`. -/
#check BinaryConstraint.eitherImplies Project.B Project.C Project.A x

/- Definition 2.59 (10): if `B` and `C`, then `A`. -/
#check BinaryConstraint.atLeastImplies 2 projectsBC Project.A x

/- Definition 2.59 (11): if two or more of `B, C, D, E`, then `A`. -/
#check BinaryConstraint.atLeastImplies 2 projectsBCDE Project.A x

/- Definition 2.59 (12): if at least `m` of `B, ..., H`, then `A`. -/
#check BinaryConstraint.atLeastImplies m projectsBCDEFGH Project.A x

end Definition_2_59
end Definition_2_59
