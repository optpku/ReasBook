/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_5_definition_2_25.SetCovering

public section

/-!
Minimum cover problem for a Steiner triple system. For the Steiner-system incidence matrix `A`,
the set covering formulation is formalized by `SetCovering.feasibleSet A`, with objective
`SetCovering.cardinalityObjective` and attained-value set `SetCovering.objectiveValues A`.
This item reuses the generic set-covering owner from Definition 2.25 without introducing a
Steiner-specific wrapper.
-/

/- Definition 2.28 (Minimum cover problem for a Steiner triple system): given the incidence
matrix `A` of a Steiner triple system, the minimum cover problem `min { ∑ j, x j | x ∈ S^C(A) }`
is formalized by `SetCovering.feasibleSet A`, `SetCovering.cardinalityObjective`, and
`SetCovering.objectiveValues A`. -/

#check SetCovering.feasibleSet
#check SetCovering.mem_feasibleSet_iff
#check SetCovering.cardinalityObjective
#check SetCovering.objectiveValues

/- Definition 2.28 (Minimum cover problem for a Steiner triple system): a value `z` belongs to
`SetCovering.objectiveValues A` exactly when some feasible binary cover vector for the
Steiner-system incidence matrix `A` attains objective value `z`. This is the canonical companion
theorem for `SetCovering.objectiveValues`. -/
#check SetCovering.mem_objectiveValues_iff
