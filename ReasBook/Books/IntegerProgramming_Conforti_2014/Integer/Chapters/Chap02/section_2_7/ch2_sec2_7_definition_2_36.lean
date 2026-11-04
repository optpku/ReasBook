/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_definition_2_36.MTZ

/-!
Definition 2.36: Miller-Tucker-Zemlin (MTZ) formulation for the asymmetric traveling salesman
problem.

This item is formalized by the reusable formulation declarations
`AsymmetricTravelingSalesmanProblem.mtzFeasible`,
`AsymmetricTravelingSalesmanProblem.mtzObjective`, and
`AsymmetricTravelingSalesmanProblem.mtzObjectiveValues`.
-/

universe u w

namespace AsymmetricTravelingSalesmanProblem

variable {V : Type u} {A : Type w}

section Definition_2_36

variable [Fintype V] [Fintype A]

/-- Definition 2.36 (Miller--Tucker--Zemlin (MTZ) formulation for ATSP): a real number `r`
belongs to `AsymmetricTravelingSalesmanProblem.mtzObjectiveValues P root` exactly when there are
arc variables `x : A → ℝ` and potential variables `u : V → ℝ` such that
`AsymmetricTravelingSalesmanProblem.mtzFeasible P root x u` holds and
`AsymmetricTravelingSalesmanProblem.mtzObjective P x = r`. The textbook distinguished vertex `1`
is represented by the explicit parameter `root`, and the constant `n` is represented by
`Fintype.card V` inside `AsymmetricTravelingSalesmanProblem.mtzFeasible P root x u`. -/
theorem mem_mtzObjectiveValues_iff
    {P : AsymmetricTravelingSalesmanProblem V A} {root : V} {r : ℝ} :
    r ∈ P.mtzObjectiveValues root ↔
      ∃ x : A → ℝ, ∃ u : V → ℝ, P.mtzFeasible root x u ∧ P.mtzObjective x = r := by
  constructor
  · intro hr
    -- Unfold the set membership once to expose the existential witnesses.
    change ∃ x : A → ℝ, ∃ u : V → ℝ, P.mtzFeasible root x u ∧ P.mtzObjective x = r at hr
    exact hr
  · rintro ⟨x, u, h_feasible, h_objective⟩
    -- Package the feasible variables and realized objective value into set membership.
    change ∃ x : A → ℝ, ∃ u : V → ℝ, P.mtzFeasible root x u ∧ P.mtzObjective x = r
    exact ⟨x, u, h_feasible, h_objective⟩

end Definition_2_36

end AsymmetricTravelingSalesmanProblem
