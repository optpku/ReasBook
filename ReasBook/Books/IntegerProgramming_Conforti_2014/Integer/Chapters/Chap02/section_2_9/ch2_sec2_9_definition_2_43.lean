/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Image
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Objective
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_9.ch2_sec2_9_definition_2_42.FeasibleSet

open scoped BigOperators
open scoped MixingNotation

public section

/-!
Make-or-buy expected-cost mixed-integer linear program.

This item is formalized by the reusable objective `Mixing.makeOrBuyObjective` on the mixing-set
feasible region `MIX[b]`, together with the attained-value set
`Mixing.makeOrBuyObjectiveValues` and its canonical membership companion.
-/

namespace Mixing

variable {n : ℕ}

/-- The expected-cost objective `hy + c * ∑ i, p i * x_i` on a mixing-set point `xy`, where
`xy.1` is the purchase vector `x` and `xy.2 0` is the production amount `y`. This is the
source-facing specialization of `mixed_linear_objective` to one continuous variable with
continuous coefficient `h` and integer coefficients `c * p i`. -/
@[expose] def makeOrBuyObjective
    (h c : ℝ) (p : Fin n → ℝ) : MixedRealPoint n 1 → ℝ :=
  mixed_linear_objective (fun i ↦ c * p i) (fun _ ↦ h)

/-- `makeOrBuyObjective h c p` is the Chapter 1 mixed linear objective specialized to the
mixing-set cost coefficients. -/
theorem makeOrBuyObjective_eq_mixed_linear_objective
    (h c : ℝ) (p : Fin n → ℝ) :
    makeOrBuyObjective h c p =
      mixed_linear_objective (fun i ↦ c * p i) (fun _ ↦ h) :=
  rfl

/-- Unfolding equation for `makeOrBuyObjective`. -/
theorem makeOrBuyObjective_def
    (h c : ℝ) (p : Fin n → ℝ) (xy : MixedRealPoint n 1) :
    makeOrBuyObjective h c p xy = h * xy.2 0 + c * ∑ i, p i * xy.1 i := by
  rw [makeOrBuyObjective_eq_mixed_linear_objective, mixed_linear_objective_def]
  simp_rw [dotProduct, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp [add_comm]

/-- Definition 2.43 (Make-or-buy expected-cost mixed-integer linear program): the attainable
objective values of `makeOrBuyObjective h c p` on the mixing-set feasible region `MIX[b]`;
minimizing this set formalizes the make-or-buy MILP over `MIX`. -/
@[expose] def makeOrBuyObjectiveValues
    (h c : ℝ) (b p : Fin n → ℝ) : Set ℝ :=
  makeOrBuyObjective h c p '' MIX[b]

/-- Companion to Definition 2.43: a real number `r` belongs to
`makeOrBuyObjectiveValues h c b p` exactly when there is a feasible mixed point `xy ∈ MIX[b]`
whose expected cost under `makeOrBuyObjective h c p` is `r`. -/
theorem mem_makeOrBuyObjectiveValues_iff
    {h c : ℝ} {b p : Fin n → ℝ} {r : ℝ} :
    r ∈ makeOrBuyObjectiveValues h c b p ↔
      ∃ xy : MixedRealPoint n 1, xy ∈ MIX[b] ∧ makeOrBuyObjective h c p xy = r :=
  Iff.rfl

/-- Every feasible mixing-set point contributes its expected cost to
`makeOrBuyObjectiveValues h c b p`. -/
theorem makeOrBuyObjective_mem_values
    {h c : ℝ} {b p : Fin n → ℝ} {xy : MixedRealPoint n 1}
    (hxy : xy ∈ MIX[b]) :
    makeOrBuyObjective h c p xy ∈ makeOrBuyObjectiveValues h c b p :=
  ⟨xy, hxy, rfl⟩

/-- Helper for Definition 2.43: the explicit textbook make-or-buy cost of a feasible point
belongs to the attainable-value set. -/
theorem explicitCost_mem_makeOrBuyObjectiveValues
    {h c : ℝ} {b p : Fin n → ℝ} {xy : MixedRealPoint n 1}
    (hxy : xy ∈ MIX[b]) :
    h * xy.2 0 + c * ∑ i, p i * xy.1 i ∈ makeOrBuyObjectiveValues h c b p := by
  -- Rewrite the displayed textbook formula as the source-facing objective value.
  rw [← makeOrBuyObjective_def]
  -- Then package the feasible point as the image-set witness.
  exact makeOrBuyObjective_mem_values hxy

end Mixing

/- Definition 2.43 (Make-or-buy expected-cost mixed-integer linear program): the textbook MILP is
formalized by the expected-cost objective `Mixing.makeOrBuyObjective`, the feasible region
`MIX[b]`, and the attained-value set `Mixing.makeOrBuyObjectiveValues`. -/
#check Mixing.makeOrBuyObjective
#check Mixing.makeOrBuyObjective_def
#check Mixing.makeOrBuyObjectiveValues

/- Definition 2.43 (Make-or-buy expected-cost mixed-integer linear program): a real number `r`
belongs to `Mixing.makeOrBuyObjectiveValues h c b p` exactly when some feasible mixed point
`xy ∈ MIX[b]` attains objective value `r` under `Mixing.makeOrBuyObjective h c p`. This is the
canonical companion theorem for `Mixing.makeOrBuyObjectiveValues`. -/
#check Mixing.mem_makeOrBuyObjectiveValues_iff

end
