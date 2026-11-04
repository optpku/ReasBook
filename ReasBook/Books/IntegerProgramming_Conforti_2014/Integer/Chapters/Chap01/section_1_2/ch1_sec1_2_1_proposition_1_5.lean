/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Set.Image
public import Mathlib.Order.Bounds.Defs
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace

public section

section Proposition15

/-- Proposition 1.5 (1). If an LP-optimal point for `P_i` already lies in `S_i ⊆ P_i`, then it is
also optimal for the restricted subproblem on `S_i`, in the sense that it realizes the greatest
objective value on `S_i`. -/
theorem lpOptimalPointInSubsetIsMilpOptimal
    {n p : ℕ}
    (P_i S_i : Set (MixedRealPoint n p))
    (objective : MixedRealPoint n p → ℝ)
    (xy_i : MixedRealPoint n p)
    (h_subset : S_i ⊆ P_i)
    (h_lp_opt : IsGreatest (objective '' P_i) (objective xy_i))
    (h_mem : xy_i ∈ S_i) :
    xy_i ∈ S_i ∧
      IsGreatest (objective '' S_i) (objective xy_i) := by
  refine ⟨h_mem, ?_⟩
  refine ⟨⟨xy_i, h_mem, rfl⟩, ?_⟩
  rintro _ ⟨y, hyS, rfl⟩
  exact h_lp_opt.2 ⟨y, h_subset hyS, rfl⟩

/-- Proposition 1.5 (1) companion. Restricting the feasible set while keeping the LP-optimal point
preserves the greatest attained objective value. -/
theorem lpOptimalPointInSubsetObjectiveIsGreatest
    {n p : ℕ}
    (P_i S_i : Set (MixedRealPoint n p))
    (objective : MixedRealPoint n p → ℝ)
    (xy_i : MixedRealPoint n p)
    (h_subset : S_i ⊆ P_i)
    (h_lp_opt : IsGreatest (objective '' P_i) (objective xy_i))
    (h_mem : xy_i ∈ S_i) :
    IsGreatest (objective '' S_i) (objective xy_i) :=
  (lpOptimalPointInSubsetIsMilpOptimal
    P_i S_i objective xy_i h_subset h_lp_opt h_mem).2

/-- Proposition 1.5 (2). Under the same hypotheses, the restricted subproblem on `S_i` attains
the objective value `z_i = objective xy_i`. -/
theorem lpOptimalPointInSubsetHasMilpValue
    {n p : ℕ}
    (P_i S_i : Set (MixedRealPoint n p))
    (objective : MixedRealPoint n p → ℝ)
    (xy_i : MixedRealPoint n p)
    (z_i : ℝ)
    (h_subset : S_i ⊆ P_i)
    (h_lp_opt : IsGreatest (objective '' P_i) (objective xy_i))
    (h_mem : xy_i ∈ S_i)
    (hz : z_i = objective xy_i) :
    IsGreatest (objective '' S_i) z_i := by
  simpa [hz] using
    lpOptimalPointInSubsetObjectiveIsGreatest P_i S_i objective xy_i h_subset h_lp_opt h_mem

end Proposition15
