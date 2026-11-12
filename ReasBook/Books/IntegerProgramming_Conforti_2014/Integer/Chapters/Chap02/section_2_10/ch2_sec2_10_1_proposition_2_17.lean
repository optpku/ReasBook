/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic

public section

open scoped BigOperators

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_10/ch2_sec2_10_1_proposition_2_17.lean.
Proposition 2.17 [Disaggregated constraints imply the aggregated constraint].
For a fixed facility column `j`, if every entry of that column satisfies `y i ≤ x`, then
the aggregated inequality `∑ i : Fin m, y i ≤ (m : ℝ) * x` holds. -/
theorem columnSum_le_scaledOpen_of_assignment_le_open
    {m : ℕ}
    {x : ℝ}
    {y : Fin m → ℝ}
    (h_assign : ∀ i : Fin m, y i ≤ x) :
    ∑ i : Fin m, y i ≤ (m : ℝ) * x := by
  -- Sum the pointwise assignment bounds over the facility column.
  have h_sum : (∑ i : Fin m, y i) ≤ ∑ _ : Fin m, x :=
    Finset.sum_le_sum fun i _ ↦ h_assign i
  -- The constant sum has `m` terms, so it is the claimed scaled bound.
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h_sum

end
