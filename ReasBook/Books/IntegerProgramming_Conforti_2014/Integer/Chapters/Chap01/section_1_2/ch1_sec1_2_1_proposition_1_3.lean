/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_1_proposition_1_3.OptimalValue

public section

universe u

/-- Proposition 1.3 (Optimal value decomposition): if `S = S₁ ∪ S₂`, then the lifted optimal
value on `S` is the maximum of the lifted optimal values on `S₁` and `S₂`, where `⊥ : EReal`
renders the source convention `max ∅ = -∞`. The source states this for a disjoint partition, but
that hypothesis is redundant for the resulting equality. -/
theorem optimalValue_eq_max_of_partition
    {α : Type u} (f : α → ℝ) {S S₁ S₂ : Set α}
    (h_partition : S = S₁ ∪ S₂) :
    optimalValue f S = max (optimalValue f S₁) (optimalValue f S₂) := by
  rw [h_partition]
  exact optimalValue_union_eq_max f S₁ S₂
