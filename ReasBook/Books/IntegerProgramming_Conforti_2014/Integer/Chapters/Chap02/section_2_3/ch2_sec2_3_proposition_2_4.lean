/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_3.ch2_sec2_3_algorithm_2_1.Pricing
public import Mathlib.Order.Bounds.Basic

public section

namespace CuttingStockColumnGeneration

section Proposition_2_4

variable {m : ℕ}

/-- Full pricing-inequality feasibility on the full pattern family `S`. This is the source-facing
dual-feasibility predicate used in Proposition 2.4, expressed through the canonical pricing owner
`pricing_objective`. -/
def pricing_dual_feasible
    (S : Finset (Fin m → ℕ)) (u : Fin m → ℝ) : Prop :=
  ∀ s ∈ S, pricing_objective u s ≤ 1

/-- Unfolding characterization of `pricing_dual_feasible`. -/
@[simp] theorem pricing_dual_feasible_iff
    {S : Finset (Fin m → ℕ)} {u : Fin m → ℝ} :
    pricing_dual_feasible S u ↔
      ∀ s ∈ S, pricing_objective u s ≤ 1 :=
  Iff.rfl

/-- Proposition 2.4 (1). Full pricing-dual feasibility on `S` is equivalent to the pricing
objective values on `S` being bounded above by `1`. The restricted-master hypotheses from the
surrounding algorithmic context are redundant for this criterion, so the canonical statement
depends only on the full pattern family `S` and the dual vector `u`. This formalizes the source's
condition `max {∑ i, u i * s i : s ∈ S} ≤ 1` as
`1 ∈ upperBounds (pricing_objective_values S u)`. -/
theorem pricing_dual_feasible_iff_one_mem_upperBounds_pricing_objective_values
    {S : Finset (Fin m → ℕ)} {u : Fin m → ℝ} :
    pricing_dual_feasible S u ↔
      1 ∈ upperBounds (pricing_objective_values S u) := by
  constructor
  · intro hDual r hr
    rcases (mem_pricing_objective_values_iff).mp hr with ⟨s, hs, rfl⟩
    exact hDual s hs
  · intro hUpper s hs
    exact hUpper <| (mem_pricing_objective_values_iff).2 ⟨s, hs, rfl⟩

/-- If `pricing_objective u sStar` is the greatest pricing objective value on `S`, then every
pattern in `S` has pricing objective value at most `pricing_objective u sStar`. -/
theorem pricing_objective_le_of_isGreatest
    {S : Finset (Fin m → ℕ)} {u : Fin m → ℝ} {sStar s : Fin m → ℕ}
    (hmax : IsGreatest (pricing_objective_values S u) (pricing_objective u sStar))
    (hs : s ∈ S) :
    pricing_objective u s ≤ pricing_objective u sStar := by
  exact hmax.2 <| (mem_pricing_objective_values_iff).2 ⟨s, hs, rfl⟩

/-- If the greatest pricing objective value on `S` is strictly larger than `1`, then `u` is not
pricing-dual feasible on `S`. -/
theorem not_pricing_dual_feasible_of_isGreatest_gt_one
    {S : Finset (Fin m → ℕ)} {u : Fin m → ℝ} {sStar : Fin m → ℕ}
    (hmax : IsGreatest (pricing_objective_values S u) (pricing_objective u sStar))
    (hviol : 1 < pricing_objective u sStar) :
    ¬ pricing_dual_feasible S u := by
  intro hDual
  have hUpper :
      1 ∈ upperBounds (pricing_objective_values S u) :=
    (pricing_dual_feasible_iff_one_mem_upperBounds_pricing_objective_values).mp hDual
  exact (not_le_of_gt hviol) (hUpper hmax.1)

/-- Proposition 2.4 (2). If the pricing maximum on `S` is attained by `sStar` and is strictly
larger than `1`, then `u` is not pricing-dual feasible on `S`, and every pricing objective value
on `S` is bounded above by `pricing_objective u sStar`. The restricted-system hypotheses from the
surrounding algorithmic context are redundant for this pricing conclusion, so the canonical
statement keeps only the full-system data. -/
theorem mostViolatedConstraint_spec
    {S : Finset (Fin m → ℕ)} {u : Fin m → ℝ} {sStar : Fin m → ℕ}
    (hmax : IsGreatest (pricing_objective_values S u) (pricing_objective u sStar))
    (hviol : 1 < pricing_objective u sStar) :
    ¬ pricing_dual_feasible S u ∧
      ∀ s ∈ S, pricing_objective u s ≤ pricing_objective u sStar := by
  constructor
  · exact not_pricing_dual_feasible_of_isGreatest_gt_one hmax hviol
  · intro s hs
    exact pricing_objective_le_of_isGreatest hmax hs

end Proposition_2_4

end CuttingStockColumnGeneration
