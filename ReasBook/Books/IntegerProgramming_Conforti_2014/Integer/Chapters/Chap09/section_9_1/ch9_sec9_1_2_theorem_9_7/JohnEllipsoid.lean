/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators InnerProductSpace

noncomputable section

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: finite contact
data expressing the balance and reconstruction identities used in John's ellipsoid theorem. -/
structure JohnContactSystem
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n r : ℕ) where
  contact : Fin r → E
  weight : Fin r → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  contact_norm : ∀ i, ‖contact i‖ = 1
  balance : ∑ i, weight i • contact i = 0
  weight_sum : ∑ i, weight i = n
  reconstruct : ∀ x, x = ∑ i, (weight i * ⟪x, contact i⟫_ℝ) • contact i

namespace JohnContactSystem

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7/JohnEllipsoid.lean`: balancing the
weighted contacts makes every corresponding weighted inner-product sum vanish. -/
lemma weightedInnerSum_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n r : ℕ}
    (system : JohnContactSystem E n r)
    (x : E) :
    ∑ i, system.weight i * ⟪x, system.contact i⟫_ℝ = 0 := by
  -- Pair the balance identity with `x` and distribute the inner product over the sum.
  calc
    ∑ i, system.weight i * ⟪x, system.contact i⟫_ℝ =
        ⟪x, ∑ i, system.weight i • system.contact i⟫_ℝ := by
          simp only [inner_sum, inner_smul_right]
    _ = 0 := by rw [system.balance, inner_zero_right]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7/JohnEllipsoid.lean

A point lying below every contact supporting hyperplane has norm at most the total John weight. -/
theorem norm_le_of_inner_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n r : ℕ}
    (system : JohnContactSystem E n r)
    (x : E)
    (hx : ∀ i, ⟪x, system.contact i⟫_ℝ ≤ 1) :
    ‖x‖ ≤ n := by
  have hshift :
      x = ∑ i, (system.weight i * (⟪x, system.contact i⟫_ℝ - 1)) •
        system.contact i := by
    -- Subtract the balanced contact sum from the reconstruction identity.
    calc
      x = ∑ i, (system.weight i * ⟪x, system.contact i⟫_ℝ) • system.contact i :=
        system.reconstruct x
      _ =
          (∑ i, (system.weight i * ⟪x, system.contact i⟫_ℝ) • system.contact i) -
            ∑ i, system.weight i • system.contact i := by rw [system.balance, sub_zero]
      _ = ∑ i, (system.weight i * (⟪x, system.contact i⟫_ℝ - 1)) •
          system.contact i := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← sub_smul]
            congr 1
            ring
  have hcoefficient_nonpos (i : Fin r) :
      system.weight i * (⟪x, system.contact i⟫_ℝ - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (system.weight_nonneg i) (sub_nonpos.mpr (hx i))
  have hinner_sum :
      ∑ i, system.weight i * ⟪x, system.contact i⟫_ℝ = 0 :=
    system.weightedInnerSum_eq_zero x
  have hcoefficient_sum :
      ∑ i, system.weight i * (1 - ⟪x, system.contact i⟫_ℝ) = n := by
    -- The coefficient sum is the total weight because the weighted inner products cancel.
    calc
      ∑ i, system.weight i * (1 - ⟪x, system.contact i⟫_ℝ) =
          (∑ i, system.weight i) -
            ∑ i, system.weight i * ⟪x, system.contact i⟫_ℝ := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
      _ = n := by rw [system.weight_sum, hinner_sum, sub_zero]
  -- Apply the triangle inequality and evaluate each nonpositive shifted coefficient exactly.
  calc
    ‖x‖ = ‖∑ i, (system.weight i * (⟪x, system.contact i⟫_ℝ - 1)) •
        system.contact i‖ := congrArg norm hshift
    _ ≤ ∑ i, ‖(system.weight i * (⟪x, system.contact i⟫_ℝ - 1)) •
        system.contact i‖ := norm_sum_le _ _
    _ = ∑ i, system.weight i * (1 - ⟪x, system.contact i⟫_ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [norm_smul, system.contact_norm i, mul_one, Real.norm_eq_abs,
        abs_of_nonpos (hcoefficient_nonpos i)]
      ring
    _ = n := hcoefficient_sum

end JohnContactSystem

#print axioms JohnContactSystem.norm_le_of_inner_le_one
