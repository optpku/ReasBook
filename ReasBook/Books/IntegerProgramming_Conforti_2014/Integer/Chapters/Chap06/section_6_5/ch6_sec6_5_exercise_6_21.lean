/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_4.ch6_sec6_4_theorem_6_40
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_definition_6_3_1_extra_2

section Exercise621

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "IntAssignment" => Rq →₀ ℤ

/-- Helper for Exercise 6.21: the cut value of a midpoint decomposition is the midpoint of the
corresponding cut values on every finitely supported assignment. -/
theorem gomory_group_validity_value_eq_midpoint
    {π π₁ π₂ : Rq → ℝ}
    {x : IntAssignment}
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    gomory_group_validity_value π x =
      (1 / 2 : ℝ) * gomory_group_validity_value π₁ x +
        (1 / 2 : ℝ) * gomory_group_validity_value π₂ x := by
  classical
  -- Expand the midpoint decomposition inside the finite-support cut-value sum.
  rw [hmid]
  rw [gomory_group_validity_value_eq, gomory_group_validity_value_eq]
  rw [gomory_group_validity_value_eq]
  rw [Finsupp.sum, Finsupp.sum, Finsupp.sum]
  simp_rw [Pi.add_apply, Pi.smul_apply, mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro r hr
    ring
  · refine Finset.sum_congr rfl ?_
    intro r hr
    ring

/-- Helper for Exercise 6.21: every tight point of a valid midpoint function is tight for each
valid midpoint component. -/
theorem gomory_group_equality_set_subset_of_midpoint_decomposition
    {f : Rq}
    {π π₁ π₂ : Rq → ℝ}
    (hπ₁ : pure_integer_valid_function f π₁)
    (hπ₂ : pure_integer_valid_function f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    gomory_group_equality_set f π ⊆
      gomory_group_equality_set f π₁ ∩ gomory_group_equality_set f π₂ := by
  intro x hx
  rcases (mem_gomory_group_equality_set_iff.mp hx) with ⟨hx_rel, hx_eq⟩
  have hπ₁_ge : 1 ≤ gomory_group_validity_value π₁ x := hπ₁.one_le_sum hx_rel
  have hπ₂_ge : 1 ≤ gomory_group_validity_value π₂ x := hπ₂.one_le_sum hx_rel
  -- Rewrite the tightness equation as an average of two valid cut values.
  have havg :
      (1 : ℝ) =
        (1 / 2 : ℝ) * gomory_group_validity_value π₁ x +
          (1 / 2 : ℝ) * gomory_group_validity_value π₂ x := by
    calc
      (1 : ℝ) = gomory_group_validity_value π x := by rw [hx_eq]
      _ =
          (1 / 2 : ℝ) * gomory_group_validity_value π₁ x +
            (1 / 2 : ℝ) * gomory_group_validity_value π₂ x :=
        gomory_group_validity_value_eq_midpoint (x := x) hmid
  have hπ₁_eq : gomory_group_validity_value π₁ x = 1 := by
    nlinarith [hπ₁_ge, hπ₂_ge, havg]
  have hπ₂_eq : gomory_group_validity_value π₂ x = 1 := by
    nlinarith [hπ₁_ge, hπ₂_ge, havg]
  -- Repackage the two equalities as membership in the component equality sets.
  refine ⟨?_, ?_⟩
  · exact mem_gomory_group_equality_set_iff.mpr ⟨hx_rel, hπ₁_eq⟩
  · exact mem_gomory_group_equality_set_iff.mpr ⟨hx_rel, hπ₂_eq⟩

/-- Helper for Exercise 6.21: a facet-defining function cannot have a nontrivial midpoint
decomposition into valid functions. -/
theorem facet_midpoint_components_eq
    {f : Rq}
    {π π₁ π₂ : Rq → ℝ}
    (hπ : defines_facet_of_gomory_group_relaxation f π)
    (hπ₁ : pure_integer_valid_function f π₁)
    (hπ₂ : pure_integer_valid_function f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    π = π₁ ∧ π = π₂ := by
  have hsubset :
      gomory_group_equality_set f π ⊆
        gomory_group_equality_set f π₁ ∩ gomory_group_equality_set f π₂ :=
    gomory_group_equality_set_subset_of_midpoint_decomposition hπ₁ hπ₂ hmid
  have hsubset₁ : gomory_group_equality_set f π ⊆ gomory_group_equality_set f π₁ := by
    intro y hy
    exact (hsubset hy).1
  have hsubset₂ : gomory_group_equality_set f π ⊆ gomory_group_equality_set f π₂ := by
    intro y hy
    exact (hsubset hy).2
  -- Facet uniqueness identifies each valid midpoint component with the original function.
  refine ⟨(hπ.eq_of_subset_equality_set hπ₁ hsubset₁).symm, ?_⟩
  exact (hπ.eq_of_subset_equality_set hπ₂ hsubset₂).symm

/-- Exercise 6.21. If a valid function defines a facet of `G_f` in the sense of Section 6.4, then
it is extreme. -/
theorem facet_defining_gomory_group_function_is_extreme
    {f : Rq}
    {π : Rq → ℝ}
    (hπ : defines_facet_of_gomory_group_relaxation f π) :
    pure_integer_extreme_valid_function f π := by
  refine
    { nonneg := hπ.nonneg
      one_le_sum := hπ.one_le_sum
      eq_of_eq_midpoint := ?_ }
  intro π₁ π₂ hπ₁ hπ₂ hmid
  -- The facet equality set forces both valid midpoint components to coincide with `π`.
  exact facet_midpoint_components_eq hπ hπ₁ hπ₂ hmid

end Exercise621
