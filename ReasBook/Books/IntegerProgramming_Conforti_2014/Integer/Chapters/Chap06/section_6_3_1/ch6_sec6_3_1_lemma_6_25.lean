/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_definition_6_3_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_theorem_6_22

section Lemma625

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ

/-- The additivity set `E(π)` consists of the pairs `(r₁, r₂)` where `π` is additive:
`π r₁ + π r₂ = π (r₁ + r₂)`. -/
def pure_integer_additivity_set (π : Rq → ℝ) : Set (Rq × Rq) :=
  {p | π p.1 + π p.2 = π (p.1 + p.2)}

namespace PureIntegerAdditivityNotation

scoped notation:max "E(" π ")" => pure_integer_additivity_set π

end PureIntegerAdditivityNotation

open scoped PureIntegerAdditivityNotation

/-- Membership in `E(π)` means that `π` is additive at the pair `(r₁, r₂)`. -/
theorem mem_pure_integer_additivity_set_iff
    {π : Rq → ℝ} {r₁ r₂ : Rq} :
    (r₁, r₂) ∈ E(π) ↔
      π r₁ + π r₂ = π (r₁ + r₂) := by
  rfl

/-- Helper for Lemma 6.25: the midpoint of two valid pure-integer functions is again valid. -/
lemma pure_integer_valid_function_midpoint
    {f : Rq} {π₁ π₂ : Rq → ℝ}
    (hπ₁ : pure_integer_valid_function f π₁)
    (hπ₂ : pure_integer_valid_function f π₂) :
    pure_integer_valid_function f ((1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) := by
  refine
    { nonneg := ?_
      one_le_sum := ?_ }
  · -- Pointwise nonnegativity is preserved by the nonnegative midpoint coefficients.
    intro r
    simp [Pi.add_apply, Pi.smul_apply]
    nlinarith [hπ₁.nonneg r, hπ₂.nonneg r]
  · -- The cut inequality is linear in the coefficient function.
    intro x hx
    have h₁ : 1 ≤ x.sum (fun r n ↦ (n : ℝ) * π₁ r) :=
      pure_integer_valid_function_one_le_sum hπ₁ hx
    have h₂ : 1 ≤ x.sum (fun r n ↦ (n : ℝ) * π₂ r) :=
      pure_integer_valid_function_one_le_sum hπ₂ hx
    have hsum :
        x.sum (fun r n ↦ (n : ℝ) * (((1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) r)) =
          (1 / 2 : ℝ) * x.sum (fun r n ↦ (n : ℝ) * π₁ r) +
            (1 / 2 : ℝ) * x.sum (fun r n ↦ (n : ℝ) * π₂ r) := by
      classical
      simp_rw [Finsupp.sum, Pi.add_apply, Pi.smul_apply, mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro r hr
        ring
      · refine Finset.sum_congr rfl ?_
        intro r hr
        ring
    rw [hsum]
    nlinarith

/-- Helper for Lemma 6.25: the left midpoint component of a minimal valid pure-integer
function is again minimal. Let `π` be a minimal valid function. If
`π = (1 / 2) • π₁ + (1 / 2) • π₂`, where `π₁` and `π₂` are valid functions, then `π₁` is also a
minimal valid function. -/
theorem left_midpoint_component_is_minimal_valid_pure_integer_function
    {f : Rq} {π π₁ π₂ : Rq → ℝ}
    (hπ : pure_integer_minimal_valid_function f π)
    (hπ₁ : pure_integer_valid_function f π₁)
    (hπ₂ : pure_integer_valid_function f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    pure_integer_minimal_valid_function f π₁ := by
  refine
    { nonneg := hπ₁.nonneg
      one_le_sum := hπ₁.one_le_sum
      eq_of_le := ?_ }
  intro π₁' hπ₁' hle
  -- Reflect a smaller valid perturbation of `π₁` across the fixed midpoint decomposition of `π`.
  have hmid_valid :
      pure_integer_valid_function f ((1 / 2 : ℝ) • π₁' + (1 / 2 : ℝ) • π₂) :=
    pure_integer_valid_function_midpoint hπ₁' hπ₂
  have hmid_le : ∀ r, (((1 / 2 : ℝ) • π₁' + (1 / 2 : ℝ) • π₂) r) ≤ π r := by
    intro r
    rw [hmid]
    simp [Pi.add_apply, Pi.smul_apply]
    nlinarith [hle r]
  have heq :
      (1 / 2 : ℝ) • π₁' + (1 / 2 : ℝ) • π₂ = π :=
    pure_integer_minimal_valid_function_eq_of_le hπ hmid_valid hmid_le
  -- Evaluating both midpoint formulas at each point isolates the first component.
  ext r
  have hpoint :
      (((1 / 2 : ℝ) • π₁' + (1 / 2 : ℝ) • π₂) r) =
        (((1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) r) := by
    calc
      (((1 / 2 : ℝ) • π₁' + (1 / 2 : ℝ) • π₂) r) = π r := by
        simpa using congrArg (fun ψ ↦ ψ r) heq
      _ = (((1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) r) := by
        simpa using congrArg (fun ψ ↦ ψ r) hmid
  simp [Pi.add_apply, Pi.smul_apply] at hpoint
  nlinarith

/-- Helper for Lemma 6.25: the right midpoint component of a minimal valid pure-integer
function is again minimal. Let `π` be a minimal valid function. If
`π = (1 / 2) • π₁ + (1 / 2) • π₂`, where `π₁` and `π₂` are valid functions, then `π₂` is also a
minimal valid function. -/
theorem right_midpoint_component_is_minimal_valid_pure_integer_function
    {f : Rq} {π π₁ π₂ : Rq → ℝ}
    (hπ : pure_integer_minimal_valid_function f π)
    (hπ₁ : pure_integer_valid_function f π₁)
    (hπ₂ : pure_integer_valid_function f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    pure_integer_minimal_valid_function f π₂ := by
  -- Symmetry of the midpoint decomposition reduces the second component to the first case.
  have hmid' : π = (1 / 2 : ℝ) • π₂ + (1 / 2 : ℝ) • π₁ := by
    simpa [add_comm] using hmid
  simpa using
    left_midpoint_component_is_minimal_valid_pure_integer_function hπ hπ₂ hπ₁ hmid'

/-- Lemma 6.25. Let `π` be a minimal valid function. Assume
`π = (1 / 2) • π₁ + (1 / 2) • π₂`, where `π₁` and `π₂` are valid functions. Then
`π₁` and `π₂` are minimal valid functions and `E(π) ⊆ E(π₁) ∩ E(π₂)`. This declaration
records the additivity-set inclusion, while the two preceding helper theorems supply the
minimality conclusions for `π₁` and `π₂`. -/
theorem pure_integer_additivity_set_subset_of_midpoint_decomposition
    {f : Rq} {π π₁ π₂ : Rq → ℝ}
    (hπ : pure_integer_minimal_valid_function f π)
    (hπ₁ : pure_integer_valid_function f π₁)
    (hπ₂ : pure_integer_valid_function f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    E(π) ⊆ E(π₁) ∩ E(π₂) := by
  have hπ₁_min :
      pure_integer_minimal_valid_function f π₁ :=
    left_midpoint_component_is_minimal_valid_pure_integer_function hπ hπ₁ hπ₂ hmid
  have hπ₂_min :
      pure_integer_minimal_valid_function f π₂ :=
    right_midpoint_component_is_minimal_valid_pure_integer_function hπ hπ₁ hπ₂ hmid
  have hsub₁ : π₁.Subadditive :=
    pure_integer_minimal_valid_function_subadditive hπ₁_min
  have hsub₂ : π₂.Subadditive :=
    pure_integer_minimal_valid_function_subadditive hπ₂_min
  intro p hp
  rcases p with ⟨r₁, r₂⟩
  rw [Set.mem_inter_iff]
  have hadd : π r₁ + π r₂ = π (r₁ + r₂) :=
    mem_pure_integer_additivity_set_iff.mp hp
  have hgap₁_nonneg : 0 ≤ π₁ r₁ + π₁ r₂ - π₁ (r₁ + r₂) := by
    linarith [hsub₁ r₁ r₂]
  have hgap₂_nonneg : 0 ≤ π₂ r₁ + π₂ r₂ - π₂ (r₁ + r₂) := by
    linarith [hsub₂ r₁ r₂]
  -- The midpoint identity turns the additivity of `π` into a zero weighted sum of the two gaps.
  have hgap_mid :
      (1 / 2 : ℝ) * (π₁ r₁ + π₁ r₂ - π₁ (r₁ + r₂)) +
        (1 / 2 : ℝ) * (π₂ r₁ + π₂ r₂ - π₂ (r₁ + r₂)) = 0 := by
    have hmid_r₁ : π r₁ = ((1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) r₁ := by
      simpa using congrArg (fun ψ ↦ ψ r₁) hmid
    have hmid_r₂ : π r₂ = ((1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) r₂ := by
      simpa using congrArg (fun ψ ↦ ψ r₂) hmid
    have hmid_sum : π (r₁ + r₂) = ((1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) (r₁ + r₂) := by
      simpa using congrArg (fun ψ ↦ ψ (r₁ + r₂)) hmid
    simp [Pi.add_apply, Pi.smul_apply] at hmid_r₁ hmid_r₂ hmid_sum
    nlinarith [hadd, hmid_r₁, hmid_r₂, hmid_sum]
  have hgap₁_zero : π₁ r₁ + π₁ r₂ - π₁ (r₁ + r₂) = 0 := by
    nlinarith [hgap₁_nonneg, hgap₂_nonneg, hgap_mid]
  have hgap₂_zero : π₂ r₁ + π₂ r₂ - π₂ (r₁ + r₂) = 0 := by
    nlinarith [hgap₁_nonneg, hgap₂_nonneg, hgap_mid]
  constructor
  · -- The first gap vanishes, so `(r₁, r₂)` belongs to `E(π₁)`.
    exact mem_pure_integer_additivity_set_iff.mpr (by nlinarith [hgap₁_zero])
  · -- The second gap vanishes, so `(r₁, r₂)` belongs to `E(π₂)`.
    exact mem_pure_integer_additivity_set_iff.mpr (by nlinarith [hgap₂_zero])

end Lemma625
