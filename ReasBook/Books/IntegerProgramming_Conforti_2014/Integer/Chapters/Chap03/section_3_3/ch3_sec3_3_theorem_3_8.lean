/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Semantic search tool `lean_leansearch` was unavailable in this environment; this statement
-- uses the Chapter 3 primal and dual feasible-region owners and expresses each
-- slackness term by the row-vector dot product `(A i) ⬝ᵥ xStar`.

/-- Theorem 3.8 (Complementary Slackness). For feasible points `xStar ∈ P = {x | A *ᵥ x ≤ b}` and
`uStar ∈ D = {u | u ᵥ* A = c ∧ 0 ≤ u}`, primal optimality of `xStar` and dual optimality of
`uStar` are equivalent to the complementary slackness equations
`uStar i * ((A i) ⬝ᵥ xStar - b i) = 0` for all `i`. -/
theorem linear_programming_complementary_slackness
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (xStar : Fin n → ℝ)
    (uStar : Fin m → ℝ)
    (hx : xStar ∈ primal_feasible_region A b)
    (hu : uStar ∈ dual_feasible_region A c) :
    (IsGreatest (primal_objective_values A b c) (c ⬝ᵥ xStar) ∧
      IsLeast (dual_objective_values A b c) (uStar ⬝ᵥ b)) ↔
      ∀ i : Fin m, uStar i * ((A i) ⬝ᵥ xStar - b i) = 0 := by
  rcases (mem_primal_feasible_region_iff A b xStar).mp hx with hx_feas
  rcases (mem_dual_feasible_region_iff A c uStar).mp hu with ⟨hu_eq, hu_nonneg⟩
  constructor
  · rintro ⟨hprimal, hdual⟩ i
    have hvalue : c ⬝ᵥ xStar = uStar ⬝ᵥ b := by
      have hstrong :=
        linear_programming_duality_optimal_value_eq A b c ⟨xStar, hx⟩ ⟨uStar, hu⟩
      calc
        c ⬝ᵥ xStar = sSup (primal_objective_values A b c) := hprimal.csSup_eq.symm
        _ = sInf (dual_objective_values A b c) := hstrong
        _ = uStar ⬝ᵥ b := hdual.csInf_eq
    have hslack_dot_zero : uStar ⬝ᵥ (b - A *ᵥ xStar) = 0 := by
      calc
        uStar ⬝ᵥ (b - A *ᵥ xStar) = uStar ⬝ᵥ b - (uStar ⬝ᵥ (A *ᵥ xStar)) := by
          rw [dotProduct_sub]
        _ = uStar ⬝ᵥ b - c ⬝ᵥ xStar := by
          rw [Matrix.dotProduct_mulVec uStar A xStar, hu_eq]
        _ = 0 := by
          rw [hvalue, sub_self]
    have hsum_zero :
        ∑ j : Fin m, uStar j * (b j - (A *ᵥ xStar) j) = 0 := by
      simpa [dotProduct] using hslack_dot_zero
    have hterm_zero :
        ∀ j : Fin m, uStar j * (b j - (A *ᵥ xStar) j) = 0 := by
      have hzero_on_univ :
          ∀ j ∈ (Finset.univ : Finset (Fin m)), uStar j * (b j - (A *ᵥ xStar) j) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ ↦ mul_nonneg (hu_nonneg j) (sub_nonneg.mpr (hx_feas j)))).1 hsum_zero
      intro j
      exact hzero_on_univ j (Finset.mem_univ j)
    by_cases huj : uStar i = 0
    · simp [huj]
    · have hslack_zero : b i - (A *ᵥ xStar) i = 0 :=
        (mul_eq_zero.mp (hterm_zero i)).resolve_left huj
      have hrow_eq : (A *ᵥ xStar) i - b i = 0 := by
        linarith
      change uStar i * ((A *ᵥ xStar) i - b i) = 0
      simp [hrow_eq]
  · intro hslack
    have hsum_zero : ∑ i : Fin m, uStar i * ((A i) ⬝ᵥ xStar - b i) = 0 := by
      simp [hslack]
    have hslack_dot_zero : uStar ⬝ᵥ (A *ᵥ xStar - b) = 0 := by
      simpa [dotProduct, Matrix.mulVec] using hsum_zero
    have hsub_eq : uStar ⬝ᵥ (A *ᵥ xStar) - uStar ⬝ᵥ b = 0 := by
      simpa [dotProduct_sub] using hslack_dot_zero
    have hvalue : c ⬝ᵥ xStar = uStar ⬝ᵥ b := by
      calc
        c ⬝ᵥ xStar = uStar ⬝ᵥ A *ᵥ xStar := by
          rw [Matrix.dotProduct_mulVec uStar A xStar, hu_eq]
        _ = uStar ⬝ᵥ b := by
          linarith
    constructor
    · refine ⟨⟨xStar, hx, rfl⟩, ?_⟩
      rintro y ⟨x, hx', rfl⟩
      calc
        c ⬝ᵥ x ≤ uStar ⬝ᵥ b := weak_duality_feasible_pair A b c hx' hu
        _ = c ⬝ᵥ xStar := hvalue.symm
    · refine ⟨⟨uStar, hu, rfl⟩, ?_⟩
      rintro y ⟨u, hu', rfl⟩
      calc
        uStar ⬝ᵥ b = c ⬝ᵥ xStar := hvalue.symm
        _ ≤ u ⬝ᵥ b := weak_duality_feasible_pair A b c hx hu'
