/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_definition_3_15_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_5

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the statement
-- shape below was verified against local mathlib matrix APIs for `*ᵥ`, `ᵥ*`, and `⬝ᵥ`.

/-- Corollary 3.47. The canonical `x`-projection of the polyhedron
`{(x, z) | A *ᵥ x + B *ᵥ z = b ∧ z ≥ 0}` is the set of `x` satisfying
`u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b` for every multiplier `u` with `u ᵥ* B ≥ 0`. -/
theorem polyhedron_x_projection_image_eq_forall_nonneg_multipliers
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    Prod.fst '' {xz : (Fin n → ℝ) × (Fin p → ℝ) |
      A *ᵥ xz.1 + B *ᵥ xz.2 = b ∧ 0 ≤ xz.2} =
      {x : Fin n → ℝ | ∀ u : Fin m → ℝ, 0 ≤ u ᵥ* B → u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b} := by
  ext x
  rw [mem_image_fst_iff]
  change (∃ z : Fin p → ℝ, A *ᵥ x + B *ᵥ z = b ∧ 0 ≤ z) ↔
    ∀ u : Fin m → ℝ, 0 ≤ u ᵥ* B → u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b
  -- Repackage the residual feasibility problem `B *ᵥ z = b - A *ᵥ x`, `z ≥ 0` as a
  -- direct specialization of Theorem 3.5 to the equivalent system `(-B) *ᵥ z = -(b - A *ᵥ x)`.
  have h_residual_feasible :
      (∃ z : Fin p → ℝ, B *ᵥ z = b - A *ᵥ x ∧ 0 ≤ z) ↔
        ∀ u : Fin m → ℝ, 0 ≤ u ᵥ* B → 0 ≤ u ⬝ᵥ (b - A *ᵥ x) := by
    have h_farkas :=
      feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers
        (-B) (-(b - A *ᵥ x))
    have h_left :
        (∃ z : Fin p → ℝ, (-B) *ᵥ z = -(b - A *ᵥ x) ∧ 0 ≤ z) ↔
          (∃ z : Fin p → ℝ, B *ᵥ z = b - A *ᵥ x ∧ 0 ≤ z) := by
      constructor
      · rintro ⟨z, hz, hz_nonneg⟩
        refine ⟨z, ?_, hz_nonneg⟩
        have hz' : -((-B) *ᵥ z) = b - A *ᵥ x := by
          simpa using congrArg Neg.neg hz
        simpa [Matrix.neg_mulVec] using hz'
      · rintro ⟨z, hz, hz_nonneg⟩
        refine ⟨z, ?_, hz_nonneg⟩
        have hz' : -(B *ᵥ z) = -(b - A *ᵥ x) := by
          simpa using congrArg Neg.neg hz
        simpa [Matrix.neg_mulVec] using hz'
    have h_right :
        (∀ u : Fin m → ℝ, u ᵥ* (-B) ≤ 0 → u ⬝ᵥ (-(b - A *ᵥ x)) ≤ 0) ↔
          ∀ u : Fin m → ℝ, 0 ≤ u ᵥ* B → 0 ≤ u ⬝ᵥ (b - A *ᵥ x) := by
      constructor
      · intro h u hu_nonneg
        have hu_neg : u ᵥ* (-B) ≤ 0 := by
          have hu' : -(u ᵥ* B) ≤ 0 := neg_nonpos.mpr hu_nonneg
          simpa [Matrix.vecMul_neg] using hu'
        have hu_eval : u ⬝ᵥ (-(b - A *ᵥ x)) ≤ 0 := h u hu_neg
        have hu_eval' : -(u ⬝ᵥ (b - A *ᵥ x)) ≤ 0 := by
          simpa [dotProduct_neg] using hu_eval
        simpa using (neg_nonneg.mpr hu_eval')
      · intro h u hu_nonpos
        have hu_nonneg : 0 ≤ u ᵥ* B := by
          have hu' : -(u ᵥ* B) ≤ 0 := by
            simpa [Matrix.vecMul_neg] using hu_nonpos
          simpa using (neg_nonneg.mpr hu')
        have hu_eval : 0 ≤ u ⬝ᵥ (b - A *ᵥ x) := h u hu_nonneg
        have hu_eval' : -(u ⬝ᵥ (b - A *ᵥ x)) ≤ 0 := neg_nonpos.mpr hu_eval
        simpa [dotProduct_neg] using hu_eval'
    exact h_left.symm.trans (h_farkas.trans h_right)
  constructor
  · intro hx
    rcases hx with ⟨z, hz_eq, hz_nonneg⟩
    -- Rewrite the original feasibility equation into the residual form
    -- needed by `h_residual_feasible`.
    have hz_residual : ∃ z : Fin p → ℝ, B *ᵥ z = b - A *ᵥ x ∧ 0 ≤ z := by
      refine ⟨z, ?_, hz_nonneg⟩
      exact eq_sub_iff_add_eq.mpr <| by
        simpa [add_comm, add_left_comm, add_assoc] using hz_eq
    -- Apply the specialized Farkas alternative, then rewrite the residual inequality back.
    intro u hu_nonneg
    have hu_residual : 0 ≤ u ⬝ᵥ (b - A *ᵥ x) := h_residual_feasible.mp hz_residual u hu_nonneg
    simpa [dotProduct_sub, sub_nonneg] using hu_residual
  · intro hx
    -- Translate the target family of valid inequalities into nonnegativity on the residual.
    have hx_residual :
        ∀ u : Fin m → ℝ, 0 ≤ u ᵥ* B → 0 ≤ u ⬝ᵥ (b - A *ᵥ x) := by
      intro u hu_nonneg
      have hu_eval : u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b := hx u hu_nonneg
      simpa [dotProduct_sub, sub_nonneg] using hu_eval
    obtain ⟨z, hz_residual_eq, hz_nonneg⟩ := h_residual_feasible.mpr hx_residual
    -- Convert residual feasibility back to the original equality-constrained projection form.
    refine ⟨z, ?_, hz_nonneg⟩
    have hz_eq : B *ᵥ z + A *ᵥ x = b := (eq_sub_iff_add_eq).mp hz_residual_eq
    simpa [add_comm, add_left_comm, add_assoc] using hz_eq
