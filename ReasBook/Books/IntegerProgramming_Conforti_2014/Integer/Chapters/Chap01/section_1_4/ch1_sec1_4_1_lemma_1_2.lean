/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_1_definition_1_32
import Mathlib.Tactic

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_lemma_1_2.lean: an integer gap above
`⌊β⌋`, scaled by the complementary fractional part, is bounded by any nonnegative slack
making the integer feasible. -/
private lemma integerGap_mul_oneSubFract_le
    (β : ℝ) (z : ℤ) (y : ℝ)
    (hy : 0 ≤ y)
    (hzy : (z : ℝ) - y ≤ β) :
    ((z : ℝ) - (⌊β⌋ : ℝ)) * (1 - Int.fract β) ≤ y := by
  have hden_pos : 0 < 1 - Int.fract β := by
    linarith [Int.fract_lt_one β]
  by_cases hz : z ≤ ⌊β⌋
  · -- A nonpositive integer gap has nonpositive scaled value, so nonnegative slack suffices.
    have hz_real : (z : ℝ) ≤ (⌊β⌋ : ℝ) := by
      exact_mod_cast hz
    have hgap_nonpos : (z : ℝ) - (⌊β⌋ : ℝ) ≤ 0 := by
      linarith
    have hscaled_nonpos :
        ((z : ℝ) - (⌊β⌋ : ℝ)) * (1 - Int.fract β) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hgap_nonpos hden_pos.le
    exact hscaled_nonpos.trans hy
  · -- Otherwise integrality makes the gap at least one; its excess absorbs `Int.fract β`.
    have hgap_one : (1 : ℝ) ≤ (z : ℝ) - (⌊β⌋ : ℝ) := by
      have hfloor_succ : ⌊β⌋ + 1 ≤ z :=
        Int.add_one_le_iff.mpr (lt_of_not_ge hz)
      have hfloor_succ_real : (⌊β⌋ : ℝ) + 1 ≤ (z : ℝ) := by
        exact_mod_cast hfloor_succ
      linarith
    have hfract_product_nonneg :
        0 ≤ Int.fract β * ((z : ℝ) - (⌊β⌋ : ℝ) - 1) :=
      mul_nonneg (Int.fract_nonneg β) (sub_nonneg.mpr hgap_one)
    nlinarith [Int.floor_add_fract β]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_lemma_1_2.lean.
Lemma 1.2. For `β : ℝ`,
every point `p ∈ mixedIntegerStrip β` satisfies the MIR inequality
`p.1 - p.2 / (1 - Int.fract β) ≤ ⌊β⌋`, where the source's `f := β - ⌊β⌋` is formalized
as `Int.fract β`. -/
theorem mixedIntegerStrip_cut_validOn
    (β : ℝ) {p : ℝ × ℝ}
    (hp : p ∈ mixedIntegerStrip β) :
    p.1 - p.2 / (1 - Int.fract β) ≤ (⌊β⌋ : ℝ) := by
  -- Expose the strip constraints and replace the first coordinate by its integer witness.
  simp only [mixedIntegerStrip, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc] at hp
  rcases hp with ⟨⟨z, hz⟩, hy, hzy⟩
  rw [← hz] at hzy ⊢
  have hden_pos : 0 < 1 - Int.fract β := by
    linarith [Int.fract_lt_one β]
  have hscaled := integerGap_mul_oneSubFract_le β z p.2 hy hzy
  -- Divide the scaled gap by the positive complementary fractional part and rearrange.
  have hgap_div :
      (z : ℝ) - (⌊β⌋ : ℝ) ≤ p.2 / (1 - Int.fract β) :=
    (le_div_iff₀ hden_pos).mpr hscaled
  linarith

#print axioms mixedIntegerStrip_cut_validOn
