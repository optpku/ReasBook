/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_1_lemma_1_2

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was not available in this environment; this statement
-- uses Mathlib's `Int.fract β` for the fractional part `β - ⌊β⌋`.

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_lemma_1_4.lean: a property valid on
`mixedIntegerStrip β` holds at every integer-real pair satisfying its scalar constraints. -/
private lemma mixedIntegerStrip_property_of_integerPair
    {β : ℝ} {P : ℝ × ℝ → Prop} {x : ℤ} {y : ℝ}
    (hvalid : ∀ p ∈ mixedIntegerStrip β, P p)
    (hy : 0 ≤ y)
    (hxy : (x : ℝ) - y ≤ β) :
    P ((x : ℝ), y) := by
  -- Use the canonical membership characterization to place the pair in the strip.
  refine hvalid ((x : ℝ), y) ?_
  exact intPair_mem_mixedIntegerStrip_iff.mpr ⟨hy, hxy⟩

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_lemma_1_4.lean.
Lemma 1.4. For an integer `x`
and a nonnegative real `y` satisfying `x - y ≤ β`, the mixed-integer cut
`x - y / (1 - Int.fract β) ≤ ⌊β⌋` is valid. -/
theorem mixed_integer_strip_cut_valid
    (β : ℝ) {x : ℤ} {y : ℝ}
    (hy : 0 ≤ y)
    (hxy : (x : ℝ) - y ≤ β) :
    (x : ℝ) - y / (1 - Int.fract β) ≤ (⌊β⌋ : ℝ) := by
  -- Specialize strip-wide validity after packaging the scalar hypotheses as membership.
  refine mixedIntegerStrip_property_of_integerPair (P := fun p ↦
    p.1 - p.2 / (1 - Int.fract β) ≤ (⌊β⌋ : ℝ)) ?_ hy hxy
  intro p hp
  exact mixedIntegerStrip_cut_validOn β hp

#print axioms mixed_integer_strip_cut_valid
