/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.Cover

public section

universe u

section KnapsackClosure

variable {ι : Type u} [DecidableEq ι]

/-- The cover-inequality closure consists of the binary points that satisfy every minimal-cover
inequality. -/
def cover_inequality_closure
    (weights : ι → ℕ) (capacity : ℕ) : Set (ι → ℝ) :=
  {x |
    (∀ i, x i = 0 ∨ x i = 1) ∧
      ∀ C : Finset ι,
        IsMinimalKnapsackCover weights capacity C →
          C.sum x ≤ cover_inequality_rhs C}

/-- A point belongs to `cover_inequality_closure weights capacity` exactly when it is binary and
satisfies the cover inequality of every minimal cover. -/
theorem mem_cover_inequality_closure_iff
    (weights : ι → ℕ) (capacity : ℕ) (x : ι → ℝ) :
    x ∈ cover_inequality_closure weights capacity ↔
      (∀ i, x i = 0 ∨ x i = 1) ∧
        ∀ C : Finset ι,
          IsMinimalKnapsackCover weights capacity C →
            C.sum x ≤ cover_inequality_rhs C := by
  -- Unfold membership in the defining closure predicate.
  rfl

end KnapsackClosure
