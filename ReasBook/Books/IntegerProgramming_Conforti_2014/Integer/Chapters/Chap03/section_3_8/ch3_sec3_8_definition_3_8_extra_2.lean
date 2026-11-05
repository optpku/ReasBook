/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_theorem_2_3.LinearFunctional

/- Definition 3.8-extra-2 reuses the earlier Chapter 2 linear-functional and exposed-face owner
API directly. This file is a thin Chapter 3 bridge import for the same canonical declarations. -/

/-- Definition 3.8-extra-2. On `Fin n → ℝ`, an exposed face is exactly either `∅` or the equality
set on `P` of a valid inequality `c ⬝ᵥ x ≤ δ`. -/
theorem isExposed_iff_eq_empty_or_eq_face_set {n : ℕ} {P F : Set (Fin n → ℝ)} :
    IsExposed ℝ P F ↔
      F = ∅ ∨ ∃ c : Fin n → ℝ, ∃ δ : ℝ, is_valid_inequality P c δ ∧ F = face_set P c δ := by
  constructor
  · intro hF
    by_cases hF_nonempty : F.Nonempty
    · right
      exact hF.exists_eq_face_set_of_nonempty hF_nonempty
    · left
      exact Set.not_nonempty_iff_eq_empty.mp hF_nonempty
  · rintro (rfl | ⟨c, δ, h_valid, rfl⟩)
    · exact isExposed_empty
    · exact isExposed_face_set_of_valid_inequality h_valid

/-- Definition 3.8-extra-2 (2). A hyperplane is supporting for `P` if it is defined by a nonzero
valid inequality whose associated face on `P` is nonempty. -/
def is_supporting_hyperplane {n : ℕ} (P H : Set (Fin n → ℝ)) : Prop :=
  ∃ c : Fin n → ℝ, ∃ δ : ℝ,
    c ≠ 0 ∧ is_valid_inequality P c δ ∧ (face_set P c δ).Nonempty ∧ H = linear_hyperplane c δ

/-- `is_supporting_hyperplane` unfolds to the existence of a nonzero valid defining inequality with
nonempty equality face. -/
theorem is_supporting_hyperplane_iff {n : ℕ} {P H : Set (Fin n → ℝ)} :
    is_supporting_hyperplane P H ↔
      ∃ c : Fin n → ℝ, ∃ δ : ℝ,
        c ≠ 0 ∧ is_valid_inequality P c δ ∧ (face_set P c δ).Nonempty ∧
          H = linear_hyperplane c δ := by
  rfl

/-- Definition 3.8-extra-2 (3). A proper face of `P` is a nonempty exposed face properly contained
in `P`. -/
def is_proper_face {n : ℕ} (P F : Set (Fin n → ℝ)) : Prop :=
  IsExposed ℝ P F ∧ F.Nonempty ∧ F ⊂ P

/-- `is_proper_face` unfolds to being a nonempty exposed face properly contained in `P`. -/
theorem is_proper_face_iff {n : ℕ} {P F : Set (Fin n → ℝ)} :
    is_proper_face P F ↔ IsExposed ℝ P F ∧ F.Nonempty ∧ F ⊂ P := by
  rfl
