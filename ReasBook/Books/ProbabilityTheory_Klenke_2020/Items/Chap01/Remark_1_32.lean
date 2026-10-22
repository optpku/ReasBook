/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_37

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

/-- Remark 1.32: For the finite-or-cofinite content on `ℕ`, the inequality in
`AddContent.IsSigmaSubadditive` is strict, so this content is not a premeasure. -/
theorem finiteCofiniteZeroInfiniteContent_nat_not_isSigmaSubadditive :
    ¬ (finiteCofiniteZeroInfiniteContent ℕ).IsSigmaSubadditive := by
  simpa using finiteCofiniteZeroInfiniteContent_not_isSigmaSubadditive ℕ

/-- Remark 1.32: The inequality corresponding to countable subadditivity for a content can be
strict. Equivalently, there exists a content on a set semiring that is not a premeasure. -/
theorem exists_content_not_sigma_subadditive :
    ∃ (α : Type u) (C : Set (Set α)), IsSetSemiring C ∧
      ∃ m : AddContent ENNReal C, ¬ m.IsSigmaSubadditive := by
  refine ⟨ULift.{u} ℕ, finiteOrCofiniteFamily (ULift.{u} ℕ), ?_, finiteCofiniteZeroInfiniteContent (ULift.{u} ℕ), ?_⟩
  · exact (finiteOrCofiniteFamily_isSetAlgebra (ULift.{u} ℕ)).isSetRing.isSetSemiring
  · simpa using finiteCofiniteZeroInfiniteContent_not_isSigmaSubadditive (ULift.{u} ℕ)
