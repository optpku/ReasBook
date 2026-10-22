/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.6: A class of subsets of `Ω` is an algebra of sets in the textbook sense.
This is the canonical mathlib predicate `MeasureTheory.IsSetAlgebra` on a family
`A : Set (Set Ω)`. -/
recall MeasureTheory.IsSetAlgebra

open MeasureTheory Set

universe u

variable {Ω : Type u} {A : Set (Set Ω)}

-- Proof sketch: from `IsSetAlgebra A`, use `univ_mem` and `isSetRing`; conversely, recover
-- `empty_mem` from `Set.univ \ Set.univ = Set.empty`, obtain complements as `Set.univ \ s`,
-- and keep binary unions from the `IsSetRing` structure.
/-- The textbook formulation is equivalent to saying that `A` contains `univ` and is a ring of
sets. -/
theorem isSetAlgebra_iff_univ_mem_and_isSetRing :
    IsSetAlgebra A ↔ univ ∈ A ∧ IsSetRing A := by
  constructor
  · intro hA
    exact ⟨hA.univ_mem, hA.isSetRing⟩
  · rintro ⟨huniv, hA⟩
    refine
      { empty_mem := ?_
        compl_mem := ?_
        union_mem := hA.union_mem }
    · simpa using hA.diff_mem huniv huniv
    · intro s hs
      simpa [compl_eq_univ_diff] using hA.diff_mem huniv hs
