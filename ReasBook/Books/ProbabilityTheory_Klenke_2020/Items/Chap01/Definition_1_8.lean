/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 1.8 (ring of sets): the textbook notion is the canonical mathlib predicate
`MeasureTheory.IsSetRing` on a family `A : Set (Set Ω)`.
-/
recall MeasureTheory.IsSetRing

universe u

open MeasureTheory Set

variable {Ω : Type u}

namespace MeasureTheory

/-- A sigma-ring of sets is a ring of sets that is also closed under countable unions. -/
class IsSetSigmaRing (A : Set (Set Ω)) : Prop extends IsSetRing A, IsCountablyUnionClosed A

/-- The full powerset of `Ω` is a sigma-ring of sets. -/
instance : IsSetSigmaRing (univ : Set (Set Ω)) where
  empty_mem := by simp
  union_mem := by
    intro s t hs ht
    simp
  diff_mem := by
    intro s t hs ht
    simp
  iUnion_mem := by
    intro s hs
    simp

end MeasureTheory
