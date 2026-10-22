/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open MeasurableSpace

universe u v

variable {Ω : Type u} {ι : Sort v}

/- Theorem 1.15: the measurable sets of the infimum of a family of measurable spaces are exactly
the sets that are measurable in every member of the family, so arbitrary intersections of
sigma-algebras are sigma-algebras. -/
recall MeasurableSpace.measurableSet_iInf

namespace MeasurableSpace.DynkinSystem

/-- The pointwise intersection of a family of Dynkin systems. -/
def iInter (D : ι → DynkinSystem Ω) : DynkinSystem Ω where
  Has s := ∀ i, (D i).Has s
  has_empty := fun i ↦ (D i).has_empty
  has_compl := fun h i ↦ (D i).has_compl (h i)
  has_iUnion_nat := fun hd h i ↦ (D i).has_iUnion_nat hd fun n ↦ h n i

@[simp] theorem has_iInter_iff (D : ι → DynkinSystem Ω) {s : Set Ω} :
    (iInter D).Has s ↔ ∀ i, (D i).Has s :=
  Iff.rfl

end MeasurableSpace.DynkinSystem

-- Proof sketch: check the empty-set, union, and difference axioms pointwise in the indexed
-- intersection, using the corresponding axiom in each `A i`.
/-- An arbitrary intersection of rings of sets is again a ring of sets. -/
theorem set_iInter_isSetRing (A : ι → Set (Set Ω)) (hA : ∀ i, IsSetRing (A i)) :
    IsSetRing (⋂ i, A i) := sorry

-- Proof sketch: keep the ring-of-sets axioms and countable-union closure pointwise across the
-- indexed intersection.
/-- An arbitrary intersection of sigma-rings of sets is again a sigma-ring of sets. -/
theorem set_iInter_isSetSigmaRing (A : ι → Set (Set Ω)) (hA : ∀ i, IsSetSigmaRing (A i)) :
    IsSetSigmaRing (⋂ i, A i) := sorry

-- Proof sketch: check containment of `univ`, complement closure, and binary union closure
-- pointwise in the indexed intersection.
/-- An arbitrary intersection of algebras of sets is again an algebra of sets. -/
theorem set_iInter_isSetAlgebra (A : ι → Set (Set Ω)) (hA : ∀ i, IsSetAlgebra (A i)) :
    IsSetAlgebra (⋂ i, A i) := sorry

/-- The first semiring in the textbook counterexample, encoded on `Fin 4` as `0, 1, 2, 3`. -/
def semiringCounterexampleOne : Set (Set (Fin 4)) :=
  {∅, (univ : Set (Fin 4)), ({0} : Set (Fin 4)), ({1, 2} : Set (Fin 4)), ({3} : Set (Fin 4))}

/-- The second semiring in the textbook counterexample, encoded on `Fin 4` as `0, 1, 2, 3`. -/
def semiringCounterexampleTwo : Set (Set (Fin 4)) :=
  {∅, (univ : Set (Fin 4)), ({0} : Set (Fin 4)), ({1} : Set (Fin 4)), ({2, 3} : Set (Fin 4))}

-- Proof sketch: verify the semiring axioms by a finite case check on the listed members of the
-- family.
/-- The first explicit family in the textbook counterexample is a semiring of sets. -/
theorem semiringCounterexampleOne_isSetSemiring :
    IsSetSemiring semiringCounterexampleOne := sorry

-- Proof sketch: verify the semiring axioms by a finite case check on the listed members of the
-- family.
/-- The second explicit family in the textbook counterexample is a semiring of sets. -/
theorem semiringCounterexampleTwo_isSetSemiring :
    IsSetSemiring semiringCounterexampleTwo := sorry

-- Proof sketch: the intersection family is `{∅, univ, {0}}`, and `univ \ {0}` cannot be written
-- as a finite disjoint union of members of that family.
/-- The textbook counterexample shows that arbitrary intersections of semirings need not be
semirings. -/
theorem semiringCounterexample_inter_not_isSetSemiring :
    ¬ IsSetSemiring (semiringCounterexampleOne ∩ semiringCounterexampleTwo) := sorry
