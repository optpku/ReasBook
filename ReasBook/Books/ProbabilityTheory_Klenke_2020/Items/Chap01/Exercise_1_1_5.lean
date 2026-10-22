/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped symmDiff BooleanRingOfBooleanAlgebra
open Set MeasureTheory

universe u

variable {Ω : Type u} {A : Set (Set Ω)}

namespace IsSetRing

/-- Closure of a ring of sets under symmetric difference. -/
-- Proof sketch: expand `s ∆ t` as `(s \ t) ∪ (t \ s)` and use closure under set difference and
-- binary union.
lemma symmDiff_mem (hA : IsSetRing A) {s t : Set Ω} (hs : s ∈ A) (ht : t ∈ A) : s ∆ t ∈ A := by
  rw [Set.symmDiff_def]
  exact hA.union_mem (hA.diff_mem hs ht) (hA.diff_mem ht hs)

/-- The non-unital subring of `Set Ω` determined by a ring of sets. -/
def toNonUnitalSubring (hA : IsSetRing A) : NonUnitalSubring (Set Ω) where
  carrier := A
  zero_mem' := hA.empty_mem
  add_mem' := symmDiff_mem hA
  neg_mem' hs := by simpa using hs
  mul_mem' := hA.inter_mem

/-- Membership in the non-unital subring attached to a ring of sets is membership in the
underlying family. -/
@[simp] lemma mem_toNonUnitalSubring (hA : IsSetRing A) {s : Set Ω} :
    s ∈ toNonUnitalSubring hA ↔ s ∈ A :=
  Iff.rfl

/-- Exercise 1.1.5: A ring of subsets of `Ω` carries the structure of a commutative non-unital
ring, with multiplication given by intersection and addition given by symmetric difference. -/
instance subtype_nonUnitalCommRing (hA : IsSetRing A) :
    NonUnitalCommRing {s : Set Ω // s ∈ A} :=
  (toNonUnitalSubring hA).toNonUnitalCommRing

end IsSetRing
