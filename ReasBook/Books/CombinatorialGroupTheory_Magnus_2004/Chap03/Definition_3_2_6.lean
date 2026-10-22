/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_1

universe u v

open CategoryTheory
open Quiver

-- Layer triage:
-- `source-facing`: the `1`-equivalence relation on paths and the resulting fundamental groupoid
-- `Π¹(C)`.
-- `core/canonical`: `CategoryTheory.Paths` is the owner abstraction for the path category,
-- `Relation.EqvGen` is the owner abstraction for generated equivalence relations, and
-- `CategoryTheory.Quotient` is the owner abstraction for quotient categories.
-- `bridge/view`: `Quiver.Path.pathOneHomRel` packages the source relation as a categorical
-- congruence so that `Π¹(C)` is a thin source-facing notation for the quotient category.
-- Domain sampling:
-- 1. `Relation.EqvGen` and `Relation.EqvGen.setoid` encode the generated equivalence relation.
-- 2. `CategoryTheory.Paths` is mathlib's owner category for paths in a quiver.
-- 3. `CategoryTheory.HomRel` and `CategoryTheory.Congruence` are the owner abstractions for a
--    quotient relation compatible with composition.
-- 4. `CategoryTheory.Quotient` is the canonical owner for the quotient category surface.
-- Primitive vs. derived:
-- the primitive source data are the elementary cancellation step and the generated
-- `path_one_equiv`; the quotient-category surface and the resulting groupoid structure are
-- derived from that relation.

namespace Quiver.Path

variable {V : Type u} [Quiver.{v} V] [Quiver.HasInvolutiveReverse V]

/-- A single elementary `1`-equivalence step inserts or deletes one backtracking segment
`ee⁻¹` inside a path. -/
def path_one_reduction_step {a b : V} (p q : Quiver.Path a b) : Prop :=
  ∃ (c d : V) (r : Quiver.Path a c) (e : c ⟶ d) (s : Quiver.Path c b),
    (p = (r.comp (e.toPath.comp (Quiver.reverse e).toPath)).comp s ∧ q = r.comp s) ∨
      (q = (r.comp (e.toPath.comp (Quiver.reverse e).toPath)).comp s ∧ p = r.comp s)

/-- Definition 3-2-6: two paths are `1`-equivalent when one can pass from one to the other by a
finite succession of insertions or deletions of subpaths of the form `ee⁻¹`. -/
def path_one_equiv {a b : V} (p q : Quiver.Path a b) : Prop :=
  Relation.EqvGen path_one_reduction_step p q

/-- `1`-equivalence is reflexive on paths. -/
theorem path_one_equiv_refl {a b : V} (p : Quiver.Path a b) : path_one_equiv p p :=
  Relation.EqvGen.refl p

/-- `1`-equivalence is symmetric on paths. -/
theorem path_one_equiv_symm {a b : V} {p q : Quiver.Path a b} (h : path_one_equiv p q) :
    path_one_equiv q p := by
  exact Relation.EqvGen.symm _ _ h

/-- `1`-equivalence is transitive on paths. -/
theorem path_one_equiv_trans {a b : V} {p q r : Quiver.Path a b}
    (hpq : path_one_equiv p q) (hqr : path_one_equiv q r) : path_one_equiv p r := by
  exact Relation.EqvGen.trans _ _ _ hpq hqr

/-- Path concatenation respects `1`-equivalence on both factors. -/
-- Proof sketch: first show that an elementary cancellation step remains elementary after
-- adjoining fixed prefix and suffix paths, then lift that statement through `Relation.EqvGen`.
theorem path_one_equiv_comp {a b c : V} {p p' : Quiver.Path a b} {q q' : Quiver.Path b c}
    (hp : path_one_equiv p p') (hq : path_one_equiv q q') :
    path_one_equiv (p.comp q) (p'.comp q') := sorry

/-- Path reversal respects `1`-equivalence. -/
-- Proof sketch: reversing an elementary inserted spur `ee⁻¹` produces another spur of the same
-- form inside the reversed path, and then `Relation.EqvGen` lifts this observation.
theorem path_one_equiv_reverse {a b : V} {p q : Quiver.Path a b} (h : path_one_equiv p q) :
    path_one_equiv p.reverse q.reverse := sorry

/-- A path followed by its inverse is `1`-equivalent to the empty path. -/
-- Proof sketch: induct on the path length, peel off the last edge, cancel the resulting terminal
-- backtracking pair, and use transitivity of `path_one_equiv`.
theorem comp_reverse_path_one_equiv_nil {a b : V} (p : Quiver.Path a b) :
    path_one_equiv (p.comp p.reverse) (Path.nil : Quiver.Path a a) := sorry

/-- The congruence on the path category whose quotient is the fundamental groupoid `Π¹(C)`. -/
def pathOneHomRel (V : Type u) [Quiver.{v} V] [Quiver.HasInvolutiveReverse V] :
    HomRel (CategoryTheory.Paths V) :=
  fun _ _ p q ↦ path_one_equiv p q

instance pathOneHomRel_congruence : Congruence (pathOneHomRel (V := V)) where
  equivalence := by
    intro a b
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact path_one_equiv_refl p
    · intro p q
      exact path_one_equiv_symm
    · intro p q r
      exact path_one_equiv_trans
  comp_left := by
    intro a b c f g g' h
    simpa [pathOneHomRel] using path_one_equiv_comp (path_one_equiv_refl f) h
  comp_right := by
    intro a b c f f' g h
    simpa [pathOneHomRel] using path_one_equiv_comp h (path_one_equiv_refl g)

/-- Definition 3-2-6: the fundamental groupoid `Π¹(C)` is the quotient of the path category by
`1`-equivalence. -/
abbrev pi1 (V : Type u) [Quiver.{v} V] [Quiver.HasInvolutiveReverse V] :=
  CategoryTheory.Quotient (pathOneHomRel (V := V))

notation "Π¹" "(" C ")" => Quiver.Path.pi1 C

private def pi1Inv {a b : Π¹(V)} (f : a ⟶ b) : b ⟶ a :=
  Quot.liftOn f
    (fun p ↦ Quot.mk _ p.reverse)
    (fun _ _ h ↦
      Quot.sound <| by
        rw [HomRel.compClosure_iff_self]
        exact path_one_equiv_reverse <| by
          rw [HomRel.compClosure_iff_self] at h
          exact h)

/-- Every morphism in `Π¹(C)` is invertible, with inverse induced by path reversal. -/
instance pi1_isIso {a b : Π¹(V)} (f : a ⟶ b) : IsIso f where
  out := ⟨pi1Inv f, by sorry, by sorry⟩

/-- The quotient category `Π¹(C)` is a groupoid. -/
noncomputable instance pi1_groupoid : Groupoid (Π¹(V)) :=
  Groupoid.ofIsIso fun f ↦ pi1_isIso f

end Quiver.Path

namespace OneComplex

open CategoryTheory
open scoped Quiver.Path

variable (C : OneComplex.{u, v}) (w : C)

/-- The source-facing fundamental group `π(C, w)` is the endomorphism group at `w` in the
fundamental groupoid `Π¹(C)`. -/
abbrev fundamentalGroup (C : OneComplex.{u, v}) (w : C) :=
  End (⟨w⟩ : Π¹(C))

scoped notation "π(" C ", " w ")" => OneComplex.fundamentalGroup C w

/-- The notation `π(C, w)` is the endomorphism group of the object `w` in the fundamental
groupoid `Π¹(C)`. -/
theorem fundamentalGroup_eq_end (C : OneComplex.{u, v}) (w : C) :
    π(C, w) = End (⟨w⟩ : Π¹(C)) :=
  rfl

/-- The fundamental group at `w` inherits a group structure from the groupoid structure on
`Π¹(C)`. -/
noncomputable instance fundamentalGroupGroup (C : OneComplex.{u, v}) (w : C) :
    Group (π(C, w)) :=
  inferInstance

end OneComplex
