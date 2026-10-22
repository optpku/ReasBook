/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_1
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_1

universe u

/-- An element is a proper power if it is an `m`th power for some exponent `m > 1`. -/
def IsProperPower {M : Type u} [Monoid M] (x : M) : Prop :=
  ∃ y : M, ∃ m : ℕ, 1 < m ∧ y ^ m = x

/-- An element is primitive if it belongs to some free basis of the ambient group. -/
def IsPrimitiveElement {F : Type u} [Group F] (p : F) : Prop :=
  ∃ (Y : Type u) (basis : FreeGroupBasis Y F) (y : Y), basis y = p

namespace IsPrimitiveElement

/-- Primitive elements stay primitive under free-group automorphisms. -/
theorem map {F : Type u} [Group F] {p : F} (hp : IsPrimitiveElement p) (e : MulAut F) :
    IsPrimitiveElement (e p) := by
  rcases hp with ⟨Y, basis, y, rfl⟩
  exact ⟨Y, basis.map e, y, rfl⟩

/-- The inverse of a primitive element is primitive. -/
theorem inv {F : Type u} [Group F] {p : F} (hp : IsPrimitiveElement p) :
    IsPrimitiveElement p⁻¹ := by
  rcases hp with ⟨Y, basis, y, rfl⟩
  exact ⟨Y, basis.map (basis.elementaryNielsenInversion y), y, by simp⟩

/-- Primitive elements are preserved under conjugacy. -/
theorem of_isConj {F : Type u} [Group F] {p q : F} (hp : IsPrimitiveElement p)
    (hconj : IsConj q p) : IsPrimitiveElement q := by
  rcases isConj_iff.1 hconj with ⟨c, hc⟩
  have hq : q = c⁻¹ * p * c := by
    simpa [mul_assoc] using congrArg (fun z ↦ c⁻¹ * z * c) hc
  rw [hq]
  simpa [MulAut.conj_apply, mul_assoc] using hp.map (MulAut.conj c⁻¹)

end IsPrimitiveElement

universe v

namespace FreeGroupBasis

/-- Every element of a free basis is primitive. -/
theorem isPrimitiveElement {F : Type u} [Group F] {X : Type v}
    (basis : FreeGroupBasis X F) (x : X) : IsPrimitiveElement (basis x) := by
  exact ⟨Set.range basis, basis.reindexRange, ⟨basis x, ⟨x, rfl⟩⟩, by simp⟩

end FreeGroupBasis

def combinatorialGroupTheoryHello := "world"
