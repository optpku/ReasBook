/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

variable {B : Type u} [Groupoid.{v} B]

/-- The vertex group at `b` acts on the star of arrows with source `b` by precomposition with
inverse loops. This is the same canonical `MulAction.ofEndHom` owner pattern used for vertex-group
actions elsewhere in the chapter. -/
instance orbitCoveringHomMulAction (b x : B) : MulAction (End b) (b ⟶ x) :=
  MulAction.ofEndHom
    { toFun := fun g ↦ fun f ↦ g⁻¹ ≫ f
      map_one' := by
        funext f
        simp [Function.End.one_def]
      map_mul' := by
        intro g h
        funext f
        simp [Function.End.mul_def, Category.assoc] }

/-- The orbit-covering action evaluates a loop by precomposing with its inverse. -/
@[simp] theorem orbitCoveringHomMulAction_smul (b x : B) (g : End b) (f : b ⟶ x) :
    g • f = g⁻¹ ≫ f :=
  rfl

/-- Construction 3.6.2: the objects of the covering attached to `H ≤ π(B,b)` are the right
`H`-cosets of arrows in the star of `b`; concretely, over each object `x : B` they are the
quotient of `b ⟶ x` by the precomposition action of `H`. -/
abbrev orbitCoveringObj (b : B) (H : Subgroup (End b)) : Type (max u v) :=
  Σ x : B, MulAction.orbitRel.Quotient H (b ⟶ x)

/-- The first component of an object of the orbit covering is its image in the base groupoid. -/
@[simp] theorem orbitCoveringObj_fst (b : B) (H : Subgroup (End b))
    (x : B) (q : MulAction.orbitRel.Quotient H (b ⟶ x)) :
    Sigma.fst ((⟨x, q⟩ : orbitCoveringObj b H)) = x :=
  rfl

/-- The object of the covering represented by the right coset of an arrow `f : b ⟶ x`. -/
abbrev orbitCoveringObjOfHom (b : B) (H : Subgroup (End b)) {x : B} (f : b ⟶ x) :
    orbitCoveringObj b H :=
  ⟨x, Quotient.mk'' f⟩

/-- The projection from the source-facing object set of `E(G/H)` to the base groupoid remembers
the target of the represented arrow. -/
abbrev orbitCoveringProjection (b : B) (H : Subgroup (End b)) :
    orbitCoveringObj b H → B :=
  Sigma.fst

/-- The projection of the coset represented by `f` is the target of `f`. -/
@[simp] theorem orbitCoveringProjection_ofHom (b : B) (H : Subgroup (End b))
    {x : B} (f : b ⟶ x) :
    orbitCoveringProjection b H (orbitCoveringObjOfHom b H f) = x := rfl
