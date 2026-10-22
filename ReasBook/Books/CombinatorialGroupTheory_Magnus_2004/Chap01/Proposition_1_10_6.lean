/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_10_4
import Mathlib.GroupTheory.SemidirectProduct

noncomputable section

universe u

/- Proposition 1-10-6 lies in Fox calculus for free groups.

Layer triage:
- `source-facing`: the faithful Fox triangular representation of `FreeGroup X`.
- `core/canonical`: `MonoidAlgebra.comapDistribMulActionSelf`, the induced `Finsupp` action on the
  Fox module, `FreeGroup.lift`, and `SemidirectProduct.rightHom`.
- `bridge/view`: the universal differential as the left coordinate of the triangular map, together
  with the pair formula `(d w, w)`.

Domain sampling:
1. `MonoidAlgebra.comapDistribMulActionSelf` is the mathlib owner for left multiplication of
   `FreeGroup X` on its integral group ring.
2. `X →₀ FreeGroupRing X` inherits the coefficientwise owner action from that ring action, so the
   previous hand-written `smul` helper was duplicate surface.
3. `FreeGroup.lift` is the owner abstraction for defining the representation from its generator
   values.
4. `SemidirectProduct.rightHom` is the owner projection detecting faithfulness.

Primitive vs. derived:
the primitive public data are the Fox module, the semidirect-product target, and the triangular
representation; the universal differential and the pair description are derived coordinate API.
-/

instance (X : Type u) : DistribMulAction (FreeGroup X) (FreeGroupRing X) :=
  MonoidAlgebra.comapDistribMulActionSelf

/-- The free left `ℤ[FreeGroup X]`-module on the formal symbols `dx`, modeled as finitely
supported coefficient families. -/
abbrev foxDifferentialModule (X : Type u) := X →₀ FreeGroupRing X

instance foxDifferentialModuleMulDistribMulAction (X : Type u) :
    MulDistribMulAction (FreeGroup X) (Multiplicative (foxDifferentialModule X)) where
  smul g d := Additive.toMul (g • d.toAdd)
  one_smul d := by
    cases d with
    | ofAdd a =>
        change Multiplicative.ofAdd ((1 : FreeGroup X) • a) = Multiplicative.ofAdd a
        exact congrArg Multiplicative.ofAdd (by simp : (1 : FreeGroup X) • a = a)
  mul_smul g h d := by
    cases d with
    | ofAdd a =>
        change Multiplicative.ofAdd ((g * h) • a) = Multiplicative.ofAdd (g • (h • a))
        exact congrArg Multiplicative.ofAdd (by simp [mul_smul] : (g * h) • a = g • (h • a))
  smul_mul g d e := by
    cases d with
    | ofAdd a =>
        cases e with
        | ofAdd b =>
            change Multiplicative.ofAdd (g • (a + b)) = Multiplicative.ofAdd (g • a + g • b)
            exact congrArg Multiplicative.ofAdd
              (by simp [smul_add] : g • (a + b) = g • a + g • b)
  smul_one g := by
    change Multiplicative.ofAdd (g • (0 : foxDifferentialModule X)) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (by simp : g • (0 : foxDifferentialModule X) = 0)

/-- The canonical semidirect-product target for the Fox triangular representation, corresponding to
upper triangular matrices whose upper-right entry lies in the Fox differential module. -/
abbrev foxTriangularRepresentationTarget (X : Type u) :=
  Multiplicative (foxDifferentialModule X) ⋊[
    MulDistribMulAction.toMulAut (FreeGroup X) (Multiplicative (foxDifferentialModule X))]
    FreeGroup X

/-- The canonical Fox triangular representation of `FreeGroup X`, written in semidirect-product
form rather than as a literal upper triangular matrix group. -/
def foxTriangularRepresentation (X : Type u) :
    FreeGroup X →* foxTriangularRepresentationTarget X :=
  FreeGroup.lift fun x ↦
    (⟨Additive.toMul (Finsupp.single x (1 : FreeGroupRing X)), FreeGroup.of x⟩ :
      foxTriangularRepresentationTarget X)

/-- The universal Fox differential `d : FreeGroup X → foxDifferentialModule X`, extracted as the
upper-right coordinate of the triangular representation. -/
def foxUniversalDifferential {X : Type u} (w : FreeGroup X) : foxDifferentialModule X :=
  (foxTriangularRepresentation X w).left.toAdd

private theorem foxTriangularRepresentation_right {X : Type u} (w : FreeGroup X) :
    SemidirectProduct.rightHom (foxTriangularRepresentation X w) = w := by
  change ((SemidirectProduct.rightHom.comp (foxTriangularRepresentation X)) w) = w
  have hcomp : SemidirectProduct.rightHom.comp (foxTriangularRepresentation X) = MonoidHom.id _ := by
    ext x
    simp [foxTriangularRepresentation]
  simp [hcomp]

/-- The semidirect-product form of the Fox representation is the pair `(d w, w)`. -/
theorem foxTriangularRepresentation_eq_pair {X : Type u} (w : FreeGroup X) :
    foxTriangularRepresentation X w =
      (⟨Additive.toMul (foxUniversalDifferential w), w⟩ :
        foxTriangularRepresentationTarget X) := by
  ext
  · rfl
  · exact foxTriangularRepresentation_right w

/-- Proposition 1-10-6: the Fox differential determines a well-defined faithful triangular
representation of `FreeGroup X`; in Lean this is packaged as `foxTriangularRepresentation`. -/
theorem foxTriangularRepresentation_injective (X : Type u) :
    Function.Injective (foxTriangularRepresentation X) := by
  intro u v h
  have h' := congrArg SemidirectProduct.rightHom h
  rw [foxTriangularRepresentation_right, foxTriangularRepresentation_right] at h'
  exact h'
