/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_7
import AlgebraicTopology_May_1999.Chap03.Proposition_3_3_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open FundamentalGroupoid
open Path.Homotopic.Quotient
open CategoryTheory.Functor.IsCovering
open scoped Cardinal

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Fiber translation along a morphism of the base groupoid is a bijection between the
corresponding fibers. -/
-- Proof sketch: `fiberTranslationFunctor hp` sends the isomorphism `asIso f` in the base groupoid
-- to an isomorphism of fibers in `Type`, whose underlying equivalence is bijective.
theorem fiberTranslationMap_bijective (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') :
    Function.Bijective (fiberTranslationMap hp f) := by
  simpa using ((fiberTranslationFunctor hp).mapIso (asIso f)).toEquiv.bijective

/-- Proposition 3.3.10: fibers over base objects connected by a morphism in a covering functor of
groupoids have the same cardinality, and hence so do the corresponding fibers of a covering space
after passing to fundamental groupoids. -/
-- Proof sketch: apply `Cardinal.mk_congr` to the equivalence of fibers induced by
-- `fiberTranslationFunctor hp` on the isomorphism `asIso f`.
theorem fiber_cardinal_eq_of_hom (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') :
    #(p.Fiber b) = #(p.Fiber b') := by
  simpa using Cardinal.mk_congr (((fiberTranslationFunctor hp).mapIso (asIso f)).toEquiv)

/-- Proposition 3.3.10: for a covering functor of groupoids over a connected base groupoid,
any two fibers have the same cardinality. -/
-- Proof sketch: in a connected groupoid there exists a morphism between any two objects, so the
-- explicit-arrow case `fiber_cardinal_eq_of_hom` applies.
theorem fiber_cardinal_eq [CategoryTheory.IsConnected B] (hp : Functor.IsCovering p) (b b' : B) :
    #(p.Fiber b) = #(p.Fiber b') := by
  let ⟨f⟩ := (inferInstance : Nonempty (b ⟶ b'))
  exact fiber_cardinal_eq_of_hom hp f

end CategoryTheory.Functor.IsCovering

namespace IsPathConnectedCoveringMap

variable {E : Type u₁} {B : Type u₂} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B}

/-- The covering-space form of Proposition 3.3.10: over a path-connected base, any two fibers of a
path-connected covering map have the same cardinality. -/
-- Proof sketch: apply the connected-groupoid statement to the induced covering functor on
-- fundamental groupoids and transport its fibers back to ordinary fibers via
-- `fundamentalGroupoidMapFiberEquiv`.
theorem fiber_cardinal_eq (hp : IsPathConnectedCoveringMap p) [PathConnectedSpace B] (b b' : B) :
    #(p ⁻¹' {b}) = #(p ⁻¹' {b'}) := by
  let f : mk b ⟶ mk b' :=
    fromPath (mk (PathConnectedSpace.somePath b b'))
  calc
    #(p ⁻¹' {b}) = #(hp.fundamentalGroupoidMap.Fiber (mk b)) := by
      simpa using Cardinal.mk_congr (hp.fundamentalGroupoidMapFiberEquiv b).symm
    _ = #(hp.fundamentalGroupoidMap.Fiber (mk b')) := by
      exact fiber_cardinal_eq_of_hom hp.fundamentalGroupoidMap_isCovering f
    _ = #(p ⁻¹' {b'}) := by
      simpa using Cardinal.mk_congr (hp.fundamentalGroupoidMapFiberEquiv b')

end IsPathConnectedCoveringMap
