/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

/-- The chosen basepoint of a based space in `Under (⊤_ TopCat)`. -/
noncomputable def underTopBasepoint (X : Under (⊤_ TopCat)) : X.right :=
  X.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)

/-- A morphism of based spaces sends the chosen basepoint to the chosen basepoint. -/
-- Proof sketch: evaluate the commutative triangle `X.hom ≫ f.right = Y.hom` at the unique point
-- of the terminal space, namely `TopCat.terminalIsoPUnit.inv PUnit.unit`.
theorem fundamentalGroupFunctorMap_basepoint {X Y : Under (⊤_ TopCat)} (f : X ⟶ Y) :
    f.right.hom (underTopBasepoint X) = underTopBasepoint Y := by
  change
    (X.hom ≫ f.right) (TopCat.terminalIsoPUnit.inv PUnit.unit) =
      Y.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)
  rw [CategoryTheory.Under.w f]

/-- The induced homomorphism on fundamental groups respects identity morphisms. -/
-- Proof sketch: the identity map of a based space induces the identity endomorphism on its
-- vertex group in the fundamental groupoid, and `mapOfEq` uses the trivial basepoint equality.
theorem fundamentalGroupFunctor_map_id (X : Under (⊤_ TopCat)) :
    GrpCat.ofHom
        (FundamentalGroup.mapOfEq (𝟙 X : X ⟶ X).right.hom
          (fundamentalGroupFunctorMap_basepoint (𝟙 X : X ⟶ X))) =
      𝟙 (GrpCat.of (FundamentalGroup X.right (underTopBasepoint X))) := by
  have hhom :
      FundamentalGroup.mapOfEq (𝟙 X : X ⟶ X).right.hom
        (fundamentalGroupFunctorMap_basepoint (𝟙 X : X ⟶ X)) =
      MonoidHom.id (FundamentalGroup X.right (underTopBasepoint X)) := by
    ext γ
    refine Quotient.inductionOn γ ?_
    intro p
    -- On a representative loop, `mapOfEq` for the identity morphism returns the same loop class.
    have hmap :=
      FundamentalGroup.mapOfEq_apply
        (f := (𝟙 X : X ⟶ X).right.hom)
        (h := fundamentalGroupFunctorMap_basepoint (𝟙 X : X ⟶ X))
        (p := p)
    simpa using hmap
  -- Convert the equality of group homomorphisms into equality in `GrpCat`.
  simpa using congrArg GrpCat.ofHom hhom

/-- The induced homomorphism on fundamental groups respects composition. -/
-- Proof sketch: functoriality follows from the corresponding composition law for
-- `FundamentalGroup.mapOfEq`, together with compatibility of the basepoint equalities under
-- composition of based maps.
theorem fundamentalGroupFunctor_map_comp {X Y Z : Under (⊤_ TopCat)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    GrpCat.ofHom
        (FundamentalGroup.mapOfEq (f ≫ g).right.hom
          (fundamentalGroupFunctorMap_basepoint (f ≫ g))) =
      GrpCat.ofHom
          (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f)) ≫
        GrpCat.ofHom
          (FundamentalGroup.mapOfEq g.right.hom (fundamentalGroupFunctorMap_basepoint g)) := by
  have hhom :
      FundamentalGroup.mapOfEq (f ≫ g).right.hom
        (fundamentalGroupFunctorMap_basepoint (f ≫ g)) =
      (FundamentalGroup.mapOfEq g.right.hom (fundamentalGroupFunctorMap_basepoint g)).comp
        (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f)) := by
    ext γ
    refine Quotient.inductionOn γ ?_
    intro p
    let pf : Path (underTopBasepoint Y) (underTopBasepoint Y) :=
      (p.map f.right.hom.continuous).cast
        (fundamentalGroupFunctorMap_basepoint f).symm
        (fundamentalGroupFunctorMap_basepoint f).symm
    -- Rewrite both sides on the representative loop `p` using the explicit `mapOfEq_apply`
    -- formula, so the statement reduces to the standard path-level composition.
    have hfg :=
      FundamentalGroup.mapOfEq_apply
        (f := (f ≫ g).right.hom)
        (h := fundamentalGroupFunctorMap_basepoint (f ≫ g))
        (p := p)
    have hf :=
      FundamentalGroup.mapOfEq_apply
        (f := f.right.hom)
        (h := fundamentalGroupFunctorMap_basepoint f)
        (p := p)
    have hg :=
      FundamentalGroup.mapOfEq_apply
        (f := g.right.hom)
        (h := fundamentalGroupFunctorMap_basepoint g)
        (p := pf)
    change
      FundamentalGroup.mapOfEq (f ≫ g).right.hom (fundamentalGroupFunctorMap_basepoint (f ≫ g))
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
        ((FundamentalGroup.mapOfEq g.right.hom (fundamentalGroupFunctorMap_basepoint g)).comp
          (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f)))
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
    rw [hfg]
    simp only [MonoidHom.comp_apply]
    rw [hf, hg]
    -- After the explicit rewrites, the two quotient classes coincide definitionally.
    congr 1
  -- Convert the equality of underlying homomorphisms into equality in `GrpCat`.
  simpa using congrArg GrpCat.ofHom hhom

/-- Lemma 2.4.2: the fundamental group defines a functor from based spaces to groups. -/
noncomputable def fundamentalGroupFunctor : Under (⊤_ TopCat) ⥤ GrpCat where
  obj X := GrpCat.of (FundamentalGroup X.right (underTopBasepoint X))
  map f :=
    GrpCat.ofHom (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f))
  map_id := fundamentalGroupFunctor_map_id
  map_comp := fundamentalGroupFunctor_map_comp

/-- The morphism part of `fundamentalGroupFunctor` is the induced map on fundamental groups. -/
-- Proof sketch: unfold `fundamentalGroupFunctor`; its `map` field was defined to be
-- `GrpCat.ofHom (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f))`.
theorem fundamentalGroupFunctor_map_eq {X Y : Under (⊤_ TopCat)} (f : X ⟶ Y) :
    fundamentalGroupFunctor.map f =
      GrpCat.ofHom
        (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f)) :=
  rfl
