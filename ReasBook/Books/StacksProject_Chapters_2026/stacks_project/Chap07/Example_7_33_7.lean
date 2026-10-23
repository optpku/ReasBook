module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.GSetForgetfulPoint
public import stacks_project.Chap07.Lemma_7_32_7
public import stacks_project.Chap07.Lemma_7_32_9
public import stacks_project.Chap07.Proposition_7_9_1

@[expose] public section

open CategoryTheory Limits Opposite
open GrothendieckTopology.Point

universe u

namespace CategoryTheory

noncomputable section

open scoped MorphismOfTopoiIn

variable (G : Type u) [Group G]

/- Domain-style sampling for Example 7.33.7:
- sampled owner declarations:
  `Point.skyscraperSheafFunctor`,
  `Point.toToposPoint_pointPushforwardIso`,
  `sheafSectionsOnLeftRegularFunctor`,
  `gSetForgetfulPointMapMulAction`;
- core/canonical owners:
  the direct-image/skyscraper owner of the point `gSetForgetfulPoint G`,
  together with the left-regular-sections functor from Proposition 7.9.1;
- source-facing declarations in this file:
  the fiber comparison `p⁻¹(p_* S) ≃ Map(G, S)` and the resulting action-level description of
  `p_* S`;
- primitive data:
  the point `gSetForgetfulPoint G`, its left regular object, and the chapter's canonical
  right-translation action on `G → S`;
- derived API:
  the objectwise `Map(G, S)` equivalence and the section/counit comparison theorems.
-/

noncomputable abbrev gSetForgetfulPoint_pushforwardObj
    (S : Type u) :
    Sheaf (Action.jointlySurjectiveTopology G) (Type u) :=
  ((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S

/-- The value of `p_* S` on the left regular `G`-set is canonically the set `Map(G, S)`. -/
noncomputable abbrev pushforwardLeftRegularObjEquiv
    (S : Type u) :
    ((gSetForgetfulPoint_pushforwardObj G S).1.obj (op (Action.leftRegular G))) ≃
      (G → S) :=
  let Φ := gSetForgetfulPoint G
  let e' :
      ((gSetForgetfulPoint_pushforwardObj G S).1.obj (op (Action.leftRegular G))) ≃
        (Φ.skyscraperPresheaf S).obj (op (Action.leftRegular G)) :=
    (((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj (op (Action.leftRegular G))).mapIso
      ((sheafToPresheaf _ _).mapIso
        ((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S))).toEquiv
  e'.trans
    (Types.productIso (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)).toEquiv

/-- The canonical map `Map(G, S) → p^{-1}(p_* S)` obtained from the generator `1 ∈ G` of the left
regular `G`-set. -/
noncomputable def gSetForgetfulPoint_pushforwardFiberMap
    (S : Type u) (ψ : G → S) :
    ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S) :=
    let Φ := gSetForgetfulPoint G
    let F := gSetForgetfulPoint_pushforwardObj G S
    let x :
        Φ.sheafFiber.obj F :=
      Φ.toPresheafFiber (Action.leftRegular G)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
        F.1
        ((pushforwardLeftRegularObjEquiv G S).symm ψ)
    ((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso Φ).app F).inv x

/-- Helper for Example 7.33.7: the distinguished object `({}_G G, 1)` in the element category of
the forgetful fiber functor. -/
noncomputable abbrev leftRegularBaseObj :
    (gSetForgetfulPoint G).fiber.Elements :=
  (gSetForgetfulPoint G).fiber.elementsMk (Action.leftRegular G) ((1 : G) : G)

/-- Helper for Example 7.33.7: the orbit map out of the left regular `G`-set through a chosen
point of a `G`-set. -/
def left_regular_hom_of_point {U : Action (Type u) G} (u : U.V) :
    Action.leftRegular G ⟶ U where
  hom := fun g ↦ U.ρ (show G from g) u
  comm := by
    -- Multiplication in the left regular action records the orbit relation.
    intro g
    ext h
    exact congrFun (MonoidHom.map_mul U.ρ (show G from g) (show G from h)) u

/-- Helper for Example 7.33.7: the point `(Action.leftRegular G, 1)` is initial in the element
category of the forgetful point. -/
noncomputable def left_regular_one_isInitial :
    IsInitial (leftRegularBaseObj G) := by
  letI : ∀ Y : (gSetForgetfulPoint G).fiber.Elements, Unique (leftRegularBaseObj G ⟶ Y) :=
    fun Y ↦
      let f0 : leftRegularBaseObj G ⟶ Y := ⟨left_regular_hom_of_point G Y.2, by
        -- The orbit map sends `1` to the chosen point.
        change (left_regular_hom_of_point G Y.2).hom ((1 : G) : G) = Y.2
        simp [left_regular_hom_of_point]⟩
      { default := f0
        uniq := by
          intro f
          apply CategoryOfElements.ext (gSetForgetfulPoint G).fiber f f0
          -- An equivariant map out of the left regular action is determined by the value at `1`.
          apply Action.hom_ext
          ext g
          have hbase : f.1.hom ((1 : G) : G) = Y.2 := f.2
          have hcomm := congrFun (f.1.comm (show G from g)) (show G from ((1 : G) : G))
          simp only [types_comp_apply] at hcomm
          rw [hbase] at hcomm
          simpa [f0, left_regular_hom_of_point] using hcomm }
  exact IsInitial.ofUnique _

/-- Helper for Example 7.33.7: the opposite of `({}_G G, 1)` is terminal in the opposite element
category. -/
noncomputable abbrev leftRegularTerminalObj :
    (gSetForgetfulPoint G).fiber.Elementsᵒᵖ :=
  op (leftRegularBaseObj G)

/-- Helper for Example 7.33.7: the terminal object in the opposite element category controlling
the fiber colimit. -/
noncomputable def leftRegularTerminal :
    IsTerminal (leftRegularTerminalObj G) :=
  terminalOpOfInitial (left_regular_one_isInitial G)

/-- Helper for Example 7.33.7: the presheaf fiber at the forgetful point is evaluation on the
left regular `G`-set. -/
noncomputable def gSetForgetfulPoint_presheafFiberObjIso_leftRegular
    (P : (Action (Type u) G)ᵒᵖ ⥤ Type u) :
    (gSetForgetfulPoint G).presheafFiber.obj P ≅ P.obj (op (Action.leftRegular G)) := by
  let Q := (CategoryOfElements.π (gSetForgetfulPoint G).fiber).op ⋙ P
  change colimit Q ≅ Q.obj (leftRegularTerminalObj G)
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitOfDiagramTerminal
    (leftRegularTerminal G) Q)

/-- Helper for Example 7.33.7: the canonical map from the left regular section into the fiber
becomes the identity after the evaluation comparison. -/
lemma toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom
    (P : (Action (Type u) G)ᵒᵖ ⥤ Type u) :
    (gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
        ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) P ≫
      (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P).hom =
        𝟙 (P.obj (op (Action.leftRegular G))) := by
  -- The defining colimit leg from the terminal object becomes the identity map.
  simpa [gSetForgetfulPoint_presheafFiberObjIso_leftRegular, GrothendieckTopology.Point.presheafFiber,
    leftRegularTerminalObj, leftRegularTerminal] using
    (colimit.comp_coconePointUniqueUpToIso_hom
      (hc := colimitOfDiagramTerminal (leftRegularTerminal G)
        ((CategoryOfElements.π (gSetForgetfulPoint G).fiber).op ⋙ P))
      (op (leftRegularBaseObj G)))

/-- Helper for Example 7.33.7: the fiber leg at any point factors through the orbit map from
`({}_G G, 1)`. -/
lemma toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom_apply
    (P : (Action (Type u) G)ᵒᵖ ⥤ Type u) (X : Action (Type u) G)
    (x : (gSetForgetfulPoint G).fiber.obj X) :
    (gSetForgetfulPoint G).toPresheafFiber X x P ≫
      (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P).hom =
        P.map (left_regular_hom_of_point G x).op := by
  have hw :
      P.map (left_regular_hom_of_point G x).op ≫
          (gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
            ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) P =
        (gSetForgetfulPoint G).toPresheafFiber X x P := by
    have hx :
        (gSetForgetfulPoint G).fiber.map (left_regular_hom_of_point G x)
          ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) = x := by
      change X.ρ 1 x = x
      exact congrFun (MonoidHom.map_one X.ρ) x
    simpa [hx] using
      (gSetForgetfulPoint G).toPresheafFiber_w (left_regular_hom_of_point G x)
        ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) P
  -- Move the comparison to `({}_G G, 1)` using the canonical orbit map.
  calc
    (gSetForgetfulPoint G).toPresheafFiber X x P ≫
        (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P).hom =
      P.map (left_regular_hom_of_point G x).op ≫
        (gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
          ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) P ≫
          (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P).hom := by
            rw [← hw, Category.assoc]
    _ = P.map (left_regular_hom_of_point G x).op := by
      rw [toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom]
      simp

/-- Helper for Example 7.33.7: the fiber functor on sheaves is evaluation on the left regular
`G`-set. -/
noncomputable def gSetForgetfulPoint_sheafFiberIso_leftRegular :
    (gSetForgetfulPoint G).sheafFiber ≅
      sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u) ⋙
        (evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj (op (Action.leftRegular G)) := by
  simpa [GrothendieckTopology.Point.sheafFiber] using
    Functor.isoWhiskerLeft
      (sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u))
      (NatIso.ofComponents
        (fun P ↦ gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P)
        (by
          intro P Q f
          apply (gSetForgetfulPoint G).presheafFiber_hom_ext
          intro X x
          rw [toPresheafFiber_naturality_assoc]
          calc
            (f.app (op X) ≫
                (gSetForgetfulPoint G).toPresheafFiber X x Q) ≫
                  (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G Q).hom =
                f.app (op X) ≫
                  ((gSetForgetfulPoint G).toPresheafFiber X x Q ≫
                    (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G Q).hom) := by
                      simp [Category.assoc]
            _ = f.app (op X) ≫ Q.map (show Action.leftRegular G ⟶ X from
                  left_regular_hom_of_point G x).op := by
                  rw [toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom_apply]
            _ = P.map (show Action.leftRegular G ⟶ X from left_regular_hom_of_point G x).op ≫
                  ((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj
                    (op (Action.leftRegular G))).map f := by
                  simpa using
                    (NatTrans.naturality f
                      (show op X ⟶ op (Action.leftRegular G) from
                        (show Action.leftRegular G ⟶ X from left_regular_hom_of_point G x).op)).symm
            _ = (gSetForgetfulPoint G).toPresheafFiber X x P ≫
                  (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P).hom ≫
                    ((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj
                      (op (Action.leftRegular G))).map f := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦
                        k ≫ ((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj
                          (op (Action.leftRegular G))).map f)
                      (toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom_apply
                        (G := G) P X x).symm))

/-- Helper for Example 7.33.7: the distinguished left-regular leg becomes the identity after the
sheaf-fiber comparison. -/
lemma toPresheafFiber_gSetForgetfulPoint_sheafFiberIso_leftRegular_hom
    (F : Sheaf (Action.jointlySurjectiveTopology G) (Type u)) :
    (gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
        ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) F.1 ≫
      ((gSetForgetfulPoint_sheafFiberIso_leftRegular G).app F).hom =
        𝟙 (F.1.obj (op (Action.leftRegular G))) := by
  -- This is the sheaf-level restatement of the presheaf comparison above.
  simpa [gSetForgetfulPoint_sheafFiberIso_leftRegular] using
    toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom (G := G) F.1

/-- Helper for Example 7.33.7: the point fiber of `p_* S` is canonically the function type
`Map(G, S)`. -/
noncomputable def gSetForgetfulPoint_pushforwardFiberIso
    (S : Type u) :
    ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S) ≅
      (G → S) :=
  ((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso
      (gSetForgetfulPoint G)).app (gSetForgetfulPoint_pushforwardObj G S)) ≪≫
    ((gSetForgetfulPoint_sheafFiberIso_leftRegular G).app
      (gSetForgetfulPoint_pushforwardObj G S)) ≪≫
    (pushforwardLeftRegularObjEquiv G S).toIso

/-- Helper for Example 7.33.7: the explicit map `Map(G, S) → p^{-1}(p_* S)` is the inverse of
the canonical fiber comparison. -/
theorem gSetForgetfulPoint_pushforwardFiberIso_hom_map
    (S : Type u) (ψ : G → S) :
    (gSetForgetfulPoint_pushforwardFiberIso G S).hom
      (gSetForgetfulPoint_pushforwardFiberMap G S ψ) = ψ := by
  let Φ := gSetForgetfulPoint G
  let F := gSetForgetfulPoint_pushforwardObj G S
  -- Evaluate the composite comparison on the distinguished left-regular section.
  have hcomp :=
    congrArg
      (fun k : F.1.obj (op (Action.leftRegular G)) ⟶
          F.1.obj (op (Action.leftRegular G)) ↦
        k ((pushforwardLeftRegularObjEquiv G S).symm ψ))
      (toPresheafFiber_gSetForgetfulPoint_sheafFiberIso_leftRegular_hom (G := G) F)
  dsimp [gSetForgetfulPoint_pushforwardFiberIso, gSetForgetfulPoint_pushforwardFiberMap, Φ, F]
  calc
    (pushforwardLeftRegularObjEquiv G S)
        (((gSetForgetfulPoint_sheafFiberIso_leftRegular G).hom.app F)
          (((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso Φ).app F).hom
            (((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso Φ).app F).inv
              ((gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
                ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G))
                F.1
                ((pushforwardLeftRegularObjEquiv G S).symm ψ))))) =
      (pushforwardLeftRegularObjEquiv G S)
        (((gSetForgetfulPoint_sheafFiberIso_leftRegular G).hom.app F)
          ((gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
            ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G))
            F.1
            ((pushforwardLeftRegularObjEquiv G S).symm ψ))) := by
              simp
    _ = ψ := by
      exact ((pushforwardLeftRegularObjEquiv G S).apply_eq_iff_eq_symm_apply).2 hcomp

-- Proof sketch: the sheaf condition on the surjective site identifies the stalk of the
-- skyscraper sheaf `p_* S` with its value on the left regular `G`-set, and the chosen generator
-- `1 ∈ G` yields the inverse direction explicitly.
/-- Example 7.33.7: the canonical map `Map(G, S) → p^{-1}(p_* S)` is bijective. -/
theorem gSetForgetfulPoint_pushforwardFiberMap_bijective
    (S : Type u) :
    Function.Bijective (gSetForgetfulPoint_pushforwardFiberMap G S) :=
  by
    refine ⟨?_, ?_⟩
    · -- The canonical fiber comparison is a left inverse to the explicit map.
      intro ψ₁ ψ₂ h
      have h' := congrArg (fun x ↦ (gSetForgetfulPoint_pushforwardFiberIso G S).hom x) h
      simpa [gSetForgetfulPoint_pushforwardFiberIso_hom_map] using h'
    · -- Surjectivity follows by evaluating an arbitrary fiber point through the comparison iso.
      intro x
      refine ⟨(gSetForgetfulPoint_pushforwardFiberIso G S).hom x, ?_⟩
      have hsurj :
          (gSetForgetfulPoint_pushforwardFiberIso G S).hom
            (gSetForgetfulPoint_pushforwardFiberMap G S
              ((gSetForgetfulPoint_pushforwardFiberIso G S).hom x)) =
            (gSetForgetfulPoint_pushforwardFiberIso G S).hom x := by
        simpa using
          gSetForgetfulPoint_pushforwardFiberIso_hom_map G S
            ((gSetForgetfulPoint_pushforwardFiberIso G S).hom x)
      exact (gSetForgetfulPoint_pushforwardFiberIso G S).toEquiv.injective hsurj

/-- The canonical identification `p^{-1}(p_* S) = Map(G, S)` from Example 7.33.7. -/
noncomputable def gSetForgetfulPoint_pushforwardFiberEquiv
    (S : Type u) :
    ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S) ≃
      (G → S) :=
  (Equiv.ofBijective
    (gSetForgetfulPoint_pushforwardFiberMap G S)
    (gSetForgetfulPoint_pushforwardFiberMap_bijective G S)).symm

@[simp] theorem gSetForgetfulPoint_pushforwardFiberEquiv_symm_apply
    (S : Type u) (ψ : G → S) :
    (gSetForgetfulPoint_pushforwardFiberEquiv G S).symm ψ =
      gSetForgetfulPoint_pushforwardFiberMap G S ψ :=
  rfl

/-- Helper for Example 7.33.7: the `PUnit`-valued explicit fiber map agrees with the canonical
section from Lemma 7.32.9. -/
theorem gSetForgetfulPoint_pushforwardFiberMap_punit :
    gSetForgetfulPoint_pushforwardFiberMap G PUnit (fun _ ↦ PUnit.unit) =
      MorphismOfTopoiIn.pointPushforwardFiberSection
        ((gSetForgetfulPoint G).toToposPoint) PUnit PUnit.unit := by
  -- The `PUnit`-valued fiber is a subsingleton, so the explicit map and the canonical section coincide.
  apply (gSetForgetfulPoint_pushforwardFiberIso G PUnit).toEquiv.injective
  exact Subsingleton.elim _ _

/-- Helper for Example 7.33.7: on left-regular sections, the pushforward along a map of sets acts
coordinatewise under the explicit `Map(G, -)` identification. -/
theorem pushforwardLeftRegularObjEquiv_symm_map
    {A B : Type u} (f : A → B) (ψ : G → A) :
    ((((gSetForgetfulPoint G).toToposPoint).typePushforward.map f).hom.app
      (op (Action.leftRegular G)))
      ((pushforwardLeftRegularObjEquiv G A).symm ψ) =
        (pushforwardLeftRegularObjEquiv G B).symm (fun x ↦ f (ψ x)) := by
  let Φ := gSetForgetfulPoint G
  -- Transport naturality of `toToposPoint_pointPushforwardIso` to the left regular component.
  have hnat :=
    congrArg
      (fun k :
        ((gSetForgetfulPoint_pushforwardObj G A).1.obj (op (Action.leftRegular G))) →
          ((Φ.skyscraperPresheaf B).obj (op (Action.leftRegular G))) ↦
        k ((pushforwardLeftRegularObjEquiv G A).symm ψ))
      (congrArg
        (fun η :
          gSetForgetfulPoint_pushforwardObj G A ⟶ Φ.skyscraperSheafFunctor.obj B ↦
          (((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj (op (Action.leftRegular G))).map
            ((sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u)).map η)))
        ((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).hom.naturality f))
  -- After this rewrite, the skyscraper map is coordinatewise application of `f`.
  apply (pushforwardLeftRegularObjEquiv G B).injective
  ext x
  have hnat_apply :=
    congrArg
      (fun z : ((Φ.skyscraperPresheaf B).obj (op (Action.leftRegular G))) ↦
        ((Types.productIso
          (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ B)).hom z) x)
      hnat
  calc
    (pushforwardLeftRegularObjEquiv G B)
        ((((gSetForgetfulPoint G).toToposPoint).typePushforward.map f).hom.app
          (op (Action.leftRegular G))
          ((pushforwardLeftRegularObjEquiv G A).symm ψ))
        x =
      f ((pushforwardLeftRegularObjEquiv G A) ((pushforwardLeftRegularObjEquiv G A).symm ψ) x) := by
        simpa [pushforwardLeftRegularObjEquiv, Φ, Category.assoc, Types.productIso_hom_comp_eval,
          Types.productIso_inv_comp_π] using hnat_apply
    _ = f (ψ x) := by
      rw [Equiv.apply_symm_apply]
    _ = (pushforwardLeftRegularObjEquiv G B)
          ((pushforwardLeftRegularObjEquiv G B).symm (fun x ↦ f (ψ x))) x := by
            rw [Equiv.apply_symm_apply]

/-- Helper for Example 7.33.7: the explicit fiber map is natural in the set variable. -/
theorem gSetForgetfulPoint_pushforwardFiberMap_naturality
    {A B : Type u} (f : A → B) (ψ : G → A) :
    ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.map
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.map f)
      (gSetForgetfulPoint_pushforwardFiberMap G A ψ) =
        gSetForgetfulPoint_pushforwardFiberMap G B (fun x ↦ f (ψ x)) := by
  let Φ := gSetForgetfulPoint G
  let FA := gSetForgetfulPoint_pushforwardObj G A
  let FB := gSetForgetfulPoint_pushforwardObj G B
  have hnat :=
    congrArg
      (fun k : Φ.sheafFiber.obj FA ⟶ Φ.toToposPoint.typeInverseImage.obj FB ↦
        k (Φ.toPresheafFiber (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
          FA.1
          ((pushforwardLeftRegularObjEquiv G A).symm ψ)))
      ((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso Φ).inv.naturality
        (Φ.toToposPoint.typePushforward.map f))
  have hfiber :
      Φ.sheafFiber.map (Φ.toToposPoint.typePushforward.map f)
        (Φ.toPresheafFiber (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
          FA.1
          ((pushforwardLeftRegularObjEquiv G A).symm ψ)) =
      Φ.toPresheafFiber (Action.leftRegular G)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
        FB.1
        ((pushforwardLeftRegularObjEquiv G B).symm (fun x ↦ f (ψ x))) := by
    have hnat_fiber :=
      congrArg
        (fun k :
          FA.1.obj (op (Action.leftRegular G)) ⟶ Φ.sheafFiber.obj FB ↦
          k ((pushforwardLeftRegularObjEquiv G A).symm ψ))
        (Φ.toPresheafFiber_naturality (Φ.toToposPoint.typePushforward.map f).hom
          (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G)))
    calc
      Φ.sheafFiber.map (Φ.toToposPoint.typePushforward.map f)
          (Φ.toPresheafFiber (Action.leftRegular G)
            ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
            FA.1
            ((pushforwardLeftRegularObjEquiv G A).symm ψ)) =
        Φ.toPresheafFiber (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
          FB.1
          ((((Φ.toToposPoint.typePushforward.map f).hom.app
            (op (Action.leftRegular G)))
            ((pushforwardLeftRegularObjEquiv G A).symm ψ))) := by
              simpa [GrothendieckTopology.Point.sheafFiber, FA, FB, Category.assoc] using hnat_fiber
      _ = Φ.toPresheafFiber (Action.leftRegular G)
            ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
            FB.1
            ((pushforwardLeftRegularObjEquiv G B).symm (fun x ↦ f (ψ x))) := by
              rw [pushforwardLeftRegularObjEquiv_symm_map]
  -- The inverse-image comparison transports the stalk map to the sheaf-fiber map.
  exact hnat.symm.trans <|
    congrArg (((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso Φ).app FB).inv) hfiber

/-- Helper for Example 7.33.7: pullback along right multiplication becomes precomposition by
`x ↦ x * g` under the explicit `Map(G, S)` identification. -/
theorem pushforwardLeftRegularObjEquiv_rightMul
    (S : Type u) (g : G)
    (ψ : (gSetForgetfulPoint_pushforwardObj G S).1.obj (op (Action.leftRegular G))) :
    pushforwardLeftRegularObjEquiv G S
        ((gSetForgetfulPoint_pushforwardObj G S).1.map
          (op (gSetForgetfulPointLeftRegularRightMul G g)) ψ) =
      fun x ↦ (pushforwardLeftRegularObjEquiv G S ψ) (x * g) := by
  let Φ := gSetForgetfulPoint G
  have hnat :=
    congrArg
      (fun k :
        ((gSetForgetfulPoint_pushforwardObj G S).1.obj (op (Action.leftRegular G))) →
          ((Φ.skyscraperPresheaf S).obj (op (Action.leftRegular G))) ↦
        k ψ)
      (((sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u)).mapIso
        ((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S)).hom.naturality
          (op (gSetForgetfulPointLeftRegularRightMul G g)))
  have hnat_apply (x : G) :=
    congrArg
      (fun z : ((Φ.skyscraperPresheaf S).obj (op (Action.leftRegular G))) ↦
        ((Types.productIso
          (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)).hom z) x)
      hnat
  let z :
      ∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S :=
    (((Φ.toToposPoint_pointPushforwardIso.hom.app S).hom.app
      (op (Action.leftRegular G))) ψ)
  -- On the skyscraper side, pullback along right multiplication just shifts the coordinate index.
  ext x
  have hπ_mor :
      ((Pi.map'
        (Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g))
        (fun _ ↦ (𝟙 S : S ⟶ S))) :
          (∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) ⟶
            ∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) ≫
        Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) x =
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        ((Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g)) x) := by
    simpa using
      (Pi.map'_comp_π
        (f := fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        (g := fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        (p := Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g))
        (q := fun _ ↦ (𝟙 S : S ⟶ S)) x)
  have hπ :
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) x
          (((Pi.map'
            (Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g))
            (fun _ ↦ 𝟙 S)) :
            (∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) ⟶
              ∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) z) =
        Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
          ((Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g)) x)
          z := by
    simpa using
      congrArg
        (fun k :
          (∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) ⟶ S ↦
          k z)
        hπ_mor
  calc
    (pushforwardLeftRegularObjEquiv G S)
        ((gSetForgetfulPoint_pushforwardObj G S).1.map
          (op (gSetForgetfulPointLeftRegularRightMul G g)) ψ) x =
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) x
        ((((Pi.map'
          (Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g))
          (fun _ ↦ 𝟙 S)) :
          (∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) ⟶
            ∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)) z) := by
        simpa [pushforwardLeftRegularObjEquiv, Φ, Category.assoc] using hnat_apply x
    _ =
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        ((Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g)) x)
        (((Φ.toToposPoint_pointPushforwardIso.hom.app S).hom.app
          (op (Action.leftRegular G))) ψ) := hπ
    _ = Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) (x * g) z := by
      rfl
    _ = (pushforwardLeftRegularObjEquiv G S) ψ (x * g) := by
      rfl

/-- Helper for Example 7.33.7: under the canonical fiber comparison, the section from Lemma 7.32.9
becomes the constant function. -/
theorem gSetForgetfulPoint_pushforwardFiberIso_hom_section_eq_const
    (S : Type u) (s : S) :
    (gSetForgetfulPoint_pushforwardFiberIso G S).hom
      (MorphismOfTopoiIn.pointPushforwardFiberSection
        ((gSetForgetfulPoint G).toToposPoint) S s) =
      fun _ ↦ s := by
  have hsection :
      ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.map
        (((gSetForgetfulPoint G).toToposPoint).typePushforward.map (fun _ : PUnit ↦ s))
        (MorphismOfTopoiIn.pointPushforwardFiberSection
          ((gSetForgetfulPoint G).toToposPoint) PUnit PUnit.unit) =
        MorphismOfTopoiIn.pointPushforwardFiberSection
          ((gSetForgetfulPoint G).toToposPoint) S s := by
    letI :
        Subsingleton (((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
          (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj PUnit)) := by
      refine ⟨fun a b ↦ ?_⟩
      apply (gSetForgetfulPoint_pushforwardFiberIso G PUnit).toEquiv.injective
      exact Subsingleton.elim _ _
    -- The canonical section is defined by functoriality from the terminal point in the `PUnit`
    -- fiber, and the intermediate `PUnit` fiber is a subsingleton.
    simpa [MorphismOfTopoiIn.pointPushforwardFiberSection] using
      congrArg
        (((gSetForgetfulPoint G).toToposPoint).typeInverseImage.map
          (((gSetForgetfulPoint G).toToposPoint).typePushforward.map (fun _ : PUnit ↦ s)))
        (Subsingleton.elim _ _)
  have hconst :
      MorphismOfTopoiIn.pointPushforwardFiberSection
        ((gSetForgetfulPoint G).toToposPoint) S s =
        gSetForgetfulPoint_pushforwardFiberMap G S (fun _ ↦ s) := by
    calc
      MorphismOfTopoiIn.pointPushforwardFiberSection
          ((gSetForgetfulPoint G).toToposPoint) S s =
        ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.map
          (((gSetForgetfulPoint G).toToposPoint).typePushforward.map (fun _ : PUnit ↦ s))
          (MorphismOfTopoiIn.pointPushforwardFiberSection
            ((gSetForgetfulPoint G).toToposPoint) PUnit PUnit.unit) := by
              symm
              exact hsection
      _ = gSetForgetfulPoint_pushforwardFiberMap G S (fun _ ↦ s) := by
        simpa [gSetForgetfulPoint_pushforwardFiberMap_punit] using
          gSetForgetfulPoint_pushforwardFiberMap_naturality G (fun _ : PUnit ↦ s)
            (fun _ ↦ PUnit.unit)
  -- Rewrite the canonical section by the explicit constant-function map and evaluate via the fiber
  -- comparison iso.
  rw [hconst]
  simpa using gSetForgetfulPoint_pushforwardFiberIso_hom_map G S (fun _ ↦ s)

/-- Helper for Example 7.33.7: the explicit fiber map sends a constant function to the canonical
section from Lemma 7.32.9. -/
theorem gSetForgetfulPoint_pushforwardFiberMap_const
    (S : Type u) (s : S) :
    gSetForgetfulPoint_pushforwardFiberMap G S (fun _ ↦ s) =
      MorphismOfTopoiIn.pointPushforwardFiberSection
        ((gSetForgetfulPoint G).toToposPoint) S s := by
  -- Compare both sides under the explicit equivalence `p^{-1}(p_* S) ≃ Map(G, S)`.
  apply (gSetForgetfulPoint_pushforwardFiberIso G S).toEquiv.injective
  calc
    (gSetForgetfulPoint_pushforwardFiberIso G S).hom
        (gSetForgetfulPoint_pushforwardFiberMap G S (fun _ ↦ s)) =
      fun _ ↦ s := by
        simpa using gSetForgetfulPoint_pushforwardFiberIso_hom_map G S (fun _ ↦ s)
    _ =
      (gSetForgetfulPoint_pushforwardFiberIso G S).hom
        (MorphismOfTopoiIn.pointPushforwardFiberSection
          ((gSetForgetfulPoint G).toToposPoint) S s) := by
            symm
            exact gSetForgetfulPoint_pushforwardFiberIso_hom_section_eq_const G S s

/-- Helper for Example 7.33.7: the `typeEquiv` counit at `yoneda' S`, evaluated at `PUnit`,
reads off the unique coordinate. -/
theorem typeEquiv_evalEquiv_symm_apply_unit
    (S : Type u) (h : PUnit → ((typeEquiv.functor.obj S).1.obj (op PUnit))) :
    (evalEquiv (typeEquiv.functor.obj S).1 (typeEquiv.functor.obj S).2 PUnit).symm
      h PUnit.unit =
      h PUnit.unit PUnit.unit := by
  -- Rewrite the inverse equivalence as `typesGlue`, then evaluate the glued section at the unique
  -- point of `PUnit`.
  change typesGlue (typeEquiv.functor.obj S).1
      ((isSheaf_iff_isSheaf_of_type _ _).1 (typeEquiv.functor.obj S).2) PUnit h PUnit.unit = _
  have hglue := eval_typesGlue (S := (typeEquiv.functor.obj S).1)
    (hs := (isSheaf_iff_isSheaf_of_type _ _).1 (typeEquiv.functor.obj S).2)
    (α := PUnit) h
  have hval := congrFun hglue PUnit.unit
  simp [typeEquiv, yoneda', eval] at hval
  simpa using congrFun hval PUnit.unit

/-- Helper for Example 7.33.7: the `typeEquiv` counit at `yoneda' S`, evaluated at `PUnit`,
reduces to applying the underlying map at `PUnit.unit`. -/
theorem typeEquiv_toAdjunction_counit_apply_unit
    (S : Type u) (z : (typeEquiv.functor.obj (PUnit → S)).1.obj (op PUnit)) :
    ((((typeEquiv.toAdjunction).counit.app (typeEquiv.functor.obj S)).hom.app
      (op PUnit)) z) PUnit.unit =
      z PUnit.unit PUnit.unit := by
  -- The `typeEquiv` counit is the inverse of the explicit `evalEquiv`.
  change (evalEquiv (typeEquiv.functor.obj S).1 (typeEquiv.functor.obj S).2 PUnit).symm
      z PUnit.unit = _
  rw [typeEquiv_evalEquiv_symm_apply_unit]

/-- Helper for Example 7.33.7: under `toToposPoint_pointInverseImageIso`, evaluating the inverse
image fiber at `PUnit.unit` returns the original sheaf fiber point. -/
theorem gSetForgetfulPoint_pointInverseImageIso_inv_apply_unit
    (S : Type u)
    (x : (gSetForgetfulPoint G).sheafFiber.obj (gSetForgetfulPoint_pushforwardObj G S)) :
    (((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso (gSetForgetfulPoint G)).app
      (gSetForgetfulPoint_pushforwardObj G S)).inv x) PUnit.unit = x := by
  -- The comparison `p⁻¹ ≅ sheafFiber` is induced by `typeEquiv.unitIso`, so evaluation at the
  -- unique point undoes the inserted `PUnit` coordinate.
  simp [GrothendieckTopology.Point.toToposPoint_pointInverseImageIso,
    GrothendieckTopology.Point.toToposPoint]

/-- Helper for Example 7.33.7: the pushforward comparison to the skyscraper sheaf is induced by
evaluation at `PUnit.unit`. -/
theorem gSetForgetfulPoint_pointPushforwardIso_hom_eval
    (S : Type u) :
    ((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso
      (gSetForgetfulPoint G)).app S).hom =
      (gSetForgetfulPoint G).skyscraperSheafFunctor.map (typeEquiv.unitIso.inv.app S) := by
  -- Unfold the `typePushforward` comparison: the remaining morphism is the identity whiskered
  -- with the skyscraper functor.
  dsimp [GrothendieckTopology.Point.toToposPoint_pointPushforwardIso,
    GrothendieckTopology.Point.toToposPoint]
  exact Category.id_comp _

/-- Helper for Example 7.33.7: the `Type`-valued counit of the induced topos point is the
`PUnit`-evaluation of the underlying sheaf-valued counit. -/
theorem gSetForgetfulPoint_typeAdjunction_counit_apply
    (S : Type u)
    (z : ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S)) :
    (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S) z =
      ((((gSetForgetfulPoint G).toToposPoint).adjunction.counit.app
        (typeEquiv.functor.obj S)).hom.app (op PUnit)) z PUnit.unit := by
  -- Expand the transported adjunction once so the final `Type`-valued counit is read as the
  -- `PUnit`-component of the sheaf-valued counit.
  simp [MorphismOfTopoiIn.typeAdjunction, CategoryTheory.Adjunction.comp_counit_app]

/-- Helper for Example 7.33.7: the counit of `p⁻¹ ⊣ p_*` becomes the skyscraper-sheaf counit
after transporting through the point comparison isomorphisms. -/
theorem gSetForgetfulPoint_typeAdjunction_counit_to_skyscraper
    (S : Type u)
    (x : (gSetForgetfulPoint G).sheafFiber.obj (gSetForgetfulPoint_pushforwardObj G S)) :
    (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S)
      ((((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso
        (gSetForgetfulPoint G)).app (gSetForgetfulPoint_pushforwardObj G S)).inv) x) =
      ((gSetForgetfulPoint G).skyscraperSheafAdjunction.counit.app S)
        (((gSetForgetfulPoint G).sheafFiber.map
          (((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso
            (gSetForgetfulPoint G)).app S).hom)) x) := by
  -- Route correction: normalize the `typeAdjunction` counit through the owner-level `typeEquiv`
  -- and skyscraper adjunctions before returning to the explicit `Map(G, S)` model.
  rw [gSetForgetfulPoint_typeAdjunction_counit_apply]
  let Φ := gSetForgetfulPoint G
  have hnat :=
    congrArg
      (fun k : ((Φ.skyscraperSheafFunctor ⋙ Φ.sheafFiber).obj (PUnit → S)) ⟶ S ↦
        k x)
      (Φ.skyscraperSheafAdjunction.counit.naturality (typeEquiv.unitIso.inv.app S))
  calc
    (((gSetForgetfulPoint G).toToposPoint).adjunction.counit.app
          (typeEquiv.functor.obj S)).hom.app
        (op PUnit)
        ((((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso
          (gSetForgetfulPoint G)).app (gSetForgetfulPoint_pushforwardObj G S)).inv) x)
        PUnit.unit =
      ((gSetForgetfulPoint G).skyscraperSheafAdjunction.counit.app (PUnit → S))
        x PUnit.unit := by
          -- Compute the `typeEquiv` counit on the `PUnit` component explicitly.
          simpa [GrothendieckTopology.Point.toToposPoint, CategoryTheory.Adjunction.comp_counit_app,
            gSetForgetfulPoint_pointInverseImageIso_inv_apply_unit] using
            (typeEquiv_toAdjunction_counit_apply_unit (S := S)
              (z := ((typeEquiv.functor.map
                ((gSetForgetfulPoint G).skyscraperSheafAdjunction.counit.app
                  (PUnit → S))).hom.app (op PUnit))
                ((((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso
                  (gSetForgetfulPoint G)).app (gSetForgetfulPoint_pushforwardObj G S)).inv) x)))
    _ = ((gSetForgetfulPoint G).skyscraperSheafAdjunction.counit.app S)
          (((gSetForgetfulPoint G).sheafFiber.map
            (((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso
              (gSetForgetfulPoint G)).app S).hom)) x) := by
                -- Naturality of the skyscraper counit transports evaluation at `PUnit.unit`
                -- across the pushforward comparison.
                simpa [gSetForgetfulPoint_pointPushforwardIso_hom_eval] using hnat.symm

/-- Helper for Example 7.33.7: after transporting the `typeAdjunction` counit to the skyscraper
adjunction, the explicit stalk element attached to `ψ : G → S` evaluates to `ψ 1`. -/
theorem gSetForgetfulPoint_pushforwardFiber_counit_on_map
    (S : Type u) (ψ : G → S) :
    (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S)
      (gSetForgetfulPoint_pushforwardFiberMap G S ψ) = ψ 1 := by
  let Φ := gSetForgetfulPoint G
  let F := gSetForgetfulPoint_pushforwardObj G S
  let t := (pushforwardLeftRegularObjEquiv G S).symm ψ
  have hs :
      Φ.toPresheafFiber (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
          ((Φ.skyscraperSheafFunctor.obj S).1) ≫
        (Φ.skyscraperSheafAdjunction.counit.app S) =
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G)) := by
    let f : Φ.skyscraperSheafFunctor.obj S ⟶ Φ.skyscraperSheafFunctor.obj S := 𝟙 _
    -- The skyscraper counit at the chosen point is projection to the corresponding factor.
    simpa [f] using
      (Φ.toPresheafFiber_skyscraperPresheafHomEquiv_symm
        (A := Type u)
        (P := (Φ.skyscraperSheafFunctor.obj S).1)
        (M := S) (f.hom) (Action.leftRegular G)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G)))
  have hnat_fiber :=
    congrArg
      (fun k : F.1.obj (op (Action.leftRegular G)) ⟶
          Φ.sheafFiber.obj (Φ.skyscraperSheafFunctor.obj S) ↦
        k t)
      (Φ.toPresheafFiber_naturality
        (((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S).hom.hom)
        (Action.leftRegular G)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G)))
  calc
    (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S)
        (gSetForgetfulPoint_pushforwardFiberMap G S ψ) =
      (Φ.skyscraperSheafAdjunction.counit.app S)
        (Φ.sheafFiber.map
          (((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S).hom)
          (Φ.toPresheafFiber (Action.leftRegular G)
            ((1 : G) : Φ.fiber.obj (Action.leftRegular G)) F.1 t)) := by
              -- First transport the `Type`-valued counit to the owner-level skyscraper counit.
              simpa [gSetForgetfulPoint_pushforwardFiberMap, Φ, F, t] using
                gSetForgetfulPoint_typeAdjunction_counit_to_skyscraper G S
                  (Φ.toPresheafFiber (Action.leftRegular G)
                    ((1 : G) : Φ.fiber.obj (Action.leftRegular G)) F.1 t)
    _ =
      (Φ.skyscraperSheafAdjunction.counit.app S)
        (Φ.toPresheafFiber (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
          ((Φ.skyscraperSheafFunctor.obj S).1)
          ((((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S).hom.hom.app
            (op (Action.leftRegular G))) t)) := by
              -- Rewrite the sheaf-fiber map through the left-regular leg, then apply the counit.
              simpa [GrothendieckTopology.Point.sheafFiber, F, Category.assoc] using
                congrArg (Φ.skyscraperSheafAdjunction.counit.app S) hnat_fiber
    _ =
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
        ((((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S).hom.hom.app
          (op (Action.leftRegular G))) t) := by
            -- The skyscraper counit now reduces to projecting to the coordinate indexed by `1`.
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  k ((((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S).hom.hom.app
                    (op (Action.leftRegular G))) t))
                hs
    _ = ψ 1 := by
      -- Under the explicit left-regular identification, the `1`-coordinate is the value `ψ 1`.
      simpa [pushforwardLeftRegularObjEquiv, Φ, t, Types.productIso_inv_comp_π] using
        congrArg (fun f : G → S ↦ f 1)
          (Equiv.apply_symm_apply (pushforwardLeftRegularObjEquiv G S) ψ)

/-- Helper for Example 7.33.7: after identifying `p_* S` with the skyscraper sheaf on `S`, the
counit evaluates a function `G → S` at `1`. -/
theorem gSetForgetfulPoint_pushforwardFiberIso_hom_eval_one
    (S : Type u)
    (z :
      ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
        (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S)) :
    (gSetForgetfulPoint_pushforwardFiberIso G S).hom z 1 =
      (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S) z := by
  -- Compare `z` with the explicit inverse-image model `Map(G, S)` and then reduce to the map case.
  let ψ := (gSetForgetfulPoint_pushforwardFiberIso G S).hom z
  have hz' :
      (gSetForgetfulPoint_pushforwardFiberIso G S).hom
        (gSetForgetfulPoint_pushforwardFiberMap G S ψ) =
          (gSetForgetfulPoint_pushforwardFiberIso G S).hom z := by
    simpa [ψ] using gSetForgetfulPoint_pushforwardFiberIso_hom_map G S ψ
  have hz : gSetForgetfulPoint_pushforwardFiberMap G S ψ = z :=
    (gSetForgetfulPoint_pushforwardFiberIso G S).toEquiv.injective hz'
  -- After rewriting by `hz`, the arbitrary fiber point is reduced to the explicit `Map(G, S)` case.
  rw [← hz]
  calc
    (gSetForgetfulPoint_pushforwardFiberIso G S).hom
        (gSetForgetfulPoint_pushforwardFiberMap G S ψ) 1 = ψ 1 := by
          simpa using congrArg (fun f : G → S ↦ f 1)
            (gSetForgetfulPoint_pushforwardFiberIso_hom_map G S ψ)
    _ = (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S)
          (gSetForgetfulPoint_pushforwardFiberMap G S ψ) := by
            symm
            exact gSetForgetfulPoint_pushforwardFiber_counit_on_map G S ψ

/-- Under the canonical equivalence `p^{-1}(p_* S) ≃ Map(G, S)` from Example 7.33.7, the section
`S → p^{-1}(p_* S)` of Lemma 7.32.9 is the constant-function map. -/
theorem gSetForgetfulPoint_pushforwardFiber_section_eq_const
    (S : Type u) :
    (fun s ↦
      gSetForgetfulPoint_pushforwardFiberEquiv G S
        (MorphismOfTopoiIn.pointPushforwardFiberSection
          ((gSetForgetfulPoint G).toToposPoint) S s)) =
      fun s _ ↦ s :=
  by
    funext s
    -- Rewrite the target through the inverse equivalence, where the statement is explicit.
    exact ((gSetForgetfulPoint_pushforwardFiberEquiv G S).apply_eq_iff_eq_symm_apply).2
      (gSetForgetfulPoint_pushforwardFiberMap_const G S s).symm

/-- Under the canonical equivalence `p^{-1}(p_* S) ≃ Map(G, S)` from Example 7.33.7, the counit
map `p^{-1}(p_* S) → S` of Lemma 7.32.9 is evaluation at `1 ∈ G`. -/
theorem gSetForgetfulPoint_pushforwardFiber_counit_eq_eval_one
    (S : Type u) :
    (fun ψ ↦
      (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S)
        ((gSetForgetfulPoint_pushforwardFiberEquiv G S).symm ψ)) =
      fun ψ ↦ ψ 1 :=
  by
    funext ψ
    -- Rewrite the inverse equivalence by the explicit fiber map and evaluate the counit there.
    simpa using gSetForgetfulPoint_pushforwardFiber_counit_on_map G S ψ

-- Proof sketch: under the canonical identification of `p_* S` on the left regular `G`-set with
-- `Map(G, S)`, pullback along right multiplication by `g` becomes precomposition by the map
-- `x ↦ x * g`.
theorem pushforwardRightTranslation_comm
    (S : Type u) (g : G) :
    ((sheafSectionsOnLeftRegularFunctor G).obj
        (gSetForgetfulPoint_pushforwardObj G S)).ρ g ≫
      (pushforwardLeftRegularObjEquiv G S).toIso.hom =
        (pushforwardLeftRegularObjEquiv G S).toIso.hom ≫
          (Action.ofMulAction G (G → S)).ρ g :=
  by
    ext ψ x
    -- The left action is pullback along right multiplication, and the explicit equivalence sends
    -- that pullback to precomposition by `x ↦ x * g`.
    simpa [sheafSectionsOnLeftRegularFunctor, gSetForgetfulPointMapMulAction_smul_apply] using
      congrArg (fun f : G → S ↦ f x)
        (pushforwardLeftRegularObjEquiv_rightMul G S g ψ)

/-- After identifying sheaves on `\mathcal T_G` with `G`-sets via evaluation on the left regular
object, the pushforward `p_* S` is the right-translation `G`-set `Map(G, S)`. -/
noncomputable def gSetForgetfulPoint_pushforwardRightTranslationIso
    (S : Type u) :
    (sheafSectionsOnLeftRegularFunctor G).obj
        (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S) ≅
      Action.ofMulAction G (G → S) :=
  Action.mkIso
    (pushforwardLeftRegularObjEquiv G S).toIso
    (pushforwardRightTranslation_comm G S)

end

end CategoryTheory
