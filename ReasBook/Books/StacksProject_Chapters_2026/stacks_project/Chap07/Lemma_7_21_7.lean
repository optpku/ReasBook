module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Plus
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w vC vD uC uD

noncomputable section

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D)
variable {A : Type w} [Category A]
variable [u.Full] [u.Faithful]

/- Domain-style sampling for Lemma 7.21.7:
- primary domain: adjunctions on `A`-valued sheaf categories induced by continuous and
  cocontinuous functors of sites;
- sampled owner API:
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionCocontinuous`,
  `Functor.lanAdjunction`,
  `Functor.ranAdjunction`;
- source/core/bridge triage:
  `source-facing`: the two canonical Stacks maps
    `ℱ ⟶ g⁻¹ g_! ℱ` and `g⁻¹ g_* ℱ ⟶ ℱ`;
  `core/canonical`: for clause `(1)`, the source-facing lower shriek `g_!` is owned by the
    sheafified left Kan extension adjunction
    `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`, while the chapter's chosen
    owner `u.sheafAdjunctionContinuous A J K` is the canonical bridge-view obtained from the same
    inverse-image functor; for clause `(2)`, the owner is
    `u.sheafAdjunctionCocontinuous A J K`;
  `bridge/view`: this file keeps the public `IsIso` consequences on the canonical unit and
    counit components, but clause `(1)` should be driven by the construction-level lower-shriek
    owner rather than by a bare abstract `IsRightAdjoint` placeholder.

Primitive data are the site functor `u` and its full faithfulness, together with the
owner-specific adjunction-existence hypotheses: for clause `(1)`, the sheafification and left
Kan-extension data defining the source-facing lower shriek `g_!`; for clause `(2)`, continuity,
cocontinuity, and pointwise right Kan extensions for the cocontinuous direct image. The `IsIso`
assertions are derived API of those owners, so the public surface should stay on the canonical
unit and counit morphisms rather than introducing a second package around them.
-/

section

variable [u.IsContinuous J K] [u.IsCocontinuous J K]
variable [HasWeakSheafify K A]
variable [HasWeakSheafify J A]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P]

/-- Helper for Lemma 7.21.7: the unit of the explicit left-Kan-extension/sheafification model
is the left Kan extension unit followed by the sheafification map. -/
lemma pullback_construction_unit_hom (ℱ : Sheaf J A) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).unit.app ℱ).hom =
      (u.op.lanAdjunction A).unit.app ℱ.obj ≫
        u.op.whiskerLeft (toSheafify K ((u.op.lan).obj ℱ.obj)) := by
  set_option backward.isDefEq.respectTransparency false in
    have h_lanUnit :
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).unit.app ℱ).hom =
          u.op.lanUnit.app ℱ.obj ≫
            u.op.whiskerLeft (toSheafify K ((u.op.lan).obj ℱ.obj)) := by
      -- Forget to presheaves so the restricted-adjunction unit becomes the explicit composite
      -- unit.
      change
        (sheafToPresheaf J A).map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).unit.app ℱ) =
          _
      simp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
        Functor.sheafPullbackConstruction.sheafPullback,
        Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app,
        sheafificationAdjunction_unit_app, Iso.refl_hom, NatTrans.id_app, Functor.id_obj,
        Functor.comp_obj, Functor.comp_map, Category.assoc]
      -- The remaining extra factor is the image of an identity under whiskering.
      have h_id :
          ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op).map
              ((sheafToPresheaf K A).map
                (𝟙 ((presheafToSheaf K A).obj
                  (u.op.lan.obj ((sheafToPresheaf J A).obj ℱ))))) =
            𝟙 (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op).obj
              ((sheafToPresheaf K A).obj
                ((presheafToSheaf K A).obj
                  (u.op.lan.obj ((sheafToPresheaf J A).obj ℱ))))) := by
        simp
      simpa [h_id, Category.assoc]
  -- Rewrite the left Kan extension unit back to the adjunction unit owner.
  simpa [Functor.lanAdjunction_unit] using h_lanUnit

/-- Helper for Lemma 7.21.7: the abstract pullback unit transports to the construction-level
unit along the canonical comparison isomorphism of left adjoints. -/
lemma unit_app_comp_sheafPullbackIso_hom (ℱ : Sheaf J A) :
    ((u.sheafAdjunctionContinuous A J K).unit.app ℱ) ≫
        (u.sheafPushforwardContinuous A J K).map
          ((Functor.sheafPullbackConstruction.sheafPullbackIso u A J K).hom.app ℱ) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).unit.app ℱ := by
  -- Compare the chosen left adjoint with the explicit construction via `leftAdjointUniq`.
  simpa using
    (Adjunction.unit_leftAdjointUniq_hom_app
      (u.sheafAdjunctionContinuous A J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u A J K)
      ℱ)

/-- Helper for Lemma 7.21.7: the left Kan extension unit along `u.op` is already invertible after
restricting back to `C`. -/
lemma lan_unit_isIso_on_pullback_of_pointwise (ℱ : Sheaf J A)
    [u.op.HasPointwiseLeftKanExtension ℱ.obj] :
    IsIso ((u.op.lanAdjunction A).unit.app ℱ.obj) := by
  -- Once pointwise left Kan extensions are available, the fully faithful unit-isomorphism
  -- instance from the Kan-extension adjunction applies directly.
  infer_instance

/-- Helper for Lemma 7.21.7: the identity arrow at `u(X)` is terminal in the comma category
indexing the raw left Kan extension over the image object `u(X)`. -/
def image_costructuredArrow_terminal (X : C) :
    CategoryTheory.Limits.IsTerminal
      (CostructuredArrow.mk (𝟙 (u.op.obj (Opposite.op X)))) :=
  CostructuredArrow.mkIdTerminal (S := u.op) (Y := Opposite.op X)

/-- Helper for Lemma 7.21.7: the comma diagram over `u(X)` has the terminal-object cocone with
vertex `ℱ(X)`. This is the source-side cocone that the remaining `lan` comparison must identify
with the canonical owner. -/
noncomputable def image_terminal_cocone (ℱ : Sheaf J A) (X : C) :
    CategoryTheory.Limits.Cocone
      (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj) :=
  CategoryTheory.Limits.coconeOfDiagramTerminal
    (image_costructuredArrow_terminal (u := u) X)
    (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj)

/-- Helper for Lemma 7.21.7: the terminal-object cocone over the comma diagram at `u(X)` is a
colimit cocone. This packages the textbook computation `u_p ℱ (u(X)) = ℱ(X)` into a reusable
Lean object for the remaining pointwise-owner comparison. -/
noncomputable def image_terminal_cocone_isColimit (ℱ : Sheaf J A) (X : C) :
    CategoryTheory.Limits.IsColimit (image_terminal_cocone (J := J) (u := u) (A := A) ℱ X) :=
  CategoryTheory.Limits.colimitOfDiagramTerminal
    (image_costructuredArrow_terminal (u := u) X)
    (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj)

/-- Helper for Lemma 7.21.7: the colimit of the comma diagram over `u(X)` is canonically the
value `ℱ(X)`. This is the explicit source-side identification used to compare the canonical `lan`
owner with the terminal-object computation. -/
noncomputable def image_terminal_colimitIso (ℱ : Sheaf J A) (X : C)
    [CategoryTheory.Limits.HasColimit
      (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj)] :
    CategoryTheory.Limits.colimit
        (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj) ≅
      ℱ.obj.obj (Opposite.op X) :=
  CategoryTheory.Limits.colimit.isoColimitCocone
    ⟨image_terminal_cocone (J := J) (u := u) (A := A) ℱ X,
      image_terminal_cocone_isColimit (J := J) (u := u) (A := A) ℱ X⟩

/-- Helper for Lemma 7.21.7: on the identity arrow of `u(X)`, the canonical map from the comma
colimit to `ℱ(X)` is literally the identity. This keeps the remaining owner-comparison rewrite
small and directed. -/
@[reassoc (attr := simp)]
lemma image_terminal_colimitIso_hom_id (ℱ : Sheaf J A) (X : C)
    [CategoryTheory.Limits.HasColimit
      (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj)] :
    CategoryTheory.Limits.colimit.ι
        (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj)
        (CostructuredArrow.mk (𝟙 (u.op.obj (Opposite.op X)))) ≫
      (image_terminal_colimitIso (J := J) (u := u) (A := A) ℱ X).hom =
        𝟙 (ℱ.obj.obj (Opposite.op X)) := by
  -- Evaluate the universal `isoColimitCocone` formula on the identity terminal object.
  let j : CostructuredArrow u.op (Opposite.op (u.obj X)) :=
    CostructuredArrow.mk (𝟙 (u.op.obj (Opposite.op X)))
  have h :=
    (CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom
      (t := ⟨image_terminal_cocone (J := J) (u := u) (A := A) ℱ X,
        image_terminal_cocone_isColimit (J := J) (u := u) (A := A) ℱ X⟩)
      (j := j))
  -- Unfold the terminal cocone only at this identity object.
  dsimp [image_terminal_colimitIso, image_terminal_cocone, image_costructuredArrow_terminal, j] at h
  have hfrom :
      (CostructuredArrow.mkIdTerminal (S := u.op) (Y := Opposite.op X)).from j = (𝟙 j : j ⟶ j) := by
    exact (CostructuredArrow.mkIdTerminal (S := u.op) (Y := Opposite.op X)).from_self
  have hidLeft :
      ((CostructuredArrow.mkIdTerminal (S := u.op) (Y := Opposite.op X)).from j).left =
        𝟙 (Opposite.op X) := by
    simpa using congrArg (fun f : j ⟶ j => f.left) hfrom
  have hid :
      ℱ.obj.map ((CostructuredArrow.mkIdTerminal (S := u.op) (Y := Opposite.op X)).from j).left =
        𝟙 (ℱ.obj.obj (Opposite.op X)) := by
    rw [hidLeft]
    exact ℱ.obj.map_id (Opposite.op X)
  exact h.trans hid

/-- Helper for Lemma 7.21.7: the inverse of the comma-colimit identification is the canonical leg
from the identity object. This records the exact map that must match the `lan` unit component in
the remaining pointwise-owner comparison. -/
@[simp]
lemma image_terminal_colimitIso_inv (ℱ : Sheaf J A) (X : C)
    [CategoryTheory.Limits.HasColimit
      (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj)] :
    (image_terminal_colimitIso (J := J) (u := u) (A := A) ℱ X).inv =
      CategoryTheory.Limits.colimit.ι
        (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj)
        (CostructuredArrow.mk (𝟙 (u.op.obj (Opposite.op X)))) := by
  -- The inverse is the unique colimit leg coming from the terminal identity object.
  let j : CostructuredArrow u.op (Opposite.op (u.obj X)) :=
    CostructuredArrow.mk (𝟙 (u.op.obj (Opposite.op X)))
  have h :=
    (CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv
      (t := ⟨image_terminal_cocone (J := J) (u := u) (A := A) ℱ X,
        image_terminal_cocone_isColimit (J := J) (u := u) (A := A) ℱ X⟩)
      (j := j))
  -- Unfold the terminal cocone only at this identity object.
  dsimp [image_terminal_colimitIso, image_terminal_cocone, image_costructuredArrow_terminal, j] at h
  have hfrom :
      (CostructuredArrow.mkIdTerminal (S := u.op) (Y := Opposite.op X)).from j = (𝟙 j : j ⟶ j) := by
    exact (CostructuredArrow.mkIdTerminal (S := u.op) (Y := Opposite.op X)).from_self
  have hidLeft :
      ((CostructuredArrow.mkIdTerminal (S := u.op) (Y := Opposite.op X)).from j).left =
        𝟙 (Opposite.op X) := by
    simpa using congrArg (fun f : j ⟶ j => f.left) hfrom
  have hid :
      ℱ.obj.map ((CostructuredArrow.mkIdTerminal (S := u.op) (Y := Opposite.op X)).from j).left =
        𝟙 (ℱ.obj.obj (Opposite.op X)) := by
    rw [hidLeft]
    exact ℱ.obj.map_id (Opposite.op X)
  change
    (CategoryTheory.Limits.colimit.isoColimitCocone
      ⟨image_terminal_cocone (J := J) (u := u) (A := A) ℱ X,
        image_terminal_cocone_isColimit (J := J) (u := u) (A := A) ℱ X⟩).inv =
      CategoryTheory.Limits.colimit.ι
        (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj)
        (CostructuredArrow.mk (𝟙 (u.op.obj (Opposite.op X))))
  have hid'left : ((𝟙 j : j ⟶ j)).left = 𝟙 (Opposite.op X) := rfl
  have hid' :
      ℱ.obj.map ((𝟙 j : j ⟶ j)).left =
        𝟙 (ℱ.obj.obj (Opposite.op X)) := by
    rw [hid'left]
    exact ℱ.obj.map_id (Opposite.op X)
  have hidExact :
      ℱ.obj.map
          (CostructuredArrow.mkIdTerminal.from
            (CostructuredArrow.mk (𝟙 (u.op.obj (Opposite.op X))))).left =
        𝟙 (ℱ.obj.obj (Opposite.op X)) := by
    simpa [j] using hid
  have h' :
      (𝟙 (ℱ.obj.obj (Opposite.op X))) ≫
          (CategoryTheory.Limits.colimit.isoColimitCocone
            ⟨image_terminal_cocone (J := J) (u := u) (A := A) ℱ X,
              image_terminal_cocone_isColimit (J := J) (u := u) (A := A) ℱ X⟩).inv =
        CategoryTheory.Limits.colimit.ι
          (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj)
          (CostructuredArrow.mk (𝟙 (u.op.obj (Opposite.op X)))) := by
    exact hidExact.symm ▸ h
  simpa [Category.id_comp, image_terminal_colimitIso] using h'

/-- Helper for Lemma 7.21.7: at each image object `u(X)`, the costructured-arrow indexing
category has a terminal identity object, so the raw left Kan extension admits the required
pointwise colimit there. -/
lemma lan_hasPointwiseLeftKanExtensionAt_image (ℱ : Sheaf J A) (X : C) :
    u.op.HasPointwiseLeftKanExtensionAt ℱ.obj (Opposite.op (u.obj X)) := by
  -- The source proof computes on the comma category over `u(X)`, and full faithfulness makes
  -- the identity arrow terminal there.
  change
    CategoryTheory.Limits.HasColimit
      (CostructuredArrow.proj u.op (Opposite.op (u.obj X)) ⋙ ℱ.obj)
  -- A diagram indexed by a terminal category has a colimit given by evaluation at that
  -- terminal object.
  exact
    CategoryTheory.Limits.HasColimit.mk
      ⟨image_terminal_cocone (J := J) (u := u) (A := A) ℱ X,
        image_terminal_cocone_isColimit (J := J) (u := u) (A := A) ℱ X⟩

/-- Helper for Lemma 7.21.7: the terminal cocone leg at a comma object `g` is the restriction of
`ℱ(X)` along the terminal morphism from `g` to the identity arrow of `u(X)`. -/
@[simp]
lemma image_terminal_cocone_ι_app (ℱ : Sheaf J A) (X : C)
    (g : CostructuredArrow u.op (Opposite.op (u.obj X))) :
    (image_terminal_cocone (J := J) (u := u) (A := A) ℱ X).ι.app g =
      ℱ.obj.map ((image_costructuredArrow_terminal (u := u) X).from g).left := by
  -- Unfold the terminal cocone only at the requested comma object.
  simp [image_terminal_cocone]

/-- Helper for Lemma 7.21.7: the identity leg of the explicit comma colimit lifts `ℱ(X)` back to
the chosen `lan` owner point at `u(X)`. -/
noncomputable def image_to_lan_owner_hom (ℱ : Sheaf J A) (X : C) :
    ℱ.obj.obj (Opposite.op X) ⟶ ((u.op.lan.obj ℱ.obj).obj (Opposite.op (u.obj X))) := by
  let E : Functor.LeftExtension u.op ℱ.obj :=
    Functor.LeftExtension.mk ((u.op.lan).obj ℱ.obj) ((u.op.lanAdjunction A).unit.app ℱ.obj)
  -- The source-proof terminal cocone is colimiting, so it provides the canonical lift from
  -- `ℱ(X)` to the point of any competing cocone, in particular the chosen owner.
  exact (image_terminal_cocone_isColimit (J := J) (u := u) (A := A) ℱ X).desc
    (E.coconeAt (Opposite.op (u.obj X)))

/-- Helper for Lemma 7.21.7: the lift from `ℱ(X)` to the chosen `lan` owner reproduces every
owner cocone leg after precomposing with the corresponding terminal cocone leg. -/
@[reassoc]
lemma image_terminal_cocone_ι_app_comp_image_to_lan_owner_hom
    (ℱ : Sheaf J A) (X : C)
    (g : CostructuredArrow u.op (Opposite.op (u.obj X))) :
    (image_terminal_cocone (J := J) (u := u) (A := A) ℱ X).ι.app g ≫
        image_to_lan_owner_hom (J := J) (u := u) (A := A) ℱ X =
      ((u.op.lanAdjunction A).unit.app ℱ.obj).app g.left ≫
        ((u.op.lan.obj ℱ.obj).map g.hom) := by
  let E : Functor.LeftExtension u.op ℱ.obj :=
    Functor.LeftExtension.mk ((u.op.lan).obj ℱ.obj) ((u.op.lanAdjunction A).unit.app ℱ.obj)
  -- Evaluate the terminal-colimit desc map on the comma leg indexed by `g`.
  simpa [image_to_lan_owner_hom, E] using
    (image_terminal_cocone_isColimit (J := J) (u := u) (A := A) ℱ X).fac
      (E.coconeAt (Opposite.op (u.obj X))) g

/-- Helper for Lemma 7.21.7: the lift from `ℱ(X)` back to the chosen `lan` owner is exactly the
unit component at `X`. -/
@[simp]
lemma image_to_lan_owner_hom_eq_unit_app (ℱ : Sheaf J A) (X : C) :
    image_to_lan_owner_hom (J := J) (u := u) (A := A) ℱ X =
      (((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X)) := by
  let E : Functor.LeftExtension u.op ℱ.obj :=
    Functor.LeftExtension.mk ((u.op.lan).obj ℱ.obj) ((u.op.lanAdjunction A).unit.app ℱ.obj)
  let g : CostructuredArrow u.op (Opposite.op (u.obj X)) :=
    CostructuredArrow.mk (𝟙 (u.op.obj (Opposite.op X)))
  have hfrom :
      (image_costructuredArrow_terminal (u := u) X).from g = (𝟙 g : g ⟶ g) := by
    exact (image_costructuredArrow_terminal (u := u) X).from_self
  have hidLeft :
      ((image_costructuredArrow_terminal (u := u) X).from g).left =
        𝟙 (Opposite.op X) := by
    simpa [g] using congrArg (fun f : g ⟶ g => f.left) hfrom
  -- Evaluate the general leg computation at the terminal identity object.
  have hleg :
      (image_terminal_cocone (J := J) (u := u) (A := A) ℱ X).ι.app g =
        𝟙 (ℱ.obj.obj (Opposite.op X)) := by
    rw [image_terminal_cocone_ι_app, hidLeft]
    exact ℱ.obj.map_id (Opposite.op X)
  have hfac :
      (image_terminal_cocone (J := J) (u := u) (A := A) ℱ X).ι.app g ≫
          image_to_lan_owner_hom (J := J) (u := u) (A := A) ℱ X =
        (((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X)) := by
    simpa [image_to_lan_owner_hom, E, g] using
      (image_terminal_cocone_isColimit (J := J) (u := u) (A := A) ℱ X).fac
        (E.coconeAt (Opposite.op (u.obj X))) g
  -- On the terminal identity object, the left leg is the identity on `ℱ(X)`.
  rw [image_terminal_cocone_ι_app, hidLeft] at hfac
  have hfac' :
      (𝟙 (ℱ.obj.obj (Opposite.op X))) ≫
          image_to_lan_owner_hom (J := J) (u := u) (A := A) ℱ X =
        (((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X)) := by
    calc
      (𝟙 (ℱ.obj.obj (Opposite.op X))) ≫
          image_to_lan_owner_hom (J := J) (u := u) (A := A) ℱ X =
        ℱ.obj.map (𝟙 (Opposite.op X)) ≫
          image_to_lan_owner_hom (J := J) (u := u) (A := A) ℱ X := by
          rw [ℱ.obj.map_id]
      _ = (((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X)) := hfac
  simpa using hfac'

/-- Helper for Lemma 7.21.7: once the raw `lan` unit at `X` is invertible, the explicit terminal
comma cocone at `u(X)` is already isomorphic to the chosen `u.op.lan` owner cocone there. This
isolates the remaining `lan`-side work to proving that single unit component is an isomorphism. -/
noncomputable def image_terminal_cocone_iso_lan_owner_cocone_of_unit_app_isIso
    (ℱ : Sheaf J A) (X : C)
    (hX :
      IsIso ((((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X)))) :
    image_terminal_cocone (J := J) (u := u) (A := A) ℱ X ≅
      (Functor.LeftExtension.mk ((u.op.lan).obj ℱ.obj)
        ((u.op.lanAdjunction A).unit.app ℱ.obj)).coconeAt
          (Opposite.op (u.obj X)) := by
  let E : Functor.LeftExtension u.op ℱ.obj :=
    Functor.LeftExtension.mk ((u.op.lan).obj ℱ.obj) ((u.op.lanAdjunction A).unit.app ℱ.obj)
  let invX :
      ((u.op.lan.obj ℱ.obj).obj (Opposite.op (u.obj X))) ⟶
        ℱ.obj.obj (Opposite.op X) :=
    Classical.choose hX.out
  have hhom :
      (((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X)) ≫ invX =
        𝟙 (ℱ.obj.obj (Opposite.op X)) := by
    exact (Classical.choose_spec hX.out).1
  have hinv :
      invX ≫ (((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X)) =
        𝟙 (((u.op.lan.obj ℱ.obj).obj (Opposite.op (u.obj X)))) := by
    exact (Classical.choose_spec hX.out).2
  let φ : ℱ.obj.obj (Opposite.op X) ≅ ((u.op.lan.obj ℱ.obj).obj (Opposite.op (u.obj X))) := by
    exact
      { hom := (((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X))
        inv := invX
        hom_inv_id := hhom
        inv_hom_id := hinv }
  -- The explicit terminal cocone and the chosen owner cocone differ only by the raw unit
  -- component at the terminal identity object.
  refine CategoryTheory.Limits.Cocone.ext φ ?_
  intro g
  -- Every cocone leg is already identified after postcomposing with that unit component.
  simpa [E, φ, image_to_lan_owner_hom_eq_unit_app]
    using image_terminal_cocone_ι_app_comp_image_to_lan_owner_hom
      (J := J) (u := u) (A := A) ℱ X g

/-- Helper for Lemma 7.21.7: at an image object `u(X)`, the only remaining step to make the
chosen `u.op.lan` owner pointwise is to show that the raw unit component at `X` is invertible. -/
noncomputable def chosen_lan_owner_isPointwise_at_image_of_unit_app_isIso
    (ℱ : Sheaf J A) (X : C)
    (hX :
      IsIso ((((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X)))) :
    (Functor.LeftExtension.mk ((u.op.lan).obj ℱ.obj) ((u.op.lanAdjunction A).unit.app ℱ.obj))
      |>.IsPointwiseLeftKanExtensionAt (Opposite.op (u.obj X)) := by
  -- Route correction: after separating the cocone transport from the isomorphism claim, the
  -- pointwise witness is formal from the terminal comma colimit.
  exact
    CategoryTheory.Limits.IsColimit.ofIsoColimit
      (image_terminal_cocone_isColimit (J := J) (u := u) (A := A) ℱ X)
      (image_terminal_cocone_iso_lan_owner_cocone_of_unit_app_isIso
        (J := J) (u := u) (A := A) ℱ X hX)

/-- Helper for Lemma 7.21.7: the chosen `u.op.lan` owner is pointwise at each image object
`u(X)`. This is the source-proof bridge from the explicit terminal comma colimit to the canonical
left Kan extension owner. -/
noncomputable def chosen_lan_owner_isPointwise_at_image (ℱ : Sheaf J A) (X : C) :
    (Functor.LeftExtension.mk ((u.op.lan).obj ℱ.obj) ((u.op.lanAdjunction A).unit.app ℱ.obj))
      |>.IsPointwiseLeftKanExtensionAt (Opposite.op (u.obj X)) := by
  have hX :
      IsIso ((((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X))) := by
    simpa [Functor.lanAdjunction_unit] using
      (inferInstance : IsIso ((u.op.lanUnit.app ℱ.obj).app (Opposite.op X)))
  exact
    chosen_lan_owner_isPointwise_at_image_of_unit_app_isIso
      (J := J) (u := u) (A := A) ℱ X hX

/-- Helper for Lemma 7.21.7: once the `lan` owner is pointwise at the image object `u(X)`, its
value there is canonically identified with the explicit terminal comma colimit and hence with
`ℱ(X)`. This packages the source-side computation into a reusable isomorphism. -/
noncomputable def lan_owner_obj_iso_image (ℱ : Sheaf J A) (X : C) :
    ((u.op.lan.obj ℱ.obj).obj (Opposite.op (u.obj X))) ≅ ℱ.obj.obj (Opposite.op X) := by
  -- Route correction: after extracting the pointwise witness at `u(X)`, the textbook comma
  -- computation only serves to prove that the raw unit component is invertible there.
  let hpoint :
      (Functor.LeftExtension.mk ((u.op.lan).obj ℱ.obj) ((u.op.lanAdjunction A).unit.app ℱ.obj))
        |>.IsPointwiseLeftKanExtensionAt (Opposite.op (u.obj X)) :=
    chosen_lan_owner_isPointwise_at_image (J := J) (u := u) (A := A) ℱ X
  letI :
      IsIso ((((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X))) :=
    Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isIso_hom_app
      (L := u.op)
      (E := Functor.LeftExtension.mk ((u.op.lan).obj ℱ.obj)
        ((u.op.lanAdjunction A).unit.app ℱ.obj))
      (X := Opposite.op X) hpoint
  exact (asIso ((((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X)))).symm

/-- Helper for Lemma 7.21.7: under the pointwise owner identification at `u(X)`, the inverse map
from `ℱ(X)` back to the owner is exactly the raw `lan` unit component. -/
@[simp]
lemma lan_owner_obj_iso_image_inv_eq_unit_app (ℱ : Sheaf J A) (X : C) :
    (lan_owner_obj_iso_image (J := J) (u := u) (A := A) ℱ X).inv =
      (((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X)) := by
  -- The image-object owner isomorphism was defined to be the inverse of `asIso` of the raw unit
  -- component, so its inverse is definitionally that unit component.
  simp [lan_owner_obj_iso_image]

/-- Helper for Lemma 7.21.7: the raw left Kan extension unit is invertible at every image object
`u(X)`. -/
lemma image_component_lan_unit_isIso (ℱ : Sheaf J A) (X : C) :
    IsIso ((((u.op.lanAdjunction A).unit.app ℱ.obj).app (Opposite.op X))) := by
  -- Once the owner point is identified with `ℱ(X)`, the unit component is the inverse of that
  -- packaged isomorphism.
  rw [← lan_owner_obj_iso_image_inv_eq_unit_app (J := J) (u := u) (A := A) ℱ X]
  infer_instance

/-- Helper for Lemma 7.21.7: the left Kan extension unit along `u.op` is already invertible after
restricting back to `C`. -/
lemma lan_unit_isIso_on_pullback (ℱ : Sheaf J A) :
    IsIso ((u.op.lanAdjunction A).unit.app ℱ.obj) := by
  -- Route correction: the source proof is now organized exactly as in the text, by evaluating the
  -- raw `lan` unit at each image object `u(X)` and then globalizing componentwise.
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  simpa using image_component_lan_unit_isIso
    (J := J) (u := u) (A := A) ℱ X.unop

/-- Helper for Lemma 7.21.7: whiskering the sheafification map of the left Kan extension along
`u.op` is already an isomorphism on `J`-sheaves. -/
lemma lan_pullback_isSheaf (ℱ : Sheaf J A) :
    Presheaf.IsSheaf J (u.op ⋙ (u.op.lan.obj ℱ.obj)) := by
  let P : Cᵒᵖ ⥤ A := u.op ⋙ (u.op.lan.obj ℱ.obj)
  have hηiso :
      IsIso ((u.op.lanAdjunction A).unit.app ℱ.obj) :=
    lan_unit_isIso_on_pullback (J := J) (u := u) (A := A) ℱ
  let eP : ℱ.obj ≅ P := by
    -- The raw `lan` unit identifies the pullback of the left Kan extension with `ℱ`.
    simpa [P, Functor.lanAdjunction_unit] using
      (asIso ((u.op.lanAdjunction A).unit.app ℱ.obj))
  have hP : Presheaf.IsSheaf J P := by
    -- Transport sheafness of `ℱ` across the source-side identification.
    exact (Presheaf.isSheaf_of_iso_iff eP).1 ℱ.property
  exact hP

/-- Helper for Lemma 7.21.7: the pullback of the sheafification of the left Kan extension is a
`J`-sheaf. -/
lemma lan_sheafification_pullback_isSheaf (ℱ : Sheaf J A) :
    Presheaf.IsSheaf J (u.op ⋙ sheafify K ((u.op.lan.obj ℱ.obj))) := by
  -- Continuity says that pulling back any `K`-sheaf along `u.op` remains a `J`-sheaf.
  simpa using
    ((presheafToSheaf K A ⋙ u.sheafPushforwardContinuous A J K).obj
      ((u.op.lan).obj ℱ.obj)).property

/-- Helper for Lemma 7.21.7: every `K`-cover of an image object `u(X)` refines to the image under
`u` of a `J`-cover of `X`. -/
lemma cover_refines_to_image_cover (X : C) (T : K.Cover (u.obj X)) :
    ∃ S : J.Cover X, ∀ I : S.Arrow,
      ∃ (j : T.Arrow) (g : u.obj I.Y ⟶ j.Y), g ≫ j.f = u.map I.f := by
  let S : J.Cover X :=
    ⟨(T : Sieve (u.obj X)).functorPullback u, by
      simpa using u.cover_lift J K T.condition⟩
  refine ⟨S, ?_⟩
  intro I
  -- By cocontinuity, the pulled-back sieve itself is covering, so each lifted arrow already
  -- lands in the original cover after applying `u`.
  exact ⟨⟨u.obj I.Y, u.map I.f, I.hf⟩, 𝟙 _, by simp⟩

/-- Helper for Lemma 7.21.7: a continuous functor of sites sends covering sieves to covering
sieves. This supplies the image-cover side of the source proof's cofinality argument. -/
lemma coverPreserving_of_isContinuous :
    CoverPreserving J K u := by
  refine ⟨?_⟩
  intro X S hS
  classical
  let R : Sieve (u.obj X) := S.functorPushforward u
  let Q : Sieve (u.obj X) := K.close R
  have hQclosed : K.IsClosed Q := by
    simpa [Q] using K.close_isClosed R
  let P : Cᵒᵖ ⥤ Type (max uD vD) := u.op ⋙ (Functor.closedSieves K).toFunctor
  have hP : Presheaf.IsSheaf J P := by
    have hclosed : Presheaf.IsSheaf K (Functor.closedSieves K).toFunctor := by
      rw [isSheaf_iff_isSheaf_of_type]
      exact CategoryTheory.classifier_isSheaf K
    exact u.op_comp_isSheaf_of_isSheaf J K (Functor.closedSieves K).toFunctor hclosed
  let s : P.obj (Opposite.op X) := ⟨Q, hQclosed⟩
  let Ttop : Sieve (u.obj X) := ⊤
  let t : P.obj (Opposite.op X) := ⟨Ttop, by
    intro Y f hf
    trivial⟩
  have hs_eq_top : s = t := by
    have hsep := ((CategoryTheory.isSheaf_iff_isSheaf_of_type J P).1 hP).isSeparated S hS
    apply hsep.ext
    intro Y f hf
    apply Subtype.ext
    apply Sieve.ext
    intro Z g
    constructor
    · intro _
      trivial
    · intro _
      dsimp [P, s, t, Q, R]
      have hmemR : R (u.map f) := by
        exact Sieve.image_mem_functorPushforward (F := u) (R := S) hf
      have hmemQ : Q (u.map f) := K.le_close R (u.map f) hmemR
      exact Q.downward_closed hmemQ g
  have hidQ : Q (𝟙 (u.obj X)) := by
    have htopQ : Q = ⊤ := by
      simpa [s, t, P] using congrArg Subtype.val hs_eq_top
    rw [htopQ]
    trivial
  have hQtop : Q = ⊤ := by
    apply eq_top_iff.2
    intro Y f _
    simpa using Q.downward_closed hidQ f
  exact (K.close_eq_top_iff_mem R).1 hQtop

/-- Helper for Lemma 7.21.7: choose a `J`-cover of `X` refining a given `K`-cover of `u(X)`. This
keeps the source proof's refinement cover available under a stable name for later glueing and
extensionality arguments. -/
noncomputable def image_cover_refinement (X : C) (T : K.Cover (u.obj X)) : J.Cover X :=
  ⟨(T : Sieve (u.obj X)).functorPullback u, by
    simpa using u.cover_lift J K T.condition⟩

/-- Helper for Lemma 7.21.7: every arrow in the chosen refinement cover maps into the original
`K`-cover after applying `u`. -/
lemma image_cover_refinement_lift (X : C) (T : K.Cover (u.obj X))
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow) :
    ∃ (j : T.Arrow) (g : u.obj I.Y ⟶ j.Y), g ≫ j.f = u.map I.f := by
  -- The canonical refinement is the pullback sieve itself, so the lift is the image arrow.
  refine ⟨⟨u.obj I.Y, u.map I.f, by simpa [image_cover_refinement] using I.hf⟩, 𝟙 _, ?_⟩
  simp

/-- Helper for Lemma 7.21.7: an image-refinement arrow determines the corresponding arrow in the
top cover of `u(X)` with the same underlying map in `C`. This isolates the special top-cover lift
used in the first `toPlus` inverse-law check. -/
def image_cover_refinement_top_arrow {X : C}
    {T : K.Cover (u.obj X)}
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow) :
    ((⊤ : K.Cover (u.obj X))).Arrow :=
  ⟨u.obj I.Y, u.map I.f, by trivial⟩

/-- Helper for Lemma 7.21.7: the top-cover arrow attached to an image refinement has exactly the
same underlying morphism after applying `u`. This keeps later multiequalizer rewrites directed. -/
@[simp]
lemma image_cover_refinement_top_arrow_f {X : C}
    {T : K.Cover (u.obj X)}
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow) :
    (image_cover_refinement_top_arrow (J := J) (K := K) (u := u) I).f = u.map I.f :=
  rfl

/-- Helper for Lemma 7.21.7: the identity map is the required witness relating an image-refinement
arrow to its top-cover avatar. This is the exact side condition fed into
`image_cover_refinement_multiequalizer_desc_map` for the source-proof top-cover comparison. -/
lemma image_cover_refinement_top_arrow_fac {X : C}
    {T : K.Cover (u.obj X)}
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow) :
    (𝟙 (u.obj I.Y)) ≫
        (image_cover_refinement_top_arrow (J := J) (K := K) (u := u) I).f =
      u.map I.f := by
  -- The chosen top-cover lift is literally `u.map I.f`, so the identity witness closes the
  -- comparison without any extra transport.
  simpa [image_cover_refinement_top_arrow] using (Category.id_comp (u.map I.f))

/-- Helper for Lemma 7.21.7: an image-refinement arrow has a canonical lift into the original
cover `T`, obtained by viewing the same image morphism as an arrow of `T`. This fixes the
generator of `T.index P` used in the remaining multiequalizer calculations. -/
def image_cover_refinement_lift_arrow {X : C} {T : K.Cover (u.obj X)}
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow) :
    T.Arrow :=
  ⟨u.obj I.Y, u.map I.f, by
    simpa [image_cover_refinement] using I.hf⟩

/-- Helper for Lemma 7.21.7: the canonical lift of an image-refinement arrow into `T` has
underlying morphism `u.map I.f`. -/
@[simp]
lemma image_cover_refinement_lift_arrow_f {X : C} {T : K.Cover (u.obj X)}
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow) :
    (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I).f = u.map I.f :=
  rfl

/-- Helper for Lemma 7.21.7: an opposite-cover morphism transports an image-refinement arrow
from the coarser cover to the finer cover without changing the underlying arrow of `C`. -/
def image_cover_refinement_arrow_map {X : C} {S T : (K.Cover (u.obj X))ᵒᵖ}
    (f : S ⟶ T)
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T.unop).Arrow) :
    (image_cover_refinement (J := J) (K := K) (u := u) X S.unop).Arrow :=
  ⟨I.Y, I.f, by
    -- The refinement cover is functorial because it is the pullback of the underlying sieve.
    have hI : (T.unop : Sieve (u.obj X)) (u.map I.f) := by
      simpa [image_cover_refinement] using I.hf
    exact f.unop.le _ hI⟩

/-- Helper for Lemma 7.21.7: transporting an image-refinement arrow along an opposite-cover
morphism does not change its source arrow in `C`. -/
@[simp]
lemma image_cover_refinement_arrow_map_f {X : C} {S T : (K.Cover (u.obj X))ᵒᵖ}
    (f : S ⟶ T)
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T.unop).Arrow) :
    (image_cover_refinement_arrow_map (J := J) (K := K) (u := u) f I).f = I.f :=
  rfl

/-- Helper for Lemma 7.21.7: a compatible family over the chosen image-cover refinement glues in
the pullback sheaf `u.op ⋙ P`. This is the exact amalgamation step needed to construct the
inverse to the whiskered `toPlus` component at an image object. -/
noncomputable def pullback_amalgamate_of_image_cover_refinement {P : Dᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) {X : C} {E : A} (T : K.Cover (u.obj X))
    (x : ∀ I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow,
      E ⟶ P.obj (Opposite.op (u.obj I.Y)))
    (hx : ∀
      ⦃I₁ I₂ : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow⦄
      (r : I₁.Relation I₂),
        x I₁ ≫ P.map (u.map r.g₁).op = x I₂ ≫ P.map (u.map r.g₂).op) :
    E ⟶ P.obj (Opposite.op (u.obj X)) :=
  -- Glue the sections on the chosen `J`-cover inside the already-sheaf pullback `u.op ⋙ P`.
  Presheaf.IsSheaf.amalgamate
    (J := J) (P := u.op ⋙ P) hP
    (image_cover_refinement (J := J) (K := K) (u := u) X T) x
    (fun {I₁ I₂} r ↦ by simpa using hx (I₁ := I₁) (I₂ := I₂) r)

/-- Helper for Lemma 7.21.7: the glued section over the chosen image-cover refinement restricts to
the prescribed family on every member of that refinement. -/
@[reassoc (attr := simp)]
lemma pullback_amalgamate_of_image_cover_refinement_map {P : Dᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) {X : C} {E : A} (T : K.Cover (u.obj X))
    (x : ∀ I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow,
      E ⟶ P.obj (Opposite.op (u.obj I.Y)))
    (hx : ∀
      ⦃I₁ I₂ : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow⦄
      (r : I₁.Relation I₂),
        x I₁ ≫ P.map (u.map r.g₁).op = x I₂ ≫ P.map (u.map r.g₂).op)
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow) :
    pullback_amalgamate_of_image_cover_refinement
        (J := J) (K := K) (u := u) hP T x hx ≫
      P.map (u.map I.f).op = x I := by
  -- This is exactly `IsSheaf.amalgamate_map` for the chosen refinement cover.
  simpa using
    (Presheaf.IsSheaf.amalgamate_map
      (J := J) (P := u.op ⋙ P) hP
      (image_cover_refinement (J := J) (K := K) (u := u) X T) x
      (fun {I₁ I₂} r ↦ by simpa using hx (I₁ := I₁) (I₂ := I₂) r) I)

/-- Helper for Lemma 7.21.7: two maps into `P(u(X))` are equal once they agree on the chosen
image-cover refinement of any `K`-cover of `u(X)`. This is the uniqueness step for the image-side
inverse construction. -/
lemma pullback_hom_ext_of_image_cover_refinement {P : Dᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) {X : C} {E : A} (T : K.Cover (u.obj X))
    {f g : E ⟶ P.obj (Opposite.op (u.obj X))}
    (hfg : ∀ I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow,
      f ≫ P.map (u.map I.f).op = g ≫ P.map (u.map I.f).op) :
    f = g := by
  -- Apply sheaf extensionality on the chosen `J`-cover refining `T`.
  exact
    Presheaf.IsSheaf.hom_ext
      (J := J) (P := u.op ⋙ P) hP
      (image_cover_refinement (J := J) (K := K) (u := u) X T) f g
      (fun I ↦ by simpa using hfg I)

/-- Helper for Lemma 7.21.7: a section of the multiequalizer attached to a `K`-cover of `u(X)`
glues to a section on `u(X)` after refining that cover by a chosen image `J`-cover of `X`. -/
noncomputable def image_cover_refinement_multiequalizer_family {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    (X : C) (T : K.Cover (u.obj X))
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow) :
    Limits.multiequalizer (T.index P) ⟶ P.obj (Opposite.op (u.obj I.Y)) :=
  let j : T.Arrow := Classical.choose (image_cover_refinement_lift (J := J) (K := K) (u := u) X T I)
  let g : u.obj I.Y ⟶ j.Y :=
    Classical.choose
      (Classical.choose_spec
        (image_cover_refinement_lift (J := J) (K := K) (u := u) X T I))
  Limits.Multiequalizer.ι (T.index P) j ≫ P.map g.op

/-- Helper for Lemma 7.21.7: the chosen leg of the multiequalizer family agrees with any other
lift of the same refinement arrow into the original `K`-cover. -/
lemma image_cover_refinement_multiequalizer_family_eq {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    {X : C} (T : K.Cover (u.obj X))
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow)
    {j : T.Arrow} {g : u.obj I.Y ⟶ j.Y} (hg : g ≫ j.f = u.map I.f) :
    image_cover_refinement_multiequalizer_family
        (J := J) (K := K) (u := u) (P := P) X T I =
      Limits.Multiequalizer.ι (T.index P) j ≫ P.map g.op := by
  classical
  let jc : T.Arrow := Classical.choose (image_cover_refinement_lift (J := J) (K := K) (u := u) X T I)
  let gc : u.obj I.Y ⟶ jc.Y :=
    Classical.choose
      (Classical.choose_spec
        (image_cover_refinement_lift (J := J) (K := K) (u := u) X T I))
  have hgc : gc ≫ jc.f = u.map I.f := by
    exact
      Classical.choose_spec
        (Classical.choose_spec
          (image_cover_refinement_lift (J := J) (K := K) (u := u) X T I))
  have hchosen :
      image_cover_refinement_multiequalizer_family
          (J := J) (K := K) (u := u) (P := P) X T I =
        Limits.Multiequalizer.ι (T.index P) jc ≫ P.map gc.op := by
    simp [image_cover_refinement_multiequalizer_family, jc, gc]
  have hlifts_agree :
      Limits.Multiequalizer.ι (T.index P) jc ≫ P.map gc.op =
        Limits.Multiequalizer.ι (T.index P) j ≫ P.map g.op := by
    let ρ : jc.Relation j :=
      { Z := u.obj I.Y
        g₁ := gc
        g₂ := g
        w := by
          calc
            gc ≫ jc.f = u.map I.f := hgc
            _ = g ≫ j.f := hg.symm }
    simpa [ρ, Category.assoc] using
      Limits.Multiequalizer.condition
        (T.index P) (GrothendieckTopology.Cover.Relation.mk' ρ)
  exact hchosen.trans hlifts_agree

/-- Helper for Lemma 7.21.7: the chosen family used to glue a `K`-cover multiequalizer over the
image refinement cover is compatible on overlaps. -/
lemma image_cover_refinement_multiequalizer_family_compatible {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    (X : C) (T : K.Cover (u.obj X)) :
    ∀ ⦃I₁ I₂ : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow⦄
      (r : I₁.Relation I₂),
        image_cover_refinement_multiequalizer_family
            (J := J) (K := K) (u := u) (P := P) X T I₁ ≫
          P.map (u.map r.g₁).op =
        image_cover_refinement_multiequalizer_family
            (J := J) (K := K) (u := u) (P := P) X T I₂ ≫
          P.map (u.map r.g₂).op := by
  classical
  intro I₁ I₂ r
  rcases image_cover_refinement_lift (J := J) (K := K) (u := u) X T I₁ with ⟨j₁, g₁, hg₁⟩
  rcases image_cover_refinement_lift (J := J) (K := K) (u := u) X T I₂ with ⟨j₂, g₂, hg₂⟩
  -- Compare the two chosen lifts by building a relation in the original `K`-cover.
  let ρ : j₁.Relation j₂ :=
    { Z := u.obj r.Z
      g₁ := u.map r.g₁ ≫ g₁
      g₂ := u.map r.g₂ ≫ g₂
      w := by
        rw [Category.assoc, hg₁, Category.assoc, hg₂]
        simpa using congrArg (fun f => u.map f) r.w }
  have h₁ :
      image_cover_refinement_multiequalizer_family
          (J := J) (K := K) (u := u) (P := P) X T I₁ =
        Limits.Multiequalizer.ι (T.index P) j₁ ≫ P.map g₁.op := by
    exact image_cover_refinement_multiequalizer_family_eq
      (J := J) (K := K) (u := u) (P := P) T I₁ hg₁
  have h₂ :
      image_cover_refinement_multiequalizer_family
          (J := J) (K := K) (u := u) (P := P) X T I₂ =
        Limits.Multiequalizer.ι (T.index P) j₂ ≫ P.map g₂.op := by
    exact image_cover_refinement_multiequalizer_family_eq
      (J := J) (K := K) (u := u) (P := P) T I₂ hg₂
  calc
    image_cover_refinement_multiequalizer_family
        (J := J) (K := K) (u := u) (P := P) X T I₁ ≫
      P.map (u.map r.g₁).op =
        Limits.Multiequalizer.ι (T.index P) j₁ ≫ P.map g₁.op ≫ P.map (u.map r.g₁).op := by
          rw [h₁, Category.assoc]
    _ = Limits.Multiequalizer.ι (T.index P) j₂ ≫ P.map g₂.op ≫ P.map (u.map r.g₂).op := by
          simpa [ρ, Category.assoc, ← P.map_comp, ← op_comp] using
            Limits.Multiequalizer.condition
              (T.index P) (GrothendieckTopology.Cover.Relation.mk' ρ)
    _ = image_cover_refinement_multiequalizer_family
          (J := J) (K := K) (u := u) (P := P) X T I₂ ≫
        P.map (u.map r.g₂).op := by
          rw [h₂, Category.assoc]

/-- Helper for Lemma 7.21.7: a section of the multiequalizer attached to a `K`-cover of `u(X)`
glues to a section on `u(X)` after refining that cover by a chosen image `J`-cover of `X`. -/
noncomputable def image_cover_refinement_multiequalizer_desc {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) (X : C) (T : K.Cover (u.obj X)) :
    Limits.multiequalizer (T.index P) ⟶ P.obj (Opposite.op (u.obj X)) :=
  pullback_amalgamate_of_image_cover_refinement
    (J := J) (K := K) (u := u) hP
    (X := X) (E := Limits.multiequalizer (T.index P)) T
    (image_cover_refinement_multiequalizer_family
      (J := J) (K := K) (u := u) (P := P) X T)
    (image_cover_refinement_multiequalizer_family_compatible
      (J := J) (K := K) (u := u) (P := P) X T)

/-- Helper for Lemma 7.21.7: the glued morphism from a `K`-cover multiequalizer to `P(u(X))`
restricts to any specified lift of a refinement arrow into that `K`-cover. -/
lemma image_cover_refinement_multiequalizer_desc_map {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) {X : C} (T : K.Cover (u.obj X))
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow)
    {j : T.Arrow} {g : u.obj I.Y ⟶ j.Y} (hg : g ≫ j.f = u.map I.f) :
    image_cover_refinement_multiequalizer_desc
        (J := J) (K := K) (u := u) hP X T ≫
      P.map (u.map I.f).op =
        Limits.Multiequalizer.ι (T.index P) j ≫ P.map g.op := by
  classical
  rcases image_cover_refinement_lift (J := J) (K := K) (u := u) X T I with ⟨j₀, g₀, hg₀⟩
  have hchosen :
      image_cover_refinement_multiequalizer_desc
          (J := J) (K := K) (u := u) hP X T ≫
        P.map (u.map I.f).op =
          image_cover_refinement_multiequalizer_family
            (J := J) (K := K) (u := u) (P := P) X T I := by
    -- Evaluate the glued family on the chosen refinement arrow.
    simpa [image_cover_refinement_multiequalizer_desc] using
      pullback_amalgamate_of_image_cover_refinement_map
        (J := J) (K := K) (u := u) (P := P) hP
        (X := X) (E := Limits.multiequalizer (T.index P)) T
        (image_cover_refinement_multiequalizer_family
          (J := J) (K := K) (u := u) (P := P) X T)
        (image_cover_refinement_multiequalizer_family_compatible
          (J := J) (K := K) (u := u) (P := P) X T)
        I
  have hfamily :
      image_cover_refinement_multiequalizer_family
          (J := J) (K := K) (u := u) (P := P) X T I =
        Limits.Multiequalizer.ι (T.index P) j₀ ≫ P.map g₀.op := by
    exact image_cover_refinement_multiequalizer_family_eq
      (J := J) (K := K) (u := u) (P := P) T I hg₀
  have hlifts_agree :
      Limits.Multiequalizer.ι (T.index P) j₀ ≫ P.map g₀.op =
        Limits.Multiequalizer.ι (T.index P) j ≫ P.map g.op := by
    let ρ : j₀.Relation j :=
      { Z := u.obj I.Y
        g₁ := g₀
        g₂ := g
        w := by
          calc
            g₀ ≫ j₀.f = u.map I.f := hg₀
            _ = g ≫ j.f := hg.symm }
    -- Two lifts of the same refinement arrow are identified by the multiequalizer relation.
    simpa [ρ, Category.assoc] using
      Limits.Multiequalizer.condition
        (T.index P) (GrothendieckTopology.Cover.Relation.mk' ρ)
  calc
    image_cover_refinement_multiequalizer_desc
        (J := J) (K := K) (u := u) hP X T ≫
      P.map (u.map I.f).op =
        image_cover_refinement_multiequalizer_family
          (J := J) (K := K) (u := u) (P := P) X T I := hchosen
    _ = Limits.Multiequalizer.ι (T.index P) j₀ ≫ P.map g₀.op := hfamily
    _ = Limits.Multiequalizer.ι (T.index P) j ≫ P.map g.op := hlifts_agree

/-- Helper for Lemma 7.21.7: the plus-diagram morphism along a refinement carries each
multiequalizer leg to the corresponding refined leg. This is the explicit shape needed when
checking cocone naturality coverwise. -/
@[reassoc (attr := simp)]
lemma diagram_map_comp_multiequalizer_ι {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    {Y : D} {S T : (K.Cover Y)ᵒᵖ} (f : S ⟶ T) (I : T.unop.Arrow) :
    (K.diagram P Y).map f ≫ Limits.Multiequalizer.ι (T.unop.index P) I =
      Limits.Multiequalizer.ι (S.unop.index P) (I.map f.unop) := by
  -- Unfold the plus-diagram morphism once and read off the leg indexed by `I`.
  dsimp [GrothendieckTopology.diagram]
  erw [Limits.Multiequalizer.lift_ι]

/-- Helper for Lemma 7.21.7: a chosen lift of an image-cover refinement arrow transports along
an opposite cover morphism by mapping the target cover arrow. This is the missing coverwise
transport step in the cocone naturality check. -/
lemma image_cover_refinement_lift_along_op_hom {X : C} {S T : (K.Cover (u.obj X))ᵒᵖ}
    (f : S ⟶ T)
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T.unop).Arrow) :
    ∃ (j : S.unop.Arrow) (g : u.obj I.Y ⟶ j.Y), g ≫ j.f = u.map I.f := by
  -- Start from the chosen lift into `T.unop` and transport it across the refinement `f.unop`.
  rcases image_cover_refinement_lift (J := J) (K := K) (u := u) X T.unop I with ⟨j, g, hg⟩
  refine ⟨j.map f.unop, g, ?_⟩
  simpa using hg

/-- Helper for Lemma 7.21.7: the cover-refinement descent maps assemble into a cocone on the
plus-construction diagram at the image object `u(X)`. This packages the source-proof gluing data
into the single `colimit.desc` input used for the inverse to the whiskered `toPlus` component. -/
noncomputable def image_cover_refinement_desc_cocone {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) (X : C) :
    CategoryTheory.Limits.Cocone (K.diagram P (u.obj X)) := by
  refine CategoryTheory.Limits.Cocone.mk (P.obj (Opposite.op (u.obj X))) ?_
  refine
    { app := fun T =>
        image_cover_refinement_multiequalizer_desc
          (J := J) (K := K) (u := u) (P := P) hP X T.unop
      naturality := ?_ }
  intro S T f
  -- Compare the two candidate legs coverwise on the refinement of `T.unop`, where the left-hand
  -- side is computed by the `T`-descent formula and the right-hand side is transported to `S`.
  apply pullback_hom_ext_of_image_cover_refinement
    (J := J) (K := K) (u := u) (P := P) hP (X := X) (T := T.unop)
  intro I
  let I' :
      (image_cover_refinement (J := J) (K := K) (u := u) X S.unop).Arrow :=
    image_cover_refinement_arrow_map (J := J) (K := K) (u := u) f I
  rcases image_cover_refinement_lift (J := J) (K := K) (u := u) X T.unop I with ⟨j, g, hg⟩
  have hleft :
      (K.diagram P (u.obj X)).map f ≫
          image_cover_refinement_multiequalizer_desc
            (J := J) (K := K) (u := u) (P := P) hP X T.unop ≫
        P.map (u.map I.f).op =
      Limits.Multiequalizer.ι (S.unop.index P) (j.map f.unop) ≫ P.map g.op := by
    -- Rewrite the `T`-side descent map, then push the multiequalizer leg across `f`.
    calc
      (K.diagram P (u.obj X)).map f ≫
          image_cover_refinement_multiequalizer_desc
            (J := J) (K := K) (u := u) (P := P) hP X T.unop ≫
          P.map (u.map I.f).op =
        (K.diagram P (u.obj X)).map f ≫
            (image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T.unop ≫
              P.map (u.map I.f).op) := by
              simp [Category.assoc]
      _ =
        (K.diagram P (u.obj X)).map f ≫
          (Limits.Multiequalizer.ι (T.unop.index P) j ≫ P.map g.op) := by
            exact congrArg
              (fun k =>
                (K.diagram P (u.obj X)).map f ≫ k)
              (image_cover_refinement_multiequalizer_desc_map
                (J := J) (K := K) (u := u) (P := P) hP (X := X) T.unop I hg)
      _ =
        ((K.diagram P (u.obj X)).map f ≫ Limits.Multiequalizer.ι (T.unop.index P) j) ≫
          P.map g.op := by
            simp [Category.assoc]
      _ = Limits.Multiequalizer.ι (S.unop.index P) (j.map f.unop) ≫ P.map g.op := by
            rw [diagram_map_comp_multiequalizer_ι]
            rfl
  have htransport :
      g ≫ (j.map f.unop).f = u.map I'.f := by
    -- The transported refinement arrow has the same underlying `C`-arrow as `I`.
    simpa [I', image_cover_refinement_arrow_map]
      using hg
  have hright :
      image_cover_refinement_multiequalizer_desc
          (J := J) (K := K) (u := u) (P := P) hP X S.unop ≫
        P.map (u.map I.f).op =
      Limits.Multiequalizer.ι (S.unop.index P) (j.map f.unop) ≫ P.map g.op := by
    -- Use the transported refinement arrow on the `S`-side, keeping the same chosen lift.
    simpa [I', image_cover_refinement_arrow_map] using
      (image_cover_refinement_multiequalizer_desc_map
        (J := J) (K := K) (u := u) (P := P) hP (X := X) S.unop I' htransport)
  simpa using hleft.trans hright.symm

/-- Helper for Lemma 7.21.7: once the image-object `toPlus` comparison is known componentwise, it
globalizes to an isomorphism after whiskering along `u.op`. -/
lemma whiskered_toPlus_isIso_on_pullback_of_app {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (X : D) (S : K.Cover X), CategoryTheory.Limits.HasMultiequalizer (S.index Q)]
    [∀ X : D, CategoryTheory.Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ A]
    (hP : ∀ X : C, IsIso ((((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X))))) :
    IsIso (u.op.whiskerLeft (K.toPlus P)) := by
  -- Globalize the image-object computation by checking the whiskered map componentwise.
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  simpa using hP X.unop

/-- Helper for Lemma 7.21.7: an isomorphism on the whiskered `toPlus` map transports sheafness
from `u.op ⋙ P` to `u.op ⋙ P⁺`. -/
lemma plus_pullback_isSheaf_of_whiskered_toPlus_isIso {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (X : D) (S : K.Cover X), CategoryTheory.Limits.HasMultiequalizer (S.index Q)]
    [∀ X : D, CategoryTheory.Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ A]
    (hP : Presheaf.IsSheaf J (u.op ⋙ P))
    [IsIso (u.op.whiskerLeft (K.toPlus P))] :
    Presheaf.IsSheaf J (u.op ⋙ K.plusObj P) := by
  let e : u.op ⋙ P ≅ u.op ⋙ K.plusObj P := asIso (u.op.whiskerLeft (K.toPlus P))
  -- Transport sheafness across the whiskered `toPlus` isomorphism.
  exact (Presheaf.isSheaf_of_iso_iff e).1 hP

/-- Helper for Lemma 7.21.7: after expanding `toSheafify` as `P ⟶ P⁺ ⟶ P⁺⁺`, whiskering along
`u.op` distributes over the two source-proof stages. -/
lemma whiskered_expanded_toSheafify_eq_whiskered_toPlus_comp (P : Dᵒᵖ ⥤ A)
    [∀ (Q : Dᵒᵖ ⥤ A) (X : D) (S : K.Cover X), CategoryTheory.Limits.HasMultiequalizer (S.index Q)]
    [∀ X : D, CategoryTheory.Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ A] :
    u.op.whiskerLeft (K.toPlus P ≫ K.plusMap (K.toPlus P)) =
      u.op.whiskerLeft (K.toPlus P) ≫
        u.op.whiskerLeft (K.plusMap (K.toPlus P)) := by
  -- Whiskering distributes over composition, so the expanded `toSheafify` composite separates.
  rfl

/-- Helper for Lemma 7.21.7: whiskering preserves the standard rewrite
`(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺`. -/
lemma whiskered_plusMap_toPlus (P : Dᵒᵖ ⥤ A)
    [∀ (Q : Dᵒᵖ ⥤ A) (X : D) (S : K.Cover X), CategoryTheory.Limits.HasMultiequalizer (S.index Q)]
    [∀ X : D, CategoryTheory.Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ A] :
    u.op.whiskerLeft (K.plusMap (K.toPlus P)) =
      u.op.whiskerLeft (K.toPlus (K.plusObj P)) := by
  -- Whisker the standard `plusMap_toPlus` identity along `u.op`.
  simpa using
    congrArg (fun η => u.op.whiskerLeft η) (GrothendieckTopology.plusMap_toPlus (J := K) (P := P))

/-- Helper for Lemma 7.21.7: on the top cover of `u(X)`, reassociating the colimit leg of the
descent cocone recovers the explicit top-cover descent morphism. This isolates the only colimit
transport needed in the first `plus` inverse-law check. -/
@[reassoc]
lemma top_cover_colimit_desc_assoc {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (X : D) (S : K.Cover X), CategoryTheory.Limits.HasMultiequalizer (S.index Q)]
    [∀ X : D, CategoryTheory.Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ A]
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) (X : C) :
    GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
      Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op (⊤ : K.Cover (u.obj X))) ≫
      Limits.colimit.desc _ (image_cover_refinement_desc_cocone
        (J := J) (K := K) (u := u) (P := P) hP X) =
        GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
          image_cover_refinement_multiequalizer_desc
            (J := J) (K := K) (u := u) (P := P) hP X (⊤ : K.Cover (u.obj X)) := by
  -- Rewrite only the top-cover colimit leg; the cocone component is the explicit descent map.
  simpa [image_cover_refinement_desc_cocone, Category.assoc] using
    congrArg
      (fun k => GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫ k)
      (Limits.colimit.ι_desc
        (c := image_cover_refinement_desc_cocone
          (J := J) (K := K) (u := u) (P := P) hP X)
        (j := Opposite.op (⊤ : K.Cover (u.obj X))))

/-- Helper for Lemma 7.21.7: the canonical map from a presheaf value to a cover
multiequalizer restricts along every cover arrow by the corresponding presheaf map. -/
@[reassoc]
lemma cover_toMultiequalizer_comp_arrow {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    {Y : D} (S : K.Cover Y) (I : S.Arrow) :
    GrothendieckTopology.Cover.toMultiequalizer S P ≫
      Limits.Multiequalizer.ι (S.index P) I =
        P.map I.f.op := by
  dsimp [GrothendieckTopology.Cover.toMultiequalizer]
  exact
    Limits.Multiequalizer.lift_ι
      (S.index P) (P.obj (Opposite.op Y)) (fun I => P.map I.f.op)
      (by
        intro I
        dsimp only [GrothendieckTopology.Cover.shape, GrothendieckTopology.Cover.index,
          GrothendieckTopology.Cover.Relation.fst, GrothendieckTopology.Cover.Relation.snd]
        simp only [← P.map_comp, ← op_comp, I.r.w])
      I

/-- Helper for Lemma 7.21.7: on the top cover of `u(X)`, the canonical multiequalizer map
evaluated at the refinement arrow coming from `X` is exactly the corresponding restriction map. -/
@[simp]
lemma top_cover_toMultiequalizer_comp_image_cover_refinement_top_arrow {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (X : D) (S : K.Cover X), CategoryTheory.Limits.HasMultiequalizer (S.index Q)]
    {X : C}
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X (⊤ : K.Cover (u.obj X))).Arrow) :
    GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
      Limits.Multiequalizer.ι (((⊤ : K.Cover (u.obj X))).index P)
        (image_cover_refinement_top_arrow (J := J) (K := K) (u := u) I) =
      P.map (u.map I.f).op := by
  -- Evaluate the top-cover multiequalizer lift on the chosen refinement arrow.
  dsimp [GrothendieckTopology.Cover.toMultiequalizer, image_cover_refinement_top_arrow]
  simpa using
    (Limits.Multiequalizer.lift_ι
      (I := ((⊤ : K.Cover (u.obj X))).index P)
      (W := P.obj (Opposite.op (u.obj X)))
      (k := fun a => P.map a.f.op)
      (h := by
        intro b
        dsimp only [GrothendieckTopology.Cover.shape, GrothendieckTopology.Cover.index,
          GrothendieckTopology.Cover.Relation.fst, GrothendieckTopology.Cover.Relation.snd]
        simp only [← P.map_comp, ← op_comp, b.r.w])
      ({ Y := u.obj I.Y, f := u.map I.f, hf := True.intro } :
        ((⊤ : K.Cover (u.obj X))).Arrow))

/-- Helper for Lemma 7.21.7: after passing through the top-cover multiequalizer leg indexed by an
image-refinement arrow, the descent map from `T` recovers the canonical multiequalizer leg of
`T` attached to the same image morphism. This is the exact generator-level computation that the
remaining `toPlus` right-inverse proof still needs. -/
@[reassoc]
lemma image_cover_refinement_desc_comp_top_cover_leg {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (X : D) (S : K.Cover X), CategoryTheory.Limits.HasMultiequalizer (S.index Q)]
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) {X : C} (T : K.Cover (u.obj X))
    (I : (image_cover_refinement (J := J) (K := K) (u := u) X T).Arrow) :
    image_cover_refinement_multiequalizer_desc
        (J := J) (K := K) (u := u) (P := P) hP X T ≫
      GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
      Limits.Multiequalizer.ι (((⊤ : K.Cover (u.obj X))).index P)
        (image_cover_refinement_top_arrow (J := J) (K := K) (u := u) I) =
      Limits.Multiequalizer.ι (T.index P)
        (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) := by
  -- First collapse the top-cover multiequalizer leg to the restriction map along `u.map I.f`.
  have htop :
      image_cover_refinement_multiequalizer_desc
          (J := J) (K := K) (u := u) (P := P) hP X T ≫
        GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
        Limits.Multiequalizer.ι (((⊤ : K.Cover (u.obj X))).index P)
          (image_cover_refinement_top_arrow (J := J) (K := K) (u := u) I) =
        image_cover_refinement_multiequalizer_desc
            (J := J) (K := K) (u := u) (P := P) hP X T ≫
          P.map (u.map I.f).op := by
    let I_top :
        (image_cover_refinement (J := J) (K := K) (u := u) X
          (⊤ : K.Cover (u.obj X))).Arrow :=
      ⟨I.Y, I.f, by trivial⟩
    simpa [Category.assoc] using
      congrArg
        (fun k =>
          image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T ≫ k)
        (top_cover_toMultiequalizer_comp_image_cover_refinement_top_arrow
          (J := J) (K := K) (u := u) (P := P)
          (X := X)
          (I := I_top))
  have hdesc :
      image_cover_refinement_multiequalizer_desc
          (J := J) (K := K) (u := u) (P := P) hP X T ≫
        P.map (u.map I.f).op =
      Limits.Multiequalizer.ι (T.index P)
        (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) ≫
        P.map (𝟙 (u.obj I.Y)).op := by
    simpa [image_cover_refinement_lift_arrow, Category.assoc] using
      (image_cover_refinement_multiequalizer_desc_map
        (J := J) (K := K) (u := u) (P := P) hP
        (X := X) (T := T) I
        (j := image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I)
        (g := 𝟙 (u.obj I.Y))
        (by simp [image_cover_refinement_lift_arrow]))
  have hid :
      Limits.Multiequalizer.ι (T.index P)
          (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) ≫
        P.map (𝟙 (u.obj I.Y)).op =
      Limits.Multiequalizer.ι (T.index P)
        (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) := by
    have hmap :
        P.map ((𝟙 (u.obj I.Y)).op) =
          𝟙 (P.obj (Opposite.op (u.obj I.Y))) := by
      simpa using P.map_id (Opposite.op (u.obj I.Y))
    calc
      Limits.Multiequalizer.ι (T.index P)
          (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) ≫
        P.map (𝟙 (u.obj I.Y)).op =
          Limits.Multiequalizer.ι (T.index P)
            (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) ≫
            𝟙 (P.obj (Opposite.op (u.obj I.Y))) := by
              exact congrArg
                (fun k =>
                  Limits.Multiequalizer.ι (T.index P)
                    (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) ≫ k)
                hmap
      _ =
          Limits.Multiequalizer.ι (T.index P)
            (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) := by
              exact Category.comp_id _
  exact htop.trans (hdesc.trans hid)

/-- Helper for Lemma 7.21.7: the descent map built from the chosen image-cover refinement is a
left inverse to the whiskered `toPlus` component at the image object `u(X)`. This is the first
explicit source-proof inverse law for the `plus` stage. -/
lemma toPlus_image_desc_left_inverse {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (X : D) (S : K.Cover X), CategoryTheory.Limits.HasMultiequalizer (S.index Q)]
    [∀ X : D, CategoryTheory.Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ A]
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) (X : C) :
    (((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X))) ≫
        Limits.colimit.desc _ (image_cover_refinement_desc_cocone
          (J := J) (K := K) (u := u) (P := P) hP X) =
      𝟙 (P.obj (Opposite.op (u.obj X))) := by
  -- Compare both maps after restricting along the image refinement of the top cover.
  apply pullback_hom_ext_of_image_cover_refinement
    (J := J) (K := K) (u := u) (P := P) hP (X := X) (T := (⊤ : K.Cover (u.obj X)))
  intro I
  have htoPlus :
      ((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X)) =
        GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
          Limits.colimit.ι (K.diagram P (u.obj X))
            (Opposite.op (⊤ : K.Cover (u.obj X))) := by
    rfl
  -- First reassociate the top-cover colimit leg into the explicit top-cover descent map.
  have htop :
      (GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
          Limits.colimit.ι (K.diagram P (u.obj X))
            (Opposite.op (⊤ : K.Cover (u.obj X))) ≫
          Limits.colimit.desc _ (image_cover_refinement_desc_cocone
            (J := J) (K := K) (u := u) (P := P) hP X)) ≫
        P.map (u.map I.f).op =
      (GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
          image_cover_refinement_multiequalizer_desc
            (J := J) (K := K) (u := u) (P := P) hP X (⊤ : K.Cover (u.obj X))) ≫
        P.map (u.map I.f).op := by
    exact congrArg
      (fun k => k ≫ P.map (u.map I.f).op)
      (top_cover_colimit_desc_assoc (J := J) (K := K) (u := u) (P := P) hP X)
  calc
    ((((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X))) ≫
        Limits.colimit.desc _ (image_cover_refinement_desc_cocone
          (J := J) (K := K) (u := u) (P := P) hP X)) ≫
      P.map (u.map I.f).op =
        (GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
            Limits.colimit.ι (K.diagram P (u.obj X))
              (Opposite.op (⊤ : K.Cover (u.obj X))) ≫
            Limits.colimit.desc _ (image_cover_refinement_desc_cocone
              (J := J) (K := K) (u := u) (P := P) hP X)) ≫
          P.map (u.map I.f).op := by
            simpa [Category.assoc] using congrArg
              (fun k => (k ≫ Limits.colimit.desc _ (image_cover_refinement_desc_cocone
                (J := J) (K := K) (u := u) (P := P) hP X)) ≫
                  P.map (u.map I.f).op)
              htoPlus
    _ =
        (GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
            image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X (⊤ : K.Cover (u.obj X))) ≫
          P.map (u.map I.f).op := htop
    _ = GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
          (Limits.Multiequalizer.ι (((⊤ : K.Cover (u.obj X))).index P)
            (image_cover_refinement_top_arrow (J := J) (K := K) (u := u) I) ≫
            P.map (𝟙 (u.obj I.Y)).op) := by
          simpa [Category.assoc] using congrArg
            (fun k => GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫ k)
            (image_cover_refinement_multiequalizer_desc_map
              (J := J) (K := K) (u := u) (P := P) hP
              (X := X) (T := (⊤ : K.Cover (u.obj X))) I
              (j := image_cover_refinement_top_arrow (J := J) (K := K) (u := u) I)
              (g := 𝟙 (u.obj I.Y))
              (image_cover_refinement_top_arrow_fac (J := J) (K := K) (u := u) I))
    _ = (GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
          Limits.Multiequalizer.ι (((⊤ : K.Cover (u.obj X))).index P)
            (image_cover_refinement_top_arrow (J := J) (K := K) (u := u) I)) ≫
          P.map (𝟙 (u.obj I.Y)).op := by
            simp [Category.assoc]
    _ = P.map (u.map I.f).op := by
          rw [top_cover_toMultiequalizer_comp_image_cover_refinement_top_arrow
            (J := J) (K := K) (u := u) (P := P) I]
          have hid :
              P.map ((𝟙 (u.obj I.Y)).op) =
                𝟙 (P.obj (Opposite.op (u.obj I.Y))) := by
            simpa using P.map_id (Opposite.op (u.obj I.Y))
          calc
            P.map (u.map I.f).op ≫ P.map ((𝟙 (u.obj I.Y)).op) =
                P.map (u.map I.f).op ≫ 𝟙 (P.obj (Opposite.op (u.obj I.Y))) := by
                  exact congrArg (fun k => P.map (u.map I.f).op ≫ k) hid
            _ = P.map (u.map I.f).op := by
                  simp
    _ = (𝟙 (P.obj (Opposite.op (u.obj X)))) ≫ P.map (u.map I.f).op := by
          simp

/-- Helper for Lemma 7.21.7: the cover-refinement descent cocone recovers the colimit leg of the
first `plus` stage after postcomposing with `toPlus` at the image object `u(X)`. -/
lemma image_cover_refinement_desc_comp_toPlus_app {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    [∀ Y : D, Limits.HasColimitsOfShape (K.Cover Y)ᵒᵖ A]
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) (X : C) (T : K.Cover (u.obj X)) :
    image_cover_refinement_multiequalizer_desc
        (J := J) (K := K) (u := u) (P := P) hP X T ≫
      ((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X)) =
        Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op T) := by
  classical
  let Sref : J.Cover X :=
    image_cover_refinement (J := J) (K := K) (u := u) X T
  let R : K.Cover (u.obj X) :=
    ⟨(Sref : Sieve X).functorPushforward u,
      (coverPreserving_of_isContinuous (J := J) (K := K) (u := u)).cover_preserve
        Sref.condition⟩
  have hRleT : R ≤ T := by
    simpa [R, Sref, image_cover_refinement] using
      (Sieve.functorPullback_pushforward_le (F := u) (R := (T : Sieve (u.obj X))))
  let fT : Opposite.op T ⟶ Opposite.op R := (homOfLE hRleT).op
  let fTop : Opposite.op (⊤ : K.Cover (u.obj X)) ⟶ Opposite.op R :=
    (homOfLE (OrderTop.le_top R)).op
  have hcommon :
      image_cover_refinement_multiequalizer_desc
          (J := J) (K := K) (u := u) (P := P) hP X T ≫
        GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
        (K.diagram P (u.obj X)).map fTop =
      (K.diagram P (u.obj X)).map fT := by
    apply Limits.Multiequalizer.hom_ext
    intro L
    rcases L.hf with ⟨Y0, g, h, hg, hfac⟩
    let I : Sref.Arrow := ⟨Y0, g, hg⟩
    have hfac' : L.f = h ≫ u.map I.f := by
      simpa [I] using hfac
    have hdesc :
        image_cover_refinement_multiequalizer_desc
            (J := J) (K := K) (u := u) (P := P) hP X T ≫
          P.map (u.map I.f).op =
        Limits.Multiequalizer.ι (T.index P)
          (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) := by
      have h0 :=
        image_cover_refinement_multiequalizer_desc_map
          (J := J) (K := K) (u := u) (P := P) hP
          (X := X) (T := T) I
          (j := image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I)
          (g := 𝟙 (u.obj I.Y))
          (by simp [image_cover_refinement_lift_arrow])
      simpa [image_cover_refinement_lift_arrow] using h0
    have hleft :
        (image_cover_refinement_multiequalizer_desc
            (J := J) (K := K) (u := u) (P := P) hP X T ≫
          GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
          (K.diagram P (u.obj X)).map fTop) ≫
          Limits.Multiequalizer.ι (R.index P) L =
        Limits.Multiequalizer.ι (T.index P)
          (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) ≫
          P.map h.op := by
      have hmapTop :
          (K.diagram P (u.obj X)).map fTop ≫
            Limits.Multiequalizer.ι (R.index P) L =
          Limits.Multiequalizer.ι (((⊤ : K.Cover (u.obj X))).index P)
            (L.map (homOfLE (OrderTop.le_top R))) := by
        simpa [fTop] using
          (diagram_map_comp_multiequalizer_ι
            (K := K) (P := P)
            (Y := u.obj X) fTop L)
      have htopLeg :
          GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
            Limits.Multiequalizer.ι (((⊤ : K.Cover (u.obj X))).index P)
              (L.map (homOfLE (OrderTop.le_top R))) =
          P.map L.f.op := by
        simpa using
          cover_toMultiequalizer_comp_arrow
            (K := K) (P := P) (Y := u.obj X)
            (S := (⊤ : K.Cover (u.obj X)))
            (I := L.map (homOfLE (OrderTop.le_top R)))
      have hLmap :
          P.map L.f.op = P.map (u.map I.f).op ≫ P.map h.op := by
        rw [hfac']
        simp [Functor.map_comp]
      have h1 :
          (image_cover_refinement_multiequalizer_desc
            (J := J) (K := K) (u := u) (P := P) hP X T ≫
          GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
          (K.diagram P (u.obj X)).map fTop) ≫
            Limits.Multiequalizer.ι (R.index P) L =
          image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T ≫
            GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
            ((K.diagram P (u.obj X)).map fTop ≫
              Limits.Multiequalizer.ι (R.index P) L) := by
        simp [Category.assoc]
      have h2 :
          image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T ≫
            GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
            ((K.diagram P (u.obj X)).map fTop ≫
              Limits.Multiequalizer.ι (R.index P) L) =
          image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T ≫
            GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
            Limits.Multiequalizer.ι (((⊤ : K.Cover (u.obj X))).index P)
              (L.map (homOfLE (OrderTop.le_top R))) := by
        simpa [Category.assoc] using congrArg
          (fun k =>
            image_cover_refinement_multiequalizer_desc
                (J := J) (K := K) (u := u) (P := P) hP X T ≫
              GrothendieckTopology.Cover.toMultiequalizer
                (⊤ : K.Cover (u.obj X)) P ≫ k)
          hmapTop
      have h3 :
          image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T ≫
            GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
            Limits.Multiequalizer.ι (((⊤ : K.Cover (u.obj X))).index P)
              (L.map (homOfLE (OrderTop.le_top R))) =
          image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T ≫
            P.map L.f.op := by
        simpa [Category.assoc] using congrArg
          (fun k =>
            image_cover_refinement_multiequalizer_desc
                (J := J) (K := K) (u := u) (P := P) hP X T ≫ k)
          htopLeg
      have h4 :
          image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T ≫
            P.map L.f.op =
          image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T ≫
            P.map (u.map I.f).op ≫ P.map h.op := by
        simpa [Category.assoc] using congrArg
          (fun k =>
            image_cover_refinement_multiequalizer_desc
                (J := J) (K := K) (u := u) (P := P) hP X T ≫ k)
          hLmap
      have h5 :
          image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T ≫
            P.map (u.map I.f).op ≫ P.map h.op =
          Limits.Multiequalizer.ι (T.index P)
              (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) ≫
            P.map h.op := by
        simpa [Category.assoc] using congrArg
          (fun k => k ≫ P.map h.op)
          hdesc
      exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
    have hright :
        (K.diagram P (u.obj X)).map fT ≫
          Limits.Multiequalizer.ι (R.index P) L =
        Limits.Multiequalizer.ι (T.index P)
          (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) ≫
          P.map h.op := by
      have hmap :
          (K.diagram P (u.obj X)).map fT ≫
            Limits.Multiequalizer.ι (R.index P) L =
          Limits.Multiequalizer.ι (T.index P) (L.map (homOfLE hRleT)) := by
        rw [diagram_map_comp_multiequalizer_ι]
        rfl
      let ρ : (L.map (homOfLE hRleT)).Relation
          (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) :=
        { Z := L.Y
          g₁ := 𝟙 L.Y
          g₂ := h
          w := by
            simpa [I, image_cover_refinement_lift_arrow] using hfac' }
      have hcond :
          Limits.Multiequalizer.ι (T.index P) (L.map (homOfLE hRleT)) ≫
              P.map (𝟙 L.Y).op =
            Limits.Multiequalizer.ι (T.index P)
              (image_cover_refinement_lift_arrow (J := J) (K := K) (u := u) I) ≫
              P.map h.op := by
        simpa [ρ, Category.assoc] using
          Limits.Multiequalizer.condition
            (T.index P) (GrothendieckTopology.Cover.Relation.mk' ρ)
      have hid :
          Limits.Multiequalizer.ι (T.index P) (L.map (homOfLE hRleT)) ≫
              P.map (𝟙 L.Y).op =
            Limits.Multiequalizer.ι (T.index P) (L.map (homOfLE hRleT)) := by
        simpa using congrArg
          (fun k => Limits.Multiequalizer.ι (T.index P) (L.map (homOfLE hRleT)) ≫ k)
          (P.map_id (Opposite.op L.Y))
      exact hmap.trans (hid.symm.trans hcond)
    exact hleft.trans hright.symm
  have htop_colim :
      GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
        Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op (⊤ : K.Cover (u.obj X))) =
      GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
        (K.diagram P (u.obj X)).map fTop ≫
        Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op R) := by
    simpa [Category.assoc] using (congrArg
      (fun k =>
        GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫ k)
      (Limits.colimit.w (K.diagram P (u.obj X)) fTop)).symm
  have hcommon_colim :
      image_cover_refinement_multiequalizer_desc
          (J := J) (K := K) (u := u) (P := P) hP X T ≫
        GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
        (K.diagram P (u.obj X)).map fTop ≫
        Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op R) =
      (K.diagram P (u.obj X)).map fT ≫
        Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op R) := by
    simpa [Category.assoc] using congrArg
      (fun k => k ≫
        Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op R))
      hcommon
  have hlast :
      (K.diagram P (u.obj X)).map fT ≫
        Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op R) =
      Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op T) := by
    simpa using (Limits.colimit.w (K.diagram P (u.obj X)) fT)
  have hfirst :
      image_cover_refinement_multiequalizer_desc
        (J := J) (K := K) (u := u) (P := P) hP X T ≫
      ((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X)) =
        image_cover_refinement_multiequalizer_desc
          (J := J) (K := K) (u := u) (P := P) hP X T ≫
        GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
        Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op (⊤ : K.Cover (u.obj X))) := by
    rfl
  have htop_step :
      image_cover_refinement_multiequalizer_desc
          (J := J) (K := K) (u := u) (P := P) hP X T ≫
        GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
        Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op (⊤ : K.Cover (u.obj X))) =
        image_cover_refinement_multiequalizer_desc
          (J := J) (K := K) (u := u) (P := P) hP X T ≫
        GrothendieckTopology.Cover.toMultiequalizer (⊤ : K.Cover (u.obj X)) P ≫
        (K.diagram P (u.obj X)).map fTop ≫
        Limits.colimit.ι (K.diagram P (u.obj X)) (Opposite.op R) := by
    simpa [Category.assoc] using congrArg
      (fun k =>
        image_cover_refinement_multiequalizer_desc
          (J := J) (K := K) (u := u) (P := P) hP X T ≫ k)
      htop_colim
  exact hfirst.trans (htop_step.trans (hcommon_colim.trans hlast))

/-- Helper for Lemma 7.21.7: the first `plus` stage is already invertible on image objects once
the pullback presheaf is a `J`-sheaf. -/
lemma whiskered_toPlus_app_isIso_on_image_of_pullback_sheaf {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    [∀ Y : D, Limits.HasColimitsOfShape (K.Cover Y)ᵒᵖ A]
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) (X : C) :
    IsIso (((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X))) := by
  let inv :
      (K.plusObj P).obj (Opposite.op (u.obj X)) ⟶ P.obj (Opposite.op (u.obj X)) :=
    Limits.colimit.desc _ (image_cover_refinement_desc_cocone
      (J := J) (K := K) (u := u) (P := P) hP X)
  refine ⟨⟨inv, ?_, ?_⟩⟩
  · simpa [inv] using
      toPlus_image_desc_left_inverse (J := J) (K := K) (u := u) (P := P) hP X
  · apply Limits.colimit.hom_ext
    intro T
    have hι :
        Limits.colimit.ι (K.diagram P (u.obj X)) T ≫
            inv ≫ ((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X)) =
          image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T.unop ≫
            ((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X)) := by
      simpa [inv, Category.assoc, image_cover_refinement_desc_cocone] using
        congrArg
          (fun k =>
            k ≫ ((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X)))
          (Limits.colimit.ι_desc
            (c := image_cover_refinement_desc_cocone
              (J := J) (K := K) (u := u) (P := P) hP X)
            (j := T))
    have hcomp :
        image_cover_refinement_multiequalizer_desc
            (J := J) (K := K) (u := u) (P := P) hP X T.unop ≫
          ((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X)) =
        Limits.colimit.ι (K.diagram P (u.obj X)) T ≫
          𝟙 ((K.plusObj P).obj (Opposite.op (u.obj X))) := by
      have hleg :
          image_cover_refinement_multiequalizer_desc
              (J := J) (K := K) (u := u) (P := P) hP X T.unop ≫
            ((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X)) =
          Limits.colimit.ι (K.diagram P (u.obj X)) T := by
        simpa using
          image_cover_refinement_desc_comp_toPlus_app
            (J := J) (K := K) (u := u) (P := P) hP X T.unop
      have hid :
          Limits.colimit.ι (K.diagram P (u.obj X)) T =
            Limits.colimit.ι (K.diagram P (u.obj X)) T ≫
              𝟙 ((K.plusObj P).obj (Opposite.op (u.obj X))) := by
        exact (Category.comp_id (Limits.colimit.ι (K.diagram P (u.obj X)) T)).symm
      exact hleg.trans hid
    exact hι.trans hcomp

/-- Helper for Lemma 7.21.7: once the first `plus`-stage comparison is invertible at every image
object, the whiskered `toPlus` map is globally invertible on the pullback. -/
lemma whiskered_toPlus_isIso_on_pullback {P : Dᵒᵖ ⥤ A}
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    [∀ Y : D, Limits.HasColimitsOfShape (K.Cover Y)ᵒᵖ A]
    (hP : Presheaf.IsSheaf J (u.op ⋙ P)) :
    IsIso (u.op.whiskerLeft (K.toPlus P)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  simpa using whiskered_toPlus_app_isIso_on_image_of_pullback_sheaf
    (J := J) (K := K) (u := u) (P := P) hP X.unop

/-- Helper for Lemma 7.21.7: under explicit `plus`-construction hypotheses, the source proof
closes by applying the first `plus`-stage computation twice. -/
lemma whiskered_twice_toPlus_app_isIso_on_image_of_plus_data
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    [∀ Y : D, Limits.HasColimitsOfShape (K.Cover Y)ᵒᵖ A]
    (ℱ : Sheaf J A) (X : C) :
    IsIso ((((u.op.whiskerLeft (K.toPlus ((u.op.lan).obj ℱ.obj))).app (Opposite.op X)) ≫
      (((u.op.whiskerLeft (K.toPlus (K.plusObj ((u.op.lan).obj ℱ.obj)))).app
        (Opposite.op X))))) := by
  let P : Dᵒᵖ ⥤ A := (u.op.lan.obj ℱ.obj)
  have hP : Presheaf.IsSheaf J (u.op ⋙ P) :=
    lan_pullback_isSheaf (J := J) (u := u) (A := A) ℱ
  have hPlus₁ : IsIso (u.op.whiskerLeft (K.toPlus P)) :=
    whiskered_toPlus_isIso_on_pullback
      (J := J) (K := K) (u := u) (P := P) hP
  letI : IsIso (u.op.whiskerLeft (K.toPlus P)) := hPlus₁
  have hPlusSheaf : Presheaf.IsSheaf J (u.op ⋙ K.plusObj P) :=
    plus_pullback_isSheaf_of_whiskered_toPlus_isIso
      (J := J) (K := K) (u := u) (P := P) hP
  have hPlus₂ : IsIso (u.op.whiskerLeft (K.toPlus (K.plusObj P))) :=
    whiskered_toPlus_isIso_on_pullback
      (J := J) (K := K) (u := u) (P := K.plusObj P) hPlusSheaf
  letI : IsIso (u.op.whiskerLeft (K.toPlus (K.plusObj P))) := hPlus₂
  have hExpanded :
      IsIso ((((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X)) ≫
        (((u.op.whiskerLeft (K.toPlus (K.plusObj P))).app (Opposite.op X))))) := by
    infer_instance
  simpa [P] using hExpanded

/-- Helper for Lemma 7.21.7: with explicit `plus`-construction data available, the expanded
image-side weak-sheafification composite `P ⟶ P⁺ ⟶ P⁺⁺` is invertible. -/
lemma whiskered_expanded_toSheafify_app_isIso_on_image_of_plus_data
    [∀ (Q : Dᵒᵖ ⥤ A) (Y : D) (S : K.Cover Y), Limits.HasMultiequalizer (S.index Q)]
    [∀ Y : D, Limits.HasColimitsOfShape (K.Cover Y)ᵒᵖ A]
    (ℱ : Sheaf J A) (X : C) :
    IsIso ((((u.op.whiskerLeft
      (K.toPlus ((u.op.lan).obj ℱ.obj) ≫
        K.plusMap (K.toPlus ((u.op.lan).obj ℱ.obj)))).app
      (Opposite.op X)))) := by
  let P : Dᵒᵖ ⥤ A := (u.op.lan.obj ℱ.obj)
  have hPlus :
      IsIso ((((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X)) ≫
        (((u.op.whiskerLeft (K.toPlus (K.plusObj P))).app (Opposite.op X))))) := by
    simpa [P] using
      whiskered_twice_toPlus_app_isIso_on_image_of_plus_data
        (J := J) (K := K) (u := u) (A := A) ℱ X
  have hExpand :
      ((u.op.whiskerLeft (K.toPlus P ≫ K.plusMap (K.toPlus P))).app (Opposite.op X)) =
        (((u.op.whiskerLeft (K.toPlus P)).app (Opposite.op X)) ≫
          ((u.op.whiskerLeft (K.plusMap (K.toPlus P))).app (Opposite.op X))) := by
    simpa using congrApp (whiskered_expanded_toSheafify_eq_whiskered_toPlus_comp P)
      (Opposite.op X)
  have hPlusMap :
      ((u.op.whiskerLeft (K.plusMap (K.toPlus P))).app (Opposite.op X)) =
        ((u.op.whiskerLeft (K.toPlus (K.plusObj P))).app (Opposite.op X)) := by
    simpa using congrApp (whiskered_plusMap_toPlus P) (Opposite.op X)
  rw [hExpand, hPlusMap]
  exact hPlus

/-- Helper for Lemma 7.21.7: whiskering the sheafification map of the left Kan extension along
`u.op` is already an isomorphism on `J`-sheaves. -/
lemma whiskered_toSheafify_app_isIso_on_image (ℱ : Sheaf J A) (X : C) :
    IsIso ((((u.op.whiskerLeft (toSheafify K ((u.op.lan).obj ℱ.obj))).app
      (Opposite.op X)))) := by
  let P : Dᵒᵖ ⥤ A := (u.op.lan.obj ℱ.obj)
  have hP : Presheaf.IsSheaf J (u.op ⋙ P) :=
    lan_pullback_isSheaf (J := J) (u := u) (A := A) ℱ
  have hToSheafify : IsIso (toSheafify J (u.op ⋙ P)) := by
    exact CategoryTheory.isIso_toSheafify J hP
  have hCompat :
      IsIso (((u.pushforwardContinuousSheafificationCompatibility A J K).hom.app P).hom) := by
    let e :=
      asIso ((u.pushforwardContinuousSheafificationCompatibility A J K).hom.app P)
    refine ⟨⟨e.inv.hom, ?_, ?_⟩⟩
    · exact ObjectProperty.isoHom_inv_id_hom e
    · exact ObjectProperty.isoInv_hom_id_hom e
  have hNat : IsIso (u.op.whiskerLeft (toSheafify K P)) := by
    rw [← u.toSheafify_pullbackSheafificationCompatibility A J K P]
    exact IsIso.comp_isIso' hToSheafify hCompat
  letI : IsIso (u.op.whiskerLeft (toSheafify K P)) := hNat
  simpa [P] using
    (inferInstance :
      IsIso (((u.op.whiskerLeft (toSheafify K P)).app (Opposite.op X))))

/-- Helper for Lemma 7.21.7: whiskering the sheafification map of the left Kan extension along
`u.op` is already an isomorphism on `J`-sheaves. -/
lemma whiskered_toSheafify_isIso_on_pullback (ℱ : Sheaf J A) :
    IsIso (u.op.whiskerLeft (toSheafify K ((u.op.lan).obj ℱ.obj))) := by
  -- Once the image-object inverse is constructed, the global isomorphism follows componentwise.
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  simpa using whiskered_toSheafify_app_isIso_on_image
    (J := J) (K := K) (u := u) (A := A) ℱ X.unop

/-- Helper for Lemma 7.21.7: if weak sheafification is also available on `J`, then the whiskered
sheafification map is the underlying morphism of the canonical pullback/sheafification
compatibility isomorphism. -/
lemma whiskered_toSheafify_isIso_on_pullback_of_hasWeakSheafify
    [HasWeakSheafify J A]
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F] (ℱ : Sheaf J A) :
    IsIso (u.op.whiskerLeft (toSheafify K ((u.op.lan).obj ℱ.obj))) := by
  let P : Dᵒᵖ ⥤ A := (u.op.lan.obj ℱ.obj)
  have hP : Presheaf.IsSheaf J (u.op ⋙ P) :=
    lan_pullback_isSheaf (J := J) (u := u) (A := A) ℱ
  have hToSheafify : IsIso (toSheafify J (u.op ⋙ P)) := by
    -- The raw pullback is already a `J`-sheaf, so its sheafification map is invertible.
    exact CategoryTheory.isIso_toSheafify J hP
  have hCompat :
      IsIso (((u.pushforwardContinuousSheafificationCompatibility A J K).hom.app P).hom) := by
    let e :=
      asIso ((u.pushforwardContinuousSheafificationCompatibility A J K).hom.app P)
    -- The comparison from pullback-after-sheafification to sheafification-after-pullback is a
    -- component of mathlib's canonical compatibility isomorphism, so its underlying presheaf map
    -- is an isomorphism as well.
    refine ⟨⟨e.inv.hom, ?_, ?_⟩⟩
    · exact ObjectProperty.isoHom_inv_id_hom e
    · exact ObjectProperty.isoInv_hom_id_hom e
  -- Route correction: once `J` also has weak sheafification, use the canonical compatibility
  -- isomorphism instead of rebuilding the comparison from covers.
  rw [← u.toSheafify_pullbackSheafificationCompatibility A J K P]
  -- The desired whiskered `toSheafify` map is the composite of two already invertible factors.
  exact IsIso.comp_isIso' hToSheafify hCompat

/-- Helper for Lemma 7.21.7: the explicit left-Kan-extension/sheafification model for `g_!`
already has an invertible unit on sheaves over `C`. -/
lemma pullback_construction_unit_isIso (ℱ : Sheaf J A) :
    IsIso ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).unit.app ℱ) := by
  -- Move to underlying presheaves so the structural decomposition from
  -- `pullback_construction_unit_hom` applies verbatim.
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J A)]
  change
    IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).unit.app ℱ).hom)
  -- Rewrite the source-facing unit into the two formal pieces isolated above.
  rw [pullback_construction_unit_hom]
  -- Once both source-faithful factors are known to be isomorphisms, their composite is as well.
  exact IsIso.comp_isIso'
    (lan_unit_isIso_on_pullback (J := J) (u := u) (A := A) ℱ)
    (whiskered_toSheafify_isIso_on_pullback (J := J) (K := K) (u := u) (A := A) ℱ)

-- Proof sketch: realize `g_!` by the sheafified left Kan extension along `u.op`, whose presheaf
-- unit is invertible for fully faithful `u.op`; then transport that source-facing construction to
-- the chapter's chosen owner `u.sheafAdjunctionContinuous`.
/-- Lemma 7.21.7 (1): for a fully faithful continuous and cocontinuous functor of sites, the
canonical map from a sheaf on `C` to `g⁻¹ g_!` of that sheaf is an isomorphism. -/
instance unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful
    (ℱ : Sheaf J A) :
    IsIso ((u.sheafAdjunctionContinuous A J K).unit.app ℱ) := by
  haveI : IsIso ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).unit.app ℱ) :=
    pullback_construction_unit_isIso (J := J) (K := K) (u := u) (A := A) ℱ
  haveI : IsIso ((Functor.sheafPullbackConstruction.sheafPullbackIso u A J K).hom.app ℱ) := by
    infer_instance
  let α :=
    (u.sheafPushforwardContinuous A J K).map
      ((Functor.sheafPullbackConstruction.sheafPullbackIso u A J K).hom.app ℱ)
  have hmap : IsIso α := by
    infer_instance
  letI := hmap
  have hcomp : IsIso
      (((u.sheafAdjunctionContinuous A J K).unit.app ℱ) ≫ α) := by
    rw [unit_app_comp_sheafPullbackIso_hom]
    exact pullback_construction_unit_isIso (J := J) (K := K) (u := u) (A := A) ℱ
  letI := hcomp
  haveI : IsIso (inv α) := by
    infer_instance
  have hfull : IsIso ((((u.sheafAdjunctionContinuous A J K).unit.app ℱ) ≫ α) ≫ inv α) :=
    IsIso.comp_isIso' hcomp inferInstance
  -- Cancel the comparison isomorphism on the right to return to the chosen owner.
  have hcancel :
      ((u.sheafAdjunctionContinuous A J K).unit.app ℱ) =
        (((u.sheafAdjunctionContinuous A J K).unit.app ℱ) ≫ α) ≫ inv α := by
    simp
  rw [hcancel]
  exact hfull

end

section

variable [u.IsContinuous J K] [u.IsCocontinuous J K]

-- Proof sketch: identify `g_*` with `u.sheafPushforwardCocontinuous` and compare its counit with
-- the counit of right Kan extension along the fully faithful functor `u.op`.
/-- Lemma 7.21.7 (2): for a fully faithful continuous and cocontinuous functor of sites, the
canonical map from `g⁻¹ g_*` of a sheaf on `C` back to the original sheaf is an isomorphism. -/
instance counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P]
    (ℱ : Sheaf J A) :
    IsIso ((u.sheafAdjunctionCocontinuous A J K).counit.app ℱ) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J A)]
  change IsIso (((u.sheafAdjunctionCocontinuous A J K).counit.app ℱ).hom)
  simpa [u.sheafAdjunctionCocontinuous_counit_app_hom A J K ℱ] using
    (inferInstance : IsIso ((u.op.ranAdjunction A).counit.app ℱ.obj))

end
