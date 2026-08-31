module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Point.Map
public import stacks_project.Chap07.Lemma_7_35_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

universe w v u

namespace CategoryTheory

open GrothendieckTopology

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]

/-- Module-mode wrapper for the membership condition in a point localized over `x`. -/
lemma localized_point_over_mem_of_eq
    {U : C} (p : Point.{w} J) {x : p.fiber.obj U} {V : Over U}
    {y : p.fiber.obj V.left} (hy : p.fiber.map V.hom y = x) :
    y ∈ (FunctorToTypes.fromOverSubfunctor p.fiber x).obj V := by
  rwa [FunctorToTypes.mem_fromOverSubfunctor_iff]

/-- Module-mode wrapper for reading localized-fiber membership as its defining equality. -/
lemma localized_point_over_eq_of_mem
    {U : C} (p : Point.{w} J) {x : p.fiber.obj U} {V : Over U}
    {y : p.fiber.obj V.left}
    (hy : y ∈ (FunctorToTypes.fromOverSubfunctor p.fiber x).obj V) :
    p.fiber.map V.hom y = x := by
  rwa [FunctorToTypes.mem_fromOverSubfunctor_iff] at hy

/- Domain-style sampling for Lemma 7.35.2:
- primary domain: points of Grothendieck sites, their localization to slice sites, and comparison
  of points under the localization functor `Over.forget U`;
- sampled owner API:
  `GrothendieckTopology.Point.over`,
  `GrothendieckTopology.Point.map`,
  `GrothendieckTopology.Point.sheafFiberMapIso`,
  `Over.mkIdTerminal`;
- best owner abstraction: the site-point owner `GrothendieckTopology.Point`, with the localized
  point `p.over x` and the image point `q.map (Over.forget U) J` as derived canonical
  constructions.

Source/core/bridge triage:
- `source-facing`: the classification of points of `(C / U, J.over U)` lying over a fixed point
  `p` by elements `x : p.fiber.obj U`;
- `core/canonical`: the owners `Point.over`, `Point.map`, the induced comparison of stalk functors
  via `Point.sheafFiberMapIso`, and the terminal object `Over.mk (𝟙 U)` supplied by
  `Over.mkIdTerminal`;
- `bridge/view`: the theorem below, which translates the source statement into the canonical point
  owners without introducing any parallel wrapper API.

Primitive data are only the point `p`, the object `U`, and the localized-site point `q`. The
fiber element `x : p.fiber.obj U` is derived by evaluating at the terminal object of `Over U`,
while the comparison with `p.over x` is derived from the owner-level localized-point construction.
-/
-- Proof sketch: if `q` lies over `p`, apply the defining isomorphism
-- `(q.map (Over.forget U) J) ≅ p` to the distinguished point of the terminal object
-- `Over.mk (𝟙 U)` (owned by `Over.mkIdTerminal`); this produces the corresponding element
-- `x : p.fiber.obj U`. Then compare the induced fiber functors using the owner-level point
-- constructions `Point.map` and `Point.over` to show that `q` is isomorphic to `p.over x`.
-- Conversely, Lemma `7.35.1` shows that every `p.over x` maps back to a point lying over `p`, and
-- uniqueness again comes from evaluating at the terminal object of `Over U`.
/-- Helper for Lemma 7.35.2: a natural isomorphism between the underlying fiber functors of two
points yields an isomorphism of points. -/
noncomputable def point_iso_of_fiber_natIso
    {K : GrothendieckTopology C} {q r : Point.{w} K} (α : q.fiber ≅ r.fiber) :
    q ≅ r where
  hom := ⟨α.inv⟩
  inv := ⟨α.hom⟩
  hom_inv_id := by
    -- Point morphisms are contravariant on fibers, so the identity check is `α.hom_inv_id`.
    ext X x
    exact congr_fun (NatTrans.congr_app α.hom_inv_id X) x
  inv_hom_id := by
    -- The opposite composite is controlled by `α.inv_hom_id`.
    ext X x
    exact congr_fun (NatTrans.congr_app α.inv_hom_id X) x

/-- Helper for Lemma 7.35.2: the localized point `p.over x` maps back to `p` under
`Over.forget U`. -/
noncomputable def point_over_map_forget_iso
    (p : Point.{w} J) (U : C) (x : p.fiber.obj U) :
    IsIsomorphic ((p.over x).map (Over.forget U) J) p := by
  let α :
      ((p.over x).map (Over.forget U) J).fiber ≅ p.fiber :=
    ((p.over x).map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.symm ≪≫
      Functor.isoWhiskerLeft shrinkYoneda
        ((p.over x).presheafFiberMapIso (Over.forget U) J (Type w)) ≪≫
      Functor.isoWhiskerLeft shrinkYoneda (point_over_overPullback_presheafFiberIso p x) ≪≫
      p.shrinkYonedaCompPresheafFiberIso
  -- Package the owner-level fiber comparison as a point isomorphism.
  exact ⟨point_iso_of_fiber_natIso α⟩

/-- Helper for Lemma 7.35.2: an isomorphism of points induces an isomorphism of the associated
presheaf-fiber functors. -/
noncomputable def point_presheafFiber_natIso
    {K : GrothendieckTopology C} {q r : Point.{w} K} (α : q ≅ r) :
    q.presheafFiber (A := Type w) ≅ r.presheafFiber (A := Type w) where
  hom := α.inv.presheafFiber
  inv := α.hom.presheafFiber
  hom_inv_id := by
    -- The presheaf-fiber functor is functorial in point morphisms, so the identity follows from
    -- `α.hom_inv_id`.
    rw [← GrothendieckTopology.Point.Hom.presheafFiber_comp]
    simpa using congrArg (fun f ↦ GrothendieckTopology.Point.Hom.presheafFiber
      (A := Type w) f) α.hom_inv_id
  inv_hom_id := by
    -- The reverse identity is the same functoriality statement applied to `α.inv_hom_id`.
    rw [← GrothendieckTopology.Point.Hom.presheafFiber_comp]
    simpa using congrArg (fun f ↦ GrothendieckTopology.Point.Hom.presheafFiber
      (A := Type w) f) α.inv_hom_id

/-- Helper for Lemma 7.35.2: an isomorphism of localized points induces an isomorphism after
mapping along `Over.forget U`. -/
noncomputable def localized_point_map_forget_iso_of_point_iso
    {U : C} {q r : Point.{w} (J.over U)} (α : q ≅ r) :
    q.map (Over.forget U) J ≅ r.map (Over.forget U) J := by
  let W :=
    (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type w)).obj (Over.forget U).op
  let β : q.presheafFiber ≅ r.presheafFiber := point_presheafFiber_natIso α
  let γ :
      (q.map (Over.forget U) J).fiber ≅ (r.map (Over.forget U) J).fiber :=
    (q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.symm ≪≫
      Functor.isoWhiskerLeft shrinkYoneda
        (q.presheafFiberMapIso (Over.forget U) J (Type w)) ≪≫
      Functor.isoWhiskerLeft shrinkYoneda (Functor.isoWhiskerLeft W β) ≪≫
      Functor.isoWhiskerLeft shrinkYoneda
        (r.presheafFiberMapIso (Over.forget U) J (Type w)).symm ≪≫
      (r.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso
  -- Package the mapped fiber comparison as a point isomorphism.
  exact point_iso_of_fiber_natIso γ

/-- Helper for Lemma 7.35.2: the terminal object `U/U` contributes a distinguished fiber element
for any point of the slice site. -/
noncomputable def localized_point_terminal_fiber_element
    {U : C} (q : Point.{w} (J.over U)) :
    q.fiber.obj (Over.mk (𝟙 U)) :=
  let h := q.uniqueFiberObj (Over.mk (𝟙 U)) Over.mkIdTerminal
  h.default

/-- Helper for Lemma 7.35.2: every element in the terminal slice fiber equals the distinguished
terminal fiber element. -/
lemma localized_point_terminal_fiber_eq
    {U : C} (q : Point.{w} (J.over U)) (V : Over U) (z : q.fiber.obj V) :
    q.fiber.map (Over.mkIdTerminal.from V) z = localized_point_terminal_fiber_element q := by
  -- The terminal slice fiber is a singleton, so every mapped element agrees with the chosen one.
  let h := q.uniqueFiberObj (Over.mk (𝟙 U)) Over.mkIdTerminal
  exact h.uniq _

/-- Helper for Lemma 7.35.2: the terminal fiber element of `q` over `U/U`, transported along an
isomorphism `q.map (Over.forget U) J ≅ p`, yields the corresponding base element of `p.fiber.obj
U`. -/
noncomputable def localized_point_base_element
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p) :
    p.fiber.obj U :=
  let z : q.fiber.obj (Over.mk (𝟙 U)) := localized_point_terminal_fiber_element q
  e.inv.hom.app U <|
    ((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app U) <|
      q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) (Over.mk (𝟙 U)) z
        (shrinkYonedaObjObjEquiv.symm (𝟙 U))

/-- Helper for Lemma 7.35.2: an isomorphism `q.map (Over.forget U) J ≅ p` induces the canonical
comparison map from each slice fiber of `q` to the corresponding base fiber of `p`. -/
noncomputable def localized_point_fiber_comparison
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p) (V : Over U) :
    q.fiber.obj V → p.fiber.obj V.left :=
  fun z ↦
    e.inv.hom.app V.left <|
      ((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left) <|
        q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
          (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))

/-- Helper for Lemma 7.35.2: the comparison element attached to `z : q.fiber.obj V` maps to the
base element of `p.fiber.obj U`, so it lies in the localized fiber of `p.over x`. -/
lemma localized_point_fiber_comparison_mem_over_fiber
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p)
    (V : Over U) (z : q.fiber.obj V) :
    p.fiber.map V.hom (localized_point_fiber_comparison (p := p) e V z) =
      localized_point_base_element (p := p) e := by
  -- First move the comparison through the point isomorphism `e`.
  have h_e :
      p.fiber.map V.hom
          (localized_point_fiber_comparison (p := p) e V z) =
        e.inv.hom.app U
          ((q.map (Over.forget U) J).fiber.map V.hom
            (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
              (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
                (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))))) := by
    -- Naturality of `e.inv.hom` transfers the ambient fiber map across the isomorphism.
    simpa [localized_point_fiber_comparison] using
      (congrFun (NatTrans.naturality e.inv.hom V.hom)
        (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
          (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
            (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))))).symm
  rw [h_e]
  -- Next rewrite the mapped fiber element via naturality of the shrink-Yoneda comparison.
  have h_shrink :
      (q.map (Over.forget U) J).fiber.map V.hom
          (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
            (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
              (shrinkYonedaObjObjEquiv.symm (𝟙 V.left)))) =
        ((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app U)
          (((q.map (Over.forget U) J).presheafFiber.map (shrinkYoneda.map V.hom))
            (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
              (shrinkYonedaObjObjEquiv.symm (𝟙 V.left)))) := by
    -- This is exactly the naturality square for the owner-level fiber/presheaf comparison.
    simpa using
      (congrFun
        ((NatTrans.naturality
          (q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom V.hom).symm)
        (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
          (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))))
  rw [h_shrink]
  -- Then replace the `shrinkYoneda` restriction by the actual arrow `V ⟶ U`.
  have h_nat :
      ((q.map (Over.forget U) J).presheafFiber.map (shrinkYoneda.map V.hom))
          (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
            (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))) =
        q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) V z
          (((shrinkYoneda.map V.hom).app (Opposite.op V.left))
            (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))) := by
    -- Naturality of `q.toPresheafFiberMap` upgrades the identity section on `V` to the arrow
    -- `V.hom : V.left ⟶ U`.
    simpa using
      (congrFun
        (q.toPresheafFiberMap_naturality (Over.forget U) J
          (shrinkYoneda.map V.hom) V z)
        (shrinkYonedaObjObjEquiv.symm (𝟙 V.left)))
  rw [h_nat]
  have h_eval :
      (((shrinkYoneda.map V.hom).app (Opposite.op V.left))
          (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))) =
        shrinkYonedaObjObjEquiv.symm V.hom := by
    -- Evaluating the Yoneda restriction of the identity section yields the arrow itself.
    simpa using
      (shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}
        (Y := Opposite.op V.left) (𝟙 V.left) V.hom)
  rw [h_eval]
  -- Finally compare the arrow `V ⟶ U` with the unique map to the terminal object `U/U`.
  have h_terminal_map :
      ((shrinkYoneda.obj U).map V.hom.op) (shrinkYonedaObjObjEquiv.symm (𝟙 U)) =
        shrinkYonedaObjObjEquiv.symm V.hom := by
    -- The restriction of the identity section along `V.hom` is the section represented by `V.hom`.
    simpa using (shrinkYonedaObjObjEquiv_symm_comp V.hom (𝟙 U)).symm
  have h_terminal :
      q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) V z
          (shrinkYonedaObjObjEquiv.symm V.hom) =
        q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) (Over.mk (𝟙 U))
          (q.fiber.map (Over.mkIdTerminal.from V) z) (shrinkYonedaObjObjEquiv.symm (𝟙 U)) := by
    -- The terminal map in `Over U` has underlying arrow `V.hom : V.left ⟶ U`.
    calc
      q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) V z
          (shrinkYonedaObjObjEquiv.symm V.hom) =
        q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) V z
          (((shrinkYoneda.obj U).map V.hom.op) (shrinkYonedaObjObjEquiv.symm (𝟙 U))) := by
            exact congrArg
              (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) V z)
              h_terminal_map.symm
      _ = q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) (Over.mk (𝟙 U))
            (q.fiber.map (Over.mkIdTerminal.from V) z) (shrinkYonedaObjObjEquiv.symm (𝟙 U)) := by
              simpa [Over.mkIdTerminal_from_left] using
                congrFun
                  (q.toPresheafFiberMap_w (Over.forget U) J (Over.mkIdTerminal.from V) z
                    (shrinkYoneda.obj U))
                  (shrinkYonedaObjObjEquiv.symm (𝟙 U))
  -- The terminal fiber of `q` is a singleton, so the remaining point is the chosen base element.
  calc
    e.inv.hom.app U
        ((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app U
          (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) V z
            (shrinkYonedaObjObjEquiv.symm V.hom))) =
      e.inv.hom.app U
        ((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app U
          (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) (Over.mk (𝟙 U))
            (q.fiber.map (Over.mkIdTerminal.from V) z) (shrinkYonedaObjObjEquiv.symm (𝟙 U)))) := by
            rw [h_terminal]
    _ = localized_point_base_element (p := p) e := by
      rw [localized_point_terminal_fiber_eq q V z]
      rfl

/-- Helper for Lemma 7.35.2: a point isomorphism transports the localized fibers objectwise. -/
noncomputable def localized_point_over_fiber_equiv_of_iso
    {U : C} {r p : Point.{w} J} (e : r ≅ p) (x : r.fiber.obj U) (V : Over U) :
    (r.over x).fiber.obj V ≃ (p.over (e.inv.hom.app U x)).fiber.obj V where
  toFun y := by
    refine ⟨e.inv.hom.app V.left y.1, ?_⟩
    -- Naturality of the point isomorphism transports the defining localization equation.
    have hnat := congrFun (NatTrans.naturality e.inv.hom V.hom) y.1
    apply localized_point_over_mem_of_eq (p := p)
    calc
      p.fiber.map V.hom (e.inv.hom.app V.left y.1) =
          e.inv.hom.app U (r.fiber.map V.hom y.1) := by
            simpa using hnat.symm
      _ = e.inv.hom.app U x := by
        exact congrArg (e.inv.hom.app U) (localized_point_over_eq_of_mem (p := r) y.2)
  invFun y := by
    refine ⟨e.hom.hom.app V.left y.1, ?_⟩
    -- Apply the inverse natural transformation to recover the original fiber condition.
    have hnat := congrFun (NatTrans.naturality e.hom.hom V.hom) y.1
    have hcomp :
        e.hom.hom.app U (e.inv.hom.app U x) = x := by
      -- The pointwise inverse relation comes from `e.hom ≫ e.inv = 𝟙 r`.
      exact congr_fun
        (NatTrans.congr_app
          (congrArg GrothendieckTopology.Point.Hom.hom e.hom_inv_id) U) x
    apply localized_point_over_mem_of_eq (p := r)
    calc
      r.fiber.map V.hom (e.hom.hom.app V.left y.1) =
          e.hom.hom.app U (p.fiber.map V.hom y.1) := by
            simpa using hnat.symm
      _ = e.hom.hom.app U (e.inv.hom.app U x) := by
        exact congrArg (e.hom.hom.app U) (localized_point_over_eq_of_mem (p := p) y.2)
      _ = x := hcomp
  left_inv y := by
    apply Subtype.ext
    -- The underlying objectwise equivalence is the pointwise inverse relation of `e`.
    exact congr_fun
      (NatTrans.congr_app
        (congrArg GrothendieckTopology.Point.Hom.hom e.hom_inv_id) V.left) y.1
  right_inv y := by
    apply Subtype.ext
    -- The reverse composite is the other pointwise inverse identity.
    exact congr_fun
      (NatTrans.congr_app
        (congrArg GrothendieckTopology.Point.Hom.hom e.inv_hom_id) V.left) y.1

/-- Helper for Lemma 7.35.2: each component of a point isomorphism is an equivalence on the
corresponding fiber. -/
noncomputable def point_component_equiv
    {K : GrothendieckTopology C} {r s : Point.{w} K} (e : r ≅ s) (X : C) :
    r.fiber.obj X ≃ s.fiber.obj X :=
  { toFun := e.inv.hom.app X
    invFun := e.hom.hom.app X
    left_inv := fun x ↦
      congr_fun
        (NatTrans.congr_app
          (congrArg GrothendieckTopology.Point.Hom.hom e.hom_inv_id) X) x
    right_inv := fun x ↦
      congr_fun
        (NatTrans.congr_app
          (congrArg GrothendieckTopology.Point.Hom.hom e.inv_hom_id) X) x }

/-- Helper for Lemma 7.35.2: the representable presheaf on `U/U` maps to the pullback of the base
representable along `Over.forget U` by taking the underlying arrow in `C`. -/
noncomputable def localized_point_terminal_to_base
    {U : C} : shrinkYoneda.obj (Over.mk (𝟙 U)) ⟶ (Over.forget U).op ⋙ shrinkYoneda.obj U where
  app W f :=
    shrinkYonedaObjObjEquiv.symm ((shrinkYonedaObjObjEquiv f).left)
  naturality X Y g := by
    -- Naturality is just composition of the underlying arrows in `C`.
    ext f
    simpa [shrinkYonedaObjObjEquiv_obj_map] using
      (shrinkYonedaObjObjEquiv_symm_comp g.unop.left ((shrinkYonedaObjObjEquiv f).left))

/-- Helper for Lemma 7.35.2: the representable presheaf on `V` maps to the pullback of the base
representable on `V.left` by forgetting the slice structure. -/
noncomputable def localized_point_representable_to_base
    {U : C} (V : Over U) :
    shrinkYoneda.obj V ⟶ (Over.forget U).op ⋙ shrinkYoneda.obj V.left where
  app W f :=
    shrinkYonedaObjObjEquiv.symm ((shrinkYonedaObjObjEquiv f).left)
  naturality X Y g := by
    -- Forgetting the slice structure commutes with restriction along `g`.
    ext f
    simpa [shrinkYonedaObjObjEquiv_obj_map] using
      (shrinkYonedaObjObjEquiv_symm_comp g.unop.left ((shrinkYonedaObjObjEquiv f).left))

/-- Helper for Lemma 7.35.2: objectwise, the top horizontal map in the source square just forgets
the slice structure and remembers the underlying arrow in `C`. -/
lemma localized_point_representable_to_base_app
    {U : C} (V : Over U) (X : (Over U)ᵒᵖ)
    (f : (shrinkYoneda.obj V).obj X) :
    shrinkYonedaObjObjEquiv ((localized_point_representable_to_base (U := U) V).app X f) =
      (shrinkYonedaObjObjEquiv f).left := by
  -- Unfolding the comparison map leaves the explicit `shrinkYonedaObjObjEquiv.symm` term.
  simpa [localized_point_representable_to_base] using
    ((shrinkYonedaObjObjEquiv (X := V.left) (Y := (Over.forget U).op.obj X)).apply_symm_apply
      ((shrinkYonedaObjObjEquiv f).left))

/-- Helper for Lemma 7.35.2: objectwise, the bottom horizontal map in the source square sends a
slice morphism to the underlying arrow into `U`. -/
lemma localized_point_terminal_to_base_app
    {U : C} (X : (Over U)ᵒᵖ)
    (f : (shrinkYoneda.obj (Over.mk (𝟙 U))).obj X) :
    shrinkYonedaObjObjEquiv ((localized_point_terminal_to_base (U := U)).app X f) =
      (shrinkYonedaObjObjEquiv f).left := by
  -- Unfolding the terminal comparison map gives the same explicit `shrinkYonedaObjObjEquiv.symm`.
  simpa [localized_point_terminal_to_base] using
    ((shrinkYonedaObjObjEquiv (X := U) (Y := (Over.forget U).op.obj X)).apply_symm_apply
      ((shrinkYonedaObjObjEquiv f).left))

/-- Helper for Lemma 7.35.2: the source square of slice representables is objectwise cartesian. -/
lemma localized_point_representable_square_isPullback
    {U : C} (V : Over U) :
    IsPullback
      (localized_point_representable_to_base (U := U) V)
      (shrinkYoneda.map (Over.mkIdTerminal.from V))
      (((Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type w)).obj (Over.forget U).op).map
        (shrinkYoneda.map V.hom))
      (localized_point_terminal_to_base (U := U)) := by
  -- The source proof works objectwise: at each `X`, the square is literally the Hom-square in the
  -- slice category over the map `V ⟶ U`.
  refine IsPullback.of_forall_isPullback_app ?_
  intro X
  refine
    (CategoryTheory.Limits.Types.isPullback_iff
      (((localized_point_representable_to_base (U := U) V).app X))
      (((((Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type w)).obj (Over.forget U).op).map
        (shrinkYoneda.map V.hom)).app X))
      ((((shrinkYoneda.map (Over.mkIdTerminal.from V))).app X))
      (((localized_point_terminal_to_base (U := U)).app X))).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · ext f
    -- Both routes forget the slice morphism and keep the same composite arrow to `U`.
    apply shrinkYonedaObjObjEquiv.injective
    simp only [types_comp_apply]
    have hterminal :
        shrinkYonedaObjObjEquiv
            (localized_point_terminal_to_base.app X
              ((shrinkYoneda.map (Over.mkIdTerminal.from V)).app X f)) =
          ((shrinkYonedaObjObjEquiv f) ≫ Over.mkIdTerminal.from V).left := by
      calc
        shrinkYonedaObjObjEquiv
            (localized_point_terminal_to_base.app X
              ((shrinkYoneda.map (Over.mkIdTerminal.from V)).app X f)) =
          (shrinkYonedaObjObjEquiv
            ((shrinkYoneda.map (Over.mkIdTerminal.from V)).app X f)).left :=
              localized_point_terminal_to_base_app (U := U) X
                ((shrinkYoneda.map (Over.mkIdTerminal.from V)).app X f)
        _ = ((shrinkYonedaObjObjEquiv f) ≫ Over.mkIdTerminal.from V).left := by
              rw [shrinkYonedaObjObjEquiv_map_app]
    have htop :
        shrinkYonedaObjObjEquiv
            ((((Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type w)).obj (Over.forget U).op).map
                (shrinkYoneda.map V.hom)).app X
              ((localized_point_representable_to_base (U := U) V).app X f)) =
          ((shrinkYonedaObjObjEquiv f) ≫ Over.mkIdTerminal.from V).left := by
      calc
        shrinkYonedaObjObjEquiv
            ((((Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type w)).obj (Over.forget U).op).map
                (shrinkYoneda.map V.hom)).app X
              ((localized_point_representable_to_base (U := U) V).app X f)) =
          shrinkYonedaObjObjEquiv ((localized_point_representable_to_base (U := U) V).app X f) ≫
            V.hom := by
              simpa using
                (shrinkYonedaObjObjEquiv_map_app
                  (f := (localized_point_representable_to_base (U := U) V).app X f)
                  (g := V.hom) (Y := (Over.forget U).op.obj X))
        _ = ((shrinkYonedaObjObjEquiv f) ≫ Over.mkIdTerminal.from V).left := by
              rw [localized_point_representable_to_base_app (U := U) V X f]
              simpa [Over.mkIdTerminal_from_left] using Over.w (shrinkYonedaObjObjEquiv f)
    exact htop.trans hterminal.symm
  · intro f g hfg
    -- Equality after forgetting the slice structure forces equality of the original slice maps.
    have hleft := congrArg shrinkYonedaObjObjEquiv hfg.1
    rw [localized_point_representable_to_base_app (U := U) V X f,
      localized_point_representable_to_base_app (U := U) V X g] at hleft
    exact shrinkYonedaObjObjEquiv.injective (Over.OverMorphism.ext hleft)
  · intro f g hfg
    -- Build the unique slice morphism whose underlying map is `f`; the pullback compatibility
    -- says precisely that it lands over the chosen terminal arrow `g`.
    have hfg' :
        shrinkYonedaObjObjEquiv f ≫ V.hom = (shrinkYonedaObjObjEquiv g).left := by
      have hmap :
          shrinkYonedaObjObjEquiv
              ((((Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type w)).obj (Over.forget U).op).map
                  (shrinkYoneda.map V.hom)).app X f) =
            shrinkYonedaObjObjEquiv f ≫ V.hom := by
        simpa using
          (shrinkYonedaObjObjEquiv_map_app (f := f) (g := V.hom)
            (Y := (Over.forget U).op.obj X))
      exact hmap.symm.trans <|
        (congrArg shrinkYonedaObjObjEquiv hfg).trans
          (localized_point_terminal_to_base_app (U := U) X g)
    have hg_left :
        (shrinkYonedaObjObjEquiv g).left = X.unop.hom := by
      simpa using Over.w (shrinkYonedaObjObjEquiv g)
    let k : X.unop ⟶ V :=
      Over.homMk (shrinkYonedaObjObjEquiv f) (hfg'.trans hg_left)
    refine ⟨shrinkYonedaObjObjEquiv.symm k, ?_, ?_⟩
    · -- The top edge of the pullback square is the prescribed underlying arrow `f`.
      apply shrinkYonedaObjObjEquiv.injective
      rw [localized_point_representable_to_base_app]
      simp [k]
    · -- The left edge is the unique map to the terminal object with that underlying arrow.
      apply shrinkYonedaObjObjEquiv.injective
      apply Over.OverMorphism.ext
      have hk :
          (shrinkYonedaObjObjEquiv
              ((shrinkYoneda.map (Over.mkIdTerminal.from V)).app X
                (shrinkYonedaObjObjEquiv.symm k))).left = X.unop.hom := by
        simpa using
          congrArg (fun m => m.left)
            (shrinkYonedaObjObjEquiv_map_app
              (f := shrinkYonedaObjObjEquiv.symm k)
              (g := Over.mkIdTerminal.from V) (Y := X))
      exact hk.trans hg_left.symm

/-- Helper for Lemma 7.35.2: the left edge of the mapped representable square is exactly the
restriction map to the terminal object of the slice site after transporting through
`q.shrinkYonedaCompPresheafFiberIso`. -/
lemma localized_point_fiber_square_left_comm
    {U : C} (q : Point.{w} (J.over U)) (V : Over U) :
    ((q.shrinkYonedaCompPresheafFiberIso.app V).symm).hom ≫
        q.presheafFiber.map (shrinkYoneda.map (Over.mkIdTerminal.from V)) =
      q.fiber.map (Over.mkIdTerminal.from V) ≫
        ((q.shrinkYonedaCompPresheafFiberIso.app (Over.mk (𝟙 U))).symm).hom := by
  -- This is exactly the naturality square for the inverse shrink-Yoneda comparison on `q`.
  ext z
  simpa using
    (q.shrinkYonedaCompPresheafFiberIso.inv.naturality_apply (Over.mkIdTerminal.from V) z).symm

/-- Helper for Lemma 7.35.2: the top-right and bottom-right corners of the mapped representable
square identify with the corresponding fibers of `p` via the owner-level map comparison and the
chosen point isomorphism `e`. -/
noncomputable def localized_point_right_corner_iso
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p) (X : C) :
    q.presheafFiber.obj ((Over.forget U).op ⋙ shrinkYoneda.obj X) ≅ p.fiber.obj X :=
  (q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj X)).symm ≪≫
    (q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.app X ≪≫
    Equiv.toIso (point_component_equiv e X)

/-- Helper for Lemma 7.35.2: the top identity section of the representable pullback square
normalizes to the canonical mapped fiber generator. -/
lemma localized_point_representable_identity_section_toPresheafFiberMap
    {U : C} {q : Point.{w} (J.over U)} (V : Over U) (z : q.fiber.obj V) :
    ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj V.left)).inv)
        (q.presheafFiber.map (localized_point_representable_to_base (U := U) V)
          (((q.shrinkYonedaCompPresheafFiberIso.app V).symm).hom z)) =
      q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
        (shrinkYonedaObjObjEquiv.symm (𝟙 V.left)) := by
  -- Rewrite the inverse shrink-Yoneda comparison as the canonical `toPresheafFiber` term.
  change
    ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj V.left)).inv)
        (q.presheafFiber.map (localized_point_representable_to_base (U := U) V)
          (q.shrinkYonedaCompPresheafFiberIso.inv.app V z)) =
      q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
        (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))
  rw [q.shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber z]
  -- Evaluate the top comparison map on the identity section of `V`.
  have h_section :
      (localized_point_representable_to_base (U := U) V).app (Opposite.op V)
          (shrinkYonedaObjObjEquiv.symm (𝟙 V)) =
        shrinkYonedaObjObjEquiv.symm (𝟙 V.left) := by
    apply shrinkYonedaObjObjEquiv.injective
    rw [localized_point_representable_to_base_app (U := U) V (Opposite.op V)
      (shrinkYonedaObjObjEquiv.symm (𝟙 V))]
    calc
      (shrinkYonedaObjObjEquiv (shrinkYonedaObjObjEquiv.symm (𝟙 V))).left = 𝟙 V.left := by
        simpa using congrArg (fun m : V ⟶ V ↦ m.left)
          (Equiv.apply_symm_apply shrinkYonedaObjObjEquiv (𝟙 V))
      _ = (shrinkYonedaObjObjEquiv (X := V.left) (Y := Opposite.op V.left))
            (shrinkYonedaObjObjEquiv.symm (𝟙 V.left)) := by
          symm
          exact
            (shrinkYonedaObjObjEquiv (X := V.left) (Y := Opposite.op V.left)).apply_symm_apply
              (𝟙 V.left)
  -- Naturality moves the section across `localized_point_representable_to_base`.
  calc
    ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj V.left)).inv)
        (q.presheafFiber.map (localized_point_representable_to_base (U := U) V)
          (q.toPresheafFiber V z (shrinkYoneda.obj V)
            (shrinkYonedaObjObjEquiv.symm (𝟙 V)))) =
      ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj V.left)).inv)
        (q.toPresheafFiber V z ((Over.forget U).op ⋙ shrinkYoneda.obj V.left)
          ((localized_point_representable_to_base (U := U) V).app (Opposite.op V)
            (shrinkYonedaObjObjEquiv.symm (𝟙 V)))) := by
              exact congrArg
                ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj V.left)).inv)
                (q.toPresheafFiber_naturality_apply
                  (localized_point_representable_to_base (U := U) V) V z
                  (shrinkYonedaObjObjEquiv.symm (𝟙 V)))
    _ = ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj V.left)).inv)
          (q.toPresheafFiber V z ((Over.forget U).op ⋙ shrinkYoneda.obj V.left)
            (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))) := by
              exact congrArg
                ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj V.left)).inv)
                (congrArg
                  (q.toPresheafFiber V z ((Over.forget U).op ⋙ shrinkYoneda.obj V.left))
                  h_section)
    _ = q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
          (shrinkYonedaObjObjEquiv.symm (𝟙 V.left)) := by
            simpa using
              congr_fun
                (q.toPresheafFiber_presheafFiberMapObjIso_inv
                  (Over.forget U) J (shrinkYoneda.obj V.left) V z)
                (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))

/-- Helper for Lemma 7.35.2: transporting the identity section of `h_{V/U}` through the right
corner comparison recovers the explicit comparison map on fibers. -/
lemma localized_point_representable_to_base_identity_section_transport
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p)
    (V : Over U) (z : q.fiber.obj V) :
    (localized_point_right_corner_iso (p := p) e V.left).hom
        (q.presheafFiber.map (localized_point_representable_to_base (U := U) V)
          (((q.shrinkYonedaCompPresheafFiberIso.app V).symm).hom z)) =
      localized_point_fiber_comparison (p := p) e V z := by
  -- Expand the right-corner comparison until only the objectwise bridge lemma remains.
  dsimp [localized_point_right_corner_iso, localized_point_fiber_comparison, point_component_equiv]
  -- The top edge has already been normalized to `toPresheafFiberMap`.
  exact congrArg
    (fun t ↦
      e.inv.hom.app V.left
        (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left) t))
    (localized_point_representable_identity_section_toPresheafFiberMap
      (q := q) (U := U) V z)

/-- Helper for Lemma 7.35.2: the right-corner transport is natural in the base arrow
`V.left ⟶ U`. -/
lemma localized_point_right_corner_transport_naturality
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p)
    (V : Over U)
    (t : q.presheafFiber.obj ((Over.forget U).op ⋙ shrinkYoneda.obj V.left)) :
    (localized_point_right_corner_iso (p := p) e U).hom
        (q.presheafFiber.map
          ((((Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type w)).obj (Over.forget U).op).map
            (shrinkYoneda.map V.hom))) t) =
      p.fiber.map V.hom ((localized_point_right_corner_iso (p := p) e V.left).hom t) := by
  -- First move across the objectwise `presheafFiberMapObjIso`.
  have h_mapObj :
      ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj U)).inv)
          (q.presheafFiber.map
            ((Over.forget U).op.whiskerLeft (shrinkYoneda.map V.hom)) t) =
        (q.map (Over.forget U) J).presheafFiber.map (shrinkYoneda.map V.hom)
          (((q.presheafFiberMapObjIso (Over.forget U) J
            (shrinkYoneda.obj V.left)).inv) t) := by
    simpa using
      congrFun
        (NatTrans.naturality
          (q.presheafFiberMapIso (Over.forget U) J (Type w)).inv (shrinkYoneda.map V.hom)) t
  -- Next pass through the shrink-Yoneda comparison on the mapped point.
  have h_shrink :
      ((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app U)
          ((q.map (Over.forget U) J).presheafFiber.map (shrinkYoneda.map V.hom)
            (((q.presheafFiberMapObjIso (Over.forget U) J
              (shrinkYoneda.obj V.left)).inv) t)) =
        (q.map (Over.forget U) J).fiber.map V.hom
          (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
            (((q.presheafFiberMapObjIso (Over.forget U) J
              (shrinkYoneda.obj V.left)).inv) t)) := by
    simpa using
      congrFun
        (NatTrans.naturality
          (q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom V.hom)
        (((q.presheafFiberMapObjIso (Over.forget U) J
          (shrinkYoneda.obj V.left)).inv) t)
  -- Finally use naturality of the chosen point isomorphism `e`.
  have h_e :
      e.inv.hom.app U
          ((q.map (Over.forget U) J).fiber.map V.hom
            (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
              (((q.presheafFiberMapObjIso (Over.forget U) J
                (shrinkYoneda.obj V.left)).inv) t))) =
        p.fiber.map V.hom
          (e.inv.hom.app V.left
            (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
              (((q.presheafFiberMapObjIso (Over.forget U) J
                (shrinkYoneda.obj V.left)).inv) t))) := by
    simpa using
      congrFun
        (NatTrans.naturality e.inv.hom V.hom)
        (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
          (((q.presheafFiberMapObjIso (Over.forget U) J
            (shrinkYoneda.obj V.left)).inv) t))
  -- Chaining the three owner-level naturality squares gives the transported right edge.
  dsimp [localized_point_right_corner_iso, point_component_equiv]
  calc
    e.inv.hom.app U
        ((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app U
          ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj U)).inv
            (q.presheafFiber.map ((Over.forget U).op.whiskerLeft (shrinkYoneda.map V.hom)) t))) =
      e.inv.hom.app U
        ((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app U
          ((q.map (Over.forget U) J).presheafFiber.map (shrinkYoneda.map V.hom)
            (((q.presheafFiberMapObjIso (Over.forget U) J
              (shrinkYoneda.obj V.left)).inv) t))) := by
              exact congrArg
                (fun s ↦
                  e.inv.hom.app U
                    (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app U) s))
                h_mapObj
    _ = e.inv.hom.app U
          ((q.map (Over.forget U) J).fiber.map V.hom
            (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
              (((q.presheafFiberMapObjIso (Over.forget U) J
                (shrinkYoneda.obj V.left)).inv) t))) := by
                  exact congrArg (e.inv.hom.app U) h_shrink
    _ = p.fiber.map V.hom
          (e.inv.hom.app V.left
            (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
              (((q.presheafFiberMapObjIso (Over.forget U) J
                (shrinkYoneda.obj V.left)).inv) t))) := h_e

/-- Helper for Lemma 7.35.2: the terminal identity section also normalizes to the canonical mapped
fiber generator used to define the base element. -/
lemma localized_point_terminal_identity_section_toPresheafFiberMap
    {U : C} {q : Point.{w} (J.over U)} :
    ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj U)).inv)
        (q.presheafFiber.map (localized_point_terminal_to_base (U := U))
          (((q.shrinkYonedaCompPresheafFiberIso.app (Over.mk (𝟙 U))).symm).hom
            (localized_point_terminal_fiber_element q))) =
      q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) (Over.mk (𝟙 U))
        (localized_point_terminal_fiber_element q) (shrinkYonedaObjObjEquiv.symm (𝟙 U)) := by
  -- Rewrite the inverse shrink-Yoneda comparison as the terminal `toPresheafFiber` term.
  change
    ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj U)).inv)
        (q.presheafFiber.map (localized_point_terminal_to_base (U := U))
          (q.shrinkYonedaCompPresheafFiberIso.inv.app (Over.mk (𝟙 U))
            (localized_point_terminal_fiber_element q))) =
      q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) (Over.mk (𝟙 U))
        (localized_point_terminal_fiber_element q) (shrinkYonedaObjObjEquiv.symm (𝟙 U))
  rw [q.shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber
    (localized_point_terminal_fiber_element q)]
  -- Evaluate the bottom comparison map on the identity section of `U/U`.
  have h_section :
      (localized_point_terminal_to_base (U := U)).app (Opposite.op (Over.mk (𝟙 U)))
          (shrinkYonedaObjObjEquiv.symm (𝟙 (Over.mk (𝟙 U)))) =
        shrinkYonedaObjObjEquiv.symm (𝟙 U) := by
    apply shrinkYonedaObjObjEquiv.injective
    rw [localized_point_terminal_to_base_app (U := U) (Opposite.op (Over.mk (𝟙 U)))
      (shrinkYonedaObjObjEquiv.symm (𝟙 (Over.mk (𝟙 U))))]
    calc
      (shrinkYonedaObjObjEquiv
          (shrinkYonedaObjObjEquiv.symm (𝟙 (Over.mk (𝟙 U))))).left = 𝟙 U := by
            simpa using congrArg (fun m : Over.mk (𝟙 U) ⟶ Over.mk (𝟙 U) ↦ m.left)
              (Equiv.apply_symm_apply shrinkYonedaObjObjEquiv (𝟙 (Over.mk (𝟙 U))))
      _ = (shrinkYonedaObjObjEquiv (X := U) (Y := Opposite.op U))
            (shrinkYonedaObjObjEquiv.symm (𝟙 U)) := by
            symm
            exact (shrinkYonedaObjObjEquiv (X := U) (Y := Opposite.op U)).apply_symm_apply
              (𝟙 U)
  -- Naturality moves the section across `localized_point_terminal_to_base`.
  calc
    ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj U)).inv)
        (q.presheafFiber.map (localized_point_terminal_to_base (U := U))
          (q.toPresheafFiber (Over.mk (𝟙 U)) (localized_point_terminal_fiber_element q)
            (shrinkYoneda.obj (Over.mk (𝟙 U)))
            (shrinkYonedaObjObjEquiv.symm (𝟙 (Over.mk (𝟙 U)))))) =
      ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj U)).inv)
        (q.toPresheafFiber (Over.mk (𝟙 U)) (localized_point_terminal_fiber_element q)
          ((Over.forget U).op ⋙ shrinkYoneda.obj U)
          ((localized_point_terminal_to_base (U := U)).app (Opposite.op (Over.mk (𝟙 U)))
            (shrinkYonedaObjObjEquiv.symm (𝟙 (Over.mk (𝟙 U)))))) := by
              exact congrArg
                ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj U)).inv)
                (q.toPresheafFiber_naturality_apply
                  (localized_point_terminal_to_base (U := U)) (Over.mk (𝟙 U))
                  (localized_point_terminal_fiber_element q)
                  (shrinkYonedaObjObjEquiv.symm (𝟙 (Over.mk (𝟙 U)))))
    _ = ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj U)).inv)
          (q.toPresheafFiber (Over.mk (𝟙 U)) (localized_point_terminal_fiber_element q)
            ((Over.forget U).op ⋙ shrinkYoneda.obj U)
            (shrinkYonedaObjObjEquiv.symm (𝟙 U))) := by
              exact congrArg
                ((q.presheafFiberMapObjIso (Over.forget U) J (shrinkYoneda.obj U)).inv)
                (congrArg
                  (q.toPresheafFiber (Over.mk (𝟙 U)) (localized_point_terminal_fiber_element q)
                    ((Over.forget U).op ⋙ shrinkYoneda.obj U))
                  h_section)
    _ = q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj U) (Over.mk (𝟙 U))
          (localized_point_terminal_fiber_element q) (shrinkYonedaObjObjEquiv.symm (𝟙 U)) := by
            simpa using
              congr_fun
                (q.toPresheafFiber_presheafFiberMapObjIso_inv
                  (Over.forget U) J (shrinkYoneda.obj U) (Over.mk (𝟙 U))
                  (localized_point_terminal_fiber_element q))
                (shrinkYonedaObjObjEquiv.symm (𝟙 U))

/-- Helper for Lemma 7.35.2: after transporting the terminal slice section to the base, the right
corner comparison yields the distinguished element of `p.fiber.obj U`. -/
lemma localized_point_terminal_to_base_transport_constant
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p)
    (z : q.fiber.obj (Over.mk (𝟙 U))) :
    (localized_point_right_corner_iso (p := p) e U).hom
        (q.presheafFiber.map (localized_point_terminal_to_base (U := U))
          (((q.shrinkYonedaCompPresheafFiberIso.app (Over.mk (𝟙 U))).symm).hom z)) =
      localized_point_base_element (p := p) e := by
  -- Replace the arbitrary terminal-fiber element by the distinguished singleton element.
  have hz : z = localized_point_terminal_fiber_element q := by
    simpa [localized_point_terminal_fiber_element] using
      (q.uniqueFiberObj (Over.mk (𝟙 U)) Over.mkIdTerminal).uniq z
  rw [hz]
  -- Expand the right corner and the chosen base element until the bottom bridge applies.
  dsimp [localized_point_right_corner_iso, localized_point_base_element, point_component_equiv]
  exact congrArg
    (fun t ↦
      e.inv.hom.app U
        (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app U) t))
    (localized_point_terminal_identity_section_toPresheafFiberMap (q := q) (U := U))

/-- Helper for Lemma 7.35.2: after transporting the representable pullback square through the point
comparison `e`, the resulting square of fibers is cartesian. -/
lemma localized_point_fiber_square_isPullback
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p) (V : Over U) :
    IsPullback
      (localized_point_fiber_comparison (p := p) e V)
      (q.fiber.map (Over.mkIdTerminal.from V))
      (p.fiber.map V.hom)
      (fun _ : q.fiber.obj (Over.mk (𝟙 U)) ↦ localized_point_base_element (p := p) e) := by
  -- Route correction: the source-faithful cartesian square is now isolated above as a representable
  -- pullback, so the only remaining task is to transport its image under `q.presheafFiber` to the
  -- concrete comparison square on `q.fiber` and `p.fiber`.
  let hsource := localized_point_representable_square_isPullback (U := U) V
  let hmapped := CategoryTheory.Functor.map_isPullback q.presheafFiber hsource
  let e₁ : q.fiber.obj V ≅ q.presheafFiber.obj (shrinkYoneda.obj V) :=
    (q.shrinkYonedaCompPresheafFiberIso.app V).symm
  let e₂ : p.fiber.obj V.left ≅ q.presheafFiber.obj ((Over.forget U).op ⋙ shrinkYoneda.obj V.left) :=
    (localized_point_right_corner_iso (p := p) e V.left).symm
  let e₃ :
      q.fiber.obj (Over.mk (𝟙 U)) ≅ q.presheafFiber.obj (shrinkYoneda.obj (Over.mk (𝟙 U))) :=
    (q.shrinkYonedaCompPresheafFiberIso.app (Over.mk (𝟙 U))).symm
  let e₄ : p.fiber.obj U ≅ q.presheafFiber.obj ((Over.forget U).op ⋙ shrinkYoneda.obj U) :=
    (localized_point_right_corner_iso (p := p) e U).symm
  -- Transport the mapped pullback square corner-by-corner to the concrete fiber square.
  refine hmapped.of_iso' e₁ e₂ e₃ e₄ ?_ ?_ ?_ ?_
  · -- The top edge is the explicit comparison on fibers.
    ext z
    apply (localized_point_right_corner_iso (p := p) e V.left).toEquiv.injective
    simpa [e₁, e₂] using
      localized_point_representable_to_base_identity_section_transport
        (p := p) e V z
  · -- The left edge is the restriction map to the terminal object in the slice site.
    simpa [e₁, e₃] using localized_point_fiber_square_left_comm q V
  · -- The right edge is the naturality square for the right-corner comparison.
    ext t
    apply (localized_point_right_corner_iso (p := p) e U).toEquiv.injective
    simpa [e₂, e₄] using
      localized_point_right_corner_transport_naturality (p := p) e V (e₂.hom t)
  · -- The bottom edge is the constant map to the distinguished base element.
    ext z
    apply (localized_point_right_corner_iso (p := p) e U).toEquiv.injective
    simpa [e₃, e₄] using
      localized_point_terminal_to_base_transport_constant (p := p) e z

/-- Helper for Lemma 7.35.2: the fiber comparison commutes with restriction maps in the slice
site. -/
lemma localized_point_fiber_comparison_naturality
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p)
    {V W : Over U} (f : V ⟶ W) (z : q.fiber.obj V) :
    localized_point_fiber_comparison (p := p) e W (q.fiber.map f z) =
      p.fiber.map f.left (localized_point_fiber_comparison (p := p) e V z) := by
  -- First move the comparison through the point isomorphism `e`.
  have h_e :
      p.fiber.map f.left
          (localized_point_fiber_comparison (p := p) e V z) =
        e.inv.hom.app W.left
          ((q.map (Over.forget U) J).fiber.map f.left
            (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
              (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
                (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))))) := by
    -- Naturality of `e.inv.hom` transfers the base restriction map across the isomorphism.
    simpa [localized_point_fiber_comparison] using
      (congrFun (NatTrans.naturality e.inv.hom f.left)
        (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
          (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
            (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))))).symm
  rw [h_e]
  -- Next move the restriction map past the shrink-Yoneda comparison.
  have h_shrink :
      (q.map (Over.forget U) J).fiber.map f.left
          (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app V.left)
            (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
              (shrinkYonedaObjObjEquiv.symm (𝟙 V.left)))) =
        ((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app W.left)
          (((q.map (Over.forget U) J).presheafFiber.map (shrinkYoneda.map f.left))
            (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
              (shrinkYonedaObjObjEquiv.symm (𝟙 V.left)))) := by
    -- This is the naturality square of the owner-level comparison with `shrinkYoneda`.
    simpa using
      (congrFun
        ((NatTrans.naturality
          (q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom f.left).symm)
        (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
          (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))))
  rw [h_shrink]
  -- Then transport the presheaf element along the base map `f.left : V.left ⟶ W.left`.
  have h_nat :
      ((q.map (Over.forget U) J).presheafFiber.map (shrinkYoneda.map f.left))
          (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj V.left) V z
            (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))) =
        q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj W.left) V z
          (((shrinkYoneda.map f.left).app (Opposite.op V.left))
            (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))) := by
    -- Naturality of `q.toPresheafFiberMap` changes the chosen presheaf from `V.left` to `W.left`.
    simpa using
      (congrFun
        (q.toPresheafFiberMap_naturality (Over.forget U) J
          (shrinkYoneda.map f.left) V z)
        (shrinkYonedaObjObjEquiv.symm (𝟙 V.left)))
  rw [h_nat]
  have h_eval :
      (((shrinkYoneda.map f.left).app (Opposite.op V.left))
          (shrinkYonedaObjObjEquiv.symm (𝟙 V.left))) =
        shrinkYonedaObjObjEquiv.symm f.left := by
    -- Restricting the identity section along `f.left` yields the section represented by `f.left`.
    simpa using
      (shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}
        (Y := Opposite.op V.left) (𝟙 V.left) f.left)
  rw [h_eval]
  -- Finally move from the arrow `f.left` to the actual slice morphism `f`.
  have h_w :
      q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj W.left) V z
          (shrinkYonedaObjObjEquiv.symm f.left) =
        q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj W.left) W
          (q.fiber.map f z) (shrinkYonedaObjObjEquiv.symm (𝟙 W.left)) := by
    -- This is the compatibility of `q.toPresheafFiberMap` with restriction along `f`.
    calc
      q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj W.left) V z
          (shrinkYonedaObjObjEquiv.symm f.left) =
        q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj W.left) V z
          (((shrinkYoneda.obj W.left).map f.left.op)
            (shrinkYonedaObjObjEquiv.symm (𝟙 W.left))) := by
              exact congrArg
                (q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj W.left) V z)
                (by simpa using shrinkYonedaObjObjEquiv_symm_comp f.left (𝟙 W.left))
      _ = q.toPresheafFiberMap (Over.forget U) J (shrinkYoneda.obj W.left) W
            (q.fiber.map f z) (shrinkYonedaObjObjEquiv.symm (𝟙 W.left)) := by
              simpa using
                congrFun
                  (q.toPresheafFiberMap_w (Over.forget U) J f z (shrinkYoneda.obj W.left))
                  (shrinkYonedaObjObjEquiv.symm (𝟙 W.left))
  -- Reinsert the actual slice morphism `f` into the owner-level comparison.
  simpa [localized_point_fiber_comparison] using
    congrArg
      (fun t ↦
        e.inv.hom.app W.left
          (((q.map (Over.forget U) J).shrinkYonedaCompPresheafFiberIso.hom.app W.left) t))
      h_w.symm

/-- Helper for Lemma 7.35.2: the fiber of `q` over `V` identifies with the localized base fiber
cut out by the element attached to `e`. -/
noncomputable def localized_point_over_fiber_equiv
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p) (V : Over U) :
    q.fiber.obj V ≃ (p.over (localized_point_base_element (p := p) e)).fiber.obj V := by
  classical
  let hpb := localized_point_fiber_square_isPullback (p := p) e V
  refine
    { toFun := fun z ↦
        ⟨localized_point_fiber_comparison (p := p) e V z,
          localized_point_over_mem_of_eq (p := p)
            (localized_point_fiber_comparison_mem_over_fiber (p := p) e V z)⟩
      invFun := fun y ↦
        Classical.choose <|
          CategoryTheory.Limits.Types.exists_of_isPullback hpb y.1
            (localized_point_terminal_fiber_element q) (localized_point_over_eq_of_mem (p := p) y.2)
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    -- The cartesian square recovers `z` from its image in the base fiber and the terminal fiber.
    have hz :=
      Classical.choose_spec
        (CategoryTheory.Limits.Types.exists_of_isPullback hpb
          (localized_point_fiber_comparison (p := p) e V z)
          (localized_point_terminal_fiber_element q)
          (localized_point_fiber_comparison_mem_over_fiber (p := p) e V z))
    exact
      CategoryTheory.Limits.Types.ext_of_isPullback hpb hz.1
        (hz.2.trans (localized_point_terminal_fiber_eq q V z).symm)
  · intro y
    -- The first projection of the cartesian square is exactly the localized section we started
    -- with, so the inverse lands back on `y`.
    apply Subtype.ext
    exact
      (Classical.choose_spec
        (CategoryTheory.Limits.Types.exists_of_isPullback hpb y.1
          (localized_point_terminal_fiber_element q) (localized_point_over_eq_of_mem (p := p) y.2))).1

/-- Helper for Lemma 7.35.2: the objectwise equivalences between `q.fiber` and
`(p.over localized_point_base_element e).fiber` are natural in `V`. -/
lemma localized_point_over_fiber_equiv_naturality
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p)
    {V W : Over U} (f : V ⟶ W) (z : q.fiber.obj V) :
    localized_point_over_fiber_equiv (p := p) e W (q.fiber.map f z) =
      (p.over (localized_point_base_element (p := p) e)).fiber.map f
        (localized_point_over_fiber_equiv (p := p) e V z) := by
  -- The explicit forward description of the equivalence is the comparison map on the first
  -- component, so naturality reduces to the naturality of that comparison.
  apply Subtype.ext
  simpa [GrothendieckTopology.Point.over_fiber] using
    localized_point_fiber_comparison_naturality (p := p) e f z

/-- Helper for Lemma 7.35.2: the objectwise localized-fiber equivalences package to a natural
isomorphism of point fibers. -/
noncomputable def localized_point_over_fiber_natIso
    {U : C} {q : Point.{w} (J.over U)} (e : q.map (Over.forget U) J ≅ p) :
    q.fiber ≅ (p.over (localized_point_base_element (p := p) e)).fiber := by
  -- Assemble the pointwise equivalences into the fiber-functor isomorphism used in the main proof.
  refine NatIso.ofComponents (fun V ↦ (localized_point_over_fiber_equiv (p := p) e V).toIso) ?_
  intro V W f
  ext z
  exact localized_point_over_fiber_equiv_naturality (p := p) e f z

/-- Lemma 7.35.2, repaired for the current isomorphism-class formulation: for a point `p` of
`(C, J)`, an object `U : C`, and a point `q` of the localized site `(C/U, J.over U)`, the point
`q` lies over `p` precisely when it is isomorphic to some localized point `p.over x`. The source
bijection is between points with their chosen lying-over identification and elements of `u(U)`;
a bare `IsIsomorphic` hypothesis is weaker and does not support uniqueness of `x`. -/
theorem localized_point_lies_over_iff_unique_fiber_element
    (p : Point.{w} J) (U : C) (q : Point.{w} (J.over U)) :
    IsIsomorphic (q.map (Over.forget U) J) p ↔
      ∃ x : p.fiber.obj U, IsIsomorphic q (p.over x) := by
  constructor
  · intro hq
    -- Route correction: close the forward direction by the source-faithful pullback comparison of
    -- slice representables, then package the resulting fiber equivalence into a point isomorphism.
    obtain ⟨e⟩ := hq
    refine ⟨localized_point_base_element (p := p) e, ?_⟩
    exact ⟨point_iso_of_fiber_natIso (localized_point_over_fiber_natIso (p := p) e)⟩
  · rintro ⟨x, hx⟩
    -- Any point isomorphic to `p.over x` maps to a point isomorphic to `p`.
    obtain ⟨i⟩ := hx
    obtain ⟨j⟩ := point_over_map_forget_iso p U x
    exact ⟨localized_point_map_forget_iso_of_point_iso i ≪≫ j⟩

end
end

end CategoryTheory
