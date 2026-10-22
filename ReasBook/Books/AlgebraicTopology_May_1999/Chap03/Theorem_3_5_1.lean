/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_3
import AlgebraicTopology_May_1999.Chap03.ProofStep_3_5_2
import AlgebraicTopology_May_1999.Chap03.Remark_3_3_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {X : Type u₁} {E : Type u₂} {B : Type u₃}
variable [Groupoid.{v₁} X] [Groupoid.{v₂} E] [Groupoid.{v₃} B]

/-- Helper for Theorem 3.5.1: the chosen endpoint associated to an object `x` is obtained by
lifting the image of the chosen path `a x : x₀ ⟶ x` from the basepoint `e₀`. -/
noncomputable def chosen_lift_obj {p : E ⥤ B} (hp : Functor.IsCovering p) {f : X ⥤ B}
    {x₀ : X} (e₀ : p.Fiber (f.obj x₀)) (a : ∀ x : X, x₀ ⟶ x) (x : X) : p.Fiber (f.obj x) :=
  fiberTranslationMap hp (f.map (a x)) e₀

/-- Helper for Theorem 3.5.1: translating along an equality morphism just transports the fiber
point across the corresponding equality of base objects. -/
lemma fiberTranslationMap_eqToHom {p : E ⥤ B} (hp : Functor.IsCovering p) {b b' : B}
    (h : b = b') (x : p.Fiber b) :
    fiberTranslationMap hp (eqToHom h) x = h ▸ x := by
  -- After reducing to `h = rfl`, this is exactly the identity action on the fiber.
  cases h
  exact congrFun (fiberTranslationMap_id hp b) x

/-- Helper for Theorem 3.5.1: a fiber translation from a general fiber point can be normalized to
the literal basepoint `⟨e, rfl⟩` by precomposing the base arrow with the equality witness. -/
lemma fiberTranslationMap_normalize_basepoint {p : E ⥤ B} (hp : Functor.IsCovering p)
    {e : E} {b b' : B} (h : p.obj e = b) (γ : b ⟶ b') :
    fiberTranslationMap hp γ ⟨e, h⟩ =
      fiberTranslationMap hp (eqToHom h ≫ γ) ⟨e, rfl⟩ := by
  -- Collapsing the equality witness reduces the statement to the identity transport.
  cases h
  simp

/-- Helper for Theorem 3.5.1: membership in the transported image subgroup is equivalent to
membership of the conjugated loop in the untransported subgroup at the literal basepoint. -/
lemma mapVertexGroup_range_transport_iff {p : E ⥤ B} {e : E} {b : B}
    (h : p.obj e = b) (δ : b ⟶ b) :
    δ ∈ h ▸ (Functor.mapVertexGroup p e).range ↔
      eqToHom h ≫ δ ≫ eqToHom h.symm ∈ (Functor.mapVertexGroup p e).range := by
  -- After eliminating the equality witness, both subgroup-membership conditions are identical.
  cases h
  simp

/-- Helper for Theorem 3.5.1: any loop whose class lies in the transported image subgroup fixes
the chosen fiber point under fiber translation. -/
lemma fiberTranslationMap_eq_self_of_mem_transport_range {p : E ⥤ B} (hp : Functor.IsCovering p)
    {e : E} {b : B} (h : p.obj e = b) (δ : b ⟶ b)
    (hδ : δ ∈ h ▸ (Functor.mapVertexGroup p e).range) :
    fiberTranslationMap hp δ ⟨e, h⟩ = ⟨e, h⟩ := by
  -- First convert the transported membership statement to the literal-basepoint loop subgroup.
  have hδ' : eqToHom h ≫ δ ≫ eqToHom h.symm ∈ (Functor.mapVertexGroup p e).range := by
    exact (mapVertexGroup_range_transport_iff h δ).1 hδ
  -- At the literal basepoint, Remark 3.3.13 shows that loops in the subgroup act trivially.
  have hbase :
      fiberTranslationMap hp (eqToHom h ≫ δ ≫ eqToHom h.symm) ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
    have hmemInv :
        𝟙 (p.obj e) * (eqToHom h ≫ δ ≫ eqToHom h.symm)⁻¹ ∈
          (Functor.mapVertexGroup p e).range := by
      simpa using Subgroup.inv_mem (Functor.mapVertexGroup p e).range hδ'
    exact
      (fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range hp e
        (eqToHom h ≫ δ ≫ eqToHom h.symm) (𝟙 (p.obj e)) hmemInv).trans
        (congrFun (fiberTranslationMap_id hp (p.obj e)) ⟨e, rfl⟩)
  -- Transport the literal-basepoint fixed-point statement back to the original fiber point.
  calc
    fiberTranslationMap hp δ ⟨e, h⟩ =
        fiberTranslationMap hp (eqToHom h ≫ δ) ⟨e, rfl⟩ := by
      simpa using fiberTranslationMap_normalize_basepoint hp h δ
    _ = fiberTranslationMap hp
          ((eqToHom h ≫ δ ≫ eqToHom h.symm) ≫ eqToHom h) ⟨e, rfl⟩ := by
      simp [Category.assoc]
    _ = fiberTranslationMap hp (eqToHom h)
          (fiberTranslationMap hp (eqToHom h ≫ δ ≫ eqToHom h.symm) ⟨e, rfl⟩) := by
      symm
      change
        (fiberTranslationMap hp (eqToHom h) ∘
            fiberTranslationMap hp (eqToHom h ≫ δ ≫ eqToHom h.symm)) ⟨e, rfl⟩ =
          fiberTranslationMap hp ((eqToHom h ≫ δ ≫ eqToHom h.symm) ≫ eqToHom h) ⟨e, rfl⟩
      exact (congrArg (fun m => m ⟨e, rfl⟩)
        (fiberTranslationMap_comp hp (eqToHom h ≫ δ ≫ eqToHom h.symm) (eqToHom h))).symm
    _ = fiberTranslationMap hp (eqToHom h) ⟨e, rfl⟩ := by
      rw [hbase]
    _ = h ▸ (⟨e, rfl⟩ : p.Fiber (p.obj e)) := by
      rw [fiberTranslationMap_eqToHom hp]
    _ = ⟨e, h⟩ := by
      cases h
      rfl

/-- Helper for Theorem 3.5.1: under the subgroup hypothesis, the endpoint of the lifted image of a
path `x₀ ⟶ x` is independent of the chosen path. -/
lemma lift_endpoint_eq_of_subgroup_inclusion {p : E ⥤ B} (hp : Functor.IsCovering p)
    {f : X ⥤ B} (x₀ : X) (e₀ : p.Fiber (f.obj x₀))
    (hsub : (Functor.mapVertexGroup f x₀).range ≤
      e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range)
    {x : X} (α₁ α₂ : x₀ ⟶ x) :
    fiberTranslationMap hp (f.map α₁) e₀ =
      fiberTranslationMap hp (f.map α₂) e₀ := by
  symm
  -- The loop comparing the two chosen paths is based at `x₀`, so the subgroup hypothesis applies.
  have hloop :
      f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁) ∈
        e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range := by
    apply hsub
    refine ⟨α₂ ≫ CategoryTheory.Groupoid.inv α₁, ?_⟩
    simp [Functor.map_comp]
  -- Once that loop fixes `e₀`, composing with `α₁` reproduces the lift along `α₂`.
  have hfix :
      fiberTranslationMap hp (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) e₀ = e₀ := by
    exact fiberTranslationMap_eq_self_of_mem_transport_range hp e₀.2
      (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) hloop
  calc
    fiberTranslationMap hp (f.map α₂) e₀ =
        fiberTranslationMap hp (f.map ((α₂ ≫ CategoryTheory.Groupoid.inv α₁) ≫ α₁)) e₀ := by
      simp
    _ = fiberTranslationMap hp (f.map α₁)
          (fiberTranslationMap hp (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) e₀) := by
      simpa [Functor.map_comp] using
        congrArg (fun m => m e₀)
          (fiberTranslationMap_comp hp
            (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) (f.map α₁))
    _ = fiberTranslationMap hp (f.map α₁) e₀ := by
      rw [hfix]

/-- Helper for Theorem 3.5.1: the chosen lifted object is compatible with transport along a
source morphism `β : x ⟶ y`. -/
lemma chosen_lift_obj_comp {p : E ⥤ B} (hp : Functor.IsCovering p) {f : X ⥤ B} (x₀ : X)
    (e₀ : p.Fiber (f.obj x₀))
    (hsub : (Functor.mapVertexGroup f x₀).range ≤
      e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range)
    (a : ∀ x : X, x₀ ⟶ x) {x y : X} (β : x ⟶ y) :
    fiberTranslationMap hp (f.map β) (chosen_lift_obj (x₀ := x₀) hp e₀ a x) =
        chosen_lift_obj (x₀ := x₀) hp e₀ a y := by
  -- First concatenate the chosen path to `x` with `β`, then invoke path independence.
  calc
    fiberTranslationMap hp (f.map β) (chosen_lift_obj (x₀ := x₀) hp e₀ a x) =
        fiberTranslationMap hp (f.map (a x ≫ β)) e₀ := by
      rw [chosen_lift_obj, Functor.map_comp]
      change
        (fiberTranslationMap hp (f.map β) ∘ fiberTranslationMap hp (f.map (a x))) e₀ =
          fiberTranslationMap hp (f.map (a x) ≫ f.map β) e₀
      exact (congrArg (fun m => m e₀)
        (fiberTranslationMap_comp hp (f.map (a x)) (f.map β))).symm
    _ = chosen_lift_obj (x₀ := x₀) hp e₀ a y := by
      rw [chosen_lift_obj]
      exact lift_endpoint_eq_of_subgroup_inclusion hp x₀ e₀ hsub (a x ≫ β) (a y)

variable [CategoryTheory.IsConnected X]

/-- Theorem 3.5.1: for a covering functor `p : E ⥤ B`, a functor `f : X ⥤ B` from a connected
groupoid `X`, and a chosen point `e₀` of the fiber over `f.obj x₀`, there is a unique lift
`g : X ⥤ E` with
`g.obj x₀ = e₀.1` exactly when the image of the vertex group at `x₀` under `f` is contained in
the image of the vertex group at `e₀.1` under `p`, after identifying both as subgroups of the
vertex group at `f.obj x₀`. -/
-- Proof sketch: the forward implication is `Functor.mapVertexGroup_range_le_of_lift`. For the
-- converse, choose for each object `x : X` a morphism `α : x₀ ⟶ x`, lift `f.map α` through the
-- covering functor starting at `e₀`, and use the subgroup inclusion hypothesis to show that the
-- resulting endpoint is independent of the chosen `α`; the same lifting prescription on morphisms
-- then defines the unique functor lift.
theorem existsUnique_lift_iff_mapVertexGroup_range_le {p : E ⥤ B} (hp : Functor.IsCovering p)
    {f : X ⥤ B} (x₀ : X) (e₀ : p.Fiber (f.obj x₀)) :
    (∃! g : X ⥤ E, g ⋙ p = f ∧ g.obj x₀ = e₀.1) ↔
      (Functor.mapVertexGroup f x₀).range ≤
        e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range := by
  constructor
  · rintro ⟨g, hg, _⟩
    exact Functor.mapVertexGroup_range_le_of_lift x₀ e₀ hg.1 hg.2
  · intro hsub
    classical
    have hVertexInjective : ∀ e : E, Function.Injective (Functor.mapVertexGroup p e) := by
      intro e γ δ hγδ
      have hUnder :
          (Under.post p).obj (Under.mk γ) = (Under.post p).obj (Under.mk δ) :=
        congrArg Under.mk hγδ
      have hEq : Under.mk γ = Under.mk δ := (hp.star_bijective e).injective hUnder
      cases hEq
      rfl
    -- Follow the source proof: choose one path from `x₀` to each object and lift it from `e₀`.
    let a : ∀ x : X, x₀ ⟶ x := fun x ↦
      Classical.choice (show Nonempty (x₀ ⟶ x) from inferInstance)
    let gObj : ∀ x : X, p.Fiber (f.obj x) := fun x ↦
      chosen_lift_obj (x₀ := x₀) hp e₀ a x
    have hgObj_comp : ∀ {x y : X} (β : x ⟶ y),
        fiberTranslationMap hp (f.map β) (gObj x) = gObj y := by
      intro x y β
      exact chosen_lift_obj_comp hp x₀ e₀ hsub a β
    have hgObj₀ : gObj x₀ = e₀ := by
      -- Path independence already identifies the chosen endpoint at `x₀` with the basepoint.
      have hid : fiberTranslationMap hp (f.map (𝟙 x₀)) e₀ = e₀ := by
        rw [f.map_id]
        exact congrFun (fiberTranslationMap_id hp (f.obj x₀)) e₀
      exact
        (lift_endpoint_eq_of_subgroup_inclusion hp x₀ e₀ hsub (a x₀) (𝟙 x₀)).trans
          hid
    have hgObj_val_comp : ∀ {x y : X} (β : x ⟶ y),
        (fiberTranslationMap hp (f.map β) (gObj x)).1 = (gObj y).1 := by
      intro x y β
      exact congrArg Subtype.val (hgObj_comp β)
    let gMap : ∀ {x y : X}, (x ⟶ y) → ((gObj x).1 ⟶ (gObj y).1) := fun {x y} β ↦
      (starLift hp (f.map β) (gObj x)).hom ≫ eqToHom (hgObj_val_comp β)
    have hgMap_transport : ∀ {x y : X} (β : x ⟶ y),
        eqToHom (starLift_obj hp (f.map β) (gObj x)).symm ≫ p.map (eqToHom (hgObj_val_comp β)) =
          eqToHom (gObj y).2.symm := by
      intro x y β
      -- The two endpoint identifications are proofs of the same equality, so proof irrelevance
      -- collapses the remaining transport.
      have hEq :
          (starLift_obj hp (f.map β) (gObj x)).symm.trans (congrArg p.obj (hgObj_val_comp β)) =
            (gObj y).2.symm := by
        apply Subsingleton.elim
      calc
        eqToHom (starLift_obj hp (f.map β) (gObj x)).symm ≫ p.map (eqToHom (hgObj_val_comp β)) =
            eqToHom (starLift_obj hp (f.map β) (gObj x)).symm ≫
              eqToHom (congrArg p.obj (hgObj_val_comp β)) := by
          rw [eqToHom_map]
        _ =
            eqToHom
              ((starLift_obj hp (f.map β) (gObj x)).symm.trans
                (congrArg p.obj (hgObj_val_comp β))) := by
          rw [eqToHom_trans]
        _ = eqToHom (gObj y).2.symm := by
          rw [hEq]
    have hgMap_over : ∀ {x y : X} (β : x ⟶ y),
        p.map (gMap β) =
          eqToHom (gObj x).2 ≫ f.map β ≫ eqToHom (gObj y).2.symm := by
      intro x y β
      -- Route correction: keep the codomain-adjustment explicit and cancel it with one transport
      -- identity, instead of repeatedly destructing dependent equalities of fiber points.
      have htransport := hgMap_transport β
      have hstar :
          p.map (gMap β) =
            ((eqToHom (gObj x).2 ≫ f.map β ≫ eqToHom (starLift_obj hp (f.map β) (gObj x)).symm) ≫
              p.map (eqToHom (hgObj_val_comp β))) := by
        have h₁ :
            p.map (gMap β) =
              p.map (starLift hp (f.map β) (gObj x)).hom ≫ p.map (eqToHom (hgObj_val_comp β)) := by
          simp [gMap]
        have h₂raw :=
          congrArg (fun k ↦ k ≫ p.map (eqToHom (hgObj_val_comp β)))
            (starLift_hom_over hp (f.map β) (gObj x))
        exact h₁.trans h₂raw
      calc
        p.map (gMap β) =
            eqToHom (gObj x).2 ≫ f.map β ≫ eqToHom (starLift_obj hp (f.map β) (gObj x)).symm ≫
              p.map (eqToHom (hgObj_val_comp β)) := by
          simpa [Category.assoc] using hstar
        _ =
            eqToHom (gObj x).2 ≫ f.map β ≫ eqToHom (gObj y).2.symm := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ eqToHom (gObj x).2 ≫ f.map β ≫ k) htransport
    have hgMap_id : ∀ x : X, gMap (𝟙 x) = 𝟙 ((gObj x).1) := by
      intro x
      -- Since both candidates are loops at `(gObj x).1`, injectivity on the vertex group
      -- upgrades equality after applying `p` to equality in `E`.
      have hmap : p.map (gMap (𝟙 x)) = 𝟙 (p.obj ((gObj x).1)) := by
        simpa using hgMap_over (𝟙 x)
      exact (hVertexInjective ((gObj x).1)) (by simpa using hmap)
    have hgMap_comp : ∀ {x y z : X} (β : x ⟶ y) (γ : y ⟶ z),
        gMap (β ≫ γ) = gMap β ≫ gMap γ := by
      intro x y z β γ
      -- Compare the two arrows by forming the loop obtained from their quotient.
      have hmap :
          p.map (gMap (β ≫ γ)) = p.map (gMap β ≫ gMap γ) := by
        calc
          p.map (gMap (β ≫ γ)) =
              eqToHom (gObj x).2 ≫ f.map (β ≫ γ) ≫ eqToHom (gObj z).2.symm := by
            rw [hgMap_over]
          _ =
              (eqToHom (gObj x).2 ≫ f.map β ≫ eqToHom (gObj y).2.symm) ≫
                (eqToHom (gObj y).2 ≫ f.map γ ≫ eqToHom (gObj z).2.symm) := by
            simp [Functor.map_comp, Category.assoc]
          _ = p.map (gMap β) ≫ p.map (gMap γ) := by
            rw [hgMap_over, hgMap_over]
          _ = p.map (gMap β ≫ gMap γ) := by
            simp [Functor.map_comp]
      let rhsComp : (gObj x).1 ⟶ (gObj z).1 := gMap β ≫ gMap γ
      have hloop :
          gMap (β ≫ γ) ≫ CategoryTheory.Groupoid.inv rhsComp = 𝟙 ((gObj x).1) := by
        apply (hVertexInjective ((gObj x).1))
        calc
          p.map (gMap (β ≫ γ) ≫ CategoryTheory.Groupoid.inv rhsComp) =
              p.map (gMap (β ≫ γ)) ≫ CategoryTheory.Groupoid.inv (p.map rhsComp) := by
            simp [Functor.map_comp]
          _ = p.map rhsComp ≫ CategoryTheory.Groupoid.inv (p.map rhsComp) := by
            rw [hmap]
          _ = (Functor.mapVertexGroup p ((gObj x).1)) (𝟙 ((gObj x).1)) := by
            simp
      have hcancel := congrArg (fun k ↦ k ≫ rhsComp) hloop
      simpa [rhsComp, Category.assoc] using hcancel
    let g : X ⥤ E := {
      obj := fun x ↦ (gObj x).1
      map := fun {x y} β ↦ gMap β
      map_id := fun x ↦ hgMap_id x
      map_comp := fun {x y z} β γ ↦ hgMap_comp β γ
    }
    have hg : g ⋙ p = f := by
      -- On objects the chosen lift lands over `f.obj x`, and on morphisms `hgMap_over` gives the
      -- required transported equality in the base.
      refine CategoryTheory.Functor.ext (fun x ↦ by simpa [g] using (gObj x).2) ?_
      intro x y β
      simpa [g, Functor.comp_map] using hgMap_over β
    have hg₀ : g.obj x₀ = e₀.1 := by
      -- The chosen lifted object at the basepoint is exactly the prescribed fiber point `e₀`.
      simpa [g] using congrArg Subtype.val hgObj₀
    refine ⟨g, ⟨hg, hg₀⟩, ?_⟩
    intro g' hg'
    let e₀' : p.Fiber (f.obj x₀) := ⟨g'.obj x₀, by
      simpa [Functor.comp_obj] using congrArg (fun k : X ⥤ B ↦ k.obj x₀) hg'.1⟩
    have he₀' : e₀' = e₀ := by
      apply Subtype.ext
      exact hg'.2
    have hpath : ∀ x : X, Under.mk (g'.map (a x)) = starLift hp (f.map (a x)) e₀' := by
      intro x
      -- Both arrows start at `g'.obj x₀`, so compare them before identifying that source with `e₀`.
      apply (hp.star_bijective (g'.obj x₀)).injective
      calc
        (Under.post p).obj (Under.mk (g'.map (a x))) = Under.mk (p.map (g'.map (a x))) := by
          simp [Under.post]
        _ =
            Under.mk
              (eqToHom e₀'.2 ≫ f.map (a x) ≫
                eqToHom (congrArg (fun k : X ⥤ B ↦ k.obj x) hg'.1).symm) := by
          simpa [e₀', Functor.comp_obj, Functor.comp_map] using
            congrArg Under.mk (Functor.congr_hom hg'.1 (a x))
        _ = Under.mk (eqToHom e₀'.2 ≫ f.map (a x)) := by
          simpa [Category.assoc] using
            under_mk_comp_eqToHom
              (eqToHom e₀'.2 ≫ f.map (a x))
              (congrArg (fun k : X ⥤ B ↦ k.obj x) hg'.1).symm
        _ = (Under.post p).obj (starLift hp (f.map (a x)) e₀') := by
          have hstar := starLift_post_eq hp (f.map (a x)) e₀'
          rw [fiber_transport_under_mk] at hstar
          exact hstar.symm
    have hobj : ∀ x : X, g'.obj x = g.obj x := by
      intro x
      -- Project the chosen-path comparison to the right endpoint of the lifted arrow.
      have hright : g'.obj x = (starLift hp (f.map (a x)) e₀').right := by
        exact congrArg Comma.right (hpath x)
      rw [he₀'] at hright
      simpa [g, gObj, chosen_lift_obj] using hright
    -- With the source and target objects identified, star-map injectivity upgrades equality after
    -- composing with `p` to equality of the lifted arrows themselves.
    refine CategoryTheory.Functor.ext hobj ?_
    intro x y β
    have hcomp : g' ⋙ p = g ⋙ p := hg'.1.trans hg.symm
    let rhs : g'.obj x ⟶ g'.obj y := eqToHom (hobj x) ≫ g.map β ≫ eqToHom (hobj y).symm
    let rhsInv : g'.obj y ⟶ g'.obj x :=
      eqToHom (hobj y) ≫ CategoryTheory.Groupoid.inv (g.map β) ≫ eqToHom (hobj x).symm
    have hmap : p.map (g'.map β) = p.map rhs := by
      simpa [rhs, Functor.comp_map, eqToHom_map, Category.assoc] using Functor.congr_hom hcomp β
    have hloop : g'.map β ≫ rhsInv = 𝟙 (g'.obj x) := by
      apply (hVertexInjective (g'.obj x))
      calc
        p.map (g'.map β ≫ rhsInv) = p.map (g'.map β) ≫ p.map rhsInv := by
          simp [rhsInv, Functor.map_comp]
        _ = p.map rhs ≫ p.map rhsInv := by
          rw [hmap]
        _ = (Functor.mapVertexGroup p (g'.obj x)) (𝟙 (g'.obj x)) := by
          simp [rhs, rhsInv, eqToHom_map, Category.assoc]
    have hcancel := congrArg (fun k ↦ k ≫ rhs) hloop
    simpa [rhs, rhsInv, Category.assoc] using hcancel

end CategoryTheory.Functor.IsCovering
