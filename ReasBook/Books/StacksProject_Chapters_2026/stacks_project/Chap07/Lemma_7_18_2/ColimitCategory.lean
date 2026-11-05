module

public import stacks_project.Chap07.Situation_7_18_1

@[expose] public section

/-!
Proof support for Lemma 7.18.2: the explicit colimit category of a cofiltered system of sites.

The source text of tag 09YL constructs the category `\mathcal C = \mathop{\mathrm{colim}}
\mathcal C_i` explicitly: its objects are the colimit of the stage object sets and its arrows are
the colimit of the stage arrow sets. This file realizes that construction verbatim: objects are a
quotient of pairs `(i, X)` with `X ∈ \mathcal C_i`, morphisms are a quotient of stage morphisms
under common lowering, and the cocone functors `u_i` are strict. The Stacks descent facts
("every object/arrow comes from some stage", "two stage arrows equal in the colimit agree after a
common lowering") are then definitional (`_root_.Quotient.exists_rep` / `_root_.Quotient.exact`) instead of
being extracted from an abstract colimit, which is impossible at this universe generality.

The common-lowering relation is phrased through equalities of `Arrow.mk` images, so that
transitivity and all stability arguments are plain `congrArg`/`Eq.trans` chains; `eqToHom`
transports appear only when a relation is unfolded into endpoint identifications.
-/

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe uI uC vC

namespace CofilteredSiteDiagram

variable (S : CofilteredSiteDiagram.{uI, uC, vC})

/-- Complete a cospan in the cofiltered index category: two index arrows with common target are
dominated by a commuting span. -/
theorem exists_span {j k₁ k₂ : S.I} (f : k₁ ⟶ j) (g : k₂ ⟶ j) :
    ∃ (m : S.I) (u : m ⟶ k₁) (v : m ⟶ k₂), u ≫ f = v ≫ g := by
  refine ⟨IsCofiltered.eq (IsCofiltered.minToLeft k₁ k₂ ≫ f) (IsCofiltered.minToRight k₁ k₂ ≫ g),
    IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToLeft k₁ k₂,
    IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToRight k₁ k₂, ?_⟩
  simpa [Category.assoc] using
    IsCofiltered.eq_condition
      (IsCofiltered.minToLeft k₁ k₂ ≫ f) (IsCofiltered.minToRight k₁ k₂ ≫ g)

section TransitionCalculus

/-- Object part of the strict composition law for transition functors. -/
theorem stageFunctor_obj_comp {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) (X : S.stage i) :
    (S.stageFunctor b).obj ((S.stageFunctor a).obj X) = (S.stageFunctor (b ≫ a)).obj X :=
  (Functor.congr_obj (S.stageFunctor_comp_eq a b) X).symm

/-- Object part of the strict identity law for transition functors. -/
theorem stageFunctor_obj_id {i : S.I} (X : S.stage i) :
    (S.stageFunctor (𝟙 i)).obj X = X :=
  Functor.congr_obj (S.stageFunctor_id_eq i) X

/-- Morphism part of the strict composition law for transition functors, with the canonical
object transports. -/
theorem stageFunctor_map_map {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    {X Y : S.stage i} (f : X ⟶ Y) :
    (S.stageFunctor b).map ((S.stageFunctor a).map f) =
      eqToHom (S.stageFunctor_obj_comp a b X) ≫ (S.stageFunctor (b ≫ a)).map f ≫
        eqToHom (S.stageFunctor_obj_comp a b Y).symm := by
  have h := Functor.congr_hom (S.stageFunctor_comp_eq a b).symm f
  simpa using h

/-- Morphism part of the strict identity law for transition functors. -/
theorem stageFunctor_map_id {i : S.I} {X Y : S.stage i} (f : X ⟶ Y) :
    (S.stageFunctor (𝟙 i)).map f =
      eqToHom (S.stageFunctor_obj_id X) ≫ f ≫ eqToHom (S.stageFunctor_obj_id Y).symm := by
  simpa using Functor.congr_hom (S.stageFunctor_id_eq i) f

/-- Arrow-level strict composition law: lowering twice is lowering along the composite. This is
the transport-free workhorse used by all common-lowering arguments below. -/
theorem arrowMk_map_map {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    {X Y : S.stage i} (f : X ⟶ Y) :
    Arrow.mk ((S.stageFunctor b).map ((S.stageFunctor a).map f)) =
      Arrow.mk ((S.stageFunctor (b ≫ a)).map f) :=
  (congrArg (fun (G : S.stage i ⥤ S.stage k) => Arrow.mk (G.map f))
    (S.stageFunctor_comp_eq a b)).symm

/-- Arrow-level strict identity law for transition functors. -/
theorem arrowMk_map_id {i : S.I} {X Y : S.stage i} (f : X ⟶ Y) :
    Arrow.mk ((S.stageFunctor (𝟙 i)).map f) = Arrow.mk f :=
  congrArg (fun (G : S.stage i ⥤ S.stage i) => Arrow.mk (G.map f))
    (S.stageFunctor_id_eq i)

end TransitionCalculus

section ArrowCalculus

variable {C : Type*} [Category C]

/-- Unfold an equality of `Arrow.mk` images into endpoint identifications and the transported
morphism equality. -/
theorem arrowMk_eq_iff {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    Arrow.mk f = Arrow.mk g ↔
      ∃ (h₁ : X₁ = X₂) (h₂ : Y₁ = Y₂), f = eqToHom h₁ ≫ g ≫ eqToHom h₂.symm := by
  constructor
  · intro h
    have h₁ : X₁ = X₂ := congrArg Comma.left h
    have h₂ : Y₁ = Y₂ := congrArg Comma.right h
    refine ⟨h₁, h₂, ?_⟩
    rw [conj_eqToHom_iff_heq f g h₁ h₂]
    exact congr_arg_heq Comma.hom h
  · rintro ⟨h₁, h₂, h⟩
    subst h₁; subst h₂
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h
    exact congrArg (fun k => Arrow.mk k) h

/-- Pre-composition with a transport does not change the `Arrow.mk` image up to the induced
endpoint identification. -/
theorem arrowMk_eqToHom_comp {X X' Y : C} (h : X' = X) (f : X ⟶ Y) :
    Arrow.mk (eqToHom h ≫ f) = Arrow.mk f := by
  subst h; simp

/-- Post-composition with a transport does not change the `Arrow.mk` image up to the induced
endpoint identification. -/
theorem arrowMk_comp_eqToHom {X Y Y' : C} (f : X ⟶ Y) (h : Y = Y') :
    Arrow.mk (f ≫ eqToHom h) = Arrow.mk f := by
  subst h; simp

/-- Horizontal pasting of `Arrow.mk` equalities along transport glue: two factor-wise equal
composites with transported middles have equal `Arrow.mk` images. -/
theorem arrowMk_glue_comp_congr {X₁ Y₁ X₂ Y₂ Z₁ W₁ Z₂ W₂ : C}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {g₁ : Z₁ ⟶ W₁} {g₂ : Z₂ ⟶ W₂}
    (hf : Arrow.mk f₁ = Arrow.mk f₂) (hg : Arrow.mk g₁ = Arrow.mk g₂)
    (h₁ : Y₁ = Z₁) (h₂ : Y₂ = Z₂) :
    Arrow.mk (f₁ ≫ eqToHom h₁ ≫ g₁) = Arrow.mk (f₂ ≫ eqToHom h₂ ≫ g₂) := by
  obtain ⟨hX, hY, hf⟩ := (arrowMk_eq_iff _ _).1 hf
  obtain ⟨hZ, hW, hg⟩ := (arrowMk_eq_iff _ _).1 hg
  subst hX; subst hY; subst hZ; subst hW
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  subst hf; subst hg
  rfl

/-- Cancel an inner transport conjugation against an outer one. -/
theorem conj_conj_cancel {X X' Y Y' : C} (p : X = X') (q : Y' = Y) (m : X ⟶ Y') :
    eqToHom p ≫ (eqToHom p.symm ≫ m ≫ eqToHom q) ≫ eqToHom q.symm = m := by
  subst p; subst q; simp

/-- Solve a transport-conjugation equation for the conjugated morphism. -/
theorem conj_of_conj {X X' Y Y' : C} {m : X ⟶ Y} {m' : X' ⟶ Y'}
    (p : X = X') (q : Y' = Y) (h : m = eqToHom p ≫ m' ≫ eqToHom q) :
    m' = eqToHom p.symm ≫ m ≫ eqToHom q.symm := by
  subst p; subst q; simpa using h.symm

/-- Collapse a doubly nested transport conjugation into a single one. -/
theorem conj_collapse_nested {A₁ A₂ A₃ A₄ B₄ B₃ B₂ B₁ : C}
    (p₁ : A₁ = A₂) (p₂ : A₂ = A₃) (p₃ : A₃ = A₄)
    (q₃ : B₄ = B₃) (q₂ : B₃ = B₂) (q₁ : B₂ = B₁)
    (m : A₄ ⟶ B₄) (z₁ : A₁ = A₄) (z₂ : B₄ = B₁) :
    eqToHom p₁ ≫ (eqToHom p₂ ≫ (eqToHom p₃ ≫ m ≫ eqToHom q₃) ≫ eqToHom q₂) ≫ eqToHom q₁ =
      eqToHom z₁ ≫ m ≫ eqToHom z₂ := by
  subst p₁; subst p₂; subst p₃; subst q₃; subst q₂; subst q₁
  simp

/-- Two transport-conjugated factors composing to the identity force the underlying factors to
compose to the identity. -/
theorem conj_pair_comp_eq_id {U V U' V' : C}
    (p : U' = U) (r : V' = V) (f : U ⟶ V) (q' : V ⟶ U) (h : f ≫ q' = 𝟙 U) :
    (eqToHom p ≫ f ≫ eqToHom r.symm) ≫ (eqToHom r ≫ q' ≫ eqToHom p.symm) = 𝟙 U' := by
  subst p; subst r; simpa using h

/-- Collapse a singly nested transport conjugation into a flat one. -/
theorem conj_collapse₂ {A₁ A₂ A₃ B₃ B₂ B₁ : C}
    (p₁ : A₁ = A₂) (p₂ : A₂ = A₃) (q₂ : B₃ = B₂) (q₁ : B₂ = B₁)
    (m : A₃ ⟶ B₃) (z₁ : A₁ = A₃) (z₂ : B₃ = B₁) :
    eqToHom p₁ ≫ (eqToHom p₂ ≫ m ≫ eqToHom q₂) ≫ eqToHom q₁ =
      eqToHom z₁ ≫ m ≫ eqToHom z₂ := by
  subst p₁; subst p₂; subst q₂; subst q₁; simp

/-- Collapse a left-nested transport conjugation into a flat one. -/
theorem conj_collapse₂' {A₁ A₂ A₃ B₄ B₃ B₂ B₁ : C}
    (p₁ : A₁ = A₂) (p₂ : A₂ = A₃) (q₃ : B₄ = B₃) (q₂ : B₃ = B₂) (q₁ : B₂ = B₁)
    (m : A₃ ⟶ B₄) (z₁ : A₁ = A₃) (z₂ : B₄ = B₁) :
    eqToHom p₁ ≫ ((eqToHom p₂ ≫ m ≫ eqToHom q₃) ≫ eqToHom q₂) ≫ eqToHom q₁ =
      eqToHom z₁ ≫ m ≫ eqToHom z₂ := by
  subst p₁; subst p₂; subst q₃; subst q₂; subst q₁; simp

/-- Flatten a left transport pair. -/
theorem conj_flat_left {X X' X'' Y Y' : C} (p : X = X') (p' : X' = X'') (q : Y = Y')
    (m : X'' ⟶ Y) (z₁ : X = X'') (z₂ : Y = Y') :
    eqToHom p ≫ (eqToHom p' ≫ m ≫ eqToHom q) = eqToHom z₁ ≫ m ≫ eqToHom z₂ := by
  subst p; subst p'; subst q; simp

/-- Fuse two transport conjugates along a cancelling middle pair. -/
theorem conj_fuse {X X' Y Y' Z Z' : C} (p : X' = X) (q : Y = Y') (r : Z = Z')
    (x : X ⟶ Y) (y : Y ⟶ Z) :
    (eqToHom p ≫ x ≫ eqToHom q) ≫ (eqToHom q.symm ≫ y ≫ eqToHom r) =
      eqToHom p ≫ (x ≫ y) ≫ eqToHom r := by
  subst p; subst q; subst r; simp

/-- Cancel a common transport conjugation. -/
theorem eq_of_conj_eq {X X' Y Y' : C} (p : X' = X) (q : Y = Y') {x y : X ⟶ Y}
    (h : eqToHom p ≫ x ≫ eqToHom q = eqToHom p ≫ y ≫ eqToHom q) : x = y := by
  subst p; subst q; simpa using h

/-- Cancel a common left transport. -/
theorem eq_of_eqToHom_comp_eq {X X' Y : C} (p : X = X') {x y : X' ⟶ Y}
    (h : eqToHom p ≫ x = eqToHom p ≫ y) : x = y := by
  subst p; simpa using h

/-- Cancel a common right transport. -/
theorem eq_of_comp_eqToHom_eq {X Y Y' : C} (p : Y = Y') {x y : X ⟶ Y}
    (h : x ≫ eqToHom p = y ≫ eqToHom p) : x = y := by
  subst p; simpa using h

/-- Solve a left-transport equation. -/
theorem eq_eqToHom_comp_of_comp_eq {X X' Y : C} (p : X = X') {x : X' ⟶ Y} {y : X ⟶ Y}
    (h : eqToHom p ≫ x = y) : x = eqToHom p.symm ≫ y := by
  subst p; simpa using h

/-- Transport a commuting square along conjugation data for its parallel sides. -/
theorem square_transport {A B₁ B₂ Cc B₁' B₂' Cc' : C}
    {x₁ : A ⟶ B₁} {x₂ : A ⟶ B₂} {m₁ : B₁ ⟶ Cc} {m₂ : B₂ ⟶ Cc}
    (p₁ : B₁ = B₁') (p₂ : B₂ = B₂') (r : Cc = Cc')
    {m₁' : B₁' ⟶ Cc'} {m₂' : B₂' ⟶ Cc'}
    (hm₁ : m₁ = eqToHom p₁ ≫ m₁' ≫ eqToHom r.symm)
    (hm₂ : m₂ = eqToHom p₂ ≫ m₂' ≫ eqToHom r.symm)
    (h : x₁ ≫ m₁ = x₂ ≫ m₂) :
    (x₁ ≫ eqToHom p₁) ≫ m₁' = (x₂ ≫ eqToHom p₂) ≫ m₂' := by
  subst p₁; subst p₂; subst r
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hm₁ hm₂ ⊢
  rw [← hm₁, ← hm₂]
  exact h

/-- Strip a symmetric transport pair after a conjugation. -/
theorem conj_unsymm {X X' Y Y' : C} (p : X' = X) (q : Y = Y') (m : X ⟶ Y) :
    (eqToHom p ≫ m ≫ eqToHom q) ≫ eqToHom q.symm = eqToHom p ≫ m := by
  subst p; subst q; simp

/-- Absorb a cancelling left transport into a conjugation. -/
theorem eqToHom_comp_conj {X X' Y Y' : C} (p : X = X') (q : Y' = Y) (m : X ⟶ Y') :
    eqToHom p ≫ (eqToHom p.symm ≫ m ≫ eqToHom q) = m ≫ eqToHom q := by
  subst p; subst q; simp

/-- Recover a morphism from its composition with a symmetric transport. -/
theorem comp_eqToHom_symm_comp_self {X Y Y' : C} (q : Y = Y') (t : X ⟶ Y') :
    (t ≫ eqToHom q.symm) ≫ eqToHom q = t := by
  subst q; simp

/-- Transport presieve membership along an equality of arrow images with common target. -/
theorem mem_of_arrowMk_eq {x : C} (P : Presieve x) {Z₁ Z₂ : C}
    {a : Z₁ ⟶ x} {b : Z₂ ⟶ x} (h : Arrow.mk a = Arrow.mk b) (hb : P b) : P a := by
  obtain ⟨h₁, h₂, hab⟩ := (arrowMk_eq_iff _ _).1 h
  subst h₁
  have hab' : a = 𝟙 _ ≫ b ≫ 𝟙 _ := hab
  rw [Category.id_comp, Category.comp_id] at hab'
  rw [hab']
  exact hb

/-- Membership in a transported presieve. -/
theorem presieve_transport_apply {A B Z : C} (h : A = B)
    (P : Presieve A) (t : Z ⟶ B) : (h ▸ P : Presieve B) t ↔ P (t ≫ eqToHom h.symm) := by
  subst h
  have hid : t ≫ eqToHom (Eq.symm (rfl : A = A)) = t := by
    have hp : Eq.symm (rfl : A = A) = rfl := rfl
    rw [hp, eqToHom_refl, Category.comp_id]
  rw [hid]

/-- Equal arrow images with a common target give equal sigma pairs. -/
theorem sigma_pair_eq_of_arrowMk {x : C} {Z₁ Z₂ : C} {a : Z₁ ⟶ x} {b : Z₂ ⟶ x}
    (h : Arrow.mk a = Arrow.mk b) : (⟨Z₁, a⟩ : Σ Y, Y ⟶ x) = ⟨Z₂, b⟩ := by
  obtain ⟨h₁, h₂, hab⟩ := (arrowMk_eq_iff _ _).1 h
  subst h₁
  have hab' : a = 𝟙 _ ≫ b ≫ 𝟙 _ := hab
  rw [Category.id_comp, Category.comp_id] at hab'
  rw [hab']

/-- Solve a double right-transport equation. -/
theorem eq_of_comp_comp_eqToHom {X Y A B : C} (p : Y = A) (q : A = B) {t : X ⟶ Y} {w : X ⟶ B}
    (h : (t ≫ eqToHom p) ≫ eqToHom q = w) : t = (w ≫ eqToHom q.symm) ≫ eqToHom p.symm := by
  subst p; subst q
  simpa using h

/-- Flatten two right transports into one. -/
theorem conj_flat_right₂ {A B Cc D E' F' : C} (p : A = B) (q : Cc = D) (r : D = E')
    (s : E' = F') (m : B ⟶ Cc) :
    ((eqToHom p ≫ m ≫ eqToHom q) ≫ eqToHom r) ≫ eqToHom s =
      eqToHom p ≫ m ≫ eqToHom ((q.trans r).trans s) := by
  subst p; subst q; subst r; subst s
  simp

/-- Assemble a conjugated factor with a transported second factor into canonical form. -/
theorem conj_assemble {Z A B Cc D W : C} (p : Z = A) (q : B = Cc) (r : Cc = D)
    (m₁ : A ⟶ B) (m₂ : D ⟶ W) :
    (eqToHom p ≫ m₁ ≫ eqToHom q) ≫ (eqToHom r ≫ m₂) =
      eqToHom p ≫ m₁ ≫ eqToHom (q.trans r) ≫ m₂ := by
  subst p; subst q; subst r; simp

/-- Associate a left-conjugated first factor into canonical form. -/
theorem conj_assoc₄ {Z A B Cc W : C} (p : Z = A) (q : B = Cc)
    (m₁ : A ⟶ B) (m₂ : Cc ⟶ W) :
    (eqToHom p ≫ m₁ ≫ eqToHom q) ≫ m₂ = eqToHom p ≫ m₁ ≫ eqToHom q ≫ m₂ := by
  subst p; subst q; simp

/-- Distribute a functor over a transport-conjugated composite. This is the matching-robust
replacement for rewriting with `Functor.map_comp` when category-instance spellings diverge. -/
theorem map_conj_distrib {D : Type*} [Category D] (G : C ⥤ D)
    {A A' B B' : C} (p : A = A') (q : B' = B) (m : A' ⟶ B') :
    G.map (eqToHom p ≫ m ≫ eqToHom q) =
      eqToHom (congrArg G.obj p) ≫ G.map m ≫ eqToHom (congrArg G.obj q) := by
  subst p; subst q; simp

/-- Distribute a functor over a left transport. -/
theorem map_eqToHom_comp_distrib {D : Type*} [Category D] (G : C ⥤ D)
    {A A' B : C} (p : A = A') (m : A' ⟶ B) :
    G.map (eqToHom p ≫ m) = eqToHom (congrArg G.obj p) ≫ G.map m := by
  subst p; simp

/-- Distribute a functor over a right transport. -/
theorem map_comp_eqToHom_distrib {D : Type*} [Category D] (G : C ⥤ D)
    {A B B' : C} (m : A ⟶ B) (q : B = B') :
    G.map (m ≫ eqToHom q) = G.map m ≫ eqToHom (congrArg G.obj q) := by
  subst q; simp

/-- Paste two transport conjugations into a five-factor chain. -/
theorem conj_paste₅ {A B Cc D E' F' W : C} (p : A = B) (q : Cc = D) (r : D = E')
    (m : B ⟶ Cc) (n : E' ⟶ F') (s : F' = W) :
    (eqToHom p ≫ m ≫ eqToHom q) ≫ (eqToHom r ≫ n ≫ eqToHom s) =
      eqToHom p ≫ m ≫ eqToHom (q.trans r) ≫ n ≫ eqToHom s := by
  subst p; subst q; subst r; subst s; simp

/-- Flatten one trailing transport into a conjugation. -/
theorem conj_flat_right₁ {A B Cc D E' : C} (p : A = B) (q : Cc = D) (r : D = E')
    (m : B ⟶ Cc) :
    (eqToHom p ≫ m ≫ eqToHom q) ≫ eqToHom r = eqToHom p ≫ m ≫ eqToHom (q.trans r) := by
  subst p; subst q; subst r; simp

/-- Destructure membership in a mapped presieve through the arrow image. -/
theorem map_apply_elim {D : Type*} [Category D] (F : C ⥤ D) {X : C}
    {P : Presieve X} {Z : D} {e : Z ⟶ F.obj X} (h : (P.map F) e) :
    ∃ (W : C) (p : W ⟶ X), P p ∧ Arrow.mk e = Arrow.mk (F.map p) := by
  cases h with
  | of hp => exact ⟨_, _, hp, rfl⟩

/-- Recover a composition identity from its transport-conjugated form. -/
theorem comp_eq_id_of_conj {U V U' V' : C} {b : U ⟶ V} {a : V ⟶ U}
    (p : U' = U) (q : V' = V) (r : V' = V) (s : U' = U)
    (h : (eqToHom p ≫ b ≫ eqToHom q.symm) ≫ (eqToHom r ≫ a ≫ eqToHom s.symm) = 𝟙 U') :
    b ≫ a = 𝟙 U := by
  subst p; subst q
  simpa using h

/-- Push a transport conjugation through a functor and flatten. -/
theorem map_conj_conj_collapse {D : Type*} [Category D] (G : C ⥤ D)
    {A₁ : D} {A₂ A₃ B₃ B₂ : C} {B₁ : D}
    (p₁ : A₁ = G.obj A₂) (p₂ : A₂ = A₃) (q₂ : B₃ = B₂) (q₁ : G.obj B₂ = B₁)
    (m : A₃ ⟶ B₃) (z₁ : A₁ = G.obj A₃) (z₂ : G.obj B₃ = B₁) :
    eqToHom p₁ ≫ G.map (eqToHom p₂ ≫ m ≫ eqToHom q₂) ≫ eqToHom q₁ =
      eqToHom z₁ ≫ G.map m ≫ eqToHom z₂ := by
  subst p₂; subst q₂; subst p₁; subst q₁
  simp

end ArrowCalculus

section Objects

/-- A raw object representative of the colimit category: a stage together with a stage object. -/
structure ObjRep where
  /-- the stage index -/
  idx : S.I
  /-- the stage object -/
  obj : S.stage idx

/-- Two object representatives are identified iff they agree after lowering to some common
stage. -/
def objRel (p q : S.ObjRep) : Prop :=
  ∃ (k : S.I) (a : k ⟶ p.idx) (b : k ⟶ q.idx),
    (S.stageFunctor a).obj p.obj = (S.stageFunctor b).obj q.obj

theorem objRel_refl (p : S.ObjRep) : S.objRel p p :=
  ⟨p.idx, 𝟙 p.idx, 𝟙 p.idx, rfl⟩

theorem objRel_symm {p q : S.ObjRep} (h : S.objRel p q) : S.objRel q p := by
  obtain ⟨k, a, b, h⟩ := h
  exact ⟨k, b, a, h.symm⟩

theorem objRel_trans {p q r : S.ObjRep} (h₁ : S.objRel p q) (h₂ : S.objRel q r) :
    S.objRel p r := by
  obtain ⟨k₁, a₁, b₁, h₁⟩ := h₁
  obtain ⟨k₂, a₂, b₂, h₂⟩ := h₂
  obtain ⟨m, u, v, huv⟩ := S.exists_span b₁ a₂
  refine ⟨m, u ≫ a₁, v ≫ b₂, ?_⟩
  calc (S.stageFunctor (u ≫ a₁)).obj p.obj
      = (S.stageFunctor u).obj ((S.stageFunctor a₁).obj p.obj) :=
        (S.stageFunctor_obj_comp a₁ u p.obj).symm
    _ = (S.stageFunctor u).obj ((S.stageFunctor b₁).obj q.obj) := by rw [h₁]
    _ = (S.stageFunctor (u ≫ b₁)).obj q.obj := S.stageFunctor_obj_comp b₁ u q.obj
    _ = (S.stageFunctor (v ≫ a₂)).obj q.obj := by rw [huv]
    _ = (S.stageFunctor v).obj ((S.stageFunctor a₂).obj q.obj) :=
        (S.stageFunctor_obj_comp a₂ v q.obj).symm
    _ = (S.stageFunctor v).obj ((S.stageFunctor b₂).obj r.obj) := by rw [h₂]
    _ = (S.stageFunctor (v ≫ b₂)).obj r.obj := S.stageFunctor_obj_comp b₂ v r.obj

instance objSetoid : Setoid (S.ObjRep) :=
  ⟨S.objRel, S.objRel_refl, S.objRel_symm, S.objRel_trans⟩

/-- The objects of the explicit colimit category: stage objects modulo common lowering. This is
the source formula `\mathop{\mathrm{Ob}}(\mathcal C) = \mathop{\mathrm{colim}}
\mathop{\mathrm{Ob}}(\mathcal C_i)`. -/
def ColimitCategory : Type max uI uC :=
  _root_.Quotient (S.objSetoid)

/-- The image of a stage object in the colimit category. -/
def ιObj (i : S.I) (X : S.stage i) : S.ColimitCategory :=
  _root_.Quotient.mk _ ⟨i, X⟩

/-- Lowering a stage object along an index arrow does not change its image in the colimit
category. -/
theorem ιObj_lower {i k : S.I} (a : k ⟶ i) (X : S.stage i) :
    S.ιObj k ((S.stageFunctor a).obj X) = S.ιObj i X :=
  _root_.Quotient.sound ⟨k, 𝟙 k, a, S.stageFunctor_obj_id ((S.stageFunctor a).obj X)⟩

/-- Every object of the colimit category is the image of a stage object. -/
theorem ιObj_surjective (x : S.ColimitCategory) :
    ∃ (i : S.I) (X : S.stage i), S.ιObj i X = x := by
  obtain ⟨⟨i, X⟩, h⟩ := _root_.Quotient.exists_rep x
  exact ⟨i, X, h⟩

/-- Two stage objects with the same image in the colimit category agree after lowering to a
common stage. -/
theorem ιObj_exact {i j : S.I} {X : S.stage i} {Y : S.stage j}
    (h : S.ιObj i X = S.ιObj j Y) :
    ∃ (k : S.I) (a : k ⟶ i) (b : k ⟶ j),
      (S.stageFunctor a).obj X = (S.stageFunctor b).obj Y :=
  _root_.Quotient.exact h

end Objects

section Homs

variable {S}

/-- A raw morphism representative between two colimit objects: a stage morphism whose endpoints
represent the given colimit objects. -/
structure HomRep (x y : S.ColimitCategory) where
  /-- the stage index -/
  idx : S.I
  /-- the stage source object -/
  src : S.stage idx
  /-- the stage target object -/
  tgt : S.stage idx
  /-- the stage morphism -/
  hom : src ⟶ tgt
  /-- the source represents `x` -/
  hsrc : S.ιObj idx src = x
  /-- the target represents `y` -/
  htgt : S.ιObj idx tgt = y

/-- Two morphism representatives are identified iff their lowerings to some common stage have
equal `Arrow.mk` images. -/
def homRel {x y : S.ColimitCategory} (r₁ r₂ : HomRep x y) : Prop :=
  ∃ (k : S.I) (a : k ⟶ r₁.idx) (b : k ⟶ r₂.idx),
    Arrow.mk ((S.stageFunctor a).map r₁.hom) = Arrow.mk ((S.stageFunctor b).map r₂.hom)

theorem homRel_refl {x y : S.ColimitCategory} (r : HomRep x y) : homRel r r :=
  ⟨r.idx, 𝟙 r.idx, 𝟙 r.idx, rfl⟩

theorem homRel_symm {x y : S.ColimitCategory} {r₁ r₂ : HomRep x y}
    (h : homRel r₁ r₂) : homRel r₂ r₁ := by
  obtain ⟨k, a, b, h⟩ := h
  exact ⟨k, b, a, h.symm⟩

theorem homRel_trans {x y : S.ColimitCategory} {r₁ r₂ r₃ : HomRep x y}
    (h₁ : homRel r₁ r₂) (h₂ : homRel r₂ r₃) : homRel r₁ r₃ := by
  obtain ⟨k₁, a₁, b₁, h₁⟩ := h₁
  obtain ⟨k₂, a₂, b₂, h₂⟩ := h₂
  obtain ⟨m, u, v, huv⟩ := S.exists_span b₁ a₂
  refine ⟨m, u ≫ a₁, v ≫ b₂, ?_⟩
  calc Arrow.mk ((S.stageFunctor (u ≫ a₁)).map r₁.hom)
      = Arrow.mk ((S.stageFunctor u).map ((S.stageFunctor a₁).map r₁.hom)) :=
        (S.arrowMk_map_map a₁ u r₁.hom).symm
    _ = Arrow.mk ((S.stageFunctor u).map ((S.stageFunctor b₁).map r₂.hom)) := by
        exact congrArg ((S.stageFunctor u).mapArrow.obj) h₁
    _ = Arrow.mk ((S.stageFunctor (u ≫ b₁)).map r₂.hom) := S.arrowMk_map_map b₁ u r₂.hom
    _ = Arrow.mk ((S.stageFunctor (v ≫ a₂)).map r₂.hom) := by rw [huv]
    _ = Arrow.mk ((S.stageFunctor v).map ((S.stageFunctor a₂).map r₂.hom)) :=
        (S.arrowMk_map_map a₂ v r₂.hom).symm
    _ = Arrow.mk ((S.stageFunctor v).map ((S.stageFunctor b₂).map r₃.hom)) := by
        exact congrArg ((S.stageFunctor v).mapArrow.obj) h₂
    _ = Arrow.mk ((S.stageFunctor (v ≫ b₂)).map r₃.hom) := S.arrowMk_map_map b₂ v r₃.hom

instance homSetoid (x y : S.ColimitCategory) : Setoid (HomRep x y) :=
  ⟨homRel, homRel_refl, homRel_symm, homRel_trans⟩

/-- Lower a morphism representative along an index arrow. -/
def HomRep.lower {x y : S.ColimitCategory} (r : HomRep x y) {k : S.I} (a : k ⟶ r.idx) :
    HomRep x y :=
  ⟨k, (S.stageFunctor a).obj r.src, (S.stageFunctor a).obj r.tgt, (S.stageFunctor a).map r.hom,
    (S.ιObj_lower a r.src).trans r.hsrc, (S.ιObj_lower a r.tgt).trans r.htgt⟩

theorem HomRep.lower_rel {x y : S.ColimitCategory} (r : HomRep x y) {k : S.I}
    (a : k ⟶ r.idx) : homRel (r.lower a) r :=
  ⟨k, 𝟙 k, a, S.arrowMk_map_id ((S.stageFunctor a).map r.hom)⟩

end Homs

section Composition

variable {S}

/-- Composition data for two composable morphism representatives: a common stage on which the
target of the first representative and the source of the second become equal. -/
structure CompData {x y z : S.ColimitCategory} (r : HomRep x y) (s : HomRep y z) where
  /-- the common stage -/
  idx : S.I
  /-- the lowering of the first representative's stage -/
  toFst : idx ⟶ r.idx
  /-- the lowering of the second representative's stage -/
  toSnd : idx ⟶ s.idx
  /-- the gluing identification -/
  glue : (S.stageFunctor toFst).obj r.tgt = (S.stageFunctor toSnd).obj s.src

/-- Some composition data always exists, because the middle endpoints represent the same colimit
object. -/
noncomputable def CompData.some {x y z : S.ColimitCategory} (r : HomRep x y)
    (s : HomRep y z) : CompData r s := by
  have h : ∃ (k : S.I) (a : k ⟶ r.idx) (b : k ⟶ s.idx),
      (S.stageFunctor a).obj r.tgt = (S.stageFunctor b).obj s.src :=
    _root_.Quotient.exact (r.htgt.trans s.hsrc.symm)
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec⟩

/-- The composite representative attached to a choice of composition data. -/
def CompData.comp {x y z : S.ColimitCategory} {r : HomRep x y} {s : HomRep y z}
    (d : CompData r s) : HomRep x z :=
  ⟨d.idx, (S.stageFunctor d.toFst).obj r.src, (S.stageFunctor d.toSnd).obj s.tgt,
    (S.stageFunctor d.toFst).map r.hom ≫ eqToHom d.glue ≫ (S.stageFunctor d.toSnd).map s.hom,
    (S.ιObj_lower d.toFst r.src).trans r.hsrc,
    (S.ιObj_lower d.toSnd s.tgt).trans s.htgt⟩

/-- Lowering the composite of a composition datum produces the evident three-factor composite.
This is the single place where the transport bookkeeping for composites is carried out. -/
theorem CompData.arrowMk_lower_comp {x y z : S.ColimitCategory} {r : HomRep x y}
    {s : HomRep y z} (d : CompData r s) {n : S.I} (w : n ⟶ d.idx) :
    Arrow.mk ((S.stageFunctor w).map d.comp.hom) =
      Arrow.mk ((S.stageFunctor (w ≫ d.toFst)).map r.hom ≫
        eqToHom ((S.stageFunctor_obj_comp d.toFst w r.tgt).symm.trans
          ((congrArg (S.stageFunctor w).obj d.glue).trans
            (S.stageFunctor_obj_comp d.toSnd w s.src))) ≫
        (S.stageFunctor (w ≫ d.toSnd)).map s.hom) := by
  change Arrow.mk ((S.stageFunctor w).map
      ((S.stageFunctor d.toFst).map r.hom ≫ eqToHom d.glue ≫
        (S.stageFunctor d.toSnd).map s.hom)) = _
  rw [arrowMk_eq_iff]
  refine ⟨S.stageFunctor_obj_comp d.toFst w r.src,
    (S.stageFunctor_obj_comp d.toSnd w s.tgt), ?_⟩
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, eqToHom_map,
    S.stageFunctor_map_map d.toFst w r.hom, S.stageFunctor_map_map d.toSnd w s.hom]
  simp [Category.assoc, eqToHom_trans_assoc]

/-- The class of the composite representative does not depend on the chosen composition data. -/
theorem CompData.comp_rel {x y z : S.ColimitCategory} {r : HomRep x y} {s : HomRep y z}
    (d d' : CompData r s) : homRel d.comp d'.comp := by
  obtain ⟨m, u, v, huv⟩ := S.exists_span d.toFst d'.toFst
  obtain ⟨n, e, he⟩ :
      ∃ (n : S.I) (e : n ⟶ m), e ≫ (u ≫ d.toSnd) = e ≫ (v ≫ d'.toSnd) := by
    refine ⟨IsCofiltered.eq (u ≫ d.toSnd) (v ≫ d'.toSnd),
      IsCofiltered.eqHom _ _, ?_⟩
    exact IsCofiltered.eq_condition _ _
  refine ⟨n, (e ≫ u), (e ≫ v), ?_⟩
  refine (d.arrowMk_lower_comp (e ≫ u)).trans
    (Eq.trans ?_ (d'.arrowMk_lower_comp (e ≫ v)).symm)
  have h₁ : (e ≫ u) ≫ d.toFst = (e ≫ v) ≫ d'.toFst := by
    simp only [Category.assoc]; rw [huv]
  have h₂ : (e ≫ u) ≫ d.toSnd = (e ≫ v) ≫ d'.toSnd := by
    simpa [Category.assoc] using he
  exact arrowMk_glue_comp_congr
    (congrArg (fun (c : n ⟶ r.idx) => Arrow.mk ((S.stageFunctor c).map r.hom)) h₁)
    (congrArg (fun (c : n ⟶ s.idx) => Arrow.mk ((S.stageFunctor c).map s.hom)) h₂)
    _ _

/-- Replacing the left representative by a related one does not change the class of the
composite. -/
theorem CompData.comp_rel_left {x y z : S.ColimitCategory} {r₁ r₂ : HomRep x y}
    {s : HomRep y z} (h : homRel r₁ r₂) (d₂ : CompData r₂ s) :
    ∃ (d₁ : CompData r₁ s), homRel d₁.comp d₂.comp := by
  obtain ⟨l, c₁, c₂, harr⟩ := h
  obtain ⟨-, htgt, -⟩ := (arrowMk_eq_iff _ _).1 harr
  obtain ⟨m, u, v, huv⟩ := S.exists_span c₂ d₂.toFst
  have glue₁ : (S.stageFunctor (u ≫ c₁)).obj r₁.tgt =
      (S.stageFunctor (v ≫ d₂.toSnd)).obj s.src := by
    calc (S.stageFunctor (u ≫ c₁)).obj r₁.tgt
        = (S.stageFunctor u).obj ((S.stageFunctor c₁).obj r₁.tgt) :=
          (S.stageFunctor_obj_comp c₁ u r₁.tgt).symm
      _ = (S.stageFunctor u).obj ((S.stageFunctor c₂).obj r₂.tgt) := by rw [htgt]
      _ = (S.stageFunctor (u ≫ c₂)).obj r₂.tgt := S.stageFunctor_obj_comp c₂ u r₂.tgt
      _ = (S.stageFunctor (v ≫ d₂.toFst)).obj r₂.tgt := by rw [huv]
      _ = (S.stageFunctor v).obj ((S.stageFunctor d₂.toFst).obj r₂.tgt) :=
          (S.stageFunctor_obj_comp d₂.toFst v r₂.tgt).symm
      _ = (S.stageFunctor v).obj ((S.stageFunctor d₂.toSnd).obj s.src) := by rw [d₂.glue]
      _ = (S.stageFunctor (v ≫ d₂.toSnd)).obj s.src :=
          S.stageFunctor_obj_comp d₂.toSnd v s.src
  -- The lowered first factors have equal arrow images.
  have hfst : Arrow.mk ((S.stageFunctor (𝟙 m ≫ (u ≫ c₁))).map r₁.hom) =
      Arrow.mk ((S.stageFunctor (v ≫ d₂.toFst)).map r₂.hom) :=
    calc Arrow.mk ((S.stageFunctor (𝟙 m ≫ (u ≫ c₁))).map r₁.hom)
        = Arrow.mk ((S.stageFunctor (u ≫ c₁)).map r₁.hom) :=
          congrArg (fun (c : m ⟶ r₁.idx) => Arrow.mk ((S.stageFunctor c).map r₁.hom))
            (Category.id_comp (u ≫ c₁))
      _ = Arrow.mk ((S.stageFunctor u).map ((S.stageFunctor c₁).map r₁.hom)) :=
          (S.arrowMk_map_map c₁ u r₁.hom).symm
      _ = Arrow.mk ((S.stageFunctor u).map ((S.stageFunctor c₂).map r₂.hom)) :=
          congrArg ((S.stageFunctor u).mapArrow.obj) harr
      _ = Arrow.mk ((S.stageFunctor (u ≫ c₂)).map r₂.hom) := S.arrowMk_map_map c₂ u r₂.hom
      _ = Arrow.mk ((S.stageFunctor (v ≫ d₂.toFst)).map r₂.hom) :=
          congrArg (fun (c : m ⟶ r₂.idx) => Arrow.mk ((S.stageFunctor c).map r₂.hom)) huv
  -- The lowered second factors agree on the nose after normalizing the identity.
  have hsnd : Arrow.mk ((S.stageFunctor (𝟙 m ≫ (v ≫ d₂.toSnd))).map s.hom) =
      Arrow.mk ((S.stageFunctor (v ≫ d₂.toSnd)).map s.hom) :=
    congrArg (fun (c : m ⟶ s.idx) => Arrow.mk ((S.stageFunctor c).map s.hom))
      (Category.id_comp (v ≫ d₂.toSnd))
  refine ⟨⟨m, u ≫ c₁, v ≫ d₂.toSnd, glue₁⟩, ?_⟩
  refine ⟨m, 𝟙 m, v, ?_⟩
  exact ((⟨m, u ≫ c₁, v ≫ d₂.toSnd, glue₁⟩ :
      CompData r₁ s).arrowMk_lower_comp (𝟙 m)).trans
    ((arrowMk_glue_comp_congr hfst hsnd _ _).trans (d₂.arrowMk_lower_comp v).symm)

/-- Replacing the right representative by a related one does not change the class of the
composite. -/
theorem CompData.comp_rel_right {x y z : S.ColimitCategory} {r : HomRep x y}
    {s₁ s₂ : HomRep y z} (h : homRel s₁ s₂) (d₂ : CompData r s₂) :
    ∃ (d₁ : CompData r s₁), homRel d₁.comp d₂.comp := by
  obtain ⟨l, c₁, c₂, harr⟩ := h
  obtain ⟨hsrc, -, -⟩ := (arrowMk_eq_iff _ _).1 harr
  obtain ⟨m, u, v, huv⟩ := S.exists_span c₂ d₂.toSnd
  have glue₁ : (S.stageFunctor (v ≫ d₂.toFst)).obj r.tgt =
      (S.stageFunctor (u ≫ c₁)).obj s₁.src := by
    calc (S.stageFunctor (v ≫ d₂.toFst)).obj r.tgt
        = (S.stageFunctor v).obj ((S.stageFunctor d₂.toFst).obj r.tgt) :=
          (S.stageFunctor_obj_comp d₂.toFst v r.tgt).symm
      _ = (S.stageFunctor v).obj ((S.stageFunctor d₂.toSnd).obj s₂.src) := by rw [d₂.glue]
      _ = (S.stageFunctor (v ≫ d₂.toSnd)).obj s₂.src :=
          S.stageFunctor_obj_comp d₂.toSnd v s₂.src
      _ = (S.stageFunctor (u ≫ c₂)).obj s₂.src := by rw [huv]
      _ = (S.stageFunctor u).obj ((S.stageFunctor c₂).obj s₂.src) :=
          (S.stageFunctor_obj_comp c₂ u s₂.src).symm
      _ = (S.stageFunctor u).obj ((S.stageFunctor c₁).obj s₁.src) := by rw [hsrc]
      _ = (S.stageFunctor (u ≫ c₁)).obj s₁.src := S.stageFunctor_obj_comp c₁ u s₁.src
  -- The lowered first factors agree on the nose after normalizing the identity.
  have hfst : Arrow.mk ((S.stageFunctor (𝟙 m ≫ (v ≫ d₂.toFst))).map r.hom) =
      Arrow.mk ((S.stageFunctor (v ≫ d₂.toFst)).map r.hom) :=
    congrArg (fun (c : m ⟶ r.idx) => Arrow.mk ((S.stageFunctor c).map r.hom))
      (Category.id_comp (v ≫ d₂.toFst))
  -- The lowered second factors have equal arrow images.
  have hsnd : Arrow.mk ((S.stageFunctor (𝟙 m ≫ (u ≫ c₁))).map s₁.hom) =
      Arrow.mk ((S.stageFunctor (v ≫ d₂.toSnd)).map s₂.hom) :=
    calc Arrow.mk ((S.stageFunctor (𝟙 m ≫ (u ≫ c₁))).map s₁.hom)
        = Arrow.mk ((S.stageFunctor (u ≫ c₁)).map s₁.hom) :=
          congrArg (fun (c : m ⟶ s₁.idx) => Arrow.mk ((S.stageFunctor c).map s₁.hom))
            (Category.id_comp (u ≫ c₁))
      _ = Arrow.mk ((S.stageFunctor u).map ((S.stageFunctor c₁).map s₁.hom)) :=
          (S.arrowMk_map_map c₁ u s₁.hom).symm
      _ = Arrow.mk ((S.stageFunctor u).map ((S.stageFunctor c₂).map s₂.hom)) :=
          congrArg ((S.stageFunctor u).mapArrow.obj) harr
      _ = Arrow.mk ((S.stageFunctor (u ≫ c₂)).map s₂.hom) := S.arrowMk_map_map c₂ u s₂.hom
      _ = Arrow.mk ((S.stageFunctor (v ≫ d₂.toSnd)).map s₂.hom) :=
          congrArg (fun (c : m ⟶ s₂.idx) => Arrow.mk ((S.stageFunctor c).map s₂.hom)) huv
  refine ⟨⟨m, v ≫ d₂.toFst, u ≫ c₁, glue₁⟩, ?_⟩
  refine ⟨m, 𝟙 m, v, ?_⟩
  exact ((⟨m, v ≫ d₂.toFst, u ≫ c₁, glue₁⟩ :
      CompData r s₁).arrowMk_lower_comp (𝟙 m)).trans
    ((arrowMk_glue_comp_congr hfst hsnd _ _).trans (d₂.arrowMk_lower_comp v).symm)

/-- Composition of morphism representatives is well defined on common-lowering classes and does
not depend on the composition data. -/
theorem CompData.comp_sound {x y z : S.ColimitCategory} {r₁ r₂ : HomRep x y}
    {s₁ s₂ : HomRep y z} (hr : homRel r₁ r₂) (hs : homRel s₁ s₂)
    (d₁ : CompData r₁ s₁) (d₂ : CompData r₂ s₂) :
    homRel d₁.comp d₂.comp := by
  obtain ⟨dmid, hmid⟩ := CompData.comp_rel_right hs d₂
  obtain ⟨d₁', h₁'⟩ := CompData.comp_rel_left hr dmid
  exact homRel_trans (CompData.comp_rel d₁ d₁') (homRel_trans h₁' hmid)

/-- Associativity of representative composition: the two nested composites agree as
common-lowering classes. -/
theorem CompData.assoc_rel {w x y z : S.ColimitCategory} (r : HomRep w x) (s : HomRep x y)
    (t : HomRep y z) :
    homRel (CompData.some (CompData.some r s).comp t).comp
      (CompData.some r (CompData.some s t).comp).comp := by
  set d₁₂ := CompData.some r s
  set d₂₃ := CompData.some s t
  obtain ⟨m, u, v, huv⟩ := S.exists_span d₁₂.toSnd d₂₃.toFst
  have glueL : (S.stageFunctor u).obj ((S.stageFunctor d₁₂.toSnd).obj s.tgt) =
      (S.stageFunctor (v ≫ d₂₃.toSnd)).obj t.src := by
    calc (S.stageFunctor u).obj ((S.stageFunctor d₁₂.toSnd).obj s.tgt)
        = (S.stageFunctor (u ≫ d₁₂.toSnd)).obj s.tgt :=
          S.stageFunctor_obj_comp d₁₂.toSnd u s.tgt
      _ = (S.stageFunctor (v ≫ d₂₃.toFst)).obj s.tgt := by rw [huv]
      _ = (S.stageFunctor v).obj ((S.stageFunctor d₂₃.toFst).obj s.tgt) :=
          (S.stageFunctor_obj_comp d₂₃.toFst v s.tgt).symm
      _ = (S.stageFunctor v).obj ((S.stageFunctor d₂₃.toSnd).obj t.src) := by rw [d₂₃.glue]
      _ = (S.stageFunctor (v ≫ d₂₃.toSnd)).obj t.src :=
          S.stageFunctor_obj_comp d₂₃.toSnd v t.src
  have glueR : (S.stageFunctor (u ≫ d₁₂.toFst)).obj r.tgt =
      (S.stageFunctor v).obj ((S.stageFunctor d₂₃.toFst).obj s.src) := by
    calc (S.stageFunctor (u ≫ d₁₂.toFst)).obj r.tgt
        = (S.stageFunctor u).obj ((S.stageFunctor d₁₂.toFst).obj r.tgt) :=
          (S.stageFunctor_obj_comp d₁₂.toFst u r.tgt).symm
      _ = (S.stageFunctor u).obj ((S.stageFunctor d₁₂.toSnd).obj s.src) := by rw [d₁₂.glue]
      _ = (S.stageFunctor (u ≫ d₁₂.toSnd)).obj s.src :=
          S.stageFunctor_obj_comp d₁₂.toSnd u s.src
      _ = (S.stageFunctor (v ≫ d₂₃.toFst)).obj s.src := by rw [huv]
      _ = (S.stageFunctor v).obj ((S.stageFunctor d₂₃.toFst).obj s.src) :=
          (S.stageFunctor_obj_comp d₂₃.toFst v s.src).symm
  refine homRel_trans
    (CompData.comp_rel (CompData.some d₁₂.comp t) ⟨m, u, v ≫ d₂₃.toSnd, glueL⟩)
    (homRel_trans ?_
      (homRel_symm
        (CompData.comp_rel (CompData.some r d₂₃.comp) ⟨m, u ≫ d₁₂.toFst, v, glueR⟩)))
  -- The lowered factors of the two explicit composites agree arrow-wise.
  have hX₁ : Arrow.mk ((S.stageFunctor u).map ((S.stageFunctor d₁₂.toFst).map r.hom)) =
      Arrow.mk ((S.stageFunctor (u ≫ d₁₂.toFst)).map r.hom) :=
    S.arrowMk_map_map d₁₂.toFst u r.hom
  have hX₂ : Arrow.mk ((S.stageFunctor u).map ((S.stageFunctor d₁₂.toSnd).map s.hom)) =
      Arrow.mk ((S.stageFunctor v).map ((S.stageFunctor d₂₃.toFst).map s.hom)) :=
    (S.arrowMk_map_map d₁₂.toSnd u s.hom).trans
      ((congrArg (fun (c : m ⟶ s.idx) => Arrow.mk ((S.stageFunctor c).map s.hom)) huv).trans
        (S.arrowMk_map_map d₂₃.toFst v s.hom).symm)
  have hX₃ : Arrow.mk ((S.stageFunctor (v ≫ d₂₃.toSnd)).map t.hom) =
      Arrow.mk ((S.stageFunctor v).map ((S.stageFunctor d₂₃.toSnd).map t.hom)) :=
    (S.arrowMk_map_map d₂₃.toSnd v t.hom).symm
  refine ⟨m, 𝟙 m, 𝟙 m, ?_⟩
  refine (S.arrowMk_map_id _).trans (Eq.trans ?_ (S.arrowMk_map_id _).symm)
  change Arrow.mk ((S.stageFunctor u).map d₁₂.comp.hom ≫ eqToHom glueL ≫
      (S.stageFunctor (v ≫ d₂₃.toSnd)).map t.hom) =
    Arrow.mk ((S.stageFunctor (u ≫ d₁₂.toFst)).map r.hom ≫ eqToHom glueR ≫
      (S.stageFunctor v).map d₂₃.comp.hom)
  have hexpL : (S.stageFunctor u).map d₁₂.comp.hom =
      (S.stageFunctor u).map ((S.stageFunctor d₁₂.toFst).map r.hom) ≫
        eqToHom (congrArg (S.stageFunctor u).obj d₁₂.glue) ≫
        (S.stageFunctor u).map ((S.stageFunctor d₁₂.toSnd).map s.hom) := by
    change (S.stageFunctor u).map ((S.stageFunctor d₁₂.toFst).map r.hom ≫ eqToHom d₁₂.glue ≫
      (S.stageFunctor d₁₂.toSnd).map s.hom) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, eqToHom_map]
  have hexpR : (S.stageFunctor v).map d₂₃.comp.hom =
      (S.stageFunctor v).map ((S.stageFunctor d₂₃.toFst).map s.hom) ≫
        eqToHom (congrArg (S.stageFunctor v).obj d₂₃.glue) ≫
        (S.stageFunctor v).map ((S.stageFunctor d₂₃.toSnd).map t.hom) := by
    change (S.stageFunctor v).map ((S.stageFunctor d₂₃.toFst).map s.hom ≫ eqToHom d₂₃.glue ≫
      (S.stageFunctor d₂₃.toSnd).map t.hom) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, eqToHom_map]
  calc Arrow.mk ((S.stageFunctor u).map d₁₂.comp.hom ≫ eqToHom glueL ≫
          (S.stageFunctor (v ≫ d₂₃.toSnd)).map t.hom)
      = Arrow.mk (((S.stageFunctor u).map ((S.stageFunctor d₁₂.toFst).map r.hom) ≫
            eqToHom (congrArg (S.stageFunctor u).obj d₁₂.glue) ≫
            (S.stageFunctor u).map ((S.stageFunctor d₁₂.toSnd).map s.hom)) ≫
          eqToHom glueL ≫ (S.stageFunctor (v ≫ d₂₃.toSnd)).map t.hom) :=
        congrArg (fun k => Arrow.mk (k ≫ eqToHom glueL ≫
          (S.stageFunctor (v ≫ d₂₃.toSnd)).map t.hom)) hexpL
    _ = Arrow.mk ((S.stageFunctor u).map ((S.stageFunctor d₁₂.toFst).map r.hom) ≫
          eqToHom (congrArg (S.stageFunctor u).obj d₁₂.glue) ≫
          (S.stageFunctor u).map ((S.stageFunctor d₁₂.toSnd).map s.hom) ≫
          eqToHom glueL ≫ (S.stageFunctor (v ≫ d₂₃.toSnd)).map t.hom) := by
        simp only [Category.assoc]
    _ = Arrow.mk ((S.stageFunctor (u ≫ d₁₂.toFst)).map r.hom ≫ eqToHom glueR ≫
          (S.stageFunctor v).map ((S.stageFunctor d₂₃.toFst).map s.hom) ≫
          eqToHom (congrArg (S.stageFunctor v).obj d₂₃.glue) ≫
          (S.stageFunctor v).map ((S.stageFunctor d₂₃.toSnd).map t.hom)) :=
        arrowMk_glue_comp_congr hX₁ (arrowMk_glue_comp_congr hX₂ hX₃ _ _) _ _
    _ = Arrow.mk ((S.stageFunctor (u ≫ d₁₂.toFst)).map r.hom ≫ eqToHom glueR ≫
          (S.stageFunctor v).map d₂₃.comp.hom) :=
        (congrArg (fun k => Arrow.mk ((S.stageFunctor (u ≫ d₁₂.toFst)).map r.hom ≫
          eqToHom glueR ≫ k)) hexpR).symm

end Composition

section CategoryInstance

variable {S}

/-- The canonical identity representative of a colimit object, through a choice of stage
representative. -/
noncomputable def idRep (x : S.ColimitCategory) : HomRep x x :=
  ⟨(_root_.Quotient.exists_rep x).choose.idx, (_root_.Quotient.exists_rep x).choose.obj,
    (_root_.Quotient.exists_rep x).choose.obj, 𝟙 (_root_.Quotient.exists_rep x).choose.obj,
    (_root_.Quotient.exists_rep x).choose_spec, (_root_.Quotient.exists_rep x).choose_spec⟩

/-- Any two identity-shaped representatives of the same colimit object are related. -/
theorem homRel_id_id {x : S.ColimitCategory} {p q : S.ObjRep}
    (hp : S.ιObj p.idx p.obj = x) (hq : S.ιObj q.idx q.obj = x) :
    homRel (⟨p.idx, p.obj, p.obj, 𝟙 p.obj, hp, hp⟩ : HomRep x x)
      ⟨q.idx, q.obj, q.obj, 𝟙 q.obj, hq, hq⟩ := by
  obtain ⟨k, a, b, h⟩ := S.ιObj_exact (hp.trans hq.symm)
  refine ⟨k, a, b, ?_⟩
  calc Arrow.mk ((S.stageFunctor a).map (𝟙 p.obj))
      = Arrow.mk (𝟙 ((S.stageFunctor a).obj p.obj)) := by rw [CategoryTheory.Functor.map_id]
    _ = Arrow.mk (𝟙 ((S.stageFunctor b).obj q.obj)) :=
        congrArg (fun Z => Arrow.mk (𝟙 Z)) h
    _ = Arrow.mk ((S.stageFunctor b).map (𝟙 q.obj)) := by rw [CategoryTheory.Functor.map_id]

/-- Composing with an identity-shaped representative on the right does not change the class. -/
theorem CompData.comp_id_rel {x y : S.ColimitCategory} {r : HomRep x y} {q : S.ObjRep}
    {hq : S.ιObj q.idx q.obj = y}
    (d : CompData r (⟨q.idx, q.obj, q.obj, 𝟙 q.obj, hq, hq⟩ : HomRep y y)) :
    homRel d.comp r := by
  refine ⟨d.idx, 𝟙 d.idx, d.toFst, ?_⟩
  refine (S.arrowMk_map_id d.comp.hom).trans ?_
  change Arrow.mk ((S.stageFunctor d.toFst).map r.hom ≫ eqToHom d.glue ≫
    (S.stageFunctor d.toSnd).map (𝟙 q.obj)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact arrowMk_comp_eqToHom _ d.glue

/-- Composing with an identity-shaped representative on the left does not change the class. -/
theorem CompData.id_comp_rel {x y : S.ColimitCategory} {r : HomRep x y} {p : S.ObjRep}
    {hp : S.ιObj p.idx p.obj = x}
    (d : CompData (⟨p.idx, p.obj, p.obj, 𝟙 p.obj, hp, hp⟩ : HomRep x x) r) :
    homRel d.comp r := by
  refine ⟨d.idx, 𝟙 d.idx, d.toSnd, ?_⟩
  refine (S.arrowMk_map_id d.comp.hom).trans ?_
  change Arrow.mk ((S.stageFunctor d.toFst).map (𝟙 p.obj) ≫ eqToHom d.glue ≫
    (S.stageFunctor d.toSnd).map r.hom) = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact arrowMk_eqToHom_comp d.glue _

variable (S)

/-- The category structure of the explicit colimit category. Identities and compositions are
chosen through stage representatives; the category laws hold because all choices merge at a
common lower stage. -/
noncomputable instance instCategoryColimitCategory :
    Category.{max uI uC vC} (S.ColimitCategory) where
  Hom x y := _root_.Quotient (homSetoid x y)
  id x := _root_.Quotient.mk _ (idRep x)
  comp {x y z} f g :=
    _root_.Quotient.lift₂
      (fun (r : HomRep x y) (s : HomRep y z) =>
        (_root_.Quotient.mk _ (CompData.some r s).comp : _root_.Quotient (homSetoid x z)))
      (fun r₁ s₁ r₂ s₂ hr hs =>
        _root_.Quotient.sound
          (CompData.comp_sound hr hs (CompData.some r₁ s₁) (CompData.some r₂ s₂)))
      f g
  id_comp {x y} f := by
    induction f using _root_.Quotient.inductionOn with
    | _ r => exact _root_.Quotient.sound (CompData.id_comp_rel _)
  comp_id {x y} f := by
    induction f using _root_.Quotient.inductionOn with
    | _ r => exact _root_.Quotient.sound (CompData.comp_id_rel _)
  assoc {w x y z} f g h := by
    induction f using _root_.Quotient.inductionOn with | _ r =>
    induction g using _root_.Quotient.inductionOn with | _ s =>
    induction h using _root_.Quotient.inductionOn with | _ t =>
    exact _root_.Quotient.sound (CompData.assoc_rel r s t)

end CategoryInstance

section Interface

variable {S}

/-- Equal-endpoint arrow equality: two parallel morphisms with equal `Arrow.mk` images are
equal. -/
theorem eq_of_arrowMk_eq {C : Type*} [Category C] {X Y : C} {u v : X ⟶ Y}
    (h : Arrow.mk u = Arrow.mk v) : u = v := by
  obtain ⟨p, q, hp⟩ := (arrowMk_eq_iff _ _).1 h
  rw [show p = rfl from rfl, show q = rfl from rfl] at hp
  simpa using hp

/-- The morphisms of the explicit colimit category between two given objects are exactly the
common-lowering classes of representatives. -/
theorem hom_mk_eq_iff {x y : S.ColimitCategory} (r₁ r₂ : HomRep x y) :
    (_root_.Quotient.mk _ r₁ : x ⟶ y) = _root_.Quotient.mk _ r₂ ↔ homRel r₁ r₂ :=
  ⟨fun h => _root_.Quotient.exact h, fun h => _root_.Quotient.sound h⟩

/-- Computation rule for composition in the explicit colimit category: the composite of two
representative classes is the explicit composite attached to any choice of composition data. -/
theorem mk_comp_mk {x y z : S.ColimitCategory} (r : HomRep x y) (s : HomRep y z)
    (d : CompData r s) :
    (_root_.Quotient.mk _ r ≫ _root_.Quotient.mk _ s : x ⟶ z) =
      _root_.Quotient.mk _ d.comp :=
  _root_.Quotient.sound (CompData.comp_rel (CompData.some r s) d)

/-- Computation rule for identities in the explicit colimit category. -/
theorem id_eq_mk {x : S.ColimitCategory} (p : S.ObjRep) (hp : S.ιObj p.idx p.obj = x) :
    (𝟙 x : x ⟶ x) =
      _root_.Quotient.mk _ (⟨p.idx, p.obj, p.obj, 𝟙 p.obj, hp, hp⟩ : HomRep x x) :=
  _root_.Quotient.sound (homRel_id_id _ hp)

/-- Computation rule for transports in the explicit colimit category. -/
theorem eqToHom_eq_mk {x y : S.ColimitCategory} (h : x = y) (p : S.ObjRep)
    (hp : S.ιObj p.idx p.obj = x) :
    eqToHom h =
      (_root_.Quotient.mk _ (⟨p.idx, p.obj, p.obj, 𝟙 p.obj, hp, hp.trans h⟩ : HomRep x y) :
        x ⟶ y) := by
  subst h
  rw [eqToHom_refl]
  exact id_eq_mk p hp

end Interface

section CoconeFunctor

/-- The cocone functor `u_i : \mathcal C_i \to \mathop{\mathrm{colim}} \mathcal C_i` of the
explicit colimit category. -/
noncomputable def stageCoconeFunctor (i : S.I) : S.stage i ⥤ S.ColimitCategory where
  obj X := S.ιObj i X
  map f := _root_.Quotient.mk _ ⟨i, _, _, f, rfl, rfl⟩
  map_id X := (id_eq_mk ⟨i, X⟩ rfl).symm
  map_comp := by
    intro X Y Z f g
    rw [mk_comp_mk _ _ ⟨i, 𝟙 i, 𝟙 i, rfl⟩]
    refine _root_.Quotient.sound ⟨i, 𝟙 i, 𝟙 i, ?_⟩
    change Arrow.mk ((S.stageFunctor (𝟙 i)).map (f ≫ g)) =
      Arrow.mk ((S.stageFunctor (𝟙 i)).map ((S.stageFunctor (𝟙 i)).map f ≫ eqToHom rfl ≫
        (S.stageFunctor (𝟙 i)).map g))
    refine (S.arrowMk_map_id (f ≫ g)).trans (Eq.trans ?_ (S.arrowMk_map_id _).symm)
    rw [arrowMk_eq_iff]
    refine ⟨(S.stageFunctor_obj_id X).symm, (S.stageFunctor_obj_id Z).symm, ?_⟩
    rw [S.stageFunctor_map_id f, S.stageFunctor_map_id g]
    simp [Category.assoc]

/-- The cocone functors are strictly compatible with the transition functors: this is the
equality `u_j ∘ u_a = u_i` of the source text. -/
theorem stageCoconeFunctor_comp_eq {i j : S.I} (a : j ⟶ i) :
    S.stageFunctor a ⋙ S.stageCoconeFunctor j = S.stageCoconeFunctor i := by
  have glue₂ : ∀ X : S.stage i,
      (S.stageFunctor (𝟙 j)).obj ((S.stageFunctor a).obj X) =
        (S.stageFunctor a).obj ((S.stageFunctor (𝟙 i)).obj X) := fun X =>
    (S.stageFunctor_obj_id _).trans
      (congrArg (S.stageFunctor a).obj (S.stageFunctor_obj_id X).symm)
  refine CategoryTheory.Functor.ext (fun X => S.ιObj_lower a X) ?_
  intro X Y f
  -- Both sides are classes of stage morphisms; rewrite the transports as identity-shaped
  -- classes and compose explicitly.
  change (_root_.Quotient.mk _ ⟨j, (S.stageFunctor a).obj X, (S.stageFunctor a).obj Y,
      (S.stageFunctor a).map f, rfl, rfl⟩ :
        S.ιObj j ((S.stageFunctor a).obj X) ⟶ S.ιObj j ((S.stageFunctor a).obj Y)) =
    eqToHom (S.ιObj_lower a X) ≫ (_root_.Quotient.mk _ ⟨i, X, Y, f, rfl, rfl⟩ :
      S.ιObj i X ⟶ S.ιObj i Y) ≫ eqToHom (S.ιObj_lower a Y).symm
  rw [eqToHom_eq_mk (S.ιObj_lower a X) ⟨j, (S.stageFunctor a).obj X⟩ rfl,
    eqToHom_eq_mk (S.ιObj_lower a Y).symm ⟨i, Y⟩ rfl]
  rw [mk_comp_mk (⟨i, X, Y, f, rfl, rfl⟩ : HomRep (S.ιObj i X) (S.ιObj i Y)) _
      ⟨i, 𝟙 i, 𝟙 i, rfl⟩,
    mk_comp_mk _ _ ⟨j, 𝟙 j, a, glue₂ X⟩]
  refine _root_.Quotient.sound ⟨j, 𝟙 j, 𝟙 j, ?_⟩
  refine (S.arrowMk_map_id _).trans (Eq.trans ?_ (S.arrowMk_map_id _).symm)
  change Arrow.mk ((S.stageFunctor a).map f) =
    Arrow.mk ((S.stageFunctor (𝟙 j)).map (𝟙 ((S.stageFunctor a).obj X)) ≫
      eqToHom (glue₂ X) ≫
      (S.stageFunctor a).map ((S.stageFunctor (𝟙 i)).map f ≫ eqToHom rfl ≫
        (S.stageFunctor (𝟙 i)).map (𝟙 Y)))
  rw [arrowMk_eq_iff]
  refine ⟨(S.stageFunctor_obj_id _).symm,
    congrArg (S.stageFunctor a).obj (S.stageFunctor_obj_id Y).symm, ?_⟩
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.map_comp,
    S.stageFunctor_map_id f, CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_map,
    CategoryTheory.Functor.map_comp, eqToHom_map]
  simp [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end CoconeFunctor

section Descent

variable {S}

/-- Arrow descent (source remark "every finite diagram comes from some stage", morphism case):
every morphism between images of stage objects is, after lowering both stages to a common one,
the image of a single stage morphism between the lowered objects. -/
theorem exists_hom_rep {i j : S.I} {X : S.stage i} {Y : S.stage j}
    (f : S.ιObj i X ⟶ S.ιObj j Y) :
    ∃ (k : S.I) (a : k ⟶ i) (b : k ⟶ j)
      (g : (S.stageFunctor a).obj X ⟶ (S.stageFunctor b).obj Y),
      f = _root_.Quotient.mk _ ⟨k, (S.stageFunctor a).obj X, (S.stageFunctor b).obj Y, g,
        S.ιObj_lower a X, S.ιObj_lower b Y⟩ := by
  induction f using _root_.Quotient.inductionOn with | _ r =>
  obtain ⟨k₁, c₁, a₁, hs⟩ := S.ιObj_exact r.hsrc
  obtain ⟨k₂, c₂, b₂, ht⟩ := S.ιObj_exact r.htgt
  obtain ⟨m, u, v, huv⟩ := S.exists_span c₁ c₂
  have hsX : (S.stageFunctor (u ≫ a₁)).obj X = (S.stageFunctor (u ≫ c₁)).obj r.src := by
    calc (S.stageFunctor (u ≫ a₁)).obj X
        = (S.stageFunctor u).obj ((S.stageFunctor a₁).obj X) :=
          (S.stageFunctor_obj_comp a₁ u X).symm
      _ = (S.stageFunctor u).obj ((S.stageFunctor c₁).obj r.src) := by rw [hs]
      _ = (S.stageFunctor (u ≫ c₁)).obj r.src := S.stageFunctor_obj_comp c₁ u r.src
  have htY : (S.stageFunctor (u ≫ c₁)).obj r.tgt = (S.stageFunctor (v ≫ b₂)).obj Y := by
    calc (S.stageFunctor (u ≫ c₁)).obj r.tgt
        = (S.stageFunctor (v ≫ c₂)).obj r.tgt := by rw [huv]
      _ = (S.stageFunctor v).obj ((S.stageFunctor c₂).obj r.tgt) :=
          (S.stageFunctor_obj_comp c₂ v r.tgt).symm
      _ = (S.stageFunctor v).obj ((S.stageFunctor b₂).obj Y) := by rw [ht]
      _ = (S.stageFunctor (v ≫ b₂)).obj Y := S.stageFunctor_obj_comp b₂ v Y
  refine ⟨m, u ≫ a₁, v ≫ b₂,
    eqToHom hsX ≫ (S.stageFunctor (u ≫ c₁)).map r.hom ≫ eqToHom htY, ?_⟩
  refine _root_.Quotient.sound ⟨m, u ≫ c₁, 𝟙 m, ?_⟩
  refine Eq.trans ?_ (S.arrowMk_map_id _).symm
  exact ((arrowMk_eqToHom_comp hsX _).trans (by
    rw [← Category.assoc]
    exact arrowMk_comp_eqToHom _ htY)).symm

/-- Arrow separation: two parallel stage morphisms with the same image in the colimit category
become equal after lowering along a single common index arrow. This is the filtered injectivity
used by the source proof of Lemma 7.18.2. -/
theorem exists_stageFunctor_map_eq {i : S.I} {X Y : S.stage i} {f g : X ⟶ Y}
    (h : (S.stageCoconeFunctor i).map f = (S.stageCoconeFunctor i).map g) :
    ∃ (k : S.I) (a : k ⟶ i), (S.stageFunctor a).map f = (S.stageFunctor a).map g := by
  have h' : homRel (⟨i, X, Y, f, rfl, rfl⟩ : HomRep (S.ιObj i X) (S.ιObj i Y))
      ⟨i, X, Y, g, rfl, rfl⟩ := _root_.Quotient.exact h
  obtain ⟨k, a, b, harr⟩ := h'
  obtain ⟨n, e, he⟩ : ∃ (n : S.I) (e : n ⟶ k), e ≫ a = e ≫ b :=
    ⟨IsCofiltered.eq a b, IsCofiltered.eqHom a b, IsCofiltered.eq_condition a b⟩
  refine ⟨n, e ≫ a, ?_⟩
  have h₂ : Arrow.mk ((S.stageFunctor (e ≫ a)).map f) =
      Arrow.mk ((S.stageFunctor (e ≫ b)).map g) :=
    (S.arrowMk_map_map a e f).symm.trans
      ((congrArg ((S.stageFunctor e).mapArrow.obj) harr).trans (S.arrowMk_map_map b e g))
  have h₃ : Arrow.mk ((S.stageFunctor (e ≫ b)).map g) =
      Arrow.mk ((S.stageFunctor (e ≫ a)).map g) :=
    congrArg (fun (c : n ⟶ i) => Arrow.mk ((S.stageFunctor c).map g)) he.symm
  exact eq_of_arrowMk_eq (h₂.trans h₃)

/-- Object descent restated for the cocone functors. -/
theorem stageCoconeFunctor_obj_surjective (x : S.ColimitCategory) :
    ∃ (i : S.I) (X : S.stage i), (S.stageCoconeFunctor i).obj X = x :=
  S.ιObj_surjective x

/-- The image of a stage morphism under the cocone functor, as a representative class. This is
the computation rule connecting `stageCoconeFunctor` with the descent interface. -/
theorem stageCoconeFunctor_map_eq {i : S.I} {X Y : S.stage i} (f : X ⟶ Y) :
    (S.stageCoconeFunctor i).map f =
      _root_.Quotient.mk _ ⟨i, X, Y, f, rfl, rfl⟩ :=
  rfl

/-- A representative class with arbitrary endpoint identifications is the transport conjugate of
the cocone image of its stage morphism. -/
theorem mk_eq_eqToHom_comp {x y : S.ColimitCategory} {k : S.I} {A B : S.stage k}
    (g : A ⟶ B) (hA : S.ιObj k A = x) (hB : S.ιObj k B = y) :
    (_root_.Quotient.mk _ (⟨k, A, B, g, hA, hB⟩ : HomRep x y) : x ⟶ y) =
      eqToHom hA.symm ≫ (S.stageCoconeFunctor k).map g ≫ eqToHom hB := by
  subst hA; subst hB
  exact (conj_eqToHom_iff_heq
    (_root_.Quotient.mk _ (⟨k, A, B, g, rfl, rfl⟩ : HomRep (S.ιObj k A) (S.ιObj k B)))
    ((S.stageCoconeFunctor k).map g) (Eq.symm rfl) rfl).2 HEq.rfl

/-- Lowering a stage morphism along an index arrow conjugates its cocone image by the canonical
object identifications. -/
theorem stageCoconeFunctor_map_lower {i k : S.I} (a : k ⟶ i) {X Y : S.stage i} (f : X ⟶ Y) :
    (S.stageCoconeFunctor i).map f =
      eqToHom (S.ιObj_lower a X).symm ≫
        (S.stageCoconeFunctor k).map ((S.stageFunctor a).map f) ≫
        eqToHom (S.ιObj_lower a Y) := by
  have h := Functor.congr_hom (S.stageCoconeFunctor_comp_eq a).symm f
  simpa using h

/-- Arrow form of `stageCoconeFunctor_map_lower`: lowering does not change the arrow image. -/
theorem arrowMk_cocone_map_lower {i k : S.I} (a : k ⟶ i) {X Y : S.stage i} (f : X ⟶ Y) :
    Arrow.mk ((S.stageCoconeFunctor i).map f) =
      Arrow.mk ((S.stageCoconeFunctor k).map ((S.stageFunctor a).map f)) :=
  congrArg (fun (G : S.stage i ⥤ S.ColimitCategory) => Arrow.mk (G.map f))
    (S.stageCoconeFunctor_comp_eq a).symm

/-- A stage morphism whose cocone image is an isomorphism becomes an isomorphism after lowering
along a single index arrow. This is the omitted axiom-(1) argument of the source proof of
Lemma 7.18.2. -/
theorem exists_stageFunctor_map_isIso {i : S.I} {X Y : S.stage i} (g : X ⟶ Y)
    [IsIso ((S.stageCoconeFunctor i).map g)] :
    ∃ (k : S.I) (a : k ⟶ i), IsIso ((S.stageFunctor a).map g) := by
  -- Extract a two-sided inverse of the image as plain data.
  obtain ⟨q, hq₁, hq₂⟩ :
      ∃ q : (S.stageCoconeFunctor i).obj Y ⟶ (S.stageCoconeFunctor i).obj X,
        (S.stageCoconeFunctor i).map g ≫ q = 𝟙 _ ∧
        q ≫ (S.stageCoconeFunctor i).map g = 𝟙 _ :=
    ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩
  -- Descend the inverse to a stage `l` below `i`.
  obtain ⟨l, c, d, h, hinv⟩ := exists_hom_rep q
  rw [mk_eq_eqToHom_comp] at hinv
  have hl := conj_of_conj (S.ιObj_lower c Y).symm (S.ιObj_lower d X) hinv
  -- Equalize the two index arrows so that the inverse becomes a stage endomorphism datum.
  obtain ⟨m, e, hed⟩ : ∃ (m : S.I) (e : m ⟶ l), e ≫ c = e ≫ d :=
    ⟨IsCofiltered.eq c d, IsCofiltered.eqHom c d, IsCofiltered.eq_condition c d⟩
  have h₁ : (S.stageFunctor (e ≫ c)).obj Y =
      (S.stageFunctor e).obj ((S.stageFunctor c).obj Y) :=
    (S.stageFunctor_obj_comp c e Y).symm
  have h₂ : (S.stageFunctor e).obj ((S.stageFunctor d).obj X) =
      (S.stageFunctor (e ≫ c)).obj X :=
    (S.stageFunctor_obj_comp d e X).trans
      (congrArg (fun (t : m ⟶ i) => (S.stageFunctor t).obj X) hed.symm)
  set hbar : (S.stageFunctor (e ≫ c)).obj Y ⟶ (S.stageFunctor (e ≫ c)).obj X :=
    eqToHom h₁ ≫ (S.stageFunctor e).map h ≫ eqToHom h₂ with hhbar
  have hml := conj_of_conj (S.ιObj_lower e ((S.stageFunctor c).obj Y)).symm
    (S.ιObj_lower e ((S.stageFunctor d).obj X)) (S.stageCoconeFunctor_map_lower e h)
  -- The lowered data compose to identities in the colimit category.
  have hbar_image : (S.stageCoconeFunctor m).map hbar =
      eqToHom (S.ιObj_lower (e ≫ c) Y) ≫ q ≫ eqToHom (S.ιObj_lower (e ≫ c) X).symm := by
    rw [hhbar, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, hml, hl]
    exact conj_collapse_nested _ _ _ _ _ _ q _ _
  have hg_image : (S.stageCoconeFunctor m).map ((S.stageFunctor (e ≫ c)).map g) =
      eqToHom (S.ιObj_lower (e ≫ c) X) ≫ (S.stageCoconeFunctor i).map g ≫
        eqToHom (S.ιObj_lower (e ≫ c) Y).symm := by
    rw [S.stageCoconeFunctor_map_lower (e ≫ c) g]
    exact (conj_conj_cancel _ _ _).symm
  have hcomp₁ : (S.stageCoconeFunctor m).map ((S.stageFunctor (e ≫ c)).map g ≫ hbar) =
      (S.stageCoconeFunctor m).map (𝟙 ((S.stageFunctor (e ≫ c)).obj X)) := by
    rw [Functor.map_comp, hg_image, hbar_image, CategoryTheory.Functor.map_id]
    exact conj_pair_comp_eq_id _ _ _ q hq₁
  have hcomp₂ : (S.stageCoconeFunctor m).map (hbar ≫ (S.stageFunctor (e ≫ c)).map g) =
      (S.stageCoconeFunctor m).map (𝟙 ((S.stageFunctor (e ≫ c)).obj Y)) := by
    rw [Functor.map_comp, hg_image, hbar_image, CategoryTheory.Functor.map_id]
    exact conj_pair_comp_eq_id _ _ q _ hq₂
  -- Merge the two stage identities at a common lower stage.
  obtain ⟨n₁, α, hα⟩ := exists_stageFunctor_map_eq hcomp₁
  obtain ⟨n₂, β, hβ⟩ := exists_stageFunctor_map_eq hcomp₂
  obtain ⟨n, u, v, huv⟩ := S.exists_span α β
  have hR : (S.stageFunctor (u ≫ α)).map ((S.stageFunctor (e ≫ c)).map g ≫ hbar) =
      𝟙 ((S.stageFunctor (u ≫ α)).obj ((S.stageFunctor (e ≫ c)).obj X)) := by
    have h3 := congrArg (S.stageFunctor u).map hα
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h3
    refine eq_of_arrowMk_eq ?_
    refine (S.arrowMk_map_map α u _).symm.trans ?_
    refine (congrArg (fun t => Arrow.mk t) h3).trans ?_
    exact congrArg (fun Z => Arrow.mk (𝟙 Z))
      (S.stageFunctor_obj_comp α u ((S.stageFunctor (e ≫ c)).obj X))
  have hL : (S.stageFunctor (v ≫ β)).map (hbar ≫ (S.stageFunctor (e ≫ c)).map g) =
      𝟙 ((S.stageFunctor (v ≫ β)).obj ((S.stageFunctor (e ≫ c)).obj Y)) := by
    have h3 := congrArg (S.stageFunctor v).map hβ
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h3
    refine eq_of_arrowMk_eq ?_
    refine (S.arrowMk_map_map β v _).symm.trans ?_
    refine (congrArg (fun t => Arrow.mk t) h3).trans ?_
    exact congrArg (fun Z => Arrow.mk (𝟙 Z))
      (S.stageFunctor_obj_comp β v ((S.stageFunctor (e ≫ c)).obj Y))
  -- The right-inverse identity, with the two composition factors named.
  have hAB : (S.stageFunctor (u ≫ α)).map ((S.stageFunctor (e ≫ c)).map g) ≫
      (S.stageFunctor (u ≫ α)).map hbar = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact hR
  -- Transport the left-inverse identity along the span commutation.
  obtain ⟨hp, hq, hA'⟩ := (arrowMk_eq_iff _ _).1
    (congrArg
      (fun (t : n ⟶ m) => Arrow.mk ((S.stageFunctor t).map ((S.stageFunctor (e ≫ c)).map g)))
      huv.symm)
  obtain ⟨hp₂, hq₂', hB'⟩ := (arrowMk_eq_iff _ _).1
    (congrArg (fun (t : n ⟶ m) => Arrow.mk ((S.stageFunctor t).map hbar)) huv.symm)
  have hBA : (S.stageFunctor (u ≫ α)).map hbar ≫
      (S.stageFunctor (u ≫ α)).map ((S.stageFunctor (e ≫ c)).map g) = 𝟙 _ := by
    have hL' : (S.stageFunctor (v ≫ β)).map hbar ≫
        (S.stageFunctor (v ≫ β)).map ((S.stageFunctor (e ≫ c)).map g) = 𝟙 _ := by
      rw [← Functor.map_comp]
      exact hL
    rw [hB', hA'] at hL'
    exact comp_eq_id_of_conj hp₂ hq₂' hp hq hL'
  have hisoA : IsIso ((S.stageFunctor (u ≫ α)).map ((S.stageFunctor (e ≫ c)).map g)) :=
    ⟨(S.stageFunctor (u ≫ α)).map hbar, hAB, hBA⟩
  rw [S.stageFunctor_map_map (e ≫ c) (u ≫ α) g] at hisoA
  haveI := hisoA
  haveI : IsIso ((S.stageFunctor ((u ≫ α) ≫ (e ≫ c))).map g ≫
      eqToHom (S.stageFunctor_obj_comp (e ≫ c) (u ≫ α) Y).symm) :=
    IsIso.of_isIso_comp_left (eqToHom (S.stageFunctor_obj_comp (e ≫ c) (u ≫ α) X)) _
  exact ⟨n, (u ≫ α) ≫ (e ≫ c),
    IsIso.of_isIso_comp_right _ (eqToHom (S.stageFunctor_obj_comp (e ≫ c) (u ≫ α) Y).symm)⟩

/-- Joint representation of two morphisms out of one colimit object into images of two objects of
one stage: both are represented at a single common stage with a single lowering of the source and
a single index arrow to the target stage. -/
theorem exists_hom_rep_pair {i₀ i : S.I} {X : S.stage i₀} {Y₁ Y₂ : S.stage i}
    (f₁ : S.ιObj i₀ X ⟶ S.ιObj i Y₁) (f₂ : S.ιObj i₀ X ⟶ S.ιObj i Y₂) :
    ∃ (k : S.I) (a : k ⟶ i₀) (b : k ⟶ i)
      (g₁ : (S.stageFunctor a).obj X ⟶ (S.stageFunctor b).obj Y₁)
      (g₂ : (S.stageFunctor a).obj X ⟶ (S.stageFunctor b).obj Y₂),
      f₁ = eqToHom (S.ιObj_lower a X).symm ≫ (S.stageCoconeFunctor k).map g₁ ≫
        eqToHom (S.ιObj_lower b Y₁) ∧
      f₂ = eqToHom (S.ιObj_lower a X).symm ≫ (S.stageCoconeFunctor k).map g₂ ≫
        eqToHom (S.ιObj_lower b Y₂) := by
  obtain ⟨k₁, a₁, b₁, g₁, h₁⟩ := exists_hom_rep f₁
  obtain ⟨k₂, a₂, b₂, g₂, h₂⟩ := exists_hom_rep f₂
  rw [mk_eq_eqToHom_comp] at h₁ h₂
  obtain ⟨m, u₁, u₂, hu⟩ := S.exists_span a₁ a₂
  obtain ⟨n, e, he⟩ : ∃ (n : S.I) (e : n ⟶ m), e ≫ (u₁ ≫ b₁) = e ≫ (u₂ ≫ b₂) :=
    ⟨_, IsCofiltered.eqHom _ _, IsCofiltered.eq_condition _ _⟩
  have ha : (e ≫ u₂) ≫ a₂ = (e ≫ u₁) ≫ a₁ := by
    simp only [Category.assoc]
    rw [hu]
  have hb : (e ≫ u₂) ≫ b₂ = (e ≫ u₁) ≫ b₁ := by
    simpa [Category.assoc] using he.symm
  refine ⟨n, (e ≫ u₁) ≫ a₁, (e ≫ u₁) ≫ b₁,
    eqToHom (S.stageFunctor_obj_comp a₁ (e ≫ u₁) X).symm ≫
      (S.stageFunctor (e ≫ u₁)).map g₁ ≫
      eqToHom (S.stageFunctor_obj_comp b₁ (e ≫ u₁) Y₁),
    eqToHom (((congrArg (fun (t : n ⟶ i₀) => (S.stageFunctor t).obj X) ha.symm).trans
        (S.stageFunctor_obj_comp a₂ (e ≫ u₂) X).symm)) ≫
      (S.stageFunctor (e ≫ u₂)).map g₂ ≫
      eqToHom ((S.stageFunctor_obj_comp b₂ (e ≫ u₂) Y₂).trans
        (congrArg (fun (t : n ⟶ i) => (S.stageFunctor t).obj Y₂) hb)),
    ?_, ?_⟩
  · rw [h₁, S.stageCoconeFunctor_map_lower (e ≫ u₁) g₁]
    exact (conj_collapse₂ _ _ _ _ _
        (((S.ιObj_lower (e ≫ u₁) ((S.stageFunctor a₁).obj X)).trans
          (S.ιObj_lower a₁ X)).symm)
        ((S.ιObj_lower (e ≫ u₁) ((S.stageFunctor b₁).obj Y₁)).trans
          (S.ιObj_lower b₁ Y₁))).trans
      (map_conj_conj_collapse (S.stageCoconeFunctor n) _ _ _ _ _
        (((S.ιObj_lower (e ≫ u₁) ((S.stageFunctor a₁).obj X)).trans
          (S.ιObj_lower a₁ X)).symm)
        ((S.ιObj_lower (e ≫ u₁) ((S.stageFunctor b₁).obj Y₁)).trans
          (S.ιObj_lower b₁ Y₁))).symm
  · rw [h₂, S.stageCoconeFunctor_map_lower (e ≫ u₂) g₂]
    exact (conj_collapse₂ _ _ _ _ _
        (((S.ιObj_lower (e ≫ u₂) ((S.stageFunctor a₂).obj X)).trans
          (S.ιObj_lower a₂ X)).symm)
        ((S.ιObj_lower (e ≫ u₂) ((S.stageFunctor b₂).obj Y₂)).trans
          (S.ιObj_lower b₂ Y₂))).trans
      (map_conj_conj_collapse (S.stageCoconeFunctor n) _ _ _ _ _
        (((S.ιObj_lower (e ≫ u₂) ((S.stageFunctor a₂).obj X)).trans
          (S.ιObj_lower a₂ X)).symm)
        ((S.ιObj_lower (e ≫ u₂) ((S.stageFunctor b₂).obj Y₂)).trans
          (S.ιObj_lower b₂ Y₂))).symm

/-- Lowering preserves stage-level equality of lowered morphisms. -/
theorem stageFunctor_map_eq_lower {k : S.I} {A B : S.stage k} {x y : A ⟶ B}
    {n : S.I} (δ : n ⟶ k) {n' : S.I} (w : n' ⟶ n)
    (h : (S.stageFunctor δ).map x = (S.stageFunctor δ).map y) :
    (S.stageFunctor (w ≫ δ)).map x = (S.stageFunctor (w ≫ δ)).map y := by
  refine eq_of_arrowMk_eq ?_
  refine (S.arrowMk_map_map δ w x).symm.trans ?_
  refine (congrArg ((S.stageFunctor w).mapArrow.obj) (congrArg (fun t => Arrow.mk t) h)).trans ?_
  exact S.arrowMk_map_map δ w y

end Descent

end CofilteredSiteDiagram
