module

public import Mathlib.Topology.IsLocalHomeomorph
public import stacks_project.Chap06.Glueing_data_for_sheaves_on_an_open_cover
public import stacks_project.Chap06.Lemma_6_33_1
public import stacks_project.Chap06.Definition_6_30_2
public import stacks_project.Chap06.Lemma_6_30_6
@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe u v

section

variable {X : TopCat.{u}} {ι : Type v} {U : ι → Opens X}

/-- Helper for Lemma 6.33.2: the inclusion of open subspaces induced by an inclusion `W ⊆ U`. -/
abbrev openSubsetHomOfLE_6_33_2 {W U : Opens X} (h : W ≤ U) :
    openSubsetSpace W ⟶ openSubsetSpace U :=
  (Opens.toTopCat X).map (homOfLE h)

/-- Helper for Lemma 6.33.2: in the open-subspace presentation, the inclusion `W ↪ U ↪ X` is the
same map as the direct inclusion `W ↪ X`. -/
@[simp] theorem openSubsetHomOfLE_comp_inclusion_6_33_2 {W U : Opens X} (h : W ≤ U) :
    openSubsetHomOfLE_6_33_2 h ≫ openSubsetInclusion U = openSubsetInclusion W :=
  rfl

/-- Helper for Lemma 6.33.2: the map of open subspaces induced by an inclusion `W ⊆ U` is an open
embedding. -/
theorem openSubsetHomOfLE_isOpenEmbedding_6_33_2 {W U : Opens X} (h : W ≤ U) :
    IsOpenEmbedding (openSubsetHomOfLE_6_33_2 h) := by
  -- Compare the composite `W ↪ U ↪ X` with the known open embedding `W ↪ X`.
  exact IsLocalHomeomorph.isOpenEmbedding_of_comp
    U.isOpenEmbedding.isLocalHomeomorph
    (by
      simpa [Function.comp, openSubsetHomOfLE_comp_inclusion_6_33_2] using
        W.isOpenEmbedding)
    (by continuity)

/-- Helper for Lemma 6.33.2: the open-subspace inclusions compose as expected. -/
@[simp] theorem openSubsetHomOfLE_comp_6_33_2 {A B C : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) :
    openSubsetHomOfLE_6_33_2 hAB ≫ openSubsetHomOfLE_6_33_2 hBC =
      openSubsetHomOfLE_6_33_2 (hAB.trans hBC) := by
  rfl

/-- Helper for Lemma 6.33.2: canceling isomorphisms on both sides of an equality recovers the
middle morphism. This is the basic algebra used to strip away represented-open section
comparisons after the endpoint formulas have been rewritten. -/
private theorem cancel_iso_conjugation
    {C : Type*} [Category C]
    {A B X Y : C}
    (e₁ : A ≅ B) (e₂ : X ≅ Y)
    {f : B ⟶ X} {g : A ⟶ Y} :
    e₁.hom ≫ f ≫ e₂.hom = g ↔ f = e₁.inv ≫ g ≫ e₂.inv := by
  constructor
  · intro h
    calc
      f = 𝟙 _ ≫ f ≫ 𝟙 _ := by simp
      _ = e₁.inv ≫ (e₁.hom ≫ f ≫ e₂.hom) ≫ e₂.inv := by
            simp [Category.assoc]
      _ = e₁.inv ≫ g ≫ e₂.inv := by
            simpa [Category.assoc] using congrArg (fun k ↦ e₁.inv ≫ k ≫ e₂.inv) h
  · intro h
    calc
      e₁.hom ≫ f ≫ e₂.hom = e₁.hom ≫ (e₁.inv ≫ g ≫ e₂.inv) ≫ e₂.hom := by
            simpa [h]
      _ = g := by
            simp [Category.assoc]

/-- Helper for Lemma 6.33.2: uniqueness of left adjoints is compatible with replacing the
second factor in a composite adjunction. -/
private theorem leftAdjointUniq_comp_second_app
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ F₁₂' : C₁ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₁₂' : F₁₂' ⊣ G₂₁)
    (X : C₀) :
    (Adjunction.leftAdjointUniq (adj₀₁.comp adj₁₂) (adj₀₁.comp adj₁₂')).hom.app X =
      (Adjunction.leftAdjointUniq adj₁₂ adj₁₂').hom.app (F₀₁.obj X) := by
  apply ((adj₀₁.comp adj₁₂).homEquiv X (F₁₂'.obj (F₀₁.obj X))).injective
  change
    ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁ ⋙ F₁₂').obj X))
        (((adj₀₁.comp adj₁₂).leftAdjointUniq (adj₀₁.comp adj₁₂')).hom.app X) =
      ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁ ⋙ F₁₂').obj X))
        ((adj₁₂.leftAdjointUniq adj₁₂').hom.app (F₀₁.obj X))
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj₀₁.comp adj₁₂) (adj₀₁.comp adj₁₂') X]
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj₁₂ adj₁₂' (F₀₁.obj X)
  simpa [Adjunction.homEquiv, Adjunction.comp_unit_app, Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ adj₀₁.unit.app X ≫ G₁₀.map k) h.symm

/-- Helper for Lemma 6.33.2: uniqueness of left adjoints is compatible with replacing the
first factor in a composite adjunction. -/
private theorem leftAdjointUniq_comp_first_app
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ F₀₁' : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₀₁' : F₀₁' ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁)
    (X : C₀) :
    (Adjunction.leftAdjointUniq (adj₀₁.comp adj₁₂) (adj₀₁'.comp adj₁₂)).hom.app X =
      F₁₂.map ((Adjunction.leftAdjointUniq adj₀₁ adj₀₁').hom.app X) := by
  apply ((adj₀₁.comp adj₁₂).homEquiv X (F₁₂.obj (F₀₁'.obj X))).injective
  change
    ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁' ⋙ F₁₂).obj X))
        (((adj₀₁.comp adj₁₂).leftAdjointUniq (adj₀₁'.comp adj₁₂)).hom.app X) =
      ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁' ⋙ F₁₂).obj X))
        (F₁₂.map ((adj₀₁.leftAdjointUniq adj₀₁').hom.app X))
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj₀₁.comp adj₁₂) (adj₀₁'.comp adj₁₂) X]
  let α := (adj₀₁.leftAdjointUniq adj₀₁').hom.app X
  have h₁ : adj₀₁.unit.app X ≫ G₁₀.map α = adj₀₁'.unit.app X := by
    simpa [α] using Adjunction.unit_leftAdjointUniq_hom_app adj₀₁ adj₀₁' X
  have h₂ :
      α ≫ adj₁₂.unit.app (F₀₁'.obj X) =
        adj₁₂.unit.app (F₀₁.obj X) ≫ G₂₁.map (F₁₂.map α) := by
    simpa [α] using adj₁₂.unit.naturality α
  have hcalc :
      adj₀₁'.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X)) =
        adj₀₁.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁.obj X)) ≫
          G₁₀.map (G₂₁.map (F₁₂.map α)) := by
    calc
      adj₀₁'.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X))
          =
        (adj₀₁.unit.app X ≫ G₁₀.map α) ≫
          G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X)) := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X))) h₁.symm
      _ =
        adj₀₁.unit.app X ≫
          G₁₀.map (α ≫ adj₁₂.unit.app (F₀₁'.obj X)) := by
            simp [Functor.map_comp, Category.assoc]
      _ =
        adj₀₁.unit.app X ≫
          G₁₀.map
            (adj₁₂.unit.app (F₀₁.obj X) ≫ G₂₁.map (F₁₂.map α)) := by
            simpa using congrArg (fun k ↦ adj₀₁.unit.app X ≫ G₁₀.map k) h₂
      _ =
      adj₀₁.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁.obj X)) ≫
        G₁₀.map (G₂₁.map (F₁₂.map α)) := by
          simp [Functor.map_comp]
  simpa [Adjunction.homEquiv, Adjunction.comp_unit_app, Functor.map_comp,
    Category.assoc, α] using hcalc

/-- Helper for Lemma 6.33.2: in the concrete category `Type`, equality of section morphisms can be
checked pointwise. -/
private theorem sectionMap_ext
    {α β : Type u} {f g : α ⟶ β} :
    f = g ↔ ∀ x, f x = g x := by
  constructor
  · intro h x
    simpa [h]
  · intro h
    funext x
    exact h x

/-- Helper for Lemma 6.33.2: components of a composite morphism of sheaves are the composites
of the components of the two morphisms. -/
@[simp] private theorem sheaf_hom_app_comp
    {Y : TopCat.{u}} {ℱ 𝒢 ℋ : Y.Sheaf (Type u)}
    (α : ℱ ⟶ 𝒢) (β : 𝒢 ⟶ ℋ) (V : (Opens Y)ᵒᵖ) :
    ((α ≫ β).hom.app V) = α.hom.app V ≫ β.hom.app V := by
  rfl

/-- Helper for Lemma 6.33.2: the open-subspace inclusion induced by `W ⊆ W` is the identity. -/
@[simp] private theorem openSubsetHomOfLE_refl (W : Opens X) :
    openSubsetHomOfLE_6_33_2 (show W ≤ W from le_rfl) = 𝟙 _ := by
  rfl

/-- Helper for Lemma 6.33.2: the inclusion `U ∩ V ↪ U` is an open embedding. -/
theorem openSubsetIntersectionLeftInclusion_isOpenEmbedding_6_33_2
    (U V : Opens X) :
    IsOpenEmbedding (openSubsetIntersectionLeftInclusion U V) :=
  openSubsetHomOfLE_isOpenEmbedding_6_33_2 inf_le_left

/-- Helper for Lemma 6.33.2: the inclusion `U ∩ V ↪ V` is an open embedding. -/
theorem openSubsetIntersectionRightInclusion_isOpenEmbedding_6_33_2
    (U V : Opens X) :
    IsOpenEmbedding (openSubsetIntersectionRightInclusion U V) :=
  openSubsetHomOfLE_isOpenEmbedding_6_33_2 inf_le_right

/-- Helper for Lemma 6.33.2: the open of `openSubsetSpace U` corresponding to an ambient open
`W ⊆ U`. This is the source-faithful owner for sections over `W` inside the local sheaf on `U`. -/
def subspace_open_of_le {W U : Opens X} (h : W ≤ U) :
    Opens (openSubsetSpace U) :=
  U.overEquivalence.functor.obj (Over.mk (homOfLE h))

/-- Helper for Lemma 6.33.2: an inclusion `A ⊆ B ⊆ U` induces a morphism between the
corresponding opens of the subspace `U`. -/
private def subspace_open_hom {A B U : Opens X}
    (hA : A ≤ U) (hB : B ≤ U) (hAB : A ≤ B) :
    subspace_open_of_le hA ⟶ subspace_open_of_le hB :=
  U.overEquivalence.functor.map
    (Over.homMk (homOfLE hAB) (by
      apply Subsingleton.elim))

/-- Helper for Lemma 6.33.2: the canonical map between identical opens of a subspace is the
identity. -/
@[simp] private theorem subspace_open_hom_refl {W U : Opens X} (hWU : W ≤ U) :
    subspace_open_hom hWU hWU (show W ≤ W from le_rfl) = 𝟙 _ := by
  apply Subsingleton.elim

/-- Helper for Lemma 6.33.2: the inclusion functor from opens of the subspace `U` back to ambient
opens of `X`. -/
abbrev subspace_inclusion_functor (U : Opens X) :
    Opens (openSubsetSpace U) ⥤ Opens X :=
  (Opens.isOpenEmbedding U).functor

/-- Helper for Lemma 6.33.2: passing from an object of `Over U` through `U.overEquivalence`
recovers its ambient open. -/
private theorem subspace_overEquivalence_functor_obj_eq
    (U : Opens X) (V : Over U) :
    (subspace_inclusion_functor U).obj (U.overEquivalence.functor.obj V) = V.left := by
  -- The open attached to `V : Over U` is exactly its image inside the ambient space.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, (leOfHom V.hom) hx⟩, hx, rfl⟩

/-- Helper for Lemma 6.33.2: viewing `W ⊆ U` as an open of the subspace `U` and then including it
back into `X` recovers the original ambient open `W`. -/
theorem subspace_open_of_le_image_eq
    {W U : Opens X} (h : W ≤ U) :
    (subspace_inclusion_functor U).obj (subspace_open_of_le h) = W := by
  -- Specialize the general `Over U` comparison to the arrow `W ⟶ U`.
  simpa [subspace_open_of_le] using
    subspace_overEquivalence_functor_obj_eq U (Over.mk (homOfLE h))

/-- Helper for Lemma 6.33.2: the subspace open defined by an inclusion `W ⊆ U` depends only on
the proposition `W ≤ U`, not on the chosen proof of that inclusion. -/
@[simp] theorem subspace_open_of_le_congr
    {W U : Opens X} {h₁ h₂ : W ≤ U} :
    subspace_open_of_le h₁ = subspace_open_of_le h₂ := by
  -- Both opens come from the same arrow in `Over U`, and proof irrelevance identifies the proofs.
  cases Subsingleton.elim h₁ h₂
  rfl

/-- Helper for Lemma 6.33.2: membership in an open of the subspace `U` is equivalent to
membership of the underlying point in the corresponding ambient open of `X`. -/
private theorem mem_subspace_open_iff
    {U : Opens X} (A : Opens (openSubsetSpace U)) (x : openSubsetSpace U) :
    x ∈ A ↔ x.1 ∈ (subspace_inclusion_functor U).obj A := by
  -- An ambient point lies in the image open exactly when it comes from a point of the subspace
  -- open, and that witness is unique because subtypes are extensional.
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    cases Subtype.ext hxy
    simpa using hy

/-- Helper for Lemma 6.33.2: the open of `openSubsetSpace W` corresponding to `W ⊆ W` is the top
open of that subspace. -/
@[simp] private theorem subspace_open_of_le_refl_eq_top (W : Opens X) :
    subspace_open_of_le (show W ≤ W from le_rfl) = ⊤ := by
  -- After converting to ambient membership, the claim is exactly that every point of the subspace
  -- lies in `W`.
  ext x
  simp [mem_subspace_open_iff, subspace_open_of_le_image_eq]

/-- Helper for Lemma 6.33.2: every open of an open subspace is represented by an ambient open
contained in that subspace. -/
private theorem open_subspace_open_representation
    {U₀ : Opens X} (V : Opens (openSubsetSpace U₀)) :
    ∃ W : Opens X, ∃ hW : W ≤ U₀, subspace_open_of_le hW = V := by
  let OV : Over U₀ := U₀.overEquivalence.inverse.obj V
  let hW : OV.left ≤ U₀ := leOfHom OV.hom
  refine ⟨OV.left, hW, ?_⟩
  -- Compare with the counit of the `Over U₀ ≌ Opens (openSubsetSpace U₀)` equivalence.
  have hEq : U₀.overEquivalence.functor.obj OV = V := by
    ext x
    constructor
    · intro hx
      exact (leOfHom ((U₀.overEquivalence.counitIso.app V).hom)) hx
    · intro hx
      exact (leOfHom ((U₀.overEquivalence.counitIso.app V).inv)) hx
  simpa [subspace_open_of_le, OV, hW] using hEq

/-- Helper for Lemma 6.33.2: a point of the subspace `U` lies in the open corresponding to
`W ∩ U ∩ V` exactly when its underlying point lies in `W` and `V`. -/
private theorem mem_triple_subspace_open_iff
    (W U V : Opens X) (x : openSubsetSpace U) :
    x ∈ subspace_open_of_le
        (show W ⊓ U ⊓ V ≤ U from le_trans inf_le_left inf_le_right) ↔
      x.1 ∈ W ∧ x.1 ∈ V := by
  -- First convert membership in the subspace open to ambient membership, then simplify the
  -- resulting membership in `W ∩ U ∩ V` using the fact that `x` already lies in `U`.
  rw [mem_subspace_open_iff, subspace_open_of_le_image_eq]
  constructor
  · intro hx
    exact ⟨hx.1.1, hx.2⟩
  · rintro ⟨hxW, hxV⟩
    exact ⟨⟨hxW, x.2⟩, hxV⟩

/-- Helper for Lemma 6.33.2: inside `openSubsetSpace D`, the open induced by `A ∩ B ⊆ D` is the
intersection of the opens induced by `A ⊆ D` and `B ⊆ D`. -/
@[simp] private theorem subspace_open_of_le_inf_eq
    {A B D : Opens X} (hAD : A ≤ D) (hBD : B ≤ D) :
    subspace_open_of_le (show A ⊓ B ≤ D from le_trans inf_le_left hAD) =
      subspace_open_of_le hAD ⊓ subspace_open_of_le hBD := by
  -- Compare the two opens pointwise inside the subspace `D`.
  ext x
  constructor
  · intro hx
    have hxAB : x.1 ∈ A ∧ x.1 ∈ B := by
      simpa [subspace_open_of_le_image_eq] using
        (mem_subspace_open_iff (U := D)
          (subspace_open_of_le (show A ⊓ B ≤ D from le_trans inf_le_left hAD)) x).1 hx
    have hxA : x.1 ∈ A := hxAB.1
    have hxB : x.1 ∈ B := hxAB.2
    exact ⟨
      (mem_subspace_open_iff (U := D) (subspace_open_of_le hAD) x).2
        (by simpa [subspace_open_of_le_image_eq] using hxA),
      (mem_subspace_open_iff (U := D) (subspace_open_of_le hBD) x).2
        (by simpa [subspace_open_of_le_image_eq] using hxB)⟩
  · rintro ⟨hxA, hxB⟩
    exact
      (mem_subspace_open_iff (U := D)
        (subspace_open_of_le (show A ⊓ B ≤ D from le_trans inf_le_left hAD)) x).2
        (by
          have hxA' : x.1 ∈ A := by
            simpa [subspace_open_of_le_image_eq] using
              (mem_subspace_open_iff (U := D) (subspace_open_of_le hAD) x).1 hxA
          have hxB' : x.1 ∈ B := by
            simpa [subspace_open_of_le_image_eq] using
              (mem_subspace_open_iff (U := D) (subspace_open_of_le hBD) x).1 hxB
          simpa [subspace_open_of_le_image_eq] using And.intro hxA' hxB')

/-- Helper for Lemma 6.33.2: the local sheaf on `U i` viewed on `X` by pushforward along the open
inclusion `U i ↪ X`. This is the owner for sections on `W ∩ U i` in the first source proof. -/
private abbrev extended_local_sheaf (data : SheafOpenCoverGlueing U) (i : ι) :
    X.Sheaf (Type u) :=
  (TopCat.Sheaf.pushforward (Type u) (openSubsetInclusion (U i))).obj (data.localSheaf i)

/-- Helper for Lemma 6.33.2: the open of `openSubsetSpace (U i)` corresponding to `W ∩ U i`. -/
private abbrev member_open (W : Opens X) (i : ι) :
    Opens (openSubsetSpace (U i)) :=
  subspace_open_of_le (show W ⊓ U i ≤ U i from inf_le_right)

/-- Helper for Lemma 6.33.2: the open of `openSubsetSpace (U i ⊓ U j)` corresponding to
`W ∩ U i ∩ U j`. -/
private abbrev pair_overlap_open (W : Opens X) (i j : ι) :
    Opens (openSubsetSpace (U i ⊓ U j)) :=
  subspace_open_of_le
    (show W ⊓ U i ⊓ U j ≤ U i ⊓ U j from inf_le_inf inf_le_right le_rfl)

/-- Helper for Lemma 6.33.2: the open of `openSubsetSpace (U i)` corresponding to
`W ∩ U i ∩ U j`. -/
private abbrev left_overlap_open (W : Opens X) (i j : ι) :
    Opens (openSubsetSpace (U i)) :=
  subspace_open_of_le
    (show W ⊓ U i ⊓ U j ≤ U i from le_trans inf_le_left inf_le_right)

/-- Helper for Lemma 6.33.2: the open of `openSubsetSpace (U j)` corresponding to
`W ∩ U i ∩ U j`. -/
private abbrev right_overlap_open (W : Opens X) (i j : ι) :
    Opens (openSubsetSpace (U j)) :=
  subspace_open_of_le
    (show W ⊓ U i ⊓ U j ≤ U j from inf_le_right)

/-- Helper for Lemma 6.33.2: the inclusion `V ∩ U i ↪ W ∩ U i` induced by `V ⊆ W`. -/
private abbrev member_open_hom {V W : Opens X} (hVW : V ≤ W) (i : ι) :
    member_open (U := U) V i ⟶ member_open (U := U) W i :=
  subspace_open_hom
    (show V ⊓ U i ≤ U i from inf_le_right)
    (show W ⊓ U i ≤ U i from inf_le_right)
    (by
      intro x hx
      exact ⟨hVW hx.1, hx.2⟩)

/-- Helper for Lemma 6.33.2: the inclusion
`V ∩ U i ∩ U j ↪ W ∩ U i ∩ U j` inside `openSubsetSpace (U i ⊓ U j)`. -/
private abbrev pair_overlap_open_hom {V W : Opens X} (hVW : V ≤ W) (i j : ι) :
    pair_overlap_open (U := U) V i j ⟶ pair_overlap_open (U := U) W i j :=
  subspace_open_hom
    (show V ⊓ U i ⊓ U j ≤ U i ⊓ U j from inf_le_inf inf_le_right le_rfl)
    (show W ⊓ U i ⊓ U j ≤ U i ⊓ U j from inf_le_inf inf_le_right le_rfl)
    (by
      intro x hx
      exact ⟨⟨hVW hx.1.1, hx.1.2⟩, hx.2⟩)

/-- Helper for Lemma 6.33.2: the inclusion
`V ∩ U i ∩ U j ↪ W ∩ U i ∩ U j` inside `openSubsetSpace (U i)`. -/
private abbrev left_overlap_open_hom {V W : Opens X} (hVW : V ≤ W) (i j : ι) :
    left_overlap_open (U := U) V i j ⟶ left_overlap_open (U := U) W i j :=
  subspace_open_hom
    (show V ⊓ U i ⊓ U j ≤ U i from le_trans inf_le_left inf_le_right)
    (show W ⊓ U i ⊓ U j ≤ U i from le_trans inf_le_left inf_le_right)
    (by
      intro x hx
      exact ⟨⟨hVW hx.1.1, hx.1.2⟩, hx.2⟩)

/-- Helper for Lemma 6.33.2: the inclusion
`V ∩ U i ∩ U j ↪ W ∩ U i ∩ U j` inside `openSubsetSpace (U j)`. -/
private abbrev right_overlap_open_hom {V W : Opens X} (hVW : V ≤ W) (i j : ι) :
    right_overlap_open (U := U) V i j ⟶ right_overlap_open (U := U) W i j :=
  subspace_open_hom
    (show V ⊓ U i ⊓ U j ≤ U j from inf_le_right)
    (show W ⊓ U i ⊓ U j ≤ U j from inf_le_right)
    (by
      intro x hx
      exact ⟨⟨hVW hx.1.1, hx.1.2⟩, hx.2⟩)

/-- Helper for Lemma 6.33.2: if `W` already lies in `U i ∩ U j`, then the represented overlap open
is exactly the open of `openSubsetSpace (U i ⊓ U j)` defined by `W`. -/
private theorem pair_overlap_open_eq_subspace_open_of_le
    {W : Opens X} {i j : ι} (hW : W ≤ U i ⊓ U j) :
    pair_overlap_open (U := U) W i j = subspace_open_of_le hW := by
  -- Compare both subspace opens by their ambient membership conditions inside `U i ∩ U j`.
  ext x
  constructor
  · intro hx
    have hx' : x.1 ∈ W ⊓ U i ⊓ U j := by
      simpa [pair_overlap_open, subspace_open_of_le_image_eq] using
        (mem_subspace_open_iff (U := U i ⊓ U j) (pair_overlap_open (U := U) W i j) x).1 hx
    exact (mem_subspace_open_iff (U := U i ⊓ U j) (subspace_open_of_le hW) x).2
      (by simpa [subspace_open_of_le_image_eq] using hx'.1.1)
  · intro hx
    exact (mem_subspace_open_iff (U := U i ⊓ U j) (pair_overlap_open (U := U) W i j) x).2
      (by
        have hx' : x.1 ∈ W := by
          simpa [subspace_open_of_le_image_eq] using
            (mem_subspace_open_iff (U := U i ⊓ U j) (subspace_open_of_le hW) x).1 hx
        simpa [pair_overlap_open, subspace_open_of_le_image_eq] using
          ⟨⟨hx', x.2.1⟩, x.2.2⟩)

/-- Helper for Lemma 6.33.2: if `W` already lies in `U i ∩ U j`, then the left overlap open is
just the open of `openSubsetSpace (U i)` represented by `W`. -/
private theorem left_overlap_open_eq_subspace_open_of_le
    {W : Opens X} {i j : ι} (hW : W ≤ U i ⊓ U j) :
    left_overlap_open (U := U) W i j =
      subspace_open_of_le (show W ≤ U i from fun _ hx ↦ (hW hx).1) := by
  -- Inside `openSubsetSpace (U i)`, both opens impose exactly the same ambient condition `x ∈ W`.
  ext x
  constructor
  · intro hx
    have hx' : x.1 ∈ W ⊓ U i ⊓ U j := by
      simpa [left_overlap_open, subspace_open_of_le_image_eq] using
        (mem_subspace_open_iff (U := U i) (left_overlap_open (U := U) W i j) x).1 hx
    exact (mem_subspace_open_iff (U := U i)
      (subspace_open_of_le (show W ≤ U i from fun _ hy ↦ (hW hy).1)) x).2
      (by simpa [subspace_open_of_le_image_eq] using hx'.1.1)
  · intro hx
    exact (mem_subspace_open_iff (U := U i) (left_overlap_open (U := U) W i j) x).2
      (by
        have hx' : x.1 ∈ W := by
          simpa [subspace_open_of_le_image_eq] using
            (mem_subspace_open_iff (U := U i)
              (subspace_open_of_le (show W ≤ U i from fun _ hy ↦ (hW hy).1)) x).1 hx
        have hx'' :
            x.1 ∈ (subspace_inclusion_functor (U i)).obj (left_overlap_open (U := U) W i j) := by
          simpa [left_overlap_open, subspace_open_of_le_image_eq] using
            (show x.1 ∈ W ⊓ U i ⊓ U j from ⟨⟨hx', x.2⟩, (hW hx').2⟩)
        exact hx'')

/-- Helper for Lemma 6.33.2: if `W` already lies in `U i ∩ U j`, then the right overlap open is
just the open of `openSubsetSpace (U j)` represented by `W`. -/
private theorem right_overlap_open_eq_subspace_open_of_le
    {W : Opens X} {i j : ι} (hW : W ≤ U i ⊓ U j) :
    right_overlap_open (U := U) W i j =
      subspace_open_of_le (show W ≤ U j from fun _ hx ↦ (hW hx).2) := by
  -- This is the symmetric ambient-membership comparison inside `openSubsetSpace (U j)`.
  ext x
  constructor
  · intro hx
    have hx' : x.1 ∈ W ⊓ U i ⊓ U j := by
      simpa [right_overlap_open, subspace_open_of_le_image_eq] using
        (mem_subspace_open_iff (U := U j) (right_overlap_open (U := U) W i j) x).1 hx
    exact (mem_subspace_open_iff (U := U j)
      (subspace_open_of_le (show W ≤ U j from fun _ hy ↦ (hW hy).2)) x).2
      (by simpa [subspace_open_of_le_image_eq] using hx'.1.1)
  · intro hx
    exact (mem_subspace_open_iff (U := U j) (right_overlap_open (U := U) W i j) x).2
      (by
        have hx' : x.1 ∈ W := by
          simpa [subspace_open_of_le_image_eq] using
            (mem_subspace_open_iff (U := U j)
              (subspace_open_of_le (show W ≤ U j from fun _ hy ↦ (hW hy).2)) x).1 hx
        have hx'' :
            x.1 ∈ (subspace_inclusion_functor (U j)).obj (right_overlap_open (U := U) W i j) := by
          simpa [right_overlap_open, subspace_open_of_le_image_eq] using
            (show x.1 ∈ W ⊓ U i ⊓ U j from ⟨⟨hx', (hW hx').1⟩, x.2⟩)
        exact hx'')

/-- Helper for Lemma 6.33.2: the open-embedding functor attached to `A ⊆ B ⊆ C` sends the
subspace open of `B` represented by `A` to the subspace open of `C` represented by the same
ambient open `A`. -/
theorem openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) :
    ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj (subspace_open_of_le hAB)) =
      subspace_open_of_le (hAB.trans hBC) := by
  -- Compare both opens by their points in the ambient space `X`.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyA : y.1 ∈ A := by
      simpa [subspace_open_of_le_image_eq] using
        (mem_subspace_open_iff (U := B) (subspace_open_of_le hAB) y).1 hy
    exact
      (mem_subspace_open_iff (U := C) (subspace_open_of_le (hAB.trans hBC))
        (openSubsetHomOfLE_6_33_2 hBC y)).2 (by
          simpa [openSubsetHomOfLE_6_33_2, subspace_open_of_le_image_eq] using hyA)
  · intro hx
    have hxA : x.1 ∈ A := by
      simpa [subspace_open_of_le_image_eq] using
        (mem_subspace_open_iff (U := C) (subspace_open_of_le (hAB.trans hBC)) x).1 hx
    refine ⟨⟨x.1, hAB hxA⟩, ?_, ?_⟩
    · exact (mem_subspace_open_iff (U := B) (subspace_open_of_le hAB) ⟨x.1, hAB hxA⟩).2 (by
        simpa [subspace_open_of_le_image_eq] using hxA)
    · apply Subtype.ext
      rfl

/-- Helper for Lemma 6.33.2: the two-step object normalization for `A ⊆ B ⊆ C ⊆ D` agrees with
the direct normalization from `B` to `D`. -/
private theorem openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le_comp
    {A B C D : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D) :
    (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD).functor.obj
        ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj
          (subspace_open_of_le hAB)) =
      (openSubsetHomOfLE_isOpenEmbedding_6_33_2 (hBC.trans hCD)).functor.obj
        (subspace_open_of_le hAB) := by
  -- Normalize the nested functor images to the common direct subspace open inside `D`.
  calc
    (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD).functor.obj
        ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj
          (subspace_open_of_le hAB))
      =
        (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD).functor.obj
          (subspace_open_of_le (hAB.trans hBC)) := by
            simp [openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le]
    _ = subspace_open_of_le ((hAB.trans hBC).trans hCD) := by
          simpa using
            openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le
              (hAB := hAB.trans hBC) (hBC := hCD)
    _ = subspace_open_of_le (hAB.trans (hBC.trans hCD)) := by
          simp
    _ =
        (openSubsetHomOfLE_isOpenEmbedding_6_33_2 (hBC.trans hCD)).functor.obj
          (subspace_open_of_le hAB) := by
            simpa using
              (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le
                (hAB := hAB) (hBC := hBC.trans hCD)).symm

/-- Helper for Lemma 6.33.2: after identifying the source and target opens via
`openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le`, the open-embedding functor map is exactly
the canonical inclusion between the corresponding subspace opens of `C`. -/
private theorem openSubsetHomOfLE_functor_map_eq_subspace_open_hom
    {A₁ A₂ B C : Opens X}
    (hA₁ : A₁ ≤ B) (hA₂ : A₂ ≤ B) (h12 : A₁ ≤ A₂) (hBC : B ≤ C) :
    eqToHom
        (by
          simp [openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le]) ≫
      (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.map
        (subspace_open_hom hA₁ hA₂ h12) =
      subspace_open_hom (hA₁.trans hBC) (hA₂.trans hBC) h12 ≫
        eqToHom
          (by
            simp [openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le]) := by
  -- Morphisms in `Opens` are subsingletons once the source and target opens agree.
  apply Subsingleton.elim

/-- Helper for Lemma 6.33.2: for composable open embeddings, the image-open functor for the
composite is the composite of the two image-open functors. -/
theorem openEmbedding_functor_comp_eq
    {Y Z T : TopCat.{u}} {f : Y ⟶ Z} {g : Z ⟶ T}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (hfg : IsOpenEmbedding (f ≫ g)) :
    hf.functor ⋙ hg.functor = hfg.functor := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro V
    ext t
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨f y, ⟨y, hy, rfl⟩, rfl⟩
  · intro V W i
    apply Subsingleton.elim

/-- Helper for Lemma 6.33.2: the naive sheaf pullback for a composite open embedding is the
composition of the naive sheaf pullbacks for the two open embeddings. -/
noncomputable def openEmbedding_sheafPullback_comp_iso
    {Y Z T : TopCat.{u}} {f : Y ⟶ Z} {g : Z ⟶ T}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (hfg : IsOpenEmbedding (f ≫ g)) :
    hg.sheafPullback (Type u) ⋙ hf.sheafPullback (Type u) ≅
      hfg.sheafPullback (Type u) :=
  haveI := hf.functor_isContinuous
  haveI := hg.functor_isContinuous
  haveI := hfg.functor_isContinuous
  Functor.sheafPushforwardContinuousComp'
    (eFG := eqToIso (openEmbedding_functor_comp_eq hf hg hfg))
    (Type u)
    (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology Z)
    (Opens.grothendieckTopology T)

/-- Helper for Lemma 6.33.2: the canonical pullback comparison for an open-subspace inclusion,
chosen as the uniqueness isomorphism between the actual sheaf pullback and the naive
open-embedding pullback. -/
public noncomputable def openSubsetHomOfLE_sheafPullbackIso
    {B C : Opens X} (hBC : B ≤ C) :
    TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC) ≅
      (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).sheafPullback (Type u) :=
  openEmbedding_sheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC)

/-- Helper for Lemma 6.33.2: the generic section-level comparison for restricting a sheaf along an
open-subspace inclusion `B ↪ C` and then evaluating on an ambient open `A ⊆ B`. -/
noncomputable def openSubsetHomOfLE_section_iso
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C)
    (ℱ : TopCat.Sheaf (Type u) (openSubsetSpace C)) :
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).obj ℱ)).1.obj
        (op (subspace_open_of_le hAB)) ≅
      ℱ.1.obj (op (subspace_open_of_le (hAB.trans hBC))) :=
  -- First compare the actual pullback with the open-embedding pullback, then rewrite the target
  -- open by the explicit `subspace_open_of_le` normalization.
  (((TopCat.Sheaf.forget (Type u) (openSubsetSpace B)).mapIso
      ((openSubsetHomOfLE_sheafPullbackIso (X := X) hBC).app ℱ)).app
      (op (subspace_open_of_le hAB))) ≪≫
    eqToIso (by
      change
        ℱ.1.obj
            (op ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj (subspace_open_of_le hAB))) =
          ℱ.1.obj (op (subspace_open_of_le (hAB.trans hBC)))
      simpa using congrArg (fun V ↦ ℱ.1.obj (op V))
        (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le hAB hBC))

/-- Helper for Lemma 6.33.2: the generic section-level comparison commutes with restriction from a
larger ambient open `A₂` to a smaller one `A₁`. -/
private theorem openSubsetHomOfLE_section_iso_naturality
    {A₁ A₂ B C : Opens X}
    (hA₁ : A₁ ≤ B) (hA₂ : A₂ ≤ B) (h12 : A₁ ≤ A₂) (hBC : B ≤ C)
    (ℱ : TopCat.Sheaf (Type u) (openSubsetSpace C)) :
    ((((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).obj ℱ)).1.map
        (subspace_open_hom hA₁ hA₂ h12).op) ≫
      (openSubsetHomOfLE_section_iso hA₁ hBC ℱ).hom =
    (openSubsetHomOfLE_section_iso hA₂ hBC ℱ).hom ≫
      ℱ.1.map (subspace_open_hom (hA₁.trans hBC) (hA₂.trans hBC) h12).op := by
  -- Route correction: instead of normalizing each overlap transport ad hoc, we use the naturality
  -- of the generic `sheafPullbackIso` comparison and rewrite the functor map once.
  let e :
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).obj ℱ)).1 ≅
        (((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).sheafPullback (Type u)).obj ℱ).1 :=
    (TopCat.Sheaf.forget (Type u) (openSubsetSpace B)).mapIso
      ((openSubsetHomOfLE_sheafPullbackIso (X := X) hBC).app ℱ)
  let p₁ :
      ℱ.1.obj (op ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj (subspace_open_of_le hA₁))) =
        ℱ.1.obj (op (subspace_open_of_le (hA₁.trans hBC))) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V))
      (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le hA₁ hBC)
  let p₂ :
      ℱ.1.obj (op ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj (subspace_open_of_le hA₂))) =
        ℱ.1.obj (op (subspace_open_of_le (hA₂.trans hBC))) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V))
      (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le hA₂ hBC)
  have hnat :=
    e.hom.naturality (subspace_open_hom hA₁ hA₂ h12).op
  have hmap :
      ℱ.1.map
          (((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.map
            (subspace_open_hom hA₁ hA₂ h12)).op) ≫
        eqToHom p₁ =
      eqToHom p₂ ≫
        ℱ.1.map (subspace_open_hom (hA₁.trans hBC) (hA₂.trans hBC) h12).op := by
    have hmap' := congrArg (fun k ↦ ℱ.1.map k.op)
      (openSubsetHomOfLE_functor_map_eq_subspace_open_hom hA₁ hA₂ h12 hBC)
    simpa [p₁, p₂, Functor.map_comp, Category.assoc, eqToHom_map] using hmap'
  calc
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).obj ℱ)).1.map
          (subspace_open_hom hA₁ hA₂ h12).op ≫
        (openSubsetHomOfLE_section_iso hA₁ hBC ℱ).hom
        =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).obj ℱ)).1.map
          (subspace_open_hom hA₁ hA₂ h12).op ≫
        e.hom.app (op (subspace_open_of_le hA₁)) ≫ eqToHom p₁ := by
          rfl
    _ =
      e.hom.app (op (subspace_open_of_le hA₂)) ≫
        (((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).sheafPullback (Type u)).obj ℱ).1.map
          (subspace_open_hom hA₁ hA₂ h12).op ≫
        eqToHom p₁ := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eqToHom p₁) hnat
    _ =
      e.hom.app (op (subspace_open_of_le hA₂)) ≫
        ℱ.1.map
          (((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.map
            (subspace_open_hom hA₁ hA₂ h12)).op) ≫
        eqToHom p₁ := by
          rfl
    _ =
      e.hom.app (op (subspace_open_of_le hA₂)) ≫
        eqToHom p₂ ≫
          ℱ.1.map (subspace_open_hom (hA₁.trans hBC) (hA₂.trans hBC) h12).op := by
          simpa [Category.assoc] using congrArg (fun k ↦ e.hom.app (op (subspace_open_of_le hA₂)) ≫ k)
            hmap
    _ =
      (e.hom.app (op (subspace_open_of_le hA₂)) ≫ eqToHom p₂) ≫
        ℱ.1.map (subspace_open_hom (hA₁.trans hBC) (hA₂.trans hBC) h12).op := by
          simp [Category.assoc]
    _ =
      (openSubsetHomOfLE_section_iso hA₂ hBC ℱ).hom ≫
        ℱ.1.map (subspace_open_hom (hA₁.trans hBC) (hA₂.trans hBC) h12).op := by
          rfl

/-- Helper for Lemma 6.33.2: the section comparison `openSubsetHomOfLE_section_iso` is natural in
sheaf morphisms. -/
private theorem openSubsetHomOfLE_section_iso_map_naturality
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C)
    {ℱ 𝒢 : TopCat.Sheaf (Type u) (openSubsetSpace C)} (η : ℱ ⟶ 𝒢) :
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).map η).hom.app
        (op (subspace_open_of_le hAB))) ≫
      (openSubsetHomOfLE_section_iso hAB hBC 𝒢).hom =
    (openSubsetHomOfLE_section_iso hAB hBC ℱ).hom ≫
      η.hom.app (op (subspace_open_of_le (hAB.trans hBC))) := by
  -- Compare both routes through the open-embedding pullback model, then rewrite the target open
  -- once using the canonical `subspace_open_of_le` identification.
  let ηpull :=
    Functor.isoWhiskerRight
      (openSubsetHomOfLE_sheafPullbackIso (X := X) hBC)
      (TopCat.Sheaf.forget (Type u) (openSubsetSpace B))
  let αℱ :=
    (((TopCat.Sheaf.forget (Type u) (openSubsetSpace B)).mapIso
        ((openSubsetHomOfLE_sheafPullbackIso (X := X) hBC).app ℱ)).hom.app
      (op (subspace_open_of_le hAB)))
  let α𝒢 :=
    (((TopCat.Sheaf.forget (Type u) (openSubsetSpace B)).mapIso
        ((openSubsetHomOfLE_sheafPullbackIso (X := X) hBC).app 𝒢)).hom.app
      (op (subspace_open_of_le hAB)))
  have hnat :
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).map η).hom.app
          (op (subspace_open_of_le hAB))) ≫
        α𝒢 =
      αℱ ≫
          η.hom.app
            (op
              ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj
                (subspace_open_of_le hAB))) := by
    simpa [ηpull, αℱ, α𝒢, TopCat.Sheaf.forget, Category.assoc] using
      congrArg (fun t ↦ t.app (op (subspace_open_of_le hAB))) (ηpull.hom.naturality η)
  let pℱ :
      ℱ.1.obj (op ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj (subspace_open_of_le hAB))) =
        ℱ.1.obj (op (subspace_open_of_le (hAB.trans hBC))) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V))
      (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le hAB hBC)
  let p𝒢 :
      𝒢.1.obj (op ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj (subspace_open_of_le hAB))) =
        𝒢.1.obj (op (subspace_open_of_le (hAB.trans hBC))) := by
    simpa using congrArg (fun V ↦ 𝒢.1.obj (op V))
      (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le hAB hBC)
  have htarget :
      η.hom.app
          (op ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj (subspace_open_of_le hAB))) ≫
        eqToHom p𝒢 =
      eqToHom pℱ ≫ η.hom.app (op (subspace_open_of_le (hAB.trans hBC))) := by
    have hnatEq :=
      η.hom.naturality
        (eqToHom (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le hAB hBC).symm).op
    simpa [pℱ, p𝒢, eqToHom_map, Category.assoc] using hnatEq.symm
  have hstep₁ :
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).map η).hom.app
          (op (subspace_open_of_le hAB))) ≫
        (openSubsetHomOfLE_section_iso hAB hBC 𝒢).hom =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).map η).hom.app
          (op (subspace_open_of_le hAB))) ≫
        α𝒢 ≫ eqToHom p𝒢 := by
    rfl
  have hstep₂ :
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).map η).hom.app
          (op (subspace_open_of_le hAB))) ≫
        α𝒢 ≫ eqToHom p𝒢 =
      αℱ ≫
        η.hom.app
          (op
            ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj
              (subspace_open_of_le hAB))) ≫
        eqToHom p𝒢 := by
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eqToHom p𝒢) hnat
  have hstep₃ :
      αℱ ≫
        η.hom.app
          (op
            ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj
              (subspace_open_of_le hAB))) ≫
        eqToHom p𝒢 =
      (openSubsetHomOfLE_section_iso hAB hBC ℱ).hom ≫
        η.hom.app (op (subspace_open_of_le (hAB.trans hBC))) := by
    calc
      αℱ ≫
          η.hom.app
            (op
              ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj
                (subspace_open_of_le hAB))) ≫
          eqToHom p𝒢
          =
        αℱ ≫ eqToHom pℱ ≫ η.hom.app (op (subspace_open_of_le (hAB.trans hBC))) := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ αℱ ≫ k) htarget
      _ =
        (openSubsetHomOfLE_section_iso hAB hBC ℱ).hom ≫
          η.hom.app (op (subspace_open_of_le (hAB.trans hBC))) := by
            rfl
  exact hstep₁.trans (hstep₂.trans hstep₃)

/-- Helper for Lemma 6.33.2: on sections, pulling back a sheaf morphism along an open-subspace
inclusion is the same as conjugating by the corresponding section-comparison isomorphisms. -/
theorem openSubsetHomOfLE_section_iso_map_compare
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C)
    {ℱ 𝒢 : TopCat.Sheaf (Type u) (openSubsetSpace C)} (η : ℱ ⟶ 𝒢) :
    (openSubsetHomOfLE_section_iso hAB hBC ℱ).hom ≫
      (((TopCat.Sheaf.forget (Type u) (openSubsetSpace C)).map η).app
        (op (subspace_open_of_le (hAB.trans hBC)))) ≫
      (openSubsetHomOfLE_section_iso hAB hBC 𝒢).inv =
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).map η).hom.app
      (op (subspace_open_of_le hAB))) := by
  -- Rewrite the right-hand side with naturality, then cancel the comparison isomorphism.
  have hforget :
      (((TopCat.Sheaf.forget (Type u) (openSubsetSpace C)).map η).app
        (op (subspace_open_of_le (hAB.trans hBC)))) =
        η.hom.app (op (subspace_open_of_le (hAB.trans hBC))) := rfl
  rw [hforget]
  calc
    (openSubsetHomOfLE_section_iso hAB hBC ℱ).hom ≫
        η.hom.app (op (subspace_open_of_le (hAB.trans hBC))) ≫
        (openSubsetHomOfLE_section_iso hAB hBC 𝒢).inv
        =
      ((((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).map η).hom.app
          (op (subspace_open_of_le hAB))) ≫
        (openSubsetHomOfLE_section_iso hAB hBC 𝒢).hom) ≫
          (openSubsetHomOfLE_section_iso hAB hBC 𝒢).inv := by
            rw [openSubsetHomOfLE_section_iso_map_naturality
              (hAB := hAB) (hBC := hBC) (η := η)]
            simp [Category.assoc]
    _ =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).map η).hom.app
        (op (subspace_open_of_le hAB))) := by
          simp [Category.assoc]

/-- Helper for Lemma 6.33.2: specializing the generic section-comparison transport to the
open-embedding pullback comparison for `C ↪ X` moves that comparison from the `B`-owner to the
`A`-owner, with the residual naive-pullback section comparison isolated explicitly. -/
private theorem openSubsetHomOfLE_section_iso_memberSheafPullbackIso_compare
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C)
    (ℱ : X.Sheaf (Type u)) :
    let eNaive :=
      openSubsetHomOfLE_section_iso hAB hBC
        (((C).isOpenEmbedding.sheafPullback (Type u)).obj ℱ)
    (openSubsetHomOfLE_section_iso hAB hBC
        ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion C)).obj ℱ)).hom ≫
      (((TopCat.Sheaf.forget (Type u) (openSubsetSpace C)).map
          ((openEmbedding_sheafPullbackIso (C).isOpenEmbedding).hom.app ℱ)).app
        (op (subspace_open_of_le (hAB.trans hBC)))) ≫
      eNaive.inv =
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).map
          ((openEmbedding_sheafPullbackIso (C).isOpenEmbedding).hom.app ℱ)).hom.app
        (op (subspace_open_of_le hAB))) := by
  -- Specialize the generic transport lemma to the open-embedding comparison `ℱ|_C ≅ hf.sheafPullback ℱ`.
  simpa using
    openSubsetHomOfLE_section_iso_map_compare
      (hAB := hAB)
      (hBC := hBC)
      (η := ((openEmbedding_sheafPullbackIso (C).isOpenEmbedding).hom.app ℱ))

/-- Helper for Lemma 6.33.2: `TopCat.Sheaf.pullbackComp` is the left-adjoint comparison for the
definitional equality of pushforwards along composable open inclusions. -/
private theorem open_subset_pullbackComp_def
    {W Y Z : TopCat.{u}} (f : W ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullbackComp f g =
      Adjunction.leftAdjointCompIso
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g))
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g =
            TopCat.Sheaf.pushforward (Type u) (f ≫ g) from rfl)) := by
  -- This is just the defining equation of the canonical comparison.
  rfl

/-- Helper for Lemma 6.33.2: the uniqueness-based open-embedding pullback comparison is
compatible with composition of open embeddings. -/
theorem openEmbedding_sheafPullbackIso_comp_hom
    {Y Z T : TopCat.{u}} {f : Y ⟶ Z} {g : Z ⟶ T}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (hfg : IsOpenEmbedding (f ≫ g))
    (ℱ : T.Sheaf (Type u)) :
    (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app ℱ ≫
      (openEmbedding_sheafPullbackIso hfg).hom.app ℱ =
    (TopCat.Sheaf.pullback (Type u) f).map
        ((openEmbedding_sheafPullbackIso hg).hom.app ℱ) ≫
      (openEmbedding_sheafPullbackIso hf).hom.app
        (((hg.sheafPullback (Type u)).obj ℱ)) ≫
        (openEmbedding_sheafPullback_comp_iso hf hg hfg).hom.app ℱ := by
  haveI := hf.functor_isContinuous
  haveI := hg.functor_isContinuous
  haveI := hfg.functor_isContinuous
  let adjActualG := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g
  let adjActualF := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f
  let adjActualDirect := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)
  let adjNaiveG :
      hg.sheafPullback (Type u) ⊣ TopCat.Sheaf.pushforward (Type u) g :=
    hg.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology Z)
      (Opens.grothendieckTopology T)
  let adjNaiveF :
      hf.sheafPullback (Type u) ⊣ TopCat.Sheaf.pushforward (Type u) f :=
    hf.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology Z)
  let adjNaiveDirect :
      hfg.sheafPullback (Type u) ⊣ TopCat.Sheaf.pushforward (Type u) (f ≫ g) :=
    hfg.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology T)
  let adjActualComp := adjActualG.comp adjActualF
  let adjMixedComp := adjNaiveG.comp adjActualF
  let adjNaiveComp := adjNaiveG.comp adjNaiveF
  have hleft :
      (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app ℱ ≫
        (openEmbedding_sheafPullbackIso hfg).hom.app ℱ =
      (Adjunction.leftAdjointUniq adjActualComp adjNaiveDirect).hom.app ℱ := by
    simpa [adjActualComp, adjActualG, adjActualF, adjActualDirect, adjNaiveDirect,
      openEmbedding_sheafPullbackIso, open_subset_pullbackComp_def, Category.assoc] using
      (Adjunction.leftAdjointUniq_trans_app
        adjActualComp adjActualDirect adjNaiveDirect ℱ)
  have hgreplace :
      (TopCat.Sheaf.pullback (Type u) f).map
          ((openEmbedding_sheafPullbackIso hg).hom.app ℱ) =
      (Adjunction.leftAdjointUniq adjActualComp adjMixedComp).hom.app ℱ := by
    simpa [adjActualComp, adjMixedComp, adjActualG, adjActualF, adjNaiveG,
      openEmbedding_sheafPullbackIso] using
      (leftAdjointUniq_comp_first_app adjActualG adjNaiveG adjActualF ℱ).symm
  have hfreplace :
      (openEmbedding_sheafPullbackIso hf).hom.app
          (((hg.sheafPullback (Type u)).obj ℱ)) =
      (Adjunction.leftAdjointUniq adjMixedComp adjNaiveComp).hom.app ℱ := by
    simpa [adjMixedComp, adjNaiveComp, adjNaiveG, adjActualF, adjNaiveF,
      openEmbedding_sheafPullbackIso] using
      (leftAdjointUniq_comp_second_app adjNaiveG adjActualF adjNaiveF ℱ).symm
  have hreplace :
      (TopCat.Sheaf.pullback (Type u) f).map
          ((openEmbedding_sheafPullbackIso hg).hom.app ℱ) ≫
        (openEmbedding_sheafPullbackIso hf).hom.app
          (((hg.sheafPullback (Type u)).obj ℱ)) =
      (Adjunction.leftAdjointUniq adjActualComp adjNaiveComp).hom.app ℱ := by
    calc
      (TopCat.Sheaf.pullback (Type u) f).map
            ((openEmbedding_sheafPullbackIso hg).hom.app ℱ) ≫
          (openEmbedding_sheafPullbackIso hf).hom.app
            (((hg.sheafPullback (Type u)).obj ℱ))
          =
        (Adjunction.leftAdjointUniq adjActualComp adjMixedComp).hom.app ℱ ≫
          (Adjunction.leftAdjointUniq adjMixedComp adjNaiveComp).hom.app ℱ := by
            simpa [hgreplace, hfreplace]
      _ =
        (Adjunction.leftAdjointUniq adjActualComp adjNaiveComp).hom.app ℱ := by
          simpa using
            (Adjunction.leftAdjointUniq_trans_app
              adjActualComp adjMixedComp adjNaiveComp ℱ)
  have hcomp :
      (openEmbedding_sheafPullback_comp_iso hf hg hfg).hom.app ℱ =
      (Adjunction.leftAdjointUniq adjNaiveComp adjNaiveDirect).hom.app ℱ := by
    apply (adjNaiveComp.homEquiv ℱ
      ((hfg.sheafPullback (Type u)).obj ℱ)).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app adjNaiveComp adjNaiveDirect ℱ]
    rw [Adjunction.homEquiv_unit]
    apply ObjectProperty.hom_ext
    ext V x
    simp [adjNaiveComp, adjNaiveG, adjNaiveF, adjNaiveDirect,
      openEmbedding_sheafPullback_comp_iso,
      Adjunction.comp, Adjunction.sheafPushforwardContinuous,
      Topology.IsOpenEmbedding.sheafPullback,
      IsOpenMap.adjunction,
      Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
      Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
      Category.assoc]
    rw [← FunctorToTypes.map_comp_apply]
    rw [← FunctorToTypes.map_comp_apply]
    congr 1
  have hright :
      (TopCat.Sheaf.pullback (Type u) f).map
          ((openEmbedding_sheafPullbackIso hg).hom.app ℱ) ≫
        (openEmbedding_sheafPullbackIso hf).hom.app
          (((hg.sheafPullback (Type u)).obj ℱ)) ≫
        (openEmbedding_sheafPullback_comp_iso hf hg hfg).hom.app ℱ =
      (Adjunction.leftAdjointUniq adjActualComp adjNaiveDirect).hom.app ℱ := by
    calc
      (TopCat.Sheaf.pullback (Type u) f).map
            ((openEmbedding_sheafPullbackIso hg).hom.app ℱ) ≫
          (openEmbedding_sheafPullbackIso hf).hom.app
            (((hg.sheafPullback (Type u)).obj ℱ)) ≫
          (openEmbedding_sheafPullback_comp_iso hf hg hfg).hom.app ℱ
          =
        (Adjunction.leftAdjointUniq adjActualComp adjNaiveComp).hom.app ℱ ≫
          (Adjunction.leftAdjointUniq adjNaiveComp adjNaiveDirect).hom.app ℱ := by
            calc
              (TopCat.Sheaf.pullback (Type u) f).map
                    ((openEmbedding_sheafPullbackIso hg).hom.app ℱ) ≫
                  (openEmbedding_sheafPullbackIso hf).hom.app
                    (((hg.sheafPullback (Type u)).obj ℱ)) ≫
                  (openEmbedding_sheafPullback_comp_iso hf hg hfg).hom.app ℱ
                  =
                ((TopCat.Sheaf.pullback (Type u) f).map
                    ((openEmbedding_sheafPullbackIso hg).hom.app ℱ) ≫
                  (openEmbedding_sheafPullbackIso hf).hom.app
                    (((hg.sheafPullback (Type u)).obj ℱ))) ≫
                  (openEmbedding_sheafPullback_comp_iso hf hg hfg).hom.app ℱ := by
                    rfl
              _ =
                (Adjunction.leftAdjointUniq adjActualComp adjNaiveComp).hom.app ℱ ≫
                  (openEmbedding_sheafPullback_comp_iso hf hg hfg).hom.app ℱ := by
                    simpa using congrArg
                      (fun k ↦ k ≫ (openEmbedding_sheafPullback_comp_iso hf hg hfg).hom.app ℱ)
                      hreplace
              _ =
                (Adjunction.leftAdjointUniq adjActualComp adjNaiveComp).hom.app ℱ ≫
                  (Adjunction.leftAdjointUniq adjNaiveComp adjNaiveDirect).hom.app ℱ := by
                    rw [hcomp]
      _ =
        (Adjunction.leftAdjointUniq adjActualComp adjNaiveDirect).hom.app ℱ := by
          simpa using
            (Adjunction.leftAdjointUniq_trans_app
              adjActualComp adjNaiveComp adjNaiveDirect ℱ)
  exact hleft.trans hright.symm

/-- Helper for Lemma 6.33.2: the definitional pushforward comparisons satisfy the obvious
associativity coherence. -/
private theorem open_subset_pushforward_assoc
    {W Y Z T : TopCat.{u}} (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward (Type u) f)
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type u) g ⋙ TopCat.Sheaf.pushforward (Type u) h =
            TopCat.Sheaf.pushforward (Type u) (g ≫ h) from rfl)) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type u) f ⋙
            TopCat.Sheaf.pushforward (Type u) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl) =
    (Functor.associator
      (TopCat.Sheaf.pushforward (Type u) f)
      (TopCat.Sheaf.pushforward (Type u) g)
      (TopCat.Sheaf.pushforward (Type u) h)).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g =
            TopCat.Sheaf.pushforward (Type u) (f ≫ g) from rfl))
        (TopCat.Sheaf.pushforward (Type u) h) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type u) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type u) h =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl) := by
  -- Both sides are definitionally the same natural isomorphism after evaluating on objects.
  ext ℱ
  rfl

/-- Helper for Lemma 6.33.2: the pullback-composition isomorphisms inherit the standard
associativity coherence from left-adjoint uniqueness. -/
private theorem open_subset_pullback_comp_assoc
    {W Y Z T : TopCat.{u}} (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft _ (TopCat.Sheaf.pullbackComp (A := Type u) f g) ≪≫
      TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (TopCat.Sheaf.pullbackComp (A := Type u) g h) _ ≪≫
        TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h) := by
  -- Route correction: package the owner-side associativity once so the later section-level bridge
  -- can reuse it without expanding adjunction data again.
  simpa [open_subset_pullbackComp_def] using
    (Adjunction.leftAdjointCompIso_assoc
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) h)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (g ≫ h))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g ≫ h))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) g ⋙ TopCat.Sheaf.pushforward (Type u) h =
          TopCat.Sheaf.pushforward (Type u) (g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type u) h =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) f ⋙
            TopCat.Sheaf.pushforward (Type u) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl))
      (open_subset_pushforward_assoc f g h))

/-- Helper for Lemma 6.33.2: cancelling the left comparison in pullback-composition coherence
identifies the composite endpoint with the direct pullback comparison. -/
private theorem open_subset_pullback_forward_endpoint
    {W Y Z T : TopCat.{u}} (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (F : T.Sheaf (Type u)) :
    (TopCat.Sheaf.pullbackComp (A := Type u) f g).inv.app
        ((TopCat.Sheaf.pullback (Type u) h).obj F) ≫
      (TopCat.Sheaf.pullback (Type u) f).map
        ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app F) ≫
      (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app F =
    (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom.app F := by
  -- Cancel the first comparison, then invoke the previously packaged associativity coherence.
  apply (cancel_epi ((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
    ((TopCat.Sheaf.pullback (Type u) h).obj F))).1
  have hcancel :
      (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
            ((TopCat.Sheaf.pullback (Type u) h).obj F) ≫
          ((TopCat.Sheaf.pullbackComp (A := Type u) f g).inv.app
            ((TopCat.Sheaf.pullback (Type u) h).obj F) ≫
            (TopCat.Sheaf.pullback (Type u) f).map
              ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app F) =
        (TopCat.Sheaf.pullback (Type u) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app F := by
    simpa [Category.assoc] using
      (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom_inv_id_app_assoc
        ((TopCat.Sheaf.pullback (Type u) h).obj F)
        ((TopCat.Sheaf.pullback (Type u) f).map
          ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app F)
  have hassoc :
      (TopCat.Sheaf.pullback (Type u) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app F =
        (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
            ((TopCat.Sheaf.pullback (Type u) h).obj F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom.app F := by
    simpa [Category.assoc] using
      (congrArg (fun α ↦ α.hom.app F) (open_subset_pullback_comp_assoc f g h)).symm
  exact hcancel.trans hassoc

/-- Helper for Lemma 6.33.2: the pullback-composition isomorphisms satisfy the inverse-form
associativity coherence used to normalize endpoint maps. -/
private theorem open_subset_pullback_pseudofunctor_associativity
    {W Y Z T : TopCat.{u}} (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).inv ≫
        (Functor.isoWhiskerRight
          (TopCat.Sheaf.pullbackComp (A := Type u) g h)
          (TopCat.Sheaf.pullback (Type u) f)).inv ≫
        (Functor.associator _ _ _).hom ≫
        (Functor.isoWhiskerLeft
          (TopCat.Sheaf.pullback (Type u) h)
          (TopCat.Sheaf.pullbackComp (A := Type u) f g)).hom ≫
        (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom =
      eqToHom (by simp) := by
  let e₁ := TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight
    (TopCat.Sheaf.pullbackComp (A := Type u) g h)
    (TopCat.Sheaf.pullback (Type u) f)
  let e₃ := Functor.isoWhiskerLeft
    (TopCat.Sheaf.pullback (Type u) h)
    (TopCat.Sheaf.pullbackComp (A := Type u) f g)
  let e₄ := TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have hcomp : e₃.hom ≫ e₄.hom = (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom := by
    exact congrArg Iso.hom (open_subset_pullback_comp_assoc f g h)
  rw [hcomp]
  ext X
  simpa using Iso.inv_hom_id_app e₁ X

/-- Helper for Lemma 6.33.2: cancelling the terminal direct restriction in the inverse
pullback-composition coherence identifies the inverse endpoint map. -/
private theorem open_subset_pullback_inverse_endpoint
    {W Y Z T : TopCat.{u}} (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (F : T.Sheaf (Type u)) :
    (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).inv.app F ≫
      (TopCat.Sheaf.pullback (Type u) f).map
        ((TopCat.Sheaf.pullbackComp (A := Type u) g h).inv.app F) ≫
      (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
        ((TopCat.Sheaf.pullback (Type u) h).obj F) =
    (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).inv.app F := by
  -- Postcompose with the direct restriction and reduce to the packaged pseudofunctor coherence.
  apply (cancel_mono ((TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom.app F)).1
  have hcoh :
      (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).inv.app F ≫
          (TopCat.Sheaf.pullback (Type u) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type u) g h).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
            ((TopCat.Sheaf.pullback (Type u) h).obj F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom.app F =
        eqToHom (by simp) := by
    simpa [Category.assoc] using
      congrArg (fun α ↦ α.app F) (open_subset_pullback_pseudofunctor_associativity f g h)
  have hid :
      eqToHom (by simp) =
        (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).inv.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom.app F := by
    simpa using
      (Iso.inv_hom_id_app (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h) F).symm
  exact hcoh.trans hid

/-- Helper for Lemma 6.33.2: evaluating the pullback of a sheaf morphism on the top open of
`openSubsetSpace A` is the same as conjugating its represented-open component by the canonical
section comparisons. -/
private theorem openSubsetHomOfLE_top_section_factorization
    {A B : Opens X} (hAB : A ≤ B)
    {ℱ 𝒢 : TopCat.Sheaf (Type u) (openSubsetSpace B)} (η : ℱ ⟶ 𝒢) :
    eqToHom
        (congrArg
          (fun V ↦
            (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).obj ℱ)).1.obj (op V))
          (subspace_open_of_le_refl_eq_top A)) ≫
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map η).hom.app
        (op ⊤)) ≫
      eqToHom
        (congrArg
          (fun V ↦
            (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).obj 𝒢)).1.obj (op V))
          (subspace_open_of_le_refl_eq_top A).symm) =
      (openSubsetHomOfLE_section_iso (show A ≤ A from le_rfl) hAB ℱ).hom ≫
        η.hom.app (op (subspace_open_of_le hAB)) ≫
        (openSubsetHomOfLE_section_iso (show A ≤ A from le_rfl) hAB 𝒢).inv := by
  let Pℱ := (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).obj ℱ)).1
  let P𝒢 := (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).obj 𝒢)).1
  let pℱ :
      Pℱ.obj (op (subspace_open_of_le (show A ≤ A from le_rfl))) = Pℱ.obj (op ⊤) := by
    simpa [Pℱ] using congrArg (fun V ↦ Pℱ.obj (op V)) (subspace_open_of_le_refl_eq_top A)
  let p𝒢 :
      P𝒢.obj (op (subspace_open_of_le (show A ≤ A from le_rfl))) = P𝒢.obj (op ⊤) := by
    simpa [P𝒢] using congrArg (fun V ↦ P𝒢.obj (op V)) (subspace_open_of_le_refl_eq_top A)
  have hmapℱ :
      Pℱ.map (eqToHom (subspace_open_of_le_refl_eq_top A).symm).op = eqToHom pℱ := by
    have hmapℱ' :
        Pℱ.map (eqToHom (subspace_open_of_le_refl_eq_top A).symm).op =
          eqToHom
            (congrArg (fun V ↦ Pℱ.obj (op V)) (subspace_open_of_le_refl_eq_top A)) := by
      simpa [Pℱ] using
        (CategoryTheory.eqToHom_map Pℱ
          (congrArg Opposite.op (subspace_open_of_le_refl_eq_top A)))
    simpa [pℱ] using hmapℱ'
  have hmap𝒢 :
      P𝒢.map (eqToHom (subspace_open_of_le_refl_eq_top A).symm).op = eqToHom p𝒢 := by
    have hmap𝒢' :
        P𝒢.map (eqToHom (subspace_open_of_le_refl_eq_top A).symm).op =
          eqToHom
            (congrArg (fun V ↦ P𝒢.obj (op V)) (subspace_open_of_le_refl_eq_top A)) := by
      simpa [P𝒢] using
        (CategoryTheory.eqToHom_map P𝒢
          (congrArg Opposite.op (subspace_open_of_le_refl_eq_top A)))
    simpa [p𝒢] using hmap𝒢'
  have hnat :=
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map η).hom.naturality
      (eqToHom (subspace_open_of_le_refl_eq_top A).symm).op)
  have htop :
      eqToHom pℱ ≫
          (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map η).hom.app
            (op ⊤)) ≫
          eqToHom p𝒢.symm =
        (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map η).hom.app
          (op (subspace_open_of_le (show A ≤ A from le_rfl)))) := by
    -- Transport the top-open component back to the represented source open.
    have hnat' :
        eqToHom pℱ ≫
            (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map η).hom.app
              (op ⊤)) =
          (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map η).hom.app
              (op (subspace_open_of_le (show A ≤ A from le_rfl)))) ≫
            eqToHom p𝒢 := by
      simpa [hmapℱ, hmap𝒢] using hnat
    calc
      eqToHom pℱ ≫
            (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map η).hom.app
              (op ⊤)) ≫
            eqToHom p𝒢.symm
          =
        ((((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map η).hom.app
              (op (subspace_open_of_le (show A ≤ A from le_rfl)))) ≫
            eqToHom p𝒢) ≫ eqToHom p𝒢.symm := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ eqToHom p𝒢.symm) hnat'
      _ =
        (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map η).hom.app
          (op (subspace_open_of_le (show A ≤ A from le_rfl)))) := by
              simp [Category.assoc]
  have hrepr :=
    (openSubsetHomOfLE_section_iso_map_compare
      (hAB := (show A ≤ A from le_rfl)) (hBC := hAB) (η := η)).symm
  exact htop.trans hrepr

/-- Helper for Lemma 6.33.2: the represented-top-open transport formula specializes cleanly to the
identity inclusion of `A` into itself. This is the reusable packaging step needed when the
remaining endpoint terms still carry an `A = A` pullback wrapper. -/
private theorem openSubsetHomOfLE_identity_top_section_factorization
    {A : Opens X}
    {ℱ 𝒢 : TopCat.Sheaf (Type u) (openSubsetSpace A)}
    (η : ℱ ⟶ 𝒢) :
    eqToHom
        (congrArg
          (fun V ↦
            (((TopCat.Sheaf.pullback (Type u)
                  (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))).obj ℱ)).1.obj (op V))
          (subspace_open_of_le_refl_eq_top A)) ≫
      (((TopCat.Sheaf.pullback (Type u)
            (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))).map η).hom.app
        (op ⊤)) ≫
      eqToHom
        (congrArg
          (fun V ↦
            (((TopCat.Sheaf.pullback (Type u)
                  (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))).obj 𝒢)).1.obj (op V))
          (subspace_open_of_le_refl_eq_top A).symm) =
      (openSubsetHomOfLE_section_iso
          (show A ≤ A from le_rfl)
          (show A ≤ A from le_rfl)
          ℱ).hom ≫
        η.hom.app (op (subspace_open_of_le (show A ≤ A from le_rfl))) ≫
          (openSubsetHomOfLE_section_iso
            (show A ≤ A from le_rfl)
            (show A ≤ A from le_rfl)
            𝒢).inv := by
  -- This is exactly the `A = A` specialization of the generic top-open transport lemma.
  simpa using
    openSubsetHomOfLE_top_section_factorization
      (hAB := (show A ≤ A from le_rfl))
      (η := η)

/-- Helper for Lemma 6.33.2: on the represented open of `A`, pulling back a sheaf morphism along
the identity inclusion is exactly the underlying section map conjugated by the identity-stage
section comparisons. -/
private theorem openSubsetHomOfLE_identity_pullback_unit_section_formula
    {A : Opens X}
    {ℱ 𝒢 : TopCat.Sheaf (Type u) (openSubsetSpace A)}
    (η : ℱ ⟶ 𝒢) :
    (((TopCat.Sheaf.pullback (Type u)
          (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))).map η).hom.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl)))) =
      (openSubsetHomOfLE_section_iso
          (show A ≤ A from le_rfl)
          (show A ≤ A from le_rfl)
          ℱ).hom ≫
        η.hom.app (op (subspace_open_of_le (show A ≤ A from le_rfl))) ≫
          (openSubsetHomOfLE_section_iso
            (show A ≤ A from le_rfl)
            (show A ≤ A from le_rfl)
            𝒢).inv := by
  -- This is the exact represented-open specialization of the generic map-comparison formula.
  simpa using
    (openSubsetHomOfLE_section_iso_map_compare
      (hAB := (show A ≤ A from le_rfl))
      (hBC := (show A ≤ A from le_rfl))
      (η := η)).symm

/-- Helper for Lemma 6.33.2: on the represented top open of `A`, the identity pullback functor
sends a composite natural transformation to the composite of its evaluated section maps. -/
private theorem openSubsetHomOfLE_identity_pullback_map_app_of_comp
    {A : Opens X}
    {ℱ 𝒢 ℋ : TopCat.Sheaf (Type u) (openSubsetSpace A)}
    (η₁ : ℱ ⟶ 𝒢) (η₂ : 𝒢 ⟶ ℋ) :
    (((TopCat.Sheaf.pullback (Type u)
          (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))).map (η₁ ≫ η₂)).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl)))) =
      (((TopCat.Sheaf.pullback (Type u)
            (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))).map η₁).1.app
          (op (subspace_open_of_le (show A ≤ A from le_rfl)))) ≫
      (((TopCat.Sheaf.pullback (Type u)
            (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))).map η₂).1.app
          (op (subspace_open_of_le (show A ≤ A from le_rfl)))) := by
  -- Split the image of the composite before matching the endpoint formulas term-by-term.
  rw [Functor.map_comp]
  rfl

/-- Helper for Lemma 6.33.2: the left identity-stage inverse endpoint rewrites its top-open
transport into the represented-open inverse component flanked by the canonical identity-stage
section comparisons. -/
private theorem openSubsetHomOfLE_left_identity_inverse_endpoint_component_formula
    {A B C : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C)
    (G : TopCat.Sheaf (Type u) (openSubsetSpace C)) :
    let leftSource :=
      ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).obj
        ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).obj G))
    let leftTarget :=
      ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))).obj
        leftSource)
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))).map
          ((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))
                (openSubsetHomOfLE_6_33_2 hAB)).symm.hom.app
            ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).obj G))).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl)))) =
      (openSubsetHomOfLE_section_iso
          (show A ≤ A from le_rfl)
          (show A ≤ A from le_rfl)
          leftSource).hom ≫
        (((TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))
              (openSubsetHomOfLE_6_33_2 hAB)).symm.hom.app
            ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).obj G)).1.app
          (op (subspace_open_of_le (show A ≤ A from le_rfl)))) ≫
          (openSubsetHomOfLE_section_iso
            (show A ≤ A from le_rfl)
            (show A ≤ A from le_rfl)
            leftTarget).inv := by
  -- This is exactly the identity-stage represented-open factorization for the left outer endpoint.
  simpa using
    openSubsetHomOfLE_identity_pullback_unit_section_formula
      (A := A)
      (η := (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))
        (openSubsetHomOfLE_6_33_2 hAB)).symm.hom.app
          ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).obj G))

/-- Helper for Lemma 6.33.2: the right identity-stage forward endpoint rewrites its top-open
transport into the represented-open forward component flanked by the canonical identity-stage
section comparisons. -/
private theorem openSubsetHomOfLE_right_identity_forward_endpoint_component_formula
    {A B C : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C)
    (G : TopCat.Sheaf (Type u) (openSubsetSpace C)) :
    let rightSource :=
      ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))).obj
        ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 (hAB.trans hBC))).obj G))
    let rightTarget :=
      ((TopCat.Sheaf.pullback (Type u)
          (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl) ≫
            openSubsetHomOfLE_6_33_2 (hAB.trans hBC))).obj G)
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))).map
          ((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))
                (openSubsetHomOfLE_6_33_2 (hAB.trans hBC))).hom.app G)).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl)))) =
      (openSubsetHomOfLE_section_iso
          (show A ≤ A from le_rfl)
          (show A ≤ A from le_rfl)
          rightSource).hom ≫
        (((TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))
              (openSubsetHomOfLE_6_33_2 (hAB.trans hBC))).hom.app G).1.app
          (op (subspace_open_of_le (show A ≤ A from le_rfl)))) ≫
          (openSubsetHomOfLE_section_iso
            (show A ≤ A from le_rfl)
            (show A ≤ A from le_rfl)
            rightTarget).inv := by
  -- This is exactly the identity-stage represented-open factorization for the right outer endpoint.
  simpa using
    openSubsetHomOfLE_identity_pullback_unit_section_formula
      (A := A)
      (η := (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetHomOfLE_6_33_2 (show A ≤ A from le_rfl))
        (openSubsetHomOfLE_6_33_2 (hAB.trans hBC))).hom.app G)

/-- Helper for Lemma 6.33.2: evaluating the inverse pullback-composition coherence at the
represented top open of `A` expands the composite sheaf morphism into the corresponding
composition of endpoint section maps. -/
private theorem openSubsetHomOfLE_inverse_endpoint_component_formula
    {A B C D : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D)
    (ℱ : TopCat.Sheaf (Type u) (openSubsetSpace D)) :
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hAB)
          (openSubsetHomOfLE_6_33_2 (hBC.trans hCD))).inv.app ℱ).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl)))) ≫
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
          ((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 hBC)
            (openSubsetHomOfLE_6_33_2 hCD)).inv.app ℱ)).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl)))) ≫
      ((((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hAB)
          (openSubsetHomOfLE_6_33_2 hBC)).hom.app
          ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl))))) =
      ((((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 (hAB.trans hBC))
          (openSubsetHomOfLE_6_33_2 hCD)).inv.app ℱ).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl))))) := by
  -- Evaluate the sheaf-level inverse endpoint identity on the represented top open of `A`.
  simpa [openSubsetHomOfLE_comp_6_33_2, NatTrans.comp_app, Category.assoc] using
    congrArg
      (fun k ↦ k.1.app (op (subspace_open_of_le (show A ≤ A from le_rfl))))
      (open_subset_pullback_inverse_endpoint
        (openSubsetHomOfLE_6_33_2 hAB)
      (openSubsetHomOfLE_6_33_2 hBC)
      (openSubsetHomOfLE_6_33_2 hCD)
      ℱ)

/-- Helper for Lemma 6.33.2: evaluating the forward pullback-composition coherence at the
represented top open of `A` expands the composite sheaf morphism into the corresponding
composition of endpoint section maps. -/
private theorem openSubsetHomOfLE_forward_endpoint_component_formula
    {A B C D : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D)
    (ℱ : TopCat.Sheaf (Type u) (openSubsetSpace D)) :
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hAB)
          (openSubsetHomOfLE_6_33_2 hBC)).inv.app
        ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl)))) ≫
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
          ((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 hBC)
            (openSubsetHomOfLE_6_33_2 hCD)).hom.app ℱ)).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl)))) ≫
      (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hAB)
          (openSubsetHomOfLE_6_33_2 (hBC.trans hCD))).hom.app ℱ).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl)))) =
      (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 (hAB.trans hBC))
          (openSubsetHomOfLE_6_33_2 hCD)).hom.app ℱ).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl)))) := by
  -- Evaluate the sheaf-level forward endpoint identity on the represented top open of `A`.
  simpa [openSubsetHomOfLE_comp_6_33_2, NatTrans.comp_app, Category.assoc] using
    congrArg
      (fun k ↦ k.1.app (op (subspace_open_of_le (show A ≤ A from le_rfl))))
      (open_subset_pullback_forward_endpoint
        (openSubsetHomOfLE_6_33_2 hAB)
      (openSubsetHomOfLE_6_33_2 hBC)
      (openSubsetHomOfLE_6_33_2 hCD)
      ℱ)

/-- Helper for Lemma 6.33.2: translating the forward pullback-composition coherence on the top
open of `A` through the canonical section comparisons yields the stagewise section factorization
used to recover the inverse endpoint comparison. -/
private theorem openSubsetHomOfLE_forward_endpoint_top_section_compare
    {A B C D : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D)
    (ℱ : TopCat.Sheaf (Type u) (openSubsetSpace D)) :
    let eAB :=
      openSubsetHomOfLE_section_iso hAB hBC
        ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)
    let eC := openSubsetHomOfLE_section_iso (hAB.trans hBC) hCD ℱ
    let eDirect := openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ
    let compHom :=
      (((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 hBC)
            (openSubsetHomOfLE_6_33_2 hCD)).hom.app ℱ).1.app
          (op (subspace_open_of_le hAB)))
    eAB.inv ≫ compHom ≫ eDirect.hom = eC.hom := by
  let eAB :=
    openSubsetHomOfLE_section_iso hAB hBC
      ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)
  let eC := openSubsetHomOfLE_section_iso (hAB.trans hBC) hCD ℱ
  let eDirect := openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ
  let eABNaive :=
    openSubsetHomOfLE_section_iso hAB hBC
      (((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD).sheafPullback (Type u)).obj ℱ)
  let compHom :=
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hBC)
          (openSubsetHomOfLE_6_33_2 hCD)).hom.app ℱ).1.app
      (op (subspace_open_of_le hAB)))
  have hbridge :=
    congrArg
      (fun η ↦ η.1.app (op (subspace_open_of_le hAB)))
      (openEmbedding_sheafPullbackIso_comp_hom
        (hf := openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC)
        (hg := openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)
        (hfg := openSubsetHomOfLE_isOpenEmbedding_6_33_2 (hBC.trans hCD))
        ℱ)
  let pDirect :
      ℱ.1.obj
        (op ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 (hBC.trans hCD)).functor.obj
          (subspace_open_of_le hAB))) =
      ℱ.1.obj (op (subspace_open_of_le (hAB.trans (hBC.trans hCD)))) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V))
      (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le hAB (hBC.trans hCD))
  let pC :
      ℱ.1.obj
        (op ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD).functor.obj
          (subspace_open_of_le (hAB.trans hBC)))) =
      ℱ.1.obj (op (subspace_open_of_le ((hAB.trans hBC).trans hCD))) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V))
      (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le (hAB.trans hBC) hCD)
  let pABActual :
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).1.obj
        (op ((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).functor.obj
          (subspace_open_of_le hAB))) =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).1.obj
        (op (subspace_open_of_le (hAB.trans hBC))) := by
    simpa using congrArg
      (fun V ↦
        (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).1.obj (op V))
      (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le hAB hBC)
  have hmap :
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).map
            ((openEmbedding_sheafPullbackIso
              (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hAB))) ≫
        eABNaive.hom =
      eAB.hom ≫
        ((openEmbedding_sheafPullbackIso
          (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ).hom.app
          (op (subspace_open_of_le (hAB.trans hBC))) := by
    have hcmp :=
      openSubsetHomOfLE_section_iso_map_compare
        (hAB := hAB) (hBC := hBC)
        (η := ((openEmbedding_sheafPullbackIso
          (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ))
    calc
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hBC)).map
            ((openEmbedding_sheafPullbackIso
              (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hAB))) ≫
        eABNaive.hom
          =
        ((eAB.hom ≫
          ((openEmbedding_sheafPullbackIso
            (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ).hom.app
            (op (subspace_open_of_le (hAB.trans hBC))) ≫
          eABNaive.inv) ≫ eABNaive.hom) := by
            simpa [eAB, eABNaive, TopCat.Sheaf.forget, Category.assoc] using
              congrArg (fun k ↦ k ≫ eABNaive.hom) hcmp.symm
      _ =
        eAB.hom ≫
          ((openEmbedding_sheafPullbackIso
            (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ).hom.app
            (op (subspace_open_of_le (hAB.trans hBC))) := by
            simp [Category.assoc]
  have hnaive :
      ((((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).sheafPullback (Type u)).map
          ((openEmbedding_sheafPullbackIso
            (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hAB))) ≫
        (((openEmbedding_sheafPullback_comp_iso
            (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC)
            (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)
            (openSubsetHomOfLE_isOpenEmbedding_6_33_2 (hBC.trans hCD))).hom.app ℱ).hom.app
          (op (subspace_open_of_le hAB))) ≫
        eqToHom pDirect =
      eqToHom pABActual ≫
        ((openEmbedding_sheafPullbackIso
          (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ).hom.app
          (op (subspace_open_of_le (hAB.trans hBC))) ≫
        eqToHom pC := by
    have hnat :=
      ((openEmbedding_sheafPullbackIso
        (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ).hom.naturality
        (eqToHom
          (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le hAB hBC).symm).op
    simpa [openSubsetHomOfLE_section_iso,
      openSubsetHomOfLE_sheafPullbackIso, openSubsetHomOfLE_comp_6_33_2,
      openEmbedding_sheafPullback_comp_iso, Topology.IsOpenEmbedding.sheafPullback,
      Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
      Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
      TopCat.Sheaf.forget, NatTrans.comp_app, eqToHom_map, subspace_open_of_le_congr,
      pDirect, pC, pABActual, Category.assoc] using
      (congrArg (fun k ↦ k ≫ eqToHom pC) hnat).symm
  have htrans : compHom ≫ eDirect.hom = eAB.hom ≫ eC.hom := by
    have hbridgePost :
        compHom ≫ eDirect.hom =
          (((openEmbedding_sheafPullbackIso
              (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC)).hom.app
            ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).hom.app
              (op (subspace_open_of_le hAB))) ≫
            ((((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).sheafPullback (Type u)).map
              ((openEmbedding_sheafPullbackIso
                (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ)).hom.app
              (op (subspace_open_of_le hAB))) ≫
            (((openEmbedding_sheafPullback_comp_iso
                (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC)
                (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)
                (openSubsetHomOfLE_isOpenEmbedding_6_33_2 (hBC.trans hCD))).hom.app ℱ).hom.app
              (op (subspace_open_of_le hAB))) ≫
            eqToHom pDirect := by
      change
        compHom ≫
            (((openEmbedding_sheafPullbackIso
              (openSubsetHomOfLE_isOpenEmbedding_6_33_2 (hBC.trans hCD))).hom.app ℱ).hom.app
              (op (subspace_open_of_le hAB))) ≫
            eqToHom pDirect =
          (((openEmbedding_sheafPullbackIso
              (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC)).hom.app
            ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).hom.app
              (op (subspace_open_of_le hAB))) ≫
            ((((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).sheafPullback (Type u)).map
              ((openEmbedding_sheafPullbackIso
                (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ)).hom.app
              (op (subspace_open_of_le hAB))) ≫
            (((openEmbedding_sheafPullback_comp_iso
                (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC)
                (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)
                (openSubsetHomOfLE_isOpenEmbedding_6_33_2 (hBC.trans hCD))).hom.app ℱ).hom.app
              (op (subspace_open_of_le hAB))) ≫
            eqToHom pDirect
      simpa [InducedCategory.comp_hom, NatTrans.comp_app, Category.assoc] using
        congrArg (fun k ↦ k ≫ eqToHom pDirect) hbridge
    calc
      compHom ≫ eDirect.hom
          =
        (((openEmbedding_sheafPullbackIso
            (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC)).hom.app
          ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).hom.app
            (op (subspace_open_of_le hAB))) ≫
          (((((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC).sheafPullback (Type u)).map
            ((openEmbedding_sheafPullbackIso
              (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ)).hom.app
            (op (subspace_open_of_le hAB))) ≫
          (((openEmbedding_sheafPullback_comp_iso
              (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC)
              (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)
              (openSubsetHomOfLE_isOpenEmbedding_6_33_2 (hBC.trans hCD))).hom.app ℱ).hom.app
            (op (subspace_open_of_le hAB))) ≫
          eqToHom pDirect) := by
            simpa [Category.assoc] using hbridgePost
      _ =
        (((openEmbedding_sheafPullbackIso
            (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC)).hom.app
          ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).hom.app
            (op (subspace_open_of_le hAB))) ≫
          (eqToHom pABActual ≫
            ((openEmbedding_sheafPullbackIso
              (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ).hom.app
              (op (subspace_open_of_le (hAB.trans hBC))) ≫
            eqToHom pC) := by
            simpa [Category.assoc] using congrArg
              (fun k ↦
                (((openEmbedding_sheafPullbackIso
                    (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hBC)).hom.app
                  ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).hom.app
                    (op (subspace_open_of_le hAB))) ≫ k)
              hnaive
      _ =
        ((openSubsetHomOfLE_section_iso hAB hBC
            ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).hom ≫
          ((openEmbedding_sheafPullbackIso
            (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hCD)).hom.app ℱ).hom.app
            (op (subspace_open_of_le (hAB.trans hBC)))) ≫
          eqToHom pC := by
            rfl
      _ = eAB.hom ≫ eC.hom := by
            rfl
  calc
    eAB.inv ≫ compHom ≫ eDirect.hom
        = eAB.inv ≫ (eAB.hom ≫ eC.hom) := by
            simpa [Category.assoc] using congrArg (fun k ↦ eAB.inv ≫ k) htrans
    _ = eC.hom := by
          simp

/-- Helper for Lemma 6.33.2: evaluating the inverse pullback-composition coherence at the top open
of `openSubsetSpace A` and translating it through the canonical section comparisons yields the
endpoint identity needed for the source-faithful stagewise factorization. -/
private theorem openSubsetHomOfLE_inverse_endpoint_top_section_compare
    {A B C D : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D)
    (ℱ : TopCat.Sheaf (Type u) (openSubsetSpace D)) :
    let eAB :=
      openSubsetHomOfLE_section_iso hAB hBC
        ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)
    let eC := openSubsetHomOfLE_section_iso (hAB.trans hBC) hCD ℱ
    let eDirect := openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ
    let comp :=
      (((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 hBC)
            (openSubsetHomOfLE_6_33_2 hCD)).symm.hom.app ℱ).1.app
          (op (subspace_open_of_le hAB)))
    eDirect.hom ≫ eC.inv = comp ≫ eAB.hom := by
  let eAB :=
    openSubsetHomOfLE_section_iso hAB hBC
      ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)
  let eC := openSubsetHomOfLE_section_iso (hAB.trans hBC) hCD ℱ
  let eDirect := openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ
  let compHom :=
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hBC)
          (openSubsetHomOfLE_6_33_2 hCD)).hom.app ℱ).1.app
      (op (subspace_open_of_le hAB)))
  let comp :=
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hBC)
          (openSubsetHomOfLE_6_33_2 hCD)).symm.hom.app ℱ).1.app
      (op (subspace_open_of_le hAB)))
  have hforward :
      eAB.inv ≫ compHom ≫ eDirect.hom = eC.hom := by
    simpa [compHom, eAB, eC, eDirect] using
      openSubsetHomOfLE_forward_endpoint_top_section_compare hAB hBC hCD ℱ
  have hcompHom :
      compHom ≫ eDirect.hom = eAB.hom ≫ eC.hom := by
    -- Cancel the left comparison isomorphism from the normalized forward endpoint equality.
    simpa [Category.assoc] using congrArg (fun k ↦ eAB.hom ≫ k) hforward
  have hpost :
      compHom ≫ eDirect.hom ≫ eC.inv = eAB.hom := by
    -- Postcompose once with the inverse target comparison to isolate the represented source map.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eC.inv) hcompHom
  have hcomp :
      comp ≫ compHom = 𝟙 _ := by
    -- The two represented-open endpoint components are the inverse pair of the same
    -- pullback-comparison isomorphism.
    simpa [compHom, comp] using
      congrArg
        (fun k ↦ k.1.app (op (subspace_open_of_le hAB)))
        (Iso.inv_hom_id_app
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 hBC)
            (openSubsetHomOfLE_6_33_2 hCD))
          ℱ)
  -- Reassociate on the right-hand side, then collapse the inverse pair back to the identity.
  exact
    (calc
      comp ≫ eAB.hom = comp ≫ (compHom ≫ eDirect.hom ≫ eC.inv) := by
        rw [hpost]
      _ = (comp ≫ compHom) ≫ eDirect.hom ≫ eC.inv := by
        simp [Category.assoc]
      _ = eDirect.hom ≫ eC.inv := by
        rw [hcomp]
        rfl).symm

/-- Helper for Lemma 6.33.2: for a chain of ambient-open inclusions `A ⊆ B ⊆ C ⊆ D`, the direct
section comparison factors through the pullback-composition endpoint map and the two stagewise
section comparisons. -/
private theorem openSubsetHomOfLE_section_iso_forward_factorization
    {A B C D : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D)
    (ℱ : TopCat.Sheaf (Type u) (openSubsetSpace D)) :
    let eAB :=
      openSubsetHomOfLE_section_iso hAB hBC
        ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)
    let eC := openSubsetHomOfLE_section_iso (hAB.trans hBC) hCD ℱ
    let eDirect := openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ
    let comp :=
      (((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 hBC)
            (openSubsetHomOfLE_6_33_2 hCD)).symm.hom.app ℱ).1.app
          (op (subspace_open_of_le hAB)))
    eDirect.hom = comp ≫ eAB.hom ≫ eC.hom := by
  let eAB :=
    openSubsetHomOfLE_section_iso hAB hBC
      ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)
  let eC := openSubsetHomOfLE_section_iso (hAB.trans hBC) hCD ℱ
  let eDirect := openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ
  let comp :=
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hBC)
          (openSubsetHomOfLE_6_33_2 hCD)).symm.hom.app ℱ).1.app
      (op (subspace_open_of_le hAB)))
  have hendpoint : eDirect.hom ≫ eC.inv = comp ≫ eAB.hom := by
    -- Reuse the isolated endpoint comparison and then restore the local `let` notation.
    simpa [eAB, eC, eDirect, comp] using
      openSubsetHomOfLE_inverse_endpoint_top_section_compare hAB hBC hCD ℱ
  calc
    eDirect.hom = (eDirect.hom ≫ eC.inv) ≫ eC.hom := by
      simp [Category.assoc]
    _ = (comp ≫ eAB.hom) ≫ eC.hom := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eC.hom) hendpoint
    _ = comp ≫ eAB.hom ≫ eC.hom := by
      simp [Category.assoc]

/-- Helper for Lemma 6.33.2: the left outer inverse-endpoint component in the source-faithful
pullback-composition coherence equals the direct top-open comparison followed by the two inverse
section comparisons along `A ⊆ B ⊆ D`. -/
private theorem openSubsetHomOfLE_left_outer_endpoint_top_section_formula
    {A B C D : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D)
    (ℱ : TopCat.Sheaf (Type u) (openSubsetSpace D)) :
    let topDirect :=
      openSubsetHomOfLE_section_iso
        (show A ≤ A from le_rfl)
        (hAB.trans (hBC.trans hCD))
        ℱ
    let eDirect := openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ
    let topStage :=
      openSubsetHomOfLE_section_iso
        (show A ≤ A from le_rfl)
        hAB
        ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 (hBC.trans hCD))).obj ℱ)
    let comp :=
      (((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 hAB)
            (openSubsetHomOfLE_6_33_2 (hBC.trans hCD))).symm.hom.app ℱ).1.app
          (op (subspace_open_of_le (show A ≤ A from le_rfl))))
    comp = topDirect.hom ≫ eDirect.inv ≫ topStage.inv := by
  let topDirect :=
    openSubsetHomOfLE_section_iso
      (show A ≤ A from le_rfl)
      (hAB.trans (hBC.trans hCD))
      ℱ
  let eDirect := openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ
  let topStage :=
    openSubsetHomOfLE_section_iso
      (show A ≤ A from le_rfl)
      hAB
      ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 (hBC.trans hCD))).obj ℱ)
  let comp :=
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hAB)
          (openSubsetHomOfLE_6_33_2 (hBC.trans hCD))).symm.hom.app ℱ).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl))))
  have hfactor :
      topDirect.hom = comp ≫ topStage.hom ≫ eDirect.hom := by
    -- Specialize the already-packaged forward factorization to the chain `A ⊆ A ⊆ B ⊆ D`.
    simpa [topDirect, topStage, eDirect, comp] using
      openSubsetHomOfLE_section_iso_forward_factorization
        (hAB := (show A ≤ A from le_rfl))
        (hBC := hAB)
        (hCD := hBC.trans hCD)
        (ℱ := ℱ)
  -- Cancel the two comparison isomorphisms on the right to isolate the left outer endpoint.
  have hcancel :
      comp = comp ≫ topStage.hom ≫ eDirect.hom ≫ eDirect.inv ≫ topStage.inv := by
    simp
  have hrewrite :
      comp ≫ topStage.hom ≫ eDirect.hom ≫ eDirect.inv ≫ topStage.inv =
        topDirect.hom ≫ eDirect.inv ≫ topStage.inv := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ eDirect.inv ≫ topStage.inv) hfactor.symm
  exact hcancel.trans hrewrite

/-- Helper for Lemma 6.33.2: the right outer inverse-endpoint component in the source-faithful
pullback-composition coherence equals the direct top-open comparison followed by the inverse
section comparisons along `A ⊆ C ⊆ D`. -/
private theorem openSubsetHomOfLE_right_outer_endpoint_top_section_formula
    {A B C D : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D)
    (ℱ : TopCat.Sheaf (Type u) (openSubsetSpace D)) :
    let topDirect :=
      openSubsetHomOfLE_section_iso
        (show A ≤ A from le_rfl)
        (hAB.trans (hBC.trans hCD))
        ℱ
    let eC := openSubsetHomOfLE_section_iso (hAB.trans hBC) hCD ℱ
    let topStage :=
      openSubsetHomOfLE_section_iso
        (show A ≤ A from le_rfl)
        (hAB.trans hBC)
        ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)
    let comp :=
      (((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 (hAB.trans hBC))
            (openSubsetHomOfLE_6_33_2 hCD)).symm.hom.app ℱ).1.app
          (op (subspace_open_of_le (show A ≤ A from le_rfl))))
    comp = topDirect.hom ≫ eC.inv ≫ topStage.inv := by
  let topDirect :=
    openSubsetHomOfLE_section_iso
      (show A ≤ A from le_rfl)
      (hAB.trans (hBC.trans hCD))
      ℱ
  let eC := openSubsetHomOfLE_section_iso (hAB.trans hBC) hCD ℱ
  let topStage :=
    openSubsetHomOfLE_section_iso
      (show A ≤ A from le_rfl)
      (hAB.trans hBC)
      ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)
  let comp :=
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 (hAB.trans hBC))
          (openSubsetHomOfLE_6_33_2 hCD)).symm.hom.app ℱ).1.app
        (op (subspace_open_of_le (show A ≤ A from le_rfl))))
  have hfactor :
      topDirect.hom = comp ≫ topStage.hom ≫ eC.hom := by
    -- Specialize the forward factorization to the chain `A ⊆ A ⊆ C ⊆ D`.
    simpa [topDirect, topStage, eC, comp] using
      openSubsetHomOfLE_section_iso_forward_factorization
        (hAB := (show A ≤ A from le_rfl))
        (hBC := hAB.trans hBC)
        (hCD := hCD)
        (ℱ := ℱ)
  -- Cancel the two comparison isomorphisms on the right to isolate the right outer endpoint.
  have hcancel :
      comp = comp ≫ topStage.hom ≫ eC.hom ≫ eC.inv ≫ topStage.inv := by
    simp
  have hrewrite :
      comp ≫ topStage.hom ≫ eC.hom ≫ eC.inv ≫ topStage.inv =
        topDirect.hom ≫ eC.inv ≫ topStage.inv := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ eC.inv ≫ topStage.inv) hfactor.symm
  exact hcancel.trans hrewrite

/-- Helper for Lemma 6.33.2: for a chain of ambient-open inclusions `A ⊆ B ⊆ C ⊆ D`, the direct
section comparison from `A` to `D` factors through the left endpoint of the iterated pullback
comparison and the stage-`C` section comparison. -/
private theorem openSubsetHomOfLE_section_iso_forward_endpoint_compare
    {A B C D : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D)
    (ℱ : TopCat.Sheaf (Type u) (openSubsetSpace D)) :
    (openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ).hom ≫
      (openSubsetHomOfLE_section_iso (hAB.trans hBC) hCD ℱ).inv =
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hBC)
          (openSubsetHomOfLE_6_33_2 hCD)).symm.hom.app ℱ).1.app
        (op (subspace_open_of_le hAB))) ≫
      (openSubsetHomOfLE_section_iso hAB hBC
        ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).hom := by
  -- The endpoint comparison is exactly the isolated top-open inverse coherence statement.
  simpa using openSubsetHomOfLE_inverse_endpoint_top_section_compare hAB hBC hCD ℱ

/-- Helper for Lemma 6.33.2: for the same chain of ambient-open inclusions, the inverse endpoint
of the iterated pullback comparison recovers the right-hand section comparison. -/
private theorem openSubsetHomOfLE_section_iso_inverse_endpoint_compare
    {A B C D : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D)
    (ℱ : TopCat.Sheaf (Type u) (openSubsetSpace D)) :
    (openSubsetHomOfLE_section_iso hAB hBC
        ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)).inv ≫
      (((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 hBC)
          (openSubsetHomOfLE_6_33_2 hCD)).symm.inv.app ℱ).1.app
          (op (subspace_open_of_le hAB))) =
    (openSubsetHomOfLE_section_iso (hAB.trans hBC) hCD ℱ).hom ≫
      (openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ).inv := by
  -- Postcompose with the direct comparison and reduce to the already normalized forward endpoint.
  apply (cancel_mono (openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ).hom).1
  let eAB :=
    openSubsetHomOfLE_section_iso hAB hBC
      ((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hCD)).obj ℱ)
  let eC := openSubsetHomOfLE_section_iso (hAB.trans hBC) hCD ℱ
  let eDirect := openSubsetHomOfLE_section_iso hAB (hBC.trans hCD) ℱ
  let compHom :=
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hBC)
          (openSubsetHomOfLE_6_33_2 hCD)).symm.inv.app ℱ).1.app
      (op (subspace_open_of_le hAB)))
  let compInv :=
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hBC)
          (openSubsetHomOfLE_6_33_2 hCD)).symm.hom.app ℱ).1.app
      (op (subspace_open_of_le hAB)))
  have hstep : eDirect.hom ≫ eC.inv = compInv ≫ eAB.hom := by
    -- Reuse the forward endpoint normalization in the compact `let`-bound notation.
    simpa [eAB, eC, eDirect, compInv] using
      openSubsetHomOfLE_section_iso_forward_endpoint_compare hAB hBC hCD ℱ
  have hcomp : compHom ≫ compInv = 𝟙 _ := by
    -- The two endpoint components are inverse because they come from the same pullback-comparison
    -- isomorphism.
    simpa [compHom, compInv] using
      congrArg
        (fun k ↦ k.1.app (op (subspace_open_of_le hAB)))
        (Iso.hom_inv_id_app
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 hBC)
            (openSubsetHomOfLE_6_33_2 hCD))
          ℱ)
  have heAB : eAB.inv ≫ eAB.hom = 𝟙 _ := by
    -- The section comparison on the intermediate stage is an isomorphism.
    simp [eAB]
  have hmain :
      compHom ≫ eDirect.hom = compHom ≫ compInv ≫ eAB.hom ≫ eC.hom := by
    -- Insert the stage-`C` inverse and then replace the forward endpoint by `hstep`.
    have hinsert :
        compHom ≫ eDirect.hom = compHom ≫ (eDirect.hom ≫ eC.inv) ≫ eC.hom := by
      simp [Category.assoc, eC, eDirect]
    have hpost :
        compHom ≫ (eDirect.hom ≫ eC.inv) ≫ eC.hom =
          compHom ≫ compInv ≫ eAB.hom ≫ eC.hom := by
      change compHom ≫ (eDirect.hom ≫ eC.inv) ≫ eC.hom =
        compHom ≫ compInv ≫ eAB.hom ≫ eC.hom
      exact congrArg (fun k ↦ compHom ≫ k ≫ eC.hom) hstep
    exact hinsert.trans hpost
  calc
    eAB.inv ≫ compHom ≫ eDirect.hom
        = eAB.inv ≫ (compHom ≫ compInv ≫ eAB.hom ≫ eC.hom) := by
            simpa [Category.assoc] using congrArg (fun k ↦ eAB.inv ≫ k) hmain
    _ = (eAB.inv ≫ eAB.hom) ≫ eC.hom := by
          -- Collapse the endpoint comparison with its inverse before canceling the section iso.
          simpa [Category.assoc, heAB] using
            congrArg (fun k ↦ eAB.inv ≫ k ≫ eAB.hom ≫ eC.hom) hcomp
    _ = eC.hom := by
          simp [heAB]
    _ = (eC.hom ≫ eDirect.inv) ≫ eDirect.hom := by
          simp [eDirect, Category.assoc]

/-- Helper for Lemma 6.33.2: the restriction map from `W ∩ U i` to `W ∩ U i ∩ U j`
inside the local sheaf on `U i`. -/
private abbrev left_component_restriction
    (data : SheafOpenCoverGlueing U) (W : Opens X) (i j : ι) :
    (extended_local_sheaf data i).1.obj (op W) →
      (data.localSheaf i).1.obj (op (left_overlap_open W i j)) :=
  (extended_local_sheaf data i).1.map
    (homOfLE
      (show W ⊓ U i ⊓ U j ≤ W from by
        intro x hx
        exact hx.1.1)).op

/-- Helper for Lemma 6.33.2: the restriction map from `W ∩ U j` to `W ∩ U i ∩ U j`
inside the local sheaf on `U j`. -/
private abbrev right_component_restriction
    (data : SheafOpenCoverGlueing U) (W : Opens X) (i j : ι) :
    (extended_local_sheaf data j).1.obj (op W) →
      (data.localSheaf j).1.obj (op (right_overlap_open W i j)) :=
  (extended_local_sheaf data j).1.map
    (homOfLE
      (show W ⊓ U i ⊓ U j ≤ W from by
        intro x hx
        exact hx.1.1)).op

/-- Helper for Lemma 6.33.2: identifies a section of the left overlap pullback sheaf on the
explicit pair-open `W ∩ U i ∩ U j` with the corresponding section of `𝓕ᵢ`. -/
private noncomputable def left_overlap_section_iso
    (data : SheafOpenCoverGlueing U) (W : Opens X) (i j : ι) :
    (((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (data.localSheaf i)).1.obj
      (op (pair_overlap_open W i j))) ≅
    (data.localSheaf i).1.obj (op (left_overlap_open W i j)) :=
  -- Specialize the generic `openSubsetHomOfLE_6_33_2` transport to the left overlap inclusion
  -- `(U i ⊓ U j) ↪ U i`.
  openSubsetHomOfLE_section_iso
    (show W ⊓ U i ⊓ U j ≤ U i ⊓ U j from inf_le_inf inf_le_right le_rfl)
    inf_le_left
    (data.localSheaf i)

/-- Helper for Lemma 6.33.2: identifies a section of the right overlap pullback sheaf on the
explicit pair-open `W ∩ U i ∩ U j` with the corresponding section of `𝓕ⱼ`. -/
private noncomputable def right_overlap_section_iso
    (data : SheafOpenCoverGlueing U) (W : Opens X) (i j : ι) :
    (((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionRightInclusion (U i) (U j))).obj (data.localSheaf j)).1.obj
      (op (pair_overlap_open W i j))) ≅
    (data.localSheaf j).1.obj (op (right_overlap_open W i j)) :=
  -- This is the symmetric specialization to the right overlap inclusion `(U i ⊓ U j) ↪ U j`.
  openSubsetHomOfLE_section_iso
    (show W ⊓ U i ⊓ U j ≤ U i ⊓ U j from inf_le_inf inf_le_right le_rfl)
    inf_le_right
    (data.localSheaf j)

/-- Helper for Lemma 6.33.2: the concrete overlap section identifications commute with restriction
from `W` to a smaller ambient open `V`. -/
private theorem overlap_section_iso_naturality
    (data : SheafOpenCoverGlueing U) {V W : Opens X} (hVW : V ≤ W) (i j : ι) :
    ((((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (data.localSheaf i)).1.map
      (pair_overlap_open_hom hVW i j).op) ≫ (left_overlap_section_iso data V i j).hom =
      (left_overlap_section_iso data W i j).hom ≫
        (data.localSheaf i).1.map (left_overlap_open_hom hVW i j).op) ∧
    ((((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionRightInclusion (U i) (U j))).obj (data.localSheaf j)).1.map
      (pair_overlap_open_hom hVW i j).op) ≫ (right_overlap_section_iso data V i j).hom =
      (right_overlap_section_iso data W i j).hom ≫
        (data.localSheaf j).1.map (right_overlap_open_hom hVW i j).op) := by
  constructor
  · -- Specialize the generic naturality statement to the left overlap inclusion.
    simpa [left_overlap_section_iso, pair_overlap_open_hom, left_overlap_open_hom] using
      openSubsetHomOfLE_section_iso_naturality
        (hA₁ := show V ⊓ U i ⊓ U j ≤ U i ⊓ U j from
          inf_le_inf inf_le_right le_rfl)
        (hA₂ := show W ⊓ U i ⊓ U j ≤ U i ⊓ U j from
          inf_le_inf inf_le_right le_rfl)
        (h12 := by
          intro x hx
          exact ⟨⟨hVW hx.1.1, hx.1.2⟩, hx.2⟩)
        (hBC := inf_le_left)
        (ℱ := data.localSheaf i)
  · -- The right overlap is the symmetric specialization.
    simpa [right_overlap_section_iso, pair_overlap_open_hom, right_overlap_open_hom] using
      openSubsetHomOfLE_section_iso_naturality
        (hA₁ := show V ⊓ U i ⊓ U j ≤ U i ⊓ U j from
          inf_le_inf inf_le_right le_rfl)
        (hA₂ := show W ⊓ U i ⊓ U j ≤ U i ⊓ U j from
          inf_le_inf inf_le_right le_rfl)
        (h12 := by
          intro x hx
          exact ⟨⟨hVW hx.1.1, hx.1.2⟩, hx.2⟩)
        (hBC := inf_le_right)
        (ℱ := data.localSheaf j)

namespace BasisCover

/-- Helper for Lemma 6.33.2: if the actual pairwise intersection of the members of a basis cover
stays in the basis, view that intersection as a basis open. -/
private abbrev actual_intersection
    {B : Set (Opens X)} {U : BasisOpen B}
    (𝒰 : BasisCover B U)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (i j : 𝒰.ι) : BasisOpen B :=
  ⟨(𝒰.obj i).obj ⊓ (𝒰.obj j).obj, hInter i j⟩

/-- Helper for Lemma 6.33.2: the actual pairwise intersection basis open maps to the left member
of the pair. -/
private abbrev actual_intersection_left
    {B : Set (Opens X)} {U : BasisOpen B}
    (𝒰 : BasisCover B U)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (i j : 𝒰.ι) :
    actual_intersection 𝒰 hInter i j ⟶ 𝒰.obj i :=
  ⟨homOfLE inf_le_left⟩

/-- Helper for Lemma 6.33.2: the actual pairwise intersection basis open maps to the right member
of the pair. -/
private abbrev actual_intersection_right
    {B : Set (Opens X)} {U : BasisOpen B}
    (𝒰 : BasisCover B U)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (i j : 𝒰.ι) :
    actual_intersection 𝒰 hInter i j ⟶ 𝒰.obj j :=
  ⟨homOfLE inf_le_right⟩

/-- Helper for Lemma 6.33.2: on a basis cover whose actual pairwise intersections stay in the
basis, generic compatibility is equivalent to equality on those concrete intersections. -/
private theorem isCompatible_iff_actual_intersections
    {B : Set (Opens X)} {U : BasisOpen B}
    (𝒰 : BasisCover B U)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (F : Presheaf.{max u v} (BasisOpen B))
    (s : FamilyOfElementsOnObjects F 𝒰.obj) :
    s.IsCompatible ↔
      ∀ i j,
        F.map ((actual_intersection_left 𝒰 hInter i j).op) (s i) =
          F.map ((actual_intersection_right 𝒰 hInter i j).op) (s j) := by
  constructor
  · intro hs i j
    simpa using
      hs (actual_intersection 𝒰 hInter i j) i j
        (actual_intersection_left 𝒰 hInter i j)
        (actual_intersection_right 𝒰 hInter i j)
  · intro hs Z i j f g
    let h : Z ⟶ actual_intersection 𝒰 hInter i j :=
      ⟨homOfLE <| le_inf (leOfHom f.hom) (leOfHom g.hom)⟩
    have hf : f = h ≫ actual_intersection_left 𝒰 hInter i j := by
      apply ObjectProperty.hom_ext
      exact Subsingleton.elim _ _
    have hg : g = h ≫ actual_intersection_right 𝒰 hInter i j := by
      apply ObjectProperty.hom_ext
      exact Subsingleton.elim _ _
    calc
      F.map f.op (s i)
          = F.map h.op (F.map ((actual_intersection_left 𝒰 hInter i j).op) (s i)) := by
              rw [hf, op_comp, FunctorToTypes.map_comp_apply]
      _ = F.map h.op (F.map ((actual_intersection_right 𝒰 hInter i j).op) (s j)) := by
            rw [hs i j]
      _ = F.map g.op (s j) := by
            rw [hg, op_comp, FunctorToTypes.map_comp_apply]

/-- Helper for Lemma 6.33.2: package actual pairwise intersections as a singleton overlap cover. -/
private def singleton_actual_intersection_cover
    {B : Set (Opens X)} {U : BasisOpen B}
    (𝒰 : BasisCover B U)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B) :
    BasisIntersectionCover B 𝒰 where
  κ _ _ := PUnit
  obj i j _ := actual_intersection 𝒰 hInter i j
  left i j _ := actual_intersection_left 𝒰 hInter i j
  right i j _ := actual_intersection_right 𝒰 hInter i j
  iUnion_eq i j := by
    ext x
    simp

/-- Helper for Lemma 6.33.2: for the singleton actual-intersection cover, the basis sheaf
condition is exactly unique gluing for compatible families. -/
private theorem hasSheafCondition_iff_uniqueGluing_actual_intersections
    {B : Set (Opens X)} {U : BasisOpen B}
    (𝒰 : BasisCover B U)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (F : Presheaf.{max u v} (BasisOpen B)) :
    BasisCover.HasSheafCondition F 𝒰 (singleton_actual_intersection_cover 𝒰 hInter) ↔
      ∀ s : FamilyOfElementsOnObjects F 𝒰.obj,
        s.IsCompatible →
          ∃! t : F.obj (op U), ∀ i, F.map (𝒰.hom i).op t = s i := by
  constructor
  · intro h s hs
    exact h s (fun i j _ ↦ (isCompatible_iff_actual_intersections 𝒰 hInter F s).1 hs i j)
  · intro h s hs
    exact h s ((isCompatible_iff_actual_intersections 𝒰 hInter F s).2 (fun i j ↦ hs i j PUnit.unit))

end BasisCover

/-- Helper for Lemma 6.33.2: to prove the chosen-chart basis presheaf is a sheaf on the basis, it
is enough to prove unique gluing on a cofinal system of covers whose actual pairwise intersections
stay inside the basis. -/
private theorem basisPresheaf_isSheaf_iff_uniqueGluing_on_cofinal_basis_covers_local
    {B : Set (Opens X)}
    (hB : Opens.IsBasis B)
    (C : ∀ U : BasisOpen B, Set (BasisCover B U)) (hC : BasisCover.IsCofinalSystem C)
    (hInter :
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ C U →
        ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (F : Presheaf.{max u v} (BasisOpen B)) :
    Presheaf.IsSheaf (basisGrothendieckTopology B hB) F ↔
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ C U →
        ∀ s : FamilyOfElementsOnObjects F 𝒰.obj,
          s.IsCompatible →
            ∃! t : F.obj (op U), ∀ i, F.map (𝒰.hom i).op t = s i := by
  let hInterC :
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ C U → BasisIntersectionCover B 𝒰 :=
    fun {U} 𝒰 h𝒰 ↦ BasisCover.singleton_actual_intersection_cover 𝒰 (hInter 𝒰 h𝒰)
  constructor
  · intro hSheaf U 𝒰 h𝒰 s hs
    have hCondition :=
      (basisPresheaf_isSheaf_iff_hasSheafCondition_on_cofinalSystem F C hInterC hB hC).1 hSheaf
    exact
      (BasisCover.hasSheafCondition_iff_uniqueGluing_actual_intersections 𝒰 (hInter 𝒰 h𝒰) F).1
        (hCondition 𝒰 h𝒰) s hs
  · intro hUnique
    refine (basisPresheaf_isSheaf_iff_hasSheafCondition_on_cofinalSystem F C hInterC hB hC).2 ?_
    intro U 𝒰 h𝒰
    exact
      (BasisCover.hasSheafCondition_iff_uniqueGluing_actual_intersections 𝒰 (hInter 𝒰 h𝒰) F).2
        (hUnique 𝒰 h𝒰)

/-- Helper for Lemma 6.33.2: the basis of opens contained in one member of the cover. -/
private def coverSubordinateOpens
    : Set (Opens X) :=
  { W | ∃ i, W ≤ U i }

/-- Helper for Lemma 6.33.2: the subordinate opens form a topological basis. -/
private theorem cover_subordinate_opens_isBasis
    (data : SheafOpenCoverGlueing U) :
    Opens.IsBasis (coverSubordinateOpens (U := U)) := by
  -- Follow the second source proof: refine any neighborhood `V` of `x` to `V ∩ U i`, where `U i`
  -- is a cover member containing `x`.
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨i, hxi⟩ := data.isCover.exists_mem x
  refine ⟨V ⊓ U i, ?_, ?_, inf_le_left⟩
  · exact ⟨i, inf_le_right⟩
  · exact ⟨hx, hxi⟩

/-- Helper for Lemma 6.33.2: choose one chart containing a subordinate basis open. -/
private noncomputable abbrev chosen_chart
    (W : BasisOpen (coverSubordinateOpens (U := U))) : ι :=
  Classical.choose W.property

/-- Helper for Lemma 6.33.2: the chosen chart indeed contains the subordinate basis open. -/
private theorem chosen_chart_le
    (W : BasisOpen (coverSubordinateOpens (U := U))) :
    W.obj ≤ U (chosen_chart W) :=
  Classical.choose_spec W.property

/-- Helper for Lemma 6.33.2: if `W` is contained in both `U i` and `U j`, then it is contained in
their overlap. -/
private def subset_overlap_le
    {W : Opens X} {i j : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j) :
    W ≤ U i ⊓ U j := fun _ hx ↦ ⟨hWi hx, hWj hx⟩

/-- Helper for Lemma 6.33.2: if `W` is contained in three cover members, then it is contained in
their triple overlap. -/
private theorem subset_triple_overlap_le
    {W : Opens X} {i j k : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j) (hWk : W ≤ U k) :
    W ≤ U i ⊓ U j ⊓ U k := by
  -- Build the triple-overlap inclusion pointwise from the three ambient containments.
  intro x hx
  exact ⟨⟨hWi hx, hWj hx⟩, hWk hx⟩

/-- Helper for Lemma 6.33.2: the left pair inclusion followed by the left overlap inclusion is the
direct first triple-overlap inclusion. -/
@[simp] private theorem openSubsetTripleToPairLeft_comp_intersectionLeft
    (V W Z : Opens X) :
    openSubsetTripleToPairLeftInclusion V W Z ≫ openSubsetIntersectionLeftInclusion V W =
      openSubsetTripleFirstInclusion V W Z :=
  rfl

/-- Helper for Lemma 6.33.2: the left pair inclusion followed by the right overlap inclusion is
the direct second triple-overlap inclusion. -/
@[simp] private theorem openSubsetTripleToPairLeft_comp_intersectionRight
    (V W Z : Opens X) :
    openSubsetTripleToPairLeftInclusion V W Z ≫ openSubsetIntersectionRightInclusion V W =
      openSubsetTripleSecondInclusion V W Z :=
  rfl

/-- Helper for Lemma 6.33.2: the center pair inclusion followed by the left overlap inclusion is
the direct second triple-overlap inclusion. -/
@[simp] private theorem openSubsetTripleToPairCenter_comp_intersectionLeft
    (V W Z : Opens X) :
    openSubsetTripleToPairCenterInclusion V W Z ≫ openSubsetIntersectionLeftInclusion W Z =
      openSubsetTripleSecondInclusion V W Z :=
  rfl

/-- Helper for Lemma 6.33.2: the center pair inclusion followed by the right overlap inclusion is
the direct third triple-overlap inclusion. -/
@[simp] private theorem openSubsetTripleToPairCenter_comp_intersectionRight
    (V W Z : Opens X) :
    openSubsetTripleToPairCenterInclusion V W Z ≫ openSubsetIntersectionRightInclusion W Z =
      openSubsetTripleThirdInclusion V W Z :=
  rfl

/-- Helper for Lemma 6.33.2: the outer pair inclusion followed by the left overlap inclusion is
the direct first triple-overlap inclusion. -/
@[simp] private theorem openSubsetTripleToPairOuter_comp_intersectionLeft
    (V W Z : Opens X) :
    openSubsetTripleToPairOuterInclusion V W Z ≫ openSubsetIntersectionLeftInclusion V Z =
      openSubsetTripleFirstInclusion V W Z :=
  rfl

/-- Helper for Lemma 6.33.2: the outer pair inclusion followed by the right overlap inclusion is
the direct third triple-overlap inclusion. -/
@[simp] private theorem openSubsetTripleToPairOuter_comp_intersectionRight
    (V W Z : Opens X) :
    openSubsetTripleToPairOuterInclusion V W Z ≫ openSubsetIntersectionRightInclusion V Z =
      openSubsetTripleThirdInclusion V W Z :=
  rfl

/-- Helper for Lemma 6.33.2: compare the two chart descriptions of sections over a subordinate
open `W`. -/
private noncomputable def subset_chart_iso
    (data : SheafOpenCoverGlueing U) {W : Opens X} {i j : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j) :
    (data.localSheaf i).1.obj (op (subspace_open_of_le hWi)) ≅
      (data.localSheaf j).1.obj (op (subspace_open_of_le hWj)) := by
  -- Restrict both local sheaves to `W` inside the overlap `U i ∩ U j`, then insert the given
  -- overlap isomorphism in the middle.
  let hWij := subset_overlap_le (U := U) hWi hWj
  exact (openSubsetHomOfLE_section_iso hWij inf_le_left (data.localSheaf i)).symm ≪≫
    (((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).mapIso
      (data.overlapIso i j)).app (op (subspace_open_of_le hWij))) ≪≫
    (openSubsetHomOfLE_section_iso hWij inf_le_right (data.localSheaf j))

/-- Helper for Lemma 6.33.2: the chart-change isomorphisms commute with restriction to a smaller
subordinate open. -/
private theorem subset_chart_iso_naturality
    (data : SheafOpenCoverGlueing U) {V W : Opens X} {i j : ι}
    (hVW : V ≤ W)
    (hVi : V ≤ U i) (hVj : V ≤ U j)
    (hWi : W ≤ U i) (hWj : W ≤ U j) :
    (data.localSheaf i).1.map (subspace_open_hom hVi hWi hVW).op ≫
      (subset_chart_iso data hVi hVj).hom =
    (subset_chart_iso data hWi hWj).hom ≫
      (data.localSheaf j).1.map (subspace_open_hom hVj hWj hVW).op := by
  -- Route correction: the basis route only needs restriction naturality of the chosen-chart
  -- comparison, and this can be obtained directly from the generic subspace comparison plus the
  -- naturality of `data.overlapIso`.
  let hVij := subset_overlap_le (U := U) hVi hVj
  let hWij := subset_overlap_le (U := U) hWi hWj
  let eLiV := openSubsetHomOfLE_section_iso hVij inf_le_left (data.localSheaf i)
  let eLiW := openSubsetHomOfLE_section_iso hWij inf_le_left (data.localSheaf i)
  let eRjV := openSubsetHomOfLE_section_iso hVij inf_le_right (data.localSheaf j)
  let eRjW := openSubsetHomOfLE_section_iso hWij inf_le_right (data.localSheaf j)
  let pairHom : subspace_open_of_le hVij ⟶ subspace_open_of_le hWij :=
    subspace_open_hom hVij hWij hVW
  let overlapIsoSections :
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (data.localSheaf i)).1 ≅
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))).obj (data.localSheaf j)).1 :=
    (TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).mapIso (data.overlapIso i j)
  have hmapi :
      subspace_open_hom (hVij.trans inf_le_left) (hWij.trans inf_le_left) hVW =
        subspace_open_hom hVi hWi hVW :=
    Subsingleton.elim _ _
  have hmapj :
      subspace_open_hom (hVij.trans inf_le_right) (hWij.trans inf_le_right) hVW =
        subspace_open_hom hVj hWj hVW :=
    Subsingleton.elim _ _
  have hleft :=
    openSubsetHomOfLE_section_iso_naturality
      (hA₁ := hVij) (hA₂ := hWij) (h12 := hVW) (hBC := inf_le_left)
      (ℱ := data.localSheaf i)
  have hright :=
    openSubsetHomOfLE_section_iso_naturality
      (hA₁ := hVij) (hA₂ := hWij) (h12 := hVW) (hBC := inf_le_right)
      (ℱ := data.localSheaf j)
  have hleft' :
      (data.localSheaf i).1.map (subspace_open_hom hVi hWi hVW).op ≫ eLiV.inv =
        eLiW.inv ≫
          (((TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (data.localSheaf i)).1.map
              pairHom.op) := by
    -- Cancel the right-hand comparison isomorphism and rewrite using the generic naturality
    -- statement specialized to the left overlap inclusion.
    rw [← cancel_mono eLiV.hom]
    simp [Category.assoc, eLiV, eLiW, pairHom, hleft, hmapi]
  have hnat := overlapIsoSections.hom.naturality pairHom.op
  calc
    (data.localSheaf i).1.map (subspace_open_hom hVi hWi hVW).op ≫
        (subset_chart_iso data hVi hVj).hom
        =
      (data.localSheaf i).1.map (subspace_open_hom hVi hWi hVW).op ≫ eLiV.inv ≫
        overlapIsoSections.hom.app (op (subspace_open_of_le hVij)) ≫ eRjV.hom := by
          rfl
    _ = eLiW.inv ≫
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (data.localSheaf i)).1.map
            pairHom.op) ≫
        overlapIsoSections.hom.app (op (subspace_open_of_le hVij)) ≫ eRjV.hom := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ overlapIsoSections.hom.app (op (subspace_open_of_le hVij)) ≫ eRjV.hom)
              hleft'
    _ = eLiW.inv ≫
        overlapIsoSections.hom.app (op (subspace_open_of_le hWij)) ≫
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))).obj (data.localSheaf j)).1.map
            pairHom.op) ≫ eRjV.hom := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ eLiW.inv ≫ k ≫ eRjV.hom) hnat
    _ = eLiW.inv ≫
        overlapIsoSections.hom.app (op (subspace_open_of_le hWij)) ≫ eRjW.hom ≫
          (data.localSheaf j).1.map (subspace_open_hom hVj hWj hVW).op := by
          simpa [Category.assoc, hmapj] using
            congrArg
              (fun k ↦ eLiW.inv ≫ overlapIsoSections.hom.app (op (subspace_open_of_le hWij)) ≫ k)
              hright
    _ = (subset_chart_iso data hWi hWj).hom ≫
        (data.localSheaf j).1.map (subspace_open_hom hVj hWj hVW).op := by
          convert rfl

/-- Helper for Lemma 6.33.2: if a subordinate basis open `V` sits inside a larger subordinate
basis open `W`, then restricting inside the chosen chart of `W` commutes with transport to any
fixed chart containing `W`. -/
private theorem chosen_chart_transport_naturality
    (data : SheafOpenCoverGlueing U)
    {V W : BasisOpen (coverSubordinateOpens (U := U))}
    (hVW : V.obj ≤ W.obj) {j : ι} (hWj : W.obj ≤ U j) :
    let i := chosen_chart W
    let hWi : W.obj ≤ U i := chosen_chart_le W
    (data.localSheaf i).1.map (subspace_open_hom (hVW.trans hWi) hWi hVW).op ≫
      (subset_chart_iso data (hVW.trans hWi) (hVW.trans hWj)).hom =
    (subset_chart_iso data hWi hWj).hom ≫
      (data.localSheaf j).1.map (subspace_open_hom (hVW.trans hWj) hWj hVW).op := by
  -- Specialize the ambient-open naturality statement to the chosen chart of the larger basis open.
  simpa using
    (subset_chart_iso_naturality data (hVW := hVW)
      (hVi := hVW.trans (chosen_chart_le W))
      (hVj := hVW.trans hWj)
      (hWi := chosen_chart_le W)
      (hWj := hWj))

/-- Helper for Lemma 6.33.2: transporting a basis-cover member into a fixed chart commutes with
restriction along any refinement morphism of cover members. -/
private theorem basis_cover_member_transport_naturality
    (data : SheafOpenCoverGlueing U)
    {W0 : BasisOpen (coverSubordinateOpens (U := U))}
    (𝒰 : BasisCover (coverSubordinateOpens (U := U)) W0)
    (i : 𝒰.ι)
    {Z : BasisOpen (coverSubordinateOpens (U := U))}
    (k : Z ⟶ 𝒰.obj i) :
    (data.localSheaf (chosen_chart (𝒰.obj i))).1.map
        (subspace_open_hom
          (k.hom.le.trans (chosen_chart_le (𝒰.obj i)))
          (chosen_chart_le (𝒰.obj i))
          k.hom.le).op ≫
      (subset_chart_iso data
        (k.hom.le.trans (chosen_chart_le (𝒰.obj i)))
        (k.hom.le.trans ((𝒰.hom i).hom.le.trans (chosen_chart_le W0)))).hom =
    (subset_chart_iso data
      (chosen_chart_le (𝒰.obj i))
      ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))).hom ≫
      (data.localSheaf (chosen_chart W0)).1.map
        (subspace_open_hom
          (k.hom.le.trans ((𝒰.hom i).hom.le.trans (chosen_chart_le W0)))
          ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))
          k.hom.le).op := by
  -- This is the fixed-chart specialization of the generic chosen-chart transport square, with the
  -- target chart taken to be the chosen chart of the ambient basis open `W0`.
  simpa using
    (chosen_chart_transport_naturality data
      (V := Z)
      (W := 𝒰.obj i)
      (hVW := k.hom.le)
      (j := chosen_chart W0)
      (hWj := (𝒰.hom i).hom.le.trans (chosen_chart_le W0)))

/-- Helper for Lemma 6.33.2: equality of sheaf morphisms yields equality on sections over any
chosen open. -/
private theorem sheaf_hom_app_congr
    {Y : TopCat} {F G : Y.Sheaf (Type u)} {V : Opens Y} {α β : F ⟶ G}
    (h : α = β) :
    α.hom.app (op V) = β.hom.app (op V) := by
  -- Componentwise equality is obtained by rewriting the morphism equality itself.
  cases h
  rfl

/-- Helper for Lemma 6.33.2: the chart-change isomorphisms compose transitively on a subordinate
open lying in three cover members. -/
private theorem subset_chart_iso_trans_normalized
    (data : SheafOpenCoverGlueing U) {W : Opens X} {i j k : ι}
    (hWijk : W ≤ U i ⊓ U j ⊓ U k) :
    ((((TopCat.Sheaf.pullbackComp
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
          (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app
          (data.localSheaf i)).1.app
        (op (subspace_open_of_le hWijk))) ≫
      ((((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).mapIso
          (data.overlapIso i j)).hom).1.app
        (op (subspace_open_of_le hWijk))) ≫
      (((TopCat.Sheaf.pullbackComp
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U i) (U j))).symm.inv.app
          (data.localSheaf j)).1.app
        (op (subspace_open_of_le hWijk)))) ≫
      ((((TopCat.Sheaf.pullbackComp
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app
          (data.localSheaf j)).1.app
        (op (subspace_open_of_le hWijk))) ≫
      ((((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).mapIso
          (data.overlapIso j k)).hom).1.app
        (op (subspace_open_of_le hWijk))) ≫
      (((TopCat.Sheaf.pullbackComp
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U j) (U k))).symm.inv.app
          (data.localSheaf k)).1.app
        (op (subspace_open_of_le hWijk)))) =
    (((TopCat.Sheaf.pullbackComp
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app
          (data.localSheaf i)).1.app
        (op (subspace_open_of_le hWijk))) ≫
      ((((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).mapIso
          (data.overlapIso i k)).hom).1.app
        (op (subspace_open_of_le hWijk))) ≫
      (((TopCat.Sheaf.pullbackComp
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U i) (U k))).symm.inv.app
          (data.localSheaf k)).1.app
        (op (subspace_open_of_le hWijk))) := by
  -- Evaluate the cocycle condition on the explicit subordinate triple-overlap open, but keep the
  -- cocycle itself at the morphism level until the final application of `sheaf_hom_app_congr`.
  let left12 :
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleFirstInclusion (U i) (U j) (U k))).obj (data.localSheaf i)) ⟶
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleSecondInclusion (U i) (U j) (U k))).obj (data.localSheaf j)) :=
    (TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app (data.localSheaf i) ≫
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).mapIso
          (data.overlapIso i j)).hom ≫
      (TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
        (openSubsetIntersectionRightInclusion (U i) (U j))).symm.inv.app (data.localSheaf j)
  let left23 :
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleSecondInclusion (U i) (U j) (U k))).obj (data.localSheaf j)) ⟶
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleThirdInclusion (U i) (U j) (U k))).obj (data.localSheaf k)) :=
    (TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app (data.localSheaf j) ≫
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).mapIso
          (data.overlapIso j k)).hom ≫
      (TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionRightInclusion (U j) (U k))).symm.inv.app (data.localSheaf k)
  let left13 :
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleFirstInclusion (U i) (U j) (U k))).obj (data.localSheaf i)) ⟶
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleThirdInclusion (U i) (U j) (U k))).obj (data.localSheaf k)) :=
    (TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app (data.localSheaf i) ≫
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).mapIso
          (data.overlapIso i k)).hom ≫
      (TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionRightInclusion (U i) (U k))).symm.inv.app (data.localSheaf k)
  have hc : left12 ≫ left23 = left13 := by
    -- This is exactly the cocycle axiom, rewritten using the explicit morphism-level abbreviations.
    simpa [left12, left23, left13] using data.cocycle i j k
  -- Now evaluate that morphism equality on the chosen subordinate triple-overlap open.
  simpa [left12, left23, left13, Category.assoc] using
    sheaf_hom_app_congr (V := subspace_open_of_le hWijk) hc

set_option maxRecDepth 4096
/-- Helper for Lemma 6.33.2: the chart-change isomorphisms compose transitively on a subordinate
open lying in three cover members. -/
private theorem subset_chart_iso_trans
    (data : SheafOpenCoverGlueing U) {W : Opens X} {i j k : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j) (hWk : W ≤ U k) :
    (subset_chart_iso data hWi hWj).hom ≫
        (subset_chart_iso data hWj hWk).hom =
      (subset_chart_iso data hWi hWk).hom := by
  -- Route correction: we prove transitivity by conjugating all three chart changes to the common
  -- triple-overlap section spaces, applying the normalized cocycle there, and cancelling the
  -- direct first/second/third comparison isomorphisms.
  let hWijk : W ≤ U i ⊓ U j ⊓ U k := subset_triple_overlap_le (U := U) hWi hWj hWk
  let directFirst :
      (((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleFirstInclusion (U i) (U j) (U k))).obj (data.localSheaf i)).1.obj
        (op (subspace_open_of_le hWijk))) ≅
      (data.localSheaf i).1.obj (op (subspace_open_of_le hWi)) :=
    openSubsetHomOfLE_section_iso
      hWijk
      (show U i ⊓ U j ⊓ U k ≤ U i from le_trans inf_le_left inf_le_left)
      (data.localSheaf i)
  let directSecond :
      (((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleSecondInclusion (U i) (U j) (U k))).obj (data.localSheaf j)).1.obj
        (op (subspace_open_of_le hWijk))) ≅
      (data.localSheaf j).1.obj (op (subspace_open_of_le hWj)) :=
    openSubsetHomOfLE_section_iso
      hWijk
      (show U i ⊓ U j ⊓ U k ≤ U j from le_trans inf_le_left inf_le_right)
      (data.localSheaf j)
  let directThird :
      (((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleThirdInclusion (U i) (U j) (U k))).obj (data.localSheaf k)).1.obj
        (op (subspace_open_of_le hWijk))) ≅
      (data.localSheaf k).1.obj (op (subspace_open_of_le hWk)) :=
    openSubsetHomOfLE_section_iso
      hWijk
      (show U i ⊓ U j ⊓ U k ≤ U k from inf_le_right)
      (data.localSheaf k)
  let left12 :
      (((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleFirstInclusion (U i) (U j) (U k))).obj (data.localSheaf i)).1.obj
        (op (subspace_open_of_le hWijk))) →
      (((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleSecondInclusion (U i) (U j) (U k))).obj (data.localSheaf j)).1.obj
        (op (subspace_open_of_le hWijk))) :=
    (((TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app
        (data.localSheaf i)).1.app
      (op (subspace_open_of_le hWijk))) ≫
    ((((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).mapIso
        (data.overlapIso i j)).hom).1.app
      (op (subspace_open_of_le hWijk))) ≫
    (((TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
        (openSubsetIntersectionRightInclusion (U i) (U j))).symm.inv.app
        (data.localSheaf j)).1.app
      (op (subspace_open_of_le hWijk)))
  let left23 :
      (((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleSecondInclusion (U i) (U j) (U k))).obj (data.localSheaf j)).1.obj
        (op (subspace_open_of_le hWijk))) →
      (((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleThirdInclusion (U i) (U j) (U k))).obj (data.localSheaf k)).1.obj
        (op (subspace_open_of_le hWijk))) :=
    (((TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app
        (data.localSheaf j)).1.app
      (op (subspace_open_of_le hWijk))) ≫
    ((((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).mapIso
        (data.overlapIso j k)).hom).1.app
      (op (subspace_open_of_le hWijk))) ≫
    (((TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionRightInclusion (U j) (U k))).symm.inv.app
        (data.localSheaf k)).1.app
      (op (subspace_open_of_le hWijk)))
  let left13 :
      (((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleFirstInclusion (U i) (U j) (U k))).obj (data.localSheaf i)).1.obj
        (op (subspace_open_of_le hWijk))) →
      (((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleThirdInclusion (U i) (U j) (U k))).obj (data.localSheaf k)).1.obj
        (op (subspace_open_of_le hWijk))) :=
    (((TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app
        (data.localSheaf i)).1.app
      (op (subspace_open_of_le hWijk))) ≫
    ((((TopCat.Sheaf.pullback (Type u)
        (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).mapIso
        (data.overlapIso i k)).hom).1.app
      (op (subspace_open_of_le hWijk))) ≫
    (((TopCat.Sheaf.pullbackComp
        (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionRightInclusion (U i) (U k))).symm.inv.app
        (data.localSheaf k)).1.app
      (op (subspace_open_of_le hWijk)))
  have h12 :
      directFirst.hom ≫ (subset_chart_iso data hWi hWj).hom ≫ directSecond.inv = left12 := by
    let eLeft :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (data.localSheaf i)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj)))) ≅
        (data.localSheaf i).1.obj (op (subspace_open_of_le hWi)) :=
      openSubsetHomOfLE_section_iso
        (subset_overlap_le (U := U) hWi hWj)
        inf_le_left
        (data.localSheaf i)
    let eRight :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))).obj (data.localSheaf j)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj)))) ≅
        (data.localSheaf j).1.obj (op (subspace_open_of_le hWj)) :=
      openSubsetHomOfLE_section_iso
        (subset_overlap_le (U := U) hWi hWj)
        inf_le_right
        (data.localSheaf j)
    let ePairLeft :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).obj
            ((TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionLeftInclusion (U i) (U j))).obj
                (data.localSheaf i))).1.obj
          (op (subspace_open_of_le hWijk))) ≅
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U j))).obj
            (data.localSheaf i)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj)))) :=
      openSubsetHomOfLE_section_iso
        hWijk
        (show U i ⊓ U j ⊓ U k ≤ U i ⊓ U j from by
          intro x hx
          exact hx.1)
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U j))).obj
            (data.localSheaf i))
    let ePairRight :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).obj
            ((TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionRightInclusion (U i) (U j))).obj
                (data.localSheaf j))).1.obj
          (op (subspace_open_of_le hWijk))) ≅
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))).obj
            (data.localSheaf j)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj)))) :=
      openSubsetHomOfLE_section_iso
        hWijk
        (show U i ⊓ U j ⊓ U k ≤ U i ⊓ U j from by
          intro x hx
          exact hx.1)
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))).obj
            (data.localSheaf j))
    have hleft :
        directFirst.hom ≫ eLeft.inv =
          (((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
                (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app
              (data.localSheaf i)).1.app
            (op (subspace_open_of_le hWijk))) ≫
            ePairLeft.hom := by
      -- Normalize the left endpoint to the direct triple-to-pair pullback comparison.
      simpa [directFirst, eLeft, ePairLeft, Category.assoc] using
        openSubsetHomOfLE_section_iso_forward_endpoint_compare
          hWijk
          (show U i ⊓ U j ⊓ U k ≤ U i ⊓ U j from by
            intro x hx
            exact hx.1)
          inf_le_left
          (data.localSheaf i)
    have hmiddle :
        ePairLeft.hom ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).map
              (data.overlapIso i j).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj))) ≫
            ePairRight.inv =
          (((TopCat.Sheaf.pullback (Type u)
                (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
              (data.overlapIso i j).hom).hom.app
            (op (subspace_open_of_le hWijk))) := by
      -- Transport the overlap isomorphism to the triple-overlap owner once.
      simpa [ePairLeft, ePairRight] using
        openSubsetHomOfLE_section_iso_map_compare
          hWijk
          (show U i ⊓ U j ⊓ U k ≤ U i ⊓ U j from by
            intro x hx
            exact hx.1)
          (data.overlapIso i j).hom
    have hright :
        eRight.hom ≫ directSecond.inv =
          ePairRight.inv ≫
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionRightInclusion (U i) (U j))).symm.inv.app
                (data.localSheaf j)).1.app
              (op (subspace_open_of_le hWijk))) := by
      -- Normalize the right endpoint symmetrically.
      simpa [directSecond, eRight, ePairRight, Category.assoc] using
        (openSubsetHomOfLE_section_iso_inverse_endpoint_compare
          hWijk
          (show U i ⊓ U j ⊓ U k ≤ U i ⊓ U j from by
            intro x hx
            exact hx.1)
          inf_le_right
          (data.localSheaf j)).symm
    -- Assemble the left endpoint, transported overlap map, and right endpoint.
    have hstep1 :
        directFirst.hom ≫ (subset_chart_iso data hWi hWj).hom ≫ directSecond.inv =
          directFirst.hom ≫ eLeft.inv ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).map
              (data.overlapIso i j).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj))) ≫
            eRight.hom ≫ directSecond.inv := by
      rfl
    have hstep2 :
        directFirst.hom ≫ eLeft.inv ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).map
              (data.overlapIso i j).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj))) ≫
            eRight.hom ≫ directSecond.inv =
          (((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
                (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app
              (data.localSheaf i)).1.app
            (op (subspace_open_of_le hWijk))) ≫
              ePairLeft.hom ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).map
                (data.overlapIso i j).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj))) ≫
              eRight.hom ≫ directSecond.inv := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            t ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).map
                (data.overlapIso i j).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj))) ≫
              eRight.hom ≫ directSecond.inv)
          hleft
    have hstep3 :
        (((TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
              (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app
            (data.localSheaf i)).1.app
          (op (subspace_open_of_le hWijk))) ≫
            ePairLeft.hom ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).map
              (data.overlapIso i j).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj))) ≫
            eRight.hom ≫ directSecond.inv =
          (((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
                (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app
              (data.localSheaf i)).1.app
            (op (subspace_open_of_le hWijk))) ≫
              ePairLeft.hom ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).map
                (data.overlapIso i j).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj))) ≫
              ePairRight.inv ≫
              (((TopCat.Sheaf.pullbackComp (A := Type u)
                    (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
                    (openSubsetIntersectionRightInclusion (U i) (U j))).symm.inv.app
                  (data.localSheaf j)).1.app
                (op (subspace_open_of_le hWijk))) := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app
                (data.localSheaf i)).1.app
              (op (subspace_open_of_le hWijk))) ≫
              ePairLeft.hom ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).map
                (data.overlapIso i j).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj))) ≫ t)
          hright
    have hstep4 :
        (((TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
              (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app
            (data.localSheaf i)).1.app
          (op (subspace_open_of_le hWijk))) ≫
            ePairLeft.hom ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).map
              (data.overlapIso i j).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWj))) ≫
            ePairRight.inv ≫
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionRightInclusion (U i) (U j))).symm.inv.app
                (data.localSheaf j)).1.app
              (op (subspace_open_of_le hWijk))) = left12 := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app
                (data.localSheaf i)).1.app
              (op (subspace_open_of_le hWijk))) ≫ t ≫
              (((TopCat.Sheaf.pullbackComp (A := Type u)
                    (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
                    (openSubsetIntersectionRightInclusion (U i) (U j))).symm.inv.app
                  (data.localSheaf j)).1.app
                (op (subspace_open_of_le hWijk))))
          hmiddle
    exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))
  have h23 :
      directSecond.hom ≫ (subset_chart_iso data hWj hWk).hom ≫ directThird.inv = left23 := by
    let eLeft :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U j) (U k))).obj (data.localSheaf j)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk)))) ≅
        (data.localSheaf j).1.obj (op (subspace_open_of_le hWj)) :=
      openSubsetHomOfLE_section_iso
        (subset_overlap_le (U := U) hWj hWk)
        inf_le_left
        (data.localSheaf j)
    let eRight :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U j) (U k))).obj (data.localSheaf k)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk)))) ≅
        (data.localSheaf k).1.obj (op (subspace_open_of_le hWk)) :=
      openSubsetHomOfLE_section_iso
        (subset_overlap_le (U := U) hWj hWk)
        inf_le_right
        (data.localSheaf k)
    let ePairLeft :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).obj
            ((TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionLeftInclusion (U j) (U k))).obj
                (data.localSheaf j))).1.obj
          (op (subspace_open_of_le hWijk))) ≅
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U j) (U k))).obj
            (data.localSheaf j)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk)))) :=
      openSubsetHomOfLE_section_iso
        hWijk
        (show U i ⊓ U j ⊓ U k ≤ U j ⊓ U k from by
          intro x hx
          exact ⟨hx.1.2, hx.2⟩)
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U j) (U k))).obj
            (data.localSheaf j))
    let ePairRight :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).obj
            ((TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionRightInclusion (U j) (U k))).obj
                (data.localSheaf k))).1.obj
          (op (subspace_open_of_le hWijk))) ≅
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U j) (U k))).obj
            (data.localSheaf k)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk)))) :=
      openSubsetHomOfLE_section_iso
        hWijk
        (show U i ⊓ U j ⊓ U k ≤ U j ⊓ U k from by
          intro x hx
          exact ⟨hx.1.2, hx.2⟩)
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U j) (U k))).obj
            (data.localSheaf k))
    have hleft :
        directSecond.hom ≫ eLeft.inv =
          (((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
                (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app
              (data.localSheaf j)).1.app
            (op (subspace_open_of_le hWijk))) ≫
            ePairLeft.hom := by
      -- Normalize the left endpoint for the center overlap.
      simpa [directSecond, eLeft, ePairLeft, Category.assoc] using
        openSubsetHomOfLE_section_iso_forward_endpoint_compare
          hWijk
          (show U i ⊓ U j ⊓ U k ≤ U j ⊓ U k from by
            intro x hx
            exact ⟨hx.1.2, hx.2⟩)
          inf_le_left
          (data.localSheaf j)
    have hmiddle :
        ePairLeft.hom ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U j ⊓ U k))).map
              (data.overlapIso j k).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk))) ≫
            ePairRight.inv =
          (((TopCat.Sheaf.pullback (Type u)
                (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
              (data.overlapIso j k).hom).hom.app
            (op (subspace_open_of_le hWijk))) := by
      -- Move the overlap isomorphism to the triple-overlap owner.
      simpa [ePairLeft, ePairRight] using
        openSubsetHomOfLE_section_iso_map_compare
          hWijk
          (show U i ⊓ U j ⊓ U k ≤ U j ⊓ U k from by
            intro x hx
            exact ⟨hx.1.2, hx.2⟩)
          (data.overlapIso j k).hom
    have hright :
        eRight.hom ≫ directThird.inv =
          ePairRight.inv ≫
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionRightInclusion (U j) (U k))).symm.inv.app
                (data.localSheaf k)).1.app
              (op (subspace_open_of_le hWijk))) := by
      -- Normalize the right endpoint for the center overlap.
      simpa [directThird, eRight, ePairRight, Category.assoc] using
        (openSubsetHomOfLE_section_iso_inverse_endpoint_compare
          hWijk
          (show U i ⊓ U j ⊓ U k ≤ U j ⊓ U k from by
            intro x hx
            exact ⟨hx.1.2, hx.2⟩)
          inf_le_right
          (data.localSheaf k)).symm
    -- Assemble the center endpoint normal form.
    have hstep1 :
        directSecond.hom ≫ (subset_chart_iso data hWj hWk).hom ≫ directThird.inv =
          directSecond.hom ≫ eLeft.inv ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U j ⊓ U k))).map
              (data.overlapIso j k).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk))) ≫
            eRight.hom ≫ directThird.inv := by
      rfl
    have hstep2 :
        directSecond.hom ≫ eLeft.inv ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U j ⊓ U k))).map
              (data.overlapIso j k).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk))) ≫
            eRight.hom ≫ directThird.inv =
          (((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
                (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app
              (data.localSheaf j)).1.app
            (op (subspace_open_of_le hWijk))) ≫
              ePairLeft.hom ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U j ⊓ U k))).map
                (data.overlapIso j k).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk))) ≫
              eRight.hom ≫ directThird.inv := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            t ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U j ⊓ U k))).map
                (data.overlapIso j k).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk))) ≫
              eRight.hom ≫ directThird.inv)
          hleft
    have hstep3 :
        (((TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
              (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app
            (data.localSheaf j)).1.app
          (op (subspace_open_of_le hWijk))) ≫
            ePairLeft.hom ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U j ⊓ U k))).map
              (data.overlapIso j k).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk))) ≫
            eRight.hom ≫ directThird.inv =
          (((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
                (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app
              (data.localSheaf j)).1.app
            (op (subspace_open_of_le hWijk))) ≫
              ePairLeft.hom ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U j ⊓ U k))).map
                (data.overlapIso j k).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk))) ≫
              ePairRight.inv ≫
              (((TopCat.Sheaf.pullbackComp (A := Type u)
                    (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
                    (openSubsetIntersectionRightInclusion (U j) (U k))).symm.inv.app
                  (data.localSheaf k)).1.app
                (op (subspace_open_of_le hWijk))) := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app
                (data.localSheaf j)).1.app
              (op (subspace_open_of_le hWijk))) ≫
              ePairLeft.hom ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U j ⊓ U k))).map
                (data.overlapIso j k).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk))) ≫ t)
          hright
    have hstep4 :
        (((TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
              (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app
            (data.localSheaf j)).1.app
          (op (subspace_open_of_le hWijk))) ≫
            ePairLeft.hom ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U j ⊓ U k))).map
              (data.overlapIso j k).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWj hWk))) ≫
            ePairRight.inv ≫
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionRightInclusion (U j) (U k))).symm.inv.app
                (data.localSheaf k)).1.app
              (op (subspace_open_of_le hWijk))) = left23 := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app
                (data.localSheaf j)).1.app
              (op (subspace_open_of_le hWijk))) ≫ t ≫
              (((TopCat.Sheaf.pullbackComp (A := Type u)
                    (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
                    (openSubsetIntersectionRightInclusion (U j) (U k))).symm.inv.app
                  (data.localSheaf k)).1.app
                (op (subspace_open_of_le hWijk))))
          hmiddle
    exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))
  have h13 :
      directFirst.hom ≫ (subset_chart_iso data hWi hWk).hom ≫ directThird.inv = left13 := by
    let eLeft :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U k))).obj (data.localSheaf i)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk)))) ≅
        (data.localSheaf i).1.obj (op (subspace_open_of_le hWi)) :=
      openSubsetHomOfLE_section_iso
        (subset_overlap_le (U := U) hWi hWk)
        inf_le_left
        (data.localSheaf i)
    let eRight :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U k))).obj (data.localSheaf k)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk)))) ≅
        (data.localSheaf k).1.obj (op (subspace_open_of_le hWk)) :=
      openSubsetHomOfLE_section_iso
        (subset_overlap_le (U := U) hWi hWk)
        inf_le_right
        (data.localSheaf k)
    let ePairLeft :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).obj
            ((TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionLeftInclusion (U i) (U k))).obj
                (data.localSheaf i))).1.obj
          (op (subspace_open_of_le hWijk))) ≅
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U k))).obj
            (data.localSheaf i)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk)))) :=
      openSubsetHomOfLE_section_iso
        hWijk
        (show U i ⊓ U j ⊓ U k ≤ U i ⊓ U k from by
          intro x hx
          exact ⟨hx.1.1, hx.2⟩)
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U k))).obj
            (data.localSheaf i))
    let ePairRight :
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).obj
            ((TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionRightInclusion (U i) (U k))).obj
                (data.localSheaf k))).1.obj
          (op (subspace_open_of_le hWijk))) ≅
        (((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U k))).obj
            (data.localSheaf k)).1.obj
          (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk)))) :=
      openSubsetHomOfLE_section_iso
        hWijk
        (show U i ⊓ U j ⊓ U k ≤ U i ⊓ U k from by
          intro x hx
          exact ⟨hx.1.1, hx.2⟩)
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U k))).obj
            (data.localSheaf k))
    have hleft :
        directFirst.hom ≫ eLeft.inv =
          (((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
                (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app
              (data.localSheaf i)).1.app
            (op (subspace_open_of_le hWijk))) ≫
            ePairLeft.hom := by
      -- Normalize the left endpoint for the outer overlap.
      simpa [directFirst, eLeft, ePairLeft, Category.assoc] using
        openSubsetHomOfLE_section_iso_forward_endpoint_compare
          hWijk
          (show U i ⊓ U j ⊓ U k ≤ U i ⊓ U k from by
            intro x hx
            exact ⟨hx.1.1, hx.2⟩)
          inf_le_left
          (data.localSheaf i)
    have hmiddle :
        ePairLeft.hom ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U k))).map
              (data.overlapIso i k).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk))) ≫
            ePairRight.inv =
          (((TopCat.Sheaf.pullback (Type u)
                (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
              (data.overlapIso i k).hom).hom.app
            (op (subspace_open_of_le hWijk))) := by
      -- Move the outer overlap isomorphism to the triple-overlap owner.
      simpa [ePairLeft, ePairRight] using
        openSubsetHomOfLE_section_iso_map_compare
          hWijk
          (show U i ⊓ U j ⊓ U k ≤ U i ⊓ U k from by
            intro x hx
            exact ⟨hx.1.1, hx.2⟩)
          (data.overlapIso i k).hom
    have hright :
        eRight.hom ≫ directThird.inv =
          ePairRight.inv ≫
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionRightInclusion (U i) (U k))).symm.inv.app
                (data.localSheaf k)).1.app
              (op (subspace_open_of_le hWijk))) := by
      -- Normalize the right endpoint for the outer overlap.
      simpa [directThird, eRight, ePairRight, Category.assoc] using
        (openSubsetHomOfLE_section_iso_inverse_endpoint_compare
          hWijk
          (show U i ⊓ U j ⊓ U k ≤ U i ⊓ U k from by
            intro x hx
            exact ⟨hx.1.1, hx.2⟩)
          inf_le_right
          (data.localSheaf k)).symm
    -- Assemble the outer endpoint normal form.
    have hstep1 :
        directFirst.hom ≫ (subset_chart_iso data hWi hWk).hom ≫ directThird.inv =
          directFirst.hom ≫ eLeft.inv ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U k))).map
              (data.overlapIso i k).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk))) ≫
            eRight.hom ≫ directThird.inv := by
      rfl
    have hstep2 :
        directFirst.hom ≫ eLeft.inv ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U k))).map
              (data.overlapIso i k).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk))) ≫
            eRight.hom ≫ directThird.inv =
          (((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
                (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app
              (data.localSheaf i)).1.app
            (op (subspace_open_of_le hWijk))) ≫
              ePairLeft.hom ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U k))).map
                (data.overlapIso i k).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk))) ≫
              eRight.hom ≫ directThird.inv := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            t ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U k))).map
                (data.overlapIso i k).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk))) ≫
              eRight.hom ≫ directThird.inv)
          hleft
    have hstep3 :
        (((TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
              (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app
            (data.localSheaf i)).1.app
          (op (subspace_open_of_le hWijk))) ≫
            ePairLeft.hom ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U k))).map
              (data.overlapIso i k).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk))) ≫
            eRight.hom ≫ directThird.inv =
          (((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
                (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app
              (data.localSheaf i)).1.app
            (op (subspace_open_of_le hWijk))) ≫
              ePairLeft.hom ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U k))).map
                (data.overlapIso i k).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk))) ≫
              ePairRight.inv ≫
              (((TopCat.Sheaf.pullbackComp (A := Type u)
                    (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
                    (openSubsetIntersectionRightInclusion (U i) (U k))).symm.inv.app
                  (data.localSheaf k)).1.app
                (op (subspace_open_of_le hWijk))) := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app
                (data.localSheaf i)).1.app
              (op (subspace_open_of_le hWijk))) ≫
              ePairLeft.hom ≫
              ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U k))).map
                (data.overlapIso i k).hom).app
                (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk))) ≫ t)
          hright
    have hstep4 :
        (((TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
              (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app
            (data.localSheaf i)).1.app
          (op (subspace_open_of_le hWijk))) ≫
            ePairLeft.hom ≫
            ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U k))).map
              (data.overlapIso i k).hom).app
              (op (subspace_open_of_le (subset_overlap_le (U := U) hWi hWk))) ≫
            ePairRight.inv ≫
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionRightInclusion (U i) (U k))).symm.inv.app
                (data.localSheaf k)).1.app
              (op (subspace_open_of_le hWijk))) = left13 := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (((TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
                  (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app
                (data.localSheaf i)).1.app
              (op (subspace_open_of_le hWijk))) ≫ t ≫
              (((TopCat.Sheaf.pullbackComp (A := Type u)
                    (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
                    (openSubsetIntersectionRightInclusion (U i) (U k))).symm.inv.app
                  (data.localSheaf k)).1.app
                (op (subspace_open_of_le hWijk))))
          hmiddle
    exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))
  -- Rewrite both sides into the common triple-overlap normal form and cancel the middle chart.
  have hs12 :
      (subset_chart_iso data hWi hWj).hom =
        directFirst.inv ≫ left12 ≫ directSecond.hom := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ directFirst.inv ≫ t ≫ directSecond.hom) h12
  have hs23 :
      (subset_chart_iso data hWj hWk).hom =
        directSecond.inv ≫ left23 ≫ directThird.hom := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ directSecond.inv ≫ t ≫ directThird.hom) h23
  have hs13 :
      (subset_chart_iso data hWi hWk).hom =
        directFirst.inv ≫ left13 ≫ directThird.hom := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ directFirst.inv ≫ t ≫ directThird.hom) h13
  have hnorm' := subset_chart_iso_trans_normalized data hWijk
  calc
    (subset_chart_iso data hWi hWj).hom ≫ (subset_chart_iso data hWj hWk).hom
        =
      (directFirst.inv ≫ left12 ≫ directSecond.hom) ≫
        (directSecond.inv ≫ left23 ≫ directThird.hom) := by
          rw [hs12, hs23]
    _ = directFirst.inv ≫ left12 ≫ left23 ≫ directThird.hom := by
          simp [Category.assoc]
    _ = directFirst.inv ≫ left13 ≫ directThird.hom := by
          simpa [left12, left23, left13, Category.assoc] using
            congrArg (fun t ↦ directFirst.inv ≫ t ≫ directThird.hom) hnorm'
    _ = (subset_chart_iso data hWi hWk).hom := by
          rw [hs13]

/-- Helper for Lemma 6.33.2: on a fixed subordinate open, changing from a chart to itself is the
identity section map. -/
private theorem subset_chart_iso_self_hom
    (data : SheafOpenCoverGlueing U) {W : Opens X} {i : ι}
    (hWi : W ≤ U i) :
    (subset_chart_iso data hWi hWi).hom = 𝟙 _ := by
  -- Apply transitivity with the same chart three times and cancel one copy of the isomorphism.
  let e := subset_chart_iso data hWi hWi
  apply (cancel_mono e.hom).1
  simpa [e, Category.assoc] using
    (subset_chart_iso_trans data hWi hWi hWi : e.hom ≫ e.hom = e.hom)

/-- Helper for Lemma 6.33.2: restriction in the chosen-chart basis presheaf first restricts inside
the larger chosen chart and then transports to the smaller chosen chart. -/
private noncomputable def open_cover_glueing_basisPresheaf_map
    (data : SheafOpenCoverGlueing U)
    {V W : (BasisOpen (coverSubordinateOpens (U := U)))ᵒᵖ} (i : V ⟶ W) :
    (data.localSheaf (chosen_chart V.unop)).1.obj
        (op (subspace_open_of_le (chosen_chart_le V.unop))) →
      (data.localSheaf (chosen_chart W.unop)).1.obj
        (op (subspace_open_of_le (chosen_chart_le W.unop))) := fun s ↦
  let hWV : W.unop.obj ≤ V.unop.obj := i.unop.hom.le
  let hWcV : W.unop.obj ≤ U (chosen_chart V.unop) := hWV.trans (chosen_chart_le V.unop)
  let restricted :=
    (data.localSheaf (chosen_chart V.unop)).1.map
      (subspace_open_hom hWcV (chosen_chart_le V.unop) hWV).op s
  (subset_chart_iso data hWcV (chosen_chart_le W.unop)).hom restricted

/-- Helper for Lemma 6.33.2: the chosen-chart basis presheaf has identity restriction maps. -/
private theorem open_cover_glueing_basisPresheaf_map_id
    (data : SheafOpenCoverGlueing U) :
    ∀ W : (BasisOpen (coverSubordinateOpens (U := U)))ᵒᵖ,
      open_cover_glueing_basisPresheaf_map data (𝟙 W) = id := by
  intro W
  funext s
  -- Normalize the restriction part to the identity and use that self chart-change is trivial.
  have hsub :
      subspace_open_hom
          (chosen_chart_le W.unop)
          (chosen_chart_le W.unop)
          (show W.unop.obj ≤ W.unop.obj from le_rfl) =
        𝟙 _ := by
    apply Subsingleton.elim
  simp [open_cover_glueing_basisPresheaf_map, subset_chart_iso_self_hom]

/-- Helper for Lemma 6.33.2: the chosen-chart restriction maps compose by first moving everything
into the smallest open and then using chart-change transitivity there. -/
private theorem open_cover_glueing_basisPresheaf_map_comp
    (data : SheafOpenCoverGlueing U) :
    ∀ {A B C : (BasisOpen (coverSubordinateOpens (U := U)))ᵒᵖ}
      (iAB : A ⟶ B) (iBC : B ⟶ C),
      open_cover_glueing_basisPresheaf_map data (iAB ≫ iBC) =
        open_cover_glueing_basisPresheaf_map data iBC ∘
          open_cover_glueing_basisPresheaf_map data iAB := by
  intro A B C iAB iBC
  funext s
  let hBA : B.unop.obj ≤ A.unop.obj := iAB.unop.hom.le
  let hCB : C.unop.obj ≤ B.unop.obj := iBC.unop.hom.le
  let hCA : C.unop.obj ≤ A.unop.obj := hCB.trans hBA
  let cA := chosen_chart A.unop
  let cB := chosen_chart B.unop
  let cC := chosen_chart C.unop
  let hAcA : A.unop.obj ≤ U cA := chosen_chart_le A.unop
  let hBcB : B.unop.obj ≤ U cB := chosen_chart_le B.unop
  let hCcC : C.unop.obj ≤ U cC := chosen_chart_le C.unop
  let hBcA : B.unop.obj ≤ U cA := hBA.trans hAcA
  let hCcA : C.unop.obj ≤ U cA := hCA.trans hAcA
  let hCcB : C.unop.obj ≤ U cB := hCB.trans hBcB
  let rAB :
      subspace_open_of_le hBcA ⟶ subspace_open_of_le hAcA :=
    subspace_open_hom hBcA hAcA hBA
  let rBC_A :
      subspace_open_of_le hCcA ⟶ subspace_open_of_le hBcA :=
    subspace_open_hom hCcA hBcA hCB
  let rBC_B :
      subspace_open_of_le hCcB ⟶ subspace_open_of_le hBcB :=
    subspace_open_hom hCcB hBcB hCB
  let rAC :
      subspace_open_of_le hCcA ⟶ subspace_open_of_le hAcA :=
    subspace_open_hom hCcA hAcA hCA
  have hrcomp :
      rBC_A ≫ rAB = rAC := by
    -- The two ambient restriction routes from `C` into `A` are the same inclusion.
    apply Subsingleton.elim
  have hmapA :
      (data.localSheaf cA).1.map rAC.op =
        (data.localSheaf cA).1.map rAB.op ≫
          (data.localSheaf cA).1.map rBC_A.op := by
    -- Rewrite the direct restriction to `C` as the composite through `B`.
    calc
      (data.localSheaf cA).1.map rAC.op
          = (data.localSheaf cA).1.map ((rBC_A ≫ rAB).op) := by
              simpa [hrcomp]
      _ = (data.localSheaf cA).1.map rAB.op ≫
            (data.localSheaf cA).1.map rBC_A.op := by
              simp [Functor.map_comp]
  have hnat :=
    subset_chart_iso_naturality data (hVW := hCB)
      (hVi := hCcA) (hVj := hCcB) (hWi := hBcA) (hWj := hBcB)
  -- Normalize the right-hand side to the smallest open `C`.
  calc
    open_cover_glueing_basisPresheaf_map data (iAB ≫ iBC) s
        =
      (subset_chart_iso data hCcA hCcC).hom
        ((data.localSheaf cA).1.map rAC.op s) := by
          rfl
    _ =
      (subset_chart_iso data hCcA hCcC).hom
        ((data.localSheaf cA).1.map rBC_A.op
          ((data.localSheaf cA).1.map rAB.op s)) := by
            simp [hmapA]
    _ =
      (subset_chart_iso data hCcB hCcC).hom
        ((subset_chart_iso data hCcA hCcB).hom
          ((data.localSheaf cA).1.map rBC_A.op
            ((data.localSheaf cA).1.map rAB.op s))) := by
            -- Reassociate the direct chart change `cA → cC` through the intermediate chart `cB`.
            have htrans := subset_chart_iso_trans data hCcA hCcB hCcC
            simpa [Category.assoc] using congrArg
              (fun f ↦ f
                ((data.localSheaf cA).1.map rBC_A.op
                  ((data.localSheaf cA).1.map rAB.op s))) htrans.symm
    _ =
      (subset_chart_iso data hCcB hCcC).hom
        ((data.localSheaf cB).1.map rBC_B.op
          ((subset_chart_iso data hBcA hBcB).hom
            ((data.localSheaf cA).1.map rAB.op s))) := by
            -- Move the middle chart change past the restriction to `C`.
            have hnat' :=
              congrArg
                (fun f ↦ f ((data.localSheaf cA).1.map rAB.op s))
                hnat
            exact congrArg (fun t ↦ (subset_chart_iso data hCcB hCcC).hom t) hnat'
    _ = open_cover_glueing_basisPresheaf_map data iBC
          (open_cover_glueing_basisPresheaf_map data iAB s) := by
          -- The inner section is exactly the first restriction map applied to `s`.
          exact congrArg (open_cover_glueing_basisPresheaf_map data iBC) rfl

/-- Helper for Lemma 6.33.2: the second source proof produces a presheaf on the subordinate-open
basis by choosing one chart containing each basis open. -/
private noncomputable def open_cover_glueing_basisPresheaf
    (data : SheafOpenCoverGlueing U) :
    Presheaf (BasisOpen (coverSubordinateOpens (U := U))) where
  obj W :=
    (data.localSheaf (chosen_chart W.unop)).1.obj
      (op (subspace_open_of_le (chosen_chart_le W.unop)))
  map i := open_cover_glueing_basisPresheaf_map data i
  map_id := open_cover_glueing_basisPresheaf_map_id data
  map_comp := open_cover_glueing_basisPresheaf_map_comp data

/-- Helper for Lemma 6.33.2: the chosen-chart basis presheaf satisfies the basis sheaf condition
once all cover members are transported into one fixed chart. -/
private theorem basis_cover_transport_to_fixed_chart_compatible
    (data : SheafOpenCoverGlueing U)
    {W0 : BasisOpen (coverSubordinateOpens (U := U))}
    (𝒰 : BasisCover (coverSubordinateOpens (U := U)) W0)
    (hInter :
      ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ coverSubordinateOpens (U := U))
    (s : FamilyOfElementsOnObjects (open_cover_glueing_basisPresheaf data) 𝒰.obj)
    (hs : s.IsCompatible) :
    TopCat.Presheaf.IsCompatible
      (data.localSheaf (chosen_chart W0)).1
      (fun i ↦ subspace_open_of_le ((𝒰.hom i).hom.le.trans (chosen_chart_le W0)))
      (fun i ↦
        (subset_chart_iso data
          (i := chosen_chart (𝒰.obj i))
          (j := chosen_chart W0)
          (chosen_chart_le (𝒰.obj i))
          ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))).hom
          (s i)) := by
  intro i j
  let c0 := chosen_chart W0
  let ci := chosen_chart (𝒰.obj i)
  let cj := chosen_chart (𝒰.obj j)
  let hI0 : (𝒰.obj i).obj ≤ U c0 := (𝒰.hom i).hom.le.trans (chosen_chart_le W0)
  let hJ0 : (𝒰.obj j).obj ≤ U c0 := (𝒰.hom j).hom.le.trans (chosen_chart_le W0)
  let Zij := BasisCover.actual_intersection 𝒰 hInter i j
  let hZ0 : Zij.obj ≤ U c0 := (BasisCover.actual_intersection_left 𝒰 hInter i j).hom.le.trans hI0
  let kLeft := BasisCover.actual_intersection_left 𝒰 hInter i j
  let kRight := BasisCover.actual_intersection_right 𝒰 hInter i j
  have hleft_nat := basis_cover_member_transport_naturality (data := data) (W0 := W0) 𝒰 i kLeft
  have hright_nat := basis_cover_member_transport_naturality (data := data) (W0 := W0) 𝒰 j kRight
  -- First rewrite the two fixed-chart restriction maps as the transported actual-intersection maps.
  have hleft_fixed :
      ((data.localSheaf c0).1.map ((subspace_open_of_le hI0).infLELeft (subspace_open_of_le hJ0)).op)
          ((subset_chart_iso data (chosen_chart_le (𝒰.obj i)) hI0).hom (s i)) =
        (subset_chart_iso data
          (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
          hZ0).hom
          ((data.localSheaf ci).1.map
            (subspace_open_hom
              (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
              (chosen_chart_le (𝒰.obj i))
              kLeft.hom.le).op
            (s i)) := by
    have hleft_eval := congrArg (fun f ↦ f (s i)) hleft_nat
    simpa [c0, ci, hI0, hJ0, hZ0, Category.assoc, subspace_open_of_le_inf_eq] using
      hleft_eval.symm
  have hright_fixed :
      ((data.localSheaf c0).1.map ((subspace_open_of_le hI0).infLERight (subspace_open_of_le hJ0)).op)
          ((subset_chart_iso data (chosen_chart_le (𝒰.obj j)) hJ0).hom (s j)) =
        (subset_chart_iso data
          (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
          hZ0).hom
          ((data.localSheaf cj).1.map
            (subspace_open_hom
              (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
              (chosen_chart_le (𝒰.obj j))
              kRight.hom.le).op
            (s j)) := by
    have hright_eval := congrArg (fun f ↦ f (s j)) hright_nat
    have hZ0' : kRight.hom.le.trans hJ0 = hZ0 := by
      apply Subsingleton.elim
    simpa [c0, cj, hI0, hJ0, hZ0, hZ0', Category.assoc, subspace_open_of_le_inf_eq] using
      hright_eval.symm
  -- Next transport the original actual-intersection compatibility into the fixed chart of `W0`.
  have hs' :=
    (BasisCover.isCompatible_iff_actual_intersections 𝒰 hInter
      (open_cover_glueing_basisPresheaf data) s).1 hs i j
  have hs_pair :
      (subset_chart_iso data
        (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
        (chosen_chart_le Zij)).hom
          ((data.localSheaf ci).1.map
            (subspace_open_hom
              (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
              (chosen_chart_le (𝒰.obj i))
              kLeft.hom.le).op
            (s i)) =
        (subset_chart_iso data
          (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
          (chosen_chart_le Zij)).hom
          ((data.localSheaf cj).1.map
            (subspace_open_hom
              (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
              (chosen_chart_le (𝒰.obj j))
              kRight.hom.le).op
            (s j)) := by
    simpa [Zij, ci, cj, open_cover_glueing_basisPresheaf_map] using hs'
  have hs_push := congrArg ((subset_chart_iso data (chosen_chart_le Zij) hZ0).hom) hs_pair
  have hleft_trans := subset_chart_iso_trans data
    (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
    (chosen_chart_le Zij)
    hZ0
  have hright_trans := subset_chart_iso_trans data
    (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
    (chosen_chart_le Zij)
    hZ0
  have hs_middle :
      (subset_chart_iso data
          (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
          hZ0).hom
          ((data.localSheaf ci).1.map
            (subspace_open_hom
              (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
              (chosen_chart_le (𝒰.obj i))
              kLeft.hom.le).op
            (s i)) =
        (subset_chart_iso data
          (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
          hZ0).hom
          ((data.localSheaf cj).1.map
            (subspace_open_hom
              (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
              (chosen_chart_le (𝒰.obj j))
              kRight.hom.le).op
            (s j)) := by
    have hleft_nested :
        (subset_chart_iso data
            (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
            hZ0).hom
            ((data.localSheaf ci).1.map
              (subspace_open_hom
                (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
                (chosen_chart_le (𝒰.obj i))
                kLeft.hom.le).op
              (s i)) =
          (subset_chart_iso data (chosen_chart_le Zij) hZ0).hom
            ((subset_chart_iso data
              (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
              (chosen_chart_le Zij)).hom
              ((data.localSheaf ci).1.map
                (subspace_open_hom
                  (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
                  (chosen_chart_le (𝒰.obj i))
                  kLeft.hom.le).op
                (s i))) := by
      simpa [Category.assoc] using
        congrArg
          (fun f ↦ f
            ((data.localSheaf ci).1.map
              (subspace_open_hom
                (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
                (chosen_chart_le (𝒰.obj i))
                kLeft.hom.le).op
              (s i)))
          hleft_trans.symm
    have hright_nested :
        (subset_chart_iso data (chosen_chart_le Zij) hZ0).hom
            ((subset_chart_iso data
              (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
              (chosen_chart_le Zij)).hom
              ((data.localSheaf cj).1.map
                (subspace_open_hom
                  (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
                  (chosen_chart_le (𝒰.obj j))
                  kRight.hom.le).op
                (s j))) =
          (subset_chart_iso data
            (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
            hZ0).hom
            ((data.localSheaf cj).1.map
              (subspace_open_hom
                (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
                (chosen_chart_le (𝒰.obj j))
                kRight.hom.le).op
              (s j)) := by
      simpa [Category.assoc] using
        congrArg
          (fun f ↦ f
            ((data.localSheaf cj).1.map
              (subspace_open_hom
                (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
                (chosen_chart_le (𝒰.obj j))
                kRight.hom.le).op
              (s j)))
          hright_trans
    exact hleft_nested.trans (hs_push.trans hright_nested)
  -- Finally chain the two endpoint normalizations with the transported compatibility equality.
  exact hleft_fixed.trans (hs_middle.trans hright_fixed.symm)

/-- Helper for Lemma 6.33.2: the chosen-chart basis presheaf satisfies the basis sheaf condition
once all cover members are transported into one fixed chart. -/
private theorem fixed_chart_gluing_recovers_basis_section
    (data : SheafOpenCoverGlueing U)
    {W0 : BasisOpen (coverSubordinateOpens (U := U))}
    (𝒰 : BasisCover (coverSubordinateOpens (U := U)) W0)
    (s : FamilyOfElementsOnObjects (open_cover_glueing_basisPresheaf data) 𝒰.obj)
    {t0 :
      (data.localSheaf (chosen_chart W0)).1.obj
        (op (subspace_open_of_le (chosen_chart_le W0)))}
    (ht0 :
      ∀ i : 𝒰.ι,
        (data.localSheaf (chosen_chart W0)).1.map
            (subspace_open_hom
              ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))
              (chosen_chart_le W0)
              (𝒰.hom i).hom.le).op
            t0 =
          (subset_chart_iso data
            (chosen_chart_le (𝒰.obj i))
            ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))).hom
            (s i)) :
    ∀ i : 𝒰.ι, open_cover_glueing_basisPresheaf_map data (𝒰.hom i).op t0 = s i := by
  intro i
  let ci := chosen_chart (𝒰.obj i)
  let hIc0 : (𝒰.obj i).obj ≤ U (chosen_chart W0) :=
    (𝒰.hom i).hom.le.trans (chosen_chart_le W0)
  have hround :
      (subset_chart_iso data (chosen_chart_le (𝒰.obj i)) hIc0).hom ≫
          (subset_chart_iso data hIc0 (chosen_chart_le (𝒰.obj i))).hom =
        𝟙 _ := by
    -- The round-trip chart change collapses to the identity in the chosen chart of `𝒰.obj i`.
    calc
      (subset_chart_iso data (chosen_chart_le (𝒰.obj i)) hIc0).hom ≫
          (subset_chart_iso data hIc0 (chosen_chart_le (𝒰.obj i))).hom
          =
        (subset_chart_iso data
          (chosen_chart_le (𝒰.obj i))
          (chosen_chart_le (𝒰.obj i))).hom := by
              simpa [ci, hIc0] using
                subset_chart_iso_trans data
                  (chosen_chart_le (𝒰.obj i))
                  hIc0
                  (chosen_chart_le (𝒰.obj i))
      _ = 𝟙 _ := by
            simpa [ci] using
              subset_chart_iso_self_hom data (hWi := chosen_chart_le (𝒰.obj i))
  -- Rewrite the fixed-chart restriction with `ht0`, then cancel the round-trip chart change.
  calc
    open_cover_glueing_basisPresheaf_map data (𝒰.hom i).op t0
        =
      (subset_chart_iso data hIc0 (chosen_chart_le (𝒰.obj i))).hom
        ((data.localSheaf (chosen_chart W0)).1.map
          (subspace_open_hom hIc0 (chosen_chart_le W0) (𝒰.hom i).hom.le).op
          t0) := by
          rfl
    _ =
      (subset_chart_iso data hIc0 (chosen_chart_le (𝒰.obj i))).hom
        ((subset_chart_iso data
          (chosen_chart_le (𝒰.obj i))
          hIc0).hom
          (s i)) := by
            rw [ht0 i]
    _ = s i := by
          have hround_eval := congrArg (fun f ↦ f (s i)) hround
          simpa [Category.assoc] using hround_eval

/-- Helper for Lemma 6.33.2: the chosen-chart basis presheaf satisfies the basis sheaf condition
once all cover members are transported into one fixed chart. -/
private theorem open_cover_glueing_basisPresheaf_isBasisSheaf
    (data : SheafOpenCoverGlueing U) :
    (open_cover_glueing_basisPresheaf data).IsBasisSheaf := by
  -- Route correction: the basis-site reduction to unique gluing is now packaged above; the only
  -- remaining work is the fixed-chart transport/gluing construction.
  refine (basisPresheaf_isBasisSheaf_iff_isSheaf
    (X := X)
    (B := coverSubordinateOpens (U := U))
    (F := open_cover_glueing_basisPresheaf data)
    (hB := cover_subordinate_opens_isBasis data)).2 ?_
  refine (basisPresheaf_isSheaf_iff_uniqueGluing_on_cofinal_basis_covers_local
    (X := X)
    (B := coverSubordinateOpens (U := U))
    (hB := cover_subordinate_opens_isBasis data)
    (C := fun _ ↦ Set.univ)
    (hC := ?_)
    (hInter := ?_)
    (F := open_cover_glueing_basisPresheaf data)).2 ?_
  · intro W0 𝒰
    refine ⟨𝒰, Set.mem_univ _, ?_⟩
    refine ⟨fun i ↦ i, ?_⟩
    intro i
    exact ⟨𝟙 _, by simp⟩
  · intro W0 𝒰 _ i j
    refine ⟨chosen_chart (𝒰.obj i), ?_⟩
    intro x hx
    exact (chosen_chart_le (𝒰.obj i)) hx.1
  · intro W0 𝒰 _ s hs
    let c0 := chosen_chart W0
    let cover :
        𝒰.ι → Opens (openSubsetSpace (U c0)) :=
      fun i ↦ subspace_open_of_le ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))
    let iUV : ∀ i : 𝒰.ι, cover i ⟶ subspace_open_of_le (chosen_chart_le W0) :=
      fun i ↦
        subspace_open_hom
          ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))
          (chosen_chart_le W0)
          (𝒰.hom i).hom.le
    have hcover :
        subspace_open_of_le (chosen_chart_le W0) ≤ iSup cover := by
      -- The fixed-chart cover is just the given basis cover, viewed inside the chosen chart of `W0`.
      intro x hx
      rw [Opens.mem_iSup]
      have hxW0 : x.1 ∈ W0.obj := by
        simpa [cover, c0, subspace_open_of_le_image_eq] using
          (mem_subspace_open_iff (U := U c0)
            (subspace_open_of_le (chosen_chart_le W0)) x).1 hx
      have hxW0' : x.1 ∈ ((W0.obj : Opens X) : Set X) := hxW0
      rw [𝒰.iUnion_eq] at hxW0'
      rcases Set.mem_iUnion.mp hxW0' with ⟨i, hxi⟩
      refine ⟨i, ?_⟩
      exact
        (mem_subspace_open_iff (U := U c0) (cover i) x).2
          (by simpa [cover, c0, subspace_open_of_le_image_eq] using hxi)
    have hcompat :=
      basis_cover_transport_to_fixed_chart_compatible
        (data := data)
        (W0 := W0)
        (𝒰 := 𝒰)
        (hInter := fun i j ↦ by
          refine ⟨chosen_chart (𝒰.obj i), ?_⟩
          intro x hx
          exact (chosen_chart_le (𝒰.obj i)) hx.1)
        (s := s)
        hs
    obtain ⟨t0, ht0, ht0uniq⟩ :=
      (data.localSheaf c0).existsUnique_gluing'
        (V := subspace_open_of_le (chosen_chart_le W0))
        (U := cover)
        iUV
        hcover
        (fun i ↦
          (subset_chart_iso data
            (chosen_chart_le (𝒰.obj i))
            ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))).hom
            (s i))
        hcompat
    refine ⟨t0, ?_, ?_⟩
    · -- Recover the original basis-cover family by undoing the transported chart changes.
      exact fixed_chart_gluing_recovers_basis_section (data := data) (𝒰 := 𝒰) (s := s) ht0
    · intro t' ht'
      apply ht0uniq
      intro i
      let outer :=
        subset_chart_iso data
          (((𝒰.hom i).hom.le.trans (chosen_chart_le W0)))
          (chosen_chart_le (𝒰.obj i))
      have houter :
          Function.Injective outer.hom := by
        intro a b hab
        have h' := congrArg outer.inv hab
        simpa using h'
      apply houter
      -- Apply the basis-presheaf restriction formula and compare with the candidate gluing.
      have hs_round :
          outer.hom
            ((subset_chart_iso data
              (chosen_chart_le (𝒰.obj i))
              ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))).hom
              (s i)) = s i := by
        have hround :
            (subset_chart_iso data
              (chosen_chart_le (𝒰.obj i))
              ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))).hom ≫ outer.hom =
              𝟙 _ := by
          calc
            (subset_chart_iso data
                (chosen_chart_le (𝒰.obj i))
                ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))).hom ≫ outer.hom
                =
              (subset_chart_iso data
                (chosen_chart_le (𝒰.obj i))
                (chosen_chart_le (𝒰.obj i))).hom := by
                    simpa [outer] using
                      subset_chart_iso_trans data
                        (chosen_chart_le (𝒰.obj i))
                        ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))
                        (chosen_chart_le (𝒰.obj i))
            _ = 𝟙 _ := by
                  simpa [outer] using
                    subset_chart_iso_self_hom data
                      (hWi := chosen_chart_le (𝒰.obj i))
        simpa [Category.assoc] using congrArg (fun f ↦ f (s i)) hround
      have hmap :
          outer.hom
              ((data.localSheaf c0).1.map
                (subspace_open_hom
                  ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))
                  (chosen_chart_le W0)
                  (𝒰.hom i).hom.le).op
                t') =
            open_cover_glueing_basisPresheaf_map data (𝒰.hom i).op t' := by
        rfl
      exact hmap.trans ((ht' i).trans hs_round.symm)

/-- Helper for Lemma 6.33.2: package the chosen-chart basis presheaf as a basis sheaf on the
subordinate-open basis. -/
private noncomputable def open_cover_glueing_basisSheaf
    (data : SheafOpenCoverGlueing U) :
    BasisSheaf (coverSubordinateOpens (U := U)) :=
  ⟨open_cover_glueing_basisPresheaf data,
    open_cover_glueing_basisPresheaf_isBasisSheaf data⟩

/-- Helper for Lemma 6.33.2: evaluating a global sheaf on an ambient open `W ⊆ A` through the
restriction to `A` is the open-embedding pullback comparison followed by the ambient-open
transport back to `W`. -/
noncomputable def ambient_open_section_iso
    (ℱ : X.Sheaf (Type u)) {W A : Opens X} (hWA : W ≤ A) :
    (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion A)).obj ℱ)).1.obj
        (op (subspace_open_of_le hWA)) ≅
      ℱ.1.obj (op W) :=
  -- Compare the actual pullback to the open-embedding pullback model, then rewrite the target
  -- open inside `X` using the explicit `subspace_open_of_le` description.
  (((TopCat.Sheaf.forget (Type u) (openSubsetSpace A)).mapIso
      ((openEmbedding_sheafPullbackIso (A).isOpenEmbedding).app ℱ)).app
      (op (subspace_open_of_le hWA))) ≪≫
    eqToIso (by
      change
        ℱ.1.obj (op ((subspace_inclusion_functor A).obj (subspace_open_of_le hWA))) =
          ℱ.1.obj (op W)
      simpa [subspace_open_of_le_image_eq])

/-- Helper for Lemma 6.33.2: `ambient_open_section_iso.hom` is definitionally the open-embedding
pullback comparison followed by the ambient-open transport `eqToHom`. -/
theorem ambient_open_section_iso_hom_eq
    (ℱ : X.Sheaf (Type u)) {W A : Opens X} (hWA : W ≤ A) :
    (ambient_open_section_iso (X := X) ℱ hWA).hom =
      (((TopCat.Sheaf.forget (Type u) (openSubsetSpace A)).mapIso
          ((openEmbedding_sheafPullbackIso (A).isOpenEmbedding).app ℱ)).app
          (op (subspace_open_of_le hWA))).hom ≫
        eqToHom (by
          change
            ℱ.1.obj (op ((subspace_inclusion_functor A).obj (subspace_open_of_le hWA))) =
              ℱ.1.obj (op W)
          simpa [subspace_open_of_le_image_eq]) := by
  -- Unfold the packaged comparison once so later overlap proofs can rewrite the two factors
  -- separately instead of repeatedly expanding the whole definition.
  rfl

/-- Helper for Lemma 6.33.2: restricting an ambient sheaf from `B` to `A` and then to `W`
matches the naive open-embedding pullback model over `B`, with only the final ambient transport
left explicit. -/
private theorem ambient_open_section_iso_compare
    (ℱ : X.Sheaf (Type u)) {W A B : Opens X}
    (hWA : W ≤ A) (hAB : A ≤ B) :
    let eNaive :=
      openSubsetHomOfLE_section_iso hWA hAB
        (((B).isOpenEmbedding.sheafPullback (Type u)).obj ℱ)
    (openSubsetHomOfLE_section_iso hWA hAB
        ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ)).hom ≫
      (ambient_open_section_iso (X := X) ℱ (hWA.trans hAB)).hom =
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
          ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).hom.app
        (op (subspace_open_of_le hWA))) ≫
      eNaive.hom ≫
        eqToHom (by
          change
            ℱ.1.obj (op ((subspace_inclusion_functor B).obj
              (subspace_open_of_le (hWA.trans hAB)))) =
              ℱ.1.obj (op W)
          simpa [subspace_open_of_le_image_eq]) := by
  let eNaive :=
    openSubsetHomOfLE_section_iso hWA hAB
      (((B).isOpenEmbedding.sheafPullback (Type u)).obj ℱ)
  have hcompare :
      (openSubsetHomOfLE_section_iso hWA hAB
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ)).hom ≫
        (((TopCat.Sheaf.forget (Type u) (openSubsetSpace B)).map
            ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).app
          (op (subspace_open_of_le (hWA.trans hAB)))) ≫
        eNaive.inv =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
            ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hWA))) := by
    -- Move the open-embedding comparison from the `A`-owner to the `W`-owner once.
    simpa [eNaive] using
      openSubsetHomOfLE_section_iso_memberSheafPullbackIso_compare
        (hAB := hWA) (hBC := hAB) (ℱ := ℱ)
  have htoNaive :
      (openSubsetHomOfLE_section_iso hWA hAB
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ)).hom ≫
        (((TopCat.Sheaf.forget (Type u) (openSubsetSpace B)).map
            ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).app
          (op (subspace_open_of_le (hWA.trans hAB)))) =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
            ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hWA))) ≫
        eNaive.hom := by
    -- Cancel the residual naive section comparison on the right-hand side of `hcompare`.
    calc
      (openSubsetHomOfLE_section_iso hWA hAB
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ)).hom ≫
        (((TopCat.Sheaf.forget (Type u) (openSubsetSpace B)).map
            ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).app
          (op (subspace_open_of_le (hWA.trans hAB)))) =
          ((openSubsetHomOfLE_section_iso hWA hAB
              ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ)).hom ≫
            (((TopCat.Sheaf.forget (Type u) (openSubsetSpace B)).map
                ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).app
              (op (subspace_open_of_le (hWA.trans hAB)))) ≫
            eNaive.inv) ≫
              eNaive.hom := by
                ext x
                simp
      _ = (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
              ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).hom.app
            (op (subspace_open_of_le hWA))) ≫
            eNaive.hom := by
              simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eNaive.hom) hcompare
  -- Replace the ambient section comparison by its naive-model spelling, then reuse `htoNaive`.
  calc
    (openSubsetHomOfLE_section_iso hWA hAB
        ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ)).hom ≫
      (ambient_open_section_iso (X := X) ℱ (hWA.trans hAB)).hom
        =
      (openSubsetHomOfLE_section_iso hWA hAB
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ)).hom ≫
        (((TopCat.Sheaf.forget (Type u) (openSubsetSpace B)).mapIso
            ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).app ℱ)).app
            (op (subspace_open_of_le (hWA.trans hAB)))).hom ≫
          eqToHom (by
            change
              ℱ.1.obj (op ((subspace_inclusion_functor B).obj
                (subspace_open_of_le (hWA.trans hAB)))) =
                ℱ.1.obj (op W)
            simpa [subspace_open_of_le_image_eq]) := by
            rw [ambient_open_section_iso_hom_eq (X := X) (ℱ := ℱ) (A := B)
              (hWA := hWA.trans hAB)]
            rfl
    _ =
      ((((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
            ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hWA))) ≫
        eNaive.hom) ≫
          eqToHom (by
            change
              ℱ.1.obj (op ((subspace_inclusion_functor B).obj
                (subspace_open_of_le (hWA.trans hAB)))) =
                ℱ.1.obj (op W)
            simpa [subspace_open_of_le_image_eq]) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  k ≫ eqToHom (by
                    change
                      ℱ.1.obj (op ((subspace_inclusion_functor B).obj
                        (subspace_open_of_le (hWA.trans hAB)))) =
                        ℱ.1.obj (op W)
                    simpa [subspace_open_of_le_image_eq]))
                htoNaive
    _ =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
            ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hWA))) ≫
        eNaive.hom ≫
          eqToHom (by
            change
              ℱ.1.obj (op ((subspace_inclusion_functor B).obj
                (subspace_open_of_le (hWA.trans hAB)))) =
                ℱ.1.obj (op W)
            simpa [subspace_open_of_le_image_eq]) := by
            simp [Category.assoc]

/-- Helper for Lemma 6.33.2: evaluating the restriction of a global sheaf to one member `U i` on a
subordinate open `W ≤ U i` recovers the ambient section over `W`. -/
private noncomputable def global_member_section_iso
    (ℱ : X.Sheaf (Type u)) {W : Opens X} {i : ι} (hWi : W ≤ U i) :
    (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).1.obj
        (op (subspace_open_of_le hWi)) ≅
      ℱ.1.obj (op W) :=
  ambient_open_section_iso (X := X) ℱ hWi

/-- Helper for Lemma 6.33.2: `global_member_section_iso.hom` is definitionally the
open-embedding pullback comparison followed by the ambient-open transport `eqToHom`. -/
private theorem global_member_section_iso_hom_eq
    (ℱ : X.Sheaf (Type u)) {W : Opens X} {i : ι} (hWi : W ≤ U i) :
    (global_member_section_iso (U := U) ℱ (i := i) hWi).hom =
      (((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i))).mapIso
          ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).app ℱ)).app
          (op (subspace_open_of_le hWi))).hom ≫
        eqToHom (by
          change
            ℱ.1.obj (op ((subspace_inclusion_functor (U i)).obj (subspace_open_of_le hWi))) =
              ℱ.1.obj (op W)
          simpa [subspace_open_of_le_image_eq]) := by
  -- This is the member-open specialization of the general ambient-open comparison formula.
  simpa [global_member_section_iso] using
    ambient_open_section_iso_hom_eq (X := X) (ℱ := ℱ) (A := U i) hWi

/-- Helper for Lemma 6.33.2: restricting a section over a member `U i` to a smaller open and then
transporting it to ambient sections factors through the pulled-back naive open-embedding model. -/
private theorem memberSectionToNaiveGlobal_compare
    (ℱ : X.Sheaf (Type u)) {A W : Opens X} {i : ι}
    (hWA : W ≤ A) (hAi : A ≤ U i) :
    let eNaive :=
      openSubsetHomOfLE_section_iso hWA hAi
        (((U i).isOpenEmbedding.sheafPullback (Type u)).obj ℱ)
    (openSubsetHomOfLE_section_iso hWA hAi
        ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).hom ≫
      (global_member_section_iso (U := U) ℱ (i := i) (hWA.trans hAi)).hom =
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAi)).map
          ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).hom.app ℱ)).hom.app
        (op (subspace_open_of_le hWA))) ≫
      eNaive.hom ≫
        eqToHom (by
          change
            ℱ.1.obj (op ((subspace_inclusion_functor (U i)).obj
              (subspace_open_of_le (hWA.trans hAi)))) =
              ℱ.1.obj (op W)
          simpa [subspace_open_of_le_image_eq]) := by
  let eNaive :=
    openSubsetHomOfLE_section_iso hWA hAi
      (((U i).isOpenEmbedding.sheafPullback (Type u)).obj ℱ)
  have hcompare :
      (openSubsetHomOfLE_section_iso hWA hAi
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).hom ≫
        (((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i))).map
            ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).hom.app ℱ)).app
          (op (subspace_open_of_le (hWA.trans hAi)))) ≫
        eNaive.inv =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAi)).map
            ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hWA))) := by
    -- Move the open-embedding comparison from the `A`-owner to the `W`-owner once.
    simpa [eNaive] using
      openSubsetHomOfLE_section_iso_memberSheafPullbackIso_compare
        (hAB := hWA) (hBC := hAi) (ℱ := ℱ)
  have htoNaive :
      (openSubsetHomOfLE_section_iso hWA hAi
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).hom ≫
        (((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i))).map
            ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).hom.app ℱ)).app
          (op (subspace_open_of_le (hWA.trans hAi)))) =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAi)).map
            ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hWA))) ≫
        eNaive.hom := by
    -- Cancel the residual naive section comparison on the right-hand side of `hcompare`.
    calc
      (openSubsetHomOfLE_section_iso hWA hAi
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).hom ≫
        (((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i))).map
            ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).hom.app ℱ)).app
          (op (subspace_open_of_le (hWA.trans hAi)))) =
          ((openSubsetHomOfLE_section_iso hWA hAi
              ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).hom ≫
            (((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i))).map
                ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).hom.app ℱ)).app
              (op (subspace_open_of_le (hWA.trans hAi)))) ≫
            eNaive.inv) ≫
              eNaive.hom := by
                ext x
                simp
      _ = (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAi)).map
              ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).hom.app ℱ)).hom.app
            (op (subspace_open_of_le hWA))) ≫
            eNaive.hom := by
              simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eNaive.hom) hcompare
  -- Replace the global section comparison by its naive-model spelling, then reuse `htoNaive`.
  calc
    (openSubsetHomOfLE_section_iso hWA hAi
        ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).hom ≫
      (global_member_section_iso (U := U) ℱ (i := i) (hWA.trans hAi)).hom
        =
      (openSubsetHomOfLE_section_iso hWA hAi
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).hom ≫
        (((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i))).mapIso
            ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).app ℱ)).app
            (op (subspace_open_of_le (hWA.trans hAi)))).hom ≫
          eqToHom (by
            change
              ℱ.1.obj (op ((subspace_inclusion_functor (U i)).obj
                (subspace_open_of_le (hWA.trans hAi)))) =
                ℱ.1.obj (op W)
            simpa [subspace_open_of_le_image_eq]) := by
            rw [global_member_section_iso_hom_eq (U := U) (ℱ := ℱ) (i := i)
              (hWi := hWA.trans hAi)]
            rfl
    _ =
      ((((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAi)).map
            ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hWA))) ≫
        eNaive.hom) ≫
          eqToHom (by
            change
              ℱ.1.obj (op ((subspace_inclusion_functor (U i)).obj
                (subspace_open_of_le (hWA.trans hAi)))) =
                ℱ.1.obj (op W)
            simpa [subspace_open_of_le_image_eq]) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  k ≫ eqToHom (by
                    change
                      ℱ.1.obj (op ((subspace_inclusion_functor (U i)).obj
                        (subspace_open_of_le (hWA.trans hAi)))) =
                        ℱ.1.obj (op W)
                    simpa [subspace_open_of_le_image_eq]))
                htoNaive
    _ =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAi)).map
            ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hWA))) ≫
        eNaive.hom ≫
          eqToHom (by
            change
              ℱ.1.obj (op ((subspace_inclusion_functor (U i)).obj
                (subspace_open_of_le (hWA.trans hAi)))) =
                ℱ.1.obj (op W)
            simpa [subspace_open_of_le_image_eq]) := by
            simp [Category.assoc]

/-- Helper for Lemma 6.33.2: restricting a global sheaf from `B` to `A` and then evaluating on
`W` should agree with first using `pullbackComp` to reach the actual `A`-owner and then applying
the ambient section comparison on `A`. -/
private noncomputable def restrictedAmbientSheafPullbackIso
    (ℱ : X.Sheaf (Type u)) {A B : Opens X} (hAB : A ≤ B) :
    (TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).obj
        ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ) ≅
      (TopCat.Sheaf.pullback (Type u) (openSubsetInclusion A)).obj ℱ :=
  let e :
      TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B) ⋙
          TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB) ≅
        TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB ≫ openSubsetInclusion B) :=
    (TopCat.Sheaf.pullbackComp (A := Type u)
      (openSubsetHomOfLE_6_33_2 hAB) (openSubsetInclusion B) :
        TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B) ⋙
            TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB) ≅
          TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB ≫ openSubsetInclusion B))
  e.app ℱ ≪≫
    eqToIso (congrArg
      (fun f ↦ (TopCat.Sheaf.pullback (Type u) f).obj ℱ)
      (openSubsetHomOfLE_comp_inclusion_6_33_2 hAB))

/-- Helper for Lemma 6.33.2: restricting a global sheaf from `B` to `A` and then evaluating on
`W` should agree with first using `pullbackComp` to reach the actual `A`-owner and then applying
the ambient section comparison on `A`. -/
private theorem actualOwnerOpenEmbeddingComposition_compare
    (ℱ : X.Sheaf (Type u)) {W A B : Opens X}
    (hWA : W ≤ A) (hAB : A ≤ B) :
    let eNaive :=
      openSubsetHomOfLE_section_iso hWA hAB
        (((B).isOpenEmbedding.sheafPullback (Type u)).obj ℱ)
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
          ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).hom.app
        (op (subspace_open_of_le hWA))) ≫
      eNaive.hom ≫
        eqToHom (by
          change
            ℱ.1.obj (op ((subspace_inclusion_functor B).obj
              (subspace_open_of_le (hWA.trans hAB)))) =
              ℱ.1.obj (op W)
          simpa [subspace_open_of_le_image_eq]) =
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hAB)
          (openSubsetInclusion B)).hom.app ℱ).1.app
        (op (subspace_open_of_le hWA))) ≫
      (ambient_open_section_iso (X := X) ℱ hWA).hom := by
  let eNaive :=
    openSubsetHomOfLE_section_iso hWA hAB
      (((B).isOpenEmbedding.sheafPullback (Type u)).obj ℱ)
  let V := op (subspace_open_of_le hWA)
  let pA :
      ℱ.1.obj (op ((subspace_inclusion_functor A).obj (subspace_open_of_le hWA))) =
        ℱ.1.obj (op W) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V)) (subspace_open_of_le_image_eq hWA)
  let pB :
      ℱ.1.obj (op ((subspace_inclusion_functor B).obj
        (subspace_open_of_le (hWA.trans hAB)))) =
        ℱ.1.obj (op W) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V))
      (subspace_open_of_le_image_eq (hWA.trans hAB))
  let mapB :=
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
        ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).hom.app V)
  let compHom :=
    (((TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetHomOfLE_6_33_2 hAB)
        (openSubsetInclusion B)).hom.app ℱ).1.app V)
  let eActual :=
    openSubsetHomOfLE_section_iso hWA hAB
      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ)
  let isoABActual :=
    (((openEmbedding_sheafPullbackIso
        (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hAB)).hom.app
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ)).hom.app V)
  let isoABNaive :=
    (((openEmbedding_sheafPullbackIso
        (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hAB)).hom.app
          (((B).isOpenEmbedding.sheafPullback (Type u)).obj ℱ)).hom.app V)
  let naiveMapB :=
    ((((openSubsetHomOfLE_isOpenEmbedding_6_33_2 hAB).sheafPullback (Type u)).map
      ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).hom.app V)
  let isoB :=
    (((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ).hom.app
      (op (subspace_open_of_le (hWA.trans hAB))))
  let naiveRestrict :=
    (((B).isOpenEmbedding.sheafPullback (Type u)).obj ℱ).1.map
      (eqToHom (congrArg Opposite.op
        (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le hWA hAB)))
  let compIso :=
    (((openEmbedding_sheafPullback_comp_iso
        (openSubsetHomOfLE_isOpenEmbedding_6_33_2 hAB)
        (B).isOpenEmbedding
        (A).isOpenEmbedding).hom.app ℱ).hom.app V)
  let isoA :=
    (((openEmbedding_sheafPullbackIso (A).isOpenEmbedding).hom.app ℱ).hom.app V)
  have hbridge :
      compHom ≫ isoA = isoABActual ≫ naiveMapB ≫ compIso := by
    simpa [V, compHom, isoABActual, naiveMapB, compIso, isoA, InducedCategory.comp_hom,
      NatTrans.comp_app, Category.assoc] using
      congrArg
        (fun η ↦ η.1.app V)
        (openEmbedding_sheafPullbackIso_comp_hom
          (hf := openSubsetHomOfLE_isOpenEmbedding_6_33_2 hAB)
          (hg := (B).isOpenEmbedding)
          (hfg := (A).isOpenEmbedding)
          ℱ)
  have htoActual :
      mapB ≫ eNaive.hom = eActual.hom ≫ isoB := by
    simpa [V, mapB, eActual, eNaive, isoB, TopCat.Sheaf.forget, Category.assoc] using
      openSubsetHomOfLE_section_iso_map_naturality
        (hAB := hWA) (hBC := hAB)
        (η := ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ))
  have htransportNat :
      eActual.hom ≫ isoB =
        isoABActual ≫ naiveMapB ≫ naiveRestrict := by
    ext x
    have hnat :=
      congrFun
        (((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ).hom.naturality
          (eqToHom
            (openSubsetHomOfLE_functor_obj_eq_subspace_open_of_le hWA hAB).symm).op)
        (isoABActual x)
    simpa [eActual, V, isoABActual, naiveMapB, isoB, naiveRestrict,
      openSubsetHomOfLE_section_iso, openSubsetHomOfLE_sheafPullbackIso,
      Topology.IsOpenEmbedding.sheafPullback,
      TopCat.Sheaf.forget, eqToHom_map,
      Category.assoc] using
      hnat
  have htail :
      naiveRestrict ≫ eqToHom pB = compIso ≫ eqToHom pA := by
    have hpB :
        eqToHom pB =
          ℱ.1.map (eqToHom (congrArg Opposite.op
            (subspace_open_of_le_image_eq (hWA.trans hAB)))) := by
      simpa [pB] using
        (CategoryTheory.eqToHom_map ℱ.1
          (congrArg Opposite.op (subspace_open_of_le_image_eq (hWA.trans hAB)))).symm
    have hpA :
        eqToHom pA =
          ℱ.1.map (eqToHom (congrArg Opposite.op
            (subspace_open_of_le_image_eq hWA))) := by
      simpa [pA] using
        (CategoryTheory.eqToHom_map ℱ.1
          (congrArg Opposite.op (subspace_open_of_le_image_eq hWA))).symm
    ext x
    simp [naiveRestrict, compIso, hpB, hpA,
      openEmbedding_sheafPullback_comp_iso, Topology.IsOpenEmbedding.sheafPullback,
      Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
      Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]
    rw [← FunctorToTypes.map_comp_apply]
    congr 1
  have htransport :
      eActual.hom ≫ isoB ≫ eqToHom pB =
        isoABActual ≫ naiveMapB ≫ compIso ≫ eqToHom pA := by
    calc
      eActual.hom ≫ isoB ≫ eqToHom pB =
          (isoABActual ≫ naiveMapB ≫ naiveRestrict) ≫ eqToHom pB := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ eqToHom pB) htransportNat
      _ = isoABActual ≫ naiveMapB ≫ compIso ≫ eqToHom pA := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ isoABActual ≫ naiveMapB ≫ k) htail
  calc
    (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
          ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).hom.app
        (op (subspace_open_of_le hWA))) ≫
      eNaive.hom ≫
        eqToHom (by
          change
            ℱ.1.obj (op ((subspace_inclusion_functor B).obj
              (subspace_open_of_le (hWA.trans hAB)))) =
              ℱ.1.obj (op W)
          simpa [subspace_open_of_le_image_eq])
        =
      (eActual.hom ≫ isoB) ≫ eqToHom pB := by
        simpa [V, mapB, pB, Category.assoc] using
          congrArg (fun k ↦ k ≫ eqToHom pB) htoActual
    _ =
      isoABActual ≫ naiveMapB ≫ compIso ≫ eqToHom pA := by
        simpa [Category.assoc] using htransport
    _ =
      (compHom ≫ isoA) ≫ eqToHom pA := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eqToHom pA) hbridge.symm
    _ =
      (((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 hAB)
            (openSubsetInclusion B)).hom.app ℱ).1.app
          (op (subspace_open_of_le hWA))) ≫
        (ambient_open_section_iso (X := X) ℱ hWA).hom := by
          rw [ambient_open_section_iso_hom_eq (X := X) (ℱ := ℱ) (A := A) (hWA := hWA)]
          rfl

/-- Helper for Lemma 6.33.2: restricting a global sheaf from `B` to `A` and then evaluating on
`W` should agree with first using `pullbackComp` to reach the actual `A`-owner and then applying
the ambient section comparison on `A`. -/
theorem actualOwnerPullbackComp_compare
    (ℱ : X.Sheaf (Type u)) {W A B : Opens X}
    (hWA : W ≤ A) (hAB : A ≤ B) :
    (openSubsetHomOfLE_section_iso hWA hAB
        ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ)).hom ≫
      (ambient_open_section_iso (X := X) ℱ (hWA.trans hAB)).hom =
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetHomOfLE_6_33_2 hAB)
          (openSubsetInclusion B)).hom.app ℱ).1.app
        (op (subspace_open_of_le hWA))) ≫
      (ambient_open_section_iso (X := X) ℱ hWA).hom := by
  let eNaive :=
    openSubsetHomOfLE_section_iso hWA hAB
      (((B).isOpenEmbedding.sheafPullback (Type u)).obj ℱ)
  -- Normalize the left-hand side to the theorem-local naive route, then replace it by `hbridge`.
  calc
    (openSubsetHomOfLE_section_iso hWA hAB
        ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion B)).obj ℱ)).hom ≫
      (ambient_open_section_iso (X := X) ℱ (hWA.trans hAB)).hom
        =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 hAB)).map
            ((openEmbedding_sheafPullbackIso (B).isOpenEmbedding).hom.app ℱ)).hom.app
          (op (subspace_open_of_le hWA))) ≫
        eNaive.hom ≫
          eqToHom (by
            change
              ℱ.1.obj (op ((subspace_inclusion_functor B).obj
                (subspace_open_of_le (hWA.trans hAB)))) =
                ℱ.1.obj (op W)
            simpa [subspace_open_of_le_image_eq]) := by
            simpa [eNaive] using
              ambient_open_section_iso_compare (X := X) (ℱ := ℱ) (hWA := hWA) (hAB := hAB)
    _ =
      (((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetHomOfLE_6_33_2 hAB)
            (openSubsetInclusion B)).hom.app ℱ).1.app
          (op (subspace_open_of_le hWA))) ≫
        (ambient_open_section_iso (X := X) ℱ hWA).hom := by
          simpa [eNaive] using
            actualOwnerOpenEmbeddingComposition_compare
              (X := X) (ℱ := ℱ) (hWA := hWA) (hAB := hAB)

/-- Helper for Lemma 6.33.2: after identifying both subspace opens with their ambient opens, the
subspace-inclusion functor sends the canonical restriction map to the ambient inclusion `W ⟶ V`. -/
private theorem subspace_inclusion_functor_map_eq_homOfLE
    (i : ι) {W V : Opens X}
    (hWi : W ≤ U i) (hVi : V ≤ U i) (hWV : W ≤ V) :
    eqToHom (subspace_open_of_le_image_eq hWi).symm ≫
        (subspace_inclusion_functor (U i)).map (subspace_open_hom hWi hVi hWV) =
      homOfLE hWV ≫ eqToHom (subspace_open_of_le_image_eq hVi).symm := by
  -- Both sides are morphisms between the same ambient opens, and `Opens X` is thin.
  apply Subsingleton.elim

/-- Helper for Lemma 6.33.2: restricting the pulled-back global sheaf between two subordinate
opens of `U i` agrees with first identifying sections with ambient sections and then restricting
in the ambient sheaf. -/
private theorem global_member_section_iso_naturality
    (ℱ : X.Sheaf (Type u)) (i : ι)
    {W V : Opens X} (hWi : W ≤ U i) (hVi : V ≤ U i) (hWV : W ≤ V) :
    ((((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).1.map
        (subspace_open_hom hWi hVi hWV).op) ≫
      (global_member_section_iso (U := U) ℱ (i := i) hWi).hom =
    (global_member_section_iso (U := U) ℱ (i := i) hVi).hom ≫
      ℱ.1.map (homOfLE hWV).op := by
  -- Compare the ordinary pullback with the open-embedding pullback model on both member opens.
  let e :
      (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).1 ≅
        (((U i).isOpenEmbedding.sheafPullback (Type u)).obj ℱ).1 :=
    (TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i))).mapIso
      ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).app ℱ)
  let pW :
      ℱ.1.obj (op ((subspace_inclusion_functor (U i)).obj (subspace_open_of_le hWi))) =
        ℱ.1.obj (op W) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V)) (subspace_open_of_le_image_eq hWi)
  let pV :
      ℱ.1.obj (op ((subspace_inclusion_functor (U i)).obj (subspace_open_of_le hVi))) =
        ℱ.1.obj (op V) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V)) (subspace_open_of_le_image_eq hVi)
  have hnat := e.hom.naturality (subspace_open_hom hWi hVi hWV).op
  have hw :
      ℱ.1.map (eqToHom (subspace_open_of_le_image_eq hWi).symm).op = eqToHom pW := by
    have hw' :
        ℱ.1.map (eqToHom (subspace_open_of_le_image_eq hWi).symm).op =
          eqToHom (congrArg (fun V ↦ ℱ.1.obj (op V)) (subspace_open_of_le_image_eq hWi)) := by
      simpa using
        (CategoryTheory.eqToHom_map ℱ.1
          (congrArg Opposite.op (subspace_open_of_le_image_eq hWi)))
    simpa [pW] using hw'
  have hv :
      ℱ.1.map (eqToHom (subspace_open_of_le_image_eq hVi).symm).op = eqToHom pV := by
    have hv' :
        ℱ.1.map (eqToHom (subspace_open_of_le_image_eq hVi).symm).op =
          eqToHom (congrArg (fun V ↦ ℱ.1.obj (op V)) (subspace_open_of_le_image_eq hVi)) := by
      simpa using
        (CategoryTheory.eqToHom_map ℱ.1
          (congrArg Opposite.op (subspace_open_of_le_image_eq hVi)))
    simpa [pV] using hv'
  have hmap' := congrArg (fun k ↦ ℱ.1.map k.op)
    (subspace_inclusion_functor_map_eq_homOfLE (U := U) i hWi hVi hWV)
  have hmap :
      ℱ.1.map (((subspace_inclusion_functor (U i)).map (subspace_open_hom hWi hVi hWV)).op) ≫
        eqToHom pW =
      eqToHom pV ≫ ℱ.1.map (homOfLE hWV).op := by
    -- Rewrite the endpoint transports as functorial images of the ambient-open equalities.
    rw [← hw, ← hv, ← Functor.map_comp, ← Functor.map_comp]
    exact hmap'
  calc
    (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).1.map
          (subspace_open_hom hWi hVi hWV).op ≫
        (global_member_section_iso (U := U) ℱ (i := i) hWi).hom
        =
      (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj ℱ)).1.map
          (subspace_open_hom hWi hVi hWV).op ≫
        e.hom.app (op (subspace_open_of_le hWi)) ≫ eqToHom pW := by
          rfl
    _ =
      e.hom.app (op (subspace_open_of_le hVi)) ≫
        (((U i).isOpenEmbedding.sheafPullback (Type u)).obj ℱ).1.map
          (subspace_open_hom hWi hVi hWV).op ≫
        eqToHom pW := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eqToHom pW) hnat
    _ =
      e.hom.app (op (subspace_open_of_le hVi)) ≫
        ℱ.1.map (((subspace_inclusion_functor (U i)).map (subspace_open_hom hWi hVi hWV)).op) ≫
        eqToHom pW := by
          rfl
    _ =
      e.hom.app (op (subspace_open_of_le hVi)) ≫
        eqToHom pV ≫ ℱ.1.map (homOfLE hWV).op := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ e.hom.app (op (subspace_open_of_le hVi)) ≫ k) hmap
    _ =
      (e.hom.app (op (subspace_open_of_le hVi)) ≫ eqToHom pV) ≫
        ℱ.1.map (homOfLE hWV).op := by
          simp [Category.assoc]
    _ =
      (global_member_section_iso (U := U) ℱ (i := i) hVi).hom ≫
        ℱ.1.map (homOfLE hWV).op := by
          rfl

/-- Helper for Lemma 6.33.2: the opens of `openSubsetSpace (U i)` coming from ambient opens
contained in `U i`. This is the basis used to compare the restriction of the glued sheaf with the
local sheaf on `U i`. -/
private def memberSubordinateOpens (i : ι) :
    Set (Opens (openSubsetSpace (U i))) :=
  { V | ∃ W : Opens X, ∃ hWi : W ≤ U i, subspace_open_of_le hWi = V }

/-- Helper for Lemma 6.33.2: every open of `openSubsetSpace (U i)` is represented by an ambient
open contained in `U i`. -/
private theorem member_subordinate_open_representation
    (i : ι) (V : Opens (openSubsetSpace (U i))) :
    ∃ W : Opens X, ∃ hWi : W ≤ U i, subspace_open_of_le hWi = V := by
  -- Reuse the generic open-subspace representation lemma at the specific ambient open `U i`.
  exact open_subspace_open_representation (U₀ := U i) V

/-- Helper for Lemma 6.33.2: the opens coming from ambient opens form a basis of
`openSubsetSpace (U i)`. -/
private theorem member_subordinate_opens_isBasis
    (i : ι) :
    Opens.IsBasis (memberSubordinateOpens (U := U) i) := by
  -- Since every open of the subspace already has such an ambient presentation, we can refine any
  -- neighborhood by that very same open.
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨W, hWi, rfl⟩ := member_subordinate_open_representation (U := U) i V
  refine ⟨subspace_open_of_le hWi, ?_, hx, le_rfl⟩
  exact ⟨W, hWi, rfl⟩

/-- Helper for Lemma 6.33.2: once the larger member-basis open is presented by an ambient
subordinate open `V₀ ≤ U i`, any morphism into it is represented by restriction from another
ambient subordinate open `W₀ ≤ V₀`. -/
private theorem member_subordinate_open_hom_representation
    (i : ι)
    {V W : (BasisOpen (memberSubordinateOpens (U := U) i))ᵒᵖ}
    (f : V ⟶ W)
    {V₀ : Opens X}
    (hVi : V₀ ≤ U i)
    (hV : subspace_open_of_le hVi = V.unop.obj) :
    ∃ (W₀ : Opens X) (hWi : W₀ ≤ U i)
      (hW : subspace_open_of_le hWi = W.unop.obj) (hWV : W₀ ≤ V₀),
      eqToHom hW ≫ f.unop.hom =
        subspace_open_hom hWi hVi hWV ≫ eqToHom hV := by
  obtain ⟨W₀, hWi, hW⟩ := member_subordinate_open_representation (U := U) i W.unop.obj
  have hWV : W₀ ≤ V₀ := by
    -- Transport membership along the given basis morphism and then rewrite both opens by the
    -- chosen ambient presentations.
    intro x hx
    have hxWsub : (⟨x, hWi hx⟩ : openSubsetSpace (U i)) ∈ W.unop.obj := by
      have hxWbase : (⟨x, hWi hx⟩ : openSubsetSpace (U i)) ∈ subspace_open_of_le hWi := by
        exact (mem_subspace_open_iff (U := U i) (subspace_open_of_le hWi) ⟨x, hWi hx⟩).2
          (by simpa [subspace_open_of_le_image_eq] using hx)
      simpa [hW] using hxWbase
    have hxVsub : (⟨x, hWi hx⟩ : openSubsetSpace (U i)) ∈ V.unop.obj :=
      f.unop.hom.down.down hxWsub
    have hxVbase : (⟨x, hWi hx⟩ : openSubsetSpace (U i)) ∈ subspace_open_of_le hVi := by
      simpa [hV] using hxVsub
    exact
      by
        simpa [subspace_open_of_le_image_eq] using
          (mem_subspace_open_iff (U := U i) (subspace_open_of_le hVi) ⟨x, hWi hx⟩).1 hxVbase
  refine ⟨W₀, hWi, hW, hWV, ?_⟩
  -- Both sides are morphisms between the same opens of `openSubsetSpace (U i)`, and that category
  -- is thin once source and target are fixed.
  apply Subsingleton.elim

/-- Helper for Lemma 6.33.2: an ambient presentation of a member-basis open is unique, because
including that subspace open back into `X` recovers the ambient open itself. -/
private theorem member_subordinate_open_representation_unique
    (i : ι) {V : Opens (openSubsetSpace (U i))}
    {W₁ W₂ : Opens X}
    (h₁ : W₁ ≤ U i) (h₂ : W₂ ≤ U i)
    (e₁ : subspace_open_of_le h₁ = V) (e₂ : subspace_open_of_le h₂ = V) :
    W₁ = W₂ := by
  -- Compare both presentations after applying the inclusion functor back to ambient opens.
  have h :=
    congrArg (fun A ↦ (subspace_inclusion_functor (U i)).obj A) (e₁.trans e₂.symm)
  simpa [subspace_open_of_le_image_eq] using h

/-- Helper for Lemma 6.33.2: on one subordinate basis open of the ambient cover basis, the
restriction of the extended glued sheaf back to the basis is identified with the original
chosen-chart section. -/
private noncomputable def cover_basis_restrict_extend_component_iso
    (data : SheafOpenCoverGlueing U)
    (W : BasisOpen (coverSubordinateOpens (U := U))) :
    ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)).1.obj
        (op W.obj) ≅
      (open_cover_glueing_basisSheaf data).1.obj (op W) := by
  let G := open_cover_glueing_basisSheaf data
  -- Build the underlying presheaf isomorphism of the basis-extension comparison, then evaluate it
  -- on the chosen basis open.
  let e := BasisSheaf.extendRestrictionIso G (cover_subordinate_opens_isBasis data)
  let d : G.obj ≅
      (BasisSheaf.restrictFromSheaf (cover_subordinate_opens_isBasis data)
        ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data))).obj :=
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := by
        ext U a
        exact congrFun (NatTrans.congr_app (ObjectProperty.isoHom_inv_id_hom e) U) a
      inv_hom_id := by
        ext U a
        exact congrFun (NatTrans.congr_app (ObjectProperty.isoInv_hom_id_hom e) U) a }
  simpa [BasisSheaf.extend, BasisSheaf.restrictFromSheaf] using d.symm.app (op W)

/-- Helper for Lemma 6.33.2: the basis-extension comparison is natural in restriction maps between
subordinate basis opens. -/
private theorem cover_basis_restrict_extend_component_naturality
    (data : SheafOpenCoverGlueing U)
    {W V : BasisOpen (coverSubordinateOpens (U := U))}
    (k : W ⟶ V) :
    (((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)).1.map
        k.hom.op) ≫
      (cover_basis_restrict_extend_component_iso (U := U) data W).hom =
    (cover_basis_restrict_extend_component_iso (U := U) data V).hom ≫
      (open_cover_glueing_basisSheaf data).1.map k.op := by
  let G := open_cover_glueing_basisSheaf data
  let e := BasisSheaf.extendRestrictionIso G (cover_subordinate_opens_isBasis data)
  let d : G.obj ≅
      (BasisSheaf.restrictFromSheaf (cover_subordinate_opens_isBasis data)
        ((open_cover_glueing_basisSheaf data).extend
          (cover_subordinate_opens_isBasis data))).obj :=
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := by
        ext U a
        exact congrFun (NatTrans.congr_app (ObjectProperty.isoHom_inv_id_hom e) U) a
      inv_hom_id := by
        ext U a
        exact congrFun (NatTrans.congr_app (ObjectProperty.isoInv_hom_id_hom e) U) a }
  -- The comparison component is the `op W` section of `d.inv`, so naturality of `d.inv` on `k`
  -- is exactly the desired restriction-compatibility square.
  change
    ((BasisSheaf.restrictFromSheaf (cover_subordinate_opens_isBasis data)
      ((open_cover_glueing_basisSheaf data).extend
        (cover_subordinate_opens_isBasis data))).obj.map k.op) ≫
      (d.inv.app (op W)) =
    (d.inv.app (op V)) ≫
      (open_cover_glueing_basisSheaf data).obj.map k.op
  simpa [G, e, d, BasisSheaf.extend, BasisSheaf.restrictFromSheaf] using
    d.inv.naturality k.op

/-- Helper for Lemma 6.33.2: an explicit ambient representative `W ≤ U i` of a member-basis open
gives the corresponding comparison component between the restricted glued sheaf and `𝓕ᵢ`. -/
private noncomputable abbrev member_space_basis_component_iso_of_rep
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
      ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)))).1.obj
        (op (subspace_open_of_le hWi)) ≅
      (data.localSheaf i).1.obj (op (subspace_open_of_le hWi)) :=
  let F := (open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)
  let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
  -- Compare the restricted glued sheaf with ambient sections on `W`, then pass through the basis
  -- extension comparison and the chosen-chart transport back to the local sheaf `𝓕ᵢ`.
  (global_member_section_iso F hWi) ≪≫
    (cover_basis_restrict_extend_component_iso (U := U) data ambientW) ≪≫
    (subset_chart_iso data (chosen_chart_le ambientW) hWi)

/-- Helper for Lemma 6.33.2: the explicit represented-open component depends only on the ambient
open `W`, not on the proof witnessing `W ≤ U i`. -/
private theorem member_space_basis_component_iso_of_rep_congr
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {W : Opens X}
    {hWi₁ hWi₂ : W ≤ U i} :
    member_space_basis_component_iso_of_rep data i hWi₁ =
      member_space_basis_component_iso_of_rep data i hWi₂ := by
  -- Every proof of `W ≤ U i` is propositionally equal, so the explicit component comparison is
  -- proof-irrelevant.
  cases Subsingleton.elim hWi₁ hWi₂
  rfl

/-- Helper for Lemma 6.33.2: once the chosen ambient representative of a member-basis open is
identified with the explicit ambient open `W`, the endpoint transport isomorphisms in the abstract
basis comparison collapse to identities. -/
private theorem member_space_basis_component_iso_eq_of_rep_transport
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {W W' : Opens X}
    (hWi : W ≤ U i) (hW'i : W' ≤ U i)
    (hV : subspace_open_of_le hW'i = subspace_open_of_le hWi)
    (hWW' : W' = W) :
    let F := (open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)
    let pLeft :
        (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).1.obj
            (op (subspace_open_of_le hWi)) =
          (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).1.obj
            (op (subspace_open_of_le hW'i)) := by
      simpa [hV] using
        congrArg
          (fun A ↦
            (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).1.obj
              (op A))
          hV.symm
    let pRight :
        (data.localSheaf i).1.obj (op (subspace_open_of_le hW'i)) =
          (data.localSheaf i).1.obj (op (subspace_open_of_le hWi)) := by
      simpa [hV] using congrArg (fun A ↦ (data.localSheaf i).1.obj (op A)) hV
    (eqToIso pLeft) ≪≫ member_space_basis_component_iso_of_rep data i hW'i ≪≫
        (eqToIso pRight) =
      member_space_basis_component_iso_of_rep data i hWi := by
  subst hWW'
  -- After replacing the ambient open, the inclusion proof and the represented-open equality are
  -- both propositionally unique, so every transport simplifies to the identity.
  have hhWi : hW'i = hWi := Subsingleton.elim _ _
  subst hhWi
  have hhV : hV = rfl := Subsingleton.elim _ _
  subst hhV
  simp

/-- Helper for Lemma 6.33.2: on a member-basis open of `U i`, the restriction of the extended
glued sheaf agrees with the local sheaf after comparison through the ambient basis extension. -/
private noncomputable def member_space_basis_component_iso
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    (V : BasisOpen (memberSubordinateOpens (U := U) i)) :
    (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
      ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)))).1.obj
        (op V.obj) ≅
      (data.localSheaf i).1.obj (op V.obj) := by
  classical
  let F := (open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)
  let hVrep := member_subordinate_open_representation (U := U) i V.obj
  let W : Opens X := Classical.choose hVrep
  let hWrep : ∃ hWi : W ≤ U i, subspace_open_of_le hWi = V.obj := Classical.choose_spec hVrep
  let hWi : W ≤ U i := Classical.choose hWrep
  let hV : subspace_open_of_le hWi = V.obj := Classical.choose_spec hWrep
  let pLeft :
      (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).1.obj (op V.obj) =
        (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).1.obj
          (op (subspace_open_of_le hWi)) := by
    simpa [hV] using
      congrArg
        (fun A ↦ (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).1.obj
          (op A))
        hV.symm
  let pRight :
      (data.localSheaf i).1.obj (op (subspace_open_of_le hWi)) =
        (data.localSheaf i).1.obj (op V.obj) := by
    simpa [hV] using congrArg (fun A ↦ (data.localSheaf i).1.obj (op A)) hV
  -- Compare the restricted glued sheaf with ambient sections on the represented open, then
  -- transport the result back to the original basis-open presentation.
  exact
    (eqToIso pLeft) ≪≫ member_space_basis_component_iso_of_rep data i hWi ≪≫ (eqToIso pRight)

/-- Helper for Lemma 6.33.2: when a member-basis open is already presented by an explicit ambient
open `W ≤ U i`, the abstract basis-component comparison reduces to that explicit representative
component. -/
private theorem member_space_basis_component_iso_eq_of_rep
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    member_space_basis_component_iso (U := U) data i
        ⟨subspace_open_of_le hWi, ⟨W, hWi, rfl⟩⟩ =
      member_space_basis_component_iso_of_rep data i hWi := by
  classical
  let V : BasisOpen (memberSubordinateOpens (U := U) i) :=
    ⟨subspace_open_of_le hWi, ⟨W, hWi, rfl⟩⟩
  let hVrep := member_subordinate_open_representation (U := U) i V.obj
  let W' : Opens X := Classical.choose hVrep
  let hWrep : ∃ hW'i : W' ≤ U i, subspace_open_of_le hW'i = V.obj := Classical.choose_spec hVrep
  let hW'i : W' ≤ U i := Classical.choose hWrep
  let hV : subspace_open_of_le hW'i = V.obj := Classical.choose_spec hWrep
  have hWW' : W' = W := by
    -- The represented member-basis open already comes from `W`, so uniqueness of ambient
    -- presentations forces the chosen representative to be exactly `W`.
    simpa [V] using
      member_subordinate_open_representation_unique (U := U) i hW'i hWi hV rfl
  -- Unfold the abstract component, replace the chosen representative by `W`, and then collapse
  -- the remaining proof-irrelevant endpoint transports.
  simpa [member_space_basis_component_iso, V, hVrep, W', hWrep, hW'i, hV] using
    member_space_basis_component_iso_eq_of_rep_transport
      (U := U) data i hWi hW'i (by simpa [V] using hV) hWW'

/-- Helper for Lemma 6.33.2: on explicit ambient representatives of member-basis opens, the
comparison components commute with restriction to a smaller ambient open. -/
private theorem member_space_basis_component_naturality_of_rep
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {W V : Opens X}
    (hWi : W ≤ U i) (hVi : V ≤ U i) (hWV : W ≤ V) :
    ((((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
        ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)))).1.map
        (subspace_open_hom hWi hVi hWV).op) ≫
      (member_space_basis_component_iso_of_rep data i hWi).hom =
    (member_space_basis_component_iso_of_rep data i hVi).hom ≫
      (data.localSheaf i).1.map (subspace_open_hom hWi hVi hWV).op := by
  let F := (open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)
  let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
  let ambientV : BasisOpen (coverSubordinateOpens (U := U)) := ⟨V, ⟨i, hVi⟩⟩
  let subsetW := subset_chart_iso data (chosen_chart_le ambientW) hWi
  let subsetV := subset_chart_iso data (chosen_chart_le ambientV) hVi
  let k : ambientW ⟶ ambientV := ⟨homOfLE hWV⟩
  have hglobal :=
    global_member_section_iso_naturality (U := U) F i hWi hVi hWV
  have hcover := cover_basis_restrict_extend_component_naturality (U := U) data k
  have htransport :=
    chosen_chart_transport_naturality
      (U := U) data (V := ambientW) (W := ambientV) (hVW := hWV)
      (j := i) (hWj := hVi)
  have hbasis :
      ((open_cover_glueing_basisSheaf data).1.map k.op) ≫ subsetW.hom =
        subsetV.hom ≫ (data.localSheaf i).1.map (subspace_open_hom hWi hVi hWV).op := by
    -- Rewrite the chosen-chart restriction map through the direct chart change into the fixed
    -- chart `i`, then apply the packaged transport naturality square.
    ext s
    let restricted :=
      (data.localSheaf (chosen_chart ambientV)).1.map
        (subspace_open_hom
          (hWV.trans (chosen_chart_le ambientV))
          (chosen_chart_le ambientV)
          hWV).op s
    have htrans :
        (subset_chart_iso data
            (hWV.trans (chosen_chart_le ambientV))
            (chosen_chart_le ambientW)).hom ≫
          subsetW.hom =
        (subset_chart_iso data
            (hWV.trans (chosen_chart_le ambientV))
            hWi).hom := by
      simpa [subsetW, ambientW, Category.assoc] using
        subset_chart_iso_trans data
          (hWV.trans (chosen_chart_le ambientV))
          (chosen_chart_le ambientW)
          hWi
    have htrans' := congrFun htrans restricted
    have htransport' := congrFun htransport s
    simpa [open_cover_glueing_basisPresheaf_map, subsetW, subsetV, ambientW, ambientV,
        k, restricted, Category.assoc] using htrans'.trans htransport'
  -- Follow the source proof route: ambient restriction, basis-extension comparison, then chart
  -- transport to the fixed local sheaf `𝓕ᵢ`.
  calc
    ((((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).1.map
          (subspace_open_hom hWi hVi hWV).op) ≫
        (member_space_basis_component_iso_of_rep data i hWi).hom
        =
      ((((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).1.map
            (subspace_open_hom hWi hVi hWV).op) ≫
          (global_member_section_iso F hWi).hom ≫
          (cover_basis_restrict_extend_component_iso (U := U) data ambientW).hom ≫
          subsetW.hom := by
            rfl
    _ =
      (global_member_section_iso F hVi).hom ≫
          F.1.map (homOfLE hWV).op ≫
          (cover_basis_restrict_extend_component_iso (U := U) data ambientW).hom ≫
          subsetW.hom := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  t ≫
                    (cover_basis_restrict_extend_component_iso (U := U) data ambientW).hom ≫
                      subsetW.hom)
                hglobal
    _ =
      (global_member_section_iso F hVi).hom ≫
          (cover_basis_restrict_extend_component_iso (U := U) data ambientV).hom ≫
          ((open_cover_glueing_basisSheaf data).1.map k.op) ≫
          subsetW.hom := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ (global_member_section_iso F hVi).hom ≫ t ≫ subsetW.hom) hcover
    _ =
      (global_member_section_iso F hVi).hom ≫
          (cover_basis_restrict_extend_component_iso (U := U) data ambientV).hom ≫
          subsetV.hom ≫
          (data.localSheaf i).1.map (subspace_open_hom hWi hVi hWV).op := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  (global_member_section_iso F hVi).hom ≫
                    (cover_basis_restrict_extend_component_iso (U := U) data ambientV).hom ≫ t)
                hbasis
    _ =
      (member_space_basis_component_iso_of_rep data i hVi).hom ≫
        (data.localSheaf i).1.map (subspace_open_hom hWi hVi hWV).op := by
            rfl

/-- Helper for Lemma 6.33.2: after choosing ambient representatives of two member-basis opens,
the restriction map of `BasisSheaf.restrictFromSheaf` on the source sheaf agrees with the ambient
restriction map up to the endpoint transports coming from those representatives. -/
private theorem member_basis_restrict_from_sheaf_map_transport
    (i : ι)
    {Fext : TopCat.Sheaf (Type u) (openSubsetSpace (U i))}
    {V W : (BasisOpen (memberSubordinateOpens (U := U) i))ᵒᵖ}
    (f : V ⟶ W)
    {V₀ W₀ : Opens X}
    (hVi : V₀ ≤ U i) (hWi : W₀ ≤ U i)
    (hV : subspace_open_of_le hVi = V.unop.obj)
    (hW : subspace_open_of_le hWi = W.unop.obj)
    (hWV : W₀ ≤ V₀)
    (hcomp : eqToHom hW ≫ f.unop.hom = subspace_open_hom hWi hVi hWV ≫ eqToHom hV) :
    (BasisSheaf.restrictFromSheaf (member_subordinate_opens_isBasis (U := U) i) Fext).obj.map f ≫
      eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW.symm) =
    eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hV.symm) ≫
      Fext.1.map (subspace_open_hom hWi hVi hWV).op := by
  -- Expose the underlying presheaf restriction map, then map the representative equality
  -- `hcomp.symm : represented ⟶ W ⟶ V = represented ⟶ V`.
  change Fext.1.map f.unop.hom.op ≫
      eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW.symm) =
    eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hV.symm) ≫
      Fext.1.map (subspace_open_hom hWi hVi hWV).op
  have hcomp' :
      f.unop.hom =
        eqToHom hW.symm ≫ subspace_open_hom hWi hVi hWV ≫ eqToHom hV := by
    simpa [Category.assoc] using congrArg (fun t ↦ eqToHom hW.symm ≫ t) hcomp
  have hmap := congrArg (fun k ↦ Fext.1.map k.op) hcomp'
  have hmap' :=
    congrArg
      (fun t ↦ t ≫ eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW.symm))
      hmap
  simpa [Functor.map_comp, Category.assoc, eqToHom_map] using hmap'

/-- Helper for Lemma 6.33.2: after choosing ambient representatives of two member-basis opens,
the restriction map of `BasisSheaf.restrictFromSheaf` on the target sheaf agrees with the ambient
restriction map up to the endpoint transports coming from those representatives. -/
private theorem member_basis_restrict_target_map_transport
    (i : ι)
    {Fext : TopCat.Sheaf (Type u) (openSubsetSpace (U i))}
    {V W : (BasisOpen (memberSubordinateOpens (U := U) i))ᵒᵖ}
    (f : V ⟶ W)
    {V₀ W₀ : Opens X}
    (hVi : V₀ ≤ U i) (hWi : W₀ ≤ U i)
    (hV : subspace_open_of_le hVi = V.unop.obj)
    (hW : subspace_open_of_le hWi = W.unop.obj)
    (hWV : W₀ ≤ V₀)
    (hcomp : eqToHom hW ≫ f.unop.hom = subspace_open_hom hWi hVi hWV ≫ eqToHom hV) :
    Fext.1.map (subspace_open_hom hWi hVi hWV).op ≫
      eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW) =
    eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hV) ≫
      (BasisSheaf.restrictFromSheaf (member_subordinate_opens_isBasis (U := U) i) Fext).obj.map f := by
  -- Rearrange `hcomp` to isolate the right endpoint transport, then map that equality through the
  -- ambient sheaf.
  change Fext.1.map (subspace_open_hom hWi hVi hWV).op ≫
      eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW) =
    eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hV) ≫
      Fext.1.map f.unop.hom.op
  have hcomp' :
      subspace_open_hom hWi hVi hWV =
        eqToHom hW ≫ f.unop.hom ≫ eqToHom hV.symm := by
    simpa [Category.assoc] using congrArg (fun t ↦ t ≫ eqToHom hV.symm) hcomp.symm
  have hmap := congrArg (fun k ↦ Fext.1.map k.op) hcomp'
  have hmap' :=
    congrArg
      (fun t ↦ t ≫ eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW))
      hmap
  simpa [Functor.map_comp, Category.assoc, eqToHom_map] using hmap'

/-- Helper for Lemma 6.33.2: the restriction of the glued sheaf to the member basis of `U i`
matches the restriction of the local sheaf `𝓕ᵢ` to that same basis. -/
private theorem member_space_basis_component_naturality
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {V W : (BasisOpen (memberSubordinateOpens (U := U) i))ᵒᵖ}
    (f : V ⟶ W) :
    ((BasisSheaf.restrictFromSheaf (member_subordinate_opens_isBasis (U := U) i)
      (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
        ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data))))).obj.map
      f) ≫
      (member_space_basis_component_iso data i W.unop).hom =
    (member_space_basis_component_iso data i V.unop).hom ≫
      (BasisSheaf.restrictFromSheaf (member_subordinate_opens_isBasis (U := U) i)
        (data.localSheaf i)).obj.map f := by
  classical
  let hVrep := member_subordinate_open_representation (U := U) i V.unop.obj
  let V₀ : Opens X := Classical.choose hVrep
  let hVrep' : ∃ hVi : V₀ ≤ U i, subspace_open_of_le hVi = V.unop.obj :=
    Classical.choose_spec hVrep
  let hVi : V₀ ≤ U i := Classical.choose hVrep'
  let hV : subspace_open_of_le hVi = V.unop.obj := Classical.choose_spec hVrep'
  let hWrep := member_subordinate_open_representation (U := U) i W.unop.obj
  let W₀ : Opens X := Classical.choose hWrep
  let hWrep' : ∃ hWi : W₀ ≤ U i, subspace_open_of_le hWi = W.unop.obj :=
    Classical.choose_spec hWrep
  let hWi : W₀ ≤ U i := Classical.choose hWrep'
  let hW : subspace_open_of_le hWi = W.unop.obj := Classical.choose_spec hWrep'
  obtain ⟨W₁, hWi₁, hW₁, hW₁V, hf₁⟩ :=
    member_subordinate_open_hom_representation (U := U) i f hVi hV
  have hWeq : W₁ = W₀ :=
    member_subordinate_open_representation_unique (U := U) i hWi₁ hWi hW₁ hW
  subst hWeq
  have hhWi : hWi₁ = hWi := Subsingleton.elim _ _
  subst hhWi
  have hcomp :
      eqToHom hW ≫ f.unop.hom =
        subspace_open_hom hWi hVi hW₁V ≫ eqToHom hV := by
    simpa using hf₁
  let Fsource :=
    (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
      ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data))))
  have hsource :=
    member_basis_restrict_from_sheaf_map_transport
      (U := U) i (Fext := Fsource) f hVi hWi hV hW hW₁V hcomp
  have hrep :=
    member_space_basis_component_naturality_of_rep
      (U := U) data i hWi hVi hW₁V
  have htarget :=
    member_basis_restrict_target_map_transport
      (U := U) i (Fext := data.localSheaf i) f hVi hWi hV hW hW₁V hcomp
  -- Replace the abstract basis restriction maps by the represented ambient maps and then insert
  -- the explicit representative naturality square between the two endpoint transports.
  have hstep₁ :
      (BasisSheaf.restrictFromSheaf
          (member_subordinate_opens_isBasis (U := U) i) Fsource).obj.map f ≫
        eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hW.symm) ≫
        (member_space_basis_component_iso_of_rep data i hWi).hom ≫
        eqToHom (congrArg (fun A ↦ (data.localSheaf i).1.obj (op A)) hW) =
      eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
        Fsource.1.map (subspace_open_hom hWi hVi hW₁V).op ≫
        (member_space_basis_component_iso_of_rep data i hWi).hom ≫
        eqToHom (congrArg (fun A ↦ (data.localSheaf i).1.obj (op A)) hW) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          k ≫
            (member_space_basis_component_iso_of_rep data i hWi).hom ≫
              eqToHom (congrArg (fun A ↦ (data.localSheaf i).1.obj (op A)) hW))
        hsource
  have hstep₂ :
      eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
        Fsource.1.map (subspace_open_hom hWi hVi hW₁V).op ≫
        (member_space_basis_component_iso_of_rep data i hWi).hom ≫
        eqToHom (congrArg (fun A ↦ (data.localSheaf i).1.obj (op A)) hW) =
      eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
        (member_space_basis_component_iso_of_rep data i hVi).hom ≫
        (data.localSheaf i).1.map (subspace_open_hom hWi hVi hW₁V).op ≫
        eqToHom (congrArg (fun A ↦ (data.localSheaf i).1.obj (op A)) hW) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
            k ≫ eqToHom (congrArg (fun A ↦ (data.localSheaf i).1.obj (op A)) hW))
        hrep
  have hstep₃ :
      eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
        (member_space_basis_component_iso_of_rep data i hVi).hom ≫
        (data.localSheaf i).1.map (subspace_open_hom hWi hVi hW₁V).op ≫
        eqToHom (congrArg (fun A ↦ (data.localSheaf i).1.obj (op A)) hW) =
      eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
        (member_space_basis_component_iso_of_rep data i hVi).hom ≫
        eqToHom (congrArg (fun A ↦ (data.localSheaf i).1.obj (op A)) hV) ≫
        (BasisSheaf.restrictFromSheaf
          (member_subordinate_opens_isBasis (U := U) i) (data.localSheaf i)).obj.map f := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
            (member_space_basis_component_iso_of_rep data i hVi).hom ≫ k)
        htarget
  exact
    (by
      simpa [member_space_basis_component_iso, Fsource, Category.assoc] using
        hstep₁.trans (hstep₂.trans hstep₃))

/-- Helper for Lemma 6.33.2: the restriction of the glued sheaf to the member basis of `U i`
matches the restriction of the local sheaf `𝓕ᵢ` to that same basis. -/
private noncomputable def member_space_basis_restrict_iso
    (data : SheafOpenCoverGlueing U)
    (i : ι) :
    BasisSheaf.restrictFromSheaf (member_subordinate_opens_isBasis (U := U) i)
      (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
        ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)))) ≅
    BasisSheaf.restrictFromSheaf (member_subordinate_opens_isBasis (U := U) i)
      (data.localSheaf i) := by
  let e :
      (BasisSheaf.restrictFromSheaf (member_subordinate_opens_isBasis (U := U) i)
        (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
          ((open_cover_glueing_basisSheaf data).extend
            (cover_subordinate_opens_isBasis data))))).obj ≅
        (BasisSheaf.restrictFromSheaf (member_subordinate_opens_isBasis (U := U) i)
          (data.localSheaf i)).obj :=
    NatIso.ofComponents (fun V ↦ member_space_basis_component_iso data i V.unop) (by
      intro V W f
      exact member_space_basis_component_naturality data i f)
  exact ObjectProperty.isoMk _ e

/-- Helper for Lemma 6.33.2: uniqueness of extension on the member basis of `U i` yields the
local realization isomorphism between the glued sheaf and `𝓕ᵢ`. -/
private noncomputable def member_restrict_extend_iso
    (data : SheafOpenCoverGlueing U)
    (i : ι) :
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
      ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data))) ≅
    data.localSheaf i := by
  let hMi := member_subordinate_opens_isBasis (U := U) i
  let G := BasisSheaf.restrictFromSheaf hMi (data.localSheaf i)
  -- Both sheaves on `openSubsetSpace (U i)` extend the same basis sheaf on subordinate opens.
  exact
    (BasisSheaf.iso_extend_of_restrictIso G hMi
      (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
        ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data))))
      (member_space_basis_restrict_iso (U := U) data i)) ≪≫
    (BasisSheaf.iso_extend_of_restrictIso G hMi (data.localSheaf i) (Iso.refl G)).symm

/-- Helper for Lemma 6.33.2: restricting the inverse dense-subsite counit on a basis open gives
the canonical `restrictExtend` comparison map for the restricted basis sheaf. -/
private theorem basisSheafCounitInv_app_eq_restrictExtendComponentHom
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (Fext : X.Sheaf (Type u))
    (U : (BasisOpen B)ᵒᵖ) :
    ((((basisSheafComparisonEquiv hB).inverse.map
          ((basisSheafComparisonEquiv hB).counitIso.app Fext).inv).hom).app U) =
      BasisSheaf.restrictExtendComponentHom
        (BasisSheaf.restrictFromSheaf hB Fext) hB U := by
  -- The inverse counit becomes the unit comparison after restricting back to the basis.
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  let e :
      BasisSiteSheaf (Type u) B hB ≌ TopCat.Sheaf (Type u) X :=
    (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology X) (Type u)
  simpa [e, basisSheafComparisonEquiv, basisSheafToBasisSiteSheafEquiv,
    BasisSheaf.extend, BasisSheaf.restrictFromSheaf] using
    congrArg (fun f ↦ f.hom.app U)
      (e.unit_app_inverse Fext).symm

/-- Helper for Lemma 6.33.2: restricting the dense-subsite counit on a basis open gives the
inverse `restrictExtend` comparison map for the restricted basis sheaf. -/
private theorem basisSheafCounitHom_app_eq_restrictExtendComponentInv
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (Fext : X.Sheaf (Type u))
    (U : (BasisOpen B)ᵒᵖ) :
    ((((basisSheafComparisonEquiv hB).inverse.map
          ((basisSheafComparisonEquiv hB).counitIso.app Fext).hom).hom).app U) =
      (((BasisSheaf.extendRestrictionIso
            (BasisSheaf.restrictFromSheaf hB Fext) hB).inv.hom).app U) := by
  -- The counit itself restricts to the inverse of the basis extension comparison.
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  let e :
      BasisSiteSheaf (Type u) B hB ≌ TopCat.Sheaf (Type u) X :=
    (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology X) (Type u)
  simpa [e, basisSheafComparisonEquiv, basisSheafToBasisSiteSheafEquiv,
    BasisSheaf.extend, BasisSheaf.restrictFromSheaf] using
    congrArg (fun f ↦ f.hom.app U)
      (e.unitInv_app_inverse Fext).symm

/-- Helper for Lemma 6.33.2: on a represented member-basis open `W ≤ U i`, the basis-level
restriction isomorphism already uses the explicit represented-open comparison map. -/
private theorem member_space_basis_restrict_iso_component_eq_of_rep
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    let F := (open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)
    let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
    (((member_space_basis_restrict_iso (U := U) data i).hom).hom.app
        (op ⟨subspace_open_of_le hWi, ⟨W, hWi, rfl⟩⟩)) =
      (global_member_section_iso F hWi).hom ≫
        (cover_basis_restrict_extend_component_iso (U := U) data ambientW).hom ≫
        (subset_chart_iso data (chosen_chart_le ambientW) hWi).hom := by
  classical
  let F := (open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)
  let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
  let basisW : BasisOpen (memberSubordinateOpens (U := U) i) :=
    ⟨subspace_open_of_le hWi, ⟨W, hWi, rfl⟩⟩
  -- The basis restriction isomorphism was built from `member_space_basis_component_iso`, so on
  -- the represented open `basisW` its component is the explicit represented-open comparison.
  simpa [member_space_basis_restrict_iso, basisW, F, ambientW] using
    congrArg Iso.hom (member_space_basis_component_iso_eq_of_rep (U := U) data i hWi)

/-- Helper for Lemma 6.33.2: restricting the equivalence-image of the member-basis comparison back
along `basisSheafComparisonEquiv.inverse` yields the basis comparison conjugated by the canonical
extension/restriction unit on the member basis. -/
private theorem memberBasisComparisonInverseMapMapIsoComponent
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    let hMi := member_subordinate_opens_isBasis (U := U) i
    let basisW : BasisOpen (memberSubordinateOpens (U := U) i) :=
      ⟨subspace_open_of_le hWi, ⟨W, hWi, rfl⟩⟩
    let Fsource :=
      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
        ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)))
    let G := BasisSheaf.restrictFromSheaf hMi (data.localSheaf i)
    (((basisSheafComparisonEquiv hMi).inverse.map
          (((basisSheafComparisonEquiv hMi).functor.mapIso
              (member_space_basis_restrict_iso (U := U) data i)).hom)).hom).app
        (op basisW) =
      (((BasisSheaf.extendRestrictionIso
            (BasisSheaf.restrictFromSheaf hMi Fsource) hMi).inv.hom).app (op basisW)) ≫
        (((member_space_basis_restrict_iso (U := U) data i).hom).hom.app (op basisW)) ≫
        (((BasisSheaf.extendRestrictionIso G hMi).hom.hom).app (op basisW)) := by
  classical
  let hMi := member_subordinate_opens_isBasis (U := U) i
  let basisW : BasisOpen (memberSubordinateOpens (U := U) i) :=
    ⟨subspace_open_of_le hWi, ⟨W, hWi, rfl⟩⟩
  let Fsource :=
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
      ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)))
  let G := BasisSheaf.restrictFromSheaf hMi (data.localSheaf i)
  -- Apply `Equivalence.inv_fun_map` and then expand the trans-equivalence defining
  -- `basisSheafComparisonEquiv` to the canonical basis extension unit.
  letI :
      (basisOpenInclusion (memberSubordinateOpens (U := U) i)).IsCoverDense
        (Opens.grothendieckTopology (openSubsetSpace (U i))) :=
    basisOpenInclusion_isCoverDense hMi
  let e :
      BasisSiteSheaf (Type u) (memberSubordinateOpens (U := U) i) hMi ≌
        TopCat.Sheaf (Type u) (openSubsetSpace (U i)) :=
    (basisOpenInclusion (memberSubordinateOpens (U := U) i)).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology (openSubsetSpace (U i))) (Type u)
  simpa [e, basisSheafComparisonEquiv, basisSheafToBasisSiteSheafEquiv,
    BasisSheaf.extend, BasisSheaf.restrictFromSheaf, BasisSheaf.extendRestrictionIso,
    Fsource, G, basisW, Category.assoc] using
    congrArg (fun k ↦ k.hom.app (op basisW))
      (CategoryTheory.Equivalence.inv_fun_map
        (basisSheafComparisonEquiv hMi)
        (BasisSheaf.restrictFromSheaf hMi Fsource)
        G
        (member_space_basis_restrict_iso (U := U) data i).hom)

/-- Helper for Lemma 6.33.2: after restricting the packaged local realization isomorphism back to
the member basis of `U i`, its underlying morphism is the composite of the two uniqueness
isomorphisms appearing in the definition of `member_restrict_extend_iso`. -/
private theorem memberRestrictExtendIso_hom_eq
    (data : SheafOpenCoverGlueing U)
    (i : ι) :
    let hMi := member_subordinate_opens_isBasis (U := U) i
    let Fsource :=
      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
        ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)))
    let G := BasisSheaf.restrictFromSheaf hMi (data.localSheaf i)
    (member_restrict_extend_iso (U := U) data i).hom =
      (BasisSheaf.iso_extend_of_restrictIso G hMi Fsource
        (member_space_basis_restrict_iso (U := U) data i)).hom ≫
        (BasisSheaf.iso_extend_of_restrictIso G hMi (data.localSheaf i) (Iso.refl G)).inv := by
  let hMi := member_subordinate_opens_isBasis (U := U) i
  let Fsource :=
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
      ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)))
  let G := BasisSheaf.restrictFromSheaf hMi (data.localSheaf i)
  -- Unfold the packaged isomorphism just once so later component arguments can work with the
  -- explicit composite instead of re-expanding `member_restrict_extend_iso`.
  rfl

/-- Helper for Lemma 6.33.2: after restricting the packaged local realization isomorphism back to
the member basis of `U i`, its component factors through the two canonical
`extendRestrictionIso` boundary comparisons and the basis-level restriction component. -/
private theorem memberRestrictExtendIso_inverseMap_component_factorization
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    let hMi := member_subordinate_opens_isBasis (U := U) i
    let basisW : BasisOpen (memberSubordinateOpens (U := U) i) :=
      ⟨subspace_open_of_le hWi, ⟨W, hWi, rfl⟩⟩
    let Fsource :=
      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
        ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)))
    let G := BasisSheaf.restrictFromSheaf hMi (data.localSheaf i)
    let sourceExtend :=
      BasisSheaf.extendRestrictionIso (BasisSheaf.restrictFromSheaf hMi Fsource) hMi
    let targetExtend := BasisSheaf.extendRestrictionIso G hMi
    let basisComp := ((member_space_basis_restrict_iso (U := U) data i).hom).hom.app (op basisW)
    (((basisSheafComparisonEquiv hMi).inverse.map
          ((member_restrict_extend_iso (U := U) data i).hom)).hom).app
        (op basisW) =
      ((sourceExtend.hom.hom).app (op basisW)) ≫
        ((sourceExtend.inv.hom).app (op basisW)) ≫
        basisComp ≫
        ((targetExtend.hom.hom).app (op basisW)) ≫
        ((targetExtend.inv.hom).app (op basisW)) := by
  -- Route correction: unfold the two uniqueness isomorphisms once, then rewrite each restricted
  -- component in the fixed basis-world spelling already provided by the existing helper lemmas.
  classical
  let hMi := member_subordinate_opens_isBasis (U := U) i
  let basisW : BasisOpen (memberSubordinateOpens (U := U) i) :=
    ⟨subspace_open_of_le hWi, ⟨W, hWi, rfl⟩⟩
  let Fsource :=
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
      ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)))
  let G := BasisSheaf.restrictFromSheaf hMi (data.localSheaf i)
  let sourceExtend :=
    BasisSheaf.extendRestrictionIso (BasisSheaf.restrictFromSheaf hMi Fsource) hMi
  let targetExtend := BasisSheaf.extendRestrictionIso G hMi
  let basisComp := ((member_space_basis_restrict_iso (U := U) data i).hom).hom.app (op basisW)
  have hleft :
      ((((basisSheafComparisonEquiv hMi).inverse.map
            ((basisSheafComparisonEquiv hMi).counitIso.app Fsource).inv).hom).app
          (op basisW)) =
        ((sourceExtend.hom.hom).app (op basisW)) := by
    -- The inverse counit on the source sheaf is exactly the canonical `restrictExtend` component.
    simpa [hMi, Fsource, sourceExtend, basisW] using
      basisSheafCounitInv_app_eq_restrictExtendComponentHom hMi Fsource (op basisW)
  have hmid :
      ((((basisSheafComparisonEquiv hMi).inverse.map
              (((basisSheafComparisonEquiv hMi).functor.mapIso
                (member_space_basis_restrict_iso (U := U) data i)).hom)).hom).app
            (op basisW)) =
        ((sourceExtend.inv.hom).app (op basisW)) ≫
          basisComp ≫
          ((targetExtend.hom.hom).app (op basisW)) := by
    -- The restricted basis comparison already packages the middle three factors in the desired
    -- orientation.
    simpa [hMi, basisW, Fsource, G, sourceExtend, targetExtend, basisComp] using
      memberBasisComparisonInverseMapMapIsoComponent (U := U) data i hWi
  have hright :
      ((((basisSheafComparisonEquiv hMi).inverse.map
              ((BasisSheaf.iso_extend_of_restrictIso G hMi
                (data.localSheaf i) (Iso.refl G)).inv)).hom).app
            (op basisW)) =
        ((targetExtend.inv.hom).app (op basisW)) := by
    have hrefl :
        ((((basisSheafComparisonEquiv hMi).inverse.map
                (((basisSheafComparisonEquiv hMi).functor.mapIso (Iso.refl G)).inv)).hom).app
              (op basisW)) =
          𝟙 _ := by
      -- Mapping the identity comparison isomorphism contributes no extra boundary map.
      simp
    have hrightCounit :
        ((((basisSheafComparisonEquiv hMi).inverse.map
                ((basisSheafComparisonEquiv hMi).counitIso.app (data.localSheaf i)).hom).hom).app
              (op basisW)) =
          ((targetExtend.inv.hom).app (op basisW)) := by
      -- The remaining target-side factor is precisely the counit component already packaged above.
      simpa [G, basisW, targetExtend] using
        basisSheafCounitHom_app_eq_restrictExtendComponentInv hMi (data.localSheaf i) (op basisW)
    -- Expand the target-side uniqueness isomorphism and cancel the mapped identity comparison.
    change
      ((((basisSheafComparisonEquiv hMi).inverse.map
              (((basisSheafComparisonEquiv hMi).functor.mapIso (Iso.refl G)).inv ≫
                ((basisSheafComparisonEquiv hMi).counitIso.app (data.localSheaf i)).hom)).hom).app
            (op basisW)) =
        ((targetExtend.inv.hom).app (op basisW))
    rw [Functor.map_comp]
    change ((((((basisSheafComparisonEquiv hMi).inverse.map
                ((basisSheafComparisonEquiv hMi).functor.mapIso (Iso.refl G)).inv).hom).app
              (op basisW)) ≫
            ((((basisSheafComparisonEquiv hMi).inverse.map
                  ((basisSheafComparisonEquiv hMi).counitIso.app (data.localSheaf i)).hom).hom).app
                (op basisW))) =
          ((targetExtend.inv.hom).app (op basisW)))
    rw [hrefl, hrightCounit]
    simp
  have hsource :
      ((((basisSheafComparisonEquiv hMi).inverse.map
              ((BasisSheaf.iso_extend_of_restrictIso G hMi Fsource
                (member_space_basis_restrict_iso (U := U) data i)).hom)).hom).app
            (op basisW)) =
        ((sourceExtend.hom.hom).app (op basisW)) ≫
          ((sourceExtend.inv.hom).app (op basisW)) ≫
          basisComp ≫
          ((targetExtend.hom.hom).app (op basisW)) := by
    -- Expand only the source-side uniqueness comparison and rewrite each factor separately.
    change
      ((((basisSheafComparisonEquiv hMi).inverse.map
              (((basisSheafComparisonEquiv hMi).counitIso.app Fsource).inv ≫
                ((basisSheafComparisonEquiv hMi).functor.mapIso
                  (member_space_basis_restrict_iso (U := U) data i)).hom)).hom).app
            (op basisW)) =
        ((sourceExtend.hom.hom).app (op basisW)) ≫
          ((sourceExtend.inv.hom).app (op basisW)) ≫
          basisComp ≫
          ((targetExtend.hom.hom).app (op basisW))
    rw [Functor.map_comp]
    change ((((((basisSheafComparisonEquiv hMi).inverse.map
                ((basisSheafComparisonEquiv hMi).counitIso.app Fsource).inv).hom).app
              (op basisW)) ≫
            ((((basisSheafComparisonEquiv hMi).inverse.map
                  ((basisSheafComparisonEquiv hMi).functor.mapIso
                    (member_space_basis_restrict_iso (U := U) data i)).hom)).hom).app
                (op basisW))) =
          (((sourceExtend.hom.hom).app (op basisW)) ≫
            ((sourceExtend.inv.hom).app (op basisW)) ≫
            basisComp ≫
            ((targetExtend.hom.hom).app (op basisW)))
    rw [hleft, hmid]
    rfl
  have hsplit :
      (((basisSheafComparisonEquiv hMi).inverse.map
            ((member_restrict_extend_iso (U := U) data i).hom)).hom).app
          (op basisW) =
        (((basisSheafComparisonEquiv hMi).inverse.map
              ((BasisSheaf.iso_extend_of_restrictIso G hMi Fsource
                (member_space_basis_restrict_iso (U := U) data i)).hom)).hom).app
            (op basisW) ≫
          (((basisSheafComparisonEquiv hMi).inverse.map
              ((BasisSheaf.iso_extend_of_restrictIso G hMi
                (data.localSheaf i) (Iso.refl G)).inv)).hom).app
            (op basisW) := by
    -- Split the packaged local realization isomorphism into its two uniqueness factors.
    rw [memberRestrictExtendIso_hom_eq]
    rw [Functor.map_comp]
    rfl
  -- Combine the split packaged isomorphism with the already normalized source and target factors.
  calc
    (((basisSheafComparisonEquiv hMi).inverse.map
          ((member_restrict_extend_iso (U := U) data i).hom)).hom).app
        (op basisW)
      =
        (((basisSheafComparisonEquiv hMi).inverse.map
              ((BasisSheaf.iso_extend_of_restrictIso G hMi Fsource
                (member_space_basis_restrict_iso (U := U) data i)).hom)).hom).app
            (op basisW) ≫
          (((basisSheafComparisonEquiv hMi).inverse.map
              ((BasisSheaf.iso_extend_of_restrictIso G hMi
                (data.localSheaf i) (Iso.refl G)).inv)).hom).app
            (op basisW) := hsplit
    _ =
        (((sourceExtend.hom.hom).app (op basisW)) ≫
          ((sourceExtend.inv.hom).app (op basisW)) ≫
          basisComp ≫
          ((targetExtend.hom.hom).app (op basisW))) ≫
          ((targetExtend.inv.hom).app (op basisW)) := by
            rw [hsource, hright]
    _ =
        ((sourceExtend.hom.hom).app (op basisW)) ≫
          ((sourceExtend.inv.hom).app (op basisW)) ≫
          basisComp ≫
          ((targetExtend.hom.hom).app (op basisW)) ≫
          ((targetExtend.inv.hom).app (op basisW)) := by
            simp [Category.assoc]

/-- Helper for Lemma 6.33.2: after restricting the packaged local realization isomorphism back to
the member basis of `U i`, its component on a represented basis open is exactly the component of
the basis-level restriction isomorphism. -/
private theorem memberRestrictExtendIso_inverseMap_app_eq_basisRestrictComponent
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    let hMi := member_subordinate_opens_isBasis (U := U) i
    let basisW : BasisOpen (memberSubordinateOpens (U := U) i) :=
      ⟨subspace_open_of_le hWi, ⟨W, hWi, rfl⟩⟩
    (((basisSheafComparisonEquiv hMi).inverse.map
          ((member_restrict_extend_iso (U := U) data i).hom)).hom).app
        (op basisW) =
      (((member_space_basis_restrict_iso (U := U) data i).hom).hom.app (op basisW)) := by
  -- Route correction: stay in the basis-world spelling and factor the component through the two
  -- `extendRestrictionIso` boundary maps before canceling them.
  classical
  let hMi := member_subordinate_opens_isBasis (U := U) i
  let basisW : BasisOpen (memberSubordinateOpens (U := U) i) :=
    ⟨subspace_open_of_le hWi, ⟨W, hWi, rfl⟩⟩
  let Fsource :=
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj
      ((open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)))
  let G := BasisSheaf.restrictFromSheaf hMi (data.localSheaf i)
  let sourceExtend :=
    BasisSheaf.extendRestrictionIso (BasisSheaf.restrictFromSheaf hMi Fsource) hMi
  let targetExtend := BasisSheaf.extendRestrictionIso G hMi
  let basisComp := ((member_space_basis_restrict_iso (U := U) data i).hom).hom.app (op basisW)
  have hfactor :
      (((basisSheafComparisonEquiv hMi).inverse.map
            ((member_restrict_extend_iso (U := U) data i).hom)).hom).app
          (op basisW) =
        ((sourceExtend.hom.hom).app (op basisW)) ≫
          ((sourceExtend.inv.hom).app (op basisW)) ≫
          basisComp ≫
          ((targetExtend.hom.hom).app (op basisW)) ≫
          ((targetExtend.inv.hom).app (op basisW)) := by
    -- Expand once to the boundary-factor normal form and leave only iso cancellation.
    simpa [hMi, Fsource, G, basisW, sourceExtend, targetExtend, basisComp] using
      memberRestrictExtendIso_inverseMap_component_factorization (U := U) data i hWi
  -- Cancel the source and target boundary pairs componentwise.
  have hsource :
      ((sourceExtend.hom.hom).app (op basisW)) ≫
          ((sourceExtend.inv.hom).app (op basisW)) =
        𝟙 _ := by
    change (((sourceExtend.hom ≫ sourceExtend.inv).hom).app (op basisW)) = 𝟙 _
    simpa using congrArg (fun f ↦ f.hom.app (op basisW)) sourceExtend.hom_inv_id
  have htarget :
      ((targetExtend.hom.hom).app (op basisW)) ≫
          ((targetExtend.inv.hom).app (op basisW)) =
        𝟙 _ := by
    change (((targetExtend.hom ≫ targetExtend.inv).hom).app (op basisW)) = 𝟙 _
    simpa using congrArg (fun f ↦ f.hom.app (op basisW)) targetExtend.hom_inv_id
  calc
    (((basisSheafComparisonEquiv hMi).inverse.map
          ((member_restrict_extend_iso (U := U) data i).hom)).hom).app
        (op basisW)
      =
        ((sourceExtend.hom.hom).app (op basisW)) ≫
          ((sourceExtend.inv.hom).app (op basisW)) ≫
          basisComp ≫
          ((targetExtend.hom.hom).app (op basisW)) ≫
          ((targetExtend.inv.hom).app (op basisW)) := hfactor
    _ = ((((sourceExtend.hom.hom).app (op basisW)) ≫
            ((sourceExtend.inv.hom).app (op basisW))) ≫
          basisComp) ≫
        (((targetExtend.hom.hom).app (op basisW)) ≫
          ((targetExtend.inv.hom).app (op basisW))):= by
      simp [Category.assoc]
    _ = basisComp := by
      rw [hsource, htarget]
      exact Category.comp_id basisComp

/-- Helper for Lemma 6.33.2: on a represented member-basis open `W ≤ U i`, the local realization
isomorphism is exactly the explicit basis-component comparison already constructed on that open. -/
private theorem member_basis_counit_component_formula
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    let hMi := member_subordinate_opens_isBasis (U := U) i
    let G := BasisSheaf.restrictFromSheaf hMi (data.localSheaf i)
    let F := (open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)
    let Fsource := ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)
    let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
    (((BasisSheaf.iso_extend_of_restrictIso G hMi Fsource
          (member_space_basis_restrict_iso (U := U) data i)).hom ≫
        (BasisSheaf.iso_extend_of_restrictIso G hMi (data.localSheaf i) (Iso.refl G)).inv).1.app
          (op (subspace_open_of_le hWi))) =
      (global_member_section_iso F hWi).hom ≫
        (cover_basis_restrict_extend_component_iso (U := U) data ambientW).hom ≫
        (subset_chart_iso data (chosen_chart_le ambientW) hWi).hom := by
  classical
  let hMi := member_subordinate_opens_isBasis (U := U) i
  let G := BasisSheaf.restrictFromSheaf hMi (data.localSheaf i)
  let F := (open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)
  let Fsource := ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)
  let basisW : BasisOpen (memberSubordinateOpens (U := U) i) :=
    ⟨subspace_open_of_le hWi, ⟨W, hWi, rfl⟩⟩
  let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
  dsimp [hMi, G, F, Fsource, ambientW]
  have hleft :
      (((basisSheafComparisonEquiv hMi).inverse.map
            ((basisSheafComparisonEquiv hMi).counitIso.app Fsource).inv).hom).app
          (op basisW) =
        BasisSheaf.restrictExtendComponentHom
          (BasisSheaf.restrictFromSheaf hMi Fsource) hMi (op basisW) := by
    -- Rewrite the inverse counit component to the canonical basis `restrictExtend` map.
    simpa [basisW] using
      basisSheafCounitInv_app_eq_restrictExtendComponentHom hMi Fsource (op basisW)
  have hright :
      (((basisSheafComparisonEquiv hMi).inverse.map
            ((basisSheafComparisonEquiv hMi).counitIso.app (data.localSheaf i)).hom).hom).app
          (op basisW) =
        (((BasisSheaf.extendRestrictionIso G hMi).inv.hom).app (op basisW)) := by
    -- Rewrite the counit component on the `Iso.refl G` side to the inverse basis comparison.
    simpa [G, basisW] using
      basisSheafCounitHom_app_eq_restrictExtendComponentInv hMi (data.localSheaf i) (op basisW)
  have hmid :=
    member_space_basis_restrict_iso_component_eq_of_rep (U := U) data i hWi
  dsimp [F, ambientW] at hmid
  have hnorm :
      (((basisSheafComparisonEquiv hMi).inverse.map
            ((member_restrict_extend_iso (U := U) data i).hom)).hom).app
          (op basisW) =
        (((member_space_basis_restrict_iso (U := U) data i).hom).hom.app
          (op basisW)) := by
    -- Normalize the packaged local realization isomorphism on the member basis before returning
    -- to the represented-open section comparison.
    simpa [hMi, basisW] using
      memberRestrictExtendIso_inverseMap_app_eq_basisRestrictComponent
        (U := U) data i hWi
  -- Rewrite the sheaf-level component through the basis comparison and then apply the explicit
  -- represented-open basis formula.
  change (((basisSheafComparisonEquiv hMi).inverse.map
        ((member_restrict_extend_iso (U := U) data i).hom)).hom).app
      (op basisW) =
    (global_member_section_iso F hWi).hom ≫
      (cover_basis_restrict_extend_component_iso (U := U) data ambientW).hom ≫
      (subset_chart_iso data (chosen_chart_le ambientW) hWi).hom
  rw [hnorm]
  simpa [basisW] using hmid

/-- Helper for Lemma 6.33.2: on a represented member-basis open `W ≤ U i`, the local realization
isomorphism is exactly the explicit basis-component comparison already constructed on that open. -/
private theorem member_restrict_extend_iso_component_eq_of_rep
    (data : SheafOpenCoverGlueing U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    ((member_restrict_extend_iso (U := U) data i).hom).1.app
        (op (subspace_open_of_le hWi)) =
      (member_space_basis_component_iso_of_rep data i hWi).hom := by
  classical
  let hMi := member_subordinate_opens_isBasis (U := U) i
  let G := BasisSheaf.restrictFromSheaf hMi (data.localSheaf i)
  let F := (open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)
  let Fsource := ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)
  let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
  -- Unfold the packaged local realization isomorphism to the single represented-open comparison.
  change (((BasisSheaf.iso_extend_of_restrictIso G hMi Fsource
        (member_space_basis_restrict_iso (U := U) data i)).hom ≫
      (BasisSheaf.iso_extend_of_restrictIso G hMi (data.localSheaf i) (Iso.refl G)).inv).1.app
        (op (subspace_open_of_le hWi))) =
    (global_member_section_iso F hWi).hom ≫
      (cover_basis_restrict_extend_component_iso (U := U) data ambientW).hom ≫
      (subset_chart_iso data (chosen_chart_le ambientW) hWi).hom
  simpa [member_space_basis_component_iso_of_rep, F, ambientW] using
    member_basis_counit_component_formula (U := U) data i hWi

/-- Helper for Lemma 6.33.2: once an ambient basis section on `W` is fixed, transporting it first
to `U i` and then across the overlap to `U j` is the same as transporting it directly to `U j`. -/
private theorem chosenChartOverlapTransport_hom
    (data : SheafOpenCoverGlueing U)
    {W : Opens X} {i j : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j) :
    let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
    (subset_chart_iso data (chosen_chart_le ambientW) hWi).hom ≫
      (subset_chart_iso data hWi hWj).hom =
        (subset_chart_iso data (chosen_chart_le ambientW) hWj).hom := by
  let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
  -- This is the morphism-level chosen-chart transport packaged from `subset_chart_iso_trans`.
  simpa [ambientW] using
    subset_chart_iso_trans data (chosen_chart_le ambientW) hWi hWj

/-- Helper for Lemma 6.33.2: once an ambient basis section on `W` is fixed, transporting it first
to `U i` and then across the overlap to `U j` is the same as transporting it directly to `U j`. -/
private theorem chosenChartOverlapTransport_apply
    (data : SheafOpenCoverGlueing U)
    {W : Opens X} {i j : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j)
    (t :
      (open_cover_glueing_basisSheaf data).1.obj
        (op ({ obj := W, property := ⟨i, hWi⟩ } :
          BasisOpen (coverSubordinateOpens (U := U))))) :
    let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
    ((subset_chart_iso data (chosen_chart_le ambientW) hWi).hom ≫
        (subset_chart_iso data hWi hWj).hom) t =
      (subset_chart_iso data (chosen_chart_le ambientW) hWj).hom t := by
  let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
  -- This is the represented-open evaluation of `subset_chart_iso_trans` at the ambient basis
  -- section `t`.
  simpa [ambientW, Category.assoc] using
    congrFun
      (chosenChartOverlapTransport_hom (U := U) data hWi hWj)
      t

/-- Helper for Lemma 6.33.2: two subordinate basis-open representatives of the same ambient open
are equal, regardless of which cover member witness is used. -/
private theorem coverSubordinateBasisOpen_eq_of_same_open
    {W : Opens X} {i j : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j) :
    (⟨W, ⟨i, hWi⟩⟩ : BasisOpen (coverSubordinateOpens (U := U))) =
      ⟨W, ⟨j, hWj⟩⟩ := by
  -- A subordinate basis open is determined by its ambient open; the witness lies in a
  -- proposition and is therefore proof-irrelevant.
  ext
  rfl

/-- Lemma 6.33.2: every gluing datum of sheaves of sets on an open cover is realized by a sheaf on
the ambient space. -/
theorem exists_sheaf_realizing_open_cover_glueing
    (data : SheafOpenCoverGlueing U) :
    ∃ F : X.Sheaf (Type u), data.Realizes F := by
  -- Route correction: the first-proof `CompatibleFamily` carrier has been removed. The remaining
  -- source-faithful route is to extend `open_cover_glueing_basisSheaf data` via Lemma 6.30.6 and
  -- then build the realization isomorphisms from `BasisSheaf.restrictExtendComponentHom`.
  let F := (open_cover_glueing_basisSheaf data).extend (cover_subordinate_opens_isBasis data)
  refine ⟨F, ?_⟩
  unfold SheafOpenCoverGlueing.Realizes
  let φ :
      ∀ i : ι, ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F) ≅
        data.localSheaf i :=
    fun i ↦
      -- The local realization isomorphism is now packaged by uniqueness of extension on the
      -- member basis of each `U i`.
      member_restrict_extend_iso (U := U) data i
  refine ⟨φ, ?_⟩
  intro i j
  -- The overlap comparison is a morphism equality of sheaves on `openSubsetSpace (U i ⊓ U j)`;
  -- extensionality reduces it to equality on every open and then on each section.
  apply CategoryTheory.Sheaf.hom_ext
  apply CategoryTheory.NatTrans.ext
  funext V
  ext s
  obtain ⟨W, hW, hV⟩ :=
    open_subspace_open_representation (U₀ := U i ⊓ U j) V.unop
  have hVop : V = op (subspace_open_of_le hW) := by
    apply Opposite.unop_injective
    simpa using hV.symm
  subst hVop
  have hWi : W ≤ U i := fun x hx ↦ (hW hx).1
  have hWj : W ≤ U j := fun x hx ↦ (hW hx).2
  have hpair :
      pair_overlap_open (U := U) W i j = subspace_open_of_le hW := by
    exact pair_overlap_open_eq_subspace_open_of_le (U := U) hW
  have hleft :
      left_overlap_open (U := U) W i j = subspace_open_of_le hWi := by
    exact left_overlap_open_eq_subspace_open_of_le (U := U) hW
  have hright :
      right_overlap_open (U := U) W i j = subspace_open_of_le hWj := by
    exact right_overlap_open_eq_subspace_open_of_le (U := U) hW
  have hφi := member_restrict_extend_iso_component_eq_of_rep (U := U) data i hWi
  have hφj := member_restrict_extend_iso_component_eq_of_rep (U := U) data j hWj
  let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
  have htrans :
      (subset_chart_iso data (chosen_chart_le ambientW) hWi).hom ≫
        (subset_chart_iso data hWi hWj).hom =
      (subset_chart_iso data (chosen_chart_le ambientW) hWj).hom := by
    simpa [ambientW] using
      chosenChartOverlapTransport_hom (U := U) data hWi hWj
  -- On the represented overlap open, both realization branches reduce to the same chart-change
  -- composite from the chosen chart of `W` to the fixed chart `j`.
  let t : (open_cover_glueing_basisSheaf data).1.obj (op ambientW) :=
    (cover_basis_restrict_extend_component_iso (U := U) data ambientW).hom
      (((global_member_section_iso (U := U) F (i := i) hWi).hom)
        ((openSubsetHomOfLE_section_iso hW inf_le_left
            ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).hom
          ((((TopCat.Sheaf.pullbackComp (A := Type u)
                (openSubsetIntersectionLeftInclusion (U i) (U j))
                (openSubsetInclusion (U i))).inv.app F).hom.app
              (op (subspace_open_of_le hW))) s)))
  have ht :
      ((subset_chart_iso data (chosen_chart_le ambientW) hWi).hom ≫
          (subset_chart_iso data hWi hWj).hom) t =
        (subset_chart_iso data (chosen_chart_le ambientW) hWj).hom t := by
    -- Package the chosen-chart transport once so the remaining blocker is only the endpoint input.
    simpa [ambientW] using chosenChartOverlapTransport_apply (U := U) data hWi hWj t
  have hφi_overlap :
      let component_i :=
        ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i))).map (φ i).hom).app
          (op (subspace_open_of_le hWi))
      (((TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionLeftInclusion (U i) (U j))).map (φ i).hom).hom.app
          (op (subspace_open_of_le hW))) =
        (openSubsetHomOfLE_section_iso hW inf_le_left
            ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).hom ≫
          component_i ≫
          (openSubsetHomOfLE_section_iso hW inf_le_left (data.localSheaf i)).inv := by
    simpa [Category.assoc] using
      (openSubsetHomOfLE_section_iso_map_compare
        (hAB := hW)
        (hBC := inf_le_left)
        (η := (φ i).hom)).symm
  have hφj_overlap :
      let component_j :=
        ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U j))).map (φ j).hom).app
          (op (subspace_open_of_le hWj))
      (((TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionRightInclusion (U i) (U j))).map (φ j).hom).hom.app
          (op (subspace_open_of_le hW))) =
        (openSubsetHomOfLE_section_iso hW inf_le_right
            ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F)).hom ≫
          component_j ≫
          (openSubsetHomOfLE_section_iso hW inf_le_right (data.localSheaf j)).inv := by
    simpa [Category.assoc] using
      (openSubsetHomOfLE_section_iso_map_compare
        (hAB := hW)
        (hBC := inf_le_right)
        (η := (φ j).hom)).symm
  have hφi_app :
      ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i))).map (φ i).hom).app
          (op (subspace_open_of_le hWi)) =
        (member_space_basis_component_iso_of_rep data i hWi).hom := by
    simpa [φ] using hφi
  have hφj_app :
      ((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U j))).map (φ j).hom).app
          (op (subspace_open_of_le hWj)) =
        (member_space_basis_component_iso_of_rep data j hWj).hom := by
    simpa [φ] using hφj
  have hφi_overlap' :
      (((TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionLeftInclusion (U i) (U j))).map (φ i).hom).hom.app
          (op (subspace_open_of_le hW))) =
        (openSubsetHomOfLE_section_iso hW inf_le_left
            ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).hom ≫
          (member_space_basis_component_iso_of_rep data i hWi).hom ≫
          (openSubsetHomOfLE_section_iso hW inf_le_left (data.localSheaf i)).inv := by
    simpa [hφi_app, member_space_basis_component_iso_of_rep, Category.assoc] using hφi_overlap
  have hφj_overlap' :
      (((TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionRightInclusion (U i) (U j))).map (φ j).hom).hom.app
          (op (subspace_open_of_le hW))) =
        (openSubsetHomOfLE_section_iso hW inf_le_right
            ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F)).hom ≫
          (member_space_basis_component_iso_of_rep data j hWj).hom ≫
          (openSubsetHomOfLE_section_iso hW inf_le_right (data.localSheaf j)).inv := by
    simpa [hφj_app, member_space_basis_component_iso_of_rep, Category.assoc] using hφj_overlap
  change
    ((((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetIntersectionLeftInclusion (U i) (U j))
            (openSubsetInclusion (U i))).inv.app F ≫
          ((TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionLeftInclusion (U i) (U j))).map (φ i).hom) ≫
            (data.overlapIso i j).hom).hom.app
        (op (subspace_open_of_le hW))) s =
      ((((TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetIntersectionRightInclusion (U i) (U j))
            (openSubsetInclusion (U j))).inv.app F ≫
          ((TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionRightInclusion (U i) (U j))).map (φ j).hom)).hom.app
        (op (subspace_open_of_le hW))) s))
  let leftApp :=
    ((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U j))
          (openSubsetInclusion (U i))).inv.app F ≫
        ((TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionLeftInclusion (U i) (U j))).map (φ i).hom) ≫
          (data.overlapIso i j).hom).hom.app (op (subspace_open_of_le hW))
  let rightApp :=
    ((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))
          (openSubsetInclusion (U j))).inv.app F ≫
        ((TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionRightInclusion (U i) (U j))).map (φ j).hom)).hom.app
      (op (subspace_open_of_le hW))
  let leftEval := leftApp s
  let rightEval := rightApp s
  let leftInput :=
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U j))
          (openSubsetInclusion (U i))).inv.app F).hom.app
      (op (subspace_open_of_le hW)) s)
  let rightInput :=
    (((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))
          (openSubsetInclusion (U j))).inv.app F).hom.app
      (op (subspace_open_of_le hW)) s)
  let rightSection := openSubsetHomOfLE_section_iso hW inf_le_right (data.localSheaf j)
  have hrightSection_inj : Function.Injective rightSection.hom := by
    intro a b hab
    simpa using congrArg rightSection.inv hab
  have overlapAmbientInputEq :
      (global_member_section_iso (U := U) F (i := i) hWi).hom
          ((openSubsetHomOfLE_section_iso hW inf_le_left
              ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).hom
            leftInput) =
        (global_member_section_iso (U := U) F (i := j) hWj).hom
          ((openSubsetHomOfLE_section_iso hW inf_le_right
            ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F)).hom
            rightInput) := by
    let overlapGlobal :
        (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i ⊓ U j))).obj F)).1.obj
            (op (subspace_open_of_le hW)) ≅
          F.1.obj (op W) :=
      ambient_open_section_iso (X := X) F hW
    let leftGlobalIso :
        (TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionLeftInclusion (U i) (U j))).obj
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F) ≅
        (TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i ⊓ U j))).obj F :=
      (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U j))
          (openSubsetInclusion (U i))).app F ≪≫
        eqToIso (congrArg
          (fun f ↦ (TopCat.Sheaf.pullback (Type u) f).obj F)
          (openSubsetHomOfLE_comp_inclusion_6_33_2 (W := U i ⊓ U j) (U := U i) inf_le_left))
    let rightGlobalIso :
        (TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionRightInclusion (U i) (U j))).obj
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F) ≅
        (TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i ⊓ U j))).obj F :=
      (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))
          (openSubsetInclusion (U j))).app F ≪≫
        eqToIso (congrArg
          (fun f ↦ (TopCat.Sheaf.pullback (Type u) f).obj F)
          (openSubsetHomOfLE_comp_inclusion_6_33_2 (W := U i ⊓ U j) (U := U j) inf_le_right))
    have naiveBranchToActualOverlapGlobal_apply
        {k : ι} (branch : U i ⊓ U j ≤ U k)
        (branchGlobalIso :
          (TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 branch)).obj
              ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U k))).obj F) ≅
            (TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i ⊓ U j))).obj F)
        (branchInput :
          (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 branch)).obj
              ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U k))).obj F))).1.obj
            (op (subspace_open_of_le hW)))
        (hbranchCompare :
          let branchNaiveMap :=
            (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 branch)).map
                  ((openEmbedding_sheafPullbackIso (U k).isOpenEmbedding).hom.app F)).hom.app
                (op (subspace_open_of_le hW))) ≫
              (openSubsetHomOfLE_section_iso hW branch
                  (((U k).isOpenEmbedding.sheafPullback (Type u)).obj F)).hom ≫
                eqToHom (by
                  change
                    F.1.obj (op ((subspace_inclusion_functor (U k)).obj
                      (subspace_open_of_le (hW.trans branch)))) =
                      F.1.obj (op W)
                  simpa [subspace_open_of_le_image_eq])
          branchNaiveMap =
            ((branchGlobalIso.hom).1.app (op (subspace_open_of_le hW))) ≫ overlapGlobal.hom)
        (hcancel :
          ((branchGlobalIso.hom).1.app (op (subspace_open_of_le hW))) branchInput = s) :
        let branchNaiveMap :=
          (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 branch)).map
                ((openEmbedding_sheafPullbackIso (U k).isOpenEmbedding).hom.app F)).hom.app
              (op (subspace_open_of_le hW))) ≫
            (openSubsetHomOfLE_section_iso hW branch
                (((U k).isOpenEmbedding.sheafPullback (Type u)).obj F)).hom ≫
              eqToHom (by
                change
                  F.1.obj (op ((subspace_inclusion_functor (U k)).obj
                    (subspace_open_of_le (hW.trans branch)))) =
                    F.1.obj (op W)
                simpa [subspace_open_of_le_image_eq])
        branchNaiveMap branchInput = overlapGlobal.hom s := by
      -- Route correction: the pointwise branch step is only valid after normalizing the branch
      -- morphism itself to the common overlap owner.
      have hbranchApp := congrFun hbranchCompare branchInput
      simpa [Category.assoc, hcancel] using hbranchApp
    have branchActualToOverlapGlobal_compare
        {k : ι} (branch : U i ⊓ U j ≤ U k) :
        let branchGlobalIso :
            (TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 branch)).obj
                ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U k))).obj F) ≅
              (TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i ⊓ U j))).obj F :=
          (TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetHomOfLE_6_33_2 branch)
              (openSubsetInclusion (U k))).app F ≪≫
            eqToIso (congrArg
              (fun f ↦ (TopCat.Sheaf.pullback (Type u) f).obj F)
              (openSubsetHomOfLE_comp_inclusion_6_33_2 (W := U i ⊓ U j) (U := U k) branch))
        let branchNaiveMap :=
          (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 branch)).map
                ((openEmbedding_sheafPullbackIso (U k).isOpenEmbedding).hom.app F)).hom.app
              (op (subspace_open_of_le hW))) ≫
            (openSubsetHomOfLE_section_iso hW branch
                (((U k).isOpenEmbedding.sheafPullback (Type u)).obj F)).hom ≫
              eqToHom (by
                change
                  F.1.obj (op ((subspace_inclusion_functor (U k)).obj
                    (subspace_open_of_le (hW.trans branch)))) =
                    F.1.obj (op W)
                simpa [subspace_open_of_le_image_eq])
        branchNaiveMap =
          ((branchGlobalIso.hom).1.app (op (subspace_open_of_le hW))) ≫ overlapGlobal.hom := by
      let branchNaiveMap :=
        (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 branch)).map
              ((openEmbedding_sheafPullbackIso (U k).isOpenEmbedding).hom.app F)).hom.app
            (op (subspace_open_of_le hW))) ≫
          (openSubsetHomOfLE_section_iso hW branch
              (((U k).isOpenEmbedding.sheafPullback (Type u)).obj F)).hom ≫
            eqToHom (by
              change
                F.1.obj (op ((subspace_inclusion_functor (U k)).obj
                  (subspace_open_of_le (hW.trans branch)))) =
                  F.1.obj (op W)
              simpa [subspace_open_of_le_image_eq])
      -- Rewrite the branch-owned naive restriction to the actual owner first.
      have htoActual :
          branchNaiveMap =
            (openSubsetHomOfLE_section_iso hW branch
                ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U k))).obj F)).hom ≫
              (ambient_open_section_iso (X := X) F (hW.trans branch)).hom := by
        simpa [branchNaiveMap, global_member_section_iso, Category.assoc] using
          (memberSectionToNaiveGlobal_compare
            (U := U) (ℱ := F) (i := k) (hWA := hW) (hAi := branch)).symm
      -- Route correction: after normalizing to the actual owner, the overlap transport is exactly
      -- the generic owner-side `pullbackComp` comparison.
      exact htoActual.trans <|
        by
          simpa [Category.assoc] using
            actualOwnerPullbackComp_compare
              (X := X) (ℱ := F) (hWA := hW) (hAB := branch)
    -- Express each two-step ambient restriction through the corresponding direct overlap pullback.
    have hleftPoint' :
        (global_member_section_iso (U := U) F (i := i) hWi).hom
            ((openSubsetHomOfLE_section_iso hW inf_le_left
                ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).hom
              leftInput) =
          overlapGlobal.hom s := by
      have hhWi : hW.trans inf_le_left = hWi := Subsingleton.elim _ _
      have hleftCancel :
          ((leftGlobalIso.hom).1.app (op (subspace_open_of_le hW))) leftInput = s := by
        simpa [leftInput, leftGlobalIso, Category.assoc] using
          congrFun
            (congrArg
              (fun k ↦ k.1.app (op (subspace_open_of_le hW)))
              (Iso.inv_hom_id_app
                (TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetIntersectionLeftInclusion (U i) (U j))
                  (openSubsetInclusion (U i)))
                F))
            s
      let leftNaiveMap :=
        (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 inf_le_left)).map
              ((openEmbedding_sheafPullbackIso (U i).isOpenEmbedding).hom.app F)).hom.app
            (op (subspace_open_of_le hW))) ≫
          (openSubsetHomOfLE_section_iso hW inf_le_left
              (((U i).isOpenEmbedding.sheafPullback (Type u)).obj F)).hom ≫
            eqToHom (by
              change
                F.1.obj (op ((subspace_inclusion_functor (U i)).obj
                  (subspace_open_of_le (hW.trans inf_le_left)))) =
                  F.1.obj (op W)
              simpa [subspace_open_of_le_image_eq])
      have hleftNaive :
          (openSubsetHomOfLE_section_iso hW inf_le_left
              ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F)).hom ≫
            (global_member_section_iso (U := U) F (i := i) hWi).hom =
          leftNaiveMap := by
        -- Route correction: first normalize the left branch to the theorem-local naive model.
        cases hhWi
        simpa [leftNaiveMap, Category.assoc] using
          memberSectionToNaiveGlobal_compare
            (U := U) (ℱ := F) (i := i) (hWA := hW) (hAi := inf_le_left)
      have hleftNaivePoint :
          leftNaiveMap leftInput = overlapGlobal.hom s := by
        have hleftBranchCompare :
            leftNaiveMap =
              ((leftGlobalIso.hom).1.app (op (subspace_open_of_le hW))) ≫ overlapGlobal.hom := by
          -- Normalize the canonical left branch owner to the common overlap owner once.
          simpa [leftNaiveMap, leftGlobalIso] using
            branchActualToOverlapGlobal_compare (k := i) (branch := inf_le_left)
        -- Reuse the generic pointwise evaluation after comparing the left branch morphism to the
        -- common overlap owner.
        simpa [leftNaiveMap] using
          naiveBranchToActualOverlapGlobal_apply
            (branch := inf_le_left)
            (branchGlobalIso := leftGlobalIso)
            (branchInput := leftInput)
            (hbranchCompare := by
              simpa [leftNaiveMap] using hleftBranchCompare)
            hleftCancel
      have hleftApp := congrFun hleftNaive leftInput
      simpa [Category.assoc, hleftNaivePoint] using hleftApp
    have hrightPoint' :
        (global_member_section_iso (U := U) F (i := j) hWj).hom
            ((openSubsetHomOfLE_section_iso hW inf_le_right
                ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F)).hom
              rightInput) =
          overlapGlobal.hom s := by
      have hhWj : hW.trans inf_le_right = hWj := Subsingleton.elim _ _
      have hrightCancel :
          ((rightGlobalIso.hom).1.app (op (subspace_open_of_le hW))) rightInput = s := by
        simpa [rightInput, rightGlobalIso, Category.assoc] using
          congrFun
            (congrArg
              (fun k ↦ k.1.app (op (subspace_open_of_le hW)))
              (Iso.inv_hom_id_app
                (TopCat.Sheaf.pullbackComp (A := Type u)
                  (openSubsetIntersectionRightInclusion (U i) (U j))
                  (openSubsetInclusion (U j)))
                F))
            s
      let rightNaiveMap :=
        (((TopCat.Sheaf.pullback (Type u) (openSubsetHomOfLE_6_33_2 inf_le_right)).map
              ((openEmbedding_sheafPullbackIso (U j).isOpenEmbedding).hom.app F)).hom.app
            (op (subspace_open_of_le hW))) ≫
          (openSubsetHomOfLE_section_iso hW inf_le_right
              (((U j).isOpenEmbedding.sheafPullback (Type u)).obj F)).hom ≫
            eqToHom (by
              change
                F.1.obj (op ((subspace_inclusion_functor (U j)).obj
                  (subspace_open_of_le (hW.trans inf_le_right)))) =
                  F.1.obj (op W)
              simpa [subspace_open_of_le_image_eq])
      have hrightNaive :
          (openSubsetHomOfLE_section_iso hW inf_le_right
              ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F)).hom ≫
            (global_member_section_iso (U := U) F (i := j) hWj).hom =
          rightNaiveMap := by
        -- Route correction: first normalize the right branch to the theorem-local naive model.
        cases hhWj
        simpa [rightNaiveMap, Category.assoc] using
          memberSectionToNaiveGlobal_compare
            (U := U) (ℱ := F) (i := j) (hWA := hW) (hAi := inf_le_right)
      have hrightNaivePoint :
          rightNaiveMap rightInput = overlapGlobal.hom s := by
        have hrightBranchCompare :
            rightNaiveMap =
              ((rightGlobalIso.hom).1.app (op (subspace_open_of_le hW))) ≫ overlapGlobal.hom := by
          -- Normalize the canonical right branch owner to the common overlap owner once.
          simpa [rightNaiveMap, rightGlobalIso] using
            branchActualToOverlapGlobal_compare (k := j) (branch := inf_le_right)
        -- Reuse the same pointwise evaluation after comparing the right branch morphism to the
        -- common overlap owner.
        simpa [rightNaiveMap] using
          naiveBranchToActualOverlapGlobal_apply
            (branch := inf_le_right)
            (branchGlobalIso := rightGlobalIso)
            (branchInput := rightInput)
            (hbranchCompare := by
              simpa [rightNaiveMap] using hrightBranchCompare)
            hrightCancel
      have hrightApp := congrFun hrightNaive rightInput
      simpa [Category.assoc, hrightNaivePoint] using hrightApp
    exact hleftPoint'.trans hrightPoint'.symm
  let tRight : (open_cover_glueing_basisSheaf data).1.obj (op ambientW) :=
    (cover_basis_restrict_extend_component_iso (U := U) data ambientW).hom
      (((global_member_section_iso (U := U) F (i := j) hWj).hom)
        ((openSubsetHomOfLE_section_iso hW inf_le_right
            ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F)).hom
          rightInput))
  have overlapBasisInputEq : tRight = t := by
    -- Push the shared ambient section through the single basis-extension comparison on `W`.
    simpa [t, tRight] using
      congrArg
        ((cover_basis_restrict_extend_component_iso (U := U) data ambientW).hom)
        overlapAmbientInputEq.symm
  have hlhs :
      rightSection.hom leftEval =
        ((subset_chart_iso data (chosen_chart_le ambientW) hWi).hom ≫
          (subset_chart_iso data hWi hWj).hom) t := by
    have hleftInput := congrFun hφi_overlap' leftInput
    have hleftInput' :=
      congrArg
        (fun z ↦
          (openSubsetHomOfLE_section_iso hW inf_le_right (data.localSheaf j)).hom
            ((((TopCat.Sheaf.forget (Type u) (openSubsetSpace (U i ⊓ U j))).map
                (data.overlapIso i j).hom).app (op (subspace_open_of_le hW))) z))
        hleftInput
    simpa [F, leftInput, rightSection, t, ambientW, subset_chart_iso,
      member_space_basis_component_iso_of_rep, Category.assoc] using hleftInput'
  have hrhs :
      rightSection.hom rightEval =
        (subset_chart_iso data (chosen_chart_le ambientW) hWj).hom t := by
    let ambientWRight : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨j, hWj⟩⟩
    have hAmbientEq : ambientWRight = ambientW := by
      -- Replace the right-owned subordinate-basis witness of `W` by the fixed ambient one.
      simpa [ambientWRight, ambientW] using
        coverSubordinateBasisOpen_eq_of_same_open (U := U) hWj hWi
    have hrightInput := congrFun hφj_overlap' rightInput
    have hrightInput' :=
      congrArg
        (fun z ↦
          (openSubsetHomOfLE_section_iso hW inf_le_right (data.localSheaf j)).hom z)
        hrightInput
    have hmember :
        rightSection.hom rightEval =
          (member_space_basis_component_iso_of_rep data j hWj).hom
            ((openSubsetHomOfLE_section_iso hW inf_le_right
                ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F)).hom
              rightInput) := by
      simpa [F, rightInput, rightSection, Category.assoc] using hrightInput'
    have htRightChart :
        (member_space_basis_component_iso_of_rep data j hWj).hom
            ((openSubsetHomOfLE_section_iso hW inf_le_right
                ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F)).hom
              rightInput) =
          (subset_chart_iso data (chosen_chart_le ambientW) hWj).hom tRight := by
      -- Expand the represented component at the right-owned witness of `W`, then transport that
      -- temporary basis witness back to the fixed ambient representative `ambientW`.
      have hchart :
          (member_space_basis_component_iso_of_rep data j hWj).hom
              ((openSubsetHomOfLE_section_iso hW inf_le_right
                  ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F)).hom
                rightInput) =
            (subset_chart_iso data (chosen_chart_le ambientWRight) hWj).hom
              ((cover_basis_restrict_extend_component_iso (U := U) data ambientWRight).hom
                (((global_member_section_iso (U := U) F (i := j) hWj).hom)
                  ((openSubsetHomOfLE_section_iso hW inf_le_right
                      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F)).hom
                    rightInput))) := by
        rfl
      have hambient :
          (subset_chart_iso data (chosen_chart_le ambientWRight) hWj).hom
              ((cover_basis_restrict_extend_component_iso (U := U) data ambientWRight).hom
                (((global_member_section_iso (U := U) F (i := j) hWj).hom)
                  ((openSubsetHomOfLE_section_iso hW inf_le_right
                      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U j))).obj F)).hom
                    rightInput))) =
            (subset_chart_iso data (chosen_chart_le ambientW) hWj).hom tRight := by
        cases hAmbientEq
        rfl
      exact hchart.trans hambient
    have htRight :
        (subset_chart_iso data (chosen_chart_le ambientW) hWj).hom tRight =
          (subset_chart_iso data (chosen_chart_le ambientW) hWj).hom t := by
      simpa [overlapBasisInputEq]
    exact hmember.trans (htRightChart.trans htRight)
  exact hrightSection_inj <| hlhs.trans (ht.trans hrhs.symm)

end
