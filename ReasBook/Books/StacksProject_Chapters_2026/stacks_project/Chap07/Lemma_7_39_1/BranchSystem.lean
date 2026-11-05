module

public import stacks_project.Chap07.Lemma_7_39_1.CoverAndRawFiber

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open GrothendieckTopology.Point
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

section

variable {J : GrothendieckTopology C}

open GrothendieckTopology.Point.ofIsCofiltered
open CategoryTheory.SemiRepresentableFamily.Over

variable (J)

/-- Helper for Lemma 7.39.1: the cofinal tail of a directed preorder above `j₁`. -/
def tail_inclusion {ι : Type w} [Preorder ι] (j₁ : ι) :
    Set.Ici j₁ ↪o ι where
  toFun := fun j ↦ j.1
  inj' := fun _ _ h ↦ Subtype.ext h
  map_rel_iff' := by
    intro a b
    rfl

/-- Helper for Lemma 7.39.1: the original inverse system restricted to the tail above `j₁`. -/
noncomputable abbrev tail_system
    {ι : Type w} [Preorder ι] (S : ιᵒᵖ ⥤ C) (j₁ : ι) :
    (Set.Ici j₁)ᵒᵖ ⥤ C :=
  ((tail_inclusion j₁).toOrderHom.toFunctor).op ⋙ S

/-- Helper for Lemma 7.39.1: the object at a tail stage in the chosen pullback branch system. -/
noncomputable abbrev branch_system_obj
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    (j : (Set.Ici j₁)ᵒᵖ) : C :=
  pullback (𝒰.obj k).hom (S.map (homOfLE (unop j).2).op ≫ f₁)

/-- Helper for Lemma 7.39.1: the stage map into `W` is compatible with restriction along the tail
ordering. -/
theorem branch_system_stage_compat
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y : (Set.Ici j₁)ᵒᵖ} (g : X ⟶ Y) :
    (S.map (homOfLE (unop X).2).op ≫ f₁) ≫ 𝟙 W =
      S.map (homOfLE (leOfHom g.unop)).op ≫ (S.map (homOfLE (unop Y).2).op ≫ f₁) := by
  -- Rewrite the restriction to `X` as the composite of the restriction to `Y`
  -- with the transition map `g.unop` inside the tail preorder.
  have htail :
      (unop Y).2.trans (leOfHom g.unop) = (unop X).2 := by
    apply Subsingleton.elim
  rw [Category.comp_id]
  -- Normalize only the right-hand side to the single transition from `j₁` to `X`.
  conv_rhs =>
    rw [← Category.assoc, ← Functor.map_comp]
  have hop :=
    congrArg (fun h => S.map h ≫ f₁)
      (congrArg Quiver.Hom.op (homOfLE_comp (unop Y).2 (leOfHom g.unop)))
  simpa only [htail] using hop

/-- Helper for Lemma 7.39.1: the transition map in the chosen pullback branch system. -/
noncomputable abbrev branch_system_map
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y : (Set.Ici j₁)ᵒᵖ} (g : X ⟶ Y) :
    branch_system_obj S j₁ f₁ 𝒰 k X ⟶ branch_system_obj S j₁ f₁ 𝒰 k Y :=
  pullback.map
    (𝒰.obj k).hom
    (S.map (homOfLE (unop X).2).op ≫ f₁)
    (𝒰.obj k).hom
    (S.map (homOfLE (unop Y).2).op ≫ f₁)
    (𝟙 _)
    (S.map (homOfLE (leOfHom g.unop)).op)
    (𝟙 _)
    (by simp)
    (branch_system_stage_compat (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) g)

/-- Helper for Lemma 7.39.1: the ambient transition map of `S` attached to the tail identity
morphism is the identity on the corresponding stage. -/
theorem tail_identity_map_on_stage
    {ι : Type w} [Preorder ι] (S : ιᵒᵖ ⥤ C) (j₁ : ι) (X : (Set.Ici j₁)ᵒᵖ) :
    S.map (homOfLE (leOfHom (𝟙 X).unop)).op =
      𝟙 (S.obj (op (((unop X : Set.Ici j₁) : ι)))) := by
  -- Normalize the identity morphism in the tail preorder to the ambient identity of `S`.
  simpa only [homOfLE_leOfHom, homOfLE_refl] using
    Functor.map_id S (op (((unop X : Set.Ici j₁) : ι)))

/-- Helper for Lemma 7.39.1: the branch transition at an identity morphism is the identity map. -/
theorem branch_system_map_id
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    (X : (Set.Ici j₁)ᵒᵖ) :
    branch_system_map S j₁ f₁ 𝒰 k (𝟙 X) = 𝟙 _ := by
  -- Route correction: first normalize the ambient identity map of `S`, then the branch map is
  -- checked on the two pullback projections.
  apply pullback.hom_ext
  · -- The first projection of `pullback.map` is the chosen first leg of the lift.
    rw [branch_system_map]
    delta pullback.map
    rw [pullback.lift_fst]
    calc
      pullback.fst (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) ≫
          𝟙 (𝒰.obj k).left =
        pullback.fst (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) := by
          simp
      _ =
        𝟙 (branch_system_obj S j₁ f₁ 𝒰 k X) ≫
          pullback.fst (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) := by
            simp
  · -- The second projection is the ambient tail identity map, which we now normalize explicitly.
    rw [branch_system_map]
    delta pullback.map
    rw [pullback.lift_snd]
    rw [tail_identity_map_on_stage (S := S) (j₁ := j₁) X]
    calc
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) ≫
          𝟙 (S.obj (op (((unop X : Set.Ici j₁) : ι)))) =
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) := by
          simp
      _ =
        𝟙 (branch_system_obj S j₁ f₁ 𝒰 k X) ≫
          pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) := by
            simp

/-- Helper for Lemma 7.39.1: branch transitions compose as expected. -/
theorem branch_system_map_comp
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y Z : (Set.Ici j₁)ᵒᵖ} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) :
    branch_system_map S j₁ f₁ 𝒰 k g₁ ≫ branch_system_map S j₁ f₁ 𝒰 k g₂ =
      branch_system_map S j₁ f₁ 𝒰 k (g₁ ≫ g₂) := by
  -- The pullback transitions compose because the second coordinates are exactly the functorial
  -- restriction maps of `S` along the tail preorder.
  simpa [branch_system_map, Category.assoc, ← Functor.map_comp, ← op_comp,
      homOfLE_comp, homOfLE_leOfHom] using
    (pullback.map_comp
      (f := (𝒰.obj k).hom)
      (g := S.map (homOfLE (unop X).2).op ≫ f₁)
      (f' := (𝒰.obj k).hom)
      (g' := S.map (homOfLE (unop Y).2).op ≫ f₁)
      (f'' := (𝒰.obj k).hom)
      (g'' := S.map (homOfLE (unop Z).2).op ≫ f₁)
      (𝟙 _)
      (𝟙 _)
      (S.map (homOfLE (leOfHom g₁.unop)).op)
      (S.map (homOfLE (leOfHom g₂.unop)).op)
      (𝟙 W)
      (𝟙 W)
      (by simp)
      (branch_system_stage_compat (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) g₁)
      (by simp)
      (branch_system_stage_compat (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) g₂))

/-- Helper for Lemma 7.39.1: the pullback branch inverse system over the tail above `j₁`
associated with the cover member `k`. -/
noncomputable def branch_system
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    (Set.Ici j₁)ᵒᵖ ⥤ C :=
  { obj := branch_system_obj S j₁ f₁ 𝒰 k
    map := fun g ↦ branch_system_map S j₁ f₁ 𝒰 k g
    map_id := branch_system_map_id (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
    map_comp := fun f g ↦
      (branch_system_map_comp (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) f g).symm }

/-- Helper for Lemma 7.39.1: the canonical colimit of the stagewise section diagram of an inverse
system identifies with the raw presheaf fiber of that system. -/
noncomputable def inverse_system_presheafFiber_colimitIso
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    colimit (S.op ⋙ F) ≅ (fiber.{max u v w} S).presheafFiber.obj F :=
  (colimit.isColimit (S.op ⋙ F)).coconePointUniqueUpToIso
    (inverse_system_presheafFiber_isColimit (S := S) F)

/-- Helper for Lemma 7.39.1: the refinement index obtained by adjoining the branch tail to the
original inverse-system index. -/
structure glued_refinement_index {ι : Type w} [Preorder ι] (j₁ : ι) where
  val : Sum ι (Set.Ici j₁)

/-- Helper for Lemma 7.39.1: order on the glued refinement index, with right-summand branch stages
lying above exactly the original stages below their underlying tail index. -/
instance glued_refinement_preorder
    {ι : Type w} [Preorder ι] (j₁ : ι) :
    Preorder (glued_refinement_index j₁) where
  le x y :=
    match x.val, y.val with
    | Sum.inl i, Sum.inl i' => i ≤ i'
    | Sum.inl i, Sum.inr j => i ≤ j.1
    | Sum.inr _, Sum.inl _ => False
    | Sum.inr j, Sum.inr j' => j ≤ j'
  le_refl x := by
    -- Each summand uses the ambient reflexive order, and there are no right-to-left relations.
    cases x with
    | mk x =>
        cases x <;> simp
  le_trans x y z hxy hyz := by
    -- Route correction: encode the source order on `J ⊔ J₀` directly, then transitivity is a
    -- finite case split over the two summands.
    cases x with
    | mk x =>
        cases y with
        | mk y =>
            cases z with
            | mk z =>
                cases x <;> cases y <;> cases z <;> simp at hxy hyz ⊢
                all_goals exact le_trans hxy hyz

/-- Helper for Lemma 7.39.1: the glued refinement index is directed, following the source proof's
order on `J ⊔ J₀`. -/
instance glued_refinement_isDirected
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (j₁ : ι) :
    IsDirected (glued_refinement_index j₁) (· ≤ ·) := by
  refine ⟨?_⟩
  intro x y
  -- Follow the source construction: choose a common upper bound in the ambient directed set and
  -- place it in the summand that stays above both inputs.
  cases x with
  | mk x =>
      cases y with
      | mk y =>
          cases x with
          | inl i =>
              cases y with
              | inl i' =>
                  obtain ⟨k, hik, hi'k⟩ := directed_of (· ≤ ·) i i'
                  exact ⟨⟨Sum.inl k⟩, by simpa using hik, by simpa using hi'k⟩
              | inr j =>
                  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j.1
                  exact ⟨⟨Sum.inr ⟨k, j.2.trans hjk⟩⟩, by simpa using hik, by simpa using hjk⟩
          | inr i =>
              cases y with
              | inl i' =>
                  obtain ⟨k, hik, hi'k⟩ := directed_of (· ≤ ·) i.1 i'
                  exact
                    ⟨⟨Sum.inr ⟨k, i.2.trans hik⟩⟩, by simpa using hik, by simpa using hi'k⟩
              | inr j =>
                  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.1 j.1
                  exact
                    ⟨⟨Sum.inr ⟨k, i.2.trans hik⟩⟩, by simpa using hik, by simpa using hjk⟩

/-- Helper for Lemma 7.39.1: the order embedding of the original inverse-system index into the
glued refinement index. -/
def glued_refinement_inclusion {ι : Type w} [Preorder ι] (j₁ : ι) :
    ι ↪o glued_refinement_index j₁ where
  toFun := fun i ↦ ⟨Sum.inl i⟩
  inj' := by
    intro i i' h
    exact Sum.inl.inj (congrArg glued_refinement_index.val h)
  map_rel_iff' := by
    intro i i'
    rfl

/-- Helper for Lemma 7.39.1: the order embedding of the chosen tail into the right summand of the
glued refinement index. -/
def glued_refinement_tail_inclusion {ι : Type w} [Preorder ι] (j₁ : ι) :
    Set.Ici j₁ ↪o glued_refinement_index j₁ where
  toFun := fun i ↦ ⟨Sum.inr i⟩
  inj' := by
    intro i i' h
    exact Sum.inr.inj (congrArg glued_refinement_index.val h)
  map_rel_iff' := by
    intro i i'
    rfl

/-- Helper for Lemma 7.39.1: the second projection of a branch transition is the ambient
restriction map of the original inverse system. -/
theorem branch_system_map_snd_assoc
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y : (Set.Ici j₁)ᵒᵖ} (g : X ⟶ Y) :
    branch_system_map S j₁ f₁ 𝒰 k g ≫
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop Y).2).op ≫ f₁) =
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) ≫
        S.map (homOfLE (leOfHom g.unop)).op := by
  -- Unfold the pullback map only far enough to read off its second projection.
  rw [branch_system_map]
  delta pullback.map
  rw [pullback.lift_snd]

/-- Helper for Lemma 7.39.1: after a right-branch transition, the mixed map from the branch tail
to the left ambient system normalizes to the direct mixed map. -/
theorem glued_refinement_mixed_map_comp
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {i : ι} {j j' : Set.Ici j₁} (hij' : i ≤ j'.1) (hjj' : j' ≤ j) :
    branch_system_map S j₁ f₁ 𝒰 k (show op j ⟶ op j' from (homOfLE hjj').op) ≫
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE j'.2).op ≫ f₁) ≫
          S.map (homOfLE hij').op =
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
        S.map (homOfLE (hij'.trans hjj')).op := by
  -- First normalize the branch transition on the pullback second projection.
  calc
    branch_system_map S j₁ f₁ 𝒰 k (show op j ⟶ op j' from (homOfLE hjj').op) ≫
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE j'.2).op ≫ f₁) ≫
          S.map (homOfLE hij').op =
      (branch_system_map S j₁ f₁ 𝒰 k
          (show op j ⟶ op j' from (homOfLE hjj').op) ≫
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE j'.2).op ≫ f₁)) ≫
          S.map (homOfLE hij').op := by
            rw [← Category.assoc]
    _ =
      (pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
          S.map (homOfLE hjj').op) ≫ S.map (homOfLE hij').op := by
            rw [branch_system_map_snd_assoc (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
              (g := show op j ⟶ op j' from (homOfLE hjj').op)]
    _ =
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
          S.map (homOfLE hjj').op ≫ S.map (homOfLE hij').op := by
            rw [Category.assoc]
    -- Then collapse the two ambient restriction maps into the single direct restriction.
    _ =
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
        S.map (homOfLE (hij'.trans hjj')).op := by
          rw [← Functor.map_comp]
          have hjj'₀ : j'.1 ≤ j.1 := hjj'
          have hcomp :
              (show op j.1 ⟶ op j'.1 from (homOfLE hjj'₀).op) ≫
                  (show op j'.1 ⟶ op i from (homOfLE hij').op) =
                (show op j.1 ⟶ op i from (homOfLE (hij'.trans hjj'₀)).op) := by
            exact Subsingleton.elim _ _
          exact congrArg
            (fun m ↦
              pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫ S.map m)
            hcomp

/-- Helper for Lemma 7.39.1: a mixed map from the right summand followed by a left-left ambient
transition is the direct mixed map to the smaller left stage. -/
theorem glued_refinement_left_map_comp
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {i i' : ι} {j : Set.Ici j₁} (hii' : i ≤ i') (hi'j : i' ≤ j.1) :
    pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
        S.map (homOfLE hi'j).op ≫ S.map (homOfLE hii').op =
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
        S.map (homOfLE (hii'.trans hi'j)).op := by
  -- This is just functoriality of the ambient system `S` on the left summand.
  simpa [Category.assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- Helper for Lemma 7.39.1: the glued refinement system uses the original stage on the left
summand and the chosen branch stage on the right summand. -/
noncomputable def glued_refinement_system_obj
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    (X : (glued_refinement_index j₁)ᵒᵖ) : C :=
  match (unop X).val with
  | Sum.inl i => S.obj (op i)
  | Sum.inr j => branch_system_obj S j₁ f₁ 𝒰 k (op j)

/-- Helper for Lemma 7.39.1: the glued refinement system uses the ambient restriction maps on the
left, the branch restriction maps on the right, and the mixed pullback-snd maps from right to
left. -/
noncomputable def glued_refinement_system_map
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y : (glued_refinement_index j₁)ᵒᵖ} (g : X ⟶ Y) :
    glued_refinement_system_obj S j₁ f₁ 𝒰 k X ⟶
      glued_refinement_system_obj S j₁ f₁ 𝒰 k Y := by
  cases X using Opposite.rec
  rename_i x
  cases Y using Opposite.rec
  rename_i y
  cases x with
  | mk x =>
      cases y with
      | mk y =>
          cases x with
          | inl i =>
              cases y with
              | inl i' =>
                  exact S.map (show op i ⟶ op i' from (homOfLE (show i' ≤ i from leOfHom g.unop)).op)
              | inr _ =>
                  exact False.elim (show False from leOfHom g.unop)
          | inr j =>
              cases y with
              | inl i =>
                  exact
                    pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
                      S.map (show op j.1 ⟶ op i from
                        (homOfLE (show i ≤ j.1 from leOfHom g.unop)).op)
              | inr j' =>
                  exact
                    branch_system_map S j₁ f₁ 𝒰 k
                      (show op j ⟶ op j' from
                        (homOfLE (show j' ≤ j from leOfHom g.unop)).op)

/-- Helper for Lemma 7.39.1: the glued morphism on the identity map is the identity. -/
theorem glued_refinement_system_map_id
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    (X : (glued_refinement_index j₁)ᵒᵖ) :
    glued_refinement_system_map S j₁ f₁ 𝒰 k (𝟙 X) =
      𝟙 (glued_refinement_system_obj S j₁ f₁ 𝒰 k X) := by
  -- The identity stays inside one summand, so the result is the ambient or branch identity map.
  cases X using Opposite.rec
  rename_i x
  cases x with
  | mk x =>
      cases x with
      | inl i =>
          simpa [glued_refinement_system_map, glued_refinement_system_obj,
            homOfLE_leOfHom, homOfLE_refl] using Functor.map_id S (op i)
      | inr j =>
          simpa [glued_refinement_system_map, glued_refinement_system_obj] using
            branch_system_map_id (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) (op j)

/-- Helper for Lemma 7.39.1: the glued morphism map is functorial. -/
theorem glued_refinement_system_map_comp
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y Z : (glued_refinement_index j₁)ᵒᵖ} (g : X ⟶ Y) (h : Y ⟶ Z) :
    glued_refinement_system_map S j₁ f₁ 𝒰 k g ≫
        glued_refinement_system_map S j₁ f₁ 𝒰 k h =
      glued_refinement_system_map S j₁ f₁ 𝒰 k (g ≫ h) := by
  -- Route correction: the source gluing has only one nontrivial composition, namely
  -- right-right followed by right-left; the remaining cases reduce to ambient or branch
  -- functoriality, or are impossible in the glued preorder.
  cases X using Opposite.rec
  rename_i x
  cases Y using Opposite.rec
  rename_i y
  cases Z using Opposite.rec
  rename_i z
  cases x with
  | mk x =>
      cases y with
      | mk y =>
          cases z with
          | mk z =>
              cases x with
              | inl i =>
                  cases y with
                  | inl i' =>
                      cases z with
                      | inl i'' =>
                          simpa [glued_refinement_system_map, ← op_comp, homOfLE_comp] using
                            (Functor.map_comp S
                              (show op i ⟶ op i' from
                                (homOfLE (show i' ≤ i from leOfHom g.unop)).op)
                              (show op i' ⟶ op i'' from
                                (homOfLE (show i'' ≤ i' from leOfHom h.unop)).op)).symm
                      | inr _ =>
                          exfalso
                          exact show False from leOfHom h.unop
                  | inr _ =>
                      exfalso
                      exact show False from leOfHom g.unop
              | inr j =>
                  cases y with
                  | inl i' =>
                      cases z with
                      | inl i =>
                          simpa [glued_refinement_system_map] using
                            glued_refinement_left_map_comp
                              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
                              (i := i) (i' := i') (j := j)
                              (hii' := show i ≤ i' from leOfHom h.unop)
                              (hi'j := show i' ≤ j.1 from leOfHom g.unop)
                      | inr _ =>
                          exfalso
                          exact show False from leOfHom h.unop
                  | inr j' =>
                      cases z with
                      | inl i =>
                          simpa [glued_refinement_system_map] using
                            glued_refinement_mixed_map_comp
                              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
                              (i := i) (j := j) (j' := j')
                              (hij' := show i ≤ j'.1 from leOfHom h.unop)
                              (hjj' := show j' ≤ j from leOfHom g.unop)
                      | inr j'' =>
                          simpa [glued_refinement_system_map] using
                            branch_system_map_comp (S := S) (j₁ := j₁) (f₁ := f₁)
                              (𝒰 := 𝒰) (k := k)
                              (show op j ⟶ op j' from
                                (homOfLE (show j' ≤ j from leOfHom g.unop)).op)
                              (show op j' ⟶ op j'' from
                                (homOfLE (show j'' ≤ j' from leOfHom h.unop)).op)

/-- Helper for Lemma 7.39.1: the glued refinement system contains the original system on the left
and the chosen pullback branch system on the right. -/
noncomputable def glued_refinement_system
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    (glued_refinement_index j₁)ᵒᵖ ⥤ C :=
  { obj := glued_refinement_system_obj S j₁ f₁ 𝒰 k
    map := fun g ↦ glued_refinement_system_map S j₁ f₁ 𝒰 k g
    map_id := glued_refinement_system_map_id (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
    map_comp := fun g h ↦
      (glued_refinement_system_map_comp
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) g h).symm }

/-- Helper for Lemma 7.39.1: restricting the glued refinement system to the left summand recovers
the original inverse system. -/
noncomputable def glued_refinement_iso
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    S ≅ ((glued_refinement_inclusion j₁).toOrderHom.toFunctor).op ⋙
      glued_refinement_system S j₁ f₁ 𝒰 k := by
  -- Restricting to the left summand does not change objects or transition maps of `S`.
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro X Y g
  have hg :
      (show op (unop X) ⟶ op (unop Y) from
        (homOfLE (show unop Y ≤ unop X from leOfHom g.unop)).op) = g := by
    exact congrArg Quiver.Hom.op (homOfLE_leOfHom g.unop)
  simpa [glued_refinement_system, glued_refinement_system_obj, glued_refinement_system_map,
    glued_refinement_inclusion] using congrArg (fun f ↦ S.map f) hg

/-- Helper for Lemma 7.39.1: on each left stage, the inverse component of the glued refinement
identification is the identity. -/
theorem glued_refinement_iso_inv_app_eq_id
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ j0 : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    (glued_refinement_iso S j₁ f₁ 𝒰 k).inv.app (op j0) = 𝟙 (S.obj (op j0)) := by
  -- The glued refinement agrees with `S` on the left summand objectwise.
  simp [glued_refinement_iso]

/-- Helper for Lemma 7.39.1: restricting the glued refinement system to the right summand recovers
the chosen pullback branch system. -/
noncomputable def glued_refinement_right_restrict_iso
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor).op ⋙
        glued_refinement_system S j₁ f₁ 𝒰 k ≅
      branch_system S j₁ f₁ 𝒰 k := by
  -- The right summand was defined to be literally the branch system, so all components are
  -- identities and the only work is the right-right map normalization.
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro X Y g
  simpa [glued_refinement_system, glued_refinement_system_obj, glued_refinement_system_map,
    branch_system, glued_refinement_tail_inclusion]

/-- Helper for Lemma 7.39.1: every stage of the glued refinement maps to some right-branch stage,
so the right summand is final for the raw-fiber colimit computation. -/
theorem glued_refinement_tail_inclusion_final
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (j₁ : ι) :
    Functor.Final ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor) := by
  -- Follow the source order on `J ⊔ J₀`: a right stage maps to itself, and a left stage maps to
  -- some tail stage above both that stage and `j₁`.
  let _ : IsDirected (Set.Ici j₁) (· ≤ ·) := by
    refine ⟨?_⟩
    intro a b
    obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨k, a.2.trans hak⟩, by simpa using hak, by simpa using hbk⟩
  refine Functor.final_of_exists_of_isFiltered
    ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor) ?_ ?_
  · intro d
    cases d with
    | mk x =>
        cases x with
        | inl i =>
            obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j₁
            refine ⟨⟨k, hjk⟩, ?_⟩
            exact ⟨show (⟨Sum.inl i⟩ : glued_refinement_index j₁) ⟶
                (glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor.obj ⟨k, hjk⟩ from
                  homOfLE hik⟩
        | inr j =>
            refine ⟨j, ?_⟩
            exact ⟨𝟙 ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor.obj j)⟩
  · intro d c s s'
    refine ⟨c, 𝟙 c, ?_⟩
    simpa using (Subsingleton.elim s s')

end

end CategoryTheory
