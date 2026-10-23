module

public import stacks_project.Chap07.Lemma_7_39_1.BranchProduct

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

/-- Helper for Lemma 7.39.1: once the source-proof product map is injective, two distinct tail
germs differ on at least one branch coordinate. -/
theorem exists_branch_raw_ne_of_tail_ne
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    [Finite 𝒰.index]
    (Fobj : Cᵒᵖ ⥤ Type (max u v w))
    {x y : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj}
    (hxy : x ≠ y)
    (hinj : Function.Injective (tail_branch_product_map
      (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj)) :
    ∃ k : 𝒰.index,
      tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k x ≠
        tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k y := by
  -- Apply the general finite-product separation lemma to the source-proof product map.
  simpa [tail_branch_product_map] using
    exists_ne_coordinate_of_injective_map
      (g := tail_branch_product_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj)
      hxy hinj

/-- Helper for Lemma 7.39.1: the right base stage of the glued refinement is the chosen pullback
object. -/
theorem glued_refinement_right_base_obj
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    (glued_refinement_system S j₁ f₁ 𝒰 k).obj
        (op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)) =
      pullback (𝒰.obj k).hom f₁ := by
  -- The right summand of the glued system is definitionally the branch pullback system.
  simp [glued_refinement_system, glued_refinement_system_obj, branch_system_obj]

/-- Helper for Lemma 7.39.1: the left stage `j0` of the glued refinement is the original stage
`S.obj (op j0)`. -/
theorem glued_refinement_left_stage_obj
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ j0 : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    (glued_refinement_system S j₁ f₁ 𝒰 k).obj
        (op (⟨Sum.inl j0⟩ : glued_refinement_index j₁)) =
      S.obj (op j0) := by
  -- The left summand of the glued system is definitionally the original inverse system.
  simp [glued_refinement_system, glued_refinement_system_obj]

/-- Helper for Lemma 7.39.1: every left stage `j0 ≤ j₁` lies below the glued right base stage. -/
theorem glued_refinement_left_stage_le_right_base
    {ι : Type w} [Preorder ι] {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) :
    (⟨Sum.inl j0⟩ : glued_refinement_index j₁) ≤ ⟨Sum.inr ⟨j₁, le_rfl⟩⟩ := by
  -- This is exactly the mixed left-to-right clause in the glued refinement preorder.
  simpa using hj₀

/-- Helper for Lemma 7.39.1: the canonical morphism from the glued right base stage to the left
stage `j0`. -/
def glued_refinement_right_base_to_left_hom
    {ι : Type w} [Preorder ι] {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) :
    op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁) ⟶
      op (⟨Sum.inl j0⟩ : glued_refinement_index j₁) :=
  (homOfLE (glued_refinement_left_stage_le_right_base (j0 := j0) (j₁ := j₁) hj₀)).op

/-- Helper for Lemma 7.39.1: the mixed morphism from the glued right base stage to the left stage
`j0` remembers exactly the source inequality `hj₀`. -/
theorem glued_refinement_right_base_to_left_hom_le
    {ι : Type w} [Preorder ι] {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) :
    leOfHom (glued_refinement_right_base_to_left_hom (j0 := j0) (j₁ := j₁) hj₀).unop = hj₀ := by
  -- The mixed glued morphism is literally the opposite of `homOfLE hj₀`.
  apply Subsingleton.elim

/-- Helper for Lemma 7.39.1: after identifying the glued right base with the chosen pullback
object, the pullback point still lands over the original stage morphism to `W`. -/
theorem glued_refinement_right_base_fst_comp_cover
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) {W : C} (f₀ : S.obj (op j0) ⟶ W)
    (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    let rightBase : (glued_refinement_index j₁)ᵒᵖ :=
      op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)
    let hRightObj :
        (glued_refinement_system S j₁ (S.map (homOfLE hj₀).op ≫ f₀) 𝒰 k).obj rightBase =
          pullback (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) :=
      by
        simpa [rightBase] using
          (glued_refinement_right_base_obj
            (S := S) (j₁ := j₁) (f₁ := S.map (homOfLE hj₀).op ≫ f₀) (𝒰 := 𝒰) (k := k))
    eqToHom hRightObj ≫ pullback.fst (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) ≫
        (𝒰.obj k).hom =
      eqToHom hRightObj ≫ pullback.snd (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) ≫
        (S.map (homOfLE hj₀).op ≫ f₀) := by
  dsimp
  let rightBase : (glued_refinement_index j₁)ᵒᵖ :=
    op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)
  have hRightObj :
      (glued_refinement_system S j₁ (S.map (homOfLE hj₀).op ≫ f₀) 𝒰 k).obj rightBase =
        pullback (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) := by
    simpa [rightBase] using
      (glued_refinement_right_base_obj
        (S := S) (j₁ := j₁) (f₁ := S.map (homOfLE hj₀).op ≫ f₀) (𝒰 := 𝒰) (k := k))
  -- This is the pullback compatibility relation, transported across the right-base object
  -- identification used in the glued refinement.
  simpa [rightBase, Category.assoc] using
    congrArg
      (fun m ↦ eqToHom hRightObj ≫ m)
      (show
        pullback.fst (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) ≫ (𝒰.obj k).hom =
          pullback.snd (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) ≫
            (S.map (homOfLE hj₀).op ≫ f₀) from
          pullback.condition)

/-- Helper for Lemma 7.39.1: at the definitional glued right-base pullback object, the cover map
already factors through the original stage map to `W`. -/
theorem glued_refinement_right_base_cover_factorization
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) {W : C} (f₀ : S.obj (op j0) ⟶ W)
    (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
    let rightBase : (glued_refinement_index j₁)ᵒᵖ :=
      op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)
    let T := glued_refinement_system S j₁ f₁ 𝒰 k
    let rightBaseHom : T.obj rightBase ⟶ (𝒰.obj k).left :=
      pullback.fst (𝒰.obj k).hom (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
    rightBaseHom ≫ (𝒰.obj k).hom =
      T.map (glued_refinement_right_base_to_left_hom (j0 := j0) (j₁ := j₁) hj₀) ≫ f₀ := by
  let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
  let rightBase : (glued_refinement_index j₁)ᵒᵖ :=
    op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let rightBaseHom : T.obj rightBase ⟶ (𝒰.obj k).left :=
    pullback.fst (𝒰.obj k).hom (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
  -- Route correction: use the definitional right-base pullback object, so the cover
  -- factorization is exactly the pullback condition plus the mixed-map formula.
  dsimp [rightBaseHom, T, f₁, rightBase]
  have hpullback :
      pullback.fst (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            (𝒰.obj k).hom =
        pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            S.map (homOfLE hj₀).op ≫ f₀ := by
    calc
      pullback.fst (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            (𝒰.obj k).hom =
        pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
              (S.map (homOfLE hj₀).op ≫ f₀)) := by
              simpa using
                (pullback.condition
                  (f := (𝒰.obj k).hom)
                  (g := S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
                    (S.map (homOfLE hj₀).op ≫ f₀)))
      _ =
        pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            S.map (homOfLE hj₀).op ≫ f₀ := by
              simp [Category.assoc]
  have hmap :
      pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            S.map (homOfLE hj₀).op ≫ f₀ =
        T.map (glued_refinement_right_base_to_left_hom (j0 := j0) (j₁ := j₁) hj₀) ≫ f₀ := by
    change pullback.snd (𝒰.obj k).hom
        (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
          (S.map (homOfLE hj₀).op ≫ f₀)) ≫
          S.map (homOfLE hj₀).op ≫ f₀ =
      (pullback.snd (𝒰.obj k).hom
        (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁) ≫
          S.map (show op j₁ ⟶ op j0 from (homOfLE hj₀).op)) ≫ f₀
    simpa [f₁, Category.assoc]
  exact hpullback.trans hmap

/-- Helper for Lemma 7.39.1: after identifying the left summand of the glued refinement with the
original stage `j0`, the morphism used in the refinement witness is literally `f₀`. -/
theorem glued_refinement_left_stage_map_eq
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) {W : C} (f₀ : S.obj (op j0) ⟶ W)
    (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
    let T := glued_refinement_system S j₁ f₁ 𝒰 k
    let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
    let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
    let leftStageMap : T.obj (op (j j0)) ⟶ W := e.inv.app (op j0) ≫ f₀
    leftStageMap = f₀ := by
  let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
  let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
  let leftStageMap : T.obj (op (j j0)) ⟶ W := e.inv.app (op j0) ≫ f₀
  -- On the left summand, the inverse component of the glued refinement is the identity.
  dsimp [leftStageMap]
  rw [glued_refinement_iso_inv_app_eq_id
    (S := S) (j₁ := j₁) (j0 := j0) (f₁ := f₁) (𝒰 := 𝒰) (k := k)]
  exact Category.id_comp f₀

/-- Helper for Lemma 7.39.1: once a branch `k` is chosen, the canonical pullback point on the
right summand of the glued refinement maps to the refined image of the original generator. -/
theorem glued_refinement_right_base_generator_eq_refinement_image
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) {W : C} (f₀ : S.obj (op j0) ⟶ W)
    (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
    let T := glued_refinement_system S j₁ f₁ 𝒰 k
    let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
    let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
    let rightBaseHom :
        T.obj (op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)) ⟶ (𝒰.obj k).left :=
      pullback.fst (𝒰.obj k).hom
        (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
    ((fiber.{max u v w} T).map (𝒰.obj k).hom) (fiberMk.{max u v w} rightBaseHom) =
      (refinementFiber j T e).app W (show (fiber.{max u v w} S).obj W from
        fiberMk.{max u v w} f₀) := by
  let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
  let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
  let rightBaseToLeft :=
    glued_refinement_right_base_to_left_hom (j0 := j0) (j₁ := j₁) hj₀
  let leftStageMap : T.obj (op (j j0)) ⟶ W := e.inv.app (op j0) ≫ f₀
  let rightBaseHom :
      T.obj (op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)) ⟶ (𝒰.obj k).left :=
    pullback.fst (𝒰.obj k).hom
      (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
  have hleftStageMap : leftStageMap = f₀ := by
    -- On the left summand, the refinement identification contributes only the identity.
    simpa [leftStageMap, f₁, T, j, e] using
      glued_refinement_left_stage_map_eq
        (S := S) (hj₀ := hj₀) (f₀ := f₀) (𝒰 := 𝒰) (k := k)
  have hmap :
      ((fiber.{max u v w} T).map (𝒰.obj k).hom) (fiberMk.{max u v w} rightBaseHom) =
        (show (fiber.{max u v w} T).obj W from
          fiberMk.{max u v w} (rightBaseHom ≫ (𝒰.obj k).hom)) := by
    -- Push the explicit right-base generator along the cover morphism.
    simpa [T, rightBaseHom] using
      (fiber_map_fiberMk.{max u v w}
        (p := T) (f := rightBaseHom) (g := (𝒰.obj k).hom) :
          ((fiber.{max u v w} T).map (𝒰.obj k).hom) (fiberMk.{max u v w} rightBaseHom) =
            fiberMk.{max u v w} (rightBaseHom ≫ (𝒰.obj k).hom))
  have hfactor :
      (show (fiber.{max u v w} T).obj W from
        fiberMk.{max u v w} (rightBaseHom ≫ (𝒰.obj k).hom)) =
      (show (fiber.{max u v w} T).obj W from
        fiberMk.{max u v w} (T.map rightBaseToLeft ≫ f₀)) := by
    -- Rewrite the pullback-point image using the cover factorization at the glued right base.
    exact congrArg
      (fun m ↦ (show (fiber.{max u v w} T).obj W from fiberMk.{max u v w} m))
      (by
        simpa [f₁, T, rightBaseHom, rightBaseToLeft] using
          glued_refinement_right_base_cover_factorization
            (S := S) (hj₀ := hj₀) (f₀ := f₀) (𝒰 := 𝒰) (k := k))
  have hrewrite :
      (show (fiber.{max u v w} T).obj W from
        fiberMk.{max u v w} (T.map rightBaseToLeft ≫ f₀)) =
      (show (fiber.{max u v w} T).obj W from
        fiberMk.{max u v w} (T.map rightBaseToLeft ≫ leftStageMap)) := by
    -- Replace the left-stage map by the explicit refinement-image morphism.
    exact congrArg
      (fun m ↦
        (show (fiber.{max u v w} T).obj W from
          fiberMk.{max u v w} (T.map rightBaseToLeft ≫ m)))
      hleftStageMap.symm
  have hcollapse :
      (show (fiber.{max u v w} T).obj W from
        fiberMk.{max u v w} (T.map rightBaseToLeft ≫ leftStageMap)) =
      (show (fiber.{max u v w} T).obj W from fiberMk.{max u v w} leftStageMap) := by
    -- Now the right-base presentation collapses to the left-stage generator.
    exact
      (fiberMk_map_comp.{max u v w} (p := T) (g := rightBaseToLeft) (f := leftStageMap) :
        fiberMk.{max u v w} (T.map rightBaseToLeft ≫ leftStageMap) =
          fiberMk.{max u v w} leftStageMap)
  have hrefine :
      (show (fiber.{max u v w} T).obj W from fiberMk.{max u v w} leftStageMap) =
        (refinementFiber j T e).app W (show (fiber.{max u v w} S).obj W from
          fiberMk.{max u v w} f₀) := by
    -- The left-stage generator is exactly the refinement image of the original one.
    symm
    simpa [leftStageMap] using
      (refinementFiber_app_fiberMk (j := j) (T := T) (e := e)
        (U := op j0) (W := W) (f := f₀))
  exact hmap.trans (hfactor.trans (hrewrite.trans (hcollapse.trans hrefine)))

/-- Helper for Lemma 7.39.1: once a branch `k` is chosen, the canonical pullback point on the
right summand of the glued refinement maps to the refined image of the original generator. -/
theorem glued_refinement_generator_lifts_cover
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) {W : C} (f₀ : S.obj (op j0) ⟶ W)
    (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
    let T := glued_refinement_system S j₁ f₁ 𝒰 k
    let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
    let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
    ∃ y : (fiber.{max u v w} T).obj (𝒰.obj k).left,
      ((fiber.{max u v w} T).map (𝒰.obj k).hom) y =
        (refinementFiber j T e).app W (show (fiber.{max u v w} S).obj W from
          fiberMk.{max u v w} f₀) := by
  let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
  let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
  let rightBaseHom :
      T.obj (op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)) ⟶ (𝒰.obj k).left :=
    pullback.fst (𝒰.obj k).hom
      (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
  -- Use the explicit pullback generator on the right base stage as the witness lifting `f₀`.
  refine ⟨fiberMk.{max u v w} rightBaseHom, ?_⟩
  simpa [f₁, T, j, e, rightBaseHom] using
    glued_refinement_right_base_generator_eq_refinement_image
      (S := S) (hj₀ := hj₀) (f₀ := f₀) (𝒰 := 𝒰) (k := k)

/-- Helper for Lemma 7.39.1: the raw presheaf fiber of the chosen branch agrees with the raw
presheaf fiber of the glued refinement by finality of the right summand. -/
noncomputable def glued_right_branch_presheafFiber_iso
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    (j₁ : ι) {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (k : 𝒰.index) (Fobj : Cᵒᵖ ⥤ Type (max u v w)) :
    (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).presheafFiber.obj Fobj ≅
      (fiber.{max u v w} (glued_refinement_system S j₁ f₁ 𝒰 k)).presheafFiber.obj Fobj := by
  let i : (Set.Ici j₁)ᵒᵖ ⥤ (glued_refinement_index j₁)ᵒᵖ :=
    ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor).op
  let B := branch_system S j₁ f₁ 𝒰 k
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let hSections : B.op ⋙ Fobj ≅ i.op ⋙ T.op ⋙ Fobj :=
    -- First identify the right restriction of the glued system with the explicit branch system,
    -- then rewrite the section diagram into the whiskered form expected by finality.
    (Functor.isoWhiskerRight
        (NatIso.op (glued_refinement_right_restrict_iso
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)).symm)
        Fobj) ≪≫
      (Functor.isoWhiskerRight (Functor.opComp i T) Fobj) ≪≫
      (Functor.associator i.op T.op Fobj)
  let _ : Functor.Final ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor) :=
    glued_refinement_tail_inclusion_final (j₁ := j₁)
  let _ : Functor.Final i.op := by infer_instance
  let _ : Nonempty (Set.Ici j₁) := ⟨⟨j₁, le_rfl⟩⟩
  let _ : IsDirected (Set.Ici j₁) (· ≤ ·) := tail_index_isDirected (j₁ := j₁)
  let _ : Nonempty (glued_refinement_index j₁) := ⟨⟨Sum.inl j₁⟩⟩
  -- Compute both raw fibers by colimits of stagewise sections and insert the finality comparison
  -- for the right summand of the glued refinement.
  exact
    (inverse_system_presheafFiber_colimitIso B Fobj).symm ≪≫
      (HasColimit.isoOfNatIso hSections) ≪≫
      (Functor.Final.colimitIso i.op (T.op ⋙ Fobj)) ≪≫
      (inverse_system_presheafFiber_colimitIso T Fobj)


end

end CategoryTheory
