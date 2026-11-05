module

public import stacks_project.Chap07.Lemma_7_39_1.TailSectionBranches

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

/-- Helper for Lemma 7.39.1: the source proof's finite-product map from the tail raw presheaf
fiber to the tuple of all branch raw presheaf fibers. -/
noncomputable def tail_branch_product_map
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) :
    (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj →
      ∀ k : 𝒰.index, (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).presheafFiber.obj Fobj :=
  fun x k ↦ tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k x

/-- Helper for Lemma 7.39.1: the branch restriction maps assemble into the source proof's
stagewise map from the tail section diagram to the product of the branch section diagrams. -/
noncomputable def tail_branch_product_diagram_hom
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) :
    (tail_system S j₁).op ⋙ Fobj ⟶
      ∏ᶜ fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj :=
  -- Route correction: the product lives in the functor category over the fixed tail index,
  -- matching the source proof's single filtered colimit of the stagewise product diagram.
  Pi.lift fun k =>
    tail_branch_diagram_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k

/-- Helper for Lemma 7.39.1: after passing to colimits and then to the finite product of branch
colimits, projecting to coordinate `k` recovers the colimit map of the `k`-th branch diagram. -/
theorem tail_branch_product_functor_projection
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    [Finite 𝒰.index] (Fobj : Cᵒᵖ ⥤ Type (max u v w)) [Fintype 𝒰.index]
    [PreservesLimit
      (Discrete.functor (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj))
      (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w)))]
    (k : 𝒰.index) :
    colim.map (tail_branch_product_diagram_hom
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)) ≫
      (PreservesProduct.iso
        (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w)))
        (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)).hom ≫
      Pi.π (fun k : 𝒰.index =>
        colimit ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)) k =
    colim.map (tail_branch_diagram_hom
      (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k) := by
  -- Project the finite-product comparison to coordinate `k` and then collapse the lifted
  -- branch tuple back to the `k`-th branch restriction map.
  let hπ :
      (PreservesProduct.iso
        (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w)))
        (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)).hom ≫
        Pi.π (fun k : 𝒰.index =>
          colimit ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)) k =
      colim.map
        (Pi.π (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) k) := by
    simpa [PreservesProduct.iso_hom] using
      (piComparison_comp_π
        (G := (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w))))
        (f := fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)
        k)
  calc
    colim.map (tail_branch_product_diagram_hom
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)) ≫
        (PreservesProduct.iso
          (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w)))
          (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)).hom ≫
        Pi.π (fun k : 𝒰.index =>
          colimit ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)) k
        =
      colim.map (tail_branch_product_diagram_hom
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)) ≫
        colim.map
          (Pi.π (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) k) := by
            simpa [Category.assoc] using
              congrArg
                (fun m ↦
                  colim.map (tail_branch_product_diagram_hom
                    (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)) ≫ m)
                hπ
    _ =
      colim.map
        (tail_branch_product_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) ≫
          Pi.π (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) k) := by
            rw [← Functor.map_comp]
    _ =
      colim.map (tail_branch_diagram_hom
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k) := by
            congr 1
            simpa [tail_branch_product_diagram_hom] using
              (Pi.lift_π
                (p := fun k : 𝒰.index =>
                  tail_branch_diagram_hom
                    (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
                k)

/-- Helper for Lemma 7.39.1: at a fixed tail stage, projecting the product-valued branch map to
coordinate `k` gives the explicit restriction map along the pullback second projection. -/
theorem tail_branch_product_projection_app_eq_stage_restriction
    [HasPullbacks C] {ι : Type w} [Preorder ι] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) (j : (Set.Ici j₁)ᵒᵖᵒᵖ) (k : 𝒰.index) :
    ((Pi.π (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) k).app j) ∘
        ((tail_branch_product_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)).app j) =
      fun t ↦
        Fobj.map
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (unop (unop j)).2).op ≫ f₁)).op t := by
  -- First project the lifted tuple to the chosen branch coordinate.
  ext t
  have hπ :
      ((Pi.π (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) k).app j)
          (((tail_branch_product_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)).app j) t) =
        ((tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k).app j) t := by
    simpa [CategoryTheory.types_comp_apply, tail_branch_product_diagram_hom] using
      congrFun
        (congrArg (fun η ↦ η.app j)
          (Pi.lift_π
            (p := fun k : 𝒰.index =>
              tail_branch_diagram_hom
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
            k))
        t
  -- Then unfold the remaining branch coordinate to the literal pullback restriction.
  simpa [tail_branch_diagram_hom, branch_system_snd_hom] using hπ

/-- Helper for Lemma 7.39.1: at each tail stage, the branch-product restriction map is injective
because the pulled-back finite cover is separating for sheaf sections. -/
theorem tail_branch_stage_product_injective
    [HasPullbacks C] {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (h𝒰 : 𝒰.toSieve ∈ J W) (ℱ : Sheaf J (Type (max u v w)))
    (j : (Set.Ici j₁)ᵒᵖᵒᵖ) :
    Function.Injective
      ((tail_branch_product_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
          (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ)).app j) := by
  -- Project each coordinate to the explicit pullback restriction map at the chosen tail stage and
  -- invoke the sheaf separatedness statement for that pulled-back finite cover.
  intro s t hst
  apply stage_pullback_cover_restriction_injective (J := J) (𝒰 := 𝒰) h𝒰 ℱ
    (S.map (homOfLE (unop (unop j)).2).op ≫ f₁)
  funext k
  let πk :
      ((∏ᶜ fun k : 𝒰.index =>
          (branch_system S j₁ f₁ 𝒰 k).op ⋙
            (sheafToPresheaf J (Type (max u v w))).obj ℱ).obj j) →
        (((branch_system S j₁ f₁ 𝒰 k).op ⋙
          (sheafToPresheaf J (Type (max u v w))).obj ℱ).obj j) :=
    ((Pi.π (fun k : 𝒰.index =>
      (branch_system S j₁ f₁ 𝒰 k).op ⋙
        (sheafToPresheaf J (Type (max u v w))).obj ℱ) k).app j)
  have hk :
      πk
          ((tail_branch_product_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ)).app j s) =
        πk
          ((tail_branch_product_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ)).app j t) := by
    exact congrArg πk hst
  have hsProj :
      πk
          ((tail_branch_product_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ)).app j s) =
        ℱ.obj.map
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (unop (unop j)).2).op ≫ f₁)).op s := by
    simpa [CategoryTheory.types_comp_apply] using
      congrFun
        (tail_branch_product_projection_app_eq_stage_restriction
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
          (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ) (j := j) (k := k))
        s
  have htProj :
      πk
          ((tail_branch_product_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ)).app j t) =
        ℱ.obj.map
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (unop (unop j)).2).op ≫ f₁)).op t := by
    simpa [CategoryTheory.types_comp_apply] using
      congrFun
        (tail_branch_product_projection_app_eq_stage_restriction
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
          (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ) (j := j) (k := k))
        t
  exact hsProj.symm.trans (hk.trans htProj)

/-- Helper for Lemma 7.39.1: equality in one branch raw presheaf fiber can be canceled back to
the corresponding equality on the branch colimit before the raw-fiber comparison isomorphism. -/
theorem tail_branch_raw_eq_implies_branch_colimit_eq
    [HasPullbacks C] {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    [Nonempty (Set.Ici j₁)] [IsDirected (Set.Ici j₁) (· ≤ ·)]
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) (k : 𝒰.index)
    {x y : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj}
    (hxy :
      tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k x =
        tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k y) :
    colim.map
        (tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
        ((inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj).inv x) =
    colim.map
        (tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
        ((inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj).inv y) := by
  let tailIso := inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj
  let branchIso := inverse_system_presheafFiber_colimitIso (branch_system S j₁ f₁ 𝒰 k) Fobj
  have hxy' : branchIso.inv
      (tail_branch_presheafFiber_map
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k x) =
    branchIso.inv
      (tail_branch_presheafFiber_map
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k y) := by
    exact congrArg branchIso.inv hxy
  -- Cancel the branch colimit comparison isomorphism on the chosen coordinate.
  simpa [tail_branch_presheafFiber_map, tailIso, branchIso] using hxy'

/-- Helper for Lemma 7.39.1: the source-proof map from the tail raw presheaf fiber to the product
of the branch raw presheaf fibers is injective for sheaf sections. -/
theorem tail_branch_product_map_injective
    [HasPullbacks C] {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    [Finite 𝒰.index] (h𝒰 : 𝒰.toSieve ∈ J W) (ℱ : Sheaf J (Type (max u v w))) :
    Function.Injective
      (tail_branch_product_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
        ((sheafToPresheaf J (Type (max u v w))).obj ℱ)) := by
  -- Route correction: the remaining gap is no longer the coordinatewise branch cancellation. The
  -- helper `tail_branch_raw_eq_implies_branch_colimit_eq` now isolates that step, so the only
  -- missing source-proof ingredient is the finite-product comparison
  -- `colimit (j ↦ ∀ k, F(V_{j,k})) ≅ ∀ k, colimit (j ↦ F(V_{j,k}))` from Lemma 4.19.2, packaged in
  -- a universe-stable form that matches `tail_branch_product_map`.
  let _ : Nonempty (Set.Ici j₁) := ⟨⟨j₁, le_rfl⟩⟩
  let _ : IsDirected (Set.Ici j₁) (· ≤ ·) := tail_index_isDirected (j₁ := j₁)
  let Fobj : Cᵒᵖ ⥤ Type (max u v w) := (sheafToPresheaf J (Type (max u v w))).obj ℱ
  let tailIso := inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj
  letI : Fintype 𝒰.index := Fintype.ofFinite 𝒰.index
  let e : Fin (Fintype.card 𝒰.index) ≃ 𝒰.index := (Fintype.equivFin 𝒰.index).symm
  let family :
      Fin (Fintype.card 𝒰.index) → (Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w) :=
    fun n => (branch_system S j₁ f₁ 𝒰 (e n)).op ⋙ Fobj
  let θ :
      (tail_system S j₁).op ⋙ Fobj ⟶ ∏ᶜ family :=
    Pi.lift fun n =>
      tail_branch_diagram_hom
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n)
  let productIso := PreservesProduct.iso
    (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w)))
    family
  let tupleIso :
      colimit (∏ᶜ family) ≅
        ∀ n : Fin (Fintype.card 𝒰.index), colimit (family n) :=
    productIso ≪≫ Types.productIso (fun n => colimit (family n))
  have htupleIso_injective : Function.Injective tupleIso.hom :=
    (ConcreteCategory.bijective_of_isIso tupleIso.hom).1
  have hθ_app_injective :
      ∀ j : (Set.Ici j₁)ᵒᵖᵒᵖ, Function.Injective (θ.app j) := by
    intro j s t hst
    -- Reindex the tuple equality back along `e : Fin n ≃ 𝒰.index`, then invoke separatedness
    -- for the pulled-back cover at the tail stage `j`.
    apply stage_pullback_cover_restriction_injective (J := J) (𝒰 := 𝒰) h𝒰 ℱ
      (S.map (homOfLE (unop (unop j)).2).op ≫ f₁)
    funext k
    let n : Fin (Fintype.card 𝒰.index) := e.symm k
    let πn :
        ((∏ᶜ family).obj j) → ((family n).obj j) :=
      (Pi.π family n).app j
    have hkEq : e n = k := by
      simp [n]
    have hπeq :
        ((tail_branch_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n)).app j) s =
          ((tail_branch_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n)).app j) t := by
      have hn :
          πn ((θ.app j) s) = πn ((θ.app j) t) := by
        exact congrArg πn hst
      have hsπ :
          πn ((θ.app j) s) =
            ((tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n)).app j) s := by
        simpa [πn, θ, CategoryTheory.types_comp_apply] using
          congrFun
            (congrArg (fun η ↦ η.app j)
              (Pi.lift_π
                (p := fun n =>
                  tail_branch_diagram_hom
                    (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
                n))
            s
      have htπ :
          πn ((θ.app j) t) =
            ((tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n)).app j) t := by
        simpa [πn, θ, CategoryTheory.types_comp_apply] using
          congrFun
            (congrArg (fun η ↦ η.app j)
              (Pi.lift_π
                (p := fun n =>
                  tail_branch_diagram_hom
                    (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
                n))
            t
      exact hsπ.symm.trans (hn.trans htπ)
    rw [hkEq] at hπeq
    simpa [Fobj, tail_branch_diagram_hom, branch_system_snd_hom] using hπeq
  have htailMap_injective : Function.Injective (colim.map θ) := by
    -- This is exactly the source-proof stagewise injectivity step on the pulled-back finite cover.
    letI : Mono θ :=
      (NatTrans.mono_iff_mono_app θ).2 fun j ↦ (mono_iff_injective _).2 (hθ_app_injective j)
    exact (mono_iff_injective _).1 (colim.map_mono θ)
  intro x y hxy
  have hcoord :
      ∀ n : Fin (Fintype.card 𝒰.index),
        colim.map
            (tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            (tailIso.inv x) =
          colim.map
            (tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            (tailIso.inv y) := by
    intro n
    -- Each product coordinate is the chosen branch raw-fiber map.
    exact
      tail_branch_raw_eq_implies_branch_colimit_eq
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (k := e n)
        (hxy := congrFun hxy (e n))
  have hproduct_hom :
      tupleIso.hom (colim.map θ (tailIso.inv x)) =
        tupleIso.hom (colim.map θ (tailIso.inv y)) := by
    -- Compare the product images coordinatewise after the finite-product comparison isomorphism.
    funext n
    have hxproj :
        (tupleIso.hom (colim.map θ (tailIso.inv x))) n =
          colim.map
            (tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            (tailIso.inv x) := by
      have hπ :
          tupleIso.hom ≫ (fun f ↦ f n) =
            colim.map (Pi.π family n) := by
        have hπ0 :
            tupleIso.hom ≫ (fun f ↦ f n) =
              productIso.hom ≫ Pi.π (fun n => colimit (family n)) n := by
          simp [tupleIso, Category.assoc, Types.productIso_hom_comp_eval]
        exact hπ0.trans <| by
          simpa [PreservesProduct.iso_hom] using
            (piComparison_comp_π
              (G := (colim :
                (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w))))
              (f := family) n)
      have hπx := congrFun hπ (colim.map θ (tailIso.inv x))
      have hmapcomp :
          colim.map (Pi.π family n) (colim.map θ (tailIso.inv x)) =
            colim.map (θ ≫ Pi.π family n) (tailIso.inv x) := by
        have hcomp :
            colim.map θ ≫ colim.map (Pi.π family n) =
              colim.map (θ ≫ Pi.π family n) := by
          rw [← Functor.map_comp]
        simpa [CategoryTheory.types_comp_apply] using congrFun hcomp (tailIso.inv x)
      have hθπ :
          θ ≫ Pi.π family n =
            tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n) := by
        simpa [θ] using
          (Pi.lift_π
            (p := fun n =>
              tail_branch_diagram_hom
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            n)
      calc
        (tupleIso.hom (colim.map θ (tailIso.inv x))) n =
          colim.map (Pi.π family n) (colim.map θ (tailIso.inv x)) := by
            simpa [CategoryTheory.types_comp_apply] using hπx
        _ = colim.map (θ ≫ Pi.π family n) (tailIso.inv x) := hmapcomp
        _ = colim.map
              (tail_branch_diagram_hom
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
              (tailIso.inv x) := by rw [hθπ]
    have hyproj :
        (tupleIso.hom (colim.map θ (tailIso.inv y))) n =
          colim.map
            (tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            (tailIso.inv y) := by
      have hπ :
          tupleIso.hom ≫ (fun f ↦ f n) =
            colim.map (Pi.π family n) := by
        have hπ0 :
            tupleIso.hom ≫ (fun f ↦ f n) =
              productIso.hom ≫ Pi.π (fun n => colimit (family n)) n := by
          simp [tupleIso, Category.assoc, Types.productIso_hom_comp_eval]
        exact hπ0.trans <| by
          simpa [PreservesProduct.iso_hom] using
            (piComparison_comp_π
              (G := (colim :
                (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w))))
              (f := family) n)
      have hπy := congrFun hπ (colim.map θ (tailIso.inv y))
      have hmapcomp :
          colim.map (Pi.π family n) (colim.map θ (tailIso.inv y)) =
            colim.map (θ ≫ Pi.π family n) (tailIso.inv y) := by
        have hcomp :
            colim.map θ ≫ colim.map (Pi.π family n) =
              colim.map (θ ≫ Pi.π family n) := by
          rw [← Functor.map_comp]
        simpa [CategoryTheory.types_comp_apply] using congrFun hcomp (tailIso.inv y)
      have hθπ :
          θ ≫ Pi.π family n =
            tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n) := by
        simpa [θ] using
          (Pi.lift_π
            (p := fun n =>
              tail_branch_diagram_hom
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            n)
      calc
        (tupleIso.hom (colim.map θ (tailIso.inv y))) n =
          colim.map (Pi.π family n) (colim.map θ (tailIso.inv y)) := by
            simpa [CategoryTheory.types_comp_apply] using hπy
        _ = colim.map (θ ≫ Pi.π family n) (tailIso.inv y) := hmapcomp
        _ = colim.map
              (tail_branch_diagram_hom
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
              (tailIso.inv y) := by rw [hθπ]
    exact hxproj.trans ((hcoord n).trans hyproj.symm)
  have hproduct : colim.map θ (tailIso.inv x) = colim.map θ (tailIso.inv y) := by
    -- Cancel the product comparison isomorphism to return to the colimit of the tuple diagram.
    exact htupleIso_injective hproduct_hom
  have htail : tailIso.inv x = tailIso.inv y := htailMap_injective hproduct
  -- Finally cancel the tail raw-fiber comparison isomorphism.
  simpa using congrArg tailIso.hom htail

end

end CategoryTheory
