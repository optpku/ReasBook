module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_8_2
public import stacks_project.Chap07.Lemma_7_39_1
public import stacks_project.Chap07.Lemma_7_39_2.OmegaSystem

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

section

variable {J : GrothendieckTopology C}

open GrothendieckTopology.Point.ofIsCofiltered

variable {ι : Type w} [Preorder ι]

/-- Helper for Lemma 7.39.2: the index type of the direct union of a directed diagram of
packaged refinement stages. A point is a stage of the diagram together with an index in that
stage. -/
def refinementStageDiagramIndex
    {δ : Type w}
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s') :=
  Σ a : δ, (A a).I

/-- Helper for Lemma 7.39.2: order on the direct-union index of a directed diagram of packaged
refinement stages. A point at stage `a` is below a point at stage `b` if `a ≤ b` in the diagram
and its image under the comparison morphism is below the target index. -/
def refinementStageDiagramIndexLE
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (x y : refinementStageDiagramIndex (J := J) A) : Prop :=
  ∃ h : x.1 ≤ y.1, (hom h).k x.2 ≤ y.2

/-- Helper for Lemma 7.39.2: extract the diagram-stage comparison from a direct-union index
comparison. -/
def refinementStageDiagramIndexLE_stageLe
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    {x y : refinementStageDiagramIndex (J := J) A}
    (hxy : refinementStageDiagramIndexLE (J := J) A hom x y) : x.1 ≤ y.1 := by
  exact Classical.choose hxy

/-- Helper for Lemma 7.39.2: the index comparison attached to a direct-union index comparison. -/
theorem refinementStageDiagramIndexLE_rel
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    {x y : refinementStageDiagramIndex (J := J) A}
    (hxy : refinementStageDiagramIndexLE (J := J) A hom x y) :
    (hom (refinementStageDiagramIndexLE_stageLe (J := J) A hom hxy)).k x.2 ≤ y.2 := by
  simpa [refinementStageDiagramIndexLE_stageLe] using Classical.choose_spec hxy

/-- Helper for Lemma 7.39.2: the direct-union index of a coherent directed diagram of packaged
refinement stages is a preorder. -/
@[reducible] def refinementStageDiagramIndexPreorder
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc)) :
    Preorder (refinementStageDiagramIndex (J := J) A) where
  le := refinementStageDiagramIndexLE (J := J) A hom
  lt := fun x y =>
    refinementStageDiagramIndexLE (J := J) A hom x y ∧
      ¬ refinementStageDiagramIndexLE (J := J) A hom y x
  le_refl x := by
    -- Reflexivity is the identity comparison at the diagram stage of `x`.
    refine ⟨le_rfl, ?_⟩
    simpa [hom_refl x.1, refinement_stage_hom_refl]
  le_trans x y z hxy hyz := by
    -- Compose the two stage comparisons and transport the order inequality through the second
    -- comparison embedding.
    let hxy_stage := refinementStageDiagramIndexLE_stageLe (J := J) A hom hxy
    let hyz_stage := refinementStageDiagramIndexLE_stageLe (J := J) A hom hyz
    let hxy_index := refinementStageDiagramIndexLE_rel (J := J) A hom hxy
    let hyz_index := refinementStageDiagramIndexLE_rel (J := J) A hom hyz
    have hxz_index :
        (hom (le_trans hxy_stage hyz_stage)).k x.2 ≤ z.2 := by
      have hcomp_k :
          (hom (le_trans hxy_stage hyz_stage)).k x.2 =
            (hom hyz_stage).k ((hom hxy_stage).k x.2) := by
        have h :=
          congrArg (fun H : refinement_stage_hom (J := J) (A x.1) (A z.1) => H.k x.2)
            (hom_comp hxy_stage hyz_stage)
        simpa [refinement_stage_hom.comp, compose_refinement_embedding] using h
      rw [hcomp_k]
      exact le_trans ((hom hyz_stage).k.map_rel_iff.mpr hxy_index) hyz_index
    exact ⟨le_trans hxy_stage hyz_stage, hxz_index⟩
  lt_iff_le_not_ge := by
    intro a b
    rfl

/-- Helper for Lemma 7.39.2: the direct-union index of a directed diagram of packaged refinement
stages is directed. -/
@[reducible] def refinementStageDiagramIndexDirected
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b)) :
    IsDirected (refinementStageDiagramIndex (J := J) A)
      (refinementStageDiagramIndexLE (J := J) A hom) where
  directed x y := by
    -- Move both indices to a common later diagram stage, then use directedness inside that
    -- packaged stage.
    rcases IsDirected.directed (r := (· ≤ ·)) x.1 y.1 with ⟨c, hxc, hyc⟩
    let x_c := (hom hxc).k x.2
    let y_c := (hom hyc).k y.2
    letI : Preorder (A c).I := (A c).instPreorder
    letI : IsDirected (A c).I (· ≤ ·) := (A c).instDirected
    rcases IsDirected.directed (r := (· ≤ ·)) x_c y_c with ⟨z, hxz, hyz⟩
    refine ⟨⟨c, z⟩, ?_, ?_⟩
    · exact ⟨hxc, hxz⟩
    · exact ⟨hyc, hyz⟩

/-- Helper for Lemma 7.39.2: a diagram stage embeds order-theoretically into the direct-union
index of a coherent directed diagram of packaged refinement stages. -/
noncomputable def refinementStageDiagramIndexInclusion
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a : δ) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    (A a).I ↪o refinementStageDiagramIndex (J := J) A := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  exact {
    toFun := fun i => ⟨a, i⟩
    inj' := by
      intro i j hij
      cases hij
      rfl
    map_rel_iff' := by
      intro i j
      constructor
      · intro hij
        rcases hij with ⟨haa, hij'⟩
        have haa_eq : haa = (le_rfl : a ≤ a) := Subsingleton.elim _ _
        simpa [haa_eq, hom_refl a, refinement_stage_hom_refl] using hij'
      · intro hij
        exact ⟨le_rfl, by simpa [hom_refl a, refinement_stage_hom_refl] using hij⟩
  }

/-- Helper for Lemma 7.39.2: the comparison morphism in `C` attached to one order comparison in
the direct-union index of a coherent directed diagram of packaged refinement stages. -/
noncomputable def refinementStageDiagramSystemMap
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (X Y : (refinementStageDiagramIndex (J := J) A)ᵒᵖ)
    (hYX : refinementStageDiagramIndexLE (J := J) A hom (Opposite.unop Y)
      (Opposite.unop X)) :
    (A (Opposite.unop X).1).T.obj (Opposite.op (Opposite.unop X).2) ⟶
      (A (Opposite.unop Y).1).T.obj (Opposite.op (Opposite.unop Y).2) := by
  let hYX_stage : (Opposite.unop Y).1 ≤ (Opposite.unop X).1 := Classical.choose hYX
  let hYX_index : (hom hYX_stage).k (Opposite.unop Y).2 ≤ (Opposite.unop X).2 :=
    Classical.choose_spec hYX
  exact
    (A (Opposite.unop X).1).T.map (homOfLE hYX_index).op ≫
      (hom hYX_stage).hT.inv.app (Opposite.op (Opposite.unop Y).2)

/-- Helper for Lemma 7.39.2: the direct-union comparison morphism is independent of the proof of
the order comparison in the direct-union index. -/
theorem refinementStageDiagramSystemMap_proof_irrel
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (X Y : (refinementStageDiagramIndex (J := J) A)ᵒᵖ)
    (h h' : refinementStageDiagramIndexLE (J := J) A hom (Opposite.unop Y)
      (Opposite.unop X)) :
    refinementStageDiagramSystemMap (J := J) A hom X Y h =
      refinementStageDiagramSystemMap (J := J) A hom X Y h' := by
  have hh : h = h' := Subsingleton.elim _ _
  subst h'
  rfl

/-- Helper for Lemma 7.39.2: the direct-union comparison morphism attached to an identity
comparison is the identity morphism in `C`. -/
theorem refinementStageDiagramSystemMap_id
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc)) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    ∀ X : (refinementStageDiagramIndex (J := J) A)ᵒᵖ,
      refinementStageDiagramSystemMap (J := J) A hom X X
          (leOfHom (𝟙 (Opposite.unop X))) =
        𝟙 ((A (Opposite.unop X).1).T.obj (Opposite.op (Opposite.unop X).2)) := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  intro X
  cases X using Opposite.rec
  rename_i x
  let hcanon : refinementStageDiagramIndexLE (J := J) A hom x x := by
    refine ⟨le_rfl, ?_⟩
    simpa [hom_refl x.1, refinement_stage_hom_refl]
  rw [refinementStageDiagramSystemMap_proof_irrel (J := J) A hom (Opposite.op x)
    (Opposite.op x) (leOfHom (𝟙 x)) hcanon]
  rcases x with ⟨a, i⟩
  -- With the canonical comparison chosen, this is the identity-stage comparison calculation.
  change (A a).T.map (homOfLE (Classical.choose_spec hcanon)).op ≫
      (hom (Classical.choose hcanon)).hT.inv.app (Opposite.op i) =
    𝟙 ((A a).T.obj (Opposite.op i))
  exact refinement_stage_hom_self_comparison_map_id (J := J) (A := A a)
    (H := hom (Classical.choose hcanon))
    (by
      have hchoose : Classical.choose hcanon = (le_rfl : a ≤ a) := Subsingleton.elim _ _
      simpa [hchoose] using hom_refl a)
    i _

/-- Helper for Lemma 7.39.2: on two indices from the same diagram stage, the direct-union
comparison morphism is the ordinary transition morphism of that stage. -/
theorem refinementStageDiagramSystemMap_same_stage
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (a : δ) {i j : (A a).I} (hij : j ≤ i) :
    refinementStageDiagramSystemMap (J := J) A hom
        (Opposite.op (⟨a, i⟩ : refinementStageDiagramIndex (J := J) A))
        (Opposite.op (⟨a, j⟩ : refinementStageDiagramIndex (J := J) A))
        (⟨le_rfl, by simpa [hom_refl a, refinement_stage_hom_refl] using hij⟩) =
      (A a).T.map (homOfLE hij).op := by
  let hcanon : refinementStageDiagramIndexLE (J := J) A hom
      (⟨a, j⟩ : refinementStageDiagramIndex (J := J) A) ⟨a, i⟩ :=
    ⟨le_rfl, by simpa [hom_refl a, refinement_stage_hom_refl] using hij⟩
  -- Normalize the chosen same-stage comparison to the identity stage morphism.
  change (A a).T.map (homOfLE (Classical.choose_spec hcanon)).op ≫
      (hom (Classical.choose hcanon)).hT.inv.app (Opposite.op j) =
    (A a).T.map (homOfLE hij).op
  exact refinement_stage_hom_self_comparison_map (J := J) (A := A a)
    (H := hom (Classical.choose hcanon))
    (by
      have hchoose : Classical.choose hcanon = (le_rfl : a ≤ a) := Subsingleton.elim _ _
      simpa [hchoose] using hom_refl a)
    i j hij _

/-- Helper for Lemma 7.39.2: direct-union comparison morphisms for a coherent diagram compose
functorially. -/
theorem refinementStageDiagramSystemMap_comp
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (X Y Z : (refinementStageDiagramIndex (J := J) A)ᵒᵖ)
    (hYX : refinementStageDiagramIndexLE (J := J) A hom (Opposite.unop Y)
      (Opposite.unop X))
    (hZY : refinementStageDiagramIndexLE (J := J) A hom (Opposite.unop Z)
      (Opposite.unop Y))
    (hZX : refinementStageDiagramIndexLE (J := J) A hom (Opposite.unop Z)
      (Opposite.unop X)) :
    refinementStageDiagramSystemMap (J := J) A hom X Z hZX =
      refinementStageDiagramSystemMap (J := J) A hom X Y hYX ≫
        refinementStageDiagramSystemMap (J := J) A hom Y Z hZY := by
  let hYX_stage := refinementStageDiagramIndexLE_stageLe (J := J) A hom hYX
  let hZY_stage := refinementStageDiagramIndexLE_stageLe (J := J) A hom hZY
  let hZX_stage := refinementStageDiagramIndexLE_stageLe (J := J) A hom hZX
  let hYX_index := refinementStageDiagramIndexLE_rel (J := J) A hom hYX
  let hZY_index := refinementStageDiagramIndexLE_rel (J := J) A hom hZY
  let hZX_index := refinementStageDiagramIndexLE_rel (J := J) A hom hZX
  have hZX_eq :
      hom hZX_stage =
        refinement_stage_hom.comp (J := J) (hom hZY_stage) (hom hYX_stage) := by
    rw [show hZX_stage = le_trans hZY_stage hYX_stage by exact Subsingleton.elim _ _]
    exact hom_comp hZY_stage hYX_stage
  -- The concrete comparison maps are precisely the comparison maps for the composed stage
  -- morphism and the two constituent stage morphisms.
  exact refinement_stage_hom_comparison_map_comp (J := J)
    (hAB := hom hZY_stage) (hBD := hom hYX_stage) (hAD := hom hZX_stage) hZX_eq
    (i := (Opposite.unop Z).2) (j := (Opposite.unop Y).2) (k := (Opposite.unop X).2)
    (hij := hZY_index) (hjk := hYX_index) (hik := hZX_index)

/-- Helper for Lemma 7.39.2: the inverse system over the direct-union index associated to a
coherent directed diagram of packaged refinement stages. -/
noncomputable def refinementStageDiagramSystem
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc)) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    (refinementStageDiagramIndex (J := J) A)ᵒᵖ ⥤ C := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  exact {
    obj := fun X => (A (Opposite.unop X).1).T.obj (Opposite.op (Opposite.unop X).2)
    map := fun {X Y} f =>
      refinementStageDiagramSystemMap (J := J) A hom X Y (leOfHom f.unop)
    map_id := by
      intro X
      exact refinementStageDiagramSystemMap_id (J := J) A hom hom_refl hom_comp X
    map_comp := by
      intro X Y Z f g
      exact refinementStageDiagramSystemMap_comp (J := J) A hom hom_comp X Y Z
        (leOfHom f.unop) (leOfHom g.unop) (leOfHom (f ≫ g).unop)
  }

/-- Helper for Lemma 7.39.2: restricting the direct-union system of a coherent directed diagram
to one diagram stage recovers that stage's inverse system. -/
noncomputable def refinementStageDiagramSystemInclusionIso
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a : δ) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    (A a).T ≅ ((refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a
      ).toOrderHom.toFunctor).op ⋙
        refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  refine NatIso.ofComponents (fun X => Iso.refl _) ?_
  intro X Y f
  have hmap :=
    refinementStageDiagramSystemMap_same_stage (J := J) A hom hom_refl a
      (leOfHom f.unop)
  simpa [refinementStageDiagramSystem, refinementStageDiagramIndexInclusion,
    Functor.comp_obj, Functor.comp_map] using hmap.symm

/-- Helper for Lemma 7.39.2: every finite-cover request on the direct-union system of a coherent
directed stage diagram is transported from a request on one diagram stage. -/
theorem refinementStageDiagramSystem_request_descends
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc)) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    ∀ r : finite_cover_lift_request J
        (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp),
      ∃ a, ∃ r0 : finite_cover_lift_request J (A a).T,
        transport_request (J := J)
          (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a)
          (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
          (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp a) r0 =
            r := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  intro r
  rcases fiberMk_jointly_surjective r.f with ⟨X, f, hf⟩
  let a : δ := (Opposite.unop X).1
  let i : (A a).I := (Opposite.unop X).2
  let f0 : (A a).T.obj (Opposite.op i) ⟶ r.W := by
    simpa [a, i, refinementStageDiagramSystem] using f
  let r0 : finite_cover_lift_request J (A a).T := {
    W := r.W
    n := r.n
    obj := r.obj
    h𝒰 := r.h𝒰
    f := fiberMk f0
  }
  refine ⟨a, r0, ?_⟩
  cases r
  simp [r0, transport_request, f0, a, i, refinementStageDiagramSystemInclusionIso,
    refinementFiber_app_fiberMk] at hf ⊢
  have hmap :
      ((refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp).map (𝟙 X)) =
        𝟙 ((A (Opposite.unop X).1).T.obj (Opposite.op (Opposite.unop X).2)) := by
    simpa [refinementStageDiagramSystem] using
      refinementStageDiagramSystemMap_id (J := J) A hom hom_refl hom_comp X
  rw [← hmap]
  exact (fiberMk_map_comp.{max u v w}
    (p := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
    (g := 𝟙 X) (f := f)).trans hf

/-- Helper for Lemma 7.39.2: the original refinement embedding of a diagram stage, followed by
the canonical inclusion of that stage into the direct-union index. -/
noncomputable def refinementStageDiagramSystemOriginalEmbedding
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a : δ) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    ι ↪o refinementStageDiagramIndex (J := J) A := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  exact compose_refinement_embedding (A a).j
    (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a)

/-- Helper for Lemma 7.39.2: restricting the direct-union system along the composed original
embedding recovers the original inverse system. -/
noncomputable def refinementStageDiagramSystemOriginalIso
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a : δ) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    S' ≅
      (((refinementStageDiagramSystemOriginalEmbedding
        (J := J) A hom hom_refl hom_comp a).toOrderHom.toFunctor).op ⋙
          refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp) := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  exact compose_refinement_iso (A a).j
    (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a)
    (A a).e (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp a)

/-- Helper for Lemma 7.39.2: the solved requests carried by the direct union of a coherent
directed diagram are exactly the transports of requests already marked solved on some stage of
the diagram. -/
def refinementStageDiagramLimitSolved
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc)) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    Set (finite_cover_lift_request J
      (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)) := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  exact {r | ∃ a, ∃ r0 : finite_cover_lift_request J (A a).T,
    r0 ∈ (A a).solved ∧
      transport_request (J := J)
        (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a)
        (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
        (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp a) r0 = r}

/-- Helper for Lemma 7.39.2: requests in the transported solved set of a direct-union diagram are
realized on the direct-union system. -/
theorem refinementStageDiagramLimitSolved_realized
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc)) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    ∀ ⦃r : finite_cover_lift_request J
        (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)⦄,
      r ∈ refinementStageDiagramLimitSolved (J := J) A hom hom_refl hom_comp →
        request_realized (J := J) r := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  intro r hr
  rcases hr with ⟨a, r0, hr0, rfl⟩
  exact request_realized_transport (J := J)
    (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a)
    (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
    (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp a)
    r0 ((A a).solved_realized hr0)

end

end CategoryTheory
