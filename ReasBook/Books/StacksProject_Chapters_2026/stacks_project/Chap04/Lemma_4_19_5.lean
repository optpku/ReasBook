module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import stacks_project.Chap04.Lemma_4_19_4
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.FunctorToTypes

universe u v

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I]
variable (M : I ⥤ AddCommGrpCat.{max u v})

/-
Domain-style sampling for Lemma 4.19.5:
- primary domain: comparison maps between `Type`-colimits and additive colimits
- inspected owner declarations:
  - `colimit.post`
  - `prodComparison_colim_surjective_of_commonSuccessor`
  - `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`
  - `CategoryTheory.epi_iff_surjective`
- source-facing hypotheses: nonemptiness of the index category and common successors for pairs of
  objects
- best owner abstraction: the canonical comparison morphism
  `colimit.post M (forget AddCommGrpCat)`; under the stronger hypothesis `[IsFiltered I]`, the
  filtered-colimit owner `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits` upgrades
  this comparison map to an isomorphism
- canonical bridge reused in the proof: `prodComparison_colim_surjective_of_commonSuccessor`
- primitive data: the additive diagram `M`, the source-level nonemptiness hypothesis `hI`, and
  the source-level common-successor hypothesis
- derived API: the surjectivity and epimorphism consequences for
  `colimit.post M (forget AddCommGrpCat)`
- target layer here: `bridge/view`, namely the surjectivity and epimorphism consequences for the
  comparison map from the `Type`-colimit to the underlying set of the additive colimit; the
  theorem stays at this layer because the source hypotheses are weaker than filteredness
-/

/-- Helper for Lemma 4.19.5: the comparison map from the `Type`-colimit to the additive colimit
agrees with the colimit inclusions on each stage. -/
theorem colimit_post_ι_apply (i : I) (x : (M ⋙ forget AddCommGrpCat).obj i) :
    colimit.post M (forget AddCommGrpCat) (colimit.ι (M ⋙ forget AddCommGrpCat) i x) =
      colimit.ι M i x := by
  -- The comparison map is characterized by compatibility with the colimit cocone.
  simpa using congrFun (colimit.ι_post M (forget AddCommGrpCat) i) x

/-- Helper for Lemma 4.19.5: the zero element of the additive colimit is represented by the zero
element at any stage. -/
theorem zero_single_stage_representative (i : I) :
    colimit.ι M i 0 = (0 : (colimit M : AddCommGrpCat.{max u v})) := by
  -- The colimit inclusion is an additive homomorphism, so it preserves zero.
  simp

/-- Helper for Lemma 4.19.5: the additive inverse of a single-stage representative is represented
at the same stage by the stagewise additive inverse. -/
theorem neg_single_stage_representative (i : I) (x : M.obj i) :
    colimit.ι M i (-x) = -(colimit.ι M i x : (colimit M : AddCommGrpCat.{max u v})) := by
  -- The colimit inclusion is an additive homomorphism, so it preserves negation.
  exact (colimit.ι M i).hom.map_neg x

/-- Helper for Lemma 4.19.5: two single-stage representatives in the additive colimit can be moved
to one common stage and summed there. -/
theorem sum_of_single_stage_representatives
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    {i j : I} (x : M.obj i) (y : M.obj j) :
    ∃ k : I, ∃ z : M.obj k, colimit.ι M k z = colimit.ι M i x + colimit.ι M j y := by
  classical
  let F : I ⥤ Type (max u v) := M ⋙ forget AddCommGrpCat
  let e := Types.binaryProductIso (colimit F) (colimit F)
  have hprodSurj : Function.Surjective (prodComparison colim F F) :=
    prodComparison_colim_surjective_of_commonSuccessor hObj F F
  -- Move the pair of representatives to one stage in the product diagram.
  obtain ⟨w, hw⟩ := hprodSurj (e.inv (colimit.ι F i x, colimit.ι F j y))
  obtain ⟨k, xy, hxy⟩ := Types.jointly_surjective' w
  let xk : M.obj k := (prod.fst : F ⨯ F ⟶ F).app k xy
  let yk : M.obj k := (prod.snd : F ⨯ F ⟶ F).app k xy
  refine ⟨k, xk + yk, ?_⟩
  have hpair :
      prodComparison colim F F (colimit.ι (F ⨯ F) k xy) =
        e.inv (colimit.ι F i x, colimit.ι F j y) := by
    rw [hxy]
    exact hw
  have hpair_fst :
      ((Types.binaryProductIso (colimit F) (colimit F)).hom
        (prodComparison colim F F (colimit.ι (F ⨯ F) k xy))).1 =
        colimit.ι F i x := by
    -- Projecting to the first factor identifies the first transported representative.
    simpa [e] using congrArg (fun p ↦ p.1) (congrArg e.hom hpair)
  have hpair_snd :
      ((Types.binaryProductIso (colimit F) (colimit F)).hom
        (prodComparison colim F F (colimit.ι (F ⨯ F) k xy))).2 =
        colimit.ι F j y := by
    -- Projecting to the second factor does the same for the second representative.
    simpa [e] using congrArg (fun p ↦ p.2) (congrArg e.hom hpair)
  have hxk : colimit.ι F k xk = colimit.ι F i x := by
    rw [← prodComparison_colim_ι_fst F F k xy]
    simpa [xk] using hpair_fst
  have hyk : colimit.ι F k yk = colimit.ι F j y := by
    rw [← prodComparison_colim_ι_snd F F k xy]
    simpa [yk] using hpair_snd
  have hxk' : colimit.ι M k xk = colimit.ι M i x := by
    -- Apply the comparison map to transport the equality back to the additive colimit.
    rw [← colimit_post_ι_apply M k xk, ← colimit_post_ι_apply M i x]
    exact congrArg (colimit.post M (forget AddCommGrpCat)) hxk
  have hyk' : colimit.ι M k yk = colimit.ι M j y := by
    rw [← colimit_post_ι_apply M k yk, ← colimit_post_ι_apply M j y]
    exact congrArg (colimit.post M (forget AddCommGrpCat)) hyk
  -- Once both terms live at one stage, their sum is represented by the stagewise sum.
  calc
    colimit.ι M k (xk + yk) = colimit.ι M k xk + colimit.ι M k yk := by
      exact (colimit.ι M k).hom.map_add xk yk
    _ = colimit.ι M i x + colimit.ι M j y := by
      rw [hxk', hyk']

/-- Helper for Lemma 4.19.5: every element of the additive colimit is already represented by one
element of one stage. -/
theorem every_colimit_element_has_single_stage_representative
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hI : Nonempty I) (z : (colimit M : AddCommGrpCat.{max u v})) :
    ∃ i : I, ∃ x : M.obj i, colimit.ι M i x = z := by
  classical
  let A : AddCommGrpCat.{max u v} := colimit M
  let i0 : I := Classical.choice hI
  let representedSet : Set A := fun a ↦ ∃ i : I, ∃ x : M.obj i, colimit.ι M i x = a
  have hzero : (0 : A) ∈ representedSet := by
    -- Nonemptiness provides a stage at which the zero element represents the colimit zero.
    refine ⟨i0, 0, ?_⟩
    exact zero_single_stage_representative M i0
  have hadd : ∀ {a b : A}, a ∈ representedSet → b ∈ representedSet → a + b ∈ representedSet := by
    intro a b ha hb
    rcases ha with ⟨i, x, rfl⟩
    rcases hb with ⟨j, y, rfl⟩
    -- The common-successor lemma compresses two stage representatives to one.
    exact sum_of_single_stage_representatives M hObj x y
  have hneg : ∀ {a : A}, a ∈ representedSet → -a ∈ representedSet := by
    intro a ha
    rcases ha with ⟨i, x, rfl⟩
    -- Negation is represented at the same stage by the stagewise additive inverse.
    exact ⟨i, -x, neg_single_stage_representative M i x⟩
  let representedSubgroup : AddSubgroup A :=
    { toAddSubmonoid :=
        { carrier := representedSet
          zero_mem' := hzero
          add_mem' := fun ha hb ↦ hadd ha hb }
      neg_mem' := fun ha ↦ hneg ha }
  have hstage_mem : ∀ i : I, ∀ x : M.obj i, colimit.ι M i x ∈ representedSubgroup := by
    intro i x
    simpa [representedSubgroup, representedSet] using
      (show ∃ j : I, ∃ y : M.obj j, colimit.ι M j y = colimit.ι M i x from ⟨i, x, rfl⟩)
  have hmap_zero :
      ∀ i : I, (⟨colimit.ι M i 0, hstage_mem i 0⟩ : representedSubgroup) = 0 := by
    intro i
    apply Subtype.ext
    simp
  have hmap_add :
      ∀ i : I, ∀ x y : M.obj i,
        (⟨colimit.ι M i (x + y), hstage_mem i (x + y)⟩ : representedSubgroup) =
          ⟨colimit.ι M i x, hstage_mem i x⟩ + ⟨colimit.ι M i y, hstage_mem i y⟩ := by
    intro i x y
    apply Subtype.ext
    simp
  let representedMap :
      ∀ i : I, M.obj i ⟶ AddCommGrpCat.of representedSubgroup := fun i ↦
        AddCommGrpCat.ofHom
          { toFun := fun x ↦ ⟨colimit.ι M i x, hstage_mem i x⟩
            map_zero' := hmap_zero i
            map_add' := hmap_add i }
  have hnatural :
      ∀ i j : I, ∀ f : i ⟶ j, M.map f ≫ representedMap j = representedMap i := by
    intro i j f
    ext x
    change (M.map f ≫ colimit.ι M j) x = colimit.ι M i x
    exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (colimit.w M f)) x
  let representedCocone : Cocone M :=
    { pt := AddCommGrpCat.of representedSubgroup
      ι :=
        { app := representedMap
          naturality := fun i j f ↦ hnatural i j f } }
  let representedIncl : AddCommGrpCat.of representedSubgroup ⟶ A :=
    AddCommGrpCat.ofHom representedSubgroup.subtype
  let descRepresented : A ⟶ AddCommGrpCat.of representedSubgroup :=
    colimit.desc M representedCocone
  have hdescRepresented : descRepresented ≫ representedIncl = 𝟙 A := by
    -- Both maps out of the colimit agree on each stage, so they agree globally.
    apply colimit.hom_ext
    intro i
    ext x
    change (((descRepresented ((colimit.ι M i) x) : representedSubgroup) : A)) = colimit.ι M i x
    have hx :
        descRepresented (colimit.ι M i x) = ⟨colimit.ι M i x, hstage_mem i x⟩ := by
      simp [descRepresented, representedCocone, representedMap]
    rw [hx]
  -- The section into the represented subgroup shows every colimit element lies there.
  let y : representedSubgroup := descRepresented z
  have hy : (y : A) = z := by
    simpa [y] using DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom hdescRepresented) z
  have hy_mem : representedSet (y : A) := by
    exact y.2
  have hy_repr : ∃ i : I, ∃ x : M.obj i, colimit.ι M i x = (y : A) := by
    simpa [representedSet] using hy_mem
  exact hy.symm ▸ hy_repr

/-- Lemma 4.19.5: if the index category is nonempty and every pair of its objects admits a common
successor, then the canonical comparison map from the colimit of `M` in sets to the underlying set
of the colimit of `M` in abelian groups is surjective. The nonemptiness hypothesis is necessary:
for the empty index category, the source colimit in `Type` is empty while the target is the
underlying singleton set of the zero abelian group. -/
-- Proof sketch: every element of the abelian-group colimit is represented by a finite sum of
-- images from objects of the diagram. The common-successor hypothesis lets us move finitely many
-- representatives to a single stage, where their sum is represented by one element, and that
-- element defines a preimage in the `Type`-colimit.
theorem addCommGrpColimitComparison_surjective_of_commonSuccessor
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hI : Nonempty I) :
    Function.Surjective (colimit.post M (forget AddCommGrpCat)) := by
  -- First represent the target element at a single stage of the additive diagram.
  intro z
  rcases every_colimit_element_has_single_stage_representative M hObj hI z with ⟨i, x, hx⟩
  -- The stage representative lifts directly to the `Type`-colimit through the comparison map.
  refine ⟨colimit.ι (M ⋙ forget AddCommGrpCat) i x, ?_⟩
  exact (colimit_post_ι_apply M i x).trans hx

/-- Categorical reformulation of Lemma 4.19.5 via the canonical `epi_iff_surjective` bridge. -/
theorem addCommGrpColimitComparison_epi_of_commonSuccessor
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hI : Nonempty I) :
    Epi (colimit.post M (forget AddCommGrpCat)) := by
  simpa using
    (epi_iff_surjective (colimit.post M (forget AddCommGrpCat))).mpr <|
      addCommGrpColimitComparison_surjective_of_commonSuccessor M hObj hI

end CategoryTheory.Limits
