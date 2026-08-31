module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_3_1
public import stacks_project.Chap07.Definition_7_17_1
public import stacks_project.Chap07.Lemma_7_17_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SemiRepresentableFamily.Over

universe z w v u

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily.Over

variable {C : Type u} [Category.{v} C] {U : C}
variable (𝒰 : SemiRepresentableFamily.Over.{w} U)
variable [𝒰.toPresieve.HasPairwisePullbacks]

/-- Pairwise pullbacks for a covering family provide the canonical pullback object of any two
members of that family. -/
instance (i j : 𝒰.index) : HasPullback (𝒰.obj i).hom (𝒰.obj j).hom := by
  let hpair : 𝒰.toPresieve.HasPairwisePullbacks := inferInstance
  exact hpair.has_pullbacks (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j)

end CategoryTheory.SemiRepresentableFamily.Over

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C}

/-- A covering family of `U` has quasi-compact pairwise overlaps if each canonical overlap
`Uᵢ ×[U] Uⱼ` is quasi-compact. -/
def HasQuasiCompactPairwiseOverlaps (J : GrothendieckTopology C)
    {U : C} (𝒰 : SemiRepresentableFamily.Over.{max u v} U)
    [𝒰.toPresieve.HasPairwisePullbacks] : Prop :=
  ∀ i j : 𝒰.index, J.QuasiCompactObject (Limits.pullback (𝒰.obj i).hom (𝒰.obj j).hom)

/-- Every covering family of `U` is refined by a finite covering family whose pairwise fiber
products exist and are quasi-compact. This is the family-based strengthening of
`HasFiniteRefinementProperty` appearing in Lemma 7.17.7 (4), stated without a global pullback
hypothesis on `C`. -/
class HasCofinalFiniteQuasiCompactOverlapCoverings
    (J : GrothendieckTopology C) (U : C) : Prop where
  finite_refinement
    (𝒰 : SemiRepresentableFamily.Over.{max u v} U)
    (h𝒰 : 𝒰.toSieve ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U) (_ : Finite 𝒱.index)
      (_ : 𝒱 ⟶ 𝒰) (_ : 𝒱.toPresieve.HasPairwisePullbacks),
      𝒱.toSieve ∈ J U ∧ HasQuasiCompactPairwiseOverlaps J 𝒱

/-- Forgetting the overlap data recovers the existing finite-refinement owner abstraction. -/
theorem HasCofinalFiniteQuasiCompactOverlapCoverings.hasFiniteRefinementProperty
    (hU : HasCofinalFiniteQuasiCompactOverlapCoverings J U) :
    HasFiniteRefinementProperty J U := by
  refine
    { finite_refinement := fun R hR ↦ by
        let 𝒰 : SemiRepresentableFamily.Over.{max u v} U :=
          ofArrows
            (fun i : R.uncurry ↦ i.1.1)
            (fun i ↦ i.1.2)
        have h𝒰toPresieve : 𝒰.toPresieve = R := by
          simpa [𝒰, toPresieve, ofArrows] using presieve_of_uncurry_eq R
        have h𝒰 : 𝒰.toSieve ∈ J U := by
          rw [toSieve, h𝒰toPresieve]
          exact hR
        obtain ⟨𝒱, h𝒱fin, φ, _, h𝒱, _⟩ := hU.finite_refinement 𝒰 h𝒰
        refine ⟨𝒱, h𝒱fin, h𝒱, ?_⟩
        simpa [toSieve, h𝒰toPresieve] using toSieve_le_of_hom φ }

/-- In particular, the overlap hypothesis implies quasi-compactness of `U`. -/
theorem HasCofinalFiniteQuasiCompactOverlapCoverings.quasiCompactObject
    (hU : HasCofinalFiniteQuasiCompactOverlapCoverings J U) :
    J.QuasiCompactObject U :=
  hasFiniteRefinementProperty_implies_quasiCompactObject hU.hasFiniteRefinementProperty

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory
open CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v z))]
variable {I : Type w} [Category I] [Small.{max u v z} I]
variable [IsFiltered I]

/-- Helper for Lemma 7.17.7: evaluating the presheaf colimit of a filtered diagram of sheaves at
`U` gives a colimit cocone on the evaluated stage sections. -/
private def presheafColimitEvaluationIsColimit
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C) :
    IsColimit
      (((evaluation Cᵒᵖ (Type (max u v z))).obj (op U)).mapCocone
        (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v z))))) :=
  isColimitOfPreserves _ (colimit.isColimit _)

/-- Helper for Lemma 7.17.7: two sections coming from the same stage of the filtered diagram
become equal in the evaluated presheaf colimit exactly when they agree after one later
transition. -/
private theorem presheafColimit_same_stage_eq_iff_eventually_equal
    (F : I ⥤ Sheaf J (Type (max u v z))) (i : I) (U : C)
    (x y : (F.obj i).1.obj (op U)) :
    ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op U)) x =
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op U)) y ↔
        ∃ (j : I) (f : i ⟶ j), ((F.map f).hom.app (op U)) x = ((F.map f).hom.app (op U)) y := by
  -- Evaluate the colimit cocone at `U` and use the filtered-colimit equality criterion in `Type`.
  simpa using
    (Types.FilteredColimit.isColimit_eq_iff'
      (presheafColimitEvaluationIsColimit (J := J) F U) x y)

/-- Helper for Lemma 7.17.7: a finite family of objects in a filtered category admits a common
upper bound. -/
private theorem finite_common_upper_bound {α : Type*} (s : Finset α) (X : α → I) :
    ∃ j : I, ∀ a ∈ s, Nonempty (X a ⟶ j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · obtain ⟨j⟩ := IsFiltered.nonempty (C := I)
    exact ⟨j, by simp⟩
  · intro a s ha hs
    obtain ⟨j, hj⟩ := hs
    refine ⟨IsFiltered.max (X a) j, ?_⟩
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb'
    · exact ⟨IsFiltered.leftToMax (X b) j⟩
    · rcases hj b hb' with ⟨f⟩
      exact ⟨f ≫ IsFiltered.rightToMax (X a) j⟩

/-- Helper for Lemma 7.17.7: finitely many morphisms with common source in a filtered category can
be equalized after passing to one later target. -/
private theorem common_target_of_finite_maps_from
    {i : I} {α : Type*} (s : Finset α) (j : α → I)
    (f : ∀ a : α, ∀ ha : a ∈ s, i ⟶ j a) :
    ∃ k : I, ∃ g : i ⟶ k, ∀ a (ha : a ∈ s), ∃ h : j a ⟶ k, f a ha ≫ h = g := by
  classical
  revert f
  refine Finset.induction_on s ?_ ?_
  · intro f
    refine ⟨i, 𝟙 i, ?_⟩
    intro a ha
    exact False.elim (Finset.notMem_empty a ha)
  · intro a s ha hs f
    obtain ⟨k, g, hg⟩ := hs (fun b hb ↦ f b (Finset.mem_insert_of_mem hb))
    let m := IsFiltered.max (j a) k
    let fa : i ⟶ m := f a (Finset.mem_insert_self a s) ≫ IsFiltered.leftToMax (j a) k
    let fg : i ⟶ m := g ≫ IsFiltered.rightToMax (j a) k
    refine ⟨IsFiltered.coeq fa fg, fa ≫ IsFiltered.coeqHom fa fg, ?_⟩
    intro b hb
    by_cases hba : b = a
    · subst b
      refine ⟨IsFiltered.leftToMax (j a) k ≫ IsFiltered.coeqHom fa fg, ?_⟩
      simp [fa, Category.assoc]
    · have hb' : b ∈ s := (Finset.mem_insert.mp hb).resolve_left hba
      obtain ⟨hbk, hhbk⟩ := hg b hb'
      refine ⟨hbk ≫ IsFiltered.rightToMax (j a) k ≫ IsFiltered.coeqHom fa fg, ?_⟩
      calc
        f b (Finset.mem_insert_of_mem hb') ≫
            (hbk ≫ IsFiltered.rightToMax (j a) k ≫ IsFiltered.coeqHom fa fg)
            = (f b (Finset.mem_insert_of_mem hb') ≫ hbk) ≫
                IsFiltered.rightToMax (j a) k ≫ IsFiltered.coeqHom fa fg := by
                  simp [Category.assoc]
        _ = g ≫ IsFiltered.rightToMax (j a) k ≫ IsFiltered.coeqHom fa fg := by
              simp [hhbk]
        _ = fa ≫ IsFiltered.coeqHom fa fg := by
              simpa [fa, fg] using (IsFiltered.coeq_condition fa fg).symm

section

variable {I' : Type w} [Category I'] [IsFiltered I']

/-- Helper for Lemma 7.17.7: a universe-stable copy of the finite common-target lemma, used for
the attached-finset synchronization step in clause (2). -/
private theorem common_target_of_finite_maps_from_aux
    {i : I'} {α : Type*} (s : Finset α) (j : α → I')
    (f : ∀ a : α, ∀ ha : a ∈ s, i ⟶ j a) :
    ∃ k : I', ∃ g : i ⟶ k, ∀ a (ha : a ∈ s), ∃ h : j a ⟶ k, f a ha ≫ h = g := by
  classical
  revert f
  refine Finset.induction_on s ?_ ?_
  · intro f
    refine ⟨i, 𝟙 i, ?_⟩
    intro a ha
    exact False.elim (Finset.notMem_empty a ha)
  · intro a s ha hs f
    obtain ⟨k, g, hg⟩ := hs (fun b hb ↦ f b (Finset.mem_insert_of_mem hb))
    let m := IsFiltered.max (j a) k
    let fa : i ⟶ m := f a (Finset.mem_insert_self a s) ≫ IsFiltered.leftToMax (j a) k
    let fg : i ⟶ m := g ≫ IsFiltered.rightToMax (j a) k
    refine ⟨IsFiltered.coeq fa fg, fa ≫ IsFiltered.coeqHom fa fg, ?_⟩
    intro b hb
    by_cases hba : b = a
    · subst b
      refine ⟨IsFiltered.leftToMax (j a) k ≫ IsFiltered.coeqHom fa fg, ?_⟩
      simp [fa, Category.assoc]
    · have hb' : b ∈ s := (Finset.mem_insert.mp hb).resolve_left hba
      obtain ⟨hbk, hhbk⟩ := hg b hb'
      refine ⟨hbk ≫ IsFiltered.rightToMax (j a) k ≫ IsFiltered.coeqHom fa fg, ?_⟩
      calc
        f b (Finset.mem_insert_of_mem hb') ≫
            (hbk ≫ IsFiltered.rightToMax (j a) k ≫ IsFiltered.coeqHom fa fg)
            = (f b (Finset.mem_insert_of_mem hb') ≫ hbk) ≫
                IsFiltered.rightToMax (j a) k ≫ IsFiltered.coeqHom fa fg := by
                  simp [Category.assoc]
        _ = g ≫ IsFiltered.rightToMax (j a) k ≫ IsFiltered.coeqHom fa fg := by
              simp [hhbk]
        _ = fa ≫ IsFiltered.coeqHom fa fg := by
              simpa [fa, fg] using (IsFiltered.coeq_condition fa fg).symm

end

/-- Helper for Lemma 7.17.7: restricting a section after a transition map agrees with first
restricting and then applying the transition map. -/
private theorem sheaf_transition_app_map_eq_map_app
    (F : I ⥤ Sheaf J (Type (max u v z))) {i j : I} (f : i ⟶ j)
    {U V : C} (g : V ⟶ U) (a : (F.obj i).1.obj (op U)) :
    ((F.map f).hom.app (op V)) (((F.obj i).1.map g.op) a) =
      ((F.obj j).1.map g.op) (((F.map f).hom.app (op U)) a) := by
  -- This is exactly the naturality square of the underlying presheaf map of `F.map f`.
  exact congrFun ((F.map f).hom.naturality g.op) a

/-- Helper for Lemma 7.17.7: the source colimit of sections over `U` is evaluation at `U` of the
underlying presheaf-colimit comparison map. -/
private theorem section_colimit_post_eq_eval
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C) :
    colimit.post F ((sheafSections J (Type (max u v z))).obj (op U)) =
      colimit.post (F ⋙ sheafToPresheaf J (Type (max u v z)))
          ((evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) ≫
        (colimit.post F (sheafToPresheaf J (Type (max u v z)))).app (op U) := by
  -- The sections functor is the composite of the forgetful functor with evaluation at `U`.
  simpa using
    (colimit.post_post F (sheafToPresheaf J (Type (max u v z)))
      ((evaluation Cᵒᵖ (Type (max u v z))).obj (op U))).symm

/-- Helper for Lemma 7.17.7: the comparison from the presheaf colimit to the underlying presheaf
of the sheaf colimit factors through the sheafification unit. -/
private theorem presheaf_colimit_comparison_factorization
    (F : I ⥤ Sheaf J (Type (max u v z))) :
    (CategoryTheory.toSheafify J
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v z))))) ≫
      (sheafToPresheaf J (Type (max u v z))).map
        ((colimit.isColimit F).coconePointUniqueUpToIso
          (Sheaf.isColimitSheafifyCocone
            (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v z))))
            (colimit.isColimit (F ⋙ sheafToPresheaf J (Type (max u v z)))))).inv =
      colimit.post F (sheafToPresheaf J (Type (max u v z))) := by
  -- Compare the two candidate maps after precomposing with each colimit injection.
  refine colimit.hom_ext ?_
  intro i
  have hleft :
      colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i ≫
          CategoryTheory.toSheafify J
            (colimit (F ⋙ sheafToPresheaf J (Type (max u v z)))) ≫
            (sheafToPresheaf J (Type (max u v z))).map
              ((colimit.isColimit F).coconePointUniqueUpToIso
                (Sheaf.isColimitSheafifyCocone
                  (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v z))))
                  (colimit.isColimit
                    (F ⋙ sheafToPresheaf J (Type (max u v z)))))).inv =
        (((Sheaf.sheafifyCocone (J := J) (D := Type (max u v z))
            (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v z))))).ι.app i).1 ≫
          (sheafToPresheaf J (Type (max u v z))).map
            ((colimit.isColimit F).coconePointUniqueUpToIso
              (Sheaf.isColimitSheafifyCocone
                (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v z))))
                (colimit.isColimit
                  (F ⋙ sheafToPresheaf J (Type (max u v z)))))).inv) := by
    -- The sheafified cocone injection is the presheaf-colimit injection followed by the unit.
    simpa [Category.assoc] using congrArg
      (fun f ↦ f ≫ (sheafToPresheaf J (Type (max u v z))).map
        ((colimit.isColimit F).coconePointUniqueUpToIso
          (Sheaf.isColimitSheafifyCocone
            (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v z))))
            (colimit.isColimit (F ⋙ sheafToPresheaf J (Type (max u v z)))))).inv)
      (Sheaf.sheafifyCocone_ι_app_val (J := J) (D := Type (max u v z))
        (E := colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v z)))) i).symm
  rw [hleft]
  have hmid :
      ((Sheaf.sheafifyCocone (J := J) (D := Type (max u v z))
          (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v z))))).ι.app i).1 ≫
        (sheafToPresheaf J (Type (max u v z))).map
          ((colimit.isColimit F).coconePointUniqueUpToIso
            (Sheaf.isColimitSheafifyCocone
              (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v z))))
              (colimit.isColimit (F ⋙ sheafToPresheaf J (Type (max u v z)))))).inv =
      (colimit.ι F i).1 := by
    -- The chosen colimit isomorphism identifies the sheafified cocone with the actual colimit.
    simpa using
      congrArg (fun f ↦ f.1)
        ((colimit.isColimit F).comp_coconePointUniqueUpToIso_inv
          (Sheaf.isColimitSheafifyCocone
            (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v z))))
            (colimit.isColimit (F ⋙ sheafToPresheaf J (Type (max u v z))))) i)
  rw [hmid]
  exact (colimit.ι_post F (sheafToPresheaf J (Type (max u v z))) i).symm

/-- Helper for Lemma 7.17.7: if all transition morphisms are monomorphisms, then the underlying
presheaf colimit is separated. -/
private theorem presheafColimit_isSeparated_of_transitionMonomorphisms
    (F : I ⥤ Sheaf J (Type (max u v z)))
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)) :
    Presieve.IsSeparated J (colimit (F ⋙ sheafToPresheaf J (Type (max u v z)))) := by
  let G : I ⥤ Cᵒᵖ ⥤ Type (max u v z) := F ⋙ sheafToPresheaf J (Type (max u v z))
  intro U S hS _ t₁ t₂ ht₁ ht₂
  let eU := colimitObjIsoColimitCompEvaluation G (op U)
  -- First move the two candidate colimit sections to one common stage over `U`.
  obtain ⟨i, a, b, ha, hb⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (colimit.isColimit (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)))
      (eU.hom t₁) (eU.hom t₂)
  have hιa :
      eU.inv
          (colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) i a) =
        ((colimit.ι G i).app (op U)) a := by
    -- The evaluation comparison identifies the chosen pointwise representative with the colimit
    -- leg of the underlying presheaf diagram.
    simpa [eU] using congrFun (colimitObjIsoColimitCompEvaluation_ι_inv G i (op U)) a
  have hιb :
      eU.inv
          (colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) i b) =
        ((colimit.ι G i).app (op U)) b := by
    -- The same comparison identifies the second representative.
    simpa [eU] using congrFun (colimitObjIsoColimitCompEvaluation_ι_inv G i (op U)) b
  have ht₁' :
      t₁ =
        eU.inv
          (colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) i a) := by
    -- Rewrite the first colimit section using the chosen stage representative.
    simpa [eU] using congrArg eU.inv ha.symm
  have ht₂' :
      t₂ =
        eU.inv
          (colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) i b) := by
    -- Rewrite the second colimit section using the chosen stage representative.
    simpa [eU] using congrArg eU.inv hb.symm
  have ht₁rep : ((colimit.ι G i).app (op U)) a = t₁ := hιa.symm.trans ht₁'.symm
  have ht₂rep : ((colimit.ι G i).app (op U)) b = t₂ := hιb.symm.trans ht₂'.symm
  have hsep_i : Presieve.IsSeparatedFor ((F.obj i).1) S.arrows := by
    exact ((isSheaf_iff_isSheaf_of_type J ((F.obj i).1)).1 (F.obj i).2).isSeparated S hS
  have hab : a = b := by
    -- Local equality in the colimit presheaf reduces to local equality in the common source stage.
    apply hsep_i.ext
    intro V f hf
    have hlocal_target : (colimit G).map f.op t₁ = (colimit G).map f.op t₂ :=
      (ht₁ f hf).trans (ht₂ f hf).symm
    let eV := colimitObjIsoColimitCompEvaluation G (op V)
    have hleft :
        eV.hom ((colimit G).map f.op (((colimit.ι G i).app (op U)) a)) =
          colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op V)) i
            (((G.obj i).map f.op) a) := by
      -- Push the restriction map through the pointwise-colimit comparison.
      have hmap :
          eV.hom ((colimit G).map f.op (((colimit.ι G i).app (op U)) a)) =
            colimMap (G.whiskerLeft ((evaluation Cᵒᵖ (Type (max u v z))).map f.op))
              (eU.hom (((colimit.ι G i).app (op U)) a)) := by
        simpa [eV, eU] using
          congrArg (fun g ↦ g (((colimit.ι G i).app (op U)) a))
            (colimit_map_colimitObjIsoColimitCompEvaluation_hom G f.op)
      rw [hmap]
      have hUrep :
          eU.hom (((colimit.ι G i).app (op U)) a) =
            colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) i a := by
        exact congrFun (colimitObjIsoColimitCompEvaluation_ι_app_hom G i (op U)) a
      rw [hUrep]
      exact congrFun
        (colimit.ι_map
          (G.whiskerLeft ((evaluation Cᵒᵖ (Type (max u v z))).map f.op)) i) a
    have hright :
        eV.hom ((colimit G).map f.op (((colimit.ι G i).app (op U)) b)) =
          colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op V)) i
            (((G.obj i).map f.op) b) := by
      -- The same computation applies to the second representative.
      have hmap :
          eV.hom ((colimit G).map f.op (((colimit.ι G i).app (op U)) b)) =
            colimMap (G.whiskerLeft ((evaluation Cᵒᵖ (Type (max u v z))).map f.op))
              (eU.hom (((colimit.ι G i).app (op U)) b)) := by
        simpa [eV, eU] using
          congrArg (fun g ↦ g (((colimit.ι G i).app (op U)) b))
            (colimit_map_colimitObjIsoColimitCompEvaluation_hom G f.op)
      rw [hmap]
      have hUrep :
          eU.hom (((colimit.ι G i).app (op U)) b) =
            colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) i b := by
        exact congrFun (colimitObjIsoColimitCompEvaluation_ι_app_hom G i (op U)) b
      rw [hUrep]
      exact congrFun
        (colimit.ι_map
          (G.whiskerLeft ((evaluation Cᵒᵖ (Type (max u v z))).map f.op)) i) b
    have hlocal_eval :
        colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op V)) i
            (((G.obj i).map f.op) a) =
          colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op V)) i
            (((G.obj i).map f.op) b) := by
      -- Move the local colimit equality to the pointwise filtered colimit over `V`.
      rw [← hleft, ← hright]
      have hlocal_target' :
          (colimit G).map f.op (((colimit.ι G i).app (op U)) a) =
            (colimit G).map f.op (((colimit.ι G i).app (op U)) b) := by
        simpa [ht₁rep, ht₂rep] using hlocal_target
      exact congrArg eV.hom hlocal_target'
    obtain ⟨k, g₁, g₂, hk⟩ :=
      (CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff
        (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op V))).1 hlocal_eval
    let h := IsFiltered.coeqHom g₁ g₂
    have hcomp := congrArg
      (((G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op V))).map h) hk
    have hcoeq_app :
        ((F.map h).hom.app (op V)) (((F.map g₁).hom.app (op V)) (((G.obj i).map f.op) a)) =
          ((F.map h).hom.app (op V)) (((F.map g₂).hom.app (op V)) (((G.obj i).map f.op) a)) := by
      -- Equalize the two tail maps in the filtered diagram.
      have hcoeq := congrArg (fun z ↦ ((F.map z).hom.app (op V)))
        (IsFiltered.coeq_condition g₁ g₂)
      simpa [h, G, Functor.map_comp, Category.assoc] using
        congrFun hcoeq (((G.obj i).map f.op) a)
    have hEq :
        ((F.map h).hom.app (op V)) (((F.map g₂).hom.app (op V)) (((G.obj i).map f.op) a)) =
          ((F.map h).hom.app (op V)) (((F.map g₂).hom.app (op V)) (((G.obj i).map f.op) b)) := by
      exact hcoeq_app.symm.trans hcomp
    have hinj :
        Function.Injective (((F.map (g₂ ≫ h)).hom.app (op V))) :=
      by
        letI : Mono (F.map (g₂ ≫ h)) := hF (g₂ ≫ h)
        exact (mono_iff_injective (((F.map (g₂ ≫ h)).hom.app (op V)))).1 inferInstance
    have hEq' :
        ((F.map (g₂ ≫ h)).hom.app (op V)) (((G.obj i).map f.op) a) =
          ((F.map (g₂ ≫ h)).hom.app (op V)) (((G.obj i).map f.op) b) := by
      simpa [h, G, Functor.map_comp, Category.assoc] using hEq
    exact hinj hEq'
  -- Transport the stage equality back to the original colimit representatives.
  exact ht₁rep.symm.trans <| (congrArg ((colimit.ι G i).app (op U)) hab).trans ht₂rep

/-- Helper for Lemma 7.17.7: separatedness of the presheaf colimit makes the sheafification unit
a monomorphism. -/
private theorem toSheafify_mono_of_presheafColimit_isSeparated
    (F : I ⥤ Sheaf J (Type (max u v z)))
    (hsep : Presieve.IsSeparated J (colimit (F ⋙ sheafToPresheaf J (Type (max u v z))))) :
    Mono (CategoryTheory.toSheafify J (colimit (F ⋙ sheafToPresheaf J (Type (max u v z))))) := by
  let P : Cᵒᵖ ⥤ Type (max u v z) := colimit (F ⋙ sheafToPresheaf J (Type (max u v z)))
  let e := plusPlusIsoSheafify J (Type (max u v z)) P
  have h_toPlus_inj :
      ∀ U : C, Function.Injective ((GrothendieckTopology.toPlus (J := J) P).app (op U)) := by
    -- Convert separatedness into the objectwise injectivity theorem owned by the plus
    -- construction.
    intro U
    exact CategoryTheory.GrothendieckTopology.Plus.inj_of_sep (J := J) (P := P)
      (fun V S x y hxy => by
        refine (hsep S.1 S.2).ext ?_
        intro Y f hf
        exact hxy ⟨Y, f, hf⟩) U
  have hsheaf_plus : Presheaf.IsSheaf J (GrothendieckTopology.plusObj (J := J) P) := by
    -- The first plus object is already a sheaf for a separated presheaf.
    exact CategoryTheory.GrothendieckTopology.Plus.isSheaf_of_sep (J := J) (P := P)
      (fun V S x y hxy => by
        refine (hsep S.1 S.2).ext ?_
        intro Y f hf
        exact hxy ⟨Y, f, hf⟩)
  have h_concrete : Mono (GrothendieckTopology.toSheafify (J := J) P) := by
    -- Separatedness makes the first `toPlus` injective, and the second one is an isomorphism.
    refine
      (CategoryTheory.Presheaf.mono_iff_injective
        (φ := GrothendieckTopology.toSheafify (J := J) P)).2 ?_
    rw [GrothendieckTopology.toSheafify, GrothendieckTopology.plusMap_toPlus]
    intro U s t hst
    letI :
        IsIso
          (GrothendieckTopology.toPlus (J := J)
            (GrothendieckTopology.plusObj (J := J) P)) :=
      GrothendieckTopology.isIso_toPlus_of_isSheaf (J := J)
        (P := GrothendieckTopology.plusObj (J := J) P) hsheaf_plus
    have h_second_inj :
        Function.Injective
          ((GrothendieckTopology.toPlus (J := J)
            (GrothendieckTopology.plusObj (J := J) P)).app (op U)) := by
      exact ((CategoryTheory.isIso_iff_bijective _).1
        ((NatTrans.isIso_iff_isIso_app _).1 inferInstance (op U))).1
    exact h_toPlus_inj U (h_second_inj hst)
  have hfac :
      GrothendieckTopology.toSheafify (J := J) P =
        CategoryTheory.toSheafify J P ≫ e.inv := by
    -- Rewrite the concrete `P⁺⁺` unit through the canonical comparison with categorical
    -- sheafification.
    rw [CategoryTheory.Iso.eq_comp_inv]
    simpa [e] using
      (CategoryTheory.toSheafify_plusPlusIsoSheafify_hom
        (J := J) (D := Type (max u v z)) P)
  have hcomp : Mono (CategoryTheory.toSheafify J P ≫ e.inv) := by
    simpa [hfac] using h_concrete
  -- Cancel the comparison isomorphism on the right to recover monicity of `toSheafify`.
  exact (mono_comp_iff_of_mono (CategoryTheory.toSheafify J P) e.inv).1 hcomp

/-- Helper for Lemma 7.17.7: evaluating the presheaf-colimit comparison at `U` is exactly the
functor-category colimit comparison isomorphism with the source-project orientation used in the
Stacks proof. -/
private theorem presheafColimit_eval_post_eq_colimitObjIso_inv
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C) :
    colimit.post (F ⋙ sheafToPresheaf J (Type (max u v z)))
        ((evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) =
      (colimitObjIsoColimitCompEvaluation
        (F ⋙ sheafToPresheaf J (Type (max u v z))) (op U)).inv := by
  let G : I ⥤ Cᵒᵖ ⥤ Type (max u v z) := F ⋙ sheafToPresheaf J (Type (max u v z))
  let eU := colimitObjIsoColimitCompEvaluation G (op U)
  -- Compare the evaluation map and the functor-category comparison after precomposing
  -- with each pointwise colimit injection.
  refine colimit.hom_ext ?_
  intro i
  rw [colimit.ι_post]
  simpa [G, eU] using (colimitObjIsoColimitCompEvaluation_ι_inv G i (op U)).symm

/-- Helper for Lemma 7.17.7: after composing the comparison map with the chosen colimit-point
isomorphism, it is exactly the evaluation of `toSheafify` on the presheaf colimit. -/
private theorem colimit_post_eq_toSheafify_comparison_app
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C) :
    colimit.post F ((sheafSections J (Type (max u v z))).obj (op U)) ≫
        ((sheafToPresheaf J (Type (max u v z))).map
          ((colimit.isColimit F).coconePointUniqueUpToIso
            (Sheaf.isColimitSheafifyCocone
              (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v z))))
              (colimit.isColimit (F ⋙ sheafToPresheaf J (Type (max u v z)))))).hom).app
          (op U) =
      (colimitObjIsoColimitCompEvaluation
          (F ⋙ sheafToPresheaf J (Type (max u v z))) (op U)).inv ≫
        (CategoryTheory.toSheafify J
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v z))))).app (op U) := by
  let G : I ⥤ Cᵒᵖ ⥤ Type (max u v z) := F ⋙ sheafToPresheaf J (Type (max u v z))
  let e :
      colimit F ≅
        ((presheafToSheaf J (Type (max u v z))).obj (colimit G)) :=
    (colimit.isColimit F).coconePointUniqueUpToIso
      (Sheaf.isColimitSheafifyCocone
        (colimit.cocone G) (colimit.isColimit G))
  -- First rewrite the section comparison as evaluation of the presheaf comparison.
  rw [section_colimit_post_eq_eval]
  have hfactor :
      (CategoryTheory.toSheafify J (colimit G)).app (op U) ≫
          ((sheafToPresheaf J (Type (max u v z))).map e.inv).app (op U) =
        (colimit.post F (sheafToPresheaf J (Type (max u v z)))).app (op U) := by
    -- Evaluate the presheaf-colimit factorization at `U`.
    simpa [G, e] using
      congrArg (fun η => η.app (op U))
        (presheaf_colimit_comparison_factorization (J := J) F)
  have htransport :
      (colimit.post F (sheafToPresheaf J (Type (max u v z)))).app (op U) ≫
          ((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U) =
        (CategoryTheory.toSheafify J (colimit G)).app (op U) := by
    -- Cancel the chosen sheaf-colimit comparison isomorphism on the right.
    calc
      (colimit.post F (sheafToPresheaf J (Type (max u v z)))).app (op U) ≫
          ((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U) =
            ((CategoryTheory.toSheafify J (colimit G)).app (op U) ≫
                ((sheafToPresheaf J (Type (max u v z))).map e.inv).app (op U)) ≫
              ((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U) := by
            rw [hfactor]
      _ = (CategoryTheory.toSheafify J (colimit G)).app (op U) := by
            ext x
            simpa using
              congrFun
                (CategoryTheory.Iso.map_inv_hom_id_app e
                  (sheafToPresheaf J (Type (max u v z))) (op U))
                (((CategoryTheory.toSheafify J (colimit G)).app (op U)) x)
  -- Route correction: isolate the evaluated-colimit orientation first, then splice in the
  -- sheafification factorization.
  calc
    colimit.post (F ⋙ sheafToPresheaf J (Type (max u v z)))
          ((evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) ≫
        (colimit.post F (sheafToPresheaf J (Type (max u v z)))).app (op U) ≫
          ((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U) =
      colimit.post (F ⋙ sheafToPresheaf J (Type (max u v z)))
          ((evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) ≫
        (CategoryTheory.toSheafify J (colimit G)).app (op U) := by
            simpa [Category.assoc] using
              congrArg
                (fun η =>
                  colimit.post (F ⋙ sheafToPresheaf J (Type (max u v z)))
                    ((evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) ≫ η)
                htransport
    _ =
      (colimitObjIsoColimitCompEvaluation G (op U)).inv ≫
        (CategoryTheory.toSheafify J (colimit G)).app (op U) := by
            simpa [G] using
              congrArg
                (fun η =>
                  η ≫ (CategoryTheory.toSheafify J (colimit G)).app (op U))
                (presheafColimit_eval_post_eq_colimitObjIso_inv (J := J) F U)

/-- Helper for Lemma 7.17.7: an arrow in the equalizer sieve of two same-stage colimit sections
forces equality after restricting those sections along that arrow. -/
private theorem equalizerSieve_restrict_eq_of_same_stage_sections
    (F : I ⥤ Sheaf J (Type (max u v z))) {i : I}
    {U V : C} (g : V ⟶ U) {a b : (F.obj i).1.obj (op U)}
    (hg :
      Presheaf.equalizerSieve
        (F := colimit (F ⋙ sheafToPresheaf J (Type (max u v z))))
        (X := op U)
        (((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op U)) a)
        (((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op U)) b) g) :
    ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op V))
        (((F.obj i).1.map g.op) a) =
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op V))
        (((F.obj i).1.map g.op) b) := by
  let G : I ⥤ Cᵒᵖ ⥤ Type (max u v z) := F ⋙ sheafToPresheaf J (Type (max u v z))
  rw [Presheaf.equalizerSieve_apply] at hg
  -- Rewrite the two restricted same-stage sections through the colimit presheaf map and read the
  -- equalizer-sieve condition there.
  calc
    ((colimit.ι G i).app (op V)) (((F.obj i).1.map g.op) a) =
        (colimit G).map g.op (((colimit.ι G i).app (op U)) a) := by
          simpa using congrFun ((colimit.ι G i).naturality g.op) a
    _ = (colimit G).map g.op (((colimit.ι G i).app (op U)) b) := by
          simpa [G] using hg
    _ = ((colimit.ι G i).app (op V)) (((F.obj i).1.map g.op) b) := by
          simpa using (congrFun ((colimit.ι G i).naturality g.op) b).symm

/-- Helper for Lemma 7.17.7: an arrow in the equalizer sieve of two same-stage colimit sections
gives eventual equality of the corresponding restricted stage sections. -/
private theorem eventual_equality_of_equalizer_sieve_arrow
    (F : I ⥤ Sheaf J (Type (max u v z))) {i : I}
    {U V : C} (g : V ⟶ U) {a b : (F.obj i).1.obj (op U)}
    (hg :
      Presheaf.equalizerSieve
        (F := colimit (F ⋙ sheafToPresheaf J (Type (max u v z))))
        (X := op U)
        (((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op U)) a)
        (((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op U)) b) g) :
    ∃ (j : I) (f : i ⟶ j),
      ((F.map f).hom.app (op V)) (((F.obj i).1.map g.op) a) =
        ((F.map f).hom.app (op V)) (((F.obj i).1.map g.op) b) := by
  -- First identify the restricted colimit classes in the presheaf colimit over `V`.
  have hrestrict :
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op V))
          (((F.obj i).1.map g.op) a) =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op V))
          (((F.obj i).1.map g.op) b) :=
    equalizerSieve_restrict_eq_of_same_stage_sections (J := J) F g hg
  -- Then use the filtered-colimit criterion to move the equality to one later stage.
  exact
    (presheafColimit_same_stage_eq_iff_eventually_equal (J := J) F i V
      (((F.obj i).1.map g.op) a) (((F.obj i).1.map g.op) b)).1 hrestrict

/-- Helper for Lemma 7.17.7: equality after restricting to one covering family of arrows in a
sheaf stage already implies equality of the original global sections. -/
private theorem same_stage_eq_of_cover_local_equality
    (F : I ⥤ Sheaf J (Type (max u v z))) {k : I} {U : C}
    (𝒱 : SemiRepresentableFamily.Over U) (h𝒱 : 𝒱.toSieve ∈ J U)
    {x y : (F.obj k).1.obj (op U)}
    (hxy :
      ∀ v : 𝒱.index,
        ((F.obj k).1.map ((𝒱.obj v).hom).op) x =
          ((F.obj k).1.map ((𝒱.obj v).hom).op) y) :
    x = y := by
  let hFk : Presheaf.IsSheaf J ((F.obj k).1) := (F.obj k).2
  have hfun :
      (fun _ : PUnit ↦ x) = fun _ : PUnit ↦ y := by
    -- Separatedness of the stage sheaf identifies the two constant families on the cover.
    apply CategoryTheory.Presheaf.IsSheaf.hom_ext_ofArrows hFk
      (fun v : 𝒱.index ↦ (𝒱.obj v).hom)
    · simpa [SemiRepresentableFamily.Over.toSieve, SemiRepresentableFamily.Over.toPresieve] using
        h𝒱
    · intro v
      funext _
      exact hxy v
  exact congrFun hfun PUnit.unit

/-- Helper for Lemma 7.17.7: once local equality holds after one transition map, it still holds
after any further transition map. -/
private theorem pushforward_equal_of_eventual_equality
    (F : I ⥤ Sheaf J (Type (max u v z))) {U V : C}
    {i j k : I} (g : V ⟶ U) {a b : (F.obj i).1.obj (op U)}
    {f : i ⟶ j} (h : j ⟶ k)
    (heq :
      ((F.map f).hom.app (op V)) (((F.obj i).1.map g.op) a) =
        ((F.map f).hom.app (op V)) (((F.obj i).1.map g.op) b)) :
    ((F.map (f ≫ h)).hom.app (op V)) (((F.obj i).1.map g.op) a) =
      ((F.map (f ≫ h)).hom.app (op V)) (((F.obj i).1.map g.op) b) := by
  -- Applying the later transition map to both sides preserves the local equality.
  simpa [Functor.map_comp] using congrArg (((F.map h).hom.app (op V))) heq

/-- Helper for Lemma 7.17.7: synchronizing witnesses over `s.attach` removes the unstable
membership transport from the finite-image refinement step. -/
private theorem common_stage_equal_on_attached_subfamily
    (F : I ⥤ Sheaf J (Type (max u v z))) {U : C}
    (𝒰 : SemiRepresentableFamily.Over U) {i : I}
    {a b : (F.obj i).1.obj (op U)}
    (s : Finset 𝒰.index)
    (hw :
      ∀ u : ↥s, ∃ (j : I) (f : i ⟶ j),
        ((F.map f).hom.app (op ((𝒰.obj u.1).left)))
            (((F.obj i).1.map ((𝒰.obj u.1).hom).op) a) =
          ((F.map f).hom.app (op ((𝒰.obj u.1).left)))
            (((F.obj i).1.map ((𝒰.obj u.1).hom).op) b)) :
    ∃ (k : I) (g : i ⟶ k), ∀ u : ↥s,
      ((F.map g).hom.app (op ((𝒰.obj u.1).left)))
          (((F.obj i).1.map ((𝒰.obj u.1).hom).op) a) =
        ((F.map g).hom.app (op ((𝒰.obj u.1).left)))
          (((F.obj i).1.map ((𝒰.obj u.1).hom).op) b) := by
  classical
  let j : ↥s → I := fun u ↦ Classical.choose (hw u)
  let f : ∀ u : ↥s, i ⟶ j u := fun u ↦
    Classical.choose (Classical.choose_spec (hw u))
  have hf :
      ∀ u : ↥s,
        ((F.map (f u)).hom.app (op ((𝒰.obj u.1).left)))
            (((F.obj i).1.map ((𝒰.obj u.1).hom).op) a) =
          ((F.map (f u)).hom.app (op ((𝒰.obj u.1).left)))
            (((F.obj i).1.map ((𝒰.obj u.1).hom).op) b) := by
    intro u
    exact Classical.choose_spec (Classical.choose_spec (hw u))
  obtain ⟨k, g, hg⟩ :=
    common_target_of_finite_maps_from_aux (s := (Finset.univ : Finset ↥s)) j
      (fun u _ ↦ f u)
  refine ⟨k, g, ?_⟩
  intro u
  obtain ⟨h, hh⟩ := hg u (by simp)
  -- Push the chosen local equality to the common target stage returned by filteredness.
  have hpush :
      ((F.map (f u ≫ h)).hom.app (op ((𝒰.obj u.1).left)))
          (((F.obj i).1.map ((𝒰.obj u.1).hom).op) a) =
        ((F.map (f u ≫ h)).hom.app (op ((𝒰.obj u.1).left)))
          (((F.obj i).1.map ((𝒰.obj u.1).hom).op) b) := by
    exact
      pushforward_equal_of_eventual_equality (J := J) (F := F) ((𝒰.obj u.1).hom) h (hf u)
  simpa [hh] using hpush

/-- Helper for Lemma 7.17.7: finitely many local eventual-equality witnesses can be synchronized
to one common later stage. -/
private theorem common_stage_equal_on_finite_subfamily
    (F : I ⥤ Sheaf J (Type (max u v z))) {U : C}
    (𝒰 : SemiRepresentableFamily.Over U) {i : I}
    {a b : (F.obj i).1.obj (op U)}
    (s : Finset 𝒰.index)
    (hw :
      ∀ t : 𝒰.index, t ∈ s → ∃ (j : I) (f : i ⟶ j),
        ((F.map f).hom.app (op ((𝒰.obj t).left)))
            (((F.obj i).1.map ((𝒰.obj t).hom).op) a) =
          ((F.map f).hom.app (op ((𝒰.obj t).left)))
            (((F.obj i).1.map ((𝒰.obj t).hom).op) b)) :
    ∃ (k : I) (g : i ⟶ k), ∀ t : 𝒰.index, t ∈ s →
      ((F.map g).hom.app (op ((𝒰.obj t).left)))
          (((F.obj i).1.map ((𝒰.obj t).hom).op) a) =
        ((F.map g).hom.app (op ((𝒰.obj t).left)))
          (((F.obj i).1.map ((𝒰.obj t).hom).op) b) := by
  -- Route correction: package `t ∈ s` as an attached element so filteredness acts on a genuine
  -- finite type and the source proof's common-stage step becomes transport-stable.
  obtain ⟨k, g, hg⟩ :=
    common_stage_equal_on_attached_subfamily (J := J) (F := F) 𝒰 s
      (fun u ↦ hw u.1 u.2)
  refine ⟨k, g, ?_⟩
  intro t ht
  -- Unpack the attached-element synchronization back to the original finset statement.
  exact hg ⟨t, ht⟩

/-- Helper for Lemma 7.17.7: the refinement map in `Over U` rewrites restriction along a refined
arrow as restriction along its image arrow followed by the horizontal map. -/
private theorem restriction_comp_eq_of_over_hom
    (F : I ⥤ Sheaf J (Type (max u v z))) {U : C}
    {𝒱 𝒰 : SemiRepresentableFamily.Over U} (φ : 𝒱 ⟶ 𝒰)
    {i : I} (v : 𝒱.index) (x : (F.obj i).1.obj (op U)) :
    ((F.obj i).1.map ((φ.f v).left).op)
        (((F.obj i).1.map ((𝒰.obj (φ.α v)).hom).op) x) =
      ((F.obj i).1.map ((𝒱.obj v).hom).op) x := by
  -- The slice compatibility `Over.w (φ.f v)` is exactly the composition identity on arrows.
  have hcomp : (φ.f v).left ≫ (𝒰.obj (φ.α v)).hom = (𝒱.obj v).hom := by
    simpa using Over.w (φ.f v)
  have hmap := congrArg (fun f => (F.obj i).1.map f.op) hcomp
  -- Evaluating the induced presheaf map identity gives the restriction comparison.
  simpa [Functor.map_comp] using congrFun hmap x

/-- Helper for Lemma 7.17.7: equality on the finite image of a refinement map transports to
equality on every arrow of the refined covering family. -/
private theorem refinement_local_equality_of_image_local_equality
    (F : I ⥤ Sheaf J (Type (max u v z))) {U : C}
    {𝒱 𝒰 : SemiRepresentableFamily.Over U} (φ : 𝒱 ⟶ 𝒰)
    {i k : I} {a b : (F.obj i).1.obj (op U)} (g : i ⟶ k)
    (himg :
      ∀ v : 𝒱.index,
        ((F.map g).hom.app (op ((𝒰.obj (φ.α v)).left)))
            (((F.obj i).1.map ((𝒰.obj (φ.α v)).hom).op) a) =
          ((F.map g).hom.app (op ((𝒰.obj (φ.α v)).left)))
            (((F.obj i).1.map ((𝒰.obj (φ.α v)).hom).op) b)) :
    ∀ v : 𝒱.index,
      ((F.map g).hom.app (op ((𝒱.obj v).left)))
          (((F.obj i).1.map ((𝒱.obj v).hom).op) a) =
        ((F.map g).hom.app (op ((𝒱.obj v).left)))
          (((F.obj i).1.map ((𝒱.obj v).hom).op) b) := by
  intro v
  have hrestrict_a :
      ((F.map g).hom.app (op ((𝒱.obj v).left)))
          (((F.obj i).1.map ((𝒱.obj v).hom).op) a) =
        ((F.obj k).1.map ((φ.f v).left).op)
            (((F.map g).hom.app (op ((𝒰.obj (φ.α v)).left)))
                (((F.obj i).1.map ((𝒰.obj (φ.α v)).hom).op) a)) := by
    -- First rewrite the refined restriction through the image arrow and then move `g` across it.
    have h₁ :
        ((F.map g).hom.app (op ((𝒱.obj v).left)))
            (((F.obj i).1.map ((𝒱.obj v).hom).op) a) =
          ((F.obj k).1.map ((𝒱.obj v).hom).op) (((F.map g).hom.app (op U)) a) := by
      simpa using
        (sheaf_transition_app_map_eq_map_app (J := J) (F := F) g ((𝒱.obj v).hom) a)
    have h₂ :
        ((F.obj k).1.map ((𝒱.obj v).hom).op) (((F.map g).hom.app (op U)) a) =
          ((F.obj k).1.map ((φ.f v).left).op)
              (((F.obj k).1.map ((𝒰.obj (φ.α v)).hom).op) (((F.map g).hom.app (op U)) a)) := by
      simpa using
        (restriction_comp_eq_of_over_hom (J := J) (F := F) φ
          (i := k) v (((F.map g).hom.app (op U)) a)).symm
    have h₃ :
        ((F.obj k).1.map ((φ.f v).left).op)
            (((F.obj k).1.map ((𝒰.obj (φ.α v)).hom).op) (((F.map g).hom.app (op U)) a)) =
          ((F.obj k).1.map ((φ.f v).left).op)
              (((F.map g).hom.app (op ((𝒰.obj (φ.α v)).left)))
                  (((F.obj i).1.map ((𝒰.obj (φ.α v)).hom).op) a)) := by
      exact congrArg (((F.obj k).1.map ((φ.f v).left).op))
        (by
          simpa using
            (sheaf_transition_app_map_eq_map_app (J := J) (F := F) g
              ((𝒰.obj (φ.α v)).hom) a).symm)
    exact h₁.trans (h₂.trans h₃)
  have hrestrict_b :
      ((F.obj k).1.map ((φ.f v).left).op)
          (((F.map g).hom.app (op ((𝒰.obj (φ.α v)).left)))
              (((F.obj i).1.map ((𝒰.obj (φ.α v)).hom).op) b)) =
        ((F.map g).hom.app (op ((𝒱.obj v).left)))
            (((F.obj i).1.map ((𝒱.obj v).hom).op) b) := by
    -- The same transport computation applies to the second section.
    have h₁ :
        ((F.obj k).1.map ((φ.f v).left).op)
            (((F.map g).hom.app (op ((𝒰.obj (φ.α v)).left)))
                (((F.obj i).1.map ((𝒰.obj (φ.α v)).hom).op) b)) =
          ((F.obj k).1.map ((φ.f v).left).op)
              (((F.obj k).1.map ((𝒰.obj (φ.α v)).hom).op) (((F.map g).hom.app (op U)) b)) := by
      exact congrArg (((F.obj k).1.map ((φ.f v).left).op))
        (by
          simpa using
            (sheaf_transition_app_map_eq_map_app (J := J) (F := F) g
              ((𝒰.obj (φ.α v)).hom) b))
    have h₂ :
        ((F.obj k).1.map ((φ.f v).left).op)
            (((F.obj k).1.map ((𝒰.obj (φ.α v)).hom).op) (((F.map g).hom.app (op U)) b)) =
          ((F.obj k).1.map ((𝒱.obj v).hom).op) (((F.map g).hom.app (op U)) b) := by
      simpa using
        (restriction_comp_eq_of_over_hom (J := J) (F := F) φ
          (i := k) v (((F.map g).hom.app (op U)) b))
    have h₃ :
        ((F.obj k).1.map ((𝒱.obj v).hom).op) (((F.map g).hom.app (op U)) b) =
          ((F.map g).hom.app (op ((𝒱.obj v).left)))
              (((F.obj i).1.map ((𝒱.obj v).hom).op) b) := by
      simpa using
        (sheaf_transition_app_map_eq_map_app (J := J) (F := F) g ((𝒱.obj v).hom) b).symm
    exact h₁.trans (h₂.trans h₃)
  -- The transported image-arrow equality now closes the refined-arrow equality.
  exact hrestrict_a.trans <| (congrArg (((F.obj k).1.map ((φ.f v).left).op)) (himg v)).trans hrestrict_b

/-- Helper for Lemma 7.17.7: once two same-stage sections agree on a covering family after one
transition, they already define the same class in the presheaf colimit. -/
private theorem same_stage_eq_in_presheaf_colimit_of_refined_cover_local_equality
    (F : I ⥤ Sheaf J (Type (max u v z))) {U : C}
    (𝒱 : SemiRepresentableFamily.Over U) (h𝒱 : 𝒱.toSieve ∈ J U)
    {i k : I} {a b : (F.obj i).1.obj (op U)} (g : i ⟶ k)
    (hxy :
      ∀ v : 𝒱.index,
        ((F.map g).hom.app (op ((𝒱.obj v).left)))
            (((F.obj i).1.map ((𝒱.obj v).hom).op) a) =
          ((F.map g).hom.app (op ((𝒱.obj v).left)))
            (((F.obj i).1.map ((𝒱.obj v).hom).op) b)) :
    ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op U)) a =
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) i).app (op U)) b := by
  have hglobal :
      ((F.map g).hom.app (op U)) a = ((F.map g).hom.app (op U)) b := by
    -- Separatedness of the stage sheaf upgrades local equality on the cover to global equality.
    apply same_stage_eq_of_cover_local_equality (J := J) (F := F) 𝒱 h𝒱
    intro v
    have hrestrict_a :
        ((F.map g).hom.app (op ((𝒱.obj v).left)))
            (((F.obj i).1.map ((𝒱.obj v).hom).op) a) =
          ((F.obj k).1.map ((𝒱.obj v).hom).op) (((F.map g).hom.app (op U)) a) := by
      simpa using
        (sheaf_transition_app_map_eq_map_app (J := J) (F := F) g
          ((𝒱.obj v).hom) a)
    have hrestrict_b :
        ((F.map g).hom.app (op ((𝒱.obj v).left)))
            (((F.obj i).1.map ((𝒱.obj v).hom).op) b) =
          ((F.obj k).1.map ((𝒱.obj v).hom).op) (((F.map g).hom.app (op U)) b) := by
      simpa using
        (sheaf_transition_app_map_eq_map_app (J := J) (F := F) g
          ((𝒱.obj v).hom) b)
    exact hrestrict_a.symm.trans ((hxy v).trans hrestrict_b)
  -- Convert the synchronized same-stage equality back to equality in the filtered colimit.
  exact
    (presheafColimit_same_stage_eq_iff_eventually_equal (J := J) F i U a b).2
      ⟨k, g, hglobal⟩

/-- Helper for Lemma 7.17.7: the plus-construction unit is locally injective for large
set-valued presheaves as well. -/
private theorem toPlus_large_isLocallySurjective
    (P : Cᵒᵖ ⥤ Type (max u v z)) :
    Presheaf.IsLocallySurjective J (GrothendieckTopology.toPlus (J := J) P) where
  imageSieve_mem x := by
    -- As in the small-universe `Type` proof, every `P⁺`-section is represented by one matching
    -- family, and that family itself gives the covering image sieve.
    obtain ⟨S, x, rfl⟩ := GrothendieckTopology.Plus.exists_rep (J := J) (P := P) x
    refine J.superset_covering (fun Y f hf => ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [GrothendieckTopology.Plus.toPlus_eq_mk, GrothendieckTopology.Plus.res_mk_eq_mk_pullback,
      GrothendieckTopology.Plus.eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using x.2
      { fst.hf := hf
        snd.hf := S.1.downward_closed hf g
        r.g₁ := g
        r.g₂ := 𝟙 Z
        .. }

/-- Helper for Lemma 7.17.7: the categorical sheafification unit is locally surjective for large
set-valued presheaves. -/
private theorem toSheafify_large_isLocallySurjective
    (P : Cᵒᵖ ⥤ Type (max u v z)) :
    Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) := by
  let _ : J.HasSheafCompose (forget (Type (max u v z))) := by
    infer_instance
  let _ : J.PreservesSheafification (forget (Type (max u v z))) := by
    infer_instance
  let P' : Cᵒᵖ ⥤ Type (max u v z) := P ⋙ forget (Type (max u v z))
  let _ : Presheaf.IsLocallySurjective J (J.toPlus P') :=
    toPlus_large_isLocallySurjective (J := J) P'
  let _ : Presheaf.IsLocallySurjective J (J.toPlus (J.plusObj P')) :=
    toPlus_large_isLocallySurjective (J := J) (J.plusObj P')
  let _ : Presheaf.IsLocallySurjective J (J.toSheafify P') := by
    -- Rewrite the concrete sheafification unit as the composite of the two large `toPlus` maps.
    change Presheaf.IsLocallySurjective J (J.toPlus P' ≫ J.plusMap (J.toPlus P'))
    rw [GrothendieckTopology.plusMap_toPlus]
    infer_instance
  -- Transport the local surjectivity statement across the standard forget/sheafification
  -- comparison isomorphisms.
  rw [Presheaf.isLocallySurjective_iff_whisker_forget,
    ← sheafComposeIso_hom_fac, ← CategoryTheory.toSheafify_plusPlusIsoSheafify_hom]
  let _ : IsIso
      ((plusPlusIsoSheafify J (Type (max u v z)) P').hom) := by
    infer_instance
  let _ : IsIso
      ((sheafifyComposeIso J (forget (Type (max u v z))) P).hom) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.17.7: the plus-construction unit is locally injective for large
set-valued presheaves as well. -/
private theorem toPlus_large_isLocallyInjective
    (P : Cᵒᵖ ⥤ Type (max u v z)) :
    Presheaf.IsLocallyInjective J (GrothendieckTopology.toPlus (J := J) P) where
  equalizerSieve_mem {X} x y h := by
    -- Equality in `P⁺` means the chosen representatives agree after restricting along one cover.
    rw [GrothendieckTopology.Plus.toPlus_eq_mk, GrothendieckTopology.Plus.toPlus_eq_mk,
      GrothendieckTopology.Plus.eq_mk_iff_exists] at h
    obtain ⟨W, _, _, eq⟩ := h
    exact
      J.superset_covering
        (fun Y f hf => congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩)
        W.2

/-- Helper for Lemma 7.17.7: if `U` is quasi-compact, then the sheafification unit on the
presheaf colimit is injective at `U`. -/
private theorem injective_toSheafify_app_of_quasiCompactObject_presheafColimit
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C) (hU : J.QuasiCompactObject U) :
    Function.Injective
      ((CategoryTheory.toSheafify J
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v z))))).app (op U)) := by
  let G : I ⥤ Cᵒᵖ ⥤ Type (max u v z) := F ⋙ sheafToPresheaf J (Type (max u v z))
  let eU := colimitObjIsoColimitCompEvaluation G (op U)
  intro x y hxy
  -- First replace the two presheaf-colimit sections by representatives from one common stage.
  obtain ⟨i, a, b, ha, hb⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (colimit.isColimit (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)))
      (eU.hom x) (eU.hom y)
  have hιa :
      eU.inv
          (colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) i a) =
        ((colimit.ι G i).app (op U)) a := by
    -- The evaluation comparison identifies the chosen representative with the stage leg.
    simpa [eU] using congrFun (colimitObjIsoColimitCompEvaluation_ι_inv G i (op U)) a
  have hιb :
      eU.inv
          (colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) i b) =
        ((colimit.ι G i).app (op U)) b := by
    -- The same identification applies to the second representative.
    simpa [eU] using congrFun (colimitObjIsoColimitCompEvaluation_ι_inv G i (op U)) b
  have hxrep :
      ((colimit.ι G i).app (op U)) a = x := by
    -- Transport the first pointwise representative back to the presheaf colimit over `U`.
    have hx :
        x =
          eU.inv
            (colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) i a) := by
      simpa [eU] using congrArg eU.inv ha.symm
    exact hιa.symm.trans hx.symm
  have hyrep :
      ((colimit.ι G i).app (op U)) b = y := by
    -- Transport the second pointwise representative back to the presheaf colimit over `U`.
    have hy :
        y =
          eU.inv
            (colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op U)) i b) := by
      simpa [eU] using congrArg eU.inv hb.symm
    exact hιb.symm.trans hy.symm
  have hsame_image :
      ((CategoryTheory.toSheafify J (colimit G)).app (op U))
          (((colimit.ι G i).app (op U)) a) =
        ((CategoryTheory.toSheafify J (colimit G)).app (op U))
          (((colimit.ι G i).app (op U)) b) := by
    -- Equality in sheafification can now be read on two same-stage representatives.
    simpa [hxrep, hyrep] using hxy
  have hsame_concrete :
      ((GrothendieckTopology.toSheafify (J := J) (colimit G)).app (op U))
          (((colimit.ι G i).app (op U)) a) =
        ((GrothendieckTopology.toSheafify (J := J) (colimit G)).app (op U))
          (((colimit.ι G i).app (op U)) b) := by
    let e := plusPlusIsoSheafify J (Type (max u v z)) (colimit G)
    have hfac :
        GrothendieckTopology.toSheafify (J := J) (colimit G) =
          CategoryTheory.toSheafify J (colimit G) ≫ e.inv := by
      rw [CategoryTheory.Iso.eq_comp_inv]
      simpa [e] using
        (CategoryTheory.toSheafify_plusPlusIsoSheafify_hom
          (J := J) (D := Type (max u v z)) (colimit G))
    -- Transport the categorical sheafification equality to the concrete `P⁺⁺` model.
    simpa [hfac, Category.assoc] using
      congrArg ((e.inv.app (op U))) hsame_image
  let R : Sieve U :=
    Presheaf.equalizerSieve
      (F := colimit G)
      (X := op U)
      (((colimit.ι G i).app (op U)) a)
      (((colimit.ι G i).app (op U)) b)
  have hR : R ∈ J U := by
    -- Route correction: use local injectivity of `toSheafify` first, then refine the resulting
    -- equalizer sieve by quasi-compactness.
    let _ :
        Presheaf.IsLocallyInjective J
          (GrothendieckTopology.toPlus (J := J) (colimit G)) :=
      toPlus_large_isLocallyInjective (J := J) (colimit G)
    let _ :
        Presheaf.IsLocallyInjective J
          (GrothendieckTopology.toPlus (J := J)
            (GrothendieckTopology.plusObj (J := J) (colimit G))) :=
      toPlus_large_isLocallyInjective (J := J)
        (GrothendieckTopology.plusObj (J := J) (colimit G))
    have hsame_plus :
        (((GrothendieckTopology.toPlus (J := J) (colimit G)) ≫
            (GrothendieckTopology.toPlus (J := J)
              (GrothendieckTopology.plusObj (J := J) (colimit G)))).app (op U))
            (((colimit.ι G i).app (op U)) a) =
          (((GrothendieckTopology.toPlus (J := J) (colimit G)) ≫
              (GrothendieckTopology.toPlus (J := J)
                (GrothendieckTopology.plusObj (J := J) (colimit G)))).app (op U))
            (((colimit.ι G i).app (op U)) b) := by
      simpa [GrothendieckTopology.toSheafify, GrothendieckTopology.plusMap_toPlus] using
        hsame_concrete
    exact
      Presheaf.equalizerSieve_mem (J := J)
        ((GrothendieckTopology.toPlus (J := J) (colimit G)) ≫
          (GrothendieckTopology.toPlus (J := J)
            (GrothendieckTopology.plusObj (J := J) (colimit G))))
        (((colimit.ι G i).app (op U)) a)
        (((colimit.ι G i).app (op U)) b)
        hsame_plus
  let 𝒰eq : SemiRepresentableFamily.Over U :=
    SemiRepresentableFamily.Over.ofArrows
      (fun t : R.arrows.category ↦ t.obj.left)
      (fun t ↦ t.obj.hom)
  have h𝒰eq : 𝒰eq.toSieve ∈ J U := by
    -- Package the equalizer sieve as an explicit covering family so quasi-compactness can refine
    -- it to finite image.
    have h𝒰eq_eq : 𝒰eq.toSieve = R := by
      simpa [𝒰eq] using (Sieve.ofArrows_category R)
    exact h𝒰eq_eq.symm ▸ hR
  obtain ⟨𝒱, h𝒱, φ, hφfin⟩ := hU.finite_image_refinement_of_family 𝒰eq h𝒰eq
  classical
  have hstage :
      ∀ t : 𝒰eq.index, t ∈ Set.range φ.α → ∃ (j : I) (f : i ⟶ j),
        ((F.map f).hom.app (op ((𝒰eq.obj t).left)))
            (((F.obj i).1.map ((𝒰eq.obj t).hom).op) a) =
          ((F.map f).hom.app (op ((𝒰eq.obj t).left)))
            (((F.obj i).1.map ((𝒰eq.obj t).hom).op) b) := by
    intro t ht
    -- Every arrow in the finite image still lies in the equalizer sieve, so it gives one local
    -- eventual-equality witness.
    have ht_mem : R ((𝒰eq.obj t).hom) := by
      simpa [R, 𝒰eq, SemiRepresentableFamily.Over.ofArrows] using t.2
    exact
      eventual_equality_of_equalizer_sieve_arrow (J := J) (F := F)
        (i := i) (g := (𝒰eq.obj t).hom) (a := a) (b := b) ht_mem
  obtain ⟨k, g, hg⟩ :=
    common_stage_equal_on_finite_subfamily (J := J) (F := F) 𝒰eq
      (i := i) (a := a) (b := b) hφfin.toFinset
      (fun t ht ↦
        hstage t <| (Set.Finite.mem_toFinset (s := Set.range φ.α) (hs := hφfin)).1 ht)
  have hlocal :
      ∀ v : 𝒱.index,
        ((F.map g).hom.app (op ((𝒱.obj v).left)))
            (((F.obj i).1.map ((𝒱.obj v).hom).op) a) =
          ((F.map g).hom.app (op ((𝒱.obj v).left)))
            (((F.obj i).1.map ((𝒱.obj v).hom).op) b) := by
    -- Transport the synchronized image equalities to every member of the refined cover.
    exact
      refinement_local_equality_of_image_local_equality (J := J) (F := F) φ
        (a := a) (b := b) g
        (fun v ↦
          hg (φ.α v)
            ((Set.Finite.mem_toFinset (s := Set.range φ.α) (hs := hφfin)).2 ⟨v, rfl⟩))
  have hcolim :
      ((colimit.ι G i).app (op U)) a = ((colimit.ι G i).app (op U)) b := by
    -- Source clause (2): after synchronizing finitely many local witnesses, separatedness of one
    -- stage sheaf closes the argument and yields equality already in the presheaf colimit.
    simpa [G] using
      same_stage_eq_in_presheaf_colimit_of_refined_cover_local_equality
        (J := J) (F := F) 𝒱 h𝒱 (i := i) (a := a) (b := b) g hlocal
  exact hxrep.symm.trans (hcolim.trans hyrep)

/- Source/core/bridge triage for 7.17.7:
- source-facing owner: `HasCofinalFiniteQuasiCompactOverlapCoverings`
- core/canonical owners: `GrothendieckTopology.HasFiniteRefinementProperty`,
  `GrothendieckTopology.QuasiCompactObject`, and `Limits.colimit.post`
- bridge/view layer in this file: `HasQuasiCompactPairwiseOverlaps` records the source-facing
  overlap hypothesis using the canonical pairwise pullback object
- bridge/view role: the overlap-covering owner implies the finite-refinement and quasi-compactness
  owners, and the four theorem statements below record the Stacks-project consequences for the
  canonical comparison morphism `colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))`
  without introducing a parallel owner for that map
-/

-- Proof sketch: view the presheaf colimit as the underlying presheaf of a separated presheaf when
-- all transition morphisms are monomorphisms, identify the sheaf colimit with its sheafification,
-- and apply injectivity of the map to sheafification for separated presheaves.
/-- Lemma 7.17.7 (1): if all transition morphisms in the filtered diagram are injective, then for
every object `U` the canonical map
`\operatorname{colim}_i \mathcal F_i(U) \to (\operatorname{colim}_i \mathcal F_i)(U)` is
injective. -/
theorem sheafFilteredColimitSectionsComparison_injective_of_transitionMonomorphisms
    (F : I ⥤ Sheaf J (Type (max u v z)))
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)) (U : C) :
    Function.Injective
      (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))) := by
  let G : I ⥤ Cᵒᵖ ⥤ Type (max u v z) := F ⋙ sheafToPresheaf J (Type (max u v z))
  let e :
      colimit F ≅
        ((presheafToSheaf J (Type (max u v z))).obj (colimit G)) :=
    (colimit.isColimit F).coconePointUniqueUpToIso
      (Sheaf.isColimitSheafifyCocone
        (colimit.cocone G) (colimit.isColimit G))
  have hsep : Presieve.IsSeparated J (colimit G) := by
    -- Source clause (1): injective transitions make the presheaf colimit separated.
    simpa [G] using
      presheafColimit_isSeparated_of_transitionMonomorphisms (J := J) F hF
  have htoSheafify :
      Mono (CategoryTheory.toSheafify J (colimit G)) := by
    -- A separated presheaf injects into its sheafification.
    simpa [G] using
      toSheafify_mono_of_presheafColimit_isSeparated (J := J) F hsep
  have hinj_toSheafify :
      Function.Injective ((CategoryTheory.toSheafify J (colimit G)).app (op U)) :=
    (CategoryTheory.Presheaf.mono_iff_injective
      (φ := CategoryTheory.toSheafify J (colimit G))).1 htoSheafify U
  have hinj_eval :
      Function.Injective
        ((colimitObjIsoColimitCompEvaluation G (op U)).inv) := by
    exact ((CategoryTheory.isIso_iff_bijective _).1 inferInstance).1
  have hcomp_inj :
      Function.Injective
        ((colimitObjIsoColimitCompEvaluation G (op U)).inv ≫
          (CategoryTheory.toSheafify J (colimit G)).app (op U)) :=
    hinj_toSheafify.comp hinj_eval
  -- Rewrite the comparison through the presheaf-colimit evaluation and the sheafification unit.
  intro s t hst
  have hcompare :
      (((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U))
          (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U)) s) =
        (((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U))
          (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U)) t) :=
    congrArg (((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U)) hst
  have hcomp_eq :
      ((CategoryTheory.toSheafify J (colimit G)).app (op U))
          (((colimitObjIsoColimitCompEvaluation G (op U)).inv) s) =
        ((CategoryTheory.toSheafify J (colimit G)).app (op U))
          (((colimitObjIsoColimitCompEvaluation G (op U)).inv) t) := by
    have hs :
        (((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U))
            (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U)) s) =
          ((CategoryTheory.toSheafify J (colimit G)).app (op U))
            (((colimitObjIsoColimitCompEvaluation G (op U)).inv) s) := by
      simpa [G, e, Category.assoc] using
        congrArg (fun f => f s)
          (colimit_post_eq_toSheafify_comparison_app (J := J) F U)
    have ht :
        (((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U))
            (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U)) t) =
          ((CategoryTheory.toSheafify J (colimit G)).app (op U))
            (((colimitObjIsoColimitCompEvaluation G (op U)).inv) t) := by
      simpa [G, e, Category.assoc] using
        congrArg (fun f => f t)
          (colimit_post_eq_toSheafify_comparison_app (J := J) F U)
    exact hs.symm.trans (hcompare.trans ht)
  exact hcomp_inj hcomp_eq

-- Proof sketch: if two classes become equal in the sheaf colimit over `U`, then they agree
-- locally on some covering. Quasi-compactness lets one refine to finitely many pieces, choose one
-- common stage of the filtered diagram, and conclude equality already in the presheaf colimit.
/-- Lemma 7.17.7 (2): if `U` is quasi-compact, then the canonical map
`\operatorname{colim}_i \mathcal F_i(U) \to (\operatorname{colim}_i \mathcal F_i)(U)` is
injective. -/
theorem sheafFilteredColimitSectionsComparison_injective_of_quasiCompactObject
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C) (hU : J.QuasiCompactObject U) :
    Function.Injective
      (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))) := by
  let G : I ⥤ Cᵒᵖ ⥤ Type (max u v z) := F ⋙ sheafToPresheaf J (Type (max u v z))
  let e :
      colimit F ≅
        ((presheafToSheaf J (Type (max u v z))).obj (colimit G)) :=
    (colimit.isColimit F).coconePointUniqueUpToIso
      (Sheaf.isColimitSheafifyCocone
        (colimit.cocone G) (colimit.isColimit G))
  have hinj_toSheafify :
      Function.Injective ((CategoryTheory.toSheafify J (colimit G)).app (op U)) := by
    -- Source clause (2): once the quasi-compact equalizer-refinement argument is proved, the
    -- sheafification unit is injective on sections over `U`.
    simpa [G] using
      injective_toSheafify_app_of_quasiCompactObject_presheafColimit (J := J) F U hU
  have hinj_eval :
      Function.Injective
        ((colimitObjIsoColimitCompEvaluation G (op U)).inv) := by
    exact ((CategoryTheory.isIso_iff_bijective _).1 inferInstance).1
  have hcomp_inj :
      Function.Injective
        ((colimitObjIsoColimitCompEvaluation G (op U)).inv ≫
          (CategoryTheory.toSheafify J (colimit G)).app (op U)) :=
    hinj_toSheafify.comp hinj_eval
  intro s t hst
  have hcompare :
      (((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U))
          (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U)) s) =
        (((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U))
          (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U)) t) :=
    congrArg (((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U)) hst
  have hcomp_eq :
      ((CategoryTheory.toSheafify J (colimit G)).app (op U))
          (((colimitObjIsoColimitCompEvaluation G (op U)).inv) s) =
        ((CategoryTheory.toSheafify J (colimit G)).app (op U))
          (((colimitObjIsoColimitCompEvaluation G (op U)).inv) t) := by
    have hs :
        (((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U))
            (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U)) s) =
          ((CategoryTheory.toSheafify J (colimit G)).app (op U))
            (((colimitObjIsoColimitCompEvaluation G (op U)).inv) s) := by
      simpa [G, e, Category.assoc] using
        congrArg (fun f => f s)
          (colimit_post_eq_toSheafify_comparison_app (J := J) F U)
    have ht :
        (((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U))
            (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U)) t) =
          ((CategoryTheory.toSheafify J (colimit G)).app (op U))
            (((colimitObjIsoColimitCompEvaluation G (op U)).inv) t) := by
      simpa [G, e, Category.assoc] using
        congrArg (fun f => f t)
          (colimit_post_eq_toSheafify_comparison_app (J := J) F U)
    exact hs.symm.trans (hcompare.trans ht)
  -- Route correction: the comparison transport is already fixed, so clause (2) now reduces
  -- cleanly to injectivity of the evaluated sheafification unit.
  exact hcomp_inj hcomp_eq

/-- Helper for Lemma 7.17.7: a target section over a quasi-compact object admits finitely many
local representatives in concrete stages of the filtered diagram. -/
private theorem finite_local_representatives_of_comparison_target
    (F : I ⥤ Sheaf J (Type (max u v z))) {U : C} (hU : J.QuasiCompactObject U)
    (t : (colimit F).1.obj (op U)) :
    ∃ (𝒰 : SemiRepresentableFamily.Over.{max u v} U) (_ : 𝒰.toSieve ∈ J U)
      (_ : Finite 𝒰.index)
      (i : 𝒰.index → I) (s : ∀ u, (F.obj (i u)).1.obj (op ((𝒰.obj u).left))),
      ∀ u, ((colimit.ι F (i u)).1.app (op ((𝒰.obj u).left))) (s u) =
        ((colimit F).1.map ((𝒰.obj u).hom).op) t := by
  classical
  let G : I ⥤ Cᵒᵖ ⥤ Type (max u v z) := F ⋙ sheafToPresheaf J (Type (max u v z))
  let e :
      colimit F ≅
        ((presheafToSheaf J (Type (max u v z))).obj (colimit G)) :=
    (colimit.isColimit F).coconePointUniqueUpToIso
      (Sheaf.isColimitSheafifyCocone
        (colimit.cocone G) (colimit.isColimit G))
  let _ : J.HasSheafCompose (forget (Type (max u v z))) := by
    infer_instance
  let _ : J.PreservesSheafification (forget (Type (max u v z))) := by
    infer_instance
  let _ : Presheaf.IsLocallySurjective J
      (CategoryTheory.toSheafify J (colimit G)) := by
    exact toSheafify_large_isLocallySurjective (J := J) (P := colimit G)
  let z :
      ((presheafToSheaf J (Type (max u v z))).obj (colimit G)).1.obj (op U) :=
    (((sheafToPresheaf J (Type (max u v z))).map e.hom).app (op U)) t
  let S : J.Cover U :=
    ⟨Presheaf.imageSieve (CategoryTheory.toSheafify J (colimit G)) z,
      Presheaf.imageSieve_mem J (CategoryTheory.toSheafify J (colimit G)) z⟩
  obtain ⟨T, hT, hTcover⟩ := hU S
  let 𝒰 : SemiRepresentableFamily.Over.{max u v} U :=
    SemiRepresentableFamily.Over.ofArrows
      (fun I : T ↦ I.1.Y)
      (fun I ↦ I.1.f)
  have h𝒰 : 𝒰.toSieve ∈ J U := by
    simpa [𝒰, toSieve, toPresieve, SemiRepresentableFamily.Over.ofArrows] using hTcover
  let x : ∀ u : 𝒰.index, (colimit G).obj (op ((𝒰.obj u).left)) := fun u ↦
    Presheaf.localPreimage
      (CategoryTheory.toSheafify J (colimit G)) z (𝒰.obj u).hom
      (by
        simpa [S, z, 𝒰, SemiRepresentableFamily.Over.ofArrows] using u.1.hf)
  have hx :
      ∀ u : 𝒰.index,
        ((CategoryTheory.toSheafify J (colimit G)).app (op ((𝒰.obj u).left))) (x u) =
          (((sheafToPresheaf J (Type (max u v z))).map e.hom).app
            (op ((𝒰.obj u).left)))
            (((colimit F).1.map ((𝒰.obj u).hom).op) t) := by
    intro u
    -- Route correction: first isolate the local `toSheafify` preimage equation, then rewrite the
    -- restricted target section by naturality of the chosen colimit/sheafification comparison.
    have hlocal :
        ((CategoryTheory.toSheafify J (colimit G)).app (op ((𝒰.obj u).left))) (x u) =
          ((presheafToSheaf J (Type (max u v z))).obj (colimit G)).1.map
            ((𝒰.obj u).hom).op z := by
      simpa [x] using
        (Presheaf.app_localPreimage
          (CategoryTheory.toSheafify J (colimit G)) z (𝒰.obj u).hom
          (by
            simpa [S, z, 𝒰, SemiRepresentableFamily.Over.ofArrows] using u.1.hf))
    have hnat :
        ((presheafToSheaf J (Type (max u v z))).obj (colimit G)).1.map
            ((𝒰.obj u).hom).op z =
          (((sheafToPresheaf J (Type (max u v z))).map e.hom).app
            (op ((𝒰.obj u).left)))
            (((colimit F).1.map ((𝒰.obj u).hom).op) t) := by
      have hnat' :=
        congrFun
          (((sheafToPresheaf J (Type (max u v z))).map e.hom).naturality
            ((𝒰.obj u).hom).op)
          t
      simpa [z] using hnat'.symm
    exact hlocal.trans hnat
  have hrep :
      ∀ u : 𝒰.index,
        ∃ i : I, ∃ s : (F.obj i).1.obj (op ((𝒰.obj u).left)),
          ((colimit.ι G i).app (op ((𝒰.obj u).left))) s = x u := by
    intro u
    let eU := colimitObjIsoColimitCompEvaluation G (op ((𝒰.obj u).left))
    -- Represent each local presheaf-colimit section by a concrete section of one stage.
    obtain ⟨i, s, hs⟩ :=
      Types.jointly_surjective_of_isColimit
        (colimit.isColimit
          (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op ((𝒰.obj u).left))))
        (eU.hom (x u))
    refine ⟨i, s, ?_⟩
    have hs' := congrArg eU.inv hs
    have hrepr :
        eU.inv
            (colimit.ι
              (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op ((𝒰.obj u).left))) i s) =
          ((colimit.ι G i).app (op ((𝒰.obj u).left))) s := by
      simpa [eU] using
        congrFun
          (colimitObjIsoColimitCompEvaluation_ι_inv G i
            (op ((𝒰.obj u).left))) s
    have hx_eq :
        x u =
          ((colimit.ι G i).app (op ((𝒰.obj u).left))) s := by
      have hx_eq' :
          x u =
            eU.inv
              (colimit.ι
                (G ⋙ (evaluation Cᵒᵖ (Type (max u v z))).obj (op ((𝒰.obj u).left))) i s) := by
        simpa [eU] using hs'.symm
      exact hx_eq'.trans hrepr
    exact hx_eq.symm
  choose i s hs using hrep
  have h𝒰fin : Finite 𝒰.index := by
    letI := hT.fintype
    change Finite T
    exact Finite.of_fintype T
  refine ⟨𝒰, h𝒰, ?_, i, s, ?_⟩
  · exact h𝒰fin
  · intro u
    let c :
        colimit (F ⋙ (sheafSections J (Type (max u v z))).obj (op ((𝒰.obj u).left))) :=
      colimit.ι (F ⋙ (sheafSections J (Type (max u v z))).obj
        (op ((𝒰.obj u).left))) (i u) (s u)
    have hbase :=
      congrArg
        (fun f ↦ f c)
        (colimit_post_eq_toSheafify_comparison_app (J := J) F ((𝒰.obj u).left))
    have hleft :
        (colimit.post F ((sheafSections J (Type (max u v z))).obj (op ((𝒰.obj u).left))) ≫
            ((sheafToPresheaf J (Type (max u v z))).map e.hom).app
              (op ((𝒰.obj u).left))) c =
          (((sheafToPresheaf J (Type (max u v z))).map e.hom).app
            (op ((𝒰.obj u).left)))
            (((colimit.ι F (i u)).1.app (op ((𝒰.obj u).left))) (s u)) := by
      have hι :=
        congrArg
          (fun f ↦
            (((sheafToPresheaf J (Type (max u v z))).map e.hom).app
              (op ((𝒰.obj u).left)))
              (f (s u)))
          (colimit.ι_post F ((sheafSections J (Type (max u v z))).obj (op ((𝒰.obj u).left)))
            (i u))
      simpa [c, Category.assoc] using hι
    have hright :
        ((colimitObjIsoColimitCompEvaluation G (op ((𝒰.obj u).left))).inv ≫
            (CategoryTheory.toSheafify J (colimit G)).app
              (op ((𝒰.obj u).left))) c =
          ((CategoryTheory.toSheafify J (colimit G)).app (op ((𝒰.obj u).left)))
            (((colimit.ι G (i u)).app (op ((𝒰.obj u).left))) (s u)) := by
      have hι :
          (colimitObjIsoColimitCompEvaluation G (op ((𝒰.obj u).left))).inv c =
            ((colimit.ι G (i u)).app (op ((𝒰.obj u).left))) (s u) := by
        simpa [c] using
          congrFun
            (colimitObjIsoColimitCompEvaluation_ι_inv G (i u)
              (op ((𝒰.obj u).left))) (s u)
      exact congrArg
        ((CategoryTheory.toSheafify J (colimit G)).app (op ((𝒰.obj u).left)))
        hι
    have hcompare :
        (((sheafToPresheaf J (Type (max u v z))).map e.hom).app
            (op ((𝒰.obj u).left)))
            (((colimit.ι F (i u)).1.app (op ((𝒰.obj u).left))) (s u)) =
          ((CategoryTheory.toSheafify J (colimit G)).app (op ((𝒰.obj u).left)))
            (((colimit.ι G (i u)).app (op ((𝒰.obj u).left))) (s u)) := by
      -- Evaluate the comparison formula on the source-colimit class represented by `s u`.
      exact hleft.symm.trans (hbase.trans hright)
    have htarget :
        (((sheafToPresheaf J (Type (max u v z))).map e.hom).app
            (op ((𝒰.obj u).left)))
            (((colimit.ι F (i u)).1.app (op ((𝒰.obj u).left))) (s u)) =
          (((sheafToPresheaf J (Type (max u v z))).map e.hom).app
            (op ((𝒰.obj u).left)))
            (((colimit F).1.map ((𝒰.obj u).hom).op) t) := by
      have hmid :
          ((CategoryTheory.toSheafify J (colimit G)).app (op ((𝒰.obj u).left)))
              (((colimit.ι G (i u)).app (op ((𝒰.obj u).left))) (s u)) =
            ((CategoryTheory.toSheafify J (colimit G)).app (op ((𝒰.obj u).left))) (x u) := by
        exact congrArg
          ((CategoryTheory.toSheafify J (colimit G)).app (op ((𝒰.obj u).left)))
          (hs u)
      exact hcompare.trans (hmid.trans (hx u))
    have hinj :
        Function.Injective
          (((sheafToPresheaf J (Type (max u v z))).map e.hom).app
            (op ((𝒰.obj u).left))) := by
      exact ((CategoryTheory.isIso_iff_bijective _).1 inferInstance).1
    exact hinj htarget

/-- Helper for Lemma 7.17.7: finitely many local stage representatives can be pushed to one common
later stage without changing the represented target section. -/
private theorem common_stage_of_finite_local_representatives
    (F : I ⥤ Sheaf J (Type (max u v z))) {U : C}
    (𝒰 : SemiRepresentableFamily.Over.{max u v} U) [Finite 𝒰.index]
    (i : 𝒰.index → I)
    (s : ∀ u, (F.obj (i u)).1.obj (op ((𝒰.obj u).left)))
    (t : (colimit F).1.obj (op U))
    (hs :
      ∀ u, ((colimit.ι F (i u)).1.app (op ((𝒰.obj u).left))) (s u) =
        ((colimit F).1.map ((𝒰.obj u).hom).op) t) :
    ∃ (k : I) (e : ∀ u, i u ⟶ k)
      (s' : ∀ u, (F.obj k).1.obj (op ((𝒰.obj u).left))),
      ∀ u, ((colimit.ι F k).1.app (op ((𝒰.obj u).left))) (s' u) =
        ((colimit F).1.map ((𝒰.obj u).hom).op) t := by
  classical
  letI : Fintype 𝒰.index := Fintype.ofFinite 𝒰.index
  let sFin : Finset 𝒰.index := Finset.univ
  have hbound :
      ∃ k : I, ∀ u ∈ sFin, Nonempty (i u ⟶ k) := by
    refine Finset.induction_on sFin ?_ ?_
    · obtain ⟨k⟩ := IsFiltered.nonempty (C := I)
      exact ⟨k, by simp⟩
    · intro a s ha hs
      obtain ⟨k, hk⟩ := hs
      refine ⟨IsFiltered.max (i a) k, ?_⟩
      intro b hb
      rcases Finset.mem_insert.1 hb with rfl | hb'
      · exact ⟨IsFiltered.leftToMax (i b) k⟩
      · rcases hk b hb' with ⟨f⟩
        exact ⟨f ≫ IsFiltered.rightToMax (i a) k⟩
  obtain ⟨k, hk⟩ := hbound
  let e : ∀ u, i u ⟶ k := fun u ↦ Classical.choice (hk u (by simp [sFin]))
  let s' : ∀ u, (F.obj k).1.obj (op ((𝒰.obj u).left)) := fun u ↦
    ((F.map (e u)).hom.app (op ((𝒰.obj u).left))) (s u)
  refine ⟨k, e, s', ?_⟩
  intro u
  -- Push the local representative to the chosen common stage and then use cocone compatibility.
  have hpush :
      ((colimit.ι F k).1.app (op ((𝒰.obj u).left))) (s' u) =
        ((colimit.ι F (i u)).1.app (op ((𝒰.obj u).left))) (s u) := by
    calc
      ((colimit.ι F k).1.app (op ((𝒰.obj u).left))) (s' u) =
          (((F.map (e u)) ≫ colimit.ι F k).1.app (op ((𝒰.obj u).left))) (s u) := by
            rfl
      _ = ((colimit.ι F (i u)).1.app (op ((𝒰.obj u).left))) (s u) := by
            simpa using
              congrArg
                (fun f ↦ f.1.app (op ((𝒰.obj u).left)) (s u))
                (colimit.w F (e u))
  -- The represented target section is unchanged after replacing the local stage by `k`.
  exact hpush.trans (hs u)

/-- Helper for Lemma 7.17.7: equality of two same-stage classes in the presheaf colimit already
forces equality of the underlying stage sections when all transition maps are monomorphisms. -/
private theorem same_stage_eq_of_presheaf_colimit_eq_of_transitionMonomorphisms
    (F : I ⥤ Sheaf J (Type (max u v z)))
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f))
    {k : I} {W : C} {x y : (F.obj k).1.obj (op W)}
    (hxy :
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) k).app (op W)) x =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) k).app (op W)) y) :
    x = y := by
  obtain ⟨j, f, hxyj⟩ :=
    (presheafColimit_same_stage_eq_iff_eventually_equal (J := J) F k W x y).1 hxy
  let _ : Mono (F.map f) := hF f
  have hmono : Mono ((F.map f).1) := by infer_instance
  have hinj :
      Function.Injective (((F.map f).1).app (op W)) :=
    (CategoryTheory.Presheaf.mono_iff_injective (φ := (F.map f).1)).1 hmono W
  exact hinj hxyj

/-- Helper for Lemma 7.17.7: once finitely many local representatives live in one common stage and
represent the same target section, clause (1) upgrades this to compatibility on all overlap
relations. -/
private theorem cover_relation_compatible_of_same_target_and_transitionMonomorphisms
    (F : I ⥤ Sheaf J (Type (max u v z)))
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f))
    {U : C} (𝒰 : SemiRepresentableFamily.Over.{max u v} U) {k : I}
    (t : (colimit F).1.obj (op U))
    (s : ∀ u, (F.obj k).1.obj (op ((𝒰.obj u).left)))
    (hs :
      ∀ u, ((colimit.ι F k).1.app (op ((𝒰.obj u).left))) (s u) =
        ((colimit F).1.map ((𝒰.obj u).hom).op) t) :
    ∀ ⦃W : C⦄ ⦃u v : 𝒰.index⦄ (a : W ⟶ (𝒰.obj u).left) (b : W ⟶ (𝒰.obj v).left),
      a ≫ (𝒰.obj u).hom = b ≫ (𝒰.obj v).hom →
        ((F.obj k).1.map a.op) (s u) = ((F.obj k).1.map b.op) (s v) := by
  intro W u v a b hab
  let x : (F.obj k).1.obj (op W) := ((F.obj k).1.map a.op) (s u)
  let y : (F.obj k).1.obj (op W) := ((F.obj k).1.map b.op) (s v)
  have hx_target :
      ((colimit.ι F k).1.app (op W)) x =
        ((colimit F).1.map (a ≫ (𝒰.obj u).hom).op) t := by
    -- Restrict the `u`-representative to `W` and rewrite it through the target section `t`.
    calc
      ((colimit.ι F k).1.app (op W)) x =
          ((colimit F).1.map a.op)
            (((colimit.ι F k).1.app (op ((𝒰.obj u).left))) (s u)) := by
              exact congrFun (((colimit.ι F k).1).naturality a.op) (s u)
      _ = ((colimit F).1.map a.op) (((colimit F).1.map ((𝒰.obj u).hom).op) t) := by
            rw [hs u]
      _ = ((colimit F).1.map (a ≫ (𝒰.obj u).hom).op) t := by
            simpa using
              (FunctorToTypes.map_comp_apply
                (F := (colimit F).1) ((𝒰.obj u).hom).op a.op t).symm
  have hy_target :
      ((colimit.ι F k).1.app (op W)) y =
        ((colimit F).1.map (b ≫ (𝒰.obj v).hom).op) t := by
    -- The same restriction rewrite holds for the `v`-representative.
    calc
      ((colimit.ι F k).1.app (op W)) y =
          ((colimit F).1.map b.op)
            (((colimit.ι F k).1.app (op ((𝒰.obj v).left))) (s v)) := by
              exact congrFun (((colimit.ι F k).1).naturality b.op) (s v)
      _ = ((colimit F).1.map b.op) (((colimit F).1.map ((𝒰.obj v).hom).op) t) := by
            rw [hs v]
      _ = ((colimit F).1.map (b ≫ (𝒰.obj v).hom).op) t := by
            simpa using
              (FunctorToTypes.map_comp_apply
                (F := (colimit F).1) ((𝒰.obj v).hom).op b.op t).symm
  have htarget :
      ((colimit.ι F k).1.app (op W)) x =
        ((colimit.ι F k).1.app (op W)) y := by
    -- The two target restrictions coincide because the arrows to `U` agree.
    calc
      ((colimit.ι F k).1.app (op W)) x =
          ((colimit F).1.map (a ≫ (𝒰.obj u).hom).op) t := hx_target
      _ = ((colimit F).1.map (b ≫ (𝒰.obj v).hom).op) t := by
            exact congrArg (fun f ↦ ((colimit F).1.map f.op) t) hab
      _ = ((colimit.ι F k).1.app (op W)) y := hy_target.symm
  let sx :
      colimit ((F ⋙ (sheafSections J (Type (max u v z))).obj (op W))) :=
    colimit.ι (F ⋙ (sheafSections J (Type (max u v z))).obj (op W)) k x
  let sy :
      colimit ((F ⋙ (sheafSections J (Type (max u v z))).obj (op W))) :=
    colimit.ι (F ⋙ (sheafSections J (Type (max u v z))).obj (op W)) k y
  have hsections : sx = sy := by
    -- Clause (1) over `W` turns equality in the sheaf colimit back into source-colimit equality.
    apply
      sheafFilteredColimitSectionsComparison_injective_of_transitionMonomorphisms
        (J := J) F hF W
    have hsx :
        colimit.post F ((sheafSections J (Type (max u v z))).obj (op W)) sx =
          ((colimit.ι F k).1.app (op W)) x := by
      -- Evaluate the source-colimit class represented by `x` in the sheaf colimit over `W`.
      dsimp [sx]
      simpa using
        congrArg
          (fun f ↦ f x)
          (colimit.ι_post F ((sheafSections J (Type (max u v z))).obj (op W)) k)
    have hsy :
        colimit.post F ((sheafSections J (Type (max u v z))).obj (op W)) sy =
          ((colimit.ι F k).1.app (op W)) y := by
      -- The same evaluation rewrite identifies the source-colimit class represented by `y`.
      dsimp [sy]
      simpa using
        congrArg
          (fun f ↦ f y)
          (colimit.ι_post F ((sheafSections J (Type (max u v z))).obj (op W)) k)
    exact hsx.trans (htarget.trans hsy.symm)
  have hpresheaf :
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) k).app (op W)) x =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) k).app (op W)) y := by
    -- Evaluate the source-colimit equality in the presheaf colimit over `W`.
    let ψ :
        colimit ((F ⋙ (sheafSections J (Type (max u v z))).obj (op W))) ⟶
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v z)))).obj (op W) :=
      colimit.post (F ⋙ sheafToPresheaf J (Type (max u v z)))
        ((evaluation Cᵒᵖ (Type (max u v z))).obj (op W))
    have hψ := congrArg ψ hsections
    have hψx :
        ψ sx =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) k).app (op W)) x := by
      -- Evaluating the source colimit in presheaves identifies `sx` with the usual stage class.
      dsimp [ψ, sx]
      simpa using
        congrArg
          (fun f ↦ f x)
          (colimit.ι_post (F ⋙ sheafToPresheaf J (Type (max u v z)))
            ((evaluation Cᵒᵖ (Type (max u v z))).obj (op W)) k)
    have hψy :
        ψ sy =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) k).app (op W)) y := by
      -- The same evaluation rewrite identifies `sy`.
      dsimp [ψ, sy]
      simpa using
        congrArg
          (fun f ↦ f y)
          (colimit.ι_post (F ⋙ sheafToPresheaf J (Type (max u v z)))
            ((evaluation Cᵒᵖ (Type (max u v z))).obj (op W)) k)
    exact hψx.symm.trans (hψ.trans hψy)
  -- The two restricted representatives already live in one stage, so same-stage injectivity
  -- identifies them once their presheaf-colimit classes agree.
  exact
    same_stage_eq_of_presheaf_colimit_eq_of_transitionMonomorphisms
      (J := J) (F := F) hF hpresheaf

-- Proof sketch: combine the injectivity from part (1) on overlaps with quasi-compactness of `U`
-- to choose finitely many local representatives in a common stage; these representatives then
-- glue in that stage sheaf, giving surjectivity, while part (2) gives injectivity.
/-- Lemma 7.17.7 (3): if `U` is quasi-compact and all transition morphisms in the filtered diagram
are injective, then the canonical map
`\operatorname{colim}_i \mathcal F_i(U) \to (\operatorname{colim}_i \mathcal F_i)(U)` is an
isomorphism. -/
theorem sheafFilteredColimitSectionsComparison_isIso_of_quasiCompactObject_of_transitionMonomorphisms
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C) (hU : J.QuasiCompactObject U)
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)) :
    IsIso (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))) := by
  classical
  rw [CategoryTheory.isIso_iff_bijective]
  refine ⟨?_, ?_⟩
  · exact
      sheafFilteredColimitSectionsComparison_injective_of_transitionMonomorphisms
        (J := J) F hF U
  · intro t
    obtain ⟨𝒰, h𝒰, h𝒰fin, i, s, hs⟩ :=
      finite_local_representatives_of_comparison_target (J := J) F hU t
    haveI : Finite 𝒰.index := h𝒰fin
    obtain ⟨k, e, s', hs'⟩ :=
      common_stage_of_finite_local_representatives (J := J) F 𝒰 i s t hs
    let hFk : Presheaf.IsSheaf J ((F.obj k).1) := (F.obj k).2
    have hcompat :
        ∀ ⦃W : C⦄ ⦃u v : 𝒰.index⦄ (a : W ⟶ (𝒰.obj u).left) (b : W ⟶ (𝒰.obj v).left),
          a ≫ (𝒰.obj u).hom = b ≫ (𝒰.obj v).hom →
            ((F.obj k).1.map a.op) (s' u) = ((F.obj k).1.map b.op) (s' v) :=
      cover_relation_compatible_of_same_target_and_transitionMonomorphisms
        (J := J) (F := F) hF 𝒰 t s' hs'
    let gluedHom : PUnit ⟶ (F.obj k).1.obj (op U) :=
      hFk.amalgamateOfArrows
        (f := fun u : 𝒰.index ↦ (𝒰.obj u).hom)
        (hf := h𝒰)
        (x := fun u _ ↦ s' u)
        (hx := by
          intro W u v a b hab
          funext _
          exact hcompat a b hab)
    let glued : (F.obj k).1.obj (op U) := gluedHom PUnit.unit
    have hglued_restrict :
        ∀ u : 𝒰.index, ((F.obj k).1.map ((𝒰.obj u).hom).op) glued = s' u := by
      intro u
      -- The glued stage section restricts to the prescribed local representative on each arrow.
      exact congrFun
        (hFk.amalgamateOfArrows_map
          (f := fun v : 𝒰.index ↦ (𝒰.obj v).hom)
          (hf := h𝒰)
          (x := fun v _ ↦ s' v)
          (hx := by
            intro W v w a b hab
            funext _
            exact hcompat a b hab)
          u)
        PUnit.unit
    have htarget :
        ((colimit.ι F k).1.app (op U)) glued = t := by
      let hColim : Presheaf.IsSheaf J ((colimit F).1) := (colimit F).2
      have hsections :
          (fun _ : PUnit ↦ ((colimit.ι F k).1.app (op U)) glued) = fun _ : PUnit ↦ t := by
        -- The glued image and `t` agree after restricting to every member of the cover `𝒰`.
        apply CategoryTheory.Presheaf.IsSheaf.hom_ext_ofArrows hColim
          (f := fun u : 𝒰.index ↦ (𝒰.obj u).hom)
          (hf := h𝒰)
        intro u
        funext _
        have hrestrict :
            ((colimit F).1.map ((𝒰.obj u).hom).op) (((colimit.ι F k).1.app (op U)) glued) =
              ((colimit.ι F k).1.app (op ((𝒰.obj u).left)))
                (((F.obj k).1.map ((𝒰.obj u).hom).op) glued) := by
          exact
            (congrFun
              (((colimit.ι F k).1).naturality ((𝒰.obj u).hom).op) glued).symm
        exact
          (hrestrict.trans <| by rw [hglued_restrict u]).trans (hs' u)
      exact congrFun hsections PUnit.unit
    refine ⟨colimit.ι (F ⋙ (sheafSections J (Type (max u v z))).obj (op U)) k glued, ?_⟩
    -- Evaluate the glued stage section in the source colimit and compare with `t`.
    have hsource :
        colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))
            (colimit.ι (F ⋙ (sheafSections J (Type (max u v z))).obj (op U)) k glued) =
          ((colimit.ι F k).1.app (op U)) glued := by
      simpa using
        congrArg
          (fun f ↦ f glued)
          (colimit.ι_post F ((sheafSections J (Type (max u v z))).obj (op U)) k)
    exact hsource.trans htarget

/-- Helper for Lemma 7.17.7: refine the finite local representative cover of a target section to
one with finite quasi-compact pairwise overlaps, transporting the local representatives along the
refinement. -/
private theorem finite_overlap_local_representatives_of_comparison_target
    (F : I ⥤ Sheaf J (Type (max u v z))) {U : C}
    (hU : HasCofinalFiniteQuasiCompactOverlapCoverings J U)
    (t : (colimit F).1.obj (op U)) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U) (_ : 𝒱.toSieve ∈ J U)
      (_ : Finite 𝒱.index) (_ : 𝒱.toPresieve.HasPairwisePullbacks)
      (_ : HasQuasiCompactPairwiseOverlaps J 𝒱)
      (i : 𝒱.index → I) (s : ∀ v, (F.obj (i v)).1.obj (op ((𝒱.obj v).left))),
      ∀ v, ((colimit.ι F (i v)).1.app (op ((𝒱.obj v).left))) (s v) =
        ((colimit F).1.map ((𝒱.obj v).hom).op) t := by
  classical
  obtain ⟨𝒰, h𝒰, h𝒰fin, i, s, hs⟩ :=
    finite_local_representatives_of_comparison_target (J := J) F hU.quasiCompactObject t
  obtain ⟨𝒱, h𝒱fin, φ, h𝒱pull, h𝒱, hqc⟩ := hU.finite_refinement 𝒰 h𝒰
  let i' : 𝒱.index → I := fun v ↦ i (φ.α v)
  let s' : ∀ v, (F.obj (i' v)).1.obj (op ((𝒱.obj v).left)) := fun v ↦
    ((F.obj (i' v)).1.map ((φ.f v).left).op) (s (φ.α v))
  refine ⟨𝒱, h𝒱, h𝒱fin, h𝒱pull, hqc, i', s', ?_⟩
  intro v
  -- Restrict the old local representative along the refinement arrow and rewrite through `t`.
  calc
    ((colimit.ι F (i' v)).1.app (op ((𝒱.obj v).left))) (s' v) =
        ((colimit F).1.map ((φ.f v).left).op)
          (((colimit.ι F (i' v)).1.app (op ((𝒰.obj (φ.α v)).left))) (s (φ.α v))) := by
            exact congrFun (((colimit.ι F (i' v)).1).naturality ((φ.f v).left).op) (s (φ.α v))
    _ =
        ((colimit F).1.map ((φ.f v).left).op)
          (((colimit F).1.map ((𝒰.obj (φ.α v)).hom).op) t) := by
            rw [hs (φ.α v)]
    _ = ((colimit F).1.map (((φ.f v).left ≫ (𝒰.obj (φ.α v)).hom)).op) t := by
          simpa using
            (FunctorToTypes.map_comp_apply
              (F := (colimit F).1) ((𝒰.obj (φ.α v)).hom).op ((φ.f v).left).op t).symm
    _ = ((colimit F).1.map ((𝒱.obj v).hom).op) t := by
          simpa [i'] using congrArg (fun f ↦ ((colimit F).1.map f.op) t) (Over.w (φ.f v))

/-- Helper for Lemma 7.17.7: after moving finitely many local representatives to one common stage,
quasi-compact pairwise overlaps force their restrictions to become compatible at one later stage. -/
private theorem common_stage_pullback_compatibility_of_same_target
    (F : I ⥤ Sheaf J (Type (max u v z))) {U : C}
    (𝒱 : SemiRepresentableFamily.Over.{max u v} U) [Finite 𝒱.index]
    [𝒱.toPresieve.HasPairwisePullbacks]
    (h𝒱qc : HasQuasiCompactPairwiseOverlaps J 𝒱)
    {k : I} (t : (colimit F).1.obj (op U))
    (s : ∀ u, (F.obj k).1.obj (op ((𝒱.obj u).left)))
    (hs :
      ∀ u, ((colimit.ι F k).1.app (op ((𝒱.obj u).left))) (s u) =
        ((colimit F).1.map ((𝒱.obj u).hom).op) t) :
    ∃ (ℓ : I) (g : k ⟶ ℓ),
      ∀ u v,
        ((F.obj ℓ).1.map (Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom).op)
            (((F.map g).hom.app (op ((𝒱.obj u).left))) (s u)) =
          ((F.obj ℓ).1.map (Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom).op)
            (((F.map g).hom.app (op ((𝒱.obj v).left))) (s v)) := by
  classical
  letI : Fintype 𝒱.index := Fintype.ofFinite 𝒱.index
  let pairs : Finset (𝒱.index × 𝒱.index) := Finset.univ
  have hw :
      ∀ p : 𝒱.index × 𝒱.index, ∃ (j : I) (f : k ⟶ j),
        ((F.map f).hom.app
            (op (Limits.pullback (𝒱.obj p.1).hom (𝒱.obj p.2).hom)))
            (((F.obj k).1.map (Limits.pullback.fst (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op)
              (s p.1)) =
          ((F.map f).hom.app
              (op (Limits.pullback (𝒱.obj p.1).hom (𝒱.obj p.2).hom)))
              (((F.obj k).1.map (Limits.pullback.snd (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op)
                (s p.2)) := by
    intro p
    let W := Limits.pullback (𝒱.obj p.1).hom (𝒱.obj p.2).hom
    let x : (F.obj k).1.obj (op W) :=
      ((F.obj k).1.map (Limits.pullback.fst (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op) (s p.1)
    let y : (F.obj k).1.obj (op W) :=
      ((F.obj k).1.map (Limits.pullback.snd (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op) (s p.2)
    let sx :
        colimit (F ⋙ (sheafSections J (Type (max u v z))).obj (op W)) :=
      colimit.ι (F ⋙ (sheafSections J (Type (max u v z))).obj (op W)) k x
    let sy :
        colimit (F ⋙ (sheafSections J (Type (max u v z))).obj (op W)) :=
      colimit.ι (F ⋙ (sheafSections J (Type (max u v z))).obj (op W)) k y
    have htarget :
        ((colimit.ι F k).1.app (op W)) x =
          ((colimit.ι F k).1.app (op W)) y := by
      -- Both restricted local representatives compute the same restriction of `t` to the
      -- canonical overlap object.
      calc
        ((colimit.ι F k).1.app (op W)) x =
            ((colimit F).1.map (Limits.pullback.fst (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op)
              (((colimit.ι F k).1.app (op ((𝒱.obj p.1).left))) (s p.1)) := by
                exact congrFun
                  (((colimit.ι F k).1).naturality
                    (Limits.pullback.fst (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op)
                  (s p.1)
        _ = ((colimit F).1.map (Limits.pullback.fst (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op)
              (((colimit F).1.map ((𝒱.obj p.1).hom).op) t) := by
              rw [hs p.1]
        _ = ((colimit F).1.map
              ((Limits.pullback.fst (𝒱.obj p.1).hom (𝒱.obj p.2).hom ≫ (𝒱.obj p.1).hom).op)) t := by
              simpa using
                (FunctorToTypes.map_comp_apply
                  (F := (colimit F).1) ((𝒱.obj p.1).hom).op
                    (Limits.pullback.fst (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op t).symm
        _ = ((colimit F).1.map
              ((Limits.pullback.snd (𝒱.obj p.1).hom (𝒱.obj p.2).hom ≫ (𝒱.obj p.2).hom).op)) t := by
              exact congrArg (fun f ↦ ((colimit F).1.map f.op) t)
                (Limits.pullback.condition
                  (f := (𝒱.obj p.1).hom) (g := (𝒱.obj p.2).hom))
        _ = ((colimit F).1.map (Limits.pullback.snd (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op)
              (((colimit F).1.map ((𝒱.obj p.2).hom).op) t) := by
              simpa using
                (FunctorToTypes.map_comp_apply
                  (F := (colimit F).1) ((𝒱.obj p.2).hom).op
                    (Limits.pullback.snd (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op t).symm
        _ = ((colimit F).1.map (Limits.pullback.snd (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op)
              (((colimit.ι F k).1.app (op ((𝒱.obj p.2).left))) (s p.2)) := by
              rw [hs p.2]
        _ = ((colimit.ι F k).1.app (op W)) y := by
              exact
                (congrFun
                  (((colimit.ι F k).1).naturality
                    (Limits.pullback.snd (𝒱.obj p.1).hom (𝒱.obj p.2).hom).op)
                  (s p.2)).symm
    have hsections : sx = sy := by
      -- Clause (2) applied to the quasi-compact overlap turns target equality into source-colimit
      -- equality over that overlap.
      apply
        sheafFilteredColimitSectionsComparison_injective_of_quasiCompactObject
          (J := J) F W (h𝒱qc p.1 p.2)
      have hsx :
          colimit.post F ((sheafSections J (Type (max u v z))).obj (op W)) sx =
            ((colimit.ι F k).1.app (op W)) x := by
        dsimp [sx]
        simpa using
          congrArg
            (fun f ↦ f x)
            (colimit.ι_post F ((sheafSections J (Type (max u v z))).obj (op W)) k)
      have hsy :
          colimit.post F ((sheafSections J (Type (max u v z))).obj (op W)) sy =
            ((colimit.ι F k).1.app (op W)) y := by
        dsimp [sy]
        simpa using
          congrArg
            (fun f ↦ f y)
            (colimit.ι_post F ((sheafSections J (Type (max u v z))).obj (op W)) k)
      exact hsx.trans (htarget.trans hsy.symm)
    let ψ :
        colimit (F ⋙ (sheafSections J (Type (max u v z))).obj (op W)) ⟶
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v z)))).obj (op W) :=
      colimit.post (F ⋙ sheafToPresheaf J (Type (max u v z)))
        ((evaluation Cᵒᵖ (Type (max u v z))).obj (op W))
    have hpresheaf :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) k).app (op W)) x =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) k).app (op W)) y := by
      -- Evaluating the source-colimit equality in presheaves puts it in the form needed by the
      -- filtered-colimit equality criterion.
      have hψ := congrArg ψ hsections
      have hψx :
          ψ sx =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) k).app (op W)) x := by
        dsimp [ψ, sx]
        simpa using
          congrArg
            (fun f ↦ f x)
            (colimit.ι_post (F ⋙ sheafToPresheaf J (Type (max u v z)))
              ((evaluation Cᵒᵖ (Type (max u v z))).obj (op W)) k)
      have hψy :
          ψ sy =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v z))) k).app (op W)) y := by
        dsimp [ψ, sy]
        simpa using
          congrArg
            (fun f ↦ f y)
            (colimit.ι_post (F ⋙ sheafToPresheaf J (Type (max u v z)))
              ((evaluation Cᵒᵖ (Type (max u v z))).obj (op W)) k)
      exact hψx.symm.trans (hψ.trans hψy)
    exact
      (presheafColimit_same_stage_eq_iff_eventually_equal (J := J) F k W x y).1 hpresheaf
  choose j f hf using hw
  obtain ⟨ℓ, g, hg⟩ :=
    common_target_of_finite_maps_from_aux (s := pairs) j (fun p _ ↦ f p)
  refine ⟨ℓ, g, ?_⟩
  intro u v
  let p : 𝒱.index × 𝒱.index := (u, v)
  let W := Limits.pullback (𝒱.obj u).hom (𝒱.obj v).hom
  let x : (F.obj k).1.obj (op W) :=
    ((F.obj k).1.map (Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom).op) (s u)
  let y : (F.obj k).1.obj (op W) :=
    ((F.obj k).1.map (Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom).op) (s v)
  obtain ⟨h, hh⟩ := hg p (by simp [pairs, p])
  have hpush :
      ((F.map (f p ≫ h)).hom.app (op W)) x =
        ((F.map (f p ≫ h)).hom.app (op W)) y := by
    simpa [x, y, Functor.map_comp] using
      congrArg (((F.map h).hom.app (op W))) (hf p)
  have hleft :
      ((F.map (f p ≫ h)).hom.app (op W)) x =
        ((F.obj ℓ).1.map (Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom).op)
          (((F.map g).hom.app (op ((𝒱.obj u).left))) (s u)) := by
    calc
      ((F.map (f p ≫ h)).hom.app (op W)) x =
          ((F.map g).hom.app (op W)) x := by simpa [p, hh]
      _ = ((F.map g).hom.app (op W))
          (((F.obj k).1.map (Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom).op) (s u)) := by
            rfl
      _ = ((F.obj ℓ).1.map (Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom).op)
            (((F.map g).hom.app (op ((𝒱.obj u).left))) (s u)) := by
              simpa using
                (sheaf_transition_app_map_eq_map_app (J := J) (F := F) g
                  (Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom) (s u))
  have hright :
      ((F.map (f p ≫ h)).hom.app (op W)) y =
        ((F.obj ℓ).1.map (Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom).op)
          (((F.map g).hom.app (op ((𝒱.obj v).left))) (s v)) := by
    calc
      ((F.map (f p ≫ h)).hom.app (op W)) y =
          ((F.map g).hom.app (op W)) y := by simpa [p, hh]
      _ = ((F.map g).hom.app (op W))
          (((F.obj k).1.map (Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom).op) (s v)) := by
            rfl
      _ = ((F.obj ℓ).1.map (Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom).op)
            (((F.map g).hom.app (op ((𝒱.obj v).left))) (s v)) := by
              simpa using
                (sheaf_transition_app_map_eq_map_app (J := J) (F := F) g
                  (Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom) (s v))
  exact hleft.symm.trans (hpush.trans hright)

/-- Helper for Lemma 7.17.7: compatibility on the canonical pullback overlaps implies the general
compatibility relation required by sheaf gluing. -/
private theorem cover_compatibility_of_pullback_compatibility
    (F : I ⥤ Sheaf J (Type (max u v z))) {U : C}
    (𝒱 : SemiRepresentableFamily.Over.{max u v} U) [𝒱.toPresieve.HasPairwisePullbacks]
    {ℓ : I} (s : ∀ u, (F.obj ℓ).1.obj (op ((𝒱.obj u).left)))
    (hs :
      ∀ u v,
        ((F.obj ℓ).1.map (Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom).op) (s u) =
          ((F.obj ℓ).1.map (Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom).op) (s v)) :
    ∀ ⦃W : C⦄ ⦃u v : 𝒱.index⦄ (a : W ⟶ (𝒱.obj u).left) (b : W ⟶ (𝒱.obj v).left),
      a ≫ (𝒱.obj u).hom = b ≫ (𝒱.obj v).hom →
        ((F.obj ℓ).1.map a.op) (s u) = ((F.obj ℓ).1.map b.op) (s v) := by
  intro W u v a b hab
  let l : W ⟶ Limits.pullback (𝒱.obj u).hom (𝒱.obj v).hom :=
    Limits.pullback.lift a b <| by simpa using hab
  have hlfst : l ≫ Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom = a := by
    simpa [l] using
      (Limits.pullback.lift_fst
        (f := (𝒱.obj u).hom) (g := (𝒱.obj v).hom) a b hab)
  have hlsnd : l ≫ Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom = b := by
    simpa [l] using
      (Limits.pullback.lift_snd
        (f := (𝒱.obj u).hom) (g := (𝒱.obj v).hom) a b hab)
  -- Factor both overlap arrows through the canonical pullback and use the assumed pullback
  -- compatibility there.
  calc
    ((F.obj ℓ).1.map a.op) (s u) =
        ((F.obj ℓ).1.map l.op)
          (((F.obj ℓ).1.map (Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom).op) (s u)) := by
            calc
              ((F.obj ℓ).1.map a.op) (s u) =
                  ((F.obj ℓ).1.map ((l ≫ Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom).op))
                    (s u) := by
                      rw [hlfst]
                      rfl
              _ = ((F.obj ℓ).1.map l.op)
                    (((F.obj ℓ).1.map (Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom).op)
                      (s u)) := by
                    simpa using
                      (FunctorToTypes.map_comp_apply
                        (F := (F.obj ℓ).1)
                        (Limits.pullback.fst (𝒱.obj u).hom (𝒱.obj v).hom).op l.op (s u)).symm
    _ = ((F.obj ℓ).1.map l.op)
          (((F.obj ℓ).1.map (Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom).op) (s v)) := by
            rw [hs u v]
    _ = ((F.obj ℓ).1.map b.op) (s v) := by
          calc
            ((F.obj ℓ).1.map l.op)
                (((F.obj ℓ).1.map (Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom).op) (s v)) =
              ((F.obj ℓ).1.map ((l ≫ Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom).op))
                (s v) := by
                  simpa using
                    (FunctorToTypes.map_comp_apply
                      (F := (F.obj ℓ).1)
                      (Limits.pullback.snd (𝒱.obj u).hom (𝒱.obj v).hom).op l.op (s v)).symm
            _ = ((F.obj ℓ).1.map b.op) (s v) := by
                  rw [hlsnd]
                  rfl

-- Proof sketch: use the assumed cofinal finite cover basis to choose a finite refinement of the
-- local representing cover of a target section. Quasi-compact pairwise pullbacks give eventual
-- agreement on overlaps, so after passing to one stage the local sections glue and produce a
-- preimage; injectivity follows from part (2) because this hypothesis implies `U` is
-- quasi-compact.
/-- Lemma 7.17.7 (4): if every covering family of `U` is refined by a finite covering family
whose pairwise fiber products are quasi-compact, then the canonical map
`\operatorname{colim}_i \mathcal F_i(U) \to (\operatorname{colim}_i \mathcal F_i)(U)` is
bijective. -/
theorem sheafFilteredColimitSectionsComparison_bijective_of_cofinalFiniteQuasiCompactOverlapCoverings
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C)
    (hU : HasCofinalFiniteQuasiCompactOverlapCoverings J U) :
    Function.Bijective
      (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))) := by
  -- Route correction: the final clause is the finite-overlap-covering source route used by
  -- Lemma 7.18.4, so the statement is preserved exactly here.
  refine ⟨?_, ?_⟩
  · exact
      sheafFilteredColimitSectionsComparison_injective_of_quasiCompactObject
        (J := J) F U hU.quasiCompactObject
  · intro t
    obtain ⟨𝒱, h𝒱, h𝒱fin, h𝒱pull, h𝒱qc, i, s, hs⟩ :=
      finite_overlap_local_representatives_of_comparison_target (J := J) F hU t
    haveI : Finite 𝒱.index := h𝒱fin
    haveI : 𝒱.toPresieve.HasPairwisePullbacks := h𝒱pull
    obtain ⟨k, e, s', hs'⟩ :=
      common_stage_of_finite_local_representatives (J := J) F 𝒱 i s t hs
    obtain ⟨ℓ, g, hpull⟩ :=
      common_stage_pullback_compatibility_of_same_target
        (J := J) (F := F) 𝒱 h𝒱qc t s' hs'
    let s'' : ∀ u, (F.obj ℓ).1.obj (op ((𝒱.obj u).left)) := fun u ↦
      ((F.map g).hom.app (op ((𝒱.obj u).left))) (s' u)
    have hs'' :
        ∀ u, ((colimit.ι F ℓ).1.app (op ((𝒱.obj u).left))) (s'' u) =
          ((colimit F).1.map ((𝒱.obj u).hom).op) t := by
      intro u
      -- Pushing the local representative from `k` to `ℓ` does not change the represented target
      -- section.
      have hpush :
          ((colimit.ι F ℓ).1.app (op ((𝒱.obj u).left))) (s'' u) =
            ((colimit.ι F k).1.app (op ((𝒱.obj u).left))) (s' u) := by
        calc
          ((colimit.ι F ℓ).1.app (op ((𝒱.obj u).left))) (s'' u) =
              (((F.map g) ≫ colimit.ι F ℓ).1.app (op ((𝒱.obj u).left))) (s' u) := by
                rfl
          _ = ((colimit.ι F k).1.app (op ((𝒱.obj u).left))) (s' u) := by
                simpa using
                  congrArg
                    (fun f ↦ f.1.app (op ((𝒱.obj u).left)) (s' u))
                    (colimit.w F g)
      exact hpush.trans (hs' u)
    have hcompat :
        ∀ ⦃W : C⦄ ⦃u v : 𝒱.index⦄ (a : W ⟶ (𝒱.obj u).left) (b : W ⟶ (𝒱.obj v).left),
          a ≫ (𝒱.obj u).hom = b ≫ (𝒱.obj v).hom →
            ((F.obj ℓ).1.map a.op) (s'' u) = ((F.obj ℓ).1.map b.op) (s'' v) :=
      cover_compatibility_of_pullback_compatibility
        (J := J) (F := F) 𝒱 s'' hpull
    let hFℓ : Presheaf.IsSheaf J ((F.obj ℓ).1) := (F.obj ℓ).2
    have hx :
        ∀ ⦃W : C⦄ ⦃u v : 𝒱.index⦄ (a : W ⟶ (𝒱.obj u).left) (b : W ⟶ (𝒱.obj v).left),
          a ≫ (𝒱.obj u).hom = b ≫ (𝒱.obj v).hom →
            (fun _ : PUnit ↦ ((F.obj ℓ).1.map a.op) (s'' u)) =
              fun _ : PUnit ↦ ((F.obj ℓ).1.map b.op) (s'' v) := by
      intro W u v a b hab
      funext _
      exact hcompat a b hab
    let gluedHom : PUnit ⟶ (F.obj ℓ).1.obj (op U) :=
      hFℓ.amalgamateOfArrows
        (f := fun u : 𝒱.index ↦ (𝒱.obj u).hom)
        (hf := h𝒱)
        (x := fun u _ ↦ s'' u)
        (hx := hx)
    let glued : (F.obj ℓ).1.obj (op U) := gluedHom PUnit.unit
    have hglued_restrict :
        ∀ u : 𝒱.index, ((F.obj ℓ).1.map ((𝒱.obj u).hom).op) glued = s'' u := by
      intro u
      -- The glued stage section restricts to the chosen local representatives.
      exact congrFun
        (hFℓ.amalgamateOfArrows_map
          (f := fun v : 𝒱.index ↦ (𝒱.obj v).hom)
          (hf := h𝒱)
          (x := fun v _ ↦ s'' v)
          (hx := hx)
          u)
        PUnit.unit
    have htarget :
        ((colimit.ι F ℓ).1.app (op U)) glued = t := by
      let hColim : Presheaf.IsSheaf J ((colimit F).1) := (colimit F).2
      have hsections :
          (fun _ : PUnit ↦ ((colimit.ι F ℓ).1.app (op U)) glued) = fun _ : PUnit ↦ t := by
        -- The glued image and the target section have the same restrictions on the covering
        -- family, so separatedness of the sheaf colimit identifies them.
        apply CategoryTheory.Presheaf.IsSheaf.hom_ext_ofArrows hColim
          (f := fun u : 𝒱.index ↦ (𝒱.obj u).hom)
          (hf := h𝒱)
        intro u
        funext _
        have hrestrict :
            ((colimit F).1.map ((𝒱.obj u).hom).op) (((colimit.ι F ℓ).1.app (op U)) glued) =
              ((colimit.ι F ℓ).1.app (op ((𝒱.obj u).left)))
                (((F.obj ℓ).1.map ((𝒱.obj u).hom).op) glued) := by
          exact
            (congrFun
              (((colimit.ι F ℓ).1).naturality ((𝒱.obj u).hom).op) glued).symm
        exact
          (hrestrict.trans <| by rw [hglued_restrict u]).trans (hs'' u)
      exact congrFun hsections PUnit.unit
    refine ⟨colimit.ι (F ⋙ (sheafSections J (Type (max u v z))).obj (op U)) ℓ glued, ?_⟩
    -- Evaluate the glued stage section in the source colimit and compare with `t`.
    have hsource :
        colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))
            (colimit.ι (F ⋙ (sheafSections J (Type (max u v z))).obj (op U)) ℓ glued) =
          ((colimit.ι F ℓ).1.app (op U)) glued := by
      simpa using
        congrArg
          (fun f ↦ f glued)
          (colimit.ι_post F ((sheafSections J (Type (max u v z))).obj (op U)) ℓ)
    exact hsource.trans htarget

end CategoryTheory
