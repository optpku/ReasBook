module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import stacks_project.Chap06.Definition_6_16_2
public import stacks_project.Chap06.Lemma_6_17_5

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.GrothendieckTopology

universe u v w z

noncomputable section

variable {X : TopCat.{u}} {I : Type v} [Category.{w} I] [IsFiltered I]
local notation "JX" => Opens.grothendieckTopology X
attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace CategoryTheory.GrothendieckTopology

/-- Helper for Lemma 6.29.1: every open cover of `U` admits a finite refinement whose members have
compact pairwise overlaps. The topology parameter is kept to match the source-facing owner
notation `HasCofinalFiniteQuasiCompactOverlapCoverings JX U`. -/
class HasCofinalFiniteQuasiCompactOverlapCoverings
    (J : GrothendieckTopology (Opens X)) (U : Opens X) : Prop where
  finite_refinement :
    ∀ {ι : Type u} (V : ι → Opens X),
      (∀ i, V i ≤ U) →
      (∀ x : U, ∃ i, x.1 ∈ V i) →
      ∃ (s : Finset (Opens X)),
        (∀ W ∈ s, W ≤ U) ∧
        (∀ W ∈ s, ∃ i, W ≤ V i) ∧
        (∀ x : U, ∃ W ∈ s, x.1 ∈ W) ∧
        (∀ W ∈ s, ∀ W' ∈ s, IsCompact (((W ⊓ W' : Opens X) : Set X)))

/-- Helper for Lemma 6.29.1: an open subset with cofinal finite refinements is compact. -/
theorem isCompact_of_cofinalFiniteQuasiCompactOverlapCoverings
    {U : Opens X} (hU : HasCofinalFiniteQuasiCompactOverlapCoverings JX U) :
    IsCompact (U : Set X) := by
  classical
  -- Compactness is equivalent to the finite-subcover property, so start from an arbitrary open
  -- cover of `U`.
  refine isCompact_of_finite_subcover ?_
  intro ι V hVopen hcover
  let Vop : ι → Opens X := fun i => ⟨V i, hVopen i⟩
  let R : ι → Opens X := fun i => U ⊓ Vop i
  -- Intersect the cover with `U` so the refinement owner applies on the nose.
  have hR_le : ∀ i, R i ≤ U := by
    intro i
    exact inf_le_left
  have hR_cover : ∀ x : U, ∃ i, x.1 ∈ R i := by
    intro x
    rcases Set.mem_iUnion.mp (hcover x.2) with ⟨i, hxi⟩
    exact ⟨i, ⟨x.2, hxi⟩⟩
  obtain ⟨s, hs_le, hs_refine, hs_cover, _⟩ := hU.finite_refinement R hR_le hR_cover
  choose f hf using hs_refine
  refine ⟨s.attach.image (fun W => f W.1 W.2), ?_⟩
  intro x hxU
  rcases hs_cover ⟨x, hxU⟩ with ⟨W, hW, hxW⟩
  have htmem : f W hW ∈ s.attach.image (fun W => f W.1 W.2) := by
    apply Finset.mem_image.mpr
    exact ⟨⟨W, hW⟩, by simp, rfl⟩
  refine Set.mem_iUnion.mpr ⟨f W hW, Set.mem_iUnion.mpr ⟨htmem, ?_⟩⟩
  exact ((hf W hW) hxW).2

end CategoryTheory.GrothendieckTopology

namespace TopCat.Presheaf

/-- Helper for Lemma 6.29.1: a locally injective map of set-valued presheaves on a topological
space is exactly a map whose equal target values become equal after restricting to a neighborhood
of each point. -/
theorem isLocallyInjective_iff
    {X : TopCat.{u}} {ℱ 𝒢 : X.Presheaf (Type z)} (T : ℱ ⟶ 𝒢) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) T ↔
      ∀ (U : Opens X) (s t : ℱ.obj (op U)), T.app _ s = T.app _ t →
        ∀ x ∈ U, ∃ (V : Opens X) (hV : V ≤ U),
          ℱ.map (homOfLE hV).op s = ℱ.map (homOfLE hV).op t ∧ x ∈ V := by
  constructor
  · intro h U s t hst x hx
    -- Convert the covering equalizer sieve into an honest neighborhood of the chosen point.
    obtain ⟨V, i, hi, hxV⟩ := h.equalizerSieve_mem s t hst x hx
    refine ⟨V, leOfHom i, ?_, hxV⟩
    simpa [CategoryTheory.Presheaf.equalizerSieve] using hi
  · intro h
    refine ⟨?_⟩
    intro U s t hst x hx
    -- The neighborhood formulation gives a covering equalizer sieve at every point.
    obtain ⟨V, hV, hEq, hxV⟩ := h U.unop s t hst x hx
    refine ⟨V, homOfLE hV, ?_, hxV⟩
    simpa [CategoryTheory.Presheaf.equalizerSieve] using hEq

end TopCat.Presheaf

/-- Helper for Lemma 6.29.1: finitely many stages in a filtered diagram admit a common target. -/
theorem common_target_of_finite_stages
    {I : Type v} [Category.{w} I] [IsFiltered I] (s : Finset I) :
    ∃ k : I, ∀ i ∈ s, Nonempty (i ⟶ k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · obtain ⟨k⟩ := IsFiltered.nonempty (C := I)
    exact ⟨k, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩
  · intro a s has hrec
    rcases hrec with ⟨k, hk⟩
    refine ⟨CategoryTheory.IsFiltered.max a k, ?_⟩
    intro j hj
    by_cases hja : j = a
    · subst j
      exact ⟨CategoryTheory.IsFiltered.leftToMax a k⟩
    · have hjs : j ∈ s := by
        exact (Finset.mem_insert.mp hj).resolve_left hja
      rcases hk j hjs with ⟨f⟩
      exact ⟨f ≫ CategoryTheory.IsFiltered.rightToMax a k⟩

/-- Helper for Lemma 6.29.1: finitely many arrows with common source in a filtered category admit a
common target on which all those arrows agree. This is the synchronization step needed to turn
finitely many local later-stage equalities into one honest pair of global sections in a single
stage sheaf. -/
theorem common_target_of_finite_maps_from
    {I : Type v} [Category.{w} I] [IsFiltered I] {i : I} {α : Type*} (s : Finset α)
    (j : α → I) (f : ∀ a : α, ∀ _ha : a ∈ s, i ⟶ j a) :
    ∃ k : I, ∃ g : i ⟶ k, ∀ a (ha : a ∈ s), ∃ h : j a ⟶ k, f a ha ≫ h = g := by
  classical
  revert f
  refine Finset.induction_on s ?_ ?_
  · intro f
    refine ⟨i, 𝟙 i, ?_⟩
    intro a ha
    exact False.elim (Finset.notMem_empty a ha)
  · intro a s has hrec f
    have hrec' := hrec (fun b hb ↦ f b (Finset.mem_insert_of_mem hb))
    rcases hrec' with ⟨k, g, hg⟩
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
      rcases hg b hb' with ⟨hbk, hhbk⟩
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

/-- Helper for Lemma 6.29.1: the chosen colimit sheaf is canonically the sheafification of the
underlying presheaf colimit. This is the comparison isomorphism that lets every part of the proof
work directly with `CategoryTheory.toSheafify`. -/
noncomputable def presheafColimitSheafifyIso
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w)))
    [_hcolim : HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))] :
    Sheaf JX (Type (max u v w)) := by
  exact
    (presheafToSheaf JX (Type (max u v w))).obj
      (colimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))))

/-- Helper for Lemma 6.29.1: the chosen colimit sheaf is canonically the sheafification of the
underlying presheaf colimit. This is the comparison isomorphism that lets every part of the proof
work directly with `CategoryTheory.toSheafify`. -/
noncomputable def presheafColimitToSheafIso
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w)))
    [hcolim : HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))] :
    ((presheafToSheaf JX (Type (max u v w))).obj
        (colimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))))) ≅ @colimit _ _ _ _ 𝓕 hcolim :=
  -- The sheafified presheaf-colimit cocone is a colimit cocone for `𝓕`, so the chosen colimit
  -- sheaf is canonically isomorphic to that sheafification.
  (colimit.isoColimitCocone
    ⟨Sheaf.sheafifyCocone
        (colimit.cocone (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).symm

/-- Helper for Lemma 6.29.1: the comparison from the presheaf colimit to the underlying presheaf
of the sheaf colimit factors through the sheafification unit, followed by the inverse of the
canonical colimit-sheaf comparison isomorphism. -/
theorem presheaf_colimit_comparison_factorization
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w)))
    [HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))] :
    (CategoryTheory.toSheafify JX
        (colimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))))) ≫
      (sheafToPresheaf JX (Type (max u v w))).map
        (colimit.isoColimitCocone
          ⟨Sheaf.sheafifyCocone
              (colimit.cocone (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))),
            Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).inv =
      colimit.post 𝓕 (sheafToPresheaf JX (Type (max u v w))) := by
  -- Compare the two candidate maps after precomposing with each colimit injection.
  refine colimit.hom_ext ?_
  intro i
  have hleft :
      colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) i ≫
          CategoryTheory.toSheafify JX
            (colimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))) ≫
            (sheafToPresheaf JX (Type (max u v w))).map
              (colimit.isoColimitCocone
                ⟨Sheaf.sheafifyCocone
                    (colimit.cocone (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))),
                  Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).inv =
        (((Sheaf.sheafifyCocone (J := JX) (D := Type (max u v w))
            (colimit.cocone (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))))).ι.app i).1 ≫
          (sheafToPresheaf JX (Type (max u v w))).map
            (colimit.isoColimitCocone
              ⟨Sheaf.sheafifyCocone
                  (colimit.cocone (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))),
                Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).inv) := by
    -- The sheafified cocone injection is the presheaf-colimit injection followed by the unit.
    simpa [Category.assoc] using congrArg
      (fun f ↦ f ≫ (sheafToPresheaf JX (Type (max u v w))).map
        (colimit.isoColimitCocone
          ⟨Sheaf.sheafifyCocone
              (colimit.cocone (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))),
            Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).inv)
      (Sheaf.sheafifyCocone_ι_app_val (J := JX) (D := Type (max u v w))
        (E := colimit.cocone (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))) i).symm
  rw [hleft]
  have hmid :
      ((Sheaf.sheafifyCocone (J := JX) (D := Type (max u v w))
          (colimit.cocone (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))))).ι.app i).1 ≫
        (sheafToPresheaf JX (Type (max u v w))).map
          (colimit.isoColimitCocone
            ⟨Sheaf.sheafifyCocone
                (colimit.cocone (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))),
              Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).inv =
      (colimit.ι 𝓕 i).1 := by
    -- The colimit isomorphism identifies the sheafified presheaf cocone with the actual colimit.
    simpa using congrArg (fun f ↦ f.1)
      (colimit.isoColimitCocone_ι_inv
        ⟨Sheaf.sheafifyCocone
            (colimit.cocone (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))),
          Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩ i)
  rw [hmid]
  exact (colimit.ι_post 𝓕 (sheafToPresheaf JX (Type (max u v w))) i).symm

/-- Helper for Lemma 6.29.1: the source colimit of sections over `U` identifies with the
evaluation of the presheaf-colimit comparison at `U`. -/
theorem section_colimit_post_eq_eval
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op U))]
    [HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))] :
    colimit.post 𝓕 ((sheafSections JX (Type (max u v w))).obj (op U)) =
      colimit.post (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))
          ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) ≫
        (colimit.post 𝓕 (sheafToPresheaf JX (Type (max u v w)))).app (op U) := by
  -- The sections functor is the composite of the forgetful functor with evaluation at `U`.
  simpa using
    (colimit.post_post 𝓕 (sheafToPresheaf JX (Type (max u v w)))
      ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U))).symm

/-- Helper for Lemma 6.29.1: evaluating a represented section of a presheaf colimit after
restricting along `f : V ⟶ U` gives the represented restricted section in the evaluation-side
filtered colimit. This is the transport identity used in the compact synchronization step. -/
theorem colimitObjIsoColimitCompEvaluation_hom_map_ι_apply
    (G : I ⥤ X.Presheaf (Type (max u v w))) {U V : Opens X} (f : V ⟶ U)
    (i : I) (a : (G.obj i).obj (op U)) :
    (colimitObjIsoColimitCompEvaluation G (op V)).hom
        (((colimit G).map f.op) (((colimit.ι G i).app (op U)) a)) =
      colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op V)) i
        (((G.obj i).map f.op) a) := by
  let eU := colimitObjIsoColimitCompEvaluation G (op U)
  let eV := colimitObjIsoColimitCompEvaluation G (op V)
  -- Move the restricted represented section across the evaluation/colimit comparison isomorphism.
  have hmap :
      eV.hom (((colimit G).map f.op) (((colimit.ι G i).app (op U)) a)) =
        colimMap (G.whiskerLeft ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).map f.op))
          (eU.hom (((colimit.ι G i).app (op U)) a)) := by
    simpa [eV, eU] using congrArg (fun g ↦ g (((colimit.ι G i).app (op U)) a))
      (colimit_map_colimitObjIsoColimitCompEvaluation_hom G f.op)
  rw [hmap]
  -- Then identify the source class in the evaluation-side colimit.
  have hUrep :
      eU.hom (((colimit.ι G i).app (op U)) a) =
        colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) i a := by
    exact congrFun (colimitObjIsoColimitCompEvaluation_ι_app_hom G i (op U)) a
  rw [hUrep]
  exact congrFun
    (colimit.ι_map
      (G.whiskerLeft ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).map f.op)) i) a

/-- Helper for Lemma 6.29.1: if every transition map is a monomorphism, then the underlying
presheaf colimit is separated. This is the textbook invariant behind clause (1), stated here in
the project’s owner language `Presieve.IsSeparated`. -/
theorem separated_presheafColimit_of_transitionMapsInjective
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w)))
    [HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))]
    (hmono : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (𝓕.map f)) :
    Presieve.IsSeparated JX (colimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))) := by
  let G : I ⥤ X.Presheaf (Type (max u v w)) :=
    𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))
  intro U S hS x t₁ t₂ ht₁ ht₂
  let eU := colimitObjIsoColimitCompEvaluation G (op U)
  -- First move the two candidate colimit sections to one common stage at `U`.
  obtain ⟨i, a, b, ha, hb⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (colimit.isColimit (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)))
      (eU.hom t₁) (eU.hom t₂)
  have hιa :
      eU.inv
          (colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) i a) =
        ((colimit.ι G i).app (op U)) a := by
    simpa [eU] using congrFun (colimitObjIsoColimitCompEvaluation_ι_inv G i (op U)) a
  have hιb :
      eU.inv
          (colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) i b) =
        ((colimit.ι G i).app (op U)) b := by
    simpa [eU] using congrFun (colimitObjIsoColimitCompEvaluation_ι_inv G i (op U)) b
  have ht₁' :
      t₁ =
        eU.inv
          (colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) i a) := by
    simpa [eU] using congrArg eU.inv ha.symm
  have ht₂' :
      t₂ =
        eU.inv
          (colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) i b) := by
    simpa [eU] using congrArg eU.inv hb.symm
  have ht₁rep : ((colimit.ι G i).app (op U)) a = t₁ := hιa.symm.trans ht₁'.symm
  have ht₂rep : ((colimit.ι G i).app (op U)) b = t₂ := hιb.symm.trans ht₂'.symm
  have hsep_i : Presieve.IsSeparatedFor ((𝓕.obj i).1) S.arrows :=
    ((isSheaf_iff_isSheaf_of_type JX ((𝓕.obj i).1)).1 (𝓕.obj i).2).isSeparated S hS
  have hab : a = b := by
    -- Reduce separatedness of the colimit presheaf to separatedness of a single stage sheaf.
    apply hsep_i.ext
    intro V f hf
    have hlocal_target : (colimit G).map f.op t₁ = (colimit G).map f.op t₂ :=
      (ht₁ f hf).trans (ht₂ f hf).symm
    let eV := colimitObjIsoColimitCompEvaluation G (op V)
    have hleft :
        eV.hom ((colimit G).map f.op (((colimit.ι G i).app (op U)) a)) =
          colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op V)) i
            (((G.obj i).map f.op) a) := by
      have hmap :
          eV.hom ((colimit G).map f.op (((colimit.ι G i).app (op U)) a)) =
            colimMap (G.whiskerLeft ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).map f.op))
              (eU.hom (((colimit.ι G i).app (op U)) a)) := by
        simpa [eV, eU] using congrArg (fun g ↦ g (((colimit.ι G i).app (op U)) a))
          (colimit_map_colimitObjIsoColimitCompEvaluation_hom G f.op)
      rw [hmap]
      have hUrep :
          eU.hom (((colimit.ι G i).app (op U)) a) =
            colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) i a := by
        exact congrFun (colimitObjIsoColimitCompEvaluation_ι_app_hom G i (op U)) a
      rw [hUrep]
      exact congrFun
        (colimit.ι_map
          (G.whiskerLeft ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).map f.op)) i) a
    have hright :
        eV.hom ((colimit G).map f.op (((colimit.ι G i).app (op U)) b)) =
          colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op V)) i
            (((G.obj i).map f.op) b) := by
      have hmap :
          eV.hom ((colimit G).map f.op (((colimit.ι G i).app (op U)) b)) =
            colimMap (G.whiskerLeft ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).map f.op))
              (eU.hom (((colimit.ι G i).app (op U)) b)) := by
        simpa [eV, eU] using congrArg (fun g ↦ g (((colimit.ι G i).app (op U)) b))
          (colimit_map_colimitObjIsoColimitCompEvaluation_hom G f.op)
      rw [hmap]
      have hUrep :
          eU.hom (((colimit.ι G i).app (op U)) b) =
            colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) i b := by
        exact congrFun (colimitObjIsoColimitCompEvaluation_ι_app_hom G i (op U)) b
      rw [hUrep]
      exact congrFun
        (colimit.ι_map
          (G.whiskerLeft ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).map f.op)) i) b
    have hlocal_eval :
        colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op V)) i
            (((G.obj i).map f.op) a) =
          colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op V)) i
            (((G.obj i).map f.op) b) := by
      rw [← hleft, ← hright]
      have hlocal_target' :
          (colimit G).map f.op (((colimit.ι G i).app (op U)) a) =
            (colimit G).map f.op (((colimit.ι G i).app (op U)) b) := by
        simpa [ht₁rep, ht₂rep] using hlocal_target
      exact congrArg eV.hom hlocal_target'
    obtain ⟨k, g₁, g₂, hk⟩ :=
      (CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff
        (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op V))).1 hlocal_eval
    let h := IsFiltered.coeqHom g₁ g₂
    have hcomp := congrArg
      (((G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op V))).map h) hk
    have hcoeq_app :
        ((𝓕.map h).1.app (op V)) (((𝓕.map g₁).1.app (op V)) (((G.obj i).map f.op) a)) =
          ((𝓕.map h).1.app (op V)) (((𝓕.map g₂).1.app (op V)) (((G.obj i).map f.op) a)) := by
      have hcoeq := congrArg (fun z ↦ ((𝓕.map z).1.app (op V)))
        (IsFiltered.coeq_condition g₁ g₂)
      simpa [h, G, Functor.map_comp, Category.assoc] using
        congrFun hcoeq (((G.obj i).map f.op) a)
    have hEq :
        ((𝓕.map h).1.app (op V)) (((𝓕.map g₂).1.app (op V)) (((G.obj i).map f.op) a)) =
          ((𝓕.map h).1.app (op V)) (((𝓕.map g₂).1.app (op V)) (((G.obj i).map f.op) b)) := by
      exact hcoeq_app.symm.trans hcomp
    have hinj : Function.Injective ((𝓕.map (g₂ ≫ h)).1.app (op V)) := by
      exact (sheaf_mono_iff_app_injective (𝓕.map (g₂ ≫ h))).1 (hmono (g₂ ≫ h)) V
    have hEq' :
        ((𝓕.map (g₂ ≫ h)).1.app (op V)) (((G.obj i).map f.op) a) =
          ((𝓕.map (g₂ ≫ h)).1.app (op V)) (((G.obj i).map f.op) b) := by
      simpa [h, G, Functor.map_comp, Category.assoc] using hEq
    exact hinj hEq'
  exact ht₁rep.symm.trans <| (congrArg ((colimit.ι G i).app (op U)) hab).trans ht₂rep

/-- Helper for Lemma 6.29.1: on a separated presheaf, the sheafification unit is injective on
sections over every open. -/
theorem injective_toSheafify_app_of_isSeparated
    (ℱ : X.Presheaf (Type (max u v w)))
    (hℱ : Presieve.IsSeparated JX ℱ) (U : Opens X) :
    Function.Injective ((CategoryTheory.toSheafify JX ℱ).app (op U)) := by
  -- First control the concrete `P⁺⁺` unit: separatedness makes the first `toPlus` injective, and
  -- the second `toPlus` is an isomorphism because `P⁺` is already a sheaf.
  have h_toPlus_inj :
      Function.Injective ((GrothendieckTopology.toPlus (J := JX) ℱ).app (op U)) := by
    exact CategoryTheory.GrothendieckTopology.Plus.inj_of_sep (J := JX) (P := ℱ)
      (fun V S x y hxy => by
        refine (hℱ S.1 S.2).ext ?_
        intro Y f hf
        exact hxy ⟨Y, f, hf⟩) U
  have hsheaf_plus : Presheaf.IsSheaf JX (GrothendieckTopology.plusObj (J := JX) ℱ) := by
    exact CategoryTheory.GrothendieckTopology.Plus.isSheaf_of_sep (J := JX) (P := ℱ)
      (fun V S x y hxy => by
        refine (hℱ S.1 S.2).ext ?_
        intro Y f hf
        exact hxy ⟨Y, f, hf⟩)
  have h_second_inj :
      Function.Injective ((GrothendieckTopology.toPlus (J := JX)
        (GrothendieckTopology.plusObj (J := JX) ℱ)).app (op U)) := by
    let hIso :
        IsIso (GrothendieckTopology.toPlus (J := JX)
          (GrothendieckTopology.plusObj (J := JX) ℱ)) :=
      GrothendieckTopology.isIso_toPlus_of_isSheaf (J := JX)
        (P := GrothendieckTopology.plusObj (J := JX) ℱ) hsheaf_plus
    exact ((CategoryTheory.isIso_iff_bijective _).1
      ((NatTrans.isIso_iff_isIso_app _).1 hIso (op U))).1
  have h_concrete :
      Function.Injective ((GrothendieckTopology.toSheafify (J := JX) ℱ).app (op U)) := by
    -- Rewrite `toSheafify` as the two-step `toPlus` construction.
    rw [GrothendieckTopology.toSheafify, GrothendieckTopology.plusMap_toPlus]
    intro s t hst
    apply h_toPlus_inj
    apply h_second_inj
    exact hst
  -- Then transport along the canonical comparison from `P⁺⁺` to categorical sheafification.
  have hfac :
      GrothendieckTopology.toSheafify (J := JX) ℱ =
        CategoryTheory.toSheafify JX ℱ ≫
          (plusPlusIsoSheafify JX (Type (max u v w)) ℱ).inv := by
    rw [CategoryTheory.Iso.eq_comp_inv]
    simpa using
      (CategoryTheory.toSheafify_plusPlusIsoSheafify_hom
        (J := JX) (D := Type (max u v w)) ℱ)
  intro s t hst
  apply h_concrete
  have hst' := congrArg (((plusPlusIsoSheafify JX (Type (max u v w)) ℱ).inv.app (op U))) hst
  simpa [hfac, Category.assoc] using hst'

/-- Helper for Lemma 6.29.1: the plus-construction unit of a set-valued presheaf is locally
injective. This packages the owner instance in a way that remains stable in the present universe
profile. -/
theorem toPlus_isLocallyInjective_type
    (P : X.Presheaf (Type (max u v w))) :
    CategoryTheory.Presheaf.IsLocallyInjective JX
      (GrothendieckTopology.toPlus (J := JX) P) where
  equalizerSieve_mem := by
    intro U x y h
    -- Equality in `P⁺` means the representatives agree after shrinking to one covering family.
    rw [GrothendieckTopology.Plus.toPlus_eq_mk, GrothendieckTopology.Plus.toPlus_eq_mk,
      GrothendieckTopology.Plus.eq_mk_iff_exists] at h
    obtain ⟨W, _, _, eq⟩ := h
    exact CategoryTheory.GrothendieckTopology.superset_covering JX
      (fun Y f hf => congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) W.2

/-- Helper for Lemma 6.29.1: the plus-construction unit of a set-valued presheaf is locally
surjective. This packages the owner instance in a way that remains stable in the present universe
profile. -/
theorem toPlus_isLocallySurjective_type
    (P : X.Presheaf (Type (max u v w))) :
    CategoryTheory.Presheaf.IsLocallySurjective JX
      (GrothendieckTopology.toPlus (J := JX) P) where
  imageSieve_mem := by
    intro U x
    -- Choose one representative family for the `P⁺`-section and restrict that family along the
    -- covering arrows to obtain local preimages.
    obtain ⟨S, x, rfl⟩ := GrothendieckTopology.Plus.exists_rep x
    refine CategoryTheory.GrothendieckTopology.superset_covering JX
      (fun Y f hf => ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [GrothendieckTopology.Plus.toPlus_eq_mk,
      GrothendieckTopology.Plus.res_mk_eq_mk_pullback,
      GrothendieckTopology.Plus.eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using x.2
      { fst.hf := hf
        snd.hf := S.1.downward_closed hf g
        r.g₁ := g
        r.g₂ := 𝟙 Z
        .. }

/-- Helper for Lemma 6.29.1: equality in the sheafification of a set-valued presheaf becomes an
honest equality after restricting to some neighborhood of each point. -/
theorem local_eq_of_toSheafify_app_eq
    (P : X.Presheaf (Type (max u v w))) (U : Opens X)
    {s t : P.obj (op U)}
    (hst : ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op U)) s =
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op U)) t) :
    ∀ x ∈ U, ∃ (V : Opens X) (hV : V ≤ U),
      P.map (homOfLE hV).op s = P.map (homOfLE hV).op t ∧ x ∈ V := by
  let Pplus := GrothendieckTopology.plusObj (J := JX) P
  have hplus2 : CategoryTheory.Presheaf.IsLocallyInjective JX
      (GrothendieckTopology.toPlus (J := JX) Pplus) := by
    -- The second plus-construction has the same explicit local-equality description.
    refine { equalizerSieve_mem := ?_ }
    intro W x y h
    rw [GrothendieckTopology.Plus.toPlus_eq_mk, GrothendieckTopology.Plus.toPlus_eq_mk,
      GrothendieckTopology.Plus.eq_mk_iff_exists] at h
    obtain ⟨S, _, _, eq⟩ := h
    exact CategoryTheory.GrothendieckTopology.superset_covering JX
      (fun Y f hf => congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) S.2
  have hplus1 : CategoryTheory.Presheaf.IsLocallyInjective JX
      (GrothendieckTopology.toPlus (J := JX) P) := by
    -- The first plus-construction has the same explicit local-equality description.
    refine { equalizerSieve_mem := ?_ }
    intro W x y h
    rw [GrothendieckTopology.Plus.toPlus_eq_mk, GrothendieckTopology.Plus.toPlus_eq_mk,
      GrothendieckTopology.Plus.eq_mk_iff_exists] at h
    obtain ⟨S, _, _, eq⟩ := h
    exact CategoryTheory.GrothendieckTopology.superset_covering JX
      (fun Y f hf => congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) S.2
  have hfac :
      GrothendieckTopology.toSheafify (J := JX) P =
        CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P ≫
          (plusPlusIsoSheafify JX (Type (max u v w)) P).inv := by
    rw [CategoryTheory.Iso.eq_comp_inv]
    simpa using
      CategoryTheory.toSheafify_plusPlusIsoSheafify_hom
        (J := JX) (D := Type (max u v w)) P
  have hst' := congrArg (((plusPlusIsoSheafify JX (Type (max u v w)) P).inv.app (op U))) hst
  have hconcrete :
      ((GrothendieckTopology.toSheafify (J := JX) P).app (op U)) s =
        ((GrothendieckTopology.toSheafify (J := JX) P).app (op U)) t := by
    -- Transport the categorical equality to the concrete `P⁺⁺` model.
    simpa [hfac, Category.assoc] using hst'
  rw [GrothendieckTopology.toSheafify, GrothendieckTopology.plusMap_toPlus] at hconcrete
  intro x hx
  -- First shrink until the two `P⁺`-sections agree.
  obtain ⟨W, hW, hW_eq, hxW⟩ :=
    (TopCat.Presheaf.isLocallyInjective_iff
      (T := GrothendieckTopology.toPlus (J := JX) Pplus)).1 hplus2 U
      (((GrothendieckTopology.toPlus (J := JX) P).app (op U)) s)
      (((GrothendieckTopology.toPlus (J := JX) P).app (op U)) t)
      hconcrete x hx
  have hW_eq' :
      ((GrothendieckTopology.toPlus (J := JX) P).app (op W))
          (P.map (homOfLE hW).op s) =
        ((GrothendieckTopology.toPlus (J := JX) P).app (op W))
          (P.map (homOfLE hW).op t) := by
    -- Rewrite the restriction of the `P⁺`-sections using naturality of `toPlus`.
    calc
      ((GrothendieckTopology.toPlus (J := JX) P).app (op W))
          (P.map (homOfLE hW).op s)
          =
        Pplus.map (homOfLE hW).op
          (((GrothendieckTopology.toPlus (J := JX) P).app (op U)) s) := by
            exact congrFun
              ((GrothendieckTopology.toPlus (J := JX) P).naturality (homOfLE hW).op) s
      _ =
        Pplus.map (homOfLE hW).op
          (((GrothendieckTopology.toPlus (J := JX) P).app (op U)) t) := hW_eq
      _ =
        ((GrothendieckTopology.toPlus (J := JX) P).app (op W))
          (P.map (homOfLE hW).op t) := by
            exact (congrFun
              ((GrothendieckTopology.toPlus (J := JX) P).naturality (homOfLE hW).op) t
              ).symm
  -- Then shrink once more until the original `P`-sections agree.
  obtain ⟨V, hV, hV_eq, hxV⟩ :=
    (TopCat.Presheaf.isLocallyInjective_iff
      (T := GrothendieckTopology.toPlus (J := JX) P)).1 hplus1 W
      (P.map (homOfLE hW).op s)
      (P.map (homOfLE hW).op t)
      hW_eq' x hxW
  refine ⟨V, le_trans hV hW, ?_, hxV⟩
  -- Compose the two restriction maps to obtain equality directly over a neighborhood of `x`.
  simpa [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp] using hV_eq

/-- Helper for Lemma 6.29.1: every sheafified section is locally represented by an actual
presheaf section on a neighborhood of each point. -/
theorem local_preimage_of_toSheafify_app
    (P : X.Presheaf (Type (max u v w))) (U : Opens X)
    (z : ((presheafToSheaf JX (Type (max u v w))).obj P).1.obj (op U)) :
    ∀ x ∈ U, ∃ (V : Opens X) (hV : V ≤ U) (s : P.obj (op V)),
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op V)) s =
        ((presheafToSheaf JX (Type (max u v w))).obj P).1.map (homOfLE hV).op z ∧ x ∈ V := by
  intro x hx
  let Pplus := GrothendieckTopology.plusObj (J := JX) P
  let PplusPlus := GrothendieckTopology.plusObj (J := JX) Pplus
  let e := plusPlusIsoSheafify JX (Type (max u v w)) P
  let z' :
      (GrothendieckTopology.plusObj (J := JX)
        (GrothendieckTopology.plusObj (J := JX) P)).obj (op U) := e.inv.app (op U) z
  have hmem₂ :
      CategoryTheory.Presheaf.imageSieve
          (GrothendieckTopology.toPlus (J := JX) Pplus) z' ∈ JX U := by
    -- Prove local surjectivity for this explicit `P⁺⁺` section directly to keep universes fixed.
    dsimp [z']
    rcases GrothendieckTopology.Plus.exists_rep
        (J := JX) (P := GrothendieckTopology.plusObj (J := JX) P) (X := U)
        (e.inv.app (op U) z) with ⟨S, rep, hz⟩
    rw [hz]
    refine CategoryTheory.GrothendieckTopology.superset_covering JX
      (fun Y f hf => ⟨rep.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [GrothendieckTopology.Plus.toPlus_eq_mk,
      GrothendieckTopology.Plus.res_mk_eq_mk_pullback,
      GrothendieckTopology.Plus.eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using rep.2
      { fst.hf := hf
        snd.hf := S.1.downward_closed hf g
        r.g₁ := g
        r.g₂ := 𝟙 Z
        .. }
  have hfac :
      GrothendieckTopology.toSheafify (J := JX) P =
        CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P ≫ e.inv := by
    rw [CategoryTheory.Iso.eq_comp_inv]
    simpa [e] using
      CategoryTheory.toSheafify_plusPlusIsoSheafify_hom
        (J := JX) (D := Type (max u v w)) P
  rcases hmem₂ x hx with ⟨W, iW, hiW, hxW⟩
  let t :
      (GrothendieckTopology.plusObj (J := JX) P).obj (op W) := CategoryTheory.Presheaf.localPreimage
    (GrothendieckTopology.toPlus (J := JX) Pplus) z' iW hiW
  have ht :
      (GrothendieckTopology.toPlus (J := JX) Pplus).app (op W) t =
        PplusPlus.map iW.op z' := by
    simpa [t] using
      (CategoryTheory.Presheaf.app_localPreimage
        (GrothendieckTopology.toPlus (J := JX) Pplus) z' iW hiW)
  have hmem₁ :
      CategoryTheory.Presheaf.imageSieve
          (GrothendieckTopology.toPlus (J := JX) P) t ∈ JX W := by
    -- Repeat the same explicit argument for the local `P⁺` section `t`.
    rcases GrothendieckTopology.Plus.exists_rep (J := JX) (P := P) (X := W) t with
      ⟨S, rep, htrep⟩
    rw [htrep]
    refine CategoryTheory.GrothendieckTopology.superset_covering JX
      (fun Y f hf => ⟨rep.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [GrothendieckTopology.Plus.toPlus_eq_mk,
      GrothendieckTopology.Plus.res_mk_eq_mk_pullback,
      GrothendieckTopology.Plus.eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using rep.2
      { fst.hf := hf
        snd.hf := S.1.downward_closed hf g
        r.g₁ := g
        r.g₂ := 𝟙 Z
        .. }
  rcases hmem₁ x hxW with ⟨V, iV, hiV, hxV⟩
  let s : P.obj (op V) := CategoryTheory.Presheaf.localPreimage
    (GrothendieckTopology.toPlus (J := JX) P) t iV hiV
  have hs :
      (GrothendieckTopology.toPlus (J := JX) P).app (op V) s =
        Pplus.map iV.op t := by
    simpa [s] using
      (CategoryTheory.Presheaf.app_localPreimage
        (GrothendieckTopology.toPlus (J := JX) P) t iV hiV)
  have hconcrete :
      (GrothendieckTopology.toSheafify (J := JX) P).app (op V) s =
        PplusPlus.map (iV ≫ iW).op z' := by
    -- Compose the two local lifts to obtain an actual `P⁺⁺` equality over one neighborhood.
    rw [GrothendieckTopology.toSheafify, GrothendieckTopology.plusMap_toPlus]
    calc
      (GrothendieckTopology.toPlus (J := JX) Pplus).app (op V)
          ((GrothendieckTopology.toPlus (J := JX) P).app (op V) s)
          =
        (GrothendieckTopology.toPlus (J := JX) Pplus).app (op V)
          (Pplus.map iV.op t) := by
            rw [hs]
      _ =
        PplusPlus.map iV.op ((GrothendieckTopology.toPlus (J := JX) Pplus).app (op W) t) := by
            exact congrFun ((GrothendieckTopology.toPlus (J := JX) Pplus).naturality iV.op) t
      _ = PplusPlus.map iV.op (PplusPlus.map iW.op z') := by
            rw [ht]
      _ = PplusPlus.map (iV ≫ iW).op z' := by
            simp [FunctorToTypes.map_comp_apply, op_comp]
  -- Read the two-step local lift as a single neighborhood `V ⟶ U`.
  refine ⟨V, leOfHom (iV ≫ iW), s, ?_, hxV⟩
  have hfacV :
      (GrothendieckTopology.toSheafify (J := JX) P).app (op V) s =
        e.inv.app (op V)
          (((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op V)) s) := by
    simpa [Category.assoc, e] using congrArg (fun η => η.app (op V) s) hfac
  have hleft :
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op V)) s =
        e.hom.app (op V) ((GrothendieckTopology.toSheafify (J := JX) P).app (op V) s) := by
    have h := congrArg (e.hom.app (op V)) hfacV
    simpa [e] using h.symm
  have hright :
      e.hom.app (op V) (PplusPlus.map (iV ≫ iW).op z') =
        ((presheafToSheaf JX (Type (max u v w))).obj P).1.map (iV ≫ iW).op z := by
    calc
      e.hom.app (op V) (PplusPlus.map (iV ≫ iW).op z') =
          ((presheafToSheaf JX (Type (max u v w))).obj P).1.map (iV ≫ iW).op
            (e.hom.app (op U) z') := by
              simpa [PplusPlus, e] using
                congrArg (fun f => f z') (e.hom.naturality ((iV ≫ iW).op))
      _ = ((presheafToSheaf JX (Type (max u v w))).obj P).1.map (iV ≫ iW).op z := by
            simpa [z', e] using
              congrArg
                (((presheafToSheaf JX (Type (max u v w))).obj P).1.map (iV ≫ iW).op)
                (CategoryTheory.inv_hom_id_app_apply e (op U) z)
  calc
    ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op V)) s
        = e.hom.app (op V) ((GrothendieckTopology.toSheafify (J := JX) P).app (op V) s) := hleft
    _ = e.hom.app (op V) (PplusPlus.map (iV ≫ iW).op z') := by
          rw [hconcrete]
    _ = ((presheafToSheaf JX (Type (max u v w))).obj P).1.map (iV ≫ iW).op z := hright

/-- Helper for Lemma 6.29.1: a local preimage under `toSheafify` stays a local preimage after
restricting to a smaller open. This packages the naturality rewrite needed in the compact gluing
arguments. -/
theorem refined_local_preimage_restriction_eq
    (P : X.Presheaf (Type (max u v w))) {U V W : Opens X}
    (hV : V ≤ U) (hW : W ≤ V)
    {z : ((presheafToSheaf JX (Type (max u v w))).obj P).1.obj (op U)}
    {s : P.obj (op V)}
    (hs :
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op V)) s =
        ((presheafToSheaf JX (Type (max u v w))).obj P).1.map (homOfLE hV).op z) :
    ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W))
        (P.map (homOfLE hW).op s) =
      ((presheafToSheaf JX (Type (max u v w))).obj P).1.map
        (homOfLE (le_trans hW hV)).op z := by
  -- Restrict the chosen preimage equality and use naturality on both sides.
  calc
    ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W))
        (P.map (homOfLE hW).op s)
      =
        ((presheafToSheaf JX (Type (max u v w))).obj P).1.map (homOfLE hW).op
          (((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op V)) s) := by
            exact congrFun
              (((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).naturality
                (homOfLE hW).op)) s
    _ =
        ((presheafToSheaf JX (Type (max u v w))).obj P).1.map (homOfLE hW).op
          (((presheafToSheaf JX (Type (max u v w))).obj P).1.map (homOfLE hV).op z) := by
            rw [hs]
    _ =
        ((presheafToSheaf JX (Type (max u v w))).obj P).1.map
          (homOfLE (le_trans hW hV)).op z := by
            rw [← FunctorToTypes.map_comp_apply]
            rw [← op_comp]
            rw [homOfLE_comp]

/-- Helper for Lemma 6.29.1: restriction commutes with every transition map in the sheaf
diagram. This is the rewrite used when finitely many local later-stage equalities are transported
to one common target stage. -/
theorem sheaf_transition_app_map_eq_map_app
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) {i j : I} (f : i ⟶ j)
    {U V : Opens X} (g : V ⟶ U) (a : (𝓕.obj i).1.obj (op U)) :
    ((𝓕.map f).1.app (op V)) (((𝓕.obj i).1.map g.op) a) =
      ((𝓕.obj j).1.map g.op) (((𝓕.map f).1.app (op U)) a) := by
  -- This is exactly the naturality square of the underlying presheaf map of `𝓕.map f`.
  exact congrFun ((𝓕.map f).1.naturality g.op) a

/-- Helper for Lemma 6.29.1: a finite family of local sections of the presheaf colimit can be
represented in a single common stage of the filtered diagram. This is the common-stage domination
step used before gluing the local representatives. -/
theorem common_stage_of_finite_local_colimit_sections
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) {α : Type*} [Finite α]
    (V : α → Opens X)
    [HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))]
    (s : ∀ a, (colimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))).obj (op (V a))) :
    ∃ k : I, ∃ t : ∀ a, (𝓕.obj k).1.obj (op (V a)),
      ∀ a,
        ((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op (V a))) (t a) = s a := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  let G : I ⥤ X.Presheaf (Type (max u v w)) := 𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))
  have hs :
      ∀ a, ∃ i : I, ∃ u : (𝓕.obj i).1.obj (op (V a)),
        ((colimit.ι G i).app (op (V a))) u = s a := by
    intro a
    let e := colimitObjIsoColimitCompEvaluation G (op (V a))
    -- Represent each local colimit section by a genuine section at some stage.
    obtain ⟨i, u, hu⟩ :=
      Types.jointly_surjective_of_isColimit
        (colimit.isColimit (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op (V a))))
        (e.hom (s a))
    refine ⟨i, u, ?_⟩
    have hu' := congrArg e.inv hu
    have hrepr :
        e.inv
            (colimit.ι
              (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op (V a))) i u) =
          ((colimit.ι G i).app (op (V a))) u := by
      simpa [e] using congrFun (colimitObjIsoColimitCompEvaluation_ι_inv G i (op (V a))) u
    have hs_eq :
        s a = ((colimit.ι G i).app (op (V a))) u := by
      have hs_eq' :
          s a = e.inv
            (colimit.ι
              (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op (V a))) i u) := by
        simpa [e] using hu'.symm
      exact hs_eq'.trans hrepr
    exact hs_eq.symm
  choose i u hu using hs
  let si : Finset I := Finset.univ.image i
  obtain ⟨k, hk⟩ := common_target_of_finite_stages si
  let f : ∀ a, i a ⟶ k := fun a ↦
    Classical.choice <|
      hk (i a) (by
        apply Finset.mem_image.mpr
        exact ⟨a, Finset.mem_univ a, rfl⟩)
  refine ⟨k, fun a ↦ ((𝓕.map (f a)).1.app (op (V a))) (u a), ?_⟩
  intro a
  -- Move the chosen representatives forward to the common stage and then compare with `s a`.
  have hnat :
      ((colimit.ι G k).app (op (V a))) (((G.map (f a)).app (op (V a))) (u a)) =
        ((colimit.ι G (i a)).app (op (V a))) (u a) := by
    exact congrFun
      (congrArg (fun η ↦ η.app (op (V a))) (colimit.w G (f a)))
      (u a)
  calc
    ((colimit.ι G k).app (op (V a))) (((𝓕.map (f a)).1.app (op (V a))) (u a))
        = ((colimit.ι G (i a)).app (op (V a))) (u a) := by
            simpa [G, Functor.comp_map, Category.assoc] using hnat
    _ = s a := hu a

/-- Helper for Lemma 6.29.1: restricting a represented section of the presheaf colimit produces the
represented restricted section at the same stage. This isolates the naturality rewrite needed in
the compact gluing argument. -/
theorem presheafColimit_map_ι_apply
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w)))
    [HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))]
    {U V : Opens X} (g : V ⟶ U) (k : I) (t : (𝓕.obj k).1.obj (op U)) :
    (@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))
        inferInstance).map g.op
        (((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op U)) t) =
      ((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op V))
        (((𝓕.obj k).1.map g.op) t) := by
  -- This is exactly the naturality square of the colimit injection, evaluated at `t`.
  simpa using (congrFun
    ((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).naturality g.op) t).symm

/-- Helper for Lemma 6.29.1: the filtered colimit of the underlying presheaves, packaged as a
named presheaf object so later theorem statements can refer to it without re-elaborating the raw
colimit term. -/
noncomputable def presheafColimitObject
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w)))
    [hcolimP : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))] :
    X.Presheaf (Type (max u v w)) :=
  @colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP

/-- Helper for Lemma 6.29.1: when `U` is compact, equality of two presheaf-colimit sections in the
sheafification already implies equality in the presheaf colimit. This is the compact finite-cover
version of the source proof’s local-equality synchronization argument. -/
theorem injective_toSheafify_app_of_isCompact_presheafColimit
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [hcolimP : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))]
    (hU : IsCompact (U : Set X)) :
    Function.Injective ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w))
      (@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP)).app (op U)) := by
  let G := 𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))
  let _ : HasColimit G := by
    simpa [G] using hcolimP
  let eU := colimitObjIsoColimitCompEvaluation G (op U)
  intro s t hst
  -- Put the two presheaf-colimit sections into one common source stage over `U`.
  obtain ⟨i, a, b, ha, hb⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (colimit.isColimit (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)))
      (eU.hom s) (eU.hom t)
  have hs_rep :
      s = ((colimit.ι G i).app (op U)) a := by
    have hs_eq := congrArg eU.inv ha
    have hrepr :
        eU.inv
            (colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) i a) =
          ((colimit.ι G i).app (op U)) a := by
      simpa [eU] using congrFun (colimitObjIsoColimitCompEvaluation_ι_inv G i (op U)) a
    simpa [hrepr] using hs_eq.symm
  have ht_rep :
      t = ((colimit.ι G i).app (op U)) b := by
    have ht_eq := congrArg eU.inv hb
    have hrepr :
        eU.inv
            (colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) i b) =
          ((colimit.ι G i).app (op U)) b := by
      simpa [eU] using congrFun (colimitObjIsoColimitCompEvaluation_ι_inv G i (op U)) b
    simpa [hrepr] using ht_eq.symm
  have hlocal :
      ∀ x : U, ∃ (V : Opens X) (hV : V ≤ U),
        (colimit G).map (homOfLE hV).op s = (colimit G).map (homOfLE hV).op t ∧ x.1 ∈ V := by
    intro x
    simpa [G] using
      local_eq_of_toSheafify_app_eq.{u, v, w}
        ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
          X.Presheaf (Type (max u v w)))
        U hst x.1 x.2
  choose V hV hEq hxV using hlocal
  -- Compactness reduces the local equalities to finitely many neighborhoods.
  obtain ⟨cover, hcover⟩ :=
    hU.elim_finite_subcover (fun x : U ↦ (V x : Set X))
      (fun x ↦ (V x).isOpen)
      (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using hxV ⟨x, hx⟩⟩)
  have hstage :
      ∀ x : U, ∃ (j : I) (f : i ⟶ j),
        ((𝓕.map f).1.app (op (V x))) (((𝓕.obj i).1.map (homOfLE (hV x)).op) a) =
          ((𝓕.map f).1.app (op (V x))) (((𝓕.obj i).1.map (homOfLE (hV x)).op) b) := by
    intro x
    let eV := colimitObjIsoColimitCompEvaluation G (op (V x))
    have hEq_colim :
        (colimit G).map (homOfLE (hV x)).op (((colimit.ι G i).app (op U)) a) =
          (colimit G).map (homOfLE (hV x)).op (((colimit.ι G i).app (op U)) b) := by
      simpa [hs_rep, ht_rep] using hEq x
    have hEq_eval :
        colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op (V x))) i
            (((𝓕.obj i).1.map (homOfLE (hV x)).op) a) =
          colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op (V x))) i
            (((𝓕.obj i).1.map (homOfLE (hV x)).op) b) := by
      have hEq_eval' := congrArg eV.hom hEq_colim
      have hleft :
          eV.hom ((colimit G).map (homOfLE (hV x)).op (((colimit.ι G i).app (op U)) a)) =
            colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op (V x))) i
              (((𝓕.obj i).1.map (homOfLE (hV x)).op) a) := by
        simpa [eV, G] using
          colimitObjIsoColimitCompEvaluation_hom_map_ι_apply G (homOfLE (hV x)) i a
      have hright :
          eV.hom ((colimit G).map (homOfLE (hV x)).op (((colimit.ι G i).app (op U)) b)) =
            colimit.ι (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op (V x))) i
              (((𝓕.obj i).1.map (homOfLE (hV x)).op) b) := by
        simpa [eV, G] using
          colimitObjIsoColimitCompEvaluation_hom_map_ι_apply G (homOfLE (hV x)) i b
      rw [hleft, hright] at hEq_eval'
      simpa [G] using hEq_eval'
    obtain ⟨j, f, hf⟩ :=
      (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
        (F := G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op (V x)))
        (t := colimit.cocone
          (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op (V x))))
        (ht := colimit.isColimit
          (G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op (V x))))
        (((𝓕.obj i).1.map (homOfLE (hV x)).op) a)
        (((𝓕.obj i).1.map (homOfLE (hV x)).op) b)).1 hEq_eval
    refine ⟨j, f, ?_⟩
    simpa [G, Functor.comp_map, Category.assoc] using hf
  choose j f hstage using hstage
  obtain ⟨k, g, hg⟩ := common_target_of_finite_maps_from cover j (fun x _ ↦ f x)
  have hlocal_k :
      ∀ x : {y // y ∈ cover},
        ((𝓕.obj k).1.map (homOfLE (hV x.1)).op) (((𝓕.map g).1.app (op U)) a) =
          ((𝓕.obj k).1.map (homOfLE (hV x.1)).op) (((𝓕.map g).1.app (op U)) b) := by
    intro x
    rcases hg x.1 x.2 with ⟨h, hh⟩
    have hx_stage := congrArg (((𝓕.map h).1.app (op (V x.1)))) (hstage x.1)
    have hx_stage_comp :
        ((𝓕.map (f x.1 ≫ h)).1.app (op (V x.1))) (((𝓕.obj i).1.map (homOfLE (hV x.1)).op) a) =
          ((𝓕.map (f x.1 ≫ h)).1.app (op (V x.1))) (((𝓕.obj i).1.map (homOfLE (hV x.1)).op) b) := by
      simpa [Functor.map_comp, Category.assoc] using hx_stage
    have hx_stage' :
        ((𝓕.map g).1.app (op (V x.1))) (((𝓕.obj i).1.map (homOfLE (hV x.1)).op) a) =
          ((𝓕.map g).1.app (op (V x.1))) (((𝓕.obj i).1.map (homOfLE (hV x.1)).op) b) := by
      simpa [hh] using hx_stage_comp
    calc
      ((𝓕.obj k).1.map (homOfLE (hV x.1)).op) (((𝓕.map g).1.app (op U)) a)
          = ((𝓕.map g).1.app (op (V x.1))) (((𝓕.obj i).1.map (homOfLE (hV x.1)).op) a) := by
              symm
              exact sheaf_transition_app_map_eq_map_app 𝓕 g (homOfLE (hV x.1)) a
      _ = ((𝓕.map g).1.app (op (V x.1))) (((𝓕.obj i).1.map (homOfLE (hV x.1)).op) b) :=
            hx_stage'
      _ = ((𝓕.obj k).1.map (homOfLE (hV x.1)).op) (((𝓕.map g).1.app (op U)) b) := by
            exact sheaf_transition_app_map_eq_map_app 𝓕 g (homOfLE (hV x.1)) b
  have hcover_opens :
      U ≤ iSup (fun x : {y // y ∈ cover} ↦ V x.1) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hcover hx) with ⟨y, hy, hxy⟩
    exact (Opens.mem_iSup).2 ⟨⟨y, hy⟩, hxy⟩
  have hab_k :
      ((𝓕.map g).1.app (op U)) a = ((𝓕.map g).1.app (op U)) b := by
    -- The common target stage is a sheaf, so local equality on the finite cover forces global
    -- equality over `U`.
    refine (𝓕.obj k).eq_of_locally_eq'
      (U := fun x : {y // y ∈ cover} ↦ V x.1)
      (V := U)
      (fun x ↦ homOfLE (hV x.1))
      hcover_opens
      (((𝓕.map g).1.app (op U)) a)
      (((𝓕.map g).1.app (op U)) b)
      hlocal_k
  let GU := G ⋙ (evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)
  have hga :
      colimit.ι GU i a =
        colimit.ι GU k (((𝓕.map g).1.app (op U)) a) := by
    simpa [GU, G, Functor.comp_map, Category.assoc] using
      (congrFun (colimit.w GU g) a).symm
  have hgb :
      colimit.ι GU i b =
        colimit.ι GU k (((𝓕.map g).1.app (op U)) b) := by
    simpa [GU, G, Functor.comp_map, Category.assoc] using
      (congrFun (colimit.w GU g) b).symm
  have h_eU_inj : Function.Injective eU.hom := by
    exact ((CategoryTheory.isIso_iff_bijective eU.hom).1
      (show IsIso eU.hom by infer_instance)).1
  -- Equality in the synchronized stage gives equality in the evaluation-side filtered colimit.
  apply h_eU_inj
  calc
    eU.hom s = colimit.ι GU i a := ha.symm
    _ = colimit.ι GU k (((𝓕.map g).1.app (op U)) a) := hga
    _ = colimit.ι GU k (((𝓕.map g).1.app (op U)) b) := by rw [hab_k]
    _ = colimit.ι GU i b := hgb.symm
    _ = eU.hom t := hb

/-- Helper for Lemma 6.29.1: evaluating the section-comparison map on an open `U` gives the
sheafification unit on the presheaf colimit, followed by the canonical comparison isomorphism on
sections. This is the concrete rewrite used in all four clauses. -/
theorem colimit_post_eq_toSheafify_comparison_app
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [hcolim : HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))]
    [HasColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op U))] :
    colimit.post 𝓕 ((sheafSections JX (Type (max u v w))).obj (op U)) =
      colimit.post (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))
          ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) ≫
        (CategoryTheory.toSheafify JX
          (colimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))))).app (op U) ≫
        ((presheafColimitToSheafIso 𝓕).hom.1.app (op U)) := by
  -- First rewrite the source comparison as evaluation of the presheaf-colimit comparison.
  rw [section_colimit_post_eq_eval]
  -- Then evaluate the presheaf-side factorization through sheafification at `U`.
  have hfactor :
      (colimit.post 𝓕 (sheafToPresheaf JX (Type (max u v w)))).app (op U) =
        (CategoryTheory.toSheafify JX
            (colimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))))).app (op U) ≫
          ((presheafColimitToSheafIso 𝓕).hom.1.app (op U)) := by
    simpa [Category.assoc, presheafColimitToSheafIso] using
      (congrArg (fun f ↦ f.app (op U))
        (presheaf_colimit_comparison_factorization 𝓕)).symm
  rw [hfactor]
  rfl

/-- Lemma 6.29.1 (1): if all transition maps are monomorphisms, equivalently pointwise injective on
the sections of every open subset, then the canonical map from the colimit of sections over `U` to
the sections of the colimit sheaf over `U` is injective. -/
theorem injective_sheafColimitSectionComparison_of_transitionMapsInjective
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op U))]
    (hmono : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (𝓕.map f)) :
    Function.Injective (colimit.post 𝓕 ((sheafSections JX (Type (max u v w))).obj (op U))) := by
  let hcolimP : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) :=
    functorCategoryHasColimit _
  let P : (Opens X)ᵒᵖ ⥤ Type (max u v w) :=
    @colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP
  let _ : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) := hcolimP
  -- Route correction: the source proof factors the comparison through presheaf sheafification, so
  -- rewrite the map into that form and then compose injective factors.
  rw [colimit_post_eq_toSheafify_comparison_app]
  let eU :=
    colimitObjIsoColimitCompEvaluation
      (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) (op U)
  have h_eval :
      Function.Injective
        (colimit.post (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))
          ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U))) := by
    -- Evaluation commutes with the colimit of the presheaf diagram via the standard comparison
    -- isomorphism `eU`.
    have hpost :
        colimit.post (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))
            ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) =
          eU.inv := by
      apply colimit.hom_ext
      intro i
      rw [colimit.ι_post]
      simpa [eU] using
        (colimitObjIsoColimitCompEvaluation_ι_inv
          (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) i (op U)).symm
    rw [hpost]
    exact ((CategoryTheory.isIso_iff_bijective eU.inv).1
      (show IsIso eU.inv by infer_instance)).1
  have h_sheafify :
      Function.Injective
        ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op U)) := by
    -- The presheaf colimit is separated under injective transition maps, so the sheafification
    -- unit is injective on sections.
    have hPsep : Presieve.IsSeparated JX P := by
      let _ : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) := hcolimP
      simpa [P] using separated_presheafColimit_of_transitionMapsInjective (𝓕 := 𝓕) hmono
    have h_toPlus_inj :
        Function.Injective ((GrothendieckTopology.toPlus (J := JX) P).app (op U)) := by
      exact CategoryTheory.GrothendieckTopology.Plus.inj_of_sep (J := JX) (P := P)
        (fun V S x y hxy => by
          refine (hPsep S.1 S.2).ext ?_
          intro Y f hf
          exact hxy ⟨Y, f, hf⟩) U
    have hsheaf_plus : Presheaf.IsSheaf JX (GrothendieckTopology.plusObj (J := JX) P) := by
      exact CategoryTheory.GrothendieckTopology.Plus.isSheaf_of_sep (J := JX) (P := P)
        (fun V S x y hxy => by
          refine (hPsep S.1 S.2).ext ?_
          intro Y f hf
          exact hxy ⟨Y, f, hf⟩)
    have h_second_inj :
        Function.Injective ((GrothendieckTopology.toPlus (J := JX)
          (GrothendieckTopology.plusObj (J := JX) P)).app (op U)) := by
      let hIso :
          IsIso (GrothendieckTopology.toPlus (J := JX)
            (GrothendieckTopology.plusObj (J := JX) P)) :=
        GrothendieckTopology.isIso_toPlus_of_isSheaf (J := JX)
          (P := GrothendieckTopology.plusObj (J := JX) P) hsheaf_plus
      exact ((CategoryTheory.isIso_iff_bijective _).1
        ((NatTrans.isIso_iff_isIso_app _).1 hIso (op U))).1
    have h_concrete :
        Function.Injective ((GrothendieckTopology.toSheafify (J := JX) P).app (op U)) := by
      rw [GrothendieckTopology.toSheafify, GrothendieckTopology.plusMap_toPlus]
      intro s t hst
      apply h_toPlus_inj
      apply h_second_inj
      exact hst
    have hfac :
        GrothendieckTopology.toSheafify (J := JX) P =
          CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P ≫
            (plusPlusIsoSheafify JX (Type (max u v w)) P).inv := by
      rw [CategoryTheory.Iso.eq_comp_inv]
      simpa using
        (CategoryTheory.toSheafify_plusPlusIsoSheafify_hom
          (J := JX) (D := Type (max u v w)) P)
    intro s t hst
    apply h_concrete
    have hst' := congrArg (((plusPlusIsoSheafify JX (Type (max u v w)) P).inv.app (op U))) hst
    simpa [hfac, Category.assoc] using hst'
  have h_iso :
      Function.Injective (((presheafColimitToSheafIso 𝓕).hom.1.app (op U))) := by
    -- The final comparison to the chosen sheaf colimit is an isomorphism on sections.
    let hIsoNat :
        IsIso ((TopCat.Sheaf.forget (Type (max u v w)) X).map
          (presheafColimitToSheafIso 𝓕).hom) := by
      infer_instance
    exact ((CategoryTheory.isIso_iff_bijective
      ((presheafColimitToSheafIso 𝓕).hom.1.app (op U))).1
        ((NatTrans.isIso_iff_isIso_app _).1 hIsoNat (op U))).1
  intro s t hst
  apply h_eval
  apply h_sheafify
  apply h_iso
  exact hst

/-- Lemma 6.29.1 (2): if `U` is quasi-compact, then the canonical map from the colimit of sections
over `U` to the sections of the colimit sheaf over `U` is injective. -/
theorem injective_sheafColimitSectionComparison_of_isCompact
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op U))]
    (hU : IsCompact (U : Set X)) :
    Function.Injective (colimit.post 𝓕 ((sheafSections JX (Type (max u v w))).obj (op U))) := by
  let hcolimP : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) :=
    functorCategoryHasColimit _
  let P : X.Presheaf (Type (max u v w)) :=
    @colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP
  let _ : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) := hcolimP
  -- Route correction: clause (2) rewrites the comparison map to the sheafification unit on the
  -- presheaf colimit, applies the compact finite-cover argument there, and then transports back.
  rw [colimit_post_eq_toSheafify_comparison_app]
  let eU :=
    colimitObjIsoColimitCompEvaluation
      (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) (op U)
  have h_eval :
      Function.Injective
        (colimit.post (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))
          ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U))) := by
    -- Evaluation commutes with the presheaf colimit via the standard comparison isomorphism.
    have hpost :
        colimit.post (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))
            ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) =
          eU.inv := by
      apply colimit.hom_ext
      intro i
      rw [colimit.ι_post]
      simpa [eU] using
        (colimitObjIsoColimitCompEvaluation_ι_inv
          (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) i (op U)).symm
    rw [hpost]
    exact ((CategoryTheory.isIso_iff_bijective eU.inv).1
      (show IsIso eU.inv by infer_instance)).1
  have h_sheafify :
      Function.Injective ((CategoryTheory.toSheafify JX P).app (op U)) := by
    -- The compact-source argument is exactly the finite local-equality synchronization in the
    -- helper theorem proved above.
    simpa [P] using injective_toSheafify_app_of_isCompact_presheafColimit 𝓕 U hU
  have h_iso :
      Function.Injective (((presheafColimitToSheafIso 𝓕).hom.1.app (op U))) := by
    -- The final comparison to the chosen sheaf colimit is an isomorphism on sections.
    let hIsoNat :
        IsIso ((TopCat.Sheaf.forget (Type (max u v w)) X).map
          (presheafColimitToSheafIso 𝓕).hom) := by
      infer_instance
    exact ((CategoryTheory.isIso_iff_bijective
      ((presheafColimitToSheafIso 𝓕).hom.1.app (op U))).1
        ((NatTrans.isIso_iff_isIso_app _).1 hIsoNat (op U))).1
  intro s t hst
  apply h_eval
  apply h_sheafify
  apply h_iso
  exact hst

/-- Helper for Lemma 6.29.1: under injective transition maps, equality of two same-stage colimit
classes already holds in that stage. -/
theorem same_stage_eq_of_equal_colimit_images_of_transitionMapsInjective
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (V : Opens X)
    [HasColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op V))]
    (hmono : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (𝓕.map f))
    {i : I} {a b : (𝓕.obj i).1.obj (op V)}
    (heq :
      colimit.ι (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op V)) i a =
        colimit.ι (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op V)) i b) :
    a = b := by
  -- The filtered-colimit equality criterion reduces equality of classes from one stage to equality
  -- after one later transition map, and monomorphy cancels that map on sections.
  obtain ⟨j, f, hf⟩ :=
    (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
      (F := 𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op V))
      (t := colimit.cocone (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op V)))
      (ht := colimit.isColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op V))) a b).1 heq
  have hinj : Function.Injective ((𝓕.map f).1.app (op V)) :=
    (sheaf_mono_iff_app_injective (𝓕.map f)).1 (hmono f) V
  exact hinj (by simpa using hf)

/-- Helper for Lemma 6.29.1: if two same-stage local representatives of one sheafified section
agree after applying `toSheafify`, then their represented restrictions to a common overlap already
agree in the presheaf colimit. -/
theorem equal_colimit_overlap_restrictions_of_common_stage_lifts
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w)))
    [hcolimP : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))]
    {U V₁ V₂ W : Opens X}
    (hV₁ : V₁ ≤ U) (hV₂ : V₂ ≤ U)
    (hW₁ : W ≤ V₁) (hW₂ : W ≤ V₂)
    {z : ((presheafToSheaf JX (Type (max u v w))).obj
      ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
        X.Presheaf (Type (max u v w)))).1.obj (op U)}
    {k : I}
    {t₁ : (𝓕.obj k).1.obj (op V₁)} {t₂ : (𝓕.obj k).1.obj (op V₂)}
    (hinj : Function.Injective
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w))
        ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
          X.Presheaf (Type (max u v w)))).app (op W)))
    (hs₁ :
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w))
          ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
            X.Presheaf (Type (max u v w)))).app (op V₁))
          (((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op V₁)) t₁) =
        ((presheafToSheaf JX (Type (max u v w))).obj
          ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
            X.Presheaf (Type (max u v w)))).1.map
          (homOfLE hV₁).op z)
    (hs₂ :
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w))
          ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
            X.Presheaf (Type (max u v w)))).app (op V₂))
          (((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op V₂)) t₂) =
        ((presheafToSheaf JX (Type (max u v w))).obj
          ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
            X.Presheaf (Type (max u v w)))).1.map
          (homOfLE hV₂).op z) :
    ((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op W))
        (((𝓕.obj k).1.map (homOfLE hW₁).op) t₁) =
      ((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op W))
        (((𝓕.obj k).1.map (homOfLE hW₂).op) t₂) := by
  let P : X.Presheaf (Type (max u v w)) :=
    ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
      X.Presheaf (Type (max u v w)))
  let Sh : X.Sheaf (Type (max u v w)) := (presheafToSheaf JX (Type (max u v w))).obj P
  have hs₁W :
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W))
          (P.map (homOfLE hW₁).op
            (((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op V₁)) t₁)) =
        Sh.1.map (homOfLE (le_trans hW₁ hV₁)).op z := by
    -- Restrict the first local lift to the overlap.
    exact refined_local_preimage_restriction_eq.{u, v, w} (P := P) hV₁ hW₁ hs₁
  have hs₂W :
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W))
          (P.map (homOfLE hW₂).op
            (((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op V₂)) t₂)) =
        Sh.1.map (homOfLE (le_trans hW₂ hV₂)).op z := by
    -- Restrict the second local lift to the same overlap.
    exact refined_local_preimage_restriction_eq.{u, v, w} (P := P) hV₂ hW₂ hs₂
  have hzW :
      Sh.1.map (homOfLE (le_trans hW₁ hV₁)).op z =
        Sh.1.map (homOfLE (le_trans hW₂ hV₂)).op z := by
    -- Both composite inclusions `W ⟶ U` are equal in the thin category of opens.
    simpa using congrArg (fun f : W ⟶ U ↦ Sh.1.map f.op z)
      (Subsingleton.elim
        (homOfLE (le_trans hW₁ hV₁) : W ⟶ U)
        (homOfLE (le_trans hW₂ hV₂) : W ⟶ U))
  apply hinj
  -- After restricting both local lifts, both sides become the same restriction of `z`.
  calc
    ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W))
        (((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op W))
          (((𝓕.obj k).1.map (homOfLE hW₁).op) t₁))
      =
        ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W))
          (P.map (homOfLE hW₁).op
            (((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op V₁)) t₁)) := by
              simpa [P] using congrArg
                (((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W)))
                (presheafColimit_map_ι_apply
                  (𝓕 := 𝓕) (g := homOfLE hW₁) (k := k) (t := t₁)).symm
    _ = Sh.1.map (homOfLE (le_trans hW₁ hV₁)).op z := hs₁W
    _ = Sh.1.map (homOfLE (le_trans hW₂ hV₂)).op z := hzW
    _ =
        ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W))
          (P.map (homOfLE hW₂).op
            (((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op V₂)) t₂)) := by
              exact hs₂W.symm
    _ =
        ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W))
          (((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op W))
            (((𝓕.obj k).1.map (homOfLE hW₂).op) t₂)) := by
              simpa [P] using congrArg
                (((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W)))
                (presheafColimit_map_ι_apply
                  (𝓕 := 𝓕) (g := homOfLE hW₂) (k := k) (t := t₂))

/-- Helper for Lemma 6.29.1: under injective transition maps, same-stage local lifts of one
sheafified section agree on every overlap after restricting to that overlap. -/
theorem same_stage_overlap_compatibility_of_equal_toSheafify_restrictions
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w)))
    [hcolimP : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))]
    {U V₁ V₂ W : Opens X}
    (hV₁ : V₁ ≤ U) (hV₂ : V₂ ≤ U)
    (hW₁ : W ≤ V₁) (hW₂ : W ≤ V₂)
    (hmono : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (𝓕.map f))
    {z : ((presheafToSheaf JX (Type (max u v w))).obj
      ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
        X.Presheaf (Type (max u v w)))).1.obj (op U)}
    {k : I}
    {t₁ : (𝓕.obj k).1.obj (op V₁)} {t₂ : (𝓕.obj k).1.obj (op V₂)}
    (hs₁ :
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w))
          ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
            X.Presheaf (Type (max u v w)))).app (op V₁))
          (((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op V₁)) t₁) =
        ((presheafToSheaf JX (Type (max u v w))).obj
          ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
            X.Presheaf (Type (max u v w)))).1.map
          (homOfLE hV₁).op z)
    (hs₂ :
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w))
          ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
            X.Presheaf (Type (max u v w)))).app (op V₂))
          (((colimit.ι (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) k).app (op V₂)) t₂) =
        ((presheafToSheaf JX (Type (max u v w))).obj
          ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
            X.Presheaf (Type (max u v w)))).1.map
          (homOfLE hV₂).op z) :
    ((𝓕.obj k).1.map (homOfLE hW₁).op) t₁ =
      ((𝓕.obj k).1.map (homOfLE hW₂).op) t₂ := by
  let P : X.Presheaf (Type (max u v w)) :=
    ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
      X.Presheaf (Type (max u v w)))
  let G : I ⥤ X.Presheaf (Type (max u v w)) := 𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))
  let eW := colimitObjIsoColimitCompEvaluation G (op W)
  have hsep : Presieve.IsSeparated JX P := by
    -- Injective transition maps make the presheaf colimit separated.
    simpa [P] using separated_presheafColimit_of_transitionMapsInjective (𝓕 := 𝓕) hmono
  have hinj :
      Function.Injective
        ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W)) := by
    -- Then the sheafification unit is injective on the overlap.
    exact injective_toSheafify_app_of_isSeparated.{u, v, w} P hsep W
  have hcolim_eq :
      ((colimit.ι G k).app (op W)) (((𝓕.obj k).1.map (homOfLE hW₁).op) t₁) =
        ((colimit.ι G k).app (op W)) (((𝓕.obj k).1.map (homOfLE hW₂).op) t₂) := by
    -- Apply the generic overlap package with injectivity supplied by separatedness.
    exact equal_colimit_overlap_restrictions_of_common_stage_lifts.{u, v, w}
      (𝓕 := 𝓕) hV₁ hV₂ hW₁ hW₂ hinj hs₁ hs₂
  have h_eval_eq :
      colimit.ι (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op W)) k
          (((𝓕.obj k).1.map (homOfLE hW₁).op) t₁) =
        colimit.ι (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op W)) k
          (((𝓕.obj k).1.map (homOfLE hW₂).op) t₂) := by
    -- Move the colimit equality to the evaluation-side filtered colimit over `W`.
    have hleft :
        eW.hom
            (((colimit.ι G k).app (op W)) (((𝓕.obj k).1.map (homOfLE hW₁).op) t₁)) =
          colimit.ι (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op W)) k
            (((𝓕.obj k).1.map (homOfLE hW₁).op) t₁) := by
      simpa [G, eW] using
        congrFun (colimitObjIsoColimitCompEvaluation_ι_app_hom G k (op W))
          (((𝓕.obj k).1.map (homOfLE hW₁).op) t₁)
    have hright :
        eW.hom
            (((colimit.ι G k).app (op W)) (((𝓕.obj k).1.map (homOfLE hW₂).op) t₂)) =
          colimit.ι (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op W)) k
            (((𝓕.obj k).1.map (homOfLE hW₂).op) t₂) := by
      simpa [G, eW] using
        congrFun (colimitObjIsoColimitCompEvaluation_ι_app_hom G k (op W))
          (((𝓕.obj k).1.map (homOfLE hW₂).op) t₂)
    rw [← hleft, ← hright]
    exact congrArg eW.hom hcolim_eq
  -- Finally cancel the common-stage colimit class using injectivity of the transition maps.
  exact same_stage_eq_of_equal_colimit_images_of_transitionMapsInjective 𝓕 W hmono h_eval_eq

-- Lemma 6.29.1 (3): if `U` is quasi-compact and all transition maps are injective, then the
-- canonical comparison map is an isomorphism. The transition-map hypothesis is stated canonically as
-- monomorphy in the sheaf category.
/-- Helper for Lemma 6.29.1: under compactness and injective transition maps, the sheafification
unit on the presheaf colimit is surjective on sections over `U`. This is the source proof’s
finite-cover gluing step before transporting back to the chosen sheaf colimit. -/
theorem surjective_toSheafify_app_of_isCompact_presheafColimit_of_transitionMapsInjective
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [hcolimP : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))]
    (hU : IsCompact (U : Set X))
    (hmono : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (𝓕.map f)) :
    Function.Surjective ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w))
      (@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP)).app (op U)) := by
  classical
  let P : X.Presheaf (Type (max u v w)) :=
    ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
      X.Presheaf (Type (max u v w)))
  let G : I ⥤ X.Presheaf (Type (max u v w)) := 𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))
  let Sh : X.Sheaf (Type (max u v w)) := (presheafToSheaf JX (Type (max u v w))).obj P
  intro z
  have hlocal :
      ∀ x : U, ∃ (V : Opens X) (hV : V ≤ U) (s : P.obj (op V)),
        ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op V)) s =
          Sh.1.map (homOfLE hV).op z ∧ x.1 ∈ V := by
    -- Every target section is locally represented by a presheaf-colimit section.
    simpa [P, Sh] using local_preimage_of_toSheafify_app.{u, v, w} P U z
  choose V hV s hs hx using hlocal
  obtain ⟨cover, hcover⟩ :=
    hU.elim_finite_subcover (fun x : U ↦ (V x : Set X))
      (fun x ↦ (V x).isOpen)
      (by
        intro x hxU
        exact Set.mem_iUnion.mpr ⟨⟨x, hxU⟩, by simpa using hx ⟨x, hxU⟩⟩)
  obtain ⟨k, t, ht⟩ :=
    common_stage_of_finite_local_colimit_sections
      (𝓕 := 𝓕)
      (V := fun x : cover ↦ V x.1)
      (s := fun x : cover ↦ s x.1)
  have hcover_opens :
      U ≤ iSup (fun x : cover ↦ V x.1) := by
    intro x hxU
    rcases Set.mem_iUnion₂.mp (hcover hxU) with ⟨y, hy, hxy⟩
    exact (Opens.mem_iSup).2 ⟨⟨y, hy⟩, hxy⟩
  have hs_common :
      ∀ x : cover,
        ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op (V x.1)))
            (((colimit.ι G k).app (op (V x.1))) (t x)) =
          Sh.1.map (homOfLE (hV x.1)).op z := by
    intro x
    -- Replace the chosen common-stage representative by the original local one.
    simpa [G] using (ht x).symm ▸ hs x.1
  have hcompat : TopCat.Presheaf.IsCompatible (𝓕.obj k).1 (fun x : cover ↦ V x.1) t := by
    intro x y
    -- Over every overlap, the two common-stage lifts agree because they represent the same
    -- sheafified section and the transition maps are injective.
    exact same_stage_overlap_compatibility_of_equal_toSheafify_restrictions
      (𝓕 := 𝓕)
      (hV₁ := hV x.1) (hV₂ := hV y.1)
      (hW₁ := inf_le_left) (hW₂ := inf_le_right)
      (hmono := hmono)
      (hs₁ := hs_common x)
      (hs₂ := hs_common y)
  obtain ⟨gl, hgl, -⟩ := (𝓕.obj k).existsUnique_gluing'
    (U := fun x : cover ↦ V x.1)
    (V := U)
    (iUV := fun x ↦ homOfLE (hV x.1))
    hcover_opens t hcompat
  refine ⟨((colimit.ι G k).app (op U)) gl, ?_⟩
  have hglue_image :
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op U))
          (((colimit.ι G k).app (op U)) gl) = z := by
    -- Compare the glued section and `z` on the finite cover and invoke the sheaf uniqueness
    -- principle in the target sheafification.
    apply Sh.eq_of_locally_eq'
      (U := fun x : cover ↦ V x.1)
      (V := U)
      (iUV := fun x ↦ homOfLE (hV x.1))
      hcover_opens
    intro x
    calc
      Sh.1.map (homOfLE (hV x.1)).op
          (((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op U))
            (((colimit.ι G k).app (op U)) gl))
        =
          ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op (V x.1)))
            (P.map (homOfLE (hV x.1)).op (((colimit.ι G k).app (op U)) gl)) := by
              exact (congrFun
                (((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).naturality
                  (homOfLE (hV x.1)).op)) (((colimit.ι G k).app (op U)) gl)).symm
      _ =
          ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op (V x.1)))
            (((colimit.ι G k).app (op (V x.1)))
              (((𝓕.obj k).1.map (homOfLE (hV x.1)).op) gl)) := by
                simpa [P, G] using congrArg
                  (((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app
                    (op (V x.1))))
                  (presheafColimit_map_ι_apply
                    (𝓕 := 𝓕) (g := homOfLE (hV x.1)) (k := k) (t := gl))
      _ =
          ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op (V x.1)))
            (((colimit.ι G k).app (op (V x.1))) (t x)) := by
              simpa [G] using congrArg
                (fun u ↦ ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app
                  (op (V x.1))) (((colimit.ι G k).app (op (V x.1))) u))
                (hgl x)
      _ = Sh.1.map (homOfLE (hV x.1)).op z := hs_common x
  simpa [P] using hglue_image

/-- Lemma 6.29.1 (3): if `U` is quasi-compact and all transition maps are injective, then the
canonical comparison map is an isomorphism. The transition-map hypothesis is stated canonically as
monomorphy in the sheaf category. -/
theorem isIso_sheafColimitSectionComparison_of_isCompact_of_transitionMapsInjective
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op U))]
    (hU : IsCompact (U : Set X))
    (hmono : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (𝓕.map f)) :
    IsIso (colimit.post 𝓕 ((sheafSections JX (Type (max u v w))).obj (op U))) := by
  let hcolimP : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) :=
    functorCategoryHasColimit _
  let P : X.Presheaf (Type (max u v w)) :=
    @colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP
  let _ : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) := hcolimP
  -- Route correction: the compact injective half is finished, so clause (3) reduces to
  -- surjectivity of the sheafification unit on the presheaf colimit and transport across the two
  -- comparison isomorphisms.
  rw [CategoryTheory.isIso_iff_bijective]
  rw [colimit_post_eq_toSheafify_comparison_app]
  let eU :=
    colimitObjIsoColimitCompEvaluation
      (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) (op U)
  have h_eval :
      Function.Bijective
        (colimit.post (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))
          ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U))) := by
    -- Evaluation commutes with the presheaf colimit via the standard comparison isomorphism.
    have hpost :
        colimit.post (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))
            ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) =
          eU.inv := by
      apply colimit.hom_ext
      intro i
      rw [colimit.ι_post]
      simpa [eU] using
        (colimitObjIsoColimitCompEvaluation_ι_inv
          (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) i (op U)).symm
    rw [hpost]
    exact (CategoryTheory.isIso_iff_bijective eU.inv).1
      (show IsIso eU.inv by infer_instance)
  have h_sheafify :
      Function.Bijective ((CategoryTheory.toSheafify JX P).app (op U)) := by
    refine ⟨?_, ?_⟩
    · -- The injective half is the compact finite-cover argument already proved above.
      simpa [P] using injective_toSheafify_app_of_isCompact_presheafColimit 𝓕 U hU
    · -- The remaining source-proof step is exactly the finite-cover gluing lemma isolated above.
      simpa [P] using
        surjective_toSheafify_app_of_isCompact_presheafColimit_of_transitionMapsInjective
          𝓕 U hU hmono
  have h_iso :
      Function.Bijective (((presheafColimitToSheafIso 𝓕).hom.1.app (op U))) := by
    -- The final comparison to the chosen sheaf colimit is an isomorphism on sections.
    let hIsoNat :
        IsIso ((TopCat.Sheaf.forget (Type (max u v w)) X).map
          (presheafColimitToSheafIso 𝓕).hom) := by
      infer_instance
    exact (CategoryTheory.isIso_iff_bijective
      ((presheafColimitToSheafIso 𝓕).hom.1.app (op U))).1
        ((NatTrans.isIso_iff_isIso_app _).1 hIsoNat (op U))
  constructor
  · intro s t hst
    exact h_eval.1 (h_sheafify.1 (h_iso.1 hst))
  · intro z
    rcases h_iso.2 z with ⟨z', rfl⟩
    rcases h_sheafify.2 z' with ⟨y, rfl⟩
    rcases h_eval.2 y with ⟨x, rfl⟩
    exact ⟨x, rfl⟩

-- TODO: apply the local finite-refinement hypothesis to the cover arising from local surjectivity
-- of sheafification, use part (2) on compact overlaps to synchronize the local representatives in a
-- common stage, and then glue those representatives over the finite refinement.
/-- Helper for Lemma 6.29.1: if `U` admits cofinal finite refinements with compact pairwise
overlaps, then the sheafification unit on the presheaf colimit is surjective on sections over
`U`. This is the source proof’s finite-refinement gluing step for clause (4). -/
theorem surjective_toSheafify_app_of_cofinalFiniteQuasiCompactOverlapCoverings
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [hcolimP : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))]
    (hU : HasCofinalFiniteQuasiCompactOverlapCoverings JX U) :
    Function.Surjective ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w))
      ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
        X.Presheaf (Type (max u v w)))).app (op U)) := by
  classical
  let P : X.Presheaf (Type (max u v w)) :=
    ((@colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP) :
      X.Presheaf (Type (max u v w)))
  let G : I ⥤ X.Presheaf (Type (max u v w)) := 𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))
  let _ : HasColimit G := by
    simpa [G] using hcolimP
  let Sh : X.Sheaf (Type (max u v w)) := (presheafToSheaf JX (Type (max u v w))).obj P
  intro z
  have hlocal :
      ∀ x : U, ∃ (V : Opens X) (hV : V ≤ U) (s : P.obj (op V)),
        ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op V)) s =
          Sh.1.map (homOfLE hV).op z ∧ x.1 ∈ V := by
    -- Local surjectivity of sheafification produces neighborhood-wise lifts of `z`.
    simpa [P, Sh] using local_preimage_of_toSheafify_app.{u, v, w} P U z
  choose V hV s hs hx using hlocal
  obtain ⟨cover, hcover_le, hcover_refine, hcover_cover, hcover_compact⟩ :=
    hU.finite_refinement V (fun x ↦ hV x) (fun x ↦ ⟨x, hx x⟩)
  choose base hbase using fun W : cover ↦ hcover_refine W.1 W.2
  let iU : ∀ W : cover, W.1 ≤ U := fun W ↦ le_trans (hbase W) (hV (base W))
  let localSection : ∀ W : cover, P.obj (op W.1) := fun W ↦
    P.map (homOfLE (hbase W)).op (s (base W))
  let localSectionRaw : ∀ W : cover, (colimit G).obj (op W.1) := fun W ↦ by
    simpa [P, G, localSection] using localSection W
  have hlocalSection :
      ∀ W : cover,
        ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W.1))
            (localSection W) =
          Sh.1.map (homOfLE (iU W)).op z := by
    intro W
    -- Shrink the chosen local lift down to the refined open `W`.
    simpa [localSection, iU] using
      refined_local_preimage_restriction_eq.{u, v, w}
        (P := P) (hV (base W)) (hbase W) (hs (base W))
  have hlocalSectionRaw :
      ∀ W : cover,
        ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w))
            ((colimit G : X.Presheaf (Type (max u v w))))).app (op W.1))
            (localSectionRaw W) =
          Sh.1.map (homOfLE (iU W)).op z := by
    intro W
    simpa [localSectionRaw, P, G] using hlocalSection W
  obtain ⟨k, t, ht⟩ :=
    common_stage_of_finite_local_colimit_sections
      (𝓕 := 𝓕)
      (V := fun W : cover ↦ W.1)
      (s := localSectionRaw)
  have hpair :
      ∀ p : cover × cover, ∃ j : I, ∃ f : k ⟶ j,
        ((𝓕.map f).1.app (op (p.1.1 ⊓ p.2.1)))
            (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t p.1)) =
          ((𝓕.map f).1.app (op (p.1.1 ⊓ p.2.1)))
            (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t p.2)) := by
    intro p
    have hoverlap_inj :
        Function.Injective
          ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w))
              ((colimit G : X.Presheaf (Type (max u v w))))).app
            (op (p.1.1 ⊓ p.2.1))) := by
      -- Clause (2) applies on each compact overlap of the refinement.
      simpa [P, G] using
        injective_toSheafify_app_of_isCompact_presheafColimit
          (𝓕 := 𝓕) (U := p.1.1 ⊓ p.2.1) (hU := hcover_compact p.1.1 p.1.2 p.2.1 p.2.2)
    have hcolim_eq :
        ((colimit.ι G k).app (op (p.1.1 ⊓ p.2.1)))
            (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t p.1)) =
          ((colimit.ι G k).app (op (p.1.1 ⊓ p.2.1)))
            (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t p.2)) := by
      -- The two refined local lifts represent the same overlap section of the sheafification.
      exact equal_colimit_overlap_restrictions_of_common_stage_lifts.{u, v, w}
        (𝓕 := 𝓕)
        (hV₁ := iU p.1) (hV₂ := iU p.2)
        (hW₁ := inf_le_left) (hW₂ := inf_le_right)
        (hinj := hoverlap_inj)
        (hs₁ := (ht p.1).symm ▸ hlocalSectionRaw p.1)
        (hs₂ := (ht p.2).symm ▸ hlocalSectionRaw p.2)
    let eW := colimitObjIsoColimitCompEvaluation G (op (p.1.1 ⊓ p.2.1))
    have hcolim_eval :
        colimit.ι (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op (p.1.1 ⊓ p.2.1))) k
            (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t p.1)) =
          colimit.ι (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op (p.1.1 ⊓ p.2.1))) k
            (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t p.2)) := by
      have hleft :
          eW.hom
              (((colimit.ι G k).app (op (p.1.1 ⊓ p.2.1)))
                (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t p.1))) =
            colimit.ι (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op (p.1.1 ⊓ p.2.1))) k
              (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t p.1)) := by
        simpa [G, eW] using
          congrFun (colimitObjIsoColimitCompEvaluation_ι_app_hom G k (op (p.1.1 ⊓ p.2.1)))
            (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t p.1))
      have hright :
          eW.hom
              (((colimit.ι G k).app (op (p.1.1 ⊓ p.2.1)))
                (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t p.2))) =
            colimit.ι (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op (p.1.1 ⊓ p.2.1))) k
              (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t p.2)) := by
        simpa [G, eW] using
          congrFun (colimitObjIsoColimitCompEvaluation_ι_app_hom G k (op (p.1.1 ⊓ p.2.1)))
            (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t p.2))
      rw [← hleft, ← hright]
      exact congrArg eW.hom hcolim_eq
    obtain ⟨j, f, hf⟩ :=
      (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
        (F := 𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op (p.1.1 ⊓ p.2.1)))
        (t := colimit.cocone
          (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op (p.1.1 ⊓ p.2.1))))
        (ht := colimit.isColimit
          (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op (p.1.1 ⊓ p.2.1))))
        (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t p.1))
        (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t p.2))).1 hcolim_eval
    refine ⟨j, f, ?_⟩
    simpa [Functor.comp_map, Category.assoc] using hf
  choose j f hpairEq using hpair
  let _ : Fintype (cover × cover) := by infer_instance
  obtain ⟨K, g, hg⟩ :=
    common_target_of_finite_maps_from
      (s := (Finset.univ : Finset (cover × cover)))
      (j := j)
      (f := fun p _ ↦ f p)
  let u : ∀ W : cover, (𝓕.obj K).1.obj (op W.1) := fun W ↦
    ((𝓕.map g).1.app (op W.1)) (t W)
  have hu_compat : TopCat.Presheaf.IsCompatible (𝓕.obj K).1 (fun W : cover ↦ W.1) u := by
    intro W W'
    rcases hg (W, W') (by simp) with ⟨h, hh⟩
    have hpairK := congrArg (((𝓕.map h).1.app (op (W.1 ⊓ W'.1))))
      (hpairEq (W, W'))
    have hpairK' :
        ((𝓕.map g).1.app (op (W.1 ⊓ W'.1)))
            (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t W)) =
          ((𝓕.map g).1.app (op (W.1 ⊓ W'.1)))
            (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t W')) := by
      calc
        ((𝓕.map g).1.app (op (W.1 ⊓ W'.1)))
            (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t W))
          =
            ((𝓕.map h).1.app (op (W.1 ⊓ W'.1)))
              (((𝓕.map (f (W, W'))).1.app (op (W.1 ⊓ W'.1)))
                (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t W))) := by
                  simpa [Functor.map_comp, Category.assoc] using
                    (congrArg
                      (fun q ↦ ((𝓕.map q).1.app (op (W.1 ⊓ W'.1)))
                        (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t W))) hh).symm
        _ =
            ((𝓕.map h).1.app (op (W.1 ⊓ W'.1)))
              (((𝓕.map (f (W, W'))).1.app (op (W.1 ⊓ W'.1)))
                (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t W'))) := hpairK
        _ =
            ((𝓕.map g).1.app (op (W.1 ⊓ W'.1)))
              (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t W')) := by
                simpa [Functor.map_comp, Category.assoc] using
                  congrArg
                    (fun q ↦ ((𝓕.map q).1.app (op (W.1 ⊓ W'.1)))
                      (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t W'))) hh
    calc
      ((𝓕.obj K).1.map (homOfLE inf_le_left).op) (u W)
          = ((𝓕.map g).1.app (op (W.1 ⊓ W'.1)))
              (((𝓕.obj k).1.map (homOfLE inf_le_left).op) (t W)) := by
                symm
                exact sheaf_transition_app_map_eq_map_app 𝓕 g (homOfLE inf_le_left) (t W)
      _ = ((𝓕.map g).1.app (op (W.1 ⊓ W'.1)))
            (((𝓕.obj k).1.map (homOfLE inf_le_right).op) (t W')) := hpairK'
      _ = ((𝓕.obj K).1.map (homOfLE inf_le_right).op) (u W') := by
            exact sheaf_transition_app_map_eq_map_app 𝓕 g (homOfLE inf_le_right) (t W')
  have hu_rep :
      ∀ W : cover, ((colimit.ι G K).app (op W.1)) (u W) = localSectionRaw W := by
    intro W
    -- Moving to the synchronized target stage preserves the represented local section.
    calc
      ((colimit.ι G K).app (op W.1)) (u W)
          = ((colimit.ι G k).app (op W.1)) (t W) := by
              simpa [u, G, Functor.comp_map, Category.assoc] using
                (congrFun (congrArg (fun η ↦ η.app (op W.1)) (colimit.w G g)) (t W))
      _ = localSectionRaw W := ht W
  have hcover_opens :
      U ≤ iSup (fun W : cover ↦ W.1) := by
    intro x hxU
    rcases hcover_cover ⟨x, hxU⟩ with ⟨W, hW, hxW⟩
    exact (Opens.mem_iSup).2 ⟨⟨W, hW⟩, hxW⟩
  obtain ⟨gl, hgl, -⟩ := (𝓕.obj K).existsUnique_gluing'
    (U := fun W : cover ↦ W.1)
    (V := U)
    (iUV := fun W ↦ homOfLE (iU W))
    hcover_opens u hu_compat
  let y : P.obj (op U) := by
    simpa [P, G] using ((colimit.ι G K).app (op U)) gl
  have hglue_image :
      ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op U)) y = z := by
    -- Compare the glued section and `z` on the finite refinement and invoke sheaf uniqueness in
    -- the target sheafification.
    apply Sh.eq_of_locally_eq'
      (U := fun W : cover ↦ W.1)
      (V := U)
      (iUV := fun W ↦ homOfLE (iU W))
      hcover_opens
    intro W
    calc
      Sh.1.map (homOfLE (iU W)).op
          (((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op U))
            y)
        =
          ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W.1))
            (P.map (homOfLE (iU W)).op y) := by
              exact (congrFun
                (((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).naturality
                  (homOfLE (iU W)).op)) y).symm
      _ =
          ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W.1))
            (((colimit.ι G K).app (op W.1))
              (((𝓕.obj K).1.map (homOfLE (iU W)).op) gl)) := by
                simpa [P, G, y] using congrArg
                  (((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app
                    (op W.1)))
                  (presheafColimit_map_ι_apply
                    (𝓕 := 𝓕) (g := homOfLE (iU W)) (k := K) (t := gl))
      _ =
          ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W.1))
              (((colimit.ι G K).app (op W.1)) (u W)) := by
              simpa [G] using congrArg
                (fun uW ↦ ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app
                  (op W.1)) (((colimit.ι G K).app (op W.1)) uW))
                (hgl W)
      _ =
          ((CategoryTheory.toSheafify (J := JX) (D := Type (max u v w)) P).app (op W.1))
            (localSectionRaw W) := by
              rw [hu_rep W]
      _ = Sh.1.map (homOfLE (iU W)).op z := hlocalSectionRaw W
  refine ⟨y, ?_⟩
  simpa [P] using hglue_image

/-- Auxiliary filtered-colimit criterion: if every open cover of `U` admits a finite refinement
whose pairwise intersections are compact, then the canonical comparison map is bijective. The
cover hypothesis is stated canonically as the opens-site owner
`HasCofinalFiniteQuasiCompactOverlapCoverings JX U`. -/
theorem bijective_sheafColimitSectionComparison_of_cofinalFiniteQuasiCompactOverlapCoverings
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op U))]
    (hU : HasCofinalFiniteQuasiCompactOverlapCoverings JX U) :
    Function.Bijective
      (colimit.post 𝓕 ((sheafSections JX (Type (max u v w))).obj (op U))) := by
  refine ⟨?_, ?_⟩
  · -- Clause (4) inherits injectivity from clause (2) because the cofinal finite-refinement
    -- hypothesis already implies compactness of `U`.
    exact injective_sheafColimitSectionComparison_of_isCompact 𝓕 U
      (isCompact_of_cofinalFiniteQuasiCompactOverlapCoverings hU)
  · let hcolimP : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) :=
      functorCategoryHasColimit _
    let P : X.Presheaf (Type (max u v w)) :=
      @colimit _ _ _ _ (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) hcolimP
    let _ : HasColimit (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) := hcolimP
    -- Route correction: clause (4) factors through the sheafification unit on the presheaf
    -- colimit, so only the finite-refinement surjective half remains after transport.
    rw [colimit_post_eq_toSheafify_comparison_app]
    let eU :=
      colimitObjIsoColimitCompEvaluation
        (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) (op U)
    have h_eval :
        Function.Bijective
          (colimit.post (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))
            ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U))) := by
      -- Evaluation commutes with the presheaf colimit via the standard comparison isomorphism.
      have hpost :
          colimit.post (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w)))
              ((evaluation (Opens X)ᵒᵖ (Type (max u v w))).obj (op U)) =
            eU.inv := by
        apply colimit.hom_ext
        intro i
        rw [colimit.ι_post]
        simpa [eU] using
          (colimitObjIsoColimitCompEvaluation_ι_inv
            (𝓕 ⋙ sheafToPresheaf JX (Type (max u v w))) i (op U)).symm
      rw [hpost]
      exact (CategoryTheory.isIso_iff_bijective eU.inv).1
        (show IsIso eU.inv by infer_instance)
    have h_sheafify :
        Function.Surjective ((CategoryTheory.toSheafify JX P).app (op U)) := by
      -- The remaining source-proof step is the finite-refinement gluing lemma proved above.
      simpa [P] using
        surjective_toSheafify_app_of_cofinalFiniteQuasiCompactOverlapCoverings
          (𝓕 := 𝓕) (U := U) hU
    have h_iso :
        Function.Bijective (((presheafColimitToSheafIso 𝓕).hom.1.app (op U))) := by
      -- The chosen sheaf colimit is canonically the sheafification of the presheaf colimit.
      let hIsoNat :
          IsIso ((TopCat.Sheaf.forget (Type (max u v w)) X).map
            (presheafColimitToSheafIso 𝓕).hom) := by
        infer_instance
      exact (CategoryTheory.isIso_iff_bijective
        ((presheafColimitToSheafIso 𝓕).hom.1.app (op U))).1
          ((NatTrans.isIso_iff_isIso_app _).1 hIsoNat (op U))
    intro z
    rcases h_iso.2 z with ⟨z', rfl⟩
    rcases h_sheafify z' with ⟨y, rfl⟩
    rcases h_eval.2 y with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
