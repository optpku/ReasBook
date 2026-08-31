module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Spectral.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.ScottTopology
public import stacks_project.Chap05.Lemma_5_23_5
import stacks_project.Chap05.Lemma_5_23_12
import stacks_project.Chap05.Lemma_5_23_13
import stacks_project.Chap05.Lemma_5_23_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite Set TopologicalSpace Topology

universe u

noncomputable section

section

variable (X : Type u) [TopologicalSpace X]

/-- Helper for Lemma 5.23.14: arbitrary Sierpinski products are spectral. -/
private theorem spectralSpace_sierpinskiProduct (ι : Type u) : SpectralSpace (ι → Prop) := by
  -- Reuse Lemma `5.23.13` with the identity embedding of the product into itself.
  refine
    (spectralSpace_iff_exists_sierpinski_product_embedding_closed_in_constructible_topology
      (X := ι → Prop)).2 ?_
  refine ⟨ι, ContinuousMap.id (ι → Prop), ?_, ?_⟩
  · simpa using (show Topology.IsEmbedding (fun x : ι → Prop => x) from Topology.IsEmbedding.id)
  · simp

/-- Helper for Lemma 5.23.14: the single-coordinate `true` cylinder is compact. -/
private theorem coordinate_true_isCompact {ι : Type u} [DecidableEq ι] (i : ι) :
    IsCompact ({x : ι → Prop | x i = True} : Set (ι → Prop)) := by
  -- Split off the chosen coordinate and identify the cylinder with `{True} × univ`.
  let e₁ : (ι → Prop) ≃ₜ ((j : {x : ι // x = i}) → Prop) × ((j : {x : ι // x ≠ i}) → Prop) :=
    Homeomorph.piEquivPiSubtypeProd (fun j : ι => j = i) (fun _ => Prop)
  let e₂ :
      ((j : {x : ι // x = i}) → Prop) × ((j : {x : ι // x ≠ i}) → Prop) ≃ₜ
        Prop × ((j : {x : ι // x ≠ i}) → Prop) :=
    Homeomorph.prodCongr (Homeomorph.funUnique {x : ι // x = i} Prop) (Homeomorph.refl _)
  let e : (ι → Prop) ≃ₜ Prop × ((j : {x : ι // x ≠ i}) → Prop) := e₁.trans e₂
  have himage :
      e '' ({x : ι → Prop | x i = True} : Set (ι → Prop)) =
        ({True} : Set Prop) ×ˢ (Set.univ : Set ((j : {x : ι // x ≠ i}) → Prop)) := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor
      · simpa [e, e₁, e₂] using hx
      · simp
    · rintro ⟨hp, -⟩
      refine ⟨e.symm p, ?_, by simp [e]⟩
      simpa [e, e₁, e₂] using hp
  rw [e.isEmbedding.isCompact_iff]
  simpa [himage] using (isCompact_singleton.prod isCompact_univ)

/-- Helper for Lemma 5.23.14: the single-coordinate `true` cylinder is constructible. -/
private theorem coordinate_true_isConstructible {ι : Type u} [DecidableEq ι]
    [SpectralSpace (ι → Prop)] (i : ι) :
    IsConstructible ({x : ι → Prop | x i = True} : Set (ι → Prop)) := by
  -- Compact-open cylinders are constructible in a spectral space.
  have hOpen : IsOpen ({x : ι → Prop | x i = True} : Set (ι → Prop)) := by
    have hpre :
        IsOpen (((fun x : ι → Prop => x i) : (ι → Prop) → Prop) ⁻¹' ({True} : Set Prop)) :=
      isOpen_singleton_true.preimage (continuous_apply i)
    simpa using hpre
  exact (coordinate_true_isCompact (i := i)).isConstructible hOpen

/-- Helper for Lemma 5.23.14: fixing one coordinate is patch-closed in a Sierpinski product. -/
private theorem coordinate_value_isClosed_patch {ι : Type u} [DecidableEq ι]
    [SpectralSpace (ι → Prop)] (i : ι) (b : Prop) :
    IsClosed[constructibleTopology (ι → Prop)] ({x : ι → Prop | x i = b} : Set (ι → Prop)) := by
  by_cases hb : b
  · have hb' : b = True := propext (iff_true_intro hb)
    simpa [hb'] using
      (isClopen_constructibleTopology_of_isConstructible
        (coordinate_true_isConstructible (i := i))).1
  · have hclosed :
        IsClosed[constructibleTopology (ι → Prop)] ({x : ι → Prop | x i = False} : Set
          (ι → Prop)) := by
      have hopenTrue :
          IsOpen[constructibleTopology (ι → Prop)] ({x : ι → Prop | x i = True} : Set
            (ι → Prop)) :=
        (isClopen_constructibleTopology_of_isConstructible
          (coordinate_true_isConstructible (i := i))).2
      have hclosedCompl :
          IsClosed[constructibleTopology (ι → Prop)]
            (({x : ι → Prop | x i = True} : Set (ι → Prop))ᶜ) := by
        let _ : TopologicalSpace (ι → Prop) := constructibleTopology (ι → Prop)
        exact hopenTrue.isClosed_compl
      convert hclosedCompl using 1
      ext x
      simp
    have hb' : b = False := propext (iff_false_intro hb)
    simpa [hb'] using hclosed

/-- Helper for Lemma 5.23.14: a finite coordinate pattern is patch-closed in a Sierpinski
product. -/
private theorem finite_coordinate_match_isClosed_patch {ι : Type u} [DecidableEq ι]
    [SpectralSpace (ι → Prop)]
    (s : Finset ι) (a : s → Prop) :
    IsClosed[constructibleTopology (ι → Prop)] ({x : ι → Prop | ∀ i : s, x i.1 = a i} : Set
      (ι → Prop)) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      simpa using (isClosed_univ : IsClosed[constructibleTopology (ι → Prop)] (Set.univ : Set
        (ι → Prop)))
  | cons i s hi hs =>
      -- Separate the new coordinate from the previously fixed finite pattern.
      let aTail : s → Prop := fun j => a ⟨j.1, by simp [j.2]⟩
      have hEq :
          ({x : ι → Prop | ∀ j : Finset.cons i s hi, x j.1 = a j} : Set (ι → Prop)) =
            ({x : ι → Prop | x i = a ⟨i, by simp⟩} ∩
              {x : ι → Prop | ∀ j : s, x j.1 = aTail j}) := by
        ext x
        constructor
        · intro hx
          constructor
          · exact hx ⟨i, by simp⟩
          · intro j
            exact hx ⟨j.1, by simp [j.2]⟩
        · rintro ⟨hHead, hTail⟩ j
          by_cases hj : j.1 = i
          · have hji : j = ⟨i, by simp⟩ := Subtype.ext hj
            simpa [hji] using hHead
          · exact hTail ⟨j.1, by simpa [Finset.mem_cons, hj] using j.2⟩
      rw [hEq]
      have hHeadClosed :
          IsClosed[constructibleTopology (ι → Prop)] ({x : ι → Prop | x i = a ⟨i, by simp⟩} :
            Set (ι → Prop)) :=
        coordinate_value_isClosed_patch (i := i) (b := a ⟨i, by simp⟩)
      have hTailClosed :
          IsClosed[constructibleTopology (ι → Prop)] ({x : ι → Prop | ∀ j : s, x j.1 = aTail j} :
            Set (ι → Prop)) :=
        hs aTail
      let _ : TopologicalSpace (ι → Prop) := constructibleTopology (ι → Prop)
      exact hHeadClosed.inter hTailClosed

/-- Helper for Lemma 5.23.14: every finite `T₀` space is quasi-sober. -/
private theorem quasiSober_of_finite_t0 (Y : Type u) [TopologicalSpace Y] [Finite Y] [T0Space Y] :
    QuasiSober Y := by
  -- Pass to the irreducible closed subset as a finite `T₀` subspace and choose a point whose
  -- singleton is open there; irreducibility then forces that singleton to be dense.
  refine (quasiSober_iff Y).2 ?_
  intro S hS hSclosed
  rcases hS.1 with ⟨x0, hx0⟩
  letI : Nonempty S := ⟨⟨x0, hx0⟩⟩
  letI : Finite S := inferInstance
  letI : T0Space S := inferInstance
  letI : PreirreducibleSpace S := Subtype.preirreducibleSpace hS.isPreirreducible
  obtain ⟨x, hxOpen⟩ := exists_open_singleton_of_finite (X := S)
  have hDense : Dense ({x} : Set S) := hxOpen.dense (Set.singleton_nonempty x)
  have hClosureSubtype : closure ({x} : Set S) = Set.univ := by
    simpa [dense_iff_closure_eq] using hDense
  have hsubset : S ⊆ closure ({x.1} : Set Y) := by
    intro y hy
    have hySub : (⟨y, hy⟩ : S) ∈ closure ({x} : Set S) := by
      simp [hClosureSubtype]
    simpa using (closure_subtype (x := ⟨y, hy⟩) (s := ({x} : Set S))).1 hySub
  have hsuperset : closure ({x.1} : Set Y) ⊆ S :=
    hSclosed.closure_subset_iff.mpr (by
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact x.2)
  refine ⟨x.1, ?_⟩
  -- The ambient closure of the chosen point is exactly the original irreducible closed subset.
  rw [isGenericPoint_def]
  exact subset_antisymm hsuperset hsubset

-- Proof sketch: for the forward implication, use Lemma `5.23.13` to identify `X` with a
-- constructibly closed subset of a Sierpinski product, then replace that closed subset by the
-- inverse system of its finite-coordinate images. For the reverse implication, convert the given
-- `Jᵒᵈ`-diagram to a `Jᵒᵖ`-diagram via `orderDualEquivalence`, apply Lemma `5.23.12`, and
-- transport spectrality back across the resulting homeomorphisms.
/-- Lemma 5.23.14: a topological space is spectral if and only if it is homeomorphic to the limit
of a directed inverse system of finite sober topological spaces. -/
theorem spectralSpace_iff_homeomorphic_directed_limit_finite_sober :
    SpectralSpace X ↔
      ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirectedOrder J)
        (F : Jᵒᵈ ⥤ TopCat.{u}) (_ : ∀ j : Jᵒᵈ, Finite (F.obj j))
        (_ : ∀ j : Jᵒᵈ, T0Space (F.obj j)),
        Nonempty (X ≃ₜ ↥(limit F)) := by
  constructor
  · intro hX
    classical
    letI : SpectralSpace X := hX
    rcases
      (spectralSpace_iff_exists_sierpinski_product_embedding_closed_in_constructible_topology
        (X := X)).1 hX with
      ⟨ι, f, hf, hclosed⟩
    letI : SpectralSpace (ι → Prop) := spectralSpace_sierpinskiProduct ι
    let E : Set (ι → Prop) := Set.range f
    have hpre : (f ⁻¹' E : Set X) = Set.univ := by
      ext x
      simp [E]
    let ePre : (f ⁻¹' E) ≃ₜ E :=
      hf.homeomorphOfSubsetRange (s := E) (by intro y hy; exact hy)
    let eRange : (Set.univ : Set X) ≃ₜ E := by
      -- The embedding identifies `X` with its range in the Sierpinski product.
      exact (Homeomorph.setCongr hpre.symm).trans ePre
    let eX : X ≃ₜ E := (Homeomorph.Set.univ X).symm.trans eRange
    letI : SpectralSpace E := spectralSpace_subtype_of_isClosed_constructibleTopology hclosed
    let G : (Finset ι)ᵒᵖ ⥤ TopCat.{u} := by
      refine
        { obj := fun s =>
            TopCat.of (Set.range (fun x : E => fun i : s.unop => x.1 i.1))
          map := fun {s t} h =>
            TopCat.ofHom
              { toFun := fun a => by
                  refine ⟨fun i => a.1 ⟨i.1, (show t.unop ≤ s.unop from h.unop.down.down) i.2⟩, ?_⟩
                  rcases a.2 with ⟨x, hx⟩
                  refine ⟨x, ?_⟩
                  ext i
                  simpa [hx] using
                    congrFun hx ⟨i.1, (show t.unop ≤ s.unop from h.unop.down.down) i.2⟩
                continuous_toFun := by
                  refine Continuous.subtype_mk ?_ ?_
                  exact
                    continuous_pi fun i =>
                      (continuous_apply
                          (⟨i.1, (show t.unop ≤ s.unop from h.unop.down.down) i.2⟩ : s.unop)).comp
                        continuous_subtype_val }
          map_id := by
            intro s
            ext a i
            rfl
          map_comp := by
            intro a b c g h
            ext u i
            rfl }
    let forgetLimitCone :
        (TopCat.limitCone G).pt → (TopCat.limitCone (finiteRestrictionDiagram ι)).pt :=
      fun u => by
        refine ⟨(fun s => (u.1 s).1), ?_⟩
        intro s t h
        simpa [G] using congrArg Subtype.val (u.2 h)
    have hforgetLimitCone :
        Continuous forgetLimitCone := by
      -- Forget only the range witnesses; the underlying stage tuples vary continuously.
      refine Continuous.subtype_mk ?_ ?_
      exact
        continuous_pi fun s =>
          continuous_subtype_val.comp ((continuous_apply s).comp continuous_subtype_val)
    have realize_limitCone_point :
        ∀ u : (TopCat.limitCone G).pt, compatibleFamilyHomeomorph ι (forgetLimitCone u) ∈ E := by
      intro u
      let v : (TopCat.limitCone (finiteRestrictionDiagram ι)).pt := forgetLimitCone u
      let M : Finset ι → Set (ι → Prop) :=
        fun s ↦ E ∩ {x : ι → Prop | ∀ i : s, x i.1 = (v.1 (Opposite.op s)) i}
      have hM_closed_patch :
          ∀ s : Finset ι, IsClosed[constructibleTopology (ι → Prop)] (M s) := by
        intro s
        have hMatchClosed :
            IsClosed[constructibleTopology (ι → Prop)]
              ({x : ι → Prop | ∀ i : s, x i.1 = (v.1 (Opposite.op s)) i} : Set (ι → Prop)) :=
          finite_coordinate_match_isClosed_patch s (v.1 (Opposite.op s))
        let _ : TopologicalSpace (ι → Prop) := constructibleTopology (ι → Prop)
        exact hclosed.inter hMatchClosed
      have hM_nonempty : ∀ s : Finset ι, (M s).Nonempty := by
        intro s
        rcases (u.1 (Opposite.op s)).2 with ⟨x, hx⟩
        refine ⟨x.1, x.2, ?_⟩
        intro i
        simpa [v, forgetLimitCone] using congrFun hx i
      have hM_directed : Directed (· ⊇ ·) M := by
        intro s t
        refine ⟨s ∪ t, ?_, ?_⟩
        · intro x hx
          constructor
          · exact hx.1
          · intro i
            let hst : Opposite.op (s ∪ t) ⟶ Opposite.op s := by
              exact Quiver.Hom.op ⟨PLift.up <| Finset.subset_union_left⟩
            have hcompat := congrArg Subtype.val (u.2 hst)
            have hi :
                (v.1 (Opposite.op (s ∪ t))) ⟨i.1, by
                  exact Finset.mem_union.mpr (Or.inl i.2)⟩ =
                  (v.1 (Opposite.op s)) i := by
              simpa [v, forgetLimitCone, G, hst] using congrFun hcompat i
            exact (hx.2 ⟨i.1, by exact Finset.mem_union.mpr (Or.inl i.2)⟩).trans hi
        · intro x hx
          constructor
          · exact hx.1
          · intro i
            let hst : Opposite.op (s ∪ t) ⟶ Opposite.op t := by
              exact Quiver.Hom.op ⟨PLift.up <| Finset.subset_union_right⟩
            have hcompat := congrArg Subtype.val (u.2 hst)
            have hi :
                (v.1 (Opposite.op (s ∪ t))) ⟨i.1, by
                  exact Finset.mem_union.mpr (Or.inr i.2)⟩ =
                  (v.1 (Opposite.op t)) i := by
              simpa [v, forgetLimitCone, G, hst] using congrFun hcompat i
            exact (hx.2 ⟨i.1, by exact Finset.mem_union.mpr (Or.inr i.2)⟩).trans hi
      have hM_compact_patch :
          ∀ s : Finset ι, @IsCompact (ι → Prop) (constructibleTopology (ι → Prop)) (M s) := by
        have hPatchCompact :
            @CompactSpace (ι → Prop) (constructibleTopology (ι → Prop)) :=
          (constructibleTopology_compactSpace_of_spectralSpace :
            @CompactSpace (ι → Prop) (constructibleTopology (ι → Prop)))
        intro s
        letI : TopologicalSpace (ι → Prop) := constructibleTopology (ι → Prop)
        letI : CompactSpace (ι → Prop) := hPatchCompact
        exact (hM_closed_patch s).isCompact
      obtain ⟨x, hx⟩ :=
        Set.nonempty_iInter.mp <|
          @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
            (ι → Prop) (constructibleTopology (ι → Prop)) (Finset ι) inferInstance M
            hM_directed hM_nonempty hM_compact_patch hM_closed_patch
      have hxEq :
          x = compatibleFamilyHomeomorph ι v := by
        funext i
        exact (hx ({i} : Finset ι)).2 ⟨i, by simp⟩
      have hxE : x ∈ E := (hx ∅).1
      simpa [v] using hxEq ▸ hxE
    let forwardLimitCone : E → (TopCat.limitCone G).pt :=
      fun x =>
        ⟨fun s => ⟨fun i => x.1 i.1, ⟨x, rfl⟩⟩, by
          intro s t h
          apply Subtype.ext
          funext i
          rfl⟩
    have hforwardLimitCone : Continuous forwardLimitCone := by
      -- Each stage is given by finite coordinate restriction of the ambient Sierpinski point.
      refine Continuous.subtype_mk ?_ ?_
      exact
        continuous_pi fun s =>
          Continuous.subtype_mk
            (continuous_pi fun i => (continuous_apply i.1).comp continuous_subtype_val)
            (fun x => ⟨x, rfl⟩)
    let reverseLimitCone : (TopCat.limitCone G).pt → E :=
      fun u => ⟨compatibleFamilyHomeomorph ι (forgetLimitCone u), realize_limitCone_point u⟩
    have hreverseLimitCone : Continuous reverseLimitCone := by
      -- Recover the global Sierpinski point from the singleton coordinates of the compatible
      -- family, then use the realization lemma to place it back in `E`.
      refine Continuous.subtype_mk ?_ ?_
      exact (compatibleFamilyHomeomorph ι).continuous_toFun.comp hforgetLimitCone
    have hforward_reverse :
        Function.LeftInverse reverseLimitCone forwardLimitCone := by
      intro x
      apply Subtype.ext
      have hforgetX :
          forgetLimitCone (forwardLimitCone x) = (compatibleFamilyHomeomorph ι).symm x.1 := by
        apply Subtype.ext
        funext s
        rfl
      simpa [reverseLimitCone, hforgetX] using (compatibleFamilyHomeomorph ι).right_inv x.1
    have hreverse_forward :
        Function.RightInverse reverseLimitCone forwardLimitCone := by
      intro u
      apply Subtype.ext
      funext s
      apply Subtype.ext
      funext i
      have hcompat :
          (compatibleFamilyHomeomorph ι).symm
              ((compatibleFamilyHomeomorph ι) (forgetLimitCone u)) =
            forgetLimitCone u :=
        (compatibleFamilyHomeomorph ι).left_inv (forgetLimitCone u)
      exact congrArg (fun v => v.1 s i) hcompat
    let eLimitCone : E ≃ₜ (TopCat.limitCone G).pt :=
      { toFun := forwardLimitCone
        invFun := reverseLimitCone
        left_inv := hforward_reverse
        right_inv := hreverse_forward
        continuous_toFun := hforwardLimitCone
        continuous_invFun := hreverseLimitCone }
    let eG : E ≃ₜ ↥(limit G) :=
      eLimitCone.trans
        (TopCat.homeoOfIso
          (IsLimit.conePointUniqueUpToIso (TopCat.limitConeIsLimit G) (limit.isLimit G)))
    let F : (Finset ι)ᵒᵈ ⥤ TopCat.{u} :=
      (CategoryTheory.orderDualEquivalence (Finset ι)).functor ⋙ G
    let eOrder : ↥(limit F) ≃ₜ ↥(limit G) :=
      TopCat.homeoOfIso
        (HasLimit.isoOfEquivalence (CategoryTheory.orderDualEquivalence (Finset ι))
          (Iso.refl F))
    refine
      ⟨Finset ι, inferInstance, inferInstance, inferInstance, F, ?_, ?_,
        ⟨eX.trans (eG.trans eOrder.symm)⟩⟩
    · intro j
      simpa [F] using
        (inferInstance :
          Finite (G.obj ((CategoryTheory.orderDualEquivalence (Finset ι)).functor.obj j)))
    · intro j
      simpa [F] using
        (inferInstance :
          T0Space (G.obj ((CategoryTheory.orderDualEquivalence (Finset ι)).functor.obj j)))
  · rintro ⟨J, _, _, _, F, hFinite, hT0, ⟨e⟩⟩
    let G : Jᵒᵖ ⥤ TopCat.{u} := (CategoryTheory.orderDualEquivalence J).inverse ⋙ F
    letI : ∀ j : Jᵒᵖ, Finite (G.obj j) := by
      intro j
      simpa [G] using hFinite ((CategoryTheory.orderDualEquivalence J).inverse.obj j)
    letI : ∀ j : Jᵒᵖ, T0Space (G.obj j) := by
      intro j
      simpa [G] using hT0 ((CategoryTheory.orderDualEquivalence J).inverse.obj j)
    letI : ∀ j : Jᵒᵖ, QuasiSober (G.obj j) := by
      intro j
      exact quasiSober_of_finite_t0 (G.obj j)
    have hLimitG : SpectralSpace ↥(limit G) :=
      spectralSpace_of_limit_finite_sober_inverse_system (F := G)
    let eLimit :
        ↥(limit F) ≃ₜ ↥(limit G) :=
      (TopCat.homeoOfIso
        (HasLimit.isoOfEquivalence
          (CategoryTheory.orderDualEquivalence J).symm
          (Iso.refl G))).symm
    have hLimitF : SpectralSpace ↥(limit F) := by
      letI : SpectralSpace ↥(limit G) := hLimitG
      letI : CompactSpace ↥(limit F) := eLimit.symm.compactSpace
      exact eLimit.isOpenEmbedding.spectralSpace
    letI : SpectralSpace ↥(limit F) := hLimitF
    letI : CompactSpace X := e.symm.compactSpace
    exact e.isOpenEmbedding.spectralSpace

end
