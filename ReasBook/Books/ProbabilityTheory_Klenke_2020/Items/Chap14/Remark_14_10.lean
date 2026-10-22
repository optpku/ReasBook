/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set MeasureTheory

variable {I : Type u} {Ω : I → Type v} [∀ i, MeasurableSpace (Ω i)]

/-- The cylinder-event `σ`-algebra on `J` is the pullback of the restricted product
`σ`-algebra along the canonical restriction map. -/
lemma cylinderEvents_eq_comap_restrict (J : Set I) :
    cylinderEvents J =
      MeasurableSpace.comap (restrict J)
        (MeasurableSpace.pi : MeasurableSpace ((j : J) → Ω j)) := by
  refine le_antisymm ?_ (measurable_restrict_cylinderEvents J).comap_le
  rw [MeasureTheory.cylinderEvents]
  refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
  simpa using
    (((measurable_pi_apply ⟨i, hi⟩).comp
      (measurable_iff_comap_le.mpr le_rfl :
        Measurable[MeasurableSpace.comap (restrict J)
          (MeasurableSpace.pi : MeasurableSpace ((j : J) → Ω j))] (restrict J))).comap_le :
      MeasurableSpace.comap
          (fun σ : (i : I) → Ω i ↦ (restrict J σ) ⟨i, hi⟩)
          (inferInstance : MeasurableSpace (Ω i)) ≤
        MeasurableSpace.comap (restrict J)
          (MeasurableSpace.pi : MeasurableSpace ((j : J) → Ω j)))

-- Proof sketch: rewrite `cylinderEvents J` as the pullback of the restricted product measurable
-- space along `restrict J`, then unpack `MeasurableSpace.measurableSet_comap`.
/-- Remark 14.10 (1): for every base set `J`, the textbook cylinder family `𝓩_J` is exactly the
measurable-set family of `MeasureTheory.cylinderEvents J`. -/
lemma measurableSets_cylinderEvents_eq_restrict_preimages (J : Set I) :
    {s : Set ((i : I) → Ω i) | MeasurableSet[cylinderEvents J] s} =
      {s | ∃ A : Set ((j : J) → Ω j), MeasurableSet A ∧ s = restrict J ⁻¹' A} := by
  ext s
  rw [cylinderEvents_eq_comap_restrict, Set.mem_setOf_eq, Set.mem_setOf_eq]
  simp [MeasurableSpace.measurableSet_comap, eq_comm]

private theorem squareCylinders_measurable_mem_finiteUnionRectangularCylinderSets
    {s : Set ((i : I) → Ω i)}
    (hs : s ∈ squareCylinders (fun i ↦ {t : Set (Ω i) | MeasurableSet t})) :
    s ∈ (finiteUnionRectangularCylinderSets : Set (Set ((i : I) → Ω i))) := by
  refine (mem_finiteUnionRectangularCylinderSets_iff).2 ?_
  refine ⟨{s}, ?_, by simp⟩
  intro t ht
  simpa [Finset.mem_singleton.mp ht] using hs

private theorem inter_squareCylinders_measurable
    {s t : Set ((i : I) → Ω i)}
    (hs : s ∈ squareCylinders (fun i ↦ {u : Set (Ω i) | MeasurableSet u}))
    (ht : t ∈ squareCylinders (fun i ↦ {u : Set (Ω i) | MeasurableSet u})) :
    s ∩ t ∈ squareCylinders (fun i ↦ {u : Set (Ω i) | MeasurableSet u}) := by
  rcases hs with ⟨s₁, t₁, h₁, rfl⟩
  rcases ht with ⟨s₂, t₂, h₂, rfl⟩
  classical
  let t₁' := s₁.piecewise t₁ (fun i ↦ univ)
  let t₂' := s₂.piecewise t₂ (fun i ↦ univ)
  have h1 : ∀ i ∈ (s₁ : Set I), t₁ i = t₁' i :=
    fun i hi ↦ (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h1' : ∀ i ∉ (s₁ : Set I), t₁' i = univ :=
    fun i hi ↦ Finset.piecewise_eq_of_notMem _ _ _ hi
  have h2 : ∀ i ∈ (s₂ : Set I), t₂ i = t₂' i :=
    fun i hi ↦ (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h2' : ∀ i ∉ (s₂ : Set I), t₂' i = univ :=
    fun i hi ↦ Finset.piecewise_eq_of_notMem _ _ _ hi
  rw [Set.pi_congr rfl h1, Set.pi_congr rfl h2, ← union_pi_inter h1' h2']
  refine ⟨s₁ ∪ s₂, fun i ↦ t₁' i ∩ t₂' i, ?_, ?_⟩
  · rw [Set.mem_pi]
    intro i _
    refine MeasurableSet.inter ?_ ?_
    · by_cases hi₁ : i ∈ s₁
      · rw [← h1 i hi₁]
        exact h₁ i (by simp)
      · rw [h1' i hi₁]
        exact MeasurableSet.univ
    · by_cases hi₂ : i ∈ s₂
      · rw [← h2 i hi₂]
        exact h₂ i (by simp)
      · rw [h2' i hi₂]
        exact MeasurableSet.univ
  · rw [Finset.coe_union]

omit [∀ i, MeasurableSpace (Ω i)] in
private theorem sUnion_image_product_inter (S T : Finset (Set ((i : I) → Ω i))) :
    ⋃₀ (((S.product T).image fun p ↦ p.1 ∩ p.2) : Set (Set ((i : I) → Ω i))) =
      ⋃₀ (S : Set (Set ((i : I) → Ω i))) ∩ ⋃₀ (T : Set (Set ((i : I) → Ω i))) := by
  classical
  ext x
  simp only [Finset.product_eq_sprod, Finset.coe_image, Finset.coe_product, image_prod,
    sUnion_image2, SetLike.mem_coe, mem_iUnion, mem_inter_iff, exists_and_left, exists_prop,
    mem_sUnion]
  constructor
  · rintro ⟨s, hxs, hs, t, ht, hxt⟩
    exact ⟨⟨s, hs, hxs⟩, ⟨t, ht, hxt⟩⟩
  · rintro ⟨⟨s, hs, hxs⟩, ⟨t, ht, hxt⟩⟩
    exact ⟨s, hxs, hs, t, ht, hxt⟩

private theorem inter_mem_finiteUnionRectangularCylinderSets
    {s t : Set ((i : I) → Ω i)}
    (hs : s ∈ (finiteUnionRectangularCylinderSets : Set (Set ((i : I) → Ω i))))
    (ht : t ∈ (finiteUnionRectangularCylinderSets : Set (Set ((i : I) → Ω i)))) :
    s ∩ t ∈ (finiteUnionRectangularCylinderSets : Set (Set ((i : I) → Ω i))) := by
  classical
  rcases (mem_finiteUnionRectangularCylinderSets_iff).1 hs with ⟨S, hS, rfl⟩
  rcases (mem_finiteUnionRectangularCylinderSets_iff).1 ht with ⟨T, hT, rfl⟩
  refine (mem_finiteUnionRectangularCylinderSets_iff).2 ?_
  refine ⟨(S.product T).image (fun p ↦ p.1 ∩ p.2), ?_, ?_⟩
  · intro u hu
    rw [Finset.mem_coe, Finset.mem_image] at hu
    rcases hu with ⟨p, hp, rfl⟩
    have hp' : p.1 ∈ S ∧ p.2 ∈ T := by
      simpa [Finset.mem_product] using hp
    exact inter_squareCylinders_measurable (hS hp'.1) (hT hp'.2)
  · rw [sUnion_image_product_inter]

private theorem compl_squareCylinders_measurable_mem_finiteUnionRectangularCylinderSets
    {s : Set ((i : I) → Ω i)}
    (hs : s ∈ squareCylinders (fun i ↦ {t : Set (Ω i) | MeasurableSet t})) :
    sᶜ ∈ (finiteUnionRectangularCylinderSets : Set (Set ((i : I) → Ω i))) := by
  classical
  rcases hs with ⟨J, A, hA, rfl⟩
  refine (mem_finiteUnionRectangularCylinderSets_iff).2 ?_
  refine ⟨J.image (fun j ↦ (J : Set I).pi (fun k ↦ if k = j then (A k)ᶜ else univ)), ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_image] at ht
    rcases ht with ⟨j, hj, rfl⟩
    refine ⟨J, fun k ↦ if k = j then (A k)ᶜ else univ, ?_, rfl⟩
    rw [Set.mem_pi] at hA ⊢
    intro i _
    have hAi : MeasurableSet (A i) := by
      simpa using hA i (by simp)
    by_cases hij : i = j
    · simp [hij, hAi]
    · simp [hij]
  · ext x
    simp only [mem_compl_iff, mem_pi, SetLike.mem_coe, not_forall, Finset.coe_image, sUnion_image,
      mem_iUnion, mem_ite_univ_right, exists_prop]
    constructor
    · rintro ⟨j, hj, hxj⟩
      exact ⟨j, hj, fun i hi hij ↦ by subst hij; simpa using hxj⟩
    · rintro ⟨j, hj, hxj⟩
      exact ⟨j, hj, hxj j hj rfl⟩

private theorem compl_sUnion_mem_finiteUnionRectangularCylinderSets
    (S : Finset (Set ((i : I) → Ω i)))
    (hS : (S : Set (Set ((i : I) → Ω i))) ⊆
      squareCylinders (fun i ↦ {t : Set (Ω i) | MeasurableSet t})) :
    (⋃₀ (S : Set (Set ((i : I) → Ω i))))ᶜ ∈
      (finiteUnionRectangularCylinderSets : Set (Set ((i : I) → Ω i))) := by
  classical
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro hS
    have huniv : (univ : Set ((i : I) → Ω i)) ∈
        squareCylinders (fun i ↦ {t : Set (Ω i) | MeasurableSet t}) := by
      refine ⟨∅, fun i ↦ univ, ?_, by simp⟩
      simp [Set.mem_pi]
    simpa using squareCylinders_measurable_mem_finiteUnionRectangularCylinderSets huniv
  · intro s S hsS ih hS
    have hs : s ∈ squareCylinders (fun i ↦ {t : Set (Ω i) | MeasurableSet t}) := by
      exact hS (by simp)
    have hS' : (S : Set (Set ((i : I) → Ω i))) ⊆
        squareCylinders (fun i ↦ {t : Set (Ω i) | MeasurableSet t}) := by
      intro t ht
      exact hS (by simp [ht])
    rw [Finset.coe_insert, sUnion_insert, compl_union]
    exact inter_mem_finiteUnionRectangularCylinderSets
      (compl_squareCylinders_measurable_mem_finiteUnionRectangularCylinderSets hs) (ih hS')

/- Remark 14.10 (2): Definition 14.9 already identifies the textbook finite-base cylinder family
`𝓩` with the owner abstraction `MeasureTheory.measurableCylinders Ω`, so the algebra-of-sets claim
is exactly the canonical theorem `MeasureTheory.isSetAlgebra_measurableCylinders`. -/
recall MeasureTheory.isSetAlgebra_measurableCylinders

-- Proof sketch: complements and finite unions of finite unions of measurable rectangular
-- cylinders are again finite unions of measurable rectangular cylinders.
/-- Remark 14.10 (3): the finite unions `𝓩_*^R` of measurable rectangular cylinders form an
algebra of sets. -/
lemma isSetAlgebra_finiteUnionRectangularCylinderSets :
    IsSetAlgebra (finiteUnionRectangularCylinderSets : Set (Set ((i : I) → Ω i))) where
  empty_mem := by
    refine (mem_finiteUnionRectangularCylinderSets_iff).2 ?_
    exact ⟨∅, by simp, by simp⟩
  compl_mem s hs := by
    rcases (mem_finiteUnionRectangularCylinderSets_iff).1 hs with ⟨S, hS, rfl⟩
    exact compl_sUnion_mem_finiteUnionRectangularCylinderSets S hS
  union_mem s t hs ht := by
    rcases (mem_finiteUnionRectangularCylinderSets_iff).1 hs with ⟨S, hS, rfl⟩
    rcases (mem_finiteUnionRectangularCylinderSets_iff).1 ht with ⟨T, hT, rfl⟩
    refine (mem_finiteUnionRectangularCylinderSets_iff).2 ⟨S ∪ T, ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · exact hS hu
      · exact hT hu
    · rw [Finset.coe_union, sUnion_union]

/- Remark 14.10 (4): with `𝓩` already refined to `MeasureTheory.measurableCylinders Ω` in
Definition 14.9, the generation statement is the owner theorem
`MeasureTheory.generateFrom_measurableCylinders`. -/
recall MeasureTheory.generateFrom_measurableCylinders
