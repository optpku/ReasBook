/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set

universe u v w w'

variable {Ω : Type u} {κ : Type v} {ι : Type w} [MeasurableSpace Ω]
variable {β : ι → Type w'} [mβ : ∀ i, MeasurableSpace (β i)]

/-- Helper for Theorem 2.26: the measurable sets of the coordinate `comap` spaces form an
independent family whenever the coordinates themselves are independent. -/
private lemma coordinate_comap_measurable_sets_iIndepSets (μ : Measure Ω) (X : ∀ i, Ω → β i)
    (hX : iIndepFun X μ) :
    iIndepSets (fun i ↦ {s | MeasurableSet[(mβ i).comap (X i)] s}) μ := by
  -- We rewrite the independence of the random variables as independence of their coordinate
  -- `comap` σ-algebras, then pass to the canonical measurable-set generators.
  exact hX.iIndep.iIndepSets fun i ↦
    (@MeasurableSpace.generateFrom_measurableSet Ω ((mβ i).comap (X i))).symm

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 2.26: intersecting cylinder classes over disjoint coordinate blocks stays in
the cylinder class over the union block. -/
private lemma inter_mem_piiUnionInter_of_disjoint (π : ι → Set (Set Ω))
    {S T : Set ι} {s t : Set Ω}
    (hST : Disjoint S T) (hs : s ∈ piiUnionInter π S) (ht : t ∈ piiUnionInter π T) :
    s ∩ t ∈ piiUnionInter π (S ∪ T) := by
  classical
  rcases hs with ⟨ps, hps, f, hf, hs_eq⟩
  rcases ht with ⟨pt, hpt, g, hg, ht_eq⟩
  have hpspt : Disjoint ps pt := by
    refine Finset.disjoint_left.mpr ?_
    intro i hip hit
    exact Set.disjoint_left.mp hST (hps hip) (hpt hit)
  let u : Finset ι := ps ∪ pt
  refine ⟨u, ?_, fun i ↦ if i ∈ ps then f i else g i, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact Or.inl (hps hi)
    · exact Or.inr (hpt hi)
  · intro i hi
    have hi' : i ∈ ps ∨ i ∈ pt := by
      simpa [u] using hi
    by_cases hip : i ∈ ps
    · simpa [hip] using hf i hip
    · have hit : i ∈ pt := by
        simpa [hip] using hi'
      simpa [hip] using hg i hit
  · rw [hs_eq, ht_eq]
    ext x
    suffices
        (∀ i, i ∈ ps ∪ pt → x ∈ if i ∈ ps then f i else g i) ↔
          ((∀ i ∈ ps, x ∈ f i) ∧ ∀ i ∈ pt, x ∈ g i) by
      simpa [u, Finset.mem_union, Set.mem_inter_iff, Set.mem_iInter] using this.symm
    constructor
    · intro hx
      constructor
      · intro i hi
        have hxi : x ∈ if i ∈ ps then f i else g i := hx i (Finset.mem_union_left pt hi)
        simpa [hi] using hxi
      · intro i hi
        have hni : i ∉ ps := fun hip ↦ Finset.disjoint_left.mp hpspt hip hi
        have hxi : x ∈ if i ∈ ps then f i else g i := hx i (Finset.mem_union_right ps hi)
        simpa [hni] using hxi
    · intro hx i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · simpa [hi] using hx.1 i hi
      · have hni : i ∉ ps := fun hip ↦ Finset.disjoint_left.mp hpspt hip hi
        simpa [hni] using hx.2 i hi

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 2.26: a finite intersection of block cylinder sets is again a cylinder set
over the union of the chosen blocks. -/
private lemma biInter_mem_piiUnionInter_iUnion_blocks (π : ι → Set (Set Ω)) (I : κ → Set ι)
    (h_disjoint : Pairwise fun k l ↦ Disjoint (I k) (I l)) (S : Finset κ) {B : κ → Set Ω}
    (hB : ∀ k, k ∈ S → B k ∈ piiUnionInter π (I k)) :
    (⋂ k ∈ S, B k) ∈ piiUnionInter π (⋃ k ∈ (S : Set κ), I k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      -- The empty block intersection is `univ`, realized by the empty coordinate support.
      refine ⟨∅, ?_, fun _ ↦ univ, ?_, ?_⟩
      · simp
      · intro i hi
        exact False.elim (Finset.notMem_empty i hi)
      · simp
  | @insert a S haS ih =>
      have hBa : B a ∈ piiUnionInter π (I a) := hB a (Finset.mem_insert_self a S)
      have hBS : ∀ k, k ∈ S → B k ∈ piiUnionInter π (I k) := by
        intro k hk
        exact hB k (Finset.mem_insert_of_mem hk)
      have hrest :
          (⋂ k ∈ S, B k) ∈ piiUnionInter π (⋃ k ∈ (S : Set κ), I k) :=
        ih hBS
      have hdisj_rest : Disjoint (I a) (⋃ k ∈ (S : Set κ), I k) := by
        refine Set.disjoint_left.mpr ?_
        intro i hiA hiS
        rcases mem_iUnion.1 hiS with ⟨k, hiS⟩
        rcases mem_iUnion.1 hiS with ⟨hk, hik⟩
        exact Set.disjoint_left.mp (h_disjoint fun h ↦ haS (by simpa [h] using hk)) hiA hik
      -- We combine the new block cylinder with the already-grouped remainder block.
      simpa [Finset.set_biInter_insert, Set.iUnion_true, Finset.mem_coe, haS, Set.union_comm,
        Set.union_left_comm, Set.union_assoc] using
        inter_mem_piiUnionInter_of_disjoint (π := π) hdisj_rest hBa hrest

/-- Helper for Theorem 2.26: grouping independent coordinate cylinder classes along pairwise
disjoint blocks preserves independence. -/
private lemma piiUnionInter_iIndepSets_of_pairwise_disjoint_blocks
    (π : ι → Set (Set Ω)) (μ : Measure Ω)
    (I : κ → Set ι) (h_indep : iIndepSets π μ)
    (h_disjoint : Pairwise fun k l ↦ Disjoint (I k) (I l)) :
    iIndepSets (fun k ↦ piiUnionInter π (I k)) μ := by
  rw [iIndepSets_iff]
  intro S B hB
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using (h_indep.isProbabilityMeasure.measure_univ : μ univ = 1)
  | @insert a S haS ih =>
      have hBS : ∀ k, k ∈ S → B k ∈ piiUnionInter π (I k) := by
        intro k hk
        exact hB k (Finset.mem_insert_of_mem hk)
      have hrest_mem :
          (⋂ k ∈ S, B k) ∈ piiUnionInter π (⋃ k ∈ (S : Set κ), I k) :=
        biInter_mem_piiUnionInter_iUnion_blocks π I h_disjoint S hBS
      have hdisj_rest : Disjoint (I a) (⋃ k ∈ (S : Set κ), I k) := by
        refine Set.disjoint_left.mpr ?_
        intro i hiA hiS
        rcases mem_iUnion.1 hiS with ⟨k, hiS⟩
        rcases mem_iUnion.1 hiS with ⟨hk, hik⟩
        exact Set.disjoint_left.mp (h_disjoint fun h ↦ haS (by simpa [h] using hk)) hiA hik
      have hpair :
          IndepSets (piiUnionInter π (I a)) (piiUnionInter π (⋃ k ∈ (S : Set κ), I k)) μ :=
        indepSets_piiUnionInter_of_disjoint h_indep hdisj_rest
      have hrest_measure :
          μ (⋂ k ∈ S, B k) = ∏ k ∈ S, μ (B k) :=
        ih hBS
      -- The inductive step factors off the new block and uses the block-vs-rest independence.
      rw [Finset.set_biInter_insert, Finset.prod_insert haS]
      calc
        μ (B a ∩ ⋂ k ∈ S, B k)
            = μ (B a) * μ (⋂ k ∈ S, B k) := by
                exact
                  (IndepSets_iff _ _ _).1 hpair _ _ (hB a (Finset.mem_insert_self a S)) hrest_mem
        _ = μ (B a) * ∏ k ∈ S, μ (B k) := by rw [hrest_measure]

/- Helper for Theorem 2.26: the `comap` of the block process agrees with the join of the
coordinate `comap` σ-algebras in that block. -/
omit [MeasurableSpace Ω] in
private lemma block_comap_pi_eq_iSup (X : ∀ i, Ω → β i) (I : κ → Set ι) (k : κ) :
    MeasurableSpace.comap (fun ω (j : I k) ↦ X j ω) inferInstance =
      ⨆ j ∈ I k, (mβ j).comap (X j) := by
  let Y : Ω → ((j : I k) → β j) := fun ω j ↦ X j ω
  change MeasurableSpace.comap Y inferInstance = _
  refine le_antisymm ?_ ?_
  · -- Each block coordinate map is measurable with respect to the joined coordinate `comap`s.
    rw [show (inferInstance : MeasurableSpace ((j : I k) → β j)) = MeasurableSpace.pi by rfl]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def]
    refine iSup_le ?_
    intro j
    exact le_iSup_of_le j.1 <| le_iSup_of_le j.2 le_rfl
  · -- Conversely, each coordinate `comap` is dominated by the full block-product `comap`.
    refine iSup₂_le fun j hj ↦ ?_
    simpa [Y] using (MeasurableSpace.comap_le_comap_pi (g := fun j : I k ↦ X j) ⟨j, hj⟩)

/-- Helper for Theorem 2.26: independence of the block cylinder π-systems upgrades directly to
independence of the σ-algebras generated by the measurable blocks. -/
private lemma iIndep_iSup_of_iIndepSets_piiUnionInter_measurable_blocks (μ : Measure Ω)
    (m : ι → MeasurableSpace Ω) (I : κ → Set ι)
    (h_le : ∀ j, m j ≤ ‹MeasurableSpace Ω›)
    (h_block :
      iIndepSets
        (fun k ↦ piiUnionInter (fun j ↦ {s | MeasurableSet[m j] s}) (I k))
        μ) :
    iIndep (fun k ↦ ⨆ j ∈ I k, m j) μ := by
  -- Once every block σ-algebra lives under the ambient measurable space, the standard
  -- π-system extension theorem upgrades block-cylinder independence in one step.
  exact ProbabilityTheory.iIndepSets.iIndep
    (μ := μ)
    (m := fun k ↦ ⨆ j ∈ I k, m j)
    (fun k ↦ iSup₂_le fun j _ ↦ h_le j)
    (fun k ↦ piiUnionInter (fun j ↦ {s | MeasurableSet[m j] s}) (I k))
    (fun k ↦
      isPiSystem_piiUnionInter
        _
        (fun j ↦ @MeasurableSpace.isPiSystem_measurableSet Ω (m j))
        _)
    (fun k ↦ (generateFrom_piiUnionInter_measurableSet m (I k)).symm)
    h_block

/-- Theorem 2.26: If `(X i)ᵢ` is an independent family of random variables and `(I k)ₖ` is a
pairwise disjoint family of index sets, then the block `σ`-algebras
`σ(X j | j ∈ I k) = ⨆ j ∈ I k, (mβ j).comap (X j)` are independent. -/
theorem iIndep_iSup_comap_of_pairwise_disjoint_blocks (μ : Measure Ω) (X : ∀ i, Ω → β i)
    (I : κ → Set ι) (h_disjoint : Pairwise fun k l ↦ Disjoint (I k) (I l))
    (hX : iIndepFun X μ) (hX_meas : ∀ i, Measurable (X i)) :
    iIndep (fun k ↦ ⨆ j ∈ I k, (mβ j).comap (X j)) μ := by
  let π : ι → Set (Set Ω) := fun i ↦ {s | MeasurableSet[(mβ i).comap (X i)] s}
  have hπ : iIndepSets π μ := by
    -- The hypothesis already gives independence of the coordinate `comap` σ-algebras.
    simpa [π] using coordinate_comap_measurable_sets_iIndepSets μ X hX
  have h_block :
      iIndepSets (fun k ↦ piiUnionInter π (I k)) μ :=
    piiUnionInter_iIndepSets_of_pairwise_disjoint_blocks π μ I hπ h_disjoint
  have h_le : ∀ j, (mβ j).comap (X j) ≤ ‹MeasurableSpace Ω› := fun j ↦ (hX_meas j).comap_le
  have h_block_iIndep :
      iIndep (fun k ↦ ⨆ j ∈ I k, (mβ j).comap (X j)) μ :=
    iIndep_iSup_of_iIndepSets_piiUnionInter_measurable_blocks μ
      (fun j ↦ (mβ j).comap (X j)) I h_le h_block
  exact h_block_iIndep

/-- Corollary: grouping an independent family of random variables along pairwise disjoint blocks
yields an independent family of block random variables. -/
theorem iIndepFun_block_of_pairwise_disjoint_blocks (μ : Measure Ω) (X : ∀ i, Ω → β i)
    (I : κ → Set ι) (h_disjoint : Pairwise fun k l ↦ Disjoint (I k) (I l))
    (hX : iIndepFun X μ) (hX_meas : ∀ i, Measurable (X i)) :
    iIndepFun (fun k ω (j : I k) ↦ X j ω) μ := by
  rw [iIndepFun_iff_iIndep]
  simpa [block_comap_pi_eq_iSup] using
    iIndep_iSup_comap_of_pairwise_disjoint_blocks μ X I h_disjoint hX hX_meas
