/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_3_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_3_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_34
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- Auxiliary predicate for Theorem 20.35: a finite measurable partition generates the ambient
σ-algebra when all backward iterates of its atoms generate the ambient measurable space. -/
def is_generator {Ω : Type*} [MeasurableSpace Ω] (τ : Ω → Ω)
    (part : MeasurableFinpartition Ω) : Prop :=
  MeasurableSpace.generateFrom
      (⋃ n : ℕ,
        Set.range fun A : part.parts ↦
          (τ^[n]) ⁻¹' ((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) =
    ‹MeasurableSpace Ω›

/-- Helper for Theorem 20.35: every fixed partition entropy rate is one of the terms in the
Kolmogorov--Sinai supremum. -/
private theorem dynamicalEntropy_le_kolmogorovSinai
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → Ω) (hτ : Measurable τ) (part : MeasurableFinpartition Ω) :
    h(P, τ, hτ; part) ≤ h(P, τ, hτ) := by
  -- Proof comment: the Kolmogorov--Sinai entropy is the supremum over all finite measurable
  -- partitions, so the chosen partition contributes one admissible term.
  rw [kolmogorov_sinai_entropy_def]
  exact le_sSup (Set.mem_range.mpr ⟨part, rfl⟩)

/-- Helper for Theorem 20.35: the atoms of a measurable finite partition cover the whole space. -/
private theorem biUnion_parts_eq_univ
    {Ω : Type*} [MeasurableSpace Ω] (part : MeasurableFinpartition Ω) :
    (⋃ s ∈ part.parts, ((s : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) = Set.univ := by
  -- Proof comment: the partition axioms already say that the supremum of the atoms is `⊤`.
  simpa [MeasureTheory.preVariation.Finset.sup_measurableSetSubtype_eq_biUnion] using
    congrArg (fun s : Subtype (MeasurableSet : Set Ω → Prop) ↦ (s : Set Ω)) part.sup_parts

/-- Helper for Theorem 20.35: take the union of the atoms indexed by a finite set of partition
labels. -/
private def blockPartsUnion
    {Ω : Type*} [MeasurableSpace Ω] (part : MeasurableFinpartition Ω)
    (U : Finset part.parts) : Set Ω :=
  ⋃ A ∈ U, (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω))

/-- Helper for Theorem 20.35: a finite union of atoms of a measurable finite partition is
measurable. -/
private theorem measurableSet_blockPartsUnion
    {Ω : Type*} [MeasurableSpace Ω] (part : MeasurableFinpartition Ω)
    (U : Finset part.parts) :
    MeasurableSet (blockPartsUnion part U) := by
  -- Proof comment: each partition atom is measurable, and the indexed union is finite.
  classical
  unfold blockPartsUnion
  exact MeasurableSet.iUnion fun A ↦ MeasurableSet.iUnion fun _ ↦ A.1.2

/-- Helper for Theorem 20.35: a candidate long-block approximation is encoded by its block length
and the finite family of block atoms used in the approximation. -/
private structure BlockApproximationData
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) where
  length : ℕ+
  atoms : Finset ((part.block τ hτ length).parts)
  carrier : Set Ω

/-- Helper for Theorem 20.35: a block approximation is good if its carrier set is within the
prescribed symmetric-difference error budget. -/
private def BlockApproximationGood
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {τ : Ω → Ω} (hτ : Measurable τ) (part : MeasurableFinpartition Ω)
    (s : Set Ω) (ε : ℝ) (approx : BlockApproximationData hτ part) : Prop :=
  P ((s \ approx.carrier) ∪ (approx.carrier \ s)) < ENNReal.ofReal ε

/-- Helper for Theorem 20.35: choose the unique partition atom containing each point. -/
private noncomputable def indexedPart
    {Ω : Type*} [MeasurableSpace Ω] (part : MeasurableFinpartition Ω) :
    IndexedPartition fun s : part.parts ↦
      ((s.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) := by
  classical
  refine IndexedPartition.mk' _ ?_ ?_ ?_
  · intro s t hst
    have hdisj :
        Disjoint (s.1 : Subtype (MeasurableSet : Set Ω → Prop)) t.1 :=
      part.disjoint s.2 t.2 (by simpa using hst)
    exact (disjoint_subtype_iff (fun {_ _} hx hy ↦ hx.inter hy) MeasurableSet.empty).1 hdisj
  · intro s
    rw [Set.nonempty_iff_ne_empty]
    intro hs
    apply part.ne_bot s.2
    ext ω
    simp [hs]
  · intro ω
    have :
        ω ∈ ⋃ s ∈ part.parts, ((s : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) := by
      rw [biUnion_parts_eq_univ part]
      simp
    simpa [Set.mem_iUnion] using this

/-- Helper for Theorem 20.35: a point lies in the atom selected by the canonical partition code. -/
private theorem mem_toSimpleFunc_atom
    {Ω : Type*} [MeasurableSpace Ω] (part : MeasurableFinpartition Ω) (ω : Ω) :
    ω ∈ (((part.toSimpleFunc ω).1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) := by
  -- Proof comment: unfold the indexed partition model so the selected atom contains `ω`
  -- by construction.
  change ω ∈ (((indexedPart part).index ω : part.parts).1 : Set Ω)
  exact (indexedPart part).mem_index ω

/-- Helper for Theorem 20.35: membership in a partition atom is equivalent to selecting that atom
under the canonical partition code. -/
private theorem mem_atom_iff_toSimpleFunc_eq
    {Ω : Type*} [MeasurableSpace Ω] (part : MeasurableFinpartition Ω)
    {A : part.parts} {ω : Ω} :
    ω ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) ↔
      part.toSimpleFunc ω = A := by
  -- Proof comment: after rewriting through the indexed partition, atom membership is exactly the
  -- statement that the index map chooses `A`.
  change ω ∈ ((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) ↔
    (indexedPart part).index ω = A
  rw [← (indexedPart part).mem_iff_index_eq]

/-- Helper for Theorem 20.35: two points in the same atom have the same canonical partition code. -/
private theorem toSimpleFunc_eq_of_mem_atom
    {Ω : Type*} [MeasurableSpace Ω] (part : MeasurableFinpartition Ω)
    {A : part.parts} {ω ω' : Ω}
    (hω : ω ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)))
    (hω' : ω' ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω))) :
    part.toSimpleFunc ω = part.toSimpleFunc ω' := by
  -- Proof comment: both points are coded by the unique atom `A` containing them.
  rw [(mem_atom_iff_toSimpleFunc_eq part).mp hω, (mem_atom_iff_toSimpleFunc_eq part).mp hω']

/-- Helper for Theorem 20.35: every nonempty fiber of a simple function is an atom of the
partition built from that simple function. -/
private theorem fiber_mem_parts_of_ofSimpleFunc
    {Ω : Type*} [MeasurableSpace Ω] {α : Type*} (f : SimpleFunc Ω α)
    {a : α} (ha : a ∈ f.range) :
    (⟨f ⁻¹' ({a} : Set α), f.measurableSet_fiber a⟩ :
      Subtype (MeasurableSet : Set Ω → Prop)) ∈
      (MeasurableFinpartition.ofSimpleFunc f).parts := by
  classical
  -- Proof comment: `ofSimpleFunc` stores exactly the nonempty singleton fibers of `f`.
  change
    (⟨f ⁻¹' ({a} : Set α), f.measurableSet_fiber a⟩ :
      Subtype (MeasurableSet : Set Ω → Prop)) ∈
      Finset.preimage _ Subtype.val Subtype.val_injective.injOn
  exact Finset.mem_preimage.mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

/-- Helper for Theorem 20.35: every atom of `MeasurableFinpartition.ofSimpleFunc g` is the fiber
of `g` over some value in the range of `g`. -/
private theorem exists_fiber_eq_of_ofSimpleFunc_part
    {Ω : Type*} [MeasurableSpace Ω] {α : Type*} (g : SimpleFunc Ω α)
    (A : (MeasurableFinpartition.ofSimpleFunc g).parts) :
    ∃ a ∈ g.range, g ⁻¹' ({a} : Set α) =
      (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) := by
  classical
  have hA :
      (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) ∈
        g.range.image (fun a ↦ g ⁻¹' ({a} : Set α)) := by
    -- Proof comment: unpack the `ofSimpleFunc` atom back to the stored singleton-fiber
    -- presentation.
    have hA' :
        (A.1 : Subtype (MeasurableSet : Set Ω → Prop)) ∈
          Finset.preimage (g.range.image (fun a ↦ g ⁻¹' ({a} : Set α)))
            Subtype.val Subtype.val_injective.injOn := by
      exact A.2
    exact Finset.mem_preimage.mp hA'
  rcases Finset.mem_image.mp hA with ⟨a, ha, hAeq⟩
  exact ⟨a, ha, hAeq⟩

/-- Helper for Theorem 20.35: each atom of `MeasurableFinpartition.ofSimpleFunc g` remembers the
unique value whose fiber it is. -/
private noncomputable def ofSimpleFuncFiberValue
    {Ω : Type*} [MeasurableSpace Ω] {α : Type*} (g : SimpleFunc Ω α)
    (A : (MeasurableFinpartition.ofSimpleFunc g).parts) : α :=
  Classical.choose (exists_fiber_eq_of_ofSimpleFunc_part g A)

/-- Helper for Theorem 20.35: the underlying set of an `ofSimpleFunc` atom is exactly the fiber
over its remembered value. -/
private theorem ofSimpleFuncFiberValue_spec
    {Ω : Type*} [MeasurableSpace Ω] {α : Type*} (g : SimpleFunc Ω α)
    (A : (MeasurableFinpartition.ofSimpleFunc g).parts) :
    g ⁻¹' ({ofSimpleFuncFiberValue g A} : Set α) =
      (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) := by
  -- Proof comment: unfold the witness chosen by `ofSimpleFuncFiberValue`.
  exact (Classical.choose_spec (exists_fiber_eq_of_ofSimpleFunc_part g A)).2

/-- Helper for Theorem 20.35: the original simple function factors through the atom code of the
partition built from its fibers. -/
private theorem simpleFunc_eq_ofSimpleFuncFiberValue_comp_toSimpleFunc
    {Ω : Type*} [MeasurableSpace Ω] {α : Type*} (g : SimpleFunc Ω α) :
    g = fun ω ↦ ofSimpleFuncFiberValue g ((MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω) := by
  funext ω
  -- Proof comment: the selected atom is the fiber containing `ω`, so its remembered value is
  -- exactly `g ω`.
  have hmem := mem_toSimpleFunc_atom (MeasurableFinpartition.ofSimpleFunc g) ω
  have hspec :=
    ofSimpleFuncFiberValue_spec g ((MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω)
  have :
      ω ∈ g ⁻¹'
        ({ofSimpleFuncFiberValue g ((MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω)} :
          Set α) := by
    simpa [hspec] using hmem
  simpa using this

/-- Helper for Theorem 20.35: the remembered fiber values injectively label the atoms of
`MeasurableFinpartition.ofSimpleFunc g`. -/
private theorem ofSimpleFuncFiberValue_injective
    {Ω : Type*} [MeasurableSpace Ω] {α : Type*} (g : SimpleFunc Ω α) :
    Function.Injective (ofSimpleFuncFiberValue g) := by
  intro A B hAB
  -- Proof comment: equal remembered values give equal singleton fibers, hence equal atoms.
  apply Subtype.ext
  apply Subtype.ext
  calc
    (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) =
        g ⁻¹' ({ofSimpleFuncFiberValue g A} : Set α) := by
      symm
      exact ofSimpleFuncFiberValue_spec g A
    _ = g ⁻¹' ({ofSimpleFuncFiberValue g B} : Set α) := by
      rw [hAB]
    _ = (((B.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) := by
      exact ofSimpleFuncFiberValue_spec g B

/-- Helper for Theorem 20.35: a finite-valued code that is constant on each atom of a partition
factors through the canonical partition code. -/
private theorem ofSimpleFunc_factorsThroughPartitionOfMonochromatic
    {Ω : Type*} [MeasurableSpace Ω] {α : Type*} (part : MeasurableFinpartition Ω)
    (g : SimpleFunc Ω α)
    (hmono :
      ∀ {A : part.parts} {ω ω' : Ω},
        ω ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) →
        ω' ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) →
        g ω = g ω') :
    ∃ Φ : part.parts → (MeasurableFinpartition.ofSimpleFunc g).parts,
      ((MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc :
          Ω → (MeasurableFinpartition.ofSimpleFunc g).parts) =
        fun ω ↦ Φ (part.toSimpleFunc ω) := by
  classical
  have hreps :
      ∀ A : part.parts,
        ∃ ω : Ω, ω ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) := by
    intro A
    have hA_nonempty :
        ((((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) : Set Ω).Nonempty := by
      by_contra hA_nonempty
      apply part.ne_bot A.2
      ext ω
      simp [Set.not_nonempty_iff_eq_empty.mp hA_nonempty]
    exact hA_nonempty
  choose rep hrep using hreps
  let Φ : part.parts → (MeasurableFinpartition.ofSimpleFunc g).parts := fun A ↦
    ⟨⟨g ⁻¹' ({g (rep A)} : Set α), g.measurableSet_fiber (g (rep A))⟩,
      fiber_mem_parts_of_ofSimpleFunc g (g.mem_range_self (rep A))⟩
  refine ⟨Φ, funext ?_⟩
  intro ω
  -- Proof comment: the selected atom contains `ω`, so monochromaticity identifies `g ω` with the
  -- representative value used to define `Φ`.
  apply (mem_atom_iff_toSimpleFunc_eq (MeasurableFinpartition.ofSimpleFunc g)).mp
  change g ω = g (rep (part.toSimpleFunc ω))
  exact hmono (mem_toSimpleFunc_atom part ω) (hrep (part.toSimpleFunc ω))

/-- Helper for Theorem 20.35: each fiber of the transparent block code is measurable. -/
private theorem measurableSet_prefixBlockCode_fiber
    {Ω : Type*} [MeasurableSpace Ω] (τ : Ω → Ω) (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) (n : ℕ+) (s : Fin n → part.parts) :
    MeasurableSet ((fun ω : Ω ↦ fun i : Fin n ↦ part.toSimpleFunc ((τ^[i]) ω)) ⁻¹' {s}) := by
  have hmeas : Measurable (fun ω : Ω ↦ fun i : Fin n ↦ part.toSimpleFunc ((τ^[i]) ω)) := by
    -- Proof comment: each coordinate of the transparent block code is measurable.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact part.toSimpleFunc.measurable.comp (Measurable.iterate hτ i)
  exact hmeas (measurableSet_singleton s)

/-- Helper for Theorem 20.35: the transparent block code records the first `n` visited atoms of
`part`. -/
private noncomputable def prefixBlockCode
    {Ω : Type*} [MeasurableSpace Ω] (τ : Ω → Ω) (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) (n : ℕ+) :
    SimpleFunc Ω (Fin n → part.parts) where
  toFun := fun ω : Ω ↦ fun i : Fin n ↦ part.toSimpleFunc ((τ^[i]) ω)
  measurableSet_fiber' := measurableSet_prefixBlockCode_fiber τ hτ part n
  finite_range' := Set.toFinite _

/-- Helper for Theorem 20.35: truncate a long block word to its initial shorter prefix. -/
private def prefixRestriction
    {α : Type*} {N M : ℕ+} (hNM : N ≤ M) : (Fin M → α) → (Fin N → α) :=
  fun w i ↦ w (Fin.castLE ((PNat.coe_le_coe N M).2 hNM) i)

/-- Helper for Theorem 20.35: the short transparent block code is the truncation of any longer
transparent block code. -/
private theorem prefixBlockCode_eq_prefixRestriction
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) {N M : ℕ+} (hNM : N ≤ M) :
    prefixBlockCode τ hτ part N =
      fun ω ↦ prefixRestriction hNM (prefixBlockCode τ hτ part M ω) := by
  -- Proof comment: both sides read off the same first `N` iterates of `τ`; the right-hand side
  -- only views them through the longer block word.
  funext ω i
  simp [prefixRestriction, prefixBlockCode]

/-- Helper for Theorem 20.35: the measurable sets determined by one finite prefix code form a
member of the reusable prefix-code approximation family. -/
private def prefixBlockPreimageFamily
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) : Set (Set Ω) :=
  Set.range fun p : Σ n : ℕ+, Set (Fin n → part.parts) ↦
    (prefixBlockCode τ hτ part p.1) ⁻¹' p.2

/-- Helper for Theorem 20.35: every member of the prefix-code approximation family is measurable. -/
private theorem measurableSet_of_mem_prefixBlockPreimageFamily
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) {s : Set Ω}
    (hs : s ∈ prefixBlockPreimageFamily hτ part) :
    MeasurableSet s := by
  rcases hs with ⟨⟨N, S⟩, rfl⟩
  -- Proof comment: each family member is a preimage of an arbitrary subset of a finite code
  -- alphabet under the measurable prefix code.
  exact (prefixBlockCode τ hτ part N).measurable (MeasurableSet.of_discrete (s := S))

/-- Helper for Theorem 20.35: the prefix-code approximation family is an algebra of sets. -/
private theorem isSetAlgebra_prefixBlockPreimageFamily
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) :
    IsSetAlgebra (prefixBlockPreimageFamily hτ part) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: the empty set is the preimage of the empty code subset.
    refine Set.mem_range.mpr ⟨⟨(1 : ℕ+), (∅ : Set (Fin (1 : ℕ+) → part.parts))⟩, ?_⟩
    ext ω
    rfl
  · rintro s ⟨⟨N, S⟩, rfl⟩
    -- Proof comment: complements stay in the same prefix length by complementing the code subset.
    refine Set.mem_range.mpr ⟨⟨N, Sᶜ⟩, ?_⟩
    ext ω
    simp
  · rintro s t ⟨⟨N, S⟩, rfl⟩ ⟨⟨M, T⟩, rfl⟩
    let K : ℕ+ := max N M
    let S' : Set (Fin K → part.parts) :=
      {w | prefixRestriction (show N ≤ K from le_max_left N M) w ∈ S}
    let T' : Set (Fin K → part.parts) :=
      {w | prefixRestriction (show M ≤ K from le_max_right N M) w ∈ T}
    -- Proof comment: raise both prefix constraints to one common block length and take the union
    -- there.
    refine Set.mem_range.mpr ⟨⟨K, S' ∪ T'⟩, ?_⟩
    ext ω
    simp [S', T',
      prefixBlockCode_eq_prefixRestriction (hτ := hτ) (part := part)
        (hNM := show N ≤ K from le_max_left N M),
      prefixBlockCode_eq_prefixRestriction (hτ := hτ) (part := part)
        (hNM := show M ≤ K from le_max_right N M)]

/-- Helper for Theorem 20.35: each generator atom already belongs to the reusable prefix-code
approximation family. -/
private theorem iterateAtom_mem_prefixBlockPreimageFamily
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) (k : ℕ) (A : part.parts) :
    (τ^[k]) ⁻¹' (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) ∈
      prefixBlockPreimageFamily hτ part := by
  -- Proof comment: the `k`-th generator atom is exactly the set of length-`k + 1` block words
  -- whose `k`-th coordinate equals `A`.
  refine Set.mem_range.mpr ⟨⟨⟨k + 1, Nat.succ_pos _⟩, {w | w ⟨k, Nat.lt_succ_self k⟩ = A}⟩, ?_⟩
  ext ω
  change part.toSimpleFunc ((τ^[k]) ω) = A ↔ ((τ^[k]) ω) ∈
    (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω))
  simpa using (mem_atom_iff_toSimpleFunc_eq part (A := A) (ω := (τ^[k]) ω)).symm

/-- Helper for Theorem 20.35: the owner block partition is definitionally the partition built from
the transparent block code. -/
private theorem block_eq_ofSimpleFunc_prefixBlockCode
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) (n : ℕ+) :
    part.block τ hτ n = MeasurableFinpartition.ofSimpleFunc (prefixBlockCode τ hτ part n) := by
  -- Proof comment: both sides unfold to the same `ofSimpleFunc` presentation of the block code.
  rfl

/-- Helper for Theorem 20.35: equality of atoms in an `ofSimpleFunc` partition forces equality of
the underlying simple-function values. -/
private theorem eq_of_toSimpleFunc_eq_of_ofSimpleFunc
    {Ω : Type*} [MeasurableSpace Ω] {α : Type*} (g : SimpleFunc Ω α) {ω ω' : Ω}
    (h :
      (MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω =
        (MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω') :
    g ω = g ω' := by
  -- Proof comment: factor `g` through its fiber partition and compare the remembered labels.
  calc
    g ω =
        ofSimpleFuncFiberValue g ((MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω) := by
      simpa using congrArg (fun f : Ω → α ↦ f ω)
        (simpleFunc_eq_ofSimpleFuncFiberValue_comp_toSimpleFunc g)
    _ = ofSimpleFuncFiberValue g ((MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω') := by
      rw [h]
    _ = g ω' := by
      simpa using congrArg (fun f : Ω → α ↦ f ω')
        (simpleFunc_eq_ofSimpleFuncFiberValue_comp_toSimpleFunc g).symm

/-- Helper for Theorem 20.35: the preimage of a value set under a finite-valued code is the union
of those atoms of the associated `ofSimpleFunc` partition whose remembered values lie in that set.
-/
private theorem preimage_eq_biUnion_parts_filter_of_ofSimpleFuncFiberValue
    {Ω : Type*} [MeasurableSpace Ω] {α : Type*} (g : SimpleFunc Ω α) (S : Set α)
    [DecidablePred fun A : (MeasurableFinpartition.ofSimpleFunc g).parts =>
      ofSimpleFuncFiberValue g A ∈ S] :
    g ⁻¹' S =
      blockPartsUnion (MeasurableFinpartition.ofSimpleFunc g)
        ((MeasurableFinpartition.ofSimpleFunc g).parts.attach.filter
          (fun A ↦ ofSimpleFuncFiberValue g A ∈ S)) := by
  ext ω
  constructor
  · intro hω
    -- Proof comment: choose the fiber atom selected by `ω`; its remembered value is exactly
    -- `g ω`, so it appears in the filtered union.
    let A : (MeasurableFinpartition.ofSimpleFunc g).parts :=
      (MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω
    refine Set.mem_iUnion.2 ⟨A, ?_⟩
    refine Set.mem_iUnion.2 ?_
    have hvalue : g ω = ofSimpleFuncFiberValue g A := by
      simpa [A] using congrArg (fun f : Ω → α ↦ f ω)
        (simpleFunc_eq_ofSimpleFuncFiberValue_comp_toSimpleFunc g)
    refine ⟨by simpa [A, hvalue] using hω, ?_⟩
    exact mem_toSimpleFunc_atom (MeasurableFinpartition.ofSimpleFunc g) ω
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨A, hω⟩
    rcases Set.mem_iUnion.1 hω with ⟨hA, hωA⟩
    have hAS : ofSimpleFuncFiberValue g A ∈ S := by
      exact (Finset.mem_filter.mp hA).2
    have hvalue : g ω = ofSimpleFuncFiberValue g A := by
      have : ω ∈ g ⁻¹' ({ofSimpleFuncFiberValue g A} : Set α) := by
        simpa [ofSimpleFuncFiberValue_spec g A] using hωA
      simpa using this
    simpa [hvalue] using hAS

/-- Helper for Theorem 20.35: a finite union of atoms of `MeasurableFinpartition.ofSimpleFunc g`
is the preimage of the corresponding finite set of remembered values. -/
private theorem blockPartsUnion_eq_preimage_image_of_ofSimpleFuncFiberValue
    {Ω : Type*} [MeasurableSpace Ω] {α : Type*} [DecidableEq α] (g : SimpleFunc Ω α)
    (U : Finset (MeasurableFinpartition.ofSimpleFunc g).parts) :
    blockPartsUnion (MeasurableFinpartition.ofSimpleFunc g) U =
      g ⁻¹' (↑(U.image (ofSimpleFuncFiberValue g)) : Set α) := by
  ext ω
  constructor
  · intro hω
    -- Proof comment: any point in the union belongs to one selected atom, so its `g`-value is one
    -- of the remembered labels carried by `U`.
    rcases Set.mem_iUnion.1 hω with ⟨A, hω⟩
    rcases Set.mem_iUnion.1 hω with ⟨hA, hωA⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨A, hA, ?_⟩)
    have hvalue : g ω = ofSimpleFuncFiberValue g A := by
      have : ω ∈ g ⁻¹' ({ofSimpleFuncFiberValue g A} : Set α) := by
        simpa [ofSimpleFuncFiberValue_spec g A] using hωA
      simpa using this
    exact hvalue.symm
  · intro hω
    have hω' : g ω ∈ U.image (ofSimpleFuncFiberValue g) := Finset.mem_coe.1 hω
    rcases Finset.mem_image.1 hω' with ⟨A, hA, hvalue⟩
    refine Set.mem_iUnion.2 ⟨A, Set.mem_iUnion.2 ⟨hA, ?_⟩⟩
    have : ω ∈ g ⁻¹' ({ofSimpleFuncFiberValue g A} : Set α) := by
      simpa [hvalue] using (show g ω ∈ ({g ω} : Set α) by simp)
    simpa [ofSimpleFuncFiberValue_spec g A] using this

/-- Helper for Theorem 20.35: equal simple-function values give equal atoms in the partition built
from that simple function. -/
private theorem toSimpleFunc_eq_of_eq_of_ofSimpleFunc
    {Ω : Type*} [MeasurableSpace Ω] {α : Type*} (g : SimpleFunc Ω α) {ω ω' : Ω}
    (h : g ω = g ω') :
    (MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω =
      (MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω' := by
  let A : (MeasurableFinpartition.ofSimpleFunc g).parts := by
    refine ⟨⟨g ⁻¹' ({g ω} : Set α), g.measurableSet_fiber (g ω)⟩, ?_⟩
    exact fiber_mem_parts_of_ofSimpleFunc g (g.mem_range_self ω)
  -- Proof comment: both points lie in the same singleton fiber of `g`, hence in the same atom of
  -- `MeasurableFinpartition.ofSimpleFunc g`.
  refine toSimpleFunc_eq_of_mem_atom (part := MeasurableFinpartition.ofSimpleFunc g) (A := A) ?_ ?_
  · simpa [A]
  · simpa [A, h] using (show ω' ∈ g ⁻¹' ({g ω'} : Set α) by simp)

/-- Helper for Theorem 20.35: points in the same atom of a block partition have identical
transparent prefix codes. -/
private theorem sameBlockAtom_samePrefixCoordinates
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) (n : ℕ+) {ω ω' : Ω}
    (h :
      (part.block τ hτ n).toSimpleFunc ω =
        (part.block τ hτ n).toSimpleFunc ω') :
    prefixBlockCode τ hτ part n ω = prefixBlockCode τ hτ part n ω' := by
  have h' :
      (MeasurableFinpartition.ofSimpleFunc (prefixBlockCode τ hτ part n)).toSimpleFunc ω =
        (MeasurableFinpartition.ofSimpleFunc (prefixBlockCode τ hτ part n)).toSimpleFunc ω' := by
    -- Proof comment: first rewrite the owner block partition to the transparent `ofSimpleFunc`
    -- presentation.
    simpa [block_eq_ofSimpleFunc_prefixBlockCode hτ part n] using h
  -- Proof comment: equality of atoms in an `ofSimpleFunc` partition is exactly equality of the
  -- underlying code.
  exact eq_of_toSimpleFunc_eq_of_ofSimpleFunc (prefixBlockCode τ hτ part n) h'

/-- Helper for Theorem 20.35: if a code factors through the `N`-block partition of `part`, then
its length-`n` block partition factors through the long block partition of length `N + n - 1`. -/
private theorem blockFactor_of_block
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) {α : Type*} (g : SimpleFunc Ω α)
    {N : ℕ+} {ψ : (part.block τ hτ N).parts → α}
    (hg : g = fun ω ↦ ψ ((part.block τ hτ N).toSimpleFunc ω)) (n : ℕ+) :
    ∃ Φ : (part.block τ hτ (N + n - 1)).parts →
        ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ n).parts,
      (((MeasurableFinpartition.ofSimpleFunc g).block τ hτ n).toSimpleFunc :
          Ω → ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ n).parts) =
        fun ω ↦ Φ ((part.block τ hτ (N + n - 1)).toSimpleFunc ω) := by
  have hmono :
      ∀ {A : (part.block τ hτ (N + n - 1)).parts} {ω ω' : Ω},
        ω ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) →
        ω' ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) →
        prefixBlockCode τ hτ (MeasurableFinpartition.ofSimpleFunc g) n ω =
          prefixBlockCode τ hτ (MeasurableFinpartition.ofSimpleFunc g) n ω' := by
    intro A ω ω' hω hω'
    have hsameLong :
        (part.block τ hτ (N + n - 1)).toSimpleFunc ω =
          (part.block τ hτ (N + n - 1)).toSimpleFunc ω' :=
      toSimpleFunc_eq_of_mem_atom (part.block τ hτ (N + n - 1)) hω hω'
    have hprefixLong :
        prefixBlockCode τ hτ part (N + n - 1) ω =
          prefixBlockCode τ hτ part (N + n - 1) ω' :=
      sameBlockAtom_samePrefixCoordinates hτ part (N + n - 1) hsameLong
    funext i
    have hNBlock :
        (part.block τ hτ N).toSimpleFunc ((τ^[i]) ω) =
          (part.block τ hτ N).toSimpleFunc ((τ^[i]) ω') := by
      have hcode :
          prefixBlockCode τ hτ part N ((τ^[i]) ω) =
            prefixBlockCode τ hτ part N ((τ^[i]) ω') := by
        funext j
        have hi_lt : (i : ℕ) < (n : ℕ) := i.2
        have hj_lt : (j : ℕ) < (N : ℕ) := j.2
        have hij_lt : (j : ℕ) + (i : ℕ) < ((N + n - 1 : ℕ+) : ℕ) := by
          pnat_to_nat
          omega
        have hcoord := congrFun hprefixLong
          (⟨(j : ℕ) + (i : ℕ), hij_lt⟩ : Fin (((N + n - 1 : ℕ+) : ℕ)))
        -- Proof comment: the long transparent block already contains the length-`N` window
        -- starting at the shift `i`.
        simpa [prefixBlockCode, Function.iterate_add_apply] using hcoord
      have hcode' :
          (MeasurableFinpartition.ofSimpleFunc (prefixBlockCode τ hτ part N)).toSimpleFunc
              ((τ^[i]) ω) =
            (MeasurableFinpartition.ofSimpleFunc (prefixBlockCode τ hτ part N)).toSimpleFunc
              ((τ^[i]) ω') :=
        toSimpleFunc_eq_of_eq_of_ofSimpleFunc (prefixBlockCode τ hτ part N) hcode
      simpa [block_eq_ofSimpleFunc_prefixBlockCode hτ part N] using hcode'
    have hgω :
        g ((τ^[i]) ω) = ψ ((part.block τ hτ N).toSimpleFunc ((τ^[i]) ω)) := by
      simpa using congrArg (fun f : Ω → α ↦ f ((τ^[i]) ω)) hg
    have hgω' :
        g ((τ^[i]) ω') = ψ ((part.block τ hτ N).toSimpleFunc ((τ^[i]) ω')) := by
      simpa using congrArg (fun f : Ω → α ↦ f ((τ^[i]) ω')) hg
    have hgshift :
        g ((τ^[i]) ω) = g ((τ^[i]) ω') := by
      calc
        g ((τ^[i]) ω) = ψ ((part.block τ hτ N).toSimpleFunc ((τ^[i]) ω)) := hgω
        _ = ψ ((part.block τ hτ N).toSimpleFunc ((τ^[i]) ω')) := by
          exact congrArg ψ hNBlock
        _ = g ((τ^[i]) ω') := hgω'.symm
    -- Proof comment: equality of the underlying `g`-values forces equality of the corresponding
    -- atoms in `MeasurableFinpartition.ofSimpleFunc g`.
    exact toSimpleFunc_eq_of_eq_of_ofSimpleFunc g hgshift
  -- Proof comment: once the transparent `g`-block code is monochromatic on long `part`-block
  -- atoms, it factors through the owner long block partition.
  simpa [block_eq_ofSimpleFunc_prefixBlockCode hτ (MeasurableFinpartition.ofSimpleFunc g) n] using
    (ofSimpleFunc_factorsThroughPartitionOfMonochromatic
      (part.block τ hτ (N + n - 1))
      (prefixBlockCode τ hτ (MeasurableFinpartition.ofSimpleFunc g) n)
      hmono)

/-- Helper for Theorem 20.35: the prefix-code approximation family generated by all finite block
codes already generates the ambient measurable space under the generator hypothesis. -/
private theorem generateFrom_prefixBlockPreimageFamily_eq
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) (hgen : is_generator τ part) :
    MeasurableSpace.generateFrom (prefixBlockPreimageFamily hτ part) = ‹MeasurableSpace Ω› := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · intro s hs
    exact measurableSet_of_mem_prefixBlockPreimageFamily hτ part hs
  · let 𝒢 : Set (Set Ω) :=
      ⋃ n : ℕ,
        Set.range fun A : part.parts ↦
          (τ^[n]) ⁻¹' ((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)
    have hsubset : 𝒢 ⊆ prefixBlockPreimageFamily hτ part := by
      intro s hs
      rw [Set.mem_iUnion] at hs
      rcases hs with ⟨k, hs⟩
      rcases hs with ⟨A, rfl⟩
      exact iterateAtom_mem_prefixBlockPreimageFamily hτ part k A
    calc
      ‹MeasurableSpace Ω› = MeasurableSpace.generateFrom 𝒢 := by
        simpa [is_generator] using hgen.symm
      _ ≤ MeasurableSpace.generateFrom (prefixBlockPreimageFamily hτ part) :=
        MeasurableSpace.generateFrom_mono hsubset

/-- Helper for Theorem 20.35: every measurable set can be approximated in measure by a union of
atoms of one sufficiently long block partition of a generating partition. -/
private theorem exists_unionBlockAtoms_symmDiff_lt_of_generator
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : Measurable τ) (part : MeasurableFinpartition Ω)
    (hgen : is_generator τ part) {s : Set Ω} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ+, ∃ U : Finset (part.block τ hτ N).parts,
      P ((s \ blockPartsUnion (part.block τ hτ N) U) ∪
          (blockPartsUnion (part.block τ hτ N) U \ s)) < ENNReal.ofReal ε := by
  classical
  let 𝒜 : Set (Set Ω) := prefixBlockPreimageFamily hτ part
  have h𝒜 : IsSetAlgebra 𝒜 := isSetAlgebra_prefixBlockPreimageFamily hτ part
  have hgen𝒜 :
      MeasurableSpace.generateFrom 𝒜 = ‹MeasurableSpace Ω› :=
    generateFrom_prefixBlockPreimageFamily_eq hτ part hgen
  let hdense : P.MeasureDense 𝒜 :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite (μ := P) (𝒜 := 𝒜) h𝒜 hgen𝒜.symm
  rcases hdense.fin_meas_approx hs (measure_ne_top P s) ε hε with ⟨t, ht, -, hclose⟩
  rcases ht with ⟨⟨N, S⟩, rfl⟩
  let U : Finset (part.block τ hτ N).parts :=
    (part.block τ hτ N).parts.attach.filter
      (fun A ↦ ofSimpleFuncFiberValue (prefixBlockCode τ hτ part N) A ∈ S)
  have hpreimage :
      (prefixBlockCode τ hτ part N) ⁻¹' S = blockPartsUnion (part.block τ hτ N) U := by
    -- Proof comment: convert the approximating prefix-code event into the corresponding finite
    -- union of nonempty block atoms.
    simpa [U, block_eq_ofSimpleFunc_prefixBlockCode hτ part N] using
      preimage_eq_biUnion_parts_filter_of_ofSimpleFuncFiberValue
        (g := prefixBlockCode τ hτ part N) (S := S)
  refine ⟨N, U, ?_⟩
  -- Proof comment: the measure approximation delivered by `MeasureDense` is exactly the desired
  -- symmetric-difference estimate after rewriting the approximant.
  simpa [hpreimage]
    using hclose

/-- Helper for Theorem 20.35: a union of `N`-block atoms can be rewritten as a union of atoms of
any longer `M`-block partition. -/
private theorem exists_liftBlockPartsUnion_eq
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) {N M : ℕ+} (hNM : N ≤ M)
    (U : Finset (part.block τ hτ N).parts) :
    ∃ V : Finset (part.block τ hτ M).parts,
      blockPartsUnion (part.block τ hτ N) U =
        blockPartsUnion (part.block τ hτ M) V := by
  classical
  let shortValues : Finset (Fin N → part.parts) :=
    U.image (ofSimpleFuncFiberValue (prefixBlockCode τ hτ part N))
  let longValueSet : Set (Fin M → part.parts) :=
    {w | prefixRestriction hNM w ∈ (↑shortValues : Set (Fin N → part.parts))}
  let V : Finset (part.block τ hτ M).parts :=
    (part.block τ hτ M).parts.attach.filter
      (fun A ↦ ofSimpleFuncFiberValue (prefixBlockCode τ hτ part M) A ∈ longValueSet)
  refine ⟨V, ?_⟩
  calc
    blockPartsUnion (part.block τ hτ N) U =
        (prefixBlockCode τ hτ part N) ⁻¹' (↑shortValues : Set (Fin N → part.parts)) := by
      -- Proof comment: rewrite the chosen short-block atoms as the preimage of their remembered
      -- value set.
      simpa [shortValues, block_eq_ofSimpleFunc_prefixBlockCode hτ part N] using
        (blockPartsUnion_eq_preimage_image_of_ofSimpleFuncFiberValue
          (g := prefixBlockCode τ hτ part N) U)
    _ = (prefixBlockCode τ hτ part M) ⁻¹' longValueSet := by
      -- Proof comment: lifting from length `N` to `M` only asks that the longer block word has a
      -- prefix among the selected short remembered values.
      ext ω
      simp [longValueSet,
        prefixBlockCode_eq_prefixRestriction (hτ := hτ) (part := part) (hNM := hNM)]
    _ = blockPartsUnion (part.block τ hτ M) V := by
      -- Proof comment: convert the lifted long-block preimage back to the corresponding finite
      -- union of long-block atoms.
      simpa [V, block_eq_ofSimpleFunc_prefixBlockCode hτ part M, longValueSet] using
        (preimage_eq_biUnion_parts_filter_of_ofSimpleFuncFiberValue
          (g := prefixBlockCode τ hτ part M) (S := longValueSet))

/-- Helper for Theorem 20.35: the atomwise generator approximations can be promoted to one common
long block length while preserving a small total symmetric-difference budget. -/
private theorem existsCommonLengthBlockAtomApproximationFamily
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : Measurable τ) (part : MeasurableFinpartition Ω)
    (hgen : is_generator τ part) (q : MeasurableFinpartition Ω) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ+, ∃ U : q.parts → Finset (part.block τ hτ N).parts,
      (∑ A : q.parts,
          P ((((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) \
                blockPartsUnion (part.block τ hτ N) (U A)) ∪
              (blockPartsUnion (part.block τ hτ N) (U A) \
                (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω))))) <
        ENNReal.ofReal δ := by
  classical
  let δshare : ℝ := δ / (Fintype.card q.parts + 1)
  have hδshare : 0 < δshare := by
    dsimp [δshare]
    positivity
  have happrox :
      ∀ A : q.parts,
        ∃ N : ℕ+, ∃ V : Finset (part.block τ hτ N).parts,
          P ((((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) \
                blockPartsUnion (part.block τ hτ N) V) ∪
              (blockPartsUnion (part.block τ hτ N) V \
                (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)))) <
            ENNReal.ofReal δshare := by
    intro A
    -- Proof comment: approximate each competitor atom separately by a union of atoms from some
    -- sufficiently long block partition of the generator.
    exact exists_unionBlockAtoms_symmDiff_lt_of_generator
      (P := P) (hτ := hτ) (part := part) hgen (s := ((A.1 : Subtype _) : Set Ω)) A.1.2 hδshare
  choose N₀ U₀ hU₀ using happrox
  let Nmax : ℕ := Finset.sup Finset.univ fun A : q.parts ↦ ((N₀ A : ℕ+) : ℕ)
  let N : ℕ+ := ⟨max Nmax 1, by positivity⟩
  have hN₀ : ∀ A : q.parts, N₀ A ≤ N := by
    intro A
    refine (PNat.coe_le_coe _ _).2 ?_
    show ((N₀ A : ℕ+) : ℕ) ≤ ((N : ℕ+) : ℕ)
    simpa [N] using
      le_trans (Finset.le_sup (s := Finset.univ) (f := fun B : q.parts ↦ ((N₀ B : ℕ+) : ℕ))
        (by simp)) (Nat.le_max_left Nmax 1)
  have hlift :
      ∀ A : q.parts,
        ∃ V : Finset (part.block τ hτ N).parts,
          blockPartsUnion (part.block τ hτ (N₀ A)) (U₀ A) =
            blockPartsUnion (part.block τ hτ N) V := by
    intro A
    exact exists_liftBlockPartsUnion_eq (hτ := hτ) (part := part) (hNM := hN₀ A) (U₀ A)
  choose U hU using hlift
  refine ⟨N, U, ?_⟩
  have hterm_le :
      ∀ A : q.parts,
        P ((((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) \
              blockPartsUnion (part.block τ hτ N) (U A)) ∪
            (blockPartsUnion (part.block τ hτ N) (U A) \
              (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)))) ≤
          ENNReal.ofReal δshare := by
    intro A
    exact (by simpa [hU A] using (hU₀ A).le)
  calc
    ∑ A : q.parts,
        P ((((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) \
              blockPartsUnion (part.block τ hτ N) (U A)) ∪
            (blockPartsUnion (part.block τ hτ N) (U A) \
              (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)))) ≤
        ∑ _A : q.parts, ENNReal.ofReal δshare := by
      exact Finset.sum_le_sum fun A _ ↦ hterm_le A
    _ = ENNReal.ofReal ((Fintype.card q.parts) • δshare) := by
      rw [ENNReal.ofReal_nsmul]
      simp
    _ < ENNReal.ofReal δ := by
      rw [ENNReal.ofReal_lt_ofReal_iff hδ]
      rw [nsmul_eq_mul]
      have hcard_lt : ((Fintype.card q.parts : ℕ) : ℝ) < Fintype.card q.parts + 1 := by
        exact_mod_cast Nat.lt_succ_self (Fintype.card q.parts)
      have hdiv_lt_one :
          ((Fintype.card q.parts : ℕ) : ℝ) / (Fintype.card q.parts + 1) < (1 : ℝ) := by
        exact (div_lt_one (by positivity)).2 hcard_lt
      have hmul_lt := mul_lt_mul_of_pos_right hdiv_lt_one hδ
      simpa [δshare, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul_lt

/-- Helper for Theorem 20.35: `Real.negMulLog` is superadditive on nonnegative reals, so merging
two masses cannot increase the corresponding Shannon contribution. -/
private theorem negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  by_cases hxy : x + y = 0
  · -- Proof comment: if the total mass is zero, both summands already vanish.
    have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  · -- Proof comment: otherwise normalize by the total mass and use the multiplicative identity
    -- for `Real.negMulLog`.
    set s : ℝ := x + y
    have hxy' : x + y ≠ 0 := by
      simpa [s] using hxy
    have hs : 0 < s := by
      dsimp [s]
      exact lt_of_le_of_ne (add_nonneg hx hy) (by simpa [ne_comm] using hxy')
    have hs_nonneg : 0 ≤ s := le_of_lt hs
    have hs_ne : s ≠ 0 := ne_of_gt hs
    have hxs : x = s * (x / s) := by
      field_simp [s, hs_ne]
    have hys : y = s * (y / s) := by
      field_simp [s, hs_ne]
    have hx_div_nonneg : 0 ≤ x / s := by positivity
    have hy_div_nonneg : 0 ≤ y / s := by positivity
    have hx_div_le_one : x / s ≤ 1 := by
      have hle : x ≤ s := by
        dsimp [s]
        linarith
      field_simp [hs_ne]
      linarith
    have hy_div_le_one : y / s ≤ 1 := by
      have hle : y ≤ s := by
        dsimp [s]
        linarith
      field_simp [hs_ne]
      linarith
    have hsum_div : x / s + y / s = 1 := by
      field_simp [s, hs_ne]
      ring
    have hsplit :
        Real.negMulLog s + (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) =
          ((x / s) * Real.negMulLog s + s * Real.negMulLog (x / s)) +
            ((y / s) * Real.negMulLog s + s * Real.negMulLog (y / s)) := by
      calc
        Real.negMulLog s + (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) =
            ((x / s + y / s) * Real.negMulLog s) +
              (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) := by
          rw [hsum_div]
          ring
        _ =
            ((x / s) * Real.negMulLog s + s * Real.negMulLog (x / s)) +
              ((y / s) * Real.negMulLog s + s * Real.negMulLog (y / s)) := by
          ring
    have hnegMulLog_x :
        Real.negMulLog x = (x / s) * Real.negMulLog s + s * Real.negMulLog (x / s) := by
      calc
        Real.negMulLog x = Real.negMulLog (s * (x / s)) := by
          exact congrArg Real.negMulLog hxs
        _ = (x / s) * Real.negMulLog s + s * Real.negMulLog (x / s) := by
          rw [Real.negMulLog_mul]
    have hnegMulLog_y :
        Real.negMulLog y = (y / s) * Real.negMulLog s + s * Real.negMulLog (y / s) := by
      calc
        Real.negMulLog y = Real.negMulLog (s * (y / s)) := by
          exact congrArg Real.negMulLog hys
        _ = (y / s) * Real.negMulLog s + s * Real.negMulLog (y / s) := by
          rw [Real.negMulLog_mul]
    calc
      Real.negMulLog (x + y) = Real.negMulLog s := by simp [s]
      _ ≤ Real.negMulLog s + (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) := by
        have hx_term_nonneg : 0 ≤ s * Real.negMulLog (x / s) := by
          exact mul_nonneg hs_nonneg (Real.negMulLog_nonneg hx_div_nonneg hx_div_le_one)
        have hy_term_nonneg : 0 ≤ s * Real.negMulLog (y / s) := by
          exact mul_nonneg hs_nonneg (Real.negMulLog_nonneg hy_div_nonneg hy_div_le_one)
        linarith
      _ =
          ((x / s) * Real.negMulLog s + s * Real.negMulLog (x / s)) +
            ((y / s) * Real.negMulLog s + s * Real.negMulLog (y / s)) := by
        exact hsplit
      _ = Real.negMulLog x + Real.negMulLog y := by
        rw [hnegMulLog_x, hnegMulLog_y]

/-- Helper for Theorem 20.35: the Shannon contribution of a finite sum of nonnegative masses is
bounded by the sum of the individual Shannon contributions. -/
private theorem negMulLog_sum_le_sum_negMulLog {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    Real.negMulLog (Finset.sum s w) ≤ Finset.sum s (fun i ↦ Real.negMulLog (w i)) := by
  induction s using Finset.cons_induction with
  | empty =>
      -- Proof comment: the empty sum has zero Shannon contribution.
      simp [Real.negMulLog_zero]
  | @cons a s ha ih =>
      -- Proof comment: split off one mass and apply the two-point superadditivity step.
      have hwa : 0 ≤ w a := hw a (by simp)
      have hws : ∀ i ∈ s, 0 ≤ w i := by
        intro i hi
        exact hw i (by simp [hi])
      have hsum_nonneg : 0 ≤ Finset.sum s w := Finset.sum_nonneg hws
      calc
        Real.negMulLog (Finset.sum (Finset.cons a s ha) w) =
            Real.negMulLog (w a + Finset.sum s w) := by
          simp
        _ ≤ Real.negMulLog (w a) + Real.negMulLog (Finset.sum s w) :=
          negMulLog_add_le hwa hsum_nonneg
        _ ≤ Real.negMulLog (w a) + Finset.sum s (fun i ↦ Real.negMulLog (w i)) := by
          gcongr
          exact ih hws
        _ = Finset.sum (Finset.cons a s ha) (fun i ↦ Real.negMulLog (w i)) := by
          simp

/-- Helper for Theorem 20.35: deterministic coding on a finite alphabet cannot increase Shannon
entropy. -/
private theorem entropy_map_le {α : Type*} {β : Type*} [Finite α] [Finite β]
    (p : PMF α) (Φ : α → β) :
    entropy (PMF.map Φ p) ≤ entropy p := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  have hmap_apply (b : β) :
      ((PMF.map Φ p) b).toReal =
        Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b)) fun a ↦ (p a).toReal := by
    -- Proof comment: rewrite the pushed-forward mass at `b` as the finite sum of the masses in
    -- its fiber.
    calc
      ((PMF.map Φ p) b).toReal =
          (∑' a : α, if b = Φ a then p a else 0).toReal := by
        rw [PMF.map_apply]
      _ = (∑ a : α, if b = Φ a then p a else 0).toReal := by
        rw [tsum_fintype]
      _ = ∑ a : α, (if b = Φ a then p a else 0).toReal := by
        refine ENNReal.toReal_sum ?_
        intro a ha
        by_cases hab : b = Φ a
        · simp [hab, p.apply_ne_top a]
        · simp [hab]
      _ = Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b)) fun a ↦ (p a).toReal := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro a ha
        by_cases hab : Φ a = b
        · simp [hab]
        · have hab' : b ≠ Φ a := by
            simpa [eq_comm] using hab
          simp [hab, hab']
  have hfiber :
      ∑ b : β, Real.negMulLog (((PMF.map Φ p) b).toReal) ≤
        ∑ b : β,
          Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b))
            fun a ↦ Real.negMulLog ((p a).toReal) := by
    -- Proof comment: apply the finite superadditivity lemma on each fiber separately.
    refine Finset.sum_le_sum ?_
    intro b hb
    rw [hmap_apply b]
    refine negMulLog_sum_le_sum_negMulLog _ _ ?_
    intro a ha
    exact ENNReal.toReal_nonneg
  have hfiberwise :
      (∑ b : β,
        Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b))
          fun a ↦ Real.negMulLog ((p a).toReal)) =
        ∑ a : α, Real.negMulLog ((p a).toReal) := by
    -- Proof comment: reassemble the fiberwise sum to recover the original entropy sum.
    simpa using
      (Finset.sum_fiberwise (s := Finset.univ) (g := Φ)
        (f := fun a : α ↦ Real.negMulLog ((p a).toReal)))
  rw [entropy_eq_sum, entropy_eq_sum]
  apply EReal.coe_le_coe
  -- Proof comment: convert both entropies to finite real sums of `Real.negMulLog`.
  calc
    (-∑ b : β, ((PMF.map Φ p) b).toReal * Real.log (((PMF.map Φ p) b).toReal) : ℝ) =
        ∑ b : β, Real.negMulLog (((PMF.map Φ p) b).toReal) := by
      simp [Real.negMulLog_def]
    _ ≤ ∑ b : β,
          Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b))
            fun a ↦ Real.negMulLog ((p a).toReal) := hfiber
    _ = ∑ a : α, Real.negMulLog ((p a).toReal) := hfiberwise
    _ = (-∑ a : α, (p a).toReal * Real.log ((p a).toReal) : ℝ) := by
      simp [Real.negMulLog_def]

/-- Helper for Theorem 20.35: an injective relabeling of a finite pmf preserves Shannon
entropy. -/
private theorem entropy_map_eq_of_injective {α : Type*} {β : Type*} [Finite α] [Finite β]
    (p : PMF α) (f : α → β) (hf : Function.Injective f) :
    entropy (PMF.map f p) = entropy p := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  let φ : β → ℝ := fun b ↦ ((PMF.map f p) b).toReal * Real.log (((PMF.map f p) b).toReal)
  have hmap : ∀ a : α, PMF.map f p (f a) = p a := by
    intro a
    -- Proof comment: injectivity collapses the pushed-forward mass at `f a` to the single source
    -- atom `a`.
    rw [PMF.map_apply]
    refine (tsum_eq_single a ?_).trans ?_
    · intro a' ha'
      have hneq : f a ≠ f a' := fun h ↦ ha' ((hf h).symm)
      simp [hneq]
    · simp
  have hzero : ∀ b : β, b ∉ Set.range f → PMF.map f p b = 0 := by
    intro b hb
    -- Proof comment: target points outside the image receive no mass.
    rw [PMF.map_apply, ENNReal.tsum_eq_zero]
    intro a
    by_cases hba : b = f a
    · exact (hb ⟨a, hba.symm⟩).elim
    · simp [hba]
  have himage :
      Finset.univ.filter (fun b : β ↦ b ∈ Set.range f) = (Finset.univ.image f) := by
    -- Proof comment: on a finite target alphabet, filtering by the range gives the image set.
    ext b
    simp
  have hfilter_sum :
      Finset.univ.sum φ = (Finset.univ.filter (fun b : β ↦ b ∈ Set.range f)).sum φ := by
    -- Proof comment: points outside the image contribute zero to the entropy sum.
    have hsubset :
        Finset.univ.filter (fun b : β ↦ b ∈ Set.range f) ⊆ Finset.univ := by
      intro b hb
      simp
    have hvanish :
        ∀ b ∈ Finset.univ, b ∉ Finset.univ.filter (fun b : β ↦ b ∈ Set.range f) → φ b = 0 := by
      intro b hb hnot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      have hb0 : PMF.map f p b = 0 := hzero b hnot
      dsimp [φ]
      rw [hb0]
      norm_num
    simpa using (Finset.sum_subset hsubset hvanish).symm
  have hreindex :
      (Finset.univ.image f).sum φ = Finset.univ.sum (fun a : α ↦ φ (f a)) := by
    -- Proof comment: reindex the image sum back along the injective relabeling.
    simpa using (Finset.sum_image (s := Finset.univ) (f := φ) hf.injOn)
  have hpointwise :
      Finset.univ.sum (fun a : α ↦ φ (f a)) =
        Finset.univ.sum (fun a : α ↦ (p a).toReal * Real.log ((p a).toReal)) := by
    -- Proof comment: on image points, the mapped pmf agrees with the original pmf.
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [φ]
    rw [hmap a]
  rw [entropy_eq_sum, entropy_eq_sum]
  calc
    ((-(Finset.univ.sum φ) : ℝ) : EReal) =
        ((-((Finset.univ.filter (fun b : β ↦ b ∈ Set.range f)).sum φ) : ℝ) : EReal) := by
      simpa using congrArg (fun t : ℝ ↦ ((-t : ℝ) : EReal)) hfilter_sum
    _ = ((-((Finset.univ.image f).sum φ) : ℝ) : EReal) := by
      rw [himage]
    _ = ((-(Finset.univ.sum fun a : α ↦ φ (f a)) : ℝ) : EReal) := by
      simpa using congrArg (fun t : ℝ ↦ ((-t : ℝ) : EReal)) hreindex
    _ = ((-(Finset.univ.sum fun a : α ↦ (p a).toReal * Real.log ((p a).toReal)) : ℝ) : EReal) := by
      simpa using congrArg (fun t : ℝ ↦ ((-t : ℝ) : EReal)) hpointwise

/-- Helper for Theorem 20.35: the real masses of a finite pmf sum to `1`. -/
private theorem pmfToReal_sum_eq_one {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a).toReal = 1 := by
  calc
    ∑ a : α, (p a).toReal = (∑ a : α, p a).toReal := by
      -- Proof comment: convert the finite sum of real masses back to the corresponding
      -- finite sum in `ℝ≥0∞`.
      symm
      exact ENNReal.toReal_sum (fun a _ ↦ p.apply_ne_top a)
    _ = 1 := by
      have hp : ∑ a : α, p a = 1 := by
        simpa [tsum_fintype] using p.tsum_coe
      rw [hp]
      simp

/-- Helper for Theorem 20.35: pushing a probability measure forward along a composition gives
the pmf pushforward of the intermediate law. -/
private theorem toPMF_eq_map_of_comp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {α β : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    (f : Ω → α) (hf : Measurable f) (g : α → β) (hg : Measurable g)
    [IsProbabilityMeasure (Measure.map f P)]
    [IsProbabilityMeasure (Measure.map (fun ω ↦ g (f ω)) P)] :
    (Measure.map (fun ω ↦ g (f ω)) P).toPMF = PMF.map g ((Measure.map f P).toPMF) := by
  -- Proof comment: compare the two pmfs by converting both sides back to the corresponding
  -- pushforward probability measures.
  apply PMF.toMeasure_injective
  rw [Measure.toPMF_toMeasure, ← PMF.toMeasure_map]
  · rw [Measure.toPMF_toMeasure, Measure.map_map hg hf]
    rfl
  · exact hg

/-- Helper for Theorem 20.35: if the coding of one finite measurable partition factors through
another partition, then the induced pmf is the corresponding pushforward of the larger partition
law. -/
private theorem toPMF_eq_map_of_toSimpleFuncFactor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {q r : MeasurableFinpartition Ω} (Φ : r.parts → q.parts)
    (hΦ : (q.toSimpleFunc : Ω → q.parts) = fun ω ↦ Φ (r.toSimpleFunc ω)) :
    q.toPMF P = PMF.map Φ (r.toPMF P) := by
  let μq : Measure q.parts := P.map q.toSimpleFunc
  let μr : Measure r.parts := P.map r.toSimpleFunc
  letI : IsProbabilityMeasure μq :=
    Measure.isProbabilityMeasure_map q.toSimpleFunc.aemeasurable
  letI : IsProbabilityMeasure μr :=
    Measure.isProbabilityMeasure_map r.toSimpleFunc.aemeasurable
  change μq.toPMF = PMF.map Φ μr.toPMF
  apply PMF.toMeasure_injective
  -- Proof comment: rewrite both sides back to the corresponding pushforward measures.
  rw [Measure.toPMF_toMeasure]
  rw [← PMF.toMeasure_map]
  · rw [Measure.toPMF_toMeasure]
    dsimp [μq, μr]
    rw [Measure.map_map (μ := P) (g := Φ) (f := r.toSimpleFunc)
      (Measurable.of_discrete (f := Φ)) r.toSimpleFunc.measurable]
    rw [hΦ]
    rfl
  · exact Measurable.of_discrete (f := Φ)

/-- Helper for Theorem 20.35: a partition that factors through another finite measurable partition
cannot have larger one-step entropy. -/
private theorem partitionEntropy_le_of_toSimpleFuncFactor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {q r : MeasurableFinpartition Ω} (Φ : r.parts → q.parts)
    (hΦ : (q.toSimpleFunc : Ω → q.parts) = fun ω ↦ Φ (r.toSimpleFunc ω)) :
    q.partitionEntropy P ≤ r.partitionEntropy P := by
  -- Proof comment: rewrite to the entropy of the pushforward law and use entropy monotonicity.
  calc
    q.partitionEntropy P = entropy (PMF.map Φ (r.toPMF P)) := by
      rw [MeasurableFinpartition.partitionEntropy_def,
        toPMF_eq_map_of_toSimpleFuncFactor P Φ hΦ]
    _ ≤ entropy (r.toPMF P) := entropy_map_le (r.toPMF P) Φ
    _ = r.partitionEntropy P := by
      rw [MeasurableFinpartition.partitionEntropy_def]

/-- Helper for Theorem 20.35: the partition entropy of `MeasurableFinpartition.ofSimpleFunc g`
is exactly the Shannon entropy of the law of `g`. -/
private theorem partitionEntropy_ofSimpleFunc_eq_entropy_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] [Finite α]
    (g : SimpleFunc Ω α) [IsProbabilityMeasure (Measure.map g P)] :
    (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P =
      entropy ((Measure.map g P).toPMF) := by
  let q : MeasurableFinpartition Ω := MeasurableFinpartition.ofSimpleFunc g
  let Φ : q.parts → α := ofSimpleFuncFiberValue g
  letI : IsProbabilityMeasure (Measure.map q.toSimpleFunc P) :=
    Measure.isProbabilityMeasure_map q.toSimpleFunc.aemeasurable
  have hfactor :
      g = fun ω ↦ Φ (q.toSimpleFunc ω) := by
    -- Proof comment: first code each point by its `ofSimpleFunc` atom and then relabel that
    -- atom by the remembered `g`-value.
    simpa [q, Φ] using simpleFunc_eq_ofSimpleFuncFiberValue_comp_toSimpleFunc g
  letI : IsProbabilityMeasure (Measure.map (fun ω ↦ Φ (q.toSimpleFunc ω)) P) := by
    simpa [hfactor] using (show IsProbabilityMeasure (Measure.map g P) from inferInstance)
  have hmap :
      (Measure.map g P).toPMF = PMF.map Φ (q.toPMF P) := by
    -- Proof comment: the law of `g` is the pushforward of the atom code law under the
    -- remembered-value relabeling.
    simpa [MeasurableFinpartition.toPMF, q, Φ, hfactor] using
      (toPMF_eq_map_of_comp (P := P) (f := q.toSimpleFunc) (hf := q.toSimpleFunc.measurable)
        (g := Φ) (hg := Measurable.of_discrete (f := Φ)))
  rw [MeasurableFinpartition.partitionEntropy_def]
  calc
    entropy (q.toPMF P) = entropy (PMF.map Φ (q.toPMF P)) := by
      symm
      exact entropy_map_eq_of_injective (q.toPMF P) Φ (ofSimpleFuncFiberValue_injective g)
    _ = entropy ((Measure.map g P).toPMF) := by
      rw [← hmap]

/-- Helper for Theorem 20.35: the block entropy of a partition coming from a finite-valued simple
function is the Shannon entropy of the corresponding block-value law. -/
private theorem blockPartitionEntropy_ofSimpleFunc_eq_entropy_valueBlockLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {τ : Ω → Ω} (hτ : Measurable τ) {α : Type*}
    [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (g : SimpleFunc Ω α) (n : ℕ+)
    [IsProbabilityMeasure
      (Measure.map (fun ω : Ω ↦ fun i : Fin n ↦ g ((τ^[i]) ω)) μ)] :
    ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ n).partitionEntropy μ =
      entropy ((Measure.map (fun ω : Ω ↦ fun i : Fin n ↦ g ((τ^[i]) ω)) μ).toPMF) := by
  classical
  let part : MeasurableFinpartition Ω := MeasurableFinpartition.ofSimpleFunc g
  let Λ : (Fin n → part.parts) → (Fin n → α) := fun s i ↦ ofSimpleFuncFiberValue g (s i)
  have hΛinj : Function.Injective Λ := by
    intro s t hst
    funext i
    exact ofSimpleFuncFiberValue_injective g (by simpa using congrFun hst i)
  have hvalueBlock :
      Measurable (fun ω : Ω ↦ fun i : Fin n ↦ g ((τ^[i]) ω)) := by
    -- Proof comment: each block coordinate is the original code evaluated after one iterate of
    -- `τ`.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact g.measurable.comp (Measurable.iterate hτ i)
  have hfactor :
      (fun ω : Ω ↦ Λ (prefixBlockCode τ hτ part n ω)) =
        fun ω : Ω ↦ fun i : Fin n ↦ g ((τ^[i]) ω) := by
    -- Proof comment: the remembered-value relabeling recovers the underlying `g`-values from each
    -- transparent block atom.
    funext ω
    funext i
    have hcode :=
      congrArg (fun f : Ω → α ↦ f ((τ^[i]) ω))
        (simpleFunc_eq_ofSimpleFuncFiberValue_comp_toSimpleFunc g)
    simpa [part, prefixBlockCode] using hcode.symm
  letI : IsProbabilityMeasure (Measure.map (prefixBlockCode τ hτ part n) μ) :=
    Measure.isProbabilityMeasure_map (prefixBlockCode τ hτ part n).aemeasurable
  letI : IsProbabilityMeasure (Measure.map (fun ω : Ω ↦ fun i : Fin n ↦ g ((τ^[i]) ω)) μ) :=
    Measure.isProbabilityMeasure_map hvalueBlock.aemeasurable
  letI :
      IsProbabilityMeasure
        (Measure.map (fun ω : Ω ↦ Λ (prefixBlockCode τ hτ part n ω)) μ) := by
    simpa [hfactor] using
      (show IsProbabilityMeasure
          (Measure.map (fun ω : Ω ↦ fun i : Fin n ↦ g ((τ^[i]) ω)) μ) from inferInstance)
  have hmapLaw :
      (Measure.map (fun ω : Ω ↦ fun i : Fin n ↦ g ((τ^[i]) ω)) μ).toPMF =
        PMF.map Λ ((Measure.map (prefixBlockCode τ hτ part n) μ).toPMF) := by
    -- Proof comment: the block-value law is the pushforward of the transparent block code law
    -- along the remembered-value relabeling.
    simpa [hfactor] using
      (toPMF_eq_map_of_comp (P := μ)
        (f := prefixBlockCode τ hτ part n)
        (hf := (prefixBlockCode τ hτ part n).measurable)
        (g := Λ) (hg := Measurable.of_discrete (f := Λ)))
  calc
    ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ n).partitionEntropy μ =
        entropy ((Measure.map (prefixBlockCode τ hτ part n) μ).toPMF) := by
      -- Proof comment: replace the owner block partition by the entropy of its transparent block
      -- code law.
      rw [block_eq_ofSimpleFunc_prefixBlockCode (hτ := hτ) (part := part) (n := n)]
      simpa using
        (partitionEntropy_ofSimpleFunc_eq_entropy_law
          (P := μ) (g := prefixBlockCode τ hτ part n))
    _ = entropy (PMF.map Λ ((Measure.map (prefixBlockCode τ hτ part n) μ).toPMF)) := by
      -- Proof comment: the remembered-value relabeling on block words is injective.
      symm
      exact entropy_map_eq_of_injective
        ((Measure.map (prefixBlockCode τ hτ part n) μ).toPMF) Λ hΛinj
    _ = entropy ((Measure.map (fun ω : Ω ↦ fun i : Fin n ↦ g ((τ^[i]) ω)) μ).toPMF) := by
      rw [← hmapLaw]

/-- Helper for Theorem 20.35: the block entropy of the pair code `(g, e)` is bounded by the sum
of the block entropies of `g` and `e`. -/
private theorem blockPartitionEntropy_pair_le_add
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {τ : Ω → Ω} (hτ : Measurable τ) {β : Type*} {γ : Type*}
    [Finite β] [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    [Finite γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] [Countable γ]
    (g : SimpleFunc Ω β) (e : SimpleFunc Ω γ) (n : ℕ+) :
    ((MeasurableFinpartition.ofSimpleFunc (g.pair e)).block τ hτ n).partitionEntropy μ ≤
      ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ n).partitionEntropy μ +
        ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ n).partitionEntropy μ := by
  classical
  let gBlock : Ω → (Fin n → β) := fun ω i ↦ g ((τ^[i]) ω)
  let eBlock : Ω → (Fin n → γ) := fun ω i ↦ e ((τ^[i]) ω)
  let geBlock : Ω → (Fin n → β × γ) := fun ω i ↦ (g ((τ^[i]) ω), e ((τ^[i]) ω))
  let Ψ : (Fin n → β × γ) → (Fin n → β) × (Fin n → γ) :=
    fun s ↦ (fun i ↦ (s i).1, fun i ↦ (s i).2)
  have hΨinj : Function.Injective Ψ := by
    intro s t hst
    have hfst : (fun i ↦ (s i).1) = fun i ↦ (t i).1 := congrArg Prod.fst hst
    have hsnd : (fun i ↦ (s i).2) = fun i ↦ (t i).2 := congrArg Prod.snd hst
    funext i
    exact Prod.ext (by simpa using congrFun hfst i) (by simpa using congrFun hsnd i)
  have hgBlock : Measurable gBlock := by
    -- Proof comment: each block coordinate of `g` is measurable after iterating `τ`.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact g.measurable.comp (Measurable.iterate hτ i)
  have heBlock : Measurable eBlock := by
    -- Proof comment: the same coordinatewise measurability argument applies to `e`.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact e.measurable.comp (Measurable.iterate hτ i)
  have hgeBlock : Measurable geBlock := by
    -- Proof comment: pair the two measurable block-value maps coordinatewise.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact (g.measurable.comp (Measurable.iterate hτ i)).prodMk
      (e.measurable.comp (Measurable.iterate hτ i))
  letI : IsProbabilityMeasure (Measure.map gBlock μ) :=
    Measure.isProbabilityMeasure_map hgBlock.aemeasurable
  letI : IsProbabilityMeasure (Measure.map eBlock μ) :=
    Measure.isProbabilityMeasure_map heBlock.aemeasurable
  letI : IsProbabilityMeasure (Measure.map geBlock μ) :=
    Measure.isProbabilityMeasure_map hgeBlock.aemeasurable
  letI :
      IsProbabilityMeasure
        (Measure.map (fun ω : Ω ↦ fun i : Fin n ↦ (g.pair e) ((τ^[i]) ω)) μ) := by
    simpa [geBlock, SimpleFunc.pair_apply] using
      (show IsProbabilityMeasure (Measure.map geBlock μ) from inferInstance)
  let geLaw : PMF (Fin n → β × γ) := (Measure.map geBlock μ).toPMF
  let pairLaw : PMF ((Fin n → β) × (Fin n → γ)) := PMF.map Ψ geLaw
  have hfstLaw : PMF.map Prod.fst pairLaw = (Measure.map gBlock μ).toPMF := by
    -- Proof comment: the first marginal of the block-pair law is exactly the block law of `g`.
    calc
      PMF.map Prod.fst pairLaw = PMF.map (Prod.fst ∘ Ψ) geLaw := by
        simp [pairLaw, PMF.map_comp]
      _ = PMF.map (fun s : Fin n → β × γ ↦ fun i ↦ (s i).1) geLaw := rfl
      _ = (Measure.map gBlock μ).toPMF := by
        symm
        exact toPMF_eq_map_of_comp (P := μ)
          (f := geBlock) (hf := hgeBlock)
          (g := fun s : Fin n → β × γ ↦ fun i ↦ (s i).1)
          (hg := Measurable.of_discrete (f := fun s : Fin n → β × γ ↦ fun i ↦ (s i).1))
  have hsndLaw : PMF.map Prod.snd pairLaw = (Measure.map eBlock μ).toPMF := by
    -- Proof comment: the second marginal of the block-pair law is exactly the block law of `e`.
    calc
      PMF.map Prod.snd pairLaw = PMF.map (Prod.snd ∘ Ψ) geLaw := by
        simp [pairLaw, PMF.map_comp]
      _ = PMF.map (fun s : Fin n → β × γ ↦ fun i ↦ (s i).2) geLaw := rfl
      _ = (Measure.map eBlock μ).toPMF := by
        symm
        exact toPMF_eq_map_of_comp (P := μ)
          (f := geBlock) (hf := hgeBlock)
          (g := fun s : Fin n → β × γ ↦ fun i ↦ (s i).2)
          (hg := Measurable.of_discrete (f := fun s : Fin n → β × γ ↦ fun i ↦ (s i).2))
  calc
    ((MeasurableFinpartition.ofSimpleFunc (g.pair e)).block τ hτ n).partitionEntropy μ =
        entropy geLaw := by
      -- Proof comment: identify the pair-block partition with the Shannon entropy of its block
      -- value law.
      simpa [geLaw, geBlock, SimpleFunc.pair_apply] using
        (blockPartitionEntropy_ofSimpleFunc_eq_entropy_valueBlockLaw
          (μ := μ) (hτ := hτ) (g := g.pair e) (n := n))
    _ = entropy pairLaw := by
      -- Proof comment: regroup each block word into the product of its first and second
      -- coordinate words through an injective relabeling.
      symm
      exact entropy_map_eq_of_injective geLaw Ψ hΨinj
    _ ≤ entropy (PMF.map Prod.fst pairLaw) + entropy (PMF.map Prod.snd pairLaw) := by
      exact entropy_le_entropy_map_fst_add_entropy_map_snd pairLaw
    _ = entropy ((Measure.map gBlock μ).toPMF) + entropy ((Measure.map eBlock μ).toPMF) := by
      rw [hfstLaw, hsndLaw]
    _ = ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ n).partitionEntropy μ +
          ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ n).partitionEntropy μ := by
      -- Proof comment: convert both marginal block-value laws back to the corresponding block
      -- partition entropies.
      rw [← blockPartitionEntropy_ofSimpleFunc_eq_entropy_valueBlockLaw
          (μ := μ) (hτ := hτ) (g := g) (n := n)]
      rw [← blockPartitionEntropy_ofSimpleFunc_eq_entropy_valueBlockLaw
          (μ := μ) (hτ := hτ) (g := e) (n := n)]

/-- Helper for Theorem 20.35: if a block code is pointwise decoded from two auxiliary codes, then
its block entropy is at most the sum of the two auxiliary block entropies. -/
private theorem blockPartitionEntropy_le_add_ofPointwiseDecode
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {τ : Ω → Ω} (hτ : Measurable τ) {α : Type*} {β : Type*} {γ : Type*}
    [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    [Finite β] [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    [Finite γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] [Countable γ]
    (q : SimpleFunc Ω α) (g : SimpleFunc Ω β) (e : SimpleFunc Ω γ)
    (decode : β → γ → α)
    (hdecode : q = fun ω ↦ decode (g ω) (e ω)) (n : ℕ+) :
    ((MeasurableFinpartition.ofSimpleFunc q).block τ hτ n).partitionEntropy μ ≤
      ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ n).partitionEntropy μ +
        ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ n).partitionEntropy μ := by
  classical
  let qBlock : Ω → (Fin n → α) := fun ω i ↦ q ((τ^[i]) ω)
  let geBlock : Ω → (Fin n → β × γ) := fun ω i ↦ (g ((τ^[i]) ω), e ((τ^[i]) ω))
  let decodeBlock : (Fin n → β × γ) → (Fin n → α) :=
    fun s i ↦ decode (s i).1 (s i).2
  have hqBlock : Measurable qBlock := by
    -- Proof comment: each decoded block coordinate is a measurable iterate of the original code
    -- `q`.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact q.measurable.comp (Measurable.iterate hτ i)
  have hgeBlock : Measurable geBlock := by
    -- Proof comment: the paired auxiliary block code is measurable coordinatewise.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact (g.measurable.comp (Measurable.iterate hτ i)).prodMk
      (e.measurable.comp (Measurable.iterate hτ i))
  have hdecodeBlock :
      qBlock = fun ω ↦ decodeBlock (geBlock ω) := by
    -- Proof comment: decode each time coordinate using the one-step pointwise identity.
    funext ω
    funext i
    have hstep := congrArg (fun f : Ω → α ↦ f ((τ^[i]) ω)) hdecode
    simpa [qBlock, geBlock, decodeBlock] using hstep
  letI : IsProbabilityMeasure (Measure.map qBlock μ) :=
    Measure.isProbabilityMeasure_map hqBlock.aemeasurable
  letI : IsProbabilityMeasure (Measure.map geBlock μ) :=
    Measure.isProbabilityMeasure_map hgeBlock.aemeasurable
  letI :
      IsProbabilityMeasure (Measure.map (fun ω : Ω ↦ fun i : Fin n ↦ q ((τ^[i]) ω)) μ) := by
    simpa [qBlock] using
      (show IsProbabilityMeasure (Measure.map qBlock μ) from inferInstance)
  letI :
      IsProbabilityMeasure
        (Measure.map (fun ω : Ω ↦ fun i : Fin n ↦ (g.pair e) ((τ^[i]) ω)) μ) := by
    simpa [geBlock, SimpleFunc.pair_apply] using
      (show IsProbabilityMeasure (Measure.map geBlock μ) from inferInstance)
  letI : IsProbabilityMeasure (Measure.map (fun ω ↦ decodeBlock (geBlock ω)) μ) := by
    simpa [hdecodeBlock] using
      (show IsProbabilityMeasure (Measure.map qBlock μ) from inferInstance)
  have hdecodeLaw :
      (Measure.map qBlock μ).toPMF =
        PMF.map decodeBlock ((Measure.map geBlock μ).toPMF) := by
    -- Proof comment: the decoded block law is the pushforward of the paired auxiliary block law.
    simpa [hdecodeBlock] using
      (toPMF_eq_map_of_comp (P := μ)
        (f := geBlock) (hf := hgeBlock)
        (g := decodeBlock) (hg := Measurable.of_discrete (f := decodeBlock)))
  calc
    ((MeasurableFinpartition.ofSimpleFunc q).block τ hτ n).partitionEntropy μ =
        entropy ((Measure.map qBlock μ).toPMF) := by
      -- Proof comment: normalize the decoded block partition to the Shannon entropy of its block
      -- value law.
      simpa [qBlock] using
        (blockPartitionEntropy_ofSimpleFunc_eq_entropy_valueBlockLaw
          (μ := μ) (hτ := hτ) (g := q) (n := n))
    _ = entropy (PMF.map decodeBlock ((Measure.map geBlock μ).toPMF)) := by
      rw [hdecodeLaw]
    _ ≤ entropy ((Measure.map geBlock μ).toPMF) := by
      exact entropy_map_le ((Measure.map geBlock μ).toPMF) decodeBlock
    _ = ((MeasurableFinpartition.ofSimpleFunc (g.pair e)).block τ hτ n).partitionEntropy μ := by
      -- Proof comment: the paired auxiliary block law is exactly the block law of the one-step
      -- pair code `(g, e)`.
      symm
      simpa [geBlock, SimpleFunc.pair_apply] using
        (blockPartitionEntropy_ofSimpleFunc_eq_entropy_valueBlockLaw
          (μ := μ) (hτ := hτ) (g := g.pair e) (n := n))
    _ ≤
        ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ n).partitionEntropy μ +
          ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ n).partitionEntropy μ := by
      exact blockPartitionEntropy_pair_le_add (μ := μ) (hτ := hτ) g e n

/-- Helper for Theorem 20.35: the entropy of an `Option β`-valued pmf is controlled by the
binary mass of `none` plus the rare non-`none` mass times `log |β|`. -/
private theorem entropyOption_le_ofNonNoneMass {β : Type*} [Fintype β] (p : PMF (Option β)) :
    entropy p ≤
      ((Real.negMulLog ((p none).toReal) + Real.negMulLog (1 - (p none).toReal) +
          (1 - (p none).toReal) * Real.log (Fintype.card β)) : ℝ) := by
  classical
  have hnone_le_one : (p none).toReal ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one none)
  have hsome_sum_real : ∑ b : β, (p (some b)).toReal = 1 - (p none).toReal := by
    have htotal :
        (p none).toReal + ∑ b : β, (p (some b)).toReal = 1 := by
      simpa [Fintype.sum_option, add_comm, add_left_comm, add_assoc] using pmfToReal_sum_eq_one p
    linarith
  have hentropy_expand :
      entropy p =
        ((Real.negMulLog ((p none).toReal) +
            ∑ b : β, Real.negMulLog ((p (some b)).toReal) : ℝ) : EReal) := by
    -- Proof comment: split the finite entropy sum into the `none` atom and the `some` atoms.
    rw [entropy_eq_sum]
    congr 1
    simp [Fintype.sum_option, Real.negMulLog_def, add_comm, add_left_comm, add_assoc]
  by_cases hq : 1 - (p none).toReal = 0
  · have hpnone : (p none).toReal = 1 := by
      linarith
    have hsome_zero :
        ∀ b : β, (p (some b)).toReal = 0 := by
      intro b
      have hsum_zero : ∑ b : β, (p (some b)).toReal = 0 := by
        simpa [hq] using hsome_sum_real
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun b _ ↦ ENNReal.toReal_nonneg)).mp hsum_zero b (by simp)
    calc
      entropy p =
          ((Real.negMulLog ((p none).toReal) +
              ∑ b : β, Real.negMulLog ((p (some b)).toReal) : ℝ) : EReal) :=
        hentropy_expand
      _ ≤
          ((Real.negMulLog ((p none).toReal) + Real.negMulLog (1 - (p none).toReal) +
              (1 - (p none).toReal) * Real.log (Fintype.card β) : ℝ) : EReal) := by
        rw [hpnone]
        simp [hsome_zero]
  · set q : ℝ := 1 - (p none).toReal with hq_def
    have hq_pos : 0 < q := by
      have hq_nonneg' : 0 ≤ q := by
        dsimp [q]
        linarith
      exact lt_of_le_of_ne hq_nonneg' (by simpa [eq_comm] using hq)
    have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
    let w : β → ENNReal := fun b ↦ ENNReal.ofReal ((p (some b)).toReal / q)
    have hw_sum_real : ∑ b : β, (p (some b)).toReal / q = 1 := by
      calc
        ∑ b : β, (p (some b)).toReal / q = (∑ b : β, (p (some b)).toReal) / q := by
          rw [Finset.sum_div]
        _ = q / q := by rw [hsome_sum_real, hq_def]
        _ = 1 := by
          field_simp [hq_pos.ne']
    have hw_sum : ∑ b : β, w b = 1 := by
      rw [show (∑ b : β, w b) =
          ENNReal.ofReal (∑ b : β, (p (some b)).toReal / q) by
        simpa [w] using
          (ENNReal.ofReal_sum_of_nonneg
            (s := Finset.univ)
            (f := fun b : β ↦ (p (some b)).toReal / q)
            (fun b _ ↦ by positivity)).symm]
      rw [hw_sum_real]
      simp
    let r : PMF β := PMF.ofFintype w hw_sum
    have hr_apply (b : β) : (r b).toReal = (p (some b)).toReal / q := by
      have hw_nonneg : 0 ≤ (p (some b)).toReal / q := by
        positivity
      simp [r, w, PMF.ofFintype_apply, hw_nonneg]
    have hsome_negMulLog :
        ∑ b : β, Real.negMulLog ((p (some b)).toReal) =
          Real.negMulLog q + q * ∑ b : β, Real.negMulLog ((r b).toReal) := by
      -- Proof comment: normalize the `some` masses by their total mass `q` and then factor each
      -- Shannon contribution through `Real.negMulLog_mul`.
      calc
        ∑ b : β, Real.negMulLog ((p (some b)).toReal) =
            ∑ b : β, Real.negMulLog (q * (r b).toReal) := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          have hmul : q * (r b).toReal = (p (some b)).toReal := by
            rw [hr_apply b]
            field_simp [hq_pos.ne']
          rw [← hmul]
        _ =
            ∑ b : β,
              ((r b).toReal * Real.negMulLog q + q * Real.negMulLog ((r b).toReal)) := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          rw [Real.negMulLog_mul]
        _ =
            (∑ b : β, (r b).toReal) * Real.negMulLog q +
              q * ∑ b : β, Real.negMulLog ((r b).toReal) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.mul_sum]
        _ = Real.negMulLog q + q * ∑ b : β, Real.negMulLog ((r b).toReal) := by
          simp [pmfToReal_sum_eq_one r]
    have hr_entropy :
        entropy r = ((∑ b : β, Real.negMulLog ((r b).toReal) : ℝ) : EReal) := by
      rw [entropy_eq_sum]
      simp [Real.negMulLog_def]
    have hr_bound :
        ∑ b : β, Real.negMulLog ((r b).toReal) ≤ Real.log (Fintype.card β) := by
      exact EReal.coe_le_coe_iff.mp <| by
        rw [← hr_entropy]
        exact entropy_le_log_card r
    have hsome_bound :
        ∑ b : β, Real.negMulLog ((p (some b)).toReal) ≤
          Real.negMulLog q + q * Real.log (Fintype.card β) := by
      calc
        ∑ b : β, Real.negMulLog ((p (some b)).toReal) =
            Real.negMulLog q + q * ∑ b : β, Real.negMulLog ((r b).toReal) :=
          hsome_negMulLog
        _ ≤ Real.negMulLog q + q * Real.log (Fintype.card β) := by
          gcongr
    calc
      entropy p =
          ((Real.negMulLog ((p none).toReal) +
              ∑ b : β, Real.negMulLog ((p (some b)).toReal) : ℝ) : EReal) :=
        hentropy_expand
      _ ≤
          ((Real.negMulLog ((p none).toReal) + (Real.negMulLog q +
              q * Real.log (Fintype.card β)) : ℝ) : EReal) := by
        apply EReal.coe_le_coe
        linarith [hsome_bound]
      _ =
          ((Real.negMulLog ((p none).toReal) + Real.negMulLog (1 - (p none).toReal) +
              (1 - (p none).toReal) * Real.log (Fintype.card β) : ℝ) : EReal) := by
        simp [q, add_assoc]

/-- Helper for Theorem 20.35: the length-one block partition has the same entropy as the original
partition. -/
private theorem blockPartitionEntropy_one_eq_partitionEntropy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω) :
    (part.block τ hτ.measurable 1).partitionEntropy P = part.partitionEntropy P := by
  classical
  let oneCode : SimpleFunc Ω (Fin 1 → part.parts) :=
    prefixBlockCode τ hτ.measurable part (1 : ℕ+)
  let constCode : part.parts → (Fin 1 → part.parts) := fun a _ ↦ a
  have hconstCode_injective : Function.Injective constCode := by
    intro a b hab
    exact congrFun hab 0
  have honeCode :
      oneCode = fun ω ↦ constCode (part.toSimpleFunc ω) := by
    -- Proof comment: a `Fin 1` block records only the time-`0` atom of `part`.
    funext ω
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    simp [oneCode, constCode, prefixBlockCode]
  letI : IsProbabilityMeasure (Measure.map part.toSimpleFunc P) :=
    Measure.isProbabilityMeasure_map part.toSimpleFunc.aemeasurable
  letI : IsProbabilityMeasure (Measure.map oneCode P) :=
    Measure.isProbabilityMeasure_map oneCode.aemeasurable
  letI : IsProbabilityMeasure (Measure.map (fun ω ↦ constCode (part.toSimpleFunc ω)) P) := by
    simpa [honeCode] using
      (show IsProbabilityMeasure (Measure.map oneCode P) from inferInstance)
  have hblockLaw :
      (part.block τ hτ.measurable 1).partitionEntropy P =
        entropy ((Measure.map oneCode P).toPMF) := by
    -- Proof comment: normalize the singleton block partition to the entropy of its block-value
    -- law.
    rw [block_eq_ofSimpleFunc_prefixBlockCode (hτ := hτ.measurable) (part := part) (n := (1 : ℕ+))]
    simpa [oneCode] using
      (partitionEntropy_ofSimpleFunc_eq_entropy_law (P := P) (g := oneCode))
  have hmapLaw :
      (Measure.map oneCode P).toPMF = PMF.map constCode (part.toPMF P) := by
    -- Proof comment: the singleton block law is the pushforward of the one-step partition law by
    -- the constant-on-`Fin 1` relabeling.
    simpa [MeasurableFinpartition.toPMF, honeCode] using
      (toPMF_eq_map_of_comp (P := P)
        (f := part.toSimpleFunc) (hf := part.toSimpleFunc.measurable)
        (g := constCode) (hg := Measurable.of_discrete (f := constCode)))
  calc
    (part.block τ hτ.measurable 1).partitionEntropy P =
        entropy ((Measure.map oneCode P).toPMF) := hblockLaw
    _ = entropy (PMF.map constCode (part.toPMF P)) := by
      rw [hmapLaw]
    _ = entropy (part.toPMF P) := by
      exact entropy_map_eq_of_injective (part.toPMF P) constCode hconstCode_injective
    _ = part.partitionEntropy P := by
      rw [MeasurableFinpartition.partitionEntropy_def]

/-- Helper for Theorem 20.35: block entropy is subadditive in the block length. -/
private theorem blockPartitionEntropy_add_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω)
    (m n : ℕ+) :
    (part.block τ hτ.measurable (m + n)).partitionEntropy P ≤
      (part.block τ hτ.measurable m).partitionEntropy P +
        (part.block τ hτ.measurable n).partitionEntropy P := by
  classical
  let q : SimpleFunc Ω (Fin (m + n) → part.parts) :=
    prefixBlockCode τ hτ.measurable part (m + n)
  let g : SimpleFunc Ω (Fin m → part.parts) :=
    prefixBlockCode τ hτ.measurable part m
  let e : SimpleFunc Ω (Fin n → part.parts) :=
    (prefixBlockCode τ hτ.measurable part n).comp (τ^[m]) (Measurable.iterate hτ.measurable m)
  have hdecode :
      q = fun ω : Ω ↦ (Fin.append (g ω) (e ω) : Fin (m + n) → part.parts) := by
    -- Proof comment: an `(m + n)`-block splits into its initial `m` coordinates and the
    -- following `n` coordinates read after shifting by `m`.
    funext ω
    ext i
    cases i using Fin.addCases with
    | left i =>
        simp [q, g, prefixBlockCode, Fin.append_left]
    | right i =>
        simp [q, e, prefixBlockCode, Fin.append_right, Function.comp_apply,
          Function.iterate_add_apply, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hshiftEntropy :
      (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P =
        (part.block τ hτ.measurable n).partitionEntropy P := by
    let base : SimpleFunc Ω (Fin n → part.parts) := prefixBlockCode τ hτ.measurable part n
    letI : IsProbabilityMeasure (Measure.map e P) :=
      Measure.isProbabilityMeasure_map e.aemeasurable
    letI : IsProbabilityMeasure (Measure.map base P) :=
      Measure.isProbabilityMeasure_map base.aemeasurable
    have hmap : Measure.map e P = Measure.map base P := by
      -- Proof comment: the shifted `n`-block has the same law as the unshifted `n`-block because
      -- every iterate of `τ` preserves `P`.
      calc
        Measure.map e P = Measure.map base (Measure.map (τ^[m]) P) := by
          simpa [e, base, Function.comp] using
            (Measure.map_map base.measurable
              (Measurable.iterate hτ.measurable m) (μ := P)).symm
        _ = Measure.map base P := by
          rw [(hτ.iterate m).map_eq]
    have hpmf :
        (Measure.map e P).toPMF = (Measure.map base P).toPMF := by
      simpa [hmap]
    calc
      (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P =
          entropy ((Measure.map e P).toPMF) := by
        -- Proof comment: rewrite the shifted block code entropy to the entropy of its law.
        simpa [e] using (partitionEntropy_ofSimpleFunc_eq_entropy_law (P := P) (g := e))
      _ = entropy ((Measure.map base P).toPMF) := by
        rw [hpmf]
      _ = (MeasurableFinpartition.ofSimpleFunc base).partitionEntropy P := by
        symm
        simpa [base] using (partitionEntropy_ofSimpleFunc_eq_entropy_law (P := P) (g := base))
      _ = (part.block τ hτ.measurable n).partitionEntropy P := by
        rw [block_eq_ofSimpleFunc_prefixBlockCode (hτ := hτ.measurable) (part := part) (n := n)]
  have hdecodeEntropy :
      (MeasurableFinpartition.ofSimpleFunc q).partitionEntropy P ≤
        (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P +
          (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P := by
    have hblock :=
      blockPartitionEntropy_le_add_ofPointwiseDecode
        (μ := P) (hτ := hτ.measurable) (q := q) (g := g) (e := e)
        (decode := Fin.append) hdecode (1 : ℕ+)
    -- Proof comment: apply the pointwise decoding inequality at block length `1`, where block
    -- entropy agrees with ordinary partition entropy.
    calc
      (MeasurableFinpartition.ofSimpleFunc q).partitionEntropy P =
          ((MeasurableFinpartition.ofSimpleFunc q).block τ hτ.measurable 1).partitionEntropy P := by
        symm
        exact blockPartitionEntropy_one_eq_partitionEntropy
          (P := P) (hτ := hτ) (part := MeasurableFinpartition.ofSimpleFunc q)
      _ ≤
          ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ.measurable 1).partitionEntropy P +
            ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable 1).partitionEntropy P := hblock
      _ =
          (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P +
            ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable 1).partitionEntropy P := by
        rw [blockPartitionEntropy_one_eq_partitionEntropy
          (P := P) (hτ := hτ) (part := MeasurableFinpartition.ofSimpleFunc g)]
      _ =
          (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P +
            (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P := by
        rw [blockPartitionEntropy_one_eq_partitionEntropy
          (P := P) (hτ := hτ) (part := MeasurableFinpartition.ofSimpleFunc e)]
  calc
    (part.block τ hτ.measurable (m + n)).partitionEntropy P =
        (MeasurableFinpartition.ofSimpleFunc q).partitionEntropy P := by
      rw [block_eq_ofSimpleFunc_prefixBlockCode
        (hτ := hτ.measurable) (part := part) (n := m + n)]
      simp [q]
    _ ≤
        (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P +
          (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P := hdecodeEntropy
    _ =
        (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P +
          (part.block τ hτ.measurable n).partitionEntropy P := by
      rw [hshiftEntropy]
    _ =
        (part.block τ hτ.measurable m).partitionEntropy P +
          (part.block τ hτ.measurable n).partitionEntropy P := by
      rw [block_eq_ofSimpleFunc_prefixBlockCode (hτ := hτ.measurable) (part := part) (n := m)]

/-- Helper for Theorem 20.35: adding one more time coordinate to a block increases the block
entropy by at most one copy of the one-step partition entropy. -/
private theorem blockPartitionEntropy_succ_le_add_partitionEntropy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω) (n : ℕ+) :
    (part.block τ hτ.measurable (n + 1)).partitionEntropy P ≤
      part.partitionEntropy P + (part.block τ hτ.measurable n).partitionEntropy P := by
  classical
  let q : SimpleFunc Ω (Fin (n + 1) → part.parts) :=
    prefixBlockCode τ hτ.measurable part (n + 1)
  let g : SimpleFunc Ω (Fin n → part.parts) :=
    prefixBlockCode τ hτ.measurable part n
  let e : SimpleFunc Ω part.parts :=
    part.toSimpleFunc.comp (τ^[n]) (Measurable.iterate hτ.measurable n)
  have hdecode : q = (fun ω : Ω ↦ (Fin.snoc (g ω) (e ω) : Fin (n + 1) → part.parts)) := by
    -- Proof comment: an `(n + 1)`-block is the `n`-prefix together with the last shifted atom.
    funext ω
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [q, g, prefixBlockCode]
    · simp [q, e, prefixBlockCode]
  have hshiftEntropy :
      (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P = part.partitionEntropy P := by
    letI : IsProbabilityMeasure (Measure.map e P) :=
      Measure.isProbabilityMeasure_map e.aemeasurable
    letI : IsProbabilityMeasure (Measure.map part.toSimpleFunc P) :=
      Measure.isProbabilityMeasure_map part.toSimpleFunc.aemeasurable
    have hmap :
        Measure.map e P = Measure.map part.toSimpleFunc P := by
      -- Proof comment: the final coordinate has the same law as the time-`0` partition because
      -- the iterate `τ^[n]` preserves `P`.
      calc
        Measure.map e P = Measure.map part.toSimpleFunc (Measure.map (τ^[n]) P) := by
          simpa [e, Function.comp] using
            (Measure.map_map part.toSimpleFunc.measurable
              (Measurable.iterate hτ.measurable n) (μ := P)).symm
        _ = Measure.map part.toSimpleFunc P := by
          rw [(hτ.iterate n).map_eq]
    have hpmf :
        (Measure.map e P).toPMF = (Measure.map part.toSimpleFunc P).toPMF := by
      simpa [hmap]
    calc
      (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P =
          entropy ((Measure.map e P).toPMF) := by
        -- Proof comment: rewrite the shifted one-step partition entropy to the entropy of its
        -- pushed-forward law.
        simpa [e] using (partitionEntropy_ofSimpleFunc_eq_entropy_law (P := P) (g := e))
      _ = entropy ((Measure.map part.toSimpleFunc P).toPMF) := by
        rw [hpmf]
      _ = entropy (part.toPMF P) := by
        rw [MeasurableFinpartition.toPMF]
      _ = part.partitionEntropy P := by
        rw [MeasurableFinpartition.partitionEntropy_def]
  have hdecodeEntropy :
      (MeasurableFinpartition.ofSimpleFunc q).partitionEntropy P ≤
        (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P +
          (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P := by
    have hblock :=
      blockPartitionEntropy_le_add_ofPointwiseDecode
        (μ := P) (hτ := hτ.measurable) (q := q) (g := g) (e := e)
        (decode := fun s a ↦ (Fin.snoc s a : Fin (n + 1) → part.parts)) hdecode (1 : ℕ+)
    -- Proof comment: reduce the decoded one-block estimate to the corresponding one-step
    -- entropies.
    calc
      (MeasurableFinpartition.ofSimpleFunc q).partitionEntropy P =
          ((MeasurableFinpartition.ofSimpleFunc q).block τ hτ.measurable 1).partitionEntropy P := by
        symm
        exact blockPartitionEntropy_one_eq_partitionEntropy
          (P := P) (hτ := hτ) (part := MeasurableFinpartition.ofSimpleFunc q)
      _ ≤
          ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ.measurable 1).partitionEntropy P +
            ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable 1).partitionEntropy P := hblock
      _ =
          (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P +
            ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable 1).partitionEntropy P := by
        rw [blockPartitionEntropy_one_eq_partitionEntropy
          (P := P) (hτ := hτ) (part := MeasurableFinpartition.ofSimpleFunc g)]
      _ =
          (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P +
            (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P := by
        rw [blockPartitionEntropy_one_eq_partitionEntropy
          (P := P) (hτ := hτ) (part := MeasurableFinpartition.ofSimpleFunc e)]
  calc
    (part.block τ hτ.measurable (n + 1)).partitionEntropy P =
        (MeasurableFinpartition.ofSimpleFunc q).partitionEntropy P := by
      rw [block_eq_ofSimpleFunc_prefixBlockCode (hτ := hτ.measurable) (part := part) (n := n + 1)]
      simp [q]
    _ ≤
        (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P +
          (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P := hdecodeEntropy
    _ = (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P + part.partitionEntropy P := by
      rw [hshiftEntropy]
    _ = part.partitionEntropy P + (part.block τ hτ.measurable n).partitionEntropy P := by
      rw [add_comm]
      rw [block_eq_ofSimpleFunc_prefixBlockCode (hτ := hτ.measurable) (part := part) (n := n)]

/-- Helper for Theorem 20.35: the entropy of an `n`-block is at most `n` times the one-step
partition entropy. -/
private theorem blockPartitionEntropy_le_mul_partitionEntropy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω) (n : ℕ+) :
    (part.block τ hτ.measurable n).partitionEntropy P ≤
      ((n : ℕ) : EReal) * part.partitionEntropy P := by
  have hpart_nonneg : 0 ≤ part.partitionEntropy P := by
    -- Proof comment: partition entropy is always nonnegative because it is Shannon entropy of a
    -- finite law.
    rw [MeasurableFinpartition.partitionEntropy_def]
    exact entropy_nonneg _
  refine PNat.recOn n ?_ ?_
  · -- Proof comment: at `n = 1`, the block entropy is exactly the one-step partition entropy.
    rw [blockPartitionEntropy_one_eq_partitionEntropy (P := P) (hτ := hτ) (part := part)]
    simp
  · intro k hk
    -- Proof comment: iterate the one-step growth estimate and then insert the induction bound
    -- for the remaining `k`-block.
    calc
      (part.block τ hτ.measurable (k + 1)).partitionEntropy P ≤
          part.partitionEntropy P + (part.block τ hτ.measurable k).partitionEntropy P :=
        blockPartitionEntropy_succ_le_add_partitionEntropy (P := P) (hτ := hτ) (part := part) k
      _ ≤ part.partitionEntropy P + (((k : ℕ) : EReal) * part.partitionEntropy P) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hk (part.partitionEntropy P)
      _ = (1 : EReal) * part.partitionEntropy P + ((k : ℕ) : EReal) * part.partitionEntropy P := by
        rw [one_mul]
      _ = (1 + ((k : ℕ) : EReal)) * part.partitionEntropy P := by
        symm
        exact EReal.right_distrib_of_nonneg (by positivity) (by positivity)
      _ = ((((k : ℕ) + 1 : ℕ) : EReal) * part.partitionEntropy P) := by
        norm_num [add_comm]

/-- Helper for Theorem 20.35: every normalized block term is bounded by the corresponding
one-step partition entropy. -/
private theorem normalizedBlockEntropyRate_le_partitionEntropy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω) (n : ℕ+) :
    (part.block τ hτ.measurable n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) ≤
      part.partitionEntropy P := by
  have hblock :
      (part.block τ hτ.measurable n).partitionEntropy P ≤
        ((n : ℕ) : EReal) * part.partitionEntropy P :=
    blockPartitionEntropy_le_mul_partitionEntropy (P := P) (hτ := hτ) (part := part) n
  have hInv_nonneg : 0 ≤ (((n : ℕ) : EReal)⁻¹) := by
    positivity
  have hpart_nonneg : 0 ≤ part.partitionEntropy P := by
    -- Proof comment: the target one-step entropy is nonnegative, so multiplying by a reciprocal
    -- preserves inequalities.
    rw [MeasurableFinpartition.partitionEntropy_def]
    exact entropy_nonneg _
  calc
    (part.block τ hτ.measurable n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) ≤
        ((((n : ℕ) : EReal) * part.partitionEntropy P) * (((n : ℕ) : EReal)⁻¹)) := by
      exact mul_le_mul_of_nonneg_right hblock hInv_nonneg
    _ = part.partitionEntropy P := by
      have hnat_cancel : (((n : ℕ) : EReal) * (((n : ℕ) : EReal)⁻¹)) = 1 := by
        have hn_real_ne : ((n : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast n.ne_zero
        change ((((n : ℕ) : ℝ) : EReal) * ((((n : ℕ) : ℝ) : EReal)⁻¹)) = 1
        rw [← EReal.coe_inv, ← EReal.coe_mul]
        norm_num [hn_real_ne]
      calc
        ((((n : ℕ) : EReal) * part.partitionEntropy P) * (((n : ℕ) : EReal)⁻¹)) =
            part.partitionEntropy P * ((((n : ℕ) : EReal) * (((n : ℕ) : EReal)⁻¹))) := by
          ac_rfl
        _ = part.partitionEntropy P * 1 := by
          rw [hnat_cancel]
        _ = part.partitionEntropy P := by
          rw [mul_one]

/-- Helper for Theorem 20.35: the normalized block entropy of an `Option β`-valued code is
bounded by the one-step rare-symbol entropy expression of its pushforward law. -/
private theorem normalizedOptionBlockEntropyRate_le_entropyLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) {β : Type*}
    [Fintype β] [MeasurableSpace (Option β)] [MeasurableSingletonClass (Option β)]
    [Countable (Option β)]
    (e : SimpleFunc Ω (Option β)) [IsProbabilityMeasure (Measure.map e P)] (n : ℕ+) :
    ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable n).partitionEntropy P *
      (((n : ℕ) : EReal)⁻¹) ≤
      ((Real.negMulLog ((((Measure.map e P).toPMF) none).toReal) +
          Real.negMulLog (1 - (((Measure.map e P).toPMF) none).toReal) +
          (1 - (((Measure.map e P).toPMF) none).toReal) * Real.log (Fintype.card β)) : ℝ) := by
  let p : PMF (Option β) := (Measure.map e P).toPMF
  have hrate :
      ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable n).partitionEntropy P *
        (((n : ℕ) : EReal)⁻¹) ≤
        (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P :=
    normalizedBlockEntropyRate_le_partitionEntropy
      (P := P) (hτ := hτ) (part := MeasurableFinpartition.ofSimpleFunc e) n
  have hpart :
      (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P ≤
        ((Real.negMulLog ((p none).toReal) + Real.negMulLog (1 - (p none).toReal) +
            (1 - (p none).toReal) * Real.log (Fintype.card β)) : ℝ) := by
    calc
      (MeasurableFinpartition.ofSimpleFunc e).partitionEntropy P = entropy p := by
        -- Proof comment: identify the one-step entropy of `e` with the Shannon entropy of its
        -- pushforward law.
        simpa [p] using (partitionEntropy_ofSimpleFunc_eq_entropy_law (P := P) (g := e))
      _ ≤
        ((Real.negMulLog ((p none).toReal) + Real.negMulLog (1 - (p none).toReal) +
            (1 - (p none).toReal) * Real.log (Fintype.card β)) : ℝ) :=
        entropyOption_le_ofNonNoneMass p
  exact le_trans hrate hpart

/-- Helper for Theorem 20.35: if the non-`none` region of an `Option β`-valued code has small
measure, then every normalized block entropy of that code is uniformly small. -/
private theorem normalizedOptionBlockEntropyRateLtOfNonNoneMeasureLt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) {β : Type*}
    [Fintype β] [MeasurableSpace (Option β)] [MeasurableSingletonClass (Option β)]
    [Countable (Option β)] {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (e : SimpleFunc Ω (Option β)) [IsProbabilityMeasure (Measure.map e P)],
        P {ω | e ω ≠ none} < ENNReal.ofReal δ →
        ∀ n : ℕ+,
          ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable n).partitionEntropy P *
            (((n : ℕ) : EReal)⁻¹) < (η : EReal) := by
  let f : ℝ → ℝ := fun x ↦
    Real.negMulLog (1 - x) + Real.negMulLog x + x * Real.log (Fintype.card β)
  have hcont_left : Continuous fun x : ℝ ↦ Real.negMulLog (1 - x) := by
    -- Proof comment: the rare-error entropy control function is continuous at `0`, so small
    -- non-`none` mass forces the one-step entropy bound to be small as well.
    simpa using (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id'))
  have hcont_right :
      Continuous fun x : ℝ ↦ Real.negMulLog x + x * Real.log (Fintype.card β) := by
    exact Real.continuous_negMulLog.add (continuous_id'.mul continuous_const)
  have hcont : Continuous f := by
    simpa [f, add_assoc] using hcont_left.add hcont_right
  have hcont0 : ContinuousAt f 0 := hcont.continuousAt
  have hf_zero : f 0 = 0 := by
    simp [f]
  rcases Metric.continuousAt_iff.mp hcont0 η hη with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro e _ hrare n
  have hrate :=
    normalizedOptionBlockEntropyRate_le_entropyLaw
      (P := P) (hτ := hτ) (β := β) e n
  have hpnone_eq :
      (((Measure.map e P).toPMF) none).toReal = (P {ω | e ω = none}).toReal := by
    -- Proof comment: the `none` mass of the pushed-forward law is exactly the measure of the
    -- `none` fiber of `e`.
    rw [Measure.toPMF_apply]
    rw [Measure.map_apply e.measurable (measurableSet_singleton none)]
    rfl
  have hprob_real :
      (P {ω | e ω = none}).toReal + (P {ω | e ω ≠ none}).toReal = 1 := by
    -- Proof comment: split the probability space into the `none` fiber and its complement.
    simpa [Set.compl_setOf, not_not] using
      probReal_add_probReal_compl (μ := P) (s := {ω | e ω = none}) (e.measurableSet_fiber none)
  have hmass :
      1 - (((Measure.map e P).toPMF) none).toReal = (P {ω | e ω ≠ none}).toReal := by
    -- Proof comment: combine the pushed-forward `none` mass identity with the complement
    -- probability decomposition.
    linarith [hprob_real, hpnone_eq]
  let x : ℝ := (P {ω | e ω ≠ none}).toReal
  have hnone_real : (P {ω | e ω = none}).toReal = 1 - x := by
    dsimp [x]
    linarith [hprob_real]
  have hpnone_real : (((Measure.map e P).toPMF) none).toReal = 1 - x := by
    rw [hpnone_eq, hnone_real]
  have hx_dist : dist x 0 < δ := by
    -- Proof comment: the rare-event mass itself is the small continuity input.
    dsimp [x]
    simpa [Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using
      ENNReal.toReal_lt_of_lt_ofReal hrare
  have hsmall_dist : dist (f x) (f 0) < η := by
    exact hδ hx_dist
  have hsmall_abs :
      |f x - f 0| < η := by
    simpa [Real.dist_eq] using hsmall_dist
  have hsmall : f x < η := by
    simpa [hf_zero] using (abs_lt.mp hsmall_abs).2
  have hrate' :
      ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable n).partitionEntropy P *
          (((n : ℕ) : EReal)⁻¹) ≤
        (f x : ℝ) := by
    calc
      ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable n).partitionEntropy P *
          (((n : ℕ) : EReal)⁻¹) ≤
        ((Real.negMulLog ((((Measure.map e P).toPMF) none).toReal) +
            Real.negMulLog (1 - (((Measure.map e P).toPMF) none).toReal) +
            (1 - (((Measure.map e P).toPMF) none).toReal) * Real.log (Fintype.card β)) : ℝ) := hrate
      _ = (f x : ℝ) := by
        simpa [f, hpnone_real, hmass, x, sub_sub_cancel]
  exact lt_of_le_of_lt hrate' <| by
    exact_mod_cast hsmall

/-- Helper for Theorem 20.35: once a code factors through an `N`-block of `part`, every `n`-block
entropy of that code is dominated by the corresponding long block entropy of `part`. -/
private theorem blockFactorEntropy_le_longBlockEntropy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : Measurable τ) (part : MeasurableFinpartition Ω)
    {α : Type*} (g : SimpleFunc Ω α) {N : ℕ+} {ψ : (part.block τ hτ N).parts → α}
    (hg : g = fun ω ↦ ψ ((part.block τ hτ N).toSimpleFunc ω)) (n : ℕ+) :
    (((MeasurableFinpartition.ofSimpleFunc g).block τ hτ n).partitionEntropy P) ≤
      (part.block τ hτ (N + n - 1)).partitionEntropy P := by
  rcases blockFactor_of_block hτ part g hg n with ⟨Φ, hΦ⟩
  -- Proof comment: the block factorization turns the long `part`-block into a coding of the
  -- `g`-block, so one-step factor monotonicity applies directly.
  exact partitionEntropy_le_of_toSimpleFuncFactor P Φ hΦ

/-- Helper for Theorem 20.35: every normalized block term bounds the dynamical entropy of a fixed
finite measurable partition from above. -/
private theorem dynamicalEntropy_le_blockTerm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → Ω) (hτ : Measurable τ) (part : MeasurableFinpartition Ω) (n : ℕ+) :
    h(P, τ, hτ; part) ≤
      (part.block τ hτ n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) := by
  -- Proof comment: expose the chosen block term as one element of the defining infimum range.
  rw [MeasurableFinpartition.dynamicalEntropy_def]
  exact sInf_le (Set.mem_range.mpr ⟨n, rfl⟩)

/-- Helper for Theorem 20.35: every block entropy is nonnegative because it is the Shannon entropy
of a finite pushed-forward law. -/
private theorem blockPartitionEntropy_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : Measurable τ) (part : MeasurableFinpartition Ω) (n : ℕ+) :
    0 ≤ (part.block τ hτ n).partitionEntropy P := by
  -- Proof comment: unfold partition entropy to the entropy of the induced block law and apply the
  -- basic Shannon nonnegativity bound.
  rw [MeasurableFinpartition.partitionEntropy_def]
  exact entropy_nonneg _

/-- Helper for Theorem 20.35: a shifted long-block term with denominator `n` still dominates the
partition dynamical entropy. -/
private theorem shiftedBlockTermInf_le_dynamicalEntropy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω)
    (N n : ℕ+) :
    h(P, τ, hτ.measurable; part) ≤
      (part.block τ hτ.measurable (N + n - 1)).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) := by
  have hbase :
      h(P, τ, hτ.measurable; part) ≤
        (part.block τ hτ.measurable (N + n - 1)).partitionEntropy P *
          ((((N + n - 1 : ℕ+) : ℕ) : EReal)⁻¹) :=
    dynamicalEntropy_le_blockTerm P τ hτ.measurable part (N + n - 1)
  have hnonneg :
      0 ≤ (part.block τ hτ.measurable (N + n - 1)).partitionEntropy P :=
    blockPartitionEntropy_nonneg P hτ.measurable part (N + n - 1)
  have hnat :
      (n : ℕ) ≤ ((N + n - 1 : ℕ+) : ℕ) := by
    have hm_pnat : n ≤ N + n - 1 := by
      exact PNat.le_sub_one_of_lt (PNat.lt_add_left n N)
    exact (PNat.coe_le_coe n (N + n - 1)).2 hm_pnat
  have hInv :
      ((((N + n - 1 : ℕ+) : ℕ) : EReal)⁻¹) ≤ (((n : ℕ) : EReal)⁻¹) := by
    -- Proof comment: enlarging the block length only decreases the reciprocal denominator.
    change ((((((N + n - 1 : ℕ+) : ℕ) : ℝ) : EReal)⁻¹) ≤
      ((((n : ℕ) : ℝ) : EReal)⁻¹))
    rw [← EReal.coe_inv, ← EReal.coe_inv]
    simpa [one_div] using
      (show 1 / ((((N + n - 1 : ℕ+) : ℕ) : ℝ)) ≤ 1 / ((n : ℕ) : ℝ) from
        one_div_le_one_div_of_le (by exact_mod_cast n.2) (by exact_mod_cast hnat))
  calc
    h(P, τ, hτ.measurable; part) ≤
        (part.block τ hτ.measurable (N + n - 1)).partitionEntropy P *
          ((((N + n - 1 : ℕ+) : ℕ) : EReal)⁻¹) :=
      hbase
    _ ≤ (part.block τ hτ.measurable (N + n - 1)).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) := by
      -- Proof comment: replace the longer reciprocal denominator by the larger `1 / n`.
      exact mul_le_mul_of_nonneg_left hInv hnonneg

/-- Helper for Theorem 20.35: if the sum of the atomwise bad-set measures is small, then the
whole bad union is small as well. -/
private theorem measure_badApproxSet_lt_of_sum_lt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] (bad : ι → Set Ω) {ε : ℝ}
    (hbad : (∑ i, P (bad i)) < ENNReal.ofReal ε) :
    P (⋃ i, bad i) < ENNReal.ofReal ε := by
  -- Proof comment: finite subadditivity upgrades the pointwise sum bound to the whole bad union.
  exact lt_of_le_of_lt (measure_iUnion_fintype_le P bad) hbad

/-- Helper for Theorem 20.35: from a common-length family of block-atom approximants, build a
total label on long block atoms that agrees with `q.toSimpleFunc` outside the bad union. -/
private theorem exists_blockLabel_of_commonLengthApproximationFamily
    {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → Ω} (hτ : Measurable τ)
    (part q : MeasurableFinpartition Ω) (N : ℕ+)
    (U : q.parts → Finset (part.block τ hτ N).parts) :
    ∃ ψ : (part.block τ hτ N).parts → q.parts,
      ∀ ⦃ω : Ω⦄,
        ω ∉
            ⋃ A : q.parts,
              ((((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) \
                    blockPartsUnion (part.block τ hτ N) (U A)) ∪
                (blockPartsUnion (part.block τ hτ N) (U A) \
                  (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)))) →
        ψ ((part.block τ hτ N).toSimpleFunc ω) = q.toSimpleFunc ω := by
  classical
  let block := part.block τ hτ N
  let claimants : block.parts → Finset q.parts := fun B ↦
    Finset.univ.filter fun A : q.parts => B ∈ U A
  have hreps :
      ∀ B : block.parts,
        ∃ ω : Ω, ω ∈ (((B.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) := by
    intro B
    have hB_nonempty :
        ((((B.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) : Set Ω).Nonempty := by
      by_contra hB_nonempty
      apply block.ne_bot B.2
      ext ω
      simp [Set.not_nonempty_iff_eq_empty.mp hB_nonempty]
    exact hB_nonempty
  choose rep hrep using hreps
  let ψ : block.parts → q.parts := fun B ↦
    if hB : (claimants B).Nonempty then hB.choose else q.toSimpleFunc (rep B)
  refine ⟨ψ, ?_⟩
  intro ω hgood
  let A : q.parts := q.toSimpleFunc ω
  let B : block.parts := block.toSimpleFunc ω
  have hωA :
      ω ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) := by
    simpa [A] using mem_toSimpleFunc_atom q ω
  have hωB :
      ω ∈ (((B.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) := by
    simpa [B] using mem_toSimpleFunc_atom block ω
  have hnot_badA :
      ω ∉
        ((((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) \
              blockPartsUnion block (U A)) ∪
          (blockPartsUnion block (U A) \
            (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)))) := by
    intro hbadA
    exact hgood <| Set.mem_iUnion.2 ⟨A, hbadA⟩
  have hω_unionA : ω ∈ blockPartsUnion block (U A) := by
    by_contra hω_unionA
    exact hnot_badA (by
      left
      exact ⟨hωA, hω_unionA⟩)
  have hB_mem : B ∈ U A := by
    rcases Set.mem_iUnion.1 hω_unionA with ⟨B', hω_unionA⟩
    rcases Set.mem_iUnion.1 hω_unionA with ⟨hB', hωB'⟩
    have hBB' : B = B' := by
      exact (mem_atom_iff_toSimpleFunc_eq block).mp hωB'
    simpa [hBB'] using hB'
  have hclaimants_nonempty : (claimants B).Nonempty := by
    refine ⟨A, ?_⟩
    simp [claimants, hB_mem]
  have hclaimants_eq :
      ∀ A' ∈ claimants B, A' = A := by
    intro A' hA'
    have hA'_mem : B ∈ U A' := by
      exact (Finset.mem_filter.mp hA').2
    have hω_unionA' : ω ∈ blockPartsUnion block (U A') := by
      exact Set.mem_iUnion.2 ⟨B, Set.mem_iUnion.2 ⟨hA'_mem, hωB⟩⟩
    have hnot_badA' :
        ω ∉
          ((((A'.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) \
                blockPartsUnion block (U A')) ∪
            (blockPartsUnion block (U A') \
              (((A'.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)))) := by
      intro hbadA'
      exact hgood <| Set.mem_iUnion.2 ⟨A', hbadA'⟩
    have hωA' :
        ω ∈ (((A'.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) := by
      by_contra hωA'
      exact hnot_badA' (by
        right
        exact ⟨hω_unionA', hωA'⟩)
    exact ((mem_atom_iff_toSimpleFunc_eq q).mp hωA').symm.trans (by rfl)
  have hψ_eq : ψ B = A := by
    dsimp [ψ]
    simp [hclaimants_nonempty]
    exact hclaimants_eq _ hclaimants_nonempty.choose_spec
  simpa [A, B] using hψ_eq

/-- Helper for Theorem 20.35: the generator approximation can be packaged as one long-block
factor of `part` together with a rare `Option`-valued error code that exactly decodes the
competitor code `q.toSimpleFunc`. -/
private theorem existsDecodedBlockCodeWithSmallError
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : Measurable τ) (part : MeasurableFinpartition Ω)
    (hgen : is_generator τ part) (q : MeasurableFinpartition Ω) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ+, ∃ ψ : (part.block τ hτ N).parts → q.parts,
      ∃ e : SimpleFunc Ω (Option q.parts),
        (q.toSimpleFunc = fun ω ↦
          Option.elim (e ω) (ψ ((part.block τ hτ N).toSimpleFunc ω)) id) ∧
        P {ω | e ω ≠ none} < ENNReal.ofReal δ := by
  classical
  rcases existsCommonLengthBlockAtomApproximationFamily
      (P := P) (hτ := hτ) (part := part) hgen q hδ with
    ⟨N, U, hU⟩
  rcases exists_blockLabel_of_commonLengthApproximationFamily
      (hτ := hτ) (part := part) (q := q) N U with
    ⟨ψ, hψ⟩
  let block : MeasurableFinpartition Ω := part.block τ hτ N
  let bad : Set Ω :=
    ⋃ A : q.parts,
      (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) \
          blockPartsUnion block (U A)) ∪
        (blockPartsUnion block (U A) \
          (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)))
  have hbad_meas : MeasurableSet bad := by
    -- Proof comment: the bad region is a finite union of measurable symmetric differences.
    refine MeasurableSet.iUnion fun A ↦ ?_
    exact (A.1.2.diff (measurableSet_blockPartsUnion block (U A))).union
      ((measurableSet_blockPartsUnion block (U A)).diff A.1.2)
  let e : SimpleFunc Ω (Option q.parts) :=
    SimpleFunc.piecewise bad hbad_meas (q.toSimpleFunc.map some) (SimpleFunc.const Ω none)
  refine ⟨N, ψ, e, ?_⟩
  constructor
  · -- Proof comment: away from the bad region the block label decodes correctly, while on the
    -- bad region the error code stores the exact atom of `q`.
    funext ω
    by_cases hω : ω ∈ bad
    · simp [e, hω]
    · have hψω : ψ (block.toSimpleFunc ω) = q.toSimpleFunc ω := hψ hω
      simp [e, hω, block, hψω]
  · have hbad_lt : P bad < ENNReal.ofReal δ := by
      -- Proof comment: finite subadditivity upgrades the atomwise approximation budget to the
      -- full bad region.
      exact measure_badApproxSet_lt_of_sum_lt (P := P)
        (bad := fun A : q.parts ↦
          (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) \
              blockPartsUnion block (U A)) ∪
            (blockPartsUnion block (U A) \
              (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)))) hU
    have hnonNone : {ω | e ω ≠ none} = bad := by
      -- Proof comment: by construction, the `Option` code is `some` exactly on the bad region.
      ext ω
      by_cases hω : ω ∈ bad <;> simp [e, hω]
    simpa [hnonNone] using hbad_lt

/-- Helper for Theorem 20.35: the Shannon entropy of a finite measurable partition is finite. -/
private theorem partitionEntropy_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (part : MeasurableFinpartition Ω) :
    part.partitionEntropy P < ⊤ := by
  -- Proof comment: the law of a finite partition is a finite pmf, so its Shannon entropy is
  -- bounded above by the logarithm of the finite alphabet size.
  rw [MeasurableFinpartition.partitionEntropy_def]
  exact lt_of_le_of_lt (entropy_le_log_card (part.toPMF P)) (by simp)

/-- Helper for Theorem 20.35: the entropy of a `k * m` block is controlled by `k` copies of the
`m`-block entropy. -/
private theorem blockPartitionEntropy_mul_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω)
    (k m : ℕ+) :
    (part.block τ hτ.measurable (k * m)).partitionEntropy P ≤
      ((k : ℕ) : EReal) * (part.block τ hτ.measurable m).partitionEntropy P := by
  have hm_nonneg :
      0 ≤ (part.block τ hτ.measurable m).partitionEntropy P :=
    blockPartitionEntropy_nonneg P hτ.measurable part m
  refine PNat.recOn k ?_ ?_
  · -- Proof comment: the single multiple is exactly the original `m`-block, and the coefficient
    -- on the right is `1`.
    rw [one_mul]
    simp
  · intro k hk
    -- Proof comment: split the `(k + 1) * m` block into a `k * m` prefix and one more `m`-block,
    -- then insert the induction bound and regroup the coefficient.
    have hmul :
        ((k + 1) * m : ℕ+) = k * m + m := by
      apply PNat.coe_injective
      simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        Nat.left_distrib, Nat.right_distrib]
    calc
      (part.block τ hτ.measurable ((k + 1) * m)).partitionEntropy P =
          (part.block τ hτ.measurable (k * m + m)).partitionEntropy P := by
        rw [hmul]
      _ ≤
          (part.block τ hτ.measurable (k * m)).partitionEntropy P +
            (part.block τ hτ.measurable m).partitionEntropy P :=
        blockPartitionEntropy_add_le (P := P) (hτ := hτ) (part := part) (k * m) m
      _ ≤
          ((k : ℕ) : EReal) * (part.block τ hτ.measurable m).partitionEntropy P +
            (part.block τ hτ.measurable m).partitionEntropy P := by
        gcongr
      _ =
          ((((k : ℕ) + 1 : ℕ) : EReal) * (part.block τ hτ.measurable m).partitionEntropy P) := by
        calc
          ((k : ℕ) : EReal) * (part.block τ hτ.measurable m).partitionEntropy P +
              (part.block τ hτ.measurable m).partitionEntropy P =
              ((k : ℕ) : EReal) * (part.block τ hτ.measurable m).partitionEntropy P +
                (part.block τ hτ.measurable m).partitionEntropy P * 1 := by
            rw [mul_one]
          _ =
              (part.block τ hτ.measurable m).partitionEntropy P *
                ((((k : ℕ) + 1 : ℕ) : EReal)) := by
            calc
              ((k : ℕ) : EReal) * (part.block τ hτ.measurable m).partitionEntropy P +
                  (part.block τ hτ.measurable m).partitionEntropy P * 1 =
                  (part.block τ hτ.measurable m).partitionEntropy P * ((k : ℕ) : EReal) +
                    (part.block τ hτ.measurable m).partitionEntropy P * 1 := by
                rw [mul_comm (((k : ℕ) : EReal))]
              _ =
                  (part.block τ hτ.measurable m).partitionEntropy P *
                    (((k : ℕ) : EReal) + 1) := by
                symm
                exact EReal.left_distrib_of_nonneg (by positivity) (by positivity)
              _ = (part.block τ hτ.measurable m).partitionEntropy P *
                    ((((k : ℕ) + 1 : ℕ) : EReal)) := by
                norm_num
          _ =
              ((((k : ℕ) + 1 : ℕ) : EReal) * (part.block τ hτ.measurable m).partitionEntropy P) := by
            rw [mul_comm]
      _ =
          (((k + 1 : ℕ+) : ℕ) : EReal) * (part.block τ hτ.measurable m).partitionEntropy P := by
        norm_num

/-- Helper for Theorem 20.35: normalized block entropy does not increase when the block length is
replaced by a positive multiple. -/
private theorem normalizedBlockEntropyRate_mul_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω)
    (k m : ℕ+) :
    (part.block τ hτ.measurable (k * m)).partitionEntropy P *
        ((((k * m : ℕ)) : EReal)⁻¹) ≤
      (part.block τ hτ.measurable m).partitionEntropy P * (((m : ℕ) : EReal)⁻¹) := by
  -- Proof comment: compare the raw block entropies first, then normalize by the same positive
  -- reciprocal and cancel the extra factor `k` at the coefficient level.
  have hmul :=
    blockPartitionEntropy_mul_le (P := P) (hτ := hτ) (part := part) k m
  have hinv_nonneg : 0 ≤ ((((k * m : ℕ)) : EReal)⁻¹) := by
    positivity
  have hcoeff :
      ((k : ℕ) : EReal) * ((((k * m : ℕ)) : EReal)⁻¹) = (((m : ℕ) : EReal)⁻¹) := by
    have hk_real_ne : ((k : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast k.ne_zero
    have hm_real_ne : ((m : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast m.ne_zero
    have hmul_real :
        ((k * m : ℕ) : ℝ) = ((k : ℕ) : ℝ) * ((m : ℕ) : ℝ) := by
      exact_mod_cast (show ((k * m : ℕ+) : ℕ) = (k : ℕ) * (m : ℕ) by rfl)
    have hcoeff_real :
        ((k : ℕ) : ℝ) * (((k * m : ℕ) : ℝ)⁻¹) = (((m : ℕ) : ℝ)⁻¹) := by
      rw [hmul_real]
      field_simp [hk_real_ne, hm_real_ne]
    calc
      ((k : ℕ) : EReal) * ((((k * m : ℕ)) : EReal)⁻¹) =
          ((((k : ℕ) : ℝ) : EReal) * ((((k * m : ℕ) : ℝ) : EReal)⁻¹)) := by
        norm_num [hmul_real]
      _ = ((((k : ℕ) : ℝ) * (((k * m : ℕ) : ℝ)⁻¹) : ℝ) : EReal) := by
        rw [← EReal.coe_inv, ← EReal.coe_mul]
      _ = (((((m : ℕ) : ℝ)⁻¹ : ℝ) : EReal)) := by
        exact_mod_cast hcoeff_real
      _ = (((m : ℕ) : EReal)⁻¹) := by
        simpa using (EReal.coe_inv (((m : ℕ) : ℝ))).symm
  calc
    (part.block τ hτ.measurable (k * m)).partitionEntropy P * ((((k * m : ℕ)) : EReal)⁻¹) ≤
        (((k : ℕ) : EReal) * (part.block τ hτ.measurable m).partitionEntropy P) *
          ((((k * m : ℕ)) : EReal)⁻¹) := by
      exact mul_le_mul_of_nonneg_right hmul hinv_nonneg
    _ =
        (part.block τ hτ.measurable m).partitionEntropy P *
          (((k : ℕ) : EReal) * ((((k * m : ℕ)) : EReal)⁻¹)) := by
      ac_rfl
    _ =
        (part.block τ hτ.measurable m).partitionEntropy P * (((m : ℕ) : EReal)⁻¹) := by
      rw [hcoeff]

/-- Helper for Theorem 20.35: adding `t` prefix coordinates costs at most `t` copies of the
one-step partition entropy. -/
private theorem blockPartitionEntropy_prefixNat_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω)
    (t : ℕ) (n : ℕ+) :
    (part.block τ hτ.measurable ⟨t + n, Nat.add_pos_right t n.2⟩).partitionEntropy P ≤
      ((t : ℕ) : EReal) * part.partitionEntropy P +
        (part.block τ hτ.measurable n).partitionEntropy P := by
  have hpart_nonneg : 0 ≤ part.partitionEntropy P := by
    rw [MeasurableFinpartition.partitionEntropy_def]
    exact entropy_nonneg _
  induction t with
  | zero =>
      -- Proof comment: with no prefix, there is nothing to pay beyond the original `n`-block.
      have hzero : (⟨0 + n, Nat.add_pos_right 0 n.2⟩ : ℕ+) = n := by
        apply PNat.coe_injective
        simp
      rw [hzero]
      simp
  | succ t ih =>
      let n' : ℕ+ := ⟨t + n, Nat.add_pos_right t n.2⟩
      have hindex :
          (⟨Nat.succ t + n, Nat.add_pos_right _ n.2⟩ : ℕ+) = n' + (1 : ℕ+) := by
        apply PNat.coe_injective
        simp [n', Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      calc
        (part.block τ hτ.measurable ⟨Nat.succ t + n, Nat.add_pos_right _ n.2⟩).partitionEntropy P =
            (part.block τ hτ.measurable (n' + (1 : ℕ+))).partitionEntropy P := by
          rw [hindex]
        _ ≤
            part.partitionEntropy P + (part.block τ hτ.measurable n').partitionEntropy P :=
          blockPartitionEntropy_succ_le_add_partitionEntropy
            (P := P) (hτ := hτ) (part := part) n'
        _ ≤ part.partitionEntropy P +
            (((t : ℕ) : EReal) * part.partitionEntropy P +
              (part.block τ hτ.measurable n).partitionEntropy P) := by
          have hih :
              (part.block τ hτ.measurable n').partitionEntropy P ≤
                ((t : ℕ) : EReal) * part.partitionEntropy P +
                  (part.block τ hτ.measurable n).partitionEntropy P := by
            simpa [n'] using ih
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left hih (part.partitionEntropy P)
        _ =
            (((Nat.succ t : ℕ) : EReal) * part.partitionEntropy P) +
              (part.block τ hτ.measurable n).partitionEntropy P := by
          -- Proof comment: regroup the two prefix-entropy summands before reassembling them as
          -- one copy of `(t + 1) * H(part)`.
          have hprefix_combine :
              part.partitionEntropy P + ((t : ℕ) : EReal) * part.partitionEntropy P =
                ((Nat.succ t : ℕ) : EReal) * part.partitionEntropy P := by
            calc
              part.partitionEntropy P + ((t : ℕ) : EReal) * part.partitionEntropy P =
                  (1 : EReal) * part.partitionEntropy P + ((t : ℕ) : EReal) * part.partitionEntropy P := by
                rw [one_mul]
              _ =
                  ((1 : EReal) + ((t : ℕ) : EReal)) * part.partitionEntropy P := by
                symm
                exact EReal.right_distrib_of_nonneg (by positivity) (by positivity)
              _ = ((Nat.succ t : ℕ) : EReal) * part.partitionEntropy P := by
                congr 1
                norm_num [Nat.succ_eq_add_one, add_comm]
          calc
            part.partitionEntropy P +
                (((t : ℕ) : EReal) * part.partitionEntropy P +
                  (part.block τ hτ.measurable n).partitionEntropy P) =
                (part.partitionEntropy P +
                    ((t : ℕ) : EReal) * part.partitionEntropy P) +
                  (part.block τ hτ.measurable n).partitionEntropy P := by
              ac_rfl
            _ =
                (((Nat.succ t : ℕ) : EReal) * part.partitionEntropy P) +
                  (part.block τ hτ.measurable n).partitionEntropy P := by
              rw [hprefix_combine]

/-- Helper for Theorem 20.35: a shifted long-block rate is bounded by the matching unshifted block
rate plus the finite entropy cost of the fixed prefix. -/
private theorem shiftedBlockEntropyRate_le_blockRate_add_prefixTail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω)
    (N n : ℕ+) :
    (part.block τ hτ.measurable (N + n - 1)).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) ≤
      (part.block τ hτ.measurable n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) +
        ((((N : ℕ) - 1 : ℕ) : EReal) * part.partitionEntropy P) * (((n : ℕ) : EReal)⁻¹) := by
  let t : ℕ := (N : ℕ) - 1
  have hindex :
      (N + n - 1 : ℕ+) = ⟨t + n, Nat.add_pos_right t n.2⟩ := by
    apply PNat.coe_injective
    dsimp [t]
    pnat_to_nat
    omega
  have hprefix :=
    blockPartitionEntropy_prefixNat_le (P := P) (hτ := hτ) (part := part) t n
  have hinv_nonneg : 0 ≤ (((n : ℕ) : EReal)⁻¹) := by
    positivity
  have hpart_nonneg : 0 ≤ part.partitionEntropy P := by
    rw [MeasurableFinpartition.partitionEntropy_def]
    exact entropy_nonneg _
  have hprefix_nonneg :
      0 ≤ ((t : ℕ) : EReal) * part.partitionEntropy P := by
    exact mul_nonneg (by positivity) hpart_nonneg
  have hblock_nonneg :
      0 ≤ (part.block τ hτ.measurable n).partitionEntropy P :=
    blockPartitionEntropy_nonneg P hτ.measurable part n
  calc
    (part.block τ hτ.measurable (N + n - 1)).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) =
        (part.block τ hτ.measurable ⟨t + n, Nat.add_pos_right t n.2⟩).partitionEntropy P *
          (((n : ℕ) : EReal)⁻¹) := by
      rw [hindex]
    _ ≤
        ((((t : ℕ) : EReal) * part.partitionEntropy P +
            (part.block τ hτ.measurable n).partitionEntropy P) * (((n : ℕ) : EReal)⁻¹)) := by
      exact mul_le_mul_of_nonneg_right hprefix hinv_nonneg
    _ =
        ((((t : ℕ) : EReal) * part.partitionEntropy P) * (((n : ℕ) : EReal)⁻¹)) +
          ((part.block τ hτ.measurable n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹)) := by
      exact EReal.right_distrib_of_nonneg hprefix_nonneg hblock_nonneg
    _ =
        (part.block τ hτ.measurable n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) +
          ((((N : ℕ) - 1 : ℕ) : EReal) * part.partitionEntropy P) * (((n : ℕ) : EReal)⁻¹) := by
      dsimp [t]
      rw [add_comm]

/-- Helper for Theorem 20.35: a finite nonnegative entropy coefficient can be made arbitrarily
small after multiplying by the reciprocal of a large positive integer. -/
private theorem exists_pnat_mul_inv_lt_of_lt
    {A : EReal} (hA_nonneg : 0 ≤ A) (hA_top : A < ⊤) {w : ℝ} (hw : 0 < w) :
    ∃ k : ℕ+, A * (((k : ℕ) : EReal)⁻¹) < (w : EReal) := by
  by_cases hA_zero : A = 0
  · refine ⟨1, ?_⟩
    simpa [hA_zero] using hw
  have hA_bot : A ≠ ⊥ := by
    intro hA_bot
    simpa [hA_bot] using hA_nonneg
  have hA_pos : 0 < A := by
    exact lt_of_le_of_ne hA_nonneg (by simpa [eq_comm] using hA_zero)
  have hA_real_pos : 0 < A.toReal := EReal.toReal_pos hA_pos hA_top.ne
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < w / A.toReal by
    exact div_pos hw hA_real_pos)
  let k : ℕ+ := ⟨m + 1, Nat.succ_pos _⟩
  refine ⟨k, ?_⟩
  have hreal :
      A.toReal * (1 / ((k : ℕ) : ℝ)) < w := by
    calc
      A.toReal * (1 / ((k : ℕ) : ℝ)) < A.toReal * (w / A.toReal) := by
        exact mul_lt_mul_of_pos_left (by simpa [k] using hm) hA_real_pos
      _ = w := by
        field_simp [hA_real_pos.ne']
  have hEq :
      A * (((k : ℕ) : EReal)⁻¹) = ((A.toReal * (1 / ((k : ℕ) : ℝ)) : ℝ) : EReal) := by
    rw [← EReal.coe_toReal hA_top.ne hA_bot]
    have hInv :
        (((k : ℕ) : EReal)⁻¹) = ((((k : ℝ))⁻¹ : ℝ) : EReal) := by
      rw [show ((k : ℕ) : EReal) = ((k : ℝ) : EReal) by norm_num]
      rw [← EReal.coe_inv (k : ℝ)]
    rw [hInv, ← EReal.coe_mul]
    norm_num [one_div]
  rw [hEq]
  exact_mod_cast hreal

/-- Helper for Theorem 20.35: from `h(P, τ; part) < u`, one can choose a shifted long block term
with the same denominator convention that is still below `u`. -/
private theorem existsShiftedLongBlockRateLt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω)
    (N : ℕ+) {u : ℝ} (hu : h(P, τ, hτ.measurable; part) < (u : EReal)) :
    ∃ n : ℕ+,
      (part.block τ hτ.measurable (N + n - 1)).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) <
        (u : EReal) := by
  rw [MeasurableFinpartition.dynamicalEntropy_def] at hu
  rcases sInf_lt_iff.mp hu with ⟨_, ⟨m, rfl⟩, hm_lt_u⟩
  obtain ⟨v, hm_lt_v, hv_lt_u⟩ := EReal.exists_between_coe_real hm_lt_u
  have huv_pos : 0 < u - v := by
    have hvu : v < u := by
      exact_mod_cast hv_lt_u
    linarith
  have hpart_nonneg : 0 ≤ part.partitionEntropy P := by
    rw [MeasurableFinpartition.partitionEntropy_def]
    exact entropy_nonneg _
  let A : EReal := ((((N : ℕ) - 1 : ℕ) : EReal) * part.partitionEntropy P)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity) hpart_nonneg
  have hA_top : A < ⊤ := by
    rw [lt_top_iff_ne_top]
    dsimp [A]
    have hNat_ne_top : ((((N : ℕ) - 1 : ℕ) : EReal) ≠ ⊤) := by
      change (((((N : ℕ) - 1 : ℕ) : ℝ) : EReal) ≠ ⊤)
      exact EReal.coe_ne_top ((((N : ℕ) - 1 : ℕ) : ℝ))
    exact (EReal.mul_ne_top _ _).2 ⟨Or.inr hpart_nonneg, Or.inl (by positivity),
      Or.inl hNat_ne_top, Or.inr (partitionEntropy_lt_top P part).ne⟩
  rcases exists_pnat_mul_inv_lt_of_lt hA_nonneg hA_top huv_pos with ⟨k, hk_tail⟩
  let n : ℕ+ := k * m
  have hmain :
      (part.block τ hτ.measurable n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) <
        (v : EReal) := by
    have hmul_rate :=
      normalizedBlockEntropyRate_mul_le (P := P) (hτ := hτ) (part := part) k m
    exact lt_of_le_of_lt (by simpa [n] using hmul_rate) hm_lt_v
  have htail_le :
      A * (((n : ℕ) : EReal)⁻¹) ≤ A * (((k : ℕ) : EReal)⁻¹) := by
    have hnat : (k : ℕ) ≤ (n : ℕ) := by
      dsimp [n]
      have hm_one : 1 ≤ (m : ℕ) := by exact_mod_cast m.2
      have hmul : (k : ℕ) * 1 ≤ (k : ℕ) * (m : ℕ) := Nat.mul_le_mul_left _ hm_one
      simpa [Nat.mul_one] using hmul
    have hInv :
        (((n : ℕ) : EReal)⁻¹) ≤ (((k : ℕ) : EReal)⁻¹) := by
      change (((((n : ℕ) : ℝ) : EReal)⁻¹) ≤ ((((k : ℕ) : ℝ) : EReal)⁻¹))
      rw [← EReal.coe_inv, ← EReal.coe_inv]
      simpa [one_div] using
        (show 1 / ((n : ℕ) : ℝ) ≤ 1 / ((k : ℕ) : ℝ) from
          one_div_le_one_div_of_le (by exact_mod_cast k.2) (by exact_mod_cast hnat))
    exact mul_le_mul_of_nonneg_left hInv hA_nonneg
  have htail :
      A * (((n : ℕ) : EReal)⁻¹) < ((u - v : ℝ) : EReal) := by
    exact lt_of_le_of_lt htail_le (by simpa [n] using hk_tail)
  refine ⟨n, ?_⟩
  have hshift :=
    shiftedBlockEntropyRate_le_blockRate_add_prefixTail (P := P) (hτ := hτ) (part := part) N n
  calc
    (part.block τ hτ.measurable (N + n - 1)).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) ≤
        (part.block τ hτ.measurable n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) +
          A * (((n : ℕ) : EReal)⁻¹) := by
      simpa [A] using hshift
    _ < (v : EReal) + (((u - v : ℝ) : EReal)) := EReal.add_lt_add hmain htail
    _ = (u : EReal) := by
      exact_mod_cast (show v + (u - v) = u by ring)

/-- Helper for Theorem 20.35: every competitor partition should be dominated by a generating
partition once the approximation-by-block and rare-error bounds are in place. -/
private theorem competitorDynamicalEntropy_le_generator
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω)
    (hgen : is_generator τ part) (q : MeasurableFinpartition Ω) :
    h(P, τ, hτ.measurable; q) ≤ h(P, τ, hτ.measurable; part) := by
  -- Route correction: the missing frontier is the long-block rate comparison, not the decoding
  -- package. We now combine the existing decoded long-block factor with the new shifted-rate
  -- lemma to contradict any strict entropy gap.
  letI : MeasurableSpace (Option q.parts) := ⊤
  letI : MeasurableSingletonClass (Option q.parts) := {
    measurableSet_singleton := by
      intro x
      trivial
  }
  letI : Countable (Option q.parts) := by
    infer_instance
  have hsmallError :
      ∀ {η : ℝ}, 0 < η →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (e : SimpleFunc Ω (Option q.parts)) [IsProbabilityMeasure (Measure.map e P)],
            P {ω | e ω ≠ none} < ENNReal.ofReal δ →
            ∀ n : ℕ+,
              ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable n).partitionEntropy P *
                (((n : ℕ) : EReal)⁻¹) < (η : EReal) := by
    intro η hη
    exact normalizedOptionBlockEntropyRateLtOfNonNoneMeasureLt
      (P := P) (hτ := hτ) (β := q.parts) hη
  by_contra hq
  have hgap : h(P, τ, hτ.measurable; part) < h(P, τ, hτ.measurable; q) :=
    lt_of_not_ge hq
  obtain ⟨u, hu_part, hu_q⟩ := EReal.exists_between_coe_real hgap
  obtain ⟨v, hv_part, hv_u⟩ := EReal.exists_between_coe_real hu_part
  have huv_pos : 0 < u - v := by
    have hv_u_real : v < u := by
      exact_mod_cast hv_u
    exact sub_pos.mpr hv_u_real
  obtain ⟨δ, hδ_pos, hδ_small⟩ := hsmallError huv_pos
  rcases existsDecodedBlockCodeWithSmallError
      (P := P) (hτ := hτ.measurable) (part := part) hgen q hδ_pos with
    ⟨N, ψ, e, hdecode, hrare⟩
  obtain ⟨n, hnlt⟩ :=
    existsShiftedLongBlockRateLt (P := P) (hτ := hτ) (part := part) N hv_part
  let g : SimpleFunc Ω q.parts :=
    (part.block τ hτ.measurable N).toSimpleFunc.map ψ
  have hg_factor :
      g = fun ω ↦ ψ ((part.block τ hτ.measurable N).toSimpleFunc ω) := by
    funext ω
    rfl
  have hg_norm_lt :
      ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ.measurable n).partitionEntropy P *
          (((n : ℕ) : EReal)⁻¹) <
        (v : EReal) := by
    have hg_long :
        ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ.measurable n).partitionEntropy P ≤
          (part.block τ hτ.measurable (N + n - 1)).partitionEntropy P :=
      blockFactorEntropy_le_longBlockEntropy
        (P := P) (hτ := hτ.measurable) (part := part) (g := g) (ψ := ψ) hg_factor n
    have hinv_nonneg : 0 ≤ (((n : ℕ) : EReal)⁻¹) := by
      positivity
    have hnorm_le :
        ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ.measurable n).partitionEntropy P *
            (((n : ℕ) : EReal)⁻¹) ≤
          (part.block τ hτ.measurable (N + n - 1)).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) := by
      exact mul_le_mul_of_nonneg_right hg_long hinv_nonneg
    exact lt_of_le_of_lt hnorm_le hnlt
  have he_norm_lt :
      ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable n).partitionEntropy P *
          (((n : ℕ) : EReal)⁻¹) <
        ((u - v : ℝ) : EReal) := by
    letI : IsProbabilityMeasure (Measure.map e P) :=
      Measure.isProbabilityMeasure_map e.aemeasurable
    exact hδ_small e hrare n
  have hdecode_block :=
    blockPartitionEntropy_le_add_ofPointwiseDecode
      (μ := P) (hτ := hτ.measurable) (q := q.toSimpleFunc) (g := g) (e := e)
      (decode := fun a o ↦ Option.elim o a id) hdecode n
  have hinv_nonneg : 0 ≤ (((n : ℕ) : EReal)⁻¹) := by
    positivity
  have hgnonneg :
      0 ≤ ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ.measurable n).partitionEntropy P :=
    blockPartitionEntropy_nonneg P hτ.measurable (MeasurableFinpartition.ofSimpleFunc g) n
  have henonneg :
      0 ≤ ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable n).partitionEntropy P :=
    blockPartitionEntropy_nonneg P hτ.measurable (MeasurableFinpartition.ofSimpleFunc e) n
  have hcontr : h(P, τ, hτ.measurable; q) < h(P, τ, hτ.measurable; q) := by
    -- Proof comment: compare the competitor entropy to one decoded block term, then split that
    -- normalized block entropy into the good-label contribution and the rare-error contribution.
    let qBlock : Ω → Fin n → q.parts := fun ω i ↦ q.toSimpleFunc ((τ^[i]) ω)
    letI : IsProbabilityMeasure (Measure.map qBlock P) :=
      Measure.isProbabilityMeasure_map (Measurable.aemeasurable <|
        measurable_pi_lambda _ fun i ↦
          q.toSimpleFunc.measurable.comp (Measurable.iterate hτ.measurable i))
    letI : IsProbabilityMeasure (Measure.map (prefixBlockCode τ hτ.measurable q n) P) :=
      Measure.isProbabilityMeasure_map (prefixBlockCode τ hτ.measurable q n).aemeasurable
    have hq_block_entropy :
        (q.block τ hτ.measurable n).partitionEntropy P =
          ((MeasurableFinpartition.ofSimpleFunc q.toSimpleFunc).block τ hτ.measurable n).partitionEntropy P := by
      calc
        (q.block τ hτ.measurable n).partitionEntropy P =
            entropy ((Measure.map qBlock P).toPMF) := by
          rw [block_eq_ofSimpleFunc_prefixBlockCode (hτ := hτ.measurable) (part := q) (n := n)]
          simpa [qBlock, prefixBlockCode] using
            (partitionEntropy_ofSimpleFunc_eq_entropy_law
              (P := P) (g := prefixBlockCode τ hτ.measurable q n))
        _ =
            ((MeasurableFinpartition.ofSimpleFunc q.toSimpleFunc).block τ hτ.measurable n).partitionEntropy P := by
          symm
          simpa [qBlock] using
            (blockPartitionEntropy_ofSimpleFunc_eq_entropy_valueBlockLaw
              (μ := P) (hτ := hτ.measurable) (g := q.toSimpleFunc) (n := n))
    calc
      h(P, τ, hτ.measurable; q) ≤
          (q.block τ hτ.measurable n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) :=
        dynamicalEntropy_le_blockTerm P τ hτ.measurable q n
      _ =
          ((MeasurableFinpartition.ofSimpleFunc q.toSimpleFunc).block τ hτ.measurable n).partitionEntropy P *
            (((n : ℕ) : EReal)⁻¹) := by
        rw [hq_block_entropy]
      _ ≤
          (((MeasurableFinpartition.ofSimpleFunc g).block τ hτ.measurable n).partitionEntropy P +
              ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable n).partitionEntropy P) *
            (((n : ℕ) : EReal)⁻¹) := by
        exact mul_le_mul_of_nonneg_right hdecode_block hinv_nonneg
      _ =
          ((MeasurableFinpartition.ofSimpleFunc g).block τ hτ.measurable n).partitionEntropy P *
              (((n : ℕ) : EReal)⁻¹) +
            ((MeasurableFinpartition.ofSimpleFunc e).block τ hτ.measurable n).partitionEntropy P *
              (((n : ℕ) : EReal)⁻¹) := by
        exact EReal.right_distrib_of_nonneg hgnonneg henonneg
      _ < (v : EReal) + ((u - v : ℝ) : EReal) := by
        exact EReal.add_lt_add hg_norm_lt he_norm_lt
      _ = (u : EReal) := by
        exact_mod_cast (show v + (u - v) = u by ring)
      _ < h(P, τ, hτ.measurable; q) := hu_q
  exact lt_irrefl _ hcontr

/-- Theorem 20.35: if `part` is a generator for the measurable space under `τ`, then the
Kolmogorov--Sinai entropy equals the dynamical entropy of `part`. -/
theorem kolmogorov_sinai_of_generator
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → Ω} (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω)
    (hgen : is_generator τ part) :
    h(P, τ, hτ.measurable) = h(P, τ, hτ.measurable; part) := by
  -- Proof comment: the easy inequality comes directly from the defining supremum. The remaining
  -- direction is the actual Kolmogorov--Sinai generator theorem.
  refine le_antisymm ?_ (dynamicalEntropy_le_kolmogorovSinai P τ hτ.measurable part)
  -- Proof comment: after rewriting the Kolmogorov--Sinai entropy as a supremum, it suffices to
  -- dominate each competitor partition by the generating partition `part`.
  rw [kolmogorov_sinai_entropy_def]
  refine sSup_le ?_
  rintro _ ⟨q, rfl⟩
  exact competitorDynamicalEntropy_le_generator P hτ part hgen q
