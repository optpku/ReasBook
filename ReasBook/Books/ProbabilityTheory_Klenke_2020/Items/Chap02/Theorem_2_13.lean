/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set

open scoped BigOperators

universe u v w

variable {Ω : Type u} {ι : Type v} {κ : Type w} [MeasurableSpace Ω]

/-- Theorem 2.13 (1): For a finite index type, independence of a family of event classes is
equivalent to the product formula for one choice of an event from each class over the whole index
set, provided each class contains `Ω`. -/
-- Proof sketch: For the forward direction, apply `iIndepSets.meas_iInter` on the finite index
-- type. For the reverse direction, recover the product formula on an arbitrary finite subfamily by
-- filling the missing indices with `univ`, which belongs to every `π i`.
theorem iIndepSets_iff_meas_iInter [Fintype ι] (π : ι → Set (Set Ω))
    (h_univ : ∀ i, univ ∈ π i) (μ : Measure Ω := by volume_tac) [IsProbabilityMeasure μ] :
    iIndepSets π μ ↔
      ∀ f : ι → Set Ω, (∀ i, f i ∈ π i) → μ (⋂ i, f i) = ∏ i, μ (f i) := by
  constructor
  · intro h f hf
    exact h.meas_iInter hf
  · intro h
    rw [iIndepSets_iff]
    intro s f hf
    classical
    let g : ι → Set Ω := fun i ↦ if i ∈ s then f i else univ
    have hg : ∀ i, g i ∈ π i := by
      intro i
      by_cases hi : i ∈ s
      · simpa [g, hi] using hf i hi
      · simpa [g, hi] using h_univ i
    have hg_eq := h g hg
    have h_inter : (⋂ i, g i) = ⋂ i ∈ s, f i := by
      ext x
      simp [g, Set.mem_iInter]
    have h_prod' : (∏ i, if i ∈ s then μ (f i) else 1) = ∏ i ∈ s, μ (f i) := by
      simp [Finset.prod_ite_mem]
    have h_prod_left : (∏ i, μ (g i)) = ∏ i, μ (if i ∈ s then f i else univ) := by
      simp [g]
    have h_pointwise : ∀ i, μ (if i ∈ s then f i else univ) = if i ∈ s then μ (f i) else 1 := by
      intro i
      by_cases hi : i ∈ s
      · simp [hi]
      · simp [hi, measure_univ]
    have h_prod_mid :
        (∏ i, μ (if i ∈ s then f i else univ)) = ∏ i, (if i ∈ s then μ (f i) else 1) := by
      exact Fintype.prod_congr _ _ h_pointwise
    have h_prod : (∏ i, μ (g i)) = ∏ i ∈ s, μ (f i) := by
      calc
        ∏ i, μ (g i) = ∏ i, μ (if i ∈ s then f i else univ) := h_prod_left
        _ = ∏ i, (if i ∈ s then μ (f i) else 1) := h_prod_mid
        _ = ∏ i ∈ s, μ (f i) := h_prod'
    rw [h_inter, h_prod] at hg_eq
    exact hg_eq

/-- Theorem 2.13 (2): A family of event classes is independent exactly when every finite subfamily
indexed by a finite set is independent. -/
-- Proof sketch: The forward implication is restriction along the inclusion `J ↪ ι` using
-- `iIndepSets.precomp`. For the reverse implication, fix a finite set of indices and apply the
-- assumed independence to the corresponding finite subtype.
theorem iIndepSets_iff_forall_finite_subfamily (π : ι → Set (Set Ω))
    (μ : Measure Ω := by volume_tac) :
    iIndepSets π μ ↔ ∀ J : Finset ι, iIndepSets (fun j : J ↦ π j) μ := by
  constructor
  · intro h J
    let g : J → ι := fun j ↦ j
    have hg : Function.Injective g := fun _ _ hij ↦ Subtype.ext hij
    simpa [g] using iIndepSets.precomp hg h
  · intro h
    rw [iIndepSets_iff]
    intro J f hf
    have hJ : μ (⋂ i ∈ J, f i) = ∏ i ∈ J.attach, μ (f i) := by
      simpa [Set.iInter_subtype, Finset.set_biInter_coe] using
        (h J).meas_iInter fun j : J ↦ hf j j.property
    calc
      μ (⋂ i ∈ J, f i) = ∏ i ∈ J.attach, μ (f i) := hJ
      _ = ∏ i ∈ J, μ (f i) := Finset.prod_attach J (fun i ↦ μ (f i))

/-- Theorem 2.13 (3): If each `π i ∪ {∅}` is intersection-stable, then independence of the event
classes is equivalent to independence of the generated σ-algebras `σ(π i)`. -/
-- Proof sketch: The reverse implication restricts independence of generated σ-algebras to the
-- generating classes. For the forward implication, use the intersection stability of
-- `insert ∅ (π i)` to pass from independent generating classes to independent generated measurable
-- spaces via the π-system extension theorem.
theorem iIndepSets_iff_iIndep_generateFrom_of_insert_empty_inter_closed
    (π : ι → Set (Set Ω)) (h_meas : ∀ i s, s ∈ π i → MeasurableSet s)
    (h_inter : ∀ i, ∀ s ∈ insert ∅ (π i), ∀ t ∈ insert ∅ (π i), s ∩ t ∈ insert ∅ (π i))
    (μ : Measure Ω := by volume_tac) :
    iIndepSets π μ ↔ iIndep (fun i ↦ MeasurableSpace.generateFrom (π i)) μ := by
  constructor
  · intro h
    have h_le : ∀ i, MeasurableSpace.generateFrom (π i) ≤ ‹MeasurableSpace Ω› := by
      intro i
      exact MeasurableSpace.generateFrom_le fun s hs ↦ h_meas i s hs
    have h_pi : ∀ i, IsPiSystem (π i) := by
      intro i s hs t ht hst
      have hmem : s ∩ t ∈ insert ∅ (π i) :=
        h_inter i s (Set.mem_insert_of_mem _ hs) t (Set.mem_insert_of_mem _ ht)
      rcases hmem with h_empty | hmem
      · exact False.elim (hst.ne_empty h_empty)
      · exact hmem
    exact h.iIndep h_le π h_pi fun _ ↦ rfl
  · intro h
    rw [iIndep_iff_iIndepSets] at h
    rw [iIndepSets_iff]
    intro S f hf
    exact h.meas_biInter S fun i hi ↦ MeasurableSpace.measurableSet_generateFrom (hf i hi)

/-- Theorem 2.13 (4): Grouping an independent family of event classes along pairwise disjoint
blocks of indices yields another independent family. -/
-- Proof sketch: To verify independence of the grouped family, choose one event class from each
-- block. Pairwise disjointness ensures that these choices come from distinct original indices, so
-- the defining finite product formula for `iIndepSets π μ` applies directly.
theorem iIndepSets_biUnion_of_pairwise_disjoint (π : ι → Set (Set Ω)) (I : κ → Set ι)
    (μ : Measure Ω := by volume_tac) (h_indep : iIndepSets π μ)
    (h_disjoint : Pairwise fun k l ↦ Disjoint (I k) (I l)) :
    iIndepSets (fun k ↦ ⋃ i ∈ I k, π i) μ := by
  rw [iIndepSets_iff]
  intro S B hB
  classical
  have h_exists : ∀ k : S, ∃ i, i ∈ I k ∧ B k ∈ π i := by
    intro k
    simpa [Set.mem_iUnion] using hB k k.property
  let g : S → ι := fun k ↦ Classical.choose (h_exists k)
  have hg_mem : ∀ k : S, g k ∈ I k := by
    intro k
    exact (Classical.choose_spec (h_exists k)).1
  have hBg : ∀ k : S, B k ∈ π (g k) := by
    intro k
    exact (Classical.choose_spec (h_exists k)).2
  have hg_injective : Function.Injective g := by
    intro a b hab
    by_cases h_eq : (a : κ) = b
    · exact Subtype.ext h_eq
    · exact False.elim <| Set.disjoint_left.mp (h_disjoint h_eq) (hg_mem a) (hab ▸ hg_mem b)
  have hS : iIndepSets (fun k : S ↦ π (g k)) μ := iIndepSets.precomp hg_injective h_indep
  have h_block : μ (⋂ i ∈ S, B i) = ∏ i ∈ S.attach, μ (B i) := by
    simpa [Set.iInter_subtype, Finset.set_biInter_coe] using hS.meas_iInter hBg
  calc
    μ (⋂ i ∈ S, B i) = ∏ i ∈ S.attach, μ (B i) := h_block
    _ = ∏ i ∈ S, μ (B i) := Finset.prod_attach S (fun i ↦ μ (B i))
