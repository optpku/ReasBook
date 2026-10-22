/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Theorem_2_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

/-- A finite subcollection of an indexed open cover is closed under nonempty finite intersections if
every nonempty finite subfamily has its intersection represented by another member of that same
finite subcollection. -/
def Finset.IsClosedUnderNonemptyFiniteIntersections
    (S : Finset ι) (O : ι → TopologicalSpace.Opens X) : Prop :=
  ∀ t : Finset ι, ∀ ht : t.Nonempty, (t : Set ι) ⊆ S → ∃ i ∈ S, t.inf' ht O = O i

/-- The source-facing owner for a nonempty finite subcollection of a cover that is itself closed
under nonempty finite intersections. -/
abbrev intersection_closed_subcover_index (O : ι → TopologicalSpace.Opens X) :=
  { S : Finset ι // S.Nonempty ∧ S.IsClosedUnderNonemptyFiniteIntersections O }

/-- Helper for ProofStep 2.7.9: the image of a continuous map from a compact parameter space lies
in a finite union of members of the ambient open cover. -/
theorem compact_image_subset_finite_union_of_cover
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (f : C(K, X)) :
    ∃ T : Finset ι, Set.range f ⊆ ⋃ i ∈ T, (O i : Set X) := by
  -- The compact image of `f` admits a finite subcover by members of the ambient open cover.
  have hcompact : IsCompact (Set.range f) := by
    simpa using isCompact_range f.continuous
  have hsU : Set.range f ⊆ ⋃ i, (O i : Set X) := by
    intro y hy
    rcases hy with ⟨k, rfl⟩
    obtain ⟨i, hi⟩ := hO.exists_mem (f k)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨T, hT⟩ :=
    hcompact.elim_finite_subcover (fun i ↦ (O i : Set X)) (fun i ↦ (O i).isOpen) hsU
  exact ⟨T, hT⟩

/-- Helper for ProofStep 2.7.9: a nonempty finite family of cover members can be enlarged to a
nonempty finite family that is internally closed under nonempty finite intersections. -/
theorem exists_nonempty_intersection_closed_finset_superset
    (O : ι → TopologicalSpace.Opens X)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (T : Finset ι) (hT : T.Nonempty) :
    ∃ S : intersection_closed_subcover_index O, T ⊆ (S : Finset ι) := by
  classical
  let nonemptySubsets : Finset { t : Finset ι // t ∈ T.powerset.filter Finset.Nonempty } :=
    (T.powerset.filter Finset.Nonempty).attach
  let representative :
      { t : Finset ι // t ∈ T.powerset.filter Finset.Nonempty } → ι := fun t ↦
    Classical.choose (hinter t.1 ((Finset.mem_filter.mp t.2).2))
  let closedCarrier : Finset ι := T ∪ nonemptySubsets.image representative
  have closedCarrier_nonempty : closedCarrier.Nonempty := by
    rcases hT with ⟨i, hi⟩
    exact ⟨i, Finset.mem_union.mpr (Or.inl hi)⟩
  have member_has_original_carrier :
      ∀ j ∈ closedCarrier, ∃ t : Finset ι,
        ∃ ht : t.Nonempty, (t : Set ι) ⊆ T ∧ t.inf' ht O = O j := by
    intro j hj
    rcases Finset.mem_union.mp hj with hjT | hjimage
    · have hj_mem_singleton : j ∈ ({j} : Finset ι) := by
        simp
      have hsingleton_nonempty : ({j} : Finset ι).Nonempty := ⟨j, hj_mem_singleton⟩
      refine ⟨{j}, hsingleton_nonempty, ?_, ?_⟩
      · intro k hk
        have hk' : k = j := by
          simpa using hk
        simpa [hk'] using hjT
      · exact Finset.inf'_singleton (f := O) (b := j)
    · rcases Finset.mem_image.mp hjimage with ⟨t, -, rfl⟩
      refine ⟨t.1, (Finset.mem_filter.mp t.2).2, ?_, ?_⟩
      · exact Finset.mem_powerset.mp (Finset.mem_filter.mp t.2).1
      · -- The chosen representative is defined to realize the finite intersection of `t`.
        simpa [representative] using
          (Classical.choose_spec (hinter t.1 ((Finset.mem_filter.mp t.2).2)))
  -- Replacing each index in a nonempty finite family by a chosen finite intersection of original
  -- cover members turns the whole finite infimum into the infimum over the union of those chosen
  -- carriers.
  have finite_inf_eq_biUnion_carrier_inf :
      ∀ (u : Finset ι) (hu : u.Nonempty) (carrier : ι → Finset ι)
        (hcarrier_nonempty : ∀ j ∈ u, (carrier j).Nonempty)
        (hcarrier_eq : ∀ j (hj : j ∈ u), O j = (carrier j).inf' (hcarrier_nonempty j hj) O)
        (hcarrier_union_nonempty : (u.biUnion carrier).Nonempty),
        u.inf' hu O =
          (u.biUnion carrier).inf' hcarrier_union_nonempty O := by
    intro u hu carrier hcarrier_nonempty hcarrier_eq hcarrier_union_nonempty
    ext x
    rw [Finset.inf'_eq_inf, Finset.inf'_eq_inf]
    rw [TopologicalSpace.Opens.coe_finset_inf, TopologicalSpace.Opens.coe_finset_inf]
    constructor
    · intro hx
      have hxu : ∀ j ∈ u, x ∈ O j := by
        simpa using hx
      have hxcarrier : ∀ j ∈ u, ∀ k ∈ carrier j, x ∈ O k := by
        intro j hj k hk
        have hxj : x ∈ O j := hxu j hj
        rw [hcarrier_eq j hj] at hxj
        rw [Finset.inf'_eq_inf] at hxj
        have hxj' : x ∈ (((carrier j).inf O : TopologicalSpace.Opens X) : Set X) := hxj
        rw [TopologicalSpace.Opens.coe_finset_inf] at hxj'
        have hforall : ∀ k ∈ carrier j, x ∈ O k := by
          simpa using hxj'
        exact hforall k hk
      simpa [Finset.mem_biUnion] using hxcarrier
    · intro hx
      have hxcarrier : ∀ j ∈ u, ∀ k ∈ carrier j, x ∈ O k := by
        simpa [Finset.mem_biUnion] using hx
      have hxu : ∀ j ∈ u, x ∈ O j := by
        intro j hj
        rw [hcarrier_eq j hj, Finset.inf'_eq_inf]
        have hforall : ∀ k ∈ carrier j, x ∈ O k := by
          intro k hk
          exact hxcarrier j hj k hk
        have hxj : x ∈ (((carrier j).inf O : TopologicalSpace.Opens X) : Set X) := by
          rw [TopologicalSpace.Opens.coe_finset_inf]
          simpa using hforall
        exact hxj
      simpa using hxu
  have closedCarrier_closed :
      closedCarrier.IsClosedUnderNonemptyFiniteIntersections O := by
    intro u hu hu_subset
    let carrier : ι → Finset ι := fun j ↦
      if hj : j ∈ closedCarrier then
        Classical.choose (member_has_original_carrier j hj)
      else
        ∅
    have carrier_nonempty : ∀ j ∈ u, (carrier j).Nonempty := by
      intro j hj
      have hjclosed : j ∈ closedCarrier := hu_subset hj
      simpa [carrier, hjclosed] using
        (Classical.choose (Classical.choose_spec (member_has_original_carrier j hjclosed)))
    have carrier_subset : ∀ j ∈ u, ((carrier j : Finset ι) : Set ι) ⊆ T := by
      intro j hj
      have hjclosed : j ∈ closedCarrier := hu_subset hj
      simpa [carrier, hjclosed] using
        (Classical.choose_spec (Classical.choose_spec (member_has_original_carrier j hjclosed))).1
    have carrier_eq : ∀ j (hj : j ∈ u),
        O j = (carrier j).inf' (carrier_nonempty j hj) O := by
      intro j hj
      have hjclosed : j ∈ closedCarrier := hu_subset hj
      symm
      simpa [carrier, hjclosed] using
        (Classical.choose_spec (Classical.choose_spec (member_has_original_carrier j hjclosed))).2
    have carrier_union_nonempty : (u.biUnion carrier).Nonempty := by
      rcases hu with ⟨j, hj⟩
      rcases carrier_nonempty j hj with ⟨k, hk⟩
      exact ⟨k, Finset.mem_biUnion.mpr ⟨j, hj, hk⟩⟩
    have carrier_union_mem :
        u.biUnion carrier ∈ T.powerset.filter Finset.Nonempty := by
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        intro k hk
        rcases Finset.mem_biUnion.mp hk with ⟨j, hj, hkj⟩
        exact carrier_subset j hj hkj
      · exact carrier_union_nonempty
    let carrierStage :
        { t : Finset ι // t ∈ T.powerset.filter Finset.Nonempty } :=
      ⟨u.biUnion carrier, carrier_union_mem⟩
    refine ⟨representative carrierStage, ?_, ?_⟩
    · have hcarrierStage_mem : carrierStage ∈ nonemptySubsets := by
        simp [nonemptySubsets]
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_image.mpr ⟨carrierStage, hcarrierStage_mem, rfl⟩
    · -- First collapse the finite infimum over `u` to the infimum over the original carriers, then
      -- use the chosen representative of that carrier union.
      calc
        u.inf' hu O
            = (u.biUnion carrier).inf' carrier_union_nonempty O := by
                exact
                  finite_inf_eq_biUnion_carrier_inf
                    u hu carrier carrier_nonempty carrier_eq carrier_union_nonempty
        _ = O (representative carrierStage) := by
              simpa [carrierStage, representative] using
                (Classical.choose_spec (hinter (u.biUnion carrier) carrier_union_nonempty))
  refine ⟨⟨closedCarrier, closedCarrier_nonempty, closedCarrier_closed⟩, ?_⟩
  -- The original finite family sits inside the enlarged intersection-closed carrier.
  intro i hi
  exact Finset.mem_union.mpr (Or.inl hi)

/-- Helper for ProofStep 2.7.9: any finite subcollection of a cover that is globally closed under
finite intersections can be enlarged to a finite subcollection whose restricted cover is itself
closed under nonempty finite intersections. -/
-- Proof sketch: split into the empty and nonempty cases. In the nonempty case, enlarge using the
-- stronger nonempty-stage lemma and then forget the subtype witness.
theorem exists_intersection_closed_finset_superset
    (O : ι → TopologicalSpace.Opens X)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (T : Finset ι) :
    ∃ S : Finset ι, T ⊆ S ∧
      S.IsClosedUnderNonemptyFiniteIntersections O := by
  classical
  by_cases hT : T.Nonempty
  · -- In the nonempty case, use the stronger stage construction and forget the nonempty witness.
    obtain ⟨S, hTS⟩ := exists_nonempty_intersection_closed_finset_superset O hinter T hT
    exact ⟨S.1, hTS, S.2.2⟩
  · -- In the empty case, the empty finite family is vacuously closed under nonempty intersections.
    refine ⟨∅, ?_, ?_⟩
    · intro i hi
      exact False.elim (hT ⟨i, hi⟩)
    · intro t ht ht_subset
      exfalso
      rcases ht with ⟨i, hi⟩
      have hi_empty : i ∈ (∅ : Finset ι) := ht_subset hi
      simp at hi_empty

/-- ProofStep 2.7.9 (1): every loop in the general cover case has image in a finite union `U_S`
coming from a nonempty finite subcover `S` of `O` that is itself closed under nonempty finite
intersections. -/
-- Proof sketch: the unit interval is compact, so the image of a loop is compact. Pull back the
-- open cover along the loop, extract a finite subcover of the image, and then enlarge the
-- resulting finite index set using `exists_intersection_closed_finset_superset`.
theorem loop_image_subset_finite_union_of_intersection_closed_subcover
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    {x : X} (γ : Path x x) :
    ∃ S : intersection_closed_subcover_index O,
      Set.range γ ⊆ ⋃ i ∈ (S : Finset ι), (O i : Set X) := by
  -- Compactness of the interval gives a finite cover of the loop image.
  obtain ⟨T, hT⟩ := compact_image_subset_finite_union_of_cover O hO γ.toContinuousMap
  have hT_nonempty : T.Nonempty := by
    -- The basepoint lies in the image, so one of the covering indices must appear in `T`.
    have hxrange : x ∈ Set.range γ := by
      refine ⟨0, ?_⟩
      simp
    have hxcover : x ∈ ⋃ i ∈ T, (O i : Set X) := hT hxrange
    rcases Set.mem_iUnion₂.mp hxcover with ⟨i, hiT, _⟩
    exact ⟨i, hiT⟩
  obtain ⟨S, hTS⟩ := exists_nonempty_intersection_closed_finset_superset O hinter T hT_nonempty
  refine ⟨S, ?_⟩
  -- Enlarge the finite image cover from `T` to the intersection-closed stage `S`.
  intro z hz
  have hzT : z ∈ ⋃ i ∈ T, (O i : Set X) := hT hz
  rcases Set.mem_iUnion₂.mp hzT with ⟨i, hiT, hzi⟩
  exact Set.mem_iUnion₂.mpr ⟨i, hTS hiT, hzi⟩

/-- ProofStep 2.7.9 (2): every homotopy between loops in the general cover case has image in a
finite union `U_S` coming from a nonempty finite subcover `S` of `O` that is itself closed under
nonempty finite intersections. -/
-- Proof sketch: the square `I × I` is compact, so the image of the homotopy is compact. Pull back
-- the open cover along the homotopy map, extract a finite subcover of its image, and then enlarge
-- the resulting finite index set using `exists_intersection_closed_finset_superset`.
theorem homotopy_image_subset_finite_union_of_intersection_closed_subcover
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁) :
    ∃ S : intersection_closed_subcover_index O,
      Set.range H ⊆ ⋃ i ∈ (S : Finset ι), (O i : Set X) := by
  -- Compactness of the square gives a finite cover of the homotopy image.
  obtain ⟨T, hT⟩ := compact_image_subset_finite_union_of_cover O hO H.toContinuousMap
  have hT_nonempty : T.Nonempty := by
    -- The constant basepoint value appears in the homotopy image, so `T` is nonempty.
    have hxrange : x ∈ Set.range H := by
      refine ⟨(0, 0), ?_⟩
      simp
    have hxcover : x ∈ ⋃ i ∈ T, (O i : Set X) := hT hxrange
    rcases Set.mem_iUnion₂.mp hxcover with ⟨i, hiT, _⟩
    exact ⟨i, hiT⟩
  obtain ⟨S, hTS⟩ := exists_nonempty_intersection_closed_finset_superset O hinter T hT_nonempty
  refine ⟨S, ?_⟩
  -- Enlarge the finite image cover from `T` to the intersection-closed stage `S`.
  intro z hz
  have hzT : z ∈ ⋃ i ∈ T, (O i : Set X) := hT hz
  rcases Set.mem_iUnion₂.mp hzT with ⟨i, hiT, hzi⟩
  exact Set.mem_iUnion₂.mpr ⟨i, hTS hiT, hzi⟩
