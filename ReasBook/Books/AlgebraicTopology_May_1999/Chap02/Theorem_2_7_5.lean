/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Theorem_2_7_1
import AlgebraicTopology_May_1999.Chap02.Lemma_2_4_2
import AlgebraicTopology_May_1999.Chap02.Proposition_2_5_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace.Opens
open unitInterval
open scoped FundamentalGroupoid

noncomputable section

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

/-- The inclusion between two members of the cover fixes the chosen common basepoint. -/
-- Proof sketch: a morphism in `TopologicalSpace.IsOpenCover.Index O` is an inclusion
-- `O i ⟶ O j`. Evaluating that inclusion at the subtype point `⟨x, hx i⟩` gives the same
-- underlying point `x`, so the source and target subtype points are equal by extensionality of
-- subtypes.
private theorem based_open_cover_map_basepoint
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {i j : TopologicalSpace.IsOpenCover.Index O} (f : i ⟶ j) :
    ((inducedFunctor O ⋙ toTopCat (TopCat.of X)).map f).hom ⟨x, hx i⟩ = ⟨x, hx j⟩ := by
  -- The cover morphism is the subtype inclusion, so it preserves the underlying point `x`.
  rfl

-- Internal bridge: regard each cover member, with the chosen common basepoint, as a based space.
private noncomputable abbrev based_open_cover_point
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (i : TopologicalSpace.IsOpenCover.Index O) :
    (inducedFunctor O ⋙ toTopCat (TopCat.of X)).obj i :=
  ⟨x, hx i⟩

private noncomputable abbrev based_open_cover_member
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (i : TopologicalSpace.IsOpenCover.Index O) :
    Under (⊤_ TopCat) :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (based_open_cover_point O x hx i)))

private theorem based_open_cover_member_hom_w
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {i j : TopologicalSpace.IsOpenCover.Index O} (f : i ⟶ j) :
    (based_open_cover_member O x hx i).hom ≫ ((inducedFunctor O ⋙ toTopCat (TopCat.of X)).map f) =
      (based_open_cover_member O x hx j).hom := by
  ext u
  change ((inducedFunctor O ⋙ toTopCat (TopCat.of X)).map f).hom
      (based_open_cover_point O x hx i) = based_open_cover_point O x hx j
  simpa [based_open_cover_point] using based_open_cover_map_basepoint O x hx f

private noncomputable def based_open_cover_diagram
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i) :
    TopologicalSpace.IsOpenCover.Index O ⥤ Under (⊤_ TopCat) where
  obj i := based_open_cover_member O x hx i
  map f :=
    Under.homMk ((inducedFunctor O ⋙ toTopCat (TopCat.of X)).map f)
      (based_open_cover_member_hom_w O x hx f)
  map_id i := by
    ext
    rfl
  map_comp {X} {Y} {Z} f g := by
    ext
    rfl

/-- The diagram sending each member of the cover to its fundamental group at the common basepoint
`x`. -/
abbrev fundamental_group_cover_diagram
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i) :
    TopologicalSpace.IsOpenCover.Index O ⥤ GrpCat :=
  based_open_cover_diagram O x hx ⋙ fundamentalGroupFunctor

/-- The inclusion of a cover member into `X` sends the chosen basepoint in that member to the
ambient basepoint `x`. -/
-- Proof sketch: the inclusion `O i ↪ X` is the subtype-valued map, so it sends the subtype point
-- `⟨x, hx i⟩` to the underlying point `x` by definition.
private theorem based_open_cover_cocone_app_basepoint
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (i : TopologicalSpace.IsOpenCover.Index O) :
    (inclusion' (O i)).hom ⟨x, hx i⟩ = x := by
  -- The ambient inclusion forgets the subtype proof and keeps the underlying point unchanged.
  rfl

/-- Helper for Theorem 2.7.5: a common-basepoint cover by path-connected members makes the ambient
space path connected. -/
private theorem ambient_path_connected_of_common_basepoint_cover
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i)) :
    PathConnectedSpace X := by
  refine PathConnectedSpace.mk ⟨x⟩ ?_
  intro y z
  obtain ⟨iy, hiy⟩ := hO.exists_mem y
  obtain ⟨iz, hiz⟩ := hO.exists_mem z
  let γy : Path x y := by
    letI := hpath iy
    exact (PathConnectedSpace.somePath ⟨x, hx iy⟩ ⟨y, hiy⟩).map continuous_subtype_val
  let γz : Path x z := by
    letI := hpath iz
    exact (PathConnectedSpace.somePath ⟨x, hx iz⟩ ⟨z, hiz⟩).map continuous_subtype_val
  -- Connect `y` to `z` by traveling from `y` back to the common basepoint and then out to `z`.
  exact ⟨γy.symm.trans γz⟩

-- Internal bridge: the ambient space `X` with the chosen basepoint `x`, viewed as a based space.
private noncomputable abbrev ambient_based_space (x : X) : Under (⊤_ TopCat) :=
  Under.mk (TopCat.terminalIsoPUnit.hom ≫ TopCat.ofHom (ContinuousMap.const PUnit x))

private noncomputable abbrev based_open_cover_inclusion
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (i : TopologicalSpace.IsOpenCover.Index O) :
    (based_open_cover_member O x hx i).right ⟶ (ambient_based_space x).right :=
  eqToHom
      (by
        rfl :
          (inducedFunctor O ⋙ toTopCat (TopCat.of X)).obj i =
            (toTopCat (TopCat.of X)).obj ((inducedFunctor O).obj i)) ≫
    inclusion' ((inducedFunctor O).obj i) ≫
      eqToHom (by rfl : TopCat.of X = (ambient_based_space x).right)

private theorem based_open_cover_cocone_app_w
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (i : TopologicalSpace.IsOpenCover.Index O) :
    (based_open_cover_member O x hx i).hom ≫ based_open_cover_inclusion O x hx i =
      (ambient_based_space x).hom := by
  ext u
  change (based_open_cover_inclusion O x hx i).hom (based_open_cover_point O x hx i) = x
  simpa [based_open_cover_inclusion, based_open_cover_point] using
    based_open_cover_cocone_app_basepoint O x hx i

private noncomputable def based_open_cover_cocone
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i) :
    Cocone (based_open_cover_diagram O x hx) where
  pt := ambient_based_space x
  ι :=
    { app := fun i ↦
        Under.homMk (based_open_cover_inclusion O x hx i) (based_open_cover_cocone_app_w O x hx i)
      naturality := fun i j f ↦ by
        ext z
        change (((inducedFunctor O ⋙ toTopCat (TopCat.of X)).map f).hom z).1 = z.1
        rfl }

/-- The canonical cocone from the fundamental groups of the cover members to `π₁(X,x)`. -/
abbrev fundamental_group_cover_cocone
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i) :
    Cocone (fundamental_group_cover_diagram O x hx) :=
  fundamentalGroupFunctor.mapCocone (based_open_cover_cocone O x hx)

/-- Helper for Theorem 2.7.5: a finite subcollection of the cover is internally closed under
nonempty finite intersections when every nonempty subfamily has its intersection represented by a
member of the same finite subcollection. -/
private def finite_subcover_closed_under_nonempty_finite_intersections
    (S : Finset ι)
    (O : ι → TopologicalSpace.Opens (TopCat.of X)) : Prop :=
  ∀ t : Finset ι, ∀ ht : t.Nonempty, (t : Set ι) ⊆ S →
    ∃ i ∈ S, t.inf' ht O = O i

/-- Helper for Theorem 2.7.5: the source-facing owner for a nonempty finite subcollection that is
itself closed under nonempty finite intersections. -/
private abbrev intersection_closed_subcover_index
    (O : ι → TopologicalSpace.Opens (TopCat.of X)) :=
  { S : Finset ι // S.Nonempty ∧ finite_subcover_closed_under_nonempty_finite_intersections S O }

/-- Helper for Theorem 2.7.5: the open subset obtained by taking the union of the members of a
finite intersection-closed subcollection. -/
private abbrev finite_intersection_closed_union
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O) : TopologicalSpace.Opens (TopCat.of X) :=
  ⨆ i : (S : Finset ι), O i

local notation "U[" O ", " S "]" => finite_intersection_closed_union O S

/-- Helper for Theorem 2.7.5: enlarging a finite intersection-closed subcollection enlarges the
corresponding finite union of open sets. -/
private theorem finite_intersection_closed_union_mono
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    {S T : intersection_closed_subcover_index O} (hST : S ≤ T) :
    U[O, S] ≤ U[O, T] := by
  -- Each summand of the smaller supremum also appears in the larger supremum.
  rw [finite_intersection_closed_union, finite_intersection_closed_union]
  refine iSup_le ?_
  intro i
  exact le_iSup (fun j : (T : Finset ι) ↦ O j) ⟨i, hST i.2⟩

/-- Helper for Theorem 2.7.5: the common basepoint belongs to every finite union attached to a
nonempty finite intersection-closed subcollection. -/
private theorem basepoint_mem_finite_intersection_closed_union
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O) :
    x ∈ U[O, S] := by
  -- Choose any index from the nonempty finite subcollection and use that summand of the union.
  rcases S.2.1 with ⟨i, hi⟩
  have hxS : x ∈ ⋃ j : (S : Finset ι), (O j : Set X) := by
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx i⟩
  simpa [finite_intersection_closed_union] using hxS

/-- Helper for Theorem 2.7.5: if a finite family of cover members is nonempty, then it can be
enlarged to a nonempty finite family that is internally closed under nonempty finite intersections.

The extra nonemptiness hypothesis is necessary here: an empty index type would make the raw
nonempty-stage statement false for `T = ∅`. -/
private theorem exists_intersection_closed_finset_superset
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
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
    · refine ⟨{j}, by simp, ?_, ?_⟩
      · intro k hk
        have hk' : k = j := by
          simpa using hk
        simpa [hk'] using hjT
      · simpa using (Finset.inf'_singleton (f := O) (b := j))
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
        (hcarrier_eq : ∀ j (hj : j ∈ u), O j = (carrier j).inf' (hcarrier_nonempty j hj) O),
        u.inf' hu O =
          (u.biUnion carrier).inf'
            (by
              rcases hu with ⟨j, hj⟩
              rcases hcarrier_nonempty j hj with ⟨k, hk⟩
              exact ⟨k, Finset.mem_biUnion.mpr ⟨j, hj, hk⟩⟩) O := by
    intro u hu carrier hcarrier_nonempty hcarrier_eq
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
        have hxj' : x ∈ (((carrier j).inf O : TopologicalSpace.Opens (TopCat.of X)) : Set X) := hxj
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
        have hxj : x ∈ (((carrier j).inf O : TopologicalSpace.Opens (TopCat.of X)) : Set X) := by
          rw [TopologicalSpace.Opens.coe_finset_inf]
          simpa using hforall
        exact hxj
      simpa using hxu
  have closedCarrier_closed :
      finite_subcover_closed_under_nonempty_finite_intersections closedCarrier O := by
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
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_image.mpr ⟨carrierStage, by simp [nonemptySubsets, representative]⟩
    · -- First collapse the finite infimum over `u` to the infimum over the original carriers, then
      -- use the chosen representative of that carrier union.
      calc
        u.inf' hu O
            = (u.biUnion carrier).inf' carrier_union_nonempty O := by
                exact finite_inf_eq_biUnion_carrier_inf u hu carrier carrier_nonempty carrier_eq
        _ = O (representative carrierStage) := by
              simpa [carrierStage, representative] using
                (Classical.choose_spec (hinter (u.biUnion carrier) carrier_union_nonempty))
  refine ⟨⟨closedCarrier, closedCarrier_nonempty, closedCarrier_closed⟩, ?_⟩
  intro i hi
  exact Finset.mem_union.mpr (Or.inl hi)

/-- Helper for Theorem 2.7.5: on a finite intersection-closed stage, one can choose for each
point a path from the common basepoint that stays inside every cover member containing that point.
-/
private theorem exists_cover_compatible_basepoint_paths
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    [Finite ι]
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O) :
    ∃ γ : ∀ y : X, Path x y,
      ∀ (i : ι) (y : X), y ∈ O i → ∀ t : I, γ y t ∈ O i := by
  classical
  letI := Fintype.ofFinite ι
  let coverAt : X → Finset ι := fun y ↦ Finset.univ.filter fun i ↦ y ∈ O i
  have coverAt_nonempty : ∀ y, (coverAt y).Nonempty := fun y ↦ by
    -- The ambient cover condition ensures that every point belongs to at least one cover member.
    obtain ⟨i, hi⟩ := hO.exists_mem y
    exact ⟨i, by simp [coverAt, hi]⟩
  let center : X → ι := fun y ↦ Classical.choose (hinter (coverAt y) (coverAt_nonempty y))
  have center_eq : ∀ y, (coverAt y).inf' (coverAt_nonempty y) O = O (center y) := fun y ↦
    Classical.choose_spec (hinter (coverAt y) (coverAt_nonempty y))
  have center_mem : ∀ y, y ∈ O (center y) := fun y ↦ by
    -- The point lies in the intersection of all cover members that contain it.
    have hy : y ∈ (coverAt y).inf' (coverAt_nonempty y) O := by
      rw [Finset.inf'_eq_inf]
      change y ∈ (((coverAt y).inf O : TopologicalSpace.Opens (TopCat.of X)) : Set X)
      rw [TopologicalSpace.Opens.coe_finset_inf]
      simp [coverAt]
    simpa [center_eq y] using hy
  have center_le : ∀ {i y}, y ∈ O i → O (center y) ≤ O i := by
    intro i y hyi
    -- Any chosen center is an intersection of a family that includes the requested cover member.
    have hi : i ∈ coverAt y := by
      simp [coverAt, hyi]
    have hle : (coverAt y).inf' (coverAt_nonempty y) O ≤ O i := by
      rw [Finset.inf'_eq_inf]
      exact Finset.inf_le hi
    simpa [center_eq y] using hle
  let γ : ∀ y : X, Path x y := fun y ↦
    letI := hpath (center y)
    (PathConnectedSpace.somePath ⟨x, hx (center y)⟩ ⟨y, center_mem y⟩).map continuous_subtype_val
  refine ⟨γ, ?_⟩
  intro i y hyi t
  -- The chosen path lies in the distinguished center open, hence in every containing cover
  -- member.
  have hγ : γ y t ∈ O (center y) := by
    simp [γ]
  exact center_le hyi hγ

/-- Helper for Theorem 2.7.5: the image of a continuous map from a compact parameter space lies in
a finite union of cover members. -/
private theorem compact_image_subset_finite_union_of_cover
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
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

/-- Helper for Theorem 2.7.5: every path in `X` is contained in a finite union of members of the
cover. -/
private theorem path_image_subset_finite_union_of_cover
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    ∃ T : Finset ι, Set.range γ ⊆ ⋃ i ∈ T, (O i : Set X) := by
  -- Specialize the compact-image lemma to the unit interval parameterizing the path.
  simpa using compact_image_subset_finite_union_of_cover O hO γ.toContinuousMap

/-- Helper for Theorem 2.7.5: every path homotopy between loops is contained in a finite union of
members of the cover. -/
private theorem homotopy_image_subset_finite_union_of_cover
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁) :
    ∃ T : Finset ι, Set.range H ⊆ ⋃ i ∈ T, (O i : Set X) := by
  -- The square `I × I` is compact, so the same finite-subcover reduction applies to homotopies.
  simpa using compact_image_subset_finite_union_of_cover O hO H.toContinuousMap

/-- Helper for Theorem 2.7.5: every path in `X` is contained in one intersection-closed finite
stage `U[O,S]`. -/
private theorem path_image_subset_finite_intersection_closed_union
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    {x y : X} (γ : Path x y) :
    ∃ S : intersection_closed_subcover_index O, Set.range γ ⊆ (U[O, S] : Set X) := by
  obtain ⟨T, hT⟩ := path_image_subset_finite_union_of_cover O hO γ
  have hT_nonempty : T.Nonempty := by
    have hxrange : x ∈ Set.range γ := ⟨0, by simp⟩
    have hxcover := hT hxrange
    rcases Set.mem_iUnion₂.mp hxcover with ⟨i, hiT, _⟩
    exact ⟨i, hiT⟩
  obtain ⟨S, hTS⟩ := exists_intersection_closed_finset_superset O hinter T hT_nonempty
  refine ⟨S, ?_⟩
  intro z hz
  have hzT : z ∈ ⋃ i ∈ T, (O i : Set X) := hT hz
  rcases Set.mem_iUnion₂.mp hzT with ⟨i, hiT, hzi⟩
  have hzS : z ∈ ⋃ j : (S : Finset ι), (O j : Set X) := by
    exact Set.mem_iUnion.mpr ⟨⟨i, hTS hiT⟩, hzi⟩
  simpa [finite_intersection_closed_union] using hzS

/-- Helper for Theorem 2.7.5: every loop homotopy in `X` is contained in one intersection-closed
finite stage `U[O,S]`. -/
private theorem homotopy_image_subset_finite_intersection_closed_union
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁) :
    ∃ S : intersection_closed_subcover_index O, Set.range H ⊆ (U[O, S] : Set X) := by
  obtain ⟨T, hT⟩ := homotopy_image_subset_finite_union_of_cover O hO H
  have hT_nonempty : T.Nonempty := by
    have hxrange : x ∈ Set.range H := ⟨(0, 0), by simp⟩
    have hxcover := hT hxrange
    rcases Set.mem_iUnion₂.mp hxcover with ⟨i, hiT, _⟩
    exact ⟨i, hiT⟩
  obtain ⟨S, hTS⟩ := exists_intersection_closed_finset_superset O hinter T hT_nonempty
  refine ⟨S, ?_⟩
  intro z hz
  have hzT : z ∈ ⋃ i ∈ T, (O i : Set X) := hT hz
  rcases Set.mem_iUnion₂.mp hzT with ⟨i, hiT, hzi⟩
  have hzS : z ∈ ⋃ j : (S : Finset ι), (O j : Set X) := by
    exact Set.mem_iUnion.mpr ⟨⟨i, hTS hiT⟩, hzi⟩
  simpa [finite_intersection_closed_union] using hzS

/-- Helper for Theorem 2.7.5: each cover member contributes the canonical inclusion of its
fundamental group into its fundamental groupoid, viewed as a one-object skeleton. -/
private noncomputable def cover_member_single_obj_inclusion
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (i : TopologicalSpace.IsOpenCover.Index O) :
    CategoryTheory.SingleObj (FundamentalGroup (O i) ⟨x, hx i⟩) ⥤
      (fundamental_groupoid_cover_diagram O).obj i :=
  CategoryTheory.SingleObj.functor (MonoidHom.id (FundamentalGroup (O i) ⟨x, hx i⟩))

/-- Helper for Theorem 2.7.5: the ambient fundamental group includes into the ambient fundamental
groupoid as the one-object subgroupoid at the chosen basepoint. -/
private noncomputable def ambient_single_obj_inclusion (x : X) :
    CategoryTheory.SingleObj (FundamentalGroup X x) ⥤ FundamentalGroupoid X :=
  CategoryTheory.SingleObj.functor (MonoidHom.id (FundamentalGroup X x))

/-- Helper for Theorem 2.7.5: the strict natural direction from the group-level cover diagram to
the groupoid cover diagram is given by the canonical one-object inclusions. -/
private theorem cover_member_single_obj_naturality
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {i j : TopologicalSpace.IsOpenCover.Index O} (f : i ⟶ j) :
    (CategoryTheory.SingleObj.mapHom _ _ ((fundamental_group_cover_diagram O x hx).map f).hom) ⋙
        cover_member_single_obj_inclusion O x hx j =
      cover_member_single_obj_inclusion O x hx i ⋙
        ((fundamental_groupoid_cover_diagram O).map f :
          FundamentalGroupoid (O i) ⥤ FundamentalGroupoid (O j)) := by
  -- The object map is forced, and the morphism map is the same induced inclusion on loop classes.
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y g
  cases X
  cases Y
  induction g using Quotient.inductionOn with
  | h p =>
      rfl

/-- Helper for Theorem 2.7.5: the canonical leg `π₁(O i, x) → π₁(X, x)` becomes the corresponding
groupoid inclusion `Π(O i) → Π(X)` after passing to one-object groupoids. -/
private theorem fundamental_group_cover_cocone_leg_naturality
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (i : TopologicalSpace.IsOpenCover.Index O) :
    (CategoryTheory.SingleObj.mapHom _ _ ((fundamental_group_cover_cocone O x hx).ι.app i).hom) ⋙
        ambient_single_obj_inclusion x =
      cover_member_single_obj_inclusion O x hx i ⋙
        ((fundamental_groupoid_cover_cocone O).ι.app i :
          FundamentalGroupoid (O i) ⥤ FundamentalGroupoid X) := by
  -- Again the object map is forced, and the loop map is induced by the same ambient inclusion.
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y g
  cases X
  cases Y
  induction g using Quotient.inductionOn with
  | h p =>
      rfl

/-- Helper for Theorem 2.7.5: membership in the finite infimum of open subsets is equivalent to
membership in each constituent open. -/
private theorem mem_finset_inf_opens
    {α : Type*} [TopologicalSpace α] {κ : Type*}
    (s : Finset κ) (U : κ → TopologicalSpace.Opens (TopCat.of α)) (x : α) :
    x ∈ s.inf U ↔ ∀ i ∈ s, x ∈ U i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty infimum is `⊤`, so every point belongs to it.
      simp
  | @insert i s hi hs =>
      -- Expand one stage of the finite infimum and use the induction hypothesis on the remainder.
      simp [Finset.inf_insert, hs]

/-- Helper for Theorem 2.7.5: for a finite intersection-closed stage `S`, the literal restricted
cover of the stage space `U[O,S]` is obtained by viewing each `O i` with `i ∈ S` as an open subset
of the subtype `U[O,S]`. -/
private abbrev stage_cover
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O) :
    ↥(S : Finset ι) → TopologicalSpace.Opens (TopCat.of U[O, S]) := fun i ↦
  ⟨{ y | y.1 ∈ O i }, (O i).isOpen.preimage continuous_subtype_val⟩

/-- Helper for Theorem 2.7.5: the literal restricted cover of a finite stage is still closed
under nonempty finite intersections. -/
private theorem stage_cover_closed_under_nonempty_finite_intersections
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O) :
    TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections (stage_cover O S) := by
  classical
  intro t ht
  let tAmbient : Finset ι := t.image fun i : ↥(S : Finset ι) ↦ (i : ι)
  have htAmbient : tAmbient.Nonempty := by
    rcases ht with ⟨i, hi⟩
    exact ⟨i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  have htAmbient_subset : (tAmbient : Set ι) ⊆ (S : Finset ι) := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, -, rfl⟩
    exact j.2
  obtain ⟨i, hiS, hti⟩ := S.2.2 tAmbient htAmbient htAmbient_subset
  refine ⟨⟨i, hiS⟩, ?_⟩
  ext y
  constructor
  · intro hy
    -- First unpack membership in the stage-level finite intersection into membership in every
    -- chosen stage member.
    have hyStage : ∀ j ∈ t, y ∈ stage_cover O S j := by
      rw [Finset.inf'_eq_inf] at hy
      exact (mem_finset_inf_opens t (stage_cover O S) y).mp hy
    -- Then pass to the corresponding ambient finite intersection indexed by the underlying
    -- members of `S`.
    have hyAmbient : y.1 ∈ tAmbient.inf' htAmbient O := by
      rw [Finset.inf'_eq_inf]
      exact (mem_finset_inf_opens tAmbient O y.1).mpr fun j hj ↦ by
        rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
        simpa [stage_cover] using hyStage k hk
    -- The ambient stage data identifies that finite intersection with one literal stage member.
    change y.1 ∈ O i
    simpa [hti] using hyAmbient
  · intro hy
    change y.1 ∈ O i at hy
    -- Rewrite membership in the representing stage member back to membership in the ambient
    -- finite intersection.
    have hyAmbient : y.1 ∈ tAmbient.inf' htAmbient O := by
      simpa [hti] using hy
    rw [Finset.inf'_eq_inf] at hyAmbient
    rw [Finset.inf'_eq_inf]
    exact (mem_finset_inf_opens t (stage_cover O S) y).mpr fun j hj ↦ by
      have hjAmbient : (j : ι) ∈ tAmbient := Finset.mem_image.mpr ⟨j, hj, rfl⟩
      exact
        (show y ∈ stage_cover O S j from by
          simpa [stage_cover] using
            (mem_finset_inf_opens tAmbient O y.1).mp hyAmbient j hjAmbient)

/-- Helper for Theorem 2.7.5: the common basepoint of `X` determines a basepoint in every member
of the literal restricted stage cover. -/
private theorem stage_cover_basepoint_mem
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (i : ↥(S : Finset ι)) :
    (⟨x, basepoint_mem_finite_intersection_closed_union O x hx S⟩ : U[O, S]) ∈
      stage_cover O S i := by
  -- The stage member is defined by membership in the original open `O i`.
  exact hx i

/-- Helper for Theorem 2.7.5: each literal stage member is canonically homeomorphic to the
corresponding ambient cover member. -/
private noncomputable def stage_cover_member_homeomorph
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O)
    (i : ↥(S : Finset ι)) :
    (stage_cover O S i : Set U[O, S]) ≃ₜ (O i : Set X) where
  toFun y := ⟨y.1.1, y.2⟩
  invFun y := by
    -- The ambient point already lies in the finite union because `O i` is one summand.
    refine ⟨⟨y.1, ?_⟩, y.2⟩
    have hyS : y.1 ∈ ⋃ j : (S : Finset ι), (O j : Set X) := by
      exact Set.mem_iUnion.mpr ⟨i, y.2⟩
    simpa [finite_intersection_closed_union] using hyS
  left_inv y := by
    -- Both sides are the same nested subtype point with identical ambient coordinate.
    ext
    rfl
  right_inv y := by
    -- Forgetting the stage-union proof returns the original ambient subtype point.
    ext
    rfl
  continuous_toFun := by
    -- The forward map just forgets the stage-union proof.
    fun_prop
  continuous_invFun := by
    -- The inverse reinstalls the ambient-union proof, then remembers membership in `O i`.
    fun_prop

/-- Helper for Theorem 2.7.5: the stage-member homeomorphism sends the stage basepoint to the
ambient basepoint in the corresponding cover member. -/
private theorem stage_cover_member_homeomorph_basepoint
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (i : ↥(S : Finset ι)) :
    stage_cover_member_homeomorph O S i
        ⟨⟨x, basepoint_mem_finite_intersection_closed_union O x hx S⟩,
          stage_cover_basepoint_mem O x hx S i⟩ =
      ⟨x, hx i⟩ := by
  -- The homeomorphism is the identity on the underlying point.
  rfl

/-- Helper for Theorem 2.7.5: the literal restricted stage family still covers the finite stage
space `U[O,S]`. -/
private theorem stage_cover_isOpenCover
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O) :
    TopologicalSpace.IsOpenCover (stage_cover O S) := by
  apply TopologicalSpace.IsOpenCover.mk
  ext y
  constructor
  · intro _
    trivial
  · intro _
    -- Unpack membership in the finite union and choose the corresponding stage index.
    have hyS : y.1 ∈ ⋃ j : (S : Finset ι), (O j : Set X) := by
      simpa [finite_intersection_closed_union] using y.2
    rcases Set.mem_iUnion.mp hyS with ⟨i, hyi⟩
    have hyi' : y ∈ stage_cover O S i := hyi
    exact (le_iSup (fun j : (S : Finset ι) ↦ stage_cover O S j) i) hyi'

/-- Helper for Theorem 2.7.5: path connectedness of ambient cover members transfers to the literal
members of every finite stage cover. -/
private theorem stage_cover_path_connected
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O)
    (hpath : ∀ i, PathConnectedSpace (O i)) :
    ∀ i : ↥(S : Finset ι), PathConnectedSpace (stage_cover O S i) := by
  intro i
  -- Transport path connectedness across the canonical stage-member homeomorphism.
  let e := stage_cover_member_homeomorph O S i
  letI : PathConnectedSpace (O i) := hpath i
  exact e.symm.surjective.pathConnectedSpace e.symm.continuous_toFun

/-- Helper for Theorem 2.7.5: the compatible-basepoint-path construction from the finite case
specializes to every literal restricted stage cover. -/
private theorem exists_stage_cover_compatible_basepoint_paths
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (hpath : ∀ i, PathConnectedSpace (O i)) :
    ∃ γ : ∀ y : U[O, S], Path ⟨x, basepoint_mem_finite_intersection_closed_union O x hx S⟩ y,
      ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
        γ y t ∈ stage_cover O S i := by
  let xS : U[O, S] := ⟨x, basepoint_mem_finite_intersection_closed_union O x hx S⟩
  -- The literal stage cover inherits the cover, path-connectedness, and finite-intersection
  -- hypotheses needed by the compatible-path construction.
  simpa [xS] using
    (exists_cover_compatible_basepoint_paths
      (stage_cover O S)
      (stage_cover_isOpenCover O S)
      xS
      (stage_cover_basepoint_mem O x hx S)
      (stage_cover_path_connected O S hpath)
      (stage_cover_closed_under_nonempty_finite_intersections O S))

/-- Helper for Theorem 2.7.5: the common basepoint of `X` determines the canonical basepoint of
the finite stage `U[O,S]`. -/
private noncomputable abbrev stage_union_basepoint
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O) :
    U[O, S] :=
  ⟨x, basepoint_mem_finite_intersection_closed_union O x hx S⟩

/-- Helper for Theorem 2.7.5: enlarging a finite stage preserves the chosen common basepoint. -/
private theorem stage_union_inclusion_basepoint
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T) :
    (((toTopCat (TopCat.of X)).map
        (homOfLE (finite_intersection_closed_union_mono O hST))).hom)
        (stage_union_basepoint O x hx S) =
      stage_union_basepoint O x hx T := by
  -- Both subtype points have the same ambient coordinate `x`; only the stage-membership proof
  -- changes under the monotonicity inclusion.
  apply Subtype.ext
  rfl

/-- Helper for Theorem 2.7.5: enlarging a finite stage induces the canonical map on fundamental
groups between the corresponding finite unions. -/
private noncomputable abbrev stage_union_inclusion_hom
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T) :
    GrpCat.of (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) ⟶
      GrpCat.of (FundamentalGroup U[O, T] (stage_union_basepoint O x hx T)) :=
  GrpCat.ofHom <|
    FundamentalGroup.mapOfEq
      (((toTopCat (TopCat.of X)).map
          (homOfLE (finite_intersection_closed_union_mono O hST))).hom)
      (stage_union_inclusion_basepoint O x hx hST)

/-- Helper for Theorem 2.7.5: the common basepoint of `X` also gives the canonical basepoint of
each literal member of a finite stage cover. -/
private noncomputable abbrev stage_cover_member_basepoint
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (i : ↥(S : Finset ι)) :
    stage_cover O S i :=
  ⟨stage_union_basepoint O x hx S, stage_cover_basepoint_mem O x hx S i⟩

/-- Helper for Theorem 2.7.5: the canonical homeomorphism from a literal stage member to the
corresponding ambient cover member is an isomorphism of the associated based spaces. -/
private noncomputable abbrev stage_cover_to_ambient_obj
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    TopologicalSpace.IsOpenCover.Index O :=
  (((show ↥(S : Finset ι) from i) : ι) : TopologicalSpace.IsOpenCover.Index O)

/-- Helper for Theorem 2.7.5: the canonical homeomorphism from a literal stage member to the
corresponding ambient cover member is an isomorphism of the associated based spaces. -/
private noncomputable def stage_cover_member_based_iso
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (i : ↥(S : Finset ι)) :
    based_open_cover_member
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)
        i ≅
      based_open_cover_member O x hx (stage_cover_to_ambient_obj O S i) := by
  refine CategoryTheory.Under.isoMk
      (TopCat.isoOfHomeo (stage_cover_member_homeomorph O S i)) ?_
  ext u
  change
    stage_cover_member_homeomorph O S i
        (based_open_cover_point
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
          (stage_cover_basepoint_mem O x hx S)
          i) =
      based_open_cover_point O x hx (i : ι)
  -- The based-space comparison uses the chosen common basepoint on both sides.
  simpa [based_open_cover_point, stage_union_basepoint] using
    stage_cover_member_homeomorph_basepoint O x hx S i

/-- Helper for Theorem 2.7.5: passing the based-space isomorphism for a literal stage member
through `fundamentalGroupFunctor` yields the corresponding group isomorphism
`π₁(stage_cover O S i, x_S) ≅ π₁(O i, x)`. -/
private noncomputable abbrev stage_member_fundamental_group_iso
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (i : ↥(S : Finset ι)) :
    (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)).obj i ≅
      (fundamental_group_cover_diagram O x hx).obj (stage_cover_to_ambient_obj O S i) :=
  fundamentalGroupFunctor.mapIso (stage_cover_member_based_iso O x hx S i)

/-- Helper for Theorem 2.7.5: a literal-stage inclusion determines the corresponding ambient cover
inclusion between the same two indexed opens. -/
private noncomputable abbrev stage_cover_to_ambient_hom
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O)
    {i j : TopologicalSpace.IsOpenCover.Index (stage_cover O S)} (f : i ⟶ j) :
    stage_cover_to_ambient_obj O S i ⟶ stage_cover_to_ambient_obj O S j :=
  InducedCategory.homMk <|
    homOfLE <| by
      intro y hy
      let yS : U[O, S] := by
        refine ⟨y, ?_⟩
        have hyS : y ∈ ⋃ k : (S : Finset ι), (O k : Set X) := by
          exact Set.mem_iUnion.mpr ⟨(i : ↥(S : Finset ι)), hy⟩
        simpa [finite_intersection_closed_union] using hyS
      let yi : stage_cover O S i := by
        exact ⟨yS, by simpa [stage_cover, yS] using hy⟩
      have hle : stage_cover O S i ≤ stage_cover O S j := leOfHom f.hom
      -- The literal-stage morphism is already an inclusion of the same underlying ambient point.
      simpa [stage_cover, yS, yi] using hle yi.2

/-- Helper for Theorem 2.7.5: the based-space isomorphisms from literal stage members to ambient
cover members commute strictly with literal-stage inclusions. -/
private theorem stage_cover_member_based_iso_naturality
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    {i j : TopologicalSpace.IsOpenCover.Index (stage_cover O S)} (f : i ⟶ j) :
    (based_open_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)).map f ≫
      (stage_cover_member_based_iso O x hx S j).hom =
    (stage_cover_member_based_iso O x hx S i).hom ≫
      (based_open_cover_diagram O x hx).map (stage_cover_to_ambient_hom O S f) := by
  -- Both composites are the same subtype inclusion from the literal stage member into `O j`.
  rfl

/-- Helper for Theorem 2.7.5: the stage-member fundamental-group isomorphisms commute strictly
with the literal-stage inclusions and their ambient counterparts. -/
private theorem stage_member_fundamental_group_iso_naturality
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    {i j : TopologicalSpace.IsOpenCover.Index (stage_cover O S)} (f : i ⟶ j) :
    (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)).map f ≫
      (stage_member_fundamental_group_iso O x hx S j).hom =
    (stage_member_fundamental_group_iso O x hx S i).hom ≫
      (fundamental_group_cover_diagram O x hx).map (stage_cover_to_ambient_hom O S f) := by
  -- Push the based-space naturality square through `fundamentalGroupFunctor`.
  have hmap :=
    congrArg fundamentalGroupFunctor.map
      (stage_cover_member_based_iso_naturality O x hx S f)
  have hsplit_left :
      fundamentalGroupFunctor.map
          ((based_open_cover_diagram
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).map f ≫
            (stage_cover_member_based_iso O x hx S j).hom) =
        fundamentalGroupFunctor.map
          ((based_open_cover_diagram
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).map f) ≫
          fundamentalGroupFunctor.map (stage_cover_member_based_iso O x hx S j).hom := by
    exact Functor.map_comp _ _ _
  have hsplit :
      fundamentalGroupFunctor.map
          ((stage_cover_member_based_iso O x hx S i).hom ≫
            (based_open_cover_diagram O x hx).map (stage_cover_to_ambient_hom O S f)) =
        fundamentalGroupFunctor.map (stage_cover_member_based_iso O x hx S i).hom ≫
          fundamentalGroupFunctor.map
            ((based_open_cover_diagram O x hx).map (stage_cover_to_ambient_hom O S f)) := by
    exact Functor.map_comp _ _ _
  have hmap' :
      fundamentalGroupFunctor.map
          ((based_open_cover_diagram
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).map f) ≫
        fundamentalGroupFunctor.map (stage_cover_member_based_iso O x hx S j).hom =
      fundamentalGroupFunctor.map (stage_cover_member_based_iso O x hx S i).hom ≫
      fundamentalGroupFunctor.map
          ((based_open_cover_diagram O x hx).map (stage_cover_to_ambient_hom O S f)) :=
    hsplit_left.symm.trans (hmap.trans hsplit)
  simpa [fundamental_group_cover_diagram, stage_member_fundamental_group_iso] using hmap'

/-- Helper for Theorem 2.7.5: an ambient cocone over the group diagram restricts to a strict
cocone over each literal finite stage cover via the stage-member fundamental-group isomorphisms. -/
private noncomputable def stage_group_cocone_of_ambient_cocone
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (C : Cocone (fundamental_group_cover_diagram O x hx))
    (S : intersection_closed_subcover_index O) :
    Cocone
      (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)) where
  pt := C.pt
  ι :=
    { app := fun i ↦
        (stage_member_fundamental_group_iso O x hx S i).hom ≫
          C.ι.app (stage_cover_to_ambient_obj O S i)
      naturality := fun i j f ↦ by
        -- The constant cocone target contributes only an identity morphism.
        simp only [Functor.const_obj_map]
        calc
          (fundamental_group_cover_diagram
                (stage_cover O S)
                (stage_union_basepoint O x hx S)
                (stage_cover_basepoint_mem O x hx S)).map f ≫
              ((stage_member_fundamental_group_iso O x hx S j).hom ≫
                C.ι.app (stage_cover_to_ambient_obj O S j))
              =
            ((fundamental_group_cover_diagram
                  (stage_cover O S)
                  (stage_union_basepoint O x hx S)
                  (stage_cover_basepoint_mem O x hx S)).map f ≫
                (stage_member_fundamental_group_iso O x hx S j).hom) ≫
              C.ι.app (stage_cover_to_ambient_obj O S j) := by
                simp [Category.assoc]
          _ =
            ((stage_member_fundamental_group_iso O x hx S i).hom ≫
                (fundamental_group_cover_diagram O x hx).map
                  (stage_cover_to_ambient_hom O S f)) ≫
              C.ι.app (stage_cover_to_ambient_obj O S j) := by
                rw [stage_member_fundamental_group_iso_naturality O x hx S f]
          _ =
            (stage_member_fundamental_group_iso O x hx S i).hom ≫
              ((fundamental_group_cover_diagram O x hx).map
                  (stage_cover_to_ambient_hom O S f) ≫
                C.ι.app (stage_cover_to_ambient_obj O S j)) := by
                  simp [Category.assoc]
          _ =
            (stage_member_fundamental_group_iso O x hx S i).hom ≫
              C.ι.app (stage_cover_to_ambient_obj O S i) := by
                simpa [Category.assoc] using
                  congrArg ((stage_member_fundamental_group_iso O x hx S i).hom ≫ ·)
                    (C.w (stage_cover_to_ambient_hom O S f)) }

/-- Helper for Theorem 2.7.5: the stage-compatible basepoint-path family can be normalized so that
the chosen path from the stage basepoint to itself is literally the constant path. -/
private theorem exists_normalized_stage_cover_compatible_basepoint_paths
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (hpath : ∀ i, PathConnectedSpace (O i)) :
    ∃ γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y,
      γ (stage_union_basepoint O x hx S) = Path.refl (stage_union_basepoint O x hx S) ∧
      ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
        γ y t ∈ stage_cover O S i := by
  classical
  let xS := stage_union_basepoint O x hx S
  obtain ⟨γ, hγ⟩ := exists_stage_cover_compatible_basepoint_paths O x hx S hpath
  let γ' : ∀ y : U[O, S], Path xS y := fun y ↦
    if hy : y = xS then
      (Path.refl xS).cast rfl hy
    else
      γ y
  refine ⟨γ', ?_, ?_⟩
  · -- Route correction: forcing the basepoint path to be reflexive removes the later unit
    -- conjugation at the one-object category.
    simp [γ', xS]
  · intro i y hy t
    by_cases hyx : y = xS
    · subst hyx
      simpa [γ', xS] using stage_cover_basepoint_mem O x hx S i
    · simpa [γ', hyx] using hγ i y hy t

/-- Helper for Theorem 2.7.5: the normalized stage path family restricts to a path inside each
literal member of the finite stage cover. -/
private theorem stage_cover_member_path_source
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι))
    (y : stage_cover O S i) :
    (⟨γ y.1 0, hγ i y.1 y.2 0⟩ : stage_cover O S i) =
      stage_cover_member_basepoint O x hx S i := by
  -- Evaluate the lifted path at `0` and use the source condition of the ambient stage path.
  ext
  simpa [stage_cover_member_basepoint, stage_union_basepoint] using (γ y.1).source

/-- Helper for Theorem 2.7.5: the lifted stage path ends at the specified point of the literal
stage member. -/
private theorem stage_cover_member_path_target
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι))
    (y : stage_cover O S i) :
    (⟨γ y.1 1, hγ i y.1 y.2 1⟩ : stage_cover O S i) = y := by
  -- Evaluate the lifted path at `1` and use the target condition of the ambient stage path.
  ext
  simpa using (γ y.1).target

/-- Helper for Theorem 2.7.5: the normalized stage path family gives a path from the chosen
basepoint to any point of a literal stage member. -/
private noncomputable def stage_cover_member_path
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι))
    (y : stage_cover O S i) :
    Path (stage_cover_member_basepoint O x hx S i) y :=
  { toContinuousMap :=
      ⟨fun t ↦ ⟨γ y.1 t, hγ i y.1 y.2 t⟩,
        (γ y.1).continuous.subtype_mk fun t ↦ hγ i y.1 y.2 t⟩
    source' := stage_cover_member_path_source O x hx S γ hγ i y
    target' := stage_cover_member_path_target O x hx S γ hγ i y }

/-- Helper for Theorem 2.7.5: lifting a normalized stage path to a literal stage member commutes
strictly with inclusions of stage members. -/
private theorem stage_cover_member_path_map
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    {i j : TopologicalSpace.IsOpenCover.Index (stage_cover O S)} (f : i ⟶ j)
    (y : stage_cover O S i) :
    (stage_cover_member_path O x hx S γ hγ i y).map
        (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous) =
      stage_cover_member_path O x hx S γ hγ j
        (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom y) := by
  -- Both paths are definitionally the same ambient path with the target-stage proof adjusted by
  -- the inclusion map.
  ext t
  rfl

/-- Helper for Theorem 2.7.5: the normalized stage path determines the chosen isomorphism from the
common basepoint object to any object of a literal stage member groupoid. -/
private noncomputable def stage_basepoint_path_iso
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι))
    (y : FundamentalGroupoid (stage_cover O S i)) :
    FundamentalGroupoid.mk (stage_cover_member_basepoint O x hx S i) ≅ y :=
  (Groupoid.isoEquivHom _ _).symm
    (FundamentalGroupoid.fromPath
      ⟦stage_cover_member_path O x hx S γ hγ i y.as⟧)

/-- Helper for Theorem 2.7.5: the chosen stage basepoint isomorphisms are respected by inclusions
between literal stage members. -/
private theorem stage_basepoint_path_iso_map_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    {i j : TopologicalSpace.IsOpenCover.Index (stage_cover O S)} (f : i ⟶ j)
    (y : stage_cover O S i) :
    ((fundamental_groupoid_cover_diagram (stage_cover O S)).map f).map
        (stage_basepoint_path_iso O x hx S γ hγ i (FundamentalGroupoid.mk y)).hom =
      (stage_basepoint_path_iso O x hx S γ hγ j
        (FundamentalGroupoid.mk
          (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom y))).hom := by
  -- First rewrite the induced map on path classes as `Path.map`, then use the strict path-level
  -- compatibility just proved for the lifted stage paths.
  change ((Path.Homotopic.Quotient.mk
      ((stage_cover_member_path O x hx S γ hγ i y).map
        (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous))) :
      Path.Homotopic.Quotient _ _) =
    Path.Homotopic.Quotient.mk
      (stage_cover_member_path O x hx S γ hγ j
        (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom y))
  exact congrArg Path.Homotopic.Quotient.mk
    (stage_cover_member_path_map O x hx S γ hγ f y)

/-- Helper for Theorem 2.7.5: the symmetric stage basepoint path also commutes strictly with
literal stage inclusions. -/
private theorem stage_cover_member_path_symm_map
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    {i j : TopologicalSpace.IsOpenCover.Index (stage_cover O S)} (f : i ⟶ j)
    (y : stage_cover O S i) :
    ((stage_cover_member_path O x hx S γ hγ i y).symm.map
        (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)) =
      (stage_cover_member_path O x hx S γ hγ j
        (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom y)).symm := by
  -- Both symmetric lifted paths evaluate to the same ambient stage point at every parameter.
  ext t
  rfl

/-- Helper for Theorem 2.7.5: transporting the stage-conjugated loop path along a literal stage
inclusion agrees with rebuilding the conjugated loop from the transported endpoints. -/
private theorem stage_conjugated_loop_path_map
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    {i j : TopologicalSpace.IsOpenCover.Index (stage_cover O S)} (f : i ⟶ j)
    {y z : stage_cover O S i} (p : Path y z) :
    (((stage_cover_member_path O x hx S γ hγ i y).trans
          (p.trans (stage_cover_member_path O x hx S γ hγ i z).symm)).map
        (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)).cast
      (based_open_cover_map_basepoint
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)
        f).symm
      (based_open_cover_map_basepoint
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)
        f).symm =
      (stage_cover_member_path O x hx S γ hγ j
          (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom y)).trans
        ((p.map (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)).trans
          (stage_cover_member_path O x hx S γ hγ j
            (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom z)).symm) := by
  let A : Path (stage_cover_member_basepoint O x hx S i) y :=
    stage_cover_member_path O x hx S γ hγ i y
  let B : Path (stage_cover_member_basepoint O x hx S i) z :=
    stage_cover_member_path O x hx S γ hγ i z
  let A' : Path (stage_cover_member_basepoint O x hx S j)
      (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom y) :=
    stage_cover_member_path O x hx S γ hγ j
      (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom y)
  let B' : Path (stage_cover_member_basepoint O x hx S j)
      (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom z) :=
    stage_cover_member_path O x hx S γ hγ j
      (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom z)
  have hy_map :
      A.map (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous) =
        A' := by
    simpa [A, A'] using stage_cover_member_path_map O x hx S γ hγ f y
  have hz_map :
      B.symm.map (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous) =
        B'.symm := by
    simpa [B, B'] using stage_cover_member_path_symm_map O x hx S γ hγ f z
  have htail :
      (p.trans B.symm).map
          (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous) =
        (p.map (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)).trans
          B'.symm := by
    -- Rewrite the tail of the conjugated loop by mapping the final inverse basepoint path.
    simpa [Path.map_trans] using
      congrArg
        (fun r ↦
          (p.map (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)).trans r)
        hz_map
  have hmap :
      ((A.trans (p.trans B.symm)).map
          (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)) =
        A'.trans
          ((p.map (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)).trans
            B'.symm) := by
    have hhead :
        ((A.trans (p.trans B.symm)).map
            (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)) =
          (A.map (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)).trans
            ((p.trans B.symm).map
              (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)) := by
      rw [Path.map_trans]
    have hmid :
        (A.map (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)).trans
            ((p.trans B.symm).map
              (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)) =
          A'.trans
            ((p.trans B.symm).map
              (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)) := by
      simpa using
        congrArg
          (fun r ↦
            r.trans
              ((p.trans B.symm).map
                (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)))
          hy_map
    have hlast :
        A'.trans
            ((p.trans B.symm).map
              (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)) =
          A'.trans
            ((p.map (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom.continuous)).trans
              B'.symm) := by
      simpa using congrArg (fun r ↦ A'.trans r) htail
    exact hhead.trans (hmid.trans hlast)
  -- The stage basepoint is fixed by the inclusion, so the remaining endpoint cast is trivial.
  cases based_open_cover_map_basepoint
      (stage_cover O S)
      (stage_union_basepoint O x hx S)
      (stage_cover_basepoint_mem O x hx S)
      f
  simpa [A', B'] using hmap

/-- Helper for Theorem 2.7.5: the reverse functor from a literal stage-member groupoid to the
one-object category on its fundamental group sends identities to the trivial loop. -/
private theorem stage_groupoid_to_stage_single_obj_map_id
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι))
    (y : FundamentalGroupoid (stage_cover O S i)) :
    (FundamentalGroup.fromArrow
      ((stage_basepoint_path_iso O x hx S γ hγ i y).hom ≫
        𝟙 y ≫
        (stage_basepoint_path_iso O x hx S γ hγ i y).inv) :
      FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) = 1 := by
  -- The chosen basepoint isomorphism cancels its inverse on identity morphisms.
  change ((stage_basepoint_path_iso O x hx S γ hγ i y).hom ≫ 𝟙 y ≫
      (stage_basepoint_path_iso O x hx S γ hγ i y).inv :
      FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) = 1
  simp

/-- Helper for Theorem 2.7.5: the reverse functor on a literal stage member converts
composition in the groupoid to multiplication in the fundamental group. -/
private theorem stage_groupoid_to_stage_single_obj_map_comp
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι))
    {X Y Z : FundamentalGroupoid (stage_cover O S i)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (FundamentalGroup.fromArrow
      ((stage_basepoint_path_iso O x hx S γ hγ i X).hom ≫
        (f ≫ g) ≫
        (stage_basepoint_path_iso O x hx S γ hγ i Z).inv) :
      FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) =
    (FundamentalGroup.fromArrow
      ((stage_basepoint_path_iso O x hx S γ hγ i X).hom ≫
        f ≫
        (stage_basepoint_path_iso O x hx S γ hγ i Y).inv) :
      FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) ≫
      (FundamentalGroup.fromArrow
        ((stage_basepoint_path_iso O x hx S γ hγ i Y).hom ≫
          g ≫
          (stage_basepoint_path_iso O x hx S γ hγ i Z).inv) :
        FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) := by
  -- Insert the middle identity through the chosen basepoint isomorphism and reassociate.
  change ((stage_basepoint_path_iso O x hx S γ hγ i X).hom ≫
      (f ≫ g) ≫
      (stage_basepoint_path_iso O x hx S γ hγ i Z).inv :
      FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) =
    (((stage_basepoint_path_iso O x hx S γ hγ i X).hom ≫
        f ≫
        (stage_basepoint_path_iso O x hx S γ hγ i Y).inv :
        FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) ≫
      ((stage_basepoint_path_iso O x hx S γ hγ i Y).hom ≫
        g ≫
        (stage_basepoint_path_iso O x hx S γ hγ i Z).inv :
        FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)))
  calc
    (stage_basepoint_path_iso O x hx S γ hγ i X).hom ≫ (f ≫ g) ≫
        (stage_basepoint_path_iso O x hx S γ hγ i Z).inv
        =
      (stage_basepoint_path_iso O x hx S γ hγ i X).hom ≫ f ≫
        ((stage_basepoint_path_iso O x hx S γ hγ i Y).inv ≫
          (stage_basepoint_path_iso O x hx S γ hγ i Y).hom) ≫
        g ≫ (stage_basepoint_path_iso O x hx S γ hγ i Z).inv := by
          simp [Category.assoc]
    _ =
      (((stage_basepoint_path_iso O x hx S γ hγ i X).hom ≫
          f ≫
          (stage_basepoint_path_iso O x hx S γ hγ i Y).inv :
          FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) ≫
        ((stage_basepoint_path_iso O x hx S γ hγ i Y).hom ≫
          g ≫
          (stage_basepoint_path_iso O x hx S γ hγ i Z).inv :
          FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))) := by
            simp [Category.assoc]

/-- Helper for Theorem 2.7.5: each literal stage member has the same basepoint-conjugation functor
to the one-object category on its fundamental group as in Proposition 2.5.7, but now built from
the normalized compatible stage paths. -/
private noncomputable def stage_groupoid_to_stage_single_obj
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι)) :
    FundamentalGroupoid (stage_cover O S i) ⥤
      SingleObj (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) where
  obj _ := SingleObj.star (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
  map {y z} f :=
    FundamentalGroup.fromArrow
      ((stage_basepoint_path_iso O x hx S γ hγ i y).hom ≫
        f ≫
        (stage_basepoint_path_iso O x hx S γ hγ i z).inv)
  map_id y := stage_groupoid_to_stage_single_obj_map_id O x hx S γ hγ i y
  map_comp f g := stage_groupoid_to_stage_single_obj_map_comp O x hx S γ hγ i f g

/-- Helper for Theorem 2.7.5: because the normalized stage basepoint path is literally reflexive,
restricting the reverse stage functor to the one-object subgroupoid at the chosen basepoint is
strictly the identity functor. -/
private theorem stage_basepoint_path_iso_self
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ0 : γ (stage_union_basepoint O x hx S) = Path.refl (stage_union_basepoint O x hx S))
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι)) :
    stage_basepoint_path_iso O x hx S γ hγ i
        (FundamentalGroupoid.mk (stage_cover_member_basepoint O x hx S i)) =
      Iso.refl (FundamentalGroupoid.mk (stage_cover_member_basepoint O x hx S i)) := by
  -- The normalized stage path at the chosen basepoint is literally `Path.refl`, so the induced
  -- groupoid isomorphism is the identity.
  apply (Groupoid.isoEquivHom _ _).injective
  change FundamentalGroupoid.fromPath
      ⟦stage_cover_member_path O x hx S γ hγ i (stage_cover_member_basepoint O x hx S i)⟧ =
    𝟙 (FundamentalGroupoid.mk (stage_cover_member_basepoint O x hx S i))
  rw [FundamentalGroupoid.id_eq_path_refl]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  simp [stage_cover_member_path, stage_cover_member_basepoint, stage_union_basepoint, hγ0]

/-- Helper for Theorem 2.7.5: because the normalized stage basepoint path is literally reflexive,
restricting the reverse stage functor to the one-object subgroupoid at the chosen basepoint is
strictly the identity functor. -/
private theorem stage_groupoid_to_stage_single_obj_comp_inclusion
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ0 : γ (stage_union_basepoint O x hx S) = Path.refl (stage_union_basepoint O x hx S))
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι)) :
    cover_member_single_obj_inclusion
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)
        i ⋙
      stage_groupoid_to_stage_single_obj O x hx S γ hγ i =
        𝟭 (SingleObj
          (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))) := by
  -- The chosen reverse functor is the identity on the unique object. On morphisms, the
  -- normalized basepoint path at the chosen object is reflexive, so the conjugation disappears.
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y a
  cases X
  cases Y
  have hself :
      stage_basepoint_path_iso O x hx S γ hγ i
          ((SingleObj.functor
                (MonoidHom.id
                  (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)))).obj
            PUnit.unit) =
        Iso.refl _ := by
    simpa [cover_member_single_obj_inclusion] using
      stage_basepoint_path_iso_self O x hx S γ hγ0 hγ i
  have hmap :
      FundamentalGroup.fromArrow
          ((stage_basepoint_path_iso O x hx S γ hγ i
                ((SingleObj.functor
                      (MonoidHom.id
                        (FundamentalGroup (stage_cover O S i)
                          (stage_cover_member_basepoint O x hx S i)))).obj
                  PUnit.unit)).hom ≫
            (SingleObj.functor
                    (MonoidHom.id
                      (FundamentalGroup (stage_cover O S i)
                        (stage_cover_member_basepoint O x hx S i)))).map
                a ≫
            (stage_basepoint_path_iso O x hx S γ hγ i
                ((SingleObj.functor
                      (MonoidHom.id
                        (FundamentalGroup (stage_cover O S i)
                          (stage_cover_member_basepoint O x hx S i)))).obj
                  PUnit.unit)).inv) =
        eqToHom (by rfl) ≫
          (𝟭 (SingleObj
              (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)))).map
            a ≫
          eqToHom (by rfl) := by
    rw [hself]
    rfl
  simpa only [Functor.comp_map, stage_groupoid_to_stage_single_obj,
    cover_member_single_obj_inclusion] using hmap

/-- Helper for Theorem 2.7.5: restricting the normalized stage path family along a literal stage
member and then forgetting to the ambient finite stage recovers the original ambient stage path. -/
private theorem stage_cover_member_path_val
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι))
    (y : stage_cover O S i) :
    (stage_cover_member_path O x hx S γ hγ i y).map continuous_subtype_val = γ y.1 := by
  -- Both paths are defined pointwise by the same ambient finite-stage path `γ y.1`.
  ext t
  rfl

/-- Helper for Theorem 2.7.5: the normalized stage path family determines the chosen isomorphism
from the common stage-basepoint object to any object of the ambient finite-stage groupoid. -/
private noncomputable def stage_union_basepoint_path_iso
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (y : FundamentalGroupoid U[O, S]) :
    FundamentalGroupoid.mk (stage_union_basepoint O x hx S) ≅ y :=
  (Groupoid.isoEquivHom _ _).symm
    (FundamentalGroupoid.fromPath ⟦γ y.as⟧)

/-- Helper for Theorem 2.7.5: the normalized stage path at the chosen stage basepoint is literally
the identity isomorphism in the ambient finite-stage groupoid. -/
private theorem stage_union_basepoint_path_iso_self
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ0 : γ (stage_union_basepoint O x hx S) = Path.refl (stage_union_basepoint O x hx S)) :
    stage_union_basepoint_path_iso O x hx S γ
        (FundamentalGroupoid.mk (stage_union_basepoint O x hx S)) =
      Iso.refl (FundamentalGroupoid.mk (stage_union_basepoint O x hx S)) := by
  -- The chosen ambient stage path at the basepoint is `Path.refl`, so the associated groupoid
  -- isomorphism is the identity.
  apply (Groupoid.isoEquivHom _ _).injective
  change FundamentalGroupoid.fromPath
      ⟦γ (stage_union_basepoint O x hx S)⟧ =
    𝟙 (FundamentalGroupoid.mk (stage_union_basepoint O x hx S))
  rw [FundamentalGroupoid.id_eq_path_refl]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  simp [hγ0]

/-- Helper for Theorem 2.7.5: forgetting a lifted stage path and then reversing it agrees with
reversing the ambient normalized stage path. -/
private theorem stage_cover_member_path_symm_val
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι))
    (y : stage_cover O S i) :
    ((stage_cover_member_path O x hx S γ hγ i y).symm.map continuous_subtype_val) =
      (γ y.1).symm := by
  -- Both reversed paths evaluate to the same ambient stage point at every parameter.
  ext t
  rfl

/-- Helper for Theorem 2.7.5: after forgetting to the finite-stage union, the tail of the
stage-conjugated loop becomes the ambient path tail `p.map` followed by the reversed normalized
stage path at the endpoint. -/
private theorem stage_cover_member_path_tail_val
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι))
    {y z : stage_cover O S i} (p : Path y z) :
    ((p.trans (stage_cover_member_path O x hx S γ hγ i z).symm).map continuous_subtype_val) =
      (p.map continuous_subtype_val).trans (γ z.1).symm := by
  -- Map the concatenation and then identify the mapped endpoint path by the previous lemma.
  have hsymm :=
    stage_cover_member_path_symm_val O x hx S γ hγ i z
  simpa [Path.map_trans] using
    congrArg
      (fun r ↦ (p.map continuous_subtype_val).trans r)
      hsymm

/-- Helper for Theorem 2.7.5: forgetting the literal stage-member conjugated loop to the ambient
finite-stage union yields the ambient conjugated loop built from the normalized stage paths. -/
private theorem stage_cover_member_conjugated_loop_val
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : ↥(S : Finset ι))
    {y z : stage_cover O S i} (p : Path y z) :
    (((stage_cover_member_path O x hx S γ hγ i y).trans
          (p.trans (stage_cover_member_path O x hx S γ hγ i z).symm)).map
        continuous_subtype_val) =
      (γ y.1).trans ((p.map continuous_subtype_val).trans (γ z.1).symm) := by
  -- Split the mapped conjugated loop into its head and tail and normalize each piece.
  have hhead :=
    stage_cover_member_path_val O x hx S γ hγ i y
  have htail :=
    stage_cover_member_path_tail_val O x hx S γ hγ i p
  simpa [Path.map_trans] using
    congrArg
      (fun r ↦ ((stage_cover_member_path O x hx S γ hγ i y).map continuous_subtype_val).trans r)
      htail

/-- Helper for Theorem 2.7.5: the normalized stage path family yields the reverse functor from the
ambient finite-stage groupoid to the one-object category on its fundamental group. -/
private noncomputable def stage_union_groupoid_to_single_obj
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y) :
    FundamentalGroupoid U[O, S] ⥤
      SingleObj (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) where
  obj _ := SingleObj.star (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
  map {y z} f :=
    FundamentalGroup.fromArrow
      ((stage_union_basepoint_path_iso O x hx S γ y).hom ≫
        f ≫
        (stage_union_basepoint_path_iso O x hx S γ z).inv)
  map_id y := by
    -- The chosen ambient stage-basepoint isomorphism cancels its inverse on identities.
    change ((stage_union_basepoint_path_iso O x hx S γ y).hom ≫
        𝟙 y ≫
        (stage_union_basepoint_path_iso O x hx S γ y).inv :
      FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) = 1
    simp
  map_comp {X} {Y} {Z} f g := by
    -- Insert the middle identity through the chosen ambient stage-basepoint isomorphism.
    change ((stage_union_basepoint_path_iso O x hx S γ X).hom ≫
        (f ≫ g) ≫
        (stage_union_basepoint_path_iso O x hx S γ Z).inv :
      FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) =
      (((stage_union_basepoint_path_iso O x hx S γ X).hom ≫
          f ≫
          (stage_union_basepoint_path_iso O x hx S γ Y).inv :
        FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) ≫
        ((stage_union_basepoint_path_iso O x hx S γ Y).hom ≫
          g ≫
          (stage_union_basepoint_path_iso O x hx S γ Z).inv :
        FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)))
    calc
      (stage_union_basepoint_path_iso O x hx S γ X).hom ≫
          (f ≫ g) ≫
          (stage_union_basepoint_path_iso O x hx S γ Z).inv
          =
        (stage_union_basepoint_path_iso O x hx S γ X).hom ≫
          f ≫
          ((stage_union_basepoint_path_iso O x hx S γ Y).inv ≫
            (stage_union_basepoint_path_iso O x hx S γ Y).hom) ≫
          g ≫
          (stage_union_basepoint_path_iso O x hx S γ Z).inv := by
            simp [Category.assoc]
      _ =
        (((stage_union_basepoint_path_iso O x hx S γ X).hom ≫
            f ≫
            (stage_union_basepoint_path_iso O x hx S γ Y).inv :
          FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) ≫
          ((stage_union_basepoint_path_iso O x hx S γ Y).hom ≫
            g ≫
            (stage_union_basepoint_path_iso O x hx S γ Z).inv :
          FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))) := by
            simp [Category.assoc]

/-- Helper for Theorem 2.7.5: because the normalized ambient stage path is reflexive at the chosen
stage basepoint, restricting the ambient reverse functor to the one-object subgroupoid there is
strictly the identity functor. -/
private theorem stage_union_groupoid_to_single_obj_comp_inclusion
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ0 : γ (stage_union_basepoint O x hx S) = Path.refl (stage_union_basepoint O x hx S)) :
    ambient_single_obj_inclusion (stage_union_basepoint O x hx S) ⋙
      stage_union_groupoid_to_single_obj O x hx S γ =
        𝟭 (SingleObj
          (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))) := by
  -- The unique object is fixed. On morphisms, the normalized ambient stage path at the basepoint
  -- is reflexive, so the conjugation defining the reverse functor disappears.
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y a
  cases X
  cases Y
  have hself :
      stage_union_basepoint_path_iso O x hx S γ
          ((SingleObj.functor
                (MonoidHom.id
                  (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)))).obj
            PUnit.unit) =
        Iso.refl _ := by
    simpa [ambient_single_obj_inclusion] using
      stage_union_basepoint_path_iso_self O x hx S γ hγ0
  have hmap :
      FundamentalGroup.fromArrow
          ((stage_union_basepoint_path_iso O x hx S γ
                ((SingleObj.functor
                      (MonoidHom.id
                        (FundamentalGroup U[O, S]
                          (stage_union_basepoint O x hx S)))).obj
                  PUnit.unit)).hom ≫
            (SingleObj.functor
                    (MonoidHom.id
                      (FundamentalGroup U[O, S]
                        (stage_union_basepoint O x hx S)))).map
                a ≫
            (stage_union_basepoint_path_iso O x hx S γ
                ((SingleObj.functor
                      (MonoidHom.id
                        (FundamentalGroup U[O, S]
                          (stage_union_basepoint O x hx S)))).obj
                  PUnit.unit)).inv) =
        eqToHom (by rfl) ≫
          (𝟭 (SingleObj
              (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)))).map a ≫
          eqToHom (by rfl) := by
    rw [hself]
    rfl
  simpa only [Functor.comp_map, stage_union_groupoid_to_single_obj,
    ambient_single_obj_inclusion] using hmap

/-- Helper for Theorem 2.7.5: the literal finite-stage group cocone leg sends the conjugated loop
used by `stage_groupoid_to_stage_single_obj` to the ambient conjugated loop used by
`stage_union_groupoid_to_single_obj`. -/
private theorem stage_union_groupoid_cover_leg_mapOfEq_normalization
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S))
    {y z : stage_cover O S i} (p : Path y z) :
    ((fundamental_group_cover_cocone
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
          (stage_cover_basepoint_mem O x hx S)).ι.app i).hom
        ((stage_groupoid_to_stage_single_obj O x hx S γ hγ i).map
          (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)) =
      (stage_union_groupoid_to_single_obj O x hx S γ).map
        (((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i).map
          (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)) := by
  let q :
      Path (stage_cover_member_basepoint O x hx S i)
        (stage_cover_member_basepoint O x hx S i) :=
    (stage_cover_member_path O x hx S γ hγ i y).trans
      (p.trans (stage_cover_member_path O x hx S γ hγ i z).symm)
  have hbasepoint :
      (based_open_cover_inclusion
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
          (stage_cover_basepoint_mem O x hx S)
          i).hom
        (stage_cover_member_basepoint O x hx S i) =
      stage_union_basepoint O x hx S := by
    simpa [based_open_cover_inclusion, stage_cover_member_basepoint] using
      based_open_cover_cocone_app_basepoint
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)
        i
  have hmapOfEq :=
    FundamentalGroup.mapOfEq_apply
      (f := (based_open_cover_inclusion
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)
        i).hom)
      (h := hbasepoint)
      (p := q)
  -- First normalize the finite-stage cocone leg with `mapOfEq_apply`.
  have hleg :
      ((fundamental_group_cover_cocone
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)).ι.app i).hom
          (FundamentalGroup.fromPath ⟦q⟧) =
        FundamentalGroup.fromPath
          ⟦((q.map continuous_subtype_val).cast hbasepoint.symm hbasepoint.symm)⟧ := by
    rw [show
        (fundamental_group_cover_cocone
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)).ι.app i =
          GrpCat.ofHom
            (FundamentalGroup.mapOfEq
              ((based_open_cover_cocone
                  (stage_cover O S)
                  (stage_union_basepoint O x hx S)
                  (stage_cover_basepoint_mem O x hx S)).ι.app i).right.hom
              (fundamentalGroupFunctorMap_basepoint
                ((based_open_cover_cocone
                    (stage_cover O S)
                    (stage_union_basepoint O x hx S)
                    (stage_cover_basepoint_mem O x hx S)).ι.app i))) from by
          simpa [fundamental_group_cover_cocone] using
            (fundamentalGroupFunctor_map_eq
              ((based_open_cover_cocone
                  (stage_cover O S)
                  (stage_union_basepoint O x hx S)
                  (stage_cover_basepoint_mem O x hx S)).ι.app i))]
    simpa [based_open_cover_cocone, based_open_cover_inclusion, based_open_cover_member,
      based_open_cover_point, stage_cover_member_basepoint] using hmapOfEq
  -- Then rewrite the mapped loop to the ambient conjugated loop built from `γ`.
  have hnorm :
      FundamentalGroup.fromPath
          ⟦((q.map continuous_subtype_val).cast hbasepoint.symm hbasepoint.symm)⟧ =
        FundamentalGroup.fromPath
          ⟦(γ y.1).trans ((p.map continuous_subtype_val).trans (γ z.1).symm)⟧ := by
  -- The literal-stage conjugated loop becomes the ambient conjugated loop after forgetting the
  -- subtype data.
    have hq :
        ((q.map continuous_subtype_val).cast hbasepoint.symm hbasepoint.symm) =
          (γ y.1).trans ((p.map continuous_subtype_val).trans (γ z.1).symm) := by
      simpa [q] using
        stage_cover_member_conjugated_loop_val O x hx S γ hγ i p
    exact congrArg FundamentalGroup.fromPath <|
      congrArg Path.Homotopic.Quotient.mk hq
  have htarget :
      FundamentalGroup.fromPath
        ⟦(γ y.1).trans ((p.map continuous_subtype_val).trans (γ z.1).symm)⟧ =
      (stage_union_groupoid_to_single_obj O x hx S γ).map
        (((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i).map
          (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)) := by
    rfl
  calc
    ((fundamental_group_cover_cocone
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
          (stage_cover_basepoint_mem O x hx S)).ι.app i).hom
        ((stage_groupoid_to_stage_single_obj O x hx S γ hγ i).map
          (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)) =
      FundamentalGroup.fromPath
        ⟦(γ y.1).trans ((p.map continuous_subtype_val).trans (γ z.1).symm)⟧ := by
          exact hleg.trans hnorm
    _ =
      (stage_union_groupoid_to_single_obj O x hx S γ).map
        (((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i).map
          (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)) := by
          exact htarget

/-- Helper for Theorem 2.7.5: restricting the ambient reverse functor of a finite stage along one
literal cover member agrees with the memberwise reverse functor followed by the canonical stage
fundamental-group leg into the stage union. -/
private theorem stage_union_groupoid_to_single_obj_cover_leg
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    ((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i) ⋙
        stage_union_groupoid_to_single_obj O x hx S γ =
      stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
        CategoryTheory.SingleObj.mapHom
          (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
          (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
          ((fundamental_group_cover_cocone
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).ι.app i).hom := by
  -- Route correction: this is the strict finite-stage restriction identity missing in the earlier
  -- uniqueness argument; both sides send a representative path to the same conjugated loop in the
  -- stage union.
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro y z g
  induction g using Quotient.inductionOn with
  | h p =>
      -- On path representatives, the memberwise conjugated loop maps to the ambient conjugated
      -- loop by the dedicated normalization lemma above.
      have hmap :=
        (stage_union_groupoid_cover_leg_mapOfEq_normalization O x hx S γ hγ i p).symm
      change
        (stage_union_groupoid_to_single_obj O x hx S γ).map
            (((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i).map
              (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)) =
          eqToHom (by rfl) ≫
            ((fundamental_group_cover_cocone
                (stage_cover O S)
                (stage_union_basepoint O x hx S)
                (stage_cover_basepoint_mem O x hx S)).ι.app i).hom
              ((stage_groupoid_to_stage_single_obj O x hx S γ hγ i).map
                (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)) ≫
            eqToHom (by rfl)
      have htransport :
          eqToHom (by rfl) ≫
              ((fundamental_group_cover_cocone
                  (stage_cover O S)
                  (stage_union_basepoint O x hx S)
                  (stage_cover_basepoint_mem O x hx S)).ι.app i).hom
                ((stage_groupoid_to_stage_single_obj O x hx S γ hγ i).map
                  (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)) ≫
              eqToHom (by rfl) =
            ((fundamental_group_cover_cocone
                (stage_cover O S)
                (stage_union_basepoint O x hx S)
                (stage_cover_basepoint_mem O x hx S)).ι.app i).hom
              ((stage_groupoid_to_stage_single_obj O x hx S γ hγ i).map
                (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)) := by
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact hmap.trans htransport.symm

/-- Helper for Theorem 2.7.5: after postcomposing with a fixed stage group cocone leg, the image
of a representative path class agrees with the image obtained by first transporting that class to
the larger stage member. -/
private theorem stage_groupoid_leg_map_eq_of_cocone
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (C : Cocone
      (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)))
    {i j : TopologicalSpace.IsOpenCover.Index (stage_cover O S)} (f : i ⟶ j)
    {y z : stage_cover O S i} (p : Path y z) :
    (C.ι.app j).hom
        ((stage_groupoid_to_stage_single_obj O x hx S γ hγ j).map
          (((fundamental_groupoid_cover_diagram (stage_cover O S)).map f).map
            (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧))) =
      (C.ι.app i).hom
        ((stage_groupoid_to_stage_single_obj O x hx S γ hγ i).map
          (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)) := by
  let gi :
      FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i) :=
    (stage_groupoid_to_stage_single_obj O x hx S γ hγ i).map
      (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)
  let gj :
      FundamentalGroup (stage_cover O S j) (stage_cover_member_basepoint O x hx S j) :=
    (stage_groupoid_to_stage_single_obj O x hx S γ hγ j).map
      (((fundamental_groupoid_cover_diagram (stage_cover O S)).map f).map
        (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧))
  have hC :
      (C.ι.app j).hom (((fundamental_group_cover_diagram
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)).map f).hom gi) =
        (C.ι.app i).hom gi := by
    -- Evaluate the cocone relation on the loop class produced in the smaller stage member.
    simpa [GrpCat.comp_apply] using
      (ConcreteCategory.congr_hom (C.w f) gi)
  have hmap :
      ((fundamental_group_cover_diagram
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)).map f).hom gi =
        gj := by
    -- Rewrite both sides to the conjugated-loop representatives determined by the normalized
    -- stage basepoint paths, then apply the explicit `mapOfEq_apply` normalization above.
    let q : Path (stage_cover_member_basepoint O x hx S i) (stage_cover_member_basepoint O x hx S i) :=
      (stage_cover_member_path O x hx S γ hγ i y).trans
        (p.trans (stage_cover_member_path O x hx S γ hγ i z).symm)
    let hbp :
        ((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom
            (stage_cover_member_basepoint O x hx S i) =
          stage_cover_member_basepoint O x hx S j :=
      based_open_cover_map_basepoint
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)
        f
    have hraw :=
      FundamentalGroup.mapOfEq_apply
        (f := ((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom)
        (h := hbp)
        (p := q)
    have hwhole :
        ((fundamental_group_cover_diagram
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).map f).hom
            (FundamentalGroup.fromPath ⟦q⟧) =
          FundamentalGroup.fromPath
            ⟦((q.map
                  (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map
                        f).hom.continuous)).cast hbp.symm hbp.symm)⟧ := by
      simpa [hbp] using hraw
    have hnorm :
        FundamentalGroup.fromPath
            ⟦((q.map
                  (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map
                        f).hom.continuous)).cast hbp.symm hbp.symm)⟧ =
          FundamentalGroup.fromPath
            ⟦(stage_cover_member_path O x hx S γ hγ j
                  (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom
                    y)).trans
                ((p.map
                      (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map
                            f).hom.continuous)).trans
                  (stage_cover_member_path O x hx S γ hγ j
                    (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom
                      z)).symm)⟧ := by
      exact congrArg FundamentalGroup.fromPath <|
        congrArg Path.Homotopic.Quotient.mk
          (stage_conjugated_loop_path_map O x hx S γ hγ f p)
    change
      ((fundamental_group_cover_diagram
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)).map f).hom
          (FundamentalGroup.fromPath ⟦q⟧) =
        FundamentalGroup.fromPath
          ⟦(stage_cover_member_path O x hx S γ hγ j
                (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom
                  y)).trans
              ((p.map
                    (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map
                          f).hom.continuous)).trans
                (stage_cover_member_path O x hx S γ hγ j
                  (((inducedFunctor (stage_cover O S) ⋙ toTopCat (TopCat.of U[O, S])).map f).hom
                    z)).symm)⟧
    exact hwhole.trans hnorm
  -- Replace the transported stage-loop class by the explicit larger-stage description.
  rw [hmap] at hC
  simpa [gi, gj] using hC

/-- Helper for Theorem 2.7.5: the object-universe lift of a one-object category still has the
induced category structure. -/
private instance ulift_single_obj_category (G : GrpCat) :
    Category (ULift (SingleObj G)) :=
  CategoryTheory.uliftCategory (C := SingleObj G)

/-- Helper for Theorem 2.7.5: the object-universe lift of a one-object groupoid is again a
groupoid. -/
private instance ulift_single_obj_groupoid (G : GrpCat) :
    Groupoid (ULift (SingleObj G)) where
  inv {X Y} f := by
    exact (show Y.down ⟶ X.down from Groupoid.inv (show X.down ⟶ Y.down from f))
  inv_comp := by
    intro X Y f
    change (show Y.down ⟶ X.down from Groupoid.inv (show X.down ⟶ Y.down from f)) ≫ f = 𝟙 Y.down
    exact Groupoid.inv_comp (f := (show X.down ⟶ Y.down from f))
  comp_inv := by
    intro X Y f
    change f ≫ (show Y.down ⟶ X.down from Groupoid.inv (show X.down ⟶ Y.down from f)) = 𝟙 X.down
    exact Groupoid.comp_inv (f := (show X.down ⟶ Y.down from f))

/-- Helper for Theorem 2.7.5: lifting the unique object of a one-object category into `ULift`
does not change any of its morphisms. -/
private noncomputable def single_obj_ulift_functor (G : GrpCat) :
    SingleObj G ⥤ Grpd.of (ULift (SingleObj G)) where
  obj _ := ⟨SingleObj.star G⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Helper for Theorem 2.7.5: the `ULift` functor on a one-object category leaves every morphism
unchanged. -/
private theorem single_obj_ulift_functor_map_eq
    {G : GrpCat} {X Y : SingleObj G} (g : X ⟶ Y) :
    (single_obj_ulift_functor G).map g = g := by
  -- The `ULift` adapter acts identically on morphisms of the one-object category.
  rfl

/-- Helper for Theorem 2.7.5: the constant-target `eqToHom` transports around a lifted morphism in
`ULift (SingleObj G)` collapse to the morphism itself. -/
private theorem single_obj_ulift_eqToHom_map_eq
    {G : GrpCat.{u}} {X Y : SingleObj G} (g : X ⟶ Y) :
    eqToHom (by rfl : (single_obj_ulift_functor G).obj X = (single_obj_ulift_functor G).obj X) ≫
        (single_obj_ulift_functor G).map g ≫
        eqToHom (by rfl : (single_obj_ulift_functor G).obj Y = (single_obj_ulift_functor G).obj Y) =
      (single_obj_ulift_functor G).map g := by
  let F : SingleObj G ⥤ Grpd.of (ULift.{u, 0} (SingleObj G)) := single_obj_ulift_functor G
  suffices
      𝟙 (F.obj X) ≫ F.map g ≫ 𝟙 (F.obj Y) = F.map g by
    simpa only [F, Grpd.coe_of, eqToHom_refl] using this
  -- After normalizing the transports to identities, only the two unit laws remain.
  calc
    𝟙 (F.obj X) ≫ F.map g ≫ 𝟙 (F.obj Y) =
      (𝟙 (F.obj X) ≫ F.map g) ≫ 𝟙 (F.obj Y) := by
        exact (Category.assoc _ _ _).symm
    _ = 𝟙 (F.obj X) ≫ F.map g := by
      exact Category.comp_id _
    _ = F.map g := by
      exact Category.id_comp _

/-- Helper for Theorem 2.7.5: the fixed-target equality from
`stage_groupoid_leg_map_eq_of_cocone` matches the exact `Functor.ext` map goal after the constant
ULift target introduces its unavoidable `eqToHom` transport. -/
private theorem stage_groupoid_ulift_leg_heq_of_cocone
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (C : Cocone
      (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)))
    {i j : TopologicalSpace.IsOpenCover.Index (stage_cover O S)} (f : i ⟶ j)
    {y z : ↑((fundamental_groupoid_cover_diagram (stage_cover O S)).obj i)}
    (g : y ⟶ z) :
    ((fundamental_groupoid_cover_diagram (stage_cover O S)).map f ≫
          stage_groupoid_to_stage_single_obj O x hx S γ hγ j ⋙
            (SingleObj.mapHom
                (FundamentalGroup (stage_cover O S j) (stage_cover_member_basepoint O x hx S j))
                (((Functor.const _).obj C.pt).obj j))
              (C.ι.app j).hom ⋙
            single_obj_ulift_functor C.pt).map
      g =
    eqToHom (by rfl) ≫
      ((stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
                (SingleObj.mapHom
                    (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
                    (((Functor.const _).obj C.pt).obj i))
                  (C.ι.app i).hom ⋙
                single_obj_ulift_functor C.pt) ≫
              ((Functor.const _).obj (Grpd.of (ULift.{u, 0} (SingleObj ↑C.pt)))).map
                f).map
          g ≫
        eqToHom (by rfl) := by
  induction g using Quotient.inductionOn with
  | h p =>
      let F : SingleObj C.pt ⥤ Grpd.of (ULift.{u, 0} (SingleObj C.pt)) := single_obj_ulift_functor C.pt
      let leftMorph : SingleObj.star C.pt ⟶ SingleObj.star C.pt :=
        (C.ι.app j).hom
          ((stage_groupoid_to_stage_single_obj O x hx S γ hγ j).map
            (((fundamental_groupoid_cover_diagram (stage_cover O S)).map f).map
              (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧)))
      let rightMorph : SingleObj.star C.pt ⟶ SingleObj.star C.pt :=
        (C.ι.app i).hom
          ((stage_groupoid_to_stage_single_obj O x hx S γ hγ i).map
            (FundamentalGroupoid.fromPath (X := stage_cover O S i) ⟦p⟧))
      have hleg : leftMorph = rightMorph := by
        -- Compare the two stage cocone legs before the constant-target transport is introduced.
        simpa [leftMorph, rightMorph] using
          stage_groupoid_leg_map_eq_of_cocone O x hx S γ hγ C f p
      have hbase :
          F.map leftMorph = F.map rightMorph := by
        -- Apply the `ULift` functor to the already-closed fixed-target stage leg equality.
        exact congrArg
          (fun c : SingleObj.star C.pt ⟶ SingleObj.star C.pt =>
            F.map c)
          hleg
      have htransport :
          eqToHom (by rfl) ≫ F.map rightMorph ≫ eqToHom (by rfl) = F.map rightMorph := by
        -- The codomain-only transport on the constant ULift target is exactly the generic
        -- one-object normalization handled above.
        suffices
            𝟙 (F.obj (SingleObj.star C.pt)) ≫ F.map rightMorph ≫
                𝟙 (F.obj (SingleObj.star C.pt)) =
              F.map rightMorph by
          simpa only [F, Grpd.coe_of, eqToHom_refl] using this
        calc
          𝟙 (F.obj (SingleObj.star C.pt)) ≫ F.map rightMorph ≫
              𝟙 (F.obj (SingleObj.star C.pt)) =
            (𝟙 (F.obj (SingleObj.star C.pt)) ≫ F.map rightMorph) ≫
              𝟙 (F.obj (SingleObj.star C.pt)) := by
              exact (Category.assoc _ _ _).symm
          _ = 𝟙 (F.obj (SingleObj.star C.pt)) ≫ F.map rightMorph := by
            exact Category.comp_id _
          _ = F.map rightMorph := by
            exact Category.id_comp _
      -- Transfer the fixed-target equality through the lifted functor, then cancel the
      -- constant-target transports on the right-hand side.
      have hfinal :
          F.map leftMorph = eqToHom (by rfl) ≫ F.map rightMorph ≫ eqToHom (by rfl) := by
        exact hbase.trans htransport.symm
      simpa [F, Functor.comp_map, leftMorph, rightMorph] using hfinal

/-- Helper for Theorem 2.7.5: a cocone over the literal stage group diagram induces a cocone over
the literal stage groupoid diagram by composing with the strict reverse stage functors. -/
private noncomputable def stage_groupoid_cocone_of_group_cocone
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (C : Cocone
      (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S))) :
    Cocone (fundamental_groupoid_cover_diagram (stage_cover O S)) :=
  by
    refine
      { pt := Grpd.of (ULift (SingleObj C.pt))
        ι :=
          { app := fun i ↦
              stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
                CategoryTheory.SingleObj.mapHom _ _ (C.ι.app i).hom ⋙
                single_obj_ulift_functor C.pt
            naturality := ?_ } }
    intro i j f
    -- The lifted cocone legs agree on each representative path class because the postcomposed
    -- stage comparison already lands in the fixed target group `C.pt`.
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro y z g
    -- Route correction: the constant-target transport is discharged once by the dedicated ULift
    -- bridge theorem instead of being normalized ad hoc inside this cocone proof.
    exact stage_groupoid_ulift_leg_heq_of_cocone O x hx S γ hγ C f g

/-- Helper for Theorem 2.7.5: a candidate morphism out of the literal finite-stage fundamental
group factors the corresponding stage groupoid cocone through the ambient reverse functor. -/
private theorem stage_groupoid_factorization_of_group_desc
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (C : Cocone
      (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)))
    (ψ :
      (fundamental_group_cover_cocone
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)).pt ⟶ C.pt)
    (hψ :
      ∀ i,
        (fundamental_group_cover_cocone
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
          ψ =
        C.ι.app i) :
    ∀ i,
      ((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i) ⋙
          stage_union_groupoid_to_single_obj O x hx S γ ⋙
          CategoryTheory.SingleObj.mapHom
            (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
            C.pt
            ψ.hom ⋙
          single_obj_ulift_functor C.pt =
        (stage_groupoid_cocone_of_group_cocone O x hx S γ hγ C).ι.app i := by
  intro i
  -- Postcompose the strict finite-stage cover-leg identity with the candidate desc morphism `ψ`.
  have hpost :=
    congrArg
      (fun K ↦
        K ⋙
          CategoryTheory.SingleObj.mapHom
            (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
            C.pt
            ψ.hom ⋙
          single_obj_ulift_functor C.pt)
      (stage_union_groupoid_to_single_obj_cover_leg O x hx S γ hγ i)
  have hψhom :
      ψ.hom.comp
          ((fundamental_group_cover_cocone
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).ι.app i).hom =
        (C.ι.app i).hom := by
    simpa [GrpCat.comp_apply] using congrArg GrpCat.Hom.hom (hψ i)
  let stageLeg :
      GrpCat.of
          (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) ⟶
        GrpCat.of (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) :=
    (fundamental_group_cover_cocone
      (stage_cover O S)
      (stage_union_basepoint O x hx S)
      (stage_cover_basepoint_mem O x hx S)).ι.app i
  have h1 :
      ((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i) ⋙
            stage_union_groupoid_to_single_obj O x hx S γ ⋙
            CategoryTheory.SingleObj.mapHom
              (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
              C.pt
              ψ.hom ⋙
            single_obj_ulift_functor C.pt =
        ((stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
              CategoryTheory.SingleObj.mapHom
                (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
                (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
                stageLeg.hom) ⋙
            CategoryTheory.SingleObj.mapHom
              (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
              C.pt
              ψ.hom) ⋙
          single_obj_ulift_functor C.pt := by
    simpa [Functor.comp_assoc, stageLeg] using hpost
  have h2 :
      ((stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
            CategoryTheory.SingleObj.mapHom
              (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
              (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
              stageLeg.hom) ⋙
          CategoryTheory.SingleObj.mapHom
            (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
            C.pt
            ψ.hom) ⋙
        single_obj_ulift_functor C.pt =
      (stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
            CategoryTheory.SingleObj.mapHom
              (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
              C.pt
              (ψ.hom.comp stageLeg.hom) ⋙
          single_obj_ulift_functor C.pt) := by
    change
      stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
          ((CategoryTheory.SingleObj.mapHom
                (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
                (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
                stageLeg.hom) ⋙
              CategoryTheory.SingleObj.mapHom
                (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
                C.pt
                ψ.hom) ⋙
            single_obj_ulift_functor C.pt =
        stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
          CategoryTheory.SingleObj.mapHom
            (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
            C.pt
            (ψ.hom.comp stageLeg.hom) ⋙
          single_obj_ulift_functor C.pt
    exact congrArg
      (fun K ↦
        stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
          K ⋙
          single_obj_ulift_functor C.pt)
      (CategoryTheory.SingleObj.mapHom_comp stageLeg.hom ψ.hom).symm
  have h3 :
      (stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
            CategoryTheory.SingleObj.mapHom
              (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
              C.pt
              (ψ.hom.comp stageLeg.hom) ⋙
          single_obj_ulift_functor C.pt) =
        (stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
            CategoryTheory.SingleObj.mapHom
              (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
              C.pt
              (C.ι.app i).hom ⋙
          single_obj_ulift_functor C.pt) := by
    simpa [stageLeg] using congrArg
      (fun f ↦
        stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
          CategoryTheory.SingleObj.mapHom
            (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
            C.pt
            f ⋙
          single_obj_ulift_functor C.pt)
      hψhom
  have h4 :
      (stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
            CategoryTheory.SingleObj.mapHom
              (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
              C.pt
              (C.ι.app i).hom ⋙
          single_obj_ulift_functor C.pt) =
        (stage_groupoid_cocone_of_group_cocone O x hx S γ hγ C).ι.app i := by
    rfl
  exact h1.trans (h2.trans (h3.trans h4))

/-- Helper for Theorem 2.7.5: a functor from the literal stage groupoid to a lifted one-object
groupoid determines a group homomorphism on loops at the chosen stage basepoint by evaluation on
endomorphisms of that basepoint object. -/
private noncomputable def stage_groupoid_desc_to_group_hom
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (G : GrpCat)
    (F : FundamentalGroupoid U[O, S] ⥤ Grpd.of (ULift (SingleObj G))) :
    GrpCat.of (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) ⟶ G :=
  -- The target is a one-object groupoid, so `F` already induces the required homomorphism on
  -- vertex groups by `Functor.mapEnd`.
  GrpCat.ofHom (F.mapEnd (FundamentalGroupoid.mk (stage_union_basepoint O x hx S)))

/-- Helper for Theorem 2.7.5: evaluating a descended stage groupoid functor on loops at the stage
basepoint is strictly the same as first entering the one-object subgroupoid at that basepoint and
then applying the induced group homomorphism. -/
private theorem stage_groupoid_desc_to_group_hom_basepoint_factorization
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (G : GrpCat)
    (F : FundamentalGroupoid U[O, S] ⥤ Grpd.of (ULift (SingleObj G))) :
    ambient_single_obj_inclusion (stage_union_basepoint O x hx S) ⋙ F =
      CategoryTheory.SingleObj.mapHom
          (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
          G
          (stage_groupoid_desc_to_group_hom O x hx S G F).hom ⋙
        single_obj_ulift_functor G := by
  -- Both functors fix the unique object, so only the loop action at the chosen stage basepoint
  -- remains. That action is exactly `Functor.mapEnd` by definition.
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y g
  cases X
  cases Y
  induction g using Quotient.inductionOn with
  | h p =>
      -- Normalize the constant-target transport on the one-object `ULift` codomain.
      simpa [stage_groupoid_desc_to_group_hom, ambient_single_obj_inclusion, Functor.comp_map] using
        (single_obj_ulift_eqToHom_map_eq
          (G := G)
          (g := (F.mapEnd (FundamentalGroupoid.mk (stage_union_basepoint O x hx S)))
            (FundamentalGroupoid.fromPath ⟦p⟧))).symm

/-- Helper for Theorem 2.7.5: if a descended stage groupoid functor agrees with a chosen stage leg
on a literal cover member, then the induced group hom on stage loops agrees with that stage leg. -/
private theorem stage_groupoid_desc_to_group_hom_fac
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y)
    (hγ0 : γ (stage_union_basepoint O x hx S) = Path.refl (stage_union_basepoint O x hx S))
    (hγ : ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      γ y t ∈ stage_cover O S i)
    (G : GrpCat)
    (F : FundamentalGroupoid U[O, S] ⥤ Grpd.of (ULift (SingleObj G)))
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S))
    (φ :
      (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)).obj i ⟶ G)
    (hF :
      ((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i) ≫ F =
        stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
          CategoryTheory.SingleObj.mapHom
            (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
            G
            φ.hom ⋙
          single_obj_ulift_functor G) :
    (fundamental_group_cover_cocone
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
      (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
        stage_groupoid_desc_to_group_hom O x hx S G F =
      φ := by
  ext g
  let g' :
      SingleObj.star
          (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) ⟶
        SingleObj.star
          (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i)) := g
  -- Compare the stage leg after entering the ambient one-object subgroupoid and postcomposing
  -- with the descended stage groupoid functor.
  have hnat :
      (((CategoryTheory.SingleObj.mapHom
              (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
              (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
              ((fundamental_group_cover_cocone
                  (stage_cover O S)
                  (stage_union_basepoint O x hx S)
                  (stage_cover_basepoint_mem O x hx S)).ι.app i).hom) ⋙
            ambient_single_obj_inclusion (stage_union_basepoint O x hx S) ⋙ F).map g') =
        ((cover_member_single_obj_inclusion
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)
              i ⋙
            ((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i) ⋙ F).map g') := by
    exact congrArg (fun K => K.map g') <|
      congrArg (fun K => K ⋙ F) <|
        fundamental_group_cover_cocone_leg_naturality
          (O := stage_cover O S)
          (x := stage_union_basepoint O x hx S)
          (hx := stage_cover_basepoint_mem O x hx S)
          i
  -- Rewrite both sides using the strict basepoint factorization and the chosen stage leg.
  rw [stage_groupoid_desc_to_group_hom_basepoint_factorization (O := O) (x := x) (hx := hx)
      (S := S) (G := G) (F := F)] at hnat
  have hF' :
      cover_member_single_obj_inclusion
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)
            i ⋙
          ((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i) ⋙ F =
        cover_member_single_obj_inclusion
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)
            i ⋙
          stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
            CategoryTheory.SingleObj.mapHom
              (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
              G
              φ.hom ⋙
            single_obj_ulift_functor G := by
    exact congrArg
      (fun K ↦
        cover_member_single_obj_inclusion
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
          (stage_cover_basepoint_mem O x hx S)
          i ⋙ K)
      hF
  rw [hF'] at hnat
  have hcomp :
      cover_member_single_obj_inclusion
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)
            i ⋙
          stage_groupoid_to_stage_single_obj O x hx S γ hγ i ⋙
            CategoryTheory.SingleObj.mapHom
              (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
              G
              φ.hom ⋙
            single_obj_ulift_functor G =
        𝟭 (SingleObj
            (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))) ⋙
          CategoryTheory.SingleObj.mapHom
            (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
            G
            φ.hom ⋙
          single_obj_ulift_functor G := by
    exact congrArg
      (fun K ↦
        K ⋙
          CategoryTheory.SingleObj.mapHom
            (FundamentalGroup (stage_cover O S i) (stage_cover_member_basepoint O x hx S i))
            G
            φ.hom ⋙
          single_obj_ulift_functor G)
      (stage_groupoid_to_stage_single_obj_comp_inclusion (O := O) (x := x) (hx := hx)
        (S := S) (γ := γ) (hγ0 := hγ0) (hγ := hγ) i)
  rw [hcomp] at hnat
  -- TODO: after these rewrites, both sides are loop images in the constant one-object `ULift`
  -- target. Normalize the residual `eqToHom` transports with
  -- `single_obj_ulift_eqToHom_map_eq` and read off the underlying group-hom equality.
  simpa [Functor.comp_map, GrpCat.comp_apply, single_obj_ulift_functor] using hnat

/-- Helper for Theorem 2.7.5: choose once and for all a normalized compatible basepoint-path
family on a literal finite stage. -/
private noncomputable def stage_normalized_path_family
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (hpath : ∀ i, PathConnectedSpace (O i)) :
    ∀ y : U[O, S], Path (stage_union_basepoint O x hx S) y :=
  Classical.choose (exists_normalized_stage_cover_compatible_basepoint_paths O x hx S hpath)

/-- Helper for Theorem 2.7.5: the chosen normalized finite-stage path family is reflexive at the
stage basepoint. -/
private theorem stage_normalized_path_family_refl
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (hpath : ∀ i, PathConnectedSpace (O i)) :
    stage_normalized_path_family O x hx S hpath (stage_union_basepoint O x hx S) =
      Path.refl (stage_union_basepoint O x hx S) := by
  -- Unpack the chosen normalized path family and read off its normalization property.
  exact (Classical.choose_spec
    (exists_normalized_stage_cover_compatible_basepoint_paths O x hx S hpath)).1

/-- Helper for Theorem 2.7.5: the chosen normalized finite-stage path family stays inside each
literal stage member containing its endpoint. -/
private theorem stage_normalized_path_family_mem
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (hpath : ∀ i, PathConnectedSpace (O i)) :
    ∀ (i : ↥(S : Finset ι)) (y : U[O, S]), y ∈ stage_cover O S i → ∀ t : I,
      stage_normalized_path_family O x hx S hpath y t ∈ stage_cover O S i := by
  -- The second component of the chosen witness is exactly the required memberwise containment.
  exact (Classical.choose_spec
    (exists_normalized_stage_cover_compatible_basepoint_paths O x hx S hpath)).2

/-- Helper for Theorem 2.7.5: a cocone over the literal finite-stage group diagram canonically
induces a cocone over the corresponding stage groupoid diagram using the chosen normalized path
family. -/
private noncomputable def stage_restricted_groupoid_cocone_of_group_cocone
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (S : intersection_closed_subcover_index O)
    (C : Cocone
      (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S))) :
    Cocone (fundamental_groupoid_cover_diagram (stage_cover O S)) :=
  stage_groupoid_cocone_of_group_cocone
    O x hx S
    (stage_normalized_path_family O x hx S hpath)
    (stage_normalized_path_family_mem O x hx S hpath)
    C

/-- Helper for Theorem 2.7.5: descending the chosen finite-stage groupoid cocone through Theorem
2.7.1 yields a functor out of the finite-stage fundamental groupoid. -/
private noncomputable def stage_restricted_groupoid_desc
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (S : intersection_closed_subcover_index O)
    (C : Cocone
      (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S))) :
    FundamentalGroupoid U[O, S] ⥤ Grpd.of (ULift (SingleObj C.pt)) :=
  (fundamental_groupoid_is_colimit_of_path_connected_open_cover
      (stage_cover O S)
      (stage_cover_isOpenCover O S)
      (stage_cover_path_connected O S hpath)
      (stage_cover_closed_under_nonempty_finite_intersections O S)).desc
    (stage_restricted_groupoid_cocone_of_group_cocone O x hx hpath S C)

/-- Helper for Theorem 2.7.5: the descended finite-stage groupoid functor induces the canonical
group morphism from the finite-stage fundamental group to the cocone point. -/
private noncomputable def stage_restricted_fundamental_group_desc
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (S : intersection_closed_subcover_index O)
    (C : Cocone
      (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S))) :
    (fundamental_group_cover_cocone
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)).pt ⟶ C.pt :=
  stage_groupoid_desc_to_group_hom
    O x hx S C.pt (stage_restricted_groupoid_desc O x hx hpath S C)

/-- Helper for Theorem 2.7.5: the descended finite-stage group morphism satisfies the literal
stage cocone equations. -/
private theorem stage_restricted_fundamental_group_desc_fac
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (S : intersection_closed_subcover_index O)
    (C : Cocone
      (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)))
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    (fundamental_group_cover_cocone
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
          (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
        stage_restricted_fundamental_group_desc O x hx hpath S C =
      C.ι.app i := by
  -- First read off the stage groupoid colimit factorization on the literal cover member `i`.
  have hdesc :
      ((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i) ≫
          stage_restricted_groupoid_desc O x hx hpath S C =
        (stage_restricted_groupoid_cocone_of_group_cocone O x hx hpath S C).ι.app i := by
    simpa [stage_restricted_groupoid_desc] using
      (fundamental_groupoid_is_colimit_of_path_connected_open_cover
          (stage_cover O S)
          (stage_cover_isOpenCover O S)
          (stage_cover_path_connected O S hpath)
          (stage_cover_closed_under_nonempty_finite_intersections O S)).fac
        (stage_restricted_groupoid_cocone_of_group_cocone O x hx hpath S C)
        i
  -- Then convert that functor-level factorization into the required group-level one.
  simpa [stage_restricted_fundamental_group_desc,
    stage_restricted_groupoid_cocone_of_group_cocone] using
    stage_groupoid_desc_to_group_hom_fac
      O x hx S
      (stage_normalized_path_family O x hx S hpath)
      (stage_normalized_path_family_refl O x hx S hpath)
      (stage_normalized_path_family_mem O x hx S hpath)
      C.pt
      (stage_restricted_groupoid_desc O x hx hpath S C)
      i
      (C.ι.app i)
      hdesc

/-- Helper for Theorem 2.7.5: any finite-stage group morphism satisfying the literal cocone
equations agrees with the descended finite-stage morphism. -/
private theorem stage_restricted_fundamental_group_desc_unique
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (S : intersection_closed_subcover_index O)
    (C : Cocone
      (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)))
    (ψ :
      (fundamental_group_cover_cocone
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)).pt ⟶ C.pt)
    (hψ :
      ∀ i,
        (fundamental_group_cover_cocone
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
          ψ =
        C.ι.app i) :
    ψ = stage_restricted_fundamental_group_desc O x hx hpath S C := by
  let Fψ :
      FundamentalGroupoid U[O, S] ⥤ Grpd.of (ULift (SingleObj C.pt)) :=
    stage_union_groupoid_to_single_obj
        O x hx S (stage_normalized_path_family O x hx S hpath) ⋙
      CategoryTheory.SingleObj.mapHom
        (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
        C.pt
        ψ.hom ⋙
      single_obj_ulift_functor C.pt
  have hfactor_Fψ :
      ∀ i,
        ((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i) ⋙ Fψ =
          (stage_restricted_groupoid_cocone_of_group_cocone O x hx hpath S C).ι.app i := by
    -- Package the candidate group morphism `ψ` as a factorization of the stage groupoid cocone.
    intro i
    simpa [Fψ, stage_restricted_groupoid_cocone_of_group_cocone] using
      stage_groupoid_factorization_of_group_desc
        O x hx S
        (stage_normalized_path_family O x hx S hpath)
        (stage_normalized_path_family_mem O x hx S hpath)
        C
        ψ
        hψ
        i
  have hfactor_desc :
      ∀ i,
        ((fundamental_groupoid_cover_cocone (stage_cover O S)).ι.app i) ⋙
            stage_restricted_groupoid_desc O x hx hpath S C =
          (stage_restricted_groupoid_cocone_of_group_cocone O x hx hpath S C).ι.app i := by
    -- The descended groupoid functor has the same cover-leg factorization by the colimit property.
    intro i
    simpa [stage_restricted_groupoid_desc] using
      (fundamental_groupoid_is_colimit_of_path_connected_open_cover
          (stage_cover O S)
          (stage_cover_isOpenCover O S)
          (stage_cover_path_connected O S hpath)
          (stage_cover_closed_under_nonempty_finite_intersections O S)).fac
        (stage_restricted_groupoid_cocone_of_group_cocone O x hx hpath S C)
        i
  have hFψ :
      Fψ = stage_restricted_groupoid_desc O x hx hpath S C := by
    -- The stage groupoid colimit identifies any two factorizations of the same lifted cocone.
    apply (fundamental_groupoid_is_colimit_of_path_connected_open_cover
      (stage_cover O S)
      (stage_cover_isOpenCover O S)
      (stage_cover_path_connected O S hpath)
      (stage_cover_closed_under_nonempty_finite_intersections O S)).hom_ext
    intro i
    exact (hfactor_Fψ i).trans (hfactor_desc i).symm
  have hbase :
      CategoryTheory.SingleObj.mapHom
            (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
            C.pt
            ψ.hom ⋙
          single_obj_ulift_functor C.pt =
        CategoryTheory.SingleObj.mapHom
            (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
            C.pt
            (stage_restricted_fundamental_group_desc O x hx hpath S C).hom ⋙
          single_obj_ulift_functor C.pt := by
    -- Restrict the functor equality to the one-object subgroupoid at the chosen stage basepoint.
    have hpre :=
      congrArg
        (fun K ↦ ambient_single_obj_inclusion (stage_union_basepoint O x hx S) ⋙ K)
        hFψ
    calc
      CategoryTheory.SingleObj.mapHom
            (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
            C.pt
            ψ.hom ⋙
          single_obj_ulift_functor C.pt =
        ambient_single_obj_inclusion (stage_union_basepoint O x hx S) ⋙ Fψ := by
          symm
          calc
            ambient_single_obj_inclusion (stage_union_basepoint O x hx S) ⋙ Fψ =
              (ambient_single_obj_inclusion (stage_union_basepoint O x hx S) ⋙
                  stage_union_groupoid_to_single_obj O x hx S
                    (stage_normalized_path_family O x hx S hpath)) ⋙
                CategoryTheory.SingleObj.mapHom
                  (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
                  C.pt
                  ψ.hom ⋙
                single_obj_ulift_functor C.pt := by
                  rfl
            _ =
              𝟭 (SingleObj
                (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))) ⋙
                CategoryTheory.SingleObj.mapHom
                  (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
                  C.pt
                  ψ.hom ⋙
                single_obj_ulift_functor C.pt := by
                  rw [stage_union_groupoid_to_single_obj_comp_inclusion
                    (O := O) (x := x) (hx := hx) (S := S)
                    (γ := stage_normalized_path_family O x hx S hpath)
                    (hγ0 := stage_normalized_path_family_refl O x hx S hpath)]
            _ =
              CategoryTheory.SingleObj.mapHom
                (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
                C.pt
                ψ.hom ⋙
              single_obj_ulift_functor C.pt := by
                rfl
      _ =
        ambient_single_obj_inclusion (stage_union_basepoint O x hx S) ⋙
          stage_restricted_groupoid_desc O x hx hpath S C := by
            simpa using hpre
      _ =
        CategoryTheory.SingleObj.mapHom
            (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
            C.pt
            (stage_restricted_fundamental_group_desc O x hx hpath S C).hom ⋙
          single_obj_ulift_functor C.pt := by
            simpa [stage_restricted_fundamental_group_desc] using
              stage_groupoid_desc_to_group_hom_basepoint_factorization
                (O := O) (x := x) (hx := hx) (S := S) (G := C.pt)
                (F := stage_restricted_groupoid_desc O x hx hpath S C)
  -- Finally compare the two one-object functors on an arbitrary loop element.
  ext g
  have hmap :=
    congrArg
      (fun K ↦
        K.map
          (show
            SingleObj.star (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) ⟶
              SingleObj.star (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S))
            from g))
      hbase
  simpa [Functor.comp_map, single_obj_ulift_functor] using hmap

/-- Helper for Theorem 2.7.5: every literal finite stage has the required group-level colimit
property. -/
private noncomputable def stage_restricted_fundamental_group_is_colimit
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (S : intersection_closed_subcover_index O) :
    IsColimit
      (fundamental_group_cover_cocone
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)) :=
  IsColimit.ofExistsUnique fun C ↦ by
    -- The finite-stage group colimit now follows from the descended morphism and its uniqueness.
    refine ⟨stage_restricted_fundamental_group_desc O x hx hpath S C, ?_, ?_⟩
    · intro i
      exact stage_restricted_fundamental_group_desc_fac O x hx hpath S C i
    · intro ψ hψ
      exact stage_restricted_fundamental_group_desc_unique O x hx hpath S C ψ hψ

/-- Helper for Theorem 2.7.5: enlarging a finite stage gives a morphism of based spaces between
the corresponding stage unions. -/
private theorem stage_union_inclusion_based_hom_w
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T) :
    (ambient_based_space (X := U[O, S]) (stage_union_basepoint O x hx S)).hom ≫
        ((toTopCat (TopCat.of X)).map
          (homOfLE (finite_intersection_closed_union_mono O hST))) =
      (ambient_based_space (X := U[O, T]) (stage_union_basepoint O x hx T)).hom := by
  -- The subtype inclusion sends the chosen stage basepoint `x` to the larger-stage basepoint `x`.
  ext u
  change (((toTopCat (TopCat.of X)).map
      (homOfLE (finite_intersection_closed_union_mono O hST))).hom)
      (stage_union_basepoint O x hx S) = stage_union_basepoint O x hx T
  simpa using stage_union_inclusion_basepoint O x hx hST

/-- Helper for Theorem 2.7.5: enlarging a finite stage gives the canonical morphism of based
spaces between the corresponding stage unions. -/
private noncomputable def stage_union_inclusion_based_hom
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T) :
    ambient_based_space (X := U[O, S]) (stage_union_basepoint O x hx S) ⟶
      ambient_based_space (X := U[O, T]) (stage_union_basepoint O x hx T) :=
  Under.homMk
    ((toTopCat (TopCat.of X)).map
      (homOfLE (finite_intersection_closed_union_mono O hST)))
    (stage_union_inclusion_based_hom_w O x hx hST)

/-- Helper for Theorem 2.7.5: on the based-space level, the literal stage leg followed by the
stage enlargement inclusion is the same subtype-inclusion square as passing through the ambient
cover member and back to the enlarged literal stage member. -/
private theorem stage_cover_to_ambient_obj_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
      ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
    stage_cover_to_ambient_obj O T iT = stage_cover_to_ambient_obj O S i := by
  cases i
  rfl

/-- Helper for Theorem 2.7.5: the shared ambient cover member underlying a literal stage member
does not depend on whether that member is viewed inside `S` or inside a larger stage `T`. -/
private theorem stage_member_enlargement_based_obj_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
      ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
    based_open_cover_member O x hx (stage_cover_to_ambient_obj O S i) =
      based_open_cover_member O x hx (stage_cover_to_ambient_obj O T iT) := by
  simpa [stage_cover_to_ambient_obj_eq O hST i] using
    congrArg (based_open_cover_member O x hx)
      (stage_cover_to_ambient_obj_eq O hST i)

/-- Helper for Theorem 2.7.5: the shared ambient group-diagram object underlying a literal stage
member does not depend on whether that member is viewed inside `S` or inside a larger stage `T`.
-/
private theorem stage_member_enlargement_obj_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
      ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
    (fundamental_group_cover_diagram O x hx).obj (stage_cover_to_ambient_obj O S i) =
      (fundamental_group_cover_diagram O x hx).obj (stage_cover_to_ambient_obj O T iT) := by
  simpa [stage_cover_to_ambient_obj_eq O hST i] using
    congrArg ((fundamental_group_cover_diagram O x hx).obj)
      (stage_cover_to_ambient_obj_eq O hST i)

/-- Helper for Theorem 2.7.5: enlarging a literal stage member gives the canonical based-space
isomorphism obtained by passing through the shared ambient cover member. -/
private noncomputable def stage_member_enlargement_based_iso
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
      ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
    based_open_cover_member
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)
        i ≅
      based_open_cover_member
        (stage_cover O T)
        (stage_union_basepoint O x hx T)
        (stage_cover_basepoint_mem O x hx T)
        iT :=
  let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
    ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
  (stage_cover_member_based_iso O x hx S i) ≪≫
    eqToIso (stage_member_enlargement_based_obj_eq O x hx hST i) ≪≫
    (stage_cover_member_based_iso O x hx T iT).symm

/-- Helper for Theorem 2.7.5: enlarging a literal stage member gives the canonical group
isomorphism obtained by passing through the shared ambient cover member. -/
private noncomputable def stage_member_enlargement_iso
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
      ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
    (fundamental_group_cover_diagram
        (stage_cover O S)
        (stage_union_basepoint O x hx S)
        (stage_cover_basepoint_mem O x hx S)).obj i ≅
    (fundamental_group_cover_diagram
        (stage_cover O T)
        (stage_union_basepoint O x hx T)
        (stage_cover_basepoint_mem O x hx T)).obj iT :=
  fundamentalGroupFunctor.mapIso (stage_member_enlargement_based_iso O x hx hST i)

/-- Helper for Theorem 2.7.5: on the based-space level, the literal stage leg followed by the
stage enlargement inclusion is the same subtype-inclusion square as passing through the enlarged
literal stage member. -/
private theorem stage_union_inclusion_cover_leg_based_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
      ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
    (based_open_cover_cocone
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
          (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
        stage_union_inclusion_based_hom O x hx hST =
      (stage_member_enlargement_based_iso O x hx hST i).hom ≫
        (based_open_cover_cocone
          (stage_cover O T)
          (stage_union_basepoint O x hx T)
          (stage_cover_basepoint_mem O x hx T)).ι.app iT := by
  -- Both composites are the same ambient subtype inclusion on the underlying point.
  ext y
  rfl

/-- Helper for Theorem 2.7.5: after applying `fundamentalGroupFunctor`, the memberwise stage leg
comparison becomes the exact group-level equality needed for stage enlargement. -/
private theorem stage_union_inclusion_cover_leg_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
      ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
    (fundamental_group_cover_cocone
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
          (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
        stage_union_inclusion_hom O x hx hST =
      (stage_member_enlargement_iso O x hx hST i).hom ≫
    (fundamental_group_cover_cocone
          (stage_cover O T)
          (stage_union_basepoint O x hx T)
          (stage_cover_basepoint_mem O x hx T)).ι.app iT := by
  let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
    ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
  -- Push the based-space enlargement square through `fundamentalGroupFunctor`.
  have hmap := congrArg fundamentalGroupFunctor.map
    (stage_union_inclusion_cover_leg_based_eq O x hx hST i)
  have hsplit_left :
      fundamentalGroupFunctor.map
          ((based_open_cover_cocone
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
            stage_union_inclusion_based_hom O x hx hST) =
        fundamentalGroupFunctor.map
          ((based_open_cover_cocone
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).ι.app i) ≫
          fundamentalGroupFunctor.map (stage_union_inclusion_based_hom O x hx hST) := by
    exact Functor.map_comp _ _ _
  have hsplit_right :
      fundamentalGroupFunctor.map
          ((stage_member_enlargement_based_iso O x hx hST i).hom ≫
            (based_open_cover_cocone
              (stage_cover O T)
              (stage_union_basepoint O x hx T)
              (stage_cover_basepoint_mem O x hx T)).ι.app iT) =
        fundamentalGroupFunctor.map (stage_member_enlargement_based_iso O x hx hST i).hom ≫
          fundamentalGroupFunctor.map
            ((based_open_cover_cocone
                (stage_cover O T)
                (stage_union_basepoint O x hx T)
                (stage_cover_basepoint_mem O x hx T)).ι.app iT) := by
    exact Functor.map_comp _ _ _
  have hmap' :
      fundamentalGroupFunctor.map
          ((based_open_cover_cocone
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).ι.app i) ≫
        fundamentalGroupFunctor.map (stage_union_inclusion_based_hom O x hx hST) =
      fundamentalGroupFunctor.map (stage_member_enlargement_based_iso O x hx hST i).hom ≫
        fundamentalGroupFunctor.map
          ((based_open_cover_cocone
              (stage_cover O T)
              (stage_union_basepoint O x hx T)
              (stage_cover_basepoint_mem O x hx T)).ι.app iT) :=
    hsplit_left.symm.trans (hmap.trans hsplit_right)
  -- Finally rewrite the mapped pieces back to the literal group-level cocone legs.
  simpa [fundamental_group_cover_cocone, stage_union_inclusion_hom,
    stage_union_inclusion_based_hom, stage_member_enlargement_iso] using hmap'

/-- Helper for Theorem 2.7.5: after restricting an ambient cocone to two finite stages, the
memberwise enlargement isomorphism followed by the larger-stage ambient leg is exactly the
smaller-stage ambient leg. -/
private theorem stage_member_enlargement_ambient_leg_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (C : Cocone (fundamental_group_cover_diagram O x hx))
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
      ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
    (stage_member_enlargement_iso O x hx hST i).hom ≫
        (stage_group_cocone_of_ambient_cocone O x hx C T).ι.app iT =
      (stage_group_cocone_of_ambient_cocone O x hx C S).ι.app i := by
  let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
    ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
  -- Unfold both ambient stage legs and cancel the common ambient comparison through the shared
  -- cover member underlying `i`.
  simp only [stage_group_cocone_of_ambient_cocone, Category.assoc]
  calc
    fundamentalGroupFunctor.map
          ((stage_cover_member_based_iso O x hx S i).hom ≫
            (stage_cover_member_based_iso O x hx T iT).inv) ≫
        fundamentalGroupFunctor.map (stage_cover_member_based_iso O x hx T iT).hom ≫
          C.ι.app (stage_cover_to_ambient_obj O T iT)
        =
      fundamentalGroupFunctor.map (stage_cover_member_based_iso O x hx S i).hom ≫
          C.ι.app (stage_cover_to_ambient_obj O T iT) := by
            rw [Functor.map_comp]
            simp [Category.assoc]
    _ =
      fundamentalGroupFunctor.map (stage_cover_member_based_iso O x hx S i).hom ≫
          C.ι.app (stage_cover_to_ambient_obj O S i) := by
            simpa [iT] using congrArg
              (fun j ↦
                fundamentalGroupFunctor.map (stage_cover_member_based_iso O x hx S i).hom ≫
                  C.ι.app j)
              (stage_cover_to_ambient_obj_eq O hST i)

/-- Helper for Theorem 2.7.5: the descended finite-stage morphisms are compatible under stage
enlargement. -/
private theorem finite_stage_desc_compatible_of_le
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (C : Cocone (fundamental_group_cover_diagram O x hx)) :
    stage_restricted_fundamental_group_desc O x hx hpath S
        (stage_group_cocone_of_ambient_cocone O x hx C S) =
      stage_union_inclusion_hom O x hx hST ≫
        stage_restricted_fundamental_group_desc O x hx hpath T
          (stage_group_cocone_of_ambient_cocone O x hx C T) := by
  -- Apply uniqueness on the smaller stage to the candidate obtained by enlarging to `T`.
  symm
  refine stage_restricted_fundamental_group_desc_unique O x hx hpath S
    (stage_group_cocone_of_ambient_cocone O x hx C S)
    (stage_union_inclusion_hom O x hx hST ≫
      stage_restricted_fundamental_group_desc O x hx hpath T
        (stage_group_cocone_of_ambient_cocone O x hx C T)) ?_
  intro i
  let iT : TopologicalSpace.IsOpenCover.Index (stage_cover O T) :=
    ⟨((show ↥(S : Finset ι) from i) : ι), hST i.2⟩
  -- Rewrite the smaller-stage leg through the enlargement square and then use the stage-`T`
  -- factorization formula.
  have hcompare :
      (fundamental_group_cover_cocone
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
          (stage_union_inclusion_hom O x hx hST ≫
            stage_restricted_fundamental_group_desc O x hx hpath T
              (stage_group_cocone_of_ambient_cocone O x hx C T)) =
        (stage_member_enlargement_iso O x hx hST i).hom ≫
          ((fundamental_group_cover_cocone
              (stage_cover O T)
              (stage_union_basepoint O x hx T)
              (stage_cover_basepoint_mem O x hx T)).ι.app iT ≫
            stage_restricted_fundamental_group_desc O x hx hpath T
              (stage_group_cocone_of_ambient_cocone O x hx C T)) := by
    simpa [Category.assoc, iT] using congrArg
      (fun k ↦
        k ≫ stage_restricted_fundamental_group_desc O x hx hpath T
          (stage_group_cocone_of_ambient_cocone O x hx C T))
      (stage_union_inclusion_cover_leg_eq O x hx hST i)
  have hfactor :
      (stage_member_enlargement_iso O x hx hST i).hom ≫
          ((fundamental_group_cover_cocone
              (stage_cover O T)
              (stage_union_basepoint O x hx T)
              (stage_cover_basepoint_mem O x hx T)).ι.app iT ≫
            stage_restricted_fundamental_group_desc O x hx hpath T
              (stage_group_cocone_of_ambient_cocone O x hx C T)) =
        (stage_member_enlargement_iso O x hx hST i).hom ≫
          (stage_group_cocone_of_ambient_cocone O x hx C T).ι.app iT := by
    rw [stage_restricted_fundamental_group_desc_fac O x hx hpath T
      (stage_group_cocone_of_ambient_cocone O x hx C T) iT]
    rfl
  have htarget :
      (stage_member_enlargement_iso O x hx hST i).hom ≫
          (stage_group_cocone_of_ambient_cocone O x hx C T).ι.app iT =
        (stage_group_cocone_of_ambient_cocone O x hx C S).ι.app i := by
    -- Normalize the enlargement isomorphism through the shared ambient cover member.
    simpa [iT] using
      stage_member_enlargement_ambient_leg_eq O x hx hST C i
  exact hcompare.trans (hfactor.trans htarget)

/-- Helper for Theorem 2.7.5: an ambient loop whose image lies in a finite stage can be regarded
as a loop in that stage union. -/
private noncomputable def ambient_loop_in_stage
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path x x)
    (hγ : Set.range γ ⊆ (U[O, S] : Set X)) :
    Path (stage_union_basepoint O x hx S) (stage_union_basepoint O x hx S) :=
  { toContinuousMap :=
      { toFun := fun t ↦ ⟨γ t, hγ ⟨t, rfl⟩⟩
        continuous_toFun := Continuous.subtype_mk γ.continuous fun t ↦ hγ ⟨t, rfl⟩ }
    source' := by
      -- Both endpoints are the same ambient point `x`; only the stage-membership proof changes.
      apply Subtype.ext
      simpa [stage_union_basepoint] using γ.source
    target' := by
      -- The target endpoint is handled identically.
      apply Subtype.ext
      simpa [stage_union_basepoint] using γ.target }

/-- Helper for Theorem 2.7.5: after enlarging a finite stage, the lifted ambient loop becomes the
same literal loop in the larger stage. -/
private theorem ambient_loop_in_stage_map_stage_union_inclusion
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (γ : Path x x)
    (hγS : Set.range γ ⊆ (U[O, S] : Set X))
    (hγT : Set.range γ ⊆ (U[O, T] : Set X)) :
    ((ambient_loop_in_stage O x hx S γ hγS).map
          (((toTopCat (TopCat.of X)).map
              (homOfLE (finite_intersection_closed_union_mono O hST))).hom.continuous)).cast
        (stage_union_inclusion_basepoint O x hx hST).symm
        (stage_union_inclusion_basepoint O x hx hST).symm =
      ambient_loop_in_stage O x hx T γ hγT := by
  -- Both paths have the same ambient coordinate at every time, so extensionality reduces the
  -- comparison to equality of subtype points.
  ext t
  apply Subtype.ext
  rfl

/-- Helper for Theorem 2.7.5: enlarging a finite stage sends the lifted ambient loop class to the
same ambient loop class viewed in the larger stage. -/
private theorem stage_union_inclusion_hom_apply_ambient_loop
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (γ : Path x x)
    (hγS : Set.range γ ⊆ (U[O, S] : Set X))
    (hγT : Set.range γ ⊆ (U[O, T] : Set X)) :
    (stage_union_inclusion_hom O x hx hST).hom
        (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
      FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧ := by
  let f :
      C(U[O, S], U[O, T]) :=
    ((toTopCat (TopCat.of X)).map
      (homOfLE (finite_intersection_closed_union_mono O hST))).hom
  have hraw :=
    FundamentalGroup.mapOfEq_apply
      (f := f)
      (h := stage_union_inclusion_basepoint O x hx hST)
      (p := ambient_loop_in_stage O x hx S γ hγS)
  have hnorm :
      FundamentalGroup.fromPath
          ⟦((ambient_loop_in_stage O x hx S γ hγS).map f.continuous).cast
              (stage_union_inclusion_basepoint O x hx hST).symm
              (stage_union_inclusion_basepoint O x hx hST).symm⟧ =
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧ := by
    -- Normalize the mapped loop to the literal larger-stage lift.
    exact congrArg FundamentalGroup.fromPath <|
      congrArg Path.Homotopic.Quotient.mk <|
        ambient_loop_in_stage_map_stage_union_inclusion O x hx hST γ hγS hγT
  -- Apply `mapOfEq_apply`, then rewrite the mapped loop into the larger-stage literal lift.
  simpa [stage_union_inclusion_hom, f] using hraw.trans hnorm

/-- Helper for Theorem 2.7.5: evaluating one ambient loop in two different finite stages gives
the same result after passing to a common refinement. -/
private theorem ambient_stage_value_eq_of_common_refinement
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (C : Cocone (fundamental_group_cover_diagram O x hx))
    (γ : Path x x)
    {S T : intersection_closed_subcover_index O}
    (hγS : Set.range γ ⊆ (U[O, S] : Set X))
    (hγT : Set.range γ ⊆ (U[O, T] : Set X)) :
    (stage_restricted_fundamental_group_desc O x hx hpath S
          (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
        (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
      (stage_restricted_fundamental_group_desc O x hx hpath T
          (stage_group_cocone_of_ambient_cocone O x hx C T)).hom
        (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧) := by
  classical
  have hST_nonempty : (((S : Finset ι) ∪ (T : Finset ι)) : Finset ι).Nonempty := by
    rcases S.2.1 with ⟨i, hi⟩
    exact ⟨i, Finset.mem_union.mpr (Or.inl hi)⟩
  obtain ⟨R, hR⟩ :=
    exists_intersection_closed_finset_superset O hinter ((S : Finset ι) ∪ (T : Finset ι))
      hST_nonempty
  have hSR : S ≤ R := fun i hi ↦ hR (Finset.mem_union.mpr (Or.inl hi))
  have hTR : T ≤ R := fun i hi ↦ hR (Finset.mem_union.mpr (Or.inr hi))
  have hγR_fromS : Set.range γ ⊆ (U[O, R] : Set X) := by
    intro y hy
    exact finite_intersection_closed_union_mono O hSR (hγS hy)
  have hγR_fromT : Set.range γ ⊆ (U[O, R] : Set X) := by
    intro y hy
    exact finite_intersection_closed_union_mono O hTR (hγT hy)
  have hS_to_R :
      (stage_restricted_fundamental_group_desc O x hx hpath S
            (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
        (stage_restricted_fundamental_group_desc O x hx hpath R
            (stage_group_cocone_of_ambient_cocone O x hx C R)).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx R γ hγR_fromS⟧) := by
    -- First compare the descended morphisms under enlargement, then normalize the mapped loop.
    have h :=
      congrArg
        (fun k ↦
          k.hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧))
        (finite_stage_desc_compatible_of_le O x hx hpath hSR C)
    change
      (stage_restricted_fundamental_group_desc O x hx hpath S
            (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
        (stage_restricted_fundamental_group_desc O x hx hpath R
            (stage_group_cocone_of_ambient_cocone O x hx C R)).hom
          ((stage_union_inclusion_hom O x hx hSR).hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧)) at h
    exact h.trans <|
      congrArg
        (fun z ↦
          (stage_restricted_fundamental_group_desc O x hx hpath R
              (stage_group_cocone_of_ambient_cocone O x hx C R)).hom z)
        (stage_union_inclusion_hom_apply_ambient_loop O x hx hSR γ hγS hγR_fromS)
  have hT_to_R :
      (stage_restricted_fundamental_group_desc O x hx hpath T
            (stage_group_cocone_of_ambient_cocone O x hx C T)).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧) =
        (stage_restricted_fundamental_group_desc O x hx hpath R
            (stage_group_cocone_of_ambient_cocone O x hx C R)).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx R γ hγR_fromT⟧) := by
    -- The same enlargement argument applies from `T` to the common refinement `R`.
    have h :=
      congrArg
        (fun k ↦
          k.hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧))
        (finite_stage_desc_compatible_of_le O x hx hpath hTR C)
    change
      (stage_restricted_fundamental_group_desc O x hx hpath T
            (stage_group_cocone_of_ambient_cocone O x hx C T)).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧) =
        (stage_restricted_fundamental_group_desc O x hx hpath R
            (stage_group_cocone_of_ambient_cocone O x hx C R)).hom
          ((stage_union_inclusion_hom O x hx hTR).hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧)) at h
    exact h.trans <|
      congrArg
        (fun z ↦
          (stage_restricted_fundamental_group_desc O x hx hpath R
              (stage_group_cocone_of_ambient_cocone O x hx C R)).hom z)
        (stage_union_inclusion_hom_apply_ambient_loop O x hx hTR γ hγT hγR_fromT)
  -- Both stage evaluations agree with the common-refinement evaluation, so they agree with each
  -- other as well.
  exact hS_to_R.trans hT_to_R.symm

/-- Helper for Theorem 2.7.5: if a loop homotopy stays inside one finite stage, then the source
loop already stays inside that stage. -/
private theorem path_range_subset_of_homotopy_source
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁)
    (hH : Set.range H ⊆ (U[O, S] : Set X)) :
    Set.range γ₀ ⊆ (U[O, S] : Set X) := by
  -- Evaluate the homotopy on the left edge of the square to recover the source loop.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact hH ⟨(0, t), by simpa using H.map_zero_left t⟩

/-- Helper for Theorem 2.7.5: if a loop homotopy stays inside one finite stage, then the target
loop already stays inside that stage. -/
private theorem path_range_subset_of_homotopy_target
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁)
    (hH : Set.range H ⊆ (U[O, S] : Set X)) :
    Set.range γ₁ ⊆ (U[O, S] : Set X) := by
  -- Evaluate the homotopy on the right edge of the square to recover the target loop.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact hH ⟨(1, t), by simpa using H.map_one_left t⟩

/-- Helper for Theorem 2.7.5: if two loops both stay inside one finite stage, then their
concatenation stays inside that stage as well. -/
private theorem path_trans_range_subset
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O)
    {x : X} {γ δ : Path x x}
    (hδ : Set.range δ ⊆ (U[O, S] : Set X))
    (hγ : Set.range γ ⊆ (U[O, S] : Set X)) :
    Set.range (δ.trans γ) ⊆ (U[O, S] : Set X) := by
  -- Split the concatenated loop at time `1 / 2` and appeal to the corresponding stage
  -- containment of each factor.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  rw [Path.trans_apply]
  split_ifs with ht
  · exact hδ ⟨⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, rfl⟩
  · exact hγ
      ⟨⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, rfl⟩

/-- Helper for Theorem 2.7.5: a loop homotopy that stays in one finite stage lifts to a literal
loop homotopy in that stage union. -/
private noncomputable def ambient_loop_homotopy_in_stage
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁)
    (hH : Set.range H ⊆ (U[O, S] : Set X)) :
    (ambient_loop_in_stage O x hx S γ₀
        (path_range_subset_of_homotopy_source O S H hH)).Homotopy
      (ambient_loop_in_stage O x hx S γ₁
        (path_range_subset_of_homotopy_target O S H hH)) := by
  -- Lift the ambient homotopy pointwise into the stage subtype.
  refine
    { toContinuousMap :=
        { toFun := fun p ↦ ⟨H p, hH ⟨p, rfl⟩⟩
          continuous_toFun := Continuous.subtype_mk H.continuous fun p ↦ hH ⟨p, rfl⟩ }
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro t
    -- On the left edge we recover the lifted source loop.
    apply Subtype.ext
    simpa [ambient_loop_in_stage] using H.map_zero_left t
  · intro t
    -- On the right edge we recover the lifted target loop.
    apply Subtype.ext
    simpa [ambient_loop_in_stage] using H.map_one_left t
  · intro t y hy
    -- Along the top and bottom edges the ambient homotopy stays at the common basepoint.
    apply Subtype.ext
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using H.prop t y hy

/-- Helper for Theorem 2.7.5: lifting an ambient concatenation into one finite stage agrees with
concatenating the two lifted stage loops. -/
private theorem ambient_loop_in_stage_trans
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ δ : Path x x)
    (hγ : Set.range γ ⊆ (U[O, S] : Set X))
    (hδ : Set.range δ ⊆ (U[O, S] : Set X)) :
    ambient_loop_in_stage O x hx S (δ.trans γ) (path_trans_range_subset O S hδ hγ) =
      (ambient_loop_in_stage O x hx S δ hδ).trans
        (ambient_loop_in_stage O x hx S γ hγ) := by
  -- Both paths have the same ambient coordinate at every time, so pointwise extensionality is
  -- enough after expanding the concatenation formula.
  ext t
  change
    (δ.trans γ) t =
      (((ambient_loop_in_stage O x hx S δ hδ).trans
          (ambient_loop_in_stage O x hx S γ hγ)) t).1
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- Helper for Theorem 2.7.5: once two ambient loops already live in one finite stage, the
descended stage value of their product is computed inside that single stage. -/
private theorem ambient_stage_value_mul_of_common_stage
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (C : Cocone (fundamental_group_cover_diagram O x hx))
    (S : intersection_closed_subcover_index O)
    (γ δ : Path x x)
    (hγ : Set.range γ ⊆ (U[O, S] : Set X))
    (hδ : Set.range δ ⊆ (U[O, S] : Set X)) :
    (stage_restricted_fundamental_group_desc O x hx hpath S
          (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
        (FundamentalGroup.fromPath
          ⟦ambient_loop_in_stage O x hx S (δ.trans γ) (path_trans_range_subset O S hδ hγ)⟧) =
      ((stage_restricted_fundamental_group_desc O x hx hpath S
            (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧)) *
        ((stage_restricted_fundamental_group_desc O x hx hpath S
              (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S δ hδ⟧)) := by
  -- Normalize the lifted concatenation to a product in the stage fundamental group, then use the
  -- multiplicativity of the descended stage morphism.
  have hloop :
      FundamentalGroup.fromPath
          ⟦ambient_loop_in_stage O x hx S (δ.trans γ) (path_trans_range_subset O S hδ hγ)⟧ =
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧ *
          FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S δ hδ⟧ := by
    rw [ambient_loop_in_stage_trans O x hx S γ δ hγ hδ]
    change FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.trans
          ⟦ambient_loop_in_stage O x hx S δ hδ⟧
          ⟦ambient_loop_in_stage O x hx S γ hγ⟧) =
      _
    change FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧ *
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S δ hδ⟧ =
      _
    rfl
  exact (congrArg
      (fun q ↦
        (stage_restricted_fundamental_group_desc O x hx hpath S
            (stage_group_cocone_of_ambient_cocone O x hx C S)).hom q)
      hloop).trans (MonoidHom.map_mul _ _ _)

/-- Helper for Theorem 2.7.5: stage reduction defines a well-defined ambient group morphism, and
its value on any loop can be computed in every finite stage containing that loop. -/
private theorem ambient_desc_well_defined_of_stage_reduction
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (C : Cocone (fundamental_group_cover_diagram O x hx)) :
    ∃ φ : FundamentalGroup X x →* C.pt,
      ∀ (γ : Path x x) (S : intersection_closed_subcover_index O)
        (hγ : Set.range γ ⊆ (U[O, S] : Set X)),
        φ (FundamentalGroup.fromPath ⟦γ⟧) =
          (stage_restricted_fundamental_group_desc O x hx hpath S
              (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧) := by
  classical
  let chosen_stage : Path x x → intersection_closed_subcover_index O := fun γ ↦
    Classical.choose (path_image_subset_finite_intersection_closed_union O hO hinter γ)
  let chosen_stage_mem : ∀ γ : Path x x, Set.range γ ⊆ (U[O, chosen_stage γ] : Set X) := fun γ ↦
    Classical.choose_spec (path_image_subset_finite_intersection_closed_union O hO hinter γ)
  let stage_value :
      (γ : Path x x) →
        (S : intersection_closed_subcover_index O) →
          Set.range γ ⊆ (U[O, S] : Set X) → C.pt := fun γ S hγ ↦
    (stage_restricted_fundamental_group_desc O x hx hpath S
        (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
      (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧)
  let raw_value : Path x x → C.pt := fun γ ↦
    stage_value γ (chosen_stage γ) (chosen_stage_mem γ)
  have raw_value_spec :
      ∀ (γ : Path x x) (S : intersection_closed_subcover_index O)
        (hγ : Set.range γ ⊆ (U[O, S] : Set X)),
        raw_value γ = stage_value γ S hγ := by
    -- The common-refinement comparison makes the chosen stage irrelevant.
    intro γ S hγ
    exact ambient_stage_value_eq_of_common_refinement O x hx hpath hinter C γ
      (chosen_stage_mem γ) hγ
  have raw_value_respects :
      ∀ {γ₀ γ₁ : Path x x}, γ₀.Homotopic γ₁ → raw_value γ₀ = raw_value γ₁ := by
    intro γ₀ γ₁ hγ
    rcases hγ with ⟨H⟩
    obtain ⟨S, hH⟩ := homotopy_image_subset_finite_intersection_closed_union O hO hinter H
    have hγ₀ : Set.range γ₀ ⊆ (U[O, S] : Set X) :=
      path_range_subset_of_homotopy_source O S H hH
    have hγ₁ : Set.range γ₁ ⊆ (U[O, S] : Set X) :=
      path_range_subset_of_homotopy_target O S H hH
    have hquot :
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ₀ hγ₀⟧ =
          FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ₁ hγ₁⟧ := by
      -- Lift the ambient homotopy to the stage and descend it to the quotient.
      apply congrArg FundamentalGroup.fromPath
      exact Quotient.sound ⟨ambient_loop_homotopy_in_stage O x hx S H hH⟩
    calc
      raw_value γ₀ = stage_value γ₀ S hγ₀ := raw_value_spec γ₀ S hγ₀
      _ = stage_value γ₁ S hγ₁ := by
            simpa [stage_value] using congrArg
              (fun q ↦
                (stage_restricted_fundamental_group_desc O x hx hpath S
                    (stage_group_cocone_of_ambient_cocone O x hx C S)).hom q)
              hquot
      _ = raw_value γ₁ := (raw_value_spec γ₁ S hγ₁).symm
  refine ⟨
    { toFun := fun q ↦ Quotient.liftOn q raw_value fun _ _ h ↦ raw_value_respects h
      map_one' := ?_
      map_mul' := ?_ }, ?_⟩
  · -- Evaluate the ambient descendant on the constant loop inside any finite stage that contains
    -- the basepoint.
    obtain ⟨S, hS⟩ :=
      path_image_subset_finite_intersection_closed_union O hO hinter (Path.refl x)
    have href :
        ambient_loop_in_stage O x hx S (Path.refl x) hS =
          Path.refl (stage_union_basepoint O x hx S) := by
      ext t
      rfl
    calc
      Quotient.liftOn (1 : FundamentalGroup X x) raw_value
          (fun _ _ h ↦ raw_value_respects h)
          =
        raw_value (Path.refl x) := by
            rfl
      _ = stage_value (Path.refl x) S hS := raw_value_spec (Path.refl x) S hS
      _ = 1 := by
            change
              (stage_restricted_fundamental_group_desc O x hx hpath S
                    (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
                  (FundamentalGroup.fromPath ⟦Path.refl (stage_union_basepoint O x hx S)⟧) = 1
            change
              (stage_restricted_fundamental_group_desc O x hx hpath S
                    (stage_group_cocone_of_ambient_cocone O x hx C S)).hom 1 = 1
            simpa using
              (stage_restricted_fundamental_group_desc O x hx hpath S
                (stage_group_cocone_of_ambient_cocone O x hx C S)).hom.map_one
  · intro a b
    induction a using Path.Homotopic.Quotient.ind with
    | mk γ =>
        induction b using Path.Homotopic.Quotient.ind with
        | mk δ =>
            -- Put the two representative loops into a common finite stage and compute there.
            obtain ⟨Sγ, hγ⟩ := path_image_subset_finite_intersection_closed_union O hO hinter γ
            obtain ⟨Sδ, hδ⟩ := path_image_subset_finite_intersection_closed_union O hO hinter δ
            have hS_nonempty : (((Sγ : Finset ι) ∪ (Sδ : Finset ι)) : Finset ι).Nonempty := by
              rcases Sγ.2.1 with ⟨i, hi⟩
              exact ⟨i, Finset.mem_union.mpr (Or.inl hi)⟩
            obtain ⟨R, hR⟩ :=
              exists_intersection_closed_finset_superset O hinter
                ((Sγ : Finset ι) ∪ (Sδ : Finset ι)) hS_nonempty
            have hγR : Set.range γ ⊆ (U[O, R] : Set X) := by
              intro y hy
              exact finite_intersection_closed_union_mono O
                (fun i hi ↦ hR (Finset.mem_union.mpr (Or.inl hi))) (hγ hy)
            have hδR : Set.range δ ⊆ (U[O, R] : Set X) := by
              intro y hy
              exact finite_intersection_closed_union_mono O
                (fun i hi ↦ hR (Finset.mem_union.mpr (Or.inr hi))) (hδ hy)
            change raw_value (δ.trans γ) = raw_value γ * raw_value δ
            calc
              raw_value (δ.trans γ) =
                  stage_value (δ.trans γ) R (path_trans_range_subset O R hδR hγR) :=
                raw_value_spec (δ.trans γ) R (path_trans_range_subset O R hδR hγR)
              _ = stage_value γ R hγR * stage_value δ R hδR := by
                    simpa [stage_value] using
                      ambient_stage_value_mul_of_common_stage O x hx hpath C R γ δ hγR hδR
              _ = raw_value γ * raw_value δ := by
                    rw [raw_value_spec γ R hγR, raw_value_spec δ R hδR]
  · intro γ S hγ
    -- The quotient lift agrees with the raw representative evaluator on a concrete loop.
    exact raw_value_spec γ S hγ

/-- Helper for Theorem 2.7.5: choose the ambient descendant produced by finite-stage reduction. -/
private noncomputable def ambient_desc_of_stage_reduction
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (C : Cocone (fundamental_group_cover_diagram O x hx)) :
    FundamentalGroup X x →* C.pt :=
  Classical.choose (ambient_desc_well_defined_of_stage_reduction O hO x hx hpath hinter C)

/-- Helper for Theorem 2.7.5: the chosen ambient descendant is computed by evaluating any loop in
any finite stage that contains its image. -/
private theorem ambient_desc_of_stage_reduction_spec
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (C : Cocone (fundamental_group_cover_diagram O x hx))
    (γ : Path x x)
    (S : intersection_closed_subcover_index O)
    (hγ : Set.range γ ⊆ (U[O, S] : Set X)) :
    ambient_desc_of_stage_reduction O hO x hx hpath hinter C
        (FundamentalGroup.fromPath ⟦γ⟧) =
      (stage_restricted_fundamental_group_desc O x hx hpath S
          (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
        (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧) :=
  Classical.choose_spec (ambient_desc_well_defined_of_stage_reduction O hO x hx hpath hinter C)
    γ S hγ

/-- Helper for Theorem 2.7.5: the inclusion of a finite stage union into `X` preserves the chosen
common basepoint. -/
private theorem stage_union_to_ambient_basepoint
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O) :
    (inclusion' U[O, S]).hom (stage_union_basepoint O x hx S) = x := by
  -- The stage-union inclusion forgets the subtype proof and keeps the underlying point `x`.
  rfl

/-- Helper for Theorem 2.7.5: the inclusion of a finite stage union into `X` gives the canonical
map on fundamental groups. -/
private theorem stage_union_to_ambient_based_hom_w
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O) :
    (ambient_based_space (X := U[O, S]) (stage_union_basepoint O x hx S)).hom ≫
        inclusion' U[O, S] =
      (ambient_based_space x).hom := by
  -- The stage-union inclusion sends the chosen stage basepoint to the ambient basepoint `x`.
  ext u
  change (inclusion' U[O, S]).hom (stage_union_basepoint O x hx S) = x
  simpa using stage_union_to_ambient_basepoint O x hx S

/-- Helper for Theorem 2.7.5: the inclusion of a finite stage union into `X` gives the canonical
based-space morphism. -/
private noncomputable def stage_union_to_ambient_based_hom
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O) :
    ambient_based_space (X := U[O, S]) (stage_union_basepoint O x hx S) ⟶
      ambient_based_space x :=
  Under.homMk (inclusion' U[O, S]) (stage_union_to_ambient_based_hom_w O x hx S)

/-- Helper for Theorem 2.7.5: the inclusion of a finite stage union into `X` gives the canonical
map on fundamental groups. -/
private noncomputable abbrev stage_union_to_ambient_hom
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O) :
    GrpCat.of (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) ⟶
      GrpCat.of (FundamentalGroup X x) :=
  GrpCat.ofHom <|
    FundamentalGroup.mapOfEq (inclusion' U[O, S]).hom
      (stage_union_to_ambient_basepoint O x hx S)

/-- Helper for Theorem 2.7.5: on the based-space level, restricting a cover member to a literal
finite stage and then including that stage union into `X` is the same map as the ambient cover
leg through the matching ambient cover member. -/
private theorem stage_union_to_ambient_cover_leg_based_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    (based_open_cover_cocone
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
          (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
        stage_union_to_ambient_based_hom O x hx S =
      (stage_cover_member_based_iso O x hx S i).hom ≫
        (based_open_cover_cocone O x hx).ι.app (stage_cover_to_ambient_obj O S i) := by
  -- Both composites are the same subtype inclusion from the literal stage member into `X`.
  ext y
  rfl

/-- Helper for Theorem 2.7.5: after applying `fundamentalGroupFunctor`, the stage-union inclusion
turns the literal stage cover leg into the corresponding ambient cover leg. -/
private theorem stage_union_to_ambient_cover_leg_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (i : TopologicalSpace.IsOpenCover.Index (stage_cover O S)) :
    (fundamental_group_cover_cocone
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
          (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
        stage_union_to_ambient_hom O x hx S =
      (stage_member_fundamental_group_iso O x hx S i).hom ≫
        (fundamental_group_cover_cocone O x hx).ι.app (stage_cover_to_ambient_obj O S i) := by
  -- Push the based-space equality through `fundamentalGroupFunctor` and rewrite the pieces back
  -- to the literal group-level morphisms.
  have hmap := congrArg fundamentalGroupFunctor.map
    (stage_union_to_ambient_cover_leg_based_eq O x hx S i)
  have hsplit_left :
      fundamentalGroupFunctor.map
          ((based_open_cover_cocone
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
            stage_union_to_ambient_based_hom O x hx S) =
        fundamentalGroupFunctor.map
          ((based_open_cover_cocone
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).ι.app i) ≫
          fundamentalGroupFunctor.map
            (stage_union_to_ambient_based_hom O x hx S) := by
    exact Functor.map_comp _ _ _
  have hsplit_right :
      fundamentalGroupFunctor.map
          ((stage_cover_member_based_iso O x hx S i).hom ≫
            (based_open_cover_cocone O x hx).ι.app (stage_cover_to_ambient_obj O S i)) =
        fundamentalGroupFunctor.map (stage_cover_member_based_iso O x hx S i).hom ≫
          fundamentalGroupFunctor.map
            ((based_open_cover_cocone O x hx).ι.app (stage_cover_to_ambient_obj O S i)) := by
    exact Functor.map_comp _ _ _
  have hmap' :
      fundamentalGroupFunctor.map
          ((based_open_cover_cocone
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).ι.app i) ≫
        fundamentalGroupFunctor.map
            (stage_union_to_ambient_based_hom O x hx S) =
      fundamentalGroupFunctor.map (stage_cover_member_based_iso O x hx S i).hom ≫
        fundamentalGroupFunctor.map
          ((based_open_cover_cocone O x hx).ι.app (stage_cover_to_ambient_obj O S i)) :=
    hsplit_left.symm.trans (hmap.trans hsplit_right)
  simpa [fundamental_group_cover_cocone, stage_union_to_ambient_hom,
    stage_union_to_ambient_based_hom] using hmap'

/-- Helper for Theorem 2.7.5: the ambient image of a loop in a finite stage still lies in that
same stage union. -/
private theorem stage_loop_range_subset
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path (stage_union_basepoint O x hx S) (stage_union_basepoint O x hx S)) :
    Set.range (γ.map continuous_subtype_val) ⊆ (U[O, S] : Set X) := by
  -- Every point of the mapped loop comes from a point of the stage-union subtype.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact (γ t).2

/-- Helper for Theorem 2.7.5: lifting the ambient image of a literal stage loop back into the
same stage recovers the original stage loop. -/
private theorem ambient_loop_in_stage_of_stage_loop
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path (stage_union_basepoint O x hx S) (stage_union_basepoint O x hx S)) :
    ambient_loop_in_stage O x hx S
        (γ.map continuous_subtype_val)
        (stage_loop_range_subset O x hx S γ) =
      γ := by
  -- Both loops have the same stage-valued coordinate at every time.
  ext t
  rfl

/-- Helper for Theorem 2.7.5: the finite-stage inclusion sends a literal stage loop class to the
class of the same loop viewed in `X`. -/
private theorem stage_union_to_ambient_hom_apply_stage_loop
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path (stage_union_basepoint O x hx S) (stage_union_basepoint O x hx S)) :
    (stage_union_to_ambient_hom O x hx S).hom (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath ⟦γ.map continuous_subtype_val⟧ := by
  -- Apply `mapOfEq_apply`, then normalize the mapped literal stage loop to the ambient path.
  have hraw :=
    FundamentalGroup.mapOfEq_apply
      (f := (inclusion' U[O, S]).hom)
      (h := stage_union_to_ambient_basepoint O x hx S)
      (p := γ)
  have hnorm :
      FundamentalGroup.fromPath
          ⟦((γ.map (inclusion' U[O, S]).hom.continuous).cast
              (stage_union_to_ambient_basepoint O x hx S).symm
              (stage_union_to_ambient_basepoint O x hx S).symm)⟧ =
        FundamentalGroup.fromPath ⟦γ.map continuous_subtype_val⟧ := by
    -- Mapping the literal stage loop to `X` is exactly the ambient coordinate path.
    exact congrArg FundamentalGroup.fromPath <|
      congrArg Path.Homotopic.Quotient.mk <| by
        ext t
        rfl
  simpa [stage_union_to_ambient_hom] using hraw.trans hnorm

/-- Helper for Theorem 2.7.5: the finite-stage inclusion sends the lifted ambient loop class back
to the original ambient loop class. -/
private theorem stage_union_to_ambient_hom_apply_ambient_loop
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path x x)
    (hγ : Set.range γ ⊆ (U[O, S] : Set X)) :
    (stage_union_to_ambient_hom O x hx S).hom
        (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧) =
      FundamentalGroup.fromPath ⟦γ⟧ := by
  -- Apply `mapOfEq_apply`, then observe that forgetting the stage subtype recovers `γ`.
  have hraw :=
    FundamentalGroup.mapOfEq_apply
      (f := (inclusion' U[O, S]).hom)
      (h := stage_union_to_ambient_basepoint O x hx S)
      (p := ambient_loop_in_stage O x hx S γ hγ)
  have hnorm :
      FundamentalGroup.fromPath
          ⟦(((ambient_loop_in_stage O x hx S γ hγ).map
                (inclusion' U[O, S]).hom.continuous).cast
              (stage_union_to_ambient_basepoint O x hx S).symm
              (stage_union_to_ambient_basepoint O x hx S).symm)⟧ =
        FundamentalGroup.fromPath ⟦γ⟧ := by
    -- The lifted stage loop has ambient coordinate path exactly equal to the original loop.
    exact congrArg FundamentalGroup.fromPath <|
      congrArg Path.Homotopic.Quotient.mk <| by
        ext t
        rfl
  simpa [stage_union_to_ambient_hom] using hraw.trans hnorm

/-- Helper for Theorem 2.7.5: restricting the ambient descendant to any finite stage recovers the
canonical finite-stage descended morphism. -/
private noncomputable abbrev ambient_desc_of_stage_reduction_hom
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (C : Cocone (fundamental_group_cover_diagram O x hx)) :
    (fundamental_group_cover_cocone O x hx).pt ⟶ C.pt :=
  GrpCat.ofHom (ambient_desc_of_stage_reduction O hO x hx hpath hinter C)

/-- Helper for Theorem 2.7.5: restricting the ambient descendant to any finite stage recovers the
canonical finite-stage descended morphism. -/
private theorem ambient_desc_restricts_to_stage
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (C : Cocone (fundamental_group_cover_diagram O x hx))
    (S : intersection_closed_subcover_index O) :
    stage_union_to_ambient_hom O x hx S ≫
        ambient_desc_of_stage_reduction_hom O hO x hx hpath hinter C =
      stage_restricted_fundamental_group_desc O x hx hpath S
        (stage_group_cocone_of_ambient_cocone O x hx C S) := by
  -- Compare both stage-union morphisms on a representative loop in the finite stage.
  ext g
  induction g using Path.Homotopic.Quotient.ind with
  | mk γ =>
      calc
        ambient_desc_of_stage_reduction O hO x hx hpath hinter C
            ((stage_union_to_ambient_hom O x hx S).hom
              (FundamentalGroup.fromPath ⟦γ⟧)) =
          ambient_desc_of_stage_reduction O hO x hx hpath hinter C
            (FundamentalGroup.fromPath ⟦γ.map continuous_subtype_val⟧) := by
              rw [stage_union_to_ambient_hom_apply_stage_loop O x hx S γ]
        _ =
          (stage_restricted_fundamental_group_desc O x hx hpath S
              (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
            (FundamentalGroup.fromPath
              ⟦ambient_loop_in_stage O x hx S
                  (γ.map continuous_subtype_val)
                  (stage_loop_range_subset O x hx S γ)⟧) := by
                exact ambient_desc_of_stage_reduction_spec O hO x hx hpath hinter C
                  (γ.map continuous_subtype_val) S (stage_loop_range_subset O x hx S γ)
        _ =
          (stage_restricted_fundamental_group_desc O x hx hpath S
              (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
            (FundamentalGroup.fromPath ⟦γ⟧) := by
                simpa using congrArg
                  (fun q ↦
                    (stage_restricted_fundamental_group_desc O x hx hpath S
                        (stage_group_cocone_of_ambient_cocone O x hx C S)).hom
                      (FundamentalGroup.fromPath q))
                  (congrArg Path.Homotopic.Quotient.mk <|
                    ambient_loop_in_stage_of_stage_loop O x hx S γ)

/-- Helper for Theorem 2.7.5: every ambient factorization restricts on each finite stage to the
canonical finite-stage descended morphism. -/
private theorem restricted_stage_desc_of_ambient_factor
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (C : Cocone (fundamental_group_cover_diagram O x hx))
    (ψ : (fundamental_group_cover_cocone O x hx).pt ⟶ C.pt)
    (hψ : ∀ j, (fundamental_group_cover_cocone O x hx).ι.app j ≫ ψ = C.ι.app j)
    (S : intersection_closed_subcover_index O) :
    stage_union_to_ambient_hom O x hx S ≫ ψ =
      stage_restricted_fundamental_group_desc O x hx hpath S
        (stage_group_cocone_of_ambient_cocone O x hx C S) := by
  -- Use the finite-stage universal property for the candidate obtained by restricting `ψ`.
  refine stage_restricted_fundamental_group_desc_unique O x hx hpath S
    (stage_group_cocone_of_ambient_cocone O x hx C S)
    (stage_union_to_ambient_hom O x hx S ≫ ψ) ?_
  intro i
  have hleg :
      (fundamental_group_cover_cocone
            (stage_cover O S)
            (stage_union_basepoint O x hx S)
            (stage_cover_basepoint_mem O x hx S)).ι.app i ≫
          (stage_union_to_ambient_hom O x hx S ≫ ψ) =
        (stage_member_fundamental_group_iso O x hx S i).hom ≫
          (fundamental_group_cover_cocone O x hx).ι.app (stage_cover_to_ambient_obj O S i) ≫ ψ := by
    -- First compare the stage leg with the ambient cover leg, then postcompose with `ψ`.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ ψ)
      (stage_union_to_ambient_cover_leg_eq O x hx S i)
  have hfac :
      (stage_member_fundamental_group_iso O x hx S i).hom ≫
          (fundamental_group_cover_cocone O x hx).ι.app (stage_cover_to_ambient_obj O S i) ≫ ψ =
        (stage_group_cocone_of_ambient_cocone O x hx C S).ι.app i := by
    -- Replace the ambient cover leg followed by `ψ` with the given cocone leg of `C`.
    simpa [stage_group_cocone_of_ambient_cocone, Category.assoc] using congrArg
      ((stage_member_fundamental_group_iso O x hx S i).hom ≫ ·)
      (hψ (stage_cover_to_ambient_obj O S i))
  exact hleg.trans hfac

/-- Helper for Theorem 2.7.5: the ambient descendant produced by stage reduction satisfies the
ambient cocone equations. -/
private theorem ambient_desc_fac_of_stage_reduction
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (C : Cocone (fundamental_group_cover_diagram O x hx))
    (j : TopologicalSpace.IsOpenCover.Index O) :
    (fundamental_group_cover_cocone O x hx).ι.app j ≫
        ambient_desc_of_stage_reduction_hom O hO x hx hpath hinter C =
      C.ι.app j := by
  -- Reduce the ambient cover leg to the singleton stage containing `j`, then apply the literal
  -- finite-stage factorization formula there.
  obtain ⟨S, hS⟩ :=
    exists_intersection_closed_finset_superset O hinter ({j} : Finset ι)
      (Finset.singleton_nonempty j)
  have hjS : j ∈ (S : Finset ι) := hS (Finset.mem_singleton_self j)
  let iS : TopologicalSpace.IsOpenCover.Index (stage_cover O S) := ⟨j, hjS⟩
  have hleg :
      (stage_member_fundamental_group_iso O x hx S iS).inv ≫
          (fundamental_group_cover_cocone
              (stage_cover O S)
              (stage_union_basepoint O x hx S)
              (stage_cover_basepoint_mem O x hx S)).ι.app iS ≫
            stage_union_to_ambient_hom O x hx S =
        (fundamental_group_cover_cocone O x hx).ι.app j := by
    -- Rewrite the stage leg through the shared ambient cover member indexed by `j`.
    simpa [iS, Category.assoc] using congrArg
      ((stage_member_fundamental_group_iso O x hx S iS).inv ≫ ·)
      (stage_union_to_ambient_cover_leg_eq O x hx S iS)
  let pre :=
    (stage_member_fundamental_group_iso O x hx S iS).inv ≫
      (fundamental_group_cover_cocone
          (stage_cover O S)
          (stage_union_basepoint O x hx S)
          (stage_cover_basepoint_mem O x hx S)).ι.app iS
  have hrestrict :
      pre ≫
          (stage_union_to_ambient_hom O x hx S ≫
            ambient_desc_of_stage_reduction_hom O hO x hx hpath hinter C) =
        pre ≫
          stage_restricted_fundamental_group_desc O x hx hpath S
            (stage_group_cocone_of_ambient_cocone O x hx C S) := by
    -- Restrict the ambient descendant to the singleton stage containing `j`.
    simpa [pre, Category.assoc] using congrArg (fun k ↦ pre ≫ k)
      (ambient_desc_restricts_to_stage O hO x hx hpath hinter C S)
  have hpre :
      pre ≫
          (stage_union_to_ambient_hom O x hx S ≫
            ambient_desc_of_stage_reduction_hom O hO x hx hpath hinter C) =
        C.ι.app j := by
    have hstage :
        pre ≫
            stage_restricted_fundamental_group_desc O x hx hpath S
              (stage_group_cocone_of_ambient_cocone O x hx C S) =
          (stage_member_fundamental_group_iso O x hx S iS).inv ≫
            (stage_group_cocone_of_ambient_cocone O x hx C S).ι.app iS := by
      -- Apply the literal finite-stage factorization and then precompose by the stage-member
      -- comparison isomorphism.
      simpa [pre, Category.assoc] using congrArg
        ((stage_member_fundamental_group_iso O x hx S iS).inv ≫ ·)
        (stage_restricted_fundamental_group_desc_fac O x hx hpath S
          (stage_group_cocone_of_ambient_cocone O x hx C S) iS)
    have htarget :
        (stage_member_fundamental_group_iso O x hx S iS).inv ≫
            (stage_group_cocone_of_ambient_cocone O x hx C S).ι.app iS =
          C.ι.app j := by
      -- The singleton-stage cocone leg is exactly the ambient cocone leg for `j`.
      simp [stage_group_cocone_of_ambient_cocone, iS, Category.assoc]
    exact hrestrict.trans (hstage.trans htarget)
  calc
    (fundamental_group_cover_cocone O x hx).ι.app j ≫
        ambient_desc_of_stage_reduction_hom O hO x hx hpath hinter C =
      pre ≫
          (stage_union_to_ambient_hom O x hx S ≫
            ambient_desc_of_stage_reduction_hom O hO x hx hpath hinter C) := by
          simpa [pre, Category.assoc] using congrArg
            (fun k ↦ k ≫ ambient_desc_of_stage_reduction_hom O hO x hx hpath hinter C)
            hleg.symm
    _ = C.ι.app j := hpre

/-- Helper for Theorem 2.7.5: the stage-reduction ambient descendant is the unique ambient
factorization of the cover cocone. -/
private theorem ambient_desc_unique_of_stage_reduction
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (C : Cocone (fundamental_group_cover_diagram O x hx))
    (ψ : (fundamental_group_cover_cocone O x hx).pt ⟶ C.pt)
    (hψ : ∀ j, (fundamental_group_cover_cocone O x hx).ι.app j ≫ ψ = C.ι.app j) :
    ψ = ambient_desc_of_stage_reduction_hom O hO x hx hpath hinter C := by
  -- Compare `ψ` and the stage-reduction descendant on one loop at a time by restricting both to
  -- a finite stage containing that loop.
  ext g
  induction g using Path.Homotopic.Quotient.ind with
  | mk γ =>
      obtain ⟨S, hγ⟩ := path_image_subset_finite_intersection_closed_union O hO hinter γ
      let loopClass :
          FundamentalGroup U[O, S] (stage_union_basepoint O x hx S) :=
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧
      have hrestrict_apply :
          (stage_union_to_ambient_hom O x hx S ≫ ψ).hom loopClass =
            (stage_restricted_fundamental_group_desc O x hx hpath S
                (stage_group_cocone_of_ambient_cocone O x hx C S)).hom loopClass := by
        -- Apply the stage restriction identity to the chosen lifted loop class.
        simpa [loopClass, GrpCat.comp_apply] using congrArg
          (fun k ↦ k.hom loopClass)
          (restricted_stage_desc_of_ambient_factor O x hx hpath C ψ hψ S)
      have hleft :
          ψ.hom (FundamentalGroup.fromPath ⟦γ⟧) =
            (stage_restricted_fundamental_group_desc O x hx hpath S
                (stage_group_cocone_of_ambient_cocone O x hx C S)).hom loopClass := by
        calc
          ψ.hom (FundamentalGroup.fromPath ⟦γ⟧) =
            (stage_union_to_ambient_hom O x hx S ≫ ψ).hom loopClass := by
              simpa [loopClass, GrpCat.comp_apply] using
                (congrArg ψ.hom
                  (stage_union_to_ambient_hom_apply_ambient_loop O x hx S γ hγ)).symm
          _ =
            (stage_restricted_fundamental_group_desc O x hx hpath S
                (stage_group_cocone_of_ambient_cocone O x hx C S)).hom loopClass :=
              hrestrict_apply
      exact hleft.trans
        (ambient_desc_of_stage_reduction_spec O hO x hx hpath hinter C γ S hγ).symm

/-- Theorem 2.7.5: if `O` is an open cover by path-connected open subsets, every member of `O`
contains the common basepoint `x`, and `O` is closed under finite intersections, then
`π₁(X, x)` is the colimit of the diagram `U ↦ π₁(U, x)` in groups. Under these hypotheses, `X` is
automatically path connected, so this is the group-level form of van Kampen obtained from the
groupoid colimit theorem and the equivalences `π₁(U, x) ≃ Π(U)` and `π₁(X, x) ≃ Π(X)`. -/
-- Proof sketch: apply Theorem 2.7.1 to the cover `O`, obtaining `Π(X)` as the colimit of the
-- fundamental-groupoid diagram. Because every cover member contains `x` and is path connected,
-- Proposition 2.5.7 identifies each `π₁(U, x)` with `Π(U)` via a one-object equivalence, and the
-- same argument identifies `π₁(X, x)` with `Π(X)`. Transport the groupoid colimit structure across
-- these equivalences to obtain the stated colimit cocone in `GrpCat`.
def fundamental_group_is_colimit_of_path_connected_open_cover
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O) :
    IsColimit (fundamental_group_cover_cocone O x hx) :=
  IsColimit.ofExistsUnique fun S ↦ by
    -- Route correction: the final step is no longer quotient-level infrastructure. Restrict the
    -- ambient candidate to each finite stage, identify that restriction with the literal
    -- finite-stage descended morphism, and then read off the ambient cocone equations and
    -- uniqueness from those finite-stage comparisons.
    refine ⟨ambient_desc_of_stage_reduction_hom O hO x hx hpath hinter S, ?_, ?_⟩
    · intro i
      exact ambient_desc_fac_of_stage_reduction O hO x hx hpath hinter S i
    · intro ψ hψ
      exact ambient_desc_unique_of_stage_reduction O hO x hx hpath hinter S ψ hψ

/-- The colimit cocone from the group-level van Kampen theorem induces the canonical comparison
morphism from `π₁(X, x)` to any other cocone over the open-cover diagram, and this morphism is
compatible with the cocone legs. -/
-- Proof sketch: apply the universal property packaged by
-- `fundamental_group_is_colimit_of_path_connected_open_cover`; its `fac` field gives the stated
-- compatibility for each member of the cover.
theorem fundamental_group_is_colimit_of_path_connected_open_cover_desc_fac
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_group_cover_diagram O x hx))
    (i : TopologicalSpace.IsOpenCover.Index O) :
    (fundamental_group_cover_cocone O x hx).ι.app i ≫
        (fundamental_group_is_colimit_of_path_connected_open_cover O hO x hx hpath hinter).desc S =
      S.ι.app i := by
  simpa using
    (fundamental_group_is_colimit_of_path_connected_open_cover O hO x hx hpath hinter).fac S i
