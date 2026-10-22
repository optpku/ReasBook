/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Lemma_1_4_2
import AlgebraicTopology_May_1999.Chap02.Theorem_2_7_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace.Opens

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- The inclusion `U ∩ V ↪ U` induces the canonical map on fundamental groups at the common
basepoint `x`. -/
abbrev fundamental_group_inf_to_left
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    FundamentalGroup ↥(U ⊓ V) ⟨x, ⟨hxU, hxV⟩⟩ →*
      FundamentalGroup U ⟨x, hxU⟩ :=
  FundamentalGroup.map (((toTopCat (TopCat.of X)).map (homOfLE inf_le_left)).hom) ⟨x, ⟨hxU, hxV⟩⟩

/-- Helper for Proposition 2.8.6: the inclusion `U ∩ V ↪ V` induces the right overlap map on
fundamental groups at the common basepoint `x`. -/
abbrev fundamental_group_inf_to_right
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    FundamentalGroup ↥(U ⊓ V) ⟨x, ⟨hxU, hxV⟩⟩ →*
      FundamentalGroup V ⟨x, hxV⟩ :=
  FundamentalGroup.map (((toTopCat (TopCat.of X)).map (homOfLE inf_le_right)).hom) ⟨x, ⟨hxU, hxV⟩⟩

/-- Helper for Proposition 2.8.6: the two ways of sending an overlap loop from `U ∩ V` into `X`
agree, via `U` or via `V`. -/
private theorem fundamental_group_overlap_to_union_eq
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩).comp
        (fundamental_group_inf_to_left U V x hxU hxV) =
      (FundamentalGroup.map (inclusion' V).hom ⟨x, hxV⟩).comp
        (fundamental_group_inf_to_right U V x hxU hxV) := by
  let pU : C(↥(U ⊓ V), ↥U) := (((toTopCat (TopCat.of X)).map (homOfLE inf_le_left)).hom)
  let pV : C(↥(U ⊓ V), ↥V) := (((toTopCat (TopCat.of X)).map (homOfLE inf_le_right)).hom)
  let qU : C(↥U, X) := (inclusion' U).hom
  let qV : C(↥V, X) := (inclusion' V).hom
  have hcomp :
      qU.comp pU = qV.comp pV := by
    -- Both composites are the literal inclusion `U ∩ V ↪ X`.
    ext y
    rfl
  -- Functoriality of `π₁` turns the equality of continuous maps into the desired equality.
  have hmap :
      FundamentalGroup.map (qU.comp pU) ⟨x, ⟨hxU, hxV⟩⟩ =
        FundamentalGroup.map (qV.comp pV) ⟨x, ⟨hxU, hxV⟩⟩ := by
    cases hcomp
    rfl
  have hleft :
      (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩).comp
          (fundamental_group_inf_to_left U V x hxU hxV) =
        FundamentalGroup.map (qU.comp pU) ⟨x, ⟨hxU, hxV⟩⟩ := by
    have hpU : pU ⟨x, ⟨hxU, hxV⟩⟩ = ⟨x, hxU⟩ := rfl
    cases hpU
    simpa [pU, qU, fundamental_group_inf_to_left] using
      (fundamental_group_map_comp pU qU ⟨x, ⟨hxU, hxV⟩⟩).symm
  have hright :
      FundamentalGroup.map (qV.comp pV) ⟨x, ⟨hxU, hxV⟩⟩ =
        (FundamentalGroup.map (inclusion' V).hom ⟨x, hxV⟩).comp
          (fundamental_group_inf_to_right U V x hxU hxV) := by
    have hpV : pV ⟨x, ⟨hxU, hxV⟩⟩ = ⟨x, hxV⟩ := rfl
    cases hpV
    simpa [pV, qV, fundamental_group_inf_to_right] using
      (fundamental_group_map_comp pV qV ⟨x, ⟨hxU, hxV⟩⟩)
  exact hleft.trans (hmap.trans hright)

/-- Helper for Proposition 2.8.6: if `V` is simply connected, then the overlap map into `V`
is the trivial homomorphism. -/
private theorem fundamental_group_inf_to_right_eq_one
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [SimplyConnectedSpace V] :
    fundamental_group_inf_to_right U V x hxU hxV = 1 := by
  -- The target fundamental group of a simply connected space is a subsingleton.
  ext γ
  let _ : Subsingleton (FundamentalGroup V ⟨x, hxV⟩) := by
    change Subsingleton (Path.Homotopic.Quotient (X := V) ⟨x, hxV⟩ ⟨x, hxV⟩)
    infer_instance
  exact Subsingleton.elim _ _

/-- Helper for Proposition 2.8.6: the normal closure of the overlap image maps trivially into
`π₁(X,x)` through the left inclusion. -/
private theorem normal_closure_range_le_left_to_union_ker
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [SimplyConnectedSpace V] :
    Subgroup.normalClosure (Set.range (fundamental_group_inf_to_left U V x hxU hxV)) ≤
      (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩).ker := by
  -- The kernel is normal, so it suffices to check the overlap generators.
  exact
    @Subgroup.normalClosure_le_normal
      (FundamentalGroup U ⟨x, hxU⟩)
      _
      (Set.range (fundamental_group_inf_to_left U V x hxU hxV))
      (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩).ker
      (MonoidHom.normal_ker (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩))
      (by
        rintro _ ⟨γ, rfl⟩
        change (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩)
            ((fundamental_group_inf_to_left U V x hxU hxV) γ) = 1
        have hoverlap :=
          DFunLike.congr_fun (fundamental_group_overlap_to_union_eq U V x hxU hxV) γ
        have hright_eq_one :
            (fundamental_group_inf_to_right U V x hxU hxV) γ = 1 := by
          exact DFunLike.congr_fun (fundamental_group_inf_to_right_eq_one U V x hxU hxV) γ
        -- Replace the left route by the right route, which is trivial because `π₁(V,x)` is trivial.
        calc
          (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩)
              ((fundamental_group_inf_to_left U V x hxU hxV) γ)
            = (FundamentalGroup.map (inclusion' V).hom ⟨x, hxV⟩)
                ((fundamental_group_inf_to_right U V x hxU hxV) γ) := by
                  exact hoverlap
          _ = (FundamentalGroup.map (inclusion' V).hom ⟨x, hxV⟩) 1 := by
                rw [hright_eq_one]
                rfl
          _ = 1 := by
                simpa using
                  (MonoidHom.map_one (FundamentalGroup.map (inclusion' V).hom ⟨x, hxV⟩)))

/-- Helper for Proposition 2.8.6: the three-piece van Kampen cover used for the decomposition
`X = (U ∩ V) ∪ U ∪ V`. -/
private abbrev union_cover_three
    (U V : TopologicalSpace.Opens (TopCat.of X)) :
    Fin 3 → TopologicalSpace.Opens (TopCat.of X) :=
  ![U ⊓ V, U, V]

/-- Helper for Proposition 2.8.6: the three-piece cover really covers `X`. -/
private theorem union_cover_three_isOpenCover
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (hcover : U ⊔ V = ⊤) :
    TopologicalSpace.IsOpenCover (union_cover_three U V) := by
  -- The extra overlap member does not change the supremum of the family.
  dsimp [TopologicalSpace.IsOpenCover, union_cover_three]
  simpa [sup_assoc, sup_left_comm, sup_comm] using hcover

/-- Helper for Proposition 2.8.6: the chosen basepoint lies in each member of the three-piece
cover. -/
private theorem union_cover_three_basepoint_mem
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    ∀ i, x ∈ union_cover_three U V i := by
  -- The basepoint data are literal on the three explicit cover members.
  intro i
  fin_cases i <;> simp [union_cover_three, hxU, hxV]

/-- Helper for Proposition 2.8.6: each member of the three-piece cover is path connected. -/
private theorem union_cover_three_path_connected
    (U V : TopologicalSpace.Opens (TopCat.of X))
    [PathConnectedSpace U]
    [PathConnectedSpace ↥(U ⊓ V)]
    [SimplyConnectedSpace V] :
    ∀ i, PathConnectedSpace (union_cover_three U V i) := by
  -- The hypotheses already provide the three required instances.
  intro i
  fin_cases i
  · change PathConnectedSpace ↥(U ⊓ V)
    infer_instance
  · change PathConnectedSpace ↥U
    infer_instance
  · change PathConnectedSpace ↥V
    infer_instance

/-- Helper for Proposition 2.8.6: every nonempty finite intersection of the three explicit cover
members is again one of those three members. -/
private theorem union_cover_three_closed_under_nonempty_finite_intersections
    (U V : TopologicalSpace.Opens (TopCat.of X)) :
    TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections (union_cover_three U V) := by
  intro s hs
  by_cases h0 : (0 : Fin 3) ∈ s
  · -- If the overlap member occurs, it already bounds the whole finite intersection from below.
    refine ⟨0, le_antisymm ?_ ?_⟩
    · exact Finset.inf'_le (s := s) (f := union_cover_three U V) h0
    · exact Finset.le_inf' (s := s) (H := hs) (f := union_cover_three U V) fun j hj ↦ by
        fin_cases j <;> simp [union_cover_three]
  · by_cases h1 : (1 : Fin 3) ∈ s
    · by_cases h2 : (2 : Fin 3) ∈ s
      · -- If both `U` and `V` occur, their intersection is again the overlap member.
        refine ⟨0, le_antisymm ?_ ?_⟩
        · refine le_inf ?_ ?_
          · exact Finset.inf'_le (s := s) (f := union_cover_three U V) h1
          · exact Finset.inf'_le (s := s) (f := union_cover_three U V) h2
        · exact Finset.le_inf' (s := s) (H := hs) (f := union_cover_three U V) fun j hj ↦ by
            fin_cases j <;> simp [union_cover_three]
      · -- Otherwise the only remaining member is `U`.
        refine ⟨1, Finset.inf'_eq_of_forall (s := s) (H := hs) (f := union_cover_three U V) ?_⟩
        intro j hj
        fin_cases j <;> simp [union_cover_three, h0, h2] at hj ⊢
    · have h2 : (2 : Fin 3) ∈ s := by
        rcases hs with ⟨j, hj⟩
        fin_cases j
        · exact False.elim (h0 hj)
        · exact False.elim (h1 hj)
        · exact hj
      -- With neither `U ∩ V` nor `U`, nonemptiness forces the family to be `{V}`.
      refine ⟨2, Finset.inf'_eq_of_forall (s := s) (H := hs) (f := union_cover_three U V) ?_⟩
      intro j hj
      fin_cases j <;> simp [union_cover_three, h0, h1] at hj ⊢

/-- Helper for Proposition 2.8.6: each canonical leg of the public van Kampen cocone is the
concrete inclusion-induced map on fundamental groups. -/
private theorem fundamental_group_cover_cocone_app_eq_map_inclusion
    {ι : Type*}
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (i : TopologicalSpace.IsOpenCover.Index O) :
    ((fundamental_group_cover_cocone O x hx).ι.app i).hom =
      FundamentalGroup.map (inclusion' (O i)).hom ⟨x, hx i⟩ := by
  -- The cocone leg is `FundamentalGroup.mapOfEq` for the literal inclusion, and the basepoint
  -- equality is definitional in this cover setup.
  ext g
  induction g using Path.Homotopic.Quotient.ind with
  | mk γ =>
      simpa [fundamental_group_cover_cocone, FundamentalGroup.map] using
        (FundamentalGroup.mapOfEq_apply (f := _) (h := rfl) (p := γ))

/-- Helper for Proposition 2.8.6: each morphism in the public van Kampen diagram is the concrete
inclusion-induced map between the corresponding fundamental groups. -/
private theorem fundamental_group_cover_diagram_map_eq_map_of_inclusion
    {ι : Type*}
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {i j : TopologicalSpace.IsOpenCover.Index O} (f : i ⟶ j) :
    ((fundamental_group_cover_diagram O x hx).map f).hom =
      FundamentalGroup.map (((toTopCat (TopCat.of X)).map f.hom).hom) ⟨x, hx i⟩ := by
  -- The diagram morphism is again a `mapOfEq` with definitional basepoint preservation.
  ext g
  induction g using Path.Homotopic.Quotient.ind with
  | mk γ =>
      simpa [fundamental_group_cover_diagram, FundamentalGroup.map] using
        (FundamentalGroup.mapOfEq_apply (f := _) (h := rfl) (p := γ))

/-- Helper for Proposition 2.8.6: any homomorphism out of the fundamental group of the simply
connected right-hand open set is trivial. -/
private theorem monoid_hom_from_right_eq_one
    (V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxV : x ∈ V)
    [SimplyConnectedSpace V]
    {G : Type*} [Group G]
    (φ : FundamentalGroup V ⟨x, hxV⟩ →* G) :
    φ = 1 := by
  -- The domain fundamental group is a subsingleton, so every homomorphism out of it is trivial.
  let _ : Subsingleton (FundamentalGroup V ⟨x, hxV⟩) := by
    change Subsingleton (Path.Homotopic.Quotient (X := V) ⟨x, hxV⟩ ⟨x, hxV⟩)
    infer_instance
  ext γ
  have hγ : γ = 1 := Subsingleton.elim _ _
  simpa [hγ] using congrArg φ hγ

/-- Helper for Proposition 2.8.6: the inclusion `V ↪ X` induces the trivial map on fundamental
groups because `V` is simply connected. -/
private theorem fundamental_group_right_to_union_eq_one
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [SimplyConnectedSpace V] :
    FundamentalGroup.map (inclusion' V).hom ⟨x, hxV⟩ = 1 := by
  -- This is the ambient specialization of the previous source-subsingleton observation.
  exact
    monoid_hom_from_right_eq_one V x hxV
      (FundamentalGroup.map (inclusion' V).hom ⟨x, hxV⟩)

/-- Helper for Proposition 2.8.6: the overlap leg to the quotient is already trivial, because the
normal closure was defined to kill the entire overlap image. -/
private theorem quotient_mk_comp_inf_left_eq_one
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    let N := Subgroup.normalClosure (Set.range (fundamental_group_inf_to_left U V x hxU hxV))
    (QuotientGroup.mk' N).comp (fundamental_group_inf_to_left U V x hxU hxV) = 1 := by
  dsimp
  ext g
  -- Every overlap generator lands in the defining normal subgroup of the quotient.
  have hg :
      (fundamental_group_inf_to_left U V x hxU hxV) g ∈
        Subgroup.normalClosure (Set.range (fundamental_group_inf_to_left U V x hxU hxV)) := by
    exact Subgroup.subset_normalClosure ⟨g, rfl⟩
  exact
    (@QuotientGroup.eq_one_iff
      (FundamentalGroup U ⟨x, hxU⟩)
      _
      (Subgroup.normalClosure (Set.range (fundamental_group_inf_to_left U V x hxU hxV)))
      (by
        simpa using
          (Subgroup.normalClosure_normal :
            (Subgroup.normalClosure
              (Set.range (fundamental_group_inf_to_left U V x hxU hxV))).Normal))
      ((fundamental_group_inf_to_left U V x hxU hxV) g)).2 hg

/-- Helper for Proposition 2.8.6: if `U ≤ V`, then the quotient by the overlap image is already
trivial because the overlap is all of `U`. -/
private theorem quotient_mk_eq_one_of_le_right
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (hUV : U ≤ V) :
    let N := Subgroup.normalClosure (Set.range (fundamental_group_inf_to_left U V x hxU hxV))
    QuotientGroup.mk' N = 1 := by
  let p : C(↥U, ↥(U ⊓ V)) :=
    (((toTopCat (TopCat.of X)).map (homOfLE (le_inf le_rfl hUV))).hom)
  have hleft_inv :
      (fundamental_group_inf_to_left U V x hxU hxV).comp (FundamentalGroup.map p ⟨x, hxU⟩) =
        MonoidHom.id _ := by
    ext g
    let q : C(↥(U ⊓ V), ↥U) := (((toTopCat (TopCat.of X)).map (homOfLE inf_le_left)).hom)
    have hcomp : q.comp p = ContinuousMap.id _ := by
      -- The route `U ↪ U ∩ V ↪ U` is literally the identity.
      ext y
      rfl
    have hmap :
        FundamentalGroup.map (q.comp p) ⟨x, hxU⟩ =
          FundamentalGroup.map (ContinuousMap.id ↥U) ⟨x, hxU⟩ := by
      cases hcomp
      rfl
    have hp : p ⟨x, hxU⟩ = ⟨x, ⟨hxU, hxV⟩⟩ := rfl
    have hfactor :
        FundamentalGroup.map (q.comp p) ⟨x, hxU⟩ =
          (fundamental_group_inf_to_left U V x hxU hxV).comp (FundamentalGroup.map p ⟨x, hxU⟩) := by
      -- Functoriality identifies the overlap inclusion followed by projection back to `U`.
      cases hp
      simpa [p, q, fundamental_group_inf_to_left] using (fundamental_group_map_comp p q ⟨x, hxU⟩)
    have hcompose :
        (fundamental_group_inf_to_left U V x hxU hxV).comp (FundamentalGroup.map p ⟨x, hxU⟩) =
          FundamentalGroup.map (ContinuousMap.id ↥U) ⟨x, hxU⟩ := by
      exact hfactor.symm.trans hmap
    have hcompose_eval :
        (fundamental_group_inf_to_left U V x hxU hxV) ((FundamentalGroup.map p ⟨x, hxU⟩) g) =
          (FundamentalGroup.map (ContinuousMap.id ↥U) ⟨x, hxU⟩) g := by
      exact DFunLike.congr_fun hcompose g
    have hid_eval :
        (FundamentalGroup.map (ContinuousMap.id ↥U) ⟨x, hxU⟩) g = g := by
      simpa using DFunLike.congr_fun (fundamental_group_map_id (⟨x, hxU⟩ : U)) g
    exact hcompose_eval.trans hid_eval
  -- Under `U ≤ V`, every loop in `U` already comes from the overlap.
  let N := Subgroup.normalClosure (Set.range (fundamental_group_inf_to_left U V x hxU hxV))
  ext g
  change (QuotientGroup.mk' N) g = 1
  have hq_eq :
      (QuotientGroup.mk' N)
          ((fundamental_group_inf_to_left U V x hxU hxV)
            ((FundamentalGroup.map p ⟨x, hxU⟩) g)) = 1 := by
    let hraw :=
      DFunLike.congr_fun (quotient_mk_comp_inf_left_eq_one U V x hxU hxV)
        ((FundamentalGroup.map p ⟨x, hxU⟩) g)
    dsimp [N] at hraw
    exact hraw
  have hq :
      (fundamental_group_inf_to_left U V x hxU hxV)
          ((FundamentalGroup.map p ⟨x, hxU⟩) g) ∈ N := by
    exact
      (@QuotientGroup.eq_one_iff
        (FundamentalGroup U ⟨x, hxU⟩)
        _
        N
        (by
          simpa [N] using
            (Subgroup.normalClosure_normal :
              (Subgroup.normalClosure
                (Set.range (fundamental_group_inf_to_left U V x hxU hxV))).Normal))
        ((fundamental_group_inf_to_left U V x hxU hxV)
          ((FundamentalGroup.map p ⟨x, hxU⟩) g))).1 hq_eq
  have hg :
      (fundamental_group_inf_to_left U V x hxU hxV)
          ((FundamentalGroup.map p ⟨x, hxU⟩) g) = g := by
    simpa using DFunLike.congr_fun hleft_inv g
  have hg_mem : g ∈ N := by
    exact hg ▸ hq
  exact
    (@QuotientGroup.eq_one_iff
      (FundamentalGroup U ⟨x, hxU⟩)
      _
      N
      (by
        simpa [N] using
          (Subgroup.normalClosure_normal :
            (Subgroup.normalClosure
              (Set.range (fundamental_group_inf_to_left U V x hxU hxV))).Normal))
      g).2 hg_mem

/-- Helper for Proposition 2.8.6: if `U ≤ V`, then the ambient map `π₁(U,x) → π₁(X,x)` is
already trivial because it factors through the simply connected space `V`. -/
private theorem fundamental_group_left_to_union_eq_one_of_le_right
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [SimplyConnectedSpace V]
    (hUV : U ≤ V) :
    FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩ = 1 := by
  let p : C(↥U, ↥V) := (((toTopCat (TopCat.of X)).map (homOfLE hUV)).hom)
  let qU : C(↥U, X) := (inclusion' U).hom
  let qV : C(↥V, X) := (inclusion' V).hom
  have hcomp : qU = qV.comp p := by
    -- Both maps are the literal inclusion `U ↪ X`.
    ext y
    rfl
  have hmap :
      FundamentalGroup.map qU ⟨x, hxU⟩ =
        FundamentalGroup.map (qV.comp p) ⟨x, hxU⟩ := by
    cases hcomp
    rfl
  have hp : p ⟨x, hxU⟩ = ⟨x, hxV⟩ := rfl
  have hfactor :
      FundamentalGroup.map (qV.comp p) ⟨x, hxU⟩ =
        (FundamentalGroup.map qV ⟨x, hxV⟩).comp (FundamentalGroup.map p ⟨x, hxU⟩) := by
    -- Functoriality identifies the left inclusion with the route through `V`.
    cases hp
    simpa [p, qV] using (fundamental_group_map_comp p qV ⟨x, hxU⟩)
  change FundamentalGroup.map qU ⟨x, hxU⟩ = 1
  rw [hmap, hfactor]
  change (FundamentalGroup.map (inclusion' V).hom ⟨x, hxV⟩).comp (FundamentalGroup.map p ⟨x, hxU⟩) = 1
  rw [fundamental_group_right_to_union_eq_one U V x hxU hxV]
  ext g
  rfl

/-- Helper for Proposition 2.8.6: the overlap leg into the range subgroup is trivial, because its
ambient image agrees with the right-hand route through the simply connected open set `V`. -/
private theorem range_restrict_comp_inf_left_eq_one
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [SimplyConnectedSpace V] :
    let π : FundamentalGroup U ⟨x, hxU⟩ →* FundamentalGroup X x :=
      FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩
    π.rangeRestrict.comp (fundamental_group_inf_to_left U V x hxU hxV) = 1 := by
  dsimp
  ext γ
  -- Compare the two ambient routes out of the overlap and kill the right-hand one.
  change (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩)
      ((fundamental_group_inf_to_left U V x hxU hxV) γ) = 1
  have hoverlap :=
    DFunLike.congr_fun (fundamental_group_overlap_to_union_eq U V x hxU hxV) γ
  have hright :
          (FundamentalGroup.map (inclusion' V).hom ⟨x, hxV⟩)
            ((fundamental_group_inf_to_right U V x hxU hxV) γ) = 1 := by
    have hmap : FundamentalGroup.map (inclusion' V).hom ⟨x, hxV⟩ = 1 :=
      fundamental_group_right_to_union_eq_one U V x hxU hxV
    exact DFunLike.congr_fun hmap ((fundamental_group_inf_to_right U V x hxU hxV) γ)
  exact hoverlap.trans hright

/-- Helper for Proposition 2.8.6: the direct overlap inclusion `U ∩ V ↪ X` induces the trivial
map on fundamental groups when `V` is simply connected. -/
private theorem fundamental_group_overlap_to_union_eq_one
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [SimplyConnectedSpace V] :
    FundamentalGroup.map (inclusion' (U ⊓ V)).hom ⟨x, ⟨hxU, hxV⟩⟩ = 1 := by
  let pV : C(↥(U ⊓ V), ↥V) := (((toTopCat (TopCat.of X)).map (homOfLE inf_le_right)).hom)
  let qV : C(↥V, X) := (inclusion' V).hom
  have hcomp : (inclusion' (U ⊓ V)).hom = qV.comp pV := by
    -- The direct inclusion of `U ∩ V` into `X` is literally the route through `V`.
    ext y
    rfl
  have hmap :
      FundamentalGroup.map (inclusion' (U ⊓ V)).hom ⟨x, ⟨hxU, hxV⟩⟩ =
        FundamentalGroup.map (qV.comp pV) ⟨x, ⟨hxU, hxV⟩⟩ := by
    cases hcomp
    rfl
  have hpV : pV ⟨x, ⟨hxU, hxV⟩⟩ = ⟨x, hxV⟩ := rfl
  have hfactor :
      FundamentalGroup.map (qV.comp pV) ⟨x, ⟨hxU, hxV⟩⟩ =
        (FundamentalGroup.map qV ⟨x, hxV⟩).comp
          (fundamental_group_inf_to_right U V x hxU hxV) := by
    -- Functoriality identifies the direct overlap inclusion with the factorization through `V`.
    cases hpV
    simpa [pV, qV, fundamental_group_inf_to_right] using
      (fundamental_group_map_comp pV qV ⟨x, ⟨hxU, hxV⟩⟩)
  have hqV : FundamentalGroup.map qV ⟨x, hxV⟩ = 1 := by
    simpa [qV] using fundamental_group_right_to_union_eq_one U V x hxU hxV
  rw [hmap, hfactor, hqV]
  ext γ
  rfl

/-- Helper for Proposition 2.8.6: the three-piece cover cocones used below all have the leg
shape `[1, φ, 1]` on `{U ∩ V, U, V}`. -/
private def union_cover_three_leg
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    {G : Type*} [Group G]
    (φ : FundamentalGroup U ⟨x, hxU⟩ →* G)
    (i : TopologicalSpace.IsOpenCover.Index (union_cover_three U V)) :
    FundamentalGroup (union_cover_three U V i)
        ⟨x, union_cover_three_basepoint_mem U V x hxU hxV i⟩ →* G :=
  match (show Fin 3 from i) with
  | 0 => 1
  | 1 => φ
  | 2 => 1

/-- Helper for Proposition 2.8.6: on the explicit cover `{U ∩ V, U, V}`, any leg assignment of
the form `[1, φ, 1]` is already a cocone once `φ` kills the overlap and becomes trivial whenever
`U ≤ V`. -/
private theorem union_cover_three_trivial_right_naturality
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [SimplyConnectedSpace V]
    {G : Type*} [Group G]
    (φ : FundamentalGroup U ⟨x, hxU⟩ →* G)
    (hφ_overlap : φ.comp (fundamental_group_inf_to_left U V x hxU hxV) = 1)
    (hφ_right : ∀ hUV : U ≤ V, φ = 1) :
    ∀ {i j : TopologicalSpace.IsOpenCover.Index (union_cover_three U V)} (f : i ⟶ j),
      (union_cover_three_leg U V x hxU hxV φ j).comp
          (((fundamental_group_cover_diagram (union_cover_three U V) x
              (union_cover_three_basepoint_mem U V x hxU hxV)).map f).hom) =
        union_cover_three_leg U V x hxU hxV φ i := by
  intro i j f
  change Fin 3 at i
  change Fin 3 at j
  fin_cases i <;> fin_cases j
  · ext g
    -- Both overlap legs are definitionally trivial.
    rfl
  · have hf : f.hom = homOfLE inf_le_left := Subsingleton.elim _ _
    cases hf
    rw [fundamental_group_cover_diagram_map_eq_map_of_inclusion
      (union_cover_three U V) x (union_cover_three_basepoint_mem U V x hxU hxV)]
    -- This is exactly the overlap-killing hypothesis on `φ`.
    simpa [union_cover_three_leg, union_cover_three, fundamental_group_inf_to_left] using
      hφ_overlap
  · ext g
    -- The target leg is trivial, so the composite from the overlap is trivial as well.
    rfl
  · have hle : U ≤ U ⊓ V := CategoryTheory.leOfHom f.hom
    have hUV : U ≤ V := le_trans hle inf_le_right
    have hφ : φ = 1 := hφ_right hUV
    ext g
    -- Any branch from `U` into the right side forces `φ` itself to be trivial.
    rw [hφ]
    rfl
  · have hf : f.hom = 𝟙 _ := Subsingleton.elim _ _
    cases hf
    rw [fundamental_group_cover_diagram_map_eq_map_of_inclusion
      (union_cover_three U V) x (union_cover_three_basepoint_mem U V x hxU hxV)]
    ext g
    -- On the diagonal `U` leg, the public diagram map is the identity.
    simpa [union_cover_three_leg, union_cover_three] using
      congrArg φ (DFunLike.congr_fun (fundamental_group_map_id (⟨x, hxU⟩ : ↥U)) g)
  · have hUV : U ≤ V := CategoryTheory.leOfHom f.hom
    have hφ : φ = 1 := hφ_right hUV
    ext g
    -- The `U → V` branch is the same right-triviality hypothesis.
    rw [hφ]
    rfl
  · have hcomp :
      (union_cover_three_leg U V x hxU hxV φ (show TopologicalSpace.IsOpenCover.Index
          (union_cover_three U V) from (0 : Fin 3))).comp
        (((fundamental_group_cover_diagram (union_cover_three U V) x
            (union_cover_three_basepoint_mem U V x hxU hxV)).map f).hom) = 1 :=
      monoid_hom_from_right_eq_one V x hxV _
    -- Any map sourced from `V` is trivial because `π₁(V,x)` is trivial.
    simpa [union_cover_three_leg] using hcomp
  · have hcomp :
      (union_cover_three_leg U V x hxU hxV φ (show TopologicalSpace.IsOpenCover.Index
          (union_cover_three U V) from (1 : Fin 3))).comp
        (((fundamental_group_cover_diagram (union_cover_three U V) x
            (union_cover_three_basepoint_mem U V x hxU hxV)).map f).hom) = 1 :=
      monoid_hom_from_right_eq_one V x hxV _
    -- Any map sourced from `V` is trivial because `π₁(V,x)` is trivial.
    simpa [union_cover_three_leg] using hcomp
  · ext g
    -- The right-hand diagonal leg is already the trivial homomorphism.
    rfl

/-- Helper for Proposition 2.8.6: the van Kampen quotient by the normal closure of the overlap
image descends from `π₁(X,x)`.

This is the structural specialization of Theorem 2.7.5 to the three-piece cover
`{U ∩ V, U, V}`. -/
private theorem fundamental_group_left_to_union_normal_closure_desc
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (hcover : U ⊔ V = ⊤)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [PathConnectedSpace U]
    [PathConnectedSpace ↥(U ⊓ V)]
    [SimplyConnectedSpace V] :
    let N := Subgroup.normalClosure (Set.range (fundamental_group_inf_to_left U V x hxU hxV))
    ∃ δ : FundamentalGroup X x →*
        (FundamentalGroup U ⟨x, hxU⟩ ⧸ N),
      δ.comp (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩) = QuotientGroup.mk' N := by
  -- Route correction: the quotient cocone must be descended directly from the explicit
  -- three-piece cover, not from the discarded quotient-surjectivity shortcut.
  let O := union_cover_three U V
  let hO := union_cover_three_isOpenCover U V hcover
  let hxO := union_cover_three_basepoint_mem U V x hxU hxV
  let hpathO := union_cover_three_path_connected U V
  let hinter := union_cover_three_closed_under_nonempty_finite_intersections U V
  let N := Subgroup.normalClosure (Set.range (fundamental_group_inf_to_left U V x hxU hxV))
  change ∃ δ : FundamentalGroup X x →* (FundamentalGroup U ⟨x, hxU⟩ ⧸ N),
      δ.comp (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩) = QuotientGroup.mk' N
  let S : Cocone (fundamental_group_cover_diagram O x hxO) := {
    pt := GrpCat.of (FundamentalGroup U ⟨x, hxU⟩ ⧸ N)
    ι := {
      app := fun i ↦ GrpCat.ofHom (union_cover_three_leg U V x hxU hxV (QuotientGroup.mk' N) i)
      naturality := fun i j f ↦ by
        -- The quotient cocone uses the packaged `[1, mk, 1]` naturality lemma.
        ext g
        exact DFunLike.congr_fun (union_cover_three_trivial_right_naturality U V x hxU hxV
          (φ := QuotientGroup.mk' N)
          (quotient_mk_comp_inf_left_eq_one U V x hxU hxV)
          (fun hUV ↦ quotient_mk_eq_one_of_le_right U V x hxU hxV hUV) f) g } }
  let δ :=
    (fundamental_group_is_colimit_of_path_connected_open_cover O hO x hxO hpathO hinter).desc S
  refine ⟨δ.hom, ?_⟩
  let iU : TopologicalSpace.IsOpenCover.Index O := (show TopologicalSpace.IsOpenCover.Index O from
    (1 : Fin 3))
  have hfac :=
    fundamental_group_is_colimit_of_path_connected_open_cover_desc_fac
      O hO x hxO hpathO hinter S iU
  have hfac_hom :
      δ.hom.comp ((fundamental_group_cover_cocone O x hxO).ι.app iU).hom =
        (S.ι.app iU).hom := by
    simpa [δ] using congrArg GrpCat.Hom.hom hfac
  -- Reading the `U` leg of the descended cocone gives the required factorization.
  rw [fundamental_group_cover_cocone_app_eq_map_inclusion O x hxO iU] at hfac_hom
  simpa [S, O, hxO, N, union_cover_three_leg] using hfac_hom

/-- Helper for Proposition 2.8.6: the range subgroup of `π₁(U,x) → π₁(X,x)` receives the
descended van Kampen comparison map from `π₁(X,x)`. -/
private theorem fundamental_group_left_to_union_range_desc
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (hcover : U ⊔ V = ⊤)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [PathConnectedSpace U]
    [PathConnectedSpace ↥(U ⊓ V)]
    [SimplyConnectedSpace V] :
    let π : FundamentalGroup U ⟨x, hxU⟩ →* FundamentalGroup X x :=
      FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩
    let R := π.range
    ∃ ε : FundamentalGroup X x →* R,
      R.subtype.comp ε = MonoidHom.id _ := by
  -- Route correction: surjectivity should be proved by descending to the actual range subgroup,
  -- not by reusing the quotient cocone.
  let O := union_cover_three U V
  let hO := union_cover_three_isOpenCover U V hcover
  let hxO := union_cover_three_basepoint_mem U V x hxU hxV
  let hpathO := union_cover_three_path_connected U V
  let hinter := union_cover_three_closed_under_nonempty_finite_intersections U V
  let π : FundamentalGroup U ⟨x, hxU⟩ →* FundamentalGroup X x :=
    FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩
  let R := π.range
  change ∃ ε : FundamentalGroup X x →* R, R.subtype.comp ε = MonoidHom.id _
  let S : Cocone (fundamental_group_cover_diagram O x hxO) := {
    pt := GrpCat.of R
    ι := {
      app := fun i ↦ GrpCat.ofHom (union_cover_three_leg U V x hxU hxV π.rangeRestrict i)
      naturality := fun i j f ↦ by
        -- The range cocone is the same `[1, φ, 1]` pattern with `φ = π.rangeRestrict`.
        ext g
        exact DFunLike.congr_fun (union_cover_three_trivial_right_naturality U V x hxU hxV
          (φ := π.rangeRestrict)
          (range_restrict_comp_inf_left_eq_one U V x hxU hxV)
          (fun hUV ↦ by
            ext a
            exact DFunLike.congr_fun
              (fundamental_group_left_to_union_eq_one_of_le_right U V x hxU hxV hUV) a) f) g } }
  let ε :=
    (fundamental_group_is_colimit_of_path_connected_open_cover O hO x hxO hpathO hinter).desc S
  refine ⟨ε.hom, ?_⟩
  have hsplit_cat : ε ≫ GrpCat.ofHom R.subtype = 𝟙 _ := by
    apply (fundamental_group_is_colimit_of_path_connected_open_cover O hO x hxO hpathO hinter).hom_ext
    intro i
    have hfac :=
      fundamental_group_is_colimit_of_path_connected_open_cover_desc_fac
        O hO x hxO hpathO hinter S i
    have hfac_hom :
        ε.hom.comp ((fundamental_group_cover_cocone O x hxO).ι.app i).hom =
          (S.ι.app i).hom := by
      simpa [ε] using congrArg GrpCat.Hom.hom hfac
    ext g
    -- Evaluate the descended factorization on a single loop and then compare the three cover legs.
    change R.subtype (ε.hom (((fundamental_group_cover_cocone O x hxO).ι.app i).hom g)) =
      ((fundamental_group_cover_cocone O x hxO).ι.app i).hom g
    have hfac_eval :
        ε.hom (((fundamental_group_cover_cocone O x hxO).ι.app i).hom g) =
          (S.ι.app i).hom g := by
      change ((ε.hom.comp ((fundamental_group_cover_cocone O x hxO).ι.app i).hom) g) =
        (S.ι.app i).hom g
      exact DFunLike.congr_fun hfac_hom g
    rw [hfac_eval]
    change R.subtype ((S.ι.app i).hom g) = ((fundamental_group_cover_cocone O x hxO).ι.app i).hom g
    change Fin 3 at i
    fin_cases i
    · -- On the overlap member, both cocones are already trivial after mapping into `X`.
      rw [fundamental_group_cover_cocone_app_eq_map_inclusion O x hxO]
      simpa [S, O, π, R, hxO, union_cover_three_leg] using
        DFunLike.congr_fun (fundamental_group_overlap_to_union_eq_one U V x hxU hxV).symm g
    · -- On the `U` member, postcomposing the range restriction recovers the original map.
      rw [fundamental_group_cover_cocone_app_eq_map_inclusion O x hxO]
      rfl
    · -- On the `V` member, both the descended cocone and the canonical cocone are trivial.
      rw [fundamental_group_cover_cocone_app_eq_map_inclusion O x hxO]
      simpa [S, O, π, R, hxO, union_cover_three_leg] using
        DFunLike.congr_fun (fundamental_group_right_to_union_eq_one U V x hxU hxV).symm g
  simpa [ε] using congrArg GrpCat.Hom.hom hsplit_cat

/-- Helper for Proposition 2.8.6: once the quotient map descends across van Kampen, every kernel
element of `π₁(U,x) → π₁(X,x)` lies in the normal closure of the overlap image. -/
private theorem left_to_union_ker_le_normal_closure_range
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (hcover : U ⊔ V = ⊤)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [PathConnectedSpace U]
    [PathConnectedSpace ↥(U ⊓ V)]
    [SimplyConnectedSpace V] :
    (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩).ker ≤
      Subgroup.normalClosure (Set.range (fundamental_group_inf_to_left U V x hxU hxV)) := by
  let π : FundamentalGroup U ⟨x, hxU⟩ →* FundamentalGroup X x :=
    FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩
  let N := Subgroup.normalClosure (Set.range (fundamental_group_inf_to_left U V x hxU hxV))
  rcases fundamental_group_left_to_union_normal_closure_desc U V hcover x hxU hxV with ⟨δ, hδ⟩
  intro g hg
  have hg' : π g = 1 := by
    simpa [π, MonoidHom.mem_ker] using hg
  -- Apply the descended quotient map to a kernel element and read the result in the quotient.
  have hq : (QuotientGroup.mk' N) g = 1 := by
    calc
      (QuotientGroup.mk' N) g = (δ.comp π) g := by
            exact (DFunLike.congr_fun hδ g).symm
      _ = δ (π g) := rfl
      _ = 1 := by simp [hg']
  exact
    (@QuotientGroup.eq_one_iff
      (FundamentalGroup U ⟨x, hxU⟩)
      _
      N
      (by
        simpa [N] using
          (Subgroup.normalClosure_normal :
            (Subgroup.normalClosure
              (Set.range (fundamental_group_inf_to_left U V x hxU hxV))).Normal))
      g).mp hq

/-- Proposition 2.8.6 (1): if `X = U ∪ V` with `U` and `U ∩ V` path connected at the basepoint
and `V` simply connected, then the inclusion-induced map `π₁(U,x) → π₁(X,x)` is surjective. -/
-- Proof sketch: descend the three-piece van Kampen cocone to the actual range subgroup of
-- `π₁(U,x) → π₁(X,x)`. The descended map `π₁(X,x) → range(π₁(U,x) → π₁(X,x))` splits the subtype
-- inclusion, so every loop in `X` already lies in the image of the left inclusion.
theorem fundamental_group_left_to_union_surjective
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (hcover : U ⊔ V = ⊤)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [PathConnectedSpace U]
    [PathConnectedSpace ↥(U ⊓ V)]
    [SimplyConnectedSpace V] :
    Function.Surjective (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩) := by
  let π : FundamentalGroup U ⟨x, hxU⟩ →* FundamentalGroup X x :=
    FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩
  let R := π.range
  rcases fundamental_group_left_to_union_range_desc U V hcover x hxU hxV with ⟨ε, hε⟩
  intro g
  rcases (ε g).2 with ⟨u, hu⟩
  -- The range witness carried by `ε g` becomes a genuine preimage after applying the splitting.
  refine ⟨u, ?_⟩
  have hsplit : R.subtype (ε g) = g := DFunLike.congr_fun hε g
  exact hu.trans hsplit

/-- Proposition 2.8.6 (2): under the same hypotheses, the kernel of `π₁(U,x) → π₁(X,x)` is the
normal closure of the image of `π₁(U ∩ V,x) → π₁(U,x)`. -/
-- Proof sketch: the overlap image lies in the kernel because the two overlap maps into `X`
-- coincide, while the route through `V` is trivial since `V` is simply connected. The reverse
-- inclusion comes from the descended quotient map to `π₁(U,x) ⧸ N`, which kills exactly `N`.
theorem fundamental_group_left_to_union_ker_eq_normal_closure_range
    (U V : TopologicalSpace.Opens (TopCat.of X))
    (hcover : U ⊔ V = ⊤)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [PathConnectedSpace U]
    [PathConnectedSpace ↥(U ⊓ V)]
    [SimplyConnectedSpace V] :
    (FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩).ker =
      Subgroup.normalClosure (Set.range (fundamental_group_inf_to_left U V x hxU hxV)) := by
  -- Combine the quotient-side upper bound with the direct overlap-side lower bound.
  refine le_antisymm
    (left_to_union_ker_le_normal_closure_range U V hcover x hxU hxV)
    (normal_closure_range_le_left_to_union_ker U V x hxU hxV)
