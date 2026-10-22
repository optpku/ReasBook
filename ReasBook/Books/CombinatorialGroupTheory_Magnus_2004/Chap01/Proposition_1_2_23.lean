/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_2
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_4
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_15

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open FreeGroup

section

variable {F : Type u} [Group F] [IsFreeGroup F]

private def signedGenerators {X : Type*} (V : List (FreeGroup X)) : List (FreeGroup X) :=
  V ++ V.map Inv.inv

private def productsOfLength {X : Type*} (generators : List (FreeGroup X)) :
    ℕ → List (FreeGroup X)
  | 0 => [1]
  | n + 1 =>
      List.flatMap (fun w ↦ generators.map fun g ↦ g * w) (productsOfLength generators n)

/-- Internal bounded search for subgroup membership after passing to an `N`-reduced generating
list. The bound is the canonical Nielsen bound `norm x` coming from the owner abstraction
`FreeGroup.IsNReduced`, not an ad hoc bound on the original finite generating set. -/
private def nReducedGeneratedSubgroupMembershipSearch {X : Type*} [DecidableEq X]
    (V : List (FreeGroup X)) (x : FreeGroup X) : Bool :=
  (List.range (norm x + 1)).any fun n ↦
    (productsOfLength (signedGenerators V) n).any fun y ↦ decide (y = x)

/-- Internal owner-side specification of the bounded search for an `N`-reduced generating list. -/
private theorem mem_closure_iff_nReducedGeneratedSubgroupMembershipSearch_eq_true
    {X : Type*} [DecidableEq X] (V : List (FreeGroup X))
    (hV : FreeGroup.IsNReduced (V.toFinset : Set (FreeGroup X))) (x : FreeGroup X) :
    x ∈ Subgroup.closure (V.toFinset : Set (FreeGroup X)) ↔
      nReducedGeneratedSubgroupMembershipSearch V x = true := by
  sorry

/-- Any finite subset of a free group admits a Nielsen-equivalent `N`-reduced generating list with
the same generated subgroup. This is the internal bridge from finite source data to the chapter's
canonical Nielsen owner abstraction. -/
private theorem exists_nReduced_generating_list {X : Type*} [DecidableEq X]
    (U : Finset (FreeGroup X)) :
    ∃ V : List (FreeGroup X),
      FreeGroup.IsNReduced (V.toFinset : Set (FreeGroup X)) ∧
        Subgroup.closure (U : Set (FreeGroup X)) =
          Subgroup.closure (V.toFinset : Set (FreeGroup X)) := by
  obtain ⟨V, hUV, hV⟩ := exists_nielsen_transform_to_n_reduced U.toList
  have hUset : Set.range U.toList.get = (U : Set (FreeGroup X)) := by
    ext x
    simpa [List.mem_iff_get] using (Finset.mem_toList : x ∈ U.toList ↔ x ∈ U)
  have hVset : Set.range V.get = (V.toFinset : Set (FreeGroup X)) := by
    ext x
    simp [List.mem_iff_get]
  refine ⟨V, ?_, ?_⟩
  · simpa [hVset] using hV
  · simpa [hUset, hVset] using
      generated_subgroup_eq_of_nielsen_transforms_to hUV

/-- Proposition 1-2-23: for a finite subset `U` of a free group, membership in the subgroup
`Gp(U) = Subgroup.closure (U : Set F)` is decidable.

The public API stays centered on the source-facing subgroup-membership problem. Its implementation
reuses the chapter/mathlib owner abstractions `FreeGroup.IsNReduced`,
`exists_nielsen_transform_to_n_reduced`, `generated_subgroup_eq_of_nielsen_transforms_to`,
`IsFreeGroup.toFreeGroup`, `Subgroup.mem_map_iff_mem`, and `MonoidHom.map_closure`. After
transporting to the canonical free-group model, it first replaces the finite generating set by an
Nielsen-equivalent `N`-reduced list and only then invokes the internal bounded search justified by
the chapter's Nielsen norm estimates. -/
-- Layer: `source-facing`.
@[reducible] noncomputable def generated_subgroup_membership_decidable (U : Finset F) :
    DecidablePred (fun x : F ↦ x ∈ Subgroup.closure (U : Set F)) :=
  fun x ↦ by
    classical
    let e : F ≃* FreeGroup (IsFreeGroup.Generators F) := IsFreeGroup.toFreeGroup F
    let _ : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
    let hVexists := exists_nReduced_generating_list (U.image e)
    let V := Classical.choose hVexists
    have hVspec :
        FreeGroup.IsNReduced
            (V.toFinset : Set (FreeGroup (IsFreeGroup.Generators F))) ∧
          Subgroup.closure ((U.image e : Finset (FreeGroup (IsFreeGroup.Generators F))) : Set _) =
            Subgroup.closure (V.toFinset : Set (FreeGroup (IsFreeGroup.Generators F))) :=
      Classical.choose_spec hVexists
    have hVnReduced :
        FreeGroup.IsNReduced
          (V.toFinset : Set (FreeGroup (IsFreeGroup.Generators F))) :=
      hVspec.1
    have hVclosure :
        Subgroup.closure ((U.image e : Finset (FreeGroup (IsFreeGroup.Generators F))) : Set _) =
          Subgroup.closure (V.toFinset : Set (FreeGroup (IsFreeGroup.Generators F))) :=
      hVspec.2
    have himage :
        ((U.image e : Finset (FreeGroup (IsFreeGroup.Generators F))) : Set _) =
          e.toMonoidHom '' (U : Set F) := by
      ext y
      simp
    have hsearch :
        x ∈ Subgroup.closure (U : Set F) ↔
          nReducedGeneratedSubgroupMembershipSearch V (e x) = true := by
      have hmem : x ∈ Subgroup.closure (U : Set F) ↔
          e x ∈ (Subgroup.closure (U : Set F)).map e.toMonoidHom :=
        (Subgroup.mem_map_iff_mem e.injective).symm
      rw [e.toMonoidHom.map_closure (U : Set F), ← himage, hVclosure] at hmem
      exact hmem.trans
        (mem_closure_iff_nReducedGeneratedSubgroupMembershipSearch_eq_true V hVnReduced (e x))
    exact
      decidable_of_iff
        (nReducedGeneratedSubgroupMembershipSearch V (e x) = true)
        hsearch.symm

/-- The decision procedure above decides exactly whether an element belongs to the subgroup
generated by `U`. -/
-- Proof sketch: install `generated_subgroup_membership_decidable U` as the local decidable
-- instance and simplify `decide` with `decide_eq_true_iff`.
theorem decide_mem_generated_subgroup_eq_true_iff (U : Finset F) (x : F) :
    letI := generated_subgroup_membership_decidable U
    decide (x ∈ Subgroup.closure (U : Set F)) = true ↔
      x ∈ Subgroup.closure (U : Set F) := by
  letI := generated_subgroup_membership_decidable U
  exact decide_eq_true_iff

end
