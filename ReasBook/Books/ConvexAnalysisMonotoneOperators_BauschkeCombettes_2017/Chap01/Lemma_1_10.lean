/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter

private lemma nhds_reverse_inclusion_directed {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirected {U : Set X // U ∈ nhds x} (fun U V => (V : Set X) ⊆ U) := by
  refine ⟨?_⟩
  intro U V
  -- Intersections provide a common smaller neighborhood, which is an upper bound
  -- for the reverse-inclusion order.
  refine ⟨⟨(U : Set X) ∩ V, inter_mem U.2 V.2⟩, ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private theorem exists_tendsto_subtype_of_mem_closure {X : Type u} [TopologicalSpace X]
    {C : Set X}
    {x : X} (h : x ∈ closure C) :
    ∃ (A : Type u) (_ : Preorder A) (_ : IsDirectedOrder A) (_ : Nonempty A)
      (ξ : A → C), Tendsto (fun a ↦ (ξ a : X)) atTop (nhds x) := by
  classical
  let A := {U : Set X // U ∈ nhds x}
  letI : LE A := ⟨fun U V => (V : Set X) ⊆ U⟩
  letI : LT A := ⟨fun U V => (V : Set X) ⊆ U ∧ ¬ (U : Set X) ⊆ V⟩
  letI : Preorder A :=
    { le_refl := fun U => Set.Subset.rfl
      le_trans := fun U V W hUV hVW => Set.Subset.trans hVW hUV
      lt_iff_le_not_ge := fun U V => Iff.rfl }
  letI : IsDirectedOrder A := nhds_reverse_inclusion_directed
  letI : Nonempty A := ⟨⟨Set.univ, univ_mem⟩⟩
  have hclosure : ∀ t ∈ nhds x, ∃ y : C, (y : X) ∈ t := (mem_closure_iff_nhds').1 h
  let ξ : A → C := fun U ↦ Classical.choose (hclosure U U.2)
  refine ⟨A, inferInstance, inferInstance, inferInstance, ξ, ?_⟩
  rw [Filter.tendsto_def]
  intro W hW
  rw [Filter.mem_atTop_sets]
  -- Once the index neighborhood lies inside `W`, the chosen point is also in `W`.
  refine ⟨⟨W, hW⟩, ?_⟩
  intro U hU
  have hξU : (ξ U : X) ∈ (U : Set X) := Classical.choose_spec (hclosure U U.2)
  exact hU hξU

/-- Lemma 1.10: a point belongs to the closure of a subset `C` exactly when there exists a
nonempty directed net with values in `C` that converges to that point. -/
-- Proof sketch: for the forward direction, index by the neighborhoods of `x` ordered by reverse
-- inclusion and choose one point of `C` in each neighborhood using closure membership; for the
-- reverse direction, a convergent net is eventually contained in every neighborhood of `x`, so
-- each neighborhood meets `C`.
theorem mem_closure_iff_exists_net_tendsto {X : Type u} [TopologicalSpace X] {C : Set X} {x : X} :
    x ∈ closure C ↔
      ∃ (A : Type u) (_ : Preorder A) (_ : IsDirectedOrder A) (_ : Nonempty A)
        (ξ : A → C), Tendsto (fun a ↦ (ξ a : X)) atTop (nhds x) := by
  constructor
  · intro hx
    -- Build the net by choosing one point of `C` in each neighborhood of `x`.
    exact exists_tendsto_subtype_of_mem_closure hx
  · rintro ⟨A, _, _, _, ξ, hξ⟩
    -- A convergent net whose values lie in `C` has limit in `closure C`.
    exact mem_closure_of_tendsto hξ <|
      Filter.Eventually.of_forall fun a ↦ (ξ a).2
