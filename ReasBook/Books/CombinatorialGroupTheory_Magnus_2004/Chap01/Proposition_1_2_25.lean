/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_23
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_24

universe u

open MulAction
open Proposition_1_2_24
open scoped Pointwise

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {F : Type u} [Group F] {ι : Type*}

/-- The diagonal conjugation action on a family of generated subgroups recovers the textbook
simultaneous conjugation-into predicate. -/
-- Layer: `bridge/view`.
-- `core/canonical`: the diagonal `ConjAct F` action on `ι → Subgroup F`, together with the
-- pointwise order on that family.
theorem exists_conjugator_for_generated_subgroup_family_le_iff_exists_smul_le
    (U V : ι → Finset F) :
    (∃ g : ConjAct F,
      g • (fun i ↦ Subgroup.closure (U i : Set F)) ≤ fun i ↦ Subgroup.closure (V i : Set F)) ↔
      ∃ g : F, ∀ i, generated_subgroup_conjugate_into_by g (U i) (V i) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨ConjAct.ofConjAct g, ?_⟩
    intro i
    simpa [generated_subgroup_conjugate_into_by, Pi.smul_apply,
      toConjAct_smul_subgroup_eq_mulAut_conj_smul] using hg i
  · rintro ⟨g, hg⟩
    refine ⟨ConjAct.toConjAct g, ?_⟩
    intro i
    simpa [generated_subgroup_conjugate_into_by, Pi.smul_apply,
      toConjAct_smul_subgroup_eq_mulAut_conj_smul] using hg i

/-- The diagonal conjugation action on a family of generated subgroups recovers the textbook
simultaneous exact-conjugacy predicate. -/
-- Layer: `bridge/view`.
-- `core/canonical`: `orbitRel (ConjAct F) (ι → Subgroup F)`.
theorem exists_conjugator_for_generated_subgroup_family_eq_iff_orbitRel
    (U V : ι → Finset F) :
    orbitRel (ConjAct F) (ι → Subgroup F)
      (fun i ↦ Subgroup.closure (V i : Set F))
      (fun i ↦ Subgroup.closure (U i : Set F)) ↔
      ∃ g : F, ∀ i,
        MulAut.conj g • Subgroup.closure (U i : Set F) = Subgroup.closure (V i : Set F) := by
  rw [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨ConjAct.ofConjAct g, ?_⟩
    intro i
    simpa [Pi.smul_apply, toConjAct_smul_subgroup_eq_mulAut_conj_smul] using congrFun hg i
  · rintro ⟨g, hg⟩
    refine ⟨ConjAct.toConjAct g, ?_⟩
    exact funext fun i ↦ by
      simpa [Pi.smul_apply, toConjAct_smul_subgroup_eq_mulAut_conj_smul] using hg i

end

noncomputable section

private def finsetLetters {ι : Type*} [DecidableEq ι] {F : Type*} [Group F]
    (basis : FreeGroupBasis ι F) (U : Finset F) : List ι :=
  U.toList.flatMap fun u ↦ (basis.repr u).toWord.map Prod.fst

private def signedLetters {ι : Type*} (letters : List ι) : List (ι × Bool) :=
  List.flatMap (fun a ↦ [(a, false), (a, true)]) letters

private def wordsOfLength {ι : Type*} (letters : List ι) : ℕ → List (List (ι × Bool))
  | 0 => [[]]
  | n + 1 =>
      List.flatMap
        (fun w ↦ (signedLetters letters).map fun a ↦ a :: w)
        (wordsOfLength letters n)

private def searchBound {ι : Type*} {F : Type u} [Group F] (basis : FreeGroupBasis ι F)
    [DecidableEq ι] (U : Finset F) : ℕ :=
  U.sum fun u ↦ FreeGroup.norm (basis.repr u)

private def candidateWords {ι : Type*} {F : Type u} [Group F] (basis : FreeGroupBasis ι F)
    [DecidableEq ι] (U : Finset F) : List (List (ι × Bool)) :=
  List.flatMap (wordsOfLength (finsetLetters basis U)) (List.range (searchBound basis U + 1))

private def candidateElements {ι : Type*} {F : Type u} [Group F] (basis : FreeGroupBasis ι F)
    [DecidableEq ι] [DecidableEq F] (U : Finset F) : Finset F :=
  ((candidateWords basis U).map fun w ↦ basis.repr.symm (FreeGroup.mk w)).toFinset

private def candidateTuples {ι : Type*} {F : Type u} [Group F] (basis : FreeGroupBasis ι F)
    [DecidableEq ι] [DecidableEq F] (U : Finset F) (n : ℕ) : Finset (Fin n → F) := by
  classical
  let _ : Fintype {x // x ∈ candidateElements basis U} := by infer_instance
  exact
    (Finset.univ : Finset (Fin n → {x // x ∈ candidateElements basis U})).image fun f i ↦
      (f i : F)

private def tupleBasisOfClosure {F : Type u} [Group F] {n : ℕ} (u : Fin n → F) : Prop :=
  IsFreeGroupBasis {x : Subgroup.closure (Set.range u) | (x : F) ∈ Set.range u}

private def tuplePresentsGeneratedSubgroup {F : Type u} [Group F] {n : ℕ}
    (U : Finset F) (u : Fin n → F) : Prop :=
  tupleBasisOfClosure u ∧ Subgroup.closure (Set.range u) = Subgroup.closure (U : Set F)

private def tupleLiesInGeneratedSubgroup {F : Type u} [Group F] {n : ℕ}
    (V : Finset F) (v : Fin n → F) : Prop :=
  ∀ i, v i ∈ Subgroup.closure (V : Set F)

private def appendTuplePair {F : Type*} [Group F]
    (uv₁ : Σ m, (Fin m → F) × (Fin m → F))
    (uv₂ : Σ n, (Fin n → F) × (Fin n → F)) :
    Σ p, (Fin p → F) × (Fin p → F) :=
  match uv₁, uv₂ with
  | ⟨m, uv₁⟩, ⟨n, uv₂⟩ =>
      ⟨m + n, (Fin.append uv₁.1 uv₂.1, Fin.append uv₁.2 uv₂.2)⟩

section Search

variable {ι : Type*} [DecidableEq ι] {F : Type u} [Group F] [IsFreeGroup F]

private noncomputable def candidateTuplePairsInto (basis : FreeGroupBasis ι F)
    [DecidableEq F] (U V : Finset F) : List (Σ m, (Fin m → F) × (Fin m → F)) := by
  classical
  exact
    (List.range (U.card + 1)).flatMap fun m ↦
      (((candidateTuples basis U m).product (candidateTuples basis V m)).toList).filterMap fun uv ↦
        letI := generated_subgroup_membership_decidable V
        if tuplePresentsGeneratedSubgroup U uv.1 ∧ tupleLiesInGeneratedSubgroup V uv.2 then
          some ⟨m, (uv.1, uv.2)⟩
        else
          none

private noncomputable def candidateTuplePairsEq (basis : FreeGroupBasis ι F)
    [DecidableEq F] (U V : Finset F) : List (Σ m, (Fin m → F) × (Fin m → F)) := by
  classical
  exact
    (List.range (Nat.min U.card V.card + 1)).flatMap fun m ↦
      (((candidateTuples basis U m).product (candidateTuples basis V m)).toList).filterMap fun uv ↦
        if tuplePresentsGeneratedSubgroup U uv.1 ∧ tuplePresentsGeneratedSubgroup V uv.2 then
          some ⟨m, (uv.1, uv.2)⟩
        else
          none

private noncomputable def familyTuplePairsInto (basis : FreeGroupBasis ι F) [DecidableEq F] :
    List (Finset F × Finset F) → List (Σ m, (Fin m → F) × (Fin m → F))
  | [] => [⟨0, (Fin.elim0, Fin.elim0)⟩]
  | (U, V) :: UVs =>
      (candidateTuplePairsInto basis U V).flatMap fun head ↦
        (familyTuplePairsInto basis UVs).map fun tail ↦ appendTuplePair head tail

private noncomputable def familyTuplePairsEq (basis : FreeGroupBasis ι F) [DecidableEq F] :
    List (Finset F × Finset F) → List (Σ m, (Fin m → F) × (Fin m → F))
  | [] => [⟨0, (Fin.elim0, Fin.elim0)⟩]
  | (U, V) :: UVs =>
      (candidateTuplePairsEq basis U V).flatMap fun head ↦
        (familyTuplePairsEq basis UVs).map fun tail ↦ appendTuplePair head tail

private noncomputable def generatedSubgroupFamilyConjugateIntoSearch {n : ℕ}
    (basis : FreeGroupBasis ι F) [DecidableEq F] (U V : Fin n → Finset F) : Bool := by
  classical
  exact
    (familyTuplePairsInto basis ((List.finRange n).map fun i ↦ (U i, V i))).any fun
      | ⟨_, uv⟩ =>
          letI := exists_common_conjugator_decidable uv.1 uv.2
          decide (∃ g : F, ∀ i, g⁻¹ * uv.1 i * g = uv.2 i)

private noncomputable def generatedSubgroupFamilyConjugateSearch {n : ℕ}
    (basis : FreeGroupBasis ι F) [DecidableEq F] (U V : Fin n → Finset F) : Bool := by
  classical
  exact
    (familyTuplePairsEq basis ((List.finRange n).map fun i ↦ (U i, V i))).any fun
      | ⟨_, uv⟩ =>
          letI := exists_common_conjugator_decidable uv.1 uv.2
          decide (∃ g : F, ∀ i, g⁻¹ * uv.1 i * g = uv.2 i)

private theorem exists_conjugator_for_generated_subgroup_family_le_iff_search_true
    (basis : FreeGroupBasis ι F) [DecidableEq F] {n : ℕ} (U V : Fin n → Finset F) :
    (∃ g : F, ∀ i, generated_subgroup_conjugate_into_by g (U i) (V i)) ↔
      generatedSubgroupFamilyConjugateIntoSearch basis U V = true := by
  sorry

private theorem generated_subgroup_family_conjugate_iff_search_true
    (basis : FreeGroupBasis ι F) [DecidableEq F] {n : ℕ} (U V : Fin n → Finset F) :
    orbitRel (ConjAct F) (Fin n → Subgroup F)
      (fun i ↦ Subgroup.closure (V i : Set F))
      (fun i ↦ Subgroup.closure (U i : Set F)) ↔
      generatedSubgroupFamilyConjugateSearch basis U V = true := by
  sorry

end Search

section Decidable

variable {F : Type u} [Group F] [IsFreeGroup F] {ι : Type*} [Fintype ι]

private theorem exists_forall_iff_exists_forall_reindex {α ι κ : Type*} (e : ι ≃ κ)
    (P : α → ι → Prop) :
    (∃ a : α, ∀ i : ι, P a i) ↔ ∃ a : α, ∀ j : κ, P a (e.symm j) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun j ↦ ha (e.symm j)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun i ↦ by simpa using ha (e i)⟩

/-- Proposition 1-2-25 (1): in a free group, it is decidable whether one element conjugates each
generated subgroup `U i` into the corresponding generated subgroup `V i` for a finite family.

This public API keeps the source-facing family predicate. Its implementation searches finite tuple
presentations of the finitely generated subgroups `Gp(U i)` and uses the chapter owner abstraction
`exists_common_conjugator_decidable` to test whether one conjugator works for the concatenated
tuple family. The search only uses letters that actually occur in the finite input subsets, so no
ambient finite-rank hypothesis appears in the public statement. The companion bridge theorem
`exists_conjugator_for_generated_subgroup_family_le_iff_exists_smul_le` identifies the
proposition with the canonical diagonal `ConjAct F` action on the family of generated subgroups. -/
-- Layer: `source-facing`.
-- `core/canonical`: the diagonal `ConjAct F` action on `ι → Subgroup F`.
-- `bridge/view`: `exists_conjugator_for_generated_subgroup_family_le_iff_exists_smul_le`.
noncomputable def exists_conjugator_for_generated_subgroup_family_le_decidable
    (U V : ι → Finset F) :
    Decidable (∃ g : F, ∀ i, generated_subgroup_conjugate_into_by g (U i) (V i)) := by
  let _ : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq F
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let U' : Fin (Fintype.card ι) → Finset F := fun i ↦ U (e.symm i)
  let V' : Fin (Fintype.card ι) → Finset F := fun i ↦ V (e.symm i)
  let basis : FreeGroupBasis (IsFreeGroup.Generators F) F := IsFreeGroup.basis F
  exact
    decidable_of_iff
      (generatedSubgroupFamilyConjugateIntoSearch basis U' V' = true)
      ((exists_forall_iff_exists_forall_reindex e
          (fun g i ↦ generated_subgroup_conjugate_into_by g (U i) (V i))).trans
        (exists_conjugator_for_generated_subgroup_family_le_iff_search_true basis U' V')).symm

/-- Proposition 1-2-25 (2): in a free group, it is decidable whether the family of generated
subgroups attached to `U` and `V` are simultaneously conjugate for a finite family.

This public statement is centered on the canonical diagonal conjugation-action orbit relation on
`ι → Subgroup F`. As above, the implementation searches finite tuple presentations of the
input-generated subgroups and delegates the common-conjugator test to the chapter's tuple owner
abstraction. The Lean owner here remains the orbit predicate itself; the companion bridge theorem
`exists_conjugator_for_generated_subgroup_family_eq_iff_orbitRel` recovers the textbook
existential formulation. -/
-- Layer: `source-facing` exact conjugacy through the owner relation on families of subgroups.
-- `core/canonical`: `orbitRel (ConjAct F) (ι → Subgroup F)`.
-- `bridge/view`: `exists_conjugator_for_generated_subgroup_family_eq_iff_orbitRel`.
noncomputable def generated_subgroup_family_conjugate_decidable
    (U V : ι → Finset F) :
    Decidable
      (orbitRel (ConjAct F) (ι → Subgroup F)
        (fun i ↦ Subgroup.closure (V i : Set F))
        (fun i ↦ Subgroup.closure (U i : Set F))) := by
  let _ : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq F
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let U' : Fin (Fintype.card ι) → Finset F := fun i ↦ U (e.symm i)
  let V' : Fin (Fintype.card ι) → Finset F := fun i ↦ V (e.symm i)
  let basis : FreeGroupBasis (IsFreeGroup.Generators F) F := IsFreeGroup.basis F
  have h_orbit :
      orbitRel (ConjAct F) (ι → Subgroup F)
          (fun i ↦ Subgroup.closure (V i : Set F))
          (fun i ↦ Subgroup.closure (U i : Set F)) ↔
        orbitRel (ConjAct F) (Fin (Fintype.card ι) → Subgroup F)
          (fun i ↦ Subgroup.closure (V' i : Set F))
          (fun i ↦ Subgroup.closure (U' i : Set F)) := by
    exact
      ((exists_conjugator_for_generated_subgroup_family_eq_iff_orbitRel U V).trans
        (exists_forall_iff_exists_forall_reindex e
          (fun g i ↦ ConjAct.toConjAct g • Subgroup.closure (U i : Set F) =
            Subgroup.closure (V i : Set F)))).trans
        (exists_conjugator_for_generated_subgroup_family_eq_iff_orbitRel U' V').symm
  exact
    decidable_of_iff
      (generatedSubgroupFamilyConjugateSearch basis U' V' = true)
      (h_orbit.trans (generated_subgroup_family_conjugate_iff_search_true basis U' V')).symm

end Decidable

end
