module

import stacks_project.Chap05.Lemma_5_13_5
import Mathlib.Tactic.Recall
public import Mathlib.Topology.Sets.Opens
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.ShrinkingLemma

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace
open scoped Topology

universe u v

section

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable {I : Type v}

/- Domain-style sampling for shrinking open covers along a compact subset:
- primary domain: shrinking lemmas in locally compact Hausdorff spaces
- same-domain declarations inspected:
  `TopologicalSpace.IsOpenCover.exists_shrinking`,
  `TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement`,
  `IsCompact.exists_open_between_and_isCompact_closure`,
  `exists_iUnion_eq_closure_subset`
- best owner abstraction: `IsCompact`

Layer triage:
- `source-facing`: the Stacks lemma below, which attaches prescribed tuplewise intersections to a
  fixed compact subset `Z`
- `core/canonical`: the compact-normal tuplewise shrinking owner
  `TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement`, together with the compact
  lifting API `IsCompact.exists_open_between_and_isCompact_closure`
- `bridge/view`: the ambient shrinking family `V`, whose cover property, closure control, and
  tuplewise containment are all derived from the compact owner data on the subtype of `Z`

Primitive data are exactly the compact subset `Z`, the ambient open family `U`, the prescribed
tuplewise opens `W`, and the two compatibility hypotheses on `Z`. The shrinking family `V` and its
closure/intersection properties are derived output, so the public API should live on the compact
owner `IsCompact` rather than as a parallel global wrapper.
-/

namespace IsCompact

/- Companion recall: the compact-normal tuplewise shrinking owner for open covers is the
chapter theorem `TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement`; the compact
subset theorem below is the corresponding source-facing bridge, used through the owner call shape
`hZ.exists_open_shrinking_with_prescribed_intersections`. -/
recall TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement

/-- A shrinking of an open family whose closures stay in the ambient opens and whose
`(p + 1)`-fold intersections land in the prescribed opens along a compact subset. -/
class IsOpenShrinkingWithPrescribedIntersections
    (Z : Set X) (p : ℕ) (U : I → Opens X) (W : (Fin (p + 1) → I) → Opens X)
    (V : I → Opens X) : Prop where
  /-- The shrunken opens still cover the compact subset. -/
  cover : Z ⊆ ⋃ i, V i
  /-- The closure of each shrunken open stays inside the corresponding ambient open. -/
  closure_subset (i : I) : closure (V i : Set X) ⊆ U i
  /-- Every `(p + 1)`-fold intersection of the shrunken family lands in the prescribed open. -/
  tuplewise_subset (σ : Fin (p + 1) → I) : (⋂ j, (V (σ j) : Set X)) ⊆ W σ

/-- Helper for Lemma 5.13.6: compactness of `Z` reduces the ambient cover to finitely many
indices, reindexed by the corresponding subtype. -/
private lemma finite_support_reduction
    {Z : Set X} (hZ : IsCompact Z) (U : I → Opens X) (hcover : Z ⊆ ⋃ i, U i) :
    ∃ s : Finset I, Z ⊆ ⋃ i : {i // i ∈ s}, (U i.1 : Set X) := by
  -- Extract a finite subcover of `Z`, then rewrite it as a subtype-indexed union.
  obtain ⟨s, hs⟩ :=
    hZ.elim_finite_subcover (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) hcover
  refine ⟨s, ?_⟩
  intro z hz
  rcases mem_iUnion₂.1 (hs hz) with ⟨i, hi, hzi⟩
  exact mem_iUnion.2 ⟨⟨i, hi⟩, hzi⟩

/-- Helper for Lemma 5.13.6: extending a subtype-indexed shrinking by `⊥` outside the chosen
finite support preserves the cover, closure, and tuplewise containment data. -/
private lemma extend_by_bot_preserves_shrinking_data
    [DecidableEq I] {Z : Set X} {p : ℕ} {s : Finset I} {U : I → Opens X}
    {W : (Fin (p + 1) → I) → Opens X} {V₀ : {i // i ∈ s} → Opens X}
    (hV₀ :
      IsOpenShrinkingWithPrescribedIntersections Z p
        (fun i : {i // i ∈ s} ↦ U i.1)
        (fun σ : Fin (p + 1) → {i // i ∈ s} ↦ W (fun j ↦ (σ j).1))
        V₀) :
    IsOpenShrinkingWithPrescribedIntersections Z p U W
      (fun i ↦ if hi : i ∈ s then V₀ ⟨i, hi⟩ else ⊥) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- The cover over the finite subtype is unchanged after extending by empty opens.
    intro z hz
    rcases mem_iUnion.1 (hV₀.cover hz) with ⟨i, hzi⟩
    refine mem_iUnion.2 ⟨i.1, ?_⟩
    simpa using hzi
  · -- Closure control is immediate on supported indices and trivial outside the support.
    intro i
    by_cases hi : i ∈ s
    · simpa [hi] using hV₀.closure_subset ⟨i, hi⟩
    · intro x hx
      have hx' : x ∈ closure ((⊥ : Opens X) : Set X) := by
        simpa [hi] using hx
      have hclosure : closure (((⊥ : Opens X) : Set X)) = (∅ : Set X) := by
        change closure (∅ : Set X) = ∅
        exact closure_empty
      have : x ∈ (∅ : Set X) := by
        simpa [hclosure] using hx'
      exact False.elim this
  · -- If every tuple entry lies in the support, reduce to the subtype theorem; otherwise the
    -- tuple intersection is empty because one factor is `⊥`.
    intro σ
    by_cases hσ : ∀ j, σ j ∈ s
    · let σ₀ : Fin (p + 1) → {i // i ∈ s} := fun j ↦ ⟨σ j, hσ j⟩
      simpa [σ₀, hσ] using hV₀.tuplewise_subset σ₀
    · have hσ' : ∃ j, σ j ∉ s := by
        simpa [not_forall] using hσ
      rcases hσ' with ⟨j, hj⟩
      intro x hx
      have hxj : x ∈ ((fun i ↦ if hi : i ∈ s then V₀ ⟨i, hi⟩ else ⊥) (σ j) : Set X) :=
        mem_iInter.1 hx j
      have : False := by
        simpa [hj] using hxj
      exact False.elim this

/-- Helper for Lemma 5.13.6: the case `p = 0` comes from shrinking a finite subcover of the
prescribed singleton neighborhoods. -/
private theorem exists_open_shrinking_with_prescribed_intersections_zero
    {Z : Set X} (hZ : IsCompact Z) (U : I → Opens X) (W : (Fin 1 → I) → Opens X)
    (hcover : Z ⊆ ⋃ i, U i)
    (hW_subset : ∀ σ, (W σ : Set X) ⊆ ⋂ j, U (σ j))
    (hW_on_Z : ∀ σ, (W σ : Set X) ∩ Z = (⋂ j, U (σ j)) ∩ Z) :
    ∃ V : I → Opens X, IsOpenShrinkingWithPrescribedIntersections Z 0 U W V := by
  classical
  obtain ⟨s, hscover⟩ := finite_support_reduction (Z := Z) hZ U hcover
  let I₀ := {i // i ∈ s}
  let W₀ : I₀ → Set X := fun i ↦ W (fun _ : Fin 1 ↦ i.1)
  have hW₀_open : ∀ i : I₀, IsOpen (W₀ i) := by
    intro i
    exact (W (fun _ : Fin 1 ↦ i.1)).isOpen
  have hW₀_cover : Z ⊆ ⋃ i : I₀, W₀ i := by
    -- On `Z`, the prescribed singleton open agrees with the original ambient open.
    intro z hz
    rcases mem_iUnion.1 (hscover hz) with ⟨i, hzi⟩
    refine mem_iUnion.2 ⟨i, ?_⟩
    have hzWZ : z ∈ (W (fun _ : Fin 1 ↦ i.1) : Set X) ∩ Z := by
      rw [hW_on_Z (fun _ : Fin 1 ↦ i.1)]
      refine ⟨?_, hz⟩
      refine mem_iInter.2 ?_
      intro j
      fin_cases j
      simpa using hzi
    exact hzWZ.1
  have hW₀_finite : ∀ x ∈ Z, { i : I₀ | x ∈ W₀ i }.Finite := by
    -- The reduced index type is finite, so the point-finiteness hypothesis is automatic.
    intro x hx
    classical
    exact Set.finite_univ.subset fun _ _ ↦ by simp
  obtain ⟨v₀, hv₀_cover, hv₀_open, hv₀_closure, _⟩ :=
    exists_subset_iUnion_closure_subset_t2space hZ hW₀_open hW₀_finite hW₀_cover
  let V₀ : I₀ → Opens X := fun i ↦ ⟨v₀ i, hv₀_open i⟩
  have hV₀ :
      IsOpenShrinkingWithPrescribedIntersections Z 0
        (fun i : I₀ ↦ U i.1)
        (fun σ : Fin 1 → I₀ ↦ W (fun j ↦ (σ j).1))
        V₀ := by
    refine ⟨hv₀_cover, ?_, ?_⟩
    · -- The singleton prescribed opens already sit inside the corresponding ambient opens.
      intro i
      exact (hv₀_closure i).trans <| by
        intro x hx
        have hxU : x ∈ ⋂ j : Fin 1, (U i.1 : Set X) := hW_subset (fun _ : Fin 1 ↦ i.1) hx
        simpa using (mem_iInter.1 hxU) 0
    · -- A `1`-fold intersection is just one member of the family.
      intro σ x hx
      have hx0 : x ∈ (V₀ (σ 0) : Set X) := by
        simpa using (mem_iInter.1 hx) 0
      have hxClosure : x ∈ closure (V₀ (σ 0) : Set X) := subset_closure hx0
      have hxW : x ∈ W (fun _ : Fin 1 ↦ (σ 0).1) :=
        hv₀_closure (σ 0) hxClosure
      have hσ : (fun j : Fin 1 ↦ (σ j).1) = fun _ : Fin 1 ↦ (σ 0).1 := by
        funext j
        fin_cases j
        rfl
      simpa [hσ] using hxW
  refine ⟨fun i ↦ if hi : i ∈ s then V₀ ⟨i, hi⟩ else ⊥, ?_⟩
  -- Returning to the original index type only adds empty opens outside the finite support.
  exact extend_by_bot_preserves_shrinking_data (Z := Z) (p := 0) (s := s)
    (U := U) (W := W) (V₀ := V₀) hV₀

/-- Helper for Lemma 5.13.6: for a finite index type, first shrink the ambient cover around `Z`,
then remove the finitely many closed bad intersections in one step. -/
private theorem exists_open_shrinking_with_prescribed_intersections_finite
    [Fintype I] {Z : Set X} (hZ : IsCompact Z) (p : ℕ) (U : I → Opens X)
    (W : (Fin (p + 1) → I) → Opens X)
    (hcover : Z ⊆ ⋃ i, U i)
    (hW_subset : ∀ σ, (W σ : Set X) ⊆ ⋂ j, U (σ j))
    (hW_on_Z : ∀ σ, (W σ : Set X) ∩ Z = (⋂ j, U (σ j)) ∩ Z) :
    ∃ V : I → Opens X, IsOpenShrinkingWithPrescribedIntersections Z p U W V := by
  classical
  have hU_finite : ∀ x ∈ Z, { i : I | x ∈ (U i : Set X) }.Finite := by
    -- A finite index type makes the point-finiteness hypothesis automatic.
    intro x hx
    exact Set.finite_univ.subset fun _ _ ↦ by simp
  obtain ⟨o, ho_cover, ho_open, ho_closure, _⟩ :=
    exists_subset_iUnion_closure_subset_t2space hZ (fun i ↦ (U i).isOpen) hU_finite hcover
  let O : I → Opens X := fun i ↦ ⟨o i, ho_open i⟩
  have hO_cover : Z ⊆ ⋃ i, (O i : Set X) := by
    -- The shrinking still covers the compact set `Z`.
    simpa [O] using ho_cover
  have hO_closure : ∀ i, closure (O i : Set X) ⊆ U i := by
    -- Each shrunk open has closure inside the corresponding ambient open.
    intro i
    simpa [O] using ho_closure i
  let bad : (Fin (p + 1) → I) → Set X :=
    fun σ ↦ closure ((⋂ j, (O (σ j) : Set X)) \ (W σ : Set X))
  have hbad_closed : ∀ σ : Fin (p + 1) → I, IsClosed (bad σ) := by
    -- By construction each bad set is a closure.
    intro σ
    exact isClosed_closure
  have hbad_disjoint_Z : ∀ σ : Fin (p + 1) → I, Disjoint (bad σ) Z := by
    intro σ
    refine disjoint_left.2 fun x hxBad hxZ ↦ ?_
    have hxW : x ∈ W σ := by
      -- Every bad closure point lying on `Z` already belongs to the prescribed open by the
      -- equality hypothesis along `Z`.
      have hxInter : x ∈ ⋂ j, U (σ j) := by
        refine mem_iInter.2 ?_
        intro j
        have hsubset :
            ((⋂ k, (O (σ k) : Set X)) \ (W σ : Set X)) ⊆ (O (σ j) : Set X) := by
          intro y hy
          exact mem_iInter.1 hy.1 j
        exact hO_closure (σ j) (closure_mono hsubset hxBad)
      have hxWZ : x ∈ (W σ : Set X) ∩ Z := by
        rw [hW_on_Z σ]
        exact ⟨hxInter, hxZ⟩
      exact hxWZ.1
    rcases mem_closure_iff.1 hxBad (W σ : Set X) (W σ).isOpen hxW with ⟨y, hyW, hyBad⟩
    exact hyBad.2 hyW
  let C : I → Set X := fun i ↦ ⋃ σ : Fin (p + 1) → I, if ∃ j, σ j = i then bad σ else ∅
  have hC_closed : ∀ i : I, IsClosed (C i) := by
    -- Only finitely many tuples occur, so each repaired closed set is a finite union.
    intro i
    exact isClosed_iUnion_of_finite fun σ ↦ by
      by_cases hσ : ∃ j, σ j = i
      · simpa [C, hσ] using hbad_closed σ
      · simp [C, hσ]
  have hC_disjoint_Z : ∀ i : I, Disjoint (C i) Z := by
    intro i
    refine disjoint_left.2 fun x hxC hxZ ↦ ?_
    rcases mem_iUnion.1 hxC with ⟨σ, hxσ⟩
    by_cases hσ : ∃ j, σ j = i
    · have hxBad : x ∈ bad σ := by
        simpa [C, hσ] using hxσ
      exact (Set.disjoint_left.1 (hbad_disjoint_Z σ)) hxBad hxZ
    · simp [C, hσ] at hxσ
  let V : I → Opens X := fun i ↦ ⟨(O i : Set X) \ C i, (O i).isOpen.sdiff (hC_closed i)⟩
  refine ⟨V, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Removing closed bad sets does not change the cover on `Z` because those bad sets miss `Z`.
    intro z hz
    rcases mem_iUnion.1 (hO_cover hz) with ⟨i, hzi⟩
    refine mem_iUnion.2 ⟨i, ?_⟩
    refine ⟨hzi, ?_⟩
    intro hzC
    exact (Set.disjoint_left.1 (hC_disjoint_Z i)) hzC hz
  · -- The final family is obtained by shrinking the original shrinking, so the closure bound
    -- survives by monotonicity.
    intro i
    exact (closure_mono fun x hx ↦ hx.1).trans (hO_closure i)
  · -- If a tuple intersection still missed the prescribed open, then its bad set would have been
    -- subtracted from the first coordinate.
    intro σ x hx
    by_contra hxW
    have hxO : x ∈ ⋂ j, (O (σ j) : Set X) := by
      refine mem_iInter.2 ?_
      intro j
      exact ((mem_iInter.1 hx) j).1
    have hxBadMem : x ∈ ((⋂ j, (O (σ j) : Set X)) \ (W σ : Set X)) := ⟨hxO, hxW⟩
    have hxBad : x ∈ bad σ := subset_closure hxBadMem
    have hxC : x ∈ C (σ 0) := by
      refine mem_iUnion.2 ⟨σ, ?_⟩
      have hσ0 : ∃ j, σ j = σ 0 := ⟨0, rfl⟩
      simpa [C, hσ0] using hxBad
    exact ((mem_iInter.1 hx) 0).2 hxC

/-- Lemma 5.13.6: a compact subset `Z` of a locally compact Hausdorff space, covered by opens
`U i` with prescribed `(p + 1)`-fold neighborhoods along `Z`, admits an open shrinking whose
closures stay in `U i` and whose `(p + 1)`-fold intersections land in the prescribed opens. -/
-- Proof sketch: reduce to the finite, quasi-compact case, then argue by induction on `p`; use
-- Lemma 5.13.4 to obtain the base-case shrinking, and in the induction step remove finitely many
-- closed error sets from the chosen opens to force the required intersection containments.
theorem exists_open_shrinking_with_prescribed_intersections
    {Z : Set X} (hZ : IsCompact Z) (p : ℕ) (U : I → Opens X)
    (W : (Fin (p + 1) → I) → Opens X)
    (hcover : Z ⊆ ⋃ i, U i)
    (hW_subset : ∀ σ, (W σ : Set X) ⊆ ⋂ j, U (σ j))
    (hW_on_Z : ∀ σ, (W σ : Set X) ∩ Z = (⋂ j, U (σ j)) ∩ Z) :
    ∃ V : I → Opens X, IsOpenShrinkingWithPrescribedIntersections Z p U W V := by
  classical
  obtain ⟨s, hscover⟩ := finite_support_reduction (Z := Z) hZ U hcover
  let I₀ := {i // i ∈ s}
  let U₀ : I₀ → Opens X := fun i ↦ U i.1
  let W₀ : (Fin (p + 1) → I₀) → Opens X := fun σ ↦ W (fun j ↦ (σ j).1)
  have hscover₀ : Z ⊆ ⋃ i : I₀, (U₀ i : Set X) := by
    -- The chosen finite subcover is the finite-index ambient problem we now solve.
    simpa [I₀, U₀] using hscover
  have hW_subset₀ : ∀ σ : Fin (p + 1) → I₀, (W₀ σ : Set X) ⊆ ⋂ j, U₀ (σ j) := by
    -- The tuplewise ambient containment is unchanged after restricting to the finite subtype.
    intro σ
    simpa [W₀, U₀] using hW_subset (fun j ↦ (σ j).1)
  have hW_on_Z₀ : ∀ σ : Fin (p + 1) → I₀,
      (W₀ σ : Set X) ∩ Z = (⋂ j, U₀ (σ j)) ∩ Z := by
    -- The prescribed opens still agree with the ambient intersections along `Z`.
    intro σ
    simpa [W₀, U₀] using hW_on_Z (fun j ↦ (σ j).1)
  haveI : Fintype I₀ := inferInstance
  obtain ⟨V₀, hV₀⟩ :=
    exists_open_shrinking_with_prescribed_intersections_finite
      (X := X) (I := I₀) (Z := Z) hZ p U₀ W₀ hscover₀ hW_subset₀ hW_on_Z₀
  refine ⟨fun i ↦ if hi : i ∈ s then V₀ ⟨i, hi⟩ else ⊥, ?_⟩
  -- Route correction: instead of an explicit induction on tuple cardinality, solve the finite
  -- support problem directly and subtract all bad tuple closures at once.
  exact extend_by_bot_preserves_shrinking_data
    (Z := Z) (p := p) (s := s) (U := U) (W := W) (V₀ := V₀) hV₀

end IsCompact

end
