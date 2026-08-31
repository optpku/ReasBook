module

public import Mathlib.Topology.NoetherianSpace
public import stacks_project.Chap05.Definition_5_28_2
import Mathlib.Topology.LocallyClosed

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace

section

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for finite good refinements of locally closed partitions in Noetherian
spaces:
- primary domain: Noetherian topological spaces, indexed stratifications, and good locally closed
  partitions
- inspected same-domain declarations:
  `LocallyClosedPartition.exists_finite_stratification_refining`,
  `IsStratification.toLocallyClosedPartition`,
  `IsStratification.toLocallyClosedPartition_isGood`, and
  `locallyFinite_of_finite`
- best owner abstraction: `LocallyClosedPartition.IsGood`

Layer triage:
- `source-facing`: the existence of a finite good refinement of a finite locally closed partition
  in a Noetherian space
- `core/canonical`: `LocallyClosedPartition.IsGood`
- `bridge/view`: the passage from a finite indexed stratification to its partition view via
  `IsStratification.toLocallyClosedPartition`

Primitive data are the Noetherian ambient space and the finite locally closed partition `P`.  The
source proof uses Noetherian induction to build a refinement satisfying the good frontier condition;
that condition is not a formal consequence of an arbitrary finite indexed stratification.
-/

/-- A finite good refinement of `P` is a refining locally closed partition that is both finite and
good. -/
class LocallyClosedPartition.IsFiniteGoodRefinement
    (Q P : LocallyClosedPartition X) : Prop where
  finite : Q.toSet.Finite
  refinement : Q ≤ P
  good : LocallyClosedPartition.IsGood Q


/-- A finite locally closed partition of an ambient subset `C`, with all parts kept as
subsets of the original space. This avoids changing closure notions during the Noetherian
induction. -/
structure LCPartitionOn (C : Set X) where
  parts : Set (Set X)
  finite : parts.Finite
  nonempty : ∀ ⦃S : Set X⦄, S ∈ parts → S.Nonempty
  subset_closed : ∀ ⦃S : Set X⦄, S ∈ parts → S ⊆ C
  cover : C ⊆ ⋃₀ parts
  pairwise : parts.PairwiseDisjoint id
  locallyClosed : ∀ ⦃S : Set X⦄, S ∈ parts → IsLocallyClosed S

namespace LCPartitionOn

theorem isPartition_univ (A : LCPartitionOn (Set.univ : Set X)) : Setoid.IsPartition A.parts := by
  refine Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty A.pairwise ?_ ?_
  · intro x
    have hx : x ∈ ⋃₀ A.parts := A.cover (by simp)
    simpa [Set.mem_sUnion] using hx
  · intro hEmpty
    exact (A.nonempty hEmpty).ne_empty rfl

noncomputable def toLocallyClosedPartition (A : LCPartitionOn (Set.univ : Set X)) : LocallyClosedPartition X where
  toPartitions := ⟨A.parts, A.isPartition_univ⟩
  locallyClosed := by
    intro S
    exact A.locallyClosed S.2

noncomputable def ofLocallyClosedPartition (P : LocallyClosedPartition X) (hPfinite : P.toSet.Finite) :
    LCPartitionOn (Set.univ : Set X) where
  parts := P.toSet
  finite := hPfinite
  nonempty := by
    intro S hS
    exact Setoid.nonempty_of_mem_partition P.isPartition hS
  subset_closed := by
    intro S hS x hx
    simp
  cover := by
    intro x hx
    rcases P.isPartition.2 x with ⟨S, ⟨hS, hxS⟩, _⟩
    exact Set.mem_sUnion.2 ⟨S, hS, hxS⟩
  pairwise := P.isPartition.pairwiseDisjoint
  locallyClosed := by
    intro S hS
    exact P.locallyClosed_of_mem hS

noncomputable def empty : LCPartitionOn (∅ : Set X) where
  parts := ∅
  finite := Set.finite_empty
  nonempty := by simp
  subset_closed := by simp
  cover := by simp
  pairwise := Set.pairwiseDisjoint_empty
  locallyClosed := by simp

/-- Split the closed complement by `closure U`, matching the boundary split in the Stacks
proof before applying the induction hypothesis. -/
noncomputable def splitByClosure {C U : Set X} (A : LCPartitionOn C)
    (hDclosed : IsClosed (C \ U)) : LCPartitionOn (C \ U) where
  parts := {R | ∃ p : A.parts × Bool,
    R = (p.1.1 ∩ (C \ U) ∩ if p.2 then closure U else (closure U)ᶜ) ∧ R.Nonempty}
  finite := by
    letI : Fintype A.parts := A.finite.fintype
    let raw : A.parts × Bool → Set X := fun p =>
      p.1.1 ∩ (C \ U) ∩ if p.2 then closure U else (closure U)ᶜ
    have hraw : (Set.range raw).Finite := Set.finite_range raw
    refine hraw.subset ?_
    intro R hR
    rcases hR with ⟨p, hEq, hne⟩
    exact ⟨p, hEq.symm⟩
  nonempty := by
    intro R hR
    rcases hR with ⟨p, hEq, hne⟩
    exact hne
  subset_closed := by
    intro R hR
    rcases hR with ⟨p, rfl, hne⟩
    intro x hx
    exact hx.1.2
  cover := by
    intro x hxD
    have hxC : x ∈ C := hxD.1
    have hxcover : x ∈ ⋃₀ A.parts := A.cover hxC
    rcases Set.mem_sUnion.1 hxcover with ⟨S, hS, hxS⟩
    by_cases hxcl : x ∈ closure U
    · let p : A.parts × Bool := (⟨S, hS⟩, true)
      let R : Set X := S ∩ (C \ U) ∩ closure U
      refine Set.mem_sUnion.2 ⟨R, ?_, ?_⟩
      · refine ⟨p, ?_, ⟨x, ?_⟩⟩
        · simp [p, R]
        · exact ⟨⟨hxS, hxD⟩, hxcl⟩
      · exact ⟨⟨hxS, hxD⟩, hxcl⟩
    · let p : A.parts × Bool := (⟨S, hS⟩, false)
      let R : Set X := S ∩ (C \ U) ∩ (closure U)ᶜ
      refine Set.mem_sUnion.2 ⟨R, ?_, ?_⟩
      · refine ⟨p, ?_, ⟨x, ?_⟩⟩
        · simp [p, R]
        · exact ⟨⟨hxS, hxD⟩, hxcl⟩
      · exact ⟨⟨hxS, hxD⟩, hxcl⟩
  pairwise := by
    intro R hR R' hR' hneq
    refine Set.disjoint_left.2 ?_
    intro x hxR hxR'
    rcases hR with ⟨p, hpR, hpne⟩
    rcases hR' with ⟨q, hqR, hqne⟩
    subst R
    subst R'
    have hpSide : x ∈ if p.2 then closure U else (closure U)ᶜ := hxR.2
    have hqSide : x ∈ if q.2 then closure U else (closure U)ᶜ := hxR'.2
    have hpart : p.1 = q.1 := by
      apply Subtype.ext
      exact A.pairwise.elim_set p.1.2 q.1.2 x hxR.1.1 hxR'.1.1
    have hbool : p.2 = q.2 := by
      cases hp : p.2 <;> cases hq : q.2
      · rfl
      · have hpSideCompl : x ∈ (closure U)ᶜ := by simpa [hp] using hpSide
        have hqSideClosed : x ∈ closure U := by simpa [hq] using hqSide
        exact False.elim (hpSideCompl hqSideClosed)
      · have hpSideClosed : x ∈ closure U := by simpa [hp] using hpSide
        have hqSideCompl : x ∈ (closure U)ᶜ := by simpa [hq] using hqSide
        exact False.elim (hqSideCompl hpSideClosed)
      · rfl
    apply hneq
    cases p
    cases q
    simp_all
  locallyClosed := by
    intro R hR
    rcases hR with ⟨p, rfl, hne⟩
    by_cases hb : p.2
    · simpa [hb] using ((A.locallyClosed p.1.2).inter hDclosed.isLocallyClosed).inter isClosed_closure.isLocallyClosed
    · simpa [hb] using ((A.locallyClosed p.1.2).inter hDclosed.isLocallyClosed).inter isClosed_closure.isOpen_compl.isLocallyClosed

theorem splitByClosure_refines {C U : Set X} (A : LCPartitionOn C)
    (hDclosed : IsClosed (C \ U)) {R : Set X}
    (hR : R ∈ (A.splitByClosure hDclosed).parts) :
    ∃ S ∈ A.parts, R ⊆ S := by
  rcases hR with ⟨p, rfl, hne⟩
  exact ⟨p.1.1, p.1.2, by intro x hx; exact hx.1.1⟩

theorem splitByClosure_subset_or_disjoint_closure {C U : Set X} (A : LCPartitionOn C)
    (hDclosed : IsClosed (C \ U)) {R : Set X}
    (hR : R ∈ (A.splitByClosure hDclosed).parts) :
    R ⊆ closure U ∨ Disjoint R (closure U) := by
  rcases hR with ⟨p, rfl, hne⟩
  by_cases hb : p.2
  · left
    intro x hx
    simpa [hb] using hx.2
  · right
    refine Set.disjoint_left.2 ?_
    intro x hxR hxcl
    have hxnot : x ∉ closure U := by simpa [hb] using hxR.2
    exact hxnot hxcl

end LCPartitionOn

/-- A good finite refinement of an ambient partition on `C`; the frontier condition is stated
using ambient closures. -/
structure GoodRefinementOn (C : Set X) (A : LCPartitionOn C) where
  toPartition : LCPartitionOn C
  refinement : ∀ ⦃S : Set X⦄, S ∈ toPartition.parts → ∃ T ∈ A.parts, S ⊆ T
  good : ∀ ⦃S : Set X⦄, S ∈ toPartition.parts → ∀ ⦃T : Set X⦄, T ∈ toPartition.parts →
    (S ∩ closure T).Nonempty → S ⊆ closure T

namespace GoodRefinementOn

noncomputable def empty {A : LCPartitionOn (∅ : Set X)} : GoodRefinementOn (∅ : Set X) A where
  toPartition := LCPartitionOn.empty
  refinement := by simp [LCPartitionOn.empty]
  good := by simp [LCPartitionOn.empty]

/-- Prepend the open stratum `U` to a good refinement of the closed complement. -/
noncomputable def prepend {C : Set X} (U T : Set X) {A : LCPartitionOn C}
    (hT : T ∈ A.parts) (hUne : U.Nonempty) (hUsubT : U ⊆ T) (hUsubC : U ⊆ C)
    (hUlc : IsLocallyClosed U) (hDclosed : IsClosed (C \ U))
    (G : GoodRefinementOn (C \ U) (A.splitByClosure hDclosed)) : GoodRefinementOn C A := by
  let U0 := U
  let T0 := T
  have hDclosed0 : IsClosed (C \ U0) := hDclosed
  refine { toPartition := ?_, refinement := ?_, good := ?_ }
  · refine
      { parts := insert U0 G.toPartition.parts
        finite := G.toPartition.finite.insert U0
        nonempty := ?_
        subset_closed := ?_
        cover := ?_
        pairwise := ?_
        locallyClosed := ?_ }
    · intro S hS
      rcases hS with rfl | hS
      · exact hUne
      · exact G.toPartition.nonempty hS
    · intro S hS
      rcases hS with rfl | hS
      · exact hUsubC
      · exact (G.toPartition.subset_closed hS).trans diff_subset
    · intro x hxC
      by_cases hxU : x ∈ U0
      · exact Set.mem_sUnion.2 ⟨U0, by simp, hxU⟩
      · have hxD : x ∈ C \ U0 := ⟨hxC, hxU⟩
        have hxOld : x ∈ ⋃₀ G.toPartition.parts := G.toPartition.cover hxD
        rcases Set.mem_sUnion.1 hxOld with ⟨S, hS, hxS⟩
        exact Set.mem_sUnion.2 ⟨S, by simp [hS], hxS⟩
    · intro S hS R hR hneq
      refine Set.disjoint_left.2 ?_
      intro x hxS hxR
      rcases hS with rfl | hS <;> rcases hR with rfl | hR
      · exact hneq rfl
      · exact (G.toPartition.subset_closed hR hxR).2 hxS
      · exact (G.toPartition.subset_closed hS hxS).2 hxR
      · exact Set.disjoint_left.1 (G.toPartition.pairwise hS hR hneq) hxS hxR
    · intro S hS
      rcases hS with rfl | hS
      · exact hUlc
      · exact G.toPartition.locallyClosed hS
  · intro S hS
    rcases hS with rfl | hS
    · exact ⟨T0, hT, hUsubT⟩
    · rcases G.refinement hS with ⟨R, hR, hSR⟩
      rcases LCPartitionOn.splitByClosure_refines A hDclosed0 hR with ⟨P, hP, hRP⟩
      exact ⟨P, hP, hSR.trans hRP⟩
  · intro S hS R hR hSRne
    rcases hS with rfl | hS <;> rcases hR with rfl | hR
    · exact subset_closure
    · exfalso
      rcases hSRne with ⟨x, hxU, hxclR⟩
      have hRsubD : R ⊆ C \ U0 := G.toPartition.subset_closed hR
      have hclosureRsubD : closure R ⊆ C \ U0 := closure_minimal hRsubD hDclosed0
      exact (hclosureRsubD hxclR).2 hxU
    · rcases G.refinement hS with ⟨Rsplit, hRsplit, hSsubRsplit⟩
      rcases LCPartitionOn.splitByClosure_subset_or_disjoint_closure A hDclosed0 hRsplit with hsub | hdisj
      · exact hSsubRsplit.trans hsub
      · exfalso
        rcases hSRne with ⟨x, hxS, hxclU⟩
        exact Set.disjoint_left.1 hdisj (hSsubRsplit hxS) hxclU
    · exact G.good hS hR hSRne

@[reducible]
noncomputable def toFiniteGoodRefinement (P : LocallyClosedPartition X) (hPfinite : P.toSet.Finite)
    (G : GoodRefinementOn (Set.univ : Set X) (LCPartitionOn.ofLocallyClosedPartition P hPfinite)) :
    (G.toPartition.toLocallyClosedPartition).IsFiniteGoodRefinement P where
  finite := by
    change G.toPartition.parts.Finite
    exact G.toPartition.finite
  refinement := by
    rw [LocallyClosedPartition.le_iff_forall_exists_mem_subset]
    intro S hS
    change S ∈ G.toPartition.parts at hS
    rcases G.refinement hS with ⟨T, hT, hST⟩
    exact ⟨T, hT, hST⟩
  good := by
    refine { frontier_condition := ?_ }
    intro S T hST
    rcases S with ⟨S, hS⟩
    rcases T with ⟨T, hT⟩
    change S ∈ G.toPartition.parts at hS
    change T ∈ G.toPartition.parts at hT
    exact G.good hS hT hST

end GoodRefinementOn

section NoetherianInduction

variable [NoetherianSpace X]

/-- Stacks 09Y5 open-stratum step: in a nonempty closed subset, choose an irreducible
component and a partition part whose closure contains it, then cut out a nonempty relatively
open subset contained in that part. -/
private theorem exists_rel_open_subset_part {C : Set X} (hCclosed : IsClosed C)
    (hCne : C.Nonempty) (A : LCPartitionOn C) :
    ∃ (U S : Set X), S ∈ A.parts ∧ U.Nonempty ∧ U ⊆ S ∧ U ⊆ C ∧
      IsLocallyClosed U ∧ IsClosed (C \ U) := by
  classical
  rcases hCne with ⟨x, hxC⟩
  let xC : C := ⟨x, hxC⟩
  let Z : Set C := irreducibleComponent xC
  have hZcomp : Z ∈ irreducibleComponents C := irreducibleComponent_mem_irreducibleComponents xC
  have hZirr : IsIrreducible Z := hZcomp.1
  let trace : Set X → Set C := fun S => (Subtype.val : C → X) ⁻¹' S
  let F : Set (Set C) := (fun S : Set X => closure (trace S)) '' A.parts
  have hFfinite : F.Finite := A.finite.image _
  have hFclosed : ∀ W ∈ F, IsClosed W := by
    rintro W ⟨S, hS, rfl⟩
    exact isClosed_closure
  have hZsub : Z ⊆ ⋃₀ F := by
    intro z hzZ
    have hzC : (z : X) ∈ C := z.2
    have hzcover : (z : X) ∈ ⋃₀ A.parts := A.cover hzC
    rcases Set.mem_sUnion.1 hzcover with ⟨S, hS, hzS⟩
    refine Set.mem_sUnion.2 ⟨closure (trace S), ⟨S, hS, rfl⟩, ?_⟩
    exact subset_closure hzS
  obtain ⟨W, hWF, hZW⟩ := (isIrreducible_iff_sUnion_isClosed.mp hZirr hFfinite.toFinset
    (by
      intro W hW
      exact hFclosed W (hFfinite.mem_toFinset.mp hW))
    (by
      simpa [hFfinite.coe_toFinset] using hZsub))
  have hWFset : W ∈ F := hFfinite.mem_toFinset.mp hWF
  rcases hWFset with ⟨S, hS, rfl⟩
  dsimp only [trace] at hZW
  rcases NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZcomp with
    ⟨Oc, hOcOpen, hOcNonempty, hOcZ⟩
  let T : Set C := (Subtype.val : C → X) ⁻¹' S
  have hclosure_inter : (closure T ∩ Oc).Nonempty := by
    rcases hOcNonempty with ⟨z, hzOc⟩
    exact ⟨z, hZW (hOcZ hzOc), hzOc⟩
  have htrace_inter : (T ∩ Oc).Nonempty := by
    exact (closure_inter_open_nonempty_iff hOcOpen).1 hclosure_inter
  rcases htrace_inter with ⟨z, hzTrace, hzOc⟩
  have hTraceLC : IsLocallyClosed T :=
    (A.locallyClosed hS).preimage continuous_subtype_val
  have Hloc : ∀ x ∈ T, ∃ U, x ∈ U ∧ IsOpen U ∧ U ∩ closure T ⊆ T :=
    ((isLocallyClosed_tfae T).out 0 3).mp hTraceLC
  rcases Hloc z hzTrace with ⟨Vc, hzVc, hVcOpen, hVcSub⟩
  let Uc : Set C := Oc ∩ Vc
  have hUcOpen : IsOpen Uc := hOcOpen.inter hVcOpen
  have hUcNonempty : Uc.Nonempty := ⟨z, hzOc, hzVc⟩
  have hUcSubsetTrace : Uc ⊆ T := by
    intro y hy
    have hyClosure : y ∈ closure T := hZW (hOcZ hy.1)
    exact hVcSub ⟨hy.2, hyClosure⟩
  rcases isOpen_induced_iff.mp hUcOpen with ⟨O, hOopen, hOpre⟩
  let U : Set X := C ∩ O
  refine ⟨U, S, hS, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hUcNonempty with ⟨y, hyUc⟩
    refine ⟨y, ?_⟩
    change (y : X) ∈ C ∩ O
    have hyPre : y ∈ (Subtype.val : C → X) ⁻¹' O := hOpre.symm ▸ hyUc
    exact ⟨y.2, hyPre⟩
  · intro y hy
    have hyC : y ∈ C := hy.1
    have hyPre : (⟨y, hyC⟩ : C) ∈ (Subtype.val : C → X) ⁻¹' O := hy.2
    have hyUc : (⟨y, hyC⟩ : C) ∈ Uc := hOpre ▸ hyPre
    exact hUcSubsetTrace hyUc
  · exact inter_subset_left
  · exact hCclosed.isLocallyClosed.inter hOopen.isLocallyClosed
  · have hdiff : C \ U = C ∩ Oᶜ := by
      ext y
      simp [U]
    rw [hdiff]
    exact hCclosed.inter hOopen.isClosed_compl

/-- Noetherian induction on closed subsets, following the proof of Stacks Lemma 09Y5. -/
theorem exists_good_refinement_on :
    ∀ Cc : Closeds X, (A : LCPartitionOn (Cc : Set X)) → Nonempty (GoodRefinementOn (Cc : Set X) A) := by
  intro Cc
  refine @WellFounded.induction (Closeds X) (· < ·) wellFounded_lt
    (fun Cc => ∀ A : LCPartitionOn (Cc : Set X), Nonempty (GoodRefinementOn (Cc : Set X) A))
    Cc ?_
  intro Cc ih A
  by_cases hCempty : (Cc : Set X) = ∅
  · let E : LCPartitionOn (Cc : Set X) :=
      { parts := ∅
        finite := Set.finite_empty
        nonempty := by simp
        subset_closed := by simp
        cover := by
          intro x hx
          have hxEmpty : x ∈ (∅ : Set X) := by
            rw [← hCempty]
            exact hx
          exact hxEmpty.elim
        pairwise := Set.pairwiseDisjoint_empty
        locallyClosed := by simp }
    exact ⟨{ toPartition := E, refinement := by simp [E], good := by simp [E] }⟩
  · have hCne : (Cc : Set X).Nonempty := Set.nonempty_iff_ne_empty.2 hCempty
    rcases exists_rel_open_subset_part Cc.2 hCne A with
      ⟨U, T, hT, hUne, hUsubT, hUsubC, hUlc, hDclosed⟩
    let D : Closeds X := ⟨(Cc : Set X) \ U, hDclosed⟩
    have hlt : D < Cc := by
      constructor
      · intro x hx
        exact hx.1
      · intro hle
        rcases hUne with ⟨x, hxU⟩
        have hxC : x ∈ (Cc : Set X) := hUsubC hxU
        have hxD : x ∈ ((Cc : Set X) \ U) := hle hxC
        exact hxD.2 hxU
    rcases ih D hlt (A.splitByClosure hDclosed) with ⟨G⟩
    exact ⟨GoodRefinementOn.prepend U T hT hUne hUsubT hUsubC hUlc hDclosed G⟩

end NoetherianInduction

/- Proof sketch: following Stacks, use Noetherian induction to split off a nonempty open subset of
an irreducible component lying in one member of the finite partition, refine the closed complement,
and prepend that open stratum. -/
/-- Lemma 5.28.8: every finite locally closed partition is refined by a finite good locally closed
partition in a Noetherian space. -/
theorem LocallyClosedPartition.exists_finite_good_refinement
    (hX : NoetherianSpace X)
    (P : LocallyClosedPartition X) (hPfinite : P.toSet.Finite) :
    ∃ Q : LocallyClosedPartition X, Q.IsFiniteGoodRefinement P := by
  letI : NoetherianSpace X := hX
  let A := LCPartitionOn.ofLocallyClosedPartition P hPfinite
  let Ctop : Closeds X := ⟨Set.univ, isClosed_univ⟩
  rcases exists_good_refinement_on Ctop A with ⟨G⟩
  exact ⟨G.toPartition.toLocallyClosedPartition, G.toFiniteGoodRefinement P hPfinite⟩

end
