module

public import stacks_project.Chap05.FiniteUnionOfLocallyClosed
public import Mathlib.Topology.JacobsonSpace
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation
open scoped TopologicalSpace

section

variable {X : Type u} [TopologicalSpace X]

local macro "X₀" : term => `(closedPoints X)

section

variable [JacobsonSpace X]

/-
Domain-style sampling for closed-point traces of finite unions of locally closed subsets:
- primary domain: Jacobson spaces, closed points, and locally closed subset traces along subtype
  inclusions
- inspected owner-level declarations:
  `closedPoints`,
  `JacobsonSpace`,
  `jacobsonSpace_iff_locallyClosed`,
  `IsLocallyClosed.preimage`
- best owner abstraction: the ambient owner `JacobsonSpace X` together with the canonical closed
  point set `X₀`; the actual trace operation is the derived bridge/view
  `X₀ ↓∩ E`

Layer triage:
- `source-facing`: the finite-union closed-point trace correspondence in Lemma 5.18.7
- `core/canonical`: `JacobsonSpace X` and `X₀`
- `bridge/view`: the canonical subtype trace `X₀ ↓∩ E`

Primitive data is the ambient Jacobson owner and the chapter bridge predicate
`IsFiniteUnionOfLocallyClosed`. The trace map itself is derived API and should therefore use the
canonical subtype-trace surface directly, rather than a second local wrapper definition.
-/

-- Proof sketch: traces to the closed-point subtype preserve locally closed
-- subsets and finite unions; surjectivity follows by lifting finite unions of locally closed
-- subsets of `X₀` piecewise from open and closed subsets of `X₀`, while injectivity is the Stacks
-- argument using that every nonempty finite union of locally closed subsets of a Jacobson space
-- meets `X₀`.
/-- Helper for Lemma 5.18.7: the empty set is a finite union of locally closed subsets. -/
private lemma isFiniteUnionOfLocallyClosed_empty {Y : Type*} [TopologicalSpace Y] :
    IsFiniteUnionOfLocallyClosed (∅ : Set Y) := by
  -- Use the empty family of locally closed pieces.
  refine ⟨∅, Set.finite_empty, ?_, ?_⟩
  · intro Z hZ
    exact False.elim (Set.notMem_empty Z hZ)
  · simp

/-- Helper for Lemma 5.18.7: finite unions of locally closed subsets are stable under binary
union. -/
private lemma isFiniteUnionOfLocallyClosed_union {Y : Type*} [TopologicalSpace Y] {E F : Set Y}
    (hE : IsFiniteUnionOfLocallyClosed E) (hF : IsFiniteUnionOfLocallyClosed F) :
    IsFiniteUnionOfLocallyClosed (E ∪ F) := by
  rcases hE with ⟨S, hSfin, hSlc, hEeq⟩
  rcases hF with ⟨T, hTfin, hTlc, hFeq⟩
  -- Combine the two finite decompositions into a single finite family.
  refine ⟨S ∪ T, hSfin.union hTfin, ?_, ?_⟩
  · intro Z hZ
    rcases hZ with hZ | hZ
    · exact hSlc Z hZ
    · exact hTlc Z hZ
  · rw [hEeq, hFeq]
    ext x
    constructor
    · rintro (hx | hx)
      · rcases hx with ⟨t, ht, hx⟩
        exact ⟨t, Or.inl ht, hx⟩
      · rcases hx with ⟨t, ht, hx⟩
        exact ⟨t, Or.inr ht, hx⟩
    · rintro ⟨t, ht, hx⟩
      rcases ht with ht | ht
      · exact Or.inl ⟨t, ht, hx⟩
      · exact Or.inr ⟨t, ht, hx⟩

/-- Helper for Lemma 5.18.7: a finite indexed union of finite unions of locally closed subsets is
again a finite union of locally closed subsets. -/
private lemma isFiniteUnionOfLocallyClosed_iUnion {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    {S : Fin n → Set Y}
    (hS : ∀ i, IsFiniteUnionOfLocallyClosed (S i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i, S i) := by
  induction n with
  | zero =>
      -- The empty indexed union is empty.
      simpa using isFiniteUnionOfLocallyClosed_empty (Y := Y)
  | succ n ih =>
      -- Split off the first piece and apply binary union stability.
      have hEq : (⋃ i : Fin (n + 1), S i) = S 0 ∪ ⋃ i : Fin n, S i.succ := by
        ext x
        simp [Fin.exists_fin_succ]
      rw [hEq]
      exact isFiniteUnionOfLocallyClosed_union (hS 0) (ih fun i ↦ hS i.succ)

/-- Helper for Lemma 5.18.7: tracing a finite union of locally closed subsets to a subspace again
produces a finite union of locally closed subsets. -/
private lemma isFiniteUnionOfLocallyClosed_preimage_val {A E : Set X}
    (hE : IsFiniteUnionOfLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed (A ↓∩ E) := by
  obtain ⟨n, S, hS, hEq⟩ := IsFiniteUnionOfLocallyClosed.exists_eq_iUnion hE
  -- Pull each locally closed piece back along the subtype map.
  rw [hEq]
  have hEq' : A ↓∩ (⋃ i, S i) = ⋃ i, A ↓∩ S i := by
    ext x
    simp
  rw [hEq']
  refine isFiniteUnionOfLocallyClosed_iUnion (Y := A) ?_
  intro i
  exact (hS i).preimage continuous_subtype_val |>.isFiniteUnionOfLocallyClosed

/-- Helper for Lemma 5.18.7: the difference of two locally closed subsets is a finite union of
locally closed subsets. -/
private lemma isFiniteUnionOfLocallyClosed_sdiff_isLocallyClosed {E E' : Set X}
    (hE : IsLocallyClosed E) (hE' : IsLocallyClosed E') :
    IsFiniteUnionOfLocallyClosed (E \ E') := by
  rcases hE with ⟨U, Z, hU, hZ, hEeq⟩
  rcases hE' with ⟨V, C, hV, hC, hE'eq⟩
  -- Split the difference according to whether a point misses the open part or the closed part of
  -- the second locally closed subset.
  have hEq : E \ E' = (U ∩ Z ∩ Vᶜ) ∪ (U ∩ V ∩ Z ∩ Cᶜ) := by
    ext x
    by_cases hxV : x ∈ V <;> by_cases hxC : x ∈ C <;>
      simp [hEeq, hE'eq, hxV, hxC, and_comm]
  rw [hEq]
  refine isFiniteUnionOfLocallyClosed_union
    (((hU.isLocallyClosed.inter hZ.isLocallyClosed).inter
      hV.isClosed_compl.isLocallyClosed).isFiniteUnionOfLocallyClosed)
    ?_
  -- The second branch is again locally closed after reordering the intersections.
  simpa [inter_assoc, inter_left_comm, inter_comm] using
    (((((hU.inter hV).inter hC.isOpen_compl).isLocallyClosed).inter
      hZ.isLocallyClosed).isFiniteUnionOfLocallyClosed)

/-- Helper for Lemma 5.18.7: subtracting a locally closed subset from a finite union of locally
closed subsets preserves the finite-union property. -/
private lemma isFiniteUnionOfLocallyClosed_sdiff_isLocallyClosed_right {E T : Set X}
    (hE : IsFiniteUnionOfLocallyClosed E) (hT : IsLocallyClosed T) :
    IsFiniteUnionOfLocallyClosed (E \ T) := by
  obtain ⟨n, S, hS, hEq⟩ := IsFiniteUnionOfLocallyClosed.exists_eq_iUnion hE
  -- Subtract `T` piecewise from the locally closed decomposition of `E`.
  rw [hEq]
  have hEq' : (⋃ i, S i) \ T = ⋃ i, S i \ T := by
    ext x
    simp
  rw [hEq']
  refine isFiniteUnionOfLocallyClosed_iUnion ?_
  intro i
  exact isFiniteUnionOfLocallyClosed_sdiff_isLocallyClosed (hS i) hT

/-- Helper for Lemma 5.18.7: subtracting a finite indexed union of locally closed subsets from a
finite union of locally closed subsets preserves the finite-union property. -/
private lemma isFiniteUnionOfLocallyClosed_sdiff_iUnion {n : ℕ} {E : Set X}
    {T : Fin n → Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hT : ∀ i, IsLocallyClosed (T i)) :
    IsFiniteUnionOfLocallyClosed (E \ ⋃ i, T i) := by
  let P : ∀ n : ℕ, Prop := fun n ↦
    ∀ {E : Set X} {T : Fin n → Set X}, IsFiniteUnionOfLocallyClosed E →
      (∀ i, IsLocallyClosed (T i)) → IsFiniteUnionOfLocallyClosed (E \ ⋃ i, T i)
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro E T hE hT
        -- The empty indexed union contributes nothing.
        simpa using hE
    | succ n ih =>
        intro E T hE hT
        -- Remove the first locally closed piece, then recurse on the tail.
        have hEq : E \ (⋃ i : Fin (n + 1), T i) = (E \ T 0) \ ⋃ i : Fin n, T i.succ := by
          ext x
          simp [Fin.exists_fin_succ, and_assoc]
        rw [hEq]
        exact ih (isFiniteUnionOfLocallyClosed_sdiff_isLocallyClosed_right hE (hT 0))
          (fun i ↦ hT i.succ)
  exact hP n hE hT

/-- Helper for Lemma 5.18.7: finite unions of locally closed subsets are stable under set
difference. -/
private lemma isFiniteUnionOfLocallyClosed_sdiff {E E' : Set X}
    (hE : IsFiniteUnionOfLocallyClosed E) (hE' : IsFiniteUnionOfLocallyClosed E') :
    IsFiniteUnionOfLocallyClosed (E \ E') := by
  obtain ⟨n, T, hT, hEq⟩ := IsFiniteUnionOfLocallyClosed.exists_eq_iUnion hE'
  -- Expand the right-hand side into finitely many locally closed pieces and subtract them one by
  -- one.
  rw [hEq]
  exact isFiniteUnionOfLocallyClosed_sdiff_iUnion hE hT

/-- Helper for Lemma 5.18.7: a nonempty finite union of locally closed subsets in a Jacobson
space contains a point closed in the ambient space. -/
private lemma nonempty_inter_closedPoints_of_isFiniteUnionOfLocallyClosed {E : Set X}
    (hEne : E.Nonempty) (hE : IsFiniteUnionOfLocallyClosed E) : (E ∩ X₀).Nonempty := by
  obtain ⟨n, S, hS, hEq⟩ := IsFiniteUnionOfLocallyClosed.exists_eq_iUnion hE
  -- Pick a nonempty locally closed piece and then use the Jacobson criterion there.
  rw [hEq, Set.nonempty_iUnion] at hEne
  obtain ⟨i, hi⟩ := hEne
  obtain ⟨x, hx, hxclosed⟩ := nonempty_inter_closedPoints hi (hS i)
  refine ⟨x, ?_, hxclosed⟩
  simpa [hEq] using Set.mem_iUnion.2 ⟨i, hx⟩

/-- Helper for Lemma 5.18.7: inclusion of finite unions of locally closed subsets is reflected by
their traces on the closed-point subspace. -/
private lemma subset_of_preimage_closedPoints_subset_of_isFiniteUnionOfLocallyClosed
    {E E' : Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hE' : IsFiniteUnionOfLocallyClosed E')
    (htrace : X₀ ↓∩ E ⊆ X₀ ↓∩ E') : E ⊆ E' := by
  intro x hxE
  by_contra hxE'
  -- A point in the difference forces a closed point in the difference, contradicting the trace
  -- inclusion.
  have hdiff_ne : (E \ E').Nonempty := ⟨x, hxE, hxE'⟩
  have hdiff : IsFiniteUnionOfLocallyClosed (E \ E') := isFiniteUnionOfLocallyClosed_sdiff hE hE'
  obtain ⟨y, hyE, hyclosed⟩ :=
    nonempty_inter_closedPoints_of_isFiniteUnionOfLocallyClosed hdiff_ne hdiff
  have hytrace : (⟨y, hyclosed⟩ : X₀) ∈ X₀ ↓∩ E := by
    simpa using hyE.1
  have hytrace' := htrace hytrace
  exact hyE.2 hytrace'

/-- Helper for Lemma 5.18.7: equality of traces on the closed-point subspace determines a finite
union of locally closed subsets uniquely. -/
private lemma eq_of_preimage_closedPoints_eq_of_isFiniteUnionOfLocallyClosed
    {E E' : Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hE' : IsFiniteUnionOfLocallyClosed E')
    (htrace : X₀ ↓∩ E = X₀ ↓∩ E') : E = E' := by
  -- Recover equality by reflecting inclusion in both directions.
  refine Set.Subset.antisymm
    (subset_of_preimage_closedPoints_subset_of_isFiniteUnionOfLocallyClosed hE hE' ?_)
    (subset_of_preimage_closedPoints_subset_of_isFiniteUnionOfLocallyClosed hE' hE ?_)
  · simp [htrace]
  · simp [htrace]

/-- Lemma 5.18.7: for a Jacobson space `X`, tracing a subset to the closed-point subspace `X₀`
induces a bijection between finite unions of locally closed subsets of `X` and of `X₀`. -/
theorem finiteUnionOfLocallyClosed_preimage_closedPoints_bijOn :
    Set.BijOn (fun E : Set X ↦ X₀ ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set X₀ | IsFiniteUnionOfLocallyClosed F} := by
  refine ⟨?_, ?_, ?_⟩
  · intro E hE
    -- Trace preservation is just pullback along the subtype map.
    exact isFiniteUnionOfLocallyClosed_preimage_val hE
  · intro E hE E' hE' htrace
    -- Injectivity is the Stacks argument via a nonempty difference meeting the closed points.
    exact eq_of_preimage_closedPoints_eq_of_isFiniteUnionOfLocallyClosed hE hE' htrace
  · intro F hF
    obtain ⟨n, S, hS, hEq⟩ := IsFiniteUnionOfLocallyClosed.exists_eq_iUnion hF
    choose T hTlc hTrace using fun i ↦
      IsInducing.subtypeVal.isLocallyClosed_iff.mp (hS i)
    refine ⟨⋃ i, T i, ?_, ?_⟩
    · -- Lift the finite locally closed decomposition of `F` piecewise to `X`.
      exact isFiniteUnionOfLocallyClosed_iUnion
        (fun i ↦ (hTlc i).isFiniteUnionOfLocallyClosed)
    · -- The trace of the lifted ambient union recovers `F`.
      rw [hEq]
      ext x
      simp [hTrace]

-- Proof sketch: monotonicity of subtype trace gives the forward implication. For the converse, apply
-- injectivity from the bijection theorem to the finite unions of locally closed subsets `E \ E'`
-- and `∅`; if the traces satisfy inclusion, Jacobsonness forces `E \ E' = ∅`.
/-- The closed-point trace correspondence reflects and preserves inclusion on finite unions of
locally closed subsets. -/
theorem finiteUnionOfLocallyClosed_preimage_closedPoints_subset_iff
    {E E' : Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hE' : IsFiniteUnionOfLocallyClosed E') :
    X₀ ↓∩ E ⊆ X₀ ↓∩ E' ↔ E ⊆ E' := by
  constructor
  · intro htrace
    -- This is the reflected-inclusion half of the correspondence.
    exact subset_of_preimage_closedPoints_subset_of_isFiniteUnionOfLocallyClosed hE hE' htrace
  · intro hsubset x hx
    -- Ordinary preimage monotonicity gives the forward implication.
    exact hsubset hx

-- Proof sketch: locally closed subsets are finite unions of locally closed subsets with one piece,
-- so the forward implication is by trace preservation. For the converse, use surjectivity of
-- the bijection to lift the locally closed trace to a locally closed subset of `X`, then apply the
-- inclusion-reflecting companion theorem in both directions to identify it with `E`.
/-- Within the closed-point trace correspondence of Lemma 5.18.7, finite unions of locally closed
subsets are locally closed exactly when their traces on `X₀` are locally closed. -/
theorem isLocallyClosed_iff_preimage_closedPoints_subtypeVal_of_isFiniteUnionOfLocallyClosed
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsLocallyClosed E ↔ IsLocallyClosed (X₀ ↓∩ E) := by
  constructor
  · intro hElc
    -- Locally closed subsets stay locally closed after pullback to the subtype.
    simpa using hElc.preimage continuous_subtype_val
  · intro htrace
    obtain ⟨T, hTlc, hTtrace⟩ := IsInducing.subtypeVal.isLocallyClosed_iff.mp htrace
    have hT : IsFiniteUnionOfLocallyClosed T := hTlc.isFiniteUnionOfLocallyClosed
    -- Lift the locally closed trace and identify the lift with `E` by trace injectivity.
    have hEq : E = T :=
      eq_of_preimage_closedPoints_eq_of_isFiniteUnionOfLocallyClosed hE hT hTtrace.symm
    simpa [hEq] using hTlc

-- Proof sketch: open subsets are locally closed, so the forward implication is by trace of an
-- open set. For the converse, lift the open trace to an open subset of `X` via the bijection and
-- use the inclusion-preserving correspondence to show that this lift equals `E`.
/-- Within the closed-point trace correspondence of Lemma 5.18.7, finite unions of locally closed
subsets are open exactly when their traces on `X₀` are open. -/
theorem isOpen_iff_preimage_closedPoints_subtypeVal_of_isFiniteUnionOfLocallyClosed
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsOpen E ↔ IsOpen (X₀ ↓∩ E) := by
  constructor
  · intro hEopen
    -- Open subsets pull back to open subsets of the subtype.
    exact hEopen.preimage continuous_subtype_val
  · intro htrace
    rcases isOpen_induced_iff.mp htrace with ⟨U, hUopen, hUtrace⟩
    have hU : IsFiniteUnionOfLocallyClosed U := hUopen.isLocallyClosed.isFiniteUnionOfLocallyClosed
    -- Lift the open trace to an ambient open subset and identify it with `E`.
    have hEq : E = U :=
      eq_of_preimage_closedPoints_eq_of_isFiniteUnionOfLocallyClosed hE hU hUtrace.symm
    simpa [hEq] using hUopen

-- Proof sketch: closed subsets are locally closed, so the forward implication is by trace of a
-- closed set. For the converse, lift the closed trace to a closed subset of `X` via the bijection
-- and again identify that lift with `E` using inclusion reflection.
/-- Within the closed-point trace correspondence of Lemma 5.18.7, finite unions of locally closed
subsets are closed exactly when their traces on `X₀` are closed. -/
theorem isClosed_iff_preimage_closedPoints_subtypeVal_of_isFiniteUnionOfLocallyClosed
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsClosed E ↔ IsClosed (X₀ ↓∩ E) := by
  constructor
  · intro hEclosed
    -- Closed subsets pull back to closed subsets of the subtype.
    exact hEclosed.preimage continuous_subtype_val
  · intro htrace
    rcases isClosed_induced_iff.mp htrace with ⟨Z, hZclosed, hZtrace⟩
    have hZ : IsFiniteUnionOfLocallyClosed Z :=
      hZclosed.isLocallyClosed.isFiniteUnionOfLocallyClosed
    -- Lift the closed trace to an ambient closed subset and identify it with `E`.
    have hEq : E = Z :=
      eq_of_preimage_closedPoints_eq_of_isFiniteUnionOfLocallyClosed hE hZ hZtrace.symm
    simpa [hEq] using hZclosed

end

end
