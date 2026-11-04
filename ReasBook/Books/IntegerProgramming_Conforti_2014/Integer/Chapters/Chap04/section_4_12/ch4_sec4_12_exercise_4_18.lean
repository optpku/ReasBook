/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.LinearAlgebra.Pi
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.RingTheory.Localization.Rat
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_34
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_theorem_4_18
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_18_support

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Semantic search note: `lean_leansearch` confirmed that mathlib's canonical owner here is
-- `SimpleGraph.incMatrix`, so the source-facing polyhedron keeps graph edge coordinates and
-- restricts the incidence matrix to `G.edgeSet`.

universe u

noncomputable section Exercise418

section Exercise418

variable {V : Type u} [Finite V]
variable (G : SimpleGraph V)

/-- The edge-indexed incidence matrix of `G`, obtained by restricting `SimpleGraph.incMatrix` to
the actual edges of `G`. -/
private abbrev graphEdgeIncMatrix
    [DecidableEq V] [DecidableRel G.Adj]
    (R : Type*) [Zero R] [One R] :
    Matrix V G.edgeSet R :=
  (G.incMatrix R).submatrix id Subtype.val

/-- The graph-indexed polyhedron `{x : A_G x ≤ b}` in the edge coordinates of `G`. -/
def graph_edge_incidence_polyhedron
    (b : V → ℚ) : Set (G.edgeSet → ℝ) :=
  let _ := Classical.decEq V
  let _ := Classical.decRel G.Adj
  {x | graphEdgeIncMatrix G ℝ *ᵥ x ≤ fun v ↦ (b v : ℝ)}

/-- Helper for Exercise 4.18: every coordinate of `b` is an even integer. -/
private lemma exists_even_integer_rhs
    (b : V → ℚ)
    (hb : ∀ v, IsLocalization.IsInteger ℤ (b v / 2)) :
    ∃ bHalf : V → ℤ, ∀ v, b v = (2 * bHalf v : ℚ) := by
  choose bHalf hbHalf using hb
  refine ⟨bHalf, ?_⟩
  intro v
  have hEq : (bHalf v : ℚ) = b v / 2 := hbHalf v
  calc
    b v = 2 * (b v / 2) := by ring
    _ = (2 * bHalf v : ℚ) := by rw [← hEq]

/-- Helper for Exercise 4.18: native membership in the graph-incidence polyhedron is exactly the
fixed rowwise incidence inequality. -/
private theorem graphEdgeIncidencePolyhedron_mem_iff_rowwise
    (b : V → ℚ) {x : G.edgeSet → ℝ} :
    x ∈ graph_edge_incidence_polyhedron G b ↔
      let _ := Classical.decEq V
      let _ := Classical.decRel G.Adj
      (graphEdgeIncMatrix G ℝ).mulVec x ≤ fun v ↦ (b v : ℝ) := by
  -- Freeze the native owner spelling once so later transport never unfolds this definition again.
  rfl

section FinitePresentation

variable [Fintype V]

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel G.Adj
local instance : Fintype (Sym2 V) := CategoryTheory.FinCategory.fintypeObj
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet (G := G)

/-- Helper for Exercise 4.18: the native split owner uses one nonnegative coordinate for the
positive part and one for the negative part of each edge variable. -/
private abbrev SplitEdge :=
  Sum G.edgeSet G.edgeSet

/-- Helper for Exercise 4.18: the split matrix records `+A_G` on the first copy of each edge and
`-A_G` on the second copy. -/
private abbrev splitGraphEdgeIncMatrix
    (R : Type*) [Ring R] :
    Matrix V (SplitEdge G) R :=
  fun v s ↦
    match s with
    | Sum.inl e => graphEdgeIncMatrix G R v e
    | Sum.inr e => -graphEdgeIncMatrix G R v e

/-- Helper for Exercise 4.18: projecting split coordinates back to native edge coordinates takes
the positive copy minus the negative copy. -/
private abbrev splitProjection
    (y : SplitEdge G → ℝ) : G.edgeSet → ℝ :=
  fun e ↦ y (Sum.inl e) - y (Sum.inr e)

/-- Helper for Exercise 4.18: the split objective gives each negative copy the opposite weight so
that it agrees with the native objective after projection. -/
private abbrev splitObjective
    (cNative : G.edgeSet → ℝ) : SplitEdge G → ℝ
  | Sum.inl e => cNative e
  | Sum.inr e => -cNative e

/-- Helper for Exercise 4.18: lifting a native vector to split coordinates records its positive
and negative parts separately. -/
private abbrev splitLift
    (x : G.edgeSet → ℝ) : SplitEdge G → ℝ
  | Sum.inl e => max (x e) 0
  | Sum.inr e => max (-x e) 0

/-- Helper for Exercise 4.18: casting the integral split matrix to `ℝ` recovers the real split
matrix entrywise. -/
private theorem splitGraphEdgeIncMatrix_intCast :
    (splitGraphEdgeIncMatrix G ℤ).map (Int.castRingHom ℝ) =
      splitGraphEdgeIncMatrix G ℝ := by
  -- Each split entry is either an incidence entry or its negation, so the cast is checked
  -- entrywise from the `0/1` incidence formulas.
  ext v s
  cases s with
  | inl e =>
      by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
      · simp [splitGraphEdgeIncMatrix, graphEdgeIncMatrix, Matrix.submatrix_apply,
          G.incMatrix_of_mem_incidenceSet (R := ℤ) h,
          G.incMatrix_of_mem_incidenceSet (R := ℝ) h]
      · simp [splitGraphEdgeIncMatrix, graphEdgeIncMatrix, Matrix.submatrix_apply,
          G.incMatrix_of_notMem_incidenceSet (R := ℤ) h,
          G.incMatrix_of_notMem_incidenceSet (R := ℝ) h]
  | inr e =>
      by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
      · simp [splitGraphEdgeIncMatrix, graphEdgeIncMatrix, Matrix.submatrix_apply,
          G.incMatrix_of_mem_incidenceSet (R := ℤ) h,
          G.incMatrix_of_mem_incidenceSet (R := ℝ) h]
      · simp [splitGraphEdgeIncMatrix, graphEdgeIncMatrix, Matrix.submatrix_apply,
          G.incMatrix_of_notMem_incidenceSet (R := ℤ) h,
          G.incMatrix_of_notMem_incidenceSet (R := ℝ) h]

/-- Helper for Exercise 4.18: multiplying the real split matrix by a split vector is exactly the
native incidence product of its projected edge vector. -/
private theorem splitGraphEdgeIncMatrix_mulVec
    (y : SplitEdge G → ℝ) :
    (splitGraphEdgeIncMatrix G ℝ).mulVec y =
      (graphEdgeIncMatrix G ℝ).mulVec (splitProjection (G := G) y) := by
  ext v
  -- Expand the split row sum into the two edge copies and then recombine them as a projection.
  calc
    ((splitGraphEdgeIncMatrix G ℝ).mulVec y) v =
        ∑ s : SplitEdge G, splitGraphEdgeIncMatrix G ℝ v s * y s := by
          simp [Matrix.mulVec, dotProduct]
    _ =
        ∑ e : G.edgeSet, graphEdgeIncMatrix G ℝ v e * y (Sum.inl e) +
          ∑ e : G.edgeSet, (-graphEdgeIncMatrix G ℝ v e) * y (Sum.inr e) := by
            simp [splitGraphEdgeIncMatrix, Fintype.sum_sum_type]
    _ = ∑ e : G.edgeSet,
          graphEdgeIncMatrix G ℝ v e * (y (Sum.inl e) - y (Sum.inr e)) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro e he
            ring
    _ = ((graphEdgeIncMatrix G ℝ).mulVec (splitProjection (G := G) y)) v := by
          simp [Matrix.mulVec, dotProduct, splitProjection]

/-- Helper for Exercise 4.18: the split objective evaluates exactly to the native objective on the
projected edge vector. -/
private theorem splitObjective_dot_eq_nativeObjective
    (cNative : G.edgeSet → ℝ)
    (y : SplitEdge G → ℝ) :
    ∑ s : SplitEdge G, splitObjective (G := G) cNative s * y s =
      ∑ e : G.edgeSet, cNative e * splitProjection (G := G) y e := by
  -- Separate the split sum by copy and recombine the two terms edgewise.
  calc
    ∑ s : SplitEdge G, splitObjective (G := G) cNative s * y s =
        ∑ e : G.edgeSet, cNative e * y (Sum.inl e) +
          ∑ e : G.edgeSet, (-cNative e) * y (Sum.inr e) := by
            simp [splitObjective, Fintype.sum_sum_type]
    _ = ∑ e : G.edgeSet, cNative e * (y (Sum.inl e) - y (Sum.inr e)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro e he
          ring
    _ = ∑ e : G.edgeSet, cNative e * splitProjection (G := G) y e := by
          simp [splitProjection]

/-- Helper for Exercise 4.18: projecting the positive/negative split lift recovers the original
native edge vector. -/
private theorem splitProjection_splitLift
    (x : G.edgeSet → ℝ) :
    splitProjection (G := G) (splitLift (G := G) x) = x := by
  -- The positive-part minus negative-part identity holds coordinatewise.
  funext e
  simpa [splitProjection, splitLift] using max_zero_sub_max_neg_zero_eq_self (x e)

/-- Helper for Exercise 4.18: lifting a native point to split coordinates preserves the objective
value. -/
private theorem splitObjective_dot_splitLift
    (cNative : G.edgeSet → ℝ)
    (x : G.edgeSet → ℝ) :
    ∑ s : SplitEdge G, splitObjective (G := G) cNative s * splitLift (G := G) x s =
      ∑ e : G.edgeSet, cNative e * x e := by
  -- First rewrite through the projection formula, then collapse the split lift back to `x`.
  calc
    ∑ s : SplitEdge G, splitObjective (G := G) cNative s * splitLift (G := G) x s =
        ∑ e : G.edgeSet, cNative e * splitProjection (G := G) (splitLift (G := G) x) e := by
          exact splitObjective_dot_eq_nativeObjective (G := G) cNative (splitLift (G := G) x)
    _ = ∑ e : G.edgeSet, cNative e * x e := by
          simp

/-- Helper for Exercise 4.18: reindex native edge-coordinate vectors by the canonical finite
enumeration of `G.edgeSet`. -/
private noncomputable def graphEdgeCoordinates
    (x : G.edgeSet → ℝ) : Fin (Nat.card G.edgeSet) → ℝ :=
  fun j ↦ x ((Finite.equivFin G.edgeSet).symm j)

/-- Helper for Exercise 4.18: the inverse coordinate reindexing sends `Fin`-indexed vectors back
to the native `G.edgeSet` coordinates. -/
private noncomputable abbrev graphEdgeCoordinateReindex :
    (Fin (Nat.card G.edgeSet) → ℝ) ≃ₗ[ℝ] (G.edgeSet → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (Finite.equivFin G.edgeSet)

/-- Helper for Exercise 4.18: evaluating the reindexed coordinate vector at an edge recovers the
corresponding finite coordinate. -/
@[simp] private theorem graphEdgeCoordinateReindex_apply
    (y : Fin (Nat.card G.edgeSet) → ℝ) (e : G.edgeSet) :
    graphEdgeCoordinateReindex (G := G) y e = y ((Finite.equivFin G.edgeSet) e) := by
  -- This is the defining formula of `LinearEquiv.funCongrLeft`.
  rw [graphEdgeCoordinateReindex, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

/-- Helper for Exercise 4.18: reindexing native edge coordinates to `Fin` and back is the
identity. -/
@[simp] private theorem graphEdgeCoordinateReindex_graphEdgeCoordinates
    (x : G.edgeSet → ℝ) :
    graphEdgeCoordinateReindex (G := G) (graphEdgeCoordinates (G := G) x) = x := by
  -- The native coordinate map is the inverse of the chosen `funCongrLeft` equivalence.
  change graphEdgeCoordinateReindex (G := G) ((graphEdgeCoordinateReindex (G := G)).symm x) = x
  exact LinearEquiv.apply_symm_apply (graphEdgeCoordinateReindex (G := G)) x

/-- Helper for Exercise 4.18: reindexing a `Fin`-indexed edge vector to native coordinates and
back is also the identity. -/
@[simp] private theorem graphEdgeCoordinates_graphEdgeCoordinateReindex
    (y : Fin (Nat.card G.edgeSet) → ℝ) :
    graphEdgeCoordinates (G := G) (graphEdgeCoordinateReindex (G := G) y) = y := by
  -- This is the inverse identity for the same coordinate equivalence.
  change (graphEdgeCoordinateReindex (G := G)).symm
      (graphEdgeCoordinateReindex (G := G) y) = y
  exact LinearEquiv.symm_apply_apply (graphEdgeCoordinateReindex (G := G)) y

/-- Helper for Exercise 4.18: casting the rational incidence matrix to `ℝ` recovers the real
incidence matrix. -/
private lemma graphEdgeIncMatrix_ratCast :
    (graphEdgeIncMatrix G ℚ).map (Rat.castHom ℝ) = graphEdgeIncMatrix G ℝ := by
  -- Both matrices encode the same `0,1` incidence pattern after coercion to `ℝ`.
  ext v e
  by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
  · simp [graphEdgeIncMatrix, Matrix.submatrix_apply,
      G.incMatrix_of_mem_incidenceSet (R := ℚ) h,
      G.incMatrix_of_mem_incidenceSet (R := ℝ) h]
  · simp [graphEdgeIncMatrix, Matrix.submatrix_apply,
      G.incMatrix_of_notMem_incidenceSet (R := ℚ) h,
      G.incMatrix_of_notMem_incidenceSet (R := ℝ) h]

/-- Helper for Exercise 4.18: the `Fin`-reindexed incidence matrix computes the same row sums as
the native `G.edgeSet`-indexed incidence matrix after coordinate transport. -/
private lemma reindexedGraphEdgeIncMatrix_mulVec_apply
    (y : Fin (Nat.card G.edgeSet) → ℝ) (v : V) :
    ((((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
        (graphEdgeIncMatrix G ℚ)).map (Rat.castHom ℝ)) *ᵥ y) ((Finite.equivFin V) v)) =
      ((graphEdgeIncMatrix G ℝ).mulVec (graphEdgeCoordinateReindex (G := G) y)) v := by
  -- Expand the reindexed matrix-vector product and reindex the finite column sum back to
  -- `G.edgeSet`.
  calc
    ((((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
        (graphEdgeIncMatrix G ℚ)).map (Rat.castHom ℝ)) *ᵥ y) ((Finite.equivFin V) v)) =
        ∑ j : Fin (Nat.card G.edgeSet),
          ((((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
              (graphEdgeIncMatrix G ℚ)).map (Rat.castHom ℝ)) ((Finite.equivFin V) v) j) * y j) := by
          simp [Matrix.mulVec, dotProduct]
    _ = ∑ e : G.edgeSet, (((graphEdgeIncMatrix G ℚ) v e : ℝ) * y ((Finite.equivFin G.edgeSet) e)) := by
          refine Fintype.sum_equiv (Finite.equivFin G.edgeSet).symm _ _ ?_
          intro e
          rw [Equiv.apply_symm_apply]
          rw [Matrix.reindex_apply]
          simp [graphEdgeIncMatrix]
    _ = ∑ e : G.edgeSet, (graphEdgeIncMatrix G ℝ) v e * graphEdgeCoordinateReindex (G := G) y e := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
          · rw [graphEdgeCoordinateReindex_apply]
            simp [graphEdgeIncMatrix, G.incMatrix_of_mem_incidenceSet (R := ℚ) h,
              G.incMatrix_of_mem_incidenceSet (R := ℝ) h]
          · rw [graphEdgeCoordinateReindex_apply]
            simp [graphEdgeIncMatrix, G.incMatrix_of_notMem_incidenceSet (R := ℚ) h,
              G.incMatrix_of_notMem_incidenceSet (R := ℝ) h]
    _ = ((graphEdgeIncMatrix G ℝ).mulVec (graphEdgeCoordinateReindex (G := G) y)) v := by
          simp [Matrix.mulVec, dotProduct]

/-- Helper for Exercise 4.18: a single native row inequality is equivalent to the corresponding
row inequality in the `Fin`-indexed presentation. -/
private lemma graphEdgeCoordinateReindex_rowBound_iff
    (b : V → ℚ) (y : Fin (Nat.card G.edgeSet) → ℝ) (v : V) :
    ((graphEdgeIncMatrix G ℝ).mulVec (graphEdgeCoordinateReindex (G := G) y)) v ≤ (b v : ℝ) ↔
      ((((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
          (graphEdgeIncMatrix G ℚ)).map (Rat.castHom ℝ)) *ᵥ y) ((Finite.equivFin V) v)) ≤
        (b v : ℝ) := by
  -- The rowwise transport is exactly the previously proved `mulVec` reindexing identity.
  rw [reindexedGraphEdgeIncMatrix_mulVec_apply (G := G) y v]

/-- Helper for Exercise 4.18: the canonical edge-coordinate reindexing identifies the native
graph-incidence polyhedron with its `Fin`-indexed rational presentation. -/
private theorem graphEdgeCoordinateReindex_mem_incidencePresentation_iff
    (b : V → ℚ) {y : Fin (Nat.card G.edgeSet) → ℝ} :
    graphEdgeCoordinateReindex (G := G) y ∈ graph_edge_incidence_polyhedron G b ↔
      y ∈
        rational_matrix_polyhedron
          (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
            (graphEdgeIncMatrix G ℚ))
          (fun i ↦ b ((Finite.equivFin V).symm i)) := by
  -- Route correction: translate membership on each row separately instead of chasing a global
  -- owner-invariance theorem for the native `mulVec`.
  simp [graph_edge_incidence_polyhedron, rational_matrix_polyhedron]
  constructor
  · intro hx i
    let v : V := (Finite.equivFin V).symm i
    -- Read the native inequality at the vertex represented by `i`, then transport that row.
    have hv : ((graphEdgeIncMatrix G ℝ).mulVec (graphEdgeCoordinateReindex (G := G) y)) v ≤
        (b v : ℝ) := by
      simpa using hx v
    have hv' :
        ((((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
            (graphEdgeIncMatrix G ℚ)).map (Rat.castHom ℝ)) *ᵥ y) ((Finite.equivFin V) v)) ≤
          (b v : ℝ) :=
      (graphEdgeCoordinateReindex_rowBound_iff (G := G) b y v).1 hv
    simpa [v] using hv'
  · intro hy v
    -- Evaluate the `Fin`-indexed row inequality at the coordinate corresponding to `v`.
    have hv :
        ((((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
            (graphEdgeIncMatrix G ℚ)).map (Rat.castHom ℝ)) *ᵥ y) ((Finite.equivFin V) v)) ≤
          (b v : ℝ) := by
      simpa using hy ((Finite.equivFin V) v)
    simpa using (graphEdgeCoordinateReindex_rowBound_iff (G := G) b y v).2 hv

/-- Helper for Exercise 4.18: reindexing the `Fin`-indexed objective back to `G.edgeSet`
preserves its value on the corresponding native point. -/
private theorem graphEdgeCoordinate_dotProduct_reindex
    (c y : Fin (Nat.card G.edgeSet) → ℝ) :
    c ⬝ᵥ y =
      ∑ e : G.edgeSet, graphEdgeCoordinateReindex (G := G) c e * graphEdgeCoordinateReindex
        (G := G) y e := by
  -- Expand the `Fin`-indexed dot product and reindex the ambient sum to `G.edgeSet`.
  rw [dotProduct]
  symm
  exact Fintype.sum_equiv (Finite.equivFin G.edgeSet) _ _ fun e ↦ by
    change (graphEdgeCoordinateReindex (G := G) c e) * (graphEdgeCoordinateReindex (G := G) y e) =
      c ((Finite.equivFin G.edgeSet) e) * y ((Finite.equivFin G.edgeSet) e)
    rw [graphEdgeCoordinateReindex_apply, graphEdgeCoordinateReindex_apply]

/-- Helper for Exercise 4.18: reindexing integer lattice points along a coordinate equivalence
preserves the integer-point owner. -/
private theorem funCongrLeftSymmImage_integerPoints
    {α β : Type*} (e : α ≃ β) :
    (LinearEquiv.funCongrLeft ℝ ℝ e.symm) ''
        Set.range (fun z : α → ℤ ↦ Int.cast ∘ z) =
      Set.range (fun z : β → ℤ ↦ Int.cast ∘ z) := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    refine ⟨fun b ↦ z (e.symm b), ?_⟩
    -- Reindex the integer witness coordinatewise along the equivalence.
    funext b
    simp
  · rintro ⟨z, rfl⟩
    refine ⟨fun a ↦ (z (e a) : ℝ), ?_, ?_⟩
    · refine ⟨fun a ↦ z (e a), ?_⟩
      funext a
      rfl
    · -- The inverse reindexing recovers the original integer-valued coordinate function.
      funext b
      simp

/-- Helper for Exercise 4.18: coordinate reindexing commutes with intersections of ambient
function-space subsets. -/
private theorem funCongrLeftSymmImage_inter
    {α β : Type*} (e : α ≃ β)
    (P Q : Set (α → ℝ)) :
    (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' (P ∩ Q) =
      (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P ∩
        (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' Q := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxP, hxQ⟩, rfl⟩
    exact ⟨⟨x, hxP, rfl⟩, ⟨x, hxQ, rfl⟩⟩
  · rintro ⟨⟨x, hxP, rfl⟩, ⟨x', hxQ, hImage⟩⟩
    -- Injectivity of the coordinate equivalence forces the two witnesses to agree.
    have hxx' : x = x' := by
      apply (LinearEquiv.funCongrLeft ℝ ℝ e.symm).injective
      simpa using hImage.symm
    exact ⟨x, ⟨hxP, hxx' ▸ hxQ⟩, rfl⟩

/-- Helper for Exercise 4.18: transporting an integral `Fin`-indexed owner through the canonical
coordinate equivalence preserves integrality. -/
private theorem isIntegralFunCongrLeftSymmImage
    {α β : Type*} [Finite α] [Finite β] (e : α ≃ β)
    {P : Set (α → ℝ)} (hP : is_integral P) :
    is_integral ((LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P) := by
  rw [is_integral_iff] at hP ⊢
  calc
    (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P =
        (LinearEquiv.funCongrLeft ℝ ℝ e.symm) ''
          convexHull ℝ (P ∩ Set.range (fun z : α → ℤ ↦ Int.cast ∘ z)) := by
          exact congrArg (Set.image (LinearEquiv.funCongrLeft ℝ ℝ e.symm)) hP
    _ = convexHull ℝ
          ((LinearEquiv.funCongrLeft ℝ ℝ e.symm) ''
            (P ∩ Set.range (fun z : α → ℤ ↦ Int.cast ∘ z))) := by
          -- Linear images commute with convex hulls.
          simpa using
            (LinearEquiv.funCongrLeft ℝ ℝ e.symm).toLinearMap.image_convexHull
              (P ∩ Set.range (fun z : α → ℤ ↦ Int.cast ∘ z))
    _ = convexHull ℝ
          ((LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P ∩
            Set.range (fun z : β → ℤ ↦ Int.cast ∘ z)) := by
          -- The image of the integer owner is exactly the reindexed integer lattice.
          rw [funCongrLeftSymmImage_inter, funCongrLeftSymmImage_integerPoints]

/-- Helper for Exercise 4.18: reindexing a native integral edge vector gives an integral
`Fin`-indexed edge vector. -/
private theorem graphEdgeCoordinates_mem_integerVectors
    {x : G.edgeSet → ℝ}
    (hx : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ fun e ↦ (z e : ℝ))) :
    graphEdgeCoordinates (G := G) x ∈ integerVectors (Nat.card G.edgeSet) := by
  rcases hx with ⟨z, rfl⟩
  refine (mem_integerVectors_iff (n := Nat.card G.edgeSet)).2 ?_
  refine ⟨fun j ↦ z ((Finite.equivFin G.edgeSet).symm j), ?_⟩
  -- Reindex the native integer witness coordinatewise along the chosen finite edge enumeration.
  funext j
  simp [graphEdgeCoordinates]

/-- Helper for Exercise 4.18: reindexing a native feasible edge vector places it in the canonical
`Fin`-indexed incidence presentation. -/
private theorem graphEdgeCoordinates_mem_incidencePresentation
    (b : V → ℚ)
    {x : G.edgeSet → ℝ}
    (hx : x ∈ graph_edge_incidence_polyhedron G b) :
    graphEdgeCoordinates (G := G) x ∈
      rational_matrix_polyhedron
        (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
          (graphEdgeIncMatrix G ℚ))
        (fun i ↦ b ((Finite.equivFin V).symm i)) := by
  have hxReindexed :
      graphEdgeCoordinateReindex (G := G) (graphEdgeCoordinates (G := G) x) ∈
        graph_edge_incidence_polyhedron G b := by
    -- The native coordinate vector is exactly the inverse image under the fixed reindexing
    -- equivalence.
    exact (graphEdgeCoordinateReindex_graphEdgeCoordinates (G := G) x).symm ▸ hx
  exact (graphEdgeCoordinateReindex_mem_incidencePresentation_iff (G := G) b).1 hxReindexed

/-- Helper for Exercise 4.18: evaluating the `Fin`-indexed objective on a reindexed native point
recovers the corresponding native edge sum. -/
private theorem graphEdgeCoordinates_dotProduct
    (c : Fin (Nat.card G.edgeSet) → ℝ)
    (x : G.edgeSet → ℝ) :
    c ⬝ᵥ graphEdgeCoordinates (G := G) x =
      ∑ e : G.edgeSet, graphEdgeCoordinateReindex (G := G) c e * x e := by
  -- First rewrite the `Fin`-indexed dot product through the reindexing equivalence, then collapse
  -- the inverse coordinate map back to `x`.
  calc
    c ⬝ᵥ graphEdgeCoordinates (G := G) x =
        ∑ e : G.edgeSet,
          graphEdgeCoordinateReindex (G := G) c e *
            graphEdgeCoordinateReindex (G := G) (graphEdgeCoordinates (G := G) x) e := by
          rw [graphEdgeCoordinate_dotProduct_reindex (G := G) c
            (graphEdgeCoordinates (G := G) x)]
    _ = ∑ e : G.edgeSet, graphEdgeCoordinateReindex (G := G) c e * x e := by
          rw [graphEdgeCoordinateReindex_graphEdgeCoordinates (G := G) x]

/-- Helper for Exercise 4.18: the canonical `Fin`-indexed rational incidence matrix of `G`. -/
private abbrev graphFinIncMatrixQ :
    Matrix (Fin (Nat.card V)) (Fin (Nat.card G.edgeSet)) ℚ :=
  Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (graphEdgeIncMatrix G ℚ)

/-- Helper for Exercise 4.18: the canonical `Fin`-indexed integral incidence matrix of `G`. -/
private abbrev graphFinIncMatrixInt :
    Matrix (Fin (Nat.card V)) (Fin (Nat.card G.edgeSet)) ℤ :=
  Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (graphEdgeIncMatrix G ℤ)

/-- Helper for Exercise 4.18: the canonical `Fin`-indexed split incidence matrix has one positive
and one negative copy of each edge column. -/
private abbrev splitFinGraphEdgeIncMatrix :
    Matrix (Fin (Nat.card V))
      (Fin (Nat.card G.edgeSet + Nat.card G.edgeSet)) ℤ :=
  Matrix.reindex (Equiv.refl _)
    finSumFinEquiv
    (Matrix.fromCols (graphFinIncMatrixInt (G := G)) (-(graphFinIncMatrixInt (G := G))))

/-- Helper for Exercise 4.18: projecting split `Fin` coordinates back to the native edge owner
takes the positive copy minus the negative copy. -/
private abbrev splitFinProjection
    (y : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ) :
    Fin (Nat.card G.edgeSet) → ℝ :=
  fun j ↦ y (Fin.castAdd (Nat.card G.edgeSet) j) -
    y (Fin.natAdd (Nat.card G.edgeSet) j)

/-- Helper for Exercise 4.18: the canonical `Fin`-indexed split objective agrees with the native
objective after projection. -/
private abbrev splitFinObjective
    (c : Fin (Nat.card G.edgeSet) → ℝ) :
    Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ :=
  Fin.append c (fun j ↦ -c j)

/-- Helper for Exercise 4.18: the canonical `Fin`-indexed split lift records positive and
negative parts separately. -/
private abbrev splitFinLift
    (x : Fin (Nat.card G.edgeSet) → ℝ) :
    Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ :=
  Fin.append (fun j ↦ max (x j) 0) (fun j ↦ max (-x j) 0)

/-- Helper for Exercise 4.18: the reindexed integral incidence matrix casts to the rational
presentation already used for the native-to-`Fin` transport layer. -/
private theorem graphFinIncMatrix_intCast :
    (graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ) =
      (graphFinIncMatrixQ (G := G)).map (Rat.castHom ℝ) := by
  -- Both reindexed matrices still encode the same `0/1` incidence pattern after coercion to `ℝ`.
  ext i j
  let v : V := (Finite.equivFin V).symm i
  let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm j
  by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
  · change (((graphEdgeIncMatrix G ℤ) v e : ℤ) : ℝ) = (((graphEdgeIncMatrix G ℚ) v e : ℚ) : ℝ)
    simp [graphEdgeIncMatrix, SimpleGraph.incMatrix_apply', h]
  · change (((graphEdgeIncMatrix G ℤ) v e : ℤ) : ℝ) = (((graphEdgeIncMatrix G ℚ) v e : ℚ) : ℝ)
    simp [graphEdgeIncMatrix, SimpleGraph.incMatrix_apply', h]

/-- Helper for Exercise 4.18: projecting the split lift recovers the original `Fin`-indexed edge
vector. -/
private theorem splitFinProjection_splitFinLift
    (x : Fin (Nat.card G.edgeSet) → ℝ) :
    splitFinProjection (G := G) (splitFinLift (G := G) x) = x := by
  -- Evaluate the positive and negative copies on each edge and collapse them with the
  -- positive-part identity.
  ext j
  rw [splitFinProjection, splitFinLift, Fin.append_left, Fin.append_right]
  simpa using max_zero_sub_max_neg_zero_eq_self (x j)

/-- Helper for Exercise 4.18: the split objective on the canonical `Fin` owner is exactly the
native objective on the projected edge vector. -/
private theorem splitFinObjective_dot_eq_projection
    (c : Fin (Nat.card G.edgeSet) → ℝ)
    (y : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ) :
    splitFinObjective (G := G) c ⬝ᵥ y = c ⬝ᵥ splitFinProjection (G := G) y := by
  -- Split the `Fin (n + n)` objective sum into the two copies and recombine them edgewise.
  rw [dotProduct, Fin.sum_univ_add]
  calc
    ∑ j : Fin (Nat.card G.edgeSet),
        splitFinObjective (G := G) c (Fin.castAdd (Nat.card G.edgeSet) j) *
          y (Fin.castAdd (Nat.card G.edgeSet) j) +
      ∑ j : Fin (Nat.card G.edgeSet),
        splitFinObjective (G := G) c (Fin.natAdd (Nat.card G.edgeSet) j) *
          y (Fin.natAdd (Nat.card G.edgeSet) j) =
        ∑ j : Fin (Nat.card G.edgeSet), c j * y (Fin.castAdd (Nat.card G.edgeSet) j) +
          ∑ j : Fin (Nat.card G.edgeSet), (-c j) * y (Fin.natAdd (Nat.card G.edgeSet) j) := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro j hj
              simp [splitFinObjective, Fin.append_left]
            · refine Finset.sum_congr rfl ?_
              intro j hj
              rw [splitFinObjective, Fin.append_right]
    _ = ∑ j : Fin (Nat.card G.edgeSet),
          c j * (y (Fin.castAdd (Nat.card G.edgeSet) j) -
            y (Fin.natAdd (Nat.card G.edgeSet) j)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = c ⬝ᵥ splitFinProjection (G := G) y := by
          simp [dotProduct, splitFinProjection]

/-- Helper for Exercise 4.18: the split objective preserves the native objective value on the
canonical `Fin` split lift. -/
private theorem splitFinObjective_dot_splitFinLift
    (c x : Fin (Nat.card G.edgeSet) → ℝ) :
    splitFinObjective (G := G) c ⬝ᵥ splitFinLift (G := G) x = c ⬝ᵥ x := by
  -- Rewrite through the split projection and then collapse the split lift back to `x`.
  rw [splitFinObjective_dot_eq_projection, splitFinProjection_splitFinLift]

/-- Helper for Exercise 4.18: the canonical split lift is coordinatewise nonnegative. -/
private theorem splitFinLift_nonneg
    (x : Fin (Nat.card G.edgeSet) → ℝ)
    (j : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet)) :
    0 ≤ splitFinLift (G := G) x j := by
  -- Check the positive and negative copies separately after decomposing `j`.
  cases j using Fin.addCases
  · rename_i i
    rw [splitFinLift, Fin.append_left]
    exact le_max_right (x i) (0 : ℝ)
  · rename_i i
    rw [splitFinLift, Fin.append_right]
    exact le_max_right (-x i) (0 : ℝ)

/-- Helper for Exercise 4.18: the split-pair perturbation adds equally to the two copies of a
single edge coordinate. -/
private abbrev splitPairDirection
    (j : Fin (Nat.card G.edgeSet)) :
    Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ :=
  Fin.append (Pi.single j (1 : ℝ)) (Pi.single j (1 : ℝ))

/-- Helper for Exercise 4.18: the split-pair perturbation has zero native projection because it
changes the positive and negative copies by the same amount. -/
private theorem splitFinProjection_pairDirection
    (j : Fin (Nat.card G.edgeSet)) :
    splitFinProjection (G := G) (splitPairDirection (G := G) j) = 0 := by
  -- Check the projected left-minus-right difference on each edge coordinate.
  ext k
  by_cases hk : k = j
  · subst hk
    rw [splitFinProjection, splitPairDirection, Fin.append_left, Fin.append_right]
    simp
  · rw [splitFinProjection, splitPairDirection, Fin.append_left, Fin.append_right]
    simp [Pi.single_apply, hk]

/-- Helper for Exercise 4.18: multiplying the canonical split `Fin` matrix by a split vector
recovers the reindexed incidence product of its projected edge coordinates. -/
private theorem splitFinGraphEdgeIncMatrix_apply_castAdd
    (i : Fin (Nat.card V)) (j : Fin (Nat.card G.edgeSet)) :
    (((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) i
        (Fin.castAdd (Nat.card G.edgeSet) j)) =
      (((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) i j) := by
  -- The positive split copy is the original reindexed incidence column.
  change
    (((Matrix.fromCols
        (graphFinIncMatrixInt (G := G))
        (-(graphFinIncMatrixInt (G := G)))) i
        (finSumFinEquiv.symm (Fin.castAdd (Nat.card G.edgeSet) j)) : ℤ) : ℝ) =
      (((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) i j)
  rw [finSumFinEquiv_symm_apply_castAdd]
  simp

/-- Helper for Exercise 4.18: the negative split copy of the canonical `Fin` split matrix is the
negated reindexed incidence column. -/
private theorem splitFinGraphEdgeIncMatrix_apply_natAdd
    (i : Fin (Nat.card V)) (j : Fin (Nat.card G.edgeSet)) :
    (((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) i
        (Fin.natAdd (Nat.card G.edgeSet) j)) =
      -(((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) i j) := by
  -- The negative split copy records the opposite incidence column.
  change
    (((Matrix.fromCols
        (graphFinIncMatrixInt (G := G))
        (-(graphFinIncMatrixInt (G := G)))) i
        (finSumFinEquiv.symm (Fin.natAdd (Nat.card G.edgeSet) j)) : ℤ) : ℝ) =
      -(((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) i j)
  rw [finSumFinEquiv_symm_apply_natAdd]
  change (((-(graphFinIncMatrixInt (G := G) i j) : ℤ) : ℝ) =
      -(((graphFinIncMatrixInt (G := G) i j : ℤ) : ℝ)))
  exact Int.cast_neg (R := ℝ) (graphFinIncMatrixInt (G := G) i j)

/-- Helper for Exercise 4.18: multiplying the canonical split `Fin` matrix by a split vector
recovers the reindexed incidence product of its projected edge coordinates. -/
private theorem splitFinGraphEdgeIncMatrix_mulVec
    (y : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ) :
    (((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) *ᵥ y) =
      (((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
        splitFinProjection (G := G) y) := by
  have happend :
      (((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
          fun j ↦ y (Fin.castAdd (Nat.card G.edgeSet) j)) +
        (((-((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ))) *ᵥ
          fun j ↦ y (Fin.natAdd (Nat.card G.edgeSet) j))) =
      (((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
        splitFinProjection (G := G) y) := by
    -- Collapse the positive and negative row sums edgewise into the projected coordinate.
    ext i
    change
      ((((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
            fun j ↦ y (Fin.castAdd (Nat.card G.edgeSet) j)) i +
          (((-((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ))) *ᵥ
              fun j ↦ y (Fin.natAdd (Nat.card G.edgeSet) j)) i)) =
        ((((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
            splitFinProjection (G := G) y) i)
    rw [Matrix.mulVec, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, dotProduct]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    change
      (((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) i j *
          y (Fin.castAdd (Nat.card G.edgeSet) j) +
        (-((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) i j) *
          y (Fin.natAdd (Nat.card G.edgeSet) j)) =
      (((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) i j *
        (y (Fin.castAdd (Nat.card G.edgeSet) j) -
          y (Fin.natAdd (Nat.card G.edgeSet) j)))
    ring
  calc
    (((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) *ᵥ y) =
        (fun i ↦
          ∑ j : Fin (Nat.card G.edgeSet),
              (((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) i
                  (Fin.castAdd (Nat.card G.edgeSet) j)) *
                y (Fin.castAdd (Nat.card G.edgeSet) j) +
            ∑ j : Fin (Nat.card G.edgeSet),
              (((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) i
                  (Fin.natAdd (Nat.card G.edgeSet) j)) *
                y (Fin.natAdd (Nat.card G.edgeSet) j)) := by
          funext i
          rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
    _ =
        (((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
            (fun j ↦ y (Fin.castAdd (Nat.card G.edgeSet) j)) +
          (-((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ))) *ᵥ
            (fun j ↦ y (Fin.natAdd (Nat.card G.edgeSet) j))) := by
          ext i
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro j hj
            rw [splitFinGraphEdgeIncMatrix_apply_castAdd]
          · refine Finset.sum_congr rfl ?_
            intro j hj
            rw [splitFinGraphEdgeIncMatrix_apply_natAdd]
            change
              -(((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) i j) *
                  y (Fin.natAdd (Nat.card G.edgeSet) j) =
                (-((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ))) i j *
                  y (Fin.natAdd (Nat.card G.edgeSet) j)
            rfl
    _ =
        (((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
          splitFinProjection (G := G) y) := happend

/-- Helper for Exercise 4.18: lifting a native feasible point into the canonical split `Fin`
owner produces a nonnegative feasible point for the even split system. -/
private theorem splitFinLift_mem_nonnegativePresentation
    (b : V → ℚ)
    (bHalf : V → ℤ)
    (hbHalf : ∀ v, b v = (2 * bHalf v : ℚ))
    {x : G.edgeSet → ℝ}
    (hx : x ∈ graph_edge_incidence_polyhedron G b) :
    splitFinLift (G := G) (graphEdgeCoordinates (G := G) x) ∈
      nonnegative_matrix_polyhedron
        (splitFinGraphEdgeIncMatrix (G := G))
        (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)) := by
  -- Unfold the split nonnegative system into its row inequalities and coordinatewise
  -- nonnegativity, then rewrite the row operator back to the native reindexed presentation.
  refine ⟨?_, ?_⟩
  · intro i
    have hxFin :
        graphEdgeCoordinates (G := G) x ∈
          rational_matrix_polyhedron
            (graphFinIncMatrixQ (G := G))
            (fun j ↦ b ((Finite.equivFin V).symm j)) :=
      graphEdgeCoordinates_mem_incidencePresentation (G := G) b hx
    have hxFinRows :
        ((graphFinIncMatrixQ (G := G)).map (Rat.castHom ℝ)) *ᵥ
            graphEdgeCoordinates (G := G) x ≤
          fun j ↦ (b ((Finite.equivFin V).symm j) : ℝ) := by
      exact (mem_rational_matrix_polyhedron
        (graphFinIncMatrixQ (G := G))
        (fun j ↦ b ((Finite.equivFin V).symm j))
        (graphEdgeCoordinates (G := G) x)).1 hxFin
    have hbHalfR :
        (b ((Finite.equivFin V).symm i) : ℝ) =
          ((2 * bHalf ((Finite.equivFin V).symm i) : ℤ) : ℝ) := by
      norm_num [hbHalf ((Finite.equivFin V).symm i)]
    calc
      ((((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) *ᵥ
          splitFinLift (G := G) (graphEdgeCoordinates (G := G) x)) i) =
          ((((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
              graphEdgeCoordinates (G := G) x) i) := by
            rw [splitFinGraphEdgeIncMatrix_mulVec, splitFinProjection_splitFinLift]
      _ = ((((graphFinIncMatrixQ (G := G)).map (Rat.castHom ℝ)) *ᵥ
              graphEdgeCoordinates (G := G) x) i) := by
            rw [graphFinIncMatrix_intCast]
      _ ≤ (b ((Finite.equivFin V).symm i) : ℝ) := hxFinRows i
      _ = ((2 * bHalf ((Finite.equivFin V).symm i) : ℤ) : ℝ) := hbHalfR
  · intro j
    -- The split lift stores positive and negative parts, so each split coordinate is nonnegative.
    exact splitFinLift_nonneg (G := G) (graphEdgeCoordinates (G := G) x) j

/-- Helper for Exercise 4.18: every nonempty exposed face of a polyhedron has the same lineality
space as the ambient polyhedron. -/
private lemma exposedFace_linealitySpace_eq
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {rhs : Fin m → ℝ}
    {F : Set (Fin n → ℝ)}
    (hF : IsExposed ℝ (polyhedron_le_set A rhs) F)
    (hF_nonempty : F.Nonempty) :
    linealitySpace F = linealitySpace (polyhedron_le_set A rhs) := by
  obtain ⟨I, hI⟩ := exists_eq_active_constraint_face_of_isExposed A rhs F hF hF_nonempty
  obtain ⟨x₀, hx₀F⟩ := hF_nonempty
  have hx₀_active : x₀ ∈ active_constraint_face A rhs I := by
    simpa [hI] using hx₀F
  have hP_nonempty : (polyhedron_le_set A rhs).Nonempty := by
    exact ⟨x₀, mem_polyhedron_of_mem_active_constraint_face hx₀_active⟩
  have hkernelP := polyhedron_linealitySpace_eq_kernel_set A rhs hP_nonempty
  rw [hI, hkernelP]
  ext r
  constructor
  · intro hr
    rw [mem_linealitySpace_iff] at hr
    ext i
    by_cases hi : i ∈ I
    · -- Active rows stay tight along any lineality direction inside the exposed face.
      have hx₀_eq : (A *ᵥ x₀) i = rhs i := (mem_active_constraint_face_iff.mp hx₀_active).1 i hi
      have htranslate_eq :
          (A *ᵥ (x₀ + (1 : ℝ) • r)) i = rhs i := by
        exact (mem_active_constraint_face_iff.mp (hr hx₀_active 1)).1 i hi
      calc
        (A *ᵥ r) i = (A *ᵥ (x₀ + (1 : ℝ) • r)) i - (A *ᵥ x₀) i := by
            simp [Matrix.mulVec_add]
        _ = rhs i - rhs i := by rw [htranslate_eq, hx₀_eq]
        _ = 0 := by simp
    · have htranslate :
          ∀ a : ℝ, (A *ᵥ (x₀ + a • r)) i ≤ rhs i := by
        intro a
        exact (mem_active_constraint_face_iff.mp (hr hx₀_active a)).2 i hi
      by_contra hri
      let a : ℝ := (rhs i - (A *ᵥ x₀) i + 1) / (A *ᵥ r) i
      have htranslate' : (A *ᵥ x₀) i + a * (A *ᵥ r) i ≤ rhs i := by
        simpa [Matrix.mulVec_add, Matrix.mulVec_smul, a] using htranslate a
      have ha_mul : a * (A *ᵥ r) i = rhs i - (A *ᵥ x₀) i + 1 := by
        dsimp [a]
        exact div_mul_cancel₀ _ hri
      linarith
  · intro hr
    rw [mem_linealitySpace_iff]
    have hr_zero : A *ᵥ r = 0 := by
      simpa [hkernelP] using hr
    intro x hxF a
    refine (mem_active_constraint_face_iff).2 ?_
    rcases mem_active_constraint_face_iff.mp hxF with ⟨hxEq, hxLe⟩
    constructor
    · intro i hi
      have hri : (A *ᵥ r) i = 0 := by
        simpa using congrFun hr_zero i
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, hri] using hxEq i hi
    · intro i hi
      have hri : (A *ᵥ r) i = 0 := by
        simpa using congrFun hr_zero i
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, hri] using hxLe i hi

/-- Helper for Exercise 4.18: any feasible point of the canonical split system projects to a
native feasible point of `graph_edge_incidence_polyhedron G b`. -/
private lemma splitFinProjection_mem_graphEdgeIncidencePolyhedron
    (b : V → ℚ)
    (bHalf : V → ℤ)
    (hbHalf : ∀ v, b v = (2 * bHalf v : ℚ))
    {y : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ}
    (hy :
      y ∈
        nonnegative_matrix_polyhedron
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i))) :
    graphEdgeCoordinateReindex (G := G) (splitFinProjection (G := G) y) ∈
      graph_edge_incidence_polyhedron G b := by
  have hyRows :
      (((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) *ᵥ y) ≤
        fun i ↦ ((2 * bHalf ((Finite.equivFin V).symm i) : ℤ) : ℝ) := by
    exact (mem_nonnegative_matrix_polyhedron_iff.1 hy).1
  have hyFin :
      splitFinProjection (G := G) y ∈
        rational_matrix_polyhedron
          (graphFinIncMatrixQ (G := G))
          (fun i ↦ b ((Finite.equivFin V).symm i)) := by
    rw [mem_rational_matrix_polyhedron]
    intro i
    calc
      ((((graphFinIncMatrixQ (G := G)).map (Rat.castHom ℝ)) *ᵥ
          splitFinProjection (G := G) y) i) =
          ((((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
              splitFinProjection (G := G) y) i) := by
            rw [graphFinIncMatrix_intCast]
      _ = ((((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) *ᵥ y) i) := by
            rw [splitFinGraphEdgeIncMatrix_mulVec]
      _ ≤ ((2 * bHalf ((Finite.equivFin V).symm i) : ℤ) : ℝ) := hyRows i
      _ = (b ((Finite.equivFin V).symm i) : ℝ) := by
            norm_num [hbHalf ((Finite.equivFin V).symm i)]
  exact (graphEdgeCoordinateReindex_mem_incidencePresentation_iff (G := G) b).2 hyFin

/-- Helper for Exercise 4.18: the canonical split maximizing face contains an extreme point. -/
private lemma splitFinOptimalFace_hasExtremePoint
    (b : V → ℚ)
    (bHalf : V → ℤ)
    (hbHalf : ∀ v, b v = (2 * bHalf v : ℚ))
    (cNative : G.edgeSet → ℝ)
    (z : ℝ)
    {y₀ : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ}
    (hy₀Feasible :
      y₀ ∈
        nonnegative_matrix_polyhedron
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
    (hy₀Objective :
      splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ y₀ = z)
    (hzNative :
      IsGreatest
        ((fun x : G.edgeSet → ℝ ↦ ∑ e : G.edgeSet, cNative e * x e) ''
          graph_edge_incidence_polyhedron G b)
        z) :
    ∃ ybar,
      ybar ∈
        (face_set
          (nonnegative_matrix_polyhedron
            (splitFinGraphEdgeIncMatrix (G := G))
            (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
          (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
          z).extremePoints ℝ := by
  let Psplit :
      Set (Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ) :=
    nonnegative_matrix_polyhedron
      (splitFinGraphEdgeIncMatrix (G := G))
      (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i))
  let Fsplit :
      Set (Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ) :=
    face_set Psplit (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative)) z
  have hPsplit_polyhedron : is_polyhedron Psplit := by
    simpa [Psplit] using
      nonnegative_matrix_polyhedron_is_polyhedron
        (splitFinGraphEdgeIncMatrix (G := G))
        (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i))
  have hFsplit_polyhedron : is_polyhedron Fsplit := by
    simpa [Psplit, Fsplit] using
      face_set_nonnegative_matrix_polyhedron_is_polyhedron
        (splitFinGraphEdgeIncMatrix (G := G))
        (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i))
        (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
        z
  have hvalid :
      is_valid_inequality Psplit
        (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
        z := by
    intro y hyPsplit
    have hyNative :
        graphEdgeCoordinateReindex (G := G) (splitFinProjection (G := G) y) ∈
          graph_edge_incidence_polyhedron G b :=
      splitFinProjection_mem_graphEdgeIncidencePolyhedron
        (G := G) b bHalf hbHalf hyPsplit
    have hyObjective_image :
        splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ y ∈
          ((fun x : G.edgeSet → ℝ ↦ ∑ e : G.edgeSet, cNative e * x e) ''
            graph_edge_incidence_polyhedron G b) := by
      refine ⟨graphEdgeCoordinateReindex (G := G) (splitFinProjection (G := G) y), hyNative, ?_⟩
      -- Rewrite the split objective through the projected native edge coordinates.
      symm
      calc
        splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ y =
            graphEdgeCoordinates (G := G) cNative ⬝ᵥ splitFinProjection (G := G) y := by
              rw [splitFinObjective_dot_eq_projection]
        _ = ∑ e : G.edgeSet,
              graphEdgeCoordinateReindex (G := G)
                  (graphEdgeCoordinates (G := G) cNative) e *
                graphEdgeCoordinateReindex (G := G)
                  (splitFinProjection (G := G) y) e := by
              rw [graphEdgeCoordinate_dotProduct_reindex (G := G)
                (graphEdgeCoordinates (G := G) cNative)
                (splitFinProjection (G := G) y)]
        _ = ∑ e : G.edgeSet,
              cNative e *
                graphEdgeCoordinateReindex (G := G)
                  (splitFinProjection (G := G) y) e := by
              rw [graphEdgeCoordinateReindex_graphEdgeCoordinates (G := G) cNative]
    exact hzNative.2 hyObjective_image
  have hy₀Fsplit : y₀ ∈ Fsplit := by
    -- The lifted native maximizer lies on the split maximizing face by construction.
    rw [mem_face_set_iff]
    exact ⟨hy₀Feasible, hy₀Objective⟩
  have hFsplit_nonempty : Fsplit.Nonempty := ⟨y₀, hy₀Fsplit⟩
  have hFsplit_exposed : IsExposed ℝ Psplit Fsplit := by
    simpa [Psplit, Fsplit] using isExposed_face_set_of_valid_inequality hvalid
  have hPsplit_lineality :
      linealitySpace Psplit = ({0} : Set (Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ)) := by
    ext r
    constructor
    · intro hr
      change r = 0
      exact eq_zero_of_mem_linealitySpace_nonnegative_matrix_polyhedron hr hy₀Feasible
    · intro hr
      rcases Set.mem_singleton_iff.mp hr with rfl
      exact zero_mem_linealitySpace
  have hFsplit_lineality :
      linealitySpace Fsplit = ({0} : Set (Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ)) := by
    let M :
        Matrix (Fin (Nat.card V + (Nat.card G.edgeSet + Nat.card G.edgeSet)))
          (Fin (Nat.card G.edgeSet + Nat.card G.edgeSet)) ℝ :=
      ((Matrix.fromRows
          (splitFinGraphEdgeIncMatrix (G := G))
          (-(1 : Matrix
            (Fin (Nat.card G.edgeSet + Nat.card G.edgeSet))
            (Fin (Nat.card G.edgeSet + Nat.card G.edgeSet)) ℤ))).reindex
          finSumFinEquiv (Equiv.refl _)).map (Int.castRingHom ℝ)
    let rhs :
        Fin (Nat.card V + (Nat.card G.edgeSet + Nat.card G.edgeSet)) → ℝ :=
      fun i ↦
        ((Sum.elim
          (fun j : Fin (Nat.card V) ↦ 2 * bHalf ((Finite.equivFin V).symm j))
          (fun _ : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) ↦ 0) ∘
            finSumFinEquiv.symm) i : ℝ)
    have hFsplit_exposed' : IsExposed ℝ (polyhedron_le_set M rhs) Fsplit := by
      simpa [Psplit, M, rhs,
        nonnegative_matrix_polyhedron_eq_polyhedron_le_set
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i))] using hFsplit_exposed
    have hlineality :
        linealitySpace Fsplit = linealitySpace (polyhedron_le_set M rhs) :=
      exposedFace_linealitySpace_eq hFsplit_exposed' hFsplit_nonempty
    have hpoly_lineality :
        linealitySpace (polyhedron_le_set M rhs) =
          ({0} : Set (Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ)) := by
      simpa [Psplit, M, rhs,
        nonnegative_matrix_polyhedron_eq_polyhedron_le_set
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i))] using hPsplit_lineality
    exact hlineality.trans hpoly_lineality
  have hFsplit_extreme_nonempty :
      (Fsplit.extremePoints ℝ).Nonempty := by
    exact
      (polyhedron_extremePoints_nonempty_iff_linealitySpace_eq_zero
        hFsplit_polyhedron hFsplit_nonempty).2 hFsplit_lineality
  simpa [Fsplit] using hFsplit_extreme_nonempty

/-- Helper for Exercise 4.18: if both split copies of one edge are positive, then a small
perturbation along `splitPairDirection` stays inside the same split optimal face. -/
private lemma splitPairDirection_mem_optimalFace
    (bHalf : V → ℤ)
    (cNative : G.edgeSet → ℝ)
    (z : ℝ)
    {ybar : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ}
    (hybarFace :
      ybar ∈
        face_set
          (nonnegative_matrix_polyhedron
            (splitFinGraphEdgeIncMatrix (G := G))
            (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
          (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
          z)
    (j : Fin (Nat.card G.edgeSet))
    (hjLeft : 0 < ybar (Fin.castAdd (Nat.card G.edgeSet) j))
    (hjRight : 0 < ybar (Fin.natAdd (Nat.card G.edgeSet) j)) :
    ∃ ε > 0,
      ybar - ε • splitPairDirection (G := G) j ∈
        face_set
          (nonnegative_matrix_polyhedron
            (splitFinGraphEdgeIncMatrix (G := G))
            (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
          (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
          z ∧
      ybar + ε • splitPairDirection (G := G) j ∈
        face_set
          (nonnegative_matrix_polyhedron
            (splitFinGraphEdgeIncMatrix (G := G))
            (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
          (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
          z ∧
      ybar - ε • splitPairDirection (G := G) j ≠ ybar ∧
      ybar + ε • splitPairDirection (G := G) j ≠ ybar := by
  have hybarFeasible :
      ybar ∈
        nonnegative_matrix_polyhedron
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)) := by
    -- Read feasibility off the split optimal-face membership.
    exact (mem_face_set_iff.mp hybarFace).1
  have hybarObjective :
      splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ ybar = z := by
    -- Read the objective equality off the same face membership.
    exact (mem_face_set_iff.mp hybarFace).2
  have hybarRows := (mem_nonnegative_matrix_polyhedron_iff.1 hybarFeasible).1
  have hybarNonneg := (mem_nonnegative_matrix_polyhedron_iff.1 hybarFeasible).2
  let ε : ℝ :=
    min (ybar (Fin.castAdd (Nat.card G.edgeSet) j))
      (ybar (Fin.natAdd (Nat.card G.edgeSet) j)) / 2
  have hε_pos : 0 < ε := by
    -- Choose half the smaller positive split coordinate so the negative perturbation stays
    -- nonnegative on both copies.
    dsimp [ε]
    have hmin_pos :
        0 <
          min (ybar (Fin.castAdd (Nat.card G.edgeSet) j))
            (ybar (Fin.natAdd (Nat.card G.edgeSet) j)) := by
      exact lt_min hjLeft hjRight
    linarith
  have hε_left :
      ε ≤ ybar (Fin.castAdd (Nat.card G.edgeSet) j) := by
    -- The chosen perturbation is bounded by the left split coordinate.
    dsimp [ε]
    have hmin_le :
        min (ybar (Fin.castAdd (Nat.card G.edgeSet) j))
            (ybar (Fin.natAdd (Nat.card G.edgeSet) j)) ≤
          ybar (Fin.castAdd (Nat.card G.edgeSet) j) :=
      min_le_left _ _
    linarith
  have hε_right :
      ε ≤ ybar (Fin.natAdd (Nat.card G.edgeSet) j) := by
    -- The same choice is also bounded by the right split coordinate.
    dsimp [ε]
    have hmin_le :
        min (ybar (Fin.castAdd (Nat.card G.edgeSet) j))
            (ybar (Fin.natAdd (Nat.card G.edgeSet) j)) ≤
          ybar (Fin.natAdd (Nat.card G.edgeSet) j) :=
      min_le_right _ _
    linarith
  have hprojection_shift :
      ∀ a : ℝ,
        splitFinProjection (G := G) (ybar + a • splitPairDirection (G := G) j) =
          splitFinProjection (G := G) ybar := by
    intro a
    -- Route correction: use the fixed split owner directly and compute the two changed
    -- coordinates, instead of reopening any global owner transport.
    ext k
    by_cases hk : k = j
    · subst hk
      simp [splitFinProjection, splitPairDirection, Fin.append_left, Fin.append_right]
      ring
    · simp [splitFinProjection, splitPairDirection, Fin.append_left, Fin.append_right, hk]
  have hminusProjection :
      splitFinProjection (G := G) (ybar - ε • splitPairDirection (G := G) j) =
        splitFinProjection (G := G) ybar := by
    simpa [sub_eq_add_neg] using hprojection_shift (-ε)
  have hplusProjection :
      splitFinProjection (G := G) (ybar + ε • splitPairDirection (G := G) j) =
        splitFinProjection (G := G) ybar :=
    hprojection_shift ε
  have hminusFeasible :
      ybar - ε • splitPairDirection (G := G) j ∈
        nonnegative_matrix_polyhedron
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)) := by
    refine ⟨?_, ?_⟩
    · intro i
      -- The perturbation has zero projected incidence effect, so every row inequality is
      -- unchanged.
      calc
        ((((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) *ᵥ
            (ybar - ε • splitPairDirection (G := G) j)) i) =
            ((((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
                splitFinProjection (G := G) (ybar - ε • splitPairDirection (G := G) j)) i) := by
              rw [splitFinGraphEdgeIncMatrix_mulVec]
        _ = ((((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
                splitFinProjection (G := G) ybar) i) := by
              rw [hminusProjection]
        _ = ((((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) *ᵥ ybar) i) := by
              rw [splitFinGraphEdgeIncMatrix_mulVec]
        _ ≤ ((2 * bHalf ((Finite.equivFin V).symm i) : ℤ) : ℝ) := by
              exact hybarRows i
    · intro k
      cases k using Fin.addCases with
      | left i =>
          by_cases hi : i = j
          · subst hi
            -- The chosen `ε` keeps the left split copy nonnegative.
            have : 0 ≤ ybar (Fin.castAdd (Nat.card G.edgeSet) j) - ε := by
              linarith [hε_left]
            simpa [sub_eq_add_neg, splitPairDirection, Fin.append_left] using this
          · -- All other left coordinates are untouched by the perturbation.
            simp [sub_eq_add_neg, splitPairDirection, Fin.append_left, hi, hybarNonneg]
      | right i =>
          by_cases hi : i = j
          · subst hi
            -- The same estimate controls the right split copy.
            have : 0 ≤ ybar (Fin.natAdd (Nat.card G.edgeSet) j) - ε := by
              linarith [hε_right]
            simpa [sub_eq_add_neg, splitPairDirection, Fin.append_right] using this
          · -- All other right coordinates are also unchanged.
            simp [sub_eq_add_neg, splitPairDirection, Fin.append_right, hi, hybarNonneg]
  have hplusFeasible :
      ybar + ε • splitPairDirection (G := G) j ∈
        nonnegative_matrix_polyhedron
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)) := by
    refine ⟨?_, ?_⟩
    · intro i
      -- The positive perturbation also has zero projected incidence effect.
      calc
        ((((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) *ᵥ
            (ybar + ε • splitPairDirection (G := G) j)) i) =
            ((((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
                splitFinProjection (G := G) (ybar + ε • splitPairDirection (G := G) j)) i) := by
              rw [splitFinGraphEdgeIncMatrix_mulVec]
        _ = ((((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
                splitFinProjection (G := G) ybar) i) := by
              rw [hplusProjection]
        _ = ((((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) *ᵥ ybar) i) := by
              rw [splitFinGraphEdgeIncMatrix_mulVec]
        _ ≤ ((2 * bHalf ((Finite.equivFin V).symm i) : ℤ) : ℝ) := by
              exact hybarRows i
    · intro k
      -- Adding a nonnegative multiple of `splitPairDirection` preserves coordinatewise
      -- nonnegativity.
      cases k using Fin.addCases with
      | left i =>
          by_cases hi : i = j
          · subst hi
            have : 0 ≤ ybar (Fin.castAdd (Nat.card G.edgeSet) j) + ε := by
              linarith [hybarNonneg (Fin.castAdd (Nat.card G.edgeSet) j), le_of_lt hε_pos]
            simpa [splitPairDirection, Fin.append_left] using this
          · simp [splitPairDirection, Fin.append_left, hi, hybarNonneg]
      | right i =>
          by_cases hi : i = j
          · subst hi
            have : 0 ≤ ybar (Fin.natAdd (Nat.card G.edgeSet) j) + ε := by
              linarith [hybarNonneg (Fin.natAdd (Nat.card G.edgeSet) j), le_of_lt hε_pos]
            simpa [splitPairDirection, Fin.append_right] using this
          · simp [splitPairDirection, Fin.append_right, hi, hybarNonneg]
  have hminusObjective :
      splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ
          (ybar - ε • splitPairDirection (G := G) j) = z := by
    -- The split objective depends only on the projected edge vector, which is unchanged.
    calc
      splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ
          (ybar - ε • splitPairDirection (G := G) j) =
          graphEdgeCoordinates (G := G) cNative ⬝ᵥ
            splitFinProjection (G := G) (ybar - ε • splitPairDirection (G := G) j) := by
            rw [splitFinObjective_dot_eq_projection]
      _ = graphEdgeCoordinates (G := G) cNative ⬝ᵥ splitFinProjection (G := G) ybar := by
            rw [hminusProjection]
      _ = splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ ybar := by
            rw [splitFinObjective_dot_eq_projection]
      _ = z := hybarObjective
  have hplusObjective :
      splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ
          (ybar + ε • splitPairDirection (G := G) j) = z := by
    -- The same projected-objective computation works for the positive perturbation.
    calc
      splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ
          (ybar + ε • splitPairDirection (G := G) j) =
          graphEdgeCoordinates (G := G) cNative ⬝ᵥ
            splitFinProjection (G := G) (ybar + ε • splitPairDirection (G := G) j) := by
            rw [splitFinObjective_dot_eq_projection]
      _ = graphEdgeCoordinates (G := G) cNative ⬝ᵥ splitFinProjection (G := G) ybar := by
            rw [hplusProjection]
      _ = splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ ybar := by
            rw [splitFinObjective_dot_eq_projection]
      _ = z := hybarObjective
  have hminus_ne : ybar - ε • splitPairDirection (G := G) j ≠ ybar := by
    intro hEq
    -- The left split coordinate changes by the strictly positive amount `ε`.
    have hcoord := congrFun hEq (Fin.castAdd (Nat.card G.edgeSet) j)
    simp [sub_eq_add_neg, Pi.smul_apply, splitPairDirection] at hcoord
    linarith
  have hplus_ne : ybar + ε • splitPairDirection (G := G) j ≠ ybar := by
    intro hEq
    -- The same coordinate check rules out equality for the positive perturbation.
    have hcoord := congrFun hEq (Fin.castAdd (Nat.card G.edgeSet) j)
    simp [Pi.smul_apply, splitPairDirection] at hcoord
    linarith
  refine ⟨ε, hε_pos, ?_, ?_, hminus_ne, hplus_ne⟩
  · -- Assemble the negative perturbation back into face membership.
    rw [mem_face_set_iff]
    exact ⟨hminusFeasible, hminusObjective⟩
  · -- Assemble the positive perturbation back into face membership.
    rw [mem_face_set_iff]
    exact ⟨hplusFeasible, hplusObjective⟩

/-- Helper for Exercise 4.18: an extreme split maximizer cannot keep both copies of the same edge
strictly positive. -/
private lemma splitSupportHasNoDoubleCopy
    (bHalf : V → ℤ)
    (cNative : G.edgeSet → ℝ)
    (z : ℝ)
    {ybar : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ}
    (hybarExtreme :
      ybar ∈
        (face_set
          (nonnegative_matrix_polyhedron
            (splitFinGraphEdgeIncMatrix (G := G))
            (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
          (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
          z).extremePoints ℝ) :
    ∀ j : Fin (Nat.card G.edgeSet),
      ¬ (0 < ybar (Fin.castAdd (Nat.card G.edgeSet) j) ∧
          0 < ybar (Fin.natAdd (Nat.card G.edgeSet) j)) := by
  intro j hdouble
  have hybarFace :
      ybar ∈
        face_set
          (nonnegative_matrix_polyhedron
            (splitFinGraphEdgeIncMatrix (G := G))
            (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
          (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
          z := extremePoints_subset hybarExtreme
  rcases splitPairDirection_mem_optimalFace
      (G := G) bHalf cNative z hybarFace j hdouble.1 hdouble.2 with
    ⟨ε, hε_pos, hminusFace, hplusFace, hminus_ne, hplus_ne⟩
  have hybarSeg :
      ybar ∈
        segment ℝ
          (ybar - ε • splitPairDirection (G := G) j)
          (ybar + ε • splitPairDirection (G := G) j) := by
    -- The original point is the midpoint of the two opposite perturbations.
    simpa using mem_segment_sub_add ybar (ε • splitPairDirection (G := G) j)
  have hybarExtremeSeg := (mem_extremePoints_iff_forall_segment).1 hybarExtreme
  rcases hybarExtremeSeg.2
      (ybar - ε • splitPairDirection (G := G) j) hminusFace
      (ybar + ε • splitPairDirection (G := G) j) hplusFace hybarSeg with hEq | hEq
  · exact hminus_ne hEq
  · exact hplus_ne hEq

/-- Helper for Exercise 4.18: the actual edge support of a split vector keeps exactly the edges
whose positive or negative copy is strictly positive. -/
private abbrev actualSupportFamily
    (y : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ) : Set G.edgeSet :=
  {e | 0 < y (Fin.castAdd (Nat.card G.edgeSet) ((Finite.equivFin G.edgeSet) e)) ∨
      0 < y (Fin.natAdd (Nat.card G.edgeSet) ((Finite.equivFin G.edgeSet) e))}

/-- Helper for Exercise 4.18: on the actual support, record whether the positive split copy is
the surviving one. -/
private noncomputable def supportOrientation
    (y : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ) :
    ↥(actualSupportFamily (G := G) y) → Bool :=
  fun e ↦ decide (0 < y (Fin.castAdd (Nat.card G.edgeSet) ((Finite.equivFin G.edgeSet) e.1)))

/-- Helper for Exercise 4.18: on the actual support, the surviving split coordinate is the sum of
the two nonnegative copies. -/
private abbrev supportMagnitude
    (y : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ) :
    ↥(actualSupportFamily (G := G) y) → ℝ :=
  fun e ↦
    y (Fin.castAdd (Nat.card G.edgeSet) ((Finite.equivFin G.edgeSet) e.1)) +
      y (Fin.natAdd (Nat.card G.edgeSet) ((Finite.equivFin G.edgeSet) e.1))

/-- Helper for Exercise 4.18: rebuild a split vector from the actual support, its orientation
choice, and its positive magnitudes. -/
private noncomputable def signedSupportExtension
    (y : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ) :
    Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ :=
  Fin.append
    (fun j ↦
      let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm j
      if h : e ∈ actualSupportFamily (G := G) y then
        if supportOrientation (G := G) y ⟨e, h⟩ then
          supportMagnitude (G := G) y ⟨e, h⟩
        else
          0
      else
        0)
    (fun j ↦
      let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm j
      if h : e ∈ actualSupportFamily (G := G) y then
        if supportOrientation (G := G) y ⟨e, h⟩ then
          0
        else
          supportMagnitude (G := G) y ⟨e, h⟩
      else
        0)

/-- Helper for Exercise 4.18: the projected native edge vector is the signed zero-extension of the
support magnitudes. -/
private noncomputable def signedSupportNativeVector
    (y : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ) :
    G.edgeSet → ℝ :=
  fun e ↦
    if h : e ∈ actualSupportFamily (G := G) y then
      if supportOrientation (G := G) y ⟨e, h⟩ then
        supportMagnitude (G := G) y ⟨e, h⟩
      else
        -supportMagnitude (G := G) y ⟨e, h⟩
    else
      0

/-- Helper for Exercise 4.18: freezing an actual support family `F`, an orientation `σ`, and a
positive magnitude vector `u` produces a split vector on the fixed `Fin (m + m)` owner. -/
private noncomputable def fixedSupportExtension
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    (u : ↥F → ℝ) :
    Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ :=
  Fin.append
    (fun j ↦
      let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm j
      if h : e ∈ F then
        if σ ⟨e, h⟩ then
          u ⟨e, h⟩
        else
          0
      else
        0)
    (fun j ↦
      let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm j
      if h : e ∈ F then
        if σ ⟨e, h⟩ then
          0
        else
          u ⟨e, h⟩
      else
        0)

/-- Helper for Exercise 4.18: the native edge vector attached to fixed support data is the signed
zero-extension of the support magnitudes. -/
private noncomputable def fixedSupportNativeVector
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    (u : ↥F → ℝ) :
    G.edgeSet → ℝ :=
  fun e ↦
    if h : e ∈ F then
      if σ ⟨e, h⟩ then
        u ⟨e, h⟩
      else
        -u ⟨e, h⟩
    else
      0

/-- Helper for Exercise 4.18: on the actual support owner, twist each incidence column by the
chosen sign so that positive support magnitudes encode the signed native edge vector. -/
private noncomputable def signedSupportReducedMatrix
    (F : Set G.edgeSet)
    (σ : ↥F → Bool) :
    Matrix ↥((edgeFamilySubgraph G F).support) ↥F ℤ :=
  fun v e ↦
    if σ e then
      edgeFamilyIncidenceSubmatrix G ℤ F v e
    else
      -edgeFamilyIncidenceSubmatrix G ℤ F v e

/-- Helper for Exercise 4.18: the reduced support objective uses the same sign choice as the
native zero-extension on the support edges. -/
private noncomputable def signedSupportReducedObjective
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    (cNative : G.edgeSet → ℝ) :
    ↥F → ℝ :=
  fun e ↦
    if σ e then
      cNative e.1
    else
      -cNative e.1

/-- Helper for Exercise 4.18: multiplying the signed support matrix by positive support
magnitudes recovers the native incidence product on the support rows. -/
private lemma signedSupportReducedMatrix_mulVec
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    (w : ↥F → ℝ) :
    ((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) *ᵥ w =
      fun v : ↥((edgeFamilySubgraph G F).support) ↦
        ((graphEdgeIncMatrix G ℝ).mulVec (fixedSupportNativeVector (G := G) F σ w)) v.1 := by
  classical
  let _ : Fintype ↥F := Fintype.ofFinite ↥F
  let _ : Fintype ↥((edgeFamilySubgraph G F).support) := Fintype.ofFinite _
  ext v
  -- Rewrite the reduced row sum directly as the native row sum over the signed zero-extension.
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  calc
    ∑ e : ↥F,
        (((if σ e then edgeFamilyIncidenceSubmatrix G ℤ F v e
              else -edgeFamilyIncidenceSubmatrix G ℤ F v e : ℤ) : ℝ) * w e) =
      ∑ e : ↥F, (graphEdgeIncMatrix G ℝ) v.1 e.1 * fixedSupportNativeVector (G := G) F σ w e.1 := by
        refine Finset.sum_congr rfl ?_
        intro e he
        by_cases hσ : σ e
        · -- Positive support columns keep the original incidence column.
          simp [signedSupportReducedMatrix, fixedSupportNativeVector, hσ,
            edgeFamilyIncidenceSubmatrix, graphEdgeIncMatrix]
        · -- Negative support columns contribute the negated incidence column.
          simp [signedSupportReducedMatrix, fixedSupportNativeVector, hσ,
            edgeFamilyIncidenceSubmatrix, graphEdgeIncMatrix]
    _ = ∑ e : G.edgeSet,
          (graphEdgeIncMatrix G ℝ) v.1 e *
            fixedSupportNativeVector (G := G) F σ w e := by
          -- Outside the support family, the native zero-extension contributes zero.
          rw [← Finset.sum_subtype_eq_sum_filter]
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hmem : e ∈ F
          · simp [hmem]
          · simp [fixedSupportNativeVector, hmem]

/-- Helper for Exercise 4.18: the reduced signed objective agrees with the native objective on the
signed zero-extension of the support magnitudes. -/
private lemma signedSupportReducedObjective_dot
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    (cNative : G.edgeSet → ℝ)
    (w : ↥F → ℝ) :
    ∑ e : ↥F, signedSupportReducedObjective (G := G) F σ cNative e * w e =
      ∑ e : G.edgeSet, cNative e * fixedSupportNativeVector (G := G) F σ w e := by
  classical
  let _ : Fintype ↥F := Fintype.ofFinite ↥F
  calc
    ∑ e : ↥F, signedSupportReducedObjective (G := G) F σ cNative e * w e =
      ∑ e : ↥F, cNative e.1 * fixedSupportNativeVector (G := G) F σ w e.1 := by
        refine Finset.sum_congr rfl ?_
        intro e he
        by_cases hσ : σ e
        · -- Positive support coordinates keep their native sign in both presentations.
          simp [signedSupportReducedObjective, fixedSupportNativeVector, hσ]
        · -- Negative support coordinates pick up the same minus sign in both presentations.
          simp [signedSupportReducedObjective, fixedSupportNativeVector, hσ]
    _ = ∑ e : G.edgeSet, cNative e * fixedSupportNativeVector (G := G) F σ w e := by
          -- The native zero-extension vanishes outside the support family, so the full sum reduces
          -- to the support-indexed one.
          rw [← Finset.sum_subtype_eq_sum_filter]
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hmem : e ∈ F
          · simp [hmem]
          · simp [fixedSupportNativeVector, hmem]

/-- Helper for Exercise 4.18: projecting the fixed-owner split extension recovers the
corresponding signed native extension. -/
private lemma splitFinProjection_fixedSupportExtension
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    (u : ↥F → ℝ) :
    splitFinProjection (G := G) (fixedSupportExtension (G := G) F σ u) =
      graphEdgeCoordinates (G := G) (fixedSupportNativeVector (G := G) F σ u) := by
  -- Freeze the support owner first, then compare the two surviving split coordinates edgewise.
  ext j
  let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm j
  by_cases hmem : e ∈ F
  · by_cases hσ : σ ⟨e, hmem⟩
    · simp [splitFinProjection, graphEdgeCoordinates, fixedSupportExtension,
        fixedSupportNativeVector, e, hmem, hσ]
    · simp [splitFinProjection, graphEdgeCoordinates, fixedSupportExtension,
        fixedSupportNativeVector, e, hmem, hσ]
  · simp [splitFinProjection, graphEdgeCoordinates, fixedSupportExtension,
      fixedSupportNativeVector, e, hmem]

/-- Helper for Exercise 4.18: the fixed-owner split extension remembers the reduced support vector
exactly, so later extreme-point arguments can be lifted back to the split owner. -/
private lemma fixedSupportExtension_injective
    (F : Set G.edgeSet)
    (σ : ↥F → Bool) :
    Function.Injective (fixedSupportExtension (G := G) F σ) := by
  -- Read each support coordinate from the unique split copy selected by `σ`.
  intro u w huw
  ext e
  let j : Fin (Nat.card G.edgeSet) := (Finite.equivFin G.edgeSet) e.1
  by_cases hσ : σ e
  · have hcoord := congrFun huw (Fin.castAdd (Nat.card G.edgeSet) j)
    simpa [fixedSupportExtension, j, e.2, hσ] using hcoord
  · have hcoord := congrFun huw (Fin.natAdd (Nat.card G.edgeSet) j)
    simpa [fixedSupportExtension, j, e.2, hσ] using hcoord

/-- Helper for Exercise 4.18: `fixedSupportExtension` is affine-linear in the reduced support
coordinates. -/
private lemma fixedSupportExtension_add_smul
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    (a b : ℝ)
    (u w : ↥F → ℝ) :
    fixedSupportExtension (G := G) F σ (a • u + b • w) =
      a • fixedSupportExtension (G := G) F σ u +
        b • fixedSupportExtension (G := G) F σ w := by
  -- Each split coordinate either keeps the corresponding support coordinate or is forced to `0`.
  ext k
  cases k using Fin.addCases with
  | left j =>
      let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm j
      by_cases hmem : e ∈ F
      · by_cases hσ : σ ⟨e, hmem⟩
        · simp [fixedSupportExtension, e, hmem, hσ, Pi.add_apply, Pi.smul_apply]
        · simp [fixedSupportExtension, e, hmem, hσ, Pi.add_apply, Pi.smul_apply]
      · simp [fixedSupportExtension, e, hmem, Pi.add_apply, Pi.smul_apply]
  | right j =>
      let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm j
      by_cases hmem : e ∈ F
      · by_cases hσ : σ ⟨e, hmem⟩
        · simp [fixedSupportExtension, e, hmem, hσ, Pi.add_apply, Pi.smul_apply]
        · simp [fixedSupportExtension, e, hmem, hσ, Pi.add_apply, Pi.smul_apply]
      · simp [fixedSupportExtension, e, hmem, Pi.add_apply, Pi.smul_apply]

/-- Helper for Exercise 4.18: lifting a reduced-support segment back to the fixed split owner
keeps the same segment relation. -/
private lemma fixedSupportExtension_mem_segment
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    {u w₁ w₂ : ↥F → ℝ}
    (hseg : u ∈ segment ℝ w₁ w₂) :
    fixedSupportExtension (G := G) F σ u ∈
      segment ℝ
        (fixedSupportExtension (G := G) F σ w₁)
        (fixedSupportExtension (G := G) F σ w₂) := by
  rcases mem_segment_iff_div.mp hseg with ⟨a, b, ha, hb, hab, hcomb⟩
  refine mem_segment_iff_div.mpr ⟨a, b, ha, hb, hab, ?_⟩
  -- Transport the convex-combination identity through the affine fixed-support extension.
  calc
    (a / (a + b)) • fixedSupportExtension (G := G) F σ w₁ +
        (b / (a + b)) • fixedSupportExtension (G := G) F σ w₂ =
      fixedSupportExtension (G := G) F σ
        ((a / (a + b)) • w₁ + (b / (a + b)) • w₂) := by
          symm
          exact fixedSupportExtension_add_smul (G := G) F σ
            (a / (a + b)) (b / (a + b)) w₁ w₂
    _ = fixedSupportExtension (G := G) F σ u := by rw [hcomb]

/-- Helper for Exercise 4.18: if a vertex is outside the support of the edge-family subgraph, then
every fixed-support native vector has zero incidence row there. -/
private lemma graphEdgeIncMatrix_mulVec_fixedSupportNativeVector_eq_zero_of_not_support
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    (w : ↥F → ℝ)
    {v : V}
    (hv : v ∉ (edgeFamilySubgraph G F).support) :
    ((graphEdgeIncMatrix G ℝ).mulVec (fixedSupportNativeVector (G := G) F σ w)) v = 0 := by
  classical
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero ?_
  intro e he
  by_cases hmem : e ∈ F
  · have hnotInc : (e : Sym2 V) ∉ G.incidenceSet v := by
      intro hinc
      have hmemv : v ∈ (e : Sym2 V) := (G.edge_mem_incidenceSet_iff (a := v) (e := e)).1 hinc
      rcases Sym2.mem_iff_exists.mp hmemv with ⟨w', hw'⟩
      have hvw' : G.Adj v w' := by
        exact G.mem_edgeSet.mp (hw'.symm ▸ e.2)
      have hsupp : v ∈ (edgeFamilySubgraph G F).support := by
        refine (Subgraph.mem_support _).2 ?_
        refine ⟨w', ?_⟩
        rw [edgeFamilySubgraph]
        change (SimpleGraph.fromEdgeSet (((↑) '' F : Set (Sym2 V)))).Adj v w'
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨⟨e, hmem, hw'.symm⟩, G.ne_of_adj hvw'⟩
      exact hv hsupp
    simp [fixedSupportNativeVector, hmem, graphEdgeIncMatrix, Matrix.submatrix_apply,
      G.incMatrix_of_notMem_incidenceSet (R := ℝ) hnotInc]
  · simp [fixedSupportNativeVector, hmem]

/-- Helper for Exercise 4.18: reduced-support feasibility upgrades to native graph-incidence
feasibility once the off-support rows are frozen by one known feasible support vector. -/
private lemma fixedSupportNativeVector_mem_graphEdgeIncidencePolyhedron
    (b : V → ℚ)
    (bHalf : V → ℤ)
    (hbHalf : ∀ v, b v = (2 * bHalf v : ℚ))
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    {w₀ w : ↥F → ℝ}
    (hw₀Feasible :
      fixedSupportNativeVector (G := G) F σ w₀ ∈ graph_edge_incidence_polyhedron G b)
    (hwFeasible :
      w ∈
        nonnegative_matrix_polyhedron
          (signedSupportReducedMatrix (G := G) F σ)
          (fun v : ↥((edgeFamilySubgraph G F).support) ↦ 2 * bHalf v.1)) :
    fixedSupportNativeVector (G := G) F σ w ∈ graph_edge_incidence_polyhedron G b := by
  classical
  let _ : Fintype ↥F := Fintype.ofFinite ↥F
  let _ : Fintype ↥((edgeFamilySubgraph G F).support) := Fintype.ofFinite _
  rw [graphEdgeIncidencePolyhedron_mem_iff_rowwise]
  intro v
  by_cases hv : v ∈ (edgeFamilySubgraph G F).support
  · let vF : ↥((edgeFamilySubgraph G F).support) := ⟨v, hv⟩
    have hwRows := (mem_nonnegative_matrix_polyhedron_iff.1 hwFeasible).1
    calc
      ((graphEdgeIncMatrix G ℝ).mulVec (fixedSupportNativeVector (G := G) F σ w)) v =
          (((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) *ᵥ w) vF := by
            symm
            simpa using congrFun (signedSupportReducedMatrix_mulVec (G := G) F σ w) vF
      _ ≤ ((2 * bHalf v : ℤ) : ℝ) := hwRows vF
      _ = (b v : ℝ) := by norm_num [hbHalf v]
  · have hw_zero :
        ((graphEdgeIncMatrix G ℝ).mulVec (fixedSupportNativeVector (G := G) F σ w)) v = 0 :=
      graphEdgeIncMatrix_mulVec_fixedSupportNativeVector_eq_zero_of_not_support
        (G := G) F σ w hv
    have hw₀_zero :
        ((graphEdgeIncMatrix G ℝ).mulVec (fixedSupportNativeVector (G := G) F σ w₀)) v = 0 :=
      graphEdgeIncMatrix_mulVec_fixedSupportNativeVector_eq_zero_of_not_support
        (G := G) F σ w₀ hv
    have hw₀_bound :
        ((graphEdgeIncMatrix G ℝ).mulVec (fixedSupportNativeVector (G := G) F σ w₀)) v ≤
          (b v : ℝ) :=
      (graphEdgeIncidencePolyhedron_mem_iff_rowwise (G := G) b).1 hw₀Feasible v
    linarith

/-- Helper for Exercise 4.18: any reduced-support feasible point with the target reduced objective
value lifts back to the fixed split optimal face. -/
private lemma fixedSupportExtension_mem_splitOptimalFace
    (b : V → ℚ)
    (bHalf : V → ℤ)
    (hbHalf : ∀ v, b v = (2 * bHalf v : ℚ))
    (cNative : G.edgeSet → ℝ)
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    {w₀ w : ↥F → ℝ}
    {z : ℝ}
    (hw₀Feasible :
      fixedSupportNativeVector (G := G) F σ w₀ ∈ graph_edge_incidence_polyhedron G b)
    (hwFeasible :
      w ∈
        nonnegative_matrix_polyhedron
          (signedSupportReducedMatrix (G := G) F σ)
          (fun v : ↥((edgeFamilySubgraph G F).support) ↦ 2 * bHalf v.1))
    (hwObjective :
      ∑ e : ↥F, signedSupportReducedObjective (G := G) F σ cNative e * w e = z) :
    fixedSupportExtension (G := G) F σ w ∈
      face_set
        (nonnegative_matrix_polyhedron
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
        (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
        z := by
  classical
  let _ : Fintype ↥F := Fintype.ofFinite ↥F
  let _ : Fintype ↥((edgeFamilySubgraph G F).support) := Fintype.ofFinite _
  have hwNativeFeasible :
      fixedSupportNativeVector (G := G) F σ w ∈ graph_edge_incidence_polyhedron G b :=
    fixedSupportNativeVector_mem_graphEdgeIncidencePolyhedron
      (G := G) b bHalf hbHalf F σ hw₀Feasible hwFeasible
  have hwSplitFeasible :
      fixedSupportExtension (G := G) F σ w ∈
        nonnegative_matrix_polyhedron
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)) := by
    refine ⟨?_, ?_⟩
    · have hwFin :
          graphEdgeCoordinates (G := G) (fixedSupportNativeVector (G := G) F σ w) ∈
            rational_matrix_polyhedron
              (graphFinIncMatrixQ (G := G))
              (fun i ↦ b ((Finite.equivFin V).symm i)) :=
        graphEdgeCoordinates_mem_incidencePresentation (G := G) b hwNativeFeasible
      have hwFinRows :
          (((graphFinIncMatrixQ (G := G)).map (Rat.castHom ℝ)) *ᵥ
              graphEdgeCoordinates (G := G) (fixedSupportNativeVector (G := G) F σ w)) ≤
            fun i ↦ (b ((Finite.equivFin V).symm i) : ℝ) := by
        exact (mem_rational_matrix_polyhedron
          (graphFinIncMatrixQ (G := G))
          (fun i ↦ b ((Finite.equivFin V).symm i))
          (graphEdgeCoordinates (G := G) (fixedSupportNativeVector (G := G) F σ w))).1 hwFin
      intro i
      -- Rewrite the split row operator through the projected native coordinates.
      calc
        ((((splitFinGraphEdgeIncMatrix (G := G)).map (Int.castRingHom ℝ)) *ᵥ
            fixedSupportExtension (G := G) F σ w) i) =
            ((((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
                splitFinProjection (G := G) (fixedSupportExtension (G := G) F σ w)) i) := by
              rw [splitFinGraphEdgeIncMatrix_mulVec]
        _ = ((((graphFinIncMatrixInt (G := G)).map (Int.castRingHom ℝ)) *ᵥ
                graphEdgeCoordinates (G := G) (fixedSupportNativeVector (G := G) F σ w)) i) := by
              rw [splitFinProjection_fixedSupportExtension]
        _ = ((((graphFinIncMatrixQ (G := G)).map (Rat.castHom ℝ)) *ᵥ
                graphEdgeCoordinates (G := G) (fixedSupportNativeVector (G := G) F σ w)) i) := by
              rw [graphFinIncMatrix_intCast]
        _ ≤ (b ((Finite.equivFin V).symm i) : ℝ) := hwFinRows i
        _ = ((2 * bHalf ((Finite.equivFin V).symm i) : ℤ) : ℝ) := by
              norm_num [hbHalf ((Finite.equivFin V).symm i)]
    · intro j
      cases j using Fin.addCases with
      | left i =>
          let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm i
          by_cases hmem : e ∈ F
          · by_cases hσ : σ ⟨e, hmem⟩
            · exact by simpa [fixedSupportExtension, e, hmem, hσ] using
                (mem_nonnegative_matrix_polyhedron_iff.1 hwFeasible).2 ⟨e, hmem⟩
            · simp [fixedSupportExtension, e, hmem, hσ]
          · simp [fixedSupportExtension, e, hmem]
      | right i =>
          let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm i
          by_cases hmem : e ∈ F
          · by_cases hσ : σ ⟨e, hmem⟩
            · simp [fixedSupportExtension, e, hmem, hσ]
            · exact by simpa [fixedSupportExtension, e, hmem, hσ] using
                (mem_nonnegative_matrix_polyhedron_iff.1 hwFeasible).2 ⟨e, hmem⟩
          · simp [fixedSupportExtension, e, hmem]
  rw [mem_face_set_iff]
  refine ⟨hwSplitFeasible, ?_⟩
  -- Rewrite the split objective back to the reduced signed objective.
  calc
    splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ
        fixedSupportExtension (G := G) F σ w =
      graphEdgeCoordinates (G := G) cNative ⬝ᵥ
        splitFinProjection (G := G) (fixedSupportExtension (G := G) F σ w) := by
          rw [splitFinObjective_dot_eq_projection]
    _ = graphEdgeCoordinates (G := G) cNative ⬝ᵥ
          graphEdgeCoordinates (G := G) (fixedSupportNativeVector (G := G) F σ w) := by
            rw [splitFinProjection_fixedSupportExtension]
    _ = ∑ e : G.edgeSet, cNative e * fixedSupportNativeVector (G := G) F σ w e := by
          exact graphEdgeCoordinate_dotProduct_reindex (G := G)
            (graphEdgeCoordinates (G := G) cNative)
            (graphEdgeCoordinates (G := G) (fixedSupportNativeVector (G := G) F σ w))
    _ = ∑ e : ↥F, signedSupportReducedObjective (G := G) F σ cNative e * w e := by
          symm
          exact signedSupportReducedObjective_dot (G := G) F σ cNative w
    _ = z := hwObjective

/-- Helper for Exercise 4.18: once an extreme split maximizer has no double copy, its positive
support canonically packages into an actual edge family, a sign choice, and a positive magnitude
vector that reconstruct both the split point and its native projection. -/
private lemma positiveSupportActualEdgeFamilyData
    (bHalf : V → ℤ)
    {ybar : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ}
    (hybarFeasible :
      ybar ∈
        nonnegative_matrix_polyhedron
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
    (hybarNoDoubleCopy :
      ∀ j : Fin (Nat.card G.edgeSet),
        ¬ (0 < ybar (Fin.castAdd (Nat.card G.edgeSet) j) ∧
            0 < ybar (Fin.natAdd (Nat.card G.edgeSet) j))) :
    (∀ e : ↥(actualSupportFamily (G := G) ybar),
        0 < supportMagnitude (G := G) ybar e) ∧
      signedSupportExtension (G := G) ybar = ybar ∧
      signedSupportNativeVector (G := G) ybar =
        graphEdgeCoordinateReindex (G := G) (splitFinProjection (G := G) ybar) := by
  have hybarNonneg := (mem_nonnegative_matrix_polyhedron_iff.1 hybarFeasible).2
  refine ⟨?_, ?_, ?_⟩
  · intro e
    let j : Fin (Nat.card G.edgeSet) := (Finite.equivFin G.edgeSet) e.1
    have hleft_nonneg : 0 ≤ ybar (Fin.castAdd (Nat.card G.edgeSet) j) :=
      hybarNonneg (Fin.castAdd (Nat.card G.edgeSet) j)
    have hright_nonneg : 0 ≤ ybar (Fin.natAdd (Nat.card G.edgeSet) j) :=
      hybarNonneg (Fin.natAdd (Nat.card G.edgeSet) j)
    rcases e.2 with hleft | hright
    · have hright_not : ¬ 0 < ybar (Fin.natAdd (Nat.card G.edgeSet) j) := by
        intro hright'
        exact hybarNoDoubleCopy j ⟨hleft, hright'⟩
      have hright_zero : ybar (Fin.natAdd (Nat.card G.edgeSet) j) = 0 :=
        le_antisymm (not_lt.mp hright_not) hright_nonneg
      simpa [supportMagnitude, j, hright_zero] using hleft
    · have hleft_not : ¬ 0 < ybar (Fin.castAdd (Nat.card G.edgeSet) j) := by
        intro hleft'
        exact hybarNoDoubleCopy j ⟨hleft', hright⟩
      have hleft_zero : ybar (Fin.castAdd (Nat.card G.edgeSet) j) = 0 :=
        le_antisymm (not_lt.mp hleft_not) hleft_nonneg
      simpa [supportMagnitude, j, hleft_zero, add_comm] using hright
  · ext k
    cases k using Fin.addCases with
    | left j =>
        let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm j
        by_cases hmem : e ∈ actualSupportFamily (G := G) ybar
        · by_cases hleft : 0 < ybar (Fin.castAdd (Nat.card G.edgeSet) j)
          · have hright_not : ¬ 0 < ybar (Fin.natAdd (Nat.card G.edgeSet) j) := by
              intro hright
              exact hybarNoDoubleCopy j ⟨hleft, hright⟩
            have hright_zero : ybar (Fin.natAdd (Nat.card G.edgeSet) j) = 0 :=
              le_antisymm (not_lt.mp hright_not)
                (hybarNonneg (Fin.natAdd (Nat.card G.edgeSet) j))
            have horient :
                supportOrientation (G := G) ybar ⟨e, hmem⟩ = true := by
              simp [supportOrientation, e, hleft]
            have hmag :
                supportMagnitude (G := G) ybar ⟨e, hmem⟩ =
                  ybar (Fin.castAdd (Nat.card G.edgeSet) j) := by
              simp [supportMagnitude, e, hright_zero]
            simp [signedSupportExtension, e, hmem, horient, hmag]
          · have hleft_zero : ybar (Fin.castAdd (Nat.card G.edgeSet) j) = 0 :=
              le_antisymm (not_lt.mp hleft)
                (hybarNonneg (Fin.castAdd (Nat.card G.edgeSet) j))
            have hright_pos : 0 < ybar (Fin.natAdd (Nat.card G.edgeSet) j) := by
              have hmem' : 0 < ybar (Fin.natAdd (Nat.card G.edgeSet) j) := by
                simpa [actualSupportFamily, e, hleft] using hmem
              exact hmem'
            have horient :
                supportOrientation (G := G) ybar ⟨e, hmem⟩ = false := by
              simp [supportOrientation, e, hleft]
            have hmag :
                supportMagnitude (G := G) ybar ⟨e, hmem⟩ =
                  ybar (Fin.natAdd (Nat.card G.edgeSet) j) := by
              simp [supportMagnitude, e, hleft_zero, add_comm]
            have hright_nonneg :
                0 ≤ ybar (Fin.natAdd (Nat.card G.edgeSet) j) :=
              le_of_lt hright_pos
            simp [signedSupportExtension, e, hmem, horient, hmag, hleft_zero, hright_nonneg]
        · have hnot_left : ¬ 0 < ybar (Fin.castAdd (Nat.card G.edgeSet) j) := by
            intro hleft
            exact hmem (by simp [actualSupportFamily, e, hleft])
          have hnot_right : ¬ 0 < ybar (Fin.natAdd (Nat.card G.edgeSet) j) := by
            intro hright
            exact hmem (by simp [actualSupportFamily, e, hright])
          have hleft_zero : ybar (Fin.castAdd (Nat.card G.edgeSet) j) = 0 :=
            le_antisymm (not_lt.mp hnot_left)
              (hybarNonneg (Fin.castAdd (Nat.card G.edgeSet) j))
          simp [signedSupportExtension, e, hmem, hleft_zero]
    | right j =>
        let e : G.edgeSet := (Finite.equivFin G.edgeSet).symm j
        by_cases hmem : e ∈ actualSupportFamily (G := G) ybar
        · by_cases hleft : 0 < ybar (Fin.castAdd (Nat.card G.edgeSet) j)
          · have hright_not : ¬ 0 < ybar (Fin.natAdd (Nat.card G.edgeSet) j) := by
              intro hright
              exact hybarNoDoubleCopy j ⟨hleft, hright⟩
            have hright_zero : ybar (Fin.natAdd (Nat.card G.edgeSet) j) = 0 :=
              le_antisymm (not_lt.mp hright_not)
                (hybarNonneg (Fin.natAdd (Nat.card G.edgeSet) j))
            have horient :
                supportOrientation (G := G) ybar ⟨e, hmem⟩ = true := by
              simp [supportOrientation, e, hleft]
            simp [signedSupportExtension, e, hmem, horient, hright_zero]
          · have hleft_zero : ybar (Fin.castAdd (Nat.card G.edgeSet) j) = 0 :=
              le_antisymm (not_lt.mp hleft)
                (hybarNonneg (Fin.castAdd (Nat.card G.edgeSet) j))
            have hright_nonneg :
                0 ≤ ybar (Fin.natAdd (Nat.card G.edgeSet) j) :=
              hybarNonneg (Fin.natAdd (Nat.card G.edgeSet) j)
            have horient :
                supportOrientation (G := G) ybar ⟨e, hmem⟩ = false := by
              simp [supportOrientation, e, hleft]
            have hmag :
                supportMagnitude (G := G) ybar ⟨e, hmem⟩ =
                  ybar (Fin.natAdd (Nat.card G.edgeSet) j) := by
              simp [supportMagnitude, e, hleft_zero, add_comm]
            simp [signedSupportExtension, e, hmem, horient, hmag, hright_nonneg]
        · have hnot_right : ¬ 0 < ybar (Fin.natAdd (Nat.card G.edgeSet) j) := by
            intro hright
            exact hmem (by simp [actualSupportFamily, e, hright])
          have hright_zero : ybar (Fin.natAdd (Nat.card G.edgeSet) j) = 0 :=
            le_antisymm (not_lt.mp hnot_right)
              (hybarNonneg (Fin.natAdd (Nat.card G.edgeSet) j))
          simp [signedSupportExtension, e, hmem, hright_zero]
  · have hproj :
        splitFinProjection (G := G) ybar =
          graphEdgeCoordinates (G := G) (signedSupportNativeVector (G := G) ybar) := by
      calc
        splitFinProjection (G := G) ybar =
            splitFinProjection (G := G) (signedSupportExtension (G := G) ybar) := by
              rw [‹signedSupportExtension (G := G) ybar = ybar›]
        _ =
            graphEdgeCoordinates (G := G)
              (fixedSupportNativeVector (G := G)
                (actualSupportFamily (G := G) ybar)
                (supportOrientation (G := G) ybar)
                (supportMagnitude (G := G) ybar)) := by
              exact splitFinProjection_fixedSupportExtension
                (G := G)
                (actualSupportFamily (G := G) ybar)
                (supportOrientation (G := G) ybar)
                (supportMagnitude (G := G) ybar)
    have hproj' := congrArg (graphEdgeCoordinateReindex (G := G)) hproj
    simpa using hproj'.symm

/-- Helper for Exercise 4.18: an extreme point of a finite polyhedron admits `|β|` active rows
whose coefficient vectors are linearly independent. -/
private lemma existsActiveRowsOfExtremePolyhedronPoint
    {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℝ)
    (b : α → ℝ)
    {xbar : β → ℝ}
    (hxbar : xbar ∈ polyhedron_le_set A b)
    (hxbar_vertex : xbar ∈ (polyhedron_le_set A b).extremePoints ℝ) :
    ∃ I : β ↪ α,
      (∀ i : β, (A *ᵥ xbar) (I i) = b (I i)) ∧
        LinearIndependent ℝ (fun i : β ↦ A (I i)) := by
  -- Reindex the finite row and column owners to `Fin` and invoke the existing Chapter 3
  -- extreme-point characterization for polyhedra.
  let AFin : Matrix (Fin (Fintype.card α)) (Fin (Fintype.card β)) ℝ :=
    Matrix.reindex (Fintype.equivFin α) (Fintype.equivFin β) A
  let bFin : Fin (Fintype.card α) → ℝ := fun i ↦ b ((Fintype.equivFin α).symm i)
  let xFin : Fin (Fintype.card β) → ℝ := fun j ↦ xbar ((Fintype.equivFin β).symm j)
  have hxFin :
      xFin ∈ polyhedron_le_set AFin bFin := by
    intro i
    simpa [AFin, bFin, xFin, Matrix.mulVec, dotProduct] using
      hxbar ((Fintype.equivFin α).symm i)
  have hxFinExtreme :
      xFin ∈ (polyhedron_le_set AFin bFin).extremePoints ℝ := by
    classical
    let eβ : (Fin (Fintype.card β) → ℝ) ≃ (β → ℝ) := Fintype.arrowCongr (Fintype.equivFin β)
    have hImage :
        polyhedron_le_set AFin bFin = eβ.symm '' polyhedron_le_set A b := by
      ext y
      constructor
      · intro hy
        refine ⟨fun j ↦ y ((Fintype.equivFin β) j), ?_, ?_⟩
        · intro i
          simpa [AFin, bFin, Matrix.mulVec, dotProduct] using hy ((Fintype.equivFin α) i)
        · funext j
          simp [eβ]
      · rintro ⟨y, hy, rfl⟩
        intro i
        simpa [AFin, bFin, Matrix.mulVec, dotProduct] using hy ((Fintype.equivFin α).symm i)
    have hxImage :
        eβ.symm xbar ∈ (eβ.symm '' polyhedron_le_set A b).extremePoints ℝ := by
      rw [← image_extremePoints (𝕜 := ℝ) (f := eβ.symm) (s := polyhedron_le_set A b)]
      exact ⟨xbar, hxbar_vertex, by simp [eβ]⟩
    simpa [hImage, xFin, eβ] using hxImage
  obtain ⟨IFin, hactiveFin, hlinearFin⟩ :=
    mem_extremePoints_iff_exists_active_linearlyIndependent_rows AFin bFin hxFin |>.1 hxFinExtreme
  refine ⟨
    ⟨fun j ↦ (Fintype.equivFin α).symm (IFin ((Fintype.equivFin β) j)), ?_⟩,
    ?_,
    ?_⟩
  · intro i j hij
    apply (Fintype.equivFin α).injective
    simpa using hij
  · intro j
    simpa [AFin, bFin, xFin, Matrix.mulVec, dotProduct] using
      hactiveFin ((Fintype.equivFin β) j)
  · have hcomp :
        LinearIndependent ℝ
          (fun j : β ↦
            A ((Fintype.equivFin α).symm (IFin ((Fintype.equivFin β) j)))) := by
      simpa [AFin, Matrix.reindex_apply] using
        hlinearFin.comp (Fintype.equivFin β) (Fintype.equivFin β).injective
    simpa using hcomp

/-- Helper for Exercise 4.18: a positive reduced extreme point forces a square system of active
graph rows on the actual support owner. -/
private lemma supportActiveGraphRows_squareSystem
    (bHalf : V → ℤ)
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    {u : ↥F → ℝ}
    (huFeasible :
      u ∈
        nonnegative_matrix_polyhedron
          (signedSupportReducedMatrix (G := G) F σ)
          (fun v : ↥((edgeFamilySubgraph G F).support) ↦ 2 * bHalf v.1))
    (huExtreme :
      u ∈
        (nonnegative_matrix_polyhedron
          (signedSupportReducedMatrix (G := G) F σ)
          (fun v : ↥((edgeFamilySubgraph G F).support) ↦ 2 * bHalf v.1)).extremePoints ℝ)
    (huPos : ∀ e : ↥F, 0 < u e) :
    ∃ ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support),
      (∀ i : ↥F,
        (((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) *ᵥ u) (ρ i) =
          (2 * bHalf (ρ i).1 : ℝ)) ∧
        LinearIndependent ℝ
          (fun i : ↥F ↦
            ((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i)) := by
  classical
  let Ared : Matrix ↥((edgeFamilySubgraph G F).support) ↥F ℤ :=
    signedSupportReducedMatrix (G := G) F σ
  let M : Matrix (Sum ↥((edgeFamilySubgraph G F).support) ↥F) ↥F ℝ :=
    fun r e ↦
      match r with
      | Sum.inl v => (Ared v e : ℝ)
      | Sum.inr e' => if e' = e then (-1 : ℝ) else 0
  let rhs : Sum ↥((edgeFamilySubgraph G F).support) ↥F → ℝ :=
    Sum.elim (fun v ↦ (2 * bHalf v.1 : ℝ)) (fun _ ↦ 0)
  have hPred_eq :
      nonnegative_matrix_polyhedron Ared
          (fun v : ↥((edgeFamilySubgraph G F).support) ↦ 2 * bHalf v.1) =
        polyhedron_le_set M rhs := by
    ext w
    constructor
    · rintro ⟨hwRows, hwNonneg⟩
      intro r
      cases r with
      | inl v =>
          simpa [M, rhs, Ared] using hwRows v
      | inr e =>
          have hnonneg : 0 ≤ w e := hwNonneg e
          simpa [M, rhs, Matrix.mulVec, dotProduct] using (neg_nonpos.mpr hnonneg)
    · intro hw
      refine ⟨?_, ?_⟩
      · intro v
        simpa [M, rhs, Ared] using hw (Sum.inl v)
      · intro e
        have hrow := hw (Sum.inr e)
        simpa [M, rhs, Matrix.mulVec, dotProduct] using hrow
  have huPoly : u ∈ polyhedron_le_set M rhs := by
    simpa [hPred_eq] using huFeasible
  have huPolyExtreme : u ∈ (polyhedron_le_set M rhs).extremePoints ℝ := by
    simpa [hPred_eq] using huExtreme
  obtain ⟨I, hactive, hlinear⟩ :=
    existsActiveRowsOfExtremePolyhedronPoint M rhs huPoly huPolyExtreme
  have hI_left : ∀ e : ↥F, ∃ v : ↥((edgeFamilySubgraph G F).support), I e = Sum.inl v := by
    intro e
    cases hIE : I e with
    | inl v =>
        exact ⟨v, hIE⟩
    | inr e' =>
        have hactiveEq : (M *ᵥ u) (Sum.inr e') = rhs (Sum.inr e') := by
          simpa [hIE] using hactive e
        have hu_zero : u e' = 0 := by
          simpa [M, rhs, Matrix.mulVec, dotProduct] using hactiveEq
        exact False.elim <| (ne_of_gt (huPos e')) hu_zero
  let ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support) :=
    ⟨fun e ↦ Classical.choose (hI_left e), by
      intro e₁ e₂ hρ
      apply I.injective
      calc
        I e₁ = Sum.inl (Classical.choose (hI_left e₁)) := Classical.choose_spec (hI_left e₁)
        _ = Sum.inl (Classical.choose (hI_left e₂)) := by simpa [hρ]
        _ = I e₂ := (Classical.choose_spec (hI_left e₂)).symm⟩
  refine ⟨ρ, ?_, ?_⟩
  · intro i
    have hactiveEq : (M *ᵥ u) (I i) = rhs (I i) := hactive i
    simpa [M, rhs, Ared, ρ, Classical.choose_spec (hI_left i)] using hactiveEq
  · -- Once positivity removes the lower `-I` rows, the selected active rows are genuine graph rows.
    simpa [M, Ared, ρ, Classical.choose_spec ∘ hI_left] using hlinear

/-- Helper for Exercise 4.18: the active reduced square system forces the supported edge family to
belong to the Exercise 4.17 class. -/
private lemma supportColumnsLinearIndependent
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (hrows :
      LinearIndependent ℝ
        (fun i : ↥F ↦
          ((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i))) :
    incidence_independent_edge_family G F := by
  classical
  let BZ : Matrix ↥F ↥F ℤ :=
    (signedSupportReducedMatrix (G := G) F σ).submatrix ρ id
  let BQ : Matrix ↥F ↥F ℚ :=
    (edgeFamilyIncidenceSubmatrix G ℚ F).submatrix ρ id
  have hrowsBZ :
      LinearIndependent ℝ (fun i : ↥F ↦ ((BZ.map (Int.castRingHom ℝ)) i)) := by
    simpa [BZ, Matrix.submatrix_apply] using hrows
  have hdet_real_ne : (BZ.map (Int.castRingHom ℝ)).det ≠ 0 := by
    intro hdet_zero
    exact hdet_zero <|
      Matrix.det_eq_zero_of_not_linearIndependent_rows
        (A := BZ.map (Int.castRingHom ℝ)) (by simpa using hrowsBZ)
  have hdet_int_ne : BZ.det ≠ 0 := by
    intro hdet_zero
    apply hdet_real_ne
    rw [show (BZ.map (Int.castRingHom ℝ)).det = (BZ.det : ℝ) by
      simpa using (RingHom.map_det (Int.castRingHom ℝ) BZ).symm]
    exact_mod_cast hdet_zero
  have hdet_rat_ne : (BZ.map (Int.castRingHom ℚ)).det ≠ 0 := by
    intro hdet_zero
    apply hdet_int_ne
    rw [show (BZ.map (Int.castRingHom ℚ)).det = (BZ.det : ℚ) by
      simpa using (RingHom.map_det (Int.castRingHom ℚ) BZ).symm] at hdet_zero
    exact_mod_cast hdet_zero
  have hsigned_cols :
      LinearIndependent ℚ ((BZ.map (Int.castRingHom ℚ)).col) := by
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet_rat_ne
  have hsign_eq :
      ((BZ.map (Int.castRingHom ℚ)).col) =
        fun e : ↥F ↦
          (if σ e then (1 : ℚˣ) else (-1 : ℚˣ)) • BQ.col e := by
    funext e
    ext v
    by_cases hσ : σ e
    · simp [BZ, BQ, Matrix.col, Matrix.submatrix_apply, signedSupportReducedMatrix, hσ]
    · simp [BZ, BQ, Matrix.col, Matrix.submatrix_apply, signedSupportReducedMatrix, hσ]
  have hBQ_cols : LinearIndependent ℚ BQ.col := by
    rw [hsign_eq] at hsigned_cols
    exact
      (LinearIndependent.units_smul_iff (v := BQ.col)
        (w := fun e : ↥F ↦ if σ e then (1 : ℚˣ) else (-1 : ℚˣ))).1 hsigned_cols
  have hBQ_rank : Fintype.card ↥F = BQ.rank := by
    exact (linearIndependent_cols_iff_card_eq_rank BQ).1 hBQ_cols
  have hA_rank_ge : Fintype.card ↥F ≤ (edgeFamilyIncidenceSubmatrix G ℚ F).rank := by
    rw [← hBQ_rank]
    simpa [BQ] using Matrix.rank_submatrix_le (edgeFamilyIncidenceSubmatrix G ℚ F) ρ id
  have hA_cols :
      LinearIndependent ℚ ((edgeFamilyIncidenceSubmatrix G ℚ F).col) := by
    exact
      (linearIndependent_cols_iff_card_eq_rank (edgeFamilyIncidenceSubmatrix G ℚ F)).2
        (le_antisymm hA_rank_ge (Matrix.rank_le_card_width _))
  exact (incMatrix_columns_linearIndependent_iff_edge_family (G := G) F).1 hA_cols

/-- Helper for Exercise 4.18: if a support row vertex is outside the connected component carrying
an edge of `F`, then the corresponding edge-family incidence entry is zero. -/
private lemma edgeFamilyIncidenceSubmatrix_eq_zero_of_not_mem_edgeComponent
    {F : Set G.edgeSet}
    (v : ↥((edgeFamilySubgraph G F).support))
    (e : ↥F)
    (hv :
      v.1 ∉
        ((edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.1.out.1).supp) :
    edgeFamilyIncidenceSubmatrix G ℤ F v e = 0 := by
  classical
  let H : SimpleGraph V := (edgeFamilySubgraph G F).spanningCoe
  -- A nonzero incidence entry would force the row vertex to be one of the two endpoints of `e`,
  -- hence inside the connected component generated by that edge.
  by_contra hne
  have hvEdge :
      v.1 ∈ ((e : G.edgeSet) : Sym2 V) := by
    have hne' :
        ((G.edgeIncMatrix ℤ).submatrix
            (Subtype.val : ↥((edgeFamilySubgraph G F).support) ↪ V) id) v e.1 ≠ 0 := by
      simpa [edgeFamilyIncidenceSubmatrix, SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply] using
        hne
    exact
      edge_incidence_submatrix_mem_edge_of_nonzero
        (G := G)
        (row := (Subtype.val : ↥((edgeFamilySubgraph G F).support) ↪ V))
        (i := v) (e := e.1) hne'
  have hvEnds : v.1 = e.1.out.1 ∨ v.1 = e.1.out.2 := by
    simpa [e.1.out_eq] using (Sym2.mem_iff.mp hvEdge)
  have hEdgeH : H.Adj e.1.out.1 e.1.out.2 := by
    have heH : ((e : G.edgeSet) : Sym2 V) ∈ H.edgeSet := by
      simpa [H, edgeFamilySubgraph_edgeEquiv_apply_coe] using
        ((edgeFamilySubgraph_edgeEquiv G F e).2)
    exact H.mem_edgeSet.mp (by simpa [e.1.out_eq] using heH)
  let C : H.ConnectedComponent := H.connectedComponentMk e.1.out.1
  have hstart : e.1.out.1 ∈ C.supp := by
    exact (ConnectedComponent.mem_supp_iff C e.1.out.1).2 (by simp [C])
  have hvComp : v.1 ∈ C.supp := by
    rcases hvEnds with rfl | rfl
    · exact hstart
    · exact (C.mem_supp_congr_adj hEdgeH).2 hstart
  exact hv hvComp

/-- Helper for Exercise 4.18: the signed reduced support matrix is block-diagonal across connected
components of `edgeFamilySubgraph G F`. -/
private lemma signedSupportReducedMatrix_eq_zero_of_not_mem_edgeComponent
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (v : ↥((edgeFamilySubgraph G F).support))
    (e : ↥F)
    (hv :
      v.1 ∉
        ((edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.1.out.1).supp) :
    signedSupportReducedMatrix (G := G) F σ v e = 0 := by
  -- The sign twist only changes the value by `±1`, so a cross-component zero stays zero.
  have hzero :
      edgeFamilyIncidenceSubmatrix G ℤ F v e = 0 :=
    edgeFamilyIncidenceSubmatrix_eq_zero_of_not_mem_edgeComponent (G := G) v e hv
  by_cases hσ : σ e
  · simp [signedSupportReducedMatrix, hσ, hzero]
  · simp [signedSupportReducedMatrix, hσ, hzero]

/-- Helper for Exercise 4.18: inside a connected component of the supported edge family, the
active square system cannot involve more support edges than active rows. -/
private lemma supportComponentEdgeCard_le_activeRows
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (hρlinear :
      LinearIndependent ℝ
        (fun i : ↥F ↦
          ((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i)))
    (hcrossZero :
        ∀ i e : ↥F,
          (ρ i).1 ∉
              ((edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1).supp →
            signedSupportReducedMatrix (G := G) F σ (ρ i) e = 0)
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent) :
    Nat.card {e : ↥F |
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ≤
      Nat.card {i : ↥F |
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} := by
  classical
  let K : SimpleGraph V := (edgeFamilySubgraph G F).spanningCoe
  let BZ : Matrix ↥F ↥F ℤ := (signedSupportReducedMatrix (G := G) F σ).submatrix ρ id
  let BQ : Matrix ↥F ↥F ℚ := BZ.map (Int.castRingHom ℚ)
  let rowComponent : ↥F → K.ConnectedComponent := fun i ↦ K.connectedComponentMk (ρ i).1
  let edgeComponent : ↥F → K.ConnectedComponent := fun e ↦ K.connectedComponentMk e.1.out.1
  let rowSet : Set ↥F := {i | rowComponent i = c}
  let _ : Fintype ↥F := Fintype.ofFinite ↥F
  let _ : Fintype K.ConnectedComponent := Fintype.ofFinite K.ConnectedComponent
  have hrowsBZ :
      LinearIndependent ℝ (fun i : ↥F ↦ ((BZ.map (Int.castRingHom ℝ)) i)) := by
    -- Reindex the selected active rows once so the square support matrix has an honest row family.
    simpa [BZ, Matrix.submatrix_apply] using hρlinear
  have hdet_real_ne : (BZ.map (Int.castRingHom ℝ)).det ≠ 0 := by
    -- A square matrix with linearly independent rows has nonzero determinant.
    intro hdet_zero
    exact hdet_zero <|
      Matrix.det_eq_zero_of_not_linearIndependent_rows
        (A := BZ.map (Int.castRingHom ℝ)) (by simpa using hrowsBZ)
  have hdet_int_ne : BZ.det ≠ 0 := by
    -- Transport the nonzero determinant statement back from `ℝ` to `ℤ`.
    intro hdet_zero
    apply hdet_real_ne
    rw [show (BZ.map (Int.castRingHom ℝ)).det = (BZ.det : ℝ) by
      simpa using (RingHom.map_det (Int.castRingHom ℝ) BZ).symm]
    exact_mod_cast hdet_zero
  have hdet_rat_ne : BQ.det ≠ 0 := by
    -- The same determinant remains nonzero after coercing to `ℚ`.
    intro hdet_zero
    apply hdet_int_ne
    rw [show BQ.det = (BZ.det : ℚ) by
      simpa [BQ] using (RingHom.map_det (Int.castRingHom ℚ) BZ).symm] at hdet_zero
    exact_mod_cast hdet_zero
  have hBQ_cols : LinearIndependent ℚ BQ.col := by
    -- The square active matrix therefore has linearly independent columns as well.
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet_rat_ne
  have hcomponentColMem :
      ∀ e : {e : ↥F // edgeComponent e = c}, BQ.col e.1 ∈ Pi.spanSubset ℚ rowSet := by
    intro e
    rw [Pi.mem_spanSubset_iff]
    intro i hi
    have hi' :
        (ρ i).1 ∉ (K.connectedComponentMk e.1.1.out.1).supp := by
      intro hmem
      have hcomp :
          K.connectedComponentMk (ρ i).1 = K.connectedComponentMk e.1.1.out.1 := by
        exact (ConnectedComponent.mem_supp_iff (K.connectedComponentMk e.1.1.out.1) (ρ i).1).1 hmem
      exact hi <| by
        dsimp [rowSet, rowComponent]
        simpa [edgeComponent] using hcomp.trans e.2
    -- Cross-component vanishing forces the whole column to live in the coordinate subspace
    -- supported on the active rows from the same connected component.
    have hzero := hcrossZero i e.1 hi'
    have hzeroQ : (BZ i e.1 : ℚ) = 0 := by
      exact_mod_cast hzero
    simpa [BQ, BZ, Matrix.col] using hzeroQ
  let componentCols :
      {e : ↥F // edgeComponent e = c} → Pi.spanSubset ℚ rowSet :=
    fun e ↦ ⟨BQ.col e.1, hcomponentColMem e⟩
  have hcomponentCols_linear : LinearIndependent ℚ componentCols := by
    -- Passing to the supported-coordinate subspace does not destroy linear independence.
    apply LinearIndependent.of_comp (Pi.spanSubset ℚ rowSet).subtype
    simpa [componentCols] using
      hBQ_cols.comp (fun e : {e : ↥F // edgeComponent e = c} ↦ e.1) Subtype.val_injective
  have hdim :
      Module.finrank ℚ (Pi.spanSubset ℚ rowSet) =
        Fintype.card {i : ↥F // rowComponent i = c} := by
    -- The support subspace has one coordinate basis vector for each active row in the component.
    simpa [rowSet, rowComponent] using
      (Pi.dim_spanSubset (R := ℚ) (ι := ↥F) (s := rowSet))
  -- The linearly independent component columns fit inside that coordinate subspace, so their
  -- cardinality is at most the number of active component rows.
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [← hdim]
  exact hcomponentCols_linear.fintype_card_le_finrank

/-- Helper for Exercise 4.18: each connected component receives exactly as many active rows from
`ρ` as support edges. -/
private lemma supportComponentActiveRows_card_eq_edges
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (hρlinear :
      LinearIndependent ℝ
        (fun i : ↥F ↦
          ((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i)))
    (hcrossZero :
        ∀ i e : ↥F,
          (ρ i).1 ∉
              ((edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1).supp →
            signedSupportReducedMatrix (G := G) F σ (ρ i) e = 0)
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent) :
    Nat.card {i : ↥F |
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} =
      Nat.card {e : ↥F |
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} := by
  classical
  let K : SimpleGraph V := (edgeFamilySubgraph G F).spanningCoe
  let rowComponent : ↥F → K.ConnectedComponent := fun i ↦ K.connectedComponentMk (ρ i).1
  let edgeComponent : ↥F → K.ConnectedComponent := fun e ↦ K.connectedComponentMk e.1.out.1
  let rowFiber : K.ConnectedComponent → Type _ := fun c' ↦ {i : ↥F // rowComponent i = c'}
  let edgeFiber : K.ConnectedComponent → Type _ := fun c' ↦ {e : ↥F // edgeComponent e = c'}
  let _ : Fintype ↥F := Fintype.ofFinite ↥F
  let _ : Fintype K.ConnectedComponent := Fintype.ofFinite K.ConnectedComponent
  have hle :
      ∀ c' : K.ConnectedComponent, Fintype.card (edgeFiber c') ≤ Fintype.card (rowFiber c') := by
    intro c'
    simpa [rowFiber, edgeFiber, rowComponent, edgeComponent] using
      supportComponentEdgeCard_le_activeRows
        (G := G) σ ρ hρlinear hcrossZero c'
  have hrowSum :
      Fintype.card ↥F = ∑ c' : K.ConnectedComponent, Fintype.card (rowFiber c') := by
    -- The active rows partition according to the connected component containing the selected row
    -- vertex `ρ i`.
    calc
      Fintype.card ↥F = Fintype.card (Σ c' : K.ConnectedComponent, rowFiber c') := by
        simpa [rowFiber] using Fintype.card_congr (Equiv.sigmaFiberEquiv rowComponent)
      _ = ∑ c' : K.ConnectedComponent, Fintype.card (rowFiber c') := Fintype.card_sigma _
  have hedgeSum :
      Fintype.card ↥F = ∑ c' : K.ConnectedComponent, Fintype.card (edgeFiber c') := by
    -- The support edges partition in the same way by their connected component.
    calc
      Fintype.card ↥F = Fintype.card (Σ c' : K.ConnectedComponent, edgeFiber c') := by
        simpa [edgeFiber] using Fintype.card_congr (Equiv.sigmaFiberEquiv edgeComponent)
      _ = ∑ c' : K.ConnectedComponent, Fintype.card (edgeFiber c') := Fintype.card_sigma _
  have hcardEq : Fintype.card (edgeFiber c) = Fintype.card (rowFiber c) := by
    by_contra hne
    have hlt : Fintype.card (edgeFiber c) < Fintype.card (rowFiber c) :=
      lt_of_le_of_ne (hle c) hne
    have hsumLt :
        ∑ c' : K.ConnectedComponent, Fintype.card (edgeFiber c') <
          ∑ c' : K.ConnectedComponent, Fintype.card (rowFiber c') := by
      exact Finset.sum_lt_sum (fun c' _ ↦ hle c') ⟨c, Finset.mem_univ c, hlt⟩
    -- Since the row and edge fibers both partition the same finite type `↥F`, strict inequality
    -- on one component would force a strict inequality on the total cardinalities.
    have : ∑ c' : K.ConnectedComponent, Fintype.card (edgeFiber c') <
        ∑ c' : K.ConnectedComponent, Fintype.card (edgeFiber c') := by
      calc
        ∑ c' : K.ConnectedComponent, Fintype.card (edgeFiber c') <
            ∑ c' : K.ConnectedComponent, Fintype.card (rowFiber c') := hsumLt
        _ = Fintype.card ↥F := hrowSum.symm
        _ = ∑ c' : K.ConnectedComponent, Fintype.card (edgeFiber c') := hedgeSum
    exact (lt_irrefl _ this)
  -- The componentwise inequality upgrades to equality because the row and edge fibers exhaust the
  -- same total cardinality `Nat.card ↥F`.
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hcardEq.symm

/-- Helper for Exercise 4.18: the active rows whose chosen support vertex lies in one connected
component embed into that component support. -/
private lemma supportComponentRowEmbedding
    {F : Set G.edgeSet}
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent) :
    {i : ↥F |
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↪ c.supp := by
  classical
  refine
    { toFun := fun i ↦ ⟨(ρ i.1).1, ?_⟩
      inj' := ?_ }
  · -- The defining fiber equation is exactly the support-membership criterion for `c`.
    exact (ConnectedComponent.mem_supp_iff c (ρ i.1).1).2 (by simpa using i.2)
  · intro i j hij
    -- Injectivity comes from the original row embedding `ρ`.
    apply Subtype.ext
    exact ρ.injective (Subtype.ext (Subtype.ext_iff.mp hij))

/-- Helper for Exercise 4.18: the support edges carried by one connected component are
canonically equivalent to the edge set of that component graph. -/
private noncomputable def supportComponentEdgeEquiv
    {F : Set G.edgeSet}
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent) :
    {e : ↥F |
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ≃
      c.toSimpleGraph.edgeSet := by
  classical
  let K : SimpleGraph V := (edgeFamilySubgraph G F).spanningCoe
  let τ : ↥F ≃ K.edgeSet := edgeFamilySubgraph_edgeEquiv G F
  let fiberEquiv :
      {e : ↥F // K.connectedComponentMk e.1.out.1 = c} ≃
        {e : K.edgeSet // K.connectedComponentMk e.1.out.1 = c} := by
    refine
      { toFun := fun e ↦ ⟨τ e.1, ?_⟩
        invFun := fun e ↦ ⟨τ.symm e.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · -- Transport the component equation across the canonical `↥F ≃ K.edgeSet` owner change.
      simpa [τ, edgeFamilySubgraph_edgeEquiv_apply_coe] using e.2
    · -- The inverse transport uses the same underlying-edge identity in reverse.
      simpa [τ, edgeFamilySubgraph_edgeEquiv_apply_coe] using e.2
    · intro e
      apply Subtype.ext
      exact τ.left_inv e.1
    · intro e
      apply Subtype.ext
      exact τ.right_inv e.1
  let edgeFiberEquiv :
      {e : K.edgeSet // K.connectedComponentMk e.1.out.1 = c} ≃ c.toSimpleGraph.edgeSet := by
    refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_ }
    · intro e
      let e₀ : K.edgeSet := e.1
      let v : V := e₀.1.out.1
      let w : V := e₀.1.out.2
      have hvw : K.Adj v w := by
        exact K.mem_edgeSet.mp (by simpa [v, w, e₀.1.out_eq] using e₀.2)
      have hv : v ∈ c.supp := by
        exact (ConnectedComponent.mem_supp_iff c v).2 (by simpa [v] using e.2)
      have hw : w ∈ c.supp := c.mem_supp_of_adj_mem_supp hv hvw
      exact ⟨s(⟨v, hv⟩, ⟨w, hw⟩), (c.toSimpleGraph_adj hv hw).2 hvw⟩
    · intro e
      let v : c.supp := e.1.out.1
      let w : c.supp := e.1.out.2
      have hvw : c.toSimpleGraph.Adj v w := by
        exact c.toSimpleGraph.mem_edgeSet.mp (by simpa [v, w, e.1.out_eq] using e.2)
      let q : Sym2 V := s(v.1, w.1)
      refine ⟨⟨q, (c.toSimpleGraph_adj v.2 w.2).1 hvw⟩, ?_⟩
      have hout_mem : q.out.1 ∈ q := by
        simpa using Sym2.out_fst_mem q
      have h_endpoint : q.out.1 = v.1 ∨ q.out.1 = w.1 := by
        simpa [q] using (Sym2.mem_iff.mp hout_mem)
      have hq : q.out.1 ∈ c.supp := by
        rcases h_endpoint with hqv | hqw
        · simpa [hqv] using v.2
        · simpa [hqw] using w.2
      exact (ConnectedComponent.mem_supp_iff c q.out.1).1 hq
    · intro e
      apply Subtype.ext
      apply Subtype.ext
      simpa using e.1.1.out_eq
    · intro e
      ext x
      rw [← e.1.out_eq]
      simp only [Sym2.mem_iff, or_comm]
  -- Compose the fiber transport with the canonical connected-component edge equivalence.
  exact fiberEquiv.trans edgeFiberEquiv

/-- Helper for Exercise 4.18: in a non-tree component, the active row embedding is automatically
an equivalence onto the full component support because the row-count bridge matches the full
vertex count. -/
private noncomputable lemma supportComponentRowEquiv_of_nonTree
    {F : Set G.edgeSet}
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent)
    (hrowCount :
      Nat.card {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} =
        Nat.card {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c})
    (hcard : Nat.card c.toSimpleGraph.edgeSet = Nat.card ↥c.supp) :
    {i : ↥F |
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ≃
      c.supp := by
  classical
  let rowEmb := supportComponentRowEmbedding (G := G) (ρ := ρ) c
  let edgeEquiv := supportComponentEdgeEquiv (G := G) c
  let _ :
      Fintype {i : ↥F //
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} :=
    Fintype.ofFinite _
  let _ : Fintype c.supp := Fintype.ofFinite _
  have hcardRows :
      Fintype.card {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} =
        Fintype.card c.supp := by
    -- First convert the active-row count to the component-edge count, then identify those edges
    -- with the canonical edge set of `c.toSimpleGraph`.
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    calc
      Nat.card {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} =
        Nat.card {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} :=
        hrowCount
      _ = Nat.card c.toSimpleGraph.edgeSet := Nat.card_congr edgeEquiv
      _ = Nat.card ↥c.supp := hcard
  have hrowEmb_bijective : Function.Bijective rowEmb := by
    -- Finite injective maps between equal-cardinality types are automatically surjective.
    exact (Fintype.bijective_iff_injective_and_card rowEmb).2 ⟨rowEmb.injective, hcardRows⟩
  -- Replace the active-row embedding by the corresponding equivalence so later determinant
  -- transport can work on the exact `c.supp` owner.
  exact rowEmb.equivOfSurjective hrowEmb_bijective.surjective

/-- Helper for Exercise 4.18: restricting the active square system to one connected component
keeps exactly the active equations on that component. -/
private lemma supportComponentSignedSystem
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    {u : ↥F → ℝ}
    {bHalf : V → ℤ}
    (hρactive :
      ∀ i : ↥F,
        (((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) *ᵥ u) (ρ i) =
          (2 * bHalf (ρ i).1 : ℝ))
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent) :
    ((((signedSupportReducedMatrix (G := G) F σ).submatrix
        (fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦ ρ i.1)
        (fun e : {e : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦ e.1)).map
        (Int.castRingHom ℝ)) *ᵥ
        (fun e : {e : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦ u e.1) =
      fun i : {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
        (2 * bHalf (ρ i.1).1 : ℝ) := by
  classical
  let K : SimpleGraph V := (edgeFamilySubgraph G F).spanningCoe
  let _ : Fintype {e : ↥F // K.connectedComponentMk e.1.out.1 = c} := Fintype.ofFinite _
  ext i
  have hrestrict :
      ∑ e : ↥F,
        (((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i.1) e) * u e =
          ∑ e : {e : ↥F // K.connectedComponentMk e.1.out.1 = c},
            (((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i.1) e.1) *
              u e.1 := by
    -- Cross-component columns vanish on a row coming from the fixed component `c`.
    rw [← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_congr rfl ?_
    intro e he
    by_cases hec : K.connectedComponentMk e.1.out.1 = c
    · simp [hec]
    · have hnotmem :
          (ρ i.1).1 ∉ (K.connectedComponentMk e.1.out.1).supp := by
        intro hmem
        have hcomp :
            K.connectedComponentMk (ρ i.1).1 = K.connectedComponentMk e.1.out.1 :=
          (ConnectedComponent.mem_supp_iff (K.connectedComponentMk e.1.out.1) (ρ i.1).1).1 hmem
        exact hec (hcomp.symm.trans i.2)
      have hzero :
          signedSupportReducedMatrix (G := G) F σ (ρ i.1) e = 0 :=
        signedSupportReducedMatrix_eq_zero_of_not_mem_edgeComponent (G := G) σ (ρ i.1) e hnotmem
      simp [hec, hzero]
  -- Rewrite the component block row as the full active row, then use the active equation.
  calc
    ((((signedSupportReducedMatrix (G := G) F σ).submatrix
        (fun i : {i : ↥F | K.connectedComponentMk (ρ i).1 = c} ↦ ρ i.1)
        (fun e : {e : ↥F | K.connectedComponentMk e.1.out.1 = c} ↦ e.1)).map
        (Int.castRingHom ℝ)) *ᵥ
        (fun e : {e : ↥F | K.connectedComponentMk e.1.out.1 = c} ↦ u e.1)) i =
      ∑ e : {e : ↥F // K.connectedComponentMk e.1.out.1 = c},
        (((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i.1) e.1) *
          u e.1 := by
            simp [Matrix.mulVec, dotProduct]
    _ = ∑ e : ↥F,
          (((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i.1) e) * u e :=
        hrestrict.symm
    _ = (2 * bHalf (ρ i.1).1 : ℝ) := by
          simpa [Matrix.mulVec, dotProduct] using hρactive i.1

/-- Helper for Exercise 4.18: row linear independence persists after restricting to one connected
component fiber. -/
private lemma supportComponentSignedRows_linearIndependent
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (hρlinear :
      LinearIndependent ℝ
        (fun i : ↥F ↦
          ((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i)))
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent) :
    LinearIndependent ℝ
      (fun i : {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
        ((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i.1)) := by
  -- Restricting the index type along the subtype embedding does not change linear independence.
  exact hρlinear.comp (fun i ↦ i.1) Subtype.val_injective

/-- Helper for Exercise 4.18: the proved row-count bridge gives an explicit equivalence between
the active rows and support edges inside one connected component. -/
private noncomputable lemma supportComponentRowEdgeEquiv
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (hρlinear :
      LinearIndependent ℝ
        (fun i : ↥F ↦
          ((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i)))
    (hcrossZero :
        ∀ i e : ↥F,
          (ρ i).1 ∉
              ((edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1).supp →
            signedSupportReducedMatrix (G := G) F σ (ρ i) e = 0)
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent) :
    {i : ↥F |
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ≃
      {e : ↥F |
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} := by
  classical
  let _ :
      Fintype {i : ↥F //
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} :=
    Fintype.ofFinite _
  let _ :
      Fintype {e : ↥F //
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} :=
    Fintype.ofFinite _
  -- Convert the already-proved `Nat.card` equality into a concrete equivalence of finite fibers.
  refine Fintype.equivOfCardEq ?_
  simpa [Nat.card_eq_fintype_card] using
    supportComponentActiveRows_card_eq_edges (G := G) σ ρ hρlinear hcrossZero c

/-- Helper for Exercise 4.18: after reindexing the component columns by a square equivalence, the
component active equations become a square system on the row fiber itself. -/
private lemma supportComponentSquareSystem
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    {u : ↥F → ℝ}
    {bHalf : V → ℤ}
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent)
    (hsystem :
      ((((signedSupportReducedMatrix (G := G) F σ).submatrix
          (fun i : {i : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
            ρ i.1)
          (fun e : {e : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
            e.1)).map
          (Int.castRingHom ℝ)) *ᵥ
          (fun e : {e : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
            u e.1)) =
        fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          (2 * bHalf (ρ i.1).1 : ℝ))
    (τ :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ≃
        {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c}) :
    ((((((signedSupportReducedMatrix (G := G) F σ).submatrix
        (fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          ρ i.1)
        (fun e : {e : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
          e.1)).submatrix id τ).map
        (Int.castRingHom ℝ)) *ᵥ
        (fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          u (τ i).1)) =
      fun i : {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
        (2 * bHalf (ρ i.1).1 : ℝ) := by
  classical
  ext i
  have hsum :
      ∑ j : {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c},
        ((((((signedSupportReducedMatrix (G := G) F σ).submatrix
            (fun i : {i : ↥F |
                (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
              ρ i.1)
            (fun e : {e : ↥F |
                (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
              e.1)).submatrix id τ).map
            (Int.castRingHom ℝ)) i j) *
          u (τ j).1 =
        ∑ e : {e : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c},
          ((((signedSupportReducedMatrix (G := G) F σ).submatrix
              (fun i : {i : ↥F |
                  (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
                ρ i.1)
              (fun e : {e : ↥F |
                  (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
                e.1)).map
              (Int.castRingHom ℝ)) i e) *
            u e.1 := by
    -- Reindex the component column sum along the chosen square equivalence.
    simpa [Matrix.submatrix_apply] using
      (τ.sum_comp
        (fun e : {e : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
          ((((signedSupportReducedMatrix (G := G) F σ).submatrix
              (fun i : {i : ↥F |
                  (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
                ρ i.1)
              (fun e : {e : ↥F |
                  (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
                e.1)).map
              (Int.castRingHom ℝ)) i e) *
            u e.1)).symm
  -- Expand the square system entrywise and change variables in the component column sum.
  calc
    ((((((signedSupportReducedMatrix (G := G) F σ).submatrix
        (fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          ρ i.1)
        (fun e : {e : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
          e.1)).submatrix id τ).map
        (Int.castRingHom ℝ)) *ᵥ
        (fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          u (τ i).1)) i =
      ∑ j : {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c},
        ((((((signedSupportReducedMatrix (G := G) F σ).submatrix
            (fun i : {i : ↥F |
                (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
              ρ i.1)
            (fun e : {e : ↥F |
                (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
              e.1)).submatrix id τ).map
            (Int.castRingHom ℝ)) i j) *
          u (τ j).1 := by
            simp [Matrix.mulVec, dotProduct]
    _ =
        ∑ e : {e : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c},
          ((((signedSupportReducedMatrix (G := G) F σ).submatrix
              (fun i : {i : ↥F |
                  (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
                ρ i.1)
              (fun e : {e : ↥F |
                  (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
                e.1)).map
              (Int.castRingHom ℝ)) i e) *
            u e.1 := hsum
    _ = (2 * bHalf (ρ i.1).1 : ℝ) := by
          simpa [Matrix.mulVec, dotProduct] using congrFun hsystem i

/-- Helper for Exercise 4.18: the exact square block used for one connected component is obtained
by restricting to the active component rows and then reindexing the component columns by the
chosen row-edge equivalence. -/
private abbrev supportComponentSquareBlock
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent)
    (τ :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ≃
        {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c}) :
    Matrix
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c}
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c}
      ℤ :=
  (((signedSupportReducedMatrix (G := G) F σ).submatrix
      (fun i : {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
        ρ i.1)
      (fun e : {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
        e.1)).submatrix id τ)

/-- Helper for Exercise 4.18: after forgetting the support signs, the active square block on one
connected component is exactly the corresponding incidence block of `c.toSimpleGraph`. -/
private lemma supportComponentIncidenceSquareBlock_eq_componentIncMatrix
    {F : Set G.edgeSet}
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent)
    (τ :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ≃
        {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c}) :
    ((((edgeFamilyIncidenceSubmatrix G ℤ F).submatrix
        (fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          ρ i.1)
        (fun e : {e : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
          e.1)).submatrix id τ) =
      ((c.toSimpleGraph.edgeIncMatrix ℤ).submatrix
        (supportComponentRowEmbedding (G := G) (ρ := ρ) c)
        ((τ.trans (supportComponentEdgeEquiv (G := G) c)).toEmbedding)) := by
  ext i j
  by_cases hinc :
      (((τ j).1 : G.edgeSet) : Sym2 V) ∈ G.incidenceSet (ρ i.1).1
  · simp [edgeFamilyIncidenceSubmatrix, Matrix.submatrix_apply, supportComponentRowEmbedding,
      supportComponentEdgeEquiv, SimpleGraph.edgeIncMatrix, SimpleGraph.incMatrix_apply', hinc]
  · simp [edgeFamilyIncidenceSubmatrix, Matrix.submatrix_apply, supportComponentRowEmbedding,
      supportComponentEdgeEquiv, SimpleGraph.edgeIncMatrix, SimpleGraph.incMatrix_apply', hinc]

/-- Helper for Exercise 4.18: moving the support signs from the active square block into the
unknown vector converts the system to the unsigned component incidence block. -/
private lemma supportComponentUnsignedSquareSystem
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    {u : ↥F → ℝ}
    {bHalf : V → ℤ}
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent)
    (τ :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ≃
        {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c})
    (hsystem :
      ((((((signedSupportReducedMatrix (G := G) F σ).submatrix
          (fun i : {i : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
            ρ i.1)
          (fun e : {e : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
            e.1)).submatrix id τ).map
          (Int.castRingHom ℝ)) *ᵥ
          (fun i : {i : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
            u ((τ i).1))) =
        fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          (2 * bHalf (ρ i.1).1 : ℝ)) :
    ((((((edgeFamilyIncidenceSubmatrix G ℤ F).submatrix
        (fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          ρ i.1)
        (fun e : {e : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
          e.1)).submatrix id τ).map
        (Int.castRingHom ℝ)) *ᵥ
        (fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          if σ ((τ i).1) then u ((τ i).1) else -u ((τ i).1))) =
      fun i : {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
        (2 * bHalf (ρ i.1).1 : ℝ) := by
  ext i
  simpa [Matrix.mulVec, dotProduct, signedSupportReducedMatrix]
    using congrFun hsystem i

/-- Helper for Exercise 4.18: the exact square block on one connected component has nonzero
determinant as soon as the selected active component rows are linearly independent. -/
private lemma supportComponentSquareDet_ne_zero
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent)
    (hlinear :
      LinearIndependent ℝ
        (fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          ((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i.1)))
    (τ :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ≃
        {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c}) :
    (supportComponentSquareBlock (G := G) σ ρ c τ).det ≠ 0 := by
  classical
  let _ :
      Fintype {i : ↥F //
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} :=
    Fintype.ofFinite _
  let Bc := supportComponentSquareBlock (G := G) σ ρ c τ
  have hrows :
      LinearIndependent ℝ (fun i ↦ ((Bc.map (Int.castRingHom ℝ)) i)) := by
    let e :
        ({e : ↥F //
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} → ℝ) ≃ₗ[ℝ]
          ({i : ↥F //
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} → ℝ) :=
      LinearEquiv.funCongrLeft ℝ ℝ τ
    have hmap : LinearIndependent ℝ (fun i ↦ e (((signedSupportReducedMatrix (G := G) F σ).map
        (Int.castRingHom ℝ)) (ρ i.1))) :=
      hlinear.map' e.toLinearMap e.ker
    -- Reindexing the columns by the component equivalence is a linear equivalence on row vectors,
    -- so row independence survives unchanged on the exact square block.
    simpa [Bc, supportComponentSquareBlock, e, Matrix.submatrix_apply,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply] using hmap
  have hdet_real_unit : IsUnit ((Bc.map (Int.castRingHom ℝ)).det) := by
    rw [Matrix.linearIndependent_rows_iff_isUnit]
    simpa using hrows
  have hdet_real_ne : (Bc.map (Int.castRingHom ℝ)).det ≠ 0 := hdet_real_unit.ne_zero
  intro hdet_zero
  apply hdet_real_ne
  rw [show (Bc.map (Int.castRingHom ℝ)).det = (Bc.det : ℝ) by
    simpa using (RingHom.map_det (Int.castRingHom ℝ) Bc).symm]
  exact_mod_cast hdet_zero

/-- Helper for Exercise 4.18: casting an integral solution vector to `ℝ` commutes with left
multiplication by an integral matrix. -/
private lemma intCast_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℤ}
    (z : ι → ℤ) :
    ((B.map (Int.castRingHom ℝ)) *ᵥ fun i ↦ (z i : ℝ)) =
      fun i ↦ ((B *ᵥ z) i : ℝ) := by
  -- Expand `mulVec` entrywise so each summand is just the cast of the corresponding integer term.
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- Helper for Exercise 4.18: a square real system coming from an integral matrix with nonzero
determinant has at most one solution. -/
private lemma eq_of_mulVec_eq_of_det_ne_zero_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℤ}
    {u v : ι → ℝ}
    (hdet_ne_zero : B.det ≠ 0)
    (huv : (B.map (Int.castRingHom ℝ)) *ᵥ u = (B.map (Int.castRingHom ℝ)) *ᵥ v) :
    u = v := by
  by_contra huv_ne
  have hsub_ne : u - v ≠ 0 := sub_ne_zero.mpr huv_ne
  have hsub_zero : (B.map (Int.castRingHom ℝ)) *ᵥ (u - v) = 0 := by
    ext i
    simpa [Matrix.mulVec_sub] using sub_eq_zero.mpr (congrFun huv i)
  have hdet_real :
      (B.map (Int.castRingHom ℝ)).det ≠ 0 := by
    rw [show (B.map (Int.castRingHom ℝ)).det = (B.det : ℝ) by
      simpa using (RingHom.map_det (Int.castRingHom ℝ) B).symm]
    exact_mod_cast hdet_ne_zero
  exact hdet_real ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨u - v, hsub_ne, hsub_zero⟩)

/-- Helper for Exercise 4.18: a square integral system with determinant `±1` and integral
right-hand side has an integral real solution. -/
private lemma squareSystem_integerSolution_of_det_one_or_neg_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℤ}
    {s : ι → ℝ}
    {rhs : ι → ℤ}
    (hsystem : (B.map (Int.castRingHom ℝ)) *ᵥ s = fun i ↦ (rhs i : ℝ))
    (hdet : B.det = 1 ∨ B.det = -1) :
    ∃ z : ι → ℤ, s = fun i ↦ (z i : ℝ) := by
  have hdet_ne_zero : B.det ≠ 0 := by
    rcases hdet with hdet | hdet <;> simpa [hdet]
  rcases hdet with hdet | hdet
  · let z : ι → ℤ := B.cramer rhs
    have hcandidate :
        ((B.map (Int.castRingHom ℝ)) *ᵥ fun i ↦ (z i : ℝ)) =
          fun i ↦ (rhs i : ℝ) := by
      -- Cramer's rule solves the casted system because `det B = 1`.
      calc
        ((B.map (Int.castRingHom ℝ)) *ᵥ fun i ↦ (z i : ℝ)) =
            fun i ↦ ((B *ᵥ z) i : ℝ) := intCast_mulVec z
        _ = fun i ↦ (((B.det • rhs) i : ℤ) : ℝ) := by
              ext i
              simp [z, Matrix.mulVec_cramer]
        _ = fun i ↦ (rhs i : ℝ) := by
              ext i
              simp [hdet]
    refine ⟨z, ?_⟩
    exact eq_of_mulVec_eq_of_det_ne_zero_local hdet_ne_zero (hsystem.trans hcandidate.symm)
  · let z : ι → ℤ := fun i ↦ -(B.cramer rhs i)
    have hcandidate :
        ((B.map (Int.castRingHom ℝ)) *ᵥ fun i ↦ (z i : ℝ)) =
          fun i ↦ (rhs i : ℝ) := by
      -- When `det B = -1`, the negated Cramer vector solves the casted system.
      calc
        ((B.map (Int.castRingHom ℝ)) *ᵥ fun i ↦ (z i : ℝ)) =
            fun i ↦ ((B *ᵥ z) i : ℝ) := intCast_mulVec z
        _ = fun i ↦ (rhs i : ℝ) := by
              ext i
              have hAt := congrFun (Matrix.mulVec_cramer B rhs) i
              simp [z, Matrix.mulVec_neg, hAt, hdet]
    refine ⟨z, ?_⟩
    exact eq_of_mulVec_eq_of_det_ne_zero_local hdet_ne_zero (hsystem.trans hcandidate.symm)

/-- Helper for Exercise 4.18: a square integral system with determinant `±2` and even
right-hand side has an integral real solution. -/
private lemma squareSystem_integerSolution_of_det_two_or_neg_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℤ}
    {s : ι → ℝ}
    {rhsHalf : ι → ℤ}
    (hsystem : (B.map (Int.castRingHom ℝ)) *ᵥ s = fun i ↦ ((2 * rhsHalf i : ℤ) : ℝ))
    (hdet : B.det = 2 ∨ B.det = -2) :
    ∃ z : ι → ℤ, s = fun i ↦ (z i : ℝ) := by
  have hdet_ne_zero : B.det ≠ 0 := by
    rcases hdet with hdet | hdet <;> simpa [hdet]
  rcases hdet with hdet | hdet
  · let z : ι → ℤ := B.cramer rhsHalf
    have hcandidate :
        ((B.map (Int.castRingHom ℝ)) *ᵥ fun i ↦ (z i : ℝ)) =
          fun i ↦ ((2 * rhsHalf i : ℤ) : ℝ) := by
      -- Cramer's rule now multiplies the half right-hand side by `det B = 2`.
      calc
        ((B.map (Int.castRingHom ℝ)) *ᵥ fun i ↦ (z i : ℝ)) =
            fun i ↦ ((B *ᵥ z) i : ℝ) := intCast_mulVec z
        _ = fun i ↦ (((B.det • rhsHalf) i : ℤ) : ℝ) := by
              ext i
              simp [z, Matrix.mulVec_cramer]
        _ = fun i ↦ ((2 * rhsHalf i : ℤ) : ℝ) := by
              ext i
              simp [hdet, two_mul]
    refine ⟨z, ?_⟩
    exact eq_of_mulVec_eq_of_det_ne_zero_local hdet_ne_zero (hsystem.trans hcandidate.symm)
  · let z : ι → ℤ := fun i ↦ -(B.cramer rhsHalf i)
    have hcandidate :
        ((B.map (Int.castRingHom ℝ)) *ᵥ fun i ↦ (z i : ℝ)) =
          fun i ↦ ((2 * rhsHalf i : ℤ) : ℝ) := by
      -- The negative determinant branch is handled by negating the Cramer vector once.
      calc
        ((B.map (Int.castRingHom ℝ)) *ᵥ fun i ↦ (z i : ℝ)) =
            fun i ↦ ((B *ᵥ z) i : ℝ) := intCast_mulVec z
        _ = fun i ↦ ((2 * rhsHalf i : ℤ) : ℝ) := by
              ext i
              have hAt := congrFun (Matrix.mulVec_cramer B rhsHalf) i
              simp [z, Matrix.mulVec_neg, hAt, hdet, two_mul]
    refine ⟨z, ?_⟩
    exact eq_of_mulVec_eq_of_det_ne_zero_local hdet_ne_zero (hsystem.trans hcandidate.symm)

/-- Helper for Exercise 4.18: a tree component of the supported edge family contributes integral
signed coordinates on its support block. -/
private lemma supportComponentTreeSignedCoordinates_integer
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    {u : ↥F → ℝ}
    {bHalf : V → ℤ}
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent)
    (τ :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ≃
        {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c})
    (hcTree : c.toSimpleGraph.IsTree)
    (hsquare :
      (((supportComponentSquareBlock (G := G) σ ρ c τ).map (Int.castRingHom ℝ)) *ᵥ
          (fun i : {i : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
            u ((τ i).1))) =
        fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          (2 * bHalf (ρ i.1).1 : ℝ))
    (hdet_block : (supportComponentSquareBlock (G := G) σ ρ c τ).det ≠ 0) :
    ∃ zc :
      {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} → ℤ,
      ∀ e,
        (if σ e.1 then u e.1 else -u e.1) = (zc e : ℝ) := by
  classical
  let _ :
      Fintype {i : ↥F //
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} :=
    Fintype.ofFinite _
  let _ :
      Fintype {e : ↥F //
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} :=
    Fintype.ofFinite _
  let rowEmb := supportComponentRowEmbedding (G := G) (ρ := ρ) c
  let edgeEquiv := supportComponentEdgeEquiv (G := G) c
  let B :
      Matrix
        {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c}
        {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c}
        ℤ :=
    (((edgeFamilyIncidenceSubmatrix G ℤ F).submatrix
        (fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          ρ i.1)
        (fun e : {e : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
          e.1)).submatrix id τ)
  let s :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} → ℝ :=
    fun i ↦ if σ ((τ i).1) then u ((τ i).1) else -u ((τ i).1)
  let rhsEven :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} → ℤ :=
    fun i ↦ 2 * bHalf (ρ i.1).1
  have hB_component :
      B =
        ((c.toSimpleGraph.edgeIncMatrix ℤ).submatrix
          rowEmb
          ((τ.trans edgeEquiv).toEmbedding)) := by
    -- The unsigned active block is the exact component incidence matrix after reindexing once.
    simpa [B, rowEmb, edgeEquiv] using
      supportComponentIncidenceSquareBlock_eq_componentIncMatrix
        (G := G) (ρ := ρ) c τ
  have hsystemB :
      ((B.map (Int.castRingHom ℝ)) *ᵥ s) =
        fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          (rhsEven i : ℝ) := by
    -- Push the support signs from the matrix into the unknown vector once and freeze that form.
    simpa [B, s, rhsEven, supportComponentSquareBlock] using
      supportComponentUnsignedSquareSystem
        (G := G) (σ := σ) (ρ := ρ) (u := u) (bHalf := bHalf) c τ hsquare
  have hB_ne_zero : B.det ≠ 0 := by
    let D :
        Matrix
          {i : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c}
          {i : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c}
          ℤ :=
      Matrix.diagonal fun i ↦ if σ ((τ i).1) then 1 else -1
    have hSigned :
        supportComponentSquareBlock (G := G) σ ρ c τ = B * D := by
      -- The signed block differs from the unsigned block only by a diagonal sign twist.
      ext i j
      by_cases hσ : σ ((τ j).1)
      · simp [supportComponentSquareBlock, B, D, signedSupportReducedMatrix, hσ]
      · simp [supportComponentSquareBlock, B, D, signedSupportReducedMatrix, hσ]
    intro hzero
    apply hdet_block
    rw [hSigned, Matrix.det_mul, hzero, zero_mul]
  have hTU0 : (c.toSimpleGraph.edgeIncMatrix ℤ).IsTotallyUnimodular :=
    (edge_incidence_matrix_isTotallyUnimodular_iff_isBipartite
      (G := c.toSimpleGraph)).2 hcTree.isBipartite
  have hTU : B.IsTotallyUnimodular := by
    -- Restrict total unimodularity to the exact active tree block.
    rw [hB_component]
    simpa [rowEmb, edgeEquiv] using
      hTU0.submatrix rowEmb ((τ.trans edgeEquiv).toEmbedding)
  have hdet_mem : B.det ∈ Set.range SignType.cast := by
    -- Every square subdeterminant of a totally unimodular matrix is in `{0, ±1}`.
    simpa [B] using ((Matrix.isTotallyUnimodular_iff B).1 hTU) _ id id
  have hdet_tree : B.det = 1 ∨ B.det = -1 := by
    rcases hdet_mem with ⟨δ, hδ⟩
    cases δ <;> simp at hδ
    · exact False.elim (hB_ne_zero hδ)
    · exact Or.inl hδ
    · exact Or.inr hδ
  rcases squareSystem_integerSolution_of_det_one_or_neg_one hsystemB hdet_tree with
    ⟨zInt, hzInt⟩
  refine ⟨fun e ↦ zInt (τ.symm e), ?_⟩
  intro e
  -- Reindex the integral solution back from the row owner to the component edge owner.
  simpa [s] using congrFun hzInt (τ.symm e)

/-- Helper for Exercise 4.18: an odd-unicyclic component of the supported edge family contributes
integral signed coordinates on its support block. -/
private lemma supportComponentOddUnicyclicSignedCoordinates_integer
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    {u : ↥F → ℝ}
    {bHalf : V → ℤ}
    (ρ : ↥F ↪ ↥((edgeFamilySubgraph G F).support))
    (c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent)
    (τ :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ≃
        {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c})
    (hcConn : c.toSimpleGraph.Connected)
    (hrowCount :
      Nat.card {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} =
        Nat.card {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c})
    (hcard : Nat.card c.toSimpleGraph.edgeSet = Nat.card ↥c.supp)
    (hcNotBip : ¬ c.toSimpleGraph.IsBipartite)
    (hsquare :
      (((supportComponentSquareBlock (G := G) σ ρ c τ).map (Int.castRingHom ℝ)) *ᵥ
          (fun i : {i : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
            u ((τ i).1))) =
        fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          (2 * bHalf (ρ i.1).1 : ℝ)) :
    ∃ zc :
      {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} → ℤ,
      ∀ e,
        (if σ e.1 then u e.1 else -u e.1) = (zc e : ℝ) := by
  classical
  let _ :
      Fintype {i : ↥F //
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} :=
    Fintype.ofFinite _
  let _ :
      Fintype {e : ↥F //
        (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} :=
    Fintype.ofFinite _
  let rowEmb := supportComponentRowEmbedding (G := G) (ρ := ρ) c
  let edgeEquiv := supportComponentEdgeEquiv (G := G) c
  let B :
      Matrix
        {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c}
        {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c}
        ℤ :=
    (((edgeFamilyIncidenceSubmatrix G ℤ F).submatrix
        (fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          ρ i.1)
        (fun e : {e : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} ↦
          e.1)).submatrix id τ)
  let s :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} → ℝ :=
    fun i ↦ if σ ((τ i).1) then u ((τ i).1) else -u ((τ i).1)
  let rhsEven :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} → ℤ :=
    fun i ↦ 2 * bHalf (ρ i.1).1
  have hB_component :
      B =
        ((c.toSimpleGraph.edgeIncMatrix ℤ).submatrix
          rowEmb
          ((τ.trans edgeEquiv).toEmbedding)) := by
    -- The unsigned active block is the exact component incidence matrix after reindexing once.
    simpa [B, rowEmb, edgeEquiv] using
      supportComponentIncidenceSquareBlock_eq_componentIncMatrix
        (G := G) (ρ := ρ) c τ
  have hsystemB :
      ((B.map (Int.castRingHom ℝ)) *ᵥ s) =
        fun i : {i : ↥F |
            (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
          (rhsEven i : ℝ) := by
    -- Push the support signs from the matrix into the unknown vector once and freeze that form.
    simpa [B, s, rhsEven, supportComponentSquareBlock] using
      supportComponentUnsignedSquareSystem
        (G := G) (σ := σ) (ρ := ρ) (u := u) (bHalf := bHalf) c τ hsquare
  let _ : Fintype c.supp := Fintype.ofFinite _
  have hcardRows :
      Fintype.card {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} =
        Fintype.card c.supp := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    calc
      Nat.card {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} =
        Nat.card {e : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} :=
        hrowCount
      _ = Nat.card c.toSimpleGraph.edgeSet := Nat.card_congr edgeEquiv
      _ = Nat.card ↥c.supp := hcard
  have hrowEmb_bijective : Function.Bijective rowEmb := by
    exact (Fintype.bijective_iff_injective_and_card rowEmb).2 ⟨rowEmb.injective, hcardRows⟩
  let rowEquiv :
      {i : ↥F |
          (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ≃ c.supp :=
    rowEmb.equivOfSurjective hrowEmb_bijective.surjective
  let σcomp : c.supp ≃ c.toSimpleGraph.edgeSet :=
    rowEquiv.symm.trans (τ.trans edgeEquiv)
  have hmatrix :
      (B.submatrix rowEquiv.symm rowEquiv.symm) =
        ((c.toSimpleGraph.edgeIncMatrix ℤ).submatrix id σcomp) := by
    rw [hB_component]
    ext i j
    simp [σcomp, rowEquiv, Matrix.submatrix_apply]
  have hdet_transport :
      B.det = ((c.toSimpleGraph.edgeIncMatrix ℤ).submatrix id σcomp).det := by
    have hdet := Matrix.det_submatrix_equiv_self rowEquiv.symm B
    rw [hmatrix] at hdet
    exact hdet.symm
  have hdet_odd : B.det = 2 ∨ B.det = -2 := by
    rcases connected_nonbipartite_unicyclic_det_eq_two_or_neg_two
        (H := c.toSimpleGraph) hcConn hcard hcNotBip σcomp with hdet | hdet
    · left
      simpa using hdet_transport.symm.trans hdet
    · right
      simpa using hdet_transport.symm.trans hdet
  rcases squareSystem_integerSolution_of_det_two_or_neg_two hsystemB hdet_odd with
    ⟨zInt, hzInt⟩
  refine ⟨fun e ↦ zInt (τ.symm e), ?_⟩
  intro e
  -- Reindex the integral solution back from the row owner to the component edge owner.
  simpa [s] using congrFun hzInt (τ.symm e)

/-- Helper for Exercise 4.18: an integer witness for the signed support coordinates on `F`
zero-extends to an integer witness on all graph edges. -/
private lemma fixedSupportNativeVector_mem_range_of_signedCoordinates
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (u : ↥F → ℝ)
    (hz :
      ∃ zF : ↥F → ℤ,
        ∀ e : ↥F, (if σ e then u e else -u e) = (zF e : ℝ)) :
    fixedSupportNativeVector (G := G) F σ u ∈
      Set.range (fun z : G.edgeSet → ℤ ↦ fun e ↦ (z e : ℝ)) := by
  rcases hz with ⟨zF, hzF⟩
  refine ⟨fun e ↦ if h : e ∈ F then zF ⟨e, h⟩ else 0, ?_⟩
  ext e
  by_cases h : e ∈ F
  · -- On the support, the native vector is exactly the signed support coordinate.
    simpa [fixedSupportNativeVector, h] using hzF ⟨e, h⟩
  · -- Outside the support, both the native vector and the integer witness vanish.
    simp [fixedSupportNativeVector, h]

/-- Helper for Exercise 4.18: componentwise integer witnesses for the signed support coordinates
assemble into one global integer native edge vector. -/
private lemma fixedSupportNativeVector_mem_range_of_componentwiseSignedCoordinates
    {F : Set G.edgeSet}
    (σ : ↥F → Bool)
    (u : ↥F → ℝ)
    (hw :
      ∀ c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent,
        ∃ zc :
          {e : ↥F //
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} → ℤ,
          ∀ e,
            (if σ e.1 then u e.1 else -u e.1) = (zc e : ℝ)) :
    fixedSupportNativeVector (G := G) F σ u ∈
      Set.range (fun z : G.edgeSet → ℤ ↦ fun e ↦ (z e : ℝ)) := by
  let K : SimpleGraph V := (edgeFamilySubgraph G F).spanningCoe
  have hz :
      ∃ zF : ↥F → ℤ,
        ∀ e : ↥F, (if σ e then u e else -u e) = (zF e : ℝ) := by
    refine ⟨fun e ↦ Classical.choose (hw (K.connectedComponentMk e.1.out.1)) ⟨e, rfl⟩, ?_⟩
    intro e
    -- Choose the integer witness from the unique connected component containing `e`.
    exact Classical.choose_spec (hw (K.connectedComponentMk e.1.out.1)) ⟨e, rfl⟩
  -- The previous zero-extension lemma packages the assembled support witness into `G.edgeSet`.
  exact fixedSupportNativeVector_mem_range_of_signedCoordinates (G := G) σ u hz

/-- Helper for Exercise 4.18: once the actual support data of the split maximizer is fixed, the
reduced-support component argument produces an integral native maximizer. -/
private lemma nonemptySupport_nativeIntegralMaximizer
    (b : V → ℚ)
    (bHalf : V → ℤ)
    (hbHalf : ∀ v, b v = (2 * bHalf v : ℚ))
    (cNative : G.edgeSet → ℝ)
    (z : ℝ)
    (hzNative :
      IsGreatest
        ((fun x : G.edgeSet → ℝ ↦ ∑ e : G.edgeSet, cNative e * x e) ''
          graph_edge_incidence_polyhedron G b)
        z)
    (F : Set G.edgeSet)
    (σ : ↥F → Bool)
    (u : ↥F → ℝ)
    {ybar : Fin (Nat.card G.edgeSet + Nat.card G.edgeSet) → ℝ}
    (hybarExtreme :
      ybar ∈
        (face_set
          (nonnegative_matrix_polyhedron
            (splitFinGraphEdgeIncMatrix (G := G))
            (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
          (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
          z).extremePoints ℝ)
    (huPos : ∀ e : ↥F, 0 < u e)
    (hybarFixed : fixedSupportExtension (G := G) F σ u = ybar)
    (hxFixed :
      fixedSupportNativeVector (G := G) F σ u =
        signedSupportNativeVector (G := G) ybar)
    (hxSupportFeasible :
      signedSupportNativeVector (G := G) ybar ∈ graph_edge_incidence_polyhedron G b)
    (hxSupportObjective :
      (∑ e : G.edgeSet, cNative e * signedSupportNativeVector (G := G) ybar e) = z) :
    ∃ x ∈
        graph_edge_incidence_polyhedron G b ∩
          Set.range (fun z : G.edgeSet → ℤ ↦ fun e ↦ (z e : ℝ)),
      (∑ e : G.edgeSet, cNative e * x e) = z := by
  classical
  let _ : Fintype ↥F := Fintype.ofFinite ↥F
  let _ : Fintype ↥((edgeFamilySubgraph G F).support) := Fintype.ofFinite _
  let x := fixedSupportNativeVector (G := G) F σ u
  have hxFeasible : x ∈ graph_edge_incidence_polyhedron G b := by
    simpa [x, hxFixed] using hxSupportFeasible
  have hxObjective : (∑ e : G.edgeSet, cNative e * x e) = z := by
    simpa [x, hxFixed] using hxSupportObjective
  have huObjective :
      ∑ e : ↥F, signedSupportReducedObjective (G := G) F σ cNative e * u e = z := by
    calc
      ∑ e : ↥F, signedSupportReducedObjective (G := G) F σ cNative e * u e =
          ∑ e : G.edgeSet, cNative e * x e := by
            simpa [x] using signedSupportReducedObjective_dot (G := G) F σ cNative u
      _ = z := hxObjective
  have huFeasible :
      u ∈
        nonnegative_matrix_polyhedron
          (signedSupportReducedMatrix (G := G) F σ)
          (fun v : ↥((edgeFamilySubgraph G F).support) ↦ 2 * bHalf v.1) := by
    refine ⟨?_, ?_⟩
    · intro v
      have hxRows := (graphEdgeIncidencePolyhedron_mem_iff_rowwise (G := G) b).1 hxFeasible
      calc
        (((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) *ᵥ u) v =
            ((graphEdgeIncMatrix G ℝ).mulVec x) v.1 := by
              simpa [x] using congrFun
                (signedSupportReducedMatrix_mulVec (G := G) F σ u) v
        _ ≤ (b v.1 : ℝ) := hxRows v.1
        _ = ((2 * bHalf v.1 : ℤ) : ℝ) := by
              norm_num [hbHalf v.1]
    · intro e
      exact le_of_lt (huPos e)
  have hw_le_z :
      ∀ {w : ↥F → ℝ},
        w ∈
            nonnegative_matrix_polyhedron
              (signedSupportReducedMatrix (G := G) F σ)
              (fun v : ↥((edgeFamilySubgraph G F).support) ↦ 2 * bHalf v.1) →
          ∑ e : ↥F, signedSupportReducedObjective (G := G) F σ cNative e * w e ≤ z := by
    intro w hw
    have hwNativeFeasible :
        fixedSupportNativeVector (G := G) F σ w ∈ graph_edge_incidence_polyhedron G b :=
      fixedSupportNativeVector_mem_graphEdgeIncidencePolyhedron
        (G := G) b bHalf hbHalf F σ hxFeasible hw
    have hwImage :
        (∑ e : G.edgeSet, cNative e * fixedSupportNativeVector (G := G) F σ w e) ∈
          ((fun x : G.edgeSet → ℝ ↦ ∑ e : G.edgeSet, cNative e * x e) ''
            graph_edge_incidence_polyhedron G b) := by
      exact ⟨fixedSupportNativeVector (G := G) F σ w, hwNativeFeasible, rfl⟩
    calc
      ∑ e : ↥F, signedSupportReducedObjective (G := G) F σ cNative e * w e =
          ∑ e : G.edgeSet, cNative e * fixedSupportNativeVector (G := G) F σ w e := by
            exact signedSupportReducedObjective_dot (G := G) F σ cNative w
      _ ≤ z := hzNative.2 hwImage
  have huExtreme :
      u ∈
        (nonnegative_matrix_polyhedron
          (signedSupportReducedMatrix (G := G) F σ)
          (fun v : ↥((edgeFamilySubgraph G F).support) ↦ 2 * bHalf v.1)).extremePoints ℝ := by
    rw [mem_extremePoints_iff_forall_segment]
    refine ⟨huFeasible, ?_⟩
    intro w₁ hw₁ w₂ hw₂ huSeg
    rcases mem_segment_iff_div.mp huSeg with ⟨a, b', ha, hb', hab, hcomb⟩
    by_cases ha0 : a = 0
    · have hb0 : b' ≠ 0 := by
        intro hb0
        linarith
      right
      simpa [ha0, hb0] using hcomb
    · by_cases hb0 : b' = 0
      · have ha0' : a ≠ 0 := ha0
        left
        simpa [hb0, ha0'] using hcomb
      · let α : ℝ := a / (a + b')
        let β : ℝ := b' / (a + b')
        have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hb_pos : 0 < b' := lt_of_le_of_ne hb' (Ne.symm hb0)
        have hα_pos : 0 < α := by
          dsimp [α]
          exact div_pos ha_pos (by linarith)
        have hβ_pos : 0 < β := by
          dsimp [β]
          exact div_pos hb_pos (by linarith)
        have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
        have hβ_nonneg : 0 ≤ β := le_of_lt hβ_pos
        have hαβ : α + β = 1 := by
          have hden : a + b' ≠ 0 := by linarith
          dsimp [α, β]
          field_simp [hden]
          ring
        let φ : (↥F → ℝ) → ℝ :=
          fun w ↦ ∑ e : ↥F, signedSupportReducedObjective (G := G) F σ cNative e * w e
        have hφu : φ u = z := huObjective
        have hφw₁_le : φ w₁ ≤ z := hw_le_z hw₁
        have hφw₂_le : φ w₂ ≤ z := hw_le_z hw₂
        have hφcomb : φ u = α * φ w₁ + β * φ w₂ := by
          rw [hcomb]
          simp [φ, α, β, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
            smul_eq_mul, mul_add, add_mul, mul_assoc, left_distrib, right_distrib]
        have hzlin : α * z + β * z = z := by
          nlinarith [hαβ]
        have hφw₁_eq : φ w₁ = z := by
          by_contra hne
          have hlt : φ w₁ < z := lt_of_le_of_ne hφw₁_le (Ne.symm hne)
          have hlt_sum :
              α * φ w₁ + β * φ w₂ < α * z + β * z := by
            exact add_lt_add_of_lt_of_le
              (mul_lt_mul_of_pos_left hlt hα_pos)
              (mul_le_mul_of_nonneg_left hφw₂_le hβ_nonneg)
          linarith [hφcomb, hφu, hzlin]
        have hφw₂_eq : φ w₂ = z := by
          by_contra hne
          have hlt : φ w₂ < z := lt_of_le_of_ne hφw₂_le (Ne.symm hne)
          have hlt_sum :
              α * φ w₁ + β * φ w₂ < α * z + β * z := by
            exact add_lt_add_of_le_of_lt
              (mul_le_mul_of_nonneg_left hφw₁_le hα_nonneg)
              (mul_lt_mul_of_pos_left hlt hβ_pos)
          linarith [hφcomb, hφu, hzlin]
        have hw₁Face :
            fixedSupportExtension (G := G) F σ w₁ ∈
              face_set
                (nonnegative_matrix_polyhedron
                  (splitFinGraphEdgeIncMatrix (G := G))
                  (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
                (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
                z := by
          exact fixedSupportExtension_mem_splitOptimalFace
            (G := G) b bHalf hbHalf cNative F σ
            (w₀ := u) (w := w₁) (z := z) hxFeasible hw₁ hφw₁_eq
        have hw₂Face :
            fixedSupportExtension (G := G) F σ w₂ ∈
              face_set
                (nonnegative_matrix_polyhedron
                  (splitFinGraphEdgeIncMatrix (G := G))
                  (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
                (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
                z := by
          exact fixedSupportExtension_mem_splitOptimalFace
            (G := G) b bHalf hbHalf cNative F σ
            (w₀ := u) (w := w₂) (z := z) hxFeasible hw₂ hφw₂_eq
        have hybarExtremeSeg := (mem_extremePoints_iff_forall_segment).1 hybarExtreme
        have hybarSeg :
            ybar ∈
              segment ℝ
                (fixedSupportExtension (G := G) F σ w₁)
                (fixedSupportExtension (G := G) F σ w₂) := by
          simpa [hybarFixed] using
            fixedSupportExtension_mem_segment (G := G) F σ huSeg
        rcases hybarExtremeSeg.2
            (fixedSupportExtension (G := G) F σ w₁) hw₁Face
            (fixedSupportExtension (G := G) F σ w₂) hw₂Face hybarSeg with hEq | hEq
        · left
          exact (fixedSupportExtension_injective (G := G) F σ) <|
            calc
              fixedSupportExtension (G := G) F σ w₁ = ybar := hEq
              _ = fixedSupportExtension (G := G) F σ u := hybarFixed.symm
        · right
          exact (fixedSupportExtension_injective (G := G) F σ) <|
            calc
              fixedSupportExtension (G := G) F σ w₂ = ybar := hEq
              _ = fixedSupportExtension (G := G) F σ u := hybarFixed.symm
  rcases supportActiveGraphRows_squareSystem
      (G := G) bHalf σ huFeasible huExtreme huPos with ⟨ρ, hρactive, hρlinear⟩
  have hcrossZero :
      ∀ i e : ↥F,
        (ρ i).1 ∉
            ((edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1).supp →
          signedSupportReducedMatrix (G := G) F σ (ρ i) e = 0 := by
    intro i e hnotmem
    exact signedSupportReducedMatrix_eq_zero_of_not_mem_edgeComponent
      (G := G) σ (ρ i) e hnotmem
  have hfamily : incidence_independent_edge_family G F :=
    supportColumnsLinearIndependent (G := G) σ ρ hρlinear
  have hcomponentwise :
      ∀ c : (edgeFamilySubgraph G F).spanningCoe.ConnectedComponent,
        ∃ zc :
          {e : ↥F //
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} → ℤ,
          ∀ e,
            (if σ e.1 then u e.1 else -u e.1) = (zc e : ℝ) := by
    intro c
    let τ := supportComponentRowEdgeEquiv (G := G) σ ρ hρlinear hcrossZero c
    have hsystem :
        ((((supportComponentSquareBlock (G := G) σ ρ c τ).map (Int.castRingHom ℝ)) *ᵥ
            (fun i : {i : ↥F |
                (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
              u ((τ i).1))) =
          fun i : {i : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
            (2 * bHalf (ρ i.1).1 : ℝ)) :=
      supportComponentSquareSystem
        (G := G) σ ρ (u := u) (bHalf := bHalf) c
        (supportComponentSignedSystem (G := G) σ ρ (u := u) (bHalf := bHalf) hρactive c) τ
    have hlinearComponent :
        LinearIndependent ℝ
          (fun i : {i : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} ↦
            ((signedSupportReducedMatrix (G := G) F σ).map (Int.castRingHom ℝ)) (ρ i.1)) :=
      supportComponentSignedRows_linearIndependent (G := G) σ ρ hρlinear c
    have hdet_block :
        (supportComponentSquareBlock (G := G) σ ρ c τ).det ≠ 0 :=
      supportComponentSquareDet_ne_zero (G := G) σ ρ c hlinearComponent τ
    have hc_family : tree_or_odd_unicyclic c.toSimpleGraph := hfamily c
    rcases hc_family with hcTree | ⟨hcConn, hcard, hcNotBip⟩
    · exact supportComponentTreeSignedCoordinates_integer
        (G := G) σ (u := u) (bHalf := bHalf) ρ c τ hcTree hsystem hdet_block
    · have hrowCount :
          Nat.card {i : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk (ρ i).1 = c} =
            Nat.card {e : ↥F |
              (edgeFamilySubgraph G F).spanningCoe.connectedComponentMk e.1.out.1 = c} :=
        supportComponentActiveRows_card_eq_edges (G := G) σ ρ hρlinear hcrossZero c
      exact supportComponentOddUnicyclicSignedCoordinates_integer
        (G := G) σ (u := u) (bHalf := bHalf) ρ c τ hcConn hrowCount hcard hcNotBip hsystem
  have hxInteger :
      x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ fun e ↦ (z e : ℝ)) := by
    exact fixedSupportNativeVector_mem_range_of_componentwiseSignedCoordinates
      (G := G) σ u hcomponentwise
  exact ⟨x, ⟨hxFeasible, hxInteger⟩, hxObjective⟩

/-- Helper for Exercise 4.18: the remaining native graph-owner maximizer step is to package the
split/extreme/support route into an actual integral edge vector. -/
private lemma nativeGraphEdgeIncidencePolyhedron_integralMaximizer_of_evenRhs
    (b : V → ℚ)
    (hb : ∀ v, IsLocalization.IsInteger ℤ (b v / 2))
    (cNative : G.edgeSet → ℝ)
    (z : ℝ)
    (hzNative :
      IsGreatest
        ((fun x : G.edgeSet → ℝ ↦ ∑ e : G.edgeSet, cNative e * x e) ''
          graph_edge_incidence_polyhedron G b)
        z) :
    ∃ x ∈
        graph_edge_incidence_polyhedron G b ∩
          Set.range (fun z : G.edgeSet → ℤ ↦ fun e ↦ (z e : ℝ)),
      (∑ e : G.edgeSet, cNative e * x e) = z := by
  classical
  obtain ⟨bHalf, hbHalf⟩ := exists_even_integer_rhs b hb
  rcases hzNative.1 with ⟨x₀, hx₀Feasible, hx₀Objective⟩
  let y₀ := splitFinLift (G := G) (graphEdgeCoordinates (G := G) x₀)
  have hy₀Feasible :
      y₀ ∈
        nonnegative_matrix_polyhedron
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)) := by
    exact splitFinLift_mem_nonnegativePresentation (G := G) b bHalf hbHalf hx₀Feasible
  have hy₀Objective :
      splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ y₀ = z := by
    calc
      splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ y₀ =
          graphEdgeCoordinates (G := G) cNative ⬝ᵥ graphEdgeCoordinates (G := G) x₀ := by
            simpa [y₀] using
              splitFinObjective_dot_splitFinLift
                (G := G) (graphEdgeCoordinates (G := G) cNative)
                (graphEdgeCoordinates (G := G) x₀)
      _ = ∑ e : G.edgeSet, cNative e * x₀ e := by
            simpa using
              graphEdgeCoordinates_dotProduct
                (G := G) (graphEdgeCoordinates (G := G) cNative) x₀
      _ = z := hx₀Objective
  rcases splitFinOptimalFace_hasExtremePoint
      (G := G) b bHalf hbHalf cNative z hy₀Feasible hy₀Objective hzNative with
    ⟨ybar, hybarExtreme⟩
  have hybarFace :
      ybar ∈
        face_set
          (nonnegative_matrix_polyhedron
            (splitFinGraphEdgeIncMatrix (G := G))
            (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)))
          (splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative))
          z := extremePoints_subset hybarExtreme
  have hybarFeasible :
      ybar ∈
        nonnegative_matrix_polyhedron
          (splitFinGraphEdgeIncMatrix (G := G))
          (fun i ↦ 2 * bHalf ((Finite.equivFin V).symm i)) := by
    exact (mem_face_set_iff.mp hybarFace).1
  have hybarObjective :
      splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ ybar = z := by
    exact (mem_face_set_iff.mp hybarFace).2
  have hybarNoDoubleCopy :
      ∀ j : Fin (Nat.card G.edgeSet),
        ¬ (0 < ybar (Fin.castAdd (Nat.card G.edgeSet) j) ∧
            0 < ybar (Fin.natAdd (Nat.card G.edgeSet) j)) :=
    splitSupportHasNoDoubleCopy (G := G) bHalf cNative z hybarExtreme
  rcases positiveSupportActualEdgeFamilyData
      (G := G) bHalf hybarFeasible hybarNoDoubleCopy with
    ⟨huPos, hybarFixed, hxFixed⟩
  let F := actualSupportFamily (G := G) ybar
  let σ := supportOrientation (G := G) ybar
  let u := supportMagnitude (G := G) ybar
  have hxSupportFeasible :
      signedSupportNativeVector (G := G) ybar ∈ graph_edge_incidence_polyhedron G b := by
    rw [hxFixed]
    exact splitFinProjection_mem_graphEdgeIncidencePolyhedron
      (G := G) b bHalf hbHalf hybarFeasible
  have hxSupportObjective :
      (∑ e : G.edgeSet, cNative e * signedSupportNativeVector (G := G) ybar e) = z := by
    calc
      ∑ e : G.edgeSet, cNative e * signedSupportNativeVector (G := G) ybar e =
          ∑ e : G.edgeSet,
            cNative e *
              graphEdgeCoordinateReindex (G := G) (splitFinProjection (G := G) ybar) e := by
            rw [hxFixed]
      _ = graphEdgeCoordinates (G := G) cNative ⬝ᵥ splitFinProjection (G := G) ybar := by
            symm
            exact graphEdgeCoordinate_dotProduct_reindex
              (G := G) (graphEdgeCoordinates (G := G) cNative)
              (splitFinProjection (G := G) ybar)
      _ = splitFinObjective (G := G) (graphEdgeCoordinates (G := G) cNative) ⬝ᵥ ybar := by
            rw [splitFinObjective_dot_eq_projection]
      _ = z := hybarObjective
  by_cases hF : Set.Nonempty F
  · exact nonemptySupport_nativeIntegralMaximizer
      (G := G) b bHalf hbHalf cNative z hzNative F σ u hybarExtreme
      (by simpa [F, u] using huPos)
      (by simpa [F, σ, u] using hybarFixed)
      (by simpa [F, σ, u] using hxFixed)
      hxSupportFeasible hxSupportObjective
  · have hFempty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hF
    have hxZero : signedSupportNativeVector (G := G) ybar = 0 := by
      funext e
      simp [signedSupportNativeVector, F, hFempty]
    refine ⟨0, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa [hxZero] using hxSupportFeasible
      · refine ⟨fun _ ↦ 0, ?_⟩
        funext e
        simp
    · simpa [hxZero] using hxSupportObjective

/-- Helper for Exercise 4.18: every finite linear maximum on the `Fin`-indexed graph-incidence
presentation should be attained by an integral feasible point once `b / 2` is integral. -/
private lemma graphIncidencePresentation_integralMaximizer_of_evenRhs
    (b : V → ℚ)
    (hb : ∀ v, IsLocalization.IsInteger ℤ (b v / 2))
    (c : Fin (Nat.card G.edgeSet) → ℝ)
    (z : ℝ)
    (hz :
      IsGreatest
        ((c ⬝ᵥ ·) ''
          rational_matrix_polyhedron
            (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
              (graphEdgeIncMatrix G ℚ))
            (fun i ↦ b ((Finite.equivFin V).symm i)))
        z) :
    ∃ x ∈
        rational_matrix_polyhedron
          (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
            (graphEdgeIncMatrix G ℚ))
          (fun i ↦ b ((Finite.equivFin V).symm i)) ∩
            integerVectors (Nat.card G.edgeSet),
      c ⬝ᵥ x = z := by
  -- Route correction: the transport layer is now sealed. Reduce the `Fin`-indexed maximum to the
  -- native `G.edgeSet` coordinates before invoking the graph-specific split/extreme/Cramer route.
  have hzNative :
      IsGreatest
        (((fun x : G.edgeSet → ℝ ↦
            ∑ e : G.edgeSet, graphEdgeCoordinateReindex (G := G) c e * x e) ''
          graph_edge_incidence_polyhedron G b))
        z := by
    rcases hz with ⟨hzMem, hzUpper⟩
    constructor
    · rcases hzMem with ⟨y, hyP, rfl⟩
      refine ⟨graphEdgeCoordinateReindex (G := G) y, ?_, ?_⟩
      · exact (graphEdgeCoordinateReindex_mem_incidencePresentation_iff (G := G) b).2 hyP
      · simpa using (graphEdgeCoordinate_dotProduct_reindex (G := G) c y).symm
    · intro r hr
      rcases hr with ⟨x, hxNative, rfl⟩
      have hxP :
          graphEdgeCoordinates (G := G) x ∈
            rational_matrix_polyhedron
              (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
                (graphEdgeIncMatrix G ℚ))
              (fun i ↦ b ((Finite.equivFin V).symm i)) := by
        have hxReindexed :
            graphEdgeCoordinateReindex (G := G) (graphEdgeCoordinates (G := G) x) ∈
              graph_edge_incidence_polyhedron G b := by
          exact (graphEdgeCoordinateReindex_graphEdgeCoordinates (G := G) x).symm ▸ hxNative
        exact (graphEdgeCoordinateReindex_mem_incidencePresentation_iff (G := G) b).1 hxReindexed
      have hdot :
          c ⬝ᵥ graphEdgeCoordinates (G := G) x =
            ∑ e : G.edgeSet, graphEdgeCoordinateReindex (G := G) c e * x e := by
        calc
          c ⬝ᵥ graphEdgeCoordinates (G := G) x =
              ∑ e : G.edgeSet,
                graphEdgeCoordinateReindex (G := G) c e *
                  graphEdgeCoordinateReindex (G := G) (graphEdgeCoordinates (G := G) x) e := by
                rw [graphEdgeCoordinate_dotProduct_reindex (G := G) c
                  (graphEdgeCoordinates (G := G) x)]
          _ = ∑ e : G.edgeSet, graphEdgeCoordinateReindex (G := G) c e * x e := by
                rw [graphEdgeCoordinateReindex_graphEdgeCoordinates (G := G) x]
      have hrP :
          (∑ e : G.edgeSet, graphEdgeCoordinateReindex (G := G) c e * x e) ∈
            ((c ⬝ᵥ ·) ''
              rational_matrix_polyhedron
                (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
                  (graphEdgeIncMatrix G ℚ))
                (fun i ↦ b ((Finite.equivFin V).symm i))) := by
        refine ⟨graphEdgeCoordinates (G := G) x, hxP, ?_⟩
        simpa using hdot
      exact hzUpper hrP
  rcases nativeGraphEdgeIncidencePolyhedron_integralMaximizer_of_evenRhs
      (G := G) (b := b) hb (graphEdgeCoordinateReindex (G := G) c) z hzNative with
    ⟨x, ⟨hxNative, hxInteger⟩, hxValue⟩
  refine ⟨graphEdgeCoordinates (G := G) x, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · -- Reindex the native feasible maximizer back to the canonical `Fin` presentation.
      exact graphEdgeCoordinates_mem_incidencePresentation (G := G) b hxNative
    · -- The native integral witness stays integral after coordinate reindexing.
      exact graphEdgeCoordinates_mem_integerVectors (G := G) hxInteger
  · -- The `Fin`-indexed objective value is exactly the native objective value of the witness.
    calc
      c ⬝ᵥ graphEdgeCoordinates (G := G) x =
          ∑ e : G.edgeSet, graphEdgeCoordinateReindex (G := G) c e * x e :=
            graphEdgeCoordinates_dotProduct (G := G) c x
      _ = z := hxValue

end FinitePresentation

/-- Exercise 4.18. Let `A_G` be the incidence matrix of a graph `G` and let `b` be a vector such
that `b / 2` is integral. Then `{x : A_G x ≤ b}` is an integral polyhedron. -/
theorem graph_edge_incidence_polyhedron_is_integral_of_halved_rhs_integral
    (b : V → ℚ)
    (hb : ∀ v, IsLocalization.IsInteger ℤ (b v / 2)) :
    is_integral (graph_edge_incidence_polyhedron G b) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let _ : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  let A : Matrix (Fin (Nat.card V)) (Fin (Nat.card G.edgeSet)) ℚ :=
    Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (graphEdgeIncMatrix G ℚ)
  let bFin : Fin (Nat.card V) → ℚ := fun i ↦ b ((Finite.equivFin V).symm i)
  let P : Set (Fin (Nat.card G.edgeSet) → ℝ) := rational_matrix_polyhedron A bFin
  have hP_rational : is_rational_polyhedron P := by
    -- The `Fin`-indexed presentation is already a rational matrix polyhedron by definition.
    rw [is_rational_polyhedron_iff]
    refine ⟨Nat.card V, A, bFin, ?_⟩
    simp [P, A, bFin, rational_matrix_polyhedron]
  have hIntegralP : is_integral P := by
    -- Route correction: reduce the native graph owner to the canonical Chapter 4.1 `Fin`
    -- presentation, so the remaining work is exactly the graph-specific maximizer lemma.
    refine
      (rational_polyhedron_is_integral_iff_linear_maxima_attained_by_integral_points
        (P := P) hP_rational).2 ?_
    intro c z hz
    simpa [P, A, bFin] using
      graphIncidencePresentation_integralMaximizer_of_evenRhs
        (G := G) (b := b) hb c z hz
  have hIntegralImage : is_integral (graphEdgeCoordinateReindex (G := G) '' P) := by
    -- The edge-coordinate equivalence preserves the integer-point owner.
    simpa [graphEdgeCoordinateReindex, P] using
      isIntegralFunCongrLeftSymmImage
        ((Finite.equivFin G.edgeSet).symm) hIntegralP
  have hImage :
      graph_edge_incidence_polyhedron G b = graphEdgeCoordinateReindex (G := G) '' P := by
    ext x
    constructor
    · intro hx
      refine ⟨graphEdgeCoordinates (G := G) x, ?_, ?_⟩
      · -- Reindex the native feasible point into the `Fin` presentation.
        have hx' :
            graphEdgeCoordinateReindex (G := G) (graphEdgeCoordinates (G := G) x) ∈
              graph_edge_incidence_polyhedron G b := by
          exact (graphEdgeCoordinateReindex_graphEdgeCoordinates (G := G) x).symm ▸ hx
        exact (graphEdgeCoordinateReindex_mem_incidencePresentation_iff (G := G) b).1 hx'
      · exact graphEdgeCoordinateReindex_graphEdgeCoordinates (G := G) x
    · rintro ⟨y, hy, rfl⟩
      exact (graphEdgeCoordinateReindex_mem_incidencePresentation_iff (G := G) b).2 hy
  -- Replace the native owner by the transported `Fin`-indexed presentation.
  rw [hImage]
  exact hIntegralImage

/-- If `b / 2` is integral coordinatewise, then the graph-incidence polyhedron is the convex hull
of its integral edge-coordinate points. -/
theorem graph_edge_incidence_polyhedron_eq_convexHull_integral_points_of_halved_rhs_integral
    (b : V → ℚ)
    (hb : ∀ v, IsLocalization.IsInteger ℤ (b v / 2)) :
    graph_edge_incidence_polyhedron G b =
      convexHull ℝ
        (graph_edge_incidence_polyhedron G b ∩
          Set.range (fun z : G.edgeSet → ℤ ↦ fun e ↦ (z e : ℝ))) := by
  -- This is exactly the defining expansion of `is_integral`.
  simpa [is_integral_iff] using
    graph_edge_incidence_polyhedron_is_integral_of_halved_rhs_integral (G := G) b hb

end Exercise418
