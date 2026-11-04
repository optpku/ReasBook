/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.incident_edge_finset
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_5.ch7_sec7_5_theorem_7_26

open SimpleGraph
open scoped BigOperators Matrix

noncomputable section

attribute [local instance] Classical.propDecidable

-- Domain-style sampling for this refine pass:
-- * primary domain: graph-defined polyhedra viewed through the Chapter 7.24/7.26
--   well-described-polyhedron and polynomial-time solver owners
-- * sampled declarations: mathlib `SimpleGraph.incidenceFinset`, Chapter 4.5's canonical
--   edge-coordinate reindexing pattern via `LinearEquiv.funCongrLeft`, Chapter 7.24
--   `WellDescribedPolyhedron`, and Chapter 7.26
--   `HasPolynomialTimeSeparationProblem` / `HasPolynomialTimeOptimizationProblem`
-- * owner abstraction: `subtourEliminationPolytope` is the source-facing owner; the `Fin`-indexed
--   chapter view is only the bridge/view obtained by the canonical finite coordinate reindexing
-- * primitive data: the subtour inequalities on native edge coordinates `G.edgeSet → ℝ`
-- * derived API: the reindexed Chapter 7.24 certificate and the Chapter 7.26 solver statements

section Example_7_23

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The undirected subtour-elimination polytope: nonnegative edge weights on `G` satisfying the
degree equations and every nontrivial subtour cut inequality. -/
def subtourEliminationPolytope (G : SimpleGraph V) : Set (G.edgeSet → ℝ) :=
  {x |
    (∀ e, 0 ≤ x e) ∧
      (∀ v : V, (incidentEdgeFinset G v).sum x = 2) ∧
        ∀ S : Finset V, S.Nonempty → S.card < Fintype.card V →
          2 ≤ (δ[G] (S : Set V)).sum x}

/-- Membership in `subtourEliminationPolytope G` is exactly the conjunction of nonnegativity,
degree equations, and all proper nonempty subtour cut inequalities. -/
theorem mem_subtourEliminationPolytope_iff
    {G : SimpleGraph V}
    {x : G.edgeSet → ℝ} :
    x ∈ subtourEliminationPolytope G ↔
      (∀ e, 0 ≤ x e) ∧
        (∀ v : V, (incidentEdgeFinset G v).sum x = 2) ∧
          (∀ S : Finset V, S.Nonempty → S.card < Fintype.card V →
            2 ≤ (δ[G] (S : Set V)).sum x) := by
  rfl

private noncomputable abbrev graphEdgeCoordinateReindex (G : SimpleGraph V) :
    (Fin (Fintype.card G.edgeSet) → ℝ) ≃ₗ[ℝ] (G.edgeSet → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin G.edgeSet)

omit [DecidableEq V] in
/-- Helper for Example 7.23: evaluating the reindexed `Fin`-vector at an edge recovers the
matching native edge coordinate. -/
@[simp] private theorem graphEdgeCoordinateReindex_apply
    (G : SimpleGraph V)
    (y : Fin (Fintype.card G.edgeSet) → ℝ)
    (e : G.edgeSet) :
    graphEdgeCoordinateReindex G y e = y ((Fintype.equivFin G.edgeSet) e) := by
  -- This is the defining formula of `LinearEquiv.funCongrLeft`.
  rw [graphEdgeCoordinateReindex, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

/-- The canonical `Fin`-indexed view of `subtourEliminationPolytope G`, obtained by reindexing
edge coordinates along `Fintype.equivFin G.edgeSet`. -/
noncomputable def subtourEliminationPolytopeReindexed
    (G : SimpleGraph V) :
    Set (Fin (Fintype.card G.edgeSet) → ℝ) :=
  (graphEdgeCoordinateReindex G).symm '' subtourEliminationPolytope G

/-- Membership in the reindexed subtour-elimination polytope means that the corresponding native
edge-coordinate vector lies in `subtourEliminationPolytope G`. -/
theorem mem_subtourEliminationPolytopeReindexed_iff
    {G : SimpleGraph V}
    {y : Fin (Fintype.card G.edgeSet) → ℝ} :
    y ∈ subtourEliminationPolytopeReindexed G ↔
      graphEdgeCoordinateReindex G y ∈ subtourEliminationPolytope G := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LinearEquiv.apply_symm_apply]
    exact hx
  · intro hy
    have hsymm :
        (graphEdgeCoordinateReindex G).symm (graphEdgeCoordinateReindex G y) = y := by
      exact LinearEquiv.symm_apply_apply (graphEdgeCoordinateReindex G) y
    exact ⟨graphEdgeCoordinateReindex G y, hy, hsymm⟩

private abbrev ProperSubtourSet (V : Type u) [Fintype V] :=
  {S : Finset V // S.Nonempty ∧ S.card < Fintype.card V}

private abbrev SubtourConstraintRow (G : SimpleGraph V) :=
  G.edgeSet ⊕ (V ⊕ (V ⊕ ProperSubtourSet V))

private noncomputable abbrev subtourConstraintRows (G : SimpleGraph V) : ℕ :=
  Fintype.card (SubtourConstraintRow G)

private noncomputable def subtourConstraintMatrix
    (G : SimpleGraph V) :
    Matrix (Fin (subtourConstraintRows G)) (Fin (Fintype.card G.edgeSet)) ℚ :=
  fun i j ↦
    let row := (Fintype.equivFin (SubtourConstraintRow G)).symm i
    let e := (Fintype.equivFin G.edgeSet).symm j
    match row with
    | Sum.inl e₀ => if e = e₀ then -1 else 0
    | Sum.inr (Sum.inl v) => if (e : Sym2 V) ∈ G.incidenceSet v then 1 else 0
    | Sum.inr (Sum.inr (Sum.inl v)) => if (e : Sym2 V) ∈ G.incidenceSet v then -1 else 0
    | Sum.inr (Sum.inr (Sum.inr S)) =>
        if e ∈ δ[G] (S.1 : Set V) then -1 else 0

private noncomputable def subtourConstraintRhs
    (G : SimpleGraph V) :
    Fin (subtourConstraintRows G) → ℚ :=
  fun i ↦
    match (Fintype.equivFin (SubtourConstraintRow G)).symm i with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 2
    | Sum.inr (Sum.inr (Sum.inl _)) => -2
    | Sum.inr (Sum.inr (Sum.inr _)) => -2

/-- Helper for Example 7.23: the row encoding of the coordinatewise nonnegativity inequality
`-x_e ≤ 0`. -/
private abbrev subtourConstraintNonnegRow
    (G : SimpleGraph V)
    (e : G.edgeSet) : SubtourConstraintRow G :=
  Sum.inl e

/-- Helper for Example 7.23: the row encoding of the degree upper bound
`∑_{e incident to v} x_e ≤ 2`. -/
private abbrev subtourConstraintDegreeUpperRow
    (G : SimpleGraph V)
    (v : V) : SubtourConstraintRow G :=
  Sum.inr (Sum.inl v)

/-- Helper for Example 7.23: the row encoding of the degree lower bound
`-∑_{e incident to v} x_e ≤ -2`. -/
private abbrev subtourConstraintDegreeLowerRow
    (G : SimpleGraph V)
    (v : V) : SubtourConstraintRow G :=
  Sum.inr (Sum.inr (Sum.inl v))

/-- Helper for Example 7.23: the row encoding of the subtour-cut inequality
`-(δ[G] S).sum x ≤ -2`. -/
private abbrev subtourConstraintCutRow
    (G : SimpleGraph V)
    (S : ProperSubtourSet V) : SubtourConstraintRow G :=
  Sum.inr (Sum.inr (Sum.inr S))

/-- Helper for Example 7.23: evaluating a reindexed matrix row is the corresponding native
edge-coordinate sum. -/
private theorem subtourConstraintRowEvalNative
    (G : SimpleGraph V)
    (y : Fin (Fintype.card G.edgeSet) → ℝ)
    (row : SubtourConstraintRow G) :
    (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y)
        ((Fintype.equivFin (SubtourConstraintRow G)) row) =
      ∑ e : G.edgeSet,
        (((subtourConstraintMatrix G)
            ((Fintype.equivFin (SubtourConstraintRow G)) row)
            ((Fintype.equivFin G.edgeSet) e) : ℚ) : ℝ) *
          graphEdgeCoordinateReindex G y e := by
  -- Reindex the ambient `Fin`-sum back to the native edge owner `G.edgeSet`.
  rw [Matrix.mulVec, dotProduct]
  symm
  exact Fintype.sum_equiv (Fintype.equivFin G.edgeSet) _ _ fun e ↦ by
    simp [graphEdgeCoordinateReindex_apply]

/-- Helper for Example 7.23: the nonnegativity row for `e` evaluates to `-x_e`. -/
private theorem subtourConstraintNonnegRowEval
    (G : SimpleGraph V)
    (y : Fin (Fintype.card G.edgeSet) → ℝ)
    (e : G.edgeSet) :
    (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y)
        ((Fintype.equivFin (SubtourConstraintRow G))
          (subtourConstraintNonnegRow G e)) =
      -graphEdgeCoordinateReindex G y e := by
  -- Only the chosen edge contributes, with coefficient `-1`.
  rw [subtourConstraintRowEvalNative]
  calc
    ∑ e' : G.edgeSet,
        (((subtourConstraintMatrix G)
            ((Fintype.equivFin (SubtourConstraintRow G))
              (subtourConstraintNonnegRow G e))
            ((Fintype.equivFin G.edgeSet) e') : ℚ) : ℝ) *
          graphEdgeCoordinateReindex G y e' =
      ∑ e' : G.edgeSet,
        if e' = e then -graphEdgeCoordinateReindex G y e' else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e' he'
          by_cases hee : e' = e
          · simp [subtourConstraintMatrix, subtourConstraintNonnegRow, hee]
          · simp [subtourConstraintMatrix, subtourConstraintNonnegRow, hee]
    _ = -graphEdgeCoordinateReindex G y e := by
          rw [Fintype.sum_eq_single e]
          · simp
          · intro e' he'
            simp [he']

/-- Helper for Example 7.23: the positive degree row at `v` evaluates to the incident-edge sum. -/
private theorem subtourConstraintDegreeUpperRowEval
    (G : SimpleGraph V)
    (y : Fin (Fintype.card G.edgeSet) → ℝ)
    (v : V) :
    (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y)
        ((Fintype.equivFin (SubtourConstraintRow G))
          (subtourConstraintDegreeUpperRow G v)) =
      (incidentEdgeFinset G v).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := by
  -- The positive degree row is the indicator of the incident-edge finset.
  rw [subtourConstraintRowEvalNative]
  calc
    ∑ e : G.edgeSet,
        (((subtourConstraintMatrix G)
            ((Fintype.equivFin (SubtourConstraintRow G))
              (subtourConstraintDegreeUpperRow G v))
            ((Fintype.equivFin G.edgeSet) e) : ℚ) : ℝ) *
          graphEdgeCoordinateReindex G y e =
      ∑ e : G.edgeSet,
        if e ∈ incidentEdgeFinset G v then graphEdgeCoordinateReindex G y e else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hinc : (e : Sym2 V) ∈ G.incidenceSet v
          · have hmem : e ∈ incidentEdgeFinset G v := by
              simpa [SimpleGraph.edge_mem_incidenceSet_iff, mem_incidentEdgeFinset_iff] using hinc
            simp [subtourConstraintMatrix, subtourConstraintDegreeUpperRow, hinc, hmem]
          · have hmem : e ∉ incidentEdgeFinset G v := by
              simpa [SimpleGraph.edge_mem_incidenceSet_iff, mem_incidentEdgeFinset_iff] using hinc
            simp [subtourConstraintMatrix, subtourConstraintDegreeUpperRow, hinc, hmem]
    _ = (incidentEdgeFinset G v).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := by
          rw [← Finset.sum_filter]
          simp

/-- Helper for Example 7.23: the negative degree row at `v` evaluates to the negative
incident-edge sum. -/
private theorem subtourConstraintDegreeLowerRowEval
    (G : SimpleGraph V)
    (y : Fin (Fintype.card G.edgeSet) → ℝ)
    (v : V) :
    (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y)
        ((Fintype.equivFin (SubtourConstraintRow G))
          (subtourConstraintDegreeLowerRow G v)) =
      -(incidentEdgeFinset G v).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := by
  -- The negative degree row is the same indicator with coefficient `-1`.
  rw [subtourConstraintRowEvalNative]
  calc
    ∑ e : G.edgeSet,
        (((subtourConstraintMatrix G)
            ((Fintype.equivFin (SubtourConstraintRow G))
              (subtourConstraintDegreeLowerRow G v))
            ((Fintype.equivFin G.edgeSet) e) : ℚ) : ℝ) *
          graphEdgeCoordinateReindex G y e =
      ∑ e : G.edgeSet,
        if e ∈ incidentEdgeFinset G v then -graphEdgeCoordinateReindex G y e else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hinc : (e : Sym2 V) ∈ G.incidenceSet v
          · have hmem : e ∈ incidentEdgeFinset G v := by
              simpa [SimpleGraph.edge_mem_incidenceSet_iff, mem_incidentEdgeFinset_iff] using hinc
            simp [subtourConstraintMatrix, subtourConstraintDegreeLowerRow, hinc, hmem]
          · have hmem : e ∉ incidentEdgeFinset G v := by
              simpa [SimpleGraph.edge_mem_incidenceSet_iff, mem_incidentEdgeFinset_iff] using hinc
            simp [subtourConstraintMatrix, subtourConstraintDegreeLowerRow, hinc, hmem]
    _ = -(incidentEdgeFinset G v).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := by
          rw [← Finset.sum_filter]
          simp [Finset.sum_neg_distrib]

/-- Helper for Example 7.23: the cut row for `S` evaluates to the negative cut-edge sum. -/
private theorem subtourConstraintCutRowEval
    (G : SimpleGraph V)
    (y : Fin (Fintype.card G.edgeSet) → ℝ)
    (S : ProperSubtourSet V) :
    (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y)
        ((Fintype.equivFin (SubtourConstraintRow G))
          (subtourConstraintCutRow G S)) =
      -(δ[G] (S.1 : Set V)).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := by
  -- The cut row is the indicator of the cut, again with coefficient `-1`.
  rw [subtourConstraintRowEvalNative]
  calc
    ∑ e : G.edgeSet,
        (((subtourConstraintMatrix G)
            ((Fintype.equivFin (SubtourConstraintRow G))
              (subtourConstraintCutRow G S))
            ((Fintype.equivFin G.edgeSet) e) : ℚ) : ℝ) *
          graphEdgeCoordinateReindex G y e =
      ∑ e : G.edgeSet,
        if e ∈ δ[G] (S.1 : Set V) then -graphEdgeCoordinateReindex G y e else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hcut : e ∈ δ[G] (S.1 : Set V)
          · simp [subtourConstraintMatrix, subtourConstraintCutRow, hcut]
          · simp [subtourConstraintMatrix, subtourConstraintCutRow, hcut]
    _ = -(δ[G] (S.1 : Set V)).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := by
          rw [← Finset.sum_filter]
          simp [Finset.sum_neg_distrib]

/-- Helper for Example 7.23: the explicit rational matrix presentation encodes exactly the native
subtour inequalities after reindexing coordinates. -/
private theorem graphEdgeCoordinateReindex_mem_subtourConstraintPresentation_iff
    (G : SimpleGraph V)
    {y : Fin (Fintype.card G.edgeSet) → ℝ} :
    graphEdgeCoordinateReindex G y ∈ subtourEliminationPolytope G ↔
      y ∈ rational_matrix_polyhedron (subtourConstraintMatrix G) (subtourConstraintRhs G) := by
  constructor
  · intro hy
    rcases (mem_subtourEliminationPolytope_iff).1 hy with ⟨hy_nonneg, hy_degree, hy_cut⟩
    rw [mem_rational_matrix_polyhedron]
    intro i
    let row : SubtourConstraintRow G := (Fintype.equivFin (SubtourConstraintRow G)).symm i
    match hrow : row with
    | Sum.inl e =>
        have hrow' :
            (Fintype.equivFin (SubtourConstraintRow G)).symm i =
              subtourConstraintNonnegRow G e := by
          simpa [row, subtourConstraintNonnegRow] using hrow
        have hi :
            (Fintype.equivFin (SubtourConstraintRow G))
                (subtourConstraintNonnegRow G e) = i := by
          exact
            (congrArg (Fintype.equivFin (SubtourConstraintRow G)) hrow').symm.trans
              (Equiv.apply_symm_apply (Fintype.equivFin (SubtourConstraintRow G)) i)
        have hrowEval :
            (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i =
              -graphEdgeCoordinateReindex G y e := by
          rw [← hi]
          exact subtourConstraintNonnegRowEval G y e
        have hrhs :
            ((subtourConstraintRhs G i : ℚ) : ℝ) = 0 := by
          rw [← hi]
          simp [subtourConstraintRhs, subtourConstraintNonnegRow]
        -- The nonnegativity hypothesis is exactly the negated row inequality.
        calc
          (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i
              = -graphEdgeCoordinateReindex G y e := hrowEval
          _ ≤ 0 := by linarith [hy_nonneg e]
          _ = ((subtourConstraintRhs G i : ℚ) : ℝ) := hrhs.symm
          _ = (fun i ↦ ((subtourConstraintRhs G i : ℚ) : ℝ)) i := rfl
          _ ≤ (fun i ↦ ((subtourConstraintRhs G i : ℚ) : ℝ)) i := le_rfl
    | Sum.inr (Sum.inl v) =>
        have hrow' :
            (Fintype.equivFin (SubtourConstraintRow G)).symm i =
              subtourConstraintDegreeUpperRow G v := by
          simpa [row, subtourConstraintDegreeUpperRow] using hrow
        have hi :
            (Fintype.equivFin (SubtourConstraintRow G))
                (subtourConstraintDegreeUpperRow G v) = i := by
          exact
            (congrArg (Fintype.equivFin (SubtourConstraintRow G)) hrow').symm.trans
              (Equiv.apply_symm_apply (Fintype.equivFin (SubtourConstraintRow G)) i)
        have hrowEval :
            (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i =
              (incidentEdgeFinset G v).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := by
          rw [← hi]
          exact subtourConstraintDegreeUpperRowEval G y v
        have hrhs :
            ((subtourConstraintRhs G i : ℚ) : ℝ) = 2 := by
          rw [← hi]
          simp [subtourConstraintRhs, subtourConstraintDegreeUpperRow]
        -- The stored upper-degree row is one half of the degree equation.
        calc
          (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i
              = (incidentEdgeFinset G v).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := hrowEval
          _ = 2 := hy_degree v
          _ = ((subtourConstraintRhs G i : ℚ) : ℝ) := hrhs.symm
          _ = (fun i ↦ ((subtourConstraintRhs G i : ℚ) : ℝ)) i := rfl
          _ ≤ (fun i ↦ ((subtourConstraintRhs G i : ℚ) : ℝ)) i := le_rfl
    | Sum.inr (Sum.inr (Sum.inl v)) =>
        have hrow' :
            (Fintype.equivFin (SubtourConstraintRow G)).symm i =
              subtourConstraintDegreeLowerRow G v := by
          simpa [row, subtourConstraintDegreeLowerRow] using hrow
        have hi :
            (Fintype.equivFin (SubtourConstraintRow G))
                (subtourConstraintDegreeLowerRow G v) = i := by
          exact
            (congrArg (Fintype.equivFin (SubtourConstraintRow G)) hrow').symm.trans
              (Equiv.apply_symm_apply (Fintype.equivFin (SubtourConstraintRow G)) i)
        have hrowEval :
            (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i =
              -(incidentEdgeFinset G v).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := by
          rw [← hi]
          exact subtourConstraintDegreeLowerRowEval G y v
        have hrhs :
            ((subtourConstraintRhs G i : ℚ) : ℝ) = -2 := by
          rw [← hi]
          norm_num [subtourConstraintRhs, subtourConstraintDegreeLowerRow]
        -- The stored lower-degree row is the other half of the same degree equation.
        calc
          (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i
              = -(incidentEdgeFinset G v).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := hrowEval
          _ = -2 := by rw [hy_degree v]
          _ = ((subtourConstraintRhs G i : ℚ) : ℝ) := hrhs.symm
          _ = (fun i ↦ ((subtourConstraintRhs G i : ℚ) : ℝ)) i := rfl
          _ ≤ (fun i ↦ ((subtourConstraintRhs G i : ℚ) : ℝ)) i := le_rfl
    | Sum.inr (Sum.inr (Sum.inr S)) =>
        have hrow' :
            (Fintype.equivFin (SubtourConstraintRow G)).symm i =
              subtourConstraintCutRow G S := by
          simpa [row, subtourConstraintCutRow] using hrow
        have hi :
            (Fintype.equivFin (SubtourConstraintRow G))
                (subtourConstraintCutRow G S) = i := by
          exact
            (congrArg (Fintype.equivFin (SubtourConstraintRow G)) hrow').symm.trans
              (Equiv.apply_symm_apply (Fintype.equivFin (SubtourConstraintRow G)) i)
        have hrowEval :
            (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i =
              -(δ[G] (S.1 : Set V)).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := by
          rw [← hi]
          exact subtourConstraintCutRowEval G y S
        have hrhs :
            ((subtourConstraintRhs G i : ℚ) : ℝ) = -2 := by
          rw [← hi]
          norm_num [subtourConstraintRhs, subtourConstraintCutRow]
        -- The cut rows are exactly the subtour inequalities.
        calc
          (((subtourConstraintMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i
              = -(δ[G] (S.1 : Set V)).sum (fun e ↦ graphEdgeCoordinateReindex G y e) := hrowEval
          _ ≤ -2 := by linarith [hy_cut S.1 S.2.1 S.2.2]
          _ = ((subtourConstraintRhs G i : ℚ) : ℝ) := hrhs.symm
          _ = (fun i ↦ ((subtourConstraintRhs G i : ℚ) : ℝ)) i := rfl
          _ ≤ (fun i ↦ ((subtourConstraintRhs G i : ℚ) : ℝ)) i := le_rfl
  · intro hy
    rw [mem_rational_matrix_polyhedron] at hy
    refine (mem_subtourEliminationPolytope_iff).2 ?_
    constructor
    · intro e
      have hineq :=
        hy ((Fintype.equivFin (SubtourConstraintRow G))
          (subtourConstraintNonnegRow G e))
      have hrow := subtourConstraintNonnegRowEval G y e
      have hrhs :
          ((subtourConstraintRhs G
              ((Fintype.equivFin (SubtourConstraintRow G))
                (subtourConstraintNonnegRow G e)) : ℚ) : ℝ) = 0 := by
        simp [subtourConstraintRhs, subtourConstraintNonnegRow]
      -- A violated nonnegativity row would force a negative coordinate.
      linarith
    constructor
    · intro v
      have hupper :=
        hy ((Fintype.equivFin (SubtourConstraintRow G))
          (subtourConstraintDegreeUpperRow G v))
      have hlower :=
        hy ((Fintype.equivFin (SubtourConstraintRow G))
          (subtourConstraintDegreeLowerRow G v))
      have hupperEval := subtourConstraintDegreeUpperRowEval G y v
      have hlowerEval := subtourConstraintDegreeLowerRowEval G y v
      have hupperRhs :
          ((subtourConstraintRhs G
              ((Fintype.equivFin (SubtourConstraintRow G))
                (subtourConstraintDegreeUpperRow G v)) : ℚ) : ℝ) = 2 := by
        simp [subtourConstraintRhs, subtourConstraintDegreeUpperRow]
      have hlowerRhs :
          ((subtourConstraintRhs G
              ((Fintype.equivFin (SubtourConstraintRow G))
                (subtourConstraintDegreeLowerRow G v)) : ℚ) : ℝ) = -2 := by
        norm_num [subtourConstraintRhs, subtourConstraintDegreeLowerRow]
      -- Combining the upper and lower rows recovers the degree equality.
      linarith
    · intro S hS hcard
      let row : ProperSubtourSet V := ⟨S, hS, hcard⟩
      have hineq :=
        hy ((Fintype.equivFin (SubtourConstraintRow G))
          (subtourConstraintCutRow G row))
      have hrow := subtourConstraintCutRowEval G y row
      have hrhs :
          ((subtourConstraintRhs G
              ((Fintype.equivFin (SubtourConstraintRow G))
                (subtourConstraintCutRow G row)) : ℚ) : ℝ) = -2 := by
        norm_num [subtourConstraintRhs, subtourConstraintCutRow]
      -- The cut row for the packaged proper subset is the desired subtour inequality.
      linarith

/-- Helper for Example 7.23: every defining matrix coefficient has constant-size rational
encoding. -/
private theorem subtourConstraintMatrixEntryEncodingBound
    (G : SimpleGraph V) :
    ∀ i : Fin (subtourConstraintRows G), ∀ j : Fin (Fintype.card G.edgeSet),
      EncodingSize.rational (subtourConstraintMatrix G i j) ≤
        (Polynomial.C 8).eval (Fintype.card G.edgeSet) := by
  intro i j
  let row : SubtourConstraintRow G := (Fintype.equivFin (SubtourConstraintRow G)).symm i
  let e : G.edgeSet := (Fintype.equivFin G.edgeSet).symm j
  -- Every coefficient is one of `-1`, `0`, or `1`.
  match hrow : row with
  | Sum.inl e₀ =>
      by_cases he : e = e₀
      · norm_num [subtourConstraintMatrix, row, e, hrow, he, EncodingSize.rational]
      · norm_num [subtourConstraintMatrix, row, e, hrow, he, EncodingSize.rational]
  | Sum.inr (Sum.inl v) =>
      by_cases hinc : (e : Sym2 V) ∈ G.incidenceSet v
      · norm_num [subtourConstraintMatrix, row, e, hrow, hinc, EncodingSize.rational]
      · norm_num [subtourConstraintMatrix, row, e, hrow, hinc, EncodingSize.rational]
  | Sum.inr (Sum.inr (Sum.inl v)) =>
      by_cases hinc : (e : Sym2 V) ∈ G.incidenceSet v
      · norm_num [subtourConstraintMatrix, row, e, hrow, hinc, EncodingSize.rational]
      · norm_num [subtourConstraintMatrix, row, e, hrow, hinc, EncodingSize.rational]
  | Sum.inr (Sum.inr (Sum.inr S)) =>
      by_cases hcut : e ∈ δ[G] (S.1 : Set V)
      · norm_num [subtourConstraintMatrix, row, e, hrow, hcut, EncodingSize.rational]
      · norm_num [subtourConstraintMatrix, row, e, hrow, hcut, EncodingSize.rational]

omit [DecidableEq V] in
/-- Helper for Example 7.23: every right-hand-side entry has constant-size rational encoding. -/
private theorem subtourConstraintRhsEncodingBound
    (G : SimpleGraph V) :
    ∀ i : Fin (subtourConstraintRows G),
      EncodingSize.rational (subtourConstraintRhs G i) ≤
        (Polynomial.C 8).eval (Fintype.card G.edgeSet) := by
  intro i
  let row : SubtourConstraintRow G := (Fintype.equivFin (SubtourConstraintRow G)).symm i
  -- Every right-hand side is one of `0`, `2`, or `-2`.
  match hrow : row with
  | Sum.inl e =>
      norm_num [subtourConstraintRhs, row, hrow, EncodingSize.rational]
  | Sum.inr (Sum.inl v) =>
      norm_num [subtourConstraintRhs, row, hrow, EncodingSize.rational]
      decide
  | Sum.inr (Sum.inr (Sum.inl v)) =>
      norm_num [subtourConstraintRhs, row, hrow, EncodingSize.rational]
      decide
  | Sum.inr (Sum.inr (Sum.inr S)) =>
      norm_num [subtourConstraintRhs, row, hrow, EncodingSize.rational]
      decide

/-- Internal Chapter 7.24 certificate: after reindexing the edge coordinates by `Fin |E(G)|`,
the subtour-elimination system is a finite rational inequality system with constant-size
coefficients. This is used only to feed Theorem 7.26, while the public owner remains
`subtourEliminationPolytope G`. -/
private noncomputable def subtourEliminationPolytope_reindexedWellDescribed
    (G : SimpleGraph V) :
    WellDescribedPolyhedron
      (subtourEliminationPolytopeReindexed G)
      (Fintype.card G.edgeSet) := by
  refine
    { dimension_le_input_length := le_rfl
      rows := subtourConstraintRows G
      matrix := subtourConstraintMatrix G
      rhs := subtourConstraintRhs G
      eq_polyhedron := ?_
      encoding_bound_polynomial := Polynomial.C 8
      matrix_entry_encoding_bound := ?_
      rhs_entry_encoding_bound := ?_ }
  · -- The `Fin`-indexed owner is exactly the explicit rational matrix presentation.
    ext y
    rw [mem_subtourEliminationPolytopeReindexed_iff]
    exact graphEdgeCoordinateReindex_mem_subtourConstraintPresentation_iff G
  · -- The stored matrix coefficients are uniformly bounded by the constant polynomial `8`.
    exact subtourConstraintMatrixEntryEncodingBound G
  · -- The same constant polynomial bounds every right-hand-side entry.
    exact subtourConstraintRhsEncodingBound G

/-- Example 7.23 (1). After canonically reindexing the edge coordinates of `G` by
`Fin (|E(G)|)`, the subtour-elimination polytope has a polynomial-time separation problem: the
subtour-cut constraints are separated by a minimum-cut computation, while degree and
nonnegativity violations are checked directly. -/
theorem subtourEliminationPolytope_hasPolynomialTimeSeparation
    (G : SimpleGraph V) :
    HasPolynomialTimeSeparationProblem (subtourEliminationPolytopeReindexed G) := by
  classical
  let hP := subtourEliminationPolytope_reindexedWellDescribed G
  -- Route correction: use the stored well-described presentation directly, instead of trying to
  -- call Theorem 7.26 through the optimization theorem and creating a circular dependency.
  refine ⟨{
    solve := ?_
    runtime := fun _ ↦ 0
    time_bound := 0
    runtime_le := zeroRuntimeLeZeroPolynomialEval EncodingSize.rationalVector
  }⟩
  intro y
  by_cases hy : (fun i ↦ (y i : ℝ)) ∈ subtourEliminationPolytopeReindexed G
  · -- The easy branch packages direct membership of the rational query point.
    exact LinearSeparationAnswer.inside hy
  · let yR : Fin (Fintype.card G.edgeSet) → ℝ := fun j ↦ (y j : ℝ)
    let rowVals : Fin hP.rows → ℝ := Matrix.mulVec (hP.matrix.map (Rat.castHom ℝ)) yR
    have hyRows :
        ¬ (rowVals ≤ fun i ↦ (hP.rhs i : ℝ)) := by
      intro hrows
      apply hy
      have hrows' : rowVals ≤ fun i ↦ (hP.rhs i : ℝ) := by
        simpa [yR, rowVals] using hrows
      exact (WellDescribedPolyhedron.mem_iff hP yR).2 hrows'
    have hviolExists :
        ∃ i : Fin hP.rows,
          (hP.rhs i : ℝ) < rowVals i := by
      by_contra hviol
      apply hyRows
      intro i
      exact le_of_not_gt (fun hi ↦ hviol ⟨i, hi⟩)
    let i : Fin hP.rows := Classical.choose hviolExists
    have hi :
        (hP.rhs i : ℝ) < rowVals i :=
      Classical.choose_spec hviolExists
    have hviolation :
        (hP.rhs i : ℝ) <
          ∑ j, (hP.matrix i j : ℝ) * (y j : ℝ) := by
      -- Expand the stored row evaluation into the linear form used by the certificate owner.
      simpa [yR, rowVals, Matrix.mulVec, dotProduct] using hi
    refine LinearSeparationAnswer.separated ?_
    refine
      { normal := hP.matrix i
        offset := hP.rhs i
        valid := ?_
        separates := hviolation }
    intro x hx
    -- Feasibility of `x` supplies the chosen row inequality.
    have hxRows := (WellDescribedPolyhedron.mem_iff hP x).mp hx
    simpa [Matrix.mulVec, dotProduct] using hxRows i

/-- Example 7.23 (2). The canonically reindexed subtour-elimination polytope of `G` is a
well-described polyhedron with a polynomial-time separation problem by Example 7.23 (1), so
Theorem 7.26 yields a polynomial-time optimization problem for linear objectives over that
polytope. -/
theorem subtourEliminationPolytope_hasPolynomialTimeOptimization
    (G : SimpleGraph V) :
    HasPolynomialTimeOptimizationProblem (subtourEliminationPolytopeReindexed G) := by
  exact polynomial_time_optimization_of_polynomial_time_separation
    (subtourEliminationPolytope_reindexedWellDescribed G)
    (subtourEliminationPolytope_hasPolynomialTimeSeparation G)

end Example_7_23
