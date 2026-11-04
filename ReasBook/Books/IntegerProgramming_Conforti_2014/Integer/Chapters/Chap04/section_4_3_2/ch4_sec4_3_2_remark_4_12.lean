/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_definition_3_14_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3.ch4_sec4_3_definition_4_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_1.ch4_sec4_3_1_definition_4_3_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_definition_4_3_3_extra_1
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

universe u v

/-- The shortest-path linear program attached to a directed network, a source `s`, a sink `t`,
and an arc-length function. -/
structure ShortestPathLinearProgram (V : Type u) (A : Type v) where
  tail : A → V
  head : A → V
  s : V
  t : V
  length : A → ℝ

namespace ShortestPathLinearProgram

/-- The vertex list visited by an arc list `p` when it starts at `u`. -/
def walkVerticesFrom (P : ShortestPathLinearProgram V A) : V → List A → List V
  | u, [] => [u]
  | u, a :: p => u :: P.walkVerticesFrom (P.head a) p

/-- `IsDirectedWalkFromTo P u v p` means that the arc list `p` forms a directed walk from `u` to
`v` in the network underlying `P`. -/
def IsDirectedWalkFromTo (P : ShortestPathLinearProgram V A) : V → V → List A → Prop
  | u, v, [] => u = v
  | u, v, a :: p =>
      P.tail a = u ∧ P.IsDirectedWalkFromTo (P.head a) v p

/-- An `s,t`-walk in `P` is a directed walk from the source `s` to the sink `t`. -/
def IsStWalk (P : ShortestPathLinearProgram V A) (p : List A) : Prop :=
  P.IsDirectedWalkFromTo P.s P.t p

/-- An `s,t`-path in `P` is an `s,t`-walk with no repeated vertices. -/
def IsStPath (P : ShortestPathLinearProgram V A) (p : List A) : Prop :=
  P.IsStWalk p ∧ (P.walkVerticesFrom P.s p).Nodup

/-- The length of an arc list is the sum of the lengths of its arcs. -/
def pathLength (P : ShortestPathLinearProgram V A) (p : List A) : ℝ :=
  (p.map P.length).sum

/-- A directed circuit in `P` is a nonempty closed directed walk with no repeated vertices away
from its basepoint. -/
def IsCircuit (P : ShortestPathLinearProgram V A) (c : List A) : Prop :=
  c ≠ [] ∧ ∃ w, P.IsDirectedWalkFromTo w w c ∧ (P.walkVerticesFrom w c).tail.Nodup

/-- `P` contains a negative-length circuit when some directed circuit has negative total length. -/
def HasNegativeLengthCircuit (P : ShortestPathLinearProgram V A) : Prop :=
  ∃ c, P.IsCircuit c ∧ P.pathLength c < 0

/-- `P` has no negative-length circuit when every directed circuit has nonnegative total length. -/
def HasNoNegativeLengthCircuit (P : ShortestPathLinearProgram V A) : Prop :=
  ∀ c, P.IsCircuit c → 0 ≤ P.pathLength c

/-- An `s,t`-path is shortest when it minimizes total length among all `s,t`-paths in `P`. -/
def IsShortestStPath (P : ShortestPathLinearProgram V A) (p : List A) : Prop :=
  P.IsStPath p ∧ ∀ q, P.IsStPath q → P.pathLength p ≤ P.pathLength q

end ShortestPathLinearProgram

section Remark_4_12

variable {V : Type} {A : Type}

namespace ShortestPathLinearProgram

/-- An arc vector is the characteristic vector of a shortest `s,t`-path when it is the indicator
vector of some shortest `s,t`-path, expressed through the chapter owner
`circuit_characteristic_vector`. -/
def IsCharacteristicVectorOfShortestStPath
    (P : ShortestPathLinearProgram V A) (x : A → ℝ) : Prop :=
  let _ : DecidableEq A := Classical.decEq A
  ∃ p : List A, P.IsShortestStPath p ∧ x = circuit_characteristic_vector p.toFinset

section Flow

variable [Fintype A]

/-- The right-hand side of the source-sink flow-conservation equation at the vertex `v`. -/
noncomputable def balanceRhs (P : ShortestPathLinearProgram V A) (v : V) : ℝ :=
  let _ : DecidableEq V := Classical.decEq V
  (if v = P.s then 1 else 0) - (if v = P.t then 1 else 0)

/-- The feasible arc vectors of the shortest-path linear program: unit `s,t`-flows. This reuses
the chapter owner `IsSTFlow`; the source/sink distinctness is a derived consequence of the unit
value condition, not primitive feasibility data. -/
def IsFeasible (P : ShortestPathLinearProgram V A) (x : A → ℝ) : Prop :=
  IsSTFlow P.tail P.head P.s P.t x ∧
    st_flow_value P.tail P.head P.s x = 1

/-- A feasible shortest-path flow necessarily has distinct source and sink. -/
theorem IsFeasible.source_ne_sink
    {P : ShortestPathLinearProgram V A} {x : A → ℝ} (hx : P.IsFeasible x) :
    P.s ≠ P.t := by
  intro hst
  rcases hx with ⟨hxflow, hxvalue⟩
  have hbalance := st_flow_value_eq_sink_balance hxflow
  have hbalance' :
      st_flow_value P.tail P.head P.s x =
        incoming_flow P.head x P.s - outgoing_flow P.tail x P.s := by
    simpa [hst] using hbalance
  have hzero : st_flow_value P.tail P.head P.s x = 0 := by
    have hsource :
        outgoing_flow P.tail x P.s = incoming_flow P.head x P.s := by
      unfold st_flow_value at hbalance'
      linarith
    rw [st_flow_value]
    exact sub_eq_zero.mpr hsource
  have h10 : (1 : ℝ) = 0 := by
    rw [← hxvalue, hzero]
  norm_num at h10

/-- The `Fin`-indexed coordinate vector obtained by reindexing an arc vector along the canonical
enumeration of `A`. -/
noncomputable def arcCoordinates (x : A → ℝ) :
    Fin (Fintype.card A) → ℝ :=
  fun j ↦ x ((Fintype.equivFin A).symm j)

section Basic

variable [Fintype V]

/-- The digraph underlying `P`, forgetting the distinguished source, sink, and arc lengths. This
is the bridge to the chapter's connected-component API for incidence matrices. -/
def digraph (P : ShortestPathLinearProgram V A) : Digraph V where
  Adj u v := ∃ a, P.tail a = u ∧ P.head a = v

/-- The `Fin`-indexed right-hand side vector obtained from `P.balanceRhs` by reindexing the
vertices along the canonical enumeration of `V`. -/
noncomputable def balanceCoordinates (P : ShortestPathLinearProgram V A) :
    Fin (Fintype.card V) → ℝ :=
  fun i ↦ P.balanceRhs ((Fintype.equivFin V).symm i)

/-- The `Fin`-indexed node-arc incidence matrix of the network underlying `P`, obtained by
reindexing the chapter owner `digraph_incidence_matrix ℝ P.tail P.head` along the canonical
`Fintype.equivFin` enumerations. -/
noncomputable abbrev incidenceMatrix (P : ShortestPathLinearProgram V A) :
    Matrix (Fin (Fintype.card V)) (Fin (Fintype.card A)) ℝ :=
  let M : Matrix V A ℝ :=
    digraph_incidence_matrix ℝ P.tail P.head
  Matrix.reindex (Fintype.equivFin V) (Fintype.equivFin A) M

/-- Helper for Remark 4.12: multiplying the unreindexed incidence matrix by an arc vector records
incoming minus outgoing flow at each vertex. -/
private theorem digraph_incidence_matrix_mulVec_apply
    (tail head : A → V) (x : A → ℝ) (v : V) :
    (digraph_incidence_matrix ℝ tail head *ᵥ x) v =
      incoming_flow head x v - outgoing_flow tail x v := by
  classical
  have hhead_sum :
      ∑ e, (if v = head e then x e else 0) = incoming_flow head x v := by
    -- The head-indicator summand keeps exactly the arcs entering `v`.
    rw [incoming_flow_eq_sum_incoming_arcs]
    rw [incoming_arcs, Finset.sum_filter]
    simp [eq_comm]
  have htail_sum :
      ∑ e, (if v = tail e then x e else 0) = outgoing_flow tail x v := by
    -- The tail-indicator summand keeps exactly the arcs leaving `v`.
    rw [outgoing_flow_eq_sum_outgoing_arcs]
    rw [outgoing_arcs, Finset.sum_filter]
    simp [eq_comm]
  -- Splitting the incidence entry into head and tail parts exposes the vertex balance formula.
  calc
    (digraph_incidence_matrix ℝ tail head *ᵥ x) v
        = ∑ e, (((if v = head e then (1 : ℝ) else 0) -
            (if v = tail e then 1 else 0)) * x e) := by
            simp [Matrix.mulVec, dotProduct, digraph_incidence_matrix]
    _ = ∑ e, ((if v = head e then x e else 0) -
          (if v = tail e then x e else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            by_cases hhead : v = head e
            · by_cases htail : v = tail e
              · have hend : head e = tail e := hhead.symm.trans htail
                simp [hhead, hend]
              · have hend : head e ≠ tail e := fun hend ↦ htail (hhead.trans hend)
                simp [hhead, hend]
            · by_cases htail : v = tail e
              · have hend : tail e ≠ head e := fun hend ↦ hhead (htail.trans hend)
                simp [htail, hend]
              · simp [hhead, htail]
    _ = (∑ e, (if v = head e then x e else 0)) -
          ∑ e, (if v = tail e then x e else 0) := by
            rw [Finset.sum_sub_distrib]
    _ = incoming_flow head x v - outgoing_flow tail x v := by
          rw [hhead_sum, htail_sum]

/-- Helper for Remark 4.12: reindexing a finite matrix to canonical `Fin` owners commutes with
matrix-vector multiplication after composing the vector with the column equivalence. -/
private theorem reindexed_mulVec_apply
    {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ)
    (eα : α ≃ Fin (Fintype.card α))
    (eβ : β ≃ Fin (Fintype.card β))
    (x : Fin (Fintype.card β) → ℝ) :
    Matrix.reindex eα eβ M *ᵥ x =
      fun i ↦ (M *ᵥ ((LinearEquiv.funCongrLeft ℝ ℝ eβ) x)) (eα.symm i) := by
  have hlin :=
    congrArg
      (fun T :
          (Fin (Fintype.card β) → ℝ) →ₗ[ℝ]
            Fin (Fintype.card α) → ℝ ↦
        T x)
      (Matrix.mulVecLin_reindex (R := ℝ) eα eβ M)
  -- Evaluating the canonical reindexing linear equivalence gives the required formula.
  simpa using hlin

/-- Helper for Remark 4.12: the reindexed incidence matrix applied to the reindexed arc vector is
the same vertex-balance vector as in the original arc owner. -/
private theorem incidenceMatrix_mulVec_arcCoordinates_apply
    (P : ShortestPathLinearProgram V A) (x : A → ℝ) (i : Fin (Fintype.card V)) :
    (P.incidenceMatrix *ᵥ arcCoordinates x) i =
      incoming_flow P.head x ((Fintype.equivFin V).symm i) -
        outgoing_flow P.tail x ((Fintype.equivFin V).symm i) := by
  let M : Matrix V A ℝ := digraph_incidence_matrix ℝ P.tail P.head
  have hcoords :
      (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin A)) (arcCoordinates x) = x := by
    -- The canonical arc-coordinate reindexing is definitionally inverse to evaluation on `A`.
    ext a
    simp [arcCoordinates]
  have hmul :=
    congrFun
      (reindexed_mulVec_apply M (Fintype.equivFin V) (Fintype.equivFin A) (arcCoordinates x))
      i
  -- After undoing the coordinate change, the unreindexed incidence-balance formula applies.
  calc
    (P.incidenceMatrix *ᵥ arcCoordinates x) i
        = (M *ᵥ ((LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin A)) (arcCoordinates x)))
            ((Fintype.equivFin V).symm i) := by
              simpa [ShortestPathLinearProgram.incidenceMatrix, M] using hmul
    _ = (M *ᵥ x) ((Fintype.equivFin V).symm i) := by rw [hcoords]
    _ = incoming_flow P.head x ((Fintype.equivFin V).symm i) -
          outgoing_flow P.tail x ((Fintype.equivFin V).symm i) := by
            simp [M, digraph_incidence_matrix_mulVec_apply]

/-- Reindexing along the canonical finite enumerations converts `P.IsFeasible x` into the
standard equality-form owner from Chapter 3, with the owner-compatible right-hand side
`-P.balanceCoordinates` dictated by the incidence-matrix sign convention; the distinctness
condition appears only here because the linear-algebraic owner by itself does not rule out
`P.s = P.t`. -/
theorem isFeasible_iff_in_standard_equality_form
    (P : ShortestPathLinearProgram V A) (x : A → ℝ) :
    P.IsFeasible x ↔
      P.s ≠ P.t ∧
        arcCoordinates x ∈ standard_equality_form P.incidenceMatrix (-P.balanceCoordinates) := by
  constructor
  · intro hx
    rcases hx with ⟨hxflow, hxvalue⟩
    have hst : P.s ≠ P.t :=
      ShortestPathLinearProgram.IsFeasible.source_ne_sink (P := P) (x := x) ⟨hxflow, hxvalue⟩
    refine ⟨hst, ?_⟩
    rw [mem_standard_equality_form_iff]
    refine ⟨?_, ?_⟩
    · ext i
      let v : V := (Fintype.equivFin V).symm i
      -- Evaluate the reindexed balance equation at the vertex represented by `i`.
      rw [incidenceMatrix_mulVec_arcCoordinates_apply]
      by_cases hvs : v = P.s
      · -- At the source, unit flow means incoming minus outgoing equals `-1`.
        -- At the source, unit flow means incoming minus outgoing equals `-1`.
        have hsource :
            incoming_flow P.head x P.s - outgoing_flow P.tail x P.s = -1 := by
          unfold st_flow_value at hxvalue
          linarith
        simpa [ShortestPathLinearProgram.balanceCoordinates,
          ShortestPathLinearProgram.balanceRhs, v, hvs, hst] using hsource
      · by_cases hvt : v = P.t
        · -- At the sink, the sink-balance identity converts the unit value into `+1`.
          -- At the sink, the sink-balance identity converts the unit value into `+1`.
          have hsink :
              incoming_flow P.head x P.t - outgoing_flow P.tail x P.t = 1 := by
            simpa [hxvalue] using (st_flow_value_eq_sink_balance hxflow).symm
          have hts : P.t ≠ P.s := fun hts ↦ hst hts.symm
          simpa [ShortestPathLinearProgram.balanceCoordinates,
            ShortestPathLinearProgram.balanceRhs, v, hvt, hts] using hsink
        · -- Every other row vanishes by flow conservation away from source and sink.
          have hcons : incoming_flow P.head x v = outgoing_flow P.tail x v :=
            hxflow.conservation v hvs hvt
          simpa [ShortestPathLinearProgram.balanceCoordinates,
            ShortestPathLinearProgram.balanceRhs, v, hvs, hvt] using (sub_eq_zero.mpr hcons)
    · intro i
      -- Nonnegativity is preserved by the canonical arc-coordinate reindexing.
      simpa [arcCoordinates] using hxflow.nonneg ((Fintype.equivFin A).symm i)
  · rintro ⟨hst, hxstd⟩
    rw [mem_standard_equality_form_iff] at hxstd
    rcases hxstd with ⟨hbalance, hnonneg⟩
    refine ⟨?_, ?_⟩
    · refine
        { nonneg := ?_
          conservation := ?_ }
      · intro a
        -- Read the nonnegativity constraint back through the arc-coordinate equivalence.
        simpa [arcCoordinates] using hnonneg (Fintype.equivFin A a)
      · intro v hvs hvt
        have hv :=
          congrFun hbalance (Fintype.equivFin V v)
        -- Route correction: read the reindexed equality row at `v` before converting it back to
        -- the original conservation identity.
        rw [incidenceMatrix_mulVec_arcCoordinates_apply] at hv
        have hzero :
            incoming_flow P.head x v - outgoing_flow P.tail x v = 0 := by
          simpa [ShortestPathLinearProgram.balanceCoordinates,
            ShortestPathLinearProgram.balanceRhs, hvs, hvt] using hv
        exact sub_eq_zero.mp hzero
    · have hsource :=
        congrFun hbalance (Fintype.equivFin V P.s)
      rw [incidenceMatrix_mulVec_arcCoordinates_apply] at hsource
      -- The source row equals `-1`, so the net flow leaving the source is `1`.
      have hsource_balance :
          incoming_flow P.head x P.s - outgoing_flow P.tail x P.s = -1 := by
        simpa [ShortestPathLinearProgram.balanceCoordinates,
          ShortestPathLinearProgram.balanceRhs, hst] using hsource
      unfold st_flow_value
      linarith

/-- The connected component of the reindexed vertex `i` in the underlying undirected support graph
of `P`. -/
noncomputable def vertexComponent
    (P : ShortestPathLinearProgram V A) (i : Fin (Fintype.card V)) :
    let G := P.digraph.toSimpleGraphInclusive
    G.ConnectedComponent :=
  let G := P.digraph.toSimpleGraphInclusive
  G.connectedComponentMk ((Fintype.equivFin V).symm i)

/-- A row set `R` is component-reduced when its complement contains exactly one reindexed vertex
from each connected component of the underlying undirected support graph of `P`. Equivalently,
the corresponding balance subsystem deletes one redundant node equation per connected component. -/
def IsComponentReducedRowSet
    (P : ShortestPathLinearProgram V A) (R : Finset (Fin (Fintype.card V))) : Prop :=
  let G := P.digraph.toSimpleGraphInclusive
  ∀ c : G.ConnectedComponent, ∃! i : Fin (Fintype.card V), i ∉ R ∧ P.vertexComponent i = c

/-- The reduced incidence matrix obtained by keeping exactly the balance rows indexed by `R`. This
is the Chapter 3 equality-form owner attached to a chosen component-reduced row set. -/
noncomputable def restrictedIncidenceMatrix
    (P : ShortestPathLinearProgram V A) (R : Finset (Fin (Fintype.card V))) :
    Matrix (Fin R.card) (Fin (Fintype.card A)) ℝ :=
  let M : Matrix {i : Fin (Fintype.card V) // i ∈ R} (Fin (Fintype.card A)) ℝ :=
    P.incidenceMatrix.submatrix Subtype.val id
  Matrix.reindex (Fintype.equivFinOfCardEq (Fintype.card_coe R)) (Equiv.refl _) M

/-- The owner-compatible right-hand side for the row-restricted balance system indexed by `R`; the
minus sign matches the incidence-matrix convention. -/
noncomputable def restrictedBalanceRhs
    (P : ShortestPathLinearProgram V A) (R : Finset (Fin (Fintype.card V))) :
    Fin R.card → ℝ :=
  fun i ↦
    (-P.balanceCoordinates) ((Fintype.equivFinOfCardEq (Fintype.card_coe R)).symm i).1

/-- The objective value of the shortest-path linear program at the arc vector `x`. -/
def objective (P : ShortestPathLinearProgram V A) (x : A → ℝ) : ℝ :=
  ∑ a, P.length a * x a

/-- An optimal solution of the shortest-path linear program is a feasible arc vector minimizing
the objective value among all feasible arc vectors. -/
def IsOptimalSolution (P : ShortestPathLinearProgram V A) (x : A → ℝ) : Prop :=
  P.IsFeasible x ∧ ∀ y, P.IsFeasible y → P.objective x ≤ P.objective y

/-- The shortest-path linear program has a feasible solution when some arc vector satisfies the
source-sink balance constraints. -/
def HasFeasibleSolution (P : ShortestPathLinearProgram V A) : Prop :=
  ∃ x, P.IsFeasible x

/-- The shortest-path linear program has an optimal solution when some feasible arc vector is
objective-minimizing. -/
def HasOptimalSolution (P : ShortestPathLinearProgram V A) : Prop :=
  ∃ x, P.IsOptimalSolution x

/-- The shortest-path linear program is unbounded when its objective is unbounded below on the
feasible region. -/
def IsUnbounded (P : ShortestPathLinearProgram V A) : Prop :=
  ∀ r : ℝ, ∃ x, P.IsFeasible x ∧ P.objective x ≤ r

/-- A basic feasible solution of the shortest-path linear program is a feasible solution whose arc
coordinates are basic for some component-reduced balance system, obtained by deleting exactly one
redundant node equation from each connected component of the underlying undirected support graph. -/
def IsBasicFeasibleSolution (P : ShortestPathLinearProgram V A) (x : A → ℝ) : Prop :=
  ∃ R : Finset (Fin (Fintype.card V)),
    P.IsComponentReducedRowSet R ∧
      is_basic_feasible_solution (P.restrictedIncidenceMatrix R) (P.restrictedBalanceRhs R)
        (arcCoordinates x)

/-- Unfolding `P.IsBasicFeasibleSolution x` gives a component-reduced balance subsystem whose
reduced incidence system realizes the arc coordinates of `x` as a basic feasible solution. -/
theorem isBasicFeasibleSolution_iff
    (P : ShortestPathLinearProgram V A) (x : A → ℝ) :
    P.IsBasicFeasibleSolution x ↔
      ∃ R : Finset (Fin (Fintype.card V)),
        P.IsComponentReducedRowSet R ∧
          is_basic_feasible_solution (P.restrictedIncidenceMatrix R) (P.restrictedBalanceRhs R)
            (arcCoordinates x) := by
  rfl

/-- A basic optimal solution is an optimal solution whose coordinate vector is basic for some
component-reduced balance system of the shortest-path linear program. -/
def IsBasicOptimalSolution (P : ShortestPathLinearProgram V A) (x : A → ℝ) : Prop :=
  P.IsBasicFeasibleSolution x ∧ P.IsOptimalSolution x

/-- Unfolding `P.IsBasicOptimalSolution x` gives component-reduced basicity together with
optimality. -/
theorem isBasicOptimalSolution_iff
    (P : ShortestPathLinearProgram V A) (x : A → ℝ) :
    P.IsBasicOptimalSolution x ↔
      P.IsBasicFeasibleSolution x ∧ P.IsOptimalSolution x := by
  rfl

end Basic

end Flow

end ShortestPathLinearProgram

variable [Fintype A]

noncomputable local instance : DecidableEq A := Classical.decEq A
noncomputable local instance : DecidableEq V := Classical.decEq V

/-- Helper for Remark 4.12: the arc-multiplicity vector attached to a walk list records how many
times each arc occurs in that list. -/
noncomputable def walkArcVector : List A → A → ℝ
  | [] => 0
  | a :: p => fun b ↦ (if b = a then 1 else 0) + walkArcVector p b

/-- Helper for Remark 4.12: the walk arc vector is coordinatewise nonnegative. -/
private theorem walkArcVector_nonneg (p : List A) (a : A) :
    0 ≤ walkArcVector p a := by
  classical
  induction p generalizing a with
  | nil =>
      -- The empty walk contributes no arcs.
      simp [walkArcVector]
  | cons b p ih =>
      -- Each recursive step adds one nonnegative singleton indicator.
      by_cases h : a = b
      · have hnonneg : 0 ≤ walkArcVector p a := ih a
        subst h
        simpa [walkArcVector] using add_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hnonneg
      · simpa [walkArcVector, h] using
          add_nonneg (show (0 : ℝ) ≤ 0 by norm_num) (ih a)

/-- Helper for Remark 4.12: the single-arc indicator contributes one unit of incoming flow exactly
at the head of that arc. -/
private theorem incomingFlow_singleArc
    (head : A → V) (a : A) (w : V) :
    incoming_flow head (fun b ↦ if b = a then (1 : ℝ) else 0) w =
      if w = head a then 1 else 0 := by
  classical
  -- Collapse the incoming-arc fiber against the singleton indicator at `a`.
  rw [incoming_flow_eq_sum_incoming_arcs]
  by_cases ha : a ∈ incoming_arcs head w
  · rw [Finset.sum_eq_single a]
    · have hmem : head a = w := by simpa using ha
      simpa [hmem]
    · intro b hb hba
      simp [hba]
    · simpa using ha
  · rw [Finset.sum_eq_zero]
    · have hnot : head a ≠ w := by
        simpa [mem_incoming_arcs_iff] using ha
      have hnot' : w ≠ head a := fun hw ↦ hnot hw.symm
      simpa [hnot']
    · intro b hb
      have hb_ne : b ≠ a := by
        intro hba
        apply ha
        simpa [hba] using hb
      simp [hb_ne]

/-- Helper for Remark 4.12: the single-arc indicator contributes one unit of outgoing flow exactly
at the tail of that arc. -/
private theorem outgoingFlow_singleArc
    (tail : A → V) (a : A) (w : V) :
    outgoing_flow tail (fun b ↦ if b = a then (1 : ℝ) else 0) w =
      if w = tail a then 1 else 0 := by
  classical
  -- Collapse the outgoing-arc fiber against the singleton indicator at `a`.
  rw [outgoing_flow_eq_sum_outgoing_arcs]
  by_cases ha : a ∈ outgoing_arcs tail w
  · rw [Finset.sum_eq_single a]
    · have hmem : tail a = w := by simpa using ha
      simpa [hmem]
    · intro b hb hba
      simp [hba]
    · simpa using ha
  · rw [Finset.sum_eq_zero]
    · have hnot : tail a ≠ w := by
        simpa [mem_outgoing_arcs_iff] using ha
      have hnot' : w ≠ tail a := fun hw ↦ hnot hw.symm
      simpa [hnot']
    · intro b hb
      have hb_ne : b ≠ a := by
        intro hba
        apply ha
        simpa [hba] using hb
      simp [hb_ne]

/-- Helper for Remark 4.12: incoming flow over a walk multiplicity vector splits into the head
contribution of the first arc plus the incoming flow of the tail walk. -/
private theorem incomingFlow_walkArcVector_cons
    (P : ShortestPathLinearProgram V A) (a : A) (p : List A) (w : V) :
    incoming_flow P.head (walkArcVector (a :: p)) w =
      incoming_flow P.head (walkArcVector p) w + (if w = P.head a then 1 else 0) := by
  classical
  -- Expand the recursive walk vector and separate the singleton contribution from the tail walk.
  calc
    incoming_flow P.head (walkArcVector (a :: p)) w
        = Finset.sum (incoming_arcs P.head w)
            (fun b ↦ (if b = a then 1 else 0) + walkArcVector p b) := by
            rw [walkArcVector, incoming_flow_eq_sum_incoming_arcs]
    _ = Finset.sum (incoming_arcs P.head w) (fun b ↦ if b = a then 1 else 0) +
          Finset.sum (incoming_arcs P.head w) (walkArcVector p) := by
            rw [Finset.sum_add_distrib]
    _ = incoming_flow P.head (fun b ↦ if b = a then 1 else 0) w +
          incoming_flow P.head (walkArcVector p) w := by
            rw [incoming_flow_eq_sum_incoming_arcs, incoming_flow_eq_sum_incoming_arcs]
    _ = incoming_flow P.head (walkArcVector p) w + (if w = P.head a then 1 else 0) := by
          rw [incomingFlow_singleArc]
          ring

/-- Helper for Remark 4.12: outgoing flow over a walk multiplicity vector splits into the tail
contribution of the first arc plus the outgoing flow of the tail walk. -/
private theorem outgoingFlow_walkArcVector_cons
    (P : ShortestPathLinearProgram V A) (a : A) (p : List A) (w : V) :
    outgoing_flow P.tail (walkArcVector (a :: p)) w =
      outgoing_flow P.tail (walkArcVector p) w + (if w = P.tail a then 1 else 0) := by
  classical
  -- Expand the recursive walk vector and separate the singleton contribution from the tail walk.
  calc
    outgoing_flow P.tail (walkArcVector (a :: p)) w
        = Finset.sum (outgoing_arcs P.tail w)
            (fun b ↦ (if b = a then 1 else 0) + walkArcVector p b) := by
            rw [walkArcVector, outgoing_flow_eq_sum_outgoing_arcs]
    _ = Finset.sum (outgoing_arcs P.tail w) (fun b ↦ if b = a then 1 else 0) +
          Finset.sum (outgoing_arcs P.tail w) (walkArcVector p) := by
            rw [Finset.sum_add_distrib]
    _ = outgoing_flow P.tail (fun b ↦ if b = a then 1 else 0) w +
          outgoing_flow P.tail (walkArcVector p) w := by
            rw [outgoing_flow_eq_sum_outgoing_arcs, outgoing_flow_eq_sum_outgoing_arcs]
    _ = outgoing_flow P.tail (walkArcVector p) w + (if w = P.tail a then 1 else 0) := by
          rw [outgoingFlow_singleArc]
          ring

/-- Helper for Remark 4.12: the multiplicity vector of a directed walk has the expected endpoint
imbalance `δ_v - δ_u`. -/
private theorem directedWalk_balance
    (P : ShortestPathLinearProgram V A) :
    ∀ {u v : V} {p : List A}, P.IsDirectedWalkFromTo u v p →
      ∀ w,
        incoming_flow P.head (walkArcVector p) w -
          outgoing_flow P.tail (walkArcVector p) w =
            (if w = v then 1 else 0) - (if w = u then 1 else 0)
  | u, v, [], hp, w => by
      classical
      subst hp
      -- The empty walk has zero imbalance at every vertex.
      simp [walkArcVector, incoming_flow_eq_sum_incoming_arcs, outgoing_flow_eq_sum_outgoing_arcs]
  | u, v, a :: p, hp, w => by
      classical
      rcases hp with ⟨htail, hpTail⟩
      have ih := directedWalk_balance (P := P) hpTail w
      -- The first arc changes the imbalance by one unit at its head and tail.
      rw [incomingFlow_walkArcVector_cons, outgoingFlow_walkArcVector_cons, htail]
      calc
        (incoming_flow P.head (walkArcVector p) w + (if w = P.head a then 1 else 0)) -
            (outgoing_flow P.tail (walkArcVector p) w + (if w = u then 1 else 0))
            =
              (incoming_flow P.head (walkArcVector p) w -
                  outgoing_flow P.tail (walkArcVector p) w) +
                ((if w = P.head a then 1 else 0) - (if w = u then 1 else 0)) := by
                  ring
        _ =
              ((if w = v then 1 else 0) - (if w = P.head a then 1 else 0)) +
                ((if w = P.head a then 1 else 0) - (if w = u then 1 else 0)) := by
                  rw [ih]
        _ = (if w = v then 1 else 0) - (if w = u then 1 else 0) := by
              ring

/-- Helper for Remark 4.12: `incoming_flow` is additive in the arc vector. -/
private theorem incomingFlow_add
    (head : A → V) (x y : A → ℝ) (w : V) :
    incoming_flow head (x + y) w = incoming_flow head x w + incoming_flow head y w := by
  classical
  rw [incoming_flow_eq_sum_incoming_arcs, incoming_flow_eq_sum_incoming_arcs,
    incoming_flow_eq_sum_incoming_arcs]
  simpa [Pi.add_apply] using
    (Finset.sum_add_distrib : _)

/-- Helper for Remark 4.12: `outgoing_flow` is additive in the arc vector. -/
private theorem outgoingFlow_add
    (tail : A → V) (x y : A → ℝ) (w : V) :
    outgoing_flow tail (x + y) w = outgoing_flow tail x w + outgoing_flow tail y w := by
  classical
  rw [outgoing_flow_eq_sum_outgoing_arcs, outgoing_flow_eq_sum_outgoing_arcs,
    outgoing_flow_eq_sum_outgoing_arcs]
  simpa [Pi.add_apply] using
    (Finset.sum_add_distrib : _)

/-- Helper for Remark 4.12: `incoming_flow` commutes with scalar multiplication. -/
private theorem incomingFlow_smul
    (head : A → V) (μ : ℝ) (x : A → ℝ) (w : V) :
    incoming_flow head (μ • x) w = μ * incoming_flow head x w := by
  classical
  rw [incoming_flow_eq_sum_incoming_arcs, incoming_flow_eq_sum_incoming_arcs]
  simp [Pi.smul_apply, Finset.mul_sum]

/-- Helper for Remark 4.12: `outgoing_flow` commutes with scalar multiplication. -/
private theorem outgoingFlow_smul
    (tail : A → V) (μ : ℝ) (x : A → ℝ) (w : V) :
    outgoing_flow tail (μ • x) w = μ * outgoing_flow tail x w := by
  classical
  rw [outgoing_flow_eq_sum_outgoing_arcs, outgoing_flow_eq_sum_outgoing_arcs]
  simp [Pi.smul_apply, Finset.mul_sum]

/-- Helper for Remark 4.12: `incoming_flow` commutes with subtraction of arc vectors. -/
private theorem incomingFlow_sub
    (head : A → V) (x y : A → ℝ) (w : V) :
    incoming_flow head (x - y) w = incoming_flow head x w - incoming_flow head y w := by
  have hneg :
      incoming_flow head (-y) w = -incoming_flow head y w := by
    simpa using (incomingFlow_smul head (-1 : ℝ) y w)
  calc
    incoming_flow head (x - y) w = incoming_flow head x w + incoming_flow head (-y) w := by
      simpa [sub_eq_add_neg] using (incomingFlow_add head x (-y) w)
    _ = incoming_flow head x w - incoming_flow head y w := by rw [hneg, sub_eq_add_neg]

/-- Helper for Remark 4.12: `outgoing_flow` commutes with subtraction of arc vectors. -/
private theorem outgoingFlow_sub
    (tail : A → V) (x y : A → ℝ) (w : V) :
    outgoing_flow tail (x - y) w = outgoing_flow tail x w - outgoing_flow tail y w := by
  have hneg :
      outgoing_flow tail (-y) w = -outgoing_flow tail y w := by
    simpa using (outgoingFlow_smul tail (-1 : ℝ) y w)
  calc
    outgoing_flow tail (x - y) w = outgoing_flow tail x w + outgoing_flow tail (-y) w := by
      simpa [sub_eq_add_neg] using (outgoingFlow_add tail x (-y) w)
    _ = outgoing_flow tail x w - outgoing_flow tail y w := by rw [hneg, sub_eq_add_neg]

/-- Helper for Remark 4.12: nonnegative arc values give a nonnegative incoming-flow total at every
vertex. -/
private theorem incomingFlow_nonneg
    (head : A → V) {x : A → ℝ}
    (hxnonneg : ∀ a, 0 ≤ x a) (w : V) :
    0 ≤ incoming_flow head x w := by
  rw [incoming_flow_eq_sum_incoming_arcs]
  exact Finset.sum_nonneg fun a _ ↦ hxnonneg a

/-- Helper for Remark 4.12: nonnegative arc values give a nonnegative outgoing-flow total at every
vertex. -/
private theorem outgoingFlow_nonneg
    (tail : A → V) {x : A → ℝ}
    (hxnonneg : ∀ a, 0 ≤ x a) (w : V) :
    0 ≤ outgoing_flow tail x w := by
  rw [outgoing_flow_eq_sum_outgoing_arcs]
  exact Finset.sum_nonneg fun a _ ↦ hxnonneg a

/-- Helper for Remark 4.12: a positive sum of nonnegative terms contains a positive summand. -/
private theorem exists_pos_of_sum_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ)
    (hnonneg : ∀ i ∈ s, 0 ≤ f i)
    (hsum : 0 < s.sum f) :
    ∃ i ∈ s, 0 < f i := by
  by_contra h
  have hnonpos : ∀ i ∈ s, f i ≤ 0 := by
    intro i hi
    by_contra hpos
    exact h ⟨i, hi, lt_of_not_ge hpos⟩
  have hzero : ∀ i ∈ s, f i = 0 := by
    intro i hi
    linarith [hnonneg i hi, hnonpos i hi]
  have hsum_zero : s.sum f = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    exact hzero i hi
  linarith

/-- Helper for Remark 4.12: a positive incoming-flow total is witnessed by a positive incoming
arc. -/
private theorem exists_positive_incoming_arc_of_incomingFlow_pos
    (P : ShortestPathLinearProgram V A) {x : A → ℝ} {v : V}
    (hxnonneg : ∀ a, 0 ≤ x a)
    (hin : 0 < incoming_flow P.head x v) :
    ∃ a ∈ incoming_arcs P.head v, 0 < x a := by
  rw [incoming_flow_eq_sum_incoming_arcs] at hin
  exact exists_pos_of_sum_pos (incoming_arcs P.head v) x (fun a _ ↦ hxnonneg a) hin

/-- Helper for Remark 4.12: a positive outgoing-flow total is witnessed by a positive outgoing
arc. -/
private theorem exists_positive_outgoing_arc_of_outgoingFlow_pos
    (P : ShortestPathLinearProgram V A) {x : A → ℝ} {v : V}
    (hxnonneg : ∀ a, 0 ≤ x a)
    (hout : 0 < outgoing_flow P.tail x v) :
    ∃ a ∈ outgoing_arcs P.tail v, 0 < x a := by
  rw [outgoing_flow_eq_sum_outgoing_arcs] at hout
  exact exists_pos_of_sum_pos (outgoing_arcs P.tail v) x (fun a _ ↦ hxnonneg a) hout

/-- Helper for Remark 4.12: a positive incoming arc forces strictly positive incoming flow. -/
private theorem incomingFlow_pos_of_exists_positive_arc
    (P : ShortestPathLinearProgram V A) {x : A → ℝ} {v : V}
    (hxnonneg : ∀ a, 0 ≤ x a)
    (hin : ∃ a ∈ incoming_arcs P.head v, 0 < x a) :
    0 < incoming_flow P.head x v := by
  rcases hin with ⟨a, ha, hxa⟩
  rw [incoming_flow_eq_sum_incoming_arcs]
  have hle : x a ≤ (incoming_arcs P.head v).sum x := by
    exact Finset.single_le_sum (fun b hb ↦ hxnonneg b) ha
  exact lt_of_lt_of_le hxa hle

/-- Helper for Remark 4.12: a positive outgoing arc forces strictly positive outgoing flow. -/
private theorem outgoingFlow_pos_of_exists_positive_arc
    (P : ShortestPathLinearProgram V A) {x : A → ℝ} {v : V}
    (hxnonneg : ∀ a, 0 ≤ x a)
    (hout : ∃ a ∈ outgoing_arcs P.tail v, 0 < x a) :
    0 < outgoing_flow P.tail x v := by
  rcases hout with ⟨a, ha, hxa⟩
  rw [outgoing_flow_eq_sum_outgoing_arcs]
  have hle : x a ≤ (outgoing_arcs P.tail v).sum x := by
    exact Finset.single_le_sum (fun b hb ↦ hxnonneg b) ha
  exact lt_of_lt_of_le hxa hle

/-- Helper for Remark 4.12: every feasible unit flow has a positive outgoing arc at the source. -/
private theorem exists_positive_outgoing_arc_at_source
    (P : ShortestPathLinearProgram V A) {x : A → ℝ}
    (hx : P.IsFeasible x) :
    ∃ a ∈ outgoing_arcs P.tail P.s, 0 < x a := by
  rcases hx with ⟨hxflow, hxvalue⟩
  have hin_nonneg :
      0 ≤ incoming_flow P.head x P.s :=
    incomingFlow_nonneg P.head hxflow.nonneg P.s
  have hout_pos :
      0 < outgoing_flow P.tail x P.s := by
    -- The source value equation is `outgoing - incoming = 1`.
    unfold st_flow_value at hxvalue
    linarith
  exact exists_positive_outgoing_arc_of_outgoingFlow_pos P hxflow.nonneg hout_pos

/-- Helper for Remark 4.12: every feasible unit flow has a positive incoming arc at the sink. -/
private theorem exists_positive_incoming_arc_at_sink
    (P : ShortestPathLinearProgram V A) {x : A → ℝ}
    (hx : P.IsFeasible x) :
    ∃ a ∈ incoming_arcs P.head P.t, 0 < x a := by
  rcases hx with ⟨hxflow, hxvalue⟩
  have hout_nonneg :
      0 ≤ outgoing_flow P.tail x P.t :=
    outgoingFlow_nonneg P.tail hxflow.nonneg P.t
  have hin_pos :
      0 < incoming_flow P.head x P.t := by
    -- The sink balance identity is the same unit value written with opposite sign convention.
    have hsink :
        st_flow_value P.tail P.head P.s x =
          incoming_flow P.head x P.t - outgoing_flow P.tail x P.t :=
      st_flow_value_eq_sink_balance hxflow
    linarith
  exact exists_positive_incoming_arc_of_incomingFlow_pos P hxflow.nonneg hin_pos

/-- Helper for Remark 4.12: once positive flow reaches an internal vertex, conservation forces a
positive outgoing arc there as well. -/
private theorem exists_positive_outgoing_arc_of_positive_incoming
    (P : ShortestPathLinearProgram V A) {x : A → ℝ}
    (hx : P.IsFeasible x) {v : V}
    (hvs : v ≠ P.s) (hvt : v ≠ P.t)
    (hin : ∃ a ∈ incoming_arcs P.head v, 0 < x a) :
    ∃ a ∈ outgoing_arcs P.tail v, 0 < x a := by
  rcases hx with ⟨hxflow, hxvalue⟩
  have hin_pos :
      0 < incoming_flow P.head x v :=
    incomingFlow_pos_of_exists_positive_arc P hxflow.nonneg hin
  have hout_pos :
      0 < outgoing_flow P.tail x v := by
    -- At internal vertices, feasibility identifies incoming and outgoing flow.
    rw [← hxflow.conservation v hvs hvt]
    exact hin_pos
  exact exists_positive_outgoing_arc_of_outgoingFlow_pos P hxflow.nonneg hout_pos

/-- Helper for Remark 4.12: the objective of a walk multiplicity vector is exactly the total
length of the walk. -/
private theorem objective_walkArcVector_eq_pathLength
    (P : ShortestPathLinearProgram V A) :
    ∀ p : List A, P.objective (walkArcVector p) = P.pathLength p
  | [] => by
      -- The empty walk contributes zero objective and zero path length.
      simp [ShortestPathLinearProgram.objective, ShortestPathLinearProgram.pathLength, walkArcVector]
  | a :: p => by
      classical
      -- Split off the first-arc contribution and apply the induction hypothesis to the tail walk.
      rw [ShortestPathLinearProgram.objective, ShortestPathLinearProgram.pathLength, walkArcVector]
      simp only [List.map_cons, List.sum_cons]
      calc
        ∑ b, P.length b * ((if b = a then 1 else 0) + walkArcVector p b)
            = ∑ b, (P.length b * (if b = a then 1 else 0) +
                P.length b * walkArcVector p b) := by
                  refine Finset.sum_congr rfl ?_
                  intro b hb
                  ring
        _ = (∑ b, P.length b * (if b = a then 1 else 0)) +
              ∑ b, P.length b * walkArcVector p b := by
                rw [Finset.sum_add_distrib]
        _ = P.length a + ∑ b, P.length b * walkArcVector p b := by
              simp
        _ = P.length a + P.pathLength p := by
              have ih := objective_walkArcVector_eq_pathLength (P := P) p
              simpa [ShortestPathLinearProgram.objective] using
                congrArg (fun r ↦ P.length a + r) ih

/-- Helper for Remark 4.12: adding a scalar multiple of a closed-walk multiplicity vector changes
the objective by that scalar times the walk length. -/
private theorem objective_add_smul_walkArcVector
    (P : ShortestPathLinearProgram V A) (x : A → ℝ) (μ : ℝ) (p : List A) :
    P.objective (x + μ • walkArcVector p) =
      P.objective x + μ * P.pathLength p := by
  -- Expand the objective coordinatewise and factor out the scalar contribution.
  unfold ShortestPathLinearProgram.objective
  calc
    ∑ a, P.length a * (x a + (μ • walkArcVector p) a)
        = ∑ a, (P.length a * x a + μ * (P.length a * walkArcVector p a)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [Pi.smul_apply]
            ring
    _ = (∑ a, P.length a * x a) + ∑ a, μ * (P.length a * walkArcVector p a) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ a, P.length a * x a) + μ * ∑ a, P.length a * walkArcVector p a := by
          rw [← Finset.mul_sum]
    _ = (∑ a, P.length a * x a) + μ * P.pathLength p := by
          have hwalk :
              ∑ a, P.length a * walkArcVector p a = P.pathLength p := by
            simpa [ShortestPathLinearProgram.objective] using
              objective_walkArcVector_eq_pathLength (P := P) p
          rw [hwalk]
    _ = P.objective x + μ * P.pathLength p := by
          rfl

/-- Helper for Remark 4.12: the shortest-path objective is linear with respect to scalar
multiplication of arc vectors. -/
private theorem objective_smul
    (P : ShortestPathLinearProgram V A) (μ : ℝ) (x : A → ℝ) :
    P.objective (μ • x) = μ * P.objective x := by
  unfold ShortestPathLinearProgram.objective
  calc
    ∑ a, P.length a * (μ * x a) = ∑ a, μ * (P.length a * x a) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      ring
    _ = μ * ∑ a, P.length a * x a := by rw [Finset.mul_sum]

/-- Helper for Remark 4.12: the finite set of vertices consisting of the source, sink, and all
endpoints of arcs of `P`. -/
private noncomputable def relevantVertices (P : ShortestPathLinearProgram V A) : Finset V :=
  insert P.s (insert P.t (circuit_vertices P.tail P.head Finset.univ))

/-- Helper for Remark 4.12: every tail endpoint of an arc of `P` belongs to `P.relevantVertices`.
-/
private theorem tail_mem_relevantVertices
    (P : ShortestPathLinearProgram V A) (a : A) :
    P.tail a ∈ relevantVertices P := by
  classical
  simp [relevantVertices, circuit_vertices]

/-- Helper for Remark 4.12: every head endpoint of an arc of `P` belongs to `P.relevantVertices`.
-/
private theorem head_mem_relevantVertices
    (P : ShortestPathLinearProgram V A) (a : A) :
    P.head a ∈ relevantVertices P := by
  classical
  simp [relevantVertices, circuit_vertices]

/-- Helper for Remark 4.12: a directed walk started inside `P.relevantVertices` never leaves that
finite vertex set. -/
private theorem mem_relevantVertices_of_mem_walkVerticesFrom
    (P : ShortestPathLinearProgram V A) :
    ∀ {u v : V} {p : List A},
      u ∈ relevantVertices P →
        P.IsDirectedWalkFromTo u v p →
          ∀ w ∈ P.walkVerticesFrom u p, w ∈ relevantVertices P
  | u, v, [], hu, hp, w, hw => by
      -- The empty walk only visits its starting vertex.
      simp [ShortestPathLinearProgram.walkVerticesFrom] at hw
      simpa [hw] using hu
  | u, v, a :: p, hu, hp, w, hw => by
      rcases hp with ⟨htail, hpTail⟩
      -- The recursive walk either stays at the current vertex or moves to the head of the first
      -- arc, which is again relevant.
      simp [ShortestPathLinearProgram.walkVerticesFrom] at hw
      rcases hw with rfl | hwTail
      · exact hu
      · exact
          mem_relevantVertices_of_mem_walkVerticesFrom P
            (head_mem_relevantVertices P a) hpTail w hwTail

/-- Helper for Remark 4.12: a simple directed walk has length at most the cardinality of the
global finite vertex set of `P`. -/
private theorem walkVerticesFrom_length_le_relevantVertices_card
    (P : ShortestPathLinearProgram V A)
    {u v : V} {p : List A}
    (hu : u ∈ relevantVertices P)
    (hp : P.IsDirectedWalkFromTo u v p)
    (hnodup : (P.walkVerticesFrom u p).Nodup) :
    (P.walkVerticesFrom u p).length ≤ (relevantVertices P).card := by
  have hsubset :
      (P.walkVerticesFrom u p).toFinset ⊆ relevantVertices P := by
    intro w hw
    exact mem_relevantVertices_of_mem_walkVerticesFrom P hu hp w (List.mem_toFinset.mp hw)
  have hcard : (P.walkVerticesFrom u p).toFinset.card ≤ (relevantVertices P).card :=
    Finset.card_le_card hsubset
  have htoFinset :
      (P.walkVerticesFrom u p).toFinset.card = (P.walkVerticesFrom u p).length := by
    simpa using List.toFinset_card_of_nodup hnodup
  rw [← htoFinset]
  exact hcard

/-- Helper for Remark 4.12: every arc occurring in a directed walk contributes its tail vertex to
the visited-vertex list of that walk. -/
private theorem tail_mem_walkVerticesFrom_of_mem
    (P : ShortestPathLinearProgram V A) :
    ∀ {u v : V} {p : List A}, P.IsDirectedWalkFromTo u v p →
      ∀ {a : A}, a ∈ p → P.tail a ∈ P.walkVerticesFrom u p
  | _, _, [], hwalk, _, hmem => by
      cases hmem
  | u, v, b :: p, hwalk, a, hmem => by
      rcases hwalk with ⟨hbu, hp⟩
      -- Split according to whether the requested arc is the first arc or lies in the tail walk.
      rw [ShortestPathLinearProgram.walkVerticesFrom]
      rcases List.mem_cons.mp hmem with rfl | hmemTail
      · simp [hbu]
      · exact List.mem_cons_of_mem _ (tail_mem_walkVerticesFrom_of_mem P hp hmemTail)

/-- Helper for Remark 4.12: a directed walk with no repeated visited vertices cannot reuse an
arc, because reusing an arc would repeat its tail vertex. -/
private theorem directedWalk_nodup_of_verticesNodup
    (P : ShortestPathLinearProgram V A) :
    ∀ {u v : V} {p : List A}, P.IsDirectedWalkFromTo u v p →
      (P.walkVerticesFrom u p).Nodup → p.Nodup
  | _, _, [], hwalk, hverts => by
      simp
  | u, v, a :: p, hwalk, hverts => by
      rcases hwalk with ⟨hau, hp⟩
      rw [ShortestPathLinearProgram.walkVerticesFrom] at hverts
      rcases List.nodup_cons.mp hverts with ⟨hu_not_mem, htailVerts⟩
      have hpNodup := directedWalk_nodup_of_verticesNodup P hp htailVerts
      have ha_not_mem : a ∉ p := by
        intro hmem
        -- Reusing `a` would place its tail `u` later in the vertex list, contradicting nodup.
        have htailMem : P.tail a ∈ P.walkVerticesFrom (P.head a) p :=
          tail_mem_walkVerticesFrom_of_mem P hp hmem
        have huMem : u ∈ P.walkVerticesFrom (P.head a) p := by
          simpa [hau] using htailMem
        exact hu_not_mem huMem
      exact List.nodup_cons.mpr ⟨ha_not_mem, hpNodup⟩

/-- Helper for Remark 4.12: the visited-vertex list is the start vertex followed by the head
endpoints of the traversed arcs. -/
private theorem walkVerticesFrom_eq_start_cons_map_head
    (P : ShortestPathLinearProgram V A) :
    ∀ (u : V) (p : List A), P.walkVerticesFrom u p = u :: p.map P.head
  | _, [] => by
      -- The empty walk visits only its starting vertex.
      simp [ShortestPathLinearProgram.walkVerticesFrom]
  | _, a :: p => by
      -- Unfold one step and reuse the recursive description of the tail walk.
      simp [ShortestPathLinearProgram.walkVerticesFrom,
        walkVerticesFrom_eq_start_cons_map_head P (P.head a) p]

/-- Helper for Remark 4.12: the tail of the visited-vertex list is the list of head endpoints of
the traversed arcs. -/
private theorem walkVerticesFrom_tail_eq_map_head
    (P : ShortestPathLinearProgram V A) :
    ∀ (u : V) (p : List A), (P.walkVerticesFrom u p).tail = p.map P.head
  | u, p => by
      -- Read the whole visited-vertex list in the normalized `start :: heads` form.
      simpa [walkVerticesFrom_eq_start_cons_map_head]

/-- Helper for Remark 4.12: concatenating two directed walks with matching intermediate endpoint
produces the obvious longer directed walk. -/
private theorem directedWalk_append
    (P : ShortestPathLinearProgram V A) :
    ∀ {u w v : V} {p q : List A},
      P.IsDirectedWalkFromTo u w p →
        P.IsDirectedWalkFromTo w v q →
          P.IsDirectedWalkFromTo u v (p ++ q)
  | _, _, _, [], q, hp, hq => by
      -- The empty prefix contributes no arcs, so the suffix walk is already the whole walk.
      subst hp
      simpa using hq
  | u, w, v, a :: p, q, hp, hq => by
      rcases hp with ⟨hau, hpTail⟩
      -- Keep the first arc and append the suffix recursively to the tail walk.
      refine ⟨hau, directedWalk_append P hpTail hq⟩

/-- Helper for Remark 4.12: if a directed walk from `u` to `v` visits `w`, then the arc list
splits into a prefix walk from `u` to `w` and a suffix walk from `w` to `v`. -/
private theorem directedWalk_split_at_visited_vertex
    (P : ShortestPathLinearProgram V A) :
    ∀ {u v w : V} {p : List A}, P.IsDirectedWalkFromTo u v p →
      w ∈ P.walkVerticesFrom u p →
        ∃ p₁ p₂, p = p₁ ++ p₂ ∧
          P.IsDirectedWalkFromTo u w p₁ ∧
            P.IsDirectedWalkFromTo w v p₂
  | u, v, w, [], hp, hw => by
      subst hp
      have hwu : w = u := by
        simpa [ShortestPathLinearProgram.walkVerticesFrom] using hw
      subst hwu
      -- The only visited vertex of the empty walk is its start/end point.
      refine ⟨[], [], rfl, rfl, rfl⟩
  | u, v, w, a :: p, hp, hw => by
      rcases hp with ⟨hau, hpTail⟩
      rw [ShortestPathLinearProgram.walkVerticesFrom] at hw
      rcases List.mem_cons.1 hw with rfl | hwTail
      · -- Splitting at the starting vertex leaves the whole walk in the suffix.
        refine ⟨[], a :: p, by simp, rfl, ?_⟩
        exact ⟨hau, hpTail⟩
      · rcases directedWalk_split_at_visited_vertex P hpTail hwTail with
          ⟨p₁, p₂, hpSplit, hp₁, hp₂⟩
        -- Otherwise split the tail walk recursively and restore the leading arc.
        refine ⟨a :: p₁, p₂, ?_, ?_, hp₂⟩
        · simp [hpSplit]
        · refine ⟨hau, ?_⟩
          simpa [hpSplit] using hp₁

/-- Helper for Remark 4.12: visited vertices of concatenated directed walks are obtained by
concatenating the visited vertices of the prefix and the tail of the visited vertices of the
suffix. -/
private theorem walkVerticesFrom_append
    (P : ShortestPathLinearProgram V A) :
    ∀ {u w v : V} {p q : List A},
      P.IsDirectedWalkFromTo u w p →
        P.IsDirectedWalkFromTo w v q →
          P.walkVerticesFrom u (p ++ q) =
            P.walkVerticesFrom u p ++ (P.walkVerticesFrom w q).tail
  | _, _, _, [], q, hp, hq => by
      subst hp
      -- The empty prefix contributes only the initial vertex of the suffix walk.
      cases q with
      | nil =>
          simp [ShortestPathLinearProgram.walkVerticesFrom]
      | cons a q =>
          simp [ShortestPathLinearProgram.walkVerticesFrom]
  | u, w, v, a :: p, q, hp, hq => by
      rcases hp with ⟨hau, hpTail⟩
      -- Peel the first arc and apply the append formula recursively to the tail walk.
      simp [ShortestPathLinearProgram.walkVerticesFrom, walkVerticesFrom_append P hpTail hq]

/-- Helper for Remark 4.12: every walk visits exactly one more vertex than the number of arcs it
contains. -/
private theorem walkVerticesFrom_length
    (P : ShortestPathLinearProgram V A) :
    ∀ (u : V) (p : List A), (P.walkVerticesFrom u p).length = p.length + 1
  | _, [] => by
      simp [ShortestPathLinearProgram.walkVerticesFrom]
  | u, a :: p => by
      -- Each additional arc adds exactly one more visited vertex.
      simp [ShortestPathLinearProgram.walkVerticesFrom, walkVerticesFrom_length P (P.head a) p]

/-- Helper for Remark 4.12: the endpoint of a directed walk always appears in its visited-vertex
list. -/
private theorem terminalVertex_mem_walkVerticesFrom
    (P : ShortestPathLinearProgram V A) :
    ∀ {u v : V} {p : List A}, P.IsDirectedWalkFromTo u v p →
      v ∈ P.walkVerticesFrom u p
  | _, _, [], hp => by
      subst hp
      -- The empty walk visits only its start/end vertex.
      simp [ShortestPathLinearProgram.walkVerticesFrom]
  | u, v, a :: p, hp => by
      rcases hp with ⟨hau, hpTail⟩
      -- The endpoint of the tail walk is still the endpoint of the whole walk.
      simp [ShortestPathLinearProgram.walkVerticesFrom,
        terminalVertex_mem_walkVerticesFrom P hpTail]

/-- Helper for Remark 4.12: a nonempty directed walk with no repeated visited vertices cannot end
where it started. -/
private theorem directedWalk_endpoint_ne_start_of_verticesNodup
    (P : ShortestPathLinearProgram V A) :
    ∀ {u v : V} {p : List A}, P.IsDirectedWalkFromTo u v p →
      p ≠ [] →
        (P.walkVerticesFrom u p).Nodup →
          v ≠ u
  | _, _, [], hp, hne, _ => by
      exact False.elim (hne rfl)
  | u, v, a :: p, hp, _, hverts => by
      rcases hp with ⟨hau, hpTail⟩
      rw [ShortestPathLinearProgram.walkVerticesFrom] at hverts
      rcases List.nodup_cons.mp hverts with ⟨hu_not_mem, _⟩
      intro hvu
      -- If the endpoint returned to the start, the tail walk would revisit the starting vertex.
      exact hu_not_mem (by simpa [hau, hvu] using terminalVertex_mem_walkVerticesFrom P hpTail)

/-- Helper for Remark 4.12: a nonempty positive directed walk has a positive incoming arc at its
endpoint. -/
private theorem exists_positive_incoming_arc_at_walkEndpoint
    (P : ShortestPathLinearProgram V A) {y : A → ℝ} :
    ∀ {u v : V} {p : List A}, P.IsDirectedWalkFromTo u v p →
      p ≠ [] →
        (∀ b ∈ p.toFinset, 0 < y b) →
          ∃ a ∈ incoming_arcs P.head v, 0 < y a
  | _, _, [], hp, hne, _ => by
      exact False.elim (hne rfl)
  | u, v, a :: p, hp, _, hpos => by
      rcases hp with ⟨hau, hpTail⟩
      by_cases hpnil : p = []
      · subst hpnil
        refine ⟨a, ?_, ?_⟩
        · simpa [mem_incoming_arcs_iff] using hpTail
        · exact hpos a (by simp)
      · have hposTail : ∀ b ∈ p.toFinset, 0 < y b := by
          intro b hb
          exact hpos b (by simpa using List.mem_cons_of_mem a (by simpa using hb))
        exact exists_positive_incoming_arc_at_walkEndpoint P hpTail hpnil hposTail

/-- Helper for Remark 4.12: if a positive directed walk tries to revisit an earlier vertex via one
more positive arc, the repeated-vertex suffix closes up to a positive directed circuit. -/
private theorem positiveWalkRepeatedVertex_yieldsCircuitSuffix
    (P : ShortestPathLinearProgram V A) {y : A → ℝ}
    {u : V} {p : List A} {a : A}
    (hp : P.IsDirectedWalkFromTo P.s u p)
    (hnodup : (P.walkVerticesFrom P.s p).Nodup)
    (hposp : ∀ b ∈ p.toFinset, 0 < y b)
    (htail : P.tail a = u)
    (hposa : 0 < y a)
    (hhead : P.head a ∈ P.walkVerticesFrom P.s p) :
    ∃ c : List A, P.IsCircuit c ∧ ∀ b ∈ c.toFinset, 0 < y b := by
  rcases directedWalk_split_at_visited_vertex P hp hhead with
    ⟨p₁, p₂, rfl, hp₁, hp₂⟩
  let w := P.head a
  let c : List A := p₂ ++ [a]
  have hsingle : P.IsDirectedWalkFromTo u w [a] := by
    -- The closing arc is a one-step directed walk from the current endpoint back to the repeated
    -- vertex.
    refine ⟨htail, rfl⟩
  have hwalkc : P.IsDirectedWalkFromTo w w c := by
    -- Appending the closing arc turns the suffix into a closed walk.
    simpa [c] using directedWalk_append P hp₂ hsingle
  have hsplitVertices :
      P.walkVerticesFrom P.s (p₁ ++ p₂) =
        P.walkVerticesFrom P.s p₁ ++ (P.walkVerticesFrom w p₂).tail := by
    simpa [w] using walkVerticesFrom_append P hp₁ hp₂
  have htailNodup : (P.walkVerticesFrom w p₂).tail.Nodup := by
    -- The suffix tail inherits nodup from the original walk after splitting at the repeated
    -- vertex.
    have happendNodup :
        (P.walkVerticesFrom P.s p₁ ++ (P.walkVerticesFrom w p₂).tail).Nodup := by
      simpa [hsplitVertices] using hnodup
    exact List.Nodup.of_append_right happendNodup
  have hw_mem_prefix : w ∈ P.walkVerticesFrom P.s p₁ :=
    terminalVertex_mem_walkVerticesFrom P hp₁
  have hw_not_mem_suffixTail : w ∉ (P.walkVerticesFrom w p₂).tail := by
    have happendNodup :
        (P.walkVerticesFrom P.s p₁ ++ (P.walkVerticesFrom w p₂).tail).Nodup := by
      simpa [hsplitVertices] using hnodup
    have hdisj :
        List.Disjoint (P.walkVerticesFrom P.s p₁) ((P.walkVerticesFrom w p₂).tail) :=
      List.disjoint_of_nodup_append happendNodup
    exact fun hwTail ↦ (List.disjoint_left.1 hdisj hw_mem_prefix hwTail)
  have hcTailNodup : (P.walkVerticesFrom w c).tail.Nodup := by
    have hvertices_c :
        P.walkVerticesFrom w c = P.walkVerticesFrom w p₂ ++ [w] := by
      -- The closing one-arc walk contributes the repeated basepoint as the final visited vertex.
      have happ := walkVerticesFrom_append P hp₂ hsingle
      simpa [c, ShortestPathLinearProgram.walkVerticesFrom, w, htail] using happ
    have htail_append :
        (P.walkVerticesFrom w c).tail = (P.walkVerticesFrom w p₂).tail ++ [w] := by
      -- Since `P.walkVerticesFrom w p₂` always starts with `w`, taking the tail removes only that
      -- first visit.
      cases p₂ with
      | nil =>
          simp [hvertices_c, ShortestPathLinearProgram.walkVerticesFrom, c, w]
      | cons b p₂ =>
          simp [hvertices_c, ShortestPathLinearProgram.walkVerticesFrom]
    have hdisjTail : List.Disjoint (P.walkVerticesFrom w p₂).tail [w] := by
      refine List.disjoint_left.2 ?_
      intro x hx hxw
      simp at hxw
      subst hxw
      exact hw_not_mem_suffixTail hx
    have hnodupTailAppend :
        ((P.walkVerticesFrom w p₂).tail ++ [w]).Nodup :=
      List.Nodup.append htailNodup (by simp) hdisjTail
    simpa [htail_append] using hnodupTailAppend
  refine ⟨c, ?_, ?_⟩
  · refine ⟨by simp [c], ?_⟩
    refine ⟨w, hwalkc, hcTailNodup⟩
  · intro b hb
    have hbList : b ∈ c := (List.mem_toFinset.mp hb)
    change b ∈ p₂ ++ [a] at hbList
    rcases List.mem_append.mp hbList with hb₂ | hbA
    · exact hposp b (by simpa using List.mem_append.mpr (Or.inr hb₂))
    · have hbEq : b = a := by simpa using hbA
      subst hbEq
      exact hposa

/-- Helper for Remark 4.12: every feasible unit flow contains either a positive directed circuit
or a positive simple `s,t`-path in its support. -/
private theorem positiveSupportPathOrCircuit
    (P : ShortestPathLinearProgram V A) {y : A → ℝ}
    (hy : P.IsFeasible y) :
    (∃ c : List A, P.IsCircuit c ∧ ∀ a ∈ c.toFinset, 0 < y a) ∨
      ∃ p : List A, P.IsStPath p ∧ ∀ a ∈ p.toFinset, 0 < y a := by
  classical
  rcases exists_positive_outgoing_arc_at_source P hy with ⟨a₀, ha₀out, hya₀⟩
  have htail₀ : P.tail a₀ = P.s := by
    simpa [mem_outgoing_arcs_iff] using ha₀out
  by_cases hloop : P.head a₀ = P.s
  · left
    refine ⟨[a₀], ?_, ?_⟩
    · refine ⟨by simp, ?_⟩
      refine ⟨P.s, ?_, ?_⟩
      · exact ⟨htail₀, hloop⟩
      · simp [ShortestPathLinearProgram.walkVerticesFrom, hloop]
    · intro b hb
      have hb' : b = a₀ := by simpa using hb
      simpa [hb'] using hya₀
  · let S : Set (List A) :=
      {p | ∃ u, P.IsDirectedWalkFromTo P.s u p ∧
          (P.walkVerticesFrom P.s p).Nodup ∧
          ∀ b ∈ p.toFinset, 0 < y b}
    have hSfinite : S.Finite := by
      refine (List.finite_length_le A (relevantVertices P).card).subset ?_
      intro p hpS
      rcases hpS with ⟨u, hwalk, hnodup, _⟩
      have hverts_card :
          (P.walkVerticesFrom P.s p).length ≤ (relevantVertices P).card :=
        walkVerticesFrom_length_le_relevantVertices_card P (by simp [relevantVertices]) hwalk
          hnodup
      have hverts_len :
          (P.walkVerticesFrom P.s p).length = p.length + 1 :=
        walkVerticesFrom_length P P.s p
      have hsucc : p.length + 1 ≤ (relevantVertices P).card := by
        simpa [hverts_len] using hverts_card
      exact Nat.le_trans (Nat.le_succ p.length) hsucc
    have ha₀_in_S : [a₀] ∈ S := by
      refine ⟨P.head a₀, ?_, ?_, ?_⟩
      · refine ⟨htail₀, rfl⟩
      · -- The initial positive arc is simple because it does not return to the source.
        simpa [ShortestPathLinearProgram.walkVerticesFrom] using
          (List.nodup_cons.2
            ⟨by simpa [List.mem_singleton, eq_comm] using hloop, List.nodup_singleton _⟩)
      · intro b hb
        have hb' : b = a₀ := by simpa using hb
        simpa [hb'] using hya₀
    have hSnonempty : S.Nonempty := ⟨[a₀], ha₀_in_S⟩
    rcases Set.exists_max_image S List.length hSfinite hSnonempty with ⟨p, hpS, hpmax⟩
    rcases hpS with ⟨u, hwalk, hnodup, hpos⟩
    by_cases hut : u = P.t
    · right
      refine ⟨p, ?_, hpos⟩
      exact ⟨by simpa [hut] using hwalk, hnodup⟩
    · have hp_nonempty : p ≠ [] := by
        have hmax₀ := hpmax [a₀] ha₀_in_S
        intro hpnil
        simpa [hpnil] using hmax₀
      have hus : u ≠ P.s :=
        directedWalk_endpoint_ne_start_of_verticesNodup P hwalk hp_nonempty hnodup
      have hin :
          ∃ a ∈ incoming_arcs P.head u, 0 < y a :=
        exists_positive_incoming_arc_at_walkEndpoint P hwalk hp_nonempty hpos
      rcases exists_positive_outgoing_arc_of_positive_incoming P hy hus hut hin with
        ⟨a, haout, hya⟩
      have htail : P.tail a = u := by
        simpa [mem_outgoing_arcs_iff] using haout
      by_cases hvisited : P.head a ∈ P.walkVerticesFrom P.s p
      · left
        exact positiveWalkRepeatedVertex_yieldsCircuitSuffix P hwalk hnodup hpos htail hya
          hvisited
      · have hsingle : P.IsDirectedWalkFromTo u (P.head a) [a] := by
          refine ⟨htail, rfl⟩
        have hwalk' : P.IsDirectedWalkFromTo P.s (P.head a) (p ++ [a]) := by
          exact directedWalk_append P hwalk hsingle
        have hvertices' :
            P.walkVerticesFrom P.s (p ++ [a]) =
              P.walkVerticesFrom P.s p ++ [P.head a] := by
          have happ := walkVerticesFrom_append P hwalk hsingle
          simpa [ShortestPathLinearProgram.walkVerticesFrom, htail] using happ
        have hnodup' : (P.walkVerticesFrom P.s (p ++ [a])).Nodup := by
          rw [hvertices']
          refine List.Nodup.append hnodup (by simp) ?_
          refine List.disjoint_left.2 ?_
          intro x hx hxlast
          simp at hxlast
          subst hxlast
          exact hvisited hx
        have hpos' : ∀ b ∈ (p ++ [a]).toFinset, 0 < y b := by
          intro b hb
          have hb' : b ∈ p ++ [a] := List.mem_toFinset.mp hb
          rcases List.mem_append.mp hb' with hb | hb
          · exact hpos b (by simpa using hb)
          · have hbEq : b = a := by simpa using hb
            subst hbEq
            exact hya
        have hpS' : p ++ [a] ∈ S := by
          exact ⟨P.head a, hwalk', hnodup', hpos'⟩
        have hle := hpmax (p ++ [a]) hpS'
        exact False.elim (Nat.not_succ_le_self p.length (by simpa using hle))

/-- Helper for Remark 4.12: in a nonnegative circulation, a positive incoming arc at a vertex
forces a positive outgoing arc there as well. -/
private theorem exists_positive_outgoing_arc_of_positive_incoming_circulation
    (P : ShortestPathLinearProgram V A) {z : A → ℝ}
    (hz : IsCirculation P.tail P.head z) {v : V}
    (hin : ∃ a ∈ incoming_arcs P.head v, 0 < z a) :
    ∃ a ∈ outgoing_arcs P.tail v, 0 < z a := by
  have hin_pos :
      0 < incoming_flow P.head z v :=
    incomingFlow_pos_of_exists_positive_arc P hz.nonneg hin
  have hout_pos :
      0 < outgoing_flow P.tail z v := by
    -- A circulation has equal incoming and outgoing flow at every vertex.
    rw [← hz.flow_conservation v]
    exact hin_pos
  exact exists_positive_outgoing_arc_of_outgoingFlow_pos P hz.nonneg hout_pos

/-- Helper for Remark 4.12: every nonzero nonnegative circulation contains a positive directed
circuit in its support. -/
private theorem positiveSupportCircuit_of_circulation
    (P : ShortestPathLinearProgram V A) {z : A → ℝ}
    (hz : IsCirculation P.tail P.head z)
    (hpos : ∃ a, 0 < z a) :
    ∃ c : List A, P.IsCircuit c ∧ ∀ a ∈ c.toFinset, 0 < z a := by
  classical
  rcases hpos with ⟨a₀, hza₀⟩
  let P₀ : ShortestPathLinearProgram V A :=
    { tail := P.tail
      head := P.head
      s := P.tail a₀
      t := P.t
      length := P.length }
  have hwalkEq :
      ∀ {u v : V} {p : List A},
        P₀.IsDirectedWalkFromTo u v p ↔ P.IsDirectedWalkFromTo u v p := by
    intro u v p
    induction p generalizing u with
    | nil =>
        simp [ShortestPathLinearProgram.IsDirectedWalkFromTo]
    | cons a p ih =>
        simp [ShortestPathLinearProgram.IsDirectedWalkFromTo, ih, P₀]
  have hverticesEq :
      ∀ (u : V) (p : List A), P₀.walkVerticesFrom u p = P.walkVerticesFrom u p := by
    intro u p
    induction p generalizing u with
    | nil =>
        simp [ShortestPathLinearProgram.walkVerticesFrom]
    | cons a p ih =>
        simp [ShortestPathLinearProgram.walkVerticesFrom, ih, P₀]
  by_cases hloop : P.head a₀ = P.tail a₀
  · refine ⟨[a₀], ?_, ?_⟩
    · refine ⟨by simp, ?_⟩
      refine ⟨P.tail a₀, ?_, ?_⟩
      · exact ⟨rfl, by simpa [ShortestPathLinearProgram.IsDirectedWalkFromTo, hloop]⟩
      · simp [ShortestPathLinearProgram.walkVerticesFrom, hloop]
    · intro a ha
      have ha' : a = a₀ := by simpa using ha
      simpa [ha'] using hza₀
  · let S : Set (List A) :=
      {p | ∃ u, P₀.IsDirectedWalkFromTo P₀.s u p ∧
          (P₀.walkVerticesFrom P₀.s p).Nodup ∧
          ∀ b ∈ p.toFinset, 0 < z b}
    have hSfinite : S.Finite := by
      refine (List.finite_length_le A (relevantVertices P₀).card).subset ?_
      intro p hpS
      rcases hpS with ⟨u, hwalk, hnodup, _⟩
      have hverts_card :
          (P₀.walkVerticesFrom P₀.s p).length ≤ (relevantVertices P₀).card :=
        walkVerticesFrom_length_le_relevantVertices_card P₀
          (by
            -- The circulation-based auxiliary program starts at the tail of the initial positive
            -- arc, which is one of the global arc endpoints.
            simp [P₀, relevantVertices, circuit_vertices])
          hwalk hnodup
      have hverts_len :
          (P₀.walkVerticesFrom P₀.s p).length = p.length + 1 :=
        walkVerticesFrom_length P₀ P₀.s p
      have hsucc : p.length + 1 ≤ (relevantVertices P₀).card := by
        simpa [hverts_len] using hverts_card
      exact Nat.le_trans (Nat.le_succ p.length) hsucc
    have ha₀_in_S : [a₀] ∈ S := by
      refine ⟨P.head a₀, ?_, ?_, ?_⟩
      · exact ⟨rfl, rfl⟩
      · -- The initial positive arc is simple because it does not return to its tail vertex.
        simpa [ShortestPathLinearProgram.walkVerticesFrom] using
          (List.nodup_cons.2
            ⟨by simpa [List.mem_singleton, eq_comm] using hloop, List.nodup_singleton _⟩)
      · intro b hb
        have hb' : b = a₀ := by simpa using hb
        simpa [hb'] using hza₀
    have hSnonempty : S.Nonempty := ⟨[a₀], ha₀_in_S⟩
    rcases Set.exists_max_image S List.length hSfinite hSnonempty with ⟨p, hpS, hpmax⟩
    rcases hpS with ⟨u, hwalk, hnodup, hposp⟩
    have hp_nonempty : p ≠ [] := by
      have hmax₀ := hpmax [a₀] ha₀_in_S
      intro hpnil
      simpa [hpnil] using hmax₀
    have hin :
        ∃ a ∈ incoming_arcs P₀.head u, 0 < z a :=
      exists_positive_incoming_arc_at_walkEndpoint P₀ hwalk hp_nonempty hposp
    rcases exists_positive_outgoing_arc_of_positive_incoming_circulation P hz hin with
      ⟨a, haout, hza⟩
    have htail : P₀.tail a = u := by
      simpa [mem_outgoing_arcs_iff] using haout
    by_cases hvisited : P₀.head a ∈ P₀.walkVerticesFrom P₀.s p
    · have hcycle :=
        positiveWalkRepeatedVertex_yieldsCircuitSuffix P₀ hwalk hnodup hposp htail hza hvisited
      rcases hcycle with ⟨c, hcircuit, hcpos⟩
      refine ⟨c, ?_, hcpos⟩
      rcases hcircuit with ⟨hcne, v, hwalkc, hnodupc⟩
      refine ⟨hcne, v, ?_, ?_⟩
      · exact (hwalkEq.mp hwalkc)
      · simpa [hverticesEq v c] using hnodupc
    · have hsingle : P₀.IsDirectedWalkFromTo u (P₀.head a) [a] := by
        exact ⟨htail, rfl⟩
      have hwalk' : P₀.IsDirectedWalkFromTo P₀.s (P₀.head a) (p ++ [a]) := by
        exact directedWalk_append P₀ hwalk hsingle
      have hvertices' :
          P₀.walkVerticesFrom P₀.s (p ++ [a]) =
            P₀.walkVerticesFrom P₀.s p ++ [P₀.head a] := by
        have happ := walkVerticesFrom_append P₀ hwalk hsingle
        simpa [ShortestPathLinearProgram.walkVerticesFrom, htail] using happ
      have hnodup' : (P₀.walkVerticesFrom P₀.s (p ++ [a])).Nodup := by
        rw [hvertices']
        refine List.Nodup.append hnodup (by simp) ?_
        refine List.disjoint_left.2 ?_
        intro x hx hxlast
        have hxhead : x = P₀.head a := by simpa using hxlast
        subst hxhead
        exact hvisited hx
      have hpos' : ∀ b ∈ (p ++ [a]).toFinset, 0 < z b := by
        intro b hb
        have hb' : b ∈ p ++ [a] := List.mem_toFinset.mp hb
        rcases List.mem_append.mp hb' with hb | hb
        · exact hposp b (by simpa using hb)
        · have hbEq : b = a := by simpa using hb
          subst hbEq
          exact hza
      have hpS' : p ++ [a] ∈ S := by
        exact ⟨P₀.head a, hwalk', hnodup', hpos'⟩
      have hle := hpmax (p ++ [a]) hpS'
      exact False.elim (Nat.not_succ_le_self p.length (by simpa using hle))

/-- Helper for Remark 4.12: the multiplicity vector of a walk with no repeated arcs is the
characteristic vector of its support set. -/
private theorem walkArcVector_eq_characteristic_of_nodup :
    ∀ {p : List A}, p.Nodup → walkArcVector p = circuit_characteristic_vector p.toFinset
  | [], hnodup => by
      ext a
      simp [walkArcVector, circuit_characteristic_vector_apply]
  | b :: p, hnodup => by
      rcases List.nodup_cons.mp hnodup with ⟨hb_not_mem, hpNodup⟩
      have ih := walkArcVector_eq_characteristic_of_nodup hpNodup
      ext a
      -- Compare the recursive multiplicity formula with membership in the deduplicated support.
      by_cases ha : a = b
      · subst ha
        have ihb : walkArcVector p a = 0 := by
          simpa [circuit_characteristic_vector_apply, hb_not_mem] using congrFun ih a
        simp [walkArcVector, circuit_characteristic_vector_apply, hb_not_mem, ihb]
      · simp [walkArcVector, circuit_characteristic_vector_apply, ha, ih]

/-- Helper for Remark 4.12: when `s ≠ t`, the characteristic vector of an `s,t`-path is a
feasible unit flow, and its objective is the path length. -/
private theorem stPathCharacteristic_spec
    (P : ShortestPathLinearProgram V A) {p : List A}
    (hst : P.s ≠ P.t) (hp : P.IsStPath p) :
    P.IsFeasible (circuit_characteristic_vector p.toFinset) ∧
      P.objective (circuit_characteristic_vector p.toFinset) = P.pathLength p := by
  -- Route correction: the unqualified statement is false when `s = t` and `p = []`, so the
  -- source/sink distinctness forced by feasibility must stay explicit in this bridge lemma.
  have hwalkFeasible : P.IsFeasible (walkArcVector p) := by
    refine ⟨?_, ?_⟩
    · refine
        { nonneg := ?_
          conservation := ?_ }
      · intro a
        -- Walk multiplicities are coordinatewise nonnegative.
        exact walkArcVector_nonneg p a
      · intro v hvs hvt
        -- Away from source and sink, the walk has zero endpoint imbalance.
        have hbalance := directedWalk_balance P hp.1 v
        exact sub_eq_zero.mp (by simpa [hvs, hvt] using hbalance)
    · have hsourceBalance := directedWalk_balance P hp.1 P.s
      -- Evaluating the walk imbalance at the source yields unit `s,t`-flow value.
      unfold st_flow_value
      have hsource :
          incoming_flow P.head (walkArcVector p) P.s -
            outgoing_flow P.tail (walkArcVector p) P.s = -1 := by
        simpa [hst] using hsourceBalance
      linarith
  have hnodupArcs :
      p.Nodup :=
    directedWalk_nodup_of_verticesNodup P hp.1 hp.2
  have hcharacteristic :
      walkArcVector p = circuit_characteristic_vector p.toFinset :=
    walkArcVector_eq_characteristic_of_nodup hnodupArcs
  constructor
  · -- Replace the walk multiplicity vector by the path support indicator.
    simpa [hcharacteristic] using hwalkFeasible
  · -- The objective identity follows from the same support-indicator rewrite.
    simpa [hcharacteristic] using objective_walkArcVector_eq_pathLength (P := P) p

/-- Helper for Remark 4.12: once an optimal feasible flow is already known to be the
characteristic vector of an `s,t`-path, optimality immediately upgrades that path to a shortest
`s,t`-path. -/
private theorem isShortestStPath_of_optimal_characteristic
    (P : ShortestPathLinearProgram V A) {x : A → ℝ} {p : List A}
    (hx : P.IsOptimalSolution x)
    (hp : P.IsStPath p)
    (hxeq : x = circuit_characteristic_vector p.toFinset) :
    P.IsShortestStPath p := by
  have hst : P.s ≠ P.t :=
    ShortestPathLinearProgram.IsFeasible.source_ne_sink (P := P) (x := x) hx.1
  refine ⟨hp, ?_⟩
  intro q hq
  have hpSpec := stPathCharacteristic_spec P hst hp
  have hqSpec := stPathCharacteristic_spec P hst hq
  -- Compare the path indicator of `p` against every competing feasible path indicator.
  have hopt := hx.2 (circuit_characteristic_vector q.toFinset) hqSpec.1
  rw [hxeq, hpSpec.2, hqSpec.2] at hopt
  exact hopt

/-- Helper for Remark 4.12: the walk multiplicity vector of a directed circuit is a nonnegative
circulation. This packages the balance algebra needed when peeling a positive circuit from a
circulation or feasible flow. -/
private theorem walkArcVector_isCirculation_of_circuit
    (P : ShortestPathLinearProgram V A) {c : List A}
    (hc : P.IsCircuit c) :
    IsCirculation P.tail P.head (walkArcVector c) := by
  rcases hc with ⟨_, v, hwalk, _⟩
  refine
    { flow_conservation := ?_
      nonneg := ?_ }
  · intro w
    -- A closed walk has zero endpoint imbalance at every vertex.
    have hbalance := directedWalk_balance P hwalk w
    exact sub_eq_zero.mp (by simpa using hbalance)
  · intro a
    -- Walk multiplicities are coordinatewise nonnegative.
    exact walkArcVector_nonneg c a

/-- Helper for Remark 4.12: subtracting the characteristic vector of an `s,t`-path from a
dominating feasible unit flow leaves a nonnegative circulation. This is the exact `μ = 1`
residual used in the path-peeling comparison argument. -/
private theorem feasibleResidual_isCirculation_of_stPathSub
    (P : ShortestPathLinearProgram V A) {y : A → ℝ} {p : List A}
    (hy : P.IsFeasible y)
    (hp : P.IsStPath p)
    (hdom : circuit_characteristic_vector p.toFinset ≤ y) :
    IsCirculation P.tail P.head (y - circuit_characteristic_vector p.toFinset) := by
  have hst : P.s ≠ P.t :=
    ShortestPathLinearProgram.IsFeasible.source_ne_sink (P := P) (x := y) hy
  have hpSpec := stPathCharacteristic_spec P hst hp
  rcases hy with ⟨hyFlow, hyValue⟩
  rcases hpSpec.1 with ⟨hpFlow, hpValue⟩
  refine
    { flow_conservation := ?_
      nonneg := ?_ }
  · intro v
    by_cases hvs : v = P.s
    · subst hvs
      -- The source imbalance of both unit flows is `-1`, so their difference is balanced.
      have hySource :
          incoming_flow P.head y P.s - outgoing_flow P.tail y P.s = -1 := by
        unfold st_flow_value at hyValue
        linarith
      have hpSource :
          incoming_flow P.head (circuit_characteristic_vector p.toFinset) P.s -
            outgoing_flow P.tail (circuit_characteristic_vector p.toFinset) P.s = -1 := by
        unfold st_flow_value at hpValue
        linarith
      calc
        incoming_flow P.head (y - circuit_characteristic_vector p.toFinset) P.s
            = incoming_flow P.head y P.s -
                incoming_flow P.head (circuit_characteristic_vector p.toFinset) P.s := by
                  simp [incoming_flow_eq_sum_incoming_arcs, Finset.sum_sub_distrib]
        _ = outgoing_flow P.tail y P.s -
              outgoing_flow P.tail (circuit_characteristic_vector p.toFinset) P.s := by
                linarith
        _ = outgoing_flow P.tail (y - circuit_characteristic_vector p.toFinset) P.s := by
              simp [outgoing_flow_eq_sum_outgoing_arcs, Finset.sum_sub_distrib]
    · by_cases hvt : v = P.t
      · subst hvt
        -- The sink imbalance of both unit flows is `+1`, so their difference is balanced.
        have hySink :
            incoming_flow P.head y P.t - outgoing_flow P.tail y P.t = 1 := by
          simpa [hyValue] using (st_flow_value_eq_sink_balance hyFlow).symm
        have hpSink :
            incoming_flow P.head (circuit_characteristic_vector p.toFinset) P.t -
              outgoing_flow P.tail (circuit_characteristic_vector p.toFinset) P.t = 1 := by
          simpa [hpValue] using (st_flow_value_eq_sink_balance hpFlow).symm
        calc
          incoming_flow P.head (y - circuit_characteristic_vector p.toFinset) P.t
              = incoming_flow P.head y P.t -
                  incoming_flow P.head (circuit_characteristic_vector p.toFinset) P.t := by
                    simp [incoming_flow_eq_sum_incoming_arcs, Finset.sum_sub_distrib]
          _ = outgoing_flow P.tail y P.t -
                outgoing_flow P.tail (circuit_characteristic_vector p.toFinset) P.t := by
                  linarith
          _ = outgoing_flow P.tail (y - circuit_characteristic_vector p.toFinset) P.t := by
                simp [outgoing_flow_eq_sum_outgoing_arcs, Finset.sum_sub_distrib]
      · -- Away from source and sink, both summands satisfy the same conservation law.
        calc
          incoming_flow P.head (y - circuit_characteristic_vector p.toFinset) v
              = incoming_flow P.head y v -
                  incoming_flow P.head (circuit_characteristic_vector p.toFinset) v := by
                    simp [incoming_flow_eq_sum_incoming_arcs, Finset.sum_sub_distrib]
          _ = outgoing_flow P.tail y v -
                outgoing_flow P.tail (circuit_characteristic_vector p.toFinset) v := by
                  rw [hyFlow.conservation v hvs hvt, hpFlow.conservation v hvs hvt]
          _ = outgoing_flow P.tail (y - circuit_characteristic_vector p.toFinset) v := by
                simp [outgoing_flow_eq_sum_outgoing_arcs, Finset.sum_sub_distrib]
  · intro a
    -- The domination hypothesis gives the residual nonnegativity coordinatewise.
    exact sub_nonneg.mpr (hdom a)

/-- Helper for Remark 4.12: the positive-support arcs of an arc vector. -/
private noncomputable def positiveSupport (x : A → ℝ) : Finset A :=
  Finset.univ.filter fun a ↦ 0 < x a

/-- Helper for Remark 4.12: subtracting a bounded nonnegative multiple of a circuit indicator from
a circulation preserves the circulation constraints. -/
private theorem circulationSub_smul_walkArcVector_of_circuit
    (P : ShortestPathLinearProgram V A) {z : A → ℝ} {c : List A}
    (hz : IsCirculation P.tail P.head z)
    (hc : P.IsCircuit c)
    {μ : ℝ} (hμnonneg : 0 ≤ μ)
    (hbound : ∀ a ∈ c.toFinset, μ ≤ z a) :
    IsCirculation P.tail P.head (z - μ • walkArcVector c) := by
  have hcirculation := walkArcVector_isCirculation_of_circuit P hc
  rcases hc with ⟨_, v, hwalk, htailNodup⟩
  have hnodupArcs : c.Nodup := by
    apply List.Nodup.of_map P.head
    simpa [walkVerticesFrom_tail_eq_map_head P v c] using htailNodup
  have hwalkVector :
      walkArcVector c = circuit_characteristic_vector c.toFinset :=
    walkArcVector_eq_characteristic_of_nodup hnodupArcs
  refine
    { flow_conservation := ?_
      nonneg := ?_ }
  · intro w
    -- Subtracting a circulation preserves every vertex-balance equation.
    calc
      incoming_flow P.head (z - μ • walkArcVector c) w
          = incoming_flow P.head z w -
              incoming_flow P.head (μ • walkArcVector c) w := by
                rw [incomingFlow_sub]
      _ = incoming_flow P.head z w -
            μ * incoming_flow P.head (walkArcVector c) w := by
              rw [incomingFlow_smul]
      _ = outgoing_flow P.tail z w -
            μ * outgoing_flow P.tail (walkArcVector c) w := by
              rw [hz.flow_conservation w, hcirculation.flow_conservation w]
      _ = outgoing_flow P.tail z w -
            outgoing_flow P.tail (μ • walkArcVector c) w := by
              rw [outgoingFlow_smul]
      _ = outgoing_flow P.tail (z - μ • walkArcVector c) w := by
            rw [outgoingFlow_sub]
  · intro a
    by_cases ha : a ∈ c.toFinset
    · -- On the circuit support, the coefficient bound on `μ` keeps the residual nonnegative.
      have hza : μ ≤ z a := hbound a ha
      have hχ : walkArcVector c a = 1 := by
        simpa [hwalkVector, circuit_characteristic_vector_apply, ha] using rfl
      simp [Pi.smul_apply, hχ]
      exact hza
    · -- Away from the circuit support, the residual agrees with the original circulation.
      have hχ : walkArcVector c a = 0 := by
        simpa [hwalkVector, circuit_characteristic_vector_apply, ha] using rfl
      simpa [Pi.smul_apply, hχ] using hz.nonneg a

/-- Helper for Remark 4.12: subtracting a bounded nonnegative multiple of a supported circuit
preserves feasibility. -/
private theorem feasibleSub_smul_walkArcVector_of_circuit
    (P : ShortestPathLinearProgram V A) {y : A → ℝ} {c : List A}
    (hy : P.IsFeasible y)
    (hc : P.IsCircuit c)
    {μ : ℝ} (hμnonneg : 0 ≤ μ)
    (hbound : ∀ a ∈ c.toFinset, μ ≤ y a) :
    P.IsFeasible (y - μ • walkArcVector c) := by
  have hcirculation := walkArcVector_isCirculation_of_circuit P hc
  rcases hy with ⟨hyFlow, hyValue⟩
  have hcValue :
      st_flow_value P.tail P.head P.s (walkArcVector c) = 0 := by
    rcases hc with ⟨_, v, hwalk, _⟩
    have hbalance :
        incoming_flow P.head (walkArcVector c) P.s -
          outgoing_flow P.tail (walkArcVector c) P.s = 0 := by
      simpa using directedWalk_balance P hwalk P.s
    -- A circuit multiplicity vector is a circulation, so its `s,t`-flow value vanishes.
    unfold st_flow_value
    linarith
  rcases hc with ⟨_, v, hwalk, htailNodup⟩
  have hnodupArcs :
      c.Nodup := by
        apply List.Nodup.of_map P.head
        simpa [walkVerticesFrom_tail_eq_map_head P v c] using htailNodup
  have hwalkVector :
      walkArcVector c = circuit_characteristic_vector c.toFinset :=
    walkArcVector_eq_characteristic_of_nodup hnodupArcs
  refine ⟨?_, ?_⟩
  · refine
      { nonneg := ?_
        conservation := ?_ }
    · intro a
      by_cases ha : a ∈ c.toFinset
      · -- On the peeled circuit, the lower bound on `μ` keeps the residual nonnegative.
        have hya : μ ≤ y a := hbound a ha
        have hχ : walkArcVector c a = 1 := by
          simpa [hwalkVector, circuit_characteristic_vector_apply, ha] using rfl
        simp [Pi.smul_apply, hχ]
        exact hya
      · -- Away from the circuit support, the residual agrees with the original feasible flow.
        have hχ : walkArcVector c a = 0 := by
          simpa [hwalkVector, circuit_characteristic_vector_apply, ha] using rfl
        simpa [Pi.smul_apply, hχ] using hyFlow.nonneg a
    · intro v hvs hvt
      -- Subtracting a circulation preserves conservation away from source and sink.
      calc
        incoming_flow P.head (y - μ • walkArcVector c) v
            = incoming_flow P.head y v -
                incoming_flow P.head (μ • walkArcVector c) v := by
                  rw [incomingFlow_sub]
        _ = incoming_flow P.head y v -
              μ * incoming_flow P.head (walkArcVector c) v := by
                rw [incomingFlow_smul]
        _ = outgoing_flow P.tail y v -
              μ * outgoing_flow P.tail (walkArcVector c) v := by
                rw [hyFlow.conservation v hvs hvt, hcirculation.flow_conservation v]
        _ = outgoing_flow P.tail y v -
              outgoing_flow P.tail (μ • walkArcVector c) v := by
                rw [outgoingFlow_smul]
        _ = outgoing_flow P.tail (y - μ • walkArcVector c) v := by
              rw [outgoingFlow_sub]
  · -- The peeled circuit contributes zero `s,t`-flow value.
    calc
      st_flow_value P.tail P.head P.s (y - μ • walkArcVector c)
          = st_flow_value P.tail P.head P.s y -
              μ * st_flow_value P.tail P.head P.s (walkArcVector c) := by
                unfold st_flow_value
                rw [outgoingFlow_sub, outgoingFlow_smul, incomingFlow_sub, incomingFlow_smul]
                ring
      _ = 1 - μ * 0 := by rw [hyValue, hcValue]
      _ = 1 := by ring

/-- Helper for Remark 4.12: peeling a supported `s,t`-path and renormalizing by the remaining
flow value preserves feasibility when the peeled amount is strictly less than `1`. -/
private theorem normalizedResidual_isFeasible_of_stPathSub
    (P : ShortestPathLinearProgram V A) {y : A → ℝ} {p : List A}
    (hy : P.IsFeasible y)
    (hp : P.IsStPath p)
    {μ : ℝ}
    (hμnonneg : 0 ≤ μ)
    (hμlt : μ < 1)
    (hbound : ∀ a ∈ p.toFinset, μ ≤ y a) :
    P.IsFeasible ((1 / (1 - μ)) • (y - μ • circuit_characteristic_vector p.toFinset)) := by
  have hst : P.s ≠ P.t :=
    ShortestPathLinearProgram.IsFeasible.source_ne_sink (P := P) (x := y) hy
  have hpSpec := stPathCharacteristic_spec P hst hp
  rcases hy with ⟨hyFlow, hyValue⟩
  rcases hpSpec.1 with ⟨hpFlow, hpValue⟩
  let r : A → ℝ := y - μ • circuit_characteristic_vector p.toFinset
  have hone_sub_pos : 0 < 1 - μ := by
    linarith
  have hone_sub_ne : 1 - μ ≠ 0 := ne_of_gt hone_sub_pos
  have hscale_nonneg : 0 ≤ 1 / (1 - μ) := by
    positivity
  have hrFlow : IsSTFlow P.tail P.head P.s P.t r := by
    refine
      { nonneg := ?_
        conservation := ?_ }
    · intro a
      by_cases ha : a ∈ p.toFinset
      · -- Along the peeled path, the coefficient bound keeps the unscaled residual nonnegative.
        have hχ : circuit_characteristic_vector p.toFinset a = 1 := by
          simp [circuit_characteristic_vector_apply, ha]
        dsimp [r]
        simp [Pi.smul_apply, hχ]
        linarith [hbound a ha]
      · -- Away from the path support, the residual agrees with the original feasible flow.
        have hχ : circuit_characteristic_vector p.toFinset a = 0 := by
          simp [circuit_characteristic_vector_apply, ha]
        dsimp [r]
        simpa [Pi.smul_apply, hχ] using hyFlow.nonneg a
    · intro v hvs hvt
      -- Both the feasible flow and the peeled path indicator satisfy the same internal balance
      -- equations, so their difference does as well.
      dsimp [r]
      calc
        incoming_flow P.head (y - μ • circuit_characteristic_vector p.toFinset) v
            = incoming_flow P.head y v -
                incoming_flow P.head (μ • circuit_characteristic_vector p.toFinset) v := by
                  rw [incomingFlow_sub]
        _ = incoming_flow P.head y v -
              μ * incoming_flow P.head (circuit_characteristic_vector p.toFinset) v := by
                rw [incomingFlow_smul]
        _ = outgoing_flow P.tail y v -
              μ * outgoing_flow P.tail (circuit_characteristic_vector p.toFinset) v := by
                rw [hyFlow.conservation v hvs hvt, hpFlow.conservation v hvs hvt]
        _ = outgoing_flow P.tail y v -
              outgoing_flow P.tail (μ • circuit_characteristic_vector p.toFinset) v := by
                rw [outgoingFlow_smul]
        _ = outgoing_flow P.tail (y - μ • circuit_characteristic_vector p.toFinset) v := by
              rw [outgoingFlow_sub]
  have hrValue :
      st_flow_value P.tail P.head P.s r = 1 - μ := by
    -- Route correction: prove the unscaled residual value first, and only then normalize.
    dsimp [r]
    calc
      st_flow_value P.tail P.head P.s
          (y - μ • circuit_characteristic_vector p.toFinset)
          = st_flow_value P.tail P.head P.s y -
              μ * st_flow_value P.tail P.head P.s
                (circuit_characteristic_vector p.toFinset) := by
                  unfold st_flow_value
                  rw [outgoingFlow_sub, outgoingFlow_smul, incomingFlow_sub, incomingFlow_smul]
                  ring
      _ = 1 - μ * 1 := by rw [hyValue, hpValue]
      _ = 1 - μ := by ring
  refine ⟨?_, ?_⟩
  · refine
      { nonneg := ?_
        conservation := ?_ }
    · intro a
      -- Scaling the nonnegative residual by a positive scalar keeps every coordinate nonnegative.
      simpa [Pi.smul_apply] using mul_nonneg hscale_nonneg (hrFlow.nonneg a)
    · intro v hvs hvt
      -- The normalized residual inherits conservation from the unscaled residual.
      calc
        incoming_flow P.head ((1 / (1 - μ)) • r) v
            = (1 / (1 - μ)) * incoming_flow P.head r v := by
                rw [incomingFlow_smul]
        _ = (1 / (1 - μ)) * outgoing_flow P.tail r v := by
              rw [hrFlow.conservation v hvs hvt]
        _ = outgoing_flow P.tail ((1 / (1 - μ)) • r) v := by
              rw [outgoingFlow_smul]
  · -- The normalization rescales the residual value `1 - μ` back to `1`.
    calc
      st_flow_value P.tail P.head P.s ((1 / (1 - μ)) • r)
          = (1 / (1 - μ)) * st_flow_value P.tail P.head P.s r := by
              unfold st_flow_value
              rw [outgoingFlow_smul, incomingFlow_smul]
              ring
      _ = (1 / (1 - μ)) * (1 - μ) := by rw [hrValue]
      _ = 1 := by
            field_simp [hone_sub_ne]

/-- Helper for Remark 4.12: positive scaling does not change which arc coordinates are strictly
positive. -/
private theorem positiveSupport_smul_of_pos
    (x : A → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    positiveSupport (μ • x) = positiveSupport x := by
  ext a
  simp [positiveSupport, Pi.smul_apply, hμ, show (0 < μ * x a) ↔ 0 < x a by
    constructor <;> intro hx <;> nlinarith]

/-- Helper for Remark 4.12: peeling a minimum positive coefficient from a nodup walk strictly
shrinks the positive support. -/
private theorem positiveSupport_card_lt_of_sub_smul_walkArcVector
    {z : A → ℝ} {p : List A}
    (hpNodup : p.Nodup)
    {μ : ℝ}
    (hμpos : 0 < μ)
    (hbound : ∀ a ∈ p.toFinset, μ ≤ z a)
    (hzero : ∃ a ∈ p.toFinset, z a = μ) :
    (positiveSupport (z - μ • walkArcVector p)).card < (positiveSupport z).card := by
  classical
  have hwalk :
      walkArcVector p = circuit_characteristic_vector p.toFinset :=
    walkArcVector_eq_characteristic_of_nodup hpNodup
  have hsubset :
      positiveSupport (z - μ • walkArcVector p) ⊆ positiveSupport z := by
    intro a ha
    rw [positiveSupport] at ha ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    by_cases hmem : a ∈ p.toFinset
    · have hχ : walkArcVector p a = 1 := by
        simpa [hwalk, circuit_characteristic_vector_apply, hmem] using rfl
      have hza : 0 < z a := lt_of_lt_of_le hμpos (hbound a hmem)
      linarith [ha]
    · have hχ : walkArcVector p a = 0 := by
        simpa [hwalk, circuit_characteristic_vector_apply, hmem] using rfl
      simpa [Pi.smul_apply, hχ] using ha
  rcases hzero with ⟨a₀, ha₀, hza₀⟩
  have ha₀_old : a₀ ∈ positiveSupport z := by
    rw [positiveSupport]
    simp [hza₀, hμpos]
  have ha₀_new : a₀ ∉ positiveSupport (z - μ • walkArcVector p) := by
    rw [positiveSupport]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    have hχ : walkArcVector p a₀ = 1 := by
      simpa [hwalk, circuit_characteristic_vector_apply, ha₀] using rfl
    have hres : (z - μ • walkArcVector p) a₀ = 0 := by
      simp [Pi.sub_apply, Pi.smul_apply, hza₀, hχ]
    simpa [hres]
  have hssub :
      positiveSupport (z - μ • walkArcVector p) ⊂ positiveSupport z := by
    exact Finset.ssubset_iff_of_subset hsubset |>.2 ⟨a₀, ha₀_old, ha₀_new⟩
  exact Finset.card_lt_card hssub

/-- Helper for Remark 4.12: in a digraph without negative-length circuits, every nonnegative
circulation has nonnegative objective value. -/
private theorem nonnegativeCirculation_objective_nonneg
    (P : ShortestPathLinearProgram V A) {z : A → ℝ}
    (hz : IsCirculation P.tail P.head z)
    (hneg : P.HasNoNegativeLengthCircuit) :
    0 ≤ P.objective z := by
  classical
  have hmain :
      ∀ n, ∀ (w : A → ℝ),
        (positiveSupport w).card = n →
        IsCirculation P.tail P.head w →
        0 ≤ P.objective w := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih w hwcard hw
    by_cases hzero : (positiveSupport w).card = 0
    · have hwempty : positiveSupport w = ∅ := Finset.card_eq_zero.mp hzero
      have hwzero : w = 0 := by
        ext a
        have hnotpos : ¬ 0 < w a := by
          intro hwa
          have ha : a ∈ positiveSupport w := by
            rw [positiveSupport]
            simp [hwa]
          simpa [hwempty] using ha
        have hwle : w a ≤ 0 := by
          linarith
        exact le_antisymm hwle (hw.nonneg a)
      -- When no coordinate is positive, nonnegativity forces the circulation to vanish.
      simpa [hwzero, ShortestPathLinearProgram.objective]
    · have hpos : ∃ a, 0 < w a := by
        rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hzero) with ⟨a, ha⟩
        exact ⟨a, (Finset.mem_filter.mp ha).2⟩
      rcases positiveSupportCircuit_of_circulation P hw hpos with ⟨c, hc, hcpos⟩
      rcases hc with ⟨hcne, v, hwalk, htailNodup⟩
      have hcNodup : c.Nodup := by
        apply List.Nodup.of_map P.head
        simpa [walkVerticesFrom_tail_eq_map_head P v c] using htailNodup
      have hcToFinsetNonempty : c.toFinset.Nonempty := by
        rcases List.ne_nil_iff_exists_cons.mp hcne with ⟨a, p, rfl⟩
        exact ⟨a, by simp⟩
      rcases Finset.exists_min_image c.toFinset w hcToFinsetNonempty with
        ⟨a₀, ha₀, hmin⟩
      let μ : ℝ := w a₀
      have hμpos : 0 < μ := by
        simpa [μ] using hcpos a₀ ha₀
      have hbound : ∀ a ∈ c.toFinset, μ ≤ w a := by
        intro a ha
        simpa [μ] using hmin a ha
      let w' : A → ℝ := w - μ • walkArcVector c
      have hw' :
          IsCirculation P.tail P.head w' := by
        -- Peel the minimum supported circuit coefficient while keeping a circulation.
        simpa [w', μ] using
          circulationSub_smul_walkArcVector_of_circuit
            (P := P) (z := w) (c := c) hw ⟨hcne, v, hwalk, htailNodup⟩
            (le_of_lt hμpos) hbound
      have hcardlt :
          (positiveSupport w').card < n := by
        have hshrink :
            (positiveSupport w').card < (positiveSupport w).card := by
          simpa [w', μ] using
            positiveSupport_card_lt_of_sub_smul_walkArcVector
              (z := w) (p := c) hcNodup hμpos hbound ⟨a₀, ha₀, by simp [μ]⟩
        simpa [hwcard] using hshrink
      have hw'obj :
          0 ≤ P.objective w' := by
        exact ih (positiveSupport w').card hcardlt w' rfl hw'
      have hobj :
          P.objective w = P.objective w' + μ * P.pathLength c := by
        have hwEq : w' + μ • walkArcVector c = w := by
          ext a
          simp [w', Pi.add_apply, Pi.smul_apply]
        -- Reassemble the peeled circulation as residual plus the minimum circuit piece.
        calc
          P.objective w = P.objective (w' + μ • walkArcVector c) := by rw [hwEq]
          _ = P.objective w' + μ * P.pathLength c := by
                simpa [w'] using objective_add_smul_walkArcVector P w' μ c
      have hcobj : 0 ≤ μ * P.pathLength c := by
        exact mul_nonneg (le_of_lt hμpos) (hneg c ⟨hcne, v, hwalk, htailNodup⟩)
      linarith
  exact hmain (positiveSupport z).card z rfl hz

/-- Helper for Remark 4.12: every feasible unit flow in a digraph without negative-length
circuits dominates the length of some `s,t`-path. -/
private theorem existsStPath_le_objective_of_feasible
    (P : ShortestPathLinearProgram V A) {y : A → ℝ}
    (hy : P.IsFeasible y)
    (hneg : P.HasNoNegativeLengthCircuit) :
    ∃ p : List A, P.IsStPath p ∧ P.pathLength p ≤ P.objective y := by
  classical
  have hst : P.s ≠ P.t :=
    ShortestPathLinearProgram.IsFeasible.source_ne_sink (P := P) (x := y) hy
  have hmain :
      ∀ n, ∀ (w : A → ℝ),
        (positiveSupport w).card = n →
        P.IsFeasible w →
        ∃ p : List A, P.IsStPath p ∧ P.pathLength p ≤ P.objective w := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih w hwcard hw
    rcases positiveSupportPathOrCircuit P hw with hcir | hpath
    · rcases hcir with ⟨c, hc, hcpos⟩
      rcases hc with ⟨hcne, v, hwalk, htailNodup⟩
      have hcNodup : c.Nodup := by
        apply List.Nodup.of_map P.head
        simpa [walkVerticesFrom_tail_eq_map_head P v c] using htailNodup
      have hcToFinsetNonempty : c.toFinset.Nonempty := by
        rcases List.ne_nil_iff_exists_cons.mp hcne with ⟨a, p, rfl⟩
        exact ⟨a, by simp⟩
      rcases Finset.exists_min_image c.toFinset w hcToFinsetNonempty with
        ⟨a₀, ha₀, hmin⟩
      let μ : ℝ := w a₀
      have hμpos : 0 < μ := by
        simpa [μ] using hcpos a₀ ha₀
      have hbound : ∀ a ∈ c.toFinset, μ ≤ w a := by
        intro a ha
        simpa [μ] using hmin a ha
      let w' : A → ℝ := w - μ • walkArcVector c
      have hw' : P.IsFeasible w' := by
        -- Peeling a supported circuit preserves feasibility.
        simpa [w', μ] using
          feasibleSub_smul_walkArcVector_of_circuit
            (P := P) (y := w) (c := c) hw ⟨hcne, v, hwalk, htailNodup⟩
            (le_of_lt hμpos) hbound
      have hcardlt :
          (positiveSupport w').card < n := by
        have hshrink :
            (positiveSupport w').card < (positiveSupport w).card := by
          simpa [w', μ] using
            positiveSupport_card_lt_of_sub_smul_walkArcVector
              (z := w) (p := c) hcNodup hμpos hbound ⟨a₀, ha₀, by simp [μ]⟩
        simpa [hwcard] using hshrink
      rcases ih (positiveSupport w').card hcardlt w' rfl hw' with ⟨p, hp, hple⟩
      have hobj :
          P.objective w = P.objective w' + μ * P.pathLength c := by
        have hwEq : w' + μ • walkArcVector c = w := by
          ext a
          simp [w', Pi.add_apply, Pi.smul_apply]
        -- Reassemble the feasible flow from the peeled residual and the circuit contribution.
        calc
          P.objective w = P.objective (w' + μ • walkArcVector c) := by rw [hwEq]
          _ = P.objective w' + μ * P.pathLength c := by
                simpa [w'] using objective_add_smul_walkArcVector P w' μ c
      have hcobj : 0 ≤ μ * P.pathLength c := by
        exact mul_nonneg (le_of_lt hμpos) (hneg c ⟨hcne, v, hwalk, htailNodup⟩)
      refine ⟨p, hp, ?_⟩
      linarith
    · rcases hpath with ⟨p, hp, hposp⟩
      have hpNodup : p.Nodup :=
        directedWalk_nodup_of_verticesNodup P hp.1 hp.2
      have hpne : p ≠ [] := by
        intro hnil
        have : P.s = P.t := by
          simpa [ShortestPathLinearProgram.IsStPath, ShortestPathLinearProgram.IsStWalk,
            ShortestPathLinearProgram.IsDirectedWalkFromTo, hnil] using hp.1
        exact hst this
      have hpToFinsetNonempty : p.toFinset.Nonempty := by
        rcases List.ne_nil_iff_exists_cons.mp hpne with ⟨a, q, rfl⟩
        exact ⟨a, by simp⟩
      rcases Finset.exists_min_image p.toFinset w hpToFinsetNonempty with
        ⟨a₀, ha₀, hmin⟩
      let μ : ℝ := min (1 : ℝ) (w a₀)
      have hμpos : 0 < μ := by
        have ha₀pos : 0 < w a₀ := hposp a₀ ha₀
        have hone : (0 : ℝ) < 1 := by norm_num
        dsimp [μ]
        exact lt_min hone ha₀pos
      have hμle : μ ≤ 1 := by
        dsimp [μ]
        exact min_le_left _ _
      have hbound : ∀ a ∈ p.toFinset, μ ≤ w a := by
        intro a ha
        exact le_trans (by simpa [μ] using (min_le_right (1 : ℝ) (w a₀))) (hmin a ha)
      by_cases hμone : μ = 1
      · have hdom : circuit_characteristic_vector p.toFinset ≤ w := by
          intro a
          by_cases ha : a ∈ p.toFinset
          · have hwa : 1 ≤ w a := by
              calc
                (1 : ℝ) = μ := by simpa [hμone]
                _ ≤ w a := hbound a ha
            simpa [circuit_characteristic_vector_apply, ha] using hwa
          · have hw_nonneg : 0 ≤ w a := hw.1.nonneg a
            simpa [circuit_characteristic_vector_apply, ha] using hw_nonneg
        have hwcir :
            IsCirculation P.tail P.head (w - circuit_characteristic_vector p.toFinset) := by
          exact feasibleResidual_isCirculation_of_stPathSub P hw hp hdom
        have hwcirObj :
            0 ≤ P.objective (w - circuit_characteristic_vector p.toFinset) := by
          exact nonnegativeCirculation_objective_nonneg P hwcir hneg
        have hpSpec := stPathCharacteristic_spec P hst hp
        have hpObj :
            P.objective w =
              P.objective (w - circuit_characteristic_vector p.toFinset) + P.pathLength p := by
          have hwalk :
              walkArcVector p = circuit_characteristic_vector p.toFinset :=
            walkArcVector_eq_characteristic_of_nodup hpNodup
          have hwEq :
              (w - circuit_characteristic_vector p.toFinset) + walkArcVector p = w := by
            ext a
            rw [hwalk]
            by_cases ha : a ∈ p.toFinset
            · simp [Pi.add_apply, circuit_characteristic_vector_apply, ha]
            · simp [Pi.add_apply, circuit_characteristic_vector_apply, ha]
          -- The peeled path contributes exactly its path length to the objective.
          calc
            P.objective w =
                P.objective
                  ((w - circuit_characteristic_vector p.toFinset) + walkArcVector p) := by
                    rw [hwEq]
            _ = P.objective (w - circuit_characteristic_vector p.toFinset) + P.pathLength p := by
                  simpa [hwalk] using
                    objective_add_smul_walkArcVector
                      P (w - circuit_characteristic_vector p.toFinset) 1 p
        refine ⟨p, hp, ?_⟩
        linarith
      · have hμlt : μ < 1 := by
          exact lt_of_le_of_ne hμle hμone
        have hwNorm :
            P.IsFeasible ((1 / (1 - μ)) • (w - μ • circuit_characteristic_vector p.toFinset)) := by
          exact normalizedResidual_isFeasible_of_stPathSub P hw hp (le_of_lt hμpos) hμlt hbound
        have hμeq : μ = w a₀ := by
          dsimp [μ]
          by_cases ha₀le : w a₀ ≤ 1
          · rw [min_eq_right ha₀le]
          · have hone_lt : 1 < w a₀ := lt_of_not_ge ha₀le
            have : μ = 1 := by
              dsimp [μ]
              rw [min_eq_left (le_of_lt hone_lt)]
            exact False.elim (hμone this)
        have hwalk :
            walkArcVector p = circuit_characteristic_vector p.toFinset :=
          walkArcVector_eq_characteristic_of_nodup hpNodup
        have hshrinkRaw :
            (positiveSupport (w - μ • circuit_characteristic_vector p.toFinset)).card <
              (positiveSupport w).card := by
          simpa [hwalk] using
            positiveSupport_card_lt_of_sub_smul_walkArcVector
              (z := w) (p := p) hpNodup hμpos hbound ⟨a₀, ha₀, hμeq.symm⟩
        have hscalePos : 0 < 1 / (1 - μ) := by
          have hone_sub_pos : 0 < 1 - μ := by linarith
          positivity
        have hcardlt :
            (positiveSupport ((1 / (1 - μ)) •
              (w - μ • circuit_characteristic_vector p.toFinset))).card < n := by
          have hscaled :
              positiveSupport ((1 / (1 - μ)) •
                (w - μ • circuit_characteristic_vector p.toFinset)) =
                positiveSupport (w - μ • circuit_characteristic_vector p.toFinset) := by
            simpa using
              positiveSupport_smul_of_pos
                (x := w - μ • circuit_characteristic_vector p.toFinset) hscalePos
          rw [hscaled]
          simpa [hwcard] using hshrinkRaw
        rcases ih
            (positiveSupport ((1 / (1 - μ)) •
              (w - μ • circuit_characteristic_vector p.toFinset))).card
            hcardlt
            (((1 / (1 - μ)) • (w - μ • circuit_characteristic_vector p.toFinset)))
            rfl hwNorm with ⟨q, hq, hqle⟩
        let w' : A → ℝ := ((1 / (1 - μ)) • (w - μ • circuit_characteristic_vector p.toFinset))
        have hwObj :
            P.objective w = μ * P.pathLength p + (1 - μ) * P.objective w' := by
          have hone_sub_ne : 1 - μ ≠ 0 := by linarith
          have hresEq :
              P.objective (w - μ • circuit_characteristic_vector p.toFinset) =
                (1 - μ) * P.objective w' := by
            calc
              P.objective (w - μ • circuit_characteristic_vector p.toFinset)
                  = (1 - μ) *
                      ((1 / (1 - μ)) *
                        P.objective (w - μ • circuit_characteristic_vector p.toFinset)) := by
                          field_simp [hone_sub_ne]
              _ = (1 - μ) * P.objective w' := by
                    rw [show P.objective w' =
                        (1 / (1 - μ)) *
                          P.objective (w - μ • circuit_characteristic_vector p.toFinset) by
                        simp [w', objective_smul]]
          have hwDecomp :
              P.objective w =
                P.objective (w - μ • circuit_characteristic_vector p.toFinset) +
                  μ * P.pathLength p := by
            have hwEq :
                (w - μ • circuit_characteristic_vector p.toFinset) + μ • walkArcVector p = w := by
              ext a
              rw [hwalk]
              by_cases ha : a ∈ p.toFinset
              · simp [Pi.add_apply, Pi.smul_apply, circuit_characteristic_vector_apply, ha]
              · simp [Pi.add_apply, Pi.smul_apply, circuit_characteristic_vector_apply, ha]
            calc
              P.objective w =
                  P.objective
                    ((w - μ • circuit_characteristic_vector p.toFinset) + μ • walkArcVector p) := by
                      rw [hwEq]
              _ = P.objective (w - μ • circuit_characteristic_vector p.toFinset) +
                    μ * P.pathLength p := by
                    simpa [hwalk] using
                      objective_add_smul_walkArcVector
                        P (w - μ • circuit_characteristic_vector p.toFinset) μ p
          linarith
        by_cases hpBetter : P.pathLength p ≤ P.objective w'
        · refine ⟨p, hp, ?_⟩
          have hcoeff : 0 ≤ 1 - μ := by linarith
          have hmul :
              (1 - μ) * P.pathLength p ≤ (1 - μ) * P.objective w' :=
            mul_le_mul_of_nonneg_left hpBetter hcoeff
          calc
            P.pathLength p = μ * P.pathLength p + (1 - μ) * P.pathLength p := by ring
            _ ≤ μ * P.pathLength p + (1 - μ) * P.objective w' := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_left hmul (μ * P.pathLength p)
            _ = P.objective w := by rw [hwObj]
        · have hw'Better : P.objective w' ≤ P.pathLength p := le_of_lt (lt_of_not_ge hpBetter)
          refine ⟨q, hq, ?_⟩
          have hcoeff : 0 ≤ μ := le_of_lt hμpos
          have hmul :
              μ * P.objective w' ≤ μ * P.pathLength p :=
            mul_le_mul_of_nonneg_left hw'Better hcoeff
          calc
            P.pathLength q ≤ P.objective w' := hqle
            _ = μ * P.objective w' + (1 - μ) * P.objective w' := by ring
            _ ≤ μ * P.pathLength p + (1 - μ) * P.objective w' := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_right hmul ((1 - μ) * P.objective w')
            _ = P.objective w := by rw [hwObj]
  exact hmain (positiveSupport y).card y rfl hy

/-- Remark 4.12 (1): if `(4.7)` is feasible and `D` contains a negative-length circuit, then the
shortest-path linear program `(4.7)` is unbounded. -/
theorem negative_length_circuit_implies_shortest_path_lp_unbounded
    (P : ShortestPathLinearProgram V A)
    (hfeas : P.HasFeasibleSolution)
    (hneg : P.HasNegativeLengthCircuit) :
    P.IsUnbounded := by
  rcases hfeas with ⟨x, hx⟩
  rcases hneg with ⟨c, hcircuit, hcneg⟩
  rcases hcircuit with ⟨_, v, hwalk, _⟩
  intro r
  let μ : ℝ := max ((P.objective x - r) / (-P.pathLength c)) 0
  have hμ_nonneg : 0 ≤ μ := by
    exact le_max_right _ _
  have hclosed_balance :
      incoming_flow P.head (walkArcVector c) P.s -
        outgoing_flow P.tail (walkArcVector c) P.s = 0 := by
    -- A closed directed walk has zero endpoint imbalance at every vertex.
    simpa using directedWalk_balance P hwalk P.s
  have hclosed_value :
      st_flow_value P.tail P.head P.s (walkArcVector c) = 0 := by
    -- Converting the source balance back to the `st_flow_value` sign convention gives zero value.
    unfold st_flow_value
    linarith
  refine ⟨x + μ • walkArcVector c, ?_, ?_⟩
  · rcases hx with ⟨hxflow, hxvalue⟩
    refine ⟨?_, ?_⟩
    · refine
        { nonneg := ?_
          conservation := ?_ }
      · intro a
        -- Nonnegativity is preserved because both the feasible flow and the circuit multiplicities
        -- are coordinatewise nonnegative, and `μ` is nonnegative.
        have hχ : 0 ≤ walkArcVector c a := walkArcVector_nonneg c a
        simpa [Pi.add_apply, Pi.smul_apply] using
          add_nonneg (hxflow.nonneg a) (mul_nonneg hμ_nonneg hχ)
      · intro w hws hwt
        have hcirculation :
            incoming_flow P.head (walkArcVector c) w =
              outgoing_flow P.tail (walkArcVector c) w := by
          have hbalance :
              incoming_flow P.head (walkArcVector c) w -
                outgoing_flow P.tail (walkArcVector c) w = 0 := by
            simpa using directedWalk_balance P hwalk w
          exact sub_eq_zero.mp hbalance
        -- The closed-walk vector is a circulation, so adding it preserves conservation.
        calc
          incoming_flow P.head (x + μ • walkArcVector c) w
              = incoming_flow P.head x w +
                  μ * incoming_flow P.head (walkArcVector c) w := by
                    rw [incomingFlow_add, incomingFlow_smul]
          _ = outgoing_flow P.tail x w +
                μ * outgoing_flow P.tail (walkArcVector c) w := by
                  rw [hxflow.conservation w hws hwt, hcirculation]
          _ = outgoing_flow P.tail (x + μ • walkArcVector c) w := by
                rw [outgoingFlow_add, outgoingFlow_smul]
    · -- The circuit multiplicity vector has zero `s,t`-flow value, so the source value stays `1`.
      calc
        st_flow_value P.tail P.head P.s (x + μ • walkArcVector c)
            = st_flow_value P.tail P.head P.s x +
                μ * st_flow_value P.tail P.head P.s (walkArcVector c) := by
                  unfold st_flow_value
                  rw [outgoingFlow_add, outgoingFlow_smul, incomingFlow_add, incomingFlow_smul]
                  ring
        _ = 1 + μ * 0 := by rw [hxvalue, hclosed_value]
        _ = 1 := by ring
  · have hdenom_pos : 0 < -P.pathLength c := by
      linarith
    have hμ_lower :
        P.objective x - r ≤ μ * (-P.pathLength c) := by
      have hdiv : (P.objective x - r) / (-P.pathLength c) ≤ μ := by
        exact le_max_left _ _
      exact (div_le_iff₀ hdenom_pos).mp hdiv
    -- Choosing `μ` above the exact threshold forces the objective below the prescribed bound.
    rw [objective_add_smul_walkArcVector]
    linarith

/-- Helper for Remark 4.12: an optimal feasible flow rules out negative-length circuits, because
otherwise part (1) would make the objective unbounded below. -/
private theorem optimalSolution_hasNoNegativeLengthCircuit
    (P : ShortestPathLinearProgram V A) {x : A → ℝ}
    (hx : P.IsOptimalSolution x) :
    P.HasNoNegativeLengthCircuit := by
  intro c hcircuit
  by_contra hcneg
  have hfeas : P.HasFeasibleSolution := ⟨x, hx.1⟩
  have hunbounded :
      P.IsUnbounded :=
    negative_length_circuit_implies_shortest_path_lp_unbounded P hfeas
      ⟨c, hcircuit, lt_of_not_ge hcneg⟩
  rcases hunbounded (P.objective x - 1) with ⟨y, hyfeas, hyobj⟩
  -- Compare the supposed optimum against the unbounded feasible point below it.
  have hopt := hx.2 y hyfeas
  linarith

/-- Helper for Remark 4.12: basic optimality already provides a component-reduced subsystem whose
support columns are linearly independent. This is the exact Chapter 3 linear-algebra input needed
for the later support-structure argument. -/
private theorem basicOptimal_exists_componentReducedRows_with_linearIndependentSupport
    [Fintype V]
    (P : ShortestPathLinearProgram V A) {x : A → ℝ}
    (hx : P.IsBasicOptimalSolution x) :
    ∃ R : Finset (Fin (Fintype.card V)),
      P.IsComponentReducedRowSet R ∧
        LinearIndependent ℝ
          (fun j : Function.support (ShortestPathLinearProgram.arcCoordinates x) ↦
            fun i : Fin R.card => P.restrictedIncidenceMatrix R i j) := by
  rcases hx.1 with ⟨R, hR, hbasic⟩
  refine ⟨R, hR, ?_⟩
  -- Read basicity directly through the Chapter 3 owner for support columns.
  exact is_basic_solution.support_columns_linearIndependent hbasic.basic

/-- Helper for Remark 4.12: a supported loop would give a zero incidence column, so support-column
linear independence rules supported loops out immediately. -/
private theorem supportColumnsLinearIndependent_forces_noSupportedLoop
    [Fintype V]
    (P : ShortestPathLinearProgram V A)
    {x : A → ℝ}
    {R : Finset (Fin (Fintype.card V))}
    (hlin :
      LinearIndependent ℝ
        (fun j : Function.support (ShortestPathLinearProgram.arcCoordinates x) ↦
          fun i : Fin R.card => P.restrictedIncidenceMatrix R i j))
    {a : A} (ha : x a ≠ 0) :
    P.tail a ≠ P.head a := by
  intro hloop
  let j : Function.support (ShortestPathLinearProgram.arcCoordinates x) :=
    ⟨(Fintype.equivFin A) a, by
      simpa [ShortestPathLinearProgram.arcCoordinates] using ha⟩
  have hzero :
      (fun i : Fin R.card => P.restrictedIncidenceMatrix R i j) = 0 := by
    ext i
    -- Unfold the reindexing once: a loop contributes `1 - 1 = 0` in every incidence row.
    simp [ShortestPathLinearProgram.restrictedIncidenceMatrix,
      ShortestPathLinearProgram.incidenceMatrix, digraph_incidence_matrix, hloop, j]
  exact (hlin.ne_zero j) hzero

/-- Helper for Remark 4.12: two distinct supported arcs cannot have the same ordered endpoints or
opposite ordered endpoints, because their restricted incidence columns would then agree up to a
nonzero scalar. -/
private theorem supportColumnsLinearIndependent_forcesNoParallelOrOppositeSupportedPair
    [Fintype V]
    (P : ShortestPathLinearProgram V A)
    {x : A → ℝ}
    {R : Finset (Fin (Fintype.card V))}
    (hlin :
      LinearIndependent ℝ
        (fun j : Function.support (ShortestPathLinearProgram.arcCoordinates x) ↦
          fun i : Fin R.card => P.restrictedIncidenceMatrix R i j))
    {a b : A} (ha : x a ≠ 0) (hb : x b ≠ 0) (hne : a ≠ b)
    (hends :
      (P.tail a = P.tail b ∧ P.head a = P.head b) ∨
        (P.tail a = P.head b ∧ P.head a = P.tail b)) :
    False := by
  let col := fun j : Function.support (ShortestPathLinearProgram.arcCoordinates x) ↦
    fun i : Fin R.card => P.restrictedIncidenceMatrix R i j
  let j : Function.support (ShortestPathLinearProgram.arcCoordinates x) :=
    ⟨(Fintype.equivFin A) a, by
      simpa [ShortestPathLinearProgram.arcCoordinates] using ha⟩
  let k : Function.support (ShortestPathLinearProgram.arcCoordinates x) :=
    ⟨(Fintype.equivFin A) b, by
      simpa [ShortestPathLinearProgram.arcCoordinates] using hb⟩
  have hjk : j ≠ k := by
    intro hjk_eq
    apply hne
    apply (Fintype.equivFin A).injective
    exact congrArg Subtype.val hjk_eq
  rcases hends with ⟨htail, hhead⟩ | ⟨htail, hhead⟩
  · have hcols : col j = col k := by
      ext i
      -- Equal ordered endpoints give identical restricted incidence columns row by row.
      simp [col, ShortestPathLinearProgram.restrictedIncidenceMatrix,
        ShortestPathLinearProgram.incidenceMatrix, digraph_incidence_matrix, j, k, htail, hhead]
    have hjk_eq : j = k :=
      LinearIndependent.eq_of_smul_apply_eq_smul_apply hlin (1 : ℝ) (1 : ℝ) j k one_ne_zero
        (by simpa [col] using hcols)
    exact hjk hjk_eq
  · have hcols : col j = - col k := by
      ext i
      -- Swapping the ordered endpoints negates the corresponding incidence column.
      simp [col, ShortestPathLinearProgram.restrictedIncidenceMatrix,
        ShortestPathLinearProgram.incidenceMatrix, digraph_incidence_matrix, j, k, htail, hhead]
    have hjk_eq : j = k :=
      LinearIndependent.eq_of_smul_apply_eq_smul_apply hlin (1 : ℝ) (-1 : ℝ) j k one_ne_zero
        (by simpa [col] using hcols)
    exact hjk hjk_eq

/-- Helper for Remark 4.12: support-column independence packages undirected support adjacency by a
unique supported arc. This is the support-graph API needed for the later cycle and forest
arguments. -/
private theorem supportedGraphAdj_iff_existsUniqueArc
    [Fintype V]
    (P : ShortestPathLinearProgram V A)
    {x : A → ℝ}
    {R : Finset (Fin (Fintype.card V))}
    (hlin :
      LinearIndependent ℝ
        (fun j : Function.support (ShortestPathLinearProgram.arcCoordinates x) ↦
          fun i : Fin R.card => P.restrictedIncidenceMatrix R i j))
    {u v : V} :
    let F : Finset A := Finset.univ.filter fun a ↦ x a ≠ 0
    let G := (arc_induced_digraph P.tail P.head F).toSimpleGraphInclusive
    G.Adj u v ↔
      u ≠ v ∧ ∃! a,
        a ∈ F ∧ ((P.tail a = u ∧ P.head a = v) ∨ (P.tail a = v ∧ P.head a = u)) := by
  classical
  let F : Finset A := Finset.univ.filter fun a ↦ x a ≠ 0
  let G := (arc_induced_digraph P.tail P.head F).toSimpleGraphInclusive
  change G.Adj u v ↔
      u ≠ v ∧ ∃! a,
        a ∈ F ∧ ((P.tail a = u ∧ P.head a = v) ∨ (P.tail a = v ∧ P.head a = u))
  constructor
  · intro huv
    -- Unpack the support-graph edge into one oriented supported arc, then use column
    -- independence to rule out any competing supported realization of the same undirected edge.
    simp [G, Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨huv_ne, huv | huv⟩
    · rw [arc_induced_digraph_adj_iff P.tail P.head F u v] at huv
      rcases huv with ⟨a, haF, htail, hhead⟩
      refine ⟨huv_ne, ⟨a, ⟨haF, Or.inl ⟨htail, hhead⟩⟩, ?_⟩⟩
      intro b hb
      rcases hb with ⟨hbF, (⟨htail', hhead'⟩ | ⟨htail', hhead'⟩)⟩
      · by_cases hba : b = a
        · exact hba
        · exfalso
          have ha : x a ≠ 0 := (Finset.mem_filter.mp haF).2
          have hb' : x b ≠ 0 := (Finset.mem_filter.mp hbF).2
          exact supportColumnsLinearIndependent_forcesNoParallelOrOppositeSupportedPair
            P hlin ha hb' (fun hab ↦ hba hab.symm)
            (Or.inl ⟨htail.trans htail'.symm, hhead.trans hhead'.symm⟩)
      · by_cases hba : b = a
        · exact hba
        · exfalso
          have ha : x a ≠ 0 := (Finset.mem_filter.mp haF).2
          have hb' : x b ≠ 0 := (Finset.mem_filter.mp hbF).2
          exact supportColumnsLinearIndependent_forcesNoParallelOrOppositeSupportedPair
            P hlin ha hb' (fun hab ↦ hba hab.symm)
            (Or.inr ⟨htail.trans hhead'.symm, hhead.trans htail'.symm⟩)
    · rw [arc_induced_digraph_adj_iff P.tail P.head F v u] at huv
      rcases huv with ⟨a, haF, htail, hhead⟩
      refine ⟨huv_ne, ⟨a, ⟨haF, Or.inr ⟨htail, hhead⟩⟩, ?_⟩⟩
      intro b hb
      rcases hb with ⟨hbF, (⟨htail', hhead'⟩ | ⟨htail', hhead'⟩)⟩
      · by_cases hba : b = a
        · exact hba
        · exfalso
          have ha : x a ≠ 0 := (Finset.mem_filter.mp haF).2
          have hb' : x b ≠ 0 := (Finset.mem_filter.mp hbF).2
          exact supportColumnsLinearIndependent_forcesNoParallelOrOppositeSupportedPair
            P hlin ha hb' (fun hab ↦ hba hab.symm)
            (Or.inr ⟨htail.trans hhead'.symm, hhead.trans htail'.symm⟩)
      · by_cases hba : b = a
        · exact hba
        · exfalso
          have ha : x a ≠ 0 := (Finset.mem_filter.mp haF).2
          have hb' : x b ≠ 0 := (Finset.mem_filter.mp hbF).2
          exact supportColumnsLinearIndependent_forcesNoParallelOrOppositeSupportedPair
            P hlin ha hb' (fun hab ↦ hba hab.symm)
            (Or.inl ⟨htail.trans htail'.symm, hhead.trans hhead'.symm⟩)
  · rintro ⟨huv_ne, ⟨a, ⟨haF, hends⟩, _⟩⟩
    -- Conversely, the unique supported arc is already a witness for the corresponding undirected
    -- support edge.
    simp [G, Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
    refine ⟨huv_ne, ?_⟩
    rcases hends with ⟨htail, hhead⟩ | ⟨htail, hhead⟩
    · left
      rw [arc_induced_digraph_adj_iff P.tail P.head F u v]
      exact ⟨a, haF, htail, hhead⟩
    · right
      rw [arc_induced_digraph_adj_iff P.tail P.head F v u]
      exact ⟨a, haF, htail, hhead⟩

/-- Helper for Remark 4.12: every supported arc contributes its endpoint pair as an undirected
support edge once support-column independence has ruled out loops. -/
private theorem supportedGraph_adj_of_supportedArc
    [Fintype V]
    (P : ShortestPathLinearProgram V A)
    {x : A → ℝ}
    {R : Finset (Fin (Fintype.card V))}
    (hlin :
      LinearIndependent ℝ
        (fun j : Function.support (ShortestPathLinearProgram.arcCoordinates x) ↦
          fun i : Fin R.card => P.restrictedIncidenceMatrix R i j))
    {a : A} (ha : x a ≠ 0) :
    let F : Finset A := Finset.univ.filter fun b ↦ x b ≠ 0
    let G := (arc_induced_digraph P.tail P.head F).toSimpleGraphInclusive
    G.Adj (P.tail a) (P.head a) := by
  classical
  let F : Finset A := Finset.univ.filter fun b ↦ x b ≠ 0
  let G := (arc_induced_digraph P.tail P.head F).toSimpleGraphInclusive
  change G.Adj (P.tail a) (P.head a)
  have htail_head : P.tail a ≠ P.head a :=
    supportColumnsLinearIndependent_forces_noSupportedLoop P hlin ha
  -- The adjacency adapter turns the supported arc itself into the unique support witness.
  refine (supportedGraphAdj_iff_existsUniqueArc (P := P) (x := x) (R := R) hlin
    (u := P.tail a) (v := P.head a)).2 ?_
  refine ⟨htail_head, ⟨a, ?_, ?_⟩⟩
  · refine ⟨by simp [ha], Or.inl ⟨rfl, rfl⟩⟩
  · intro b hb
    rcases hb with ⟨hbF, (⟨htail, hhead⟩ | ⟨htail, hhead⟩)⟩
    · by_cases hba : b = a
      · exact hba
      · exfalso
        have hb' : x b ≠ 0 := (Finset.mem_filter.mp hbF).2
        exact supportColumnsLinearIndependent_forcesNoParallelOrOppositeSupportedPair
          P hlin ha hb' (fun hab ↦ hba hab.symm) (Or.inl ⟨htail.symm, hhead.symm⟩)
    · by_cases hba : b = a
      · exact hba
      · exfalso
        have hb' : x b ≠ 0 := (Finset.mem_filter.mp hbF).2
        exact supportColumnsLinearIndependent_forcesNoParallelOrOppositeSupportedPair
          P hlin ha hb' (fun hab ↦ hba hab.symm) (Or.inr ⟨hhead.symm, htail.symm⟩)

/-- Helper for Remark 4.12: `restrictedRowVertex R i` is the original vertex represented by the
retained balance row `i`. -/
private noncomputable def restrictedRowVertex
    [Fintype V]
    (R : Finset (Fin (Fintype.card V))) (i : Fin R.card) : V :=
  (Fintype.equivFin V).symm (((Fintype.equivFinOfCardEq (Fintype.card_coe R)).symm i).1)

/-- Helper for Remark 4.12: a supported arc gives a nonzero coordinate in the exact
`arcCoordinates` owner used by the restricted-column family. -/
private theorem arcCoordinates_ne_zero_of_ne_zero
    {x : A → ℝ} {a : A} (ha : x a ≠ 0) :
    ShortestPathLinearProgram.arcCoordinates x (Fintype.equivFin A a) ≠ 0 := by
  -- The canonical `Fin` reindexing does not change whether a coordinate is zero.
  simpa [ShortestPathLinearProgram.arcCoordinates] using ha

/-- Helper for Remark 4.12: package a supported arc as an index of the exact support subtype used
by the restricted incidence-column family. -/
private noncomputable def supportIndexOfArc
    (x : A → ℝ) {a : A} (ha : x a ≠ 0) :
    Function.support (ShortestPathLinearProgram.arcCoordinates x) :=
  ⟨Fintype.equivFin A a, arcCoordinates_ne_zero_of_ne_zero (x := x) ha⟩

/-- Helper for Remark 4.12: adding a single support coefficient adds exactly that restricted
incidence column to the linear combination. -/
private theorem restrictedIncidenceAddSingleCoefficientSum
    [Fintype V]
    (P : ShortestPathLinearProgram V A)
    {x : A → ℝ}
    {R : Finset (Fin (Fintype.card V))}
    (σ : Function.support (ShortestPathLinearProgram.arcCoordinates x) → ℝ)
    (j : Function.support (ShortestPathLinearProgram.arcCoordinates x)) (r : ℝ) :
    (∑ k : Function.support (ShortestPathLinearProgram.arcCoordinates x),
        (σ k + if k = j then r else 0) •
          (fun i : Fin R.card => P.restrictedIncidenceMatrix R i k)) =
      (∑ k : Function.support (ShortestPathLinearProgram.arcCoordinates x),
          σ k • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i k)) +
        r • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i j) := by
  -- Rewrite the updated coefficient family as the old relation plus one singleton column.
  simp_rw [add_smul]
  rw [Finset.sum_add_distrib]
  simp

/-- Helper for Remark 4.12: traversing a supported arc contributes the restricted endpoint-delta
vector, with sign determined by whether the stored orientation agrees with the traversal. -/
private theorem restrictedIncidenceColumn_eq_endpoint_delta
    [Fintype V]
    (P : ShortestPathLinearProgram V A)
    (R : Finset (Fin (Fintype.card V)))
    {a : A} {u v : V} (hne : u ≠ v)
    (hends : (P.tail a = u ∧ P.head a = v) ∨ (P.tail a = v ∧ P.head a = u)) :
    let sign : ℝ := if P.tail a = u ∧ P.head a = v then 1 else -1
    sign • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i (Fintype.equivFin A a)) =
      fun i : Fin R.card ↦
        (if restrictedRowVertex R i = v then (1 : ℝ) else 0) -
          (if restrictedRowVertex R i = u then 1 else 0) := by
  classical
  rcases hends with hforward | hreverse
  · -- In the forward orientation, the restricted column is already the endpoint delta.
    have htail_ne_head : P.tail a ≠ P.head a := by
      simpa [hforward.1, hforward.2] using hne
    have hsign : (if P.tail a = u ∧ P.head a = v then (1 : ℝ) else -1) = 1 := by
      simp [hforward]
    ext i
    by_cases hiv : restrictedRowVertex R i = v
    · have hentry :
          P.restrictedIncidenceMatrix R i (Fintype.equivFin A a) = 1 := by
        have hw_head : restrictedRowVertex R i = P.head a := by
          simpa [hforward.2] using hiv
        have hentry' :
            digraph_incidence_matrix ℝ P.tail P.head (restrictedRowVertex R i) a = 1 := by
          simpa [hw_head] using (digraph_incidence_matrix_head ℝ P.tail P.head a htail_ne_head)
        simpa [ShortestPathLinearProgram.restrictedIncidenceMatrix,
          ShortestPathLinearProgram.incidenceMatrix, restrictedRowVertex] using hentry'
      rw [Pi.smul_apply, hsign, hentry]
      have hvu : v ≠ u := hne.symm
      simp [hiv, hvu]
    · by_cases hiu : restrictedRowVertex R i = u
      · have hentry :
            P.restrictedIncidenceMatrix R i (Fintype.equivFin A a) = -1 := by
          have hw_tail : restrictedRowVertex R i = P.tail a := by
            simpa [hforward.1] using hiu
          have hentry' :
              digraph_incidence_matrix ℝ P.tail P.head (restrictedRowVertex R i) a = -1 := by
            simpa [hw_tail] using (digraph_incidence_matrix_tail ℝ P.tail P.head a htail_ne_head)
          simpa [ShortestPathLinearProgram.restrictedIncidenceMatrix,
            ShortestPathLinearProgram.incidenceMatrix, restrictedRowVertex] using hentry'
        rw [Pi.smul_apply, hsign, hentry]
        have huv : u ≠ v := hne
        simp [hiu, huv]
      · have hentry :
            P.restrictedIncidenceMatrix R i (Fintype.equivFin A a) = 0 := by
          have hw_tail : restrictedRowVertex R i ≠ P.tail a := by
            simpa [hforward.1] using hiu
          have hw_head : restrictedRowVertex R i ≠ P.head a := by
            simpa [hforward.2] using hiv
          simpa [ShortestPathLinearProgram.restrictedIncidenceMatrix,
            ShortestPathLinearProgram.incidenceMatrix, restrictedRowVertex] using
            (digraph_incidence_matrix_eq_zero_of_ne_endpoints ℝ P.tail P.head hw_tail hw_head)
        rw [Pi.smul_apply, hsign, hentry]
        simp [hiv, hiu]
  · -- Route correction: the reverse orientation contributes the negated endpoint delta.
    have htail_ne_head : P.tail a ≠ P.head a := by
      simpa [hreverse.1, hreverse.2] using hne.symm
    have hnot_forward : ¬ (P.tail a = u ∧ P.head a = v) := by
      intro hforward
      exact hne (hforward.1.symm.trans hreverse.1)
    have hsign : (if P.tail a = u ∧ P.head a = v then (1 : ℝ) else -1) = -1 := by
      simp [hnot_forward]
    ext i
    by_cases hiv : restrictedRowVertex R i = v
    · have hentry :
          P.restrictedIncidenceMatrix R i (Fintype.equivFin A a) = -1 := by
        have hw_tail : restrictedRowVertex R i = P.tail a := by
          simpa [hreverse.1] using hiv
        have hentry' :
            digraph_incidence_matrix ℝ P.tail P.head (restrictedRowVertex R i) a = -1 := by
          simpa [hw_tail] using (digraph_incidence_matrix_tail ℝ P.tail P.head a htail_ne_head)
        simpa [ShortestPathLinearProgram.restrictedIncidenceMatrix,
          ShortestPathLinearProgram.incidenceMatrix, restrictedRowVertex] using hentry'
      rw [Pi.smul_apply, hsign, hentry]
      have hvu : v ≠ u := hne.symm
      simp [hiv, hvu]
    · by_cases hiu : restrictedRowVertex R i = u
      · have hentry :
            P.restrictedIncidenceMatrix R i (Fintype.equivFin A a) = 1 := by
          have hw_head : restrictedRowVertex R i = P.head a := by
            simpa [hreverse.2] using hiu
          have hentry' :
              digraph_incidence_matrix ℝ P.tail P.head (restrictedRowVertex R i) a = 1 := by
            simpa [hw_head] using (digraph_incidence_matrix_head ℝ P.tail P.head a htail_ne_head)
          simpa [ShortestPathLinearProgram.restrictedIncidenceMatrix,
            ShortestPathLinearProgram.incidenceMatrix, restrictedRowVertex] using hentry'
        rw [Pi.smul_apply, hsign, hentry]
        have huv : u ≠ v := hne
        simp [hiu, huv]
      · have hentry :
            P.restrictedIncidenceMatrix R i (Fintype.equivFin A a) = 0 := by
          have hw_tail : restrictedRowVertex R i ≠ P.tail a := by
            simpa [hreverse.1] using hiv
          have hw_head : restrictedRowVertex R i ≠ P.head a := by
            simpa [hreverse.2] using hiu
          simpa [ShortestPathLinearProgram.restrictedIncidenceMatrix,
            ShortestPathLinearProgram.incidenceMatrix, restrictedRowVertex] using
            (digraph_incidence_matrix_eq_zero_of_ne_endpoints ℝ P.tail P.head hw_tail hw_head)
        rw [Pi.smul_apply, hsign, hentry]
        simp [hiv, hiu]

/-- Helper for Remark 4.12: a walk in the supported undirected graph yields a signed restricted
incidence relation telescoping to the endpoint-delta vector on the retained rows. -/
private theorem supportedWalkRestrictedIncidence_telescopes
    [Fintype V]
    (P : ShortestPathLinearProgram V A)
    {x : A → ℝ}
    {R : Finset (Fin (Fintype.card V))}
    {F : Finset A}
    {G : SimpleGraph V}
    (hAdj :
      ∀ {u v : V}, G.Adj u v ↔
        u ≠ v ∧ ∃! a,
          a ∈ F ∧ ((P.tail a = u ∧ P.head a = v) ∨ (P.tail a = v ∧ P.head a = u)))
    (hF : F = Finset.univ.filter fun a ↦ x a ≠ 0)
    {u v : V} (q : G.Walk u v) :
    ∃ σ : Function.support (ShortestPathLinearProgram.arcCoordinates x) → ℝ,
      ((∑ j : Function.support (ShortestPathLinearProgram.arcCoordinates x),
          σ j • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i j)) =
        (fun i : Fin R.card ↦
          (if restrictedRowVertex R i = v then (1 : ℝ) else 0) -
            (if restrictedRowVertex R i = u then 1 else 0))) ∧
      (∀ j : Function.support (ShortestPathLinearProgram.arcCoordinates x), σ j ≠ 0 →
          s(P.tail ((Fintype.equivFin A).symm j.1), P.head ((Fintype.equivFin A).symm j.1))
            ∈ q.edges) := by
  classical
  letI : Fintype (Function.support (ShortestPathLinearProgram.arcCoordinates x)) :=
    CategoryTheory.FinCategory.fintypeObj
  -- Route correction: keep the exact support subtype spelling from the theorem statement so the
  -- finite sums and restricted columns never need transport rewrites during the walk induction.
  induction q with
  | nil =>
      refine ⟨fun _ ↦ 0, ?_, ?_⟩
      · -- The empty walk telescopes to the zero endpoint delta.
        ext i
        simp
      · intro j hσ
        exact False.elim (hσ rfl)
  | @cons u w v huw q ih =>
      rcases ih with ⟨σ, hσsum, hσsupp⟩
      rcases (hAdj (u := u) (v := w)).1 huw with ⟨huw_ne, ⟨a, ⟨haF, hends⟩, _⟩⟩
      have ha : x a ≠ 0 := by
        rw [hF] at haF
        exact (Finset.mem_filter.mp haF).2
      let j : Function.support (ShortestPathLinearProgram.arcCoordinates x) := supportIndexOfArc x ha
      let sign : ℝ := if P.tail a = u ∧ P.head a = w then 1 else -1
      have hedge :
          s(P.tail a, P.head a) = s(u, w) := by
        rcases hends with ⟨htail, hhead⟩ | ⟨htail, hhead⟩
        · simpa [htail, hhead]
        · simpa [htail, hhead]
      have hcol :
          sign • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i j) =
            (fun i : Fin R.card ↦
              (if restrictedRowVertex R i = w then (1 : ℝ) else 0) -
                (if restrictedRowVertex R i = u then 1 else 0)) := by
        simpa [j, sign, supportIndexOfArc] using
          (restrictedIncidenceColumn_eq_endpoint_delta (P := P) (R := R)
            (a := a) (u := u) (v := w) huw_ne hends)
      have hdelta :
          (fun i : Fin R.card ↦
            ((if restrictedRowVertex R i = v then (1 : ℝ) else 0) -
                (if restrictedRowVertex R i = w then 1 else 0)) +
              ((if restrictedRowVertex R i = w then (1 : ℝ) else 0) -
                (if restrictedRowVertex R i = u then 1 else 0))) =
            (fun i : Fin R.card ↦
              (if restrictedRowVertex R i = v then (1 : ℝ) else 0) -
                (if restrictedRowVertex R i = u then 1 else 0)) := by
        ext i
        simp
      refine ⟨fun k ↦ σ k + if k = j then sign else 0, ?_, ?_⟩
      · -- Add the first-edge column to the suffix relation and let the endpoint deltas telescope.
        calc
          (∑ k : Function.support (ShortestPathLinearProgram.arcCoordinates x),
              (σ k + if k = j then sign else 0) •
                (fun i : Fin R.card => P.restrictedIncidenceMatrix R i k)) =
              (∑ k : Function.support (ShortestPathLinearProgram.arcCoordinates x),
                  σ k • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i k)) +
                sign • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i j) := by
                  simpa [j, sign] using
                    (restrictedIncidenceAddSingleCoefficientSum
                      (P := P) (x := x) (R := R) σ j sign)
          _ =
              (fun i : Fin R.card ↦
                (if restrictedRowVertex R i = v then (1 : ℝ) else 0) -
                  (if restrictedRowVertex R i = w then 1 else 0)) +
                (fun i : Fin R.card ↦
                  (if restrictedRowVertex R i = w then (1 : ℝ) else 0) -
                    (if restrictedRowVertex R i = u then 1 else 0)) := by
                rw [hσsum, hcol]
          _ =
              (fun i : Fin R.card ↦
                (if restrictedRowVertex R i = v then (1 : ℝ) else 0) -
                  (if restrictedRowVertex R i = u then 1 else 0)) := hdelta
      · intro k hk
        by_cases hkj : k = j
        · -- The new nonzero coefficient is carried by the first traversed support edge.
          subst hkj
          have hjval : (Fintype.equivFin A).symm j.1 = a := by
            simp [j, supportIndexOfArc]
          have hmem :
              s(P.tail ((Fintype.equivFin A).symm j.1),
                  P.head ((Fintype.equivFin A).symm j.1)) ∈
                (SimpleGraph.Walk.cons huw q).edges := by
            rw [SimpleGraph.Walk.edges_cons]
            rw [hjval]
            simp [hedge]
          simpa [hjval] using hmem
        · -- Any other nonzero coefficient already came from the suffix walk.
          have hσk : σ k ≠ 0 := by
            intro hzero
            apply hk
            simp [hkj, hzero]
          have hmem :
              s(P.tail ((Fintype.equivFin A).symm k.1),
                  P.head ((Fintype.equivFin A).symm k.1)) ∈ q.edges :=
            hσsupp k hσk
          simpa [SimpleGraph.Walk.edges_cons] using Or.inr hmem

/-- Helper for Remark 4.12: an undirected support cycle gives a nontrivial linear dependence among
the restricted incidence columns indexed by the exact positive support. -/
private theorem restrictedIncidenceColumns_notLinearIndependent_of_supportedUndirectedCycle
    [Fintype V]
    (P : ShortestPathLinearProgram V A)
    {x : A → ℝ}
    {R : Finset (Fin (Fintype.card V))}
    {F : Finset A}
    {G : SimpleGraph V}
    (hAdj :
      ∀ {u v : V}, G.Adj u v ↔
        u ≠ v ∧ ∃! a,
          a ∈ F ∧ ((P.tail a = u ∧ P.head a = v) ∨ (P.tail a = v ∧ P.head a = u)))
    (hF : F = Finset.univ.filter fun a ↦ x a ≠ 0)
    (hcycle : ∃ u, ∃ q : G.Walk u u, q.IsCycle) :
    ¬ LinearIndependent ℝ
      (fun j : Function.support (ShortestPathLinearProgram.arcCoordinates x) ↦
        fun i : Fin R.card => P.restrictedIncidenceMatrix R i j) := by
  classical
  letI : Fintype (Function.support (ShortestPathLinearProgram.arcCoordinates x)) :=
    CategoryTheory.FinCategory.fintypeObj
  rcases hcycle with ⟨u, p, hpcycle⟩
  rcases SimpleGraph.Walk.not_nil_iff.mp hpcycle.not_nil with ⟨w, huw, q, hpcons⟩
  have hpcycle' : (SimpleGraph.Walk.cons huw q).IsCycle := by
    simpa [hpcons] using hpcycle
  have hqinfo := (SimpleGraph.Walk.cons_isCycle_iff q huw).1 hpcycle'
  rcases hqinfo with ⟨_, hfirst_not_mem⟩
  rcases (hAdj (u := u) (v := w)).1 huw with ⟨huw_ne, ⟨a, ⟨haF, hends⟩, _⟩⟩
  have ha : x a ≠ 0 := by
    rw [hF] at haF
    exact (Finset.mem_filter.mp haF).2
  let j : Function.support (ShortestPathLinearProgram.arcCoordinates x) := supportIndexOfArc x ha
  let sign : ℝ := if P.tail a = u ∧ P.head a = w then 1 else -1
  rcases supportedWalkRestrictedIncidence_telescopes
      (P := P) (x := x) (R := R) (F := F) (G := G) hAdj hF q with
    ⟨σ, hσsum, hσsupp⟩
  have hedge :
      s(P.tail a, P.head a) = s(u, w) := by
    rcases hends with ⟨htail, hhead⟩ | ⟨htail, hhead⟩
    · simpa [htail, hhead]
    · simpa [htail, hhead]
  have hσj_zero : σ j = 0 := by
    by_contra hσj
    have hmem :
        s(P.tail ((Fintype.equivFin A).symm j.1),
            P.head ((Fintype.equivFin A).symm j.1)) ∈ q.edges :=
      hσsupp j hσj
    have hjval : (Fintype.equivFin A).symm j.1 = a := by
      simp [j, supportIndexOfArc]
    have hmem' : s(P.tail a, P.head a) ∈ q.edges := by
      simpa [hjval] using hmem
    exact hfirst_not_mem (hedge ▸ hmem')
  have hcol :
      sign • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i j) =
        (fun i : Fin R.card ↦
          (if restrictedRowVertex R i = w then (1 : ℝ) else 0) -
            (if restrictedRowVertex R i = u then 1 else 0)) := by
    simpa [j, sign, supportIndexOfArc] using
      (restrictedIncidenceColumn_eq_endpoint_delta (P := P) (R := R)
        (a := a) (u := u) (v := w) huw_ne hends)
  have hzero :
      (fun i : Fin R.card ↦
        ((if restrictedRowVertex R i = u then (1 : ℝ) else 0) -
            (if restrictedRowVertex R i = w then 1 else 0)) +
          ((if restrictedRowVertex R i = w then (1 : ℝ) else 0) -
            (if restrictedRowVertex R i = u then 1 else 0))) = 0 := by
    ext i
    simp
  rw [Fintype.not_linearIndependent_iff]
  refine ⟨fun k ↦ σ k + if k = j then sign else 0, ?_, ?_⟩
  · -- The suffix contributes `δ_u - δ_w`; adding the first edge gives `δ_w - δ_u`.
    calc
      (∑ k : Function.support (ShortestPathLinearProgram.arcCoordinates x),
          (σ k + if k = j then sign else 0) •
            (fun i : Fin R.card => P.restrictedIncidenceMatrix R i k)) =
          (∑ k : Function.support (ShortestPathLinearProgram.arcCoordinates x),
              σ k • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i k)) +
            sign • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i j) := by
              simp_rw [add_smul]
              rw [Finset.sum_add_distrib]
              simp
      _ =
          (fun i : Fin R.card ↦
            (if restrictedRowVertex R i = u then (1 : ℝ) else 0) -
              (if restrictedRowVertex R i = w then 1 else 0)) +
            sign • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i j) := by
              simpa using
                congrArg
                  (fun f : Fin R.card → ℝ ↦
                    f + sign • (fun i : Fin R.card => P.restrictedIncidenceMatrix R i j))
                  hσsum
      _ =
          (fun i : Fin R.card ↦
            (if restrictedRowVertex R i = u then (1 : ℝ) else 0) -
              (if restrictedRowVertex R i = w then 1 else 0)) +
            (fun i : Fin R.card ↦
              (if restrictedRowVertex R i = w then (1 : ℝ) else 0) -
                (if restrictedRowVertex R i = u then 1 else 0)) := by
              rw [hcol]
      _ = 0 := hzero
  · -- The first supported edge carries the new nonzero coefficient, so the dependence is nontrivial.
    refine ⟨j, ?_⟩
    by_cases hforward : P.tail a = u ∧ P.head a = w
    · simpa [j, sign, hσj_zero, hforward]
    · simpa [j, sign, hσj_zero, hforward]

/-- Remark 4.12 (2): if `(4.7)` is feasible and `D` contains no negative-length circuit, then the
shortest-path linear program `(4.7)` has an optimal solution. -/
theorem no_negative_length_circuit_implies_shortest_path_lp_has_optimal_solution
    (P : ShortestPathLinearProgram V A)
    (hfeas : P.HasFeasibleSolution)
    (hneg : P.HasNoNegativeLengthCircuit) :
    P.HasOptimalSolution := by
  rcases hfeas with ⟨x, hx⟩
  have hst : P.s ≠ P.t :=
    ShortestPathLinearProgram.IsFeasible.source_ne_sink (P := P) (x := x) hx
  have hpathsNonempty : {p : List A | P.IsStPath p}.Nonempty := by
    rcases existsStPath_le_objective_of_feasible P hx hneg with ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  have hpathsFinite : {p : List A | P.IsStPath p}.Finite := by
    refine (List.finite_length_le A (Fintype.card A)).subset ?_
    intro p hp
    have hnodupArcs : p.Nodup :=
      directedWalk_nodup_of_verticesNodup P hp.1 hp.2
    exact List.Nodup.length_le_card hnodupArcs
  rcases Set.exists_min_image {p : List A | P.IsStPath p} P.pathLength hpathsFinite hpathsNonempty
      with ⟨p, hp, hpmin⟩
  have hpSpec := stPathCharacteristic_spec P hst hp
  refine ⟨circuit_characteristic_vector p.toFinset, ?_⟩
  refine ⟨hpSpec.1, ?_⟩
  intro y hy
  rcases existsStPath_le_objective_of_feasible P hy hneg with ⟨q, hq, hqle⟩
  -- Minimize over the finite family of `s,t`-paths and compare an arbitrary feasible flow by the
  -- comparison lemma above.
  calc
    P.objective (circuit_characteristic_vector p.toFinset) = P.pathLength p := hpSpec.2
    _ ≤ P.pathLength q := hpmin q hq
    _ ≤ P.objective y := hqle

/-- Helper for Remark 4.12: a basic optimal solution packages a single supported digraph whose
undirected support graph is acyclic and whose adjacency is witnessed by unique supported arcs. -/
private theorem basicOptimal_supportGraphAcyclic
    [Fintype V]
    (P : ShortestPathLinearProgram V A)
    {x : A → ℝ}
    (hx : P.IsBasicOptimalSolution x) :
    ∃ (R : Finset (Fin (Fintype.card V))) (F : Finset A) (G : SimpleGraph V),
      F = Finset.univ.filter (fun a ↦ x a ≠ 0) ∧
      G = (arc_induced_digraph P.tail P.head F).toSimpleGraphInclusive ∧
      (∀ {u v : V}, G.Adj u v ↔
        u ≠ v ∧ ∃! a,
          a ∈ F ∧ ((P.tail a = u ∧ P.head a = v) ∨ (P.tail a = v ∧ P.head a = u))) ∧
      (∀ {a : A}, x a ≠ 0 → G.Adj (P.tail a) (P.head a)) ∧
      G.IsAcyclic := by
  rcases basicOptimal_exists_componentReducedRows_with_linearIndependentSupport P hx with
    ⟨R, _, hlinR⟩
  let F : Finset A := Finset.univ.filter fun a ↦ x a ≠ 0
  let G := (arc_induced_digraph P.tail P.head F).toSimpleGraphInclusive
  refine ⟨R, F, G, rfl, rfl, ?_, ?_, ?_⟩
  · intro u v
    -- Translate support-graph adjacency into the unique-supported-arc interface induced by `hlinR`.
    simpa [F, G] using
      (supportedGraphAdj_iff_existsUniqueArc (P := P) (x := x) (R := R) hlinR (u := u) (v := v))
  · intro a ha
    -- Every supported arc yields its endpoint edge in the undirected support graph.
    simpa [F, G] using
      (supportedGraph_adj_of_supportedArc (P := P) (x := x) (R := R) hlinR ha)
  · -- Route correction: support-column independence already forbids every undirected support cycle.
    by_contra hnotAcyc
    rcases (SimpleGraph.exists_girth_eq_length (G := G)).2 hnotAcyc with
      ⟨u, q, hqcycle, _⟩
    exact
      restrictedIncidenceColumns_notLinearIndependent_of_supportedUndirectedCycle
        (P := P) (x := x) (R := R) (F := F) (G := G)
        (by
          intro u v
          simpa [F, G] using
            (supportedGraphAdj_iff_existsUniqueArc
              (P := P) (x := x) (R := R) hlinR (u := u) (v := v)))
        rfl ⟨u, q, hqcycle⟩ hlinR

/-- Remark 4.12 (3): every basic optimal solution of `(4.7)` is the characteristic vector of a
shortest `s,t`-path. The no-negative-circuit condition is already forced by optimality. -/
theorem basic_optimal_solution_is_characteristic_vector_of_shortest_st_path
    [Fintype V]
    (P : ShortestPathLinearProgram V A)
    {x : A → ℝ}
    (hx : P.IsBasicOptimalSolution x) :
    P.IsCharacteristicVectorOfShortestStPath x := by
  have hst : P.s ≠ P.t :=
    ShortestPathLinearProgram.IsFeasible.source_ne_sink (P := P) (x := x) hx.2.1
  -- Helper for Remark 4.12: a directed walk whose arcs stay in the support of `x` induces an
  -- undirected walk in the support graph with the same visited-vertex list.
  have exists_supportGraphWalk_of_supportedDirectedWalk :
      ∀ {R : Finset (Fin (Fintype.card V))}
        {F : Finset A} {G : SimpleGraph V},
        (∀ {a : A}, x a ≠ 0 → G.Adj (P.tail a) (P.head a)) →
        ∀ {u v : V} {p : List A},
          P.IsDirectedWalkFromTo u v p →
          (∀ a ∈ p.toFinset, x a ≠ 0) →
          ∃ q : G.Walk u v,
            q.length = p.length ∧
              q.support = P.walkVerticesFrom u p := by
    intro R F G hArcAdj
    intro u v p
    induction p generalizing u with
    | nil =>
        intro hp hsupp
        subst hp
        refine ⟨SimpleGraph.Walk.nil, rfl, ?_⟩
        simp [ShortestPathLinearProgram.walkVerticesFrom]
    | cons a p ih =>
        intro hp hsupp
        rcases hp with ⟨hau, hpTail⟩
        have ha : x a ≠ 0 := hsupp a (by simp)
        have hadj : G.Adj u (P.head a) := by
          simpa [hau] using hArcAdj ha
        have hsuppTail : ∀ b ∈ p.toFinset, x b ≠ 0 := by
          intro b hb
          exact hsupp b (by simpa using List.mem_cons_of_mem a (List.mem_toFinset.mp hb))
        rcases ih hpTail hsuppTail with ⟨q, hqlen, hqsupp⟩
        refine ⟨SimpleGraph.Walk.cons hadj q, by simpa [SimpleGraph.Walk.length_cons] using congrArg Nat.succ hqlen, ?_⟩
        simp [SimpleGraph.Walk.support_cons, ShortestPathLinearProgram.walkVerticesFrom, hqsupp]
  -- Helper for Remark 4.12: in an acyclic support graph, a supported directed circuit would force
  -- two distinct undirected `u,v` paths, so it cannot occur.
  have supportedCircuit_contradicts_acyclicSupport :
      ∀ {R : Finset (Fin (Fintype.card V))}
        {F : Finset A} {G : SimpleGraph V},
        (∀ {u v : V}, G.Adj u v ↔
          u ≠ v ∧ ∃! a,
            a ∈ F ∧ ((P.tail a = u ∧ P.head a = v) ∨ (P.tail a = v ∧ P.head a = u))) →
        F = Finset.univ.filter (fun a ↦ x a ≠ 0) →
        (∀ {a : A}, x a ≠ 0 → G.Adj (P.tail a) (P.head a)) →
        G.IsAcyclic →
        ∀ {c : List A},
          P.IsCircuit c →
          (∀ a ∈ c.toFinset, x a ≠ 0) →
          False := by
    intro R F G hAdj hF hArcAdj hacyc c hc hsupp
    rcases hc with ⟨hcne, u, hwalk, htailNodup⟩
    cases c with
    | nil =>
        exact (hcne rfl).elim
    | cons a p =>
        rcases hwalk with ⟨hau, hpTail⟩
        have ha : x a ≠ 0 := hsupp a (by simp)
        have hadj : G.Adj u (P.head a) := by
          simpa [hau] using hArcAdj ha
        have hsuppTail : ∀ b ∈ p.toFinset, x b ≠ 0 := by
          intro b hb
          exact hsupp b (by simpa using List.mem_cons_of_mem a (List.mem_toFinset.mp hb))
        have htailPathNodup : (P.walkVerticesFrom (P.head a) p).Nodup := by
          simpa [ShortestPathLinearProgram.walkVerticesFrom] using htailNodup
        rcases exists_supportGraphWalk_of_supportedDirectedWalk
            (R := R) (F := F) (G := G) hArcAdj hpTail hsuppTail with ⟨q, hqlen, hqsupp⟩
        have hqPath : q.IsPath := by
          apply SimpleGraph.Walk.IsPath.mk'
          rw [hqsupp]
          simpa using htailPathNodup
        let qrevPath : G.Path u (P.head a) := ⟨q.reverse, by simpa using hqPath.reverse⟩
        have hpathEq : SimpleGraph.Path.singleton hadj = qrevPath := by
          exact hacyc.path_unique _ _
        have hqrevLen : q.reverse.length = 1 := by
          have hpathLenEq := congrArg (fun r : G.Path u (P.head a) ↦ (r : G.Walk u (P.head a)).length)
            hpathEq.symm
          simpa [qrevPath, SimpleGraph.Path.singleton] using hpathLenEq
        have hqLenOne : q.length = 1 := by
          simpa [SimpleGraph.Walk.length_reverse] using hqrevLen
        have hpLenOne : p.length = 1 := by
          simpa [hqlen] using hqLenOne
        cases p with
        | nil =>
            simp at hpLenOne
        | cons b p' =>
            have hp'Nil : p' = [] := by
              cases p' with
              | nil => rfl
              | cons c p'' =>
                  simp at hpLenOne
            subst hp'Nil
            rcases hpTail with ⟨hbu, hpEnd⟩
            subst hpEnd
            have hb : x b ≠ 0 := hsuppTail b (by simp)
            have hF_a : a ∈ F := by
              rw [hF]
              simp [ha]
            have hF_b : b ∈ F := by
              rw [hF]
              simp [hb]
            have hadjTail : G.Adj (P.tail a) (P.head a) := by
              simpa [hau] using hadj
            rcases (hAdj (u := P.tail a) (v := P.head a)).1 hadjTail with
              ⟨huneq, ⟨e, he, heuniq⟩⟩
            have haEq : a = e := heuniq a ⟨hF_a, Or.inl ⟨rfl, rfl⟩⟩
            have hbEq : b = e := heuniq b ⟨hF_b, Or.inr ⟨hbu, hau.symm⟩⟩
            have hab : a = b := haEq.trans hbEq.symm
            have hloop : P.tail a = P.head a := by
              simpa [hau, hab, hbu]
            exact huneq (by simpa [hau] using hloop)
  -- Helper for Remark 4.12: a supported `s,t`-path induces a `SimpleGraph.Path` in the acyclic
  -- support graph with the same visited vertices.
  have supportedStPath_to_supportGraphPath :
      ∀ {R : Finset (Fin (Fintype.card V))}
        {F : Finset A} {G : SimpleGraph V},
        (∀ {a : A}, x a ≠ 0 → G.Adj (P.tail a) (P.head a)) →
        ∀ {p : List A},
          P.IsStPath p →
          (∀ a ∈ p.toFinset, x a ≠ 0) →
          ∃ q : G.Path P.s P.t,
            (q : G.Walk P.s P.t).support = P.walkVerticesFrom P.s p := by
    intro R F G hArcAdj p hp hsupp
    rcases exists_supportGraphWalk_of_supportedDirectedWalk
        (R := R) (F := F) (G := G) hArcAdj hp.1 hsupp with ⟨q, _, hqsupp⟩
    have hqPath : q.IsPath := by
      apply SimpleGraph.Walk.IsPath.mk'
      rw [hqsupp]
      simpa using hp.2
    exact ⟨⟨q, hqPath⟩, hqsupp⟩
  -- Helper for Remark 4.12: in the support graph with a unique supported arc on each undirected
  -- edge, a directed walk is determined by its visited-vertex list.
  have supportedDirectedWalk_eq_of_walkVertices_eq :
      ∀ {R : Finset (Fin (Fintype.card V))}
        {F : Finset A} {G : SimpleGraph V},
        (∀ {u v : V}, G.Adj u v ↔
          u ≠ v ∧ ∃! a,
            a ∈ F ∧ ((P.tail a = u ∧ P.head a = v) ∨ (P.tail a = v ∧ P.head a = u))) →
        F = Finset.univ.filter (fun a ↦ x a ≠ 0) →
        (∀ {a : A}, x a ≠ 0 → G.Adj (P.tail a) (P.head a)) →
        ∀ {u v : V} {p q : List A},
          P.IsDirectedWalkFromTo u v p →
          P.IsDirectedWalkFromTo u v q →
          P.walkVerticesFrom u p = P.walkVerticesFrom u q →
          (∀ a ∈ p.toFinset, x a ≠ 0) →
          (∀ a ∈ q.toFinset, x a ≠ 0) →
          p = q := by
    intro R F G hAdj hF hArcAdj
    intro u v p
    induction p generalizing u v with
    | nil =>
        intro q hp hq hverts hsuppp hsuppq
        cases q with
        | nil => rfl
        | cons b q =>
            have htail := congrArg List.tail hverts
            cases q with
            | nil =>
                simp [ShortestPathLinearProgram.walkVerticesFrom] at htail
            | cons c q' =>
                simp [ShortestPathLinearProgram.walkVerticesFrom] at htail
    | cons a p ih =>
        intro q hp hq hverts hsuppp hsuppq
        rcases hp with ⟨hau, hpTail⟩
        cases q with
        | nil =>
            have htail := congrArg List.tail hverts
            cases p with
            | nil =>
                simp [ShortestPathLinearProgram.walkVerticesFrom] at htail
            | cons c p' =>
                simp [ShortestPathLinearProgram.walkVerticesFrom] at htail
        | cons b q =>
            rcases hq with ⟨hbu, hqTail⟩
            have ha : x a ≠ 0 := hsuppp a (by simp)
            have hb : x b ≠ 0 := hsuppq b (by simp)
            have hadj : G.Adj u (P.head a) := by
              simpa [hau] using hArcAdj ha
            have hvertsTail :
                P.walkVerticesFrom (P.head a) p = P.walkVerticesFrom (P.head b) q := by
              simpa [ShortestPathLinearProgram.walkVerticesFrom] using congrArg List.tail hverts
            have hheadEq : P.head a = P.head b := by
              have hvertsHeads :
                  (a :: p).map P.head = (b :: q).map P.head := by
                simpa [walkVerticesFrom_eq_start_cons_map_head P] using congrArg List.tail hverts
              have htmp := hvertsHeads
              simp at htmp
              exact htmp.1
            rcases (hAdj (u := u) (v := P.head a)).1 hadj with ⟨hneq, ⟨e, he, heuniq⟩⟩
            have hFa : a ∈ F := by
              rw [hF]
              simp [ha]
            have hFb : b ∈ F := by
              rw [hF]
              simp [hb]
            have haEq : a = e := heuniq a ⟨hFa, Or.inl ⟨hau, rfl⟩⟩
            have hbEq : b = e := by
              apply heuniq
              refine ⟨hFb, Or.inl ?_⟩
              exact ⟨hbu, hheadEq.symm⟩
            have hab : a = b := haEq.trans hbEq.symm
            subst hab
            have hsupppTail : ∀ c ∈ p.toFinset, x c ≠ 0 := by
              intro c hc
              exact hsuppp c (by simpa using List.mem_cons_of_mem a (List.mem_toFinset.mp hc))
            have hsuppqTail : ∀ c ∈ q.toFinset, x c ≠ 0 := by
              intro c hc
              exact hsuppq c (by simpa using List.mem_cons_of_mem a (List.mem_toFinset.mp hc))
            have hvertsTail' :
                P.walkVerticesFrom (P.head a) p = P.walkVerticesFrom (P.head a) q := by
              simpa [hheadEq] using hvertsTail
            have htailEq :=
              ih hpTail hqTail hvertsTail' hsupppTail hsuppqTail
            simp [htailEq]
  -- Helper for Remark 4.12: two supported `s,t`-paths in the same acyclic support graph have the
  -- same characteristic vector.
  have supportedStPath_characteristic_eq_of_acyclicSupport :
      ∀ {R : Finset (Fin (Fintype.card V))}
        {F : Finset A} {G : SimpleGraph V},
        (∀ {u v : V}, G.Adj u v ↔
          u ≠ v ∧ ∃! a,
            a ∈ F ∧ ((P.tail a = u ∧ P.head a = v) ∨ (P.tail a = v ∧ P.head a = u))) →
        F = Finset.univ.filter (fun a ↦ x a ≠ 0) →
        (∀ {a : A}, x a ≠ 0 → G.Adj (P.tail a) (P.head a)) →
        G.IsAcyclic →
        ∀ {p q : List A},
          P.IsStPath p →
          P.IsStPath q →
          (∀ a ∈ p.toFinset, x a ≠ 0) →
          (∀ a ∈ q.toFinset, x a ≠ 0) →
          circuit_characteristic_vector p.toFinset =
            circuit_characteristic_vector q.toFinset := by
    intro R F G hAdj hF hArcAdj hacyc p q hp hq hsuppp hsuppq
    rcases supportedStPath_to_supportGraphPath
        (R := R) (F := F) (G := G) hArcAdj hp hsuppp with ⟨ppath, hppath⟩
    rcases supportedStPath_to_supportGraphPath
        (R := R) (F := F) (G := G) hArcAdj hq hsuppq with ⟨qpath, hqpath⟩
    have hpathEq : ppath = qpath := hacyc.path_unique _ _
    have hverts :
        P.walkVerticesFrom P.s p = P.walkVerticesFrom P.s q := by
      have hsupportEq :
          ((ppath : G.Walk P.s P.t).support) =
            ((qpath : G.Walk P.s P.t).support) := by
        exact congrArg (fun r : G.Path P.s P.t ↦ ((r : G.Walk P.s P.t).support)) hpathEq
      simpa [hppath, hqpath] using hsupportEq
    have hpqEq :
        p = q :=
      supportedDirectedWalk_eq_of_walkVertices_eq
        (R := R) (F := F) (G := G) hAdj hF hArcAdj hp.1 hq.1 hverts hsuppp hsuppq
    simpa [hpqEq]
  -- Helper for Remark 4.12: a feasible unit flow whose positive support stays inside the acyclic
  -- support graph of `x` must already be a single supported `s,t`-path indicator.
  have acyclicSupportedFeasible_eq_characteristic :
      ∀ {R : Finset (Fin (Fintype.card V))}
        {F : Finset A} {G : SimpleGraph V},
        (∀ {u v : V}, G.Adj u v ↔
          u ≠ v ∧ ∃! a,
            a ∈ F ∧ ((P.tail a = u ∧ P.head a = v) ∨ (P.tail a = v ∧ P.head a = u))) →
        F = Finset.univ.filter (fun a ↦ x a ≠ 0) →
        (∀ {a : A}, x a ≠ 0 → G.Adj (P.tail a) (P.head a)) →
        G.IsAcyclic →
        ∀ {y : A → ℝ},
          P.IsFeasible y →
          (∀ a, 0 < y a → x a ≠ 0) →
          ∃ p : List A, P.IsStPath p ∧ y = circuit_characteristic_vector p.toFinset := by
    intro R F G hAdj hF hArcAdj hacyc
    have hmain :
        ∀ n, ∀ y : A → ℝ,
          (positiveSupport y).card = n →
          P.IsFeasible y →
          (∀ a, 0 < y a → x a ≠ 0) →
          ∃ p : List A, P.IsStPath p ∧ y = circuit_characteristic_vector p.toFinset := by
      intro n
      refine Nat.strong_induction_on n ?_
      intro n ih y hycard hy hsub
      rcases positiveSupportPathOrCircuit P hy with hcir | hpath
      · rcases hcir with ⟨c, hc, hcpos⟩
        exact False.elim <|
          supportedCircuit_contradicts_acyclicSupport
            (R := R) (F := F) (G := G) hAdj hF hArcAdj hacyc hc
            (fun a ha ↦ hsub a (hcpos a ha))
      · rcases hpath with ⟨p, hp, hposp⟩
        have hpNodup : p.Nodup :=
          directedWalk_nodup_of_verticesNodup P hp.1 hp.2
        have hpne : p ≠ [] := by
          intro hnil
          have : P.s = P.t := by
            simpa [ShortestPathLinearProgram.IsStPath, ShortestPathLinearProgram.IsStWalk,
              ShortestPathLinearProgram.IsDirectedWalkFromTo, hnil] using hp.1
          exact hst this
        have hpToFinsetNonempty : p.toFinset.Nonempty := by
          rcases List.ne_nil_iff_exists_cons.mp hpne with ⟨a, q, rfl⟩
          exact ⟨a, by simp⟩
        rcases Finset.exists_min_image p.toFinset y hpToFinsetNonempty with
          ⟨a₀, ha₀, hmin⟩
        let μ : ℝ := min (1 : ℝ) (y a₀)
        have hμpos : 0 < μ := by
          have ha₀pos : 0 < y a₀ := hposp a₀ ha₀
          dsimp [μ]
          exact lt_min (by norm_num) ha₀pos
        have hμle : μ ≤ 1 := by
          dsimp [μ]
          exact min_le_left _ _
        have hbound : ∀ a ∈ p.toFinset, μ ≤ y a := by
          intro a ha
          exact le_trans (by simpa [μ] using (min_le_right (1 : ℝ) (y a₀))) (hmin a ha)
        by_cases hμone : μ = 1
        · have hdom : circuit_characteristic_vector p.toFinset ≤ y := by
            intro a
            by_cases ha : a ∈ p.toFinset
            · have hya : 1 ≤ y a := by
                calc
                  (1 : ℝ) = μ := by simpa [hμone]
                  _ ≤ y a := hbound a ha
              simpa [circuit_characteristic_vector_apply, ha] using hya
            · have hya : 0 ≤ y a := hy.1.nonneg a
              simpa [circuit_characteristic_vector_apply, ha] using hya
          let z : A → ℝ := y - circuit_characteristic_vector p.toFinset
          have hzCir : IsCirculation P.tail P.head z := by
            simpa [z] using feasibleResidual_isCirculation_of_stPathSub P hy hp hdom
          have hzSub : ∀ a, 0 < z a → x a ≠ 0 := by
            intro a hza
            have hya : 0 < y a := by
              by_cases ha : a ∈ p.toFinset
              · have hχ : circuit_characteristic_vector p.toFinset a = 1 := by
                  simp [circuit_characteristic_vector_apply, ha]
                have : y a = z a + 1 := by
                  simp [z, Pi.sub_apply, hχ]
                linarith
              · have hχ : circuit_characteristic_vector p.toFinset a = 0 := by
                  simp [circuit_characteristic_vector_apply, ha]
                simpa [z, Pi.sub_apply, hχ] using hza
            exact hsub a hya
          have hzZero : z = 0 := by
            by_contra hzero
            have hposz : ∃ a, 0 < z a := by
              by_contra hnotpos
              apply hzero
              ext a
              have hnonneg : 0 ≤ z a := hzCir.nonneg a
              have hnot : ¬ 0 < z a := by
                intro hlt
                exact hnotpos ⟨a, hlt⟩
              have hnonpos : z a ≤ 0 := le_of_not_gt hnot
              exact le_antisymm hnonpos hnonneg
            rcases positiveSupportCircuit_of_circulation P hzCir hposz with ⟨c, hc, hcpos⟩
            exact
              supportedCircuit_contradicts_acyclicSupport
                (R := R) (F := F) (G := G) hAdj hF hArcAdj hacyc hc
                (fun a ha ↦ hzSub a (hcpos a ha))
          refine ⟨p, hp, ?_⟩
          ext a
          have := congrArg (fun z : A → ℝ ↦ z a) hzZero
          simp [z, Pi.sub_apply] at this
          linarith [this]
        · have hμlt : μ < 1 := lt_of_le_of_ne hμle hμone
          let y' : A → ℝ := (1 / (1 - μ)) • (y - μ • circuit_characteristic_vector p.toFinset)
          have hy' : P.IsFeasible y' := by
            simpa [y'] using
              normalizedResidual_isFeasible_of_stPathSub P hy hp (le_of_lt hμpos) hμlt hbound
          have hμeq : μ = y a₀ := by
            dsimp [μ]
            by_cases ha₀le : y a₀ ≤ 1
            · rw [min_eq_right ha₀le]
            · have hone_lt : 1 < y a₀ := lt_of_not_ge ha₀le
              have : μ = 1 := by
                dsimp [μ]
                rw [min_eq_left (le_of_lt hone_lt)]
              exact False.elim (hμone this)
          have hwalk :
              walkArcVector p = circuit_characteristic_vector p.toFinset :=
            walkArcVector_eq_characteristic_of_nodup hpNodup
          have hshrinkRaw :
              (positiveSupport (y - μ • circuit_characteristic_vector p.toFinset)).card <
                (positiveSupport y).card := by
            simpa [hwalk] using
              positiveSupport_card_lt_of_sub_smul_walkArcVector
                (z := y) (p := p) hpNodup hμpos hbound ⟨a₀, ha₀, hμeq.symm⟩
          have hscalePos : 0 < 1 / (1 - μ) := by
            have hone_sub_pos : 0 < 1 - μ := by linarith
            positivity
          have hy'Sub : ∀ a, 0 < y' a → x a ≠ 0 := by
            intro a hya'
            have hresPos : 0 < (y - μ • circuit_characteristic_vector p.toFinset) a := by
              have hscale : 0 < 1 / (1 - μ) := hscalePos
              have : y' a = (1 / (1 - μ)) * (y - μ • circuit_characteristic_vector p.toFinset) a := by
                simp [y', Pi.smul_apply]
              rw [this] at hya'
              exact (mul_pos_iff_of_pos_left hscale).1 hya'
            have hya : 0 < y a := by
              by_cases ha : a ∈ p.toFinset
              · have hχ : circuit_characteristic_vector p.toFinset a = 1 := by
                  simp [circuit_characteristic_vector_apply, ha]
                have : y a = (y - μ • circuit_characteristic_vector p.toFinset) a + μ := by
                  simp [Pi.sub_apply, Pi.smul_apply, hχ]
                linarith
              · have hχ : circuit_characteristic_vector p.toFinset a = 0 := by
                  simp [circuit_characteristic_vector_apply, ha]
                simpa [Pi.sub_apply, Pi.smul_apply, hχ] using hresPos
            exact hsub a hya
          have hcardlt :
              (positiveSupport y').card < n := by
            have hscaled :
                positiveSupport y' =
                  positiveSupport (y - μ • circuit_characteristic_vector p.toFinset) := by
              simpa [y'] using
                positiveSupport_smul_of_pos
                  (x := y - μ • circuit_characteristic_vector p.toFinset) hscalePos
            rw [hscaled]
            simpa [hycard] using hshrinkRaw
          rcases ih (positiveSupport y').card hcardlt y' rfl hy' hy'Sub with
            ⟨q, hq, hy'Eq⟩
          have hqSupp : ∀ a ∈ q.toFinset, x a ≠ 0 := by
            intro a ha
            have hya' : 0 < y' a := by
              rw [hy'Eq]
              simp [circuit_characteristic_vector_apply, ha]
            exact hy'Sub a hya'
          have hpSupp : ∀ a ∈ p.toFinset, x a ≠ 0 := by
            intro a ha
            exact hsub a (hposp a ha)
          have hpathsEq :
              circuit_characteristic_vector q.toFinset =
                circuit_characteristic_vector p.toFinset := by
            exact
              supportedStPath_characteristic_eq_of_acyclicSupport
                (R := R) (F := F) (G := G) hAdj hF hArcAdj hacyc hq hp hqSupp hpSupp
          have hwDecomp :
              y = μ • circuit_characteristic_vector p.toFinset + (1 - μ) • y' := by
            ext a
            have hone_sub_ne : 1 - μ ≠ 0 := by linarith
            simp [y', Pi.smul_apply, Pi.sub_apply]
            field_simp [hone_sub_ne]
            ring
          refine ⟨p, hp, ?_⟩
          rw [hwDecomp, hy'Eq, hpathsEq]
          ext a
          by_cases ha : a ∈ p.toFinset
          · simp [Pi.smul_apply, circuit_characteristic_vector_apply, ha]
          · simp [Pi.smul_apply, circuit_characteristic_vector_apply, ha]
    intro y hy hsub
    exact hmain (positiveSupport y).card y rfl hy hsub
  have hrecover :
      ∃ p : List A, P.IsStPath p ∧ x = circuit_characteristic_vector p.toFinset := by
    rcases basicOptimal_supportGraphAcyclic (P := P) (x := x) hx with
      ⟨R, F, G, hF, _, hAdj, hArcAdj, hacyc⟩
    -- With the support graph now known to be acyclic, the remaining feasible-flow mass can only
    -- move along one supported `s,t`-path; every alternative would create a supported circuit.
    have hxsub : ∀ a, 0 < x a → x a ≠ 0 := by
      intro a hxa
      exact ne_of_gt hxa
    exact
      acyclicSupportedFeasible_eq_characteristic
        (R := R) (F := F) (G := G) hAdj hF hArcAdj hacyc hx.2.1 hxsub
  rcases hrecover with ⟨p, hp, hxeq⟩
  refine ⟨p, ?_, hxeq⟩
  exact isShortestStPath_of_optimal_characteristic P hx.2 hp hxeq

end Remark_4_12
