/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators

/-
Definition 7.22 lies in the chapter's truss-topology / simplex-constrained minimization domain.

Sampled owner-style declarations:
- `StdSimplex.Strict` in `Chap03/Definition_3_4`, the chapter owner for strictly positive simplex
  weights;
- `Matrix.PosDef`, the canonical positive-definite matrix owner for the inverse-defined stiffness
  domain;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective on a fixed ambient design space;
- `SetConstrainedMinimizationProblem.optimalValue` and `optimalValue_eq_sInf_image` in
  `Chap01/Definition_1_3_7`, the canonical constrained optimal-value owner on that ambient space;
- `Fin.castLE`, the canonical inclusion of a smaller `Fin` type into a larger one.

Best owner abstraction:
- source-facing: the truss data, the stiffness operator `B(t)`, and the objective on feasible
  strict-simplex designs;
- core/canonical: `SetConstrainedMinimizationProblem (StdSimplex.Strict ℝ (Fin m))`, with
  feasibility cutting out exactly the designs for which `B(t)` is positive definite;
- bridge/view: the source-facing feasible-design objective together with the explicit
  `sInf`-over-feasible-designs formula for the owner optimal value.

Primitive data:
- node positions, arc endpoints, the order constraint `i_k < j_k`, and external forces.
- per-arc geometric nondegeneracy, so every bar has nonzero length.

Derived API:
- the induced full-node inclusion `tailNode`;
- the optional free head `freeHead?`;
- the arc displacement, direction/vector, stacked force vector, and stiffness matrix;
- the feasible-set predicate `B(t).PosDef` on strict simplex designs;
- the objective on the feasible subtype of strict simplex designs;
- the Chapter 1 bridge `toSetConstrainedMinimizationProblem`.

Source/core/bridge triage:
- source-facing: `TrussTopologyDesignProblem` and its truss-specific geometric constructions;
- core/canonical: the constrained minimization owner on the ambient strict-simplex design space;
- bridge/view: the feasible-set and optimal-value rewrites attached to that owner.

The source-facing truss data stay in this file. The only duplicate wheel removed here is the local
infimum-valued `optimalValue` definition: the optimization layer now reuses the Chapter 1 owner
directly, which also gives the faithful `EReal` codomain for empty or unbounded cases. The
source-facing truss objective is the canonical function on the feasible subtype of strict simplex
weights, while the Chapter 1 owner keeps the ambient strict-simplex design space and uses the
feasible-set predicate only in the constrained bridge.
-/

/-- Definition 7.22: a truss topology design problem consists of node positions in `ℝ²`, arcs
joining a free node to a later node, and external forces on the free nodes. The free nodes are
indexed by `Fin n`, the fixed nodes occupy the remaining indices in `Fin (n + p)`, and the
strictly positive simplex weights used for the design objective are introduced below. The endpoint
positions of each arc are required to be distinct, so the normalized bar directions are
well-defined. -/
structure TrussTopologyDesignProblem (n p m : ℕ) where
  /-- The positions of all free and fixed nodes in `ℝ²`. -/
  nodePosition : Fin (n + p) → EuclideanSpace ℝ (Fin 2)
  /-- The tail of each arc, required to be a free node. -/
  tail : Fin m → Fin n
  /-- The head of each arc, allowed to be either free or fixed. -/
  head : Fin m → Fin (n + p)
  /-- Each arc joins its free tail to a later node, matching the condition `j_k > i_k`. -/
  tail_lt_head : ∀ k, ((tail k : Fin n) : ℕ) < (head k : ℕ)
  /-- Each arc has nonzero geometric length, so its endpoint positions are distinct. -/
  endpointPosition_ne :
    ∀ k,
      nodePosition (Fin.castLE (Nat.le_add_right n p) (tail k)) ≠ nodePosition (head k)
  /-- The external forces applied at the free nodes. -/
  externalForce : Fin n → EuclideanSpace ℝ (Fin 2)

namespace TrussTopologyDesignProblem

variable {n p m : ℕ}

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "Efree" => EuclideanSpace ℝ (Fin n × Fin 2)

/-- The inclusion of a free-node index into the full node index set. -/
def tailNode (problem : TrussTopologyDesignProblem n p m) (k : Fin m) : Fin (n + p) :=
  Fin.castLE (Nat.le_add_right n p) (problem.tail k)

/-- The free-node index corresponding to the head of an arc, when that head is not fixed. -/
def freeHead? (problem : TrussTopologyDesignProblem n p m) (k : Fin m) : Option (Fin n) :=
  if h : (problem.head k : ℕ) < n then
    some ⟨(problem.head k : ℕ), h⟩
  else
    none

/-- The displacement vector `x_{i_k} - x_{j_k}` along an arc. -/
def arcDisplacement (problem : TrussTopologyDesignProblem n p m) (k : Fin m) : E2 :=
  problem.nodePosition (problem.tailNode k) - problem.nodePosition (problem.head k)

/-- The endpoint positions of an arc are distinct, so the arc displacement is nonzero. -/
theorem arcDisplacement_ne_zero (problem : TrussTopologyDesignProblem n p m) (k : Fin m) :
    problem.arcDisplacement k ≠ 0 := by
  simpa [arcDisplacement] using sub_ne_zero.mpr (problem.endpointPosition_ne k)

/-- The squared Euclidean length of an arc is positive. -/
theorem arcLengthSq_pos (problem : TrussTopologyDesignProblem n p m) (k : Fin m) :
    0 < ‖problem.arcDisplacement k‖ ^ (2 : ℕ) := by
  refine pow_pos ?_ 2
  exact norm_pos_iff.mpr (problem.arcDisplacement_ne_zero k)

/-- The squared Euclidean length of an arc is nonzero. -/
theorem arcLengthSq_ne_zero (problem : TrussTopologyDesignProblem n p m) (k : Fin m) :
    ‖problem.arcDisplacement k‖ ^ (2 : ℕ) ≠ 0 :=
  (problem.arcLengthSq_pos k).ne'

/-- The normalized direction vector `d_k = (x_{i_k} - x_{j_k}) / ‖x_{i_k} - x_{j_k}‖²` attached
to an arc. -/
def arcDirection (problem : TrussTopologyDesignProblem n p m) (k : Fin m) : E2 :=
  (‖problem.arcDisplacement k‖ ^ (2 : ℕ))⁻¹ • problem.arcDisplacement k

/-- The block vector `a_k ∈ ℝ^(2n)` with block `d_k` at the tail, block `-d_k` at a free head,
and zero otherwise. -/
def arcVector (problem : TrussTopologyDesignProblem n p m) (k : Fin m) : Efree :=
  WithLp.toLp 2 <| fun qc : Fin n × Fin 2 ↦
    if qc.1 = problem.tail k then
      problem.arcDirection k qc.2
    else
      match problem.freeHead? k with
      | some j => if qc.1 = j then -(problem.arcDirection k qc.2) else 0
      | none => 0

/-- The stacked external force vector `f = (f₁, …, fₙ)` in block coordinates. -/
def forceVector (problem : TrussTopologyDesignProblem n p m) : Efree :=
  WithLp.toLp 2 <| fun qc : Fin n × Fin 2 ↦ problem.externalForce qc.1 qc.2

/-- The stiffness matrix `B(t) = ∑ₖ t^(k) a_k a_kᵀ` associated to a simplex design vector. -/
def stiffnessMatrix (problem : TrussTopologyDesignProblem n p m) (t : StdSimplex ℝ (Fin m)) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  ∑ k, t.weights k • Matrix.vecMulVec (problem.arcVector k) (problem.arcVector k)

namespace StiffnessMatrix

/- Source-facing Lean notation for the textbook stiffness operator `B(t)`. -/
scoped notation:max "B[" problem:arg "](" t:arg ")" => stiffnessMatrix problem t

end StiffnessMatrix

open scoped StiffnessMatrix

/-- The admissible strict-simplex designs are exactly those for which the stiffness matrix `B(t)`
is positive definite. -/
def feasibleSet (problem : TrussTopologyDesignProblem n p m) : Set (StdSimplex.Strict ℝ (Fin m)) :=
  {t | (B[problem](t)).PosDef}

/-- Membership in the feasible set means positive definiteness of the stiffness matrix `B(t)`. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : TrussTopologyDesignProblem n p m) (t : StdSimplex.Strict ℝ (Fin m)) :
    t ∈ problem.feasibleSet ↔ (B[problem](t)).PosDef :=
  Iff.rfl

/-- Every feasible strict-simplex design has positive-definite stiffness matrix. -/
theorem stiffnessMatrix_posDef
    {problem : TrussTopologyDesignProblem n p m} {t : StdSimplex.Strict ℝ (Fin m)}
    (ht : t ∈ problem.feasibleSet) :
    (B[problem](t)).PosDef := by
  simpa using ht

/-- The objective value `⟪B(t)⁻¹ f, f⟫` evaluated on the feasible-design subtype. -/
def objective (problem : TrussTopologyDesignProblem n p m) :
    problem.feasibleSet → ℝ :=
  fun t ↦ dotProduct (((B[problem](t))⁻¹).mulVec problem.forceVector) problem.forceVector

/-- A truss topology design problem can be used as its objective on feasible strict-simplex
designs. -/
instance : CoeFun (TrussTopologyDesignProblem n p m) (fun problem ↦ problem.feasibleSet → ℝ) where
  coe problem := problem.objective

/-- Evaluating a truss topology design problem at a feasible design returns the source-facing
objective value. -/
@[simp] theorem coe_apply
    (problem : TrussTopologyDesignProblem n p m) (t : problem.feasibleSet) :
    problem t = problem.objective t :=
  rfl

/-- The canonical Chapter 1 minimization owner attached to the truss topology design objective on
the ambient strict-simplex design space. -/
def toSetConstrainedMinimizationProblem
    (problem : TrussTopologyDesignProblem n p m) :
    SetConstrainedMinimizationProblem (StdSimplex.Strict ℝ (Fin m)) where
  feasibleSet := problem.feasibleSet
  objective := fun t ↦ by
    classical
    by_cases ht : t ∈ problem.feasibleSet
    · exact problem.objective ⟨t, ht⟩
    · exact 0

@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : TrussTopologyDesignProblem n p m) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- On a feasible design, the Chapter 1 bridge recovers the source-facing truss objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply_of_mem_feasibleSet
    (problem : TrussTopologyDesignProblem n p m) (t : StdSimplex.Strict ℝ (Fin m))
    (ht : t ∈ problem.feasibleSet) :
    problem.toSetConstrainedMinimizationProblem t = problem.objective ⟨t, ht⟩ := by
  simp [toSetConstrainedMinimizationProblem, objective, ht]

/-- Expanding `arcDirection` gives the normalized difference
of the endpoint positions of the arc. -/
-- Proof sketch: unfold `arcDirection`.
theorem arcDirection_eq (problem : TrussTopologyDesignProblem n p m) (k : Fin m) :
    problem.arcDirection k =
      let xi := problem.nodePosition (problem.tailNode k)
      let xj := problem.nodePosition (problem.head k)
      (‖xi - xj‖ ^ (2 : ℕ))⁻¹ • (xi - xj) := by
  -- Unfold the displacement-based definition to the displayed endpoint formula.
  simp [arcDirection, arcDisplacement]

/-- Evaluating the stacked force vector at a block index recovers the corresponding coordinate of
the external force at that free node. -/
-- Proof sketch: unfold `forceVector`; `WithLp.toLp` preserves the displayed coordinate function.
theorem forceVector_apply
    (problem : TrussTopologyDesignProblem n p m) (q : Fin n) (c : Fin 2) :
    problem.forceVector (q, c) = problem.externalForce q c := by
  -- The coordinate evaluation is definitionally the underlying external-force component.
  rfl

/-- Expanding `B[problem](t)` gives the weighted sum of the rank-one matrices `a_k a_kᵀ`. -/
-- Proof sketch: unfold `stiffnessMatrix`.
theorem stiffnessMatrix_apply
    (problem : TrussTopologyDesignProblem n p m) (t : StdSimplex ℝ (Fin m)) :
    B[problem](t) =
      ∑ k, t.weights k • Matrix.vecMulVec (problem.arcVector k) (problem.arcVector k) := by
  -- The source-facing notation `B[problem](t)` is exactly `stiffnessMatrix problem t`.
  rfl

/-- Expanding `objective` gives the quadratic form `⟪B(t)⁻¹ f, f⟫` at a feasible design. -/
-- Proof sketch: unfold `objective`.
theorem objective_eq
    (problem : TrussTopologyDesignProblem n p m) (t : problem.feasibleSet) :
    problem.objective t =
      dotProduct (((B[problem](t))⁻¹).mulVec problem.forceVector)
        problem.forceVector := by
  -- The objective is defined by this quadratic form on the feasible-design subtype.
  rfl

/-- The canonical owner optimal value for Definition 7.22 is the infimum of the objective over
feasible strict-simplex designs, viewed in `EReal`. -/
theorem optimalValue_eq_sInf_range (problem : TrussTopologyDesignProblem n p m) :
    problem.toSetConstrainedMinimizationProblem.optimalValue =
      sInf (Set.range fun t : problem.feasibleSet ↦ (problem.objective t : EReal)) := by
  rw [problem.toSetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  congr 1
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    simpa using
      congrArg (fun r : ℝ ↦ (r : EReal))
        (problem.toSetConstrainedMinimizationProblem_apply_of_mem_feasibleSet t ht).symm
  · rintro ⟨t, rfl⟩
    refine ⟨t.1, t.2, ?_⟩
    exact
      congrArg (fun r : ℝ ↦ (r : EReal))
        (problem.toSetConstrainedMinimizationProblem_apply_of_mem_feasibleSet t.1 t.2)

end TrussTopologyDesignProblem
