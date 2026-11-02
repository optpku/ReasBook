import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

open scoped BigOperators MatrixOrder

-- Semantic search note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this runner, so this file follows the `Option V`-indexed PSD witness surface from
-- Chapter 10.2 and the finite `SimpleGraph`/`Sym2` weighted-edge summation style from earlier
-- graph-polytope files by direct local inspection.

section Exercise_10_4

section Feasibility

variable {V : Type*}

/-- The `0/1` node assignments used in the textbook formulation of the max-cut problem. -/
def max_cut_node_feasible (χ : V → ℝ) : Prop :=
  ∀ v, χ v = 0 ∨ χ v = 1

/-- Membership in `max_cut_node_feasible` means that every node variable is either `0` or `1`. -/
theorem max_cut_node_feasible_iff
    {χ : V → ℝ} :
    max_cut_node_feasible χ ↔ ∀ v, χ v = 0 ∨ χ v = 1 :=
  Iff.rfl

end Feasibility

section Objectives

variable {V : Type*}

private def edgeFinsetStable (G : SimpleGraph V) [Fintype V] : Finset (Sym2 V) := by
  classical
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  let _ : Fintype G.edgeSet := by infer_instance
  exact G.edgeFinset

private theorem edgeFinsetStable_eq_edgeFinset
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    edgeFinsetStable G = G.edgeFinset := by
  classical
  simp [edgeFinsetStable]

section NodeObjective

variable (G : SimpleGraph V) [Fintype V]

noncomputable local instance : DecidableRel G.Adj := Classical.decRel G.Adj

/-- The weighted max-cut objective written with `0/1` node variables `χ`. -/
def max_cut_node_objective (G : SimpleGraph V) [Fintype V] (w : Sym2 V → ℝ) (χ : V → ℝ) : ℝ :=
  Finset.sum (edgeFinsetStable G) fun e ↦
    w e *
      Sym2.lift
        ⟨fun u v : V ↦ χ u + χ v - 2 * χ u * χ v, by
          intro u v
          ring⟩
        e

/-- `max_cut_node_objective G w χ` expands to the sum of the edge weights multiplied by the
textbook expression `χ_i + χ_j - 2 χ_i χ_j`. -/
theorem max_cut_node_objective_eq_sum
    (w : Sym2 V → ℝ) (χ : V → ℝ) :
    max_cut_node_objective G w χ =
      Finset.sum G.edgeFinset fun e ↦
        w e *
          Sym2.lift
            ⟨fun u v : V ↦ χ u + χ v - 2 * χ u * χ v, by
              intro u v
              ring⟩
            e :=
  by
    rw [max_cut_node_objective, edgeFinsetStable_eq_edgeFinset]

/-- The attainable objective values of the integral `0/1` max-cut formulation. -/
def max_cut_node_objective_values (G : SimpleGraph V) [Fintype V] (w : Sym2 V → ℝ) : Set ℝ :=
  {r | ∃ χ : V → ℝ, max_cut_node_feasible χ ∧ max_cut_node_objective G w χ = r}

/-- Membership in `max_cut_node_objective_values G w` means that `r` is attained by a feasible
`0/1` node assignment. -/
theorem mem_max_cut_node_objective_values_iff
    {w : Sym2 V → ℝ} {r : ℝ} :
    r ∈ max_cut_node_objective_values G w ↔
      ∃ χ : V → ℝ, max_cut_node_feasible χ ∧ max_cut_node_objective G w χ = r :=
  Iff.rfl

/-- The optimal value `z_I` of the integral max-cut problem. -/
def max_cut_integer_value (G : SimpleGraph V) [Fintype V] (w : Sym2 V → ℝ) : ℝ :=
  sSup (max_cut_node_objective_values G w)

/-- `max_cut_integer_value G w` is the supremum of the attainable objective values of the integral
max-cut formulation. -/
theorem max_cut_integer_value_eq_sSup
    (w : Sym2 V → ℝ) :
    max_cut_integer_value G w = sSup (max_cut_node_objective_values G w) :=
  rfl

end NodeObjective

section LiftedSdpFeasibility

/-- Feasibility for the lifted semidefinite relaxation with variables `χ` and `Z`. -/
def max_cut_sdp'_feasible
    (χ : V → ℝ) (Z : Matrix (Option V) (Option V) ℝ) : Prop :=
  Z.PosSemidef ∧
    Z none none = 1 ∧
      (∀ v : V, Z none (some v) = χ v) ∧
        (∀ v : V, Z (some v) none = χ v) ∧
          ∀ v : V, Z (some v) (some v) = χ v

/-- Membership in `max_cut_sdp'_feasible χ Z` is exactly the positive-semidefinite condition and
the affine equalities `z_{00} = 1` and `z_{0j} = z_{j0} = z_{jj} = χ_j`. -/
theorem max_cut_sdp'_feasible_iff
    {χ : V → ℝ} {Z : Matrix (Option V) (Option V) ℝ} :
    max_cut_sdp'_feasible χ Z ↔
      Z.PosSemidef ∧
        Z none none = 1 ∧
          (∀ v : V, Z none (some v) = χ v) ∧
            (∀ v : V, Z (some v) none = χ v) ∧
              ∀ v : V, Z (some v) (some v) = χ v :=
  Iff.rfl

namespace max_cut_sdp'_feasible

/-- Constructor for the feasibility conditions of the lifted max-cut semidefinite relaxation. -/
theorem mk
    {χ : V → ℝ} {Z : Matrix (Option V) (Option V) ℝ}
    (hPosSemidef : Z.PosSemidef)
    (hNoneNone : Z none none = 1)
    (hNoneSome : ∀ v : V, Z none (some v) = χ v)
    (hSomeNone : ∀ v : V, Z (some v) none = χ v)
    (hDiag : ∀ v : V, Z (some v) (some v) = χ v) :
    max_cut_sdp'_feasible χ Z :=
  ⟨hPosSemidef, hNoneNone, hNoneSome, hSomeNone, hDiag⟩

/-- A feasible lifted max-cut witness matrix is positive semidefinite. -/
theorem posSemidef
    {χ : V → ℝ} {Z : Matrix (Option V) (Option V) ℝ}
    (hZ : max_cut_sdp'_feasible χ Z) :
    Z.PosSemidef :=
  hZ.1

/-- A feasible lifted max-cut witness matrix is normalized by `Z none none = 1`. -/
theorem apply_none_none
    {χ : V → ℝ} {Z : Matrix (Option V) (Option V) ℝ}
    (hZ : max_cut_sdp'_feasible χ Z) :
    Z none none = 1 :=
  hZ.2.1

/-- The `none` row of a feasible lifted max-cut witness matrix recovers `χ`. -/
theorem apply_none_some
    {χ : V → ℝ} {Z : Matrix (Option V) (Option V) ℝ}
    (hZ : max_cut_sdp'_feasible χ Z) (v : V) :
    Z none (some v) = χ v :=
  hZ.2.2.1 v

/-- The `none` column of a feasible lifted max-cut witness matrix recovers `χ`. -/
theorem apply_some_none
    {χ : V → ℝ} {Z : Matrix (Option V) (Option V) ℝ}
    (hZ : max_cut_sdp'_feasible χ Z) (v : V) :
    Z (some v) none = χ v :=
  hZ.2.2.2.1 v

/-- The diagonal entries indexed by `some v` recover `χ v`. -/
theorem apply_some_some
    {χ : V → ℝ} {Z : Matrix (Option V) (Option V) ℝ}
    (hZ : max_cut_sdp'_feasible χ Z) (v : V) :
    Z (some v) (some v) = χ v :=
  hZ.2.2.2.2 v

end max_cut_sdp'_feasible

end LiftedSdpFeasibility

section LiftedSdpObjective

variable (G : SimpleGraph V) [Fintype V]

noncomputable local instance : DecidableRel G.Adj := Classical.decRel G.Adj

/-- The objective of the lifted semidefinite relaxation. On feasible points, the symmetric edge
term below is the textbook quantity `χ_i + χ_j - 2 z_ij`. -/
def max_cut_sdp'_objective
    (G : SimpleGraph V) [Fintype V] (w : Sym2 V → ℝ) (χ : V → ℝ)
    (Z : Matrix (Option V) (Option V) ℝ) : ℝ :=
  Finset.sum (edgeFinsetStable G) fun e ↦
    w e *
      Sym2.lift
        ⟨fun u v : V ↦ χ u + χ v - (Z (some u) (some v) + Z (some v) (some u)), by
          intro u v
          ring⟩
        e

/-- `max_cut_sdp'_objective G w χ Z` expands to the weighted sum of the lifted edge terms. -/
theorem max_cut_sdp'_objective_eq_sum
    (w : Sym2 V → ℝ) (χ : V → ℝ) (Z : Matrix (Option V) (Option V) ℝ) :
    max_cut_sdp'_objective G w χ Z =
      Finset.sum G.edgeFinset fun e ↦
        w e *
          Sym2.lift
            ⟨fun u v : V ↦ χ u + χ v - (Z (some u) (some v) + Z (some v) (some u)), by
              intro u v
              ring⟩
            e :=
  by
    rw [max_cut_sdp'_objective, edgeFinsetStable_eq_edgeFinset]

/-- The attainable objective values of the lifted semidefinite max-cut relaxation. -/
def max_cut_sdp'_objective_values (G : SimpleGraph V) [Fintype V] (w : Sym2 V → ℝ) : Set ℝ :=
  {r | ∃ χ : V → ℝ, ∃ Z : Matrix (Option V) (Option V) ℝ,
      max_cut_sdp'_feasible χ Z ∧ max_cut_sdp'_objective G w χ Z = r}

/-- Membership in `max_cut_sdp'_objective_values G w` means that `r` is attained by a feasible
lifted semidefinite point `(χ, Z)`. -/
theorem mem_max_cut_sdp'_objective_values_iff
    {w : Sym2 V → ℝ} {r : ℝ} :
    r ∈ max_cut_sdp'_objective_values G w ↔
      ∃ χ : V → ℝ, ∃ Z : Matrix (Option V) (Option V) ℝ,
        max_cut_sdp'_feasible χ Z ∧ max_cut_sdp'_objective G w χ Z = r :=
  Iff.rfl

/-- The optimal value `z'_sdp` of the lifted semidefinite max-cut relaxation. -/
def max_cut_sdp'_value (G : SimpleGraph V) [Fintype V] (w : Sym2 V → ℝ) : ℝ :=
  sSup (max_cut_sdp'_objective_values G w)

/-- `max_cut_sdp'_value G w` is the supremum of the objective values attained by feasible lifted
semidefinite points. -/
theorem max_cut_sdp'_value_eq_sSup
    (w : Sym2 V → ℝ) :
    max_cut_sdp'_value G w = sSup (max_cut_sdp'_objective_values G w) :=
  rfl

end LiftedSdpObjective

section GoemansWilliamsonFeasibility

/-- Feasibility for the Goemans-Williamson semidefinite relaxation. -/
def goemans_williamson_feasible
    (X : Matrix V V ℝ) : Prop :=
  X.PosSemidef ∧ ∀ v : V, X v v = 1

/-- Membership in `goemans_williamson_feasible X` is exactly positive semidefiniteness together
with unit diagonal. -/
theorem goemans_williamson_feasible_iff
    {X : Matrix V V ℝ} :
    goemans_williamson_feasible X ↔
      X.PosSemidef ∧ ∀ v : V, X v v = 1 :=
  Iff.rfl

namespace goemans_williamson_feasible

/-- Constructor for the feasibility conditions of the Goemans-Williamson relaxation. -/
theorem mk
    {X : Matrix V V ℝ}
    (hPosSemidef : X.PosSemidef)
    (hDiag : ∀ v : V, X v v = 1) :
    goemans_williamson_feasible X :=
  ⟨hPosSemidef, hDiag⟩

/-- A Goemans-Williamson feasible matrix is positive semidefinite. -/
theorem posSemidef
    {X : Matrix V V ℝ} (hX : goemans_williamson_feasible X) :
    X.PosSemidef :=
  hX.1

/-- A Goemans-Williamson feasible matrix has diagonal entries equal to `1`. -/
theorem diag_eq_one
    {X : Matrix V V ℝ} (hX : goemans_williamson_feasible X) (v : V) :
    X v v = 1 :=
  hX.2 v

end goemans_williamson_feasible

end GoemansWilliamsonFeasibility

section GoemansWilliamsonObjective

variable (G : SimpleGraph V) [Fintype V]

noncomputable local instance : DecidableRel G.Adj := Classical.decRel G.Adj

/-- The Goemans-Williamson objective. On feasible matrices, the symmetric edge term below is the
usual textbook quantity `(1 - X_ij) / 2`. -/
def goemans_williamson_objective
    (G : SimpleGraph V) [Fintype V] (w : Sym2 V → ℝ) (X : Matrix V V ℝ) : ℝ :=
  Finset.sum (edgeFinsetStable G) fun e ↦
    w e *
      Sym2.lift
        ⟨fun u v : V ↦ ((2 : ℝ) - X u v - X v u) / 4, by
          intro u v
          ring⟩
        e

/-- `goemans_williamson_objective G w X` expands to the weighted sum of the standard semidefinite
edge terms. -/
theorem goemans_williamson_objective_eq_sum
    (w : Sym2 V → ℝ) (X : Matrix V V ℝ) :
    goemans_williamson_objective G w X =
      Finset.sum G.edgeFinset fun e ↦
        w e *
          Sym2.lift
            ⟨fun u v : V ↦ ((2 : ℝ) - X u v - X v u) / 4, by
              intro u v
              ring⟩
            e :=
  by
    rw [goemans_williamson_objective, edgeFinsetStable_eq_edgeFinset]

/-- The attainable objective values of the Goemans-Williamson semidefinite relaxation. -/
def goemans_williamson_objective_values (G : SimpleGraph V) [Fintype V] (w : Sym2 V → ℝ) : Set ℝ :=
  {r | ∃ X : Matrix V V ℝ,
      goemans_williamson_feasible X ∧ goemans_williamson_objective G w X = r}

/-- Membership in `goemans_williamson_objective_values G w` means that `r` is attained by a
Goemans-Williamson feasible matrix. -/
theorem mem_goemans_williamson_objective_values_iff
    {w : Sym2 V → ℝ} {r : ℝ} :
    r ∈ goemans_williamson_objective_values G w ↔
      ∃ X : Matrix V V ℝ,
        goemans_williamson_feasible X ∧ goemans_williamson_objective G w X = r :=
  Iff.rfl

/-- The optimal value `z_sdp` of the Goemans-Williamson semidefinite relaxation. -/
def goemans_williamson_value (G : SimpleGraph V) [Fintype V] (w : Sym2 V → ℝ) : ℝ :=
  sSup (goemans_williamson_objective_values G w)

/-- `goemans_williamson_value G w` is the supremum of the objective values attained by feasible
Goemans-Williamson matrices. -/
theorem goemans_williamson_value_eq_sSup
    (w : Sym2 V → ℝ) :
    goemans_williamson_value G w = sSup (goemans_williamson_objective_values G w) :=
  rfl

end GoemansWilliamsonObjective

section ComparisonTheorems

variable (G : SimpleGraph V) [Fintype V]

/-- Helper for Exercise 10.4: the rank-one lifted witness reproduces the integral edge term on
each edge. -/
lemma rankOneLiftedEdgeTerm_pointwise
    (χ : V → ℝ) (u v : V) :
    χ u + χ v -
        (Matrix.vecMulVec (Option.elim' 1 χ) (Option.elim' 1 χ) (some u) (some v) +
          Matrix.vecMulVec (Option.elim' 1 χ) (Option.elim' 1 χ) (some v) (some u)) =
      χ u + χ v - 2 * χ u * χ v := by
  simp [Matrix.vecMulVec_apply]
  ring_nf

/-- Helper for Exercise 10.4: the quadratic form of `X` on `e_u - e_v` gives the lower-edge
expression. -/
lemma goemansWilliamsonEdgeMinusEval
    [DecidableEq V] {X : Matrix V V ℝ} (hX : goemans_williamson_feasible X) (u v : V) :
    (Pi.single u 1 - Pi.single v 1) ⬝ᵥ (X *ᵥ (Pi.single u 1 - Pi.single v 1)) =
      (2 : ℝ) - X u v - X v u := by
  rw [sub_eq_add_neg, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one]
  simp [goemans_williamson_feasible.diag_eq_one hX]
  ring

/-- Helper for Exercise 10.4: the quadratic form of `X` on `e_u + e_v` gives the upper-edge
expression. -/
lemma goemansWilliamsonEdgePlusEval
    [DecidableEq V] {X : Matrix V V ℝ} (hX : goemans_williamson_feasible X) (u v : V) :
    (Pi.single u 1 + Pi.single v 1) ⬝ᵥ (X *ᵥ (Pi.single u 1 + Pi.single v 1)) =
      (2 : ℝ) + X u v + X v u := by
  rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp [goemans_williamson_feasible.diag_eq_one hX]
  ring

/-- Helper for Exercise 10.4: the affine matrix bridge `B Z Bᵀ` evaluates to the textbook
Goemans-Williamson matrix formula. -/
lemma liftedBridgeMatrix_apply
    [DecidableEq V] (χ : V → ℝ) (Z : Matrix (Option V) (Option V) ℝ)
    (hZ : max_cut_sdp'_feasible χ Z) (u v : V) :
    let B : Matrix V (Option V) ℝ := fun u i =>
      match i with
      | none => 1
      | some u' => if u' = u then -2 else 0
    (B * Z * B.conjTranspose) u v = 1 - 2 * χ u - 2 * χ v + 4 * Z (some u) (some v) := by
  classical
  simp [Matrix.mul_apply, Fintype.sum_option]
  rw [max_cut_sdp'_feasible.apply_none_none hZ, max_cut_sdp'_feasible.apply_some_none hZ u,
    max_cut_sdp'_feasible.apply_none_some hZ v]
  ring

/-- Helper for Exercise 10.4: the affine map from lifted witnesses to the Goemans-Williamson
relaxation preserves each edge term. -/
lemma liftedToGoemansWilliamsonEdgeTerm_pointwise
    (χ : V → ℝ) (Z : Matrix (Option V) (Option V) ℝ) (u v : V) :
    let X : Matrix V V ℝ := fun u v ↦ 1 - 2 * χ u - 2 * χ v + 4 * Z (some u) (some v)
    ((2 : ℝ) - X u v - X v u) / 4 =
      χ u + χ v - (Z (some u) (some v) + Z (some v) (some u)) := by
  simp
  ring

/-- Helper for Exercise 10.4: the lifted witness built from a Goemans-Williamson matrix splits as
the sum of a rank-one PSD matrix and an embedded PSD matrix. -/
lemma goemansWilliamsonLiftedDecomposition_apply
    [DecidableEq V] (X : Matrix V V ℝ) (i j : Option V) :
    let a : Option V → ℝ := fun k =>
      match k with
      | none => 1
      | some _ => (1 / 2 : ℝ)
    let E : Matrix (Option V) V ℝ := fun k v =>
      match k with
      | none => 0
      | some u => if u = v then 1 else 0
    let Z : Matrix (Option V) (Option V) ℝ := fun k l =>
      match k, l with
      | none, none => 1
      | none, some _ => (1 / 2 : ℝ)
      | some _, none => (1 / 2 : ℝ)
      | some u, some v => (1 + X u v) / 4
    Z i j = (Matrix.vecMulVec a a + (1 / 4 : ℝ) • (E * X * E.conjTranspose)) i j := by
  cases i <;> cases j <;> simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Fintype.sum_option]
  ring_nf

/-- Helper for Exercise 10.4: the lifted witness reconstructed from a Goemans-Williamson matrix
preserves each edge term. -/
lemma goemansWilliamsonToLiftedEdgeTerm_pointwise
    (X : Matrix V V ℝ) (u v : V) :
    let χ : V → ℝ := fun _ ↦ (1 / 2 : ℝ)
    let Z : Matrix (Option V) (Option V) ℝ := fun i j =>
      match i, j with
      | none, none => 1
      | none, some _ => (1 / 2 : ℝ)
      | some _, none => (1 / 2 : ℝ)
      | some u, some v => (1 + X u v) / 4
    χ u + χ v - (Z (some u) (some v) + Z (some v) (some u)) =
      ((2 : ℝ) - X u v - X v u) / 4 := by
  simp
  ring

/-- Helper for Exercise 10.4: every integral max-cut objective value is already attained by a
feasible point of the lifted semidefinite relaxation. -/
lemma maxCutNodeObjectiveValues_subset_maxCutSdp'ObjectiveValues
    (w : Sym2 V → ℝ) :
    max_cut_node_objective_values G w ⊆ max_cut_sdp'_objective_values G w := by
  classical
  intro r hr
  rcases hr with ⟨χ, hχ, rfl⟩
  let a : Option V → ℝ := Option.elim' 1 χ
  let Z : Matrix (Option V) (Option V) ℝ := Matrix.vecMulVec a a
  refine ⟨χ, Z, ?_, ?_⟩
  · -- Build the lifted witness as a rank-one matrix and use `χ^2 = χ` on binary assignments.
    refine max_cut_sdp'_feasible.mk ?_ ?_ ?_ ?_ ?_
    · simpa [Z, a] using Matrix.posSemidef_vecMulVec_self_star a
    · simp [Z, a, Matrix.vecMulVec_apply]
    · intro v
      simp [Z, a, Matrix.vecMulVec_apply]
    · intro v
      simp [Z, a, Matrix.vecMulVec_apply]
    · intro v
      rcases hχ v with h0 | h1
      · simp [Z, a, Matrix.vecMulVec_apply, h0]
      · simp [Z, a, Matrix.vecMulVec_apply, h1]
  · -- Expand both objectives and match the symmetric edge term on each edge.
    rw [max_cut_sdp'_objective_eq_sum, max_cut_node_objective_eq_sum]
    refine Finset.sum_congr rfl ?_
    intro e _
    have hEdge :
        Sym2.lift
          ⟨fun u v : V ↦
              χ u + χ v - (Z (some u) (some v) + Z (some v) (some u)), by
            intro u v
            ring⟩ e =
        Sym2.lift
          ⟨fun u v : V ↦ χ u + χ v - 2 * χ u * χ v, by
            intro u v
            ring⟩ e := by
      refine Sym2.ind ?_ e
      intro u v
      simpa [Z, a, Sym2.lift_mk] using rankOneLiftedEdgeTerm_pointwise χ u v
    rw [hEdge]

/-- Helper for Exercise 10.4: every Goemans-Williamson edge term lies in the interval `[0, 1]`. -/
lemma goemansWilliamsonEdgeTerm_mem_Icc_zero_one
    {X : Matrix V V ℝ} (hX : goemans_williamson_feasible X) (u v : V) :
    0 ≤ ((2 : ℝ) - X u v - X v u) / 4 ∧
      ((2 : ℝ) - X u v - X v u) / 4 ≤ 1 := by
  classical
  let _ : DecidableEq V := Classical.decEq V
  let xMinus : V → ℝ := Pi.single u 1 - Pi.single v 1
  let xPlus : V → ℝ := Pi.single u 1 + Pi.single v 1
  -- Evaluate the quadratic form on `e_u - e_v` to get the lower bound.
  have hminus :
      0 ≤ xMinus ⬝ᵥ (X *ᵥ xMinus) := by
    simpa [xMinus] using
      (goemans_williamson_feasible.posSemidef hX).dotProduct_mulVec_nonneg xMinus
  have hminusEval :
      xMinus ⬝ᵥ (X *ᵥ xMinus) = (2 : ℝ) - X u v - X v u := by
    simpa [xMinus] using goemansWilliamsonEdgeMinusEval (hX := hX) u v
  have hLower : 0 ≤ ((2 : ℝ) - X u v - X v u) / 4 := by
    have hminusScaled : 0 ≤ (xMinus ⬝ᵥ (X *ᵥ xMinus)) / 4 := by
      positivity
    rw [hminusEval] at hminusScaled
    simpa using hminusScaled
  -- Evaluate the quadratic form on `e_u + e_v` to control the same term from above.
  have hplus :
      0 ≤ xPlus ⬝ᵥ (X *ᵥ xPlus) := by
    simpa [xPlus] using
      (goemans_williamson_feasible.posSemidef hX).dotProduct_mulVec_nonneg xPlus
  have hplusEval :
      xPlus ⬝ᵥ (X *ᵥ xPlus) = (2 : ℝ) + X u v + X v u := by
    simpa [xPlus] using goemansWilliamsonEdgePlusEval (hX := hX) u v
  have hplus' : 0 ≤ (2 : ℝ) + X u v + X v u := by
    have hplusExpanded := hplus
    rw [hplusEval] at hplusExpanded
    exact hplusExpanded
  have hUpper : ((2 : ℝ) - X u v - X v u) / 4 ≤ 1 := by
    nlinarith
  exact ⟨hLower, hUpper⟩

/-- Helper for Exercise 10.4: the Goemans-Williamson attainable-value set is bounded above. -/
lemma goemansWilliamsonObjectiveValues_bddAbove
    (w : Sym2 V → ℝ) :
    BddAbove (goemans_williamson_objective_values G w) := by
  classical
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  use ∑ e ∈ G.edgeFinset, |w e|
  intro r hr
  rcases hr with ⟨X, hX, rfl⟩
  -- Bound each weighted edge contribution by the absolute edge weight.
  rw [goemans_williamson_objective_eq_sum]
  refine Finset.sum_le_sum ?_
  intro e _
  obtain ⟨p, rfl⟩ := Sym2.mk_surjective e
  rcases p with ⟨u, v⟩
  have hEdge := goemansWilliamsonEdgeTerm_mem_Icc_zero_one (hX := hX) u v
  have hw :
      w s(u, v) * (((2 : ℝ) - X u v - X v u) / 4) ≤ |w s(u, v)| := by
    by_cases hwu : 0 ≤ w s(u, v)
    · have habs : |w s(u, v)| = w s(u, v) := abs_of_nonneg hwu
      rw [habs]
      nlinarith [hEdge.1, hEdge.2]
    · have habs : |w s(u, v)| = -w s(u, v) := abs_of_neg (lt_of_not_ge hwu)
      rw [habs]
      nlinarith [hEdge.1]
  simpa [Sym2.lift_mk] using hw

/-- Helper for Exercise 10.4: the affine map `X = B Z Bᵀ` sends every lifted feasible point to a
Goemans-Williamson feasible matrix with the same objective value. -/
lemma maxCutSdp'ObjectiveValues_subset_goemansWilliamsonObjectiveValues
    (w : Sym2 V → ℝ) :
    max_cut_sdp'_objective_values G w ⊆ goemans_williamson_objective_values G w := by
  classical
  intro r hr
  rcases hr with ⟨χ, Z, hZ, rfl⟩
  let B : Matrix V (Option V) ℝ := fun u i =>
    match i with
    | none => 1
    | some u' => if u' = u then -2 else 0
  let X : Matrix V V ℝ := fun u v ↦ 1 - 2 * χ u - 2 * χ v + 4 * Z (some u) (some v)
  refine ⟨X, ?_, ?_⟩
  · -- The bridge matrix turns the lifted PSD witness into a GW PSD witness.
    refine goemans_williamson_feasible.mk ?_ ?_
    · have hXeq : X = B * Z * B.conjTranspose := by
        ext u v
        simpa [X, B] using (liftedBridgeMatrix_apply (χ := χ) (Z := Z) hZ u v).symm
      rw [hXeq]
      exact (max_cut_sdp'_feasible.posSemidef hZ).mul_mul_conjTranspose_same B
    · intro v
      simp [X, max_cut_sdp'_feasible.apply_some_some hZ]
      ring
  · -- Expand both objectives and match the affine edge-term transformation.
    rw [goemans_williamson_objective_eq_sum, max_cut_sdp'_objective_eq_sum]
    refine Finset.sum_congr rfl ?_
    intro e _
    have hEdge :
        Sym2.lift
          ⟨fun u v : V ↦ ((2 : ℝ) - X u v - X v u) / 4, by
            intro u v
            ring⟩ e =
        Sym2.lift
          ⟨fun u v : V ↦ χ u + χ v - (Z (some u) (some v) + Z (some v) (some u)), by
            intro u v
            ring⟩ e := by
      refine Sym2.ind ?_ e
      intro u v
      simpa [X, Sym2.lift_mk] using liftedToGoemansWilliamsonEdgeTerm_pointwise χ Z u v
    rw [hEdge]

/-- Helper for Exercise 10.4: every Goemans-Williamson feasible matrix lifts to a feasible point
of the textbook semidefinite relaxation with the same objective value. -/
lemma goemansWilliamsonObjectiveValues_subset_maxCutSdp'ObjectiveValues
    (w : Sym2 V → ℝ) :
    goemans_williamson_objective_values G w ⊆ max_cut_sdp'_objective_values G w := by
  classical
  intro r hr
  rcases hr with ⟨X, hX, rfl⟩
  let χ : V → ℝ := fun _ ↦ (1 / 2 : ℝ)
  let a : Option V → ℝ := fun i =>
    match i with
    | none => 1
    | some _ => (1 / 2 : ℝ)
  let E : Matrix (Option V) V ℝ := fun i v =>
    match i with
    | none => 0
    | some u => if u = v then 1 else 0
  let Z : Matrix (Option V) (Option V) ℝ := fun i j =>
    match i, j with
    | none, none => 1
    | none, some _ => (1 / 2 : ℝ)
    | some _, none => (1 / 2 : ℝ)
    | some u, some v => (1 + X u v) / 4
  refine ⟨χ, Z, ?_, ?_⟩
  · -- Route correction: decompose the lifted witness into rank-one and embedded PSD parts.
    refine max_cut_sdp'_feasible.mk ?_ ?_ ?_ ?_ ?_
    · have hZdecomp :
          Z = Matrix.vecMulVec a a + (1 / 4 : ℝ) • (E * X * E.conjTranspose) := by
        ext i j
        simpa [Z, a, E] using goemansWilliamsonLiftedDecomposition_apply X i j
      rw [hZdecomp]
      have hRankOne : (Matrix.vecMulVec a a).PosSemidef := by
        simpa using Matrix.posSemidef_vecMulVec_self_star a
      have hEmbedded : (E * X * E.conjTranspose).PosSemidef := by
        exact (goemans_williamson_feasible.posSemidef hX).mul_mul_conjTranspose_same E
      exact hRankOne.add (hEmbedded.smul (show 0 ≤ (1 / 4 : ℝ) by norm_num))
    · simp [Z]
    · intro v
      simp [χ, Z]
    · intro v
      simp [χ, Z]
    · intro v
      rw [show Z (some v) (some v) = (1 + X v v) / 4 by simp [Z]]
      rw [goemans_williamson_feasible.diag_eq_one hX]
      norm_num [χ]
  · -- Expand both objectives and match the reverse affine edge transformation.
    rw [max_cut_sdp'_objective_eq_sum, goemans_williamson_objective_eq_sum]
    refine Finset.sum_congr rfl ?_
    intro e _
    have hEdge :
        Sym2.lift
          ⟨fun u v : V ↦ χ u + χ v - (Z (some u) (some v) + Z (some v) (some u)), by
            intro u v
            ring⟩ e =
        Sym2.lift
          ⟨fun u v : V ↦ ((2 : ℝ) - X u v - X v u) / 4, by
            intro u v
            ring⟩ e := by
      refine Sym2.ind ?_ e
      intro u v
      simpa [χ, Z, Sym2.lift_mk] using goemansWilliamsonToLiftedEdgeTerm_pointwise X u v
    rw [hEdge]

/-- Helper for Exercise 10.4: the lifted SDP and the Goemans-Williamson relaxation have the same
attainable objective values. -/
lemma maxCutSdp'ObjectiveValues_eq_goemansWilliamsonObjectiveValues
    (w : Sym2 V → ℝ) :
    max_cut_sdp'_objective_values G w = goemans_williamson_objective_values G w := by
  -- The two explicit witness maps give the desired equality of attainable-value sets.
  refine Set.Subset.antisymm ?_ ?_
  · exact maxCutSdp'ObjectiveValues_subset_goemansWilliamsonObjectiveValues (G := G) w
  · exact goemansWilliamsonObjectiveValues_subset_maxCutSdp'ObjectiveValues (G := G) w

/-- Exercise 10.4 (1). The lifted semidefinite program with variables `χ` and `Z` is a relaxation
of the integral max-cut problem, so its optimal value is at least the integral value `z_I`. -/
theorem max_cut_integer_value_le_max_cut_sdp'_value
    (w : Sym2 V → ℝ) :
    max_cut_integer_value G w ≤ max_cut_sdp'_value G w := by
  -- Compare the two supremums after bounding the lifted attainable-value set above.
  rw [max_cut_integer_value_eq_sSup, max_cut_sdp'_value_eq_sSup]
  refine csSup_le_csSup ?_ ?_ ?_
  · simpa [maxCutSdp'ObjectiveValues_eq_goemansWilliamsonObjectiveValues (G := G) w] using
      goemansWilliamsonObjectiveValues_bddAbove (G := G) w
  · refine ⟨max_cut_node_objective G w (fun _ ↦ 0), ?_⟩
    refine ⟨fun _ ↦ 0, ?_, rfl⟩
    intro v
    exact Or.inl rfl
  · exact maxCutNodeObjectiveValues_subset_maxCutSdp'ObjectiveValues (G := G) w

/-- Exercise 10.4 (2). The lifted semidefinite value `z'_sdp` agrees with the value `z_sdp` of
the Goemans-Williamson relaxation from Section 10.2.1. -/
theorem max_cut_sdp'_value_eq_goemans_williamson_value
    (w : Sym2 V → ℝ) :
    max_cut_sdp'_value G w = goemans_williamson_value G w := by
  -- Once the attainable-value sets agree, the optimal values agree by taking suprema.
  have hValueSets :
      sSup (max_cut_sdp'_objective_values G w) =
        sSup (goemans_williamson_objective_values G w) := by
    exact congrArg sSup (maxCutSdp'ObjectiveValues_eq_goemansWilliamsonObjectiveValues (G := G) w)
  simpa [max_cut_sdp'_value_eq_sSup, goemans_williamson_value_eq_sSup] using hValueSets

end ComparisonTheorems

end Objectives

end Exercise_10_4
