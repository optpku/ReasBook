/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Algorithm_11_5_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_5_extra_1

noncomputable section

section

open Matrix

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "Multiplier" => EuclideanSpace ℝ (Fin m)
local notation "ConstraintMatrix" => Matrix (Fin n) (Fin m) ℝ

-- Domain sampling for this item:
-- * source-facing layer: the Chapter 11 KKT characterization for a linear equality-constrained
--   problem.
-- * core/canonical owners already in this chapter: `linearlyConstrainedFeasibleSet` and
--   `nearestPointProjection`.
-- * bridge/view layer here: the equality-only Chapter 8 constrained-optimization view of the
--   Chapter 11 problem owner.
-- * derived API here: the problem owner together with its feasible-set owner, the source-facing
--   multiplier characterization, and the bridge to `ConstrainedOptimizationProblem.IsKKTPoint`;
--   the projection side is stated directly with the canonical `nearestPointProjection`.

/-- The linearly equality-constrained feasible set `linearlyConstrainedFeasibleSet A b` is
complete. -/
theorem isComplete_linearlyConstrainedFeasibleSet
    (A : ConstraintMatrix) (b : ConstraintPoint) :
    IsComplete (linearlyConstrainedFeasibleSet A b) := by
  -- Realize the feasible set as the preimage of the closed singleton `{b}` under the linear map
  -- `x ↦ Aᵀ x`.
  let T : Point →ₗ[ℝ] ConstraintPoint := Matrix.toEuclideanLin A.transpose
  have hset :
      linearlyConstrainedFeasibleSet A b = T ⁻¹' ({b} : Set ConstraintPoint) := by
    ext x
    constructor
    · intro hx
      simpa [linearlyConstrainedFeasibleSet, T, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (WithLp.toLp 2) hx
    · intro hx
      simpa [linearlyConstrainedFeasibleSet, T, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg WithLp.ofLp hx
  have hclosed : IsClosed (linearlyConstrainedFeasibleSet A b) := by
    rw [hset]
    exact isClosed_singleton.preimage T.continuous_of_finiteDimensional
  exact hclosed.isComplete

/-- The linearly equality-constrained feasible set `linearlyConstrainedFeasibleSet A b` is
convex. -/
theorem convex_linearlyConstrainedFeasibleSet
    (A : ConstraintMatrix) (b : ConstraintPoint) :
    Convex ℝ (linearlyConstrainedFeasibleSet A b) := by
  -- The same linear-preimage description shows convexity because `{b}` is convex.
  let T : Point →ₗ[ℝ] ConstraintPoint := Matrix.toEuclideanLin A.transpose
  have hset :
      linearlyConstrainedFeasibleSet A b = T ⁻¹' ({b} : Set ConstraintPoint) := by
    ext x
    constructor
    · intro hx
      simpa [linearlyConstrainedFeasibleSet, T, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (WithLp.toLp 2) hx
    · intro hx
      simpa [linearlyConstrainedFeasibleSet, T, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg WithLp.ofLp hx
  rw [hset]
  simpa [Set.preimage] using (convex_singleton b).linear_preimage T

/-- Helper for Chapter11 Lemma 11.5.4: pairing against `A λ` is the same as pairing `Aᵀ x`
against `λ`. -/
lemma inner_matrix_action_eq_inner_transpose_action
    (A : ConstraintMatrix) (x : Point) (multiplier : Multiplier) :
    inner ℝ x (Matrix.toEuclideanLin A multiplier) =
      inner ℝ (Matrix.toEuclideanLin A.transpose x) multiplier := by
  have hadj : LinearMap.adjoint (Matrix.toEuclideanLin A.transpose) = Matrix.toEuclideanLin A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := A.transpose)).symm
  -- Rewrite the right-hand side through the adjoint of `x ↦ Aᵀ x`.
  calc
    inner ℝ x (Matrix.toEuclideanLin A multiplier)
        = inner ℝ x ((Matrix.toEuclideanLin A.transpose).adjoint multiplier) := by
            rw [hadj]
    _ = inner ℝ (Matrix.toEuclideanLin A.transpose x) multiplier := by
          simpa using
            (LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A.transpose) x multiplier)

/-- Helper for Chapter11 Lemma 11.5.4: the affine constraint sum in the Chapter 8 Lagrangian is
the linear pairing with `A λ` minus the constant term `⟪b, λ⟫`. -/
lemma transpose_constraint_sum_eq_inner
    (A : ConstraintMatrix) (b : ConstraintPoint) (x : Point) (multiplier : Multiplier) :
    (∑ i : Fin m, multiplier i * ((A.transpose.mulVec x - b) i)) =
      inner ℝ x (Matrix.toEuclideanLin A multiplier) - inner ℝ b multiplier := by
  have hmain :
      inner ℝ x (Matrix.toEuclideanLin A multiplier) =
        inner ℝ (Matrix.toEuclideanLin A.transpose x) multiplier :=
    inner_matrix_action_eq_inner_transpose_action A x multiplier
  -- First compress the coordinate sum into a single inner product on the constraint space.
  calc
    (∑ i : Fin m, multiplier i * ((A.transpose.mulVec x - b) i))
        = inner ℝ (Matrix.toEuclideanLin A.transpose x - b) multiplier := by
            simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.toEuclideanLin,
              Matrix.toLpLin_apply, Matrix.mulVec, mul_comm]
    _ = inner ℝ (Matrix.toEuclideanLin A.transpose x) multiplier - inner ℝ b multiplier := by
          rw [inner_sub_left]
    _ = inner ℝ x (Matrix.toEuclideanLin A multiplier) - inner ℝ b multiplier := by
          rw [← hmain]

/-- Helper for Chapter11 Lemma 11.5.4: orthogonality to the kernel of the Euclidean matrix action
forces membership in the range of the transpose action. -/
lemma exists_in_range_transpose_of_orthogonal_ker
    {rows cols : ℕ}
    (A : Matrix (Fin rows) (Fin cols) ℝ) (g : EuclideanSpace ℝ (Fin cols))
    (hg : ∀ d : EuclideanSpace ℝ (Fin cols),
      Matrix.toEuclideanLin A d = 0 → inner ℝ d g = 0) :
    ∃ multiplier : EuclideanSpace ℝ (Fin rows),
      Matrix.toEuclideanLin A.transpose multiplier = g := by
  let T : EuclideanSpace ℝ (Fin cols) →ₗ[ℝ] EuclideanSpace ℝ (Fin rows) := Matrix.toEuclideanLin A
  have hgOrth : g ∈ T.kerᗮ := by
    rw [Submodule.mem_orthogonal']
    intro d hd
    -- Convert kernel membership back to the matrix equation used by the affine-feasible route.
    simpa [real_inner_comm] using hg d (by simpa [T] using hd)
  rw [LinearMap.orthogonal_ker] at hgOrth
  have hadj : LinearMap.adjoint T = Matrix.toEuclideanLin A.transpose := by
    dsimp [T]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := A)).symm
  rcases hgOrth with ⟨multiplier, hmultiplier⟩
  refine ⟨multiplier, ?_⟩
  simpa [hadj] using hmultiplier

/-- A linearly equality-constrained optimization problem on `Point` with constraint system
`Aᵀ x = b`. -/
structure LinearEqualityConstrainedProblem (n m : ℕ) where
  objective : EuclideanSpace ℝ (Fin n) → ℝ
  constraintMatrix : Matrix (Fin n) (Fin m) ℝ
  constraintTarget : EuclideanSpace ℝ (Fin m)

namespace LinearEqualityConstrainedProblem

/-- The feasible set of `problem` consists of the points satisfying `Aᵀ x = b`. -/
def feasibleSet (problem : LinearEqualityConstrainedProblem n m) : Set Point :=
  linearlyConstrainedFeasibleSet problem.constraintMatrix problem.constraintTarget

/-- Feasibility in `problem` is membership in `problem.feasibleSet`. -/
instance : Membership Point (LinearEqualityConstrainedProblem n m) where
  mem problem x := x ∈ problem.feasibleSet

/-- Membership in `problem.feasibleSet` is exactly the equality constraint system `Aᵀ x = b`. -/
theorem mem_feasibleSet_iff
    (problem : LinearEqualityConstrainedProblem n m) (x : Point) :
    x ∈ problem.feasibleSet ↔
      problem.constraintMatrixᵀ *ᵥ x = problem.constraintTarget := by
  simpa [feasibleSet] using
    mem_linearlyConstrainedFeasibleSet_iff problem.constraintMatrix problem.constraintTarget x

/-- The feasible set `problem.feasibleSet` is complete. -/
theorem isComplete_feasibleSet
    (problem : LinearEqualityConstrainedProblem n m) :
    IsComplete problem.feasibleSet := by
  simpa [feasibleSet] using
    isComplete_linearlyConstrainedFeasibleSet
      problem.constraintMatrix
      problem.constraintTarget

/-- The feasible set `problem.feasibleSet` is convex. -/
theorem convex_feasibleSet
    (problem : LinearEqualityConstrainedProblem n m) :
    Convex ℝ problem.feasibleSet := by
  simpa [feasibleSet] using
    convex_linearlyConstrainedFeasibleSet
      problem.constraintMatrix
      problem.constraintTarget

/-- `problem.toConstrainedOptimizationProblem` is the canonical Chapter 8 equality-only view of
the Chapter 11 linear equality-constrained problem. -/
def toConstrainedOptimizationProblem (problem : LinearEqualityConstrainedProblem n m) :
    _root_.ConstrainedOptimizationProblem n m Set.univ (∅ : Set (Fin m)) where
  objective := fun x ↦ problem.objective (WithLp.toLp 2 x)
  constraint := fun i x ↦
    (problem.constraintMatrixᵀ *ᵥ x - problem.constraintTarget.ofLp) i
  eqIndices_union_ineqIndices := by
    ext i
    simp
  eqIndices_disjoint_ineqIndices := by
    simp

@[simp] theorem toConstrainedOptimizationProblem_objective_apply
    (problem : LinearEqualityConstrainedProblem n m) (x : Point) :
    problem.toConstrainedOptimizationProblem.objective x.ofLp = problem.objective x := by
  simp [toConstrainedOptimizationProblem]

@[simp] theorem toConstrainedOptimizationProblem_constraint_apply
    (problem : LinearEqualityConstrainedProblem n m) (i : Fin m) (x : Point) :
    problem.toConstrainedOptimizationProblem.constraint i x.ofLp =
      (problem.constraintMatrixᵀ *ᵥ x.ofLp - problem.constraintTarget.ofLp) i := by
  simp [toConstrainedOptimizationProblem]

/-- A Euclidean-space point is feasible for `problem.toConstrainedOptimizationProblem` exactly
when it is feasible for the original Chapter 11 equality-constrained problem. -/
@[simp] theorem mem_toConstrainedOptimizationProblem_iff
    (problem : LinearEqualityConstrainedProblem n m) (x : Point) :
    x.ofLp ∈ problem.toConstrainedOptimizationProblem ↔ x ∈ problem := by
  constructor
  · intro hx
    have h_constraints :
        ∀ i : Fin m,
          problem.toConstrainedOptimizationProblem.constraint i x.ofLp = 0 := by
      intro i
      exact (ConstrainedOptimizationProblem.mem_iff _ _).1 hx |>.1 i (by simp)
    refine (problem.mem_feasibleSet_iff x).2 ?_
    ext i
    exact sub_eq_zero.mp <| by
      simpa using h_constraints i
  · intro hx
    have h_eq :
        problem.constraintMatrixᵀ *ᵥ x.ofLp = problem.constraintTarget.ofLp :=
      (problem.mem_feasibleSet_iff x).1 hx
    refine (ConstrainedOptimizationProblem.mem_iff _ _).2 ?_
    refine ⟨?_, ?_⟩
    · intro i hi
      have hcoord :
          (problem.constraintMatrixᵀ *ᵥ x.ofLp) i = problem.constraintTarget.ofLp i := by
        exact congrArg (fun v : Fin m → ℝ ↦ v i) h_eq
      exact sub_eq_zero.mpr <| by
        simpa using hcoord
    · intro i hi
      simp at hi

/-- Under differentiability of `problem.objective` at `x`, existence of a Chapter 8 KKT
multiplier for the equality-only bridge is equivalent to the source equality-constrained KKT
system `∇ f(x) = A λ` together with feasibility of `x`. -/
theorem isKKTPoint_toConstrainedOptimizationProblem_iff
    (problem : LinearEqualityConstrainedProblem n m) (x : Point)
    (multiplier : Multiplier)
    (hDiff : DifferentiableAt ℝ problem.objective x) :
    problem.toConstrainedOptimizationProblem.IsKKTPoint x.ofLp multiplier.ofLp ↔
      x ∈ problem ∧ gradient problem.objective x = problem.constraintMatrix.mulVec multiplier :=
  by
  have hlag_eq :
      problem.toConstrainedOptimizationProblem.euclideanLagrangian multiplier.ofLp =
        fun y : Point ↦
          problem.objective y -
            inner ℝ y (Matrix.toEuclideanLin problem.constraintMatrix multiplier) +
              inner ℝ problem.constraintTarget multiplier := by
    funext y
    have hcoord : WithLp.toLp 2 ((EuclideanSpace.equiv (Fin n) ℝ) y) = y := by
      ext i
      rfl
    have hcoord' : (EuclideanSpace.equiv (Fin n) ℝ) y = y.ofLp := rfl
    -- Rewrite the Chapter 8 Lagrangian into the source objective minus the affine constraint
    -- pairing `⟪y, A λ⟫`, plus the constant correction `⟪b, λ⟫`.
    calc
      problem.toConstrainedOptimizationProblem.euclideanLagrangian multiplier.ofLp y
          = problem.objective (WithLp.toLp 2 ((EuclideanSpace.equiv (Fin n) ℝ) y)) -
              ∑ i : Fin m,
                multiplier i *
                  ((problem.constraintMatrix.transpose.mulVec y - problem.constraintTarget) i) := by
                    simp [ConstrainedOptimizationProblem.euclideanLagrangian,
                      ConstrainedOptimizationProblem.lagrangian,
                      LinearEqualityConstrainedProblem.toConstrainedOptimizationProblem,
                      hcoord']
      _ = problem.objective y -
            inner ℝ y (Matrix.toEuclideanLin problem.constraintMatrix multiplier) +
              inner ℝ problem.constraintTarget multiplier := by
            rw [hcoord, transpose_constraint_sum_eq_inner]
            ring
  have hlinfun :
      (((InnerProductSpace.toDual ℝ Point)
          (Matrix.toEuclideanLin problem.constraintMatrix multiplier)) : Point → ℝ) =
        fun z : Point ↦ inner ℝ z (Matrix.toEuclideanLin problem.constraintMatrix multiplier) := by
    funext z
    simp [InnerProductSpace.toDual_apply_apply, real_inner_comm]
  have hlin :
      HasGradientAt
        (fun z : Point ↦ inner ℝ z (Matrix.toEuclideanLin problem.constraintMatrix multiplier))
        (Matrix.toEuclideanLin problem.constraintMatrix multiplier) x := by
    rw [← hlinfun]
    have h :=
      (((InnerProductSpace.toDual ℝ Point)
          (Matrix.toEuclideanLin problem.constraintMatrix multiplier)).hasFDerivAt.hasGradientAt :
        HasGradientAt
          (((InnerProductSpace.toDual ℝ Point)
            (Matrix.toEuclideanLin problem.constraintMatrix multiplier)) : Point → ℝ)
          ((InnerProductSpace.toDual ℝ Point).symm
            ((InnerProductSpace.toDual ℝ Point)
              (Matrix.toEuclideanLin problem.constraintMatrix multiplier))) x)
    simpa using h
  have hgrad_eq :
      gradient
          (problem.toConstrainedOptimizationProblem.euclideanLagrangian multiplier.ofLp)
          x =
        gradient problem.objective x -
          Matrix.toEuclideanLin problem.constraintMatrix multiplier := by
    have hlag :
        HasGradientAt
          (fun y : Point ↦
            problem.objective y -
              inner ℝ y (Matrix.toEuclideanLin problem.constraintMatrix multiplier) +
                inner ℝ problem.constraintTarget multiplier)
          (gradient problem.objective x -
            Matrix.toEuclideanLin problem.constraintMatrix multiplier)
          x := by
      -- Differentiate the objective-minus-linear-functional presentation of the Lagrangian.
      simpa using
        ((hDiff.hasGradientAt.hasFDerivAt.sub hlin.hasFDerivAt).add_const
          (inner ℝ problem.constraintTarget multiplier)).hasGradientAt
    simpa [hlag_eq] using hlag.gradient
  constructor
  · intro hKKT
    refine ⟨(problem.mem_toConstrainedOptimizationProblem_iff x).1 hKKT.feasible, ?_⟩
    -- On the equality-only bridge, stationarity is exactly `∇ f(x) = A λ`.
    have hstationary :
        gradient problem.objective x -
            Matrix.toEuclideanLin problem.constraintMatrix multiplier = 0 := by
      simpa [hgrad_eq] using hKKT.stationarity
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
      congrArg WithLp.ofLp (sub_eq_zero.mp hstationary)
  · rintro ⟨hx, hgradient⟩
    refine ⟨(problem.mem_toConstrainedOptimizationProblem_iff x).2 hx, ?_, ?_, ?_⟩
    · intro i hi
      cases hi
    · -- Replace Chapter 8 stationarity by the source matrix equality.
      have hgradient' :
          gradient problem.objective x =
            Matrix.toEuclideanLin problem.constraintMatrix multiplier := by
        simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
          congrArg (WithLp.toLp 2) hgradient
      simpa [hgrad_eq] using sub_eq_zero.mpr hgradient'
    · intro i hi
      cases hi

/-- Under differentiability of `problem.objective` at `x`, existence of a Chapter 8 KKT
multiplier for the equality-only bridge is exactly the source equality-constrained KKT system
`∇ f(x) = A λ` together with feasibility of `x`. -/
theorem exists_isKKTPoint_toConstrainedOptimizationProblem_iff
    (problem : LinearEqualityConstrainedProblem n m) (x : Point)
    (hDiff : DifferentiableAt ℝ problem.objective x) :
    (∃ multiplier : Multiplier,
      problem.toConstrainedOptimizationProblem.IsKKTPoint x.ofLp multiplier.ofLp) ↔
      ∃ multiplier : Multiplier,
        x ∈ problem ∧
          gradient problem.objective x = problem.constraintMatrix.mulVec multiplier := by
  constructor
  · rintro ⟨multiplier, hKKT⟩
    exact ⟨multiplier, (isKKTPoint_toConstrainedOptimizationProblem_iff
      problem x multiplier hDiff).1 hKKT⟩
  · rintro ⟨multiplier, hKKT⟩
    exact ⟨multiplier, (isKKTPoint_toConstrainedOptimizationProblem_iff
      problem x multiplier hDiff).2 hKKT⟩

/-- Helper for Chapter11 Lemma 11.5.4: for a positive projected-gradient step, the projection is
fixed exactly when every feasible displacement has nonnegative pairing with the direction `g`. -/
lemma projection_fixed_iff_nonnegative_pairing
    (problem : LinearEqualityConstrainedProblem n m) (xStar : Point)
    (hxStar : xStar ∈ problem) (g : Point) {α : ℝ} (hα : 0 < α) :
    nearestPointProjection
        problem.feasibleSet
        ⟨xStar, hxStar⟩
        problem.isComplete_feasibleSet
        problem.convex_feasibleSet
        (xStar - α • g) = xStar ↔
      ∀ x : Point, x ∈ problem → 0 ≤ inner ℝ (x - xStar) g := by
  constructor
  · intro hProjection x hx
    have hprojection_le :
        inner ℝ
            ((xStar - α • g) -
              nearestPointProjection
                problem.feasibleSet
                ⟨xStar, hxStar⟩
                problem.isComplete_feasibleSet
                problem.convex_feasibleSet
                (xStar - α • g))
            (x - nearestPointProjection
              problem.feasibleSet
              ⟨xStar, hxStar⟩
              problem.isComplete_feasibleSet
              problem.convex_feasibleSet
              (xStar - α • g)) ≤ 0 := by
      simpa using
        real_inner_sub_nearestPointProjection_le_zero
          problem.feasibleSet
          ⟨xStar, hxStar⟩
          problem.isComplete_feasibleSet
          problem.convex_feasibleSet
          (xStar - α • g)
          x
          hx
    have hscaled :
        -α * inner ℝ (x - xStar) g ≤ 0 := by
      have hsub : (xStar - α • g) - xStar = -α • g := by simp
      rw [hProjection, hsub] at hprojection_le
      simpa [inner_smul_left, real_inner_comm, mul_comm, mul_left_comm, mul_assoc] using
        hprojection_le
    have hpair : 0 ≤ inner ℝ (x - xStar) g := by
      nlinarith
    exact hpair
  · intro hpair
    let projection :=
      nearestPointProjection
        problem.feasibleSet
        ⟨xStar, hxStar⟩
        problem.isComplete_feasibleSet
        problem.convex_feasibleSet
        (xStar - α • g)
    have hprojection_mem : projection ∈ problem := by
      exact
        nearestPointProjection_mem
          problem.feasibleSet
          ⟨xStar, hxStar⟩
          problem.isComplete_feasibleSet
          problem.convex_feasibleSet
          (xStar - α • g)
    have hprojection_le :
        inner ℝ ((xStar - α • g) - projection) (xStar - projection) ≤ 0 := by
      simpa [projection] using
        real_inner_sub_nearestPointProjection_le_zero
          problem.feasibleSet
          ⟨xStar, hxStar⟩
          problem.isComplete_feasibleSet
          problem.convex_feasibleSet
          (xStar - α • g)
          xStar
          hxStar
    have hpair_projection :
        0 ≤ inner ℝ (projection - xStar) g := hpair projection hprojection_mem
    have hpair_le :
        inner ℝ (xStar - projection) g ≤ 0 := by
      simpa [sub_eq_add_neg, inner_add_left, inner_add_right, inner_neg_left] using
        hpair_projection
    have hpair_le' :
        inner ℝ g (xStar - projection) ≤ 0 := by
      simpa [real_inner_comm] using hpair_le
    have hnorm_sq_le :
        ‖xStar - projection‖ ^ (2 : ℕ) ≤ 0 := by
      -- Combine the projection inequality with the nonnegative-pairing hypothesis at the
      -- projected point to force the norm square to vanish.
      have hmain :
          ‖xStar - projection‖ ^ (2 : ℕ) ≤ α * inner ℝ g (xStar - projection) := by
        have hsub :
            (xStar - α • g) - projection = (xStar - projection) - α • g := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        rw [hsub] at hprojection_le
        simpa [inner_sub_left, inner_smul_left, real_inner_comm, mul_comm, mul_left_comm,
          mul_assoc, sq] using hprojection_le
      nlinarith [hmain, hpair_le', hα]
    have hnorm_sq_nonneg : 0 ≤ ‖xStar - projection‖ ^ (2 : ℕ) := by positivity
    have hnorm_sq_eq : ‖xStar - projection‖ ^ (2 : ℕ) = 0 :=
      le_antisymm hnorm_sq_le hnorm_sq_nonneg
    have hzero : xStar - projection = 0 := by
      have hnorm_zero : ‖xStar - projection‖ = 0 := by
        nlinarith [hnorm_sq_eq]
      exact norm_eq_zero.mp hnorm_zero
    exact (sub_eq_zero.mp hzero).symm

/-- Helper for Chapter11 Lemma 11.5.4: the variational inequality
`0 ≤ ⟪x - xStar, g⟫` on the affine feasible set is equivalent to `g` lying in the range of the
constraint matrix. -/
lemma exists_multiplier_iff_nonnegative_pairing
    (problem : LinearEqualityConstrainedProblem n m) (xStar : Point)
    (hxStar : xStar ∈ problem) (g : Point) :
    (∃ multiplier : Multiplier,
      g = Matrix.toEuclideanLin problem.constraintMatrix multiplier) ↔
      ∀ x : Point, x ∈ problem → 0 ≤ inner ℝ (x - xStar) g := by
  constructor
  · rintro ⟨multiplier, hg⟩ x hx
    have hx_lin :
        Matrix.toEuclideanLin problem.constraintMatrix.transpose x =
          problem.constraintTarget := by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (WithLp.toLp 2) ((problem.mem_feasibleSet_iff x).1 hx)
    have hxStar_lin :
        Matrix.toEuclideanLin problem.constraintMatrix.transpose xStar =
          problem.constraintTarget := by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (WithLp.toLp 2) ((problem.mem_feasibleSet_iff xStar).1 hxStar)
    have hker :
        Matrix.toEuclideanLin problem.constraintMatrix.transpose (x - xStar) = 0 := by
      calc
        Matrix.toEuclideanLin problem.constraintMatrix.transpose (x - xStar)
            = Matrix.toEuclideanLin problem.constraintMatrix.transpose x -
                Matrix.toEuclideanLin problem.constraintMatrix.transpose xStar := by
                  simp
        _ = 0 := by simp [hx_lin, hxStar_lin]
    have hinner_zero :
        inner ℝ (x - xStar) (Matrix.toEuclideanLin problem.constraintMatrix multiplier) = 0 := by
      calc
        inner ℝ (x - xStar) (Matrix.toEuclideanLin problem.constraintMatrix multiplier)
            = inner ℝ
                (Matrix.toEuclideanLin problem.constraintMatrix.transpose (x - xStar))
                multiplier := by
                  rw [inner_matrix_action_eq_inner_transpose_action]
        _ = 0 := by simp [hker]
    simpa [hg, hinner_zero]
  · intro hpair
    have hxStar_lin :
        Matrix.toEuclideanLin problem.constraintMatrix.transpose xStar =
          problem.constraintTarget := by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (WithLp.toLp 2) ((problem.mem_feasibleSet_iff xStar).1 hxStar)
    have horth :
        ∀ d : Point,
          Matrix.toEuclideanLin problem.constraintMatrix.transpose d = 0 →
            inner ℝ d g = 0 := by
      intro d hd
      have hxAdd : xStar + d ∈ problem := by
        have hxAdd_eq :
            Matrix.toEuclideanLin problem.constraintMatrix.transpose (xStar + d) =
              problem.constraintTarget := by
          calc
            Matrix.toEuclideanLin problem.constraintMatrix.transpose (xStar + d)
                = Matrix.toEuclideanLin problem.constraintMatrix.transpose xStar +
                    Matrix.toEuclideanLin problem.constraintMatrix.transpose d := by
                      simp
            _ = problem.constraintTarget := by simp [hxStar_lin, hd]
        refine (problem.mem_feasibleSet_iff (xStar + d)).2 ?_
        simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
          congrArg WithLp.ofLp hxAdd_eq
      have hxSub : xStar - d ∈ problem := by
        have hxSub_eq :
            Matrix.toEuclideanLin problem.constraintMatrix.transpose (xStar - d) =
              problem.constraintTarget := by
          calc
            Matrix.toEuclideanLin problem.constraintMatrix.transpose (xStar - d)
                = Matrix.toEuclideanLin problem.constraintMatrix.transpose xStar -
                    Matrix.toEuclideanLin problem.constraintMatrix.transpose d := by
                      simp
            _ = problem.constraintTarget := by simp [hxStar_lin, hd]
        refine (problem.mem_feasibleSet_iff (xStar - d)).2 ?_
        simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
          congrArg WithLp.ofLp hxSub_eq
      have hnonneg_add : 0 ≤ inner ℝ d g := by
        simpa [sub_eq_add_neg] using hpair (xStar + d) hxAdd
      have hnonneg_sub : 0 ≤ inner ℝ (-d) g := by
        simpa [sub_eq_add_neg] using hpair (xStar - d) hxSub
      have hnonpos : inner ℝ d g ≤ 0 := by
        simpa [inner_neg_left] using hnonneg_sub
      exact le_antisymm hnonpos hnonneg_add
    rcases
      exists_in_range_transpose_of_orthogonal_ker
        problem.constraintMatrix.transpose g horth with
      ⟨multiplier, hmultiplier⟩
    refine ⟨multiplier, ?_⟩
    exact by simpa [Matrix.transpose_transpose] using hmultiplier.symm

/-- Chapter11 Lemma 11.5.4: for a feasible point `xStar` of a linearly equality-constrained
problem with `problem.objective` differentiable at `xStar`, there exists a multiplier vector
such that `∇ f(xStar) = A λ` if and only if there exists `δBar > 0`
such that the nearest-point projection of `xStar - α • ∇ f(xStar)` onto the feasible set of
`problem` is again `xStar` for every `α ∈ [0, δBar]`. -/
-- `DifferentiableAt.hasGradientAt` is the semantic bridge ensuring that the displayed
-- `gradient problem.objective xStar` denotes the actual gradient at `xStar`.
theorem exists_multiplier_iff_projection_fixedPoint
    (problem : LinearEqualityConstrainedProblem n m) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (hDiff : DifferentiableAt ℝ problem.objective xStar) :
    (∃ multiplier : Multiplier,
      gradient problem.objective xStar = problem.constraintMatrix.mulVec multiplier) ↔
      ∃ δBar : ℝ,
        0 < δBar ∧
          ∀ α ∈ Set.Icc (0 : ℝ) δBar,
            nearestPointProjection
                problem.feasibleSet
                ⟨xStar, hxStar⟩
                problem.isComplete_feasibleSet
                problem.convex_feasibleSet
                (xStar - α • gradient problem.objective xStar) = xStar := by
  constructor
  · intro hmultiplier
    rcases hmultiplier with ⟨multiplier, hmultiplier⟩
    have hmultiplier' :
        ∃ multiplier : Multiplier,
          gradient problem.objective xStar =
            Matrix.toEuclideanLin problem.constraintMatrix multiplier := by
      refine ⟨multiplier, ?_⟩
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (WithLp.toLp 2) hmultiplier
    have hpair :
        ∀ x : Point, x ∈ problem → 0 ≤ inner ℝ (x - xStar) (gradient problem.objective xStar) :=
      (exists_multiplier_iff_nonnegative_pairing problem xStar hxStar
        (gradient problem.objective xStar)).1 hmultiplier'
    refine ⟨1, zero_lt_one, ?_⟩
    intro α hα
    rcases hα with ⟨hα_nonneg, hα_le⟩
    rcases eq_or_lt_of_le hα_nonneg with rfl | hα_pos
    · -- The zero step is fixed because `xStar` is already feasible.
      simpa using
        nearestPointProjection_eq_self
          problem.feasibleSet
          ⟨xStar, hxStar⟩
          problem.isComplete_feasibleSet
          problem.convex_feasibleSet
          hxStar
    · exact
        (projection_fixed_iff_nonnegative_pairing problem xStar hxStar
          (gradient problem.objective xStar) hα_pos).2 hpair
  · rintro ⟨δBar, hδBar, hprojection⟩
    have hfixed :
        nearestPointProjection
            problem.feasibleSet
            ⟨xStar, hxStar⟩
            problem.isComplete_feasibleSet
            problem.convex_feasibleSet
            (xStar - δBar • gradient problem.objective xStar) = xStar :=
      hprojection δBar ⟨le_of_lt hδBar, le_rfl⟩
    have hpair :
        ∀ x : Point, x ∈ problem → 0 ≤ inner ℝ (x - xStar) (gradient problem.objective xStar) :=
      (projection_fixed_iff_nonnegative_pairing problem xStar hxStar
        (gradient problem.objective xStar) hδBar).1 hfixed
    have hmultiplier' :
        ∃ multiplier : Multiplier,
          gradient problem.objective xStar =
            Matrix.toEuclideanLin problem.constraintMatrix multiplier :=
      (exists_multiplier_iff_nonnegative_pairing problem xStar hxStar
        (gradient problem.objective xStar)).2 hpair
    rcases hmultiplier' with ⟨multiplier, hmultiplier⟩
    refine ⟨multiplier, ?_⟩
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
      congrArg WithLp.ofLp hmultiplier

/-- Bridge/view companion to Lemma 11.5.4: the source equality-constrained multiplier condition
is equivalent to existence of a Chapter 8 KKT multiplier for the equality-only constrained
problem bridge, so the projection characterization can also be stated with the Chapter 8 KKT
owner. -/
theorem exists_isKKTPoint_toConstrainedOptimizationProblem_iff_projection_fixedPoint
    (problem : LinearEqualityConstrainedProblem n m) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (hDiff : DifferentiableAt ℝ problem.objective xStar) :
    (∃ multiplier : Multiplier,
      problem.toConstrainedOptimizationProblem.IsKKTPoint xStar.ofLp multiplier.ofLp) ↔
      ∃ δBar : ℝ,
        0 < δBar ∧
          ∀ α ∈ Set.Icc (0 : ℝ) δBar,
            nearestPointProjection
                problem.feasibleSet
                ⟨xStar, hxStar⟩
                problem.isComplete_feasibleSet
                problem.convex_feasibleSet
                (xStar - α • gradient problem.objective xStar) = xStar := by
  rw [exists_isKKTPoint_toConstrainedOptimizationProblem_iff problem xStar hDiff]
  constructor
  · rintro ⟨multiplier, -, hGradient⟩
    exact (exists_multiplier_iff_projection_fixedPoint problem xStar hxStar hDiff).1
      ⟨multiplier, hGradient⟩
  · intro hProjection
    rcases (exists_multiplier_iff_projection_fixedPoint problem xStar hxStar hDiff).2
      hProjection with ⟨multiplier, hGradient⟩
    exact ⟨multiplier, hxStar, hGradient⟩

end LinearEqualityConstrainedProblem

end
