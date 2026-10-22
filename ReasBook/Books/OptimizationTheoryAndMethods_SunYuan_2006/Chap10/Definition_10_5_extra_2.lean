/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_5_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.StandardPenaltyProblemBridge

noncomputable section

open scoped BigOperators

variable {n m : ℕ}

-- Local notation justification (file-local vocabulary): Chapter 10 optimization files use
-- `Point` and `MultiplierVec` as readable Euclidean-space shorthands, and keeping them local
-- avoids introducing public alias owners for ambient types that this item does not own.
local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MultiplierVec" => EuclideanSpace ℝ (Fin m)

-- Domain-style sampling pass:
-- * primary domain: Chapter 10 equality-constrained smooth exact penalty functions and their
--   linearized subproblems.
-- * sampled owner declarations in the minimal project closure:
--   - `equalitySmoothExactPenaltyFunction`
--   - `simpleSmoothExactPenaltyFunction`
--   - `constantConstraintPoint`
--   - `fletcherSimpleSmoothExactPenaltyFunction`
-- * best owner abstraction: `Definition_10_5_extra_1.equalitySmoothExactPenaltyFunction`.
-- * primitive data kept here: the explicit multiplier field
--   `equalitySmoothExactPenaltyMultiplier` and the correction matrix
--   `equalitySmoothExactPenaltyCorrection`.
-- * derived API here: bridge comments pointing back to that owner, together with the associated
--   linearized multiplier/dual statements.
--
-- Source/core/bridge triage:
-- * source-facing layer here: the explicit multiplier formula and the linearized subproblem
--   predicates attached to Definition 10.5-extra-2.
-- * core/canonical owners reused here:
--   `equalitySmoothExactPenaltyFunction` from `Definition_10_5_extra_1`,
--   `equalitySmoothExactPenaltySubproblemObjective`,
--   `generalSmoothExactPenaltyFeasibleSet`,
--   `isGeneralSmoothExactPenaltySubproblemMultiplier`,
--   and the Euclidean matrix action `Matrix.toEuclideanLin`.
-- * bridge/view retained here:
--   `constraintGradientMatrix`, which packages an explicit gradient family into the Jacobian
--   matrix used by `HasFDerivAt`, and the equality-case specialization lemmas relating the
--   matrix-based subproblem formulas to the general gradient-family owner.

/-- The matrix whose `i`th column is the chosen gradient vector `gradConstraint i x`. -/
def constraintGradientMatrix
    (gradConstraint : Fin m → Point → Point) (x : Point) :
    Matrix (Fin n) (Fin m) ℝ :=
  fun j i ↦ gradConstraint i x j

/-- The column family of a matrix field, viewed in the ambient Euclidean point space. -/
abbrev matrixColumnFamily
    (A : Point → Matrix (Fin n) (Fin m) ℝ) :
    Fin m → Point → Point :=
  fun i x ↦ WithLp.toLp 2 (fun j ↦ A x j i)

/-- Equality-case helper: the matrix replacing `D` in `(10.5.3)` is
`2 * σ * (A⁺ x) * (A⁺ x)ᵀ`. -/
def equalitySmoothExactPenaltyCorrection
    (Aplus : Point → Matrix (Fin m) (Fin n) ℝ) (σ : ℝ) (x : Point) :
    Matrix (Fin m) (Fin m) ℝ :=
  (2 * σ) • (Aplus x * (Aplus x).transpose)

/-- Evaluating `equalitySmoothExactPenaltyCorrection` expands to the source matrix formula
`2 * σ * (A⁺ x) * (A⁺ x)ᵀ`. -/
theorem equalitySmoothExactPenaltyCorrection_apply
    (Aplus : Point → Matrix (Fin m) (Fin n) ℝ) (σ : ℝ) (x : Point) :
    equalitySmoothExactPenaltyCorrection Aplus σ x =
      (2 * σ) • (Aplus x * (Aplus x).transpose) := rfl

/-- Equality-case helper: in the equality-constrained case, the multiplier
function is `π(x) = A⁺ x (g x - σ * (A⁺ x)ᵀ c(x))`. -/
def equalitySmoothExactPenaltyMultiplier
    (g : Point → Point) (c : Point → MultiplierVec)
    (Aplus : Point → Matrix (Fin m) (Fin n) ℝ) (σ : ℝ) (x : Point) :
    MultiplierVec :=
  Matrix.toEuclideanLin (Aplus x)
    (g x - σ • Matrix.toEuclideanLin ((Aplus x).transpose) (c x))

/-- Evaluating `equalitySmoothExactPenaltyMultiplier` gives the source formula
`π(x) = A⁺ x (g x - σ * (A⁺ x)ᵀ c(x))`. -/
theorem equalitySmoothExactPenaltyMultiplier_apply
    (g : Point → Point) (c : Point → MultiplierVec)
    (Aplus : Point → Matrix (Fin m) (Fin n) ℝ) (σ : ℝ) (x : Point) :
    equalitySmoothExactPenaltyMultiplier g c Aplus σ x =
      Matrix.toEuclideanLin (Aplus x)
        (g x - σ • Matrix.toEuclideanLin ((Aplus x).transpose) (c x)) := rfl

/-- Equality-case helper: in the equality-constrained case, the source penalty
formula `P(x) = f x - π(x)ᵀ c(x)` is the Chapter 10 owner
`equalitySmoothExactPenaltyFunction` specialized to the multiplier field
`equalitySmoothExactPenaltyMultiplier g c Aplus σ` and zero diagonal penalty. -/
def equalitySmoothExactPenaltyFunctionOfMultiplier
    (f : Point → ℝ)
    (g : Point → Point) (c : Point → MultiplierVec)
    (Aplus : Point → Matrix (Fin m) (Fin n) ℝ) (σ : ℝ) (x : Point) : ℝ :=
  equalitySmoothExactPenaltyFunction
    f (equalitySmoothExactPenaltyMultiplier g c Aplus σ) c (constantConstraintPoint 0) x

/-- Evaluating `equalitySmoothExactPenaltyFunctionOfMultiplier` gives the source formula
`P(x) = f x - π(x)ᵀ c(x)` from `(10.5.8)`. -/
theorem equalitySmoothExactPenaltyFunctionOfMultiplier_apply
    (f : Point → ℝ)
    (g : Point → Point) (c : Point → MultiplierVec)
    (Aplus : Point → Matrix (Fin m) (Fin n) ℝ) (σ : ℝ) (x : Point) :
    equalitySmoothExactPenaltyFunctionOfMultiplier f g c Aplus σ x =
      f x - dotProduct (equalitySmoothExactPenaltyMultiplier g c Aplus σ x) (c x) := by
  simp [equalitySmoothExactPenaltyFunctionOfMultiplier, equalitySmoothExactPenaltyFunction,
    constantConstraintPoint_def]

/-- The feasible set of the equality-constrained quadratic subproblem
`A(x)ᵀ d + c(x) = 0`. -/
def equalitySmoothExactPenaltyFeasibleSet
    (A : Point → Matrix (Fin n) (Fin m) ℝ) (c : Point → MultiplierVec) (x : Point) :
    Set Point :=
  {d | Matrix.toEuclideanLin ((A x).transpose) d + c x = 0}

/-- Membership in `equalitySmoothExactPenaltyFeasibleSet A c x` is exactly the source linearized
equality constraint `A(x)ᵀ d + c(x) = 0`. -/
theorem mem_equalitySmoothExactPenaltyFeasibleSet_iff
    (A : Point → Matrix (Fin n) (Fin m) ℝ) (c : Point → MultiplierVec)
    (x d : Point) :
    d ∈ equalitySmoothExactPenaltyFeasibleSet A c x ↔
      Matrix.toEuclideanLin ((A x).transpose) d + c x = 0 := Iff.rfl

/-- The quadratic objective of the equality-constrained subproblem `(10.5.10)` is
`d ↦ g(x)ᵀ d + (σ / 2) * ‖d‖²`. -/
def equalitySmoothExactPenaltySubproblemObjective
    (g : Point → Point) (σ : ℝ) (x d : Point) : ℝ :=
  dotProduct (g x) d + (σ / 2) * ‖d‖ ^ (2 : ℕ)

/-- Evaluating `equalitySmoothExactPenaltySubproblemObjective g σ x` gives the source quadratic
objective from `(10.5.10)`. -/
theorem equalitySmoothExactPenaltySubproblemObjective_apply
    (g : Point → Point) (σ : ℝ) (x d : Point) :
    equalitySmoothExactPenaltySubproblemObjective g σ x d =
      dotProduct (g x) d + (σ / 2) * ‖d‖ ^ (2 : ℕ) := rfl

/-- `isEqualitySmoothExactPenaltySubproblemMultiplier A g c σ x π` means that `π` is a
Lagrange multiplier for the equality-constrained quadratic subproblem `(10.5.10)`-`(10.5.11)`
at the base point `x`, witnessed by some minimizer `d`. -/
def isEqualitySmoothExactPenaltySubproblemMultiplier
    (A : Point → Matrix (Fin n) (Fin m) ℝ) (g : Point → Point) (c : Point → MultiplierVec)
    (σ : ℝ) (x : Point) (π : MultiplierVec) : Prop :=
  ∃ d : Point,
    d ∈ equalitySmoothExactPenaltyFeasibleSet A c x ∧
      IsMinOn (equalitySmoothExactPenaltySubproblemObjective g σ x)
        (equalitySmoothExactPenaltyFeasibleSet A c x) d ∧
      g x + σ • d = Matrix.toEuclideanLin (A x) π

/-- Unfolding `isEqualitySmoothExactPenaltySubproblemMultiplier A g c σ x π` gives the
existence of a minimizing direction `d` together with the source stationarity equation
`g(x) + σ d = A(x) π`. -/
theorem isEqualitySmoothExactPenaltySubproblemMultiplier_iff
    (A : Point → Matrix (Fin n) (Fin m) ℝ) (g : Point → Point) (c : Point → MultiplierVec)
    (σ : ℝ) (x : Point) (π : MultiplierVec) :
    isEqualitySmoothExactPenaltySubproblemMultiplier A g c σ x π ↔
      ∃ d : Point,
        d ∈ equalitySmoothExactPenaltyFeasibleSet A c x ∧
          IsMinOn (equalitySmoothExactPenaltySubproblemObjective g σ x)
            (equalitySmoothExactPenaltyFeasibleSet A c x) d ∧
          g x + σ • d = Matrix.toEuclideanLin (A x) π := Iff.rfl

/-- Helper: matrix multiplication inside
`Matrix.toEuclideanLin` evaluates as composition of the two matrix actions. -/
theorem toEuclideanLin_mul_apply
    {l m n : ℕ}
    (M : Matrix (Fin l) (Fin m) ℝ) (N : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (M * N) v =
      Matrix.toEuclideanLin M (Matrix.toEuclideanLin N v) := by
  -- Evaluate the composed matrix action coordinatewise and use `Matrix.mulVec_mulVec`.
  ext i
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- Helper: pairing `Matrix.toEuclideanLin A u` with `v`
transfers the matrix action to the transpose. -/
theorem dotProduct_toEuclideanLin_eq_transpose
    (A : Matrix (Fin n) (Fin m) ℝ) (u : MultiplierVec) (v : Point) :
    dotProduct (Matrix.toEuclideanLin A u) v =
      dotProduct u (Matrix.toEuclideanLin A.transpose v) := by
  -- Expand both dot products to the same finite sum over matrix entries.
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]

/-- Helper: the Penrose identities imply
`(A x)ᵀ * A x * Aplus x = (A x)ᵀ`. -/
theorem transpose_mul_mul_pseudoInverse_eq
    (A : Point → Matrix (Fin n) (Fin m) ℝ)
    (Aplus : Point → Matrix (Fin m) (Fin n) ℝ)
    (x : Point)
    (hAplus : isChosenPseudoInverseAt A Aplus x) :
    (A x).transpose * A x * Aplus x = (A x).transpose := by
  rcases hAplus with ⟨hleft, _, hsymLeft, _⟩
  have hsym : (Aplus x).transpose * (A x).transpose = A x * Aplus x := by
    simpa [Matrix.transpose_mul] using hsymLeft
  apply Matrix.transpose_injective
  -- Transpose the target identity and collapse it with `A * Aplus * A = A`.
  calc
    (((A x).transpose * A x * Aplus x).transpose)
        = (Aplus x).transpose * (A x).transpose * A x := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (A x * Aplus x) * A x := by
          rw [hsym, Matrix.mul_assoc]
    _ = A x := hleft
    _ = ((A x).transpose).transpose := by simp

/-- Helper: the row projector `Aplus x * A x` fixes the
row space of `A x`, so it fixes vectors of the form `(A x)ᵀ d`. -/
theorem rowProjector_mul_transpose_eq
    (A : Point → Matrix (Fin n) (Fin m) ℝ)
    (Aplus : Point → Matrix (Fin m) (Fin n) ℝ)
    (x : Point)
    (hAplus : isChosenPseudoInverseAt A Aplus x) :
    Aplus x * A x * (A x).transpose = (A x).transpose := by
  rcases hAplus with ⟨hleft, _, _, hsymRight⟩
  have hsym : (A x).transpose * (Aplus x).transpose = Aplus x * A x := by
    simpa [Matrix.transpose_mul] using hsymRight
  apply Matrix.transpose_injective
  -- Again, transpose the target identity and reduce to `A * Aplus * A = A`.
  calc
    ((Aplus x * A x * (A x).transpose).transpose)
        = A x * (A x).transpose * (Aplus x).transpose := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = A x * ((A x).transpose * (Aplus x).transpose) := by
          rw [Matrix.mul_assoc]
    _ = A x * (Aplus x * A x) := by rw [hsym]
    _ = A x * Aplus x * A x := by rw [Matrix.mul_assoc]
    _ = A x := hleft
    _ = ((A x).transpose).transpose := by simp

/-- Helper: feasibility supplies that `c x` lies in the
row space of `A x`, so the row projector `Aplus x * A x` fixes `c x`. -/
theorem rowProjector_apply_constraint_eq
    (A : Point → Matrix (Fin n) (Fin m) ℝ)
    (Aplus : Point → Matrix (Fin m) (Fin n) ℝ)
    (c : Point → MultiplierVec)
    (x : Point)
    (hAplus : isChosenPseudoInverseAt A Aplus x)
    {d0 : Point}
    (hd0 : d0 ∈ equalitySmoothExactPenaltyFeasibleSet A c x) :
    Matrix.toEuclideanLin (Aplus x * A x) (c x) = c x := by
  have hconstraint :
      Matrix.toEuclideanLin ((A x).transpose) d0 = - c x := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using
      (mem_equalitySmoothExactPenaltyFeasibleSet_iff A c x d0).1 hd0
  -- Rewrite `c x` through a feasible witness and then collapse the row projector on the row space.
  calc
    Matrix.toEuclideanLin (Aplus x * A x) (c x)
        = Matrix.toEuclideanLin (Aplus x * A x)
            (-Matrix.toEuclideanLin ((A x).transpose) d0) := by
              congr 1
              simpa [hconstraint]
    _ = -Matrix.toEuclideanLin (Aplus x * A x)
          (Matrix.toEuclideanLin ((A x).transpose) d0) := by
            simp
    _ = -Matrix.toEuclideanLin ((Aplus x * A x) * (A x).transpose) d0 := by
          rw [← toEuclideanLin_mul_apply]
    _ = -Matrix.toEuclideanLin ((A x).transpose) d0 := by
          rw [rowProjector_mul_transpose_eq A Aplus x hAplus]
    _ = c x := by
          rw [hconstraint]
          simp

-- A feasible difference lives in the homogeneous kernel of the transpose constraint map.
/-- Helper for Chapter10 Definition 10.5-extra-2: feasible directions differ by an element of
the kernel of `A(x)ᵀ`. -/
theorem equalityFeasibleDiff_transpose_apply_eq_zero
    (A : Point → Matrix (Fin n) (Fin m) ℝ)
    (c : Point → MultiplierVec) (x : Point)
    {d y : Point}
    (hd : d ∈ equalitySmoothExactPenaltyFeasibleSet A c x)
    (hy : y ∈ equalitySmoothExactPenaltyFeasibleSet A c x) :
    Matrix.toEuclideanLin ((A x).transpose) (y - d) = 0 := by
  -- Rewrite both feasible points against the same affine constraint right-hand side.
  have hdEq : Matrix.toEuclideanLin ((A x).transpose) d = -c x := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using (mem_equalitySmoothExactPenaltyFeasibleSet_iff A c x d).1 hd
  have hyEq : Matrix.toEuclideanLin ((A x).transpose) y = -c x := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using (mem_equalitySmoothExactPenaltyFeasibleSet_iff A c x y).1 hy
  -- Subtract the two affine equations to place the feasible difference in the homogeneous kernel.
  calc
    Matrix.toEuclideanLin ((A x).transpose) (y - d)
        = Matrix.toEuclideanLin ((A x).transpose) y -
            Matrix.toEuclideanLin ((A x).transpose) d := by
              simp
    _ = (-c x) - (-c x) := by rw [hyEq, hdEq]
    _ = 0 := by simp

/-- Helper for Chapter10 Definition 10.5-extra-2: the half squared-norm gap between two
Euclidean vectors splits into a bilinear term plus the squared norm of their difference. -/
theorem halfNormSq_gap_eq
    (u v : Point) :
    (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * ‖v‖ ^ (2 : ℕ) =
      dotProduct v (u - v) + (1 / 2 : ℝ) * ‖u - v‖ ^ (2 : ℕ) := by
  -- Route correction: normalize the quadratic term once at the vector level instead of
  -- re-expanding coordinates inside each objective-gap theorem.
  calc
    (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * ‖v‖ ^ (2 : ℕ)
        = ∑ i, ((1 / 2 : ℝ) * (u i) ^ (2 : ℕ) - (1 / 2 : ℝ) * (v i) ^ (2 : ℕ)) := by
            rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
              Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ = ∑ i, (v i * (u i - v i) + (1 / 2 : ℝ) * ((u - v) i) ^ (2 : ℕ)) := by
          -- Normalize each coordinate contribution with scalar arithmetic.
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp
          ring
    _ = dotProduct v (u - v) + (1 / 2 : ℝ) * ‖u - v‖ ^ (2 : ℕ) := by
          -- Fold the coordinate sums back into the dot product and Euclidean norm.
          rw [dotProduct, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          simp

/-- Helper for Chapter10 Definition 10.5-extra-2: the equality-subproblem objective gap from
`d` to `y` splits into the affine stationarity term and a quadratic remainder. -/
theorem equalitySmoothExactPenaltySubproblemObjective_gap_eq
    (g : Point → Point) (σ : ℝ) (x d y : Point) :
    equalitySmoothExactPenaltySubproblemObjective g σ x y -
      equalitySmoothExactPenaltySubproblemObjective g σ x d =
      dotProduct (g x + σ • d) (y - d) +
        (σ / 2) * ‖y - d‖ ^ (2 : ℕ) := by
  have hsmul : σ * dotProduct d (y - d) = dotProduct (σ • d) (y - d) := by
    simpa [smul_eq_mul] using (smul_dotProduct σ d (y - d)).symm
  -- Split the objective gap into its linear part and the shared half-norm-square gap.
  calc
    equalitySmoothExactPenaltySubproblemObjective g σ x y -
        equalitySmoothExactPenaltySubproblemObjective g σ x d
      = dotProduct (g x) (y - d) +
          ((σ / 2) * ‖y‖ ^ (2 : ℕ) - (σ / 2) * ‖d‖ ^ (2 : ℕ)) := by
            rw [equalitySmoothExactPenaltySubproblemObjective_apply,
              equalitySmoothExactPenaltySubproblemObjective_apply, add_sub_add_comm,
              dotProduct_sub]
    _ = dotProduct (g x) (y - d) +
          σ * ((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ)) := by
            ring
    _ = dotProduct (g x) (y - d) +
          σ * (dotProduct d (y - d) + (1 / 2 : ℝ) * ‖y - d‖ ^ (2 : ℕ)) := by
            rw [halfNormSq_gap_eq y d]
    _ = dotProduct (g x) (y - d) +
          (dotProduct (σ • d) (y - d) + (σ / 2) * ‖y - d‖ ^ (2 : ℕ)) := by
            rw [mul_add, hsmul]
            ring
    _ = (dotProduct (g x) (y - d) + dotProduct (σ • d) (y - d)) +
          (σ / 2) * ‖y - d‖ ^ (2 : ℕ) := by
            rw [add_assoc]
    _ = dotProduct (g x + σ • d) (y - d) +
          (σ / 2) * ‖y - d‖ ^ (2 : ℕ) := by
            rw [← add_dotProduct]
            simp

theorem isMinOn_of_equalitySubproblemStationary
    (A : Point → Matrix (Fin n) (Fin m) ℝ)
    (g : Point → Point) (c : Point → MultiplierVec)
    (σ : ℝ) (x : Point) (π : MultiplierVec) (d : Point)
    (hσ : 0 < σ)
    (hd : d ∈ equalitySmoothExactPenaltyFeasibleSet A c x)
    (hstationary : g x + σ • d = Matrix.toEuclideanLin (A x) π) :
    IsMinOn (equalitySmoothExactPenaltySubproblemObjective g σ x)
      (equalitySmoothExactPenaltyFeasibleSet A c x) d := by
  rw [isMinOn_iff]
  intro y hy
  have htransposeZero :
      Matrix.toEuclideanLin ((A x).transpose) (y - d) = 0 :=
    equalityFeasibleDiff_transpose_apply_eq_zero A c x hd hy
  have hlinear :
      dotProduct (g x + σ • d) (y - d) = 0 := by
    -- Pair stationarity with the feasible difference and move the matrix action to `A(x)ᵀ`.
    calc
      dotProduct (g x + σ • d) (y - d)
          = dotProduct (Matrix.toEuclideanLin (A x) π) (y - d) := by rw [hstationary]
      _ = dotProduct π (Matrix.toEuclideanLin ((A x).transpose) (y - d)) := by
            simpa using dotProduct_toEuclideanLin_eq_transpose (A x) π (y - d)
      _ = 0 := by simp [htransposeZero]
  have hnorm_nonneg : 0 ≤ ‖y - d‖ ^ (2 : ℕ) := by
    simpa [pow_two] using sq_nonneg ‖y - d‖
  have hquad_nonneg : 0 ≤ (σ / 2) * ‖y - d‖ ^ (2 : ℕ) := by
    have hsigmaHalf : 0 ≤ σ / 2 := by linarith
    exact mul_nonneg hsigmaHalf hnorm_nonneg
  have hgap_nonneg :
      0 ≤ equalitySmoothExactPenaltySubproblemObjective g σ x y -
        equalitySmoothExactPenaltySubproblemObjective g σ x d := by
    -- After the stationarity term vanishes, only the nonnegative quadratic remainder remains.
    rw [equalitySmoothExactPenaltySubproblemObjective_gap_eq g σ x d y, hlinear]
    simpa using hquad_nonneg
  linarith

/-- Equality-case bridge theorem: if `A x` is the Jacobian `∇ c(x)` and `Aplus x` is
the chosen pseudoinverse used in `(10.5.7)`-`(10.5.9)`, then, provided the linearized equality
subproblem `(10.5.10)`-`(10.5.11)` is feasible at `x`, the explicit vector
`equalitySmoothExactPenaltyMultiplier g c Aplus σ x` is a Lagrange multiplier of that
equality-constrained quadratic subproblem for a positive penalty parameter `σ`. -/
theorem equalitySmoothExactPenaltyMultiplier_isLagrangeMultiplier
    (A : Point → Matrix (Fin n) (Fin m) ℝ)
    (Aplus : Point → Matrix (Fin m) (Fin n) ℝ)
    (g : Point → Point) (c : Point → MultiplierVec)
    (σ : ℝ) (x : Point)
    (hσ : 0 < σ)
    (hA : HasFDerivAt c ((Matrix.toEuclideanLin ((A x).transpose)).toContinuousLinearMap) x)
    (hAplus : isChosenPseudoInverseAt A Aplus x)
    (hfeasible : Set.Nonempty (equalitySmoothExactPenaltyFeasibleSet A c x)) :
    isEqualitySmoothExactPenaltySubproblemMultiplier A g c σ x
      (equalitySmoothExactPenaltyMultiplier g c Aplus σ x) := by
  let _ := hA
  rcases hfeasible with ⟨d0, hd0⟩
  let π := equalitySmoothExactPenaltyMultiplier g c Aplus σ x
  let d : Point := (σ⁻¹) • (Matrix.toEuclideanLin (A x) π - g x)
  have hrowProjector :
      Matrix.toEuclideanLin (Aplus x * A x) (c x) = c x :=
    rowProjector_apply_constraint_eq A Aplus c x hAplus hd0
  have hAπ :
      Matrix.toEuclideanLin ((A x).transpose) (Matrix.toEuclideanLin (A x) π) =
        Matrix.toEuclideanLin ((A x).transpose) (g x) - σ • c x := by
    -- Collapse the pseudoinverse formula for `π` down to the affine constraint residual.
    calc
      Matrix.toEuclideanLin ((A x).transpose) (Matrix.toEuclideanLin (A x) π)
          = Matrix.toEuclideanLin ((A x).transpose * A x) π := by
              rw [toEuclideanLin_mul_apply]
      _ = Matrix.toEuclideanLin (((A x).transpose * A x) * Aplus x)
            (g x - σ • Matrix.toEuclideanLin ((Aplus x).transpose) (c x)) := by
              simp [π, equalitySmoothExactPenaltyMultiplier_apply]
      _ = Matrix.toEuclideanLin ((A x).transpose)
            (g x - σ • Matrix.toEuclideanLin ((Aplus x).transpose) (c x)) := by
              rw [transpose_mul_mul_pseudoInverse_eq A Aplus x hAplus]
      _ = Matrix.toEuclideanLin ((A x).transpose) (g x) -
            σ • Matrix.toEuclideanLin ((A x).transpose)
              (Matrix.toEuclideanLin ((Aplus x).transpose) (c x)) := by
              simp
      _ = Matrix.toEuclideanLin ((A x).transpose) (g x) -
            σ • Matrix.toEuclideanLin (((A x).transpose) * (Aplus x).transpose) (c x) := by
              rw [toEuclideanLin_mul_apply]
      _ = Matrix.toEuclideanLin ((A x).transpose) (g x) -
            σ • Matrix.toEuclideanLin ((Aplus x * A x).transpose) (c x) := by
              simp [Matrix.transpose_mul]
      _ = Matrix.toEuclideanLin ((A x).transpose) (g x) -
            σ • Matrix.toEuclideanLin (Aplus x * A x) (c x) := by
              rw [hAplus.2.2.2]
      _ = Matrix.toEuclideanLin ((A x).transpose) (g x) - σ • c x := by
              rw [hrowProjector]
  have hdFeasible : d ∈ equalitySmoothExactPenaltyFeasibleSet A c x := by
    -- The candidate direction satisfies `A(x)ᵀ d + c(x) = 0` by the projector identity above.
    rw [mem_equalitySmoothExactPenaltyFeasibleSet_iff]
    calc
      Matrix.toEuclideanLin ((A x).transpose) d + c x
          = σ⁻¹ •
              (Matrix.toEuclideanLin ((A x).transpose)
                (Matrix.toEuclideanLin (A x) π) -
                Matrix.toEuclideanLin ((A x).transpose) (g x)) +
              c x := by
                simp [d, LinearMap.map_sub]
      _ = σ⁻¹ • (-σ • c x) + c x := by
            rw [hAπ]
            simp
      _ = 0 := by
            simp [smul_smul, hσ.ne', mul_assoc, mul_comm, mul_left_comm]
  have hstationary :
      g x + σ • d = Matrix.toEuclideanLin (A x) π := by
    -- The candidate direction was chosen to make the stationarity equation exact.
    calc
      g x + σ • d
          = g x + σ • ((σ⁻¹) • (Matrix.toEuclideanLin (A x) π - g x)) := by
              rfl
      _ = g x + (Matrix.toEuclideanLin (A x) π - g x) := by
            simp [smul_smul, hσ.ne', mul_assoc, mul_comm, mul_left_comm]
      _ = Matrix.toEuclideanLin (A x) π := by
            simp
  refine ⟨d, hdFeasible, ?_, ?_⟩
  · -- A feasible stationary point minimizes the quadratic objective on the affine feasible set.
    exact isMinOn_of_equalitySubproblemStationary A g c σ x π d hσ hdFeasible hstationary
  · simpa [π] using hstationary

/- For a general equality-and-inequality constrained problem, the quadratic objective from
`(10.5.12)` is the same owner `equalitySmoothExactPenaltySubproblemObjective` used in the
equality-constrained case. -/
#check equalitySmoothExactPenaltySubproblemObjective

/-- The feasible set of the linearized equality-and-inequality constrained subproblem
`(10.5.13)`-`(10.5.14)`, with `E` and `I` the equality and inequality index sets. -/
def generalSmoothExactPenaltyFeasibleSet
    (E I : Set (Fin m))
    (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point) (x : Point) : Set Point :=
  {d |
    (∀ i ∈ E, c x i + dotProduct d (gradConstraint i x) = 0) ∧
      ∀ i ∈ I, 0 ≤ c x i + dotProduct d (gradConstraint i x)}

/-- Membership in `generalSmoothExactPenaltyFeasibleSet E I c gradConstraint x` is
exactly the system of linearized equality and inequality constraints from
`(10.5.13)`-`(10.5.14)`. -/
theorem mem_generalSmoothExactPenaltyFeasibleSet_iff
    (E I : Set (Fin m))
    (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point) (x d : Point) :
    d ∈ generalSmoothExactPenaltyFeasibleSet E I c gradConstraint x ↔
      (∀ i ∈ E, c x i + dotProduct d (gradConstraint i x) = 0) ∧
        ∀ i ∈ I, 0 ≤ c x i + dotProduct d (gradConstraint i x) := Iff.rfl

/-- The dual-feasible multiplier vectors for `(10.5.16)`, requiring only the nonnegativity
constraints `π_i ≥ 0` on the inequality index set `I`. -/
def generalSmoothExactPenaltyDualFeasibleSet
    (I : Set (Fin m)) : Set MultiplierVec :=
  {π | ∀ i ∈ I, 0 ≤ π i}

/-- Membership in `generalSmoothExactPenaltyDualFeasibleSet I` is exactly the source side
condition `π_i ≥ 0` for `i ∈ I`. -/
theorem mem_generalSmoothExactPenaltyDualFeasibleSet_iff
    (I : Set (Fin m)) (π : MultiplierVec) :
    π ∈ generalSmoothExactPenaltyDualFeasibleSet I ↔ ∀ i ∈ I, 0 ≤ π i := Iff.rfl

/-- `generalSmoothExactPenaltySubproblemStationarity g gradConstraint σ x π d` is the source
stationarity equation `g(x) + σ d = ∑ i, π_i ∇ c_i(x)`. -/
def generalSmoothExactPenaltySubproblemStationarity
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) (d : Point) : Prop :=
  g x + σ • d = ∑ i : Fin m, π i • gradConstraint i x

/-- Unfolding `generalSmoothExactPenaltySubproblemStationarity g gradConstraint σ x π d` gives
the source stationarity equation. -/
theorem generalSmoothExactPenaltySubproblemStationarity_iff
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) (d : Point) :
    generalSmoothExactPenaltySubproblemStationarity g gradConstraint σ x π d ↔
      g x + σ • d = ∑ i : Fin m, π i • gradConstraint i x := Iff.rfl

/-- `generalSmoothExactPenaltySubproblemComplementarity I c gradConstraint x π d` is the source
complementarity condition for the inequality constraints. -/
def generalSmoothExactPenaltySubproblemComplementarity
    (I : Set (Fin m)) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (x : Point) (π : MultiplierVec) (d : Point) : Prop :=
  ∀ i ∈ I, π i * (c x i + dotProduct d (gradConstraint i x)) = 0

/-- Unfolding
`generalSmoothExactPenaltySubproblemComplementarity I c gradConstraint x π d` gives the source
complementarity equations. -/
theorem generalSmoothExactPenaltySubproblemComplementarity_iff
    (I : Set (Fin m)) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (x : Point) (π : MultiplierVec) (d : Point) :
    generalSmoothExactPenaltySubproblemComplementarity I c gradConstraint x π d ↔
      ∀ i ∈ I, π i * (c x i + dotProduct d (gradConstraint i x)) = 0 := Iff.rfl

/-- `generalSmoothExactPenaltySubproblemFirstOrderConditions I g c gradConstraint σ x π d`
collects the source stationarity and complementarity conditions. -/
def generalSmoothExactPenaltySubproblemFirstOrderConditions
    (I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) (d : Point) : Prop :=
  generalSmoothExactPenaltySubproblemStationarity g gradConstraint σ x π d ∧
    generalSmoothExactPenaltySubproblemComplementarity I c gradConstraint x π d

/-- Unfolding `generalSmoothExactPenaltySubproblemFirstOrderConditions` gives the source
stationarity and complementarity conditions. -/
theorem generalSmoothExactPenaltySubproblemFirstOrderConditions_iff
    (I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) (d : Point) :
    generalSmoothExactPenaltySubproblemFirstOrderConditions
        I g c gradConstraint σ x π d ↔
      generalSmoothExactPenaltySubproblemStationarity g gradConstraint σ x π d ∧
        generalSmoothExactPenaltySubproblemComplementarity I c gradConstraint x π d := Iff.rfl

/-- `generalSmoothExactPenaltySubproblemKKT I g c gradConstraint σ x π d` collects the source
dual-feasibility and first-order conditions for the linearized subproblem. -/
def generalSmoothExactPenaltySubproblemKKT
    (I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) (d : Point) : Prop :=
  π ∈ generalSmoothExactPenaltyDualFeasibleSet I ∧
    generalSmoothExactPenaltySubproblemFirstOrderConditions
      I g c gradConstraint σ x π d

/-- Unfolding `generalSmoothExactPenaltySubproblemKKT` gives the source dual-feasibility,
stationarity, and complementarity conditions. -/
theorem generalSmoothExactPenaltySubproblemKKT_iff
    (I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) (d : Point) :
    generalSmoothExactPenaltySubproblemKKT
        I g c gradConstraint σ x π d ↔
      π ∈ generalSmoothExactPenaltyDualFeasibleSet I ∧
        generalSmoothExactPenaltySubproblemFirstOrderConditions
          I g c gradConstraint σ x π d := Iff.rfl

/-- Helper: for a general equality-and-inequality constrained
problem, `isGeneralSmoothExactPenaltySubproblemMultiplier E I g c gradConstraint σ x π` means
that `π` is a Lagrange multiplier for the linearized subproblem `(10.5.12)`-`(10.5.14)` at the
base point `x`, with `E` and `I` forming the source equality/inequality partition of all
constraint indices. -/
structure isGeneralSmoothExactPenaltySubproblemMultiplier
    (E I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec)
    (hcover : E ∪ I = Set.univ) (hdisj : Disjoint E I) : Prop where
  exists_direction :
    ∃ d : Point,
      d ∈ generalSmoothExactPenaltyFeasibleSet E I c gradConstraint x ∧
        IsMinOn (equalitySmoothExactPenaltySubproblemObjective g σ x)
          (generalSmoothExactPenaltyFeasibleSet E I c gradConstraint x) d ∧
        generalSmoothExactPenaltySubproblemKKT I g c gradConstraint σ x π d

namespace isGeneralSmoothExactPenaltySubproblemMultiplier

/-- Build a general smooth exact penalty multiplier witness from an explicit minimizing direction
and its KKT conditions. -/
def ofDirection
    (E I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec)
    (hcover : E ∪ I = Set.univ) (hdisj : Disjoint E I)
    (d : Point)
    (hdFeasible : d ∈ generalSmoothExactPenaltyFeasibleSet E I c gradConstraint x)
    (hdmin : IsMinOn (equalitySmoothExactPenaltySubproblemObjective g σ x)
      (generalSmoothExactPenaltyFeasibleSet E I c gradConstraint x) d)
    (hkkt : generalSmoothExactPenaltySubproblemKKT I g c gradConstraint σ x π d) :
    isGeneralSmoothExactPenaltySubproblemMultiplier
      E I g c gradConstraint σ x π hcover hdisj :=
  ⟨⟨d, hdFeasible, hdmin, hkkt⟩⟩

end isGeneralSmoothExactPenaltySubproblemMultiplier

/-- Unfolding `isGeneralSmoothExactPenaltySubproblemMultiplier` gives a minimizing direction
together with the source dual-feasibility, stationarity, and complementarity conditions. -/
theorem isGeneralSmoothExactPenaltySubproblemMultiplier_iff
    (E I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ)
    (hcover : E ∪ I = Set.univ) (hdisj : Disjoint E I)
    (x : Point) (π : MultiplierVec) :
    isGeneralSmoothExactPenaltySubproblemMultiplier
        E I g c gradConstraint σ x π hcover hdisj ↔
      ∃ d : Point,
        d ∈ generalSmoothExactPenaltyFeasibleSet E I c gradConstraint x ∧
          IsMinOn (equalitySmoothExactPenaltySubproblemObjective g σ x)
            (generalSmoothExactPenaltyFeasibleSet E I c gradConstraint x) d ∧
          generalSmoothExactPenaltySubproblemKKT I g c gradConstraint σ x π d := by
  constructor
  · intro h
    exact h.exists_direction
  · rintro ⟨d, hdFeasible, hdmin, hkkt⟩
    exact ⟨⟨d, hdFeasible, hdmin, hkkt⟩⟩

/-- For a matrix field `A`, the general stationarity equation specialized to the column family
`i ↦ A(·)_{· i}` recovers the equality-constrained matrix equation `g(x) + σ d = A(x) π`. -/
theorem generalSmoothExactPenaltySubproblemStationarity_iff_matrix
    (A : Point → Matrix (Fin n) (Fin m) ℝ)
    (g : Point → Point) (σ : ℝ) (x : Point) (π : MultiplierVec) (d : Point) :
    generalSmoothExactPenaltySubproblemStationarity
        g (matrixColumnFamily A) σ x π d ↔
      g x + σ • d = Matrix.toEuclideanLin (A x) π := by
  constructor <;> intro h <;> ext j
  · have hcoord := congrArg (fun v : Point ↦ v j) h
    simpa [generalSmoothExactPenaltySubproblemStationarity, matrixColumnFamily,
      Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, mul_comm] using hcoord
  · have hcoord := congrArg (fun v : Point ↦ v j) h
    simpa [generalSmoothExactPenaltySubproblemStationarity, matrixColumnFamily,
      Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, mul_comm] using hcoord

namespace equalitySmoothExactPenaltyFeasibleSet

/-- The equality-constrained feasible set is the general feasible set specialized to equality
indices `Set.univ`, no inequality indices, and the column family of the Jacobian matrix `A(x)`. -/
theorem eq_general
    (A : Point → Matrix (Fin n) (Fin m) ℝ) (c : Point → MultiplierVec) (x : Point) :
    equalitySmoothExactPenaltyFeasibleSet A c x =
      generalSmoothExactPenaltyFeasibleSet
        Set.univ (∅ : Set (Fin m)) c (matrixColumnFamily A) x := by
  ext d
  constructor
  · intro hd
    constructor
    · intro i hi
      have hcoord := congrArg (fun v : MultiplierVec ↦ v i) hd
      simpa [equalitySmoothExactPenaltyFeasibleSet, generalSmoothExactPenaltyFeasibleSet,
        matrixColumnFamily, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        Matrix.mulVec,
        dotProduct, add_comm, mul_comm] using hcoord
    · intro i hi
      simp at hi
  · intro hd
    ext i
    have hcoord := hd.1 i (by simp : i ∈ (Set.univ : Set (Fin m)))
    simpa [equalitySmoothExactPenaltyFeasibleSet, generalSmoothExactPenaltyFeasibleSet,
      matrixColumnFamily, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec,
      dotProduct, add_comm, mul_comm] using hcoord

end equalitySmoothExactPenaltyFeasibleSet

/-- The equality-constrained multiplier predicate is the general subproblem multiplier predicate
specialized to equality indices `Set.univ`, no inequality indices, and the column family of
`A(x)`. -/
theorem isEqualitySmoothExactPenaltySubproblemMultiplier_iff_general
    (A : Point → Matrix (Fin n) (Fin m) ℝ) (g : Point → Point) (c : Point → MultiplierVec)
    (σ : ℝ) (x : Point) (π : MultiplierVec) :
    isEqualitySmoothExactPenaltySubproblemMultiplier A g c σ x π ↔
      isGeneralSmoothExactPenaltySubproblemMultiplier
        Set.univ (∅ : Set (Fin m)) g c (matrixColumnFamily A) σ x π (by simp) (by simp) := by
  constructor
  · rintro ⟨d, hdFeasible, hdmin, hstationary⟩
    refine isGeneralSmoothExactPenaltySubproblemMultiplier.ofDirection
      Set.univ (∅ : Set (Fin m)) g c (matrixColumnFamily A) σ x π (by simp) (by simp) d ?_ ?_ ?_
    · simpa [equalitySmoothExactPenaltyFeasibleSet.eq_general
        A c x] using hdFeasible
    · simpa [equalitySmoothExactPenaltyFeasibleSet.eq_general
        A c x] using hdmin
    · refine ⟨?_, ?_⟩
      · simp [generalSmoothExactPenaltyDualFeasibleSet]
      · refine ⟨?_, ?_⟩
        · exact
            (generalSmoothExactPenaltySubproblemStationarity_iff_matrix
              A g σ x π d).2 hstationary
        · simp [generalSmoothExactPenaltySubproblemComplementarity]
  · intro h
    rcases h.exists_direction with ⟨d, hdFeasible, hdmin, hkkt⟩
    refine ⟨d, ?_, ?_, ?_⟩
    · simpa [equalitySmoothExactPenaltyFeasibleSet.eq_general
        A c x] using hdFeasible
    · simpa [equalitySmoothExactPenaltyFeasibleSet.eq_general
        A c x] using hdmin
    · rcases hkkt with ⟨_, hfirst⟩
      rcases hfirst with ⟨hstationary, _⟩
      exact
        (generalSmoothExactPenaltySubproblemStationarity_iff_matrix
          A g σ x π d).1 hstationary

/-- `isGeneralSmoothExactPenaltyMultiplierField E I g c gradConstraint σ π` means that the
selector `π` chooses, for every base point `x`, a multiplier of the linearized subproblem
`(10.5.12)`-`(10.5.14)`, where `E` and `I` cover all constraint indices without overlap. -/
def isGeneralSmoothExactPenaltyMultiplierField
    (E I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ)
    (hcover : E ∪ I = Set.univ) (hdisj : Disjoint E I)
    (π : Point → MultiplierVec) : Prop :=
  ∀ x : Point,
    isGeneralSmoothExactPenaltySubproblemMultiplier
      E I g c gradConstraint σ x (π x) hcover hdisj

/-- Unfolding `isGeneralSmoothExactPenaltyMultiplierField` gives the pointwise requirement that
`π x` be a multiplier of the linearized subproblem at every base point `x`. -/
theorem isGeneralSmoothExactPenaltyMultiplierField_iff
    (E I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ)
    (hcover : E ∪ I = Set.univ) (hdisj : Disjoint E I)
    (π : Point → MultiplierVec) :
    isGeneralSmoothExactPenaltyMultiplierField
        E I g c gradConstraint σ hcover hdisj π ↔
      ∀ x : Point,
        isGeneralSmoothExactPenaltySubproblemMultiplier
          E I g c gradConstraint σ x (π x) hcover hdisj := Iff.rfl

/-- Helper: if `π` is chosen pointwise as a multiplier of the
linearized subproblem `(10.5.12)`-`(10.5.14)`, then the penalty function is
`P(x) = f x - π(x)ᵀ c(x)`, with `E` and `I` the source equality/inequality partition of all
constraint indices. This is the Chapter 10 owner `equalitySmoothExactPenaltyFunction`
specialized to zero diagonal penalty. -/
def generalSmoothExactPenaltyFunction
    (f : Point → ℝ)
    (E I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ)
    (hcover : E ∪ I = Set.univ) (hdisj : Disjoint E I)
    (π : Point → MultiplierVec)
    (hπ : isGeneralSmoothExactPenaltyMultiplierField E I g c gradConstraint σ hcover hdisj π)
    (x : Point) : ℝ :=
  let _ := hπ
  equalitySmoothExactPenaltyFunction f π c (constantConstraintPoint 0) x

/-- Evaluating `generalSmoothExactPenaltyFunction` gives the source formula
`P(x) = f x - π(x)ᵀ c(x)` from Definition 10.5-extra-2 (6). -/
theorem generalSmoothExactPenaltyFunction_apply
    (f : Point → ℝ)
    (E I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ)
    (hcover : E ∪ I = Set.univ) (hdisj : Disjoint E I)
    (π : Point → MultiplierVec)
    (hπ : isGeneralSmoothExactPenaltyMultiplierField E I g c gradConstraint σ hcover hdisj π)
    (x : Point) :
    generalSmoothExactPenaltyFunction f E I g c gradConstraint σ hcover hdisj π hπ x =
      f x - dotProduct (π x) (c x) := by
  simp [generalSmoothExactPenaltyFunction, equalitySmoothExactPenaltyFunction,
    constantConstraintPoint_def]

/-- Helper: specializing `equalitySmoothExactPenaltyFunction` to zero diagonal penalty gives the
formula `P(x) = f x - π(x)ᵀ c(x)` for an arbitrary selector `π`. -/
theorem equalitySmoothExactPenaltyFunction_zeroDiagonal_apply
    (f : Point → ℝ)
    (c : Point → MultiplierVec)
    (π : Point → MultiplierVec)
    (x : Point) :
    equalitySmoothExactPenaltyFunction f π c (constantConstraintPoint 0) x =
      f x - dotProduct (π x) (c x) := by
  simp [equalitySmoothExactPenaltyFunction, constantConstraintPoint_def]

/-- Helper: the dual objective associated to the linearized
subproblem `(10.5.12)`-`(10.5.14)` is
`π ↦ (1 / 2) * ‖g(x) - ∑ i, π_i • ∇ c_i(x)‖² + σ * πᵀ c(x)`. -/
def generalSmoothExactPenaltyDualObjective
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) : ℝ :=
  (1 / 2 : ℝ) * ‖g x - ∑ i : Fin m, π i • gradConstraint i x‖ ^ (2 : ℕ) +
    σ * dotProduct π (c x)

/-- Evaluating `generalSmoothExactPenaltyDualObjective g c gradConstraint σ x` gives the source
dual objective from `(10.5.16)`. -/
theorem generalSmoothExactPenaltyDualObjective_apply
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) :
    generalSmoothExactPenaltyDualObjective g c gradConstraint σ x π =
      (1 / 2 : ℝ) * ‖g x - ∑ i : Fin m, π i • gradConstraint i x‖ ^ (2 : ℕ) +
        σ * dotProduct π (c x) := rfl

/-- `isGeneralSmoothExactPenaltyDualSolution I g c gradConstraint σ x π` says that `π` solves
the dual minimization problem `(10.5.16)` with the source nonnegativity constraints on the
inequality index set `I`. -/
def isGeneralSmoothExactPenaltyDualSolution
    (I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) : Prop :=
  IsMinOn
    (generalSmoothExactPenaltyDualObjective g c gradConstraint σ x)
    (generalSmoothExactPenaltyDualFeasibleSet I)
    π

/-- Unfolding `isGeneralSmoothExactPenaltyDualSolution` gives the source dual minimization
problem `(10.5.16)` together with the nonnegativity constraints on `I`. -/
theorem isGeneralSmoothExactPenaltyDualSolution_iff
    (I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) :
    isGeneralSmoothExactPenaltyDualSolution
        I g c gradConstraint σ x π ↔
      IsMinOn
        (generalSmoothExactPenaltyDualObjective g c gradConstraint σ x)
        (generalSmoothExactPenaltyDualFeasibleSet I)
        π := Iff.rfl

/-- Helper for Chapter10 Definition 10.5-extra-2: the dual residual at `μ` is the dual residual
at `π` minus the gradient combination weighted by `μ - π`. -/
theorem generalSmoothExactPenaltyDualResidual_eq_sub
    (g : Point → Point)
    (gradConstraint : Fin m → Point → Point)
    (x : Point) (π μ : MultiplierVec) :
    g x - ∑ i : Fin m, μ i • gradConstraint i x =
      (g x - ∑ i : Fin m, π i • gradConstraint i x) -
        ∑ i : Fin m, (μ i - π i) • gradConstraint i x := by
  -- Reexpress the `μ`-residual through the `π`-residual and the multiplier difference.
  calc
    g x - ∑ i : Fin m, μ i • gradConstraint i x
        = g x -
            ((∑ i : Fin m, π i • gradConstraint i x) +
              ∑ i : Fin m, (μ i - π i) • gradConstraint i x) := by
              congr 1
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [sub_eq_add_neg, add_smul, add_comm]
    _ = (g x - ∑ i : Fin m, π i • gradConstraint i x) -
          ∑ i : Fin m, (μ i - π i) • gradConstraint i x := by
            simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Helper for Chapter10 Definition 10.5-extra-2: under the subproblem stationarity equation,
the dual objective gap from `π` to `μ` splits into a squared norm plus a residual-weighted sum. -/
theorem generalSmoothExactPenaltyDualObjective_gap_eq
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π μ : MultiplierVec) (d : Point)
    (hstationary : generalSmoothExactPenaltySubproblemStationarity
      g gradConstraint σ x π d) :
    generalSmoothExactPenaltyDualObjective g c gradConstraint σ x μ -
      generalSmoothExactPenaltyDualObjective g c gradConstraint σ x π =
      (1 / 2 : ℝ) * ‖∑ i : Fin m, (μ i - π i) • gradConstraint i x‖ ^ (2 : ℕ) +
        σ * ∑ i : Fin m, (μ i - π i) * (c x i + dotProduct d (gradConstraint i x)) := by
  let residualPi : Point := g x - ∑ i : Fin m, π i • gradConstraint i x
  let residualDiff : Point := ∑ i : Fin m, (μ i - π i) • gradConstraint i x
  have hstationaryEq :
      g x + σ • d = ∑ i : Fin m, π i • gradConstraint i x :=
    (generalSmoothExactPenaltySubproblemStationarity_iff g gradConstraint σ x π d).1 hstationary
  have hresMu :
      g x - ∑ i : Fin m, μ i • gradConstraint i x = residualPi - residualDiff := by
    simpa [residualPi, residualDiff] using
      generalSmoothExactPenaltyDualResidual_eq_sub g gradConstraint x π μ
  have hresMuSub :
      (g x - ∑ i : Fin m, μ i • gradConstraint i x) - residualPi = -residualDiff := by
    rw [hresMu]
    simp [sub_eq_add_neg, residualDiff, add_assoc]
  have hresPi : residualPi = -σ • d := by
    -- Stationarity turns the `π`-residual into the negative quadratic-gradient term `-σ d`.
    calc
      residualPi = g x - ∑ i : Fin m, π i • gradConstraint i x := by rfl
      _ = g x - (g x + σ • d) := by rw [hstationaryEq]
      _ = -σ • d := by simp
  have hdotResidualDiff :
      dotProduct d residualDiff =
        ∑ i : Fin m, (μ i - π i) * dotProduct d (gradConstraint i x) := by
    -- Expand the dot product against the multiplier-difference gradient sum one term at a time.
    calc
      dotProduct d residualDiff
          = dotProduct d (∑ i ∈ Finset.univ, (μ i - π i) • gradConstraint i x) := by
              simp [residualDiff]
      _ = ∑ i ∈ Finset.univ, dotProduct d ((μ i - π i) • gradConstraint i x) := by
            rw [dotProduct_sum]
      _ = ∑ i ∈ Finset.univ, (μ i - π i) * dotProduct d (gradConstraint i x) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [dotProduct_smul]
            rfl
      _ = ∑ i : Fin m, (μ i - π i) * dotProduct d (gradConstraint i x) := by simp
  have hbilinearFirst :
      dotProduct residualPi ((g x - ∑ i : Fin m, μ i • gradConstraint i x) - residualPi) =
        dotProduct residualPi (-residualDiff) := by
    simpa using congrArg (fun w : Point => dotProduct residualPi w) hresMuSub
  have hbilinear :
      dotProduct residualPi ((g x - ∑ i : Fin m, μ i • gradConstraint i x) - residualPi) =
        σ * ∑ i : Fin m, (μ i - π i) * dotProduct d (gradConstraint i x) := by
    -- Replace the `π`-residual by `-σ d` and push the dot product through the finite sum.
    calc
      dotProduct residualPi ((g x - ∑ i : Fin m, μ i • gradConstraint i x) - residualPi)
          = dotProduct residualPi (-residualDiff) := hbilinearFirst
      _ = dotProduct (-σ • d) (-residualDiff) := by rw [hresPi]
      _ = dotProduct (σ • d) residualDiff := by simp
      _ = σ * dotProduct d residualDiff := by
            simpa [smul_eq_mul] using (smul_dotProduct σ d residualDiff)
      _ = σ * ∑ i : Fin m, (μ i - π i) * dotProduct d (gradConstraint i x) := by
            rw [hdotResidualDiff]
  have hlinearBase :
      dotProduct μ (c x) - dotProduct π (c x) =
        ∑ i : Fin m, (μ i - π i) * c x i := by
    -- The linear part of the dual objective is already the multiplier-difference pairing
    -- with `c x`.
    calc
      dotProduct μ (c x) - dotProduct π (c x)
          = dotProduct (μ - π) (c x) := by
              simpa using (sub_dotProduct μ π (c x)).symm
      _ = ∑ i : Fin m, (μ i - π i) * c x i := by
            simp [dotProduct]
  have hlinear :
      σ * (dotProduct μ (c x) - dotProduct π (c x)) =
        σ * ∑ i : Fin m, (μ i - π i) * c x i := by
    rw [hlinearBase]
  have hsumCombine :
      σ * ∑ i : Fin m, (μ i - π i) * dotProduct d (gradConstraint i x) +
          σ * ∑ i : Fin m, (μ i - π i) * c x i =
        σ * ∑ i : Fin m, (μ i - π i) * (c x i + dotProduct d (gradConstraint i x)) := by
    -- Merge the two weighted sums before restoring the final residual form.
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine congrArg (fun t : ℝ => σ * t) ?_
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  -- Apply the shared quadratic-gap lemma to the two residual vectors and then rewrite the
  -- bilinear and linear terms into the source residual-weighted sum.
  calc
    generalSmoothExactPenaltyDualObjective g c gradConstraint σ x μ -
        generalSmoothExactPenaltyDualObjective g c gradConstraint σ x π
      = ((1 / 2 : ℝ) * ‖g x - ∑ i : Fin m, μ i • gradConstraint i x‖ ^ (2 : ℕ) -
            (1 / 2 : ℝ) * ‖g x - ∑ i : Fin m, π i • gradConstraint i x‖ ^ (2 : ℕ)) +
          σ * (dotProduct μ (c x) - dotProduct π (c x)) := by
            rw [generalSmoothExactPenaltyDualObjective_apply,
              generalSmoothExactPenaltyDualObjective_apply]
            ring
    _ = dotProduct residualPi ((g x - ∑ i : Fin m, μ i • gradConstraint i x) - residualPi) +
          (1 / 2 : ℝ) * ‖(g x - ∑ i : Fin m, μ i • gradConstraint i x) - residualPi‖ ^ (2 : ℕ) +
          σ * (dotProduct μ (c x) - dotProduct π (c x)) := by
            simpa [residualPi] using
              (halfNormSq_gap_eq (g x - ∑ i : Fin m, μ i • gradConstraint i x) residualPi)
    _ = σ * ∑ i : Fin m, (μ i - π i) * dotProduct d (gradConstraint i x) +
          (1 / 2 : ℝ) * ‖residualDiff‖ ^ (2 : ℕ) +
          σ * ∑ i : Fin m, (μ i - π i) * c x i := by
            rw [hbilinear, hlinear, hresMuSub]
            simp [norm_neg]
    _ = (1 / 2 : ℝ) * ‖residualDiff‖ ^ (2 : ℕ) +
          (σ * ∑ i : Fin m, (μ i - π i) * dotProduct d (gradConstraint i x) +
            σ * ∑ i : Fin m, (μ i - π i) * c x i) := by
            ring
    _ = (1 / 2 : ℝ) * ‖residualDiff‖ ^ (2 : ℕ) +
          σ * ∑ i : Fin m, (μ i - π i) * (c x i + dotProduct d (gradConstraint i x)) := by
            rw [hsumCombine]
    _ = (1 / 2 : ℝ) * ‖∑ i : Fin m, (μ i - π i) • gradConstraint i x‖ ^ (2 : ℕ) +
          σ * ∑ i : Fin m, (μ i - π i) * (c x i + dotProduct d (gradConstraint i x)) := by
            rfl

/-- Helper for Chapter10 Definition 10.5-extra-2: feasibility and complementarity force the
residual-weighted sum in the dual gap identity to be nonnegative. -/
theorem generalResidualWeightedSum_nonneg
    (E I : Set (Fin m))
    (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (x : Point) (π μ : MultiplierVec) (d : Point)
    (hcover : E ∪ I = Set.univ)
    (hdFeasible : d ∈ generalSmoothExactPenaltyFeasibleSet E I c gradConstraint x)
    (hμ : μ ∈ generalSmoothExactPenaltyDualFeasibleSet I)
    (hcomp : generalSmoothExactPenaltySubproblemComplementarity I c gradConstraint x π d) :
    0 ≤ ∑ i : Fin m, (μ i - π i) * (c x i + dotProduct d (gradConstraint i x)) := by
  have hdEqIneq :=
    (mem_generalSmoothExactPenaltyFeasibleSet_iff E I c gradConstraint x d).1 hdFeasible
  have hμNonneg := (mem_generalSmoothExactPenaltyDualFeasibleSet_iff I μ).1 hμ
  have hcompEq := (generalSmoothExactPenaltySubproblemComplementarity_iff
    I c gradConstraint x π d).1 hcomp
  refine Finset.sum_nonneg ?_
  intro i hi
  have hcoveri : i ∈ E ∨ i ∈ I := by
    have hmem : i ∈ E ∪ I := by
      rw [hcover]
      simp
    rw [Set.mem_union] at hmem
    exact hmem
  rcases hcoveri with hEi | hIi
  · -- Equality-index residuals vanish by primal feasibility.
    have hresEq : c x i + dotProduct d (gradConstraint i x) = 0 := hdEqIneq.1 i hEi
    simp [hresEq]
  · -- Inequality-index residuals survive with coefficient `μ i`, since complementarity kills
    -- the `π i` contribution and dual feasibility supplies `μ i ≥ 0`.
    have hresNonneg : 0 ≤ c x i + dotProduct d (gradConstraint i x) := hdEqIneq.2 i hIi
    have hterm :
        (μ i - π i) * (c x i + dotProduct d (gradConstraint i x)) =
          μ i * (c x i + dotProduct d (gradConstraint i x)) := by
      calc
        (μ i - π i) * (c x i + dotProduct d (gradConstraint i x))
            = μ i * (c x i + dotProduct d (gradConstraint i x)) -
                π i * (c x i + dotProduct d (gradConstraint i x)) := by
                  ring
        _ = μ i * (c x i + dotProduct d (gradConstraint i x)) := by
              rw [hcompEq i hIi]
              ring
    rw [hterm]
    exact mul_nonneg (hμNonneg i hIi) hresNonneg

/-- Mixed-constraint bridge theorem: if `gradConstraint i x` is the actual gradient
`∇ c_i(x)` and `π` is the multiplier of the linearized subproblem `(10.5.12)`-`(10.5.14)`, then
`π` can also be obtained as a solution of the dual problem `(10.5.16)` for a positive penalty
parameter `σ`, provided the equality and inequality index sets cover all constraint indices. -/
theorem generalSmoothExactPenaltyMultiplier_isDualSolution
    (E I : Set (Fin m))
    (g : Point → Point) (c : Point → MultiplierVec)
    (gradConstraint : Fin m → Point → Point)
    (σ : ℝ)
    (x : Point) (π : MultiplierVec)
    (hσ : 0 < σ)
    (hcover : E ∪ I = Set.univ)
    (hdisj : Disjoint E I)
    (hgrad : HasFDerivAt c
      ((Matrix.toEuclideanLin
        ((constraintGradientMatrix gradConstraint x).transpose)).toContinuousLinearMap)
      x)
    (hπ : isGeneralSmoothExactPenaltySubproblemMultiplier
      E I g c gradConstraint σ x π hcover hdisj) :
    isGeneralSmoothExactPenaltyDualSolution
      I g c gradConstraint σ x π := by
  let _ := hgrad
  rcases hπ.exists_direction with ⟨d, hdFeasible, _, hkkt⟩
  rcases (generalSmoothExactPenaltySubproblemKKT_iff I g c gradConstraint σ x π d).1 hkkt with
    ⟨hπFeasible, hfirst⟩
  rcases
      (generalSmoothExactPenaltySubproblemFirstOrderConditions_iff
        I g c gradConstraint σ x π d).1 hfirst with
    ⟨hstationary, hcomp⟩
  rw [isGeneralSmoothExactPenaltyDualSolution_iff, isMinOn_iff]
  intro μ hμ
  have hgap :
      generalSmoothExactPenaltyDualObjective g c gradConstraint σ x μ -
        generalSmoothExactPenaltyDualObjective g c gradConstraint σ x π =
        (1 / 2 : ℝ) * ‖∑ i : Fin m, (μ i - π i) • gradConstraint i x‖ ^ (2 : ℕ) +
          σ * ∑ i : Fin m, (μ i - π i) * (c x i + dotProduct d (gradConstraint i x)) :=
    generalSmoothExactPenaltyDualObjective_gap_eq
      g c gradConstraint σ x π μ d hstationary
  have hnorm_nonneg :
      0 ≤ ‖∑ i : Fin m, (μ i - π i) • gradConstraint i x‖ ^ (2 : ℕ) := by
    simpa [pow_two] using
      sq_nonneg ‖∑ i : Fin m, (μ i - π i) • gradConstraint i x‖
  have hsq_nonneg :
      0 ≤ (1 / 2 : ℝ) * ‖∑ i : Fin m, (μ i - π i) • gradConstraint i x‖ ^ (2 : ℕ) := by
    exact mul_nonneg (by norm_num) hnorm_nonneg
  have hresidual_nonneg :
      0 ≤ ∑ i : Fin m, (μ i - π i) * (c x i + dotProduct d (gradConstraint i x)) :=
    generalResidualWeightedSum_nonneg E I c gradConstraint x π μ d hcover hdFeasible hμ hcomp
  have hweighted_nonneg :
      0 ≤ σ * ∑ i : Fin m, (μ i - π i) * (c x i + dotProduct d (gradConstraint i x)) := by
    exact mul_nonneg hσ.le hresidual_nonneg
  have hdiff_nonneg :
      0 ≤ generalSmoothExactPenaltyDualObjective g c gradConstraint σ x μ -
        generalSmoothExactPenaltyDualObjective g c gradConstraint σ x π := by
    rw [hgap]
    exact add_nonneg hsq_nonneg hweighted_nonneg
  linarith

namespace StandardPenaltyProblem

/-- The linearized subproblem multiplier predicate from `(10.5.12)`-`(10.5.14)`, transported to
the canonical mixed-constraint owner `StandardPenaltyProblem` through its contiguous equality and
inequality blocks `problem.eqIndices` and `problem.ineqIndices`. -/
def IsSmoothExactPenaltySubproblemMultiplier
    (problem : StandardPenaltyProblem n m)
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) : Prop :=
  isGeneralSmoothExactPenaltySubproblemMultiplier
    problem.eqIndices problem.ineqIndices g problem.constraintMap gradConstraint σ x π
    problem.eqIndices_union_ineqIndices problem.eqIndices_disjoint_ineqIndices

/-- Unfolding `problem.IsSmoothExactPenaltySubproblemMultiplier g gradConstraint σ x π` recovers
the mixed-constraint multiplier predicate over `problem.eqIndices` and `problem.ineqIndices`. -/
theorem isSmoothExactPenaltySubproblemMultiplier_iff
    (problem : StandardPenaltyProblem n m)
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) :
    problem.IsSmoothExactPenaltySubproblemMultiplier g gradConstraint σ x π ↔
      isGeneralSmoothExactPenaltySubproblemMultiplier
        problem.eqIndices problem.ineqIndices g problem.constraintMap gradConstraint σ x π
        problem.eqIndices_union_ineqIndices problem.eqIndices_disjoint_ineqIndices := Iff.rfl

/-- A selector `π` is a smooth exact penalty multiplier field for `problem` when each `π x`
solves the linearized mixed-constraint subproblem at `x` relative to the canonical equality and
inequality split of `problem`. -/
def IsSmoothExactPenaltyMultiplierField
    (problem : StandardPenaltyProblem n m)
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (π : Point → MultiplierVec) : Prop :=
  ∀ x : Point, problem.IsSmoothExactPenaltySubproblemMultiplier g gradConstraint σ x (π x)

/-- Unfolding `problem.IsSmoothExactPenaltyMultiplierField g gradConstraint σ π` gives the
pointwise mixed-constraint multiplier requirement. -/
theorem isSmoothExactPenaltyMultiplierField_iff
    (problem : StandardPenaltyProblem n m)
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (π : Point → MultiplierVec) :
    problem.IsSmoothExactPenaltyMultiplierField g gradConstraint σ π ↔
      ∀ x : Point, problem.IsSmoothExactPenaltySubproblemMultiplier g gradConstraint σ x (π x) :=
  Iff.rfl

/-- Chapter10 Definition 10.5-extra-2: for a mixed equality-and-inequality constrained
`StandardPenaltyProblem`, if `π` is chosen pointwise as a multiplier of the linearized
subproblem `(10.5.12)`-`(10.5.14)` relative to the canonical split
`problem.eqIndices` / `problem.ineqIndices`, then the smooth exact penalty function is
`P(x) = f(x) - π(x)ᵀ c(x)`. The equality-case formulas and the dual formulation `(10.5.16)`
remain available as companion helpers and bridge theorems in this file. -/
def smoothExactPenaltyFunction
    (problem : StandardPenaltyProblem n m)
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (π : Point → MultiplierVec)
    (hπ : problem.IsSmoothExactPenaltyMultiplierField g gradConstraint σ π)
    (x : Point) : ℝ :=
  generalSmoothExactPenaltyFunction
    problem.objective problem.eqIndices problem.ineqIndices g problem.constraintMap
    gradConstraint σ problem.eqIndices_union_ineqIndices
    problem.eqIndices_disjoint_ineqIndices π hπ x

/-- Evaluating `problem.smoothExactPenaltyFunction g gradConstraint σ π hπ x` gives the source
formula `P(x) = f(x) - π(x)ᵀ c(x)` written through `problem.constraintMap x`. -/
theorem smoothExactPenaltyFunction_apply
    (problem : StandardPenaltyProblem n m)
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (π : Point → MultiplierVec)
    (hπ : problem.IsSmoothExactPenaltyMultiplierField g gradConstraint σ π)
    (x : Point) :
    problem.smoothExactPenaltyFunction g gradConstraint σ π hπ x =
      problem.objective x - dotProduct (π x) (problem.constraintMap x) := by
  simpa [smoothExactPenaltyFunction] using
    generalSmoothExactPenaltyFunction_apply
      problem.objective problem.eqIndices problem.ineqIndices g problem.constraintMap
      gradConstraint σ problem.eqIndices_union_ineqIndices
      problem.eqIndices_disjoint_ineqIndices π hπ x

/-- The dual objective from `(10.5.16)`, transported to `StandardPenaltyProblem` via
`problem.constraintMap` and `problem.ineqIndices`. -/
def smoothExactPenaltyDualObjective
    (problem : StandardPenaltyProblem n m)
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) : ℝ :=
  generalSmoothExactPenaltyDualObjective g problem.constraintMap gradConstraint σ x π

/-- Evaluating `problem.smoothExactPenaltyDualObjective g gradConstraint σ x π` gives the source
dual objective written through the canonical mixed-constraint owner. -/
theorem smoothExactPenaltyDualObjective_apply
    (problem : StandardPenaltyProblem n m)
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) :
    problem.smoothExactPenaltyDualObjective g gradConstraint σ x π =
      (1 / 2 : ℝ) * ‖g x - ∑ i : Fin m, π i • gradConstraint i x‖ ^ (2 : ℕ) +
        σ * dotProduct π (problem.constraintMap x) := rfl

/-- `problem.IsSmoothExactPenaltyDualSolution g gradConstraint σ x π` says that `π` solves the
dual problem `(10.5.16)` subject only to the nonnegativity conditions on the inequality block
`problem.ineqIndices`. -/
def IsSmoothExactPenaltyDualSolution
    (problem : StandardPenaltyProblem n m)
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) : Prop :=
  isGeneralSmoothExactPenaltyDualSolution
    problem.ineqIndices g problem.constraintMap gradConstraint σ x π

/-- Unfolding `problem.IsSmoothExactPenaltyDualSolution g gradConstraint σ x π` recovers the
dual minimization problem over `problem.ineqIndices`. -/
theorem isSmoothExactPenaltyDualSolution_iff
    (problem : StandardPenaltyProblem n m)
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ) (x : Point) (π : MultiplierVec) :
    problem.IsSmoothExactPenaltyDualSolution g gradConstraint σ x π ↔
      isGeneralSmoothExactPenaltyDualSolution
        problem.ineqIndices g problem.constraintMap gradConstraint σ x π := Iff.rfl

/-- If `gradConstraint i x` is the actual gradient `∇ c_i(x)` and `π` is a multiplier of the
linearized mixed-constraint subproblem for `problem`, then `π` also solves the corresponding
dual problem `(10.5.16)` over the inequality block `problem.ineqIndices`. -/
theorem smoothExactPenaltyMultiplier_isDualSolution
    (problem : StandardPenaltyProblem n m)
    (g : Point → Point) (gradConstraint : Fin m → Point → Point)
    (σ : ℝ)
    (x : Point) (π : MultiplierVec)
    (hσ : 0 < σ)
    (hgrad : HasFDerivAt problem.constraintMap
      ((Matrix.toEuclideanLin
        ((constraintGradientMatrix gradConstraint x).transpose)).toContinuousLinearMap)
      x)
    (hπ : problem.IsSmoothExactPenaltySubproblemMultiplier g gradConstraint σ x π) :
    problem.IsSmoothExactPenaltyDualSolution g gradConstraint σ x π := by
  simpa [IsSmoothExactPenaltySubproblemMultiplier, IsSmoothExactPenaltyDualSolution] using
    generalSmoothExactPenaltyMultiplier_isDualSolution
      problem.eqIndices problem.ineqIndices g problem.constraintMap gradConstraint σ x π hσ
      problem.eqIndices_union_ineqIndices problem.eqIndices_disjoint_ineqIndices
      hgrad hπ

end StandardPenaltyProblem

#print axioms equalitySmoothExactPenaltyCorrection
#print axioms equalitySmoothExactPenaltyMultiplier
#print axioms equalitySmoothExactPenaltyFunction
#print axioms generalSmoothExactPenaltyFunction
#print axioms generalSmoothExactPenaltyFeasibleSet
#print axioms generalSmoothExactPenaltyDualFeasibleSet
#print axioms generalSmoothExactPenaltyDualObjective
