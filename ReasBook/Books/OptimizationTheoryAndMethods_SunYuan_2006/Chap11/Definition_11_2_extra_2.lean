/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Extr

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "BasicPoint" => EuclideanSpace ℝ (Fin m)
local notation "NonbasicPoint" => EuclideanSpace ℝ (Fin (n - m))
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

/-- The standard Euclidean basis on the ambient point space. -/
abbrev pointBasis :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- The standard Euclidean basis on the basic-variable space. -/
abbrev basicBasis :=
  (EuclideanSpace.basisFun (Fin m) ℝ).toBasis

/-- Unfolding formula for `basicBasis`. -/
theorem basicBasis_eq :
    basicBasis = (EuclideanSpace.basisFun (Fin m) ℝ).toBasis :=
  rfl

/-- The standard Euclidean basis on the constraint space. -/
abbrev constraintBasis :=
  (EuclideanSpace.basisFun (Fin m) ℝ).toBasis

/-- The standard Euclidean basis on the nonbasic-variable space. -/
abbrev nonbasicBasis :=
  (EuclideanSpace.basisFun (Fin (n - m)) ℝ).toBasis

/-- Unfolding formula for `nonbasicBasis`. -/
theorem nonbasicBasis_eq :
    nonbasicBasis = (EuclideanSpace.basisFun (Fin (n - m)) ℝ).toBasis :=
  rfl

-- Semantic recall: `lean_leansearch` surfaced `Matrix.submatrix`, `gradient`, and
-- `LinearMap.toMatrix` as the canonical ingredients. This file therefore records the source
-- setup through one nonsingular matrix `S`, with `S_B` and `S_N` derived as its basic and
-- nonbasic column blocks.

/-- The block-matrix geometry `x = S_B w_B + S_N w_N` underlying generalized elimination. -/
structure GeneralizedEliminationGeometry where
  m_le_n : m ≤ n
  S : Matrix (Fin n) (Fin n) ℝ
  hS : IsUnit S

local notation "Geometry" => @_root_.GeneralizedEliminationGeometry n m

namespace GeneralizedEliminationGeometry

/-- The basic block `S_B` is the first `m` columns of the source matrix `S`. -/
def basicBlock (G : Geometry) :
    Matrix (Fin n) (Fin m) ℝ :=
  G.S.submatrix id (fun i : Fin m ↦ ⟨i.1, lt_of_lt_of_le i.2 G.m_le_n⟩)

/-- Unfolding formula for `basicBlock`. -/
theorem basicBlock_eq (G : Geometry) :
    G.basicBlock = G.S.submatrix id (fun i : Fin m ↦ ⟨i.1, lt_of_lt_of_le i.2 G.m_le_n⟩) :=
  rfl

/-- The nonbasic block `S_N` is the remaining `n - m` columns of the source matrix `S`. -/
def nonbasicBlock (G : Geometry) :
    Matrix (Fin n) (Fin (n - m)) ℝ :=
  G.S.submatrix id
    (fun i : Fin (n - m) ↦
      ⟨m + i.1, by
        simpa [Nat.add_sub_of_le G.m_le_n] using Nat.add_lt_add_left i.2 m⟩)

/-- Unfolding formula for `nonbasicBlock`. -/
theorem nonbasicBlock_eq (G : Geometry) :
    G.nonbasicBlock =
      G.S.submatrix id
        (fun i : Fin (n - m) ↦
          ⟨m + i.1, by
            simpa [Nat.add_sub_of_le G.m_le_n] using Nat.add_lt_add_left i.2 m⟩) :=
  rfl

/-- The transformed point `x = S_B w_B + S_N w_N` determined by the elimination geometry. -/
def point (G : Geometry)
    (wB : BasicPoint) (wN : NonbasicPoint) : Point :=
  Matrix.toEuclideanLin G.basicBlock wB + Matrix.toEuclideanLin G.nonbasicBlock wN

/-- Unfolding formula for `point`. -/
theorem point_eq (G : Geometry)
    (wB : BasicPoint) (wN : NonbasicPoint) :
    G.point wB wN =
      Matrix.toEuclideanLin G.basicBlock wB + Matrix.toEuclideanLin G.nonbasicBlock wN :=
  rfl

end GeneralizedEliminationGeometry

/-- The generalized elimination method attached to `Chapter11 Definition 11.2-extra-2` is
determined by a
nonsingular matrix `S : ℝ^(n × n)`, a split `w = [w_B; w_N]` with `w_B ∈ ℝ^m` and
`w_N ∈ ℝ^(n - m)`, and an elimination map `phiBar` satisfying the transformed constraint
equation `c (S_B w_B + S_N w_N) = 0` exactly through `w_B = phiBar w_N`. -/
structure GeneralizedEliminationMethod extends Geometry where
  constraint : Point → ConstraintPoint
  phiBar : NonbasicPoint → BasicPoint
  eliminationEq (wB : BasicPoint) (wN : NonbasicPoint) :
    constraint (toGeneralizedEliminationGeometry.point wB wN) =
      0 ↔
    wB = phiBar wN

local notation "Elimination" => @_root_.GeneralizedEliminationMethod n m

namespace GeneralizedEliminationMethod

/-- A generalized elimination method coerces to its eliminated basic-variable map `phiBar`. -/
instance : CoeFun Elimination
    (fun _ ↦ NonbasicPoint → BasicPoint) where
  coe M := M.phiBar

/-- The basic block `S_B` is the first `m` columns of the source matrix `S`. -/
def basicBlock (M : Elimination) :
    Matrix (Fin n) (Fin m) ℝ :=
  M.toGeneralizedEliminationGeometry.basicBlock

/-- Unfolding formula for `basicBlock`. -/
theorem basicBlock_eq (M : Elimination) :
    M.basicBlock = M.S.submatrix id (fun i : Fin m ↦ ⟨i.1, lt_of_lt_of_le i.2 M.m_le_n⟩) :=
  M.toGeneralizedEliminationGeometry.basicBlock_eq

/-- The nonbasic block `S_N` is the remaining `n - m` columns of the source matrix `S`. -/
def nonbasicBlock (M : Elimination) :
    Matrix (Fin n) (Fin (n - m)) ℝ :=
  M.toGeneralizedEliminationGeometry.nonbasicBlock

/-- Unfolding formula for `nonbasicBlock`. -/
theorem nonbasicBlock_eq (M : Elimination) :
    M.nonbasicBlock =
      M.S.submatrix id
        (fun i : Fin (n - m) ↦
          ⟨m + i.1, by
            simpa [Nat.add_sub_of_le M.m_le_n] using Nat.add_lt_add_left i.2 m⟩) :=
  M.toGeneralizedEliminationGeometry.nonbasicBlock_eq

/-- The transformed point `x = S_B w_B + S_N w_N` used in generalized elimination. -/
def point (M : Elimination)
    (wB : BasicPoint) (wN : NonbasicPoint) : Point :=
  M.toGeneralizedEliminationGeometry.point wB wN

/-- Unfolding formula for `point`. -/
theorem point_eq (M : Elimination)
    (wB : BasicPoint) (wN : NonbasicPoint) :
    M.point wB wN =
      Matrix.toEuclideanLin M.basicBlock wB + Matrix.toEuclideanLin M.nonbasicBlock wN :=
  M.toGeneralizedEliminationGeometry.point_eq wB wN

/-- The point on the elimination graph over `w_N`, namely `S_B (phiBar w_N) + S_N w_N`. -/
def graphPoint (M : Elimination) (wN : NonbasicPoint) : Point :=
  M.point (M wN) wN

/-- Unfolding formula for `graphPoint`. -/
theorem graphPoint_eq (M : Elimination) (wN : NonbasicPoint) :
    M.graphPoint wN = M.point (M wN) wN :=
  rfl

/-- The Jacobian matrix of the constraint map `c : x ↦ c(x)` at `x`, written in the Euclidean
bases so that its transpose models the source term `∇ c(x)ᵀ`. -/
abbrev generalizedEliminationConstraintJacobian
    (c : Point → ConstraintPoint) (x : Point) : Matrix (Fin m) (Fin n) ℝ :=
  LinearMap.toMatrix pointBasis constraintBasis (fderiv ℝ c x).toLinearMap

/-- Unfolding formula for `generalizedEliminationConstraintJacobian`. -/
theorem generalizedEliminationConstraintJacobian_eq
    (c : Point → ConstraintPoint) (x : Point) :
    generalizedEliminationConstraintJacobian c x =
      LinearMap.toMatrix pointBasis constraintBasis (fderiv ℝ c x).toLinearMap :=
  rfl

/-- The reduced objective `bar f(w_N) = f (S_B (phiBar w_N) + S_N w_N)`. -/
def reducedObjective (M : Elimination)
    (f : Point → ℝ) (wN : NonbasicPoint) : ℝ :=
  f (M.graphPoint wN)

/-- Unfolding formula for `reducedObjective`. -/
theorem reducedObjective_eq (M : Elimination)
    (f : Point → ℝ) (wN : NonbasicPoint) :
    M.reducedObjective f wN = f (M.graphPoint wN) :=
  rfl

/-- The transformed constraint equation is solved exactly by the eliminated basic variable
`w_B = phiBar w_N`. -/
theorem constraint_eq_zero_iff_eq_phiBar
    (M : Elimination)
    (wB : BasicPoint) (wN : NonbasicPoint) :
    M.constraint (M.point wB wN) = 0 ↔ wB = M wN :=
  M.eliminationEq wB wN

/-- The elimination map `phiBar` satisfies the transformed constraint equation `c (S_B w_B +
S_N w_N) = 0` at the eliminated basic point `w_B = phiBar w_N`. -/
theorem constraint_eq_zero (M : Elimination)
    (wN : NonbasicPoint) :
    M.constraint (M.graphPoint wN) = 0 := by
  exact (M.constraint_eq_zero_iff_eq_phiBar (M wN) wN).2 rfl

/-- The transformed feasible set consists of the points `x = S_B w_B + S_N w_N` satisfying the
source constraint equation `c x = 0`. -/
def transformedFeasibleSet (M : Elimination) : Set Point :=
  { x | ∃ wB : BasicPoint, ∃ wN : NonbasicPoint, x = M.point wB wN ∧ M.constraint x = 0 }

/-- Membership in the transformed feasible set is equivalent to the eliminated parametrization
`x = S_B (phiBar w_N) + S_N w_N`. -/
theorem mem_transformedFeasibleSet_iff
    (M : Elimination) (x : Point) :
    x ∈ M.transformedFeasibleSet ↔
      x ∈ Set.range M.graphPoint := by
  constructor
  · rintro ⟨wB, wN, rfl, hw⟩
    refine ⟨wN, ?_⟩
    rw [M.graphPoint_eq, (M.constraint_eq_zero_iff_eq_phiBar wB wN).1 hw]
  · rintro ⟨wN, rfl⟩
    exact ⟨M wN, wN, rfl, M.constraint_eq_zero wN⟩

/-- The transformed feasible set is exactly the range of the eliminated parametrization. -/
theorem transformedFeasibleSet_eq_range
    (M : Elimination) :
    M.transformedFeasibleSet = Set.range M.graphPoint := by
  ext x
  exact M.mem_transformedFeasibleSet_iff x

/-- Minimizing `f` on the transformed feasible set
`{x | ∃ w_B, ∃ w_N, x = S_B w_B + S_N w_N ∧ c x = 0}` is equivalent to minimizing the
reduced objective `bar f`, which is the source reformulation `(11.2.31)`. -/
theorem isMinOn_point_iff_isMinOn_reducedObjective
    (M : Elimination)
    (f : Point → ℝ) (wN : NonbasicPoint) :
    IsMinOn
        f
        M.transformedFeasibleSet
        (M.graphPoint wN) ↔
      IsMinOn (M.reducedObjective f) Set.univ wN := by
  rw [isMinOn_iff, isMinOn_univ_iff]
  constructor
  · intro h yN
    exact h (M.graphPoint yN) ((M.mem_transformedFeasibleSet_iff _).2 ⟨yN, rfl⟩)
  · intro h x hx
    rcases (M.mem_transformedFeasibleSet_iff x).1 hx with ⟨yN, rfl⟩
    exact h yN

/-- The reduced gradient `bar g(w_N) = ∇_{w_N} bar f(w_N)` of the generalized elimination
objective. -/
def reducedGradient (M : Elimination)
    (f : Point → ℝ) (wN : NonbasicPoint) : NonbasicPoint :=
  gradient (M.reducedObjective f) wN

/-- Unfolding formula for `reducedGradient`. -/
theorem reducedGradient_eq (M : Elimination)
    (f : Point → ℝ) (wN : NonbasicPoint) :
    M.reducedGradient f wN = gradient (M.reducedObjective f) wN :=
  rfl

/-- The Jacobian matrix of the eliminated basic-variable map `phiBar : w_N ↦ w_B`,
written with the nonbasic-variable basis on the domain and the basic-variable basis on the
codomain. -/
abbrev eliminatedBasicJacobian
    (M : Elimination) (wN : NonbasicPoint) :
    Matrix (Fin m) (Fin (n - m)) ℝ :=
  LinearMap.toMatrix nonbasicBasis basicBasis (fderiv ℝ M.phiBar wN).toLinearMap

/-- Unfolding formula for `eliminatedBasicJacobian`. -/
theorem eliminatedBasicJacobian_eq
    (M : Elimination) (wN : NonbasicPoint) :
    M.eliminatedBasicJacobian wN =
      LinearMap.toMatrix nonbasicBasis basicBasis (fderiv ℝ M.phiBar wN).toLinearMap :=
  rfl

/-- Helper for Chapter11 Definition 11.2-extra-2: the Euclidean action of a matrix product is
the composition of the Euclidean actions of its factors. -/
lemma toEuclideanLin_mul_apply
    {p q r : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (B : Matrix (Fin q) (Fin r) ℝ)
    (x : EuclideanSpace ℝ (Fin r)) :
    Matrix.toEuclideanLin (A * B) x =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) := by
  -- Rewrite matrix multiplication through the canonical Euclidean linear maps.
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
    (Matrix.toLin_mul_apply
      (v₁ := (EuclideanSpace.basisFun (Fin r) ℝ).toBasis)
      (v₂ := (EuclideanSpace.basisFun (Fin q) ℝ).toBasis)
      (v₃ := (EuclideanSpace.basisFun (Fin p) ℝ).toBasis)
      A B x)

/-- Helper for Chapter11 Definition 11.2-extra-2: pairing against `Aᵀ g` is the same as pairing
`g` against `A v`. -/
lemma inner_toEuclideanLin_transpose_apply
    {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ)
    (g : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) :
    inner ℝ (Matrix.toEuclideanLin A.transpose g) v =
      inner ℝ g (Matrix.toEuclideanLin A v) := by
  have hadj : LinearMap.adjoint (Matrix.toEuclideanLin A.transpose) = Matrix.toEuclideanLin A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := A.transpose)).symm
  -- Move the transpose action across the inner product via the adjoint.
  calc
    inner ℝ (Matrix.toEuclideanLin A.transpose g) v =
        inner ℝ g (LinearMap.adjoint (Matrix.toEuclideanLin A.transpose) v) := by
            symm
            simpa using
              (LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A.transpose) g v)
    _ = inner ℝ g (Matrix.toEuclideanLin A v) := by
          rw [hadj]

/-- Helper for Chapter11 Definition 11.2-extra-2: the eliminated basic Jacobian matrix acts by
the derivative of `phiBar`. -/
lemma eliminatedBasicJacobian_apply
    (M : Elimination) (wN v : NonbasicPoint) :
    Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN) v =
      fderiv ℝ M.phiBar wN v := by
  have hToLin :
      Matrix.toLin nonbasicBasis basicBasis (M.eliminatedBasicJacobian wN) v =
        (fderiv ℝ M.phiBar wN).toLinearMap v := by
    -- Reconstruct the derivative map from its coordinate matrix on the Euclidean bases.
    rw [M.eliminatedBasicJacobian_eq]
    exact
      congrArg
        (fun L : NonbasicPoint →ₗ[ℝ] BasicPoint => L v)
        (Matrix.toLin_toMatrix
          (v₁ := nonbasicBasis)
          (v₂ := basicBasis)
          ((fderiv ℝ M.phiBar wN).toLinearMap))
  simp [Matrix.toEuclideanLin_eq_toLin_orthonormal, basicBasis_eq] at hToLin ⊢

/-- Helper for Chapter11 Definition 11.2-extra-2: the constraint Jacobian matrix acts by the
derivative of `constraint`. -/
lemma generalizedEliminationConstraintJacobian_apply
    (c : Point → ConstraintPoint) (x u : Point) :
    Matrix.toEuclideanLin (generalizedEliminationConstraintJacobian c x) u =
      fderiv ℝ c x u := by
  have hToLin :
      Matrix.toLin pointBasis constraintBasis (generalizedEliminationConstraintJacobian c x) u =
        (fderiv ℝ c x).toLinearMap u := by
    -- Reconstruct the derivative map from its Euclidean coordinate matrix.
    rw [generalizedEliminationConstraintJacobian_eq]
    exact
      congrArg
        (fun L : Point →ₗ[ℝ] ConstraintPoint => L u)
        (Matrix.toLin_toMatrix
          (v₁ := pointBasis)
          (v₂ := constraintBasis)
          ((fderiv ℝ c x).toLinearMap))
  simp [Matrix.toEuclideanLin_eq_toLin_orthonormal, pointBasis, constraintBasis] at hToLin ⊢

/-- Helper for Chapter11 Definition 11.2-extra-2: the elimination graph differentiates to the
basic-block action on `D phiBar(w_N)` plus the nonbasic block. -/
lemma graphPoint_hasFDerivAt
    (M : Elimination) (wN : NonbasicPoint)
    (hPhiBar : DifferentiableAt ℝ M.phiBar wN) :
    HasFDerivAt M.graphPoint
      ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.basicBlock)).comp
          (fderiv ℝ M.phiBar wN) +
        LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.nonbasicBlock))
      wN := by
  have hBasic :
      HasFDerivAt
        (fun yN : NonbasicPoint ↦ Matrix.toEuclideanLin M.basicBlock (M.phiBar yN))
        ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.basicBlock)).comp
          (fderiv ℝ M.phiBar wN))
        wN := by
    -- Differentiate the basic-block contribution by composing the linear block map with `phiBar`.
    exact (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.basicBlock)).hasFDerivAt.comp
      wN hPhiBar.hasFDerivAt
  have hNonbasic :
      HasFDerivAt
        (fun yN : NonbasicPoint ↦ Matrix.toEuclideanLin M.nonbasicBlock yN)
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.nonbasicBlock))
        wN := by
    -- The nonbasic-block contribution is linear, so its derivative is itself.
    exact (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.nonbasicBlock)).hasFDerivAt
  have hGraphEq :
      (fun yN : NonbasicPoint ↦
        Matrix.toEuclideanLin M.basicBlock (M.phiBar yN) +
          Matrix.toEuclideanLin M.nonbasicBlock yN) = M.graphPoint := by
    funext yN
    simp [M.graphPoint_eq, M.point_eq]
  -- Differentiate the explicit graph formula `S_B (phiBar yN) + S_N yN`.
  rw [← hGraphEq]
  exact hBasic.add hNonbasic

/-- Helper for Chapter11 Definition 11.2-extra-2: differentiating the constant graph constraint
first gives the untransposed Jacobian identity
`(∇ c(x)) * S_B * D phiBar(w_N) + (∇ c(x)) * S_N = 0`. -/
lemma eliminatedConstraintDerivativeRelation_untransposed
    (M : Elimination) (wN : NonbasicPoint)
    (hPhiBar : DifferentiableAt ℝ M.phiBar wN)
    (hc : DifferentiableAt ℝ M.constraint (M.graphPoint wN)) :
    ((generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) * M.basicBlock) *
        M.eliminatedBasicJacobian wN +
      (generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) *
        M.nonbasicBlock =
        0 := by
  let graphDeriv : NonbasicPoint →L[ℝ] Point :=
    ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.basicBlock)).comp
        (fderiv ℝ M.phiBar wN) +
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.nonbasicBlock))
  have hGraph :
      HasFDerivAt M.graphPoint graphDeriv wN := by
    -- Reuse the explicit derivative of the elimination graph.
    simpa [graphDeriv] using M.graphPoint_hasFDerivAt wN hPhiBar
  have hGraphDiff : DifferentiableAt ℝ M.graphPoint wN := hGraph.differentiableAt
  have hGraphConstraintFDeriv :
      fderiv ℝ (fun yN : NonbasicPoint ↦ M.constraint (M.graphPoint yN)) wN =
        (fderiv ℝ M.constraint (M.graphPoint wN)).comp graphDeriv := by
    -- Apply the chain rule to `constraint ∘ graphPoint`.
    calc
      fderiv ℝ (fun yN : NonbasicPoint ↦ M.constraint (M.graphPoint yN)) wN
          = fderiv ℝ (M.constraint ∘ M.graphPoint) wN := by
              rfl
      _ = (fderiv ℝ M.constraint (M.graphPoint wN)).comp (fderiv ℝ M.graphPoint wN) := by
            simpa using
              (fderiv_comp (x := wN) (f := M.graphPoint) (g := M.constraint) hc hGraphDiff)
      _ = (fderiv ℝ M.constraint (M.graphPoint wN)).comp graphDeriv := by
            rw [hGraph.fderiv]
  have hConstraint :
      ∀ᶠ yN in nhds wN, M.constraint (M.graphPoint yN) = 0 :=
    Filter.Eventually.of_forall M.constraint_eq_zero
  have hConst :
      HasFDerivAt (fun yN : NonbasicPoint ↦ M.constraint (M.graphPoint yN))
        (0 : NonbasicPoint →L[ℝ] ConstraintPoint) wN :=
    -- The graph constraint is identically zero, so its derivative vanishes.
    hasFDerivAt_zero_of_eventually_const (0 : ConstraintPoint) hConstraint
  apply Matrix.toEuclideanLin.injective
  ext v i
  have hBasicMap :
      Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN) v =
        fderiv ℝ M.phiBar wN v := by
    simpa using M.eliminatedBasicJacobian_apply wN v
  have hBasicContribution :
      Matrix.toEuclideanLin
          (((generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) *
              M.basicBlock) *
            M.eliminatedBasicJacobian wN)
          v =
        fderiv ℝ M.constraint (M.graphPoint wN)
          (Matrix.toEuclideanLin M.basicBlock (fderiv ℝ M.phiBar wN v)) := by
    -- Normalize the two matrix products into the derivative of `constraint` along the basic part.
    rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, hBasicMap]
    rw [generalizedEliminationConstraintJacobian_apply]
  have hNonbasicContribution :
      Matrix.toEuclideanLin
          ((generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) *
            M.nonbasicBlock)
          v =
        fderiv ℝ M.constraint (M.graphPoint wN)
          (Matrix.toEuclideanLin M.nonbasicBlock v) := by
    -- Normalize the nonbasic block term in the same way.
    rw [toEuclideanLin_mul_apply, generalizedEliminationConstraintJacobian_apply]
  have hZeroApply :
      fderiv ℝ (fun yN : NonbasicPoint ↦ M.constraint (M.graphPoint yN)) wN v = 0 := by
    rw [hConst.fderiv]
    simp
  have hChainApply :
      fderiv ℝ (fun yN : NonbasicPoint ↦ M.constraint (M.graphPoint yN)) wN v =
        fderiv ℝ M.constraint (M.graphPoint wN)
            (Matrix.toEuclideanLin M.basicBlock (fderiv ℝ M.phiBar wN v)) +
          fderiv ℝ M.constraint (M.graphPoint wN)
            (Matrix.toEuclideanLin M.nonbasicBlock v) := by
    -- Evaluate the chain rule using the explicit derivative of the elimination graph.
    rw [hGraphConstraintFDeriv]
    simp [graphDeriv, ContinuousLinearMap.comp_apply]
  have hVec :
      Matrix.toEuclideanLin
          (((generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) *
              M.basicBlock) *
            M.eliminatedBasicJacobian wN +
            (generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) *
              M.nonbasicBlock)
          v =
        0 := by
    calc
      Matrix.toEuclideanLin
          (((generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) *
              M.basicBlock) *
            M.eliminatedBasicJacobian wN +
            (generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) *
              M.nonbasicBlock)
          v
          =
        Matrix.toEuclideanLin
            (((generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) *
                M.basicBlock) *
              M.eliminatedBasicJacobian wN)
            v +
          Matrix.toEuclideanLin
            ((generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) *
              M.nonbasicBlock)
            v := by
              simp
      _ =
        fderiv ℝ M.constraint (M.graphPoint wN)
            (Matrix.toEuclideanLin M.basicBlock (fderiv ℝ M.phiBar wN v)) +
          fderiv ℝ M.constraint (M.graphPoint wN)
            (Matrix.toEuclideanLin M.nonbasicBlock v) := by
              rw [hBasicContribution, hNonbasicContribution]
      _ = 0 := by
            simpa [hChainApply] using hZeroApply
  simpa using congrArg (fun z : ConstraintPoint ↦ z i) hVec

/-- Helper for Chapter11 Definition 11.2-extra-2: the reduced gradient is the nonbasic block
applied to `∇ f(x)` plus the eliminated-basic correction term. -/
lemma reducedGradient_eq_nonbasicGradient_add_basicContribution
    (M : Elimination)
    (f : Point → ℝ) (wN : NonbasicPoint)
    (hPhiBar : DifferentiableAt ℝ M.phiBar wN)
    (hf : DifferentiableAt ℝ f (M.graphPoint wN)) :
    M.reducedGradient f wN =
      Matrix.toEuclideanLin M.nonbasicBlock.transpose (gradient f (M.graphPoint wN)) +
        Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN).transpose
          (Matrix.toEuclideanLin M.basicBlock.transpose (gradient f (M.graphPoint wN))) := by
  let graphDeriv : NonbasicPoint →L[ℝ] Point :=
    ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.basicBlock)).comp
        (fderiv ℝ M.phiBar wN) +
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M.nonbasicBlock))
  have hGraph :
      HasFDerivAt M.graphPoint graphDeriv wN := by
    -- Reuse the explicit derivative of the elimination graph inside the reduced objective.
    simpa [graphDeriv] using M.graphPoint_hasFDerivAt wN hPhiBar
  have hGraphDiff : DifferentiableAt ℝ M.graphPoint wN := hGraph.differentiableAt
  have hReducedObjectiveFDeriv :
      fderiv ℝ (M.reducedObjective f) wN =
        (fderiv ℝ f (M.graphPoint wN)).comp graphDeriv := by
    -- Differentiate `bar f = f ∘ graphPoint`.
    calc
      fderiv ℝ (M.reducedObjective f) wN
          = fderiv ℝ (f ∘ M.graphPoint) wN := by
              rfl
      _ = (fderiv ℝ f (M.graphPoint wN)).comp (fderiv ℝ M.graphPoint wN) := by
            simpa using (fderiv_comp (x := wN) (f := M.graphPoint) (g := f) hf hGraphDiff)
      _ = (fderiv ℝ f (M.graphPoint wN)).comp graphDeriv := by
            rw [hGraph.fderiv]
  have hReducedObjectiveDiff : DifferentiableAt ℝ (M.reducedObjective f) wN := by
    -- The reduced objective is differentiable because both factors of the composition are.
    have hCompDiff : DifferentiableAt ℝ (f ∘ M.graphPoint) wN := by
      exact hf.comp wN hGraphDiff
    have hEq : M.reducedObjective f = f ∘ M.graphPoint := by
      funext yN
      rfl
    exact hCompDiff.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hEq.symm)
  have hReducedGrad :
      HasGradientAt (M.reducedObjective f) (M.reducedGradient f wN) wN := by
    -- Unfold `reducedGradient` into the gradient of the reduced objective.
    simpa [M.reducedGradient_eq] using hReducedObjectiveDiff.hasGradientAt
  have hObjectiveGrad :
      HasGradientAt f (gradient f (M.graphPoint wN)) (M.graphPoint wN) := by
    -- Read the ambient derivative of `f` through its gradient at the graph point.
    simpa using hf.hasGradientAt
  -- Compare the reduced gradient and the claimed formula via the Euclidean dual pairing.
  apply (InnerProductSpace.toDual ℝ NonbasicPoint).injective
  ext v
  calc
    (InnerProductSpace.toDual ℝ NonbasicPoint (M.reducedGradient f wN)) v
        = fderiv ℝ (M.reducedObjective f) wN v := by
            rw [hReducedGrad.hasFDerivAt.fderiv]
    _ = fderiv ℝ f (M.graphPoint wN) (graphDeriv v) := by
          rw [hReducedObjectiveFDeriv]
          simp [ContinuousLinearMap.comp_apply]
    _ = inner ℝ (gradient f (M.graphPoint wN)) (graphDeriv v) := by
          rw [hObjectiveGrad.hasFDerivAt.fderiv]
          simp [InnerProductSpace.toDual_apply_apply]
    _ = inner ℝ (gradient f (M.graphPoint wN))
          (Matrix.toEuclideanLin M.basicBlock (fderiv ℝ M.phiBar wN v) +
            Matrix.toEuclideanLin M.nonbasicBlock v) := by
          simp [graphDeriv, ContinuousLinearMap.comp_apply]
    _ = inner ℝ (gradient f (M.graphPoint wN))
          (Matrix.toEuclideanLin M.basicBlock (fderiv ℝ M.phiBar wN v)) +
        inner ℝ (gradient f (M.graphPoint wN))
          (Matrix.toEuclideanLin M.nonbasicBlock v) := by
          rw [inner_add_right]
    _ = inner ℝ
          (Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN).transpose
            (Matrix.toEuclideanLin M.basicBlock.transpose (gradient f (M.graphPoint wN))))
          v +
        inner ℝ
          (Matrix.toEuclideanLin M.nonbasicBlock.transpose (gradient f (M.graphPoint wN)))
          v := by
          congr 1
          · calc
              inner ℝ (gradient f (M.graphPoint wN))
                  (Matrix.toEuclideanLin M.basicBlock (fderiv ℝ M.phiBar wN v))
                  =
                inner ℝ
                  (Matrix.toEuclideanLin M.basicBlock.transpose (gradient f (M.graphPoint wN)))
                  (fderiv ℝ M.phiBar wN v) := by
                    symm
                    exact inner_toEuclideanLin_transpose_apply
                      M.basicBlock
                      (gradient f (M.graphPoint wN))
                      (fderiv ℝ M.phiBar wN v)
            _ = inner ℝ
                  (Matrix.toEuclideanLin M.basicBlock.transpose (gradient f (M.graphPoint wN)))
                  (Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN) v) := by
                    rw [M.eliminatedBasicJacobian_apply wN v]
            _ = inner ℝ
                  (Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN).transpose
                    (Matrix.toEuclideanLin M.basicBlock.transpose
                      (gradient f (M.graphPoint wN))))
                  v := by
                    symm
                    exact inner_toEuclideanLin_transpose_apply
                      (M.eliminatedBasicJacobian wN)
                      (Matrix.toEuclideanLin M.basicBlock.transpose
                        (gradient f (M.graphPoint wN)))
                      v
          · symm
            exact inner_toEuclideanLin_transpose_apply
              M.nonbasicBlock
              (gradient f (M.graphPoint wN))
              v
    _ = (InnerProductSpace.toDual ℝ NonbasicPoint
          (Matrix.toEuclideanLin M.nonbasicBlock.transpose (gradient f (M.graphPoint wN)) +
            Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN).transpose
              (Matrix.toEuclideanLin M.basicBlock.transpose
                (gradient f (M.graphPoint wN))))) v := by
          simp [InnerProductSpace.toDual_apply_apply, real_inner_comm, add_comm]

/-- Differentiating the built-in feasibility identity
`c (S_B (phiBar w_N) + S_N w_N) = 0` yields the matrix relation used to solve for
`D phiBar(w_N)`. -/
theorem eliminatedConstraintDerivativeRelation
    (M : Elimination) (wN : NonbasicPoint)
    (hPhiBar : DifferentiableAt ℝ M.phiBar wN)
    (hc : DifferentiableAt ℝ M.constraint (M.graphPoint wN)) :
    (M.eliminatedBasicJacobian wN).transpose *
        (M.basicBlock.transpose *
          (generalizedEliminationConstraintJacobian M.constraint
            (M.graphPoint wN)).transpose) +
      (M.nonbasicBlock.transpose *
        (generalizedEliminationConstraintJacobian M.constraint
          (M.graphPoint wN)).transpose) =
        0 := by
  have hUntransposed :
      ((generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) * M.basicBlock) *
          M.eliminatedBasicJacobian wN +
        (generalizedEliminationConstraintJacobian M.constraint (M.graphPoint wN)) *
          M.nonbasicBlock =
          0 :=
    M.eliminatedConstraintDerivativeRelation_untransposed wN hPhiBar hc
  -- Transpose the untransposed graph-constraint identity to reach the displayed source form.
  simpa [Matrix.transpose_add, Matrix.transpose_mul] using congrArg Matrix.transpose hUntransposed

/-- The source basic-block stationarity equation
`S_Bᵀ [∇ f(x) - ∇ c(x)ᵀ λ] = 0` at the transformed point
`x = S_B (phiBar w_N) + S_N w_N`. -/
def multiplierEquation (M : Elimination)
    (f : Point → ℝ) (wN : NonbasicPoint) (lam : ConstraintPoint) : Prop :=
  let x := M.graphPoint wN
  Matrix.toEuclideanLin M.basicBlock.transpose
      (gradient f x -
        Matrix.toEuclideanLin
          (generalizedEliminationConstraintJacobian M.constraint x).transpose lam) =
        0

/-- Unfolding formula for `multiplierEquation`. -/
theorem multiplierEquation_iff (M : Elimination)
    (f : Point → ℝ) (wN : NonbasicPoint) (lam : ConstraintPoint) :
    M.multiplierEquation f wN lam ↔
      Matrix.toEuclideanLin M.basicBlock.transpose
          (gradient f (M.graphPoint wN) -
            Matrix.toEuclideanLin
              (generalizedEliminationConstraintJacobian M.constraint
                (M.graphPoint wN)).transpose lam) =
        0 := by
  rfl

/-- Chapter11 Definition 11.2-extra-2: if `phiBar`, `f`, and `constraint` are differentiable at
the evaluation point, and
`S_Bᵀ ∇ c(x)ᵀ` is nonsingular at `x = S_B (phiBar w_N) + S_N w_N`, then every multiplier `λ`
satisfying `S_Bᵀ [∇ f(x) - ∇ c(x)ᵀ λ] = 0` gives the generalized-elimination
reduced-gradient formula `bar g(w_N) = S_Nᵀ [∇ f(x) - ∇ c(x)ᵀ λ]` from `(11.2.32)`-`(11.2.33)`;
the derivative relation is taken from `eliminatedConstraintDerivativeRelation`, not as an
extra public hypothesis. -/
theorem reducedGradient_eq_nonbasicStationarityResidual
    (M : Elimination)
    (f : Point → ℝ) (wN : NonbasicPoint) (lam : ConstraintPoint)
    (hPhiBar : DifferentiableAt ℝ M.phiBar wN)
    (hf : DifferentiableAt ℝ f (M.graphPoint wN))
    (hc : DifferentiableAt ℝ M.constraint (M.graphPoint wN))
    (hNonsingular :
      IsUnit
        (M.basicBlock.transpose *
          (generalizedEliminationConstraintJacobian M.constraint
            (M.graphPoint wN)).transpose))
    (hMultiplier : M.multiplierEquation f wN lam) :
    M.reducedGradient f wN =
      Matrix.toEuclideanLin M.nonbasicBlock.transpose
        (gradient f (M.graphPoint wN) -
          Matrix.toEuclideanLin
            (generalizedEliminationConstraintJacobian M.constraint
              (M.graphPoint wN)).transpose lam) := by
  let x := M.graphPoint wN
  let J : Matrix (Fin m) (Fin n) ℝ := generalizedEliminationConstraintJacobian M.constraint x
  have _hBasicConstraintUnit : IsUnit (M.basicBlock.transpose * J.transpose) := by
    simpa [x, J] using hNonsingular
  have hReduced :
      M.reducedGradient f wN =
        Matrix.toEuclideanLin M.nonbasicBlock.transpose (gradient f x) +
          Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN).transpose
            (Matrix.toEuclideanLin M.basicBlock.transpose (gradient f x)) := by
    -- Start from the chain-rule expansion of the reduced gradient along the elimination graph.
    simpa [x] using
      M.reducedGradient_eq_nonbasicGradient_add_basicContribution f wN hPhiBar hf
  have hBasicResidual :
      Matrix.toEuclideanLin M.basicBlock.transpose (gradient f x) =
        Matrix.toEuclideanLin (M.basicBlock.transpose * J.transpose) lam := by
    have hEq :
        Matrix.toEuclideanLin M.basicBlock.transpose
            (gradient f x - Matrix.toEuclideanLin J.transpose lam) =
          0 := by
      simpa [x, J] using (M.multiplierEquation_iff f wN lam).1 hMultiplier
    -- Rewrite the multiplier equation into an equality for the basic-block contribution.
    have hSub :
        Matrix.toEuclideanLin M.basicBlock.transpose (gradient f x) -
          Matrix.toEuclideanLin M.basicBlock.transpose
            (Matrix.toEuclideanLin J.transpose lam) =
          0 := by
      simpa [map_sub] using hEq
    have hBasicEq :
        Matrix.toEuclideanLin M.basicBlock.transpose (gradient f x) =
          Matrix.toEuclideanLin M.basicBlock.transpose
            (Matrix.toEuclideanLin J.transpose lam) := by
      exact sub_eq_zero.mp hSub
    simpa [J, toEuclideanLin_mul_apply] using hBasicEq
  have hConstraintApply :
      Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN).transpose
          (Matrix.toEuclideanLin (M.basicBlock.transpose * J.transpose) lam) +
        Matrix.toEuclideanLin M.nonbasicBlock.transpose
          (Matrix.toEuclideanLin J.transpose lam) =
          0 := by
    have hMatrix :
        (M.eliminatedBasicJacobian wN).transpose * (M.basicBlock.transpose * J.transpose) +
          M.nonbasicBlock.transpose * J.transpose =
          0 := by
      simpa [x, J] using M.eliminatedConstraintDerivativeRelation wN hPhiBar hc
    -- Apply the derivative relation to the multiplier vector `lam`.
    have hApply :=
      congrArg
        (fun A : Matrix (Fin (n - m)) (Fin m) ℝ => Matrix.toEuclideanLin A lam)
        hMatrix
    simpa [J, toEuclideanLin_mul_apply] using hApply
  -- Substitute the multiplier equation and then cancel the basic contribution with the
  -- differentiated graph-constraint relation.
  calc
    M.reducedGradient f wN
        = Matrix.toEuclideanLin M.nonbasicBlock.transpose (gradient f x) +
            Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN).transpose
              (Matrix.toEuclideanLin M.basicBlock.transpose (gradient f x)) := hReduced
    _ = Matrix.toEuclideanLin M.nonbasicBlock.transpose (gradient f x) +
          Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN).transpose
            (Matrix.toEuclideanLin (M.basicBlock.transpose * J.transpose) lam) := by
              rw [hBasicResidual]
    _ = Matrix.toEuclideanLin M.nonbasicBlock.transpose (gradient f x) -
          Matrix.toEuclideanLin M.nonbasicBlock.transpose
            (Matrix.toEuclideanLin J.transpose lam) := by
              have hCancel :
                  Matrix.toEuclideanLin (M.eliminatedBasicJacobian wN).transpose
                      (Matrix.toEuclideanLin (M.basicBlock.transpose * J.transpose) lam) =
                    -Matrix.toEuclideanLin M.nonbasicBlock.transpose
                      (Matrix.toEuclideanLin J.transpose lam) := by
                exact eq_neg_of_add_eq_zero_left hConstraintApply
              rw [hCancel]
              simp [sub_eq_add_neg]
    _ = Matrix.toEuclideanLin M.nonbasicBlock.transpose
          (gradient f x - Matrix.toEuclideanLin J.transpose lam) := by
            symm
            exact map_sub (Matrix.toEuclideanLin M.nonbasicBlock.transpose)
              (gradient f x) (Matrix.toEuclideanLin J.transpose lam)
    _ = Matrix.toEuclideanLin M.nonbasicBlock.transpose
          (gradient f (M.graphPoint wN) -
            Matrix.toEuclideanLin
              (generalizedEliminationConstraintJacobian M.constraint
                (M.graphPoint wN)).transpose lam) := by
            simp [x, J]

#print axioms GeneralizedEliminationMethod.basicBlock
#print axioms GeneralizedEliminationMethod.nonbasicBlock
#print axioms basicBasis
#print axioms constraintBasis
#print axioms generalizedEliminationConstraintJacobian
#print axioms GeneralizedEliminationMethod.eliminatedBasicJacobian
#print axioms GeneralizedEliminationMethod.point
#print axioms GeneralizedEliminationMethod.reducedObjective
#print axioms GeneralizedEliminationMethod.reducedGradient

end GeneralizedEliminationMethod

end
