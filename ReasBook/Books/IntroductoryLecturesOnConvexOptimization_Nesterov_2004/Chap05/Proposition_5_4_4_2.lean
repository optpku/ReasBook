/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Alg_5_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open RealSymmetricMatrixSpace

open scoped BigOperators Gradient RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

local instance instLocalChap05_Proposition_5_4_4_21 : NormedAddCommGroup SymmMat :=
  RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup

local instance instLocalChap05_Proposition_5_4_4_22 : NormedSpace ℝ SymmMat :=
  RealSymmetricMatrixSpace.symmetricMatrixNormedSpace

local instance instLocalChap05_Proposition_5_4_4_23 : InnerProductSpace ℝ SymmMat :=
  RealSymmetricMatrixSpace.symmetricMatrixInnerProductSpace

local instance instLocalChap05_Proposition_5_4_4_24 : CompleteSpace SymmMat :=
  RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace

/-
Proposition 5.4.4.2 lies in the Chapter 5 semidefinite Newton-direction domain.

Sampled owner-style declarations:
* `semidefiniteNewtonDirectionSet` in `Definition_5_4_4_7`, the source-facing Newton-direction
  owner;
* `mem_semidefiniteNewtonDirectionSet_iff_frobenius_isMinOn` in `Definition_5_4_4_7`, the
  tangent-kernel/minimizer bridge for that owner;
* `IsSemidefiniteNewtonDirectionOutput` and `IsSemidefiniteNewtonMultiplier` in `Alg_5_4_4_1`,
  the chapter owners for a Newton-system multiplier solution and its reconstructed direction;
* `semidefiniteNewtonNormalMatrix`, `semidefiniteNewtonNormalRhs`, and
  `semidefiniteNewtonDirectionFromMultiplier` in `Alg_5_4_4_1`, the canonical normal-system data.

Best owner abstraction:
* source-facing: `semidefiniteNewtonDirectionSet A X U`;
* core/canonical: `IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ`;
* bridge/view: the coordinate normal equations obtained by expanding `Matrix.mulVec`.

Primitive data:
* `A : Fin m → 𝕊^n`;
* `X : 𝕊^n₊₊`;
* `U : 𝕊^n`;
* `Δ : 𝕊^n`.

Derived API:
* tangent feasibility `∀ i, ⟪A i, Δ⟫_F = 0`;
* the owner-level Newton-system multiplier/output relation;
* the coordinate normal equations and recovered direction.

This refinement removes the duplicate local KKT/stationarity/primal-step wrappers and reuses the
existing Chapter 5 Newton-system owner from `Alg_5_4_4_1`, keeping coordinate equations only as a
thin companion expansion.
-/

/-- A Newton direction is tangent to the Frobenius constraint kernel. -/
theorem semidefiniteNewtonDirectionSet_feasible
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    (hΔ : Δ ∈ semidefiniteNewtonDirectionSet A X U) :
    ∀ i : Fin m, ⟪A i, Δ⟫_F = 0 := by
  exact (mem_semidefiniteNewtonDirectionSet_iff_frobenius_isMinOn.mp hΔ).1

/-- Expanding `IsSemidefiniteNewtonDirectionOutput` through `Matrix.mulVec` gives the coordinate
normal equations together with the reconstructed Newton direction. -/
theorem isSemidefiniteNewtonDirectionOutput_iff_coordinate
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat} {multiplier : Fin m → ℝ} :
    IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ ↔
      (∀ i : Fin m,
        ∑ j, semidefiniteNewtonNormalMatrix X A i j * multiplier j =
          semidefiniteNewtonNormalRhs X U A i) ∧
      Δ = semidefiniteNewtonDirectionFromMultiplier X U A multiplier := by
  rw [isSemidefiniteNewtonDirectionOutput_iff]
  constructor
  · rintro ⟨hmul, rfl⟩
    refine ⟨?_, rfl⟩
    intro i
    simpa [Matrix.mulVec] using congrArg (fun v : Fin m → ℝ ↦ v i) hmul
  · rintro ⟨hcoord, rfl⟩
    refine ⟨?_, rfl⟩
    ext i
    simpa [Matrix.mulVec] using hcoord i

/-- Helper for Proposition 5.4.4.2: conjugation by a fixed symmetric matrix distributes over
addition. -/
theorem sandwich_add
    (K Y Z : SymmMat) :
    sandwich K (Y + Z) = sandwich K Y + sandwich K Z := by
  -- Expand the ambient matrix multiplication and use bilinearity in the middle factor.
  apply Subtype.ext
  ext i j
  simp [RealSymmetricMatrixSpace.sandwich, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- Helper for Proposition 5.4.4.2: conjugation by a fixed symmetric matrix is linear in the
middle factor. -/
theorem sandwich_smul
    (c : ℝ) (K Y : SymmMat) :
    sandwich K (c • Y) = c • sandwich K Y := by
  -- Expand the ambient matrix multiplication and move the scalar through the product.
  apply Subtype.ext
  ext i j
  simp [RealSymmetricMatrixSpace.sandwich, Matrix.mul_assoc]

/-- Helper for Proposition 5.4.4.2: conjugation by `K` as a linear operator on `𝕊^n`. -/
def sandwichLinearMap
    (K : SymmMat) : SymmMat →ₗ[ℝ] SymmMat where
  toFun := fun Y ↦ sandwich K Y
  map_add' := sandwich_add K
  map_smul' c Y := sandwich_smul c K Y

/-- Helper for Proposition 5.4.4.2: the sandwich operator is self-adjoint for the Frobenius
pairing. -/
theorem frobeniusInner_sandwich_eq
    (X Y Z : SymmMat) :
    ⟪sandwich X Y, Z⟫_F = ⟪Y, sandwich X Z⟫_F := by
  -- Rewrite both Frobenius pairings as traces and cycle the ambient matrix factors.
  rw [frobeniusInner_def, frobeniusInner_def]
  simp [RealSymmetricMatrixSpace.coe_sandwich, Matrix.transpose_mul, Matrix.mul_assoc,
    (isSymm X).eq, (isSymm Y).eq]
  have hcomm :
      Matrix.trace ((((X : SymmMat) : Mat) * ((Y : SymmMat) : Mat)) *
          (((X : SymmMat) : Mat) * ((Z : SymmMat) : Mat))) =
        Matrix.trace ((((X : SymmMat) : Mat) * ((Z : SymmMat) : Mat)) *
          (((X : SymmMat) : Mat) * ((Y : SymmMat) : Mat))) := by
    exact Matrix.trace_mul_comm _ _
  have hcycle :
      Matrix.trace ((((X : SymmMat) : Mat) * ((Z : SymmMat) : Mat)) *
          (((X : SymmMat) : Mat) * ((Y : SymmMat) : Mat))) =
        Matrix.trace ((((Y : SymmMat) : Mat) * (((X : SymmMat) : Mat) * ((Z : SymmMat) : Mat))) *
          ((X : SymmMat) : Mat)) := by
    simpa [Matrix.mul_assoc] using
      (Matrix.trace_mul_cycle'
        ((((X : SymmMat) : Mat) * ((Z : SymmMat) : Mat)))
        (((X : SymmMat) : Mat))
        (((Y : SymmMat) : Mat)))
  simpa [Matrix.mul_assoc] using hcomm.trans hcycle

/-- Helper for Proposition 5.4.4.2: conjugation by a symmetric matrix is symmetric for the
Frobenius pairing. -/
theorem sandwichLinearMap_isSymmetric
    (K : SymmMat) :
    (sandwichLinearMap K).IsSymmetric := by
  -- The sandwich map is symmetric because Frobenius pairing commutes with moving `K` across.
  intro Y Z
  exact frobeniusInner_sandwich_eq K Y Z

/-- Helper for Proposition 5.4.4.2: the adjoint of the Frobenius constraint map is the linear
combination of the constraint matrices with the multiplier coefficients. -/
theorem realSymmetricMatrixConstraintMap_adjoint_apply
    {A : Fin m → SymmMat} (multiplier : EuclideanSpace ℝ (Fin m)) :
    (realSymmetricMatrixConstraintMap A).adjoint multiplier =
      ∑ j, multiplier.ofLp j • A j := by
  -- Compare both sides against an arbitrary Frobenius test matrix.
  apply ext_inner_right ℝ
  intro Y
  rw [LinearMap.adjoint_inner_left]
  calc
    inner ℝ multiplier ((realSymmetricMatrixConstraintMap A) Y) =
        ∑ x, inner ℝ (multiplier.ofLp x) (inner ℝ (A x) Y) := by
      simp [PiLp.inner_apply, realSymmetricMatrixConstraintMap_apply]
    _ = ∑ x, multiplier.ofLp x * inner ℝ (A x) Y := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [show inner ℝ (multiplier.ofLp x) (inner ℝ (A x) Y) =
          inner ℝ (A x) Y * multiplier.ofLp x by rfl]
      rw [mul_comm]
    _ = inner ℝ (∑ j, multiplier.ofLp j • A j) Y := by
      rw [sum_inner]
      simp [real_inner_smul_left]

/-- Helper for Proposition 5.4.4.2: conjugating `X⁻¹ Δ X⁻¹` by `X` recovers `Δ`. -/
theorem sandwich_inv_cancel
    {X : 𝕊^n₊₊} {Δ : SymmMat} :
    sandwich (X : SymmMat) (sandwich (StrictPositiveSemidefiniteCone.inv X) Δ) = Δ := by
  letI := (strictPositiveSemidefiniteCone_posDef X).isUnit.invertible
  -- Expand the ambient matrix products and cancel the inverse factors of `X`.
  apply Subtype.ext
  ext i j
  simp [RealSymmetricMatrixSpace.sandwich, Matrix.mul_assoc, StrictPositiveSemidefiniteCone.coe_inv]

/-- Helper for Proposition 5.4.4.2: each feasibility equation of the reconstructed Newton
direction is exactly one coordinate of the multiplier normal system. -/
theorem reconstructed_direction_feasibility_coordinate
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U : SymmMat}
    {multiplier : Fin m → ℝ} (i : Fin m) :
    ⟪A i, semidefiniteNewtonDirectionFromMultiplier X U A multiplier⟫_F =
      - semidefiniteNewtonNormalRhs X U A i +
        ∑ j, semidefiniteNewtonNormalMatrix X A i j * multiplier j := by
  -- Expand the reconstructed direction into the `-U` term plus the multiplier-weighted
  -- constraint sum, then read each piece as one normal-system contribution.
  calc
    ⟪A i, semidefiniteNewtonDirectionFromMultiplier X U A multiplier⟫_F =
        ⟪A i, sandwich (X : SymmMat) (-U)⟫_F +
          ⟪A i, sandwich (X : SymmMat) (∑ j, multiplier j • A j)⟫_F := by
      simp [semidefiniteNewtonDirectionFromMultiplier, sandwich_add, inner_add_right]
    _ = - semidefiniteNewtonNormalRhs X U A i +
          ⟪A i, sandwich (X : SymmMat) (∑ j, multiplier j • A j)⟫_F := by
      simp [semidefiniteNewtonNormalRhs]
    _ = - semidefiniteNewtonNormalRhs X U A i +
          ∑ j, semidefiniteNewtonNormalMatrix X A i j * multiplier j := by
      have hsum :
          sandwich (X : SymmMat) (∑ j, multiplier j • A j) =
            ∑ j, multiplier j • sandwich (X : SymmMat) (A j) := by
        classical
        have hs_aux :
            ∀ s : Finset (Fin m),
              sandwich (X : SymmMat) (Finset.sum s (fun j ↦ multiplier j • A j)) =
                Finset.sum s (fun j ↦ multiplier j • sandwich (X : SymmMat) (A j)) := by
          intro s
          induction s using Finset.induction_on with
          | empty =>
              simpa using (sandwich_smul (0 : ℝ) (X : SymmMat) (0 : SymmMat))
          | @insert j s hj hs =>
              simp [Finset.sum_insert, hj, sandwich_add, sandwich_smul, hs]
        simpa using hs_aux Finset.univ
      calc
        - semidefiniteNewtonNormalRhs X U A i +
            ⟪A i, sandwich (X : SymmMat) (∑ j, multiplier j • A j)⟫_F
            =
          - semidefiniteNewtonNormalRhs X U A i +
            ⟪A i, ∑ j, multiplier j • sandwich (X : SymmMat) (A j)⟫_F := by
              rw [hsum]
        _ =
          - semidefiniteNewtonNormalRhs X U A i +
            ∑ j, semidefiniteNewtonNormalMatrix X A i j * multiplier j := by
              simp [semidefiniteNewtonNormalMatrix, inner_sum, inner_smul_right, mul_comm]

/-- Helper for Proposition 5.4.4.2: feasibility of a reconstructed Newton direction forces the
multiplier normal equations. -/
theorem reconstructed_direction_feasible_implies_isSemidefiniteNewtonMultiplier
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    {multiplier : Fin m → ℝ}
    (hfeasible : ∀ i : Fin m, ⟪A i, Δ⟫_F = 0)
    (hΔ :
      Δ = semidefiniteNewtonDirectionFromMultiplier X U A multiplier) :
    IsSemidefiniteNewtonMultiplier X U A multiplier := by
  -- Read each feasibility equation as one coordinate of `S λ = d`.
  rw [isSemidefiniteNewtonMultiplier_iff]
  ext i
  have hzero :
      - semidefiniteNewtonNormalRhs X U A i +
        ∑ j, semidefiniteNewtonNormalMatrix X A i j * multiplier j = 0 := by
    -- Rewrite the feasible reconstructed direction into the normal-equation coordinate form.
    rw [← reconstructed_direction_feasibility_coordinate (A := A) (X := X) (U := U)
      (multiplier := multiplier) i]
    simpa [hΔ] using hfeasible i
  -- Move the right-hand side term across to recover the coordinate equation `S λ = d`.
  have hcoord :
      ∑ j, semidefiniteNewtonNormalMatrix X A i j * multiplier j =
        semidefiniteNewtonNormalRhs X U A i := by
    linarith
  simpa [Matrix.mulVec] using hcoord

-- Proof sketch: first-order optimality of the quadratic Newton model on the tangent kernel
-- yields exactly the Chapter 5 Newton normal system already packaged by
-- `IsSemidefiniteNewtonDirectionOutput`.
/-- Proposition 5.4.4.2: a Newton direction is an output of the Chapter 5 semidefinite Newton
system. -/
theorem semidefiniteNewtonDirectionSet_output
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    (hΔ : Δ ∈ semidefiniteNewtonDirectionSet A X U) :
    ∃ multiplier : Fin m → ℝ,
      IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ := by
  rcases mem_semidefiniteNewtonDirectionSet_iff_frobenius_isMinOn.mp hΔ with ⟨hfeasible, hmin⟩
  have hconstraint : realSymmetricMatrixConstraintMap A Δ = 0 := by
    -- Repackage the Frobenius feasibility equations as membership in the linear constraint kernel.
    apply PiLp.ext
    intro i
    simpa [realSymmetricMatrixConstraintMap_apply] using hfeasible i
  letI : PseudoMetricSpace SymmMat := by
    infer_instance
  letI : UniformSpace SymmMat :=
    PseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace SymmMat :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let K : SymmMat →L[ℝ] SymmMat := {
    toLinearMap := sandwichLinearMap (StrictPositiveSemidefiniteCone.inv X)
    cont :=
      (sandwichLinearMap
        (StrictPositiveSemidefiniteCone.inv X)).continuous_of_finiteDimensional
  }
  have hself : IsSelfAdjoint K := by
    -- The quadratic term is self-adjoint because Frobenius pairing moves the sandwich operator
    -- across the inner product.
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    simpa [K] using sandwichLinearMap_isSymmetric (StrictPositiveSemidefiniteCone.inv X)
  have hobjective :
      semidefiniteNewtonDirectionObjective X U =
        quadraticAffineObjective 0 U K := by
    -- Under the intrinsic Frobenius topology, the Newton model is exactly the Chapter 5
    -- quadratic-affine objective with quadratic part `Δ ↦ X⁻¹ Δ X⁻¹`.
    funext Y
    simp [semidefiniteNewtonDirectionObjective, quadraticAffineObjective, K, sandwichLinearMap]
  have hdiff :
      DifferentiableAt ℝ (semidefiniteNewtonDirectionObjective X U) Δ := by
    -- The source objective inherits smoothness from the quadratic-affine model.
    rw [hobjective]
    let hcont : ContDiff ℝ 3 (quadraticAffineObjective 0 U K) :=
      quadraticAffineObjective_contDiff 0 U K
    exact hcont.contDiffAt.differentiableAt (by norm_num)
  have hgradient :
      ∇ (semidefiniteNewtonDirectionObjective X U) Δ =
        U + sandwich (StrictPositiveSemidefiniteCone.inv X) Δ := by
    -- Read off the pointwise gradient from the quadratic-affine gradient formula and unfold the
    -- sandwich operator once.
    rw [hobjective]
    simpa [K, sandwichLinearMap] using
      congrFun (quadraticAffineObjective_gradient_eq 0 U K hself) Δ
  have hlocal :
      IsLocalMinOn
        (semidefiniteNewtonDirectionObjective X U)
        ((realSymmetricMatrixConstraintMap A).ker : Set SymmMat)
        Δ :=
    hmin.localize
  have hlocal_level :
      IsLocalMinOn
        (semidefiniteNewtonDirectionObjective X U)
        {Y : SymmMat | realSymmetricMatrixConstraintMap A Y = 0}
        Δ := by
    -- Rewrite the kernel constraint in the level-set shape expected by Theorem 1.4.14.
    simpa [LinearMap.mem_ker] using hlocal
  have hgrad_mem :
      ∇ (semidefiniteNewtonDirectionObjective X U) Δ ∈
        (realSymmetricMatrixConstraintMap A).adjoint.range := by
    -- First-order optimality on the linear level set puts the gradient in the adjoint range.
    exact
      gradient_mem_adjoint_range_of_isLocalMinOn_linearLevelSet
        (f := semidefiniteNewtonDirectionObjective X U)
        (L := realSymmetricMatrixConstraintMap A)
        (b := 0)
        (hf := hdiff)
        (hxStar := hconstraint)
        (hmin := hlocal_level)
  rcases hgrad_mem with ⟨μ, hμ⟩
  have hstationary :
      ∑ j, μ.ofLp j • A j =
        U + sandwich (StrictPositiveSemidefiniteCone.inv X) Δ := by
    -- Expand the adjoint witness into the textbook stationarity equation.
    rw [realSymmetricMatrixConstraintMap_adjoint_apply] at hμ
    rw [hgradient] at hμ
    simpa using hμ
  have hsandwich :
      sandwich (StrictPositiveSemidefiniteCone.inv X) Δ =
        -U + ∑ j, μ.ofLp j • A j := by
    -- Move `U` to the other side to isolate the conjugated Newton direction.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg (fun Y : SymmMat ↦ Y - U) hstationary.symm
  have hdirection :
      Δ = semidefiniteNewtonDirectionFromMultiplier X U A μ.ofLp := by
    -- Conjugate the stationarity identity by `X` and use `X (X⁻¹ Δ X⁻¹) X = Δ`.
    calc
      Δ = sandwich (X : SymmMat) (sandwich (StrictPositiveSemidefiniteCone.inv X) Δ) := by
        symm
        exact sandwich_inv_cancel (X := X) (Δ := Δ)
      _ = sandwich (X : SymmMat) (-U + ∑ j, μ.ofLp j • A j) := by
        rw [hsandwich]
      _ = semidefiniteNewtonDirectionFromMultiplier X U A μ.ofLp := by
        simp [semidefiniteNewtonDirectionFromMultiplier]
  have hmultiplier :
      IsSemidefiniteNewtonMultiplier X U A μ.ofLp :=
    reconstructed_direction_feasible_implies_isSemidefiniteNewtonMultiplier
      hfeasible
      hdirection
  exact ⟨μ.ofLp, hmultiplier, hdirection⟩

/-- Proposition 5.4.4.2 in coordinate form: a Newton direction admits multipliers solving the
normal equations, and `Δ` is the reconstructed direction attached to those multipliers. -/
theorem semidefiniteNewtonDirectionSet_normal_system
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    (hΔ : Δ ∈ semidefiniteNewtonDirectionSet A X U) :
    ∃ multiplier : Fin m → ℝ,
      (∀ i : Fin m,
        ∑ j, semidefiniteNewtonNormalMatrix X A i j * multiplier j =
          semidefiniteNewtonNormalRhs X U A i) ∧
      Δ = semidefiniteNewtonDirectionFromMultiplier X U A multiplier := by
  rcases semidefiniteNewtonDirectionSet_output hΔ with ⟨multiplier, hOutput⟩
  exact ⟨multiplier, isSemidefiniteNewtonDirectionOutput_iff_coordinate.mp hOutput⟩

end
