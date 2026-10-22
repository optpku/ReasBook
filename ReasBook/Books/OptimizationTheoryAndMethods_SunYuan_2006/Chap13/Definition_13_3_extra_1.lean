/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_1
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

noncomputable section

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "Jacobian" => Matrix (Fin n) (Fin m) ℝ

/-
This item only uses the affine residual map and the scaled trust-region feasible-set API.
They are restated locally so this file does not depend on the currently broken Chapter 12
optimization-program import chain.
-/

/-- The affine linearized constraint vector `c + Aᵀ d`. -/
def linearizedConstraintValue
    (c : ConstraintPoint) (A : Jacobian) (d : Point) : ConstraintPoint :=
  c + Matrix.toEuclideanLin A.transpose d

/-- Evaluating `linearizedConstraintValue c A d` gives the source affine constraint vector
`c + Aᵀ d`. -/
@[simp] theorem linearizedConstraintValue_apply
    (c : ConstraintPoint) (A : Jacobian) (d : Point) (i : Fin m) :
    linearizedConstraintValue c A d i = c i + (Matrix.toEuclideanLin A.transpose d) i :=
  rfl

/-- A step satisfies the chosen trust-region bound exactly when the chosen vector norm
`ρ` is at most `Δ` on the coordinate realization `d.ofLp`. -/
def satisfiesTrustRegionConstraint
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (Δ : ℝ) (d : Point) : Prop :=
  ρ d.ofLp ≤ Δ

/-- Unfolding `satisfiesTrustRegionConstraint ρ Δ d` gives the source trust-region bound. -/
theorem satisfiesTrustRegionConstraint_iff
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (Δ : ℝ) (d : Point) :
    satisfiesTrustRegionConstraint ρ Δ d ↔ ρ d.ofLp ≤ Δ :=
  Iff.rfl

/-- A step satisfies the scaled linearized constraints when equality-block coordinates vanish
and inequality-block coordinates are nonnegative after replacing `c` by `θ • c`. -/
def satisfiesScaledLinearizedConstraints
    (eqCount : ℕ) (θ : ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) : Prop :=
  (∀ i : Fin m, i.1 < eqCount → linearizedConstraintValue (θ • c) A d i = 0) ∧
    ∀ i : Fin m, eqCount ≤ i.1 → 0 ≤ linearizedConstraintValue (θ • c) A d i

/-- Unfolding `satisfiesScaledLinearizedConstraints eqCount θ c A d` gives the equality and
inequality constraints of the scaled linearized system. -/
theorem satisfiesScaledLinearizedConstraints_iff
    (eqCount : ℕ) (θ : ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    satisfiesScaledLinearizedConstraints eqCount θ c A d ↔
      (∀ i : Fin m, i.1 < eqCount → linearizedConstraintValue (θ • c) A d i = 0) ∧
        ∀ i : Fin m, eqCount ≤ i.1 → 0 ≤ linearizedConstraintValue (θ • c) A d i :=
  Iff.rfl

/-- The feasible set cut out by the trust-region bound `ρ d ≤ Δ` together with the scaled
linearized constraints. -/
def scaledTrustRegionFeasibleSet
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (eqCount : ℕ) (Δ θ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) : Set Point :=
  {d | satisfiesTrustRegionConstraint ρ Δ d ∧
      satisfiesScaledLinearizedConstraints eqCount θ c A d}

/-- Membership in `scaledTrustRegionFeasibleSet ρ eqCount Δ θ c A` is exactly the trust-region
bound together with the scaled linearized constraints. -/
theorem mem_scaledTrustRegionFeasibleSet_iff
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (eqCount : ℕ) (Δ θ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    d ∈ scaledTrustRegionFeasibleSet ρ eqCount Δ θ c A ↔
      satisfiesTrustRegionConstraint ρ Δ d ∧
        satisfiesScaledLinearizedConstraints eqCount θ c A d :=
  Iff.rfl

/-- The Euclidean constraint space carries the coordinatewise negative-part operation `v ↦ v⁻`. -/
instance instNegPartConstraintPoint : NegPart ConstraintPoint where
  negPart v := WithLp.toLp 2 fun i ↦ (v i)⁻

/-- Evaluating `v⁻` gives the coordinatewise negative part of `v`. -/
@[simp] theorem constraintPoint_negPart_apply
    (v : ConstraintPoint) (i : Fin m) :
    (v⁻) i = (v i)⁻ :=
  rfl

-- Domain sampling:
-- * primary domain: Gauss-Newton trust-region feasibility for linearized inequality systems in
--   Euclidean coordinates
-- * source-facing layer: `gaussNewtonResidualObjective`, `IsGaussNewtonStep`, and the source
--   feasibility equivalence `(13.3.11)`
-- * core/canonical owners sampled upstream in this chapter: `linearizedConstraintValue` from
--   `Definition_13_3_extra_2`, `satisfiesTrustRegionConstraint`,
--   `satisfiesScaledLinearizedConstraints`, and `scaledTrustRegionFeasibleSet` from
--   `Remark_13_1_extra_1`, together with mathlib's `IsMinOn`
-- * bridge/view layer in this file: the inequality-only specialization `eqCount = 0` and the
--   Euclidean norm specialization `ρ = l2Norm`
-- * primitive data here: the residual vector `ck`, Jacobian `Ak`, trust-region radius `Δk`,
--   scaling `θk`, and step `dGN`
-- * derived API here: the Gauss-Newton minimum-norm minimizer property and the source-facing
--   specialization of the Chapter 13 scaled trust-region feasible set

/-- The objective in `(13.3.10)` is the `ℓ2` norm of the negative part of the linearized
constraint vector on `ConstraintPoint = EuclideanSpace ℝ (Fin m)`. -/
def gaussNewtonResidualObjective
    (ck : ConstraintPoint) (Ak : Jacobian) (d : Point) : ℝ :=
  ‖(linearizedConstraintValue ck Ak d)⁻‖

/-- Unfolding `gaussNewtonResidualObjective ck Ak d` gives the source objective
`‖(c(x_k) + A(x_k)ᵀ d)⁻‖₂`. -/
theorem gaussNewtonResidualObjective_eq
    (ck : ConstraintPoint) (Ak : Jacobian) (d : Point) :
    gaussNewtonResidualObjective ck Ak d =
      ‖(linearizedConstraintValue ck Ak d)⁻‖ :=
  rfl

/-- A Gauss-Newton step for Chapter13 Definition 13.3-extra-1 (1): a vector `dGN` for the
current residual `ck` and Jacobian `Ak` minimizes `d ↦ ‖(ck + A(x_k)ᵀ d)⁻‖` and,
among all global minimizers of that `ℓ2`-norm problem on `Point = EuclideanSpace ℝ (Fin n)`,
has minimum norm. -/
class IsGaussNewtonStep
    (ck : ConstraintPoint) (Ak : Jacobian) (dGN : Point) : Prop where
  isMinOn : IsMinOn (gaussNewtonResidualObjective ck Ak) Set.univ dGN
  minNormOfIsMinOn (d : Point)
      (_ : IsMinOn (gaussNewtonResidualObjective ck Ak) Set.univ d) : ‖dGN‖ ≤ ‖d‖

/-- `IsGaussNewtonStep ck Ak dGN` is proposition-valued, hence subsingleton. -/
instance isGaussNewtonStepSubsingleton
    (ck : ConstraintPoint) (Ak : Jacobian) (dGN : Point) :
    Subsingleton (IsGaussNewtonStep ck Ak dGN) := inferInstance

/-- Unfolding `IsGaussNewtonStep ck Ak dGN` gives the minimum-objective and minimum-norm
conditions from `(13.3.10)` at the canonical `IsMinOn` layer. -/
theorem isGaussNewtonStep_iff_isMinOn
    (ck : ConstraintPoint) (Ak : Jacobian) (dGN : Point) :
    IsGaussNewtonStep ck Ak dGN ↔
      IsMinOn (gaussNewtonResidualObjective ck Ak) Set.univ dGN ∧
        ∀ d : Point,
          ∀ _ : IsMinOn (gaussNewtonResidualObjective ck Ak) Set.univ d,
            ‖dGN‖ ≤ ‖d‖ := by
  constructor
  · intro h
    exact ⟨h.isMinOn, h.minNormOfIsMinOn⟩
  · rintro ⟨hMin, hNorm⟩
    exact ⟨hMin, hNorm⟩

/-- Unfolding `IsGaussNewtonStep ck Ak dGN` gives the minimum-objective and minimum-norm
conditions from `(13.3.10)`. -/
theorem isGaussNewtonStep_iff
    (ck : ConstraintPoint) (Ak : Jacobian) (dGN : Point) :
    IsGaussNewtonStep ck Ak dGN ↔
      (∀ d : Point,
        gaussNewtonResidualObjective ck Ak dGN ≤
          gaussNewtonResidualObjective ck Ak d) ∧
        ∀ d : Point,
          (∀ d' : Point,
            gaussNewtonResidualObjective ck Ak d ≤
              gaussNewtonResidualObjective ck Ak d') →
            ‖dGN‖ ≤ ‖d‖ := by
  simpa [isMinOn_univ_iff] using
    (isGaussNewtonStep_iff_isMinOn ck Ak dGN)

/-- When `eqCount = 0`, the Chapter 13 scaled linearized constraints reduce to the pure
coordinatewise inequalities `0 ≤ θk • ck + A(x_k)ᵀ d`. -/
theorem satisfiesScaledLinearizedConstraints_zero_iff
    (ck : ConstraintPoint) (Ak : Jacobian) (θk : ℝ) (d : Point) :
    satisfiesScaledLinearizedConstraints 0 θk ck Ak d ↔
      ∀ i : Fin m, 0 ≤ linearizedConstraintValue (θk • ck) Ak d i := by
  rw [satisfiesScaledLinearizedConstraints_iff]
  constructor
  · intro h i
    exact h.2 i (Nat.zero_le _)
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (Nat.not_lt_zero _ hi).elim
    · intro i _
      exact h i

/-- Membership in the Chapter 13 owner `scaledTrustRegionFeasibleSet l2Norm 0 Δk θk ck Ak`
is exactly the source system `(13.3.7)`-`(13.3.9)` for the inequality-only Euclidean case. -/
theorem mem_scaledTrustRegionFeasibleSet_l2_zero_iff
    (ck : ConstraintPoint) (Ak : Jacobian) (θk Δk : ℝ) (d : Point) :
    d ∈ scaledTrustRegionFeasibleSet l2Norm 0 Δk θk ck Ak ↔
      ‖d‖ ≤ Δk ∧
        ∀ i : Fin m, 0 ≤ linearizedConstraintValue (θk • ck) Ak d i := by
  rw [mem_scaledTrustRegionFeasibleSet_iff, satisfiesTrustRegionConstraint_iff,
    satisfiesScaledLinearizedConstraints_zero_iff]
  constructor
  · rintro ⟨hd, hlin⟩
    refine ⟨?_, hlin⟩
    simpa [l2Norm, lpNorm] using hd
  · rintro ⟨hd, hlin⟩
    refine ⟨?_, hlin⟩
    simpa [l2Norm, lpNorm] using hd

/-- Helper for Chapter13 Definition 13.3-extra-1: scaling both the residual vector and the step
scales the linearized constraint value by the same factor. -/
theorem linearizedConstraintValue_smul
    (ck : ConstraintPoint) (Ak : Jacobian) (θ : ℝ) (d : Point) :
    linearizedConstraintValue (θ • ck) Ak (θ • d) =
      θ • linearizedConstraintValue ck Ak d := by
  -- Work coordinatewise so the affine-linear map reduces to scalar distributivity.
  ext i
  simp [linearizedConstraintValue_apply, mul_add]

/-- Helper for Chapter13 Definition 13.3-extra-1: rescaling a feasible point of the scaled
system by `θ⁻¹` pulls it back to the unscaled linearized residual. -/
theorem linearizedConstraintValue_inv_smul
    (ck : ConstraintPoint) (Ak : Jacobian) (θ : ℝ) (d : Point) (hθ : θ ≠ 0) :
    linearizedConstraintValue ck Ak ((θ⁻¹) • d) =
      θ⁻¹ • linearizedConstraintValue (θ • ck) Ak d := by
  -- Route correction: prove the rescaling identity coordinatewise instead of unfolding the
  -- whole feasible-set definition in the main theorems.
  ext i
  simp [linearizedConstraintValue_apply, mul_add, hθ]

/-- Helper for Chapter13 Definition 13.3-extra-1: the Gauss-Newton residual objective vanishes
exactly when every linearized constraint component is nonnegative. -/
theorem gaussNewtonResidualObjective_eq_zero_iff
    (ck : ConstraintPoint) (Ak : Jacobian) (d : Point) :
    gaussNewtonResidualObjective ck Ak d = 0 ↔
      ∀ i : Fin m, 0 ≤ linearizedConstraintValue ck Ak d i := by
  constructor
  · intro h i
    -- Convert norm-zero into vector-zero, then read off the `i`-th coordinate.
    have hnegPartZero : ‖(linearizedConstraintValue ck Ak d)⁻‖ = 0 := by
      simpa [gaussNewtonResidualObjective_eq] using h
    have hvecZero : (linearizedConstraintValue ck Ak d)⁻ = 0 :=
      norm_eq_zero.mp hnegPartZero
    have hcoordZero :
        ((linearizedConstraintValue ck Ak d)⁻) i = 0 := by
      exact congrArg (fun v : ConstraintPoint ↦ v i) hvecZero
    exact negPart_eq_zero.mp (by simpa using hcoordZero)
  · intro h
    -- Conversely, coordinatewise nonnegativity makes every negative-part coordinate vanish.
    rw [gaussNewtonResidualObjective_eq]
    apply norm_eq_zero.2
    ext i
    simpa using (negPart_eq_zero.mpr (h i))

/-- If the existing feasible set for `(13.3.7)`-`(13.3.9)` is nonempty and `dGN` is a
Gauss-Newton step, then `dGN` satisfies the unscaled linearized inequalities
`c(x_k) + A(x_k)ᵀ dGN ≥ 0`. -/
theorem gaussNewtonStep_linearizedFeasible_of_problemFeasible
    (ck : ConstraintPoint) (Ak : Jacobian) (θk Δk : ℝ) (dGN : Point)
    (hθk : 0 < θk)
    (hGN : IsGaussNewtonStep ck Ak dGN)
    (hFeasible : ∃ d : Point, d ∈ scaledTrustRegionFeasibleSet l2Norm 0 Δk θk ck Ak) :
    ∀ i : Fin m, 0 ≤ linearizedConstraintValue ck Ak dGN i := by
  rcases hFeasible with ⟨d, hdmem⟩
  rcases (mem_scaledTrustRegionFeasibleSet_l2_zero_iff ck Ak θk Δk d).1 hdmem with
    ⟨_, hlin⟩
  -- Rescale the feasible point into an unscaled competitor with zero residual objective.
  have hcompetitorZero :
      gaussNewtonResidualObjective ck Ak ((θk⁻¹) • d) = 0 := by
    rw [gaussNewtonResidualObjective_eq_zero_iff]
    intro i
    have hcoord :
        linearizedConstraintValue ck Ak ((θk⁻¹) • d) i =
          θk⁻¹ * linearizedConstraintValue (θk • ck) Ak d i := by
      simpa using congrArg (fun v : ConstraintPoint ↦ v i)
        (linearizedConstraintValue_inv_smul ck Ak θk d hθk.ne')
    rw [hcoord]
    exact mul_nonneg (inv_nonneg.mpr hθk.le) (hlin i)
  -- Compare the Gauss-Newton minimizer against that zero-objective competitor.
  have hminGN :
      gaussNewtonResidualObjective ck Ak dGN ≤
        gaussNewtonResidualObjective ck Ak ((θk⁻¹) • d) := by
    exact (isMinOn_univ_iff.mp hGN.isMinOn) ((θk⁻¹) • d)
  have hobjectiveNonneg : 0 ≤ gaussNewtonResidualObjective ck Ak dGN := by
    rw [gaussNewtonResidualObjective_eq]
    exact norm_nonneg _
  have hobjectiveZero : gaussNewtonResidualObjective ck Ak dGN = 0 := by
    rw [hcompetitorZero] at hminGN
    exact le_antisymm hminGN hobjectiveNonneg
  exact (gaussNewtonResidualObjective_eq_zero_iff ck Ak dGN).mp hobjectiveZero

/-- Chapter13 Definition 13.3-extra-1 (2): if `dGN` is the Gauss-Newton step and already
solves the unscaled linearized inequalities, then feasibility of `(13.3.7)`-`(13.3.9)` is
equivalent to the source inequality `θk * ‖dGN‖ ≤ Δk` from `(13.3.11)`. -/
theorem scaledGaussNewtonStep_feasible_iff
    (ck : ConstraintPoint) (Ak : Jacobian) (θk Δk : ℝ) (dGN : Point)
    (hθk : 0 < θk)
    (hGN : IsGaussNewtonStep ck Ak dGN)
    (hdGN_feasible : ∀ i : Fin m, 0 ≤ linearizedConstraintValue ck Ak dGN i) :
    (∃ d : Point, d ∈ scaledTrustRegionFeasibleSet l2Norm 0 Δk θk ck Ak) ↔
      θk * ‖dGN‖ ≤ Δk := by
  constructor
  · rintro ⟨d, hdmem⟩
    rcases (mem_scaledTrustRegionFeasibleSet_l2_zero_iff ck Ak θk Δk d).1 hdmem with
      ⟨hdNorm, hlin⟩
    -- Rescale the feasible point to get a zero-objective minimizer of the unscaled problem.
    have hcompetitorZero :
        gaussNewtonResidualObjective ck Ak ((θk⁻¹) • d) = 0 := by
      rw [gaussNewtonResidualObjective_eq_zero_iff]
      intro i
      have hcoord :
          linearizedConstraintValue ck Ak ((θk⁻¹) • d) i =
            θk⁻¹ * linearizedConstraintValue (θk • ck) Ak d i := by
        simpa using congrArg (fun v : ConstraintPoint ↦ v i)
          (linearizedConstraintValue_inv_smul ck Ak θk d hθk.ne')
      rw [hcoord]
      exact mul_nonneg (inv_nonneg.mpr hθk.le) (hlin i)
    have hcompetitorMin :
        IsMinOn (gaussNewtonResidualObjective ck Ak) Set.univ ((θk⁻¹) • d) := by
      rw [isMinOn_univ_iff]
      intro d'
      rw [hcompetitorZero]
      rw [gaussNewtonResidualObjective_eq]
      exact norm_nonneg _
    have hnormMin :
        ‖dGN‖ ≤ ‖(θk⁻¹) • d‖ :=
      hGN.minNormOfIsMinOn ((θk⁻¹) • d) hcompetitorMin
    have hscaledNorm :
        ‖(θk⁻¹) • d‖ = θk⁻¹ * ‖d‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hθk.le)]
    have hmulNorm :
        θk * ‖dGN‖ ≤ ‖d‖ := by
      have hmul :=
        mul_le_mul_of_nonneg_left (hscaledNorm ▸ hnormMin) hθk.le
      simpa [mul_assoc, hθk.ne', inv_mul_cancel₀, one_mul] using hmul
    exact le_trans hmulNorm hdNorm
  · intro hbound
    refine ⟨θk • dGN, ?_⟩
    rw [mem_scaledTrustRegionFeasibleSet_l2_zero_iff]
    refine ⟨?_, ?_⟩
    · -- The trust-region inequality is exactly the stated scalar bound after norm scaling.
      simpa [norm_smul, Real.norm_of_nonneg hθk.le] using hbound
    · intro i
      -- The scaled residual stays nonnegative because both `θk` and the unscaled residual are.
      have hcoord :
          linearizedConstraintValue (θk • ck) Ak (θk • dGN) i =
            θk * linearizedConstraintValue ck Ak dGN i := by
        simpa using congrArg (fun v : ConstraintPoint ↦ v i)
          (linearizedConstraintValue_smul ck Ak θk dGN)
      rw [hcoord]
      exact mul_nonneg hθk.le (hdGN_feasible i)

#print axioms gaussNewtonResidualObjective
#print axioms IsGaussNewtonStep
#print axioms satisfiesScaledLinearizedConstraints
#print axioms scaledTrustRegionFeasibleSet

end
