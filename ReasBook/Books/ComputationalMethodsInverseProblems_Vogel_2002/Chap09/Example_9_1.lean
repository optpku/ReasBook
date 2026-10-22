/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_2.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_36
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Notation_2_4
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_42
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_4.QuadraticFunctional
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_8.FeasibleSet
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_15.Projector
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1.Blur2D
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_17
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

noncomputable section

open scoped BigOperators Matrix

namespace Example91

/-- Example 9.1-extra-1 (0). The mixed data model `(9.1)` consists of
independent coordinates together with the coordinatewise Poisson-plus-Gaussian
laws whose nonnegative rates realize `[(K fTrue)] i`. -/
abbrev HasMixedDataModel
    {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (fTrue : EuclideanSpace ℝ (Fin n)) (rate : Fin n → NNReal)
    (σ2 : NNReal) (d : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ i : Fin n, (rate i : ℝ) = Matrix.toEuclideanLin K fTrue i) ∧
    ProbabilityTheory.iIndepFun (fun i ω ↦ d ω i) μ ∧
      ∀ i : Fin n,
        ProbabilityTheory.HasLaw (fun ω ↦ d ω i)
          (Blur2D.pixelNoiseLaw (rate i) σ2) μ

@[simp] theorem hasMixedDataModel_iff
    {Ω : Type _} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    {fTrue : EuclideanSpace ℝ (Fin n)} {rate : Fin n → NNReal}
    {σ2 : NNReal} {d : Ω → EuclideanSpace ℝ (Fin n)} :
    HasMixedDataModel μ K fTrue rate σ2 d ↔
      (∀ i : Fin n, (rate i : ℝ) = Matrix.toEuclideanLin K fTrue i) ∧
        ProbabilityTheory.iIndepFun (fun i ω ↦ d ω i) μ ∧
          ∀ i : Fin n,
            ProbabilityTheory.HasLaw (fun ω ↦ d ω i)
              (Blur2D.pixelNoiseLaw (rate i) σ2) μ :=
  Iff.rfl

end Example91

/-- Helper for Example 9.1-extra-1: the shifted Poisson-likelihood functional
with the displayed formula `(9.5)`, using data truncation
`d̄_i = max {d_i, 0}` and variance shift `σ2`. -/
def example91LikelihoodFunctional (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 α : ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun f ↦
    (∑ i : Fin n, (Matrix.toEuclideanLin K f i + σ2)) -
      ∑ i : Fin n, (max (d i) 0 + σ2) * Real.log (Matrix.toEuclideanLin K f i + σ2) +
        (α / 2) * ‖f‖ ^ 2

/-- Helper for Example 9.1-extra-1: the defining formula for
`example91LikelihoodFunctional`. -/
@[simp] theorem example91LikelihoodFunctional_def (n : ℕ)
    (K : Matrix (Fin n) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n))
    (σ2 α : ℝ) (f : EuclideanSpace ℝ (Fin n)) :
    example91LikelihoodFunctional n K d σ2 α f =
      (∑ i : Fin n, (Matrix.toEuclideanLin K f i + σ2)) -
        ∑ i : Fin n, (max (d i) 0 + σ2) * Real.log (Matrix.toEuclideanLin K f i + σ2) +
          (α / 2) * ‖f‖ ^ 2 :=
by
  simp [example91LikelihoodFunctional]

/-- Helper for Example 9.1-extra-1: the diagonal matrix `D(f)` from `(9.8)`
for the shifted likelihood Hessian. -/
def example91LikelihoodDiagonal (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 : ℝ) (f : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal
    (fun i ↦ (max (d i) 0 + σ2) / (Matrix.toEuclideanLin K f i + σ2) ^ 2)

/-- Helper for Example 9.1-extra-1: the matrix `D(f)` from `(9.8)` is
diagonal with entries `(d̄_i + σ2) / ([K f]_i + σ2)^2`. -/
@[simp] theorem example91LikelihoodDiagonal_def (n : ℕ)
    (K : Matrix (Fin n) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n))
    (σ2 : ℝ) (f : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    example91LikelihoodDiagonal n K d σ2 f i j =
      if i = j then
        (max (d i) 0 + σ2) / (Matrix.toEuclideanLin K f i + σ2) ^ 2
      else 0 := by
  by_cases h : i = j
  · simp [example91LikelihoodDiagonal, h]
  · simp [example91LikelihoodDiagonal, h]

/-- Example 9.1-extra-1 (1). The least-squares objective `(9.2)` is the
canonical Tikhonov functional after transporting the matrix `K` to
`K.toEuclideanLin.toContinuousLinearMap` and taking the penalty operator
`(1 / 2) • id`. -/
theorem example91LsObjective_eq_tikhonovFunctional
    (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (α : ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    ContinuousLinearMap.tikhonovFunctional
      K.toEuclideanLin.toContinuousLinearMap
      ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      d α f =
      ‖Matrix.toEuclideanLin K f - d‖ ^ 2 / 2 + (α / 2) * ‖f‖ ^ 2 := by
  -- Unfold the specialized Tikhonov functional and normalize the half-scaled identity penalty.
  rw [ContinuousLinearMap.tikhonovFunctional_def, halfScaledId_inner_eq_half_normSq]
  have hscale : α * (‖f‖ ^ 2 / 2) = (α / 2) * ‖f‖ ^ 2 := by
    ring
  simp [hscale, add_comm]

/- Example 9.1-extra-1 (2). The displayed inverse-form unconstrained minimizer
after `(9.2)` is already formalized by the canonical repository theorem
`Tikhonov.reconstruction_eq`.
-/
#check Tikhonov.reconstruction_eq

/-- Example 9.1-extra-1 (3). The nonnegative least-squares problem `(9.3)` is
the Tikhonov minimization problem over `NonnegativeOrthant.feasibleSet n`. -/
theorem example91NnlsProblem_iff
    (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (α : ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    ContinuousLinearMap.IsTikhonovMinimizer
      K.toEuclideanLin.toContinuousLinearMap
      ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      (NonnegativeOrthant.feasibleSet n) d α f ↔
      f ∈ NonnegativeOrthant.feasibleSet n ∧
        IsMinOn
          (fun g : EuclideanSpace ℝ (Fin n) ↦
            ‖Matrix.toEuclideanLin K g - d‖ ^ 2 / 2 + (α / 2) * ‖g‖ ^ 2)
          (NonnegativeOrthant.feasibleSet n) f := by
  -- Expose the minimizer predicate and rewrite its pointwise objective values into `(9.2)`.
  rw [ContinuousLinearMap.isTikhonovMinimizer_iff]
  constructor
  · rintro ⟨hf_mem, hf_min⟩
    refine ⟨hf_mem, ?_⟩
    intro g hg
    change
      ‖Matrix.toEuclideanLin K f - d‖ ^ 2 / 2 + (α / 2) * ‖f‖ ^ 2 ≤
        ‖Matrix.toEuclideanLin K g - d‖ ^ 2 / 2 + (α / 2) * ‖g‖ ^ 2
    have hfg :
        ContinuousLinearMap.tikhonovFunctional
            K.toEuclideanLin.toContinuousLinearMap
            ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
            d α f ≤
          ContinuousLinearMap.tikhonovFunctional
            K.toEuclideanLin.toContinuousLinearMap
            ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
            d α g := by
      simpa [Set.mem_setOf_eq] using hf_min hg
    calc
      ‖Matrix.toEuclideanLin K f - d‖ ^ 2 / 2 + (α / 2) * ‖f‖ ^ 2
          =
        ContinuousLinearMap.tikhonovFunctional
          K.toEuclideanLin.toContinuousLinearMap
          ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
          d α f := (example91LsObjective_eq_tikhonovFunctional n K d α f).symm
      _ ≤
        ContinuousLinearMap.tikhonovFunctional
          K.toEuclideanLin.toContinuousLinearMap
          ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
          d α g := hfg
      _ =
        ‖Matrix.toEuclideanLin K g - d‖ ^ 2 / 2 + (α / 2) * ‖g‖ ^ 2 :=
          example91LsObjective_eq_tikhonovFunctional n K d α g
  · rintro ⟨hf_mem, hf_min⟩
    refine ⟨hf_mem, ?_⟩
    intro g hg
    change
      ContinuousLinearMap.tikhonovFunctional
          K.toEuclideanLin.toContinuousLinearMap
          ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
          d α f ≤
        ContinuousLinearMap.tikhonovFunctional
          K.toEuclideanLin.toContinuousLinearMap
          ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
          d α g
    have hfg :
        ‖Matrix.toEuclideanLin K f - d‖ ^ 2 / 2 + (α / 2) * ‖f‖ ^ 2 ≤
          ‖Matrix.toEuclideanLin K g - d‖ ^ 2 / 2 + (α / 2) * ‖g‖ ^ 2 := by
      simpa [Set.mem_setOf_eq] using hf_min hg
    calc
      ContinuousLinearMap.tikhonovFunctional
          K.toEuclideanLin.toContinuousLinearMap
          ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
          d α f
          =
        ‖Matrix.toEuclideanLin K f - d‖ ^ 2 / 2 + (α / 2) * ‖f‖ ^ 2 :=
          example91LsObjective_eq_tikhonovFunctional n K d α f
      _ ≤
        ‖Matrix.toEuclideanLin K g - d‖ ^ 2 / 2 + (α / 2) * ‖g‖ ^ 2 := hfg
      _ =
        ContinuousLinearMap.tikhonovFunctional
          K.toEuclideanLin.toContinuousLinearMap
          ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
          d α g := (example91LsObjective_eq_tikhonovFunctional n K d α g).symm

/-- Helper for Example 9.1-extra-1: the displayed least-squares objective is
the quadratic functional with matrix part `Kᵀ * K + α I`. -/
lemma example91LsObjective_eq_quadraticFunctional
    (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (α : ℝ) :
    (fun f : EuclideanSpace ℝ (Fin n) ↦
      ‖Matrix.toEuclideanLin K f - d‖ ^ 2 / 2 + (α / 2) * ‖f‖ ^ 2) =
      QuadraticOptimization.quadraticFunctional
        (‖d‖ ^ 2 / 2)
        (-Matrix.toEuclideanLin K.transpose d)
        (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  funext f
  -- Expand the residual square and regroup the quadratic, linear, and constant pieces.
  rw [QuadraticOptimization.quadraticFunctional_def, ← real_inner_self_eq_norm_sq,
    inner_sub_left, inner_sub_right, inner_sub_right]
  have hCross :
      inner ℝ d (Matrix.toEuclideanLin K f) =
        inner ℝ (Matrix.toEuclideanLin K.transpose d) f := by
    calc
      inner ℝ d (Matrix.toEuclideanLin K f)
          = inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin K)) d) f := by
              simpa using
                (LinearMap.adjoint_inner_left (A := Matrix.toEuclideanLin K) (x := f) (y := d)).symm
      _ = inner ℝ (Matrix.toEuclideanLin K.transpose d) f := by
            rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint K,
              Matrix.conjTranspose_eq_transpose_of_trivial]
  have hCross' :
      inner ℝ (Matrix.toEuclideanLin K f) d =
        inner ℝ (Matrix.toEuclideanLin K.transpose d) f := by
    rw [real_inner_comm, hCross]
  have hQuadratic :
      inner ℝ (Matrix.toEuclideanLin K f) (Matrix.toEuclideanLin K f) =
        inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f := by
    calc
      inner ℝ (Matrix.toEuclideanLin K f) (Matrix.toEuclideanLin K f)
          = inner ℝ ((Matrix.toEuclideanLin K).adjoint (Matrix.toEuclideanLin K f)) f := by
              simpa using
                (LinearMap.adjoint_inner_left
                  (A := Matrix.toEuclideanLin K) (x := f) (y := Matrix.toEuclideanLin K f)).symm
      _ = inner ℝ (Matrix.toEuclideanLin K.transpose (Matrix.toEuclideanLin K f)) f := by
            simpa using congrArg (fun T => inner ℝ (T (Matrix.toEuclideanLin K f)) f)
              (Matrix.toEuclideanLin_conjTranspose_eq_adjoint K).symm
      _ = inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f := by
            simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have hMatrixPart :
      inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f + α * inner ℝ f f =
        inner ℝ
          (Matrix.toEuclideanLin
            (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)) f) f := by
    -- Combine the Gramian and identity-shift contributions into a single matrix action.
    calc
      inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f + α * inner ℝ f f
          = inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f +
              inner ℝ (α • f) f := by
                rw [real_inner_smul_left]
      _ =
          inner ℝ
            (Matrix.toEuclideanLin (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)) f) f := by
              simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, inner_add_left]
  rw [hCross, hCross', hQuadratic]
  calc
    (inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f -
          inner ℝ (Matrix.toEuclideanLin K.transpose d) f -
            (inner ℝ (Matrix.toEuclideanLin K.transpose d) f - inner ℝ d d)) /
        2 +
        (α / 2) * ‖f‖ ^ 2
        =
      ‖d‖ ^ 2 / 2 - inner ℝ (Matrix.toEuclideanLin K.transpose d) f +
        (1 / 2 : ℝ) *
          (inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f + α * inner ℝ f f) := by
            rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
            ring
    _ =
      ‖d‖ ^ 2 / 2 - inner ℝ (Matrix.toEuclideanLin K.transpose d) f +
        (1 / 2 : ℝ) *
          inner ℝ
            (Matrix.toEuclideanLin
              (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)) f) f := by
            rw [hMatrixPart]
    _ =
      ‖d‖ ^ 2 / 2 + inner ℝ (-Matrix.toEuclideanLin K.transpose d) f +
        (1 / 2 : ℝ) *
          inner ℝ
            (Matrix.toEuclideanLin
              (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)) f) f := by
            rw [sub_eq_add_neg, ← inner_neg_left]

/-- Helper for Example 9.1-extra-1: the shifted Gramian
`Kᵀ * K + α I` is positive definite when `α > 0`. -/
lemma example91GramShift_posDef
    (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 0 < α) :
    (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have hGram : (K.transpose * K).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self K
  have hShift : (α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
    simpa using (Matrix.PosDef.smul (x := (1 : Matrix (Fin n) (Fin n) ℝ)) Matrix.PosDef.one hα)
  -- The positive-definite identity shift upgrades the Gramian from semidefinite to definite.
  simpa [add_comm] using hShift.add_posSemidef hGram

/-- Example 9.1-extra-1 (4). The nonnegative least-squares problem `(9.3)`
has a unique Tikhonov minimizer on `NonnegativeOrthant.feasibleSet n` when
`α > 0`; `example91NnlsProblem_iff` exposes the explicit `IsMinOn` surface. -/
theorem example91ExistsUniqueNnlsMinimizer
    (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (α : ℝ)
    (hα : 0 < α) :
    ∃! f : EuclideanSpace ℝ (Fin n),
      ContinuousLinearMap.IsTikhonovMinimizer
        K.toEuclideanLin.toContinuousLinearMap
        ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
        (NonnegativeOrthant.feasibleSet n) d α f := by
  let J : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun f ↦ ‖Matrix.toEuclideanLin K f - d‖ ^ 2 / 2 + (α / 2) * ‖f‖ ^ 2
  have hJ_cont : Continuous J := by
    -- The least-squares objective is a polynomial expression in continuous linear maps.
    fun_prop
  have hC_convex : Convex ℝ (NonnegativeOrthant.feasibleSet n) :=
    (NonnegativeOrthant.closedConvex_feasibleSet n).convex
  have hJ_strict_univ : StrictConvexOn ℝ Set.univ J := by
    -- Rewrite the objective into Chapter 3's quadratic normal form and use positive definiteness.
    dsimp [J]
    rw [example91LsObjective_eq_quadraticFunctional n K d α]
    exact
      QuadraticOptimization.strictConvexOn_quadraticFunctional_of_posDef
        (‖d‖ ^ 2 / 2)
        (-Matrix.toEuclideanLin K.transpose d)
        (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ))
        (example91GramShift_posDef n K α hα)
  have hJ_strict : StrictConvexOn ℝ (NonnegativeOrthant.feasibleSet n) J :=
    hJ_strict_univ.subset (by intro f hf; simp) hC_convex
  have h0_mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ NonnegativeOrthant.feasibleSet n := by
    simp [NonnegativeOrthant.mem_feasibleSet]
  have hLower : ∀ f : EuclideanSpace ℝ (Fin n), (α / 2) * ‖f‖ ^ 2 ≤ J f := by
    intro f
    dsimp [J]
    nlinarith [sq_nonneg ‖Matrix.toEuclideanLin K f - d‖]
  let B : ℝ := |J 0| + 1
  let R : ℝ := max 1 (2 * B / α + 1)
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith [le_max_left (1 : ℝ) (2 * B / α + 1)]
  have h0_ball : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall 0 R := by
    simp [Metric.mem_closedBall, hR_pos.le]
  have hCompact :
      IsCompact (NonnegativeOrthant.feasibleSet n ∩ Metric.closedBall 0 R) := by
    have hClosed :
        IsClosed (NonnegativeOrthant.feasibleSet n ∩ Metric.closedBall 0 R) :=
      (NonnegativeOrthant.closedConvex_feasibleSet n).isClosed.inter Metric.isClosed_closedBall
    exact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).of_isClosed_subset hClosed
        (by intro f hf; exact hf.2)
  obtain ⟨fStar, hfStar_mem, hfStar_min⟩ :=
    hCompact.exists_isMinOn ⟨0, ⟨h0_mem, h0_ball⟩⟩ hJ_cont.continuousOn
  have hfStar_feasible : fStar ∈ NonnegativeOrthant.feasibleSet n := hfStar_mem.1
  have hfStar_le_zero : J fStar ≤ J 0 := hfStar_min ⟨h0_mem, h0_ball⟩
  have hGlobalMin : IsMinOn J (NonnegativeOrthant.feasibleSet n) fStar := by
    intro f hf
    by_cases hfBall : f ∈ Metric.closedBall 0 R
    · exact hfStar_min ⟨hf, hfBall⟩
    · have hR_lt_norm : R < ‖f‖ := by
        have hfBall' : ¬ ‖f‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hfBall
        exact lt_of_not_ge hfBall'
      have hBig : 2 * B / α < ‖f‖ := by
        have hAux : 2 * B / α + 1 ≤ R := le_max_right (1 : ℝ) (2 * B / α + 1)
        linarith
      have hNorm_gt_one : 1 < ‖f‖ := by
        have hOne : 1 ≤ R := le_max_left (1 : ℝ) (2 * B / α + 1)
        linarith
      have hNorm_sq : ‖f‖ < ‖f‖ ^ 2 := by
        nlinarith
      have hPenaltyBig : B < (α / 2) * ‖f‖ ^ 2 := by
        have hBigSq : 2 * B / α < ‖f‖ ^ 2 := lt_trans hBig hNorm_sq
        have hBigMulSq : 2 * B < α * ‖f‖ ^ 2 := by
          have htmp : 2 * B < ‖f‖ ^ 2 * α := (div_lt_iff₀ hα).mp hBigSq
          simpa [mul_comm] using htmp
        nlinarith [hBigMulSq]
      have hZero_lt_B : J 0 < B := by
        dsimp [B]
        linarith [le_abs_self (J 0)]
      have hZero_lt_Jf : J 0 < J f := by
        exact lt_of_lt_of_le (lt_trans hZero_lt_B hPenaltyBig) (hLower f)
      exact hfStar_le_zero.trans hZero_lt_Jf.le
  refine ⟨fStar, ?_, ?_⟩
  · -- Repackage the explicit minimizer on the feasible set into the Tikhonov predicate.
    exact (example91NnlsProblem_iff n K d α fStar).2 ⟨hfStar_feasible, hGlobalMin⟩
  · intro g hg
    have hg' := (example91NnlsProblem_iff n K d α g).1 hg
    -- Strict convexity forces any two feasible minimizers to coincide.
    exact hJ_strict.eq_of_isMinOn hg'.2 hGlobalMin hg'.1 hfStar_feasible

/- Example 9.1-extra-1 (5). The shifted likelihood functional `(9.5)` is
formalized by `example91LikelihoodFunctional`, with displayed formula exposed
by `example91LikelihoodFunctional_def`. -/
#check example91LikelihoodFunctional_def

/- Example 9.1-extra-1 (8). The diagonal matrix formula `(9.8)` is formalized
by `example91LikelihoodDiagonal_def`. -/
#check example91LikelihoodDiagonal_def

/-- Helper for Example 9.1-extra-1: the scalar shifted Poisson term
`b ↦ b - a * log b` is minimized at `b = a` on the positive half-line. -/
lemma shiftedPoissonCoordinateTerm_le_of_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - a * Real.log a ≤ b - a * Real.log b := by
  -- Rewrite the target through `log (b / a) ≤ b / a - 1`.
  have hlog :
      Real.log (b / a) ≤ b / a - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hscaled : a * Real.log (b / a) ≤ b - a := by
    have hmul := mul_le_mul_of_nonneg_left hlog ha.le
    have hright : a * (b / a - 1) = b - a := by
      field_simp [ha.ne']
    simpa [hright] using hmul
  rw [Real.log_div hb.ne' ha.ne'] at hscaled
  linarith

/-- Helper for Example 9.1-extra-1: for nonnegative weight `a`, the scalar
shifted Poisson term `x ↦ x - a * log x` is convex on `(0, ∞)`. -/
lemma shiftedPoissonCoordinateConvexOn
    {a : ℝ} (ha : 0 ≤ a) :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ ↦ x - a * Real.log x) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  have hlog :
      α * Real.log x + β * Real.log y ≤ Real.log (α * x + β * y) := by
    simpa [smul_eq_mul] using
      strictConcaveOn_log_Ioi.concaveOn.2 hx hy hα hβ hαβ
  have hscaled :
      a * (α * Real.log x + β * Real.log y) ≤
        a * Real.log (α * x + β * y) :=
    mul_le_mul_of_nonneg_left hlog ha
  calc
    (α * x + β * y) - a * Real.log (α * x + β * y) ≤
        (α * x + β * y) - a * (α * Real.log x + β * Real.log y) := by
      linarith
    _ = α * (x - a * Real.log x) + β * (y - a * Real.log y) := by
      ring

/-- Helper for Example 9.1-extra-1: the shifted likelihood objective is
continuous on the feasible set because `hpos` keeps every log argument away from
zero there. -/
lemma example91LikelihoodContinuousOnFeasible
    (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 α : ℝ)
    (hpos :
      ∀ f : EuclideanSpace ℝ (Fin n),
        f ∈ NonnegativeOrthant.feasibleSet n →
          ∀ i : Fin n, 0 < Matrix.toEuclideanLin K f i + σ2) :
    ContinuousOn (example91LikelihoodFunctional n K d σ2 α)
      (NonnegativeOrthant.feasibleSet n) := by
  let s : Set (EuclideanSpace ℝ (Fin n)) := NonnegativeOrthant.feasibleSet n
  let argTerm : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i f ↦ Matrix.toEuclideanLin K f i + σ2
  let logTerm : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i f ↦ (max (d i) 0 + σ2) * Real.log (argTerm i f)
  have hargCont : ∀ i : Fin n, ContinuousOn (argTerm i) s := by
    intro i
    exact
      (((PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) i).comp
          (Matrix.toEuclideanLin K).toContinuousLinearMap.continuous).add
        continuous_const).continuousOn
  have hlogCont : ∀ i : Fin n, ContinuousOn (logTerm i) s := by
    intro i
    have hlog :
        ContinuousOn (fun f : EuclideanSpace ℝ (Fin n) ↦ Real.log (argTerm i f)) s := by
      exact (hargCont i).log (fun f hf ↦ (hpos f hf i).ne')
    exact
      (continuousOn_const : ContinuousOn
          (fun _ : EuclideanSpace ℝ (Fin n) ↦ max (d i) 0 + σ2) s).mul hlog
  have hsumArg :
      ContinuousOn (fun f : EuclideanSpace ℝ (Fin n) ↦ ∑ i : Fin n, argTerm i f) s := by
    exact continuousOn_finsetSum Finset.univ (fun i _ ↦ hargCont i)
  have hsumLog :
      ContinuousOn (fun f : EuclideanSpace ℝ (Fin n) ↦ ∑ i : Fin n, logTerm i f) s := by
    exact continuousOn_finsetSum Finset.univ (fun i _ ↦ hlogCont i)
  have hpen :
      ContinuousOn (fun f : EuclideanSpace ℝ (Fin n) ↦ (α / 2) * ‖f‖ ^ 2) s := by
    exact (continuous_const.mul (continuous_norm.pow 2)).continuousOn
  have hObjectiveEq :
      example91LikelihoodFunctional n K d σ2 α =
        (fun f : EuclideanSpace ℝ (Fin n) ↦
          (∑ i : Fin n, argTerm i f) - ∑ i : Fin n, logTerm i f +
            (α / 2) * ‖f‖ ^ 2) := by
    funext f
    simp [example91LikelihoodFunctional_def, argTerm, logTerm, Finset.sum_add_distrib]
  rw [hObjectiveEq]
  exact (hsumArg.sub hsumLog).add hpen

/-- Helper for Example 9.1-extra-1: the shifted likelihood objective is
strictly convex on the feasible set once the positive log-domain and
regularization hypotheses are enforced. -/
lemma example91LikelihoodStrictConvexOnFeasible
    (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 α : ℝ)
    (hα : 0 < α)
    (hpos :
      ∀ f : EuclideanSpace ℝ (Fin n),
        f ∈ NonnegativeOrthant.feasibleSet n →
          ∀ i : Fin n, 0 < Matrix.toEuclideanLin K f i + σ2) :
    StrictConvexOn ℝ (NonnegativeOrthant.feasibleSet n)
      (example91LikelihoodFunctional n K d σ2 α) := by
  let s : Set (EuclideanSpace ℝ (Fin n)) := NonnegativeOrthant.feasibleSet n
  let a : Fin n → ℝ := fun i ↦ max (d i) 0 + σ2
  let coordTerm : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i f ↦
      (Matrix.toEuclideanLin K f i + σ2) -
        a i * Real.log (Matrix.toEuclideanLin K f i + σ2)
  let penalty : EuclideanSpace ℝ (Fin n) → ℝ := fun f ↦ (α / 2) * ‖f‖ ^ 2
  have hsConvex : Convex ℝ s :=
    (NonnegativeOrthant.closedConvex_feasibleSet n).convex
  have h0_mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ s := by
    simp [s, NonnegativeOrthant.mem_feasibleSet]
  have hcoordConvex : ∀ i : Fin n, ConvexOn ℝ s (coordTerm i) := by
    intro i
    refine ⟨hsConvex, ?_⟩
    intro x hx y hy β γ hβ hγ hβγ
    have hxpos : 0 < Matrix.toEuclideanLin K x i + σ2 := hpos x hx i
    have hypos : 0 < Matrix.toEuclideanLin K y i + σ2 := hpos y hy i
    have hai : 0 ≤ a i := by
      dsimp [a]
      have hσ2 : 0 < σ2 := by
        simpa using (hpos 0 h0_mem i)
      exact add_nonneg (le_max_right _ _) hσ2.le
    have hcoord :=
      (shiftedPoissonCoordinateConvexOn (a := a i) hai).2
        hxpos hypos hβ hγ hβγ
    have hcombo :
        (K *ᵥ (β • x.ofLp + γ • y.ofLp)) i + σ2 =
          β * ((K *ᵥ x.ofLp) i + σ2) +
            γ * ((K *ᵥ y.ofLp) i + σ2) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      calc
        (β • (K *ᵥ x.ofLp) + γ • (K *ᵥ y.ofLp)) i + σ2
            = β * (K *ᵥ x.ofLp) i + γ * (K *ᵥ y.ofLp) i + σ2 := by
                simp [smul_eq_mul, add_assoc]
        _ = β * (K *ᵥ x.ofLp) i + γ * (K *ᵥ y.ofLp) i + (β + γ) * σ2 := by
              rw [hβγ, one_mul]
        _ =
            β * ((K *ᵥ x.ofLp) i + σ2) +
              γ * ((K *ᵥ y.ofLp) i + σ2) := by
                ring
    simpa [coordTerm, hcombo, Matrix.toEuclideanLin, smul_eq_mul]
      using hcoord
  have hDataConvex :
      ConvexOn ℝ s (fun f : EuclideanSpace ℝ (Fin n) ↦ ∑ i : Fin n, coordTerm i f) := by
    refine ⟨hsConvex, ?_⟩
    intro x hx y hy β γ hβ hγ hβγ
    simpa [Finset.sum_add_distrib, Finset.mul_sum, smul_eq_mul, mul_add, add_mul,
      add_assoc, add_left_comm, add_comm]
      using Finset.sum_le_sum fun i _ ↦ (hcoordConvex i).2 hx hy hβ hγ hβγ
  have hPenaltyEq :
      penalty =
        QuadraticOptimization.quadraticFunctional
          (0 : ℝ) (0 : EuclideanSpace ℝ (Fin n))
          (α • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    funext f
    rw [QuadraticOptimization.quadraticFunctional_def]
    have hmat :
        Matrix.toEuclideanLin (α • (1 : Matrix (Fin n) (Fin n) ℝ)) f = α • f := by
      simp [Matrix.toEuclideanLin]
    rw [hmat, real_inner_smul_left, real_inner_self_eq_norm_sq]
    simp [penalty]
    ring
  have hPenaltyMatrix :
      (α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
    simpa using
      (Matrix.PosDef.smul (x := (1 : Matrix (Fin n) (Fin n) ℝ))
        Matrix.PosDef.one hα)
  have hPenaltyStrictUniv : StrictConvexOn ℝ Set.univ penalty := by
    rw [hPenaltyEq]
    exact
      QuadraticOptimization.strictConvexOn_quadraticFunctional_of_posDef
        (0 : ℝ) (0 : EuclideanSpace ℝ (Fin n))
        (α • (1 : Matrix (Fin n) (Fin n) ℝ)) hPenaltyMatrix
  have hPenaltyStrict : StrictConvexOn ℝ s penalty :=
    hPenaltyStrictUniv.subset (by intro f hf; simp) hsConvex
  have hObjectiveEq :
      example91LikelihoodFunctional n K d σ2 α =
        (fun f : EuclideanSpace ℝ (Fin n) ↦
          (∑ i : Fin n, coordTerm i f) + penalty f) := by
    funext f
    simp [example91LikelihoodFunctional_def, coordTerm, penalty, a]
  rw [hObjectiveEq]
  exact hDataConvex.add_strictConvexOn hPenaltyStrict

/-- Helper for Example 9.1-extra-1: the shifted likelihood objective admits an
explicit feasible-set lower bound consisting of a constant log term plus the
quadratic penalty. -/
lemma example91LikelihoodLowerBoundOnFeasible
    (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 α : ℝ)
    (hpos :
      ∀ f : EuclideanSpace ℝ (Fin n),
        f ∈ NonnegativeOrthant.feasibleSet n →
          ∀ i : Fin n, 0 < Matrix.toEuclideanLin K f i + σ2) :
    ∀ f : EuclideanSpace ℝ (Fin n),
      f ∈ NonnegativeOrthant.feasibleSet n →
        (∑ i : Fin n,
          ((max (d i) 0 + σ2) - (max (d i) 0 + σ2) * Real.log (max (d i) 0 + σ2))) +
          (α / 2) * ‖f‖ ^ 2 ≤
          example91LikelihoodFunctional n K d σ2 α f := by
  let s : Set (EuclideanSpace ℝ (Fin n)) := NonnegativeOrthant.feasibleSet n
  have h0_mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ s := by
    simp [s, NonnegativeOrthant.mem_feasibleSet]
  intro f hf
  have hcoord :
      ∀ i : Fin n,
        ((max (d i) 0 + σ2) - (max (d i) 0 + σ2) * Real.log (max (d i) 0 + σ2)) ≤
          (Matrix.toEuclideanLin K f i + σ2) -
            (max (d i) 0 + σ2) * Real.log (Matrix.toEuclideanLin K f i + σ2) := by
    intro i
    have hai : 0 < max (d i) 0 + σ2 := by
      have hσ2 : 0 < σ2 := by
        simpa using (hpos 0 h0_mem i)
      exact add_pos_of_nonneg_of_pos (le_max_right _ _) hσ2
    exact shiftedPoissonCoordinateTerm_le_of_pos hai (hpos f hf i)
  have hsum :
      (∑ i : Fin n,
        ((max (d i) 0 + σ2) - (max (d i) 0 + σ2) * Real.log (max (d i) 0 + σ2))) ≤
        ∑ i : Fin n,
          ((Matrix.toEuclideanLin K f i + σ2) -
            (max (d i) 0 + σ2) * Real.log (Matrix.toEuclideanLin K f i + σ2)) := by
    exact Finset.sum_le_sum fun i _ ↦ hcoord i
  have hpen :
      (∑ i : Fin n,
        ((max (d i) 0 + σ2) - (max (d i) 0 + σ2) * Real.log (max (d i) 0 + σ2))) +
          (α / 2) * ‖f‖ ^ 2 ≤
        (∑ i : Fin n,
          ((Matrix.toEuclideanLin K f i + σ2) -
            (max (d i) 0 + σ2) * Real.log (Matrix.toEuclideanLin K f i + σ2))) +
          (α / 2) * ‖f‖ ^ 2 := by
    simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hsum ((α / 2) * ‖f‖ ^ 2)
  simpa [example91LikelihoodFunctional_def, s, sub_eq_add_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, add_assoc, add_left_comm,
    add_comm]
    using hpen

/-- Example 9.1-extra-1 (9). The nonnegative likelihood problem
`(9.4)`-`(9.5)`
has a unique minimizer on `NonnegativeOrthant.feasibleSet n` when `α > 0` and
every feasible point stays in the positive log domain. -/
theorem example91ExistsUniqueLikelihoodMinimizer
    (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 α : ℝ)
    (hα : 0 < α)
    (hpos :
      ∀ f : EuclideanSpace ℝ (Fin n),
        f ∈ NonnegativeOrthant.feasibleSet n →
          ∀ i : Fin n, 0 < Matrix.toEuclideanLin K f i + σ2) :
    ∃! f : EuclideanSpace ℝ (Fin n),
      f ∈ NonnegativeOrthant.feasibleSet n ∧
        IsMinOn (example91LikelihoodFunctional n K d σ2 α)
          (NonnegativeOrthant.feasibleSet n) f := by
  let J : EuclideanSpace ℝ (Fin n) → ℝ := example91LikelihoodFunctional n K d σ2 α
  let s : Set (EuclideanSpace ℝ (Fin n)) := NonnegativeOrthant.feasibleSet n
  let a : Fin n → ℝ := fun i ↦ max (d i) 0 + σ2
  let L : ℝ := ∑ i : Fin n, (a i - a i * Real.log (a i))
  have hJ_cont : ContinuousOn J s :=
    example91LikelihoodContinuousOnFeasible n K d σ2 α hpos
  have hJ_strict : StrictConvexOn ℝ s J :=
    example91LikelihoodStrictConvexOnFeasible n K d σ2 α hα hpos
  have h0_mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ s := by
    simp [s, NonnegativeOrthant.mem_feasibleSet]
  have hLower :
      ∀ f : EuclideanSpace ℝ (Fin n),
        f ∈ s → L + (α / 2) * ‖f‖ ^ 2 ≤ J f := by
    simpa [J, s, a, L] using
      (example91LikelihoodLowerBoundOnFeasible n K d σ2 α hpos)
  let B : ℝ := |J 0 - L| + 1
  let R : ℝ := max 1 (2 * B / α + 1)
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith [le_max_left (1 : ℝ) (2 * B / α + 1)]
  have h0_ball : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall 0 R := by
    simp [Metric.mem_closedBall, hR_pos.le]
  have hCompact : IsCompact (s ∩ Metric.closedBall 0 R) := by
    have hClosed : IsClosed (s ∩ Metric.closedBall 0 R) :=
      (NonnegativeOrthant.closedConvex_feasibleSet n).isClosed.inter Metric.isClosed_closedBall
    exact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).of_isClosed_subset
        hClosed (by intro f hf; exact hf.2)
  obtain ⟨fStar, hfStar_mem, hfStar_min⟩ :=
    hCompact.exists_isMinOn ⟨0, ⟨h0_mem, h0_ball⟩⟩
      (hJ_cont.mono (by intro f hf; exact hf.1))
  have hfStar_feasible : fStar ∈ s := hfStar_mem.1
  have hfStar_le_zero : J fStar ≤ J 0 := hfStar_min ⟨h0_mem, h0_ball⟩
  have hGlobalMin : IsMinOn J s fStar := by
    intro f hf
    by_cases hfBall : f ∈ Metric.closedBall 0 R
    · exact hfStar_min ⟨hf, hfBall⟩
    · have hR_lt_norm : R < ‖f‖ := by
        have hfBall' : ¬ ‖f‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hfBall
        exact lt_of_not_ge hfBall'
      have hBig : 2 * B / α < ‖f‖ := by
        have hAux : 2 * B / α + 1 ≤ R := le_max_right (1 : ℝ) (2 * B / α + 1)
        linarith
      have hNorm_gt_one : 1 < ‖f‖ := by
        have hOne : 1 ≤ R := le_max_left (1 : ℝ) (2 * B / α + 1)
        linarith
      have hNorm_sq : ‖f‖ < ‖f‖ ^ 2 := by
        nlinarith
      have hPenaltyBig : B < (α / 2) * ‖f‖ ^ 2 := by
        have hBigSq : 2 * B / α < ‖f‖ ^ 2 := lt_trans hBig hNorm_sq
        have hBigMulSq : 2 * B < α * ‖f‖ ^ 2 := by
          have htmp : 2 * B < ‖f‖ ^ 2 * α := (div_lt_iff₀ hα).mp hBigSq
          simpa [mul_comm] using htmp
        nlinarith [hBigMulSq]
      have hZero_lt_B : J 0 < L + B := by
        dsimp [B]
        linarith [le_abs_self (J 0 - L)]
      have hLB_lt_Jf : L + B < J f := by
        have hLB_lt_pen : L + B < L + (α / 2) * ‖f‖ ^ 2 := by
          linarith
        exact lt_of_lt_of_le hLB_lt_pen (hLower f hf)
      have hZero_lt_Jf : J 0 < J f := lt_trans hZero_lt_B hLB_lt_Jf
      exact hfStar_le_zero.trans hZero_lt_Jf.le
  refine ⟨fStar, ⟨hfStar_feasible, hGlobalMin⟩, ?_⟩
  intro g hg
  exact hJ_strict.eq_of_isMinOn hg.2 hGlobalMin hg.1 hfStar_feasible
