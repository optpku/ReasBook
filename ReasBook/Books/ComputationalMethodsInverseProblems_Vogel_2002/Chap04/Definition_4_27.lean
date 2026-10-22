/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_12.Covariance
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_27.SecondMoment
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_27.CrossCorrelation
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

public section

noncomputable section

open scoped ProbabilityTheory

namespace ProbabilityTheory

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v}
variable {m : Type w}
variable {μ : MeasureTheory.Measure Ω}
variable {X : Ω → EuclideanSpace ℝ n}
variable {Z : Ω → EuclideanSpace ℝ m}

/-
Definition 4.27 (1). The textbook cross-correlation matrix `Γ[X, Z; μ]` is the canonical
owner `ProbabilityTheory.crossCorrelationMatrix μ X Z`.
-/
#check (Γ[X, Z; μ])

/-
Definition 4.27 (2). The entry formula for `Γ[X, Z; μ]` is
`ProbabilityTheory.crossCorrelationMatrix_apply`.
-/
#check ProbabilityTheory.crossCorrelationMatrix_apply

/- Definition 4.27 (3). The textbook autocorrelation matrix `Γ[X; μ]`, i.e. `ΓXX`, is the
canonical owner `ProbabilityTheory.secondMomentMatrix μ X`, with entry theorem
`ProbabilityTheory.secondMomentMatrix_apply`. -/
#check (Γ[X; μ])
#check ProbabilityTheory.secondMomentMatrix_apply

/-
Definition 4.27 (4). Swapping the random vectors transposes `Γ[X, Z; μ]`.
-/
#check ProbabilityTheory.crossCorrelationMatrix_transpose

end

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v}
variable {μ : MeasureTheory.Measure Ω}
variable {X : Ω → EuclideanSpace ℝ n}

/- The square self-case identifies `Γ[X, X; μ]` with `Γ[X; μ]`. -/
#check ProbabilityTheory.crossCorrelationMatrix_self

/-- Helper for Definition 4.27: the quadratic form of `Γ[X; μ]` along a finitely supported
coefficient vector is the expected square of the corresponding scalar projection. -/
lemma secondMomentMatrixQuadraticForm_eq_integral_sq
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n}
    (hX : ∀ i, MeasureTheory.MemLp (fun ω ↦ X ω i) 2 μ)
    (x : n →₀ ℝ) :
    x.sum (fun i xi ↦ x.sum (fun j xj ↦ star xi * Γ[X; μ] i j * xj)) =
      ∫ ω, (∑ i ∈ x.support, x i * X ω i) ^ 2 ∂μ := by
  classical
  have hXi : ∀ i, MeasureTheory.MemLp (fun ω ↦ x i * X ω i) 2 μ := fun i ↦
    (hX i).const_mul (x i)
  calc
    x.sum (fun i xi ↦ x.sum (fun j xj ↦ star xi * Γ[X; μ] i j * xj))
        = x.support.sum fun i ↦ x.support.sum fun j ↦
            (x i * Γ[X; μ] i j) * x j := by
            simp [Finsupp.sum]
    _ = x.support.sum fun i ↦ x.support.sum fun j ↦
          ∫ ω, (x i * X ω i) * (x j * X ω j) ∂μ := by
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            refine Finset.sum_congr rfl fun j hj ↦ ?_
            rw [secondMomentMatrix_apply, ← MeasureTheory.integral_const_mul]
            have hmul :
                (fun ω ↦ x i * ((X ω).ofLp i * (X ω).ofLp j)) =
                  fun ω ↦ x i * (X ω).ofLp i * (X ω).ofLp j := by
              funext ω
              ring
            rw [hmul]
            have hmul_right :
                (∫ ω, x i * (X ω).ofLp i * (x j * (X ω).ofLp j) ∂μ) =
                  ∫ ω, (x i * (X ω).ofLp i * (X ω).ofLp j) * x j ∂μ := by
              congr 1 with ω
              ring
            rw [hmul_right, MeasureTheory.integral_mul_const]
    _ = ∫ ω, ∑ i ∈ x.support, ∑ j ∈ x.support, (x i * X ω i) * (x j * X ω j) ∂μ := by
          symm
          have hInner :
              ∀ i ∈ x.support, MeasureTheory.Integrable
                (fun ω ↦ ∑ j ∈ x.support, (x i * X ω i) * (x j * X ω j)) μ := by
            intro i hi
            exact MeasureTheory.integrable_finsetSum _ fun j hj ↦ (hXi i).integrable_mul (hXi j)
          calc
            ∫ ω, ∑ i ∈ x.support, ∑ j ∈ x.support, (x i * X ω i) * (x j * X ω j) ∂μ
                = ∑ i ∈ x.support, ∫ ω, ∑ j ∈ x.support, (x i * X ω i) * (x j * X ω j) ∂μ := by
                    simpa using
                      (MeasureTheory.integral_finsetSum x.support hInner)
            _ = ∑ i ∈ x.support, ∑ j ∈ x.support, ∫ ω, (x i * X ω i) * (x j * X ω j) ∂μ := by
                  refine Finset.sum_congr rfl fun i hi ↦ ?_
                  simpa using
                    (MeasureTheory.integral_finsetSum x.support
                      (fun j hj ↦ (hXi i).integrable_mul (hXi j)))
    _ = ∫ ω, (∑ i ∈ x.support, x i * X ω i) * (∑ j ∈ x.support, x j * X ω j) ∂μ := by
          congr 1 with ω
          symm
          rw [Finset.sum_mul]
          simp_rw [Finset.mul_sum]
    _ = ∫ ω, (∑ i ∈ x.support, x i * X ω i) ^ 2 ∂μ := by
          congr 1 with ω
          ring

/-- Definition 4.27 (5). The autocorrelation matrix `Γ[X; μ]` is symmetric. -/
theorem secondMomentMatrix_isSymm
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n} :
    Matrix.IsSymm Γ[X; μ] :=
  secondMomentMatrix_transpose

/-- Definition 4.27 (6). Under a finite second-moment hypothesis, the autocorrelation matrix
`Γ[X; μ]` is positive semidefinite. -/
theorem secondMomentMatrix_posSemidef
    [Fintype n] {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n}
    (hX : MeasureTheory.MemLp X 2 μ) :
    Matrix.PosSemidef Γ[X; μ] := by
  have hXcoord : ∀ i, MeasureTheory.MemLp (fun ω ↦ X ω i) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hX
  refine ⟨?_, ?_⟩
  · simpa using (secondMomentMatrix_isSymm : Matrix.IsSymm Γ[X; μ])
  · intro x
    rw [secondMomentMatrixQuadraticForm_eq_integral_sq hXcoord x]
    exact MeasureTheory.integral_nonneg fun ω ↦ by positivity

section

variable [Fintype n]

/-- Definition 4.27 (7). If `μ[X] = 0`, then the autocorrelation matrix reduces to the
centered covariance matrix `covarianceMatrix μ X`. -/
theorem secondMomentMatrix_eq_covarianceMatrix_of_mean_zero
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} (hX : MeasureTheory.MemLp X 2 μ) (h_mean_zero : μ[X] = 0) :
    Γ[X; μ] = covarianceMatrix μ X := by
  have hXcoord : ∀ k, MeasureTheory.MemLp (fun ω ↦ X ω k) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hX
  ext i j
  have hXi : μ[fun ω ↦ X ω i] = 0 := by
    simpa [MeasureTheory.eval_integral_piLp
      (fun k ↦ (hXcoord k).integrable (by norm_num)) i] using
      congrArg (fun x : EuclideanSpace ℝ n ↦ x i) h_mean_zero
  have hXj : μ[fun ω ↦ X ω j] = 0 := by
    simpa [MeasureTheory.eval_integral_piLp
      (fun k ↦ (hXcoord k).integrable (by norm_num)) j] using
      congrArg (fun x : EuclideanSpace ℝ n ↦ x j) h_mean_zero
  rw [secondMomentMatrix_apply, covarianceMatrix_apply]
  rw [ProbabilityTheory.covariance_eq_sub (hXcoord i) (hXcoord j)]
  simp [hXi, hXj]

end

end

end ProbabilityTheory
