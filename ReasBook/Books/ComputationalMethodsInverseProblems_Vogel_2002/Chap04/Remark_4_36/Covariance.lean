/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_12.Covariance
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Notation

public section

noncomputable section

open scoped Matrix ProbabilityTheory

namespace ProbabilityTheory

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n] [DecidableEq n]
variable {m : Type w} [Fintype m]

/-- The linear model `Z = fun ω ↦ K.toEuclideanLin (X ω) + N ω` identifies the
cross-covariance of `X` with `Z` as `C_X * Kᵀ` when `X` and `N` are independent,
centered, and have covariance matrix `C_X` for `X`. -/
theorem crossCovarianceMatrix_linearModel
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {N Z : Ω → EuclideanSpace ℝ m}
    {K : Matrix m n ℝ} {C_X : Matrix n n ℝ}
    (hX_memLp : MeasureTheory.MemLp X 2 μ)
    (hN_memLp : MeasureTheory.MemLp N 2 μ)
    (h_indep : ProbabilityTheory.IndepFun X N μ)
    (hX_cov : covarianceMatrix μ X = C_X)
    (h_model : Z = fun ω ↦ K.toEuclideanLin (X ω) + N ω) :
    crossCovarianceMatrix μ X Z = C_X * Kᵀ := by
  have hXcoord : ∀ i, MeasureTheory.MemLp (fun ω ↦ X ω i) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hX_memLp
  have hNcoord : ∀ j, MeasureTheory.MemLp (fun ω ↦ N ω j) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hN_memLp
  have hXcovEntry :
      ∀ a b, cov[fun ω ↦ X ω a, fun ω ↦ X ω b; μ] = C_X a b := by
    intro a b
    simpa [covarianceMatrix_apply] using
      congrArg (fun M : Matrix n n ℝ ↦ M a b) hX_cov
  have hSignalCoord : ∀ j, MeasureTheory.MemLp (fun ω ↦ ∑ k, K j k * X ω k) 2 μ := by
    intro j
    convert
      (MeasureTheory.memLp_finsetSum' (μ := μ) (s := Finset.univ)
        (f := fun k ω ↦ K j k * X ω k)
        (fun k _ ↦ (hXcoord k).const_mul (K j k))) using 1
    ext ω
    simp
  ext i j
  rw [crossCovarianceMatrix_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [h_model]
  have hZj :
      (fun ω ↦ (K.toEuclideanLin (X ω) + N ω) j) =
        ((fun ω ↦ ∑ k, K j k * X ω k) + fun ω ↦ N ω j) := by
    funext ω
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [hZj]
  rw [covariance_add_right (hXcoord i) (hSignalCoord j) (hNcoord j)]
  have hNoise :
      cov[fun ω ↦ X ω i, fun ω ↦ N ω j; μ] = 0 := by
    have hMeasX :
        Measurable (fun x : EuclideanSpace ℝ n ↦ x.ofLp i) :=
      by
        fun_prop
    have hMeasN :
        Measurable (fun x : EuclideanSpace ℝ m ↦ x.ofLp j) :=
      by
        fun_prop
    have hNoiseComp :
        cov[(fun x : EuclideanSpace ℝ n ↦ x.ofLp i) ∘ X,
          (fun x : EuclideanSpace ℝ m ↦ x.ofLp j) ∘ N; μ] = 0 := by
      exact (h_indep.comp hMeasX hMeasN).covariance_eq_zero (hXcoord i) (hNcoord j)
    have hCovEq :
        cov[fun ω ↦ (X ω).ofLp i, fun ω ↦ (N ω).ofLp j; μ] =
          cov[(fun x : EuclideanSpace ℝ n ↦ x.ofLp i) ∘ X,
            (fun x : EuclideanSpace ℝ m ↦ x.ofLp j) ∘ N; μ] := by
      simp [ProbabilityTheory.covariance, Function.comp]
    exact hCovEq.trans hNoiseComp
  rw [hNoise, add_zero]
  rw [covariance_fun_sum_right (X := fun k ω ↦ K j k * X ω k)
    (fun k ↦ (hXcoord k).const_mul (K j k)) (hXcoord i)]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [covariance_const_mul_right, hXcovEntry i k]
  ring

/-- The linear model `Z = fun ω ↦ K.toEuclideanLin (X ω) + N ω` identifies the
covariance of `Z` as `K * C_X * Kᵀ + C_N` when `X` and `N` are independent,
centered, and have covariance matrices `C_X` and `C_N`. -/
theorem covarianceMatrix_linearModel
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {N Z : Ω → EuclideanSpace ℝ m}
    {K : Matrix m n ℝ} {C_X : Matrix n n ℝ} {C_N : Matrix m m ℝ}
    (hX_memLp : MeasureTheory.MemLp X 2 μ)
    (hN_memLp : MeasureTheory.MemLp N 2 μ)
    (h_indep : ProbabilityTheory.IndepFun X N μ)
    (hX_cov : covarianceMatrix μ X = C_X)
    (hN_cov : covarianceMatrix μ N = C_N)
    (h_model : Z = fun ω ↦ K.toEuclideanLin (X ω) + N ω) :
    covarianceMatrix μ Z = K * C_X * Kᵀ + C_N := by
  have hXcoord : ∀ i, MeasureTheory.MemLp (fun ω ↦ X ω i) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hX_memLp
  have hNcoord : ∀ j, MeasureTheory.MemLp (fun ω ↦ N ω j) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hN_memLp
  have hXcovEntry :
      ∀ a b, cov[fun ω ↦ X ω a, fun ω ↦ X ω b; μ] = C_X a b := by
    intro a b
    simpa [covarianceMatrix_apply] using
      congrArg (fun M : Matrix n n ℝ ↦ M a b) hX_cov
  have hNcovEntry :
      ∀ a b, cov[fun ω ↦ N ω a, fun ω ↦ N ω b; μ] = C_N a b := by
    intro a b
    simpa [covarianceMatrix_apply] using
      congrArg (fun M : Matrix m m ℝ ↦ M a b) hN_cov
  have hSignalCoord : ∀ j, MeasureTheory.MemLp (fun ω ↦ ∑ k, K j k * X ω k) 2 μ := by
    intro j
    convert
      (MeasureTheory.memLp_finsetSum' (μ := μ) (s := Finset.univ)
        (f := fun k ω ↦ K j k * X ω k)
        (fun k _ ↦ (hXcoord k).const_mul (K j k))) using 1
    ext ω
    simp
  have hSignalNoise :
      ∀ i j, cov[fun ω ↦ ∑ k, K i k * X ω k, fun ω ↦ N ω j; μ] = 0 := by
    intro i j
    rw [covariance_fun_sum_left (X := fun k ω ↦ K i k * X ω k)
      (fun k ↦ (hXcoord k).const_mul (K i k)) (hNcoord j)]
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hMeasX :
        Measurable (fun x : EuclideanSpace ℝ n ↦ x.ofLp k) :=
      by
        fun_prop
    have hMeasN :
        Measurable (fun x : EuclideanSpace ℝ m ↦ x.ofLp j) :=
      by
        fun_prop
    have hNoiseComp :
        cov[(fun x : EuclideanSpace ℝ n ↦ x.ofLp k) ∘ X,
          (fun x : EuclideanSpace ℝ m ↦ x.ofLp j) ∘ N; μ] = 0 := by
      exact (h_indep.comp hMeasX hMeasN).covariance_eq_zero (hXcoord k) (hNcoord j)
    rw [covariance_const_mul_left]
    rw [show cov[fun ω ↦ X ω k, fun ω ↦ N ω j; μ] = 0 by
      have hCovEq :
          cov[fun ω ↦ (X ω).ofLp k, fun ω ↦ (N ω).ofLp j; μ] =
            cov[(fun x : EuclideanSpace ℝ n ↦ x.ofLp k) ∘ X,
              (fun x : EuclideanSpace ℝ m ↦ x.ofLp j) ∘ N; μ] := by
        simp [ProbabilityTheory.covariance, Function.comp]
      exact hCovEq.trans hNoiseComp]
    ring
  have hSignalSignal :
      ∀ i j,
        cov[fun ω ↦ ∑ k, K i k * X ω k, fun ω ↦ ∑ l, K j l * X ω l; μ] =
          (K * C_X * Kᵀ) i j := by
    intro i j
    rw [covariance_fun_sum_fun_sum
      (X := fun k ω ↦ K i k * X ω k)
      (Y := fun l ω ↦ K j l * X ω l)
      (fun k ↦ (hXcoord k).const_mul (K i k))
      (fun l ↦ (hXcoord l).const_mul (K j l))]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right, hXcovEntry]
    have hMatrixExpansion :
        (K * C_X * Kᵀ) i j = ∑ b, ∑ a, K i a * (C_X a b * K j b) := by
      simp [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, mul_left_comm, mul_comm]
    calc
      ∑ a, ∑ b, K i a * (K j b * C_X a b)
          = ∑ a, ∑ b, K i a * C_X a b * K j b := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            refine Finset.sum_congr rfl ?_
            intro b hb
            ring
      _ = ∑ b, ∑ a, K i a * (C_X a b * K j b) := by
            rw [Finset.sum_comm]
            simp [mul_assoc]
      _ = (K * C_X * Kᵀ) i j := by
            symm
            exact hMatrixExpansion
  ext i j
  rw [covarianceMatrix_apply, Matrix.add_apply]
  rw [h_model]
  have hZi :
      (fun ω ↦ (K.toEuclideanLin (X ω) + N ω) i) =
        ((fun ω ↦ ∑ k, K i k * X ω k) + fun ω ↦ N ω i) := by
    funext ω
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  have hZj :
      (fun ω ↦ (K.toEuclideanLin (X ω) + N ω) j) =
        ((fun ω ↦ ∑ k, K j k * X ω k) + fun ω ↦ N ω j) := by
    funext ω
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [hZi, hZj]
  rw [covariance_add_left (hSignalCoord i) (hNcoord i) ((hSignalCoord j).add (hNcoord j))]
  rw [covariance_add_right (hSignalCoord i) (hSignalCoord j) (hNcoord j)]
  rw [covariance_add_right (hNcoord i) (hSignalCoord j) (hNcoord j)]
  rw [hSignalSignal i j, hSignalNoise i j, covariance_comm, hSignalNoise j i]
  rw [hNcovEntry i j]
  ring

end

end ProbabilityTheory
