/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_12
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Exercise_4_4.Moments

public section

noncomputable section

open scoped ProbabilityTheory NNReal

namespace ProbabilityTheory

universe u v

/-- Helper for Exercise 4.4: the identity random variable is integrable under the real-valued
Poisson law `Po(ℝ, r)`. -/
lemma integrable_id_mapCastPoissonMeasure (r : ℝ≥0) :
    MeasureTheory.Integrable (fun x : ℝ ↦ x) Po(ℝ, r) := by
  -- First prove integrability for the scalar Poisson law on `ℕ`.
  have h_nat : MeasureTheory.Integrable (fun n : ℕ ↦ (n : ℝ)) Po(r) := by
    rw [integrable_poissonMeasure_iff]
    let a : ℕ → ℝ :=
      fun n ↦ Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ) * ‖(n : ℝ)‖
    change Summable a
    exact (summable_nat_add_iff 1 (f := a)).1 <| by
      have hs :
          Summable (fun n : ℕ ↦
            (Real.exp (-(r : ℝ)) * (r : ℝ)) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ))) := by
        simpa [mul_assoc] using
          (Real.summable_pow_div_factorial (r : ℝ)).mul_left
            (Real.exp (-(r : ℝ)) * (r : ℝ))
      have hshift :
          (fun n : ℕ ↦ a (n + 1)) =
            fun n : ℕ ↦
              (Real.exp (-(r : ℝ)) * (r : ℝ)) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
        funext n
        have habs : |((n + 1 : ℕ) : ℝ)| = (n : ℝ) + 1 := by
          rw [abs_of_nonneg]
          · norm_num
          · positivity
        dsimp [a]
        rw [habs, pow_succ, Nat.factorial_succ, Nat.cast_mul]
        have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp [hn]
        rw [Nat.cast_add, Nat.cast_one]
      -- Shift the series once so that the extra factor `n` cancels against `(n + 1)!`.
      rwa [hshift]
  -- Then transport integrability along the map description of `Po(ℝ, r)`.
  exact (MeasureTheory.integrable_map_measure aestronglyMeasurable_id (by fun_prop)).2 h_nat

/-- Helper for Exercise 4.4: the centered identity random variable has mean zero under
`Po(ℝ, r)`. -/
lemma integral_centered_id_mapCastPoissonMeasure_eq_zero (r : ℝ≥0) :
    ∫ x, (x - (r : ℝ)) ∂Po(ℝ, r) = 0 := by
  -- Compute the centered first moment by linearity and the scalar Poisson expectation formula.
  rw [MeasureTheory.integral_sub (integrable_id_mapCastPoissonMeasure r)
    (MeasureTheory.integrable_const _)]
  rw [integral_id_map_cast_poissonMeasure]
  simp

/-- Helper for Exercise 4.4: a real random variable with Poisson law `Po(ℝ, r)` has covariance
with itself equal to the rate `r`. -/
lemma poissonCoordinateCovarianceSelf_eq_rate
    {Ω : Type u} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {r : ℝ≥0} (hY : HasLaw Y Po(ℝ, r) μ) :
    cov[Y, Y; μ] = (r : ℝ) := by
  -- Rewrite covariance as variance and transport the scalar variance along the law.
  rw [covariance_self hY.aemeasurable, hY.variance_eq, variance_id_map_cast_poissonMeasure]

/-- Mean-vector formula for Exercise 4.4. If the coordinates of a finite real-valued random
vector are independent and `X i` has Poisson law `Po(ℝ, λ i)` for each `i`, then its mean
vector is `fun i ↦ (rate i : ℝ)`. -/
theorem poissonVector_mean_eq
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ ι} {rate : ι → ℝ≥0}
    (h_poisson : ∀ i, HasLaw (fun ω ↦ X ω i) Po(ℝ, rate i) μ) :
    μ[X] = fun i ↦ (rate i : ℝ) := by
  -- First pull scalar integrability back along each coordinate law.
  have h_coord_int : ∀ i, MeasureTheory.Integrable (fun ω ↦ X ω i) μ := by
    intro i
    have hid : MeasureTheory.Integrable (fun x : ℝ ↦ x) Po(ℝ, rate i) :=
      integrable_id_mapCastPoissonMeasure (rate i)
    rw [← (h_poisson i).map_eq] at hid
    exact (MeasureTheory.integrable_map_measure aestronglyMeasurable_id
      (h_poisson i).aemeasurable).1 hid
  have hX_int : MeasureTheory.Integrable X μ :=
    MeasureTheory.Integrable.of_eval_piLp h_coord_int
  ext i
  -- Compare the `i`-th coordinate of the mean vector with the scalar Poisson expectation.
  have hcoord : μ[fun ω ↦ X ω i] = (rate i : ℝ) := by
    calc
      μ[fun ω ↦ X ω i] = ∫ x, x ∂Po(ℝ, rate i) := (h_poisson i).integral_eq
      _ = (rate i : ℝ) := integral_id_map_cast_poissonMeasure (rate i)
  have hproj : (∫ x, (X x).ofLp ∂μ) i = μ[fun ω ↦ X ω i] := by
    simpa using
      (MeasureTheory.eval_integral (f := fun ω ↦ (X ω).ofLp) h_coord_int i)
  exact hproj.trans hcoord

/-- Exercise 4.4 (2). If the coordinates of a finite real-valued random vector are
independent and `X i` has Poisson law `Po(ℝ, λ i)` for each `i`, then its covariance
matrix is `Matrix.diagonal (fun i ↦ (λ i : ℝ))`. -/
theorem poissonVector_covarianceMatrix_eq_diagonal
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [DecidableEq ι]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ ι} {rate : ι → ℝ≥0}
    (h_indep : iIndepFun (fun i ω ↦ X ω i) μ)
    (h_poisson : ∀ i, HasLaw (fun ω ↦ X ω i) Po(ℝ, rate i) μ) :
    covarianceMatrix μ X =
      Matrix.diagonal (fun i ↦ (rate i : ℝ)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    -- On the diagonal, each entry is the scalar covariance of a Poisson coordinate.
    rw [covarianceMatrix_apply]
    simpa [Matrix.diagonal_apply] using
      poissonCoordinateCovarianceSelf_eq_rate (h_poisson i)
  · -- Off the diagonal, transport to the product Poisson law and factor the centered product.
    rw [covarianceMatrix_apply, Matrix.diagonal_apply, if_neg hij]
    have hmean_i : μ[fun ω ↦ X ω i] = (rate i : ℝ) := by
      calc
        μ[fun ω ↦ X ω i] = ∫ x, x ∂Po(ℝ, rate i) := (h_poisson i).integral_eq
        _ = (rate i : ℝ) := integral_id_map_cast_poissonMeasure (rate i)
    have hmean_j : μ[fun ω ↦ X ω j] = (rate j : ℝ) := by
      calc
        μ[fun ω ↦ X ω j] = ∫ x, x ∂Po(ℝ, rate j) := (h_poisson j).integral_eq
        _ = (rate j : ℝ) := integral_id_map_cast_poissonMeasure (rate j)
    let centeredProd : ℝ × ℝ → ℝ :=
      fun z ↦ (z.1 - (rate i : ℝ)) * (z.2 - (rate j : ℝ))
    have h_pair :
        HasLaw (fun ω ↦ (X ω i, X ω j)) (Po(ℝ, rate i).prod Po(ℝ, rate j)) μ :=
      (h_indep.indepFun hij).hasLaw_prod (h_poisson i) (h_poisson j)
    calc
      cov[fun ω ↦ X ω i, fun ω ↦ X ω j; μ]
          = μ[fun ω ↦ centeredProd (X ω i, X ω j)] := by
              simp [ProbabilityTheory.covariance, centeredProd, hmean_i, hmean_j]
      _ = ∫ z, centeredProd z ∂(Po(ℝ, rate i).prod Po(ℝ, rate j)) := by
            simpa [centeredProd, Function.comp_def] using
              h_pair.integral_comp (f := centeredProd) (by fun_prop)
      _ = (∫ x, (x - (rate i : ℝ)) ∂Po(ℝ, rate i)) *
            ∫ y, (y - (rate j : ℝ)) ∂Po(ℝ, rate j) := by
              simpa [centeredProd] using
                (MeasureTheory.integral_prod_mul
                  (μ := Po(ℝ, rate i)) (ν := Po(ℝ, rate j))
                  (fun x : ℝ ↦ x - (rate i : ℝ))
                  (fun y : ℝ ↦ y - (rate j : ℝ)))
      _ = 0 := by
            rw [integral_centered_id_mapCastPoissonMeasure_eq_zero,
              integral_centered_id_mapCastPoissonMeasure_eq_zero]
            simp

end ProbabilityTheory
