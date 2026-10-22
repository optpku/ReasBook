/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_2_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_4.QuadraticFunctional
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Theorem_3_7
public import Mathlib.LinearAlgebra.Eigenspace.Zero

public section

noncomputable section

open QuadraticOptimization

namespace ConjugateGradient

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Helper for Corollary 3.8: a positive-definite matrix acts injectively on
`EuclideanSpace` through `Matrix.toEuclideanLin`. -/
theorem eq_zero_of_toEuclideanLin_eq_zero_of_posDef
    (A : Matrix n n ℝ) (hA : A.PosDef) {x : EuclideanSpace ℝ n}
    (hx : A.toEuclideanLin x = 0) :
    x = 0 := by
  have hA_det : IsUnit A.det := by
    exact A.isUnit_iff_isUnit_det.mp hA.isUnit
  -- Apply the inverse matrix to transport the zero equation back to the vector.
  calc
    x = Matrix.toEuclideanLin (1 : Matrix n n ℝ) x := by
      simp
    _ = Matrix.toEuclideanLin (A⁻¹ * A) x := by
      rw [← Matrix.nonsing_inv_mul A hA_det]
    _ = Matrix.toEuclideanLin A⁻¹ (A.toEuclideanLin x) := by
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    _ = 0 := by
      simp [hx]

/-- Corollary 3.8. For a positive-definite matrix `A`, any right-hand side `b`,
and any initial guess `f₀`, the conjugate-gradient iterates reach the exact
solution `quadraticFunctionalMinimizer b A` of `A f = -b` in at most
`Fintype.card n` steps. -/
theorem terminates_at_exact_solution_from_any_initial_guess
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) :
    ∃ k ≤ Fintype.card n,
      (iterates A b f₀ k).solution = quadraticFunctionalMinimizer b A := by
  let k := Fintype.card n
  let φ : Module.End ℝ (EuclideanSpace ℝ n) := A.toEuclideanLin
  let χ : Polynomial ℝ := LinearMap.charpoly φ
  let q : Polynomial ℝ := Polynomial.C (χ.coeff 0)⁻¹ * χ
  have hχ0 : χ.coeff 0 ≠ 0 := by
    intro hzero
    obtain ⟨x, hx_ne, hx_zero⟩ :=
      (LinearMap.charpoly_constantCoeff_eq_zero_iff φ).mp (by
        simpa [χ] using hzero)
    exact hx_ne (eq_zero_of_toEuclideanLin_eq_zero_of_posDef A hA hx_zero)
  have hq0 : q.eval 0 = 1 := by
    -- Normalize the characteristic polynomial so its constant term is `1`.
    calc
      q.eval 0 = (χ.coeff 0)⁻¹ * χ.eval 0 := by
        simp [q]
      _ = (χ.coeff 0)⁻¹ * χ.coeff 0 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero]
      _ = 1 := by
        exact inv_mul_cancel₀ hχ0
  have hqdeg : q.degree ≤ k := by
    -- Scaling by a nonzero constant preserves the characteristic-polynomial degree.
    have hχnat : χ.natDegree ≤ k := by
      simpa [χ, φ, k] using (LinearMap.charpoly_natDegree (f := φ)).le
    have hχdeg : χ.degree ≤ k := Polynomial.degree_le_of_natDegree_le hχnat
    calc
      q.degree = χ.degree := by
        simpa [q] using Polynomial.degree_C_mul (p := χ) (a := (χ.coeff 0)⁻¹) (inv_ne_zero hχ0)
      _ ≤ k := hχdeg
  have hqaeval_zero : (Polynomial.aeval φ q) (initialError A b f₀) = 0 := by
    -- Cayley-Hamilton annihilates every vector under the normalized charpoly.
    have hqaeval : Polynomial.aeval φ q = 0 := by
      calc
        Polynomial.aeval φ q
            = (algebraMap ℝ (Module.End ℝ (EuclideanSpace ℝ n))) (χ.coeff 0)⁻¹ *
                Polynomial.aeval φ χ := by
              simp [q, map_mul]
        _ = (algebraMap ℝ (Module.End ℝ (EuclideanSpace ℝ n))) (χ.coeff 0)⁻¹ * 0 := by
              simp [χ, LinearMap.aeval_self_charpoly]
        _ = 0 := by simp
    simp [hqaeval]
  have hle :=
    energyNorm_error_le_aeval_initialError A b f₀ hA k q hq0 hqdeg
  have hkzero : energyNormError A b f₀ hA k = 0 := by
    have hnonneg : 0 ≤ energyNormError A b f₀ hA k := by
      rw [energyNormError_eq, Matrix.energyNorm_eq_sqrt_energyInner]
      exact Real.sqrt_nonneg _
    have hupper : energyNormError A b f₀ hA k ≤ 0 := by
      rw [hqaeval_zero] at hle
      simpa [Matrix.energyNorm_eq_sqrt_energyInner, Matrix.energyInner_eq] using hle
    exact le_antisymm hupper hnonneg
  have herr_zero : error A b f₀ k = 0 := by
    -- The spectral lower bound forces the Euclidean error norm to vanish.
    obtain hempty | hnonempty := isEmpty_or_nonempty n
    · exact Subsingleton.elim _ _
    · have henergy_zero : Matrix.energyNorm A hA (error A b f₀ k) = 0 := by
        simpa [energyNormError_eq] using hkzero
      have hsqrt_pos : 0 < Real.sqrt (sInf (spectrum ℝ A)) := by
        exact Real.sqrt_pos.mpr <|
          by simpa [Matrix.lambdaMin_eq_sInf_spectrum] using Matrix.lambdaMin_pos_of_posDef A hA
      have hbound := Matrix.energyNorm_lowerBound A hA (error A b f₀ k)
      have hnorm_zero : ‖error A b f₀ k‖ = 0 := by
        have hnorm_nonneg : 0 ≤ ‖error A b f₀ k‖ := norm_nonneg _
        rw [henergy_zero] at hbound
        nlinarith
      exact norm_eq_zero.mp hnorm_zero
  refine ⟨k, le_rfl, ?_⟩
  -- Unfold the error term to identify the iterate with the exact minimizer.
  exact sub_eq_zero.mp (by
    simpa [ConjugateGradient.error, QuadraticOptimization.error_eq_sub] using herr_zero)

/-- Companion to
`terminates_at_exact_solution_from_any_initial_guess`: the same terminating
index can be chosen so that the iterate is both the exact solution and a
solution of `A f = -b`. -/
theorem terminates_at_exact_solution_from_any_initial_guess_spec
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) :
    ∃ k ≤ Fintype.card n,
      (iterates A b f₀ k).solution = quadraticFunctionalMinimizer b A ∧
      A.toEuclideanLin ((iterates A b f₀ k).solution) = -b := by
  obtain ⟨k, hk, hkExact⟩ :=
    terminates_at_exact_solution_from_any_initial_guess A b f₀ hA
  refine ⟨k, hk, hkExact, ?_⟩
  rw [hkExact]
  rw [eq_neg_iff_add_eq_zero]
  simpa [add_comm] using quadraticFunctionalMinimizer_isCriticalPoint b A hA

/-- At the terminating index recorded by
`terminates_at_exact_solution_from_any_initial_guess_spec`, the
conjugate-gradient iterate solves the linear system `A f = -b`. -/
theorem solves_system_from_any_initial_guess
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) :
    ∃ k ≤ Fintype.card n,
      A.toEuclideanLin ((iterates A b f₀ k).solution) = -b := by
  obtain ⟨k, hk, -, hkSolve⟩ :=
    terminates_at_exact_solution_from_any_initial_guess_spec A b f₀ hA
  exact ⟨k, hk, hkSolve⟩

end ConjugateGradient
