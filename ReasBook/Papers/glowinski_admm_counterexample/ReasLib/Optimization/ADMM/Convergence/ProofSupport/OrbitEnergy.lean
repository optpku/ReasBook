/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.StorageDynamics
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open scoped BigOperators

namespace ADMM.ConvergenceProof

/-- The coordinate square, independent of the supremum norm instance on
`Fin m → ℝ`, used by the finite-memory certificates. -/
def coordinateSquare {m : ℕ} (x : Fin m → ℝ) : ℝ := dotProduct x x

lemma coordinateSquare_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ coordinateSquare x := by
  unfold coordinateSquare dotProduct
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (x i)

/-- Exact energy identity for one reduced ADMM step, in the certificate's
coordinates `η = -v` and `w = u / γ`. -/
theorem reduced_energy_identity {m : ℕ} (γ : ℝ)
    (η₀ η₁ w₀ w₁ : Fin m → ℝ) :
    (γ ^ 2 * coordinateSquare w₁ + γ * coordinateSquare η₁) -
      (γ ^ 2 * coordinateSquare w₀ + γ * coordinateSquare η₀) =
    -2 * γ *
      (dotProduct (η₀ - γ • w₀ - (η₁ + (w₁ - w₀))) (η₁ + (w₁ - w₀)) +
        dotProduct (γ • w₀ + (w₁ - w₀)) η₁) -
      γ * coordinateSquare (η₁ - η₀) -
      2 * γ * dotProduct (η₁ - η₀) (w₁ - w₀) -
      γ * (2 - γ) * coordinateSquare (w₁ - w₀) := by
  simp only [coordinateSquare, add_dotProduct, sub_dotProduct, dotProduct_add,
    dotProduct_sub, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm η₀ η₁, dotProduct_comm η₀ w₁, dotProduct_comm η₀ w₀,
    dotProduct_comm η₁ w₁, dotProduct_comm η₁ w₀, dotProduct_comm w₀ w₁]
  ring

/-- Young's inequality in coordinate squares with the constants used by the
ADMM energy estimate. -/
theorem coordinate_young_bound {m : ℕ} (d r : Fin m → ℝ) :
    -2 * dotProduct d r ≤ coordinateSquare d / 2 + 2 * coordinateSquare r := by
  have h := coordinateSquare_nonneg (d + (2 : ℝ) • r)
  simp only [coordinateSquare, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul] at h
  rw [dotProduct_comm r d] at h
  dsimp only [coordinateSquare]
  nlinarith

/-- The exact reduced energy identity controls increment squares and the two
monotonicity pairings, with the residual square as a summable forcing term. -/
theorem reduced_energy_descent {m : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (η₀ η₁ w₀ w₁ : Fin m → ℝ) :
    (γ ^ 2 * coordinateSquare w₁ + γ * coordinateSquare η₁) +
      (γ / 2) * coordinateSquare (η₁ - η₀) +
      2 * γ *
        (dotProduct (η₀ - γ • w₀ - (η₁ + (w₁ - w₀))) (η₁ + (w₁ - w₀)) +
          dotProduct (γ • w₀ + (w₁ - w₀)) η₁) ≤
    (γ ^ 2 * coordinateSquare w₀ + γ * coordinateSquare η₀) +
      γ ^ 2 * coordinateSquare (w₁ - w₀) := by
  have hid := reduced_energy_identity γ η₀ η₁ w₀ w₁
  have hyoung := mul_le_mul_of_nonneg_left (coordinate_young_bound (η₁ - η₀)
    (w₁ - w₀)) hγ
  nlinarith

/-- Summable residuals and nonnegative graph pairings give square-summable
second-image increments. This is the analytic consequence of the exact
energy identity needed before identifying cluster points. -/
theorem reduced_increment_summable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (η w : ℕ → Fin m → ℝ)
    (hpair : ∀ k, 0 ≤
      dotProduct (η k - γ • w k - (η (k + 1) + (w (k + 1) - w k)))
        (η (k + 1) + (w (k + 1) - w k)) +
      dotProduct (γ • w k + (w (k + 1) - w k)) (η (k + 1)))
    (hres : Summable (fun k ↦ coordinateSquare (w (k + 1) - w k))) :
    Summable (fun k ↦ coordinateSquare (η (k + 1) - η k)) := by
  let L : ℕ → ℝ := fun k ↦ γ ^ 2 * coordinateSquare (w k) +
    γ * coordinateSquare (η k)
  have hL : ∀ k, 0 ≤ L k := by
    intro k
    exact add_nonneg (mul_nonneg (sq_nonneg _) (coordinateSquare_nonneg _))
      (mul_nonneg hγ.le (coordinateSquare_nonneg _))
  have hstep : ∀ k, L (k + 1) + (γ / 2) * coordinateSquare (η (k + 1) - η k) ≤
      L k + γ ^ 2 * coordinateSquare (w (k + 1) - w k) := by
    intro k
    have h := reduced_energy_descent hγ.le (η k) (η (k + 1)) (w k) (w (k + 1))
    have hnonneg := mul_nonneg (show 0 ≤ 2 * γ by positivity) (hpair k)
    dsimp only [L]
    linarith
  have hs := energy_forced_dissipation_summable hL
    (fun k ↦ mul_nonneg (by positivity) (coordinateSquare_nonneg _))
    (fun k ↦ mul_nonneg (sq_nonneg _) (coordinateSquare_nonneg _))
    (hres.mul_left (γ ^ 2)) hstep
  have hhalf : γ / 2 ≠ 0 := by positivity
  simpa only [← mul_assoc, inv_mul_cancel₀ hhalf, one_mul] using hs.mul_left (γ / 2)⁻¹

end ADMM.ConvergenceProof
