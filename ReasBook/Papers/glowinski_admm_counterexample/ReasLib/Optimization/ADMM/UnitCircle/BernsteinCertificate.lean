/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace ADMM.UnitCircle

open scoped BigOperators Polynomial

/-- A polynomial presented in the degree-`n` Bernstein basis on `[0,1]`.
The data generator may propose coefficients; polynomial equality is checked in Lean. -/
noncomputable def bernsteinExpansion (n : ℕ) (c : Fin (n + 1) → ℝ) : ℝ[X] :=
  ∑ k, Polynomial.C (c k) * bernsteinPolynomial ℝ n k

/-- A common positive coefficient lower bound yields the same pointwise lower bound.
This is the soundness step used at each leaf of the certificate's subdivision tree. -/
theorem bernsteinExpansion_eval_ge (n : ℕ) (c : Fin (n + 1) → ℝ) (δ : ℝ)
    (hc : ∀ k, δ ≤ c k) (x : unitInterval) :
    δ ≤ (bernsteinExpansion n c).eval (x : ℝ) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦
    mul_le_mul_of_nonneg_right (hc k) (bernstein_nonneg (n := n) (ν := k) (x := x)))
  have hsum := bernstein.probability n x
  have hleft : (∑ k : Fin (n + 1), δ * bernstein n k x) = δ := by
    rw [← Finset.mul_sum, hsum, mul_one]
  rw [hleft] at h
  change δ ≤ ∑ k : Fin (n + 1), c k * (bernsteinPolynomial ℝ n k).eval (x : ℝ) at h
  simpa only [bernsteinExpansion, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C] using h

/-- A positive rational margin and a Bernstein expansion prove strict positivity. -/
theorem polynomial_pos_of_bernstein_expansion {p : ℝ[X]} (n : ℕ)
    (c : Fin (n + 1) → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hc : ∀ k, δ ≤ c k) (hp : p = bernsteinExpansion n c)
    (x : unitInterval) : 0 < p.eval (x : ℝ) := by
  rw [hp]
  exact hδ.trans_le (bernsteinExpansion_eval_ge n c δ hc x)

/-- A verified affine pullback extends the certificate to any closed interval. -/
theorem polynomial_pos_on_interval_of_bernstein {p : ℝ[X]} (a b : ℝ) (hab : a < b)
    (n : ℕ) (c : Fin (n + 1) → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hc : ∀ k, δ ≤ c k)
    (hp : ∀ t : unitInterval,
      p.eval (a + (b - a) * (t : ℝ)) = (bernsteinExpansion n c).eval (t : ℝ))
    {x : ℝ} (hx : x ∈ Set.Icc a b) : 0 < p.eval x := by
  have hba : 0 < b - a := sub_pos.mpr hab
  let t : unitInterval := ⟨(x - a) / (b - a), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hba.le
    · exact (div_le_one hba).mpr (sub_le_sub_right hx.2 a)⟩
  have hxt : a + (b - a) * (t : ℝ) = x := by
    dsimp [t]
    rw [mul_div_cancel₀ _ (ne_of_gt hba)]
    ring
  rw [← hxt, hp t]
  exact hδ.trans_le (bernsteinExpansion_eval_ge n c δ hc t)

end ADMM.UnitCircle
