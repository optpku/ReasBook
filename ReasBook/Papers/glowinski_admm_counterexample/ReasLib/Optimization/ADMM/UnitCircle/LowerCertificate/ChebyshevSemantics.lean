/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.SupplySemantics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators
open Polynomial

theorem unitCircle_zpow_re {z : ℂ} (hz : ‖z‖ = 1) (k : ℤ) :
    (z ^ k).re = (Chebyshev.T ℝ k).eval z.re := by
  obtain ⟨θ, rfl⟩ := (Complex.norm_eq_one_iff z).mp hz
  rw [← Complex.exp_int_mul]
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im, Chebyshev.T_real_cos]

theorem unitCircle_zpow_im {z : ℂ} (hz : ‖z‖ = 1) (k : ℤ) :
    (z ^ k).im = z.im * (Chebyshev.U ℝ (k - 1)).eval z.re := by
  obtain ⟨θ, rfl⟩ := (Complex.norm_eq_one_iff z).mp hz
  rw [← Complex.exp_int_mul]
  simp only [Complex.exp_im, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  simp only [mul_zero, zero_mul, mul_one, zero_add, add_zero, sub_zero,
    Real.exp_zero, one_mul]
  rw [mul_comm (Real.sin θ), Chebyshev.U_real_cos]
  congr 1
  push_cast
  ring

/-- Real and imaginary scalar polynomials associated with an exact rational
Laurent expression; the latter is multiplied by the circle's imaginary coordinate. -/
noncomputable def realPolynomial (p : Laurent) : ℝ[X] :=
  (p.map (fun e ↦ C (e.2 : ℝ) * Chebyshev.T ℝ e.1)).sum

noncomputable def imagPolynomial (p : Laurent) : ℝ[X] :=
  (p.map (fun e ↦ C (e.2 : ℝ) * Chebyshev.U ℝ (e.1 - 1))).sum

theorem evaluateLaurent_re (p : Laurent) {z : ℂ} (hz : ‖z‖ = 1) :
    (evaluateLaurent p z).re = (realPolynomial p).eval z.re := by
  induction p with
  | nil => simp [realPolynomial]
  | cons e p ih =>
    simp [realPolynomial, evaluateLaurent_cons, Complex.mul_re,
      unitCircle_zpow_re hz, ih]

theorem evaluateLaurent_im (p : Laurent) {z : ℂ} (hz : ‖z‖ = 1) :
    (evaluateLaurent p z).im = z.im * (imagPolynomial p).eval z.re := by
  induction p with
  | nil => simp [imagPolynomial]
  | cons e p ih =>
    simp [imagPolynomial, evaluateLaurent_cons, Complex.mul_im,
      unitCircle_zpow_im hz, ih]
    ring

end ADMM.UnitCircle.LowerCertificate
