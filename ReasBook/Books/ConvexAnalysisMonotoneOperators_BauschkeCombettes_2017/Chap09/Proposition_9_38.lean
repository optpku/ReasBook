/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The absolute product of Hölder-conjugate real-valued `L^p` and `L^{p*}` functions is
integrable. -/
theorem holder_integrable_abs_mul
    {p : ℝ} (hp : 1 < p) {x y : Ω → ℝ}
    (hx : MemLp x (ENNReal.ofReal p) μ)
    (hy : MemLp y (ENNReal.ofReal (Real.conjExponent p)) μ) :
    Integrable (fun ω ↦ |x ω * y ω|) μ := by
  let _ :
      ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal (Real.conjExponent p)) :=
    (Real.HolderConjugate.conjExponent hp).ennrealOfReal
  simpa [Pi.mul_apply, Real.norm_eq_abs] using (hx.integrable_mul hy).norm

/-- Proposition 9.38: if `p ∈ (1, +∞)` and `p* = p / (p - 1) = Real.conjExponent p`, then for
`x ∈ L^p(μ)` and `y ∈ L^{p*}(μ)` one has Hölder's inequality
`∫ |x y| ≤ (∫ |x|^p)^(1/p) * (∫ |y|^p*)^(1/p*)`. -/
theorem holder_integral_abs_mul_le
    {p : ℝ} (hp : 1 < p) {x y : Ω → ℝ}
    (hx : MemLp x (ENNReal.ofReal p) μ)
    (hy : MemLp y (ENNReal.ofReal (Real.conjExponent p)) μ) :
    ∫ ω, |x ω * y ω| ∂μ
      ≤ (∫ ω, |x ω| ^ p ∂μ) ^ (1 / p) *
          (∫ ω, |y ω| ^ Real.conjExponent p ∂μ) ^ (1 / Real.conjExponent p) := by
  simpa [Real.norm_eq_abs] using
    integral_mul_norm_le_Lp_mul_Lq (Real.HolderConjugate.conjExponent hp) hx hy
