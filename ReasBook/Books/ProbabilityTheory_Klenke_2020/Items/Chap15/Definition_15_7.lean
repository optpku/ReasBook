/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory
open scoped RealInnerProductSpace

/- Definition 15.7: For a finite measure on `ℝ^d`, the characteristic function is the canonical
mathlib map `MeasureTheory.charFun`, given by the Fourier kernel integral. -/
recall MeasureTheory.charFun

variable {d : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin d))}

/-- Bridge to the textbook formula on `ℝ^d`: `MeasureTheory.charFun` is the Fourier kernel
integral with the inner product written as `⟪t, x⟫`. -/
-- Proof sketch: unfold `MeasureTheory.charFun` and use the symmetry of the real inner product to
-- rewrite `⟪x, t⟫` as `⟪t, x⟫`.
theorem charFun_eq_integral_exp_inner_comm (t : EuclideanSpace ℝ (Fin d)) :
    charFun μ t = ∫ x, Complex.exp (⟪t, x⟫ * Complex.I) ∂μ := by
  rw [charFun_apply]
  congr with x
  rw [real_inner_comm]
