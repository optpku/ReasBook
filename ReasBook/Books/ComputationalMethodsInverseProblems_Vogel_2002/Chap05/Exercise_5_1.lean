/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1.Blur2D

public section

namespace Blur2D

/-- Midpoint sampling of a translation-invariant blur kernel depends only on the
corresponding index differences, so the sampled four-index PSF reduces to
`translationInvariantDiscretePSF`. -/
theorem sampledPSFMidpoint_eq_discretePSF
    (κ : (ℝ × ℝ) → ℝ)
    (Δx Δy : ℝ)
    {n_x n_y : ℕ}
    (i μ : Fin n_x)
    (j ν : Fin n_y) :
    sampledPSF (translationInvariantKernel κ) Δx Δy
        (fun a ↦ ((((a : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δx))
        (fun b ↦ ((((b : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δy))
        i μ j ν =
      translationInvariantDiscretePSF κ Δx Δy
        (((i : ℕ) : ℤ) - ((μ : ℕ) : ℤ))
        (((j : ℕ) : ℤ) - ((ν : ℕ) : ℤ)) := by
  have hx :
      ((((i : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δx) - ((((μ : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δx) =
        (((((i : ℕ) : ℤ) - ((μ : ℕ) : ℤ) : ℤ) : ℝ) * Δx) := by
    push_cast
    ring
  have hy :
      ((((j : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δy) - ((((ν : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δy) =
        (((((j : ℕ) : ℤ) - ((ν : ℕ) : ℤ) : ℤ) : ℝ) * Δy) := by
    push_cast
    ring
  have hpair :
      ((((i : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δx, (((j : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δy) -
          ((((μ : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δx, (((ν : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δy) =
        ((((((i : ℕ) : ℤ) - ((μ : ℕ) : ℤ) : ℤ) : ℝ) * Δx),
          (((((j : ℕ) : ℤ) - ((ν : ℕ) : ℤ) : ℤ) : ℝ) * Δy)) := by
    ext
    · exact hx
    · exact hy
  rw [sampledPSF_apply, translationInvariantKernel_apply, translationInvariantDiscretePSF_apply]
  rw [hpair]

/-- Exercise 5.1. The textbook midpoint-quadrature kernel entries `t_ij` are
formalized by
`translationInvariantDiscretePSF κ ((1 : ℝ) / n_x) ((1 : ℝ) / n_y) (i - 1) (j - 1)`,
which satisfies the displayed formula
`κ ((((i - 1 : ℤ) : ℝ) / n_x), (((j - 1 : ℤ) : ℝ) / n_y)) * ((1 : ℝ) / n_x) * ((1 : ℝ) / n_y)`. -/
theorem midpointKernelFormula
    (κ : (ℝ × ℝ) → ℝ)
    (n_x n_y : ℕ)
    (i j : ℤ) :
    translationInvariantDiscretePSF κ ((1 : ℝ) / n_x) ((1 : ℝ) / n_y) (i - 1) (j - 1) =
      κ ((((i - 1 : ℤ) : ℝ) / n_x), (((j - 1 : ℤ) : ℝ) / n_y)) *
        ((1 : ℝ) / n_x) * ((1 : ℝ) / n_y) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    translationInvariantDiscretePSF_apply κ ((1 : ℝ) / n_x) ((1 : ℝ) / n_y) (i - 1) (j - 1)

end Blur2D
