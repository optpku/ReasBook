/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Example 2.27: an infinite-dimensional real Hilbert space admits a discontinuous real linear
functional. -/
-- Proof sketch: choose a countable orthonormal family and extend it to a Hamel basis; define the
-- linear functional by summing the coefficients along the orthonormal part. Partial sums built
-- from an `ℓ² \ ℓ¹` coefficient sequence converge in `H` while their images diverge, so the
-- functional is discontinuous; equivalently, its kernel is not closed.
theorem exists_discontinuous_linear_form
    (hH : ¬ FiniteDimensional ℝ H) :
    ∃ f : H →ₗ[ℝ] ℝ, ¬ Continuous f := sorry

/-- The closed-kernel criterion for linear forms recasts Example 2.27 in the equivalent form that
the kernel of a real linear functional need not be closed. -/
theorem exists_linear_form_with_nonclosed_kernel
    (hH : ¬ FiniteDimensional ℝ H) :
    ∃ f : H →ₗ[ℝ] ℝ, ¬ IsClosed (f.ker : Set H) := by
  rcases exists_discontinuous_linear_form hH with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  exact fun hker ↦ hf ((LinearMap.continuous_iff_isClosed_ker f).mpr hker)
