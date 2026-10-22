/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open scoped ZMod

noncomputable section

namespace ProbabilityTheory
namespace Exercise1845Support

/-- Helper for Exercise 18.4.5: peeling the zero Fourier mode rewrites a normalized full Fourier
sum as the scaled nonzero-mode remainder. -/
theorem deviation_eq_scaledNonzeroModeSum
    (N : ℕ) [NeZero N] (mass : ℂ) (fourierTerm : ZMod N → ℂ)
    (hmass : mass = (N : ℂ)⁻¹ * ∑ k : ZMod N, fourierTerm k)
    (hzero : fourierTerm (0 : ZMod N) = 1) :
    mass - ((N : ℝ)⁻¹ : ℂ) =
      (N : ℂ)⁻¹ * ∑ k in Finset.univ.erase (0 : ZMod N), fourierTerm k := by
  have hNinv : ((N : ℝ)⁻¹ : ℂ) = (N : ℂ)⁻¹ := by
    simpa using (Complex.ofReal_inv (N : ℝ)).symm
  -- Proof comment: expand the full Fourier sum, split off the zero mode, and cancel the uniform
  -- contribution coming from `fourierTerm 0 = 1`.
  calc
    mass - ((N : ℝ)⁻¹ : ℂ)
      = (N : ℂ)⁻¹ * ∑ k : ZMod N, fourierTerm k - (N : ℂ)⁻¹ := by
          rw [hmass, hNinv]
    _ = (N : ℂ)⁻¹ *
          (fourierTerm (0 : ZMod N) +
            ∑ k in Finset.univ.erase (0 : ZMod N), fourierTerm k) -
          (N : ℂ)⁻¹ := by
          rw [← Finset.sum_erase_add
            (f := fun k : ZMod N ↦ fourierTerm k)
            (Finset.mem_univ (0 : ZMod N))]
    _ = (N : ℂ)⁻¹ * (1 + ∑ k in Finset.univ.erase (0 : ZMod N), fourierTerm k) -
          (N : ℂ)⁻¹ := by
          rw [hzero]
    _ = (N : ℂ)⁻¹ * ∑ k in Finset.univ.erase (0 : ZMod N), fourierTerm k := by
          rw [mul_add, mul_one, add_sub_cancel_left]

/-- Helper for Exercise 18.4.5: if every nonzero Fourier mode is bounded by `A`, then the norm of
their sum is bounded by `(N - 1) * A`. -/
theorem nonzeroModeSum_norm_le_of_bound
    (N : ℕ) [NeZero N] (A : ℝ) (fourierTerm : ZMod N → ℂ)
    (hbound : ∀ ⦃k : ZMod N⦄, k ≠ 0 → ‖fourierTerm k‖ ≤ A) :
    ‖∑ k in Finset.univ.erase (0 : ZMod N), fourierTerm k‖ ≤ (N - 1 : ℝ) * A := by
  have hsum_bound :
      ‖∑ k in Finset.univ.erase (0 : ZMod N), fourierTerm k‖ ≤
        ∑ k in Finset.univ.erase (0 : ZMod N), A := by
    -- Proof comment: use the triangle inequality and then insert the uniform pointwise bound on
    -- each nonzero mode.
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hbound (Finset.mem_erase.mp hk).1
  have hcard : (Finset.univ.erase (0 : ZMod N)).card = N - 1 := by
    -- Proof comment: the nonzero modes are exactly the `N - 1` elements left after erasing `0`
    -- from the `N` Fourier modes.
    rw [Finset.card_erase]
    simp [Fintype.card_zmod]
  calc
    ‖∑ k in Finset.univ.erase (0 : ZMod N), fourierTerm k‖
      ≤ ∑ k in Finset.univ.erase (0 : ZMod N), A := hsum_bound
    _ = (N - 1 : ℝ) * A := by
          simp [hcard, nsmul_eq_mul]

/-- Helper for Exercise 18.4.5: once the singleton-mass deviation is written as `(N : ℂ)⁻¹`
times a remainder with norm at most `(N - 1) * A`, its norm is bounded by `((N - 1) / N) * A`.
-/
theorem deviation_norm_le_of_remainderBound
    (N : ℕ) [NeZero N] (mass remainder : ℂ) (A : ℝ)
    (hdeviation : mass - ((N : ℝ)⁻¹ : ℂ) = (N : ℂ)⁻¹ * remainder)
    (hbound : ‖remainder‖ ≤ (N - 1 : ℝ) * A) :
    ‖mass - ((N : ℝ)⁻¹ : ℂ)‖ ≤ ((N - 1 : ℝ) / N) * A := by
  have hnorm_inv : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
  -- Proof comment: rewrite the deviation through the scaled remainder and then multiply the
  -- remainder estimate by the explicit norm of `(N : ℂ)⁻¹`.
  rw [hdeviation, norm_mul]
  calc
    ‖(N : ℂ)⁻¹‖ * ‖remainder‖ ≤ ‖(N : ℂ)⁻¹‖ * ((N - 1 : ℝ) * A) := by
      exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = (N : ℝ)⁻¹ * ((N - 1 : ℝ) * A) := by
          rw [hnorm_inv]
    _ = ((N - 1 : ℝ) / N) * A := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end Exercise1845Support
end ProbabilityTheory
