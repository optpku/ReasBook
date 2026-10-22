/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Fact 2.24: every continuous linear functional on a real Hilbert space is represented by a
unique vector through the inner product, and the representing vector has the same norm as the
functional. -/
-- Proof sketch: the representing vector is `(toDual ℝ H).symm f`; rewrite the Riesz equation
-- pointwise via the inner product, and use injectivity of `toDual` for uniqueness.
theorem riesz_frechet_representation (f : H →L[ℝ] ℝ) :
    ∃! u : H, (∀ x : H, f x = ⟪x, u⟫_ℝ) ∧ ‖f‖ = ‖u‖ := by
  refine ⟨(toDual ℝ H).symm f, ?_, ?_⟩
  · constructor
    · intro x
      have hu_apply : toDual ℝ H ((toDual ℝ H).symm f) x = f x := by
        exact DFunLike.congr_fun ((toDual ℝ H).apply_symm_apply f) x
      calc
        f x = toDual ℝ H ((toDual ℝ H).symm f) x := hu_apply.symm
        _ = ⟪x, (toDual ℝ H).symm f⟫_ℝ := by
          rw [toDual_apply_apply, real_inner_comm]
    · exact (((toDual ℝ H).symm).norm_map f).symm
  · intro v hv
    have hv_toDual : toDual ℝ H v = f := by
      ext x
      simpa [toDual_apply_apply, real_inner_comm] using (hv.1 x).symm
    exact (toDual ℝ H).injective <|
      hv_toDual.trans ((toDual ℝ H).apply_symm_apply f).symm
