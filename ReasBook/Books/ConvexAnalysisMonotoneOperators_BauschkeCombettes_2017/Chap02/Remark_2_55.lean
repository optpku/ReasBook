/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Remark 2.55: on a real Hilbert space, the Fréchet derivative within `C` is represented by the
canonical vector `gradientWithin f C x`. -/
-- Proof sketch: use `DifferentiableWithinAt.hasGradientWithinAt`, identify the derivative with
-- `fderivWithin`, and rewrite using symmetry of the real inner product.
theorem fderivWithin_eq_inner_gradientWithin
    {C : Set H} {f : H → ℝ} {x y : H}
    (hf : DifferentiableWithinAt ℝ f C x) (hC : UniqueDiffWithinAt ℝ C x) :
    fderivWithin ℝ f C x y = ⟪y, gradientWithin f C x⟫_ℝ := by
  simpa [real_inner_comm] using (inner_gradientWithin_left hf hC).symm

/-- The Fréchet derivative within `C` has `gradientWithin f C x` as its unique Riesz
representer. -/
theorem existsUnique_gradientWithin_of_differentiableWithinAt
    {C : Set H} {f : H → ℝ} {x : H}
    (hf : DifferentiableWithinAt ℝ f C x) (hC : UniqueDiffWithinAt ℝ C x) :
    ∃! g : H, ∀ y : H, fderivWithin ℝ f C x y = ⟪y, g⟫_ℝ := by
  have hgradient : ∀ y : H, fderivWithin ℝ f C x y = ⟪y, gradientWithin f C x⟫_ℝ :=
    fun y ↦ fderivWithin_eq_inner_gradientWithin hf hC
  refine ⟨gradientWithin f C x, hgradient, ?_⟩
  intro g hg
  exact ext_inner_left ℝ fun y ↦ (hg y).symm.trans (hgradient y)
