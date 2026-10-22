/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {ι : Type u} {Ω : Type v} [Preorder ι]
variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ι m0} {μ : Measure Ω}

-- Proof sketch: the constant process `a` is a martingale on a finite measure space, so
-- `X - a` is a submartingale by subtraction of a martingale; then apply `Submartingale.pos`.
/-- Corollary 9.34: if `X` is a submartingale and `a : ℝ`, then the positive part of the shifted
process `X - a` is again a submartingale. -/
theorem submartingale_pos_sub_const {X : ι → Ω → ℝ} [IsFiniteMeasure μ]
    (hX : Submartingale X ℱ μ) (a : ℝ) :
    Submartingale ((X - fun _ _ ↦ a)⁺) ℱ μ := by
  simpa using (hX.sub_martingale (martingale_const ℱ μ a)).pos
