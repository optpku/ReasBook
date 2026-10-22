/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

-- Proof sketch: apply the canonical convolution formula for the pushforward laws of two
-- independent measurable additive random variables, namely `IndepFun.map_add_eq_map_conv_map`.
/-- Theorem 2.31: if `X` and `Y` are independent `ℤ`-valued random variables, then the
distribution of their sum is the convolution of their marginal distributions:
`P.map (X + Y) = (P.map X) ∗ (P.map Y)`. -/
theorem sum_distribution_eq_convolution_of_indepFun {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℤ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : X ⟂ᵢ[P] Y) :
    P.map (X + Y) = (P.map X) ∗ (P.map Y) := by
  -- The canonical independence API already packages the singleton-fiber summation argument
  -- from the textbook into the equality between the law of a sum and measure convolution.
  exact hXY.map_add_eq_map_conv_map hX hY
