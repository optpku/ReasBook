/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 14.19 (1): for independent `ℝⁿ`-valued random variables with Lebesgue densities,
`X + Y` again has a Lebesgue density, namely the additive convolution of the densities. This is
exactly the canonical owner theorem `ProbabilityTheory.IndepFun.add_hasPDF`, specialized in the
textbook to `G = Fin n → ℝ` and `μ = volume`. -/
recall ProbabilityTheory.IndepFun.add_hasPDF

/- Companion to Theorem 14.19 (1): the canonical pdf associated with the density of `X + Y` is
almost everywhere the additive convolution of the canonical pdfs of `X` and `Y`. -/
recall ProbabilityTheory.IndepFun.pdf_add_eq_lconvolution_pdf

/- Theorem 14.19 (2): the convolution of two Lebesgue-density measures on `ℝⁿ` is the
Lebesgue-density measure associated with the additive convolution of the densities. This is
exactly the canonical owner theorem `MeasureTheory.conv_withDensity_eq_lconvolution`,
specialized in the textbook to `G = Fin n → ℝ` and `μ = volume`. -/
recall MeasureTheory.conv_withDensity_eq_lconvolution
