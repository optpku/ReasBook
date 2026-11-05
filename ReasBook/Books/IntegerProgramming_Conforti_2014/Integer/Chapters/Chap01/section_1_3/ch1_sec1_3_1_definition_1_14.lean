/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_14.PolynomialBound

public section

/- Definition 1.14. Let `S` be a type, let `f : S → ℝ`, and let
`g : Fin t → S → ℝ` encode the finite family `g₁, ..., g_t : S → ℝ`. The source-facing notion of
`f` being polynomially bounded by `g` is formalized by the reusable owner
`Function.PolynomiallyBoundedByFamily`. -/
#check Function.PolynomiallyBoundedByFamily
