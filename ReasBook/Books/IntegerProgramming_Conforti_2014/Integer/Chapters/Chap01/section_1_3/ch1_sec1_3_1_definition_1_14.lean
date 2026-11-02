module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_14.PolynomialBound

public section

/- Definition 1.14. Let `S` be a type, let `f : S → ℝ`, and let
`g : Fin t → S → ℝ` encode the finite family `g₁, ..., g_t : S → ℝ`. The source-facing notion of
`f` being polynomially bounded by `g` is formalized by the reusable owner
`Function.PolynomiallyBoundedByFamily`. -/
#check Function.PolynomiallyBoundedByFamily
