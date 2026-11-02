module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_2_definition_1_17.PolynomialBound

public section

/- Definition 1.17. Let `S` be a type, let `runtime : S → ℕ` measure the number of arithmetic
operations performed by an algorithm on each instance, and let `encodingSize : S → ℕ` measure the
input encoding size. The algorithm is polynomial-time exactly when `runtime` is polynomially
bounded by `encodingSize`. -/
#check Function.PolynomiallyBoundedByNat
