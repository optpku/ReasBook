module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator

public section

/- Theorem 1.2 (1): for `v : Fin n → ℚ`, the source common denominator
`D = rational_vector_common_denominator v` clears all coordinate denominators, and the
explicit integer vector `common_denominator_scaled_vector v : Fin n → ℤ` realizes the source
claim that `D • v ∈ ℤ^n`. -/
#check common_denominator_scaled_vector_eq_smul

/- Theorem 1.2 (2): with `L = EncodingSize.rationalVector v`, the encoding size of the
integer vector `common_denominator_scaled_vector v` is at most `nL`. -/
#check common_denominator_scaled_vector_encoding_size_le
