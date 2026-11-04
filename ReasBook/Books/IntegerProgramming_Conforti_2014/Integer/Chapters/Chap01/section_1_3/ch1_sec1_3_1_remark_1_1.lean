/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator

/- Remark 1.1: the encoding-size conventions used for rational and integer vectors are the
canonical owners `EncodingSize.rational`, `EncodingSize.rationalVector`, and
`EncodingSize.integerVector`. -/
#check EncodingSize.rational
#check EncodingSize.rationalVector
#check EncodingSize.integerVector

/- Remark 1.1: clearing the denominators of a rational vector uses the common denominator
`rational_vector_common_denominator v` and the associated integer vector
`common_denominator_scaled_vector v`. -/
#check rational_vector_common_denominator
#check common_denominator_scaled_vector

/- Remark 1.1 (1): scaling a rational vector by the least common multiple of its coordinate
denominators produces an integer vector whose rational realization is exactly the scaled vector. -/
#check common_denominator_scaled_vector_eq_smul

/- Remark 1.1 (2): the encoding size of the scaled integer vector is at most `n` times the
encoding size of the original rational vector. -/
#check common_denominator_scaled_vector_encoding_size_le
