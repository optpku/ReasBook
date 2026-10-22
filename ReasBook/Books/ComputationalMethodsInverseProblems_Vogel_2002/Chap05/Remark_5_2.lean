/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_6

public section

/- Remark 5.2. Chapter 5 uses the symmetric `1 / √n` normalization in
`Matrix.fourierMatrix n`, rather than the more common `fft`/`ifft` convention
with an unnormalized forward transform and an inverse scaled by `1 / n`.

This normalization choice is expository rather than a new mathematical owner.
Its checked source-relevant content is already carried by the normalized
Fourier-matrix owner `Matrix.fourierUnitary n` together with Exercise 5.6,
which records preservation of Euclidean inner products and norms on
`EuclideanSpace ℂ (Fin n)`. -/

#check Matrix.fourierMatrix
#check Matrix.fourierUnitary
#check dftInnerPreserving
#check dftNormPreserving
