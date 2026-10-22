/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_5.Filters
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Lemma_7_5
public import Mathlib.LinearAlgebra.Matrix.Trace

public section

noncomputable section

universe u

/- Remark 7.4. The current Chapter 7 API does not support turning this remark
into a precise theorem without choosing between two different counts.
`Definition_7_2` uses `Matrix.trace (1 - A)` in the denominator of `(7.23)`,
while `influenceMatrix_trace_of_spectralRep` together with
`SpectralFilter.tsvd` identifies `Matrix.trace Aα` with the retained-term side
of the TSVD expansion. Accordingly, this item records only the verified anchors
and rewrites the denominator term algebraically, but it does not identify
`Matrix.trace (1 - Aα)` with either a retained-count or a discarded-count
convention until the source wording is clarified. -/

section

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Remark 7.4 companion. Under the spectral representation from `Lemma 7.5`,
the complementary trace term in the GCV denominator is the ambient dimension
minus the spectral trace sum. This is the available algebraic bridge; it does
not choose a retained-count or discarded-count interpretation. -/
theorem influenceMatrix_trace_one_sub_of_spectralRep
    (Aα U : Matrix n n ℝ) (wα : ℝ → ℝ) (s : n → ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hAα : Aα = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2)) * U.transpose) :
    Matrix.trace (1 - Aα) = (Fintype.card n : ℝ) - ∑ i, wα (s i ^ 2) := by
  let hRep : HasInfluenceMatrixSpectralRep Aα U wα s :=
    HasInfluenceMatrixSpectralRep.ofOrthogonalEq hU hAα
  rw [Matrix.trace_sub, Matrix.trace_one,
    influenceMatrix_trace_of_spectralRep hRep]

end

section

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Remark 7.4 companion. Rewriting the denominator trace term in `gcvValue`
with the spectral representation from `Lemma 7.5` yields the explicit
dimension-minus-trace formula used by the current Chapter 7 API. -/
theorem gcvValue_eq_of_spectralRep
    (Aα U : Matrix n n ℝ) (wα : ℝ → ℝ) (s : n → ℝ)
    (d : EuclideanSpace ℝ n) (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hAα : Aα = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2)) * U.transpose) :
    gcvValue Aα d =
      predictiveRisk (regularizedResidual Aα d) /
        ((((Fintype.card n : ℝ) - ∑ i, wα (s i ^ 2)) / (Fintype.card n : ℝ)) ^ 2) := by
  rw [gcvValue_def, influenceMatrix_trace_one_sub_of_spectralRep Aα U wα s hU hAα]

end

#check gcvValue
#check influenceMatrix_trace_of_spectralRep
#check SpectralFilter.tsvd
