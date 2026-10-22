/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_29
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Lemma_7_5

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_4
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6

public section

/- Remark 7.7. Equation `(7.45)` is somewhat analogous to the error expressions
from Section `1.2.1`. The current repository now exposes Proposition 7.6 as a
source-facing expected-error decomposition together with its spectral variance
rewrite, while the reusable Chapter 7 owners remain
`FilterRegularization.expectedSqEstimationError`,
`FilterRegularization.nullspaceComponent`, and
`FilterRegularization.noiseAmplificationTrace`. The comparison with Section
`1.2.1` is therefore mediated by those owners, the truncation/noise-error
split, and the trace backend from Proposition 4.29 and Lemma 7.5. No new
theorem is asserted here. -/

#check FilterRegularization.expectedSqEstimationError
#check FilterRegularization.expectedSqEstimationError_def
#check FilterRegularization.nullspaceComponent
#check FilterRegularization.nullspaceComponent_eq_sub_orthogonalProjection
#check FilterRegularization.noiseAmplificationTrace
#check FilterRegularization.noiseAmplificationTrace_eq_trace_adjoint_comp
#check ProbabilityTheory.expected_sqNorm_eq_trace_secondMomentMatrix
#check FilterRegularization.truncationError
#check FilterRegularization.truncationError_eq
#check FilterRegularization.error_eq_truncationError_add_noiseError
#check reconstruction_trace_transpose_mul_of_spectralRep
