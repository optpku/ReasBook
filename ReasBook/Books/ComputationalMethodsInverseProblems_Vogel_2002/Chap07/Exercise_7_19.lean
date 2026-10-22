/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.ExpectedError

public section

/- Exercise 7.19 (1). In equation `(7.81)`, the nonsaturated constant `C₃`
is already formalized directly by the canonical Chapter 7 owner
`TikhonovEstimation.errorConstantC3`. -/
#check TikhonovEstimation.errorConstantC3

/- Exercise 7.19 (2). In equation `(7.81)`, the critical constant `C₄` is
already formalized directly by the canonical Chapter 7 owner
`TikhonovEstimation.errorConstantC4`. -/
#check TikhonovEstimation.errorConstantC4

/- Exercise 7.19 (3). In equation `(7.81)`, the saturated constant `C₅` is
already formalized directly by the canonical Chapter 7 owner
`TikhonovEstimation.errorConstantC5`. -/
#check TikhonovEstimation.errorConstantC5

end
