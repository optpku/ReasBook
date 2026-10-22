/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33

/-- Helper for Remark 7.17: package an asymptotic equivalence as
`ParameterChoice.IsAsymptoticallyOptimal`. -/
theorem parameterChoiceIsAsymptoticallyOptimalOfIsEquivalent
    {α αopt : ℕ → ℝ}
    (h : Asymptotics.IsEquivalent Filter.atTop α αopt) :
    ParameterChoice.IsAsymptoticallyOptimal α αopt := by
  -- Rewrite the owner wrapper to its generated equality form before using the
  -- given asymptotic-equivalence witness.
  rw [ParameterChoice.IsAsymptoticallyOptimal.eq_1]
  exact h
