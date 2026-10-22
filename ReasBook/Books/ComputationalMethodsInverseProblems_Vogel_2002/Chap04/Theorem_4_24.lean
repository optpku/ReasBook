/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Theorem_4_24.PosteriorPmf

public section

noncomputable section

namespace ProbabilityTheory.JointPmf

universe v w

variable {α : Type v} {β : Type w}

/-- Theorem 4.24. For a joint PMF `joint` on `α × β`, the reverse conditional PMF
`condFstGivenSnd joint y hy` satisfies the discrete Bayes rule
`condFstGivenSnd joint y hy x =
  (condSndGivenFst joint x hx y * fstMarginal joint x) / sndMarginal joint y`. -/
theorem condFstGivenSnd_apply_bayes
    (joint : PMF (α × β)) (x : α) (y : β)
    (hy : sndMarginal joint y ≠ 0) (hx : fstMarginal joint x ≠ 0) :
    condFstGivenSnd joint y hy x =
      (condSndGivenFst joint x hx y * fstMarginal joint x) / sndMarginal joint y := by
  rw [condFstGivenSnd_apply, condSndGivenFst_apply]
  rw [ENNReal.div_mul_cancel hx ((fstMarginal joint).apply_ne_top x)]

end ProbabilityTheory.JointPmf
