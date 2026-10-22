/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.Density
public import Mathlib.Probability.Kernel.CondDistrib

public section

/- Remark 4.22. For continuous random vectors `X` and `Y`, the Chapter 4 analogues of
joint and marginal laws, conditioning, and conditional expectation are expressed through
probability densities and conditional distributions. In this setting, the discrete sums in
`(4.9)`-`(4.12)` are replaced by the corresponding integrals, so the source-facing API here
should point directly at the canonical density and conditional-distribution identities rather
than introduce local wrappers. The embedded Table 4.2 is motivational context for the next
proposition rather than a separate owner to formalize here. -/

#check MeasureTheory.HasPDF
#check MeasureTheory.pdf
#check MeasureTheory.map_eq_setLIntegral_pdf
#check MeasureTheory.pdf.integral_pdf_smul
#check ProbabilityTheory.condDistrib
#check ProbabilityTheory.condDistrib_ae_eq_condExp
#check ProbabilityTheory.condExp_ae_eq_integral_condDistrib'
