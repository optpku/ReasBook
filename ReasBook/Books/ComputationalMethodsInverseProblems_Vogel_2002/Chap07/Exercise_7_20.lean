/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_10.Filters
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_25.DiscrepancyChoice

public section

/-!
Exercise 7.20. Statement-stage blocker.

The authoritative source payload for this item still says only
`7.20. Verify equation (7.88).` It does not include the displayed equation
`(7.88)` itself or the inherited Chapter 7 TSVD binders and side conditions
needed to determine the final source-facing theorem statement precisely.

Accordingly this file intentionally exports no guessed source-facing theorem,
no surrogate equation, and no placeholder declaration. The `#check` entries
below record only the verified Chapter 7 owners and specification theorem that
an eventual faithful formalization should reuse once `(7.88)` is supplied
verbatim.
-/

/- Exercise 7.20. Main labeled blocker entry.

The current workspace snapshot still lacks the verbatim display of `(7.88)` and
its inherited TSVD setup, so no source-faithful theorem or definition can be
introduced here yet. The `#check` entries below record the pointwise
discrepancy owner, its defining equation-specification theorem, the discrete
TSVD filter owner, and the TSVD reconstruction-family owner that determine the
ambient setup. Once `(7.88)` is available verbatim, replace this blocker with
exactly one source-faithful entry rather than guessing a new equation surface. -/

#check TsvdDiscrepancy.IsDiscrepancyChoiceAt
#check TsvdDiscrepancy.isDiscrepancyChoiceAt_iff
#check SpectralFilter.discreteTsvd
#check TsvdEstimation.IsTsvdReconstructionFamily

end
