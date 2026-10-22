/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

public section

/-!
Remark 8.10. Check-only interpretation.

This source item is explanatory prose: it interprets the Chapter 8 dual
definition of total variation as a weak form of `TV(f) = ∫ x in Ω, ‖∇ f x‖`
motivated by dualizing the Euclidean norm and formally integrating by parts so
compact support removes the boundary term.

The current file therefore reuses the existing Chapter 8 owner
`VariationalRegularization.totalVariation` together with its source-facing
admissible-test-field pairing surface instead of inventing a new theorem.
A rigorous theorem-level formalization of the displayed equalities would still
need the exact `(8.68)` and `(8.69)` anchors together with explicit hypotheses
on `Ω`, the regularity of `f`, the boundary measure/outward-unit-normal
convention, and the bridge from the admissible dual pairing to the weak
gradient integral.
-/

/- Remark 8.10. Main labeled source-facing entry for the current blocked-item
state: this remark interprets the existing Chapter 8 owner
`VariationalRegularization.totalVariation` as the weak integration-by-parts
motivation for `TV(f) = ∫_Ω |∇ f|`, but the repository does not yet provide the
exact source equations `(8.68)` and `(8.69)` or the full boundary/regularity
surface needed for a faithful theorem statement. The `#check` entries below
therefore record the verified Chapter 8 dual owner, its admissible
test-field/divergence-pairing surface, and generic divergence-theorem backend
anchors. -/

#check VariationalRegularization.AdmissibleTestField
#check VariationalRegularization.AdmissibleTestField.spec
#check VariationalRegularization.admissibleDivergencePairing
#check VariationalRegularization.admissibleDivergencePairing_def
#check VariationalRegularization.totalVariation
#check VariationalRegularization.totalVariation_def
#check MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
#check MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
