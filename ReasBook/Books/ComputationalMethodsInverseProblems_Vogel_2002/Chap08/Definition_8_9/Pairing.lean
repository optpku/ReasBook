/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9.TestFields

public section

noncomputable section

namespace VariationalRegularization

open scoped BigOperators

variable {d : ℕ}

/-- The coordinate divergence of an admissible test field on `Ω`. -/
@[expose]
def admissibleDivergence
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, fderiv ℝ v.toTestFunction x (EuclideanSpace.single i (1 : ℝ)) i

/-- The defining coordinate formula for `admissibleDivergence`. -/
theorem admissibleDivergence_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) (x : EuclideanSpace ℝ (Fin d)) :
    admissibleDivergence v x =
      ∑ i : Fin d, fderiv ℝ v.toTestFunction x (EuclideanSpace.single i (1 : ℝ)) i := rfl

/-- The divergence pairing `∫_Ω f · div v` against an admissible test field. -/
@[expose]
def admissibleDivergencePairing
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (v : AdmissibleTestField Ω) : ℝ :=
  ∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω

/-- The defining integral formula for `admissibleDivergencePairing`. -/
theorem admissibleDivergencePairing_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (v : AdmissibleTestField Ω) :
    admissibleDivergencePairing f v =
      ∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω := rfl

end VariationalRegularization
