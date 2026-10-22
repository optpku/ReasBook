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

variable {d : ℕ}

/-- The canonical inclusion from `L^p(Ω)` to `L¹(Ω)` on a finite-measure domain. -/
def lpToL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    MeasureTheory.Lp ℝ 1 (domainMeasure Ω) :=
  ⟨(f : (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ),
    MeasureTheory.Lp.antitone (E := ℝ) (μ := domainMeasure Ω)
      (show (1 : ENNReal) ≤ p from Fact.out) f.2⟩

/-- `lpToL1` preserves the underlying almost-everywhere equivalence class. -/
@[simp] theorem lpToL1_toAEEqFun
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    ((lpToL1 f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) =
      (f : (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) := by
  simp [lpToL1]

/-- The `L¹(Ω)` image produced by `lpToL1` agrees almost everywhere with the original
`L^p(Ω)` representative. -/
theorem lpToL1_ae_eq
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    lpToL1 f =ᵐ[domainMeasure Ω] f := by
  simp [lpToL1]

end VariationalRegularization
