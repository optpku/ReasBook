/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.Density
public import Mathlib.Probability.CDF

public section

namespace ProbabilityTheory

universe u

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ}

/-- Definition 4.3 (1). For a measurable real random variable, the source continuity condition is
the canonical `MeasureTheory.HasPDF` condition, equivalently absolute continuity of the law with
respect to volume. -/
theorem hasPDF_iff_map_absolutelyContinuous [MeasureTheory.SFinite μ] (hX : Measurable X) :
    MeasureTheory.HasPDF X μ ↔
      (MeasureTheory.Measure.map X μ).AbsolutelyContinuous MeasureTheory.volume := by
  simpa using (Real.hasPDF_iff_of_aemeasurable hX.aemeasurable)

end

end ProbabilityTheory

/- Definition 4.3 (1). A real random variable is continuous when its law has a density with
respect to volume; `MeasureTheory.HasPDF` is the canonical owner, and
`Real.hasPDF_iff_of_aemeasurable` gives the absolute-continuity bridge on `ℝ`. -/
#check MeasureTheory.HasPDF
#check Real.hasPDF_iff_of_aemeasurable

namespace ProbabilityTheory

universe u

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
variable {X : Ω → ℝ}

/-- Definition 4.3 (2). The cumulative distribution function of a continuous real random variable
is recovered as the real value of the volume set integral of its `pdf` over `Set.Iic x`. -/
theorem cdf_map_eq_setLIntegral_pdf [MeasureTheory.HasPDF X μ] (x : ℝ) :
    ProbabilityTheory.cdf (MeasureTheory.Measure.map X μ) x =
      (∫⁻ t in Set.Iic x, MeasureTheory.pdf X μ MeasureTheory.volume t
        ∂MeasureTheory.volume).toReal := by
  have hprob : MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.map X μ) :=
    MeasureTheory.Measure.isProbabilityMeasure_map
      (MeasureTheory.HasPDF.aemeasurable X μ MeasureTheory.volume)
  calc
    ProbabilityTheory.cdf (MeasureTheory.Measure.map X μ) x =
        (MeasureTheory.Measure.map X μ).real (Set.Iic x) := by
      simpa using (@ProbabilityTheory.cdf_eq_real (MeasureTheory.Measure.map X μ) hprob x)
    _ =
        (∫⁻ t in Set.Iic x, MeasureTheory.pdf X μ MeasureTheory.volume t
          ∂MeasureTheory.volume).toReal := by
      rw [MeasureTheory.measureReal_def,
        MeasureTheory.map_eq_setLIntegral_pdf X μ MeasureTheory.volume measurableSet_Iic]

end

end ProbabilityTheory

/- Definition 4.3 (2). The source CDF formula is recovered by combining the density integral
formula for the pushed-forward law with the real-line identity
`ProbabilityTheory.cdf μ x = μ.real (Set.Iic x)`. -/
#check ProbabilityTheory.cdf_map_eq_setLIntegral_pdf
#check ProbabilityTheory.cdf_eq_real

/- Definition 4.3 (3). The source probability density function is the Radon–Nikodym derivative of
the law with respect to volume, i.e.
`MeasureTheory.pdf X μ MeasureTheory.volume
  = (MeasureTheory.Measure.map X μ).rnDeriv MeasureTheory.volume`. -/
#check MeasureTheory.pdf_def
#check MeasureTheory.pdf
