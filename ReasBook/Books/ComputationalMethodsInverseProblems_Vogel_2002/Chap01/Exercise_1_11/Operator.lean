/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_1.Fredholm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space

public section

noncomputable section

namespace Fredholm1D

/-- The measure model for `L²(0, 1)` used in Exercise 1.11. -/
def unitIntervalMeasure : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)

/-- The pointwise Gaussian Fredholm blur of an `L²(0, 1)` datum. -/
def gaussianBlurFunction (C γ : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) : ℝ → ℝ :=
  fun x ↦ ∫ t, gaussianKernel C γ (x - t) * f t ∂unitIntervalMeasure

/-- The defining integral formula for `gaussianBlurFunction`. -/
theorem gaussianBlurFunction_apply (C γ : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) (x : ℝ) :
    gaussianBlurFunction C γ f x =
      ∫ t, gaussianKernel C γ (x - t) * f t ∂unitIntervalMeasure := sorry

/-- The Gaussian blur of an `L²(0, 1)` datum is again an `L²(0, 1)` function class. -/
theorem gaussianBlurFunction_memLp (C γ : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    MeasureTheory.MemLp (gaussianBlurFunction C γ f) 2 unitIntervalMeasure := sorry

/-- The `L²(0, 1)` Gaussian blur respects addition. -/
theorem gaussianBlurL2_map_add (C γ : ℝ)
    (f g : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    (gaussianBlurFunction_memLp C γ (f + g)).toLp (gaussianBlurFunction C γ (f + g)) =
      (gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f) +
        (gaussianBlurFunction_memLp C γ g).toLp (gaussianBlurFunction C γ g) := sorry

/-- The `L²(0, 1)` Gaussian blur commutes with scalar multiplication. -/
theorem gaussianBlurL2_map_smul (C γ a : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    (gaussianBlurFunction_memLp C γ (a • f)).toLp (gaussianBlurFunction C γ (a • f)) =
      a • (gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f) := sorry

/-- The pointwise Gaussian blur induces a continuous `L²(0, 1)` operator. -/
theorem gaussianBlurL2_continuous (C γ : ℝ) :
    Continuous (fun f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure ↦
      (gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f)) := sorry

/-- The Chapter 1 Gaussian Fredholm blur operator on `L²(0, 1)`. -/
def gaussianBlurL2 (C γ : ℝ) :
    MeasureTheory.Lp ℝ 2 unitIntervalMeasure →L[ℝ] MeasureTheory.Lp ℝ 2 unitIntervalMeasure :=
  { toLinearMap :=
      { toFun := fun f ↦
          (gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f)
        map_add' := gaussianBlurL2_map_add C γ
        map_smul' := gaussianBlurL2_map_smul C γ }
    cont := gaussianBlurL2_continuous C γ }

/-- Applying `gaussianBlurL2` is the `Lp` class of `gaussianBlurFunction`. -/
theorem gaussianBlurL2_apply (C γ : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    gaussianBlurL2 C γ f =
      (gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f) := sorry

/-- The bundled Gaussian `L²(0, 1)` blur realizes the source operator `(1.1)`
specialized to `gaussianKernel C γ`. -/
theorem gaussianBlurL2_realizesOperator (C γ : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    gaussianBlurFunction C γ f = operator (gaussianKernel C γ) f := sorry

/-- The Gaussian `L²(0, 1)` blur operator is self-adjoint. -/
theorem gaussianBlurL2_adjoint_eq (C γ : ℝ) :
    ContinuousLinearMap.adjoint (gaussianBlurL2 C γ) = gaussianBlurL2 C γ := sorry

end Fredholm1D
