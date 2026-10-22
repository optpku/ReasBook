/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Data.NNReal.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The compensator `t ↦ ∫_0^t H_s^2 ds` attached to a real-valued process `H`. -/
noncomputable def secondMomentCompensator (H : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦
    ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (H s.toNNReal ω) ^ 2

/-- The compensated square process `M_t^2 - ∫_0^t H_s^2 ds`. -/
noncomputable def brownianItoCompensatedSquareProcess
    (I H : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ (I t ω) ^ 2 - secondMomentCompensator H t ω

omit [MeasurableSpace Ω] in
/-- Evaluating the compensated square process gives `M_t^2 - ∫_0^t H_s^2 ds`. -/
theorem brownianItoCompensatedSquareProcess_apply
    (I H : NNReal → Ω → ℝ) (t : NNReal) (ω : Ω) :
    brownianItoCompensatedSquareProcess I H t ω =
      (I t ω) ^ 2 - secondMomentCompensator H t ω := rfl

omit [MeasurableSpace Ω] in
/-- The explicit compensator starts from `0`. -/
theorem secondMomentCompensator_zero (H : NNReal → Ω → ℝ) :
    secondMomentCompensator H 0 = 0 := by
  funext ω
  simp [secondMomentCompensator]

omit [MeasurableSpace Ω] in
/-- If `M 0 = 0`, then the compensated square process also starts from `0`. -/
lemma brownianItoCompensatedSquareProcess_zero
    {M H : NNReal → Ω → ℝ} (hM_zero : M 0 = 0) :
    brownianItoCompensatedSquareProcess M H 0 = 0 := by
  funext ω
  have hω : M 0 ω = 0 := congrFun hM_zero ω
  simp [brownianItoCompensatedSquareProcess, secondMomentCompensator_zero, hω]

end MeasureTheory
