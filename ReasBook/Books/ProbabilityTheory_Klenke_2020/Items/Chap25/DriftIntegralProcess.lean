/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "Process" => NNReal → Ω → ℝ

/-- The finite-variation drift part `t ↦ ∫_0^t b_s ds` of a real-valued process `b`. -/
def driftIntegralProcess (b : Process) : Process :=
  fun t ω ↦ ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω

-- Proof sketch: unfold `driftIntegralProcess`; the value at `(t, ω)` is exactly the defining
-- Lebesgue integral of the time slice `s ↦ b_s(ω)` over `[0, t]`.
/-- Evaluating `driftIntegralProcess b` gives the time integral `∫_0^t b_s ds`. -/
@[simp] theorem driftIntegralProcess_apply (b : Process) (t : NNReal) (ω : Ω) :
    driftIntegralProcess b t ω =
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω :=
  rfl

end ProbabilityTheory
