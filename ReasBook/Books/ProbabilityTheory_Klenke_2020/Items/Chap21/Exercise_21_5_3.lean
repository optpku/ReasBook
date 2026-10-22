/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Exercise_26_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: Exercise 26.1.1 later formalizes the process
-- `Y_t = X_t - a - t (b - a)` for the explicit Brownian-bridge SDE solution
-- `X = brownianBridgeSDESolutionCandidate a b W`. In the zero-endpoint case `a = b = 0`, this is
-- exactly the source process `Y_t = (1 - t) ∫_0^t (1 - s)⁻¹ dW_s`, and Exercise 26.1.1 proves the
-- Brownian-bridge owner statement directly for that centered process.
/-- Exercise 21.5.3: the zero-endpoint Brownian-bridge SDE solution,
viewed through its centered bridge process, is a Brownian bridge on `[0,1]`. -/
theorem brownianBridgeSDEZeroEndpoint_bridgeProcess_isBrownianBridge
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W) :
    IsBrownianBridge μ
      (brownianBridgeSDEBridgeProcess (brownianBridgeSDESolutionCandidate 0 0 W) 0 0) :=
  brownianBridgeSDESolutionCandidate_bridgeProcess_isBrownianBridge hW 0 0

end ProbabilityTheory
