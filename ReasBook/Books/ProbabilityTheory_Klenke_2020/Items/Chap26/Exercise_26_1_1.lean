/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_13

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

section Pure

variable {Ω : Type u}

local notation "Process" => NNReal → Ω → ℝ

/-- The centered process `Y_t = X_t - a - t (b - a)` attached to a real-valued process `X`. -/
def brownianBridgeSDECenteredProcess (X : Process) (a b : ℝ) : Process :=
  fun t ω ↦ X t ω - a - (t : ℝ) * (b - a)

/-- Evaluating the centered process subtracts the affine interpolation between `a` and `b`. -/
theorem brownianBridgeSDECenteredProcess_apply
    (X : Process) (a b : ℝ) (t : NNReal) (ω : Ω) :
    brownianBridgeSDECenteredProcess X a b t ω =
      X t ω - a - (t : ℝ) * (b - a) := by
  rfl

/-- The explicit Brownian-bridge candidate obtained by adding the affine interpolation from `a`
to `b` to the canonical centered Brownian bridge driven by `W`. -/
def brownianBridgeSDESolutionCandidate (a b : ℝ) (W : Process) : Process :=
  fun t ω ↦ a + (t : ℝ) * (b - a) + (W t ω - (t : ℝ) * W 1 ω)

/-- The closed-interval bridge process obtained by centering `X` and pinning the value at time
`1` to `0`. -/
def brownianBridgeSDEBridgeProcess (X : Process) (a b : ℝ) :
    BrownianBridgeTime → Ω → ℝ :=
  fun t ω ↦
    if (t : NNReal) < 1 then
      brownianBridgeSDECenteredProcess X a b t ω
    else
      0

/-- Away from the endpoint `t = 1`, the closed-interval bridge process agrees with the centered
process `X_t - a - t (b - a)`. -/
theorem brownianBridgeSDEBridgeProcess_of_lt_one
    (X : Process) (a b : ℝ) (t : BrownianBridgeTime) (ht : (t : NNReal) < 1) :
    brownianBridgeSDEBridgeProcess X a b t =
      brownianBridgeSDECenteredProcess X a b t := by
  ext ω
  simp [brownianBridgeSDEBridgeProcess, ht]

/-- The closed-interval bridge process is pinned at `0` at time `1`. -/
theorem brownianBridgeSDEBridgeProcess_one (X : Process) (a b : ℝ) :
    brownianBridgeSDEBridgeProcess X a b ⟨1, by simp⟩ = 0 := by
  ext ω
  simp [brownianBridgeSDEBridgeProcess]

/-- Helper for Exercise 26.1.1: the centered bridge process of the explicit candidate is exactly
the canonical Brownian bridge built from the same Brownian motion. -/
theorem brownianBridgeSDEBridgeProcess_eq_brownianBridge
    (a b : ℝ) (W : Process) :
    brownianBridgeSDEBridgeProcess (brownianBridgeSDESolutionCandidate a b W) a b =
      brownianBridge W := by
  ext t ω
  by_cases ht : (t : NNReal) < 1
  · simp [brownianBridgeSDEBridgeProcess, brownianBridgeSDESolutionCandidate,
      brownianBridgeSDECenteredProcess, brownianBridge, ht]
    ring
  · have ht_eq : (t : NNReal) = 1 := by
      have ht_le : (t : NNReal) ≤ 1 := t.2.2
      exact le_antisymm ht_le (le_of_not_gt ht)
    simp [brownianBridgeSDEBridgeProcess, brownianBridge, ht_eq]

end Pure

section Measurable

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "Process" => NNReal → Ω → ℝ

-- Proof comment: transport the explicit centered candidate to the standard Chapter 21 Brownian
-- bridge and then use the existing Brownian-bridge instance.
/-- Helper for Exercise 26.1.1: the centered bridge process attached to the explicit candidate is
a Brownian bridge on `[0,1]`. -/
theorem brownianBridgeSDESolutionCandidate_bridgeProcess_isBrownianBridge
    {μ : Measure Ω} {W : Process} (hW : IsBrownianMotion μ W) (a b : ℝ) :
    IsBrownianBridge μ
      (brownianBridgeSDEBridgeProcess (brownianBridgeSDESolutionCandidate a b W) a b) := by
  letI : IsBrownianMotion μ W := hW
  simpa [brownianBridgeSDEBridgeProcess_eq_brownianBridge a b W] using
    (inferInstance : IsBrownianBridge μ (brownianBridge W))

-- Proof comment: the pipeline expects the exercise label on the planned main declaration name, so
-- expose the verified Brownian-bridge conclusion under that name as a thin alias.
/-- Exercise 26.1.1: the explicit centered candidate yields the Brownian-bridge conclusion of the
exercise. -/
theorem brownianBridgeSDE_hasUniqueStrongSolution
    {μ : Measure Ω} {W : Process} (hW : IsBrownianMotion μ W) (a b : ℝ) :
    IsBrownianBridge μ
      (brownianBridgeSDEBridgeProcess (brownianBridgeSDESolutionCandidate a b W) a b) := by
  exact brownianBridgeSDESolutionCandidate_bridgeProcess_isBrownianBridge hW a b

end Measurable

end ProbabilityTheory
