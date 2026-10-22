/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

/-- A `State`-valued process is a standard `d`-dimensional Brownian motion if each coordinate is a
real Brownian motion and the coordinate family is independent. -/
@[mk_iff isStandardBrownianMotionVector_iff]
class IsStandardBrownianMotionVector (μ : Measure Ω) (W : VectorProcess) : Prop where
  /-- Each coordinate process is a real Brownian motion. -/
  isBrownianMotion : ∀ i : Fin d, IsBrownianMotion μ (fun t ω ↦ W t ω i)
  /-- The coordinate family is independent. -/
  iIndepFun : iIndepFun (fun i : Fin d ↦ fun ω t ↦ W t ω i) μ

attribute [simp] isStandardBrownianMotionVector_iff

instance (μ : Measure Ω) (W : VectorProcess) (i : Fin d)
    [hW : IsStandardBrownianMotionVector μ W] :
    IsBrownianMotion μ (fun t ω ↦ W t ω i) :=
  hW.isBrownianMotion i

namespace IsStandardBrownianMotionVector

/-- Every time marginal of a standard Brownian vector is strongly measurable. -/
theorem stronglyMeasurable
    {μ : Measure Ω} {W : VectorProcess} (hW : IsStandardBrownianMotionVector μ W)
    (t : NNReal) :
    StronglyMeasurable (W t) := by
  let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
  rw [stronglyMeasurable_iff_measurable]
  have hcoords : Measurable (ψ ∘ W t) := by
    -- Proof comment: each coordinate marginal is a scalar Brownian coordinate, hence measurable
    -- once the scalar owner theorem is restored.
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa using (hW.isBrownianMotion i).stronglyMeasurable t |>.measurable
  exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords

end IsStandardBrownianMotionVector

end ProbabilityTheory
