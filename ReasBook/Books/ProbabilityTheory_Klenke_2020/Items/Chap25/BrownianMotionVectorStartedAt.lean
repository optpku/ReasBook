/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.BrownianStartedAt
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

/-- A `State`-valued Brownian motion started from `x` is a process whose coordinates are
independent one-dimensional Brownian motions started from the corresponding coordinates of `x`. -/
@[mk_iff isBrownianMotionVectorStartedAt_iff]
class IsBrownianMotionVectorStartedAt
    (μ : Measure Ω) (W : VectorProcess) (x : State) : Prop where
  /-- Each coordinate process is a one-dimensional Brownian motion started at the corresponding
  coordinate of `x`. -/
  isBrownianMotionStartedAt : ∀ i : Fin d, IsBrownianMotionStartedAt μ (fun t ω ↦ W t ω i) (x i)
  /-- The coordinate processes are independent. -/
  iIndepFun : iIndepFun (fun i : Fin d ↦ fun ω t ↦ W t ω i) μ

attribute [simp] isBrownianMotionVectorStartedAt_iff

instance (μ : Measure Ω) (W : VectorProcess) (x : State) (i : Fin d)
    [hW : IsBrownianMotionVectorStartedAt μ W x] :
    IsBrownianMotionStartedAt μ (fun t ω ↦ W t ω i) (x i) :=
  hW.isBrownianMotionStartedAt i

/-- Helper for Brownian vectors started at a point: every deterministic-time marginal is strongly
measurable. -/
theorem brownianVectorStartedAt_stronglyMeasurable
    {μ : Measure Ω} {V : VectorProcess} {x : State}
    (hV : IsBrownianMotionVectorStartedAt μ V x) (t : NNReal) :
    StronglyMeasurable (V t) := by
  let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
  rw [stronglyMeasurable_iff_measurable]
  have hcoords : Measurable (ψ ∘ V t) := by
    -- Proof comment: the Euclidean marginal is measurable once every coordinate slice is
    -- measurable.
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa using (hV.isBrownianMotionStartedAt i).stronglyMeasurable t |>.measurable
  exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords

/-- A standard `d`-dimensional Brownian motion is Brownian motion started from `0`. -/
instance (μ : Measure Ω) (W : VectorProcess) [hW : IsStandardBrownianMotionVector μ W] :
    IsBrownianMotionVectorStartedAt μ W 0 where
  -- Proof comment: each coordinate is already a scalar Brownian motion, so the scalar owner
  -- instance upgrades it to a Brownian motion started at `0`.
  isBrownianMotionStartedAt i := by
    simpa using
      (inferInstance : IsBrownianMotionStartedAt μ (fun t ω ↦ W t ω i) 0)
  -- Proof comment: the coordinate independence is part of the standard Brownian vector data.
  iIndepFun := hW.iIndepFun

end ProbabilityTheory
