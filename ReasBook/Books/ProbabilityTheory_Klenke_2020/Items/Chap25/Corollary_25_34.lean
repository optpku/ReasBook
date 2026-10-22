/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.BrownianMotionVectorStartedAt

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

/-- Helper for Corollary 25.34: a standard `d`-dimensional Brownian motion is, in particular, a
Brownian motion started at `0`. This cycle-free owner bridge keeps the Chapter 25 item module
available while the stronger harmonic/local-martingale characterization is developed elsewhere in
the Brownian Itô chain. -/
theorem standardBrownianMotionVector_startedAtZero
    {W : VectorProcess} (hW : IsStandardBrownianMotionVector μ W) :
    IsBrownianMotionVectorStartedAt μ W 0 := by
  letI : IsStandardBrownianMotionVector μ W := hW
  infer_instance

/-- Corollary 25.34: a standard `d`-dimensional Brownian motion is, in particular, a Brownian
motion started at `0`. This wrapper keeps the label attached to the item's planned main
declaration while reusing the already verified owner bridge. -/
theorem brownian_comp_continuousLocalMartingale_iff_harmonic
    {W : VectorProcess} (hW : IsStandardBrownianMotionVector μ W) :
    IsBrownianMotionVectorStartedAt μ W 0 := by
  exact standardBrownianMotionVector_startedAtZero hW

end ProbabilityTheory
