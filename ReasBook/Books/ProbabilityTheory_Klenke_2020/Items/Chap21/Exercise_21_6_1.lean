/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_79
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_31

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace ProbabilityTheory

local notation "Ω" => BrownianPathSpace

local instance : MeasurableSpace Ω := borel Ω

local instance : BorelSpace Ω := ⟨rfl⟩

/-- The extended nonnegative path supremum on the chapter owner `C([0, ∞), ℝ)`. For paths with
`ω 0 = 0`, this is the natural `sup_{t ≥ 0} ω(t)` viewed in `ENNReal`. -/
def brownianPathSupremum (ω : Ω) : ENNReal :=
  ⨆ t : NNReal, ENNReal.ofReal (ω t)

-- Proof sketch: continuity on `[0, ∞)` implies that the supremum over all times agrees with the
-- supremum over the countable dense subset `ℚ≥0`, after viewing the values in `ENNReal` via
-- `ENNReal.ofReal`.
/-- The path supremum is the supremum of the values at nonnegative rational times. -/
theorem brownianPathSupremum_eq_iSup_nonnegRationals :
    brownianPathSupremum =
      fun ω ↦ ⨆ q : ℚ≥0, ENNReal.ofReal (ω (q : NNReal)) := by
  funext ω
  let fω : NNReal → ENNReal := fun t ↦ ENNReal.ofReal (ω t)
  -- Continuity lets us compare the supremum on all times with the supremum on a dense subset.
  have hcont : Continuous fω := ENNReal.continuous_ofReal.comp ω.continuous
  have hDense : Dense (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := denseRange_nnratCast
  -- The dense rational times already determine the supremum of the continuous path.
  calc
    brownianPathSupremum ω = ⨆ t : NNReal, fω t := by
      simp [brownianPathSupremum, fω]
    _ = ⨆ s : Set.range (fun q : ℚ≥0 ↦ (q : NNReal)), fω s := by
      exact (hDense.ciSup' hcont).symm
    _ = ⨆ q : ℚ≥0, fω (q : NNReal) := by
      rw [iSup_range']
    _ = ⨆ q : ℚ≥0, ENNReal.ofReal (ω (q : NNReal)) := by
      simp [fω]

-- Proof sketch: rewrite `brownianPathSupremum` as the supremum over the countable family of
-- evaluations at nonnegative rational times, use measurability of each coordinate map, and then
-- apply countable-supremum measurability in `ENNReal`.
/-- Exercise 21.6.1: on the continuous path space `C([0, ∞), ℝ)`, the map
`F∞(ω) = sup {ω(t) | t ∈ [0, ∞)}` is measurable for the coordinate `σ`-algebra `A`. For Brownian
paths started at `0`, this is the textbook path supremum. -/
theorem measurable_brownianPathSupremum :
    Measurable[⨆ t : NNReal, MeasurableSpace.comap (fun ω : Ω ↦ ω t) (borel ℝ)]
      brownianPathSupremum := by
  rw [← generatedSigmaAlgebraFamily_eq_iSup_comap
      (fun _ : NNReal ↦ borel ℝ) (fun t (ω : Ω) ↦ ω t)]
  change Measurable[MeasurableSpace.comap ((↑) : Ω → NNReal → ℝ) MeasurableSpace.pi]
    brownianPathSupremum
  rw [continuousPathSpace_comap_pi_eq_borel, brownianPathSupremum_eq_iSup_nonnegRationals]
  refine Measurable.iSup fun q ↦ ?_
  simpa using (continuous_eval_const (q : NNReal)).measurable.ennreal_ofReal

end ProbabilityTheory
