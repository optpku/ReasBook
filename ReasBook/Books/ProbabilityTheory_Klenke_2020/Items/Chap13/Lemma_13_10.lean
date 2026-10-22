/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.Topology.MetricSpace.ThickenedIndicator

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval
open Set

noncomputable section

universe u

variable {E : Type u} [PseudoMetricSpace E]

/-- Lemma 13.10: the canonical thickened-indicator cutoff yields a real-valued Lipschitz function
with values in `[0,1]`, equal to `1` on `A` and equal to `0` once the distance to `A` is at least
`ε`. In particular, this gives the source's closed-set cutoff. -/
-- Proof sketch: take `ρ x = thickenedIndicator hε A x`; this is `ε⁻¹`-Lipschitz by
-- `lipschitzWith_thickenedIndicator`, it takes values in `I` by `thickenedIndicator_le_one`, it
-- is `1` on `A` by `thickenedIndicator_one`, and it vanishes off the `ε`-thickening by
-- `thickenedIndicator_zero`.
lemma exists_lipschitz_closed_set_cutoff (A : Set E) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : E → ℝ,
      LipschitzWith ε.toNNReal⁻¹ ρ ∧
      MapsTo ρ univ I ∧
      (∀ ⦃x : E⦄, x ∈ A → ρ x = 1) ∧
      ∀ ⦃x : E⦄, ε ≤ Metric.infDist x A → ρ x = 0 := by
  let ρ : BoundedContinuousFunction E NNReal := thickenedIndicator hε A
  refine ⟨fun x ↦ (ρ x : ℝ), ?_, ?_, ?_, ?_⟩
  · simpa [ρ] using lipschitzWith_thickenedIndicator hε A
  · intro x _
    constructor
    · exact_mod_cast (show (0 : NNReal) ≤ ρ x from bot_le)
    · exact_mod_cast (show ρ x ≤ (1 : NNReal) by simpa [ρ] using thickenedIndicator_le_one hε A x)
  · intro x hx
    have hρ : ρ x = (1 : NNReal) := by
      simpa [ρ] using thickenedIndicator_one hε A hx
    simpa using congrArg (fun r : NNReal ↦ (r : ℝ)) hρ
  · intro x hx
    have hx' : x ∉ Metric.thickening ε A := by
      rw [Metric.mem_thickening_iff]
      rintro ⟨z, hzA, hzx⟩
      exact not_lt_of_ge hx ((Metric.infDist_le_dist_of_mem hzA).trans_lt hzx)
    have hρ : ρ x = (0 : NNReal) := by
      simpa [ρ] using thickenedIndicator_zero hε A hx'
    simpa using congrArg (fun r : NNReal ↦ (r : ℝ)) hρ
