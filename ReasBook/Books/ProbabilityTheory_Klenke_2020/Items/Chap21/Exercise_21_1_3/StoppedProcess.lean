/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Topology.Defs.Basic
import Mathlib.Probability.Process.Stopping
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_21

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u}
variable {E : Type v} [TopologicalSpace E]

-- Proof sketch: fix a sample point `ω`. Along that path, the map `t ↦ min t (τ ω).untopA` is
-- right continuous, so composing the right-continuous path `t ↦ X t ω` with this time change
-- preserves right continuity.
/-- Helper for Exercise 21.1.3: the stopped process of a right-continuous process is still right
continuous. -/
theorem stoppedProcess_hasRightContinuousPaths
    {X : NNReal → Ω → E} (hX_rc : HasRightContinuousPaths X) {τ : Ω → ENNReal} :
    HasRightContinuousPaths (stoppedProcess X τ) := by
  intro ω t
  by_cases hτtop : τ ω = ⊤
  · -- Proof comment: if `τ ω = ⊤`, the stopped path is just the original path.
    simpa [stoppedProcess, hτtop] using hX_rc ω t
  · lift τ ω to NNReal using hτtop with c hc
    let φ : NNReal → NNReal := fun s ↦ min s c
    have hφ_cont : ContinuousWithinAt φ (Set.Ici t) t :=
      (continuous_id.min continuous_const).continuousWithinAt
    have hφ_maps : MapsTo φ (Set.Ici t) (Set.Ici (φ t)) := by
      intro s hs
      exact min_le_min_right c hs
    have hcomp : ContinuousWithinAt (fun s : NNReal ↦ X (φ s) ω) (Set.Ici t) t :=
      ContinuousWithinAt.comp (hX_rc ω (φ t)) hφ_cont hφ_maps
    have hstop_eq : ∀ s : NNReal, stoppedProcess X τ s ω = X (φ s) ω := by
      intro s
      rw [stoppedProcess, ← hc]
      by_cases hs : s ≤ c
      · have hs_enn : (s : ENNReal) ≤ (c : ENNReal) := by exact_mod_cast hs
        have hcoe : min (↑s : ENNReal) ↑c = (s : ENNReal) := by
          simp [hs_enn]
        calc
          X (min (↑s : ENNReal) ↑c).untopA ω = X ((↑s : ENNReal).untopA) ω := by
            exact congrArg (fun z : ENNReal ↦ X z.untopA ω) hcoe
          _ = X s ω := by
            rfl
          _ = X (φ s) ω := by
            simp [φ, hs]
      · have hc_enn : (c : ENNReal) ≤ (s : ENNReal) := by exact_mod_cast le_of_not_ge hs
        have hcoe : min (↑s : ENNReal) ↑c = (c : ENNReal) := by
          simp [hc_enn]
        calc
          X (min (↑s : ENNReal) ↑c).untopA ω = X ((↑c : ENNReal).untopA) ω := by
            exact congrArg (fun z : ENNReal ↦ X z.untopA ω) hcoe
          _ = X c ω := by
            rfl
          _ = X (φ s) ω := by
            simp [φ, le_of_not_ge hs]
    -- Proof comment: on the finite branch, stopping composes the original path with the
    -- continuous time change `s ↦ min s c`.
    exact hcomp.congr_of_mem (fun s _ ↦ hstop_eq s) (by simpa using hstop_eq t)

end ProbabilityTheory
