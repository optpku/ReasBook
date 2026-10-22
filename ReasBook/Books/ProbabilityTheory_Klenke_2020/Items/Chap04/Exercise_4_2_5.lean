/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENNReal
open MeasureTheory

/-- Exercise 4.2.5: every real-valued `L^p` function on `ℝ` with respect to Lebesgue measure can
be approximated arbitrarily well in `eLpNorm` by a continuous real-valued function. -/
-- Proof sketch: apply the canonical smooth compact-support approximation theorem
-- `MemLp.exist_eLpNorm_sub_le` with tolerance `ε / 2`, then forget smoothness to continuity and
-- upgrade `≤ ENNReal.ofReal (ε / 2)` to the strict inequality required here.
theorem exists_continuous_eLpNorm_sub_lt_of_memLp
    {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℝ,
      Continuous h ∧ eLpNorm (f - h) (ENNReal.ofReal p) volume < ENNReal.ofReal ε := by
  have hε₂ : 0 < ε / 2 := by positivity
  have hp' : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  obtain ⟨h, _hh_compact, hh_smooth, hh_le⟩ :=
    hf.exist_eLpNorm_sub_le ENNReal.ofReal_ne_top hp' hε₂
  have hhalf_lt : ε / 2 < ε := by linarith
  have hε₂_lt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε := by
    simpa using (ENNReal.ofReal_lt_ofReal_iff hε).2 hhalf_lt
  exact ⟨h, hh_smooth.continuous, lt_of_le_of_lt hh_le hε₂_lt⟩
