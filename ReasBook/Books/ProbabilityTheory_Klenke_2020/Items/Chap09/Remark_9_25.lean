/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {ι : Type u} {Ω : Type v} [Preorder ι]
variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ι m0} {μ : Measure Ω}
variable [SigmaFiniteFiltration μ ℱ]
variable {X : ι → Ω → ℝ}

-- Proof sketch: apply `Martingale.setIntegral_eq` with the measurable set `Set.univ`, and rewrite
-- the resulting set integrals as expectations.
/-- Remark 9.25 (1): For a martingale, the expectation is constant in time: whenever `s ≤ t`, the
expectations of `X s` and `X t` agree. -/
theorem martingale_expectation_eq (hX : Martingale X ℱ μ) {s t : ι} (hst : s ≤ t) :
    μ[X s] = μ[X t] := by
  simpa [setIntegral_univ] using hX.setIntegral_eq hst MeasurableSet.univ

-- Proof sketch: for `s ≤ t`, use `Submartingale.setIntegral_le` on `Set.univ` to obtain
-- `μ[X s] ≤ μ[X t]`, then package the result as monotonicity.
/-- Remark 9.25 (2): For a submartingale, the expectation is monotone increasing in time. -/
theorem submartingale_expectation_monotone (hX : Submartingale X ℱ μ) :
    Monotone fun t ↦ μ[X t] := by
  intro s t hst
  simpa [setIntegral_univ] using hX.setIntegral_le hst MeasurableSet.univ

-- Proof sketch: for `s ≤ t`, use `Supermartingale.setIntegral_le` on `Set.univ` to obtain
-- `μ[X t] ≤ μ[X s]`, then package the result as antitonicity.
/-- Remark 9.25 (3): For a supermartingale, the expectation is monotone decreasing in time. -/
theorem supermartingale_expectation_antitone (hX : Supermartingale X ℱ μ) :
    Antitone fun t ↦ μ[X t] := by
  intro s t hst
  simpa [setIntegral_univ] using hX.setIntegral_le hst MeasurableSet.univ
