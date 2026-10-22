/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_25

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} {ι : Type v}
variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
variable [Countable ι] [OrderBot ι]
variable {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ι m0}
variable [SigmaFiniteFiltration μ ℱ]

/- Lemma 10.10 is `bridge/view`: the owner optional-sampling statement is the canonical mathlib
theorem `Martingale.stoppedValue_ae_eq_condExp_of_le_const`, and the source-level sampled process
`ω ↦ X (τ ω) ω` is its finite-valued stopping-time view via `stoppedValue X fun ω ↦ (τ ω :
WithTop ι)`. -/
recall Martingale.stoppedValue_ae_eq_condExp_of_le_const

-- Proof sketch: integrate the optional-sampling identity from
-- `MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le_const`, use `integral_condExp` on the stopping-time
-- σ-algebra, and then use constancy of expectations for martingales between the initial time `⊥`
-- and the terminal time `T`.
omit [FirstCountableTopology ι] in
/-- The expectation of a martingale at a finite stopping time agrees with its initial
expectation. -/
theorem martingale_expectation_stopping_time_eq_initial
    {X : ι → Ω → ℝ} {τ : Ω → ι} {T : ι} (hX : Martingale X ℱ μ)
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ι)) (hτ_le : ∀ ω, τ ω ≤ T) :
    μ[stoppedValue X fun ω ↦ (τ ω : WithTop ι)] = μ[X ⊥] := by
  have hτ_le' : ∀ ω, (τ ω : WithTop ι) ≤ T := fun ω ↦ mod_cast hτ_le ω
  calc
    μ[stoppedValue X fun ω ↦ (τ ω : WithTop ι)] = μ[μ[X T | hτ.measurableSpace]] := by
      exact integral_congr_ae (hX.stoppedValue_ae_eq_condExp_of_le_const hτ hτ_le')
    _ = μ[X T] := by
      rw [integral_condExp (hτ.measurableSpace_le_of_le hτ_le')]
    _ = μ[X ⊥] := by
      simpa using (martingale_expectation_eq hX bot_le).symm
