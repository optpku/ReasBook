/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MeasureTheory

open MeasureTheory

universe u

section

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω} [IsFiniteMeasure μ] [NeZero μ]
variable {ℱ : Filtration ℕ mΩ}

-- Proof sketch: since `stoppedValue X τ_b` is almost surely the constant `b`, its conditional
-- expectation with respect to `ℱ 0` is also almost surely the constant `b` by `condExp_const`.
-- The strict inequality `X 0 < b` almost surely then rules out almost-sure equality between
-- `X 0` and that conditional expectation.
/-- Remark 10.18: if the stopped value `X_{τ_b}` is almost surely the constant level `b` and the
initial value `X_0` is almost surely strictly smaller than `b`, then the optional-sampling
equality at time `0` fails for this stopped process. This formalizes the remark's warning that the
optional sampling conclusion can fail for an unbounded stopping time on a nontrivial finite
measure space. -/
theorem optional_sampling_equality_fails_of_constant_stopped_value {X : ℕ → Ω → ℝ}
    {τ_b : Ω → ℕ∞} {b : ℝ}
    (hXτb : stoppedValue X τ_b =ᵐ[μ] fun _ ↦ b)
    (hX0_lt : ∀ᵐ ω ∂μ, X 0 ω < b) :
    ¬ (μ[stoppedValue X τ_b | ℱ 0] =ᵐ[μ] X 0) := by
  intro hEq
  have hX0_eq : X 0 =ᵐ[μ] fun _ ↦ b := hEq.symm.trans <| by
    simpa [condExp_const (ℱ.le 0) b] using
      (condExp_congr_ae hXτb :
        μ[stoppedValue X τ_b | ℱ 0] =ᵐ[μ] μ[fun _ : Ω ↦ b | ℱ 0])
  have hFalse : ∀ᵐ ω ∂μ, False := by
    filter_upwards [hX0_eq, hX0_lt] with ω hω_eq hω_lt
    simp [hω_eq] at hω_lt
  have hμ0 : μ Set.univ = 0 := by
    simpa [ae_iff] using hFalse
  exact (Measure.measure_univ_ne_zero.2 <| NeZero.ne μ) hμ0

end
