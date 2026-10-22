/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_5

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

universe u

variable {Ω : Type u}

-- Proof sketch: an ergodic measurable invariant event is almost empty or almost full; on a
-- probability space this is exactly the bridge between positive probability and almost sure
-- occurrence.
/-- On a probability space, any measurable invariant event for an ergodic transformation has
positive probability if and only if it occurs almost surely. -/
theorem ae_iff_measure_pos_of_ergodic_of_is_invariant_event
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : Ergodic τ P) {A : Set Ω} (hInvariantEvent : is_invariant_event τ A) :
    (∀ᵐ ω ∂P, ω ∈ A) ↔ 0 < P A := by
  change MeasurableSet A ∧ τ ⁻¹' A = A at hInvariantEvent
  have hA : MeasurableSet A := hInvariantEvent.1
  have hτA : τ ⁻¹' A = A := hInvariantEvent.2
  constructor
  · intro hAae
    have hAuniv : A =ᵐ[P] Set.univ := by
      simpa using hAae
    have hPA : P A = 1 := by
      simpa using measure_congr hAuniv
    simp [hPA]
  · intro hPA
    rcases hτ.toPreErgodic.ae_empty_or_univ hA hτA with hAempty | hAuniv
    · have hPA0 : P A = 0 := by
        simpa using measure_congr hAempty
      simp [hPA0] at hPA
    · simpa using hAuniv

variable [MeasurableSpace Ω]

-- Proof sketch: each Birkhoff sum is measurable by the recursive formula
-- `S_{n+1}(ω) = X₀(ω) + S_n(τ ω)`.
/-- The orbit partial sums `ω ↦ birkhoffSum τ X₀ n ω` are measurable for every `n` whenever `τ`
and `X₀` are measurable. -/
theorem measurable_birkhoffSum {τ : Ω → Ω} (hτ : Measurable τ) {X₀ : Ω → ℝ}
    (hX₀ : Measurable X₀) (n : ℕ) : Measurable (fun ω ↦ birkhoffSum τ X₀ n ω) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [show (fun ω ↦ birkhoffSum τ X₀ (n + 1) ω)
          = fun ω ↦ X₀ ω + birkhoffSum τ X₀ n (τ ω) by
            funext ω
            rw [birkhoffSum_succ']]
      exact hX₀.add (ih.comp hτ)

-- Proof sketch: combine `measurableSet_tendsto` with the shift-invariance proof coming from
-- `birkhoffSum_succ'`.
/-- The event that the orbit partial sums tend to `+∞` is an invariant event. -/
theorem is_invariant_event_orbit_partial_sum_tendsto_atTop {τ : Ω → Ω} (hτ : Measurable τ)
    {X₀ : Ω → ℝ} (hX₀ : Measurable X₀) :
    is_invariant_event τ {ω | Tendsto (fun n ↦ birkhoffSum τ X₀ n ω) atTop atTop} := by
  change MeasurableSet {ω | Tendsto (fun n ↦ birkhoffSum τ X₀ n ω) atTop atTop} ∧
      τ ⁻¹' {ω | Tendsto (fun n ↦ birkhoffSum τ X₀ n ω) atTop atTop}
        = {ω | Tendsto (fun n ↦ birkhoffSum τ X₀ n ω) atTop atTop}
  refine ⟨measurableSet_tendsto atTop (measurable_birkhoffSum hτ hX₀), ?_⟩
  ext ω
  constructor
  · intro h
    change Tendsto (fun n ↦ birkhoffSum τ X₀ n (τ ω)) atTop atTop at h
    have hEq : (fun n ↦ birkhoffSum τ X₀ (n + 1) ω)
        = fun n ↦ X₀ ω + birkhoffSum τ X₀ n (τ ω) := by
      funext n
      rw [birkhoffSum_succ']
    have hshift : Tendsto (fun n ↦ birkhoffSum τ X₀ (n + 1) ω) atTop atTop := by
      rw [hEq]
      simpa using tendsto_atTop_add_const_left atTop (X₀ ω) h
    exact (tendsto_add_atTop_iff_nat 1).1 hshift
  · intro h
    have hshift : Tendsto (fun n ↦ birkhoffSum τ X₀ (n + 1) ω) atTop atTop :=
      (tendsto_add_atTop_iff_nat 1).2 h
    have hEq : (fun n ↦ birkhoffSum τ X₀ (n + 1) ω)
        = fun n ↦ X₀ ω + birkhoffSum τ X₀ n (τ ω) := by
      funext n
      rw [birkhoffSum_succ']
    rw [hEq] at hshift
    have h' := tendsto_atTop_add_const_left atTop (-X₀ ω) hshift
    simpa [add_assoc] using h'

-- Proof sketch: combine the generic ergodic invariant-event bridge with the measurable/invariant
-- structure of the orbit-divergence event established above.
/-- Remark 20.22: the positive-probability criterion from Theorem 20.21 remains valid without an
integrability hypothesis. For an ergodic process, the event that the orbit partial sums tend to
`+∞` has positive probability if and only if it occurs almost surely. In Lean's `0`-based
indexing, `X₀` represents the textbook coordinate `X₁`. -/
theorem orbit_partial_sum_tendsto_atTop_ae_iff_measure_pos_of_ergodic
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : Ergodic τ P) {X₀ : Ω → ℝ} (hX₀ : Measurable X₀) :
    (∀ᵐ ω ∂P, Tendsto (fun n ↦ birkhoffSum τ X₀ n ω) atTop atTop) ↔
      0 < P {ω | Tendsto (fun n ↦ birkhoffSum τ X₀ n ω) atTop atTop} := by
  simpa using ae_iff_measure_pos_of_ergodic_of_is_invariant_event P hτ
    (is_invariant_event_orbit_partial_sum_tendsto_atTop hτ.measurable hX₀)
