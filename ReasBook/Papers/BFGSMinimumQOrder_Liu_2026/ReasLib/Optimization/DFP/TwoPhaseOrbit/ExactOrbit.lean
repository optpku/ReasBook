module

public import ReasLib.Optimization.DFP.Orbit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ExactCycle.MetricTransport
import ReasLib.Optimization.DFP.AbstractSecantStep.OrthogonalTransport
import Mathlib.Tactic.Abel
import Mathlib.Tactic

/-!
# Exact classical DFP orbits from exact two-phase cycles

An exact two-phase orbit already contains all point, gradient, metric, and
step-length recurrences in phase coordinates.  Orthogonal transport turns
those phasewise certificates into the flattened classical inverse-form DFP
recurrence for any objective realizing the prescribed endpoint gradients.
-/

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoPhaseOrbit

/-- Exactness of every two-phase cycle, together with gradient certificates
for an objective at the flattened endpoints, makes the flattened data a
classical inverse-form DFP orbit. -/
theorem isOrbit_of_exactCycles (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hgradient : ∀ k, HasGradientAt f (orbit.endpointGradient k)
      (orbit.endpoint k)) :
    DFP.IsOrbit f (orbit.endpointStepLength h_exact)
      orbit.endpoint orbit.endpointGradient orbit.endpointMetric := by
  have hphase (j : ℕ) (i : Fin 2) :
      orbit.endpoint (2 * j + i.val + 1) =
          orbit.endpoint (2 * j + i.val) +
            orbit.endpointStepLength h_exact (2 * j + i.val) •
              (-WithLp.toLp 2
                (orbit.endpointMetric (2 * j + i.val) *ᵥ
                  WithLp.ofLp (orbit.endpointGradient (2 * j + i.val)))) ∧
        orbit.endpointMetric (2 * j + i.val + 1) =
          Matrix.inverseDFPUpdate (orbit.endpointMetric (2 * j + i.val))
            (WithLp.ofLp
              (orbit.endpointStepLength h_exact (2 * j + i.val) •
                (-WithLp.toLp 2
                  (orbit.endpointMetric (2 * j + i.val) *ᵥ
                    WithLp.ofLp (orbit.endpointGradient (2 * j + i.val))))))
            (WithLp.ofLp
              (orbit.endpointGradient (2 * j + i.val + 1) -
                orbit.endpointGradient (2 * j + i.val))) := by
    let z := (h_exact j).step i
    let R := (orbit.state j).phaseFrame i
    have hRspecial : R ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
      exact (h_exact j).valid.phaseFrame_mem_specialOrthogonal i
    have hR : R ∈ Matrix.orthogonalGroup (Fin 2) ℝ :=
      (Matrix.mem_specialOrthogonalGroup_iff.mp hRspecial).1
    apply DFP.AbstractSecantStep.recurrences_of_orthogonalTransport
      (z := z) (R := R) (hR := hR)
    · exact endpointStepLength_eq_exactStep orbit h_exact j i
    · have hstep := endpointStep_eq_exactStepTransport orbit j i (h_exact j)
      calc
        orbit.endpoint (2 * j + i.val + 1) =
            orbit.endpoint (2 * j + i.val) +
              (orbit.endpoint (2 * j + i.val + 1) -
                orbit.endpoint (2 * j + i.val)) := by
          abel
        _ = orbit.endpoint (2 * j + i.val) +
            WithLp.toLp 2 (R *ᵥ z.displacement) := by
          rw [hstep]
    · exact endpointGradient_eq_exactStepTransport orbit j i (h_exact j)
    · exact endpointGradient_succ_eq_exactStepTransport orbit j i (h_exact j)
    · exact endpointMetric_eq_exactStepTransport orbit j i (h_exact j)
    · exact endpointMetric_succ_eq_exactStepTransport orbit j i (h_exact j)
  apply DFP.IsOrbit.ofHasGradientAt
  · intro k
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [endpointStepLength_even]
      exact ((h_exact j).step 0).stepLength_pos
    · rw [endpointStepLength_odd]
      exact ((h_exact j).step 1).stepLength_pos
  · exact hgradient
  · intro k
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · have hzero := (hphase j (0 : Fin 2)).1
      have hindex : 2 * j + (0 : Fin 2).val = 2 * j := by omega
      rw [hindex] at hzero
      simpa only [DFP.steps_apply, DFP.directions_apply] using hzero
    · have hone := (hphase j (1 : Fin 2)).1
      have hindex : 2 * j + (1 : Fin 2).val = 2 * j + 1 := by omega
      rw [hindex] at hone
      simpa only [DFP.steps_apply, DFP.directions_apply] using hone
  · intro k
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · have hzero := (hphase j (0 : Fin 2)).2
      have hindex : 2 * j + (0 : Fin 2).val = 2 * j := by omega
      rw [hindex] at hzero
      simpa only [DFP.steps_apply, DFP.directions_apply,
        DFP.gradientChanges_apply] using hzero
    · have hone := (hphase j (1 : Fin 2)).2
      have hindex : 2 * j + (1 : Fin 2).val = 2 * j + 1 := by omega
      rw [hindex] at hone
      simpa only [DFP.steps_apply, DFP.directions_apply,
        DFP.gradientChanges_apply] using hone

end DFP.TwoPhaseOrbit
