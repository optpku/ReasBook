/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Notation_4_5.DiscreteEM
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

public section

noncomputable section

open scoped BigOperators

namespace DiscreteEM

universe u v w

variable {Theta : Type u} {X : Type v} {Y : Type w}

/-- Helper for Proposition 4.37: the real-valued posterior weights sum to `1`. -/
lemma sum_posteriorPmf_toReal_eq_one
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) :
    (∑ x, (posteriorPmf joint theta y hy x).toReal) = 1 := by
  have hsum : ∑ x, posteriorPmf joint theta y hy x = 1 := by
    -- Rewrite the posterior mass function back to the normalized joint ratio.
    simpa [posteriorPmf_apply] using posteriorPmf_mass_eq_one joint theta y hy
  -- Convert the finite `ENNReal` sum into a real-valued sum termwise.
  calc
    ∑ x, (posteriorPmf joint theta y hy x).toReal
        = ENNReal.toReal (∑ x, posteriorPmf joint theta y hy x) := by
          symm
          refine ENNReal.toReal_sum ?_
          intro x hx
          exact PMF.apply_ne_top (posteriorPmf joint theta y hy) x
    _ = 1 := by rw [hsum, ENNReal.toReal_one]

/-- Helper for Proposition 4.37: positive reference posterior weight forces positive
candidate posterior weight under the EM support condition. -/
lemma posteriorPmf_toReal_pos_of_reference_pos
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta thetaV : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) (hV : observedPmf joint thetaV y ≠ 0)
    (hSupport : ∀ x, posteriorPmf joint thetaV y hV x ≠ 0 → joint theta (x, y) ≠ 0)
    {x : X} :
    0 < (posteriorPmf joint thetaV y hV x).toReal →
      0 < (posteriorPmf joint theta y hy x).toReal := by
  intro hx
  have href_ne_zero : posteriorPmf joint thetaV y hV x ≠ 0 := by
    -- A strictly positive real coercion comes from a nonzero posterior mass.
    exact fun hzero => by simpa [hzero] using hx
  have hjoint_ne_zero : joint theta (x, y) ≠ 0 :=
    hSupport x href_ne_zero
  have hpost_ne_zero : posteriorPmf joint theta y hy x ≠ 0 := by
    -- The support hypothesis keeps the normalized candidate posterior nonzero.
    rw [posteriorPmf_apply]
    exact ENNReal.div_ne_zero.2 ⟨hjoint_ne_zero, PMF.apply_ne_top (observedPmf joint theta) y⟩
  -- Convert the nonzero `ENNReal` posterior mass back to positive real form.
  exact ENNReal.toReal_pos_iff.mpr
    ⟨pos_iff_ne_zero.mpr hpost_ne_zero, PMF.apply_lt_top (posteriorPmf joint theta y hy) x⟩

/-- Helper for Proposition 4.37: the scalar log-gap dominates the mass gap. -/
lemma weightedLogDiff_ge_massDiff {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a → 0 < b) :
    a * (Real.log a - Real.log b) ≥ a - b := by
  by_cases ha0 : a = 0
  · -- At zero reference weight, the right-hand side is nonpositive.
    subst ha0
    nlinarith
  have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
  have hb_pos : 0 < b := hab ha_pos
  have hbase : a / b - 1 ≤ (a / b) * Real.log (a / b) :=
    Real.self_sub_one_le_mul_log (x := a / b) (by positivity)
  have hscaled : b * (a / b - 1) ≤ b * ((a / b) * Real.log (a / b)) :=
    mul_le_mul_of_nonneg_left hbase hb
  have hleft : b * (a / b - 1) = a - b := by
    field_simp [ha_pos.ne, hb_pos.ne]
  have hright :
      b * ((a / b) * Real.log (a / b)) = a * (Real.log a - Real.log b) := by
    rw [Real.log_div ha_pos.ne' hb_pos.ne']
    field_simp [ha_pos.ne, hb_pos.ne]
  -- Rescale the standard inequality for `x * log x` back to `(a, b)`.
  rw [hleft, hright] at hscaled
  exact hscaled

/-- The entropy correction term in the discrete EM decomposition is maximized at
the reference parameter `thetaV`, so replacing `thetaV` by `theta` cannot increase
`hFunction`. -/
theorem hFunction_le_self
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta thetaV : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) (hV : observedPmf joint thetaV y ≠ 0)
    (hSupport : ∀ x, posteriorPmf joint thetaV y hV x ≠ 0 → joint theta (x, y) ≠ 0) :
    hFunction joint theta thetaV y hy hV ≤ hFunction joint thetaV thetaV y hV hV := by
  -- Rewrite both entropy terms as finite sums of posterior weights times posterior logs.
  rw [hFunction_def, hFunction_def]
  simp_rw [conditionalLogLikelihood_def]
  let w : X → ℝ := fun x ↦ (posteriorPmf joint thetaV y hV x).toReal
  let p : X → ℝ := fun x ↦ (posteriorPmf joint theta y hy x).toReal
  have hw_nonneg : ∀ x, 0 ≤ w x := by
    intro x
    simp [w]
  have hp_nonneg : ∀ x, 0 ≤ p x := by
    intro x
    simp [p]
  have hmassV : ∑ x, w x = 1 := by
    -- The reference posterior is a probability mass function.
    simpa [w] using sum_posteriorPmf_toReal_eq_one joint thetaV y hV
  have hmass : ∑ x, p x = 1 := by
    -- The candidate posterior is also normalized.
    simpa [p] using sum_posteriorPmf_toReal_eq_one joint theta y hy
  have hterm :
      ∀ x, w x * (Real.log (w x) - Real.log (p x)) ≥ w x - p x := by
    intro x
    -- Apply the scalar log bound pointwise to the two posterior masses at `x`.
    refine weightedLogDiff_ge_massDiff (a := w x) (b := p x) (hw_nonneg x) (hp_nonneg x) ?_
    intro hw_pos
    simpa [w, p] using
      posteriorPmf_toReal_pos_of_reference_pos joint theta thetaV y hy hV hSupport
        (x := x) hw_pos
  have hsum_nonneg : 0 ≤ ∑ x, w x * (Real.log (w x) - Real.log (p x)) := by
    have hsum_lower :
        ∑ x, (w x - p x) ≤ ∑ x, w x * (Real.log (w x) - Real.log (p x)) := by
      -- Sum the pointwise lower bounds over the finite hidden-state space.
      exact Finset.sum_le_sum fun x hx ↦ hterm x
    have hsum_zero : ∑ x, (w x - p x) = 0 := by
      -- Both posterior families have total mass `1`, so the mass-difference sum vanishes.
      calc
        ∑ x, (w x - p x) = (∑ x, w x) - ∑ x, p x := by
          rw [Finset.sum_sub_distrib]
        _ = 0 := by simp [hmassV, hmass]
    linarith
  have hgap :
      0 ≤ (∑ x, w x * Real.log (w x)) - ∑ x, w x * Real.log (p x) := by
    -- Expand the summed log-gap into the difference of the two entropy sums.
    calc
      0 ≤ ∑ x, w x * (Real.log (w x) - Real.log (p x)) := hsum_nonneg
      _ = (∑ x, w x * Real.log (w x)) - ∑ x, w x * Real.log (p x) := by
        calc
          ∑ x, w x * (Real.log (w x) - Real.log (p x))
              = ∑ x, (w x * Real.log (w x) - w x * Real.log (p x)) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  rw [mul_sub]
          _ = (∑ x, w x * Real.log (w x)) - ∑ x, w x * Real.log (p x) := by
                  rw [Finset.sum_sub_distrib]
  -- Repackage the nonnegative entropy gap as the desired order relation.
  exact sub_nonneg.mp hgap

/-- Proposition 4.37. If the discrete EM auxiliary function `qFunction` at a
candidate parameter `theta` is at least its value at the current iterate `thetaV`,
then the observed-data log-likelihood `observedLogLikelihood` does not decrease. -/
theorem observedLogLikelihood_ge_of_qFunction_ge
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta thetaV : Theta) (y : Y)
    (hV : observedPmf joint thetaV y ≠ 0)
    (hSupport : ∀ x, posteriorPmf joint thetaV y hV x ≠ 0 → joint theta (x, y) ≠ 0)
    (hQ : qFunction joint theta thetaV y hV ≥ qFunction joint thetaV thetaV y hV) :
    observedLogLikelihood joint theta y ≥ observedLogLikelihood joint thetaV y := by
  have hy : observedPmf joint theta y ≠ 0 :=
    observedPmf_ne_zero_of_posterior_support joint theta thetaV y hV hSupport
  have hSelfSupport : ∀ x, posteriorPmf joint thetaV y hV x ≠ 0 → joint thetaV (x, y) ≠ 0 := by
    intro x hx hJoint
    exact hx <| by simp [posteriorPmf_apply, hJoint]
  calc
    observedLogLikelihood joint thetaV y
        = qFunction joint thetaV thetaV y hV - hFunction joint thetaV thetaV y hV hV := by
      exact observedLogLikelihood_eq_qFunction_sub_hFunction_of_nonvanishing
        joint thetaV thetaV y hV hV hSelfSupport
    _ ≤ qFunction joint theta thetaV y hV - hFunction joint thetaV thetaV y hV hV := by
      exact sub_le_sub_right hQ _
    _ ≤ qFunction joint theta thetaV y hV - hFunction joint theta thetaV y hy hV := by
      exact sub_le_sub_left (hFunction_le_self joint theta thetaV y hy hV hSupport) _
    _ = observedLogLikelihood joint theta y := by
      exact (observedLogLikelihood_eq_qFunction_sub_hFunction_of_nonvanishing
        joint theta thetaV y hy hV hSupport
      ).symm

end DiscreteEM
