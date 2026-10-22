/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Example_23_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Theorem_23_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace ProbabilityTheory

open MeasureTheory
open Set

/-- Helper for Example 23.5: the symmetric two-point law on `ℝ` concentrated on `{-1, 1}`. -/
private noncomputable abbrev rademacherMeasure : Measure ℝ :=
  ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) +
    ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ))

/-- Helper for Example 23.5: the cumulant-generating function of the symmetric two-point law is
`t ↦ log (cosh t)`. -/
private theorem rademacherCgf_eq_logCosh (t : ℝ) :
    cgf id rademacherMeasure t = Real.log (Real.cosh t) := by
  have hleft :
      Integrable (fun ω : ℝ ↦ Real.exp (t * ω))
        ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) := by
    -- Proof comment: a single Dirac mass makes the exponential tilt a constant integrable
    -- function, and scalar multiplication preserves integrability.
    exact (integrable_dirac (a := (-1 : ℝ)) (by simp)).smul_measure (by norm_num)
  have hright :
      Integrable (fun ω : ℝ ↦ Real.exp (t * ω))
        ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) := by
    -- Proof comment: the same Dirac-mass argument handles the atom at `1`.
    exact (integrable_dirac (a := (1 : ℝ)) (by simp)).smul_measure (by norm_num)
  rw [cgf]
  -- Proof comment: evaluate the two atomic contributions to the mgf and rewrite the average of
  -- `exp t` and `exp (-t)` as `cosh t`.
  rw [show mgf id rademacherMeasure t = (1 / 2 : ℝ) * Real.exp (-t) + (1 / 2 : ℝ) * Real.exp t by
    change mgf (fun ω : ℝ ↦ ω) rademacherMeasure t = _
    rw [ProbabilityTheory.mgf_add_measure hleft hright]
    rw [ProbabilityTheory.mgf_smul_measure, ProbabilityTheory.mgf_smul_measure]
    simp [ProbabilityTheory.mgf_dirac']]
  rw [Real.cosh_eq]
  ring_nf

/-- Helper for Example 23.5: the explicit Rademacher Legendre objective is maximized at
`t = Real.artanh z` for `z ∈ (-1, 1)`. -/
private theorem rademacherObjective_le_stationaryValue {z t : ℝ}
    (hz : z ∈ Ioo (-1) 1) :
    z * t - Real.log (Real.cosh t) ≤
      z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) := by
  let u := t - Real.artanh z
  have hu : t = Real.artanh z + u := by
    -- Proof comment: shift the optimization variable so the stationary point becomes the origin.
    dsimp [u]
    ring
  have hwPlus : 0 ≤ (1 + z) / 2 := by
    linarith [hz.1]
  have hwMinus : 0 ≤ (1 - z) / 2 := by
    linarith [hz.2]
  have hwSum : (1 + z) / 2 + (1 - z) / 2 = 1 := by
    ring
  have hconv :
      Real.exp (((1 + z) / 2) * u + -((1 - z) / 2 * u)) ≤
        ((1 + z) / 2) * Real.exp u + ((1 - z) / 2) * Real.exp (-u) := by
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
      using (convexOn_exp.2 (x := u) (y := -u) (by simp) (by simp) hwPlus hwMinus hwSum)
  have hexponent : ((1 + z) / 2) * u + -((1 - z) / 2 * u) = z * u := by
    ring
  have hconv' :
      Real.exp (z * u) ≤
        ((1 + z) / 2) * Real.exp u + ((1 - z) / 2) * Real.exp (-u) := by
    simpa [hexponent] using hconv
  have hfactor :
      Real.cosh u + z * Real.sinh u =
        ((1 + z) / 2) * Real.exp u + ((1 - z) / 2) * Real.exp (-u) := by
    -- Proof comment: rewrite the shifted hyperbolic term in exponential coordinates.
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hfactor_le : Real.exp (z * u) ≤ Real.cosh u + z * Real.sinh u := by
    simpa [hfactor] using hconv'
  have hfactor_pos : 0 < Real.cosh u + z * Real.sinh u := by
    exact (Real.exp_pos (z * u)).trans_le hfactor_le
  have hcosh_pos : 0 < Real.cosh (Real.artanh z) := Real.cosh_pos _
  have hsinh_eq :
      Real.sinh (Real.artanh z) = z * Real.cosh (Real.artanh z) := by
    -- Proof comment: convert `tanh (artanh z) = z` into the linear relation between `sinh` and
    -- `cosh` at the maximizing tilt.
    have htanh : Real.tanh (Real.artanh z) = z := Real.tanh_artanh hz
    rw [Real.tanh_eq_sinh_div_cosh] at htanh
    exact (div_eq_iff hcosh_pos.ne').mp htanh
  have hcosh_add :
      Real.cosh (Real.artanh z + u) =
        Real.cosh (Real.artanh z) * (Real.cosh u + z * Real.sinh u) := by
    -- Proof comment: expand `cosh (artanh z + u)` and factor out the positive
    -- `cosh (artanh z)`.
    calc
      Real.cosh (Real.artanh z + u)
          = Real.cosh (Real.artanh z) * Real.cosh u +
              Real.sinh (Real.artanh z) * Real.sinh u := by
              rw [Real.cosh_add]
      _ = Real.cosh (Real.artanh z) * Real.cosh u +
            (z * Real.cosh (Real.artanh z)) * Real.sinh u := by
            rw [hsinh_eq]
      _ = Real.cosh (Real.artanh z) * (Real.cosh u + z * Real.sinh u) := by
            ring
  have hlog :
      Real.log (Real.cosh (Real.artanh z + u)) =
        Real.log (Real.cosh (Real.artanh z)) + Real.log (Real.cosh u + z * Real.sinh u) := by
    rw [hcosh_add, Real.log_mul hcosh_pos.ne' hfactor_pos.ne']
  have hzu_le : z * u ≤ Real.log (Real.cosh u + z * Real.sinh u) := by
    -- Proof comment: convert the convexity estimate for `exp` back to a logarithmic estimate.
    exact (Real.le_log_iff_exp_le hfactor_pos).2 hfactor_le
  calc
    z * t - Real.log (Real.cosh t)
        = z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) +
            (z * u - Real.log (Real.cosh u + z * Real.sinh u)) := by
            rw [hu, hlog]
            ring
    _ ≤ z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) := by
          linarith

-- `bridge/view` layer: on `(-1, 1)`, the optimizer of the Legendre transform for the symmetric
-- `{-1, 1}` law is `t = Real.artanh z`, so the variational problem reduces to the textbook
-- stationary value `z * artanh z - log (cosh (artanh z))`.
private theorem rademacher_legendreCgfRateFunction_eq_stationaryValue {z : ℝ}
    (hz : z ∈ Ioo (-1) 1) :
    legendreCgfRateFunction id rademacherMeasure z =
      ((z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) : ℝ) : EReal) :=
  by
  apply le_antisymm
  · -- Proof comment: rewrite each affine summand with the explicit cgf and bound it by the
    -- stationary value before taking the supremum.
    have hupper :
        legendreCgfRateFunction id rademacherMeasure z ≤
          ((z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) : ℝ) : EReal) := by
      rw [legendreCgfRateFunction]
      refine sSup_le ?_
      rintro _ ⟨t, rfl⟩
      have hreal :
          t * z - cgf id rademacherMeasure t ≤
            z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) := by
        rw [rademacherCgf_eq_logCosh]
        simpa [mul_comm] using rademacherObjective_le_stationaryValue (hz := hz) (t := t)
      have hcast :
          (((t * z - cgf id rademacherMeasure t : ℝ)) : EReal) ≤
            (((z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) : ℝ)) : EReal) := by
        exact_mod_cast hreal
      simpa using hcast
    simpa using hupper
  · -- Proof comment: evaluate the supremum family at the witness `t = Real.artanh z`.
    have hpoint :
        (((Real.artanh z) * z - cgf id rademacherMeasure (Real.artanh z) : ℝ) : EReal) ≤
          legendreCgfRateFunction id rademacherMeasure z := by
      rw [legendreCgfRateFunction]
      exact le_sSup ⟨Real.artanh z, rfl⟩
    have hwitness :
        ((z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) : ℝ) : EReal) ≤
          legendreCgfRateFunction id rademacherMeasure z := by
      calc
        ((z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) : ℝ) : EReal)
            = (((Real.artanh z) * z - cgf id rademacherMeasure (Real.artanh z) : ℝ) : EReal) := by
                rw [rademacherCgf_eq_logCosh]
                exact congrArg (fun y : ℝ ↦ (y : EReal)) (by ring)
        _ ≤ legendreCgfRateFunction id rademacherMeasure z := hpoint
    simpa using hwitness

-- Proof sketch: rewrite `Real.artanh z` using `Real.artanh_eq_half_log` on `[-1, 1]`, rewrite
-- `Real.cosh (Real.artanh z)` using `Real.cosh_artanh`, and simplify the resulting logarithms and
-- algebraic expression to the Bernoulli Cramér branch `bernoulliCramerRateFunction z`, whose
-- defining formula is the entropy expression from Remark 23.2.
private theorem rademacher_stationaryValue_eq_bernoulliCramerRateFunction {z : ℝ}
    (hz : z ∈ Ioo (-1) 1) :
    ((z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) : ℝ) : EReal) =
      bernoulliCramerRateFunction z :=
  by
  have hzIcc : z ∈ Icc (-1 : ℝ) 1 := ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hplus : 0 < 1 + z := by
    nlinarith [hz.1]
  have hminus : 0 < 1 - z := by
    nlinarith [hz.2]
  have hsq_nonneg : 0 ≤ 1 - z ^ 2 := by
    nlinarith
  have hartanh : Real.artanh z = (1 / 2 : ℝ) * Real.log ((1 + z) / (1 - z)) := by
    simpa using Real.artanh_eq_half_log hzIcc
  have hlogcosh : Real.log (Real.cosh (Real.artanh z)) = -(Real.log (1 - z ^ 2) / 2) := by
    -- Proof comment: the explicit `cosh (artanh z)` formula turns the logarithm into the
    -- half-logarithm of `1 - z^2`.
    rw [Real.cosh_artanh hz, one_div, Real.log_inv, Real.log_sqrt hsq_nonneg]
  rw [bernoulliCramerRateFunction]
  -- Proof comment: rewrite `artanh` and `cosh (artanh _)`, split the logarithms of the quotient
  -- and product, and collect coefficients into the Bernoulli entropy expression.
  exact congrArg (fun y : ℝ ↦ (y : EReal)) <| by
    calc
      z * Real.artanh z - Real.log (Real.cosh (Real.artanh z))
          = z * ((1 / 2 : ℝ) * Real.log ((1 + z) / (1 - z))) -
              (-(Real.log (1 - z ^ 2) / 2)) := by
                rw [hlogcosh, hartanh]
      _ = (z / 2) * Real.log ((1 + z) / (1 - z)) + Real.log (1 - z ^ 2) / 2 := by
            ring
      _ = (z / 2) * (Real.log (1 + z) - Real.log (1 - z)) +
            Real.log ((1 - z) * (1 + z)) / 2 := by
              rw [Real.log_div hplus.ne' hminus.ne',
                show 1 - z ^ 2 = (1 - z) * (1 + z) by ring]
      _ = (z / 2) * (Real.log (1 + z) - Real.log (1 - z)) +
            (Real.log (1 - z) + Real.log (1 + z)) / 2 := by
              rw [Real.log_mul hminus.ne' hplus.ne']
      _ = ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)) / 2 := by
            ring

/-- Example 23.5: for the symmetric `{-1, 1}`-valued law and `z ∈ (-1, 1)`, the Legendre transform
of the cumulant-generating function agrees with the chapter's Rademacher Cramér rate function. -/
theorem legendreCgfRateFunction_id_rademacherMeasure_eq_rademacherCramerRateFunction {z : ℝ}
    (hz : z ∈ Ioo (-1) 1) :
    legendreCgfRateFunction id
      (((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) +
        ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ))) z =
      rademacherCramerRateFunction z := by
  -- Proof comment: on `(-1, 1)`, replace the variational supremum by its stationary value and
  -- then normalize that value to the Bernoulli branch from Theorem 23.1.
  have hzabs : |z| < 1 := by
    simpa [mem_Ioo, abs_lt] using hz
  have hmain :
      legendreCgfRateFunction id rademacherMeasure z = rademacherCramerRateFunction z := by
    rw [rademacher_legendreCgfRateFunction_eq_stationaryValue hz]
    rw [rademacher_stationaryValue_eq_bernoulliCramerRateFunction hz]
    rw [rademacherCramerRateFunction_of_abs_le_one hzabs.le]
  simpa [rademacherMeasure] using hmain

end ProbabilityTheory
