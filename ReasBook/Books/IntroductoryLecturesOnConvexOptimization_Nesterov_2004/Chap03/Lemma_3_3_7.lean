/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

/-
Primary domain: complete-data level-method scalar geometric decay.

Owner declarations sampled before refining:
* `HasGeometricRateOfConvergence`
* `HasGeometricRateOfConvergence.of_step_bound`
* `LevelMethodHistory` in `Lemma_3_3_1.lean`
* `constrainedMinimizationInternalGap_hasGeometricRateOfConvergence` in
  `Chap02/Proposition_2_30.lean`

Best owner abstraction:
* `HasGeometricRateOfConvergence` on the scalar sequence
  `k ↦ exactValue (j k) X (t k)`

Primitive data:
* the selector sequence `j` and threshold sequence `t`
* the exact and estimated value families
* the scalar comparison hypotheses and the initial gap bound

Derived API:
* the canonical owner statement `HasGeometricRateOfConvergence`
* the textbook geometric upper bound for the selected exact values

Source/core/bridge triage:
* source-facing: Lemma 3.3.7 in the `exactValue` / `estimatedValue` notation
* core/canonical: `HasGeometricRateOfConvergence`
* bridge/view: the pointwise unpacked geometric bound

Although the sampled values form the two scalar fields of a `LevelMethodHistory`, this lemma only
uses those primitive fields, so the public header stays source-facing instead of repackaging the
data through that owner. The proof core, however, is the owner-level statement
`HasGeometricRateOfConvergence`; the displayed bound is derived from that canonical abstraction.
-/

open HasGeometricRateOfConvergence

section

universe u v

variable {χ : Type u} {ι : Type v}

/-- Lemma 3.3.7 in canonical owner form: under the complete-data level-method hypotheses with
`ε < 1` and the three comparison inequalities between
`f_{j(k)}^*(X; t_k)` and `\hat f_{j(k)}^*(X; t_k)`, if the initial approximate value is bounded by
the initial gap, then the selected exact-value sequence has geometric rate with parameter
`1 - (2 * (1 - ε))⁻¹` and initial constant `(t 0 - tStar) / (1 - ε)`. The explicit threshold
recursion and step-size bounds from the source are redundant for this scalar consequence, and the
stronger contractivity side condition belongs only to later iteration-threshold consequences. -/
-- Proof sketch: the comparison assumptions imply the one-step contraction
-- `gap (k + 1) ≤ (1 / (2 * (1 - ε))) * gap k` for the selected exact-value sequence
-- `gap k = exactValue (j k) X (t k)`. Combine this with the zeroth-step bound
-- `estimatedValue (j 0) X (t 0) ≤ t 0 - tStar`, convert it to a bound on `gap 0`, and apply the
-- canonical constructor `HasGeometricRateOfConvergence.of_step_bound`.
theorem selectedExactValue_hasGeometricRateOfConvergence
    {ε tStar : ℝ} {X : χ} {t : ℕ → ℝ} {j : ℕ → ι}
    {exactValue estimatedValue : ι → χ → ℝ → ℝ}
    (hε : ε < 1)
    (hestimated_ge :
      ∀ k : ℕ,
        estimatedValue (j k) X (t k) ≥ (1 - ε) * exactValue (j k) X (t k))
    (hestimated_prev_ge_two_curr :
      ∀ k : ℕ,
        estimatedValue (j (k + 1)) X (t k) ≥
          2 * estimatedValue (j (k + 1)) X (t (k + 1)))
    (hexact_prev_ge_estimated_prev :
      ∀ k : ℕ,
        exactValue (j k) X (t k) ≥ estimatedValue (j (k + 1)) X (t k))
    (hestimated0_le_gap :
      estimatedValue (j 0) X (t 0) ≤ t 0 - tStar) :
    HasGeometricRateOfConvergence
      (fun k ↦ exactValue (j k) X (t k))
      (1 - (2 * (1 - ε))⁻¹)
      ((t 0 - tStar) / (1 - ε)) := by
  let gap : ℕ → ℝ := fun k ↦ exactValue (j k) X (t k)
  let β : ℝ := 1 / (2 * (1 - ε))
  have hone_sub_epsilon_pos : 0 < 1 - ε := sub_pos.mpr hε
  have hdouble_pos : 0 < (2 * (1 - ε) : ℝ) := by
    nlinarith
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    positivity
  have hstep :
      ∀ k : ℕ, gap (k + 1) ≤ β * gap k := by
    intro k
    dsimp [gap, β]
    have hscaled :
        (2 * (1 - ε)) * exactValue (j (k + 1)) X (t (k + 1)) ≤
          exactValue (j k) X (t k) := by
      calc
        (2 * (1 - ε)) * exactValue (j (k + 1)) X (t (k + 1))
            = 2 * ((1 - ε) * exactValue (j (k + 1)) X (t (k + 1))) := by ring
        _ ≤ 2 * estimatedValue (j (k + 1)) X (t (k + 1)) := by
          nlinarith [hestimated_ge (k + 1)]
        _ ≤ estimatedValue (j (k + 1)) X (t k) := by
          exact hestimated_prev_ge_two_curr k
        _ ≤ exactValue (j k) X (t k) := by
          exact hexact_prev_ge_estimated_prev k
    have hdiv :
        exactValue (j (k + 1)) X (t (k + 1)) ≤
          exactValue (j k) X (t k) / (2 * (1 - ε)) := by
      refine (le_div_iff₀ hdouble_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hgap0_le :
      gap 0 ≤ (t 0 - tStar) / (1 - ε) := by
    dsimp [gap]
    have hscaled :
        (1 - ε) * exactValue (j 0) X (t 0) ≤ t 0 - tStar := by
      calc
        (1 - ε) * exactValue (j 0) X (t 0) ≤ estimatedValue (j 0) X (t 0) := by
          exact hestimated_ge 0
        _ ≤ t 0 - tStar := hestimated0_le_gap
    refine (le_div_iff₀ hone_sub_epsilon_pos).2 ?_
    simpa [mul_comm] using hscaled
  have hgap_rate :
      HasGeometricRateOfConvergence gap (1 - β) ((t 0 - tStar) / (1 - ε)) := by
    have hq₁ : 1 - β ≤ 1 := by
      linarith
    refine of_step_bound hq₁ hgap0_le ?_
    intro k
    calc
      gap (k + 1) ≤ β * gap k := hstep k
      _ = (1 - (1 - β)) * gap k := by ring
  simpa [gap, β, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hgap_rate

/-- Lemma 3.3.7 in the displayed source-facing form: under the same hypotheses, the selected exact
values satisfy the textbook geometric upper bound. The stronger contractivity side condition is
only needed later when this estimate is converted to an iteration-threshold statement. -/
theorem selected_exactValue_le_initial_gap_div_one_sub_epsilon_mul_geometric_decay
    {ε tStar : ℝ} {X : χ} {t : ℕ → ℝ} {j : ℕ → ι}
    {exactValue estimatedValue : ι → χ → ℝ → ℝ}
    (hε : ε < 1)
    (hestimated_ge :
      ∀ k : ℕ,
        estimatedValue (j k) X (t k) ≥ (1 - ε) * exactValue (j k) X (t k))
    (hestimated_prev_ge_two_curr :
      ∀ k : ℕ,
        estimatedValue (j (k + 1)) X (t k) ≥
          2 * estimatedValue (j (k + 1)) X (t (k + 1)))
    (hexact_prev_ge_estimated_prev :
      ∀ k : ℕ,
        exactValue (j k) X (t k) ≥ estimatedValue (j (k + 1)) X (t k))
    (hestimated0_le_gap :
      estimatedValue (j 0) X (t 0) ≤ t 0 - tStar)
    (k : ℕ) :
    exactValue (j k) X (t k) ≤
      ((t 0 - tStar) / (1 - ε)) * ((1 / (2 * (1 - ε))) ^ k) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    selectedExactValue_hasGeometricRateOfConvergence
      hε
      hestimated_ge
      hestimated_prev_ge_two_curr
      hexact_prev_ge_estimated_prev
      hestimated0_le_gap
      k

end
