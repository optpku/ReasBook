/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open HasGeometricRateOfConvergence

universe u v

/-
Primary domain: scalar geometric-decay thresholds for the complete-data selected exact values.

Owner declarations sampled before refining:
* `HasGeometricRateOfConvergence` in `Chap01/Definition_1_2_6.lean`
* `HasGeometricRateOfConvergence.iterationThreshold` in `Chap01/Definition_1_2_6.lean`
* `HasGeometricRateOfConvergence.le_target_of_iterationThreshold_le` in
  `Chap01/Definition_1_2_6.lean`
* `HasGeometricRateOfConvergence.le_target_at_natCeil_iterationThreshold` in
  `Chap01/Definition_1_2_6.lean`

Best owner abstraction:
* `HasGeometricRateOfConvergence` on the scalar sequence
  `k ↦ exactValue (j k) X (t k)`

Primitive data:
* the selector sequence `j` and threshold sequence `t`
* the exact-value family
* the pointwise geometric upper bound from Lemma `3.3.7`

Derived API:
* the explicit logarithmic threshold consequence in Theorem `3.3.2`

Source/core/bridge triage:
* source-facing: Theorem `3.3.2`, stated with the textbook logarithmic formula and the direct
  contraction hypothesis `1 < 2 * (1 - ε)`
* core/canonical: `HasGeometricRateOfConvergence` and its threshold API
* bridge/view: the conversion from the displayed geometric bound to the owner predicate

The former file duplicated the owner threshold as a local abbreviation
`completeDataMasterIterationCountBound` and duplicated the owner threshold theorem in a second
public helper specialization. The refined file removes those parallel declarations and keeps only
the source-facing theorem specialized to the explicit textbook formula. The contraction input is
kept in the direct scalar form `1 < 2 * (1 - ε)` rather than the derived logarithmic reformulation
`0 < log (2 * (1 - ε))`.
-/

section

variable {χ : Type u} {ι : Type v}

/-- Theorem 3.3.2: in view of Lemma `3.3.7`, the master process reaches the global-stop threshold,
and hence the estimate `(3.3.9)`, after at most
`log ((t₀ - t^*) / ((1 - ε) ε)) / log (2 (1 - ε))` full iterations. -/
-- Proof sketch: reinterpret the geometric estimate from Lemma `3.3.7` as the canonical owner
-- statement `HasGeometricRateOfConvergence` for the selected exact-value sequence, then apply
-- `HasGeometricRateOfConvergence.le_target_at_natCeil_iterationThreshold` and simplify the owner
-- threshold to the displayed logarithmic formula. The canonical contraction input is the direct
-- scalar inequality `1 < 2 * (1 - ε)`, not the derived positivity of `log (2 * (1 - ε))`.
theorem selected_exactValue_le_epsilon_at_natCeil_masterIterationCountBound
    {ε tStar : ℝ} {X : χ} {t : ℕ → ℝ} {j : ℕ → ι}
    {exactValue : ι → χ → ℝ → ℝ}
    (hε : 0 < ε)
    (hε_contract : 1 < 2 * (1 - ε))
    (hgeom :
      ∀ k : ℕ,
        exactValue (j k) X (t k) ≤
          ((t 0 - tStar) / (1 - ε)) * ((1 / (2 * (1 - ε))) ^ k)) :
    exactValue
        (j ⌈Real.log ((t 0 - tStar) / ((1 - ε) * ε)) / Real.log (2 * (1 - ε))⌉₊)
        X
        (t ⌈Real.log ((t 0 - tStar) / ((1 - ε) * ε)) / Real.log (2 * (1 - ε))⌉₊) ≤
      ε := by
  let base : ℝ := 2 * (1 - ε)
  have hrate :
      HasGeometricRateOfConvergence
        (fun k ↦ exactValue (j k) X (t k))
        (1 - (2 * (1 - ε))⁻¹)
        ((t 0 - tStar) / (1 - ε)) := by
    intro k
    simpa [div_eq_mul_inv] using hgeom k
  have hbase_pos : 0 < base := by
    simpa [base] using (lt_trans zero_lt_one hε_contract)
  have hbase_ne : base ≠ 0 := ne_of_gt hbase_pos
  have howner_contract : 1 < (1 - (1 - base⁻¹))⁻¹ := by
    calc
      1 < base := by simpa [base] using hε_contract
      _ = (1 - (1 - base⁻¹))⁻¹ := by
        field_simp [hbase_ne]
        simp
  simpa [base, iterationThreshold, Real.logb, hbase_ne, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using
    HasGeometricRateOfConvergence.le_target_at_natCeil_iterationThreshold
      hrate howner_contract hε

end

end
