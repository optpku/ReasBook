/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_41

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 7.42 lies in Chapter 7's absolute-accuracy / scalar iteration-bound domain.

Mandatory domain-style sampling before refinement:
- `quasi_newton_absolute_accuracy_iteration_bound` and
  `quasi_newton_absolute_accuracy_iteration_bound_eq_closed_form` in `Proposition_7_41`, the
  upstream owner and closed-form bridge for the finite-dimensional threshold `T_n(ε)`;
- `relativeScaleIterationBound`, `relativeScaleUniformIterationBound`, and
  `relativeScaleIterationBound_lt_uniformBound` in `Proposition_7_40`, the sibling owner pattern
  for a logarithmic finite-dimensional bound and its dimension-free comparison;
- `mixedAccuracyIterationCountBound`, `mixedAccuracyUniformIterationCountBound`, and
  `mixedAccuracyIterationCountBound_lt_uniformUpperBound` in `Proposition_7_38`, the same Chapter
  7 comparison pattern in the mixed-accuracy lane.

Best owner abstraction:
- source-facing: Proposition 7.42's strict comparison between the finite-dimensional absolute-
  accuracy threshold `T_n(ε)` and its dimension-free comparison bound;
- core/canonical: the upstream owner `quasi_newton_absolute_accuracy_iteration_bound`;
- bridge/view: the closed-form expansion
  `quasi_newton_absolute_accuracy_iteration_bound_eq_closed_form`.

Primitive data:
- the positive dimension `n : ℕ+`;
- the constants `L`, `R`, and `ε`.

Derived API:
- the new dimension-free comparison owner below;
- its expansion theorem;
- the strict comparison theorem obtained from `log (1 + x) < x`.

This refinement deletes the duplicate local finite-dimensional closed-form owner. The finite side
of Proposition 7.42 now reuses the Chapter 7 owner from `Proposition_7_41`, while this file owns
only the genuinely new dimension-free comparison quantity and the strict inequality relating the
two bounds.
-/

/-- The dimension-free comparison bound
`T_∞(ε) = (1 / 2) (1 + 2 L R / ε)^2` for the absolute-accuracy iteration threshold. -/
abbrev quasi_newton_absolute_accuracy_uniform_iteration_bound
    (L R ε : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 + 2 * L * R / ε) ^ 2

-- Proof sketch: unfold `quasi_newton_absolute_accuracy_uniform_iteration_bound`.
/-- Expanding `quasi_newton_absolute_accuracy_uniform_iteration_bound L R ε` recovers the formula
`(1 / 2) (1 + 2 L R / ε)^2`. -/
theorem quasi_newton_absolute_accuracy_uniform_iteration_bound_def
    (L R ε : ℝ) :
    quasi_newton_absolute_accuracy_uniform_iteration_bound L R ε =
      (1 / 2 : ℝ) * (1 + 2 * L * R / ε) ^ 2 := rfl

-- Proof sketch: split on `L * R = 0`. In the degenerate case the finite-dimensional threshold
-- collapses to `0`, while the dimension-free comparison bound is `1 / 2`. Otherwise use the
-- closed-form bridge from `Proposition_7_41`, write `T_n(ε) = n a log (1 + x)` with
-- `a = 1 + 2 L R / ε` and `x = (ε + 2 L R) / (2 n ε) = a / (2 n)`, apply
-- `log (1 + x) < x`, and simplify `n a x = (1 / 2) a²`.
/-- Proposition 7.42: if `ε > 0` and the logarithmic parameter `1 + 2 L R / ε` is positive,
equivalently `ε + 2 L R > 0`, then the finite-dimensional absolute-accuracy iteration threshold
`T_n(ε)` is strictly smaller than the dimension-free comparison bound
`T_∞(ε) = (1 / 2) (1 + 2 L R / ε)^2`. -/
theorem quasi_newton_absolute_accuracy_iteration_bound_lt_uniform_bound
    (n : ℕ+) (L R ε : ℝ)
    (hε : 0 < ε) (hsum : 0 < ε + 2 * L * R) :
    quasi_newton_absolute_accuracy_iteration_bound n ε L R <
      quasi_newton_absolute_accuracy_uniform_iteration_bound L R ε := by
  let a : ℝ := 1 + 2 * L * R / ε
  let x : ℝ := (ε + 2 * L * R) / (2 * (n : ℝ) * ε)
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have ha_eq : a = (ε + 2 * L * R) / ε := by
    dsimp [a]
    field_simp [hε.ne']
  have ha : 0 < a := by
    rw [ha_eq]
    exact div_pos hsum hε
  have hx : 0 < x := by
    dsimp [x]
    positivity
  by_cases hLR : L * R = 0
  · have hsum_eq : ε + 2 * L * R = ε := by
      nlinarith
    have hfinite_zero : quasi_newton_absolute_accuracy_iteration_bound n ε L R = 0 := by
      rw [quasi_newton_absolute_accuracy_iteration_bound_def]
      rw [quasi_newton_absolute_accuracy_delta_def]
      simp [hsum_eq, hLR, hε.ne']
    have huniform_half :
        quasi_newton_absolute_accuracy_uniform_iteration_bound L R ε = (1 / 2 : ℝ) := by
      rw [quasi_newton_absolute_accuracy_uniform_iteration_bound_def]
      have htwoLR : 2 * L * R = 0 := by
        nlinarith
      simp [htwoLR]
    rw [hfinite_zero, huniform_half]
    norm_num
  · have hLR_ne : L * R ≠ 0 := hLR
    have hlog : Real.log (1 + x) < x := by
      have hpos : 0 < 1 + x := by linarith
      have hne : 1 + x ≠ (1 : ℝ) := by linarith
      simpa [sub_eq_add_neg] using Real.log_lt_sub_one_of_pos hpos hne
    have hmul :
        (n : ℝ) * a * Real.log (1 + x) <
          (n : ℝ) * a * x := by
      exact mul_lt_mul_of_pos_left hlog (mul_pos hn ha)
    have hx_eq : x = a / (2 * (n : ℝ)) := by
      dsimp [x, a]
      field_simp [hε.ne', hn.ne']
    calc
      quasi_newton_absolute_accuracy_iteration_bound n ε L R
          = (n : ℝ) * a * Real.log (1 + x) := by
              simpa [a, x] using
                quasi_newton_absolute_accuracy_iteration_bound_eq_closed_form n hε hsum hLR_ne
      _ < (n : ℝ) * a * x := hmul
      _ = (n : ℝ) * a * (a / (2 * (n : ℝ))) := by rw [hx_eq]
      _ = (1 / 2 : ℝ) * a ^ 2 := by
            field_simp [hn.ne']
      _ = quasi_newton_absolute_accuracy_uniform_iteration_bound L R ε := by
            simp [quasi_newton_absolute_accuracy_uniform_iteration_bound, a]

end
