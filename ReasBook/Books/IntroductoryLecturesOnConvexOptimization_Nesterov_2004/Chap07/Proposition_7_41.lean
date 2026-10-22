/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Proposition 7.41 lies in Chapter 7's mixed-to-absolute accuracy / scalar iteration-bound
domain.

Relevant owner-style declarations sampled before refinement:
- `mixedAccuracyIterationCountBound` in `Proposition_7_38`, the chapter owner for a logarithmic
  mixed-accuracy iteration budget with an `abbrev` owner and `rfl` expansion theorem;
- `relativeScaleIterationBound` in `Proposition_7_40`, the sibling quasi-Newton logarithmic owner
  in the same scalar-iteration-bound lane;
- `HasMixedAccuracy` in `Definition_7_89`, the later chapter owner for the scalar mixed
  absolute-relative accuracy inequality;
- `IsAbsoluteAccuracyApproximateSolutionOn` in `Definition_7_93`, the later chapter owner for the
  absolute-accuracy optimization conclusion.

Best owner abstraction:
- source-facing: the Proposition 7.41 quantity `δ(ε)`, the iteration threshold `T_n(ε)`, and the
  final absolute-accuracy theorem with its displayed gap estimate;
- core/canonical: the chapter's transparent scalar-owner pattern for such quantities, namely
  `abbrev` owners with direct definitional bridge theorems rather than opaque wrapper `def`s;
- bridge/view: the expansion theorems and the closed-form rewriting of `T_n(ε)`.

Primitive data:
- the positive dimension `n : ℕ+`;
- the iteration index `k`;
- the scalars `L`, `R`, and `ε`;
- the assumed gap estimate and the threshold lower bound on `k`.

Derived API:
- the specialization `δ(ε) = ε / (ε + 2 L R)`;
- the threshold `T_n(ε)` and its closed logarithmic form;
- the absolute-accuracy conclusion `φ x_k^* ≤ φ* + ε`.

There is no earlier project owner with exactly the Proposition 7.41 formulas, so the refinement
keeps these declarations source-facing. The cleanup is instead to align them with the chapter's
canonical scalar-owner style: transparent abbreviations for the reusable source quantities,
`rfl` bridge lemmas for those owners, and the displayed mixed-to-absolute gap estimate kept inline
in the proposition rather than exported as a one-off wrapper.
-/

/-- The parameter `δ(ε) = ε / (ε + 2 L R)` used to convert the mixed-accuracy estimate into an
absolute-accuracy estimate. -/
abbrev quasi_newton_absolute_accuracy_delta
    (ε L R : ℝ) : ℝ :=
  ε / (ε + 2 * L * R)

-- Proof sketch: unfold `quasi_newton_absolute_accuracy_delta`; the right-hand side is exactly the
-- defining formula for `δ(ε)`.
/-- Expanding `quasi_newton_absolute_accuracy_delta ε L R` recovers the formula
`ε / (ε + 2 L R)`. -/
theorem quasi_newton_absolute_accuracy_delta_def
    (ε L R : ℝ) :
    quasi_newton_absolute_accuracy_delta ε L R =
      ε / (ε + 2 * L * R) := rfl

/-- The iteration threshold
`T_n(ε) = (n / δ(ε)) * log (1 + LR / (n ε (1 - δ(ε))))` from Proposition 7.41. -/
abbrev quasi_newton_absolute_accuracy_iteration_bound
    (n : ℕ+) (ε L R : ℝ) : ℝ :=
  let δ := quasi_newton_absolute_accuracy_delta ε L R
  ((n : ℝ) / δ) * Real.log (1 + (L * R) / ((n : ℝ) * ε * (1 - δ)))

-- Proof sketch: unfold `quasi_newton_absolute_accuracy_iteration_bound`; the result is exactly the
-- definition of `T_n(ε)` written in terms of `δ(ε)`.
/-- Expanding `quasi_newton_absolute_accuracy_iteration_bound n ε L R` recovers the formula
`(n / δ(ε)) * log (1 + LR / (n ε (1 - δ(ε))))`. -/
theorem quasi_newton_absolute_accuracy_iteration_bound_def
    (n : ℕ+) (ε L R : ℝ) :
    quasi_newton_absolute_accuracy_iteration_bound n ε L R =
      let δ := quasi_newton_absolute_accuracy_delta ε L R
      ((n : ℝ) / δ) * Real.log (1 + (L * R) / ((n : ℝ) * ε * (1 - δ))) := rfl

-- Proof sketch: substitute `δ(ε) = ε / (ε + 2 L R)`, simplify
-- `1 - δ(ε) = 2 L R / (ε + 2 L R)` and
-- `(n / δ(ε)) = n * (1 + 2 L R / ε)`, then rewrite the logarithm argument accordingly. The
-- cancellation in the logarithm denominator only needs `L * R ≠ 0`, while the positivity input
-- is exactly `ε > 0` and `ε + 2 L R > 0`.
/-- Rewriting `T_n(ε)` using the explicit formula for `δ(ε)` gives the closed form
`n (1 + 2LR / ε) log (1 + (ε + 2LR) / (2 n ε))` whenever `ε > 0`,
`ε + 2LR > 0`, and `LR ≠ 0`. -/
theorem quasi_newton_absolute_accuracy_iteration_bound_eq_closed_form
    (n : ℕ+) {ε L R : ℝ} (hε : 0 < ε) (hsum : 0 < ε + 2 * L * R) (hLR : L * R ≠ 0) :
    quasi_newton_absolute_accuracy_iteration_bound n ε L R =
      (n : ℝ) * (1 + (2 * L * R) / ε) *
        Real.log (1 + (ε + 2 * L * R) / (2 * (n : ℝ) * ε)) := by
  have hε_ne : ε ≠ 0 := hε.ne'
  have hsum_ne : ε + 2 * L * R ≠ 0 := hsum.ne'
  have htwoLR_ne : 2 * L * R ≠ 0 := by
    rw [show 2 * L * R = (2 : ℝ) * (L * R) by ring]
    exact mul_ne_zero (by norm_num) hLR
  rw [quasi_newton_absolute_accuracy_iteration_bound_def]
  simp [quasi_newton_absolute_accuracy_delta]
  field_simp [hε_ne, hsum_ne]
  congr 1
  field_simp [hε_ne, htwoLR_ne]
  ring

-- Proof sketch: set `δ := δ(ε) = ε / (ε + 2 L R)`. The identity
-- `L R * δ / (1 - δ) = ε / 2` gives half of the target accuracy budget. The lower bound
-- `k ≥ T_n(ε)` implies
-- `exp (δ (k + 1) / n) - 1 ≥ LR / (n ε (1 - δ))`, so the remaining exponential term is at most
-- `ε / 2`. Adding the two contributions yields `φ xkStar - φStar ≤ ε`, hence
-- `φ xkStar ≤ φStar + ε`.
/-- Proposition 7.41: if the `k`-th iterate satisfies the mixed-accuracy gap estimate with
`δ = ε / (ε + 2LR)` and `k` is at least the threshold `T_n(ε)`, then its objective value is
within absolute accuracy `ε` of `φ*`. -/
theorem quasi_newton_absolute_accuracy_of_iteration_bound
    {X : Type u} (φ : X → ℝ) (xkStar : X) (φStar : ℝ)
    (n : ℕ+) (k : ℕ) (L R ε : ℝ)
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hgap :
      φ xkStar - φStar ≤
        let δ := quasi_newton_absolute_accuracy_delta ε L R
        L * R *
          (δ / (1 - δ) +
            1 /
              (2 * (n : ℝ) *
                (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1) *
                (1 - δ))))
    (hk :
      quasi_newton_absolute_accuracy_iteration_bound n ε L R ≤ (k : ℝ)) :
    φ xkStar ≤ φStar + ε := by
  let δ := quasi_newton_absolute_accuracy_delta ε L R
  let a : ℝ := (L * R) / ((n : ℝ) * ε * (1 - δ))
  let e : ℝ := Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1
  have hgap' :
      φ xkStar - φStar ≤
        L * R * (δ / (1 - δ) + 1 / (2 * (n : ℝ) * e * (1 - δ))) := by
    simpa [δ, e] using hgap
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have hδ_pos : 0 < δ := by
    dsimp [δ, quasi_newton_absolute_accuracy_delta]
    positivity
  have h_one_sub_δ_pos : 0 < 1 - δ := by
    dsimp [δ, quasi_newton_absolute_accuracy_delta]
    have hden_ne : ε + 2 * L * R ≠ 0 := by positivity
    field_simp [hden_ne]
    nlinarith [hL, hR, hε]
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hfirst_eq : L * R * (δ / (1 - δ)) = ε / 2 := by
    dsimp [δ, quasi_newton_absolute_accuracy_delta]
    field_simp [hε.ne', hL.ne', hR.ne']
    ring
  have hk_div : Real.log (1 + a) ≤ (k : ℝ) / ((n : ℝ) / δ) := by
    apply (le_div_iff₀ (div_pos hn hδ_pos)).2
    simpa [quasi_newton_absolute_accuracy_iteration_bound, δ, a, mul_comm, mul_left_comm,
      mul_assoc] using hk
  have hk_log : Real.log (1 + a) ≤ δ * (k : ℝ) / (n : ℝ) := by
    have hk_div' : Real.log (1 + a) ≤ (k : ℝ) * (δ / (n : ℝ)) := by
      simpa [div_eq_mul_inv, hδ_pos.ne', hn.ne', mul_assoc, mul_comm, mul_left_comm] using hk_div
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hk_div'
  have hk_log_succ : Real.log (1 + a) ≤ δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by
    refine hk_log.trans ?_
    have hk_le : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ k
    gcongr
  have h_exp_le : 1 + a ≤ e + 1 := by
    have hlogexp : 1 + a = Real.exp (Real.log (1 + a)) := by
      rw [Real.exp_log (by linarith [ha_pos])]
    rw [hlogexp]
    simpa [e] using Real.exp_le_exp.mpr hk_log_succ
  have ha_le_e : a ≤ e := by
    linarith
  have he_pos : 0 < e := lt_of_lt_of_le ha_pos ha_le_e
  have hden_lower : (2 * L * R) / ε ≤ 2 * (n : ℝ) * e * (1 - δ) := by
    have hmul := mul_le_mul_of_nonneg_right ha_le_e (by positivity : 0 ≤ 2 * (n : ℝ) * (1 - δ))
    dsimp [a] at hmul
    simpa [div_eq_mul_inv, hε.ne', hn.ne', h_one_sub_δ_pos.ne', mul_assoc, mul_left_comm,
      mul_comm] using hmul
  have hsecond_le :
      L * R * (1 / (2 * (n : ℝ) * e * (1 - δ))) ≤ ε / 2 := by
    have hden_pos : 0 < 2 * (n : ℝ) * e * (1 - δ) := by
      positivity
    rw [mul_one_div]
    apply (div_le_iff₀ hden_pos).2
    have hmul2 := mul_le_mul_of_nonneg_left hden_lower (by positivity : 0 ≤ ε / 2)
    simpa [div_eq_mul_inv, hε.ne', mul_assoc, mul_left_comm, mul_comm] using hmul2
  have hsum_le :
      L * R * (δ / (1 - δ)) + L * R * (1 / (2 * (n : ℝ) * e * (1 - δ))) + φStar ≤
        ε / 2 + ε / 2 + φStar := by
    nlinarith [hfirst_eq, hsecond_le]
  calc
    φ xkStar = (φ xkStar - φStar) + φStar := by ring
    _ ≤ (L * R * (δ / (1 - δ) + 1 / (2 * (n : ℝ) * e * (1 - δ)))) + φStar := by
      linarith
    _ = L * R * (δ / (1 - δ)) + L * R * (1 / (2 * (n : ℝ) * e * (1 - δ))) + φStar := by
      ring
    _ ≤ ε / 2 + ε / 2 + φStar := hsum_le
    _ = φStar + ε := by ring
