/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_14

noncomputable section

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 7.13 lies in the chapter's finite max-absolute-linear / symmetric log-sum-exp
smoothing domain.

Sampled owner-style declarations:
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`;
- `absLinearLogSumExp` and `absLinearLogSumExp_apply` in `Chap07/Proposition_7_14`;
- the same finite-max owner specialized to the absolute inner-product family.

Best owner abstraction:
- source-facing: Proposition 7.13's smoothing inequality for `x ↦ max_i |⟪a_i, x⟫|`;
- core/canonical: `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)` and `absLinearLogSumExp μ a`;
- bridge/view: the source-facing bound below.

Primitive data:
- the finite family `a : ι → E`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the canonical unsmoothed owner `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`;
- the canonical smoothing owner `absLinearLogSumExp μ a`;
- the additive error term `μ log (2 * Fintype.card ι)`.

This refinement deletes the duplicate local wrappers `absoluteInnerMaxObjective` and
`maxAbsoluteInnerLogSumExpSmoothing`, and reuses the project owner `maxTypeObjective` directly
instead of a second Chapter 7 max-objective owner. -/

/- Proposition 7.13 works in the same finite-family symmetric log-sum-exp setting as
`absLinearLogSumExp`; the helper lemmas below isolate the pairwise and summed exponential
comparisons used in the textbook proof. -/
/-- Helper for Proposition 7.13: each symmetric pair-weight dominates the exponential of the
absolute pairing. -/
theorem absLinearLogSumExpPairWeight_ge_exp_abs_inner
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (i : ι) (x : E) :
    Real.exp (|inner ℝ (a i) x| / (μ : ℝ)) ≤ absLinearLogSumExpPairWeight μ a i x := by
  by_cases hinner : 0 ≤ inner ℝ (a i) x
  · -- In the nonnegative branch, the `+ exp (-z)` term makes the symmetric weight at least `exp z`.
    rw [absLinearLogSumExpPairWeight_eq]
    have hpos : 0 < Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) := Real.exp_pos _
    rw [abs_of_nonneg hinner]
    exact le_add_of_nonneg_right (le_of_lt hpos)
  · -- In the nonpositive branch, the `+ exp z` term makes the symmetric weight at least `exp (-z)`.
    have habs :
        |inner ℝ (a i) x| / (μ : ℝ) = -(inner ℝ (a i) x / (μ : ℝ)) := by
      rw [abs_of_nonpos (le_of_not_ge hinner)]
      ring
    rw [absLinearLogSumExpPairWeight_eq, habs]
    have hpos : 0 < Real.exp (inner ℝ (a i) x / (μ : ℝ)) := Real.exp_pos _
    calc
      Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) ≤
          Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) +
            Real.exp (inner ℝ (a i) x / (μ : ℝ)) :=
        le_add_of_nonneg_right (le_of_lt hpos)
      _ = Real.exp (inner ℝ (a i) x / (μ : ℝ)) +
            Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) := by ring

/-- Helper for Proposition 7.13: each symmetric pair-weight is at most twice the exponential of
the absolute pairing. -/
theorem absLinearLogSumExpPairWeight_le_two_mul_exp_abs_inner
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (i : ι) (x : E) :
    absLinearLogSumExpPairWeight μ a i x ≤ 2 * Real.exp (|inner ℝ (a i) x| / (μ : ℝ)) := by
  by_cases hinner : 0 ≤ inner ℝ (a i) x
  · -- In the nonnegative branch, `exp (-z) ≤ exp z`, so the symmetric weight is at most `2 exp z`.
    rw [absLinearLogSumExpPairWeight_eq, abs_of_nonneg hinner]
    have hz_nonneg : 0 ≤ inner ℝ (a i) x / (μ : ℝ) := by
      exact div_nonneg hinner (le_of_lt μ.2)
    have hle :
        Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) ≤ Real.exp (inner ℝ (a i) x / (μ : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hsum :
        Real.exp (inner ℝ (a i) x / (μ : ℝ)) + Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) ≤
          Real.exp (inner ℝ (a i) x / (μ : ℝ)) + Real.exp (inner ℝ (a i) x / (μ : ℝ)) :=
      add_le_add le_rfl hle
    simpa [two_mul] using hsum
  · -- In the nonpositive branch, `exp z ≤ exp (-z)`, so the symmetric weight is at most `2 exp (-z)`.
    have habs :
        |inner ℝ (a i) x| / (μ : ℝ) = -(inner ℝ (a i) x / (μ : ℝ)) := by
      rw [abs_of_nonpos (le_of_not_ge hinner)]
      ring
    rw [absLinearLogSumExpPairWeight_eq, habs]
    have hz_nonpos : inner ℝ (a i) x / (μ : ℝ) ≤ 0 := by
      have hscaled :
          inner ℝ (a i) x * (μ : ℝ)⁻¹ ≤ 0 * (μ : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_right (le_of_not_ge hinner) (inv_nonneg.mpr (le_of_lt μ.2))
      simpa [div_eq_mul_inv] using hscaled
    have hle :
        Real.exp (inner ℝ (a i) x / (μ : ℝ)) ≤ Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hsum :
        Real.exp (inner ℝ (a i) x / (μ : ℝ)) + Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) ≤
          Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) +
            Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) :=
      add_le_add hle le_rfl
    calc
      Real.exp (inner ℝ (a i) x / (μ : ℝ)) + Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) ≤
          Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) +
            Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) :=
        hsum
      _ = 2 * Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) := by ring

/-- Helper for Proposition 7.13: the normalizing sum dominates the exponential of the max absolute
pairing. -/
theorem absLinearLogSumExpOmega_ge_exp_maxTypeObjective_absInner
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    Real.exp (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x / (μ : ℝ)) ≤
      absLinearLogSumExpOmega μ a x := by
  -- Choose an index where the finite maximum of `|⟪aᵢ, x⟫|` is attained.
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) x|)
  have hnonneg : ∀ j : ι, 0 ≤ absLinearLogSumExpPairWeight μ a j x := by
    intro j
    rw [absLinearLogSumExpPairWeight_eq]
    positivity
  rw [absLinearLogSumExpOmega_eq, maxTypeObjective_apply]
  calc
    Real.exp
        (Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) x|) / (μ : ℝ)) =
        Real.exp (|inner ℝ (a i) x| / (μ : ℝ)) := by rw [← hi]
    _ ≤ absLinearLogSumExpPairWeight μ a i x :=
      absLinearLogSumExpPairWeight_ge_exp_abs_inner a μ i x
    _ ≤ ∑ j, absLinearLogSumExpPairWeight μ a j x := by
      exact Finset.single_le_sum (fun j _ ↦ hnonneg j) (Finset.mem_univ i)

/-- Helper for Proposition 7.13: the normalizing sum is at most the cardinality factor times the
exponential of the max absolute pairing. -/
theorem absLinearLogSumExpOmega_le_two_card_mul_exp_maxTypeObjective_absInner
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    absLinearLogSumExpOmega μ a x ≤
      (2 * Fintype.card ι : ℝ) *
        Real.exp (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x / (μ : ℝ)) := by
  let M : ℝ := maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x
  rw [absLinearLogSumExpOmega_eq]
  calc
    ∑ i, absLinearLogSumExpPairWeight μ a i x ≤
        ∑ i, 2 * Real.exp (|inner ℝ (a i) x| / (μ : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact absLinearLogSumExpPairWeight_le_two_mul_exp_abs_inner a μ i x
    _ ≤ ∑ i, 2 * Real.exp (M / (μ : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi_le : |inner ℝ (a i) x| ≤ M := by
        dsimp [M]
        rw [maxTypeObjective_apply]
        exact Finset.le_sup' (fun j : ι ↦ |inner ℝ (a j) x|) (by simp)
      have hexp_le :
          Real.exp (|inner ℝ (a i) x| / (μ : ℝ)) ≤ Real.exp (M / (μ : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hscaled :
            |inner ℝ (a i) x| * (μ : ℝ)⁻¹ ≤ M * (μ : ℝ)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hi_le (inv_nonneg.mpr (le_of_lt μ.2))
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
      exact mul_le_mul_of_nonneg_left hexp_le (by norm_num)
    _ = (Fintype.card ι : ℝ) * (2 * Real.exp (M / (μ : ℝ))) := by simp
    _ = (2 * Fintype.card ι : ℝ) * Real.exp (M / (μ : ℝ)) := by ring

/-- Proposition 7.13: for a finite family `aᵢ` in a real inner product space and a positive
smoothing parameter `μ`, the symmetric smoothing of `x ↦ max_i |⟪a_i, x⟫|` lies between that max
and the same max plus `μ log (2 * Fintype.card ι)` at every point `x`. -/
-- Proof sketch: use `maxTypeObjective_apply`, specialized to the absolute inner-product family,
-- to identify the unsmoothed objective with
-- the finite maximum of the absolute pairings, and `absLinearLogSumExp_apply` together with
-- `absLinearLogSumExpOmega_eq` to expand the smoothing. For each `i`, compare
-- `exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)` with `exp (|⟪aᵢ, x⟫| / μ)` from below and with
-- `2 * exp (|⟪aᵢ, x⟫| / μ)` from above, sum over `i`, and apply `μ * log`.
theorem maxTypeObjective_absInner_smoothing_bounds
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x ≤ absLinearLogSumExp μ a x ∧
      absLinearLogSumExp μ a x ≤
        maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x +
          (μ : ℝ) * Real.log (2 * Fintype.card ι) := by
  let M : ℝ := maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x
  let ω : ℝ := absLinearLogSumExpOmega μ a x
  have hμ_pos : 0 < (μ : ℝ) := μ.2
  have hω_pos : 0 < ω := by
    -- The logarithm is evaluated on the strictly positive normalizing sum.
    simpa [ω] using absLinearLogSumExpOmega_pos (μ := μ) (a := a) x
  have homega_lower : Real.exp (M / (μ : ℝ)) ≤ ω := by
    -- The lower sandwich comes from the index attaining the max absolute pairing.
    simpa [M, ω] using absLinearLogSumExpOmega_ge_exp_maxTypeObjective_absInner a μ x
  have homega_upper :
      ω ≤ (2 * Fintype.card ι : ℝ) * Real.exp (M / (μ : ℝ)) := by
    -- The upper sandwich comes from summing the pointwise `2 exp` bounds.
    simpa [M, ω] using absLinearLogSumExpOmega_le_two_card_mul_exp_maxTypeObjective_absInner a μ x
  have hmul_div_cancel : (μ : ℝ) * (M / (μ : ℝ)) = M := by
    field_simp [hμ_pos.ne']
  have hlower_log : M / (μ : ℝ) ≤ Real.log ω := by
    -- Taking logs preserves the lower omega bound because both sides are positive.
    have hlog :
        Real.log (Real.exp (M / (μ : ℝ))) ≤ Real.log ω := by
      exact Real.log_le_log (Real.exp_pos _) homega_lower
    simpa [ω] using hlog
  have hcard_pos : 0 < (2 * Fintype.card ι : ℝ) := by
    have hcard_pos_nat : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
    positivity
  have hupper_log :
      Real.log ω ≤ Real.log ((2 * Fintype.card ι : ℝ) * Real.exp (M / (μ : ℝ))) := by
    -- The same monotonicity gives the upper logarithmic bound.
    exact Real.log_le_log hω_pos homega_upper
  have hlog_mul :
      Real.log ((2 * Fintype.card ι : ℝ) * Real.exp (M / (μ : ℝ))) =
        Real.log (2 * Fintype.card ι) + M / (μ : ℝ) := by
    rw [Real.log_mul hcard_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  constructor
  · -- Multiply the lower logarithmic bound by `μ` to recover the unsmoothed objective.
    rw [absLinearLogSumExp_apply]
    calc
      M = (μ : ℝ) * (M / (μ : ℝ)) := by symm; exact hmul_div_cancel
      _ ≤ (μ : ℝ) * Real.log ω :=
        mul_le_mul_of_nonneg_left hlower_log (le_of_lt hμ_pos)
      _ = absLinearLogSumExp μ a x := by simp [ω, absLinearLogSumExp_apply]
  · -- Multiply the upper logarithmic bound by `μ` and split the resulting logarithm.
    rw [absLinearLogSumExp_apply]
    calc
      (μ : ℝ) * Real.log ω ≤
          (μ : ℝ) * Real.log ((2 * Fintype.card ι : ℝ) * Real.exp (M / (μ : ℝ))) :=
        mul_le_mul_of_nonneg_left hupper_log (le_of_lt hμ_pos)
      _ = (μ : ℝ) * (Real.log (2 * Fintype.card ι) + M / (μ : ℝ)) := by
        rw [hlog_mul]
      _ = (μ : ℝ) * Real.log (2 * Fintype.card ι) + M := by
        rw [mul_add, hmul_div_cancel]
      _ = M + (μ : ℝ) * Real.log (2 * Fintype.card ι) := by ring
