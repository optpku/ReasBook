/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {σ2 L τ : ℝ} {f : E → ℝ} {xStar : E}

/- Lemma 4.2.6 lies in the first-order nondegeneracy / strong-convexity-smoothness domain on
real Hilbert spaces.

Sampled owner declarations:
* `IsStrongConvexSmoothObjective` in `Chap02/Definition_2_17`, the chapter owner for positive
  strong convexity together with the `C¹` and Lipschitz-gradient data making `∇ f` genuinely
  first-order;
* `IsStrongConvexSmoothObjective.contDiff`, the canonical source of pointwise
  `HasGradientAt f (∇ f x) x`;
* `IsStrongConvexSmoothObjective.mu_le_L`, the owner comparison theorem showing that on
  nontrivial spaces the smoothness parameter dominates the strong-convexity parameter;
* `firstOrderNondegeneracyCoefficient` in `Definition_4_2_15`, the Chapter 4 owner of the
  normalized gradient/displacement coefficient;
* `IsFirstOrderNondegenerate` in `Definition_4_2_15`, the source-facing owner obtained by
  forgetting the explicit threshold formulas and retaining only the positive lower bound.

Best owner abstraction:
* source-facing: the explicit existence of a scalar `τ` with the displayed threshold and strict
  improvement properties;
* core/canonical: `IsStrongConvexSmoothObjective σ₂ L f`;
* bridge/view: the coefficient `firstOrderNondegeneracyCoefficient f xStar x` and the owner class
  `IsFirstOrderNondegenerate f xStar`.

Primitive data:
* `σ2`, `L`, the objective `f`, and the chosen minimizer `xStar`;
* the source-facing class membership hypothesis `f ∈ 𝓢[σ₂, L]¹¹`;
* the global minimizer witness `IsMinOn f Set.univ xStar`.

Derived API:
* the existence of a positive lower bound `τ`;
* the explicit threshold `2 * sqrt q[σ₂, L] / (1 + q[σ₂, L]) ≤ τ`;
* under the primitive scalar assumptions `0 < σ₂` and `σ₂ < L`, the strict improvement
  `sqrt q[σ₂, L] < τ`;
* the pointwise coefficient bound through `firstOrderNondegeneracyCoefficient`;
* the first-order owner bridge `HasGradientAt f (∇ f x) x` obtained from the smooth owner.

This refinement keeps the lemma source-facing while moving its assumptions to the chapter owner
that already packages the intended first-order meaning of `∇ f`. The coefficient and
nondegeneracy owner remain the downstream bridge/view layer. -/

-- Proof sketch: use the interpolation inequality for a `σ₂`-strongly convex function with
-- `L`-Lipschitz gradient to show that, for every `x ≠ xStar`,
-- `⟪∇ f x, x - xStar⟫` is bounded below by
-- `(2 * sqrt (σ₂ * L) / (σ₂ + L)) * ‖∇ f x‖ * ‖x - xStar‖`. Dividing by the product of the
-- norms gives a uniform lower bound for the coefficient, and the same scalar expression rewrites
-- as `2 * sqrt q[σ₂, L] / (1 + q[σ₂, L])`.
/-- Helper for Lemma 4.2.6: when `σ₂ ≥ 0` and `L > 0`, the chapter threshold
`2 * sqrt q[σ₂, L] / (1 + q[σ₂, L])` rewrites to the secant constant
`2 * sqrt (σ₂ * L) / (σ₂ + L)`. -/
theorem firstOrderNondegeneracyThreshold_eq_secant_constant
    (hσ2 : 0 ≤ σ2)
    (hL : 0 < L) :
    2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]) =
      2 * Real.sqrt (σ2 * L) / (σ2 + L) := by
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hsqrtL_ne : Real.sqrt L ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hL)
  -- Rewrite the chapter ratio through `q[σ₂, L] = σ₂ / L`.
  calc
    2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L])
        = 2 * Real.sqrt (σ2 / L) / ((σ2 + L) / L) := by
            rw [show (1 : ℝ) + σ2 / L = (σ2 + L) / L by
              field_simp [hL_ne]
              ring]
    _ = 2 * (Real.sqrt σ2 / Real.sqrt L) / ((σ2 + L) / L) := by
          rw [Real.sqrt_div hσ2 L]
    _ = 2 * ((Real.sqrt σ2 / Real.sqrt L) * L) / (σ2 + L) := by
          field_simp [hL_ne]
    _ = 2 * (Real.sqrt σ2 * Real.sqrt L) / (σ2 + L) := by
          congr 1
          field_simp [hsqrtL_ne]
          rw [Real.sq_sqrt hL.le]
    _ = 2 * Real.sqrt (σ2 * L) / (σ2 + L) := by
          rw [← Real.sqrt_mul hσ2 L]

/-- Helper for Lemma 4.2.6: away from the minimizer, the strengthened secant inequality for a
strongly convex smooth objective gives the desired lower bound on the first-order coefficient. -/
theorem firstOrderNondegeneracyThreshold_le_coefficient_of_mem_S11
    [Nontrivial E]
    (hf : f ∈ 𝓢[σ2, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    {x : E} (hx : x ≠ xStar) :
    2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]) ≤
      firstOrderNondegeneracyCoefficient f xStar x := by
  have hf' : IsStrongConvexSmoothObjective σ2 L f := mem_S11_iff.mp hf
  have hσ2_pos : 0 < σ2 := hf'.mu_pos
  have hσ2_nonneg : 0 ≤ σ2 := hσ2_pos.le
  have hσ2_le_L : σ2 ≤ L := hf'.mu_le_L
  have hL_pos : 0 < L := lt_of_lt_of_le hσ2_pos hσ2_le_L
  have hden_pos : 0 < σ2 + L := by
    nlinarith
  have hdist_pos : 0 < ‖x - xStar‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hgradStar : ∇ f xStar = 0 := hf'.gradient_eq_zero_of_isMinOn hxStar
  -- Strong monotonicity at `(x, xStar)` forces the gradient norm to stay positive away from the
  -- minimizer, so the coefficient denominator can be divided out safely.
  have hmono :
      σ2 * ‖x - xStar‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x) (x - xStar) := by
    simpa [hgradStar, sub_zero] using hf'.gradient_strong_mono x xStar
  have hgrad_pos : 0 < ‖∇ f x‖ := by
    have hcs :
        inner ℝ (∇ f x) (x - xStar) ≤ ‖∇ f x‖ * ‖x - xStar‖ := by
      exact real_inner_le_norm _ _
    have hbound :
        σ2 * ‖x - xStar‖ ^ (2 : ℕ) ≤ ‖∇ f x‖ * ‖x - xStar‖ :=
      le_trans hmono hcs
    have hdist_sq_pos : 0 < ‖x - xStar‖ ^ (2 : ℕ) := by
      positivity
    have hnorm_ne : ‖∇ f x‖ ≠ 0 := by
      intro hzero
      have hleft_pos : 0 < σ2 * ‖x - xStar‖ ^ (2 : ℕ) := by
        positivity
      have : σ2 * ‖x - xStar‖ ^ (2 : ℕ) ≤ 0 := by
        calc
          σ2 * ‖x - xStar‖ ^ (2 : ℕ) ≤ ‖∇ f x‖ * ‖x - xStar‖ := hbound
          _ = 0 := by simp [hzero]
      linarith
    have hnorm_nonneg : 0 ≤ ‖∇ f x‖ := norm_nonneg _
    exact lt_of_le_of_ne hnorm_nonneg (by simpa [eq_comm] using hnorm_ne)
  have hprod_pos : 0 < ‖∇ f x‖ * ‖x - xStar‖ := by
    exact mul_pos hgrad_pos hdist_pos
  have hpair :
      (σ2 * L / (σ2 + L)) * ‖x - xStar‖ ^ (2 : ℕ) +
          (1 / (σ2 + L)) * ‖∇ f x‖ ^ (2 : ℕ) ≤
        inner ℝ (∇ f x) (x - xStar) := by
    simpa [hgradStar, sub_zero] using hf'.pairing_lower_bound x xStar
  have hpair' :
      ((σ2 * L) * ‖x - xStar‖ ^ (2 : ℕ) + ‖∇ f x‖ ^ (2 : ℕ)) / (σ2 + L) ≤
        inner ℝ (∇ f x) (x - xStar) := by
    convert hpair using 1 <;> ring
  -- Apply scalar AM-GM to the two secant terms before normalizing by the positive denominator.
  have hAMGM :
      2 * Real.sqrt (σ2 * L) * ‖x - xStar‖ * ‖∇ f x‖ ≤
        (σ2 * L) * ‖x - xStar‖ ^ (2 : ℕ) + ‖∇ f x‖ ^ (2 : ℕ) := by
    have hsquare :
        0 ≤ (Real.sqrt (σ2 * L) * ‖x - xStar‖ - ‖∇ f x‖) ^ (2 : ℕ) := by
      positivity
    have hsqrt_sq :
        Real.sqrt (σ2 * L) * Real.sqrt (σ2 * L) = σ2 * L := by
      calc
        Real.sqrt (σ2 * L) * Real.sqrt (σ2 * L) = (Real.sqrt (σ2 * L)) ^ (2 : ℕ) := by
          ring
        _ = σ2 * L := by
          rw [Real.sq_sqrt]
          positivity
    nlinarith [hsqrt_sq]
  have hcore :
      2 * Real.sqrt (σ2 * L) / (σ2 + L) * (‖∇ f x‖ * ‖x - xStar‖) ≤
        inner ℝ (∇ f x) (x - xStar) := by
    calc
      2 * Real.sqrt (σ2 * L) / (σ2 + L) * (‖∇ f x‖ * ‖x - xStar‖)
          = (2 * Real.sqrt (σ2 * L) * ‖x - xStar‖ * ‖∇ f x‖) / (σ2 + L) := by
              field_simp [hden_pos.ne']
      _ ≤ ((σ2 * L) * ‖x - xStar‖ ^ (2 : ℕ) + ‖∇ f x‖ ^ (2 : ℕ)) / (σ2 + L) := by
            exact div_le_div_of_nonneg_right hAMGM hden_pos.le
      _ ≤ inner ℝ (∇ f x) (x - xStar) := hpair'
  -- Rewrite the threshold and divide by the positive coefficient denominator.
  rw [firstOrderNondegeneracyThreshold_eq_secant_constant hσ2_nonneg hL_pos]
  rw [firstOrderNondegeneracyCoefficient_def]
  exact (le_div_iff₀ hprod_pos).2 <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcore

/-- Lemma 4.2.6 (1): if `f` lies in the strong-convex smooth class `𝓢^{1,1}_{σ₂,L}`, then
relative to any chosen global minimizer `xStar` there exists a uniform first-order
nondegeneracy lower bound `τ` whose size is at least the explicit threshold
`2 * sqrt q[σ₂, L] / (1 + q[σ₂, L])`. -/
theorem exists_firstOrderNondegeneracyLowerBound_of_mem_S11
    (hf : f ∈ 𝓢[σ2, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar) :
    ∃ τ : ℝ,
      2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]) ≤ τ ∧
        IsFirstOrderNondegeneracyLowerBound f xStar τ := by
  by_cases hE : Subsingleton E
  · let τ0 : ℝ := max (2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L])) 1
    refine ⟨τ0, le_max_left _ _, ?_⟩
    refine ⟨lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro x hx
    exact (hx (hE.elim x xStar)).elim
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hf' : IsStrongConvexSmoothObjective σ2 L f := mem_S11_iff.mp hf
    have hσ2_le_L : σ2 ≤ L := hf'.mu_le_L
    have hL_pos : 0 < L := lt_of_lt_of_le hf'.mu_pos hσ2_le_L
    have hq_pos : 0 < q[σ2, L] := by
      change 0 < σ2 / L
      exact div_pos hf'.mu_pos hL_pos
    have hτ_pos : 0 < 2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]) := by
      have hden_pos : 0 < 1 + q[σ2, L] := by
        nlinarith
      exact div_pos (mul_pos two_pos (Real.sqrt_pos.2 hq_pos)) hden_pos
    refine ⟨2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]), le_rfl, ?_⟩
    refine ⟨hτ_pos, ?_⟩
    intro x hx
    -- The pointwise lower bound is the normalized secant inequality proved above.
    exact firstOrderNondegeneracyThreshold_le_coefficient_of_mem_S11 hf hxStar hx

-- Proof sketch: apply the scalar inequality `2 * sqrt γ / (1 + γ) > sqrt γ` with
-- `γ = q[σ₂, L]`. The primitive scalar assumptions `0 < σ₂` and `σ₂ < L` give
-- `0 < q[σ₂, L] < 1`, so any `τ` above the explicit threshold automatically satisfies
-- `sqrt q[σ₂, L] < τ`.
/-- Lemma 4.2.6 (2): if `0 < σ₂` and `σ₂ < L`, then every lower bound `τ` dominating the explicit
threshold `2 * sqrt q[σ₂, L] / (1 + q[σ₂, L])` automatically satisfies the strict improvement
`sqrt q[σ₂, L] < τ`. -/
theorem sqrt_q_lt_of_firstOrderNondegeneracyThreshold_le
    (hσ2 : 0 < σ2)
    (hσL : σ2 < L)
    (hτ : 2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]) ≤ τ) :
    Real.sqrt q[σ2, L] < τ := by
  have hL_pos : 0 < L := lt_trans hσ2 hσL
  have hq_pos : 0 < q[σ2, L] := by
    change 0 < σ2 / L
    exact div_pos hσ2 hL_pos
  have hq_lt_one : q[σ2, L] < 1 := by
    change σ2 / L < 1
    exact (div_lt_one hL_pos).2 hσL
  have hfactor_gt : 1 < 2 / (1 + q[σ2, L]) := by
    have hden_pos : 0 < 1 + q[σ2, L] := by
      linarith
    have hnum : 1 + q[σ2, L] < 2 := by
      linarith
    exact (one_lt_div hden_pos).2 hnum
  have hsqrt_pos : 0 < Real.sqrt q[σ2, L] := Real.sqrt_pos.2 hq_pos
  have hstrict_threshold :
      Real.sqrt q[σ2, L] < 2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]) := by
    have hmul :
        Real.sqrt q[σ2, L] * 1 <
          Real.sqrt q[σ2, L] * (2 / (1 + q[σ2, L])) := by
      exact mul_lt_mul_of_pos_left hfactor_gt hsqrt_pos
    calc
      Real.sqrt q[σ2, L] = Real.sqrt q[σ2, L] * 1 := by ring
      _ < Real.sqrt q[σ2, L] * (2 / (1 + q[σ2, L])) := hmul
      _ = 2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]) := by ring
  exact lt_of_lt_of_le hstrict_threshold hτ

/-- A global minimizer of a strongly convex smooth objective is first-order nondegenerate as soon
as Lemma 4.2.6 supplies the explicit positive lower bound on the coefficient. -/
-- Proof sketch: extract `τ` from Lemma 4.2.6 (1), use the `C¹` component of
-- `IsStrongConvexSmoothObjective` to obtain `HasGradientAt f (∇ f x) x` away from `xStar`, and
-- package these data into `IsFirstOrderNondegenerate f xStar`.
theorem isFirstOrderNondegenerate_of_mem_S11
    (hf : f ∈ 𝓢[σ2, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar) :
    IsFirstOrderNondegenerate f xStar := by
  have hf' : IsStrongConvexSmoothObjective σ2 L f := mem_S11_iff.mp hf
  obtain ⟨τ0, -, hτ0⟩ := exists_firstOrderNondegeneracyLowerBound_of_mem_S11 hf hxStar
  refine ⟨hxStar, ?_, ⟨τ0, hτ0⟩⟩
  intro x hx
  -- The smooth owner already packages `C¹` regularity, so differentiability is immediate.
  exact hf'.contDiff.differentiable_one x
