/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_4_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators LocalModelNotation Manifold
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonLocalDecreaseNotation
open scoped ModifiedGaussNewtonQuadraticChiNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Theorem 4.4.1 lies in the modified Gauss--Newton trajectory / infinite-series domain.

Sampled owner declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate and
  regularization sequences;
* `ModifiedGaussNewtonStep.residualAtUniv` in `Definition_4_4_12`, the canonical whole-space
  residual view attached to a chosen modified Gauss--Newton step;
* `localModelDecreaseAt` in `Definition_4_4_13`, the canonical local-decrease owner specialized
  here through the finite-domain bridge from `Lemma_4_4_3`;
* `χ` in `Lemma_4_4_3`, the source-facing quadratic cutoff entering the textbook lower bounds;
* `cubicRegularization_residual_cube_summable_and_tsum_le` in `Theorem_4_1_1`, the nearby chapter
  pattern for expressing nonnegative infinite-tail bounds via `Summable` together with a `tsum`
  inequality.

Source/core/bridge triage:
* source-facing: Theorem 4.4.1 for the residual-square and chi-weighted tail estimates along a
  modified Gauss--Newton trajectory;
* core/canonical: `ModifiedGaussNewtonMethod` together with the step residual owner
  `ModifiedGaussNewtonStep.residualAtUniv` and the local-decrease owner
  `localModelDecreaseAt`;
* bridge/view: comparison of the varying regularization sequence `M_k` with the fixed parameter
  `2L`, yielding fixed-parameter tail bounds from the trajectory-owned varying tails.

Primitive data:
* a modified Gauss--Newton method `method`;
* a lower bound `fStar ≤ f z` for the merit reformulation;
* a fixed comparison step at regularization `2L`;
* the radius parameter `r` used in the local-decrease lower bound.

Derived API:
* summability of the nonnegative residual-square and chi-weighted tails;
* gap bounds on the corresponding infinite sums;
* summability and comparison bounds for the fixed-parameter tails derived from the varying ones.

The owner abstraction is therefore still the chapter trajectory object `ModifiedGaussNewtonMethod`.
The refinement here is on the derived series API: the nonnegative tails are stated on a
semantics-preserving `Summable` + `tsum` surface instead of as bare real `tsum` inequalities.
-/

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable
    (problem : SmoothMap)
    (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    (L0 L : ℝ) (x0 : E₁)

local notation "f" => meritFunctionReformulation problem φ
local notation "ψ" => ψ[problem; φ; (fderiv ℝ problem)]

namespace ModifiedGaussNewtonMethod

-- Proof sketch: sum the one-step decrease inequalities
-- `f(x_i) - f(x_{i+1}) ≥ (M_i / 2) r_{M_i}(x_i)^2`, first derived once from
-- `method.step_value_le_modelValue`, `method.step_modelValue_le_merit`, and Lemma 4.4.2, along
-- the tail starting at
-- `k`, telescope the partial sums, and bound the remaining iterate values below by `fStar` via
-- `hf_lower`. Since the residual-square terms are nonnegative, the bounded partial sums give both
-- summability of the tail and the asserted `tsum` bound.
theorem meritFunction_sub_succ_ge_half_mul_residual_sq
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ) :
    f (method k) - f (method (k + 1)) ≥
      (method.regularization k / 2 : ℝ) *
        (r[(method.step k)] (method k)) ^ (2 : ℕ) := by
  -- Compare the accepted next iterate with the owner-side model value at `x_k`.
  have hstep :
      f (method (k + 1)) ≤ f[(method.step k)] (method k) := by
    simpa [method.x_succ k] using method.step_value_le_modelValue k
  -- Lemma 4.4.2 turns the model gap at `x_k` into the residual-square lower bound.
  have hgap :
      δ[(method.step k); f] (method k) ≥
        (method.regularization k / 2 : ℝ) *
          (r[(method.step k)] (method k)) ^ (2 : ℕ) := by
    have hconv :
        ConvexOn ℝ Set.univ (ψ (method k)) := by
      simpa using
        modifiedGaussNewtonLocalModel_convex problem φ (fderiv ℝ problem)
          (IsSharpMeritFunction.convex (φ := φ)) (method k)
    simpa using
      modifiedGaussNewton_modelGap_ge_half_mul_residual_sq
        (step := method.step k) (x := method k) hconv
  -- Rewriting the model gap gives the true one-step merit decrease.
  rw [ModifiedGaussNewtonStep.modelGapAtUniv_def] at hgap
  linarith

/-- Helper for Theorem 4.4.1: telescoping a nonnegative tail whose terms are controlled by the
one-step merit decrease yields both summability of the tail and the corresponding gap bound. -/
lemma tail_summable_and_gap_ge_tsum_of_one_step_decrease
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    {fStar c : ℝ}
    (hf_lower : ∀ z : E₁, fStar ≤ f z)
    (hc : 0 < c)
    (k : ℕ)
    (a : ℕ → ℝ)
    (ha_nonneg : ∀ i, 0 ≤ a i)
    (hdecrease :
      ∀ i,
        c * a i ≤ f (method (k + i)) - f (method (k + i + 1))) :
    Summable a ∧
      f (method k) - fStar ≥ c * ∑' i, a i := by
  have hsum_range_le :
      ∀ n : ℕ, ∑ i ∈ Finset.range n, a i ≤ (f (method k) - fStar) / c := by
    intro n
    have hpointwise :
        ∀ i ∈ Finset.range n,
          a i ≤ (1 / c) * (f (method (k + i)) - f (method (k + i + 1))) := by
      intro i hi
      have hfactor_nonneg : 0 ≤ 1 / c := by positivity
      calc
        a i = (1 / c) * (c * a i) := by
          field_simp [hc.ne']
        _ ≤ (1 / c) * (f (method (k + i)) - f (method (k + i + 1))) := by
          exact mul_le_mul_of_nonneg_left (hdecrease i) hfactor_nonneg
    have htel :
        ∑ i ∈ Finset.range n, (f (method (k + i)) - f (method (k + i + 1))) =
          f (method k) - f (method (k + n)) := by
      simpa [Nat.add_assoc] using
        (Finset.sum_range_sub' (fun i ↦ f (method (k + i))) n)
    have hterminal :
        f (method k) - f (method (k + n)) ≤ f (method k) - fStar := by
      simpa using sub_le_sub_left (hf_lower (method (k + n))) (f (method k))
    have hfactor_nonneg : 0 ≤ 1 / c := by positivity
    calc
      ∑ i ∈ Finset.range n, a i
          ≤ ∑ i ∈ Finset.range n,
              (1 / c) * (f (method (k + i)) - f (method (k + i + 1))) :=
        Finset.sum_le_sum hpointwise
      _ = (1 / c) * ∑ i ∈ Finset.range n,
            (f (method (k + i)) - f (method (k + i + 1))) := by
          rw [Finset.mul_sum]
      _ = (1 / c) * (f (method k) - f (method (k + n))) := by
          rw [htel]
      _ ≤ (1 / c) * (f (method k) - fStar) := by
          exact mul_le_mul_of_nonneg_left hterminal hfactor_nonneg
      _ = (f (method k) - fStar) / c := by
          rw [div_eq_mul_inv, mul_comm]
  have hsum : Summable a :=
    summable_of_sum_range_le ha_nonneg hsum_range_le
  have htsum_le :
      ∑' i, a i ≤ (f (method k) - fStar) / c :=
    Real.tsum_le_of_sum_range_le ha_nonneg hsum_range_le
  refine ⟨hsum, ?_⟩
  -- Multiply the `tsum` estimate by `c` to recover the textbook gap bound.
  simpa [ge_iff_le] using
    (show c * ∑' i, a i ≤ f (method k) - fStar from
      calc
        c * ∑' i, a i ≤ c * ((f (method k) - fStar) / c) := by
          exact mul_le_mul_of_nonneg_left htsum_le hc.le
        _ = f (method k) - fStar := by
          field_simp [hc.ne'])

/-- Helper for Theorem 4.4.1: increasing the regularization parameter can only decrease the
squared residual of a whole-space minimizing modified Gauss--Newton step. -/
lemma residual_sq_le_of_regularization_le
    {M1 M2 : ℝ}
    (hM : M1 ≤ M2)
    (step1 : ModifiedGaussNewtonStep ψ Set.univ M1)
    (step2 : ModifiedGaussNewtonStep ψ Set.univ M2)
    (x : E₁) :
    (r[step2] (x)) ^ (2 : ℕ) ≤ (r[step1] (x)) ^ (2 : ℕ) := by
  have hstep1 :=
    (isMinOn_univ_iff.mp (step1.isMinOn_point x)) (step2.point x)
  have hstep2 :=
    (isMinOn_univ_iff.mp (step2.isMinOn_point x)) (step1.point x)
  -- Adding the two minimizer inequalities cancels the local-model terms.
  have hsum := add_le_add hstep1 hstep2
  rw [quadraticallyRegularizedObjective_apply,
    quadraticallyRegularizedObjective_apply,
    quadraticallyRegularizedObjective_apply,
    quadraticallyRegularizedObjective_apply] at hsum
  have hnorm :
      ‖step2.point x - x‖ ^ (2 : ℕ) ≤ ‖step1.point x - x‖ ^ (2 : ℕ) := by
    nlinarith
  simpa [ModifiedGaussNewtonStep.residualAtUniv_def] using hnorm

/-- Theorem 4.4.1 (1): the residual-square tail starting at `x_k` is summable, and the merit gap
at iterate `x_k` dominates its weighted sum `(L₀ / 2) ∑_{i=k}^∞ r_{Mᵢ}(xᵢ)^2`. -/
theorem gap_ge_residualSqTail
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    {fStar : ℝ}
    (hf_lower : ∀ z : E₁, fStar ≤ f z)
    (k : ℕ) :
    Summable (fun i ↦ (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ)) ∧
      f (method k) - fStar ≥
        (L0 / 2 : ℝ) *
          ∑' i, (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ) := by
  let a : ℕ → ℝ := fun i ↦ (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ)
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    dsimp [a]
    positivity
  -- Apply the generic telescoping lemma with the uniform lower coefficient `L₀ / 2`.
  simpa [a] using
    tail_summable_and_gap_ge_tsum_of_one_step_decrease
      (problem := problem) (φ := φ) (L0 := L0) (L := L) (x0 := x0)
      method hf_lower (show 0 < (L0 / 2 : ℝ) by positivity) k a ha_nonneg
      (fun i ↦ by
        have hratio :
            (L0 / 2 : ℝ) ≤ method.regularization (k + i) / 2 := by
          nlinarith [method.L0_le_regularization (k + i)]
        have hscaled :
            (L0 / 2 : ℝ) * a i ≤
              (method.regularization (k + i) / 2 : ℝ) * a i := by
          exact mul_le_mul_of_nonneg_right hratio (ha_nonneg i)
        exact hscaled.trans
          (method.meritFunction_sub_succ_ge_half_mul_residual_sq (k + i)))

-- Proof sketch: use `method.regularization (k + i) ≤ 2L` termwise to compare the varying
-- regularization residuals with the fixed-parameter residuals. If the varying tail is summable,
-- termwise comparison yields summability of the fixed-parameter tail together with the tail
-- inequality.
/-- Theorem 4.4.1 (2): if the varying-parameter residual-square tail is summable, then the
comparison tail computed with the fixed parameter `2L` is also summable and is bounded by it. -/
theorem residualSqTail_ge_residualSqTailAt_two_mul_L
    (step2L : ModifiedGaussNewtonStep ψ Set.univ (2 * L))
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ)
    (hvarying :
      Summable (fun i ↦ (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ))) :
    Summable (fun i ↦ (r[step2L] (method (k + i))) ^ (2 : ℕ)) ∧
      (L0 / 2 : ℝ) *
          ∑' i, (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ) ≥
        (L0 / 2 : ℝ) *
          ∑' i, (r[step2L] (method (k + i))) ^ (2 : ℕ) := by
  let a : ℕ → ℝ := fun i ↦ (r[step2L] (method (k + i))) ^ (2 : ℕ)
  let b : ℕ → ℝ := fun i ↦ (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ)
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    dsimp [a]
    positivity
  have hterm : ∀ i, a i ≤ b i := by
    intro i
    dsimp [a, b]
    exact
      residual_sq_le_of_regularization_le
        (problem := problem) (φ := φ)
        (hM := method.regularization_le_two_mul_L (k + i))
        (step1 := method.step (k + i))
        (step2 := step2L)
        (x := method (k + i))
  have hfixed : Summable a :=
    hvarying.of_nonneg_of_le ha_nonneg hterm
  have htsum :
      ∑' i, a i ≤ ∑' i, b i :=
    hfixed.tsum_le_tsum hterm hvarying
  refine ⟨by simpa [a] using hfixed, ?_⟩
  -- Multiply the termwise tail comparison by the positive factor `L₀ / 2`.
  simpa [a, b] using
    calc
    (L0 / 2 : ℝ) * ∑' i, b i ≥ (L0 / 2 : ℝ) * ∑' i, a i := by
      exact mul_le_mul_of_nonneg_left htsum (show 0 ≤ (L0 / 2 : ℝ) by positivity)

-- Proof sketch: sum the one-step decrease inequalities
-- `f(x_i) - f(x_{i+1}) ≥ r^2 M_i χ(Δ[problem; φ; r](x_i) / (M_i r^2))`, first derived once from
-- `method.step_value_le_modelValue`, `method.step_modelValue_le_merit`, and Lemma 4.4.3, along
-- the tail
-- starting at `k`, telescope the partial sums, and bound the remaining limit below by `fStar`
-- via `hf_lower`. The chi-weighted terms are nonnegative, so the same argument yields
-- summability of the tail together with the `tsum` inequality.
theorem meritFunction_sub_succ_ge_chiWeighted
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ) (r : NNReal) :
    f (method k) - f (method (k + 1)) ≥
      method.regularization k * (r : ℝ) ^ (2 : ℕ) *
        χ (Δ[problem; φ; r]((method k)) /
          (method.regularization k * (r : ℝ) ^ (2 : ℕ))) := by
  have hstep :
      f (method (k + 1)) ≤ f[(method.step k)] (method k) := by
    simpa [method.x_succ k] using method.step_value_le_modelValue k
  -- Lemma 4.4.3 gives the chi-weighted lower bound on the model gap at `x_k`.
  have hgap :
      δ[(method.step k); f] (method k) ≥
        method.regularization k * (r : ℝ) ^ (2 : ℕ) *
          χ (Δ[problem; φ; r]((method k)) /
            (method.regularization k * (r : ℝ) ^ (2 : ℕ))) := by
    simpa using
      modifiedGaussNewton_modelGap_ge_localModelDecrease_chi
        (problem := problem) (φ := φ)
        (M := method.regularization k)
        (method.regularization_pos k)
        (step := method.step k) (x := method k) r
  -- Rewriting the model gap again yields the true accepted-step decrease.
  rw [ModifiedGaussNewtonStep.modelGapAtUniv_def] at hgap
  linarith

/-- Helper for Theorem 4.4.1: the radius-zero local-model decrease vanishes, since the closed ball
`Metric.closedBall x 0` contains only the center point. -/
lemma localDecrease_zero
    (x : E₁) :
    Δ[problem; φ; (0 : NNReal)](x) = 0 := by
  have hS_bdd :
      BddBelow (ψ x '' Metric.closedBall x (0 : NNReal)) := by
    simpa using
      bddBelow_image_closedBall_of_nonneg
        (ψ[problem; φ; (fderiv ℝ problem)]) (0 : NNReal)
        (fun x y ↦
          show 0 ≤ φ (problem x + fderiv ℝ problem x (y - x)) from
            IsMeritFunction.nonneg _)
        x
  have hDelta :
      Δ[problem; φ; (0 : NNReal)](x) =
        f x - sInf (ψ x '' Metric.closedBall x (0 : NNReal)) := by
    simpa using
      localModelDecreaseAt_eq_sub_sInf_of_bddBelow f ψ (0 : NNReal) x hS_bdd
  have hclosedBall : Metric.closedBall x (0 : NNReal) = {x} := by
    ext y
    constructor
    · intro hy
      have hy_le : dist y x ≤ 0 := by simpa using hy
      have hy_eq : y = x := by
        exact dist_eq_zero.mp (le_antisymm hy_le dist_nonneg)
      simpa [hy_eq]
    · rintro rfl
      simpa using (show dist x x ≤ (0 : ℝ) by simp)
  rw [hDelta, hclosedBall]
  simp [modifiedGaussNewtonLocalModel_apply, meritFunctionReformulation_apply]

/-- Helper for Theorem 4.4.1: each chi-weighted summand is nonnegative for a positive
regularization parameter. -/
lemma chi_weighted_term_nonneg
    (x : E₁) (r : NNReal) {M : ℝ} (hM : 0 < M) :
    0 ≤ M *
      χ (Δ[problem; φ; r](x) /
        (M * (r : ℝ) ^ (2 : ℕ))) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simpa [modifiedGaussNewtonQuadraticChi, localDecrease_zero (problem := problem) (φ := φ) x]
  let t : ℝ :=
    Δ[problem; φ; r](x) / (M * (r : ℝ) ^ (2 : ℕ))
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    have hΔ_nonneg : 0 ≤ Δ[problem; φ; r](x) :=
      modifiedGaussNewton_localDecrease_nonneg problem φ r x
    have hr_ne : (r : ℝ) ≠ 0 := by
      exact_mod_cast hr0
    have hr_sq_pos : 0 < (r : ℝ) ^ (2 : ℕ) := by
      have : 0 < (r : ℝ) ^ 2 := sq_pos_of_ne_zero hr_ne
      simpa using this
    exact div_nonneg hΔ_nonneg (mul_pos hM hr_sq_pos).le
  have hchi_nonneg : 0 ≤ χ t := by
    by_cases hbranch : 1 ≤ t
    · rw [modifiedGaussNewtonQuadraticChi_of_one_le hbranch]
      nlinarith
    · rw [modifiedGaussNewtonQuadraticChi_of_lt_one (lt_of_not_ge hbranch)]
      positivity
  exact mul_nonneg hM.le hchi_nonneg

/-- Theorem 4.4.1 (3): for every radius `r`, the chi-weighted tail
`∑_{i=k}^∞ Mᵢ χ(Δ_r(xᵢ) / (Mᵢ r²))` is summable, and the merit gap at iterate `x_k` dominates the
weighted sum `r² ∑_{i=k}^∞ Mᵢ χ(Δ_r(xᵢ) / (Mᵢ r²))`. -/
theorem gap_ge_chiWeightedTail
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    {fStar : ℝ}
    (hf_lower : ∀ z : E₁, fStar ≤ f z)
    (k : ℕ) (r : NNReal) :
    Summable
        (fun i ↦
          method.regularization (k + i) *
            χ (Δ[problem; φ; r]((method (k + i))) /
              (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ)))) ∧
      f (method k) - fStar ≥
        (r : ℝ) ^ (2 : ℕ) *
          ∑' i,
            (method.regularization (k + i) *
              χ (Δ[problem; φ; r]((method (k + i))) /
                (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ)))) := by
  by_cases hr0 : r = 0
  · constructor
    · -- At radius `0`, every local decrease is zero, so the entire tail vanishes.
      simpa [modifiedGaussNewtonQuadraticChi, hr0,
        localDecrease_zero (problem := problem) (φ := φ)] using
        (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
    · have hgap_nonneg : 0 ≤ f (method k) - fStar := by
        nlinarith [hf_lower (method k)]
      simpa [hr0] using hgap_nonneg
  let a : ℕ → ℝ := fun i ↦
    method.regularization (k + i) *
      χ (Δ[problem; φ; r]((method (k + i))) /
        (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ)))
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    dsimp [a]
    exact
      chi_weighted_term_nonneg
        (problem := problem) (φ := φ)
        (x := method (k + i)) (r := r)
        (method.regularization_pos (k + i))
  have hr_sq_pos : 0 < (r : ℝ) ^ (2 : ℕ) := by
    have hr_ne : (r : ℝ) ≠ 0 := by
      exact_mod_cast hr0
    have : 0 < (r : ℝ) ^ 2 := sq_pos_of_ne_zero hr_ne
    simpa using this
  -- Reuse the generic telescoping argument with coefficient `r²`.
  simpa [a] using
    tail_summable_and_gap_ge_tsum_of_one_step_decrease
      (problem := problem) (φ := φ) (L0 := L0) (L := L) (x0 := x0)
      method hf_lower hr_sq_pos k a ha_nonneg
      (fun i ↦ by
        simpa [a, mul_assoc, mul_left_comm, mul_comm] using
          method.meritFunction_sub_succ_ge_chiWeighted (k + i) r)

-- Proof sketch: apply the antitonicity of
-- `M ↦ M χ(Δ[problem; φ; r](x_i) / (M r^2))` together with
-- `method.regularization (k + i) ≤ 2L` termwise,
-- then compare the resulting weighted tails. If the varying weighted tail is summable, the same
-- termwise comparison gives summability of the fixed-parameter weighted chi-tail and the asserted
-- bound.
/-- Theorem 4.4.1 (4): if the weighted chi-tail for the varying regularization parameters is
summable, then the comparison weighted chi-tail at the fixed parameter `2L` is summable and is
bounded by the varying-parameter tail. -/
theorem chiWeightedTail_ge_chiWeightedTailAt_two_mul_L
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ) (r : NNReal)
    (hvarying :
      Summable
        (fun i ↦
          method.regularization (k + i) *
            χ (Δ[problem; φ; r]((method (k + i))) /
              (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ))))) :
    Summable
        (fun i ↦
          (2 * L) *
            χ (Δ[problem; φ; r]((method (k + i))) /
              ((2 * L) * (r : ℝ) ^ (2 : ℕ)))) ∧
      (r : ℝ) ^ (2 : ℕ) *
          ∑' i,
            (method.regularization (k + i) *
              χ (Δ[problem; φ; r]((method (k + i))) /
                (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ)))) ≥
        (2 * L) * (r : ℝ) ^ (2 : ℕ) *
          ∑' i,
            χ (Δ[problem; φ; r]((method (k + i))) /
              ((2 * L) * (r : ℝ) ^ (2 : ℕ))) := by
  by_cases hr0 : r = 0
  · constructor
    · -- In the zero-radius regime, both weighted chi tails are identically zero.
      simpa [modifiedGaussNewtonQuadraticChi, hr0,
        localDecrease_zero (problem := problem) (φ := φ)] using
        (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
    · simp [modifiedGaussNewtonQuadraticChi, hr0,
        localDecrease_zero (problem := problem) (φ := φ)]
  let a : ℕ → ℝ := fun i ↦
    (2 * L) *
      χ (Δ[problem; φ; r]((method (k + i))) /
        ((2 * L) * (r : ℝ) ^ (2 : ℕ)))
  let b : ℕ → ℝ := fun i ↦
    method.regularization (k + i) *
      χ (Δ[problem; φ; r]((method (k + i))) /
        (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ)))
  have hr_sq_pos : 0 < (r : ℝ) ^ (2 : ℕ) := by
    have hr_ne : (r : ℝ) ≠ 0 := by
      exact_mod_cast hr0
    have : 0 < (r : ℝ) ^ 2 := sq_pos_of_ne_zero hr_ne
    simpa using this
  have hterm : ∀ i, a i ≤ b i := by
    intro i
    have h2L_pos : 0 < 2 * L := by
      exact lt_of_lt_of_le
        (method.regularization_pos (k + i))
        (method.regularization_le_two_mul_L (k + i))
    have hweighted :
        (r : ℝ) ^ (2 : ℕ) * a i ≤ (r : ℝ) ^ (2 : ℕ) * b i := by
      dsimp [a, b]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (modifiedGaussNewton_lowerBound_rhs_antitoneOn
          (problem := problem) (φ := φ) (x := method (k + i)) r)
          (method.regularization (k + i))
          (method.regularization_pos (k + i))
          (2 * L)
          h2L_pos
          (method.regularization_le_two_mul_L (k + i))
    exact (mul_le_mul_left hr_sq_pos).mp hweighted
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    have h2L_pos : 0 < 2 * L := by
      exact lt_of_lt_of_le
        (method.regularization_pos (k + i))
        (method.regularization_le_two_mul_L (k + i))
    dsimp [a]
    exact
      chi_weighted_term_nonneg
        (problem := problem) (φ := φ)
        (x := method (k + i)) (r := r)
        (M := 2 * L) h2L_pos
  have hfixed : Summable a :=
    hvarying.of_nonneg_of_le ha_nonneg hterm
  have htsum :
      ∑' i, a i ≤ ∑' i, b i :=
    hfixed.tsum_le_tsum hterm hvarying
  refine ⟨by simpa [a] using hfixed, ?_⟩
  -- Multiply the unweighted comparison by `r²` to recover the displayed inequality.
  simpa [a, b, mul_assoc, mul_left_comm, mul_comm] using
    calc
    (r : ℝ) ^ (2 : ℕ) * ∑' i, b i ≥ (r : ℝ) ^ (2 : ℕ) * ∑' i, a i := by
      exact mul_le_mul_of_nonneg_left htsum (show 0 ≤ (r : ℝ) ^ (2 : ℕ) by positivity)
    _ = (2 * L) * (r : ℝ) ^ (2 : ℕ) *
          ∑' i,
            χ (Δ[problem; φ; r]((method (k + i))) /
              ((2 * L) * (r : ℝ) ^ (2 : ℕ))) := by
          rw [tsum_mul_left]
          ring

end ModifiedGaussNewtonMethod

end
