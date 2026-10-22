/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped LocalModelNotation Manifold
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation
open ModifiedGaussNewtonStep

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable (problem : SmoothMap) (φ : E₂ → ℝ) [IsSharpMeritFunction φ]

local notation "f" => meritFunctionReformulation problem φ
local notation "ψ" => ψ[problem; φ; (fderiv ℝ problem)]

/-- The modified Gauss--Newton local model is finite on every closed trust-region ball, so the
source-facing local-model decrease `Δ_r(x)` is defined at every point. -/
theorem modifiedGaussNewtonLocalModel_mem_finiteDomain
    (problem : SmoothMap) (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    (r : NNReal) (x : E₁) :
    x ∈ localModelFiniteDomain (ψ[problem; φ; (fderiv ℝ problem)]) r :=
  mem_localModelFiniteDomain_of_bddBelow (ψ[problem; φ; (fderiv ℝ problem)]) r x
    (bddBelow_image_closedBall_of_nonneg (ψ[problem; φ; (fderiv ℝ problem)]) r
      (fun x y ↦
        show 0 ≤ φ (problem x + fderiv ℝ problem x (y - x)) from
          IsMeritFunction.nonneg _)
      x)

/-- The scalar cutoff function `χ` from the quadratic-regularization lower bound, given by
`χ(t) = t - 1 / 2` for `t ≥ 1` and `χ(t) = t² / 2` for `t < 1`. -/
def modifiedGaussNewtonQuadraticChi (t : ℝ) : ℝ :=
  if 1 ≤ t then t - 1 / 2 else (1 / 2 : ℝ) * t ^ (2 : ℕ)

namespace ModifiedGaussNewtonQuadraticChiNotation

scoped notation:max "χ" => modifiedGaussNewtonQuadraticChi

end ModifiedGaussNewtonQuadraticChiNotation

open scoped ModifiedGaussNewtonQuadraticChiNotation

-- Proof sketch: unfold `modifiedGaussNewtonQuadraticChi` and use the branch condition `t < 1`
-- to select the quadratic branch of the `if`.
/-- Below the threshold `t = 1`, the cutoff function `χ` is equal to `t² / 2`. -/
theorem modifiedGaussNewtonQuadraticChi_of_lt_one {t : ℝ} (ht : t < 1) :
    χ t = (1 / 2 : ℝ) * t ^ (2 : ℕ) := by
  simp [modifiedGaussNewtonQuadraticChi, if_neg (not_le_of_gt ht)]

-- Proof sketch: unfold `modifiedGaussNewtonQuadraticChi` and use the branch condition `1 ≤ t`
-- to select the affine branch of the `if`.
/-- Above the threshold `t = 1`, the cutoff function `χ` is equal to `t - 1 / 2`. -/
theorem modifiedGaussNewtonQuadraticChi_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    χ t = t - 1 / 2 := by
  simp [modifiedGaussNewtonQuadraticChi, if_pos ht]

/-- The modified Gauss--Newton specialization of the canonical local-model decrease `Δ_r(x)`,
obtained by supplying the finite-domain proof coming from the nonnegativity of the sharp merit
function on each closed trust-region ball. The source-facing notation is
`Δ[problem; φ; r](x)`. -/
abbrev modifiedGaussNewtonLocalDecrease
    (problem : SmoothMap) (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    (r : NNReal) (x : E₁) : ℝ :=
  localModelDecreaseAt
    (meritFunctionReformulation problem φ)
    (ψ[problem; φ; (fderiv ℝ problem)])
    r x
    (modifiedGaussNewtonLocalModel_mem_finiteDomain problem φ r x)

namespace ModifiedGaussNewtonLocalDecreaseNotation

/- Source-facing Lean notation for the textbook modified Gauss--Newton local decrease `Δ_r(x)`. -/
scoped notation:max "Δ[" problem:arg "; " φ:arg "; " r:arg "](" x:arg ")" =>
  modifiedGaussNewtonLocalDecrease problem φ r x

end ModifiedGaussNewtonLocalDecreaseNotation

open scoped ModifiedGaussNewtonLocalDecreaseNotation

/-- Helper for Lemma 4.4.3: the modified Gauss--Newton local-model decrease over a closed
trust-region ball is always nonnegative. -/
theorem modifiedGaussNewton_localDecrease_nonneg
    (problem : SmoothMap) (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    (r : NNReal) (x : E₁) :
    0 ≤ Δ[problem; φ; r](x) := by
  -- Reuse the closed-ball infimum formula for `Δ_r(x)` with the canonical nonnegativity bound.
  have hS_bdd :
      BddBelow
        ((modifiedGaussNewtonLocalModel problem φ (fderiv ℝ problem)) x ''
          Metric.closedBall x r) := by
    simpa using
      bddBelow_image_closedBall_of_nonneg
        (modifiedGaussNewtonLocalModel problem φ (fderiv ℝ problem)) r
        (fun x₀ y ↦
          show 0 ≤ φ (problem x₀ + fderiv ℝ problem x₀ (y - x₀)) from
            IsMeritFunction.nonneg _)
        x
  have hDelta :
      Δ[problem; φ; r](x) =
        meritFunctionReformulation problem φ x -
          sInf
            ((modifiedGaussNewtonLocalModel problem φ (fderiv ℝ problem)) x ''
              Metric.closedBall x r) := by
    simpa using
      localModelDecreaseAt_eq_sub_sInf_of_bddBelow
        (meritFunctionReformulation problem φ)
        (modifiedGaussNewtonLocalModel problem φ (fderiv ℝ problem))
        r x hS_bdd
  have hsInf_le_fx :
      sInf
          ((modifiedGaussNewtonLocalModel problem φ (fderiv ℝ problem)) x ''
            Metric.closedBall x r) ≤
        meritFunctionReformulation problem φ x := by
    refine csInf_le hS_bdd ?_
    refine ⟨x, Metric.mem_closedBall_self r.2, ?_⟩
    simp [modifiedGaussNewtonLocalModel_apply, meritFunctionReformulation_apply]
  -- Compare the infimum with the value at the center point `x`.
  linarith [hDelta, hsInf_le_fx]

/-- Helper for Lemma 4.4.3: every `t ∈ [0, 1]` gives a quadratic lower bound on the modified
Gauss--Newton model gap in terms of the trust-region decrease `Δ_r(x)`. -/
theorem modifiedGaussNewton_modelGap_ge_scaled_localDecrease
    (M : ℝ)
    (hM : 0 < M)
    (step :
      ModifiedGaussNewtonStep
        ψ
        Set.univ M)
    (x : E₁) (r : NNReal) (t : ℝ)
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    δ[step; f](x) ≥
      t * Δ[problem; φ; r](x) -
        (M / 2 : ℝ) * t ^ (2 : ℕ) * (r : ℝ) ^ (2 : ℕ) := by
  let merit : E₁ → ℝ := meritFunctionReformulation problem φ
  let model : E₁ → E₁ → ℝ :=
    modifiedGaussNewtonLocalModel problem φ (fderiv ℝ problem)
  let S : Set ℝ := model x '' Metric.closedBall x r
  have hS_bdd : BddBelow S := by
    simpa [S] using
      bddBelow_image_closedBall_of_nonneg model r
        (fun x y ↦ by
          simpa [modifiedGaussNewtonLocalModel_apply] using
            (IsMeritFunction.nonneg (φ := φ)
              (problem x + fderiv ℝ problem x (y - x))))
        x
  have hDelta :
      Δ[problem; φ; r](x) = merit x - sInf S := by
    simpa [S, merit, model] using
      localModelDecreaseAt_eq_sub_sInf_of_bddBelow merit model r x hS_bdd
  have hconv : ConvexOn ℝ Set.univ (model x) := by
    simpa using
      modifiedGaussNewtonLocalModel_convex problem φ (fderiv ℝ problem)
        (IsSharpMeritFunction.convex (φ := φ)) x
  have hmin :
      IsMinOn (quadraticallyRegularizedObjective (model x) M x) Set.univ (step.point x) := by
    simpa using step.isMinOn_point x
  -- Remove the infimum by choosing an `ε`-approximate minimizer on the closed ball.
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hS_nonempty : S.Nonempty := by
    refine ⟨ψ x x, ?_⟩
    refine ⟨x, Metric.mem_closedBall_self r.2, rfl⟩
  have hsInf_lt : sInf S < sInf S + ε := lt_add_of_pos_right (sInf S) hε
  rcases exists_lt_of_csInf_lt hS_nonempty hsInf_lt with ⟨v, hvS, hvlt⟩
  rcases hvS with ⟨y, hyBall, rfl⟩
  let z : E₁ := x + t • (y - x)
  have hmin_z :
      f[step](x) ≤ quadraticallyRegularizedObjective (model x) M x z := by
    simpa [z, modelValueAtUniv_def, residualAtUniv_def, quadraticallyRegularizedObjective_apply]
      using (isMinOn_univ_iff.mp hmin) z
  have hpsi_y :
      model x y ≤ merit x - Δ[problem; φ; r](x) + ε := by
    rw [hDelta]
    linarith
  have hsegment : z = AffineMap.lineMap x y t := by
    rw [AffineMap.lineMap_apply_module']
    simp [z]
    abel_nf
  have hpsi_z_convex :
      model x z ≤ (1 - t) * model x x + t * model x y := by
    simpa [hsegment, AffineMap.lineMap_apply_module, smul_eq_mul] using
      hconv.2 (by simp) (by simp) (sub_nonneg.mpr ht1) ht0 (by ring)
  have hpsi_x : model x x = merit x := by
    simp [merit, model, meritFunctionReformulation_apply]
  have hpsi_z :
      model x z ≤ merit x - t * Δ[problem; φ; r](x) + t * ε := by
    rw [hpsi_x] at hpsi_z_convex
    nlinarith
  have hz_sub : z - x = t • (y - x) := by
    simp [z]
    abel_nf
  have hy_norm : ‖y - x‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hyBall
  have hy_sq :
      ‖y - x‖ ^ (2 : ℕ) ≤ (r : ℝ) ^ (2 : ℕ) := by
    nlinarith
  have hnorm_z :
      ‖z - x‖ ^ (2 : ℕ) = t ^ (2 : ℕ) * ‖y - x‖ ^ (2 : ℕ) := by
    rw [hz_sub, norm_smul, Real.norm_of_nonneg ht0, mul_pow]
  have hnorm_z_le :
      ‖z - x‖ ^ (2 : ℕ) ≤ t ^ (2 : ℕ) * (r : ℝ) ^ (2 : ℕ) := by
    rw [hnorm_z]
    exact mul_le_mul_of_nonneg_left hy_sq (sq_nonneg t)
  have hpenalty_z :
      (M / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) ≤
        (M / 2 : ℝ) * t ^ (2 : ℕ) * (r : ℝ) ^ (2 : ℕ) := by
    have hcoeff_nonneg : 0 ≤ (M / 2 : ℝ) := by positivity
    have :=
      mul_le_mul_of_nonneg_left hnorm_z_le hcoeff_nonneg
    simpa [mul_assoc] using this
  have htε_le : t * ε ≤ ε := by
    nlinarith
  have hmodel_bound :
      f[step](x) ≤
        f x - t * Δ[problem; φ; r](x) + ε +
          (M / 2 : ℝ) * t ^ (2 : ℕ) * (r : ℝ) ^ (2 : ℕ) := by
    linarith
  -- Rearranging the upper bound on the model value gives the desired lower bound on `δ_M(x)`.
  have hdelta : δ[step; f](x) = f x - f[step](x) := by
    simp
  rw [hdelta]
  linarith

/-- Helper for Lemma 4.4.3: on a positive scale `c`, the weighted chi-expression can be rewritten
as a reciprocal branch below the threshold and an affine branch above it. -/
theorem modifiedGaussNewton_chi_weighted_eq_piecewise
    {a c M : ℝ}
    (ha : 0 ≤ a)
    (hc : 0 < c)
    (hM : 0 < M) :
    M * c * χ (a / (M * c)) =
      if a ≤ M * c then a ^ (2 : ℕ) / (2 * M * c) else a - (M * c) / 2 := by
  have hMc : 0 < M * c := mul_pos hM hc
  by_cases hle : a ≤ M * c
  · by_cases heq : a = M * c
    · subst heq
      have hratio : 1 ≤ (M * c) / (M * c) := by
        rw [div_self hMc.ne']
      rw [modifiedGaussNewtonQuadraticChi_of_one_le hratio, if_pos le_rfl]
      field_simp [hMc.ne']
      ring
    · have hlt : a < M * c := lt_of_le_of_ne hle heq
      have hratio : a / (M * c) < 1 := by
        exact (div_lt_one hMc).2 hlt
      rw [modifiedGaussNewtonQuadraticChi_of_lt_one hratio, if_pos hle]
      field_simp [hMc.ne']
  · have hratio : 1 ≤ a / (M * c) := by
      exact (one_le_div hMc).2 (by linarith)
    rw [modifiedGaussNewtonQuadraticChi_of_one_le hratio, if_neg hle]
    field_simp [hMc.ne']

-- Proof sketch: compare the quadratic-regularized model value at the minimizer `step x` with the
-- one-dimensional path `y = x + τ (y₀ - x)` for a point `y₀` in the radius-`r` ball that nearly
-- attains the local-model infimum; convexity of the sharp merit function gives
-- `ψ(x; x + τ (y₀ - x)) ≤ f(x) - τ Δ_r(x)`, and maximizing the resulting scalar quadratic over
-- `τ ∈ [0, 1]` yields the factor `M r² χ(Δ_r(x) / (M r²))`.
/-- Lemma 4.4.3: for a smooth nonlinear equation problem `problem`, a sharp merit function `φ`,
and a modified Gauss--Newton step with positive regularization parameter `M`, the model gap
`δ_M(x)` is bounded below by `M r² χ(Δ_r(x) / (M r²))` for every `x` and every radius `r`. -/
theorem modifiedGaussNewton_modelGap_ge_localModelDecrease_chi
    (M : ℝ)
    (hM : 0 < M)
    (step :
      ModifiedGaussNewtonStep
        ψ
        Set.univ M)
    (x : E₁) (r : NNReal) :
    δ[step; f](x) ≥
      M * (r : ℝ) ^ (2 : ℕ) *
        χ (Δ[problem; φ; r](x) /
          (M * (r : ℝ) ^ (2 : ℕ))) := by
  by_cases hr0 : r = 0
  · have hdelta_nonneg : 0 ≤ δ[step; f](x) := by
      have hmin_x := (isMinOn_univ_iff.mp (step.isMinOn_point x)) x
      simpa [modelValueAtUniv_def, residualAtUniv_def, quadraticallyRegularizedObjective_apply,
        meritFunctionReformulation_apply, hr0] using hmin_x
    simpa [hr0] using hdelta_nonneg
  have ha : 0 ≤ Δ[problem; φ; r](x) :=
    modifiedGaussNewton_localDecrease_nonneg problem φ r x
  have hr_ne : (r : ℝ) ≠ 0 := by
    exact_mod_cast hr0
  have hr_sq_pos : 0 < (r : ℝ) ^ (2 : ℕ) := by
    have : 0 < (r : ℝ) ^ 2 := sq_pos_of_ne_zero hr_ne
    simpa using this
  have hden_pos : 0 < M * (r : ℝ) ^ (2 : ℕ) := mul_pos hM hr_sq_pos
  by_cases hratio :
      1 ≤ Δ[problem; φ; r](x) / (M * (r : ℝ) ^ (2 : ℕ))
  · -- In the affine branch, the optimizer is `t = 1`.
    calc
      δ[step; f](x) ≥
          (1 : ℝ) * Δ[problem; φ; r](x) -
            (M / 2 : ℝ) * (1 : ℝ) ^ (2 : ℕ) * (r : ℝ) ^ (2 : ℕ) := by
        exact
          modifiedGaussNewton_modelGap_ge_scaled_localDecrease
            problem φ M hM step x r 1 le_rfl le_rfl
      _ = Δ[problem; φ; r](x) - (M * (r : ℝ) ^ (2 : ℕ)) / 2 := by ring
      _ = M * (r : ℝ) ^ (2 : ℕ) *
            χ (Δ[problem; φ; r](x) / (M * (r : ℝ) ^ (2 : ℕ))) := by
          rw [modifiedGaussNewtonQuadraticChi_of_one_le hratio]
          field_simp [hden_pos.ne']
          ring
  · have hratio_lt :
        Δ[problem; φ; r](x) / (M * (r : ℝ) ^ (2 : ℕ)) < 1 :=
      lt_of_not_ge hratio
    let t : ℝ := Δ[problem; φ; r](x) / (M * (r : ℝ) ^ (2 : ℕ))
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg ha hden_pos.le
    have ht1 : t ≤ 1 := hratio_lt.le
    -- In the quadratic branch, the optimizer is `t = Δ / (M r²)`.
    calc
      δ[step; f](x) ≥
          t * Δ[problem; φ; r](x) -
            (M / 2 : ℝ) * t ^ (2 : ℕ) * (r : ℝ) ^ (2 : ℕ) := by
        exact
          modifiedGaussNewton_modelGap_ge_scaled_localDecrease
            problem φ M hM step x r t ht0 ht1
      _ = (Δ[problem; φ; r](x)) ^ (2 : ℕ) /
            (2 * M * (r : ℝ) ^ (2 : ℕ)) := by
          dsimp [t]
          field_simp [hden_pos.ne']
          ring
      _ = M * (r : ℝ) ^ (2 : ℕ) *
            χ (Δ[problem; φ; r](x) / (M * (r : ℝ) ^ (2 : ℕ))) := by
          rw [modifiedGaussNewtonQuadraticChi_of_lt_one hratio_lt]
          field_simp [hden_pos.ne']
          ring

-- Proof sketch: write the right-hand side as a scalar function of `M > 0`, split into the
-- regimes `Δ_r(x) / (M r²) ≥ 1` and `Δ_r(x) / (M r²) < 1`, and check directly in each branch
-- that increasing `M` decreases the value.
/-- For fixed `problem`, `φ`, `x`, and radius `r`, the right-hand side of the lower
bound in `modifiedGaussNewton_modelGap_ge_localModelDecrease_chi` is decreasing as a function of
the regularization parameter `M > 0`. -/
theorem modifiedGaussNewton_lowerBound_rhs_antitoneOn
    (x : E₁) (r : NNReal) :
    AntitoneOn
      (fun M : ℝ ↦
        M * (r : ℝ) ^ (2 : ℕ) *
          χ (Δ[problem; φ; r](x) /
            (M * (r : ℝ) ^ (2 : ℕ))))
      (Set.Ioi (0 : ℝ)) := by
  intro M₁ hM₁ M₂ hM₂ hMle
  by_cases hr0 : r = 0
  · simp [hr0]
  let a : ℝ := Δ[problem; φ; r](x)
  let c : ℝ := (r : ℝ) ^ (2 : ℕ)
  have ha : 0 ≤ a := by
    simpa [a] using modifiedGaussNewton_localDecrease_nonneg problem φ r x
  have hr_ne : (r : ℝ) ≠ 0 := by
    exact_mod_cast hr0
  have hc : 0 < c := by
    dsimp [c]
    have : 0 < (r : ℝ) ^ 2 := sq_pos_of_ne_zero hr_ne
    simpa using this
  have hpiece₁ :
      M₁ * c * χ (a / (M₁ * c)) =
        if a ≤ M₁ * c then a ^ (2 : ℕ) / (2 * M₁ * c) else a - (M₁ * c) / 2 := by
    simpa [a, c] using modifiedGaussNewton_chi_weighted_eq_piecewise ha hc hM₁
  have hpiece₂ :
      M₂ * c * χ (a / (M₂ * c)) =
        if a ≤ M₂ * c then a ^ (2 : ℕ) / (2 * M₂ * c) else a - (M₂ * c) / 2 := by
    simpa [a, c] using modifiedGaussNewton_chi_weighted_eq_piecewise ha hc hM₂
  -- Compare the two positive-parameter branches using the threshold `a ≤ M c`.
  change M₂ * c * χ (a / (M₂ * c)) ≤ M₁ * c * χ (a / (M₁ * c))
  by_cases hbranch₁ : a ≤ M₁ * c
  · have hbranch₂ : a ≤ M₂ * c := by
      calc
        a ≤ M₁ * c := hbranch₁
        _ ≤ M₂ * c := by
          gcongr
    rw [hpiece₁, hpiece₂, if_pos hbranch₁, if_pos hbranch₂]
    have hden₁_pos : 0 < 2 * M₁ * c := by positivity
    have hden_le : 2 * M₁ * c ≤ 2 * M₂ * c := by
      nlinarith
    have hinv :
        (2 * M₂ * c)⁻¹ ≤ (2 * M₁ * c)⁻¹ := by
      exact one_div_le_one_div_of_le hden₁_pos hden_le
    have :=
      mul_le_mul_of_nonneg_left hinv (sq_nonneg a)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  · have hgt₁ : M₁ * c < a := lt_of_not_ge hbranch₁
    by_cases hbranch₂ : a ≤ M₂ * c
    · rw [hpiece₁, hpiece₂, if_neg hbranch₁, if_pos hbranch₂]
      have hMc₂_pos : 0 < M₂ * c := mul_pos hM₂ hc
      have hnum_le : a ^ (2 : ℕ) ≤ a * (M₂ * c) := by
        calc
          a ^ (2 : ℕ) = a * a := by ring
          _ ≤ a * (M₂ * c) := mul_le_mul_of_nonneg_left hbranch₂ ha
      have hdiv :
          a ^ (2 : ℕ) / (M₂ * c) ≤ a := by
        rw [div_le_iff hMc₂_pos]
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hnum_le
      have hhalf_upper :
          a ^ (2 : ℕ) / (2 * M₂ * c) ≤ a / 2 := by
        have :=
          mul_le_mul_of_nonneg_left hdiv (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have hhalf_lower :
          a / 2 ≤ a - (M₁ * c) / 2 := by
        nlinarith
      exact hhalf_upper.trans hhalf_lower
    · rw [hpiece₁, hpiece₂, if_neg hbranch₁, if_neg hbranch₂]
      nlinarith

end
