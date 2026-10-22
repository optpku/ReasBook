/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_1_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

section

variable (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)

local notation "ψ" => cubicRegularizedQuadraticDualFunction g H M
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)
local notation "A" lam => H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)
local notation "resolvent" lam => -Matrix.mulVec ((A lam)⁻¹) g

variable {lamStar : ℝ}

/-- Helper for Proposition 4.1.14: a dual maximizer over
`cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici 0` is nonnegative. -/
lemma dual_maximizer_nonneg
    (hmax : IsMaxOn ψ Dplus lamStar) :
    0 ≤ lamStar := by
  -- Read the nonnegativity constraint directly from the `Set.Ici 0` factor of `Dplus`.
  simpa using hmax.1.2

omit g H in
/-- Helper for Proposition 4.1.14: if `r = (2 / M) λ*`, then the fixed-point parameter
`(M r) / 2` recovers `λ*`. -/
lemma step_length_parameter_eq_lambda
    (hM : 0 < M)
    {lamStar r : ℝ}
    (hr : r = (2 / M : ℝ) * lamStar) :
    (M * r) / 2 = lamStar := by
  -- Rewrite `r` by the scalar identity from Proposition 4.1.14 (1).
  rw [hr]
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hMul : M * (2 / M : ℝ) = 2 := by
    field_simp [hM_ne]
  -- Collapse the parameter algebraically to `λ*`.
  calc
    (M * ((2 / M : ℝ) * lamStar)) / 2
        = ((M * (2 / M : ℝ)) * lamStar) / 2 := by ring
    _ = (2 * lamStar) / 2 := by rw [hMul]
    _ = lamStar := by ring

omit g M in
/-- Helper for Proposition 4.1.14: the interior spectral bound and dual feasibility imply
`(-λ_min(H))⁺ ≤ λ*`. -/
lemma posPart_neg_leastEigenvalue_le_dual_multiplier
    (hlam : -λ_min(H) < lamStar)
    (hnonneg : 0 ≤ lamStar) :
    (-λ_min(H))⁺ ≤ lamStar := by
  -- Rewrite the positive part as a maximum and bound each branch separately.
  simpa [posPart_def] using
    (max_le_iff.mpr ⟨le_of_lt hlam, hnonneg⟩)

-- Proof sketch: rewrite the chosen point `hStar` by the resolvent representation and then apply
-- the earlier norm identity from Proposition 4.1.13.
/-- Proposition 4.1.14 (1): if the chosen point `hStar` is represented by
`hStar = -(H + λ* I)⁻¹ g` and `r := ‖hStar‖`, then `r = (2 / M) λ*`. -/
theorem cubicRegularizedQuadratic_stepLength_eq
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    (hStar : E) (hhStar : hStar = resolvent lamStar) :
    let r := ‖hStar‖
    r = (2 / M : ℝ) * lamStar := by
  -- Unfold the displayed step length and compare the chosen point with the canonical resolvent.
  dsimp
  have hhNorm : ‖hStar‖ = ‖resolvent lamStar‖ := by
    simpa using congrArg norm hhStar
  -- Proposition 4.1.13 already proves the norm identity for the resolvent point.
  calc
    ‖hStar‖ = ‖resolvent lamStar‖ := hhNorm
    _ = (2 / M : ℝ) * lamStar := by
      simpa using
        cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer
          (g := g) (H := H) (M := M) hM hH hmax hlam

-- Proof sketch: Proposition 4.1.14 (1) identifies `r` with `(2 / M) λ*`, so
-- `(M * r) / 2 = λ*`. Substituting that identity into the resolvent formula yields the claimed
-- fixed-point relation.
/-- Fixed-point reformulation from Proposition 4.1.14: if
`hStar = -(H + λ* I)⁻¹ g` and `r := ‖hStar‖`, then
`r = ‖-(H + (M r / 2) I)⁻¹ g‖`. -/
theorem cubicRegularizedQuadratic_stepLength_fixedPoint
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    (hStar : E) (hhStar : hStar = resolvent lamStar) :
    let r := ‖hStar‖
    r = ‖resolvent ((M * r) / 2)‖ := by
  -- Unfold the scalar step length so the parameter becomes `(M * ‖hStar‖) / 2`.
  dsimp
  have hr : ‖hStar‖ = (2 / M : ℝ) * lamStar := by
    simpa using
      cubicRegularizedQuadratic_stepLength_eq
        (g := g) (H := H) (M := M) hM hH hmax hlam hStar hhStar
  have hparam : (M * ‖hStar‖) / 2 = lamStar := by
    exact step_length_parameter_eq_lambda (M := M) hM hr
  have hhNorm : ‖hStar‖ = ‖resolvent lamStar‖ := by
    simpa using congrArg norm hhStar
  -- Substituting the recovered parameter turns the right-hand side back into `‖hStar‖`.
  rw [hparam]
  exact hhNorm

-- Proof sketch: the maximizer hypothesis gives `0 ≤ λ*`, while `hlam` yields
-- `-λ_min(H) ≤ λ*`. Hence `(-λ_min(H))⁺ ≤ λ*`. Multiply by the nonnegative factor `2 / M` and
-- use Proposition 4.1.14 (1).
/-- Lower-bound conclusion from Proposition 4.1.14: if
`hStar = -(H + λ* I)⁻¹ g` and `r := ‖hStar‖`, then
`(2 / M) (-λ_min(H))_+ ≤ r`. -/
theorem cubicRegularizedQuadratic_stepLength_lower_bound
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    (hStar : E) (hhStar : hStar = resolvent lamStar) :
    let r := ‖hStar‖
    (2 / M : ℝ) * (-λ_min(H))⁺ ≤ r := by
  -- Unfold the displayed step length and recover the dual-side scalar bounds.
  dsimp
  have hr : ‖hStar‖ = (2 / M : ℝ) * lamStar := by
    simpa using
      cubicRegularizedQuadratic_stepLength_eq
        (g := g) (H := H) (M := M) hM hH hmax hlam hStar hhStar
  have hnonneg : 0 ≤ lamStar := dual_maximizer_nonneg (lamStar := lamStar) hmax
  have hposPart : (-λ_min(H))⁺ ≤ lamStar := by
    exact posPart_neg_leastEigenvalue_le_dual_multiplier
      (H := H) (lamStar := lamStar) hlam hnonneg
  have hscale : 0 ≤ (2 / M : ℝ) := by
    positivity
  -- Scale the dual-side comparison and then rewrite the right-hand side by Proposition 4.1.14 (1).
  calc
    (2 / M : ℝ) * (-λ_min(H))⁺ ≤ (2 / M : ℝ) * lamStar := by
      exact mul_le_mul_of_nonneg_left hposPart hscale
    _ = ‖hStar‖ := by rw [hr]

end
