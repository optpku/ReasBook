/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Algorithm_3_6_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Lemma_3_6_1
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.Basic

open Filter

section InexactNewtonMethod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Semantic recall: the Chapter 3.6 algorithm file already owns the source-facing
-- `IsInexactNewtonSequence` predicate, so this theorem file reuses that owner and only
-- adds the regular-zero hypothesis and convergence packaging it needs.

/-- A point `xStar` is a regular zero of `F : E → E` when `F xStar = 0`, `F` is continuously
differentiable on a neighborhood of `xStar`, and `fderiv ℝ F xStar` is invertible. -/
def IsRegularZero (F : E → E) (xStar : E) : Prop :=
  F xStar = 0 ∧
    (∃ s ∈ nhds xStar, ContDiffOn ℝ 1 F s) ∧
    (fderiv ℝ F xStar).IsInvertible

/-- Unfolding formula for `IsRegularZero`. -/
theorem isRegularZero_iff (F : E → E) (xStar : E) :
    IsRegularZero F xStar ↔
      F xStar = 0 ∧
        (∃ s ∈ nhds xStar, ContDiffOn ℝ 1 F s) ∧
        (fderiv ℝ F xStar).IsInvertible :=
  Iff.rfl

/-- Linear convergence of an inexact Newton sequence `x` to `xStar` in the source norm induced
by `fderiv ℝ F xStar`. -/
structure InexactNewtonLinearConvergence
    (F : E → E) (xStar : E) (t : ℝ) (x : ℕ → E) : Prop where
  tendsto : Tendsto x atTop (nhds xStar)
  linearRate :
    ∀ k : ℕ,
      ‖fderiv ℝ F xStar (x (k + 1) - xStar)‖ ≤
        t * ‖fderiv ℝ F xStar (x k - xStar)‖

/-- Unfolding specification for `InexactNewtonLinearConvergence`. -/
theorem InexactNewtonLinearConvergence.spec
    {F : E → E} {xStar : E} {t : ℝ} {x : ℕ → E} :
    InexactNewtonLinearConvergence F xStar t x ↔
      Tendsto x atTop (nhds xStar) ∧
        ∀ k : ℕ,
          ‖fderiv ℝ F xStar (x (k + 1) - xStar)‖ ≤
            t * ‖fderiv ℝ F xStar (x k - xStar)‖ := by
  constructor
  · intro h
    exact ⟨h.tendsto, h.linearRate⟩
  · rintro ⟨htendsto, hlinearRate⟩
    exact ⟨htendsto, hlinearRate⟩

/- The supporting owners `IsRegularZero`, `IsInexactNewtonSequence`, and
`InexactNewtonLinearConvergence` are coordinate-free, but the labeled source theorem itself
remains in the textbook setting `F : ℝⁿ → ℝⁿ`. -/
section Euclidean

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- Helper for Chapter03 Theorem 3.6.2: a regular zero gives a `C¹` germ at the root. -/
lemma contDiffAt_of_regular_zero
    (F : Point → Point) (xStar : Point)
    (h_regular : IsRegularZero F xStar) :
    ContDiffAt ℝ 1 F xStar := by
  -- The neighborhood `C¹` witness in `IsRegularZero` immediately yields the pointwise `C¹` fact.
  rcases h_regular with ⟨_, ⟨s, hs_nhds, hs_contDiff⟩, _⟩
  exact hs_contDiff.contDiffAt hs_nhds

/-- Helper for Chapter03 Theorem 3.6.2: the source norm `y ↦ ‖fderiv ℝ F xStar y‖` is equivalent
to the ambient Euclidean norm at a regular zero. -/
lemma source_norm_equiv_of_regular_zero
    (F : Point → Point) (xStar : Point)
    (h_regular : IsRegularZero F xStar) :
    ∀ y : Point,
      (1 / max ‖fderiv ℝ F xStar‖ ‖(fderiv ℝ F xStar).inverse‖) * ‖y‖ ≤
        ‖fderiv ℝ F xStar y‖ ∧
      ‖fderiv ℝ F xStar y‖ ≤
        max ‖fderiv ℝ F xStar‖ ‖(fderiv ℝ F xStar).inverse‖ * ‖y‖ := by
  let A := fderiv ℝ F xStar
  let μ : ℝ := max ‖A‖ ‖A.inverse‖
  have hAinv : A.IsInvertible := h_regular.2.2
  intro y
  by_cases hμ : μ = 0
  · -- In the degenerate `μ = 0` case, both `A` and `A.inverse` have zero norm, so both bounds
    -- collapse to the trivial zero inequality.
    have hA_norm : ‖A‖ = 0 := by
      have hA_le : ‖A‖ ≤ μ := le_max_left ‖A‖ ‖A.inverse‖
      rw [hμ] at hA_le
      exact le_antisymm hA_le (norm_nonneg _)
    have hAinv_norm : ‖A.inverse‖ = 0 := by
      have hAinv_le : ‖A.inverse‖ ≤ μ := le_max_right ‖A‖ ‖A.inverse‖
      rw [hμ] at hAinv_le
      exact le_antisymm hAinv_le (norm_nonneg _)
    have hA_zero : A = 0 := norm_eq_zero.mp hA_norm
    constructor
    · simp [A, hA_zero]
    · simp [A, hA_zero]
  · -- For `μ > 0`, the upper bound comes from the operator norm of `A`, and the lower bound
    -- comes from applying the operator-norm bound to `A.inverse` and rewriting by invertibility.
    have hμ_nonneg : 0 ≤ μ := by
      exact le_trans (norm_nonneg A) (le_max_left ‖A‖ ‖A.inverse‖)
    have hμ_pos : 0 < μ := lt_of_le_of_ne hμ_nonneg (Ne.symm hμ)
    have h_upper :
        ‖A y‖ ≤ μ * ‖y‖ := by
      calc
        ‖A y‖ ≤ ‖A‖ * ‖y‖ := A.le_opNorm y
        _ ≤ μ * ‖y‖ := by
          gcongr
          exact le_max_left ‖A‖ ‖A.inverse‖
    have h_inverse_bound :
        ‖y‖ ≤ μ * ‖A y‖ := by
      calc
        ‖y‖ = ‖A.inverse (A y)‖ := by rw [hAinv.inverse_apply_self]
        _ ≤ ‖A.inverse‖ * ‖A y‖ := A.inverse.le_opNorm (A y)
        _ ≤ μ * ‖A y‖ := by
          gcongr
          exact le_max_right ‖A‖ ‖A.inverse‖
    have h_lower :
        (1 / μ) * ‖y‖ ≤ ‖A y‖ := by
      rw [one_div, mul_comm, ← div_eq_mul_inv]
      exact (div_le_iff₀ hμ_pos).2 (by simpa [mul_comm] using h_inverse_bound)
    simpa [A, μ] using And.intro h_lower h_upper

/-- Helper for Chapter03 Theorem 3.6.2: the ambient Euclidean norm is bounded by the source
norm multiplied by `μ = max ‖F'(xStar)‖ ‖F'(xStar)⁻¹‖`. -/
lemma ambient_norm_le_source_norm_of_regular_zero
    (F : Point → Point) (xStar : Point)
    (h_regular : IsRegularZero F xStar) :
    ∀ y : Point,
      ‖y‖ ≤
        max ‖fderiv ℝ F xStar‖ ‖(fderiv ℝ F xStar).inverse‖ *
          ‖fderiv ℝ F xStar y‖ := by
  let A := fderiv ℝ F xStar
  let μ : ℝ := max ‖A‖ ‖A.inverse‖
  have hAinv : A.IsInvertible := h_regular.2.2
  intro y
  by_cases hμ : μ = 0
  · -- If `μ = 0`, then `A = 0`; invertibility forces the space to be trivial, so the estimate
    -- reduces to `0 ≤ 0`.
    have hA_norm : ‖A‖ = 0 := by
      have hA_le : ‖A‖ ≤ μ := le_max_left ‖A‖ ‖A.inverse‖
      rw [hμ] at hA_le
      exact le_antisymm hA_le (norm_nonneg _)
    have hA_zero : A = 0 := norm_eq_zero.mp hA_norm
    have hy_zero : y = 0 := by
      calc
        y = A.inverse (A y) := by rw [hAinv.inverse_apply_self]
        _ = 0 := by simp [hA_zero]
    simp [A, μ, hμ, hy_zero]
  · -- Otherwise, multiply the lower source-norm estimate by the positive scalar `μ`.
    have hμ_nonneg : 0 ≤ μ := by
      exact le_trans (norm_nonneg A) (le_max_left ‖A‖ ‖A.inverse‖)
    have hμ_pos : 0 < μ := lt_of_le_of_ne hμ_nonneg (Ne.symm hμ)
    have hlower := (source_norm_equiv_of_regular_zero F xStar h_regular y).1
    have hmul :
        μ * ((1 / μ) * ‖y‖) ≤ μ * ‖A y‖ :=
      mul_le_mul_of_nonneg_left hlower hμ_nonneg
    calc
      ‖y‖ = μ * ((1 / μ) * ‖y‖) := by
        field_simp [hμ]
      _ ≤ μ * ‖A y‖ := hmul

/-- Helper for Chapter03 Theorem 3.6.2: one small ball around a regular zero controls nearby
invertibility, derivative perturbation, inverse-derivative perturbation, and the first-order
remainder estimate used in `(3.6.13)`-`(3.6.15)`. -/
lemma regular_zero_local_gamma_estimates
    (F : Point → Point) (xStar : Point) (γ : ℝ)
    (h_regular : IsRegularZero F xStar)
    (hγ : 0 < γ) :
    ∃ δ > 0, ∀ {y : Point}, ‖y - xStar‖ < δ →
      (fderiv ℝ F y).IsInvertible ∧
      ‖fderiv ℝ F y - fderiv ℝ F xStar‖ ≤ γ ∧
      ‖(fderiv ℝ F y).inverse - (fderiv ℝ F xStar).inverse‖ ≤ γ ∧
      ‖F y - F xStar - fderiv ℝ F xStar (y - xStar)‖ ≤ γ * ‖y - xStar‖ := by
  let A := fderiv ℝ F xStar
  have hAinv : A.IsInvertible := h_regular.2.2
  have hcontDiffAt : ContDiffAt ℝ 1 F xStar := contDiffAt_of_regular_zero F xStar h_regular
  rcases exists_isInvertible_fderiv_ball F xStar hcontDiffAt hAinv with
    ⟨δinv, hδinv, hinv⟩
  have hderivCont : ContinuousAt (fderiv ℝ F) xStar :=
    hcontDiffAt.continuousAt_fderiv one_ne_zero
  have hderivSet :
      {y : Point | ‖fderiv ℝ F y - A‖ < γ} ∈ nhds xStar := by
    simpa [Set.preimage, A, Metric.mem_ball, dist_eq_norm] using
      (hderivCont (Metric.ball_mem_nhds A hγ) :
        fderiv ℝ F ⁻¹' Metric.ball A γ ∈ nhds xStar)
  have hderivEvent :
      ∀ᶠ y in nhds xStar, ‖fderiv ℝ F y - A‖ < γ := by
    exact hderivSet
  rcases Metric.eventually_nhds_iff_ball.mp hderivEvent with ⟨δderiv, hδderiv, hderiv⟩
  have hinverseCont :
      ContinuousAt (fun y : Point ↦ (fderiv ℝ F y).inverse) xStar :=
    continuousAt_inverse_fderiv F xStar hcontDiffAt hAinv
  have hinverseSet :
      {y : Point | ‖(fderiv ℝ F y).inverse - A.inverse‖ < γ} ∈ nhds xStar := by
    simpa [Set.preimage, A, Metric.mem_ball, dist_eq_norm] using
      (hinverseCont (Metric.ball_mem_nhds A.inverse hγ) :
        (fun y : Point ↦ (fderiv ℝ F y).inverse) ⁻¹' Metric.ball A.inverse γ ∈ nhds xStar)
  have hinverseEvent :
      ∀ᶠ y in nhds xStar, ‖(fderiv ℝ F y).inverse - A.inverse‖ < γ := by
    exact hinverseSet
  rcases Metric.eventually_nhds_iff_ball.mp hinverseEvent with ⟨δinverse, hδinverse, hinverse⟩
  have hremainderEvent :
      ∀ᶠ y in nhds xStar,
        ‖F y - F xStar - A (y - xStar)‖ ≤ γ * ‖y - xStar‖ := by
    simpa [A] using
      hcontDiffAt.differentiableAt_one.hasFDerivAt.isLittleO.bound hγ
  rcases Metric.eventually_nhds_iff_ball.mp hremainderEvent with
    ⟨δremainder, hδremainder, hremainder⟩
  refine
    ⟨min δinv (min δderiv (min δinverse δremainder)),
      lt_min hδinv (lt_min hδderiv (lt_min hδinverse hδremainder)), ?_⟩
  intro y hy
  have hyinv : ‖y - xStar‖ < δinv := lt_of_lt_of_le hy (min_le_left _ _)
  have hyrest : ‖y - xStar‖ < min δderiv (min δinverse δremainder) :=
    lt_of_lt_of_le hy (min_le_right _ _)
  have hyderiv : ‖y - xStar‖ < δderiv := lt_of_lt_of_le hyrest (min_le_left _ _)
  have hyrest' : ‖y - xStar‖ < min δinverse δremainder :=
    lt_of_lt_of_le hyrest (min_le_right _ _)
  have hyinverse : ‖y - xStar‖ < δinverse := lt_of_lt_of_le hyrest' (min_le_left _ _)
  have hyremainder : ‖y - xStar‖ < δremainder := lt_of_lt_of_le hyrest' (min_le_right _ _)
  have hy_ball_deriv : y ∈ Metric.ball xStar δderiv := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, norm_sub_rev] using hyderiv
  have hy_ball_inverse : y ∈ Metric.ball xStar δinverse := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, norm_sub_rev] using hyinverse
  have hy_ball_remainder : y ∈ Metric.ball xStar δremainder := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, norm_sub_rev] using hyremainder
  exact ⟨hinv hyinv, le_of_lt (hderiv y hy_ball_deriv), le_of_lt (hinverse y hy_ball_inverse),
    hremainder y hy_ball_remainder⟩

/-- Helper for Chapter03 Theorem 3.6.2: the remainder estimate yields the source-side residual
bound `(3.6.18)`. -/
lemma source_residual_bound
    (F : Point → Point) (xStar y : Point)
    (h_root : F xStar = 0)
    (h_remainder :
      ‖F y - F xStar - fderiv ℝ F xStar (y - xStar)‖ ≤
        γ * ‖y - xStar‖) :
    ‖F y‖ ≤ ‖fderiv ℝ F xStar (y - xStar)‖ + γ * ‖y - xStar‖ := by
  -- Rewrite `F y` as the linear part plus the first-order remainder and apply the triangle
  -- inequality.
  calc
    ‖F y‖ =
        ‖(F y - F xStar - fderiv ℝ F xStar (y - xStar)) +
            fderiv ℝ F xStar (y - xStar)‖ := by
          simp [h_root, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ ≤ ‖F y - F xStar - fderiv ℝ F xStar (y - xStar)‖ +
          ‖fderiv ℝ F xStar (y - xStar)‖ := norm_add_le _ _
    _ ≤ γ * ‖y - xStar‖ + ‖fderiv ℝ F xStar (y - xStar)‖ := by
      gcongr
    _ = ‖fderiv ℝ F xStar (y - xStar)‖ + γ * ‖y - xStar‖ := by ring

/-- Helper for Chapter03 Theorem 3.6.2: `(3.6.16)` is first an exact algebraic identity for the
Newton error before any norm estimates are applied. -/
lemma inexact_newton_step_bracket_identity
    (F : Point → Point) (xStar : Point)
    (x s r : ℕ → Point) (ηSeq : ℕ → ℝ) (k : ℕ)
    (h_root : F xStar = 0)
    (h_inexact : IsInexactNewtonSequence F x s r ηSeq) :
    fderiv ℝ F (x k) (x (k + 1) - xStar) =
      r k + (fderiv ℝ F (x k) - fderiv ℝ F xStar) (x k - xStar) -
        (F (x k) - F xStar - fderiv ℝ F xStar (x k - xStar)) := by
  let A := fderiv ℝ F xStar
  let B := fderiv ℝ F (x k)
  let e : Point := x k - xStar
  have hupdate := h_inexact.update k
  have hlin := h_inexact.linearSystem k
  -- Route correction: keep `(3.6.16)` as a pure rewrite so the later norm proof only sees the
  -- textbook bracket and a separate prefactor bound.
  calc
    B (x (k + 1) - xStar) = B (e + s k) := by
      congr 1
      dsimp [e]
      rw [hupdate]
      abel
    _ = B e + B (s k) := by
      rw [B.map_add]
    _ = B e + (-F (x k) + r k) := by
      rw [hlin]
    _ = r k + B e - F (x k) := by
      abel
    _ = r k + (B - A) e - (F (x k) - F xStar - A e) := by
      dsimp [A, B, e]
      simp [h_root]
      abel

/-- Helper for Chapter03 Theorem 3.6.2: if the inverse derivative at `x k` is `γ`-close to the
inverse derivative at `xStar`, then the prefactor `A ∘ B⁻¹` in `(3.6.16)` is bounded by
`1 + μ γ` on each vector. -/
lemma source_inverse_prefactor_bound
    (A B : Point →L[ℝ] Point) (μ γ : ℝ)
    (hAinv : A.IsInvertible)
    (hμ : μ = max ‖A‖ ‖A.inverse‖)
    (hγ_nonneg : 0 ≤ γ)
    (hBclose : ‖B.inverse - A.inverse‖ ≤ γ) :
    ∀ z : Point, ‖A (B.inverse z)‖ ≤ (1 + μ * γ) * ‖z‖ := by
  intro z
  have hAterm :
      ‖A ((B.inverse - A.inverse) z)‖ ≤
        (‖A‖ * ‖B.inverse - A.inverse‖) * ‖z‖ := by
    -- Bound the perturbation term by the operator norms of `A` and `B.inverse - A.inverse`.
    calc
      ‖A ((B.inverse - A.inverse) z)‖ ≤ ‖A‖ * ‖(B.inverse - A.inverse) z‖ := A.le_opNorm _
      _ ≤ ‖A‖ * (‖B.inverse - A.inverse‖ * ‖z‖) := by
        gcongr
        exact (B.inverse - A.inverse).le_opNorm z
      _ = (‖A‖ * ‖B.inverse - A.inverse‖) * ‖z‖ := by
        ring
  -- Split `A (B⁻¹ z)` into the exact identity part `z` and the inverse perturbation term.
  calc
    ‖A (B.inverse z)‖ = ‖z + A ((B.inverse - A.inverse) z)‖ := by
      congr 1
      calc
        A (B.inverse z) = A (A.inverse z + (B.inverse - A.inverse) z) := by
          congr 1
          simp [sub_eq_add_neg]
        _ = A (A.inverse z) + A ((B.inverse - A.inverse) z) := by
          rw [A.map_add]
        _ = z + A ((B.inverse - A.inverse) z) := by
          rw [hAinv.self_apply_inverse]
    _ ≤ ‖z‖ + ‖A ((B.inverse - A.inverse) z)‖ := norm_add_le _ _
    _ ≤ ‖z‖ + (‖A‖ * ‖B.inverse - A.inverse‖) * ‖z‖ := by
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hAterm ‖z‖
    _ ≤ ‖z‖ + (‖A‖ * γ) * ‖z‖ := by
      gcongr
    _ ≤ ‖z‖ + (μ * γ) * ‖z‖ := by
      gcongr
      rw [hμ]
      exact le_max_left ‖A‖ ‖A.inverse‖
    _ = (1 + μ * γ) * ‖z‖ := by
      ring

/-- Helper for Chapter03 Theorem 3.6.2: the Newton update satisfies the textbook source-norm
one-step estimate once the local `(3.6.13)`-`(3.6.15)` estimates hold at the current iterate. -/
lemma inexact_newton_source_norm_step_estimate
    (F : Point → Point) (xStar : Point) (η γ : ℝ)
    (x s r : ℕ → Point) (ηSeq : ℕ → ℝ) (k : ℕ)
    (h_regular : IsRegularZero F xStar)
    (hη_nonneg : 0 ≤ η)
    (hγ_nonneg : 0 ≤ γ)
    (h_inexact : IsInexactNewtonSequence F x s r ηSeq)
    (hηk : ηSeq k ≤ η)
    (h_local :
      (fderiv ℝ F (x k)).IsInvertible ∧
      ‖fderiv ℝ F (x k) - fderiv ℝ F xStar‖ ≤ γ ∧
      ‖(fderiv ℝ F (x k)).inverse - (fderiv ℝ F xStar).inverse‖ ≤ γ ∧
      ‖F (x k) - F xStar - fderiv ℝ F xStar (x k - xStar)‖ ≤ γ * ‖x k - xStar‖)
    (hambient :
      ‖x k - xStar‖ ≤
        max ‖fderiv ℝ F xStar‖ ‖(fderiv ℝ F xStar).inverse‖ *
          ‖fderiv ℝ F xStar (x k - xStar)‖) :
    ‖fderiv ℝ F xStar (x (k + 1) - xStar)‖ ≤
      (1 + max ‖fderiv ℝ F xStar‖ ‖(fderiv ℝ F xStar).inverse‖ * γ) *
        (η * (1 + max ‖fderiv ℝ F xStar‖ ‖(fderiv ℝ F xStar).inverse‖ * γ) +
          2 * max ‖fderiv ℝ F xStar‖ ‖(fderiv ℝ F xStar).inverse‖ * γ) *
        ‖fderiv ℝ F xStar (x k - xStar)‖ := by
  let A := fderiv ℝ F xStar
  let B := fderiv ℝ F (x k)
  let μ : ℝ := max ‖A‖ ‖A.inverse‖
  let e : Point := x k - xStar
  let z : Point := r k + (B - A) e - (F (x k) - F xStar - A e)
  have hμ_nonneg : 0 ≤ μ := by
    exact le_trans (norm_nonneg A) (le_max_left ‖A‖ ‖A.inverse‖)
  have hAinv : A.IsInvertible := h_regular.2.2
  have hBinv : B.IsInvertible := h_local.1
  have h_root : F xStar = 0 := h_regular.1
  have hstep :
      x (k + 1) - xStar = B.inverse z := by
    -- Rewrite the next Newton error by applying the inverse of the current derivative to the
    -- bracket from `(3.6.16)`.
    have hbracket : B (x (k + 1) - xStar) = z := by
      simpa [A, B, e, z] using
        inexact_newton_step_bracket_identity F xStar x s r ηSeq k h_root h_inexact
    have hstep' : B.inverse (B (x (k + 1) - xStar)) = B.inverse z := congrArg B.inverse hbracket
    simpa [hBinv.inverse_apply_self] using hstep'
  have hresidual :
      ‖r k‖ ≤ η * ‖F (x k)‖ := by
    exact le_trans (h_inexact.residualBound k) <|
      mul_le_mul_of_nonneg_right hηk (norm_nonneg _)
  have hremainder :
      ‖F (x k) - F xStar - A e‖ ≤ γ * ‖e‖ := by
    simpa [A, e] using h_local.2.2.2
  have hderiv_term :
      ‖(B - A) e‖ ≤ γ * ‖e‖ := by
    calc
      ‖(B - A) e‖ ≤ ‖B - A‖ * ‖e‖ := (B - A).le_opNorm e
      _ ≤ γ * ‖e‖ := by
        gcongr
        exact h_local.2.1
  have hsource_residual :
      ‖F (x k)‖ ≤ ‖A e‖ + γ * ‖e‖ := by
    simpa [A, e] using source_residual_bound F xStar (x k) h_root hremainder
  have hz_triangle :
      ‖z‖ ≤ ‖r k‖ + ‖(B - A) e‖ + ‖F (x k) - F xStar - A e‖ := by
    have hz₁ :
        ‖z‖ ≤ ‖r k + (B - A) e‖ + ‖F (x k) - F xStar - A e‖ := by
      simpa [z] using norm_sub_le (r k + (B - A) e) (F (x k) - F xStar - A e)
    have hz₂ :
        ‖r k + (B - A) e‖ ≤ ‖r k‖ + ‖(B - A) e‖ := norm_add_le _ _
    linarith
  have hz_raw :
      ‖z‖ ≤ η * (‖A e‖ + γ * ‖e‖) + γ * ‖e‖ + γ * ‖e‖ := by
    have hz₃ : ‖z‖ ≤ η * ‖F (x k)‖ + γ * ‖e‖ + γ * ‖e‖ := by
      nlinarith [hz_triangle, hresidual, hderiv_term, hremainder]
    nlinarith [hz₃, hsource_residual]
  have hγambient :
      γ * ‖e‖ ≤ γ * (μ * ‖A e‖) :=
    mul_le_mul_of_nonneg_left hambient hγ_nonneg
  have hηpart :
      η * (‖A e‖ + γ * ‖e‖) ≤ η * (‖A e‖ + γ * (μ * ‖A e‖)) :=
    mul_le_mul_of_nonneg_left
      (by simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hγambient ‖A e‖)
      hη_nonneg
  have hz_bound :
      ‖z‖ ≤ (η * (1 + μ * γ) + 2 * μ * γ) * ‖A e‖ := by
    have htail :
        γ * ‖e‖ + γ * ‖e‖ ≤ γ * (μ * ‖A e‖) + γ * (μ * ‖A e‖) := by
      nlinarith [hγambient]
    calc
      ‖z‖ ≤ η * (‖A e‖ + γ * ‖e‖) + γ * ‖e‖ + γ * ‖e‖ := hz_raw
      _ ≤ η * (‖A e‖ + γ * (μ * ‖A e‖)) + γ * (μ * ‖A e‖) + γ * (μ * ‖A e‖) := by
        nlinarith [hηpart, htail]
      _ = (η * (1 + μ * γ) + 2 * μ * γ) * ‖A e‖ := by
        ring
  have hprefactor :
      ‖A (B.inverse z)‖ ≤ (1 + μ * γ) * ‖z‖ :=
    source_inverse_prefactor_bound A B μ γ hAinv rfl hγ_nonneg h_local.2.2.1 z
  have hpref_nonneg : 0 ≤ 1 + μ * γ := by
    nlinarith
  -- Apply the bracket rewrite, then bound the prefactor and the bracket separately.
  calc
    ‖A (x (k + 1) - xStar)‖ = ‖A (B.inverse z)‖ := by
      rw [hstep]
    _ ≤ (1 + μ * γ) * ‖z‖ := hprefactor
    _ ≤ (1 + μ * γ) * ((η * (1 + μ * γ) + 2 * μ * γ) * ‖A e‖) := by
      exact mul_le_mul_of_nonneg_left hz_bound hpref_nonneg
    _ = (1 + μ * γ) * (η * (1 + μ * γ) + 2 * μ * γ) * ‖A e‖ := by
      ring
    _ = (1 + max ‖fderiv ℝ F xStar‖ ‖(fderiv ℝ F xStar).inverse‖ * γ) *
          (η * (1 + max ‖fderiv ℝ F xStar‖ ‖(fderiv ℝ F xStar).inverse‖ * γ) +
            2 * max ‖fderiv ℝ F xStar‖ ‖(fderiv ℝ F xStar).inverse‖ * γ) *
          ‖fderiv ℝ F xStar (x k - xStar)‖ := by
      simp [A, μ, e]

/-- Helper for Chapter03 Theorem 3.6.2: because the textbook coefficient tends to `η` at
`γ = 0`, one can choose a positive `γ` so that the one-step coefficient is at most `t`. -/
lemma exists_gamma_for_source_contraction
    (μ η t : ℝ)
    (hμ_nonneg : 0 ≤ μ)
    (hη_nonneg : 0 ≤ η)
    (hη_lt_t : η < t) :
    ∃ γ > 0, (1 + μ * γ) * (η * (1 + μ * γ) + 2 * μ * γ) ≤ t := by
  by_cases hμ : μ = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    simpa [hμ] using hη_lt_t.le
  · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ_nonneg (Ne.symm hμ)
    let α : ℝ := min 1 ((t - η) / (3 * η + 4))
    have hden_pos : 0 < 3 * η + 4 := by
      nlinarith
    have hratio_pos : 0 < (t - η) / (3 * η + 4) := by
      exact div_pos (sub_pos.mpr hη_lt_t) hden_pos
    have hα_pos : 0 < α := by
      dsimp [α]
      exact lt_min zero_lt_one hratio_pos
    have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
    have hα_le_one : α ≤ 1 := by
      dsimp [α]
      exact min_le_left _ _
    have hα_le_ratio : α ≤ (t - η) / (3 * η + 4) := by
      dsimp [α]
      exact min_le_right _ _
    have hαsq_le : α ^ 2 ≤ α := by
      nlinarith
    have hcoeff :
        (1 + α) * (η * (1 + α) + 2 * α) ≤ η + α * (3 * η + 4) := by
      calc
        (1 + α) * (η * (1 + α) + 2 * α)
            = η + 2 * η * α + η * α ^ 2 + 2 * α + 2 * α ^ 2 := by ring
        _ ≤ η + 2 * η * α + η * α + 2 * α + 2 * α := by
          gcongr
        _ = η + α * (3 * η + 4) := by
          ring
    have hmul : α * (3 * η + 4) ≤ t - η := by
      exact (le_div_iff₀ hden_pos).mp hα_le_ratio
    have hfinal : η + α * (3 * η + 4) ≤ t := by
      nlinarith
    let γ : ℝ := α / μ
    have hγ_pos : 0 < γ := by
      dsimp [γ]
      exact div_pos hα_pos hμ_pos
    have hμγ : μ * γ = α := by
      dsimp [γ]
      field_simp [hμ_pos.ne']
    have htwo : 2 * μ * γ = 2 * α := by
      calc
        2 * μ * γ = 2 * (μ * γ) := by ring
        _ = 2 * α := by rw [hμγ]
    refine ⟨γ, hγ_pos, ?_⟩
    calc
      (1 + μ * γ) * (η * (1 + μ * γ) + 2 * μ * γ)
          = (1 + α) * (η * (1 + α) + 2 * μ * γ) := by rw [hμγ]
      _ = (1 + α) * (η * (1 + α) + 2 * α) := by rw [htwo]
      _ ≤ η + α * (3 * η + 4) := hcoeff
      _ ≤ t := hfinal

/-- Helper for Chapter03 Theorem 3.6.2: geometric contraction in the source norm implies
convergence to `xStar` by applying the inverse derivative at the root. -/
lemma source_norm_contraction_tendsto
    (F : Point → Point) (xStar : Point) (t : ℝ) (x : ℕ → Point)
    (hAinv : (fderiv ℝ F xStar).IsInvertible)
    (h0t : 0 ≤ t) (ht : t < 1)
    (hlinear :
      ∀ k : ℕ,
        ‖fderiv ℝ F xStar (x (k + 1) - xStar)‖ ≤
          t * ‖fderiv ℝ F xStar (x k - xStar)‖) :
    Tendsto x atTop (nhds xStar) := by
  let A := fderiv ℝ F xStar
  have hpow :
      ∀ k : ℕ, ‖A (x k - xStar)‖ ≤ t ^ k * ‖A (x 0 - xStar)‖ := by
    intro k
    induction k with
    | zero =>
        simp [A]
    | succ k hk =>
        -- Iterate the one-step contraction to obtain the geometric source-norm bound.
        calc
          ‖A (x (k + 1) - xStar)‖ ≤ t * ‖A (x k - xStar)‖ := hlinear k
          _ ≤ t * (t ^ k * ‖A (x 0 - xStar)‖) := by
            exact mul_le_mul_of_nonneg_left hk h0t
          _ = t ^ (k + 1) * ‖A (x 0 - xStar)‖ := by
            rw [pow_succ']
            ring
  have hpow_tendsto :
      Tendsto (fun k : ℕ ↦ t ^ k * ‖A (x 0 - xStar)‖) atTop (nhds 0) := by
    simpa [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one h0t ht).mul_const ‖A (x 0 - xStar)‖
  have herror_tendsto :
      Tendsto (fun k : ℕ ↦ x k - xStar) atTop (nhds 0) := by
    refine squeeze_zero_norm (a := fun k : ℕ ↦ ‖A.inverse‖ * (t ^ k * ‖A (x 0 - xStar)‖)) ?_ ?_
    · intro k
      -- Convert the source-norm decay to ambient decay through the inverse derivative.
      calc
        ‖x k - xStar‖ = ‖A.inverse (A (x k - xStar))‖ := by
          rw [hAinv.inverse_apply_self]
        _ ≤ ‖A.inverse‖ * ‖A (x k - xStar)‖ := A.inverse.le_opNorm _
        _ ≤ ‖A.inverse‖ * (t ^ k * ‖A (x 0 - xStar)‖) := by
          gcongr
          exact hpow k
    · simpa [zero_mul] using hpow_tendsto.const_mul ‖A.inverse‖
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using herror_tendsto.const_add xStar

/-- Chapter03 Theorem 3.6.2: if `xStar` is a regular zero of `F : ℝⁿ → ℝⁿ` in the sense of
`(A1)`-`(A3)`, and the forcing sequence `ηSeq` of an inexact Newton sequence `x, s, r, ηSeq`
satisfies `ηSeq k ≤ η < t < 1`, then for some `ε > 0`, every initial iterate with
`‖x 0 - xStar‖ ≤ ε` generates a sequence converging to `xStar`, and the convergence is linear
in the source norm `y ↦ ‖fderiv ℝ F xStar y‖`. -/
theorem inexactNewton_converges_linearly
    (F : Point → Point) (xStar : Point) (η t : ℝ)
    (h_regular : IsRegularZero F xStar)
    (hη_nonneg : 0 ≤ η)
    (hη_lt_t : η < t)
    (ht_lt_one : t < 1) :
    ∃ ε > 0, ∀ x s r : ℕ → Point, ∀ ηSeq : ℕ → ℝ,
      ‖x 0 - xStar‖ ≤ ε →
      IsInexactNewtonSequence F x s r ηSeq →
      (∀ k : ℕ, ηSeq k ≤ η) →
      InexactNewtonLinearConvergence F xStar t x := by
  let A := fderiv ℝ F xStar
  let μ : ℝ := max ‖A‖ ‖A.inverse‖
  have hAinv : A.IsInvertible := h_regular.2.2
  have hcontDiffAt : ContDiffAt ℝ 1 F xStar := contDiffAt_of_regular_zero F xStar h_regular
  have hsource :
      ∀ y : Point, (1 / μ) * ‖y‖ ≤ ‖A y‖ ∧ ‖A y‖ ≤ μ * ‖y‖ := by
    simpa [A, μ] using source_norm_equiv_of_regular_zero F xStar h_regular
  have hambient :
      ∀ y : Point, ‖y‖ ≤ μ * ‖A y‖ := by
    simpa [A, μ] using ambient_norm_le_source_norm_of_regular_zero F xStar h_regular
  have hμ_nonneg : 0 ≤ μ := by
    exact le_trans (norm_nonneg A) (le_max_left ‖A‖ ‖A.inverse‖)
  have ht_pos : 0 < t := lt_of_le_of_lt hη_nonneg hη_lt_t
  have h0t : 0 ≤ t := le_of_lt ht_pos
  -- Route correction: keep the book's source-norm induction. The proved local lemmas above
  -- already package `(3.6.13)`-`(3.6.18)`; the remaining work is to combine them with the
  -- one-step estimate, the scalar `γ` choice, and the geometric-decay closeout.
  rcases exists_gamma_for_source_contraction μ η t hμ_nonneg hη_nonneg hη_lt_t with
    ⟨γ, hγ_pos, hγcontract⟩
  rcases regular_zero_local_gamma_estimates F xStar γ h_regular hγ_pos with
    ⟨δ, hδ, hlocal⟩
  let ε : ℝ := min (δ / 2) (δ / (μ ^ 2 + 1))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    refine lt_min ?_ ?_
    · exact half_pos hδ
    · have hden_pos : 0 < μ ^ 2 + 1 := by
        nlinarith [sq_nonneg μ]
      exact div_pos hδ hden_pos
  refine ⟨ε, hε_pos, ?_⟩
  intro x s r ηSeq hx0 h_inexact hηSeq
  have hε_lt_δ : ε < δ := by
    have hhalf_lt : δ / 2 < δ := by
      nlinarith [hδ]
    exact lt_of_le_of_lt (min_le_left _ _) hhalf_lt
  have hε_le_source : ε ≤ δ / (μ ^ 2 + 1) := by
    dsimp [ε]
    exact min_le_right _ _
  have hx0_ball : ‖x 0 - xStar‖ < δ := lt_of_le_of_lt hx0 hε_lt_δ
  have hμsq_div_lt : μ ^ 2 * (δ / (μ ^ 2 + 1)) < δ := by
    have hden_pos : 0 < μ ^ 2 + 1 := by
      nlinarith [sq_nonneg μ]
    have hfrac_lt_one : μ ^ 2 / (μ ^ 2 + 1) < 1 := by
      exact (div_lt_iff₀ hden_pos).2 (by nlinarith)
    calc
      μ ^ 2 * (δ / (μ ^ 2 + 1)) = (μ ^ 2 / (μ ^ 2 + 1)) * δ := by
        ring
      _ < 1 * δ := by
        exact mul_lt_mul_of_pos_right hfrac_lt_one hδ
      _ = δ := by ring
  have hInvariant :
      ∀ k : ℕ,
        ‖A (x k - xStar)‖ ≤ t ^ k * ‖A (x 0 - xStar)‖ ∧
          ‖x k - xStar‖ < δ := by
    intro k
    induction k with
    | zero =>
        exact ⟨by simp [A], hx0_ball⟩
    | succ k hk =>
        rcases hk with ⟨hk_rate, hk_ball⟩
        have hlocalk := hlocal hk_ball
        have hkambient :
            ‖x k - xStar‖ ≤ μ * ‖A (x k - xStar)‖ := by
          simpa [A, μ] using hambient (x k - xStar)
        have hk_step :
            ‖A (x (k + 1) - xStar)‖ ≤
              (1 + μ * γ) * (η * (1 + μ * γ) + 2 * μ * γ) *
                ‖A (x k - xStar)‖ := by
          simpa [A, μ] using
            inexact_newton_source_norm_step_estimate F xStar η γ x s r ηSeq k h_regular
              hη_nonneg (le_of_lt hγ_pos) h_inexact (hηSeq k) hlocalk hkambient
        have hk_linear :
            ‖A (x (k + 1) - xStar)‖ ≤ t * ‖A (x k - xStar)‖ := by
          exact le_trans hk_step <|
            mul_le_mul_of_nonneg_right hγcontract (norm_nonneg _)
        have hk_rate_succ :
            ‖A (x (k + 1) - xStar)‖ ≤ t ^ (k + 1) * ‖A (x 0 - xStar)‖ := by
          calc
            ‖A (x (k + 1) - xStar)‖ ≤ t * ‖A (x k - xStar)‖ := hk_linear
            _ ≤ t * (t ^ k * ‖A (x 0 - xStar)‖) := by
              exact mul_le_mul_of_nonneg_left hk_rate h0t
            _ = t ^ (k + 1) * ‖A (x 0 - xStar)‖ := by
              rw [pow_succ']
              ring
        have hsource0 :
            ‖A (x 0 - xStar)‖ ≤ μ * ‖x 0 - xStar‖ := by
          simpa [A, μ] using (hsource (x 0 - xStar)).2
        have hk_ball_le :
            ‖x (k + 1) - xStar‖ ≤ μ ^ 2 * ‖x 0 - xStar‖ := by
          have hk_pow_le_one : t ^ (k + 1) ≤ 1 := pow_le_one₀ h0t ht_lt_one.le
          calc
            ‖x (k + 1) - xStar‖ ≤ μ * ‖A (x (k + 1) - xStar)‖ := by
              simpa [A, μ] using hambient (x (k + 1) - xStar)
            _ ≤ μ * (t ^ (k + 1) * ‖A (x 0 - xStar)‖) := by
              gcongr
            _ ≤ μ * ‖A (x 0 - xStar)‖ := by
              have htmp :
                  t ^ (k + 1) * ‖A (x 0 - xStar)‖ ≤ ‖A (x 0 - xStar)‖ := by
                exact mul_le_of_le_one_left (norm_nonneg _) hk_pow_le_one
              exact mul_le_mul_of_nonneg_left htmp hμ_nonneg
            _ ≤ μ * (μ * ‖x 0 - xStar‖) := by
              gcongr
            _ = μ ^ 2 * ‖x 0 - xStar‖ := by
              ring
        have hk_ball_eps :
            μ ^ 2 * ‖x 0 - xStar‖ ≤ μ ^ 2 * ε :=
          mul_le_mul_of_nonneg_left hx0 (sq_nonneg μ)
        have hk_ball_source :
            μ ^ 2 * ε ≤ μ ^ 2 * (δ / (μ ^ 2 + 1)) :=
          mul_le_mul_of_nonneg_left hε_le_source (sq_nonneg μ)
        have hk_ball_succ :
            ‖x (k + 1) - xStar‖ < δ := by
          exact lt_of_le_of_lt (le_trans hk_ball_le (le_trans hk_ball_eps hk_ball_source))
            hμsq_div_lt
        exact ⟨hk_rate_succ, hk_ball_succ⟩
  have hlinear :
      ∀ k : ℕ,
        ‖A (x (k + 1) - xStar)‖ ≤ t * ‖A (x k - xStar)‖ := by
    intro k
    have hk_ball := (hInvariant k).2
    have hkambient :
        ‖x k - xStar‖ ≤ μ * ‖A (x k - xStar)‖ := by
      simpa [A, μ] using hambient (x k - xStar)
    have hk_step :
        ‖A (x (k + 1) - xStar)‖ ≤
          (1 + μ * γ) * (η * (1 + μ * γ) + 2 * μ * γ) *
            ‖A (x k - xStar)‖ := by
      simpa [A, μ] using
        inexact_newton_source_norm_step_estimate F xStar η γ x s r ηSeq k h_regular
          hη_nonneg (le_of_lt hγ_pos) h_inexact (hηSeq k) (hlocal hk_ball) hkambient
    exact le_trans hk_step <|
      mul_le_mul_of_nonneg_right hγcontract (norm_nonneg _)
  refine ⟨source_norm_contraction_tendsto F xStar t x hAinv h0t ht_lt_one hlinear, ?_⟩
  intro k
  simpa [A] using hlinear k

end Euclidean

end InexactNewtonMethod
