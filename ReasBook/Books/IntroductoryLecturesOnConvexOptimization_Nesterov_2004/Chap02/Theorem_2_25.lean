/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_6_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SmoothConvex MinGradientNormAlongIterates

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Primary domain: smooth-convex gradient descent on real Hilbert spaces, with a finite-dimensional
Chapter 2 specialization.

Owner-style declarations sampled before refining this file:
* `gradientMethod` in `Algorithm_2_1`, the chapter recall of the canonical gradient-method
  trajectory;
* `minGradientNormAlongIterates` in `Definition_2_23`, the owner finite-window realization of the
  textbook quantity `g_{0,T}`;
* `minGradientNormAlongIterates_le_sqrt` in `Chap01/Theorem_1_6_8`, the owner Chapter 1 theorem
  for the same finite-window best-gradient quantity under a sufficient-decrease hypothesis;
* `gradient_step_value_descent_of_lipschitzGradient` in `Lemma_2_16`, the reciprocal-`L`
  one-step descent theorem on the weaker differentiable/Lipschitz-gradient owner layer.

Source/core/bridge triage:
* source-facing: Theorem 2.25's sharp reciprocal-`L` bound for the textbook quantity `g_{0,T}`;
* core/canonical: `ConvexOn ℝ Set.univ f`, the ambient-gradient owner
  `∀ x : E, HasGradientAt f (∇ f x) x`, `LipschitzWith L (∇ f)`,
  `IsMinOn f Set.univ xStar`, the trajectory `gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0`, and
  the finite-window minimum `minGradientNormAlongIterates`;
* bridge/view: the finite-dimensional Chapter 2 specialization
  `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`, whose projections `hf.hasGradientAt` and
  `hf.gradient_lipschitz` recover the intrinsic owner hypotheses; the textbook Euclidean theorem
  is the specialization `E = EuclideanSpace ℝ (Fin n)`.

Best owner abstraction:
* the intrinsic smooth-convex owner hypotheses `ConvexOn ℝ Set.univ f`, the actual ambient
  gradient witnesses `∀ x : E, HasGradientAt f (∇ f x) x`, and `LipschitzWith L (∇ f)`;
* the constant-step trajectory `gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0`;
* the finite-window minimum `minGradientNormAlongIterates f ... 0 T (Nat.zero_le T)`.

Primitive data:
* whole-space convexity of `f`;
* actual ambient-gradient existence at every point;
* the `L`-Lipschitz bound for `∇ f`;
* a minimizer `xStar` with `IsMinOn f Set.univ xStar`;
* the initial point `x0`.

Derived API:
* the intrinsic sharp `g_{0,T}` bound below;
* the finite-dimensional Chapter 2 specialization theorem;
* the direct Euclidean iterate-existence specialization in `Theorem_2_24`.

Accordingly, Theorem 2.25 is kept on the weaker intrinsic real-Hilbert-space owner layer
`ConvexOn + HasGradientAt + LipschitzWith`, while the Chapter 2 notation
`f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` remains only a thin finite-dimensional specialization bridge
rather than primitive public data. -/

namespace ConvexC1SeminormSmooth

variable {L : NNReal} {f : E → ℝ}

section

variable [CompleteSpace E]

/-- Helper for Theorem 2.25: a globally defined gradient field that is Lipschitz is continuous as
the Fréchet derivative, so the objective is `C¹`. -/
lemma contDiff_one_of_hasGradientAt_lipschitz
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    ContDiff ℝ 1 f := by
  -- Rewrite the derivative through the Riesz map and use continuity of the Lipschitz gradient.
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x ↦ (hgrad x).differentiableAt, ?_⟩
  have hEq : fderiv ℝ f = fun x ↦ InnerProductSpace.toDual ℝ E (∇ f x) := by
    funext x
    simpa using (hgrad x).hasFDerivAt.fderiv
  have hcont : Continuous (fun x ↦ InnerProductSpace.toDual ℝ E (∇ f x)) :=
    (InnerProductSpace.toDual ℝ E).continuous.comp hgrad_lipschitz.continuous
  simpa [hEq] using hcont

/-- Helper for Theorem 2.25: every reciprocal-`L` gradient step satisfies the `ω = 1 / 2`
descent inequality needed by the Chapter 1 `g_{0,T}` estimate. -/
lemma gradientMethod_sufficient_decrease_half
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (x0 : E)
    (hL : 0 < (L : ℝ)) :
    ∀ k : ℕ,
      (((1 / 2 : ℝ) / (L : ℝ)) *
          ‖∇ f ((gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0) k)‖ ^ (2 : ℕ)) ≤
        f ((gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0) k) -
          f ((gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0) (k + 1)) := by
  intro k
  have hdescent :
      f ((gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0) (k + 1)) ≤
        f ((gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0) k) -
          (1 / (2 * (L : ℝ))) *
            ‖∇ f ((gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0) k)‖ ^ (2 : ℕ) := by
    -- Apply the one-step smooth descent lemma at the current iterate.
    simpa [gradientMethod_succ] using
      gradient_step_value_descent_of_lipschitzGradient
        f hL
        (fun x ↦ (hgrad x).differentiableAt)
        (by simpa using hgrad_lipschitz)
        ((gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0) k)
  have hcoeff :
      (((1 / 2 : ℝ) / (L : ℝ)) *
          ‖∇ f ((gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0) k)‖ ^ (2 : ℕ)) =
        (1 / (2 * (L : ℝ))) *
          ‖∇ f ((gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0) k)‖ ^ (2 : ℕ) := by
    field_simp [ne_of_gt hL]
  rw [hcoeff]
  linarith

/-- Helper for Theorem 2.25: the initial objective gap is bounded by the smooth quadratic model
at a minimizer. -/
lemma initial_objective_gap_le_half_mul_sqdist_to_minimizer
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) :
    f x0 - f xStar ≤ ((L : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  have hfC1 : ContDiff ℝ 1 f :=
    contDiff_one_of_hasGradientAt_lipschitz hgrad hgrad_lipschitz
  have hstationary : HasGradientAt f 0 xStar := by
    exact isMinOn_hasGradientAt_zero_of_differentiableAt
      (hfC1.differentiable_one xStar) hxStar
  -- Apply the Taylor upper bound at the minimizer and remove the vanishing linear term.
  calc
    f x0 - f xStar
        ≤ firstOrderTaylorModelAt f xStar x0 +
            ((L : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) - f xStar := by
          have hupper :=
            taylor_upper_bound_of_contDiffOne_withLipschitzGradient
              hfC1 hgrad_lipschitz xStar x0
          linarith
    _ = ((L : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
          simp [hstationary.gradient]

/-- Helper for Theorem 2.25: restarting constant-step gradient descent from iterate `k` produces
the tail of the original trajectory. -/
lemma gradientMethod_restart_eq_tail
    (f : E → ℝ) (α : ℝ) (x0 : E) (k j : ℕ) :
    gradientMethod (fun _ ↦ α) f (gradientMethod (fun _ ↦ α) f x0 k) j =
      gradientMethod (fun _ ↦ α) f x0 (k + j) := by
  -- Rewrite both trajectories as iterates of the same autonomous gradient-step map.
  calc
    gradientMethod (fun _ ↦ α) f (gradientMethod (fun _ ↦ α) f x0 k) j =
        (fun x ↦ x - α • ∇ f x)^[j] (gradientMethod (fun _ ↦ α) f x0 k) := by
          simpa using
            gradientMethod_const_eq_iterate f α (gradientMethod (fun _ ↦ α) f x0 k) j
    _ = (fun x ↦ x - α • ∇ f x)^[j] ((fun x ↦ x - α • ∇ f x)^[k] x0) := by
          rw [gradientMethod_const_eq_iterate]
    _ = (fun x ↦ x - α • ∇ f x)^[k + j] x0 := by
          rw [← Function.iterate_add_apply, Nat.add_comm]
    _ = gradientMethod (fun _ ↦ α) f x0 (k + j) := by
          symm
          simpa using gradientMethod_const_eq_iterate f α x0 (k + j)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Helper for Theorem 2.25: a whole-space minimizer realizes the exact infimum of the objective
value set. -/
lemma objective_value_isGLB_of_isMinOn
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar) :
    IsGLB (Set.range f) (f xStar) := by
  -- Repackage whole-space minimality as the exact infimum of the range.
  refine ⟨?_, ?_⟩
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    exact (isMinOn_univ_iff.mp hxStar) z
  · intro b hb
    exact hb ⟨xStar, rfl⟩

/-- Helper for Theorem 2.25: the earlier Chapter 2 objective-gap theorem specializes at stepsize
`1 / L` to the bound `f(x_k) - f(x*) ≤ 2 L ‖x₀ - x*‖² / (k + 4)`. -/
lemma gradientMethod_objective_gap_le_two_mul_L_sqdist_div_add_four
    (hconv : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) (hL : 0 < (L : ℝ)) (k : ℕ) :
    f (gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0 k) - f xStar ≤
      (2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ) := by
  let traj : ℕ → E := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0
  let Δ0 : ℝ := f x0 - f xStar
  let R2 : ℝ := ‖x0 - xStar‖ ^ (2 : ℕ)
  by_cases hx0 : x0 = xStar
  · subst hx0
    have hgrad0 : ∇ f x0 = 0 := isMinOn_gradient_eq_zero hxStar
    have htraj : ∀ n : ℕ, gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0 n = x0 := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n hn =>
          rw [gradientMethod_succ, hn, hgrad0]
          simp
    -- Starting from a minimizer makes the entire trajectory stationary.
    have hgap_zero : f (traj k) - f x0 = 0 := by
      exact sub_eq_zero.mpr <| by simpa [traj] using congrArg f (htraj k)
    have hrhs_zero :
        (2 * (L : ℝ) * ‖x0 - x0‖ ^ (2 : ℕ)) / (k + 4 : ℝ) = 0 := by
      simp
    rw [hgap_zero, hrhs_zero]
  · have hfC1 : ContDiff ℝ 1 f :=
      contDiff_one_of_hasGradientAt_lipschitz hgrad hgrad_lipschitz
    have hΔ0_nonneg : 0 ≤ Δ0 := by
      dsimp [Δ0]
      exact sub_nonneg.mpr ((isMinOn_univ_iff.mp hxStar) x0)
    have hR2_pos : 0 < R2 := by
      have hsub_ne : x0 - xStar ≠ 0 := sub_ne_zero.mpr hx0
      have hnorm_pos : 0 < ‖x0 - xStar‖ := norm_pos_iff.mpr hsub_ne
      dsimp [R2]
      positivity
    let A : ℝ := ((L : ℝ) / 2) * R2
    let c : ℝ := (k : ℝ) / (L : ℝ)
    have hgap0_le :
        Δ0 ≤ A := by
      simpa [Δ0, R2, A, mul_assoc, mul_left_comm, mul_comm] using
        initial_objective_gap_le_half_mul_sqdist_to_minimizer
          hgrad hgrad_lipschitz xStar hxStar x0
    have hraw :=
      gradientMethod_objective_gap_le_explicit_rate
        hconv hfC1 hgrad_lipschitz xStar hxStar
        (1 / (L : ℝ)) (by positivity)
        (by
          have : (1 : ℝ) ≤ 2 := by norm_num
          exact (div_le_div_of_nonneg_right this hL.le))
        x0 k
    have hraw' :
        f (traj k) - f xStar ≤
          (2 * Δ0 * R2) / (2 * R2 + c * Δ0) := by
      -- Rewrite the theorem with the specialized stepsize `h = 1 / L`.
      have hone : 2 - (L : ℝ) * (1 / (L : ℝ)) = 1 := by
        field_simp [ne_of_gt hL]
        norm_num
      have hraw0 := hraw
      rw [hone, mul_one] at hraw0
      simpa [traj, Δ0, R2, c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
        add_assoc, add_left_comm, add_comm] using hraw0
    have hmono :
        (2 * Δ0 * R2) / (2 * R2 + c * Δ0) ≤
          (2 * A * R2) / (2 * R2 + c * A) := by
      have hden0_pos : 0 < 2 * R2 + c * Δ0 := by
        positivity
      have hdenA_pos : 0 < 2 * R2 + c * A := by
        positivity
      refine (div_le_div_iff₀ hden0_pos hdenA_pos).2 ?_
      have hgap0_le' : 2 * Δ0 ≤ (L : ℝ) * R2 := by
        dsimp [A] at hgap0_le
        nlinarith
      dsimp [A, c]
      ring_nf
      nlinarith [hgap0_le', hR2_pos.le, hL.le]
    have hA_eval :
        (2 * A * R2) / (2 * R2 + c * A) =
          (2 * (L : ℝ) * R2) / (k + 4 : ℝ) := by
      dsimp [A, c]
      field_simp [ne_of_gt hL, ne_of_gt hR2_pos]
      ring_nf
    calc
      f (traj k) - f xStar ≤ (2 * Δ0 * R2) / (2 * R2 + c * Δ0) := hraw'
      _ ≤ (2 * A * R2) / (2 * R2 + c * A) := hmono
      _ = (2 * (L : ℝ) * R2) / (k + 4 : ℝ) := hA_eval
      _ = (2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ) := by
            simp [R2]

/-- Helper for Theorem 2.25: every tail window `k, …, T` satisfies the explicit squared
`g_{k,T}` bound obtained by combining the Chapter 1 tail estimate with the stage-`k`
objective-gap decay. -/
lemma tail_window_min_gradient_sq_le_explicit_bound
    (hconv : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) (hL : 0 < (L : ℝ)) {k T : ℕ} (hkT : k ≤ T) :
    let traj := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0
    let tail := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k)
    g[f; tail; 0, T - k | Nat.zero_le (T - k)] ^ (2 : ℕ) ≤
      (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
  let traj : ℕ → E := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0
  let tail : ℕ → E := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k)
  have hglb : IsGLB (Set.range f) (f xStar) :=
    objective_value_isGLB_of_isMinOn (f := f) hxStar
  have hdesc :
      ∀ j : ℕ,
        (((1 / 2 : ℝ) / (L : ℝ)) * ‖∇ f (tail j)‖ ^ (2 : ℕ)) ≤
          f (tail j) - f (tail (j + 1)) :=
    gradientMethod_sufficient_decrease_half hgrad hgrad_lipschitz (traj k) hL
  have htail_nonneg :
      0 ≤ g[f; tail; 0, T - k | Nat.zero_le (T - k)] := by
    -- The tail-window minimum is attained by a norm value.
    rcases minGradientNormAlongIterates.exists_eq f tail (Nat.zero_le (T - k)) with
      ⟨j, -, -, hj⟩
    rw [hj]
    exact norm_nonneg _
  have hroot :=
    minGradientNormAlongIterates_le_sqrt
      (stepSize := fun _ ↦ 1 / (L : ℝ))
      (x0 := traj k) (f := f) (L := (L : ℝ)) (ω := (1 / 2 : ℝ))
      hglb hL (by norm_num) hdesc (T - k)
  have hgapk_nonneg : 0 ≤ f (traj k) - f xStar := by
    exact sub_nonneg.mpr ((isMinOn_univ_iff.mp hxStar) (traj k))
  have hsq_gap :
      g[f; tail; 0, T - k | Nat.zero_le (T - k)] ^ (2 : ℕ) ≤
        ((L : ℝ) * (f (traj k) - f xStar)) / (((1 / 2 : ℝ) * (T - k + 1 : ℝ))) := by
    have hroot' :
        g[f; tail; 0, T - k | Nat.zero_le (T - k)] ≤
          Real.sqrt
            (((L : ℝ) * (f (traj k) - f xStar)) /
              ((1 / 2 : ℝ) * (T - k + 1 : ℝ))) := by
      simpa [tail, Nat.cast_sub hkT] using hroot
    have hinside_nonneg :
        0 ≤ ((L : ℝ) * (f (traj k) - f xStar)) / (((1 / 2 : ℝ) * (T - k + 1 : ℝ))) := by
      have hkT' : (k : ℝ) ≤ T := by
        exact_mod_cast hkT
      have hden_nonneg : 0 ≤ ((1 / 2 : ℝ) * (T - k + 1 : ℝ)) := by
        nlinarith
      exact div_nonneg (mul_nonneg (by exact_mod_cast L.2) hgapk_nonneg) hden_nonneg
    exact (Real.le_sqrt htail_nonneg hinside_nonneg).1 hroot'
  have hgapk :
      f (traj k) - f xStar ≤
        (2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ) :=
    gradientMethod_objective_gap_le_two_mul_L_sqdist_div_add_four
      hconv hgrad hgrad_lipschitz xStar hxStar x0 hL k
  have hinside_le :
      ((L : ℝ) * (f (traj k) - f xStar)) / (((1 / 2 : ℝ) * (T - k + 1 : ℝ))) ≤
        (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
    -- Insert the stage-`k` gap estimate into the Chapter 1 square-root radicand.
    have hden_nonneg : 0 ≤ (T - k + 1 : ℝ) := by
      have hkT' : (k : ℝ) ≤ T := by
        exact_mod_cast hkT
      nlinarith
    calc
      ((L : ℝ) * (f (traj k) - f xStar)) / (((1 / 2 : ℝ) * (T - k + 1 : ℝ)))
          = (2 * (L : ℝ) * (f (traj k) - f xStar)) / (T - k + 1 : ℝ) := by
            field_simp
      _ ≤ (2 * (L : ℝ) *
            ((2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ))) /
            (T - k + 1 : ℝ) := by
            exact div_le_div_of_nonneg_right (by gcongr) hden_nonneg
      _ = (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
            field_simp
            ring_nf
  exact hsq_gap.trans hinside_le

/-- Helper for Theorem 2.25: the midpoint-like choice `k = (T - 3) / 2` makes the tail-window
product dominate a quarter of the target denominator `(T + 4) (T + 6)`. -/
lemma midpoint_window_product_ge_quarter_target
    {T : ℕ} (hT : 3 ≤ T) :
    let k := (T - 3) / 2
    ((T + 4 : ℝ) * (T + 6 : ℝ)) / 4 ≤ (k + 4 : ℝ) * (T - k + 1 : ℝ) := by
  let k : ℕ := (T - 3) / 2
  have hkT : k ≤ T := by
    dsimp [k]
    omega
  let r : ℕ := (T - 3) % 2
  have hr : r = 0 ∨ r = 1 := by
    have hr_lt : r < 2 := by
      dsimp [r]
      exact Nat.mod_lt _ (by decide)
    omega
  have hdecomp : T = 2 * k + r + 3 := by
    dsimp [k, r]
    have hmod := Nat.mod_add_div (T - 3) 2
    omega
  have hnat :
      (T + 4) * (T + 6) ≤ 4 * ((((T - 3) / 2 + 4) * (T - (T - 3) / 2 + 1)) : ℕ) := by
    -- The chosen index is close enough to the midpoint for the elementary quadratic bound.
    rcases hr with hr | hr
    · rw [hr] at hdecomp
      rw [hdecomp]
      have hkdiv0 : (2 * k + 0 + 3 - 3) / 2 = k := by
        omega
      have hsub0 : 2 * k + 0 + 3 - k = k + 3 := by
        omega
      rw [hkdiv0, hsub0]
      have hreal :
          ((2 * (k : ℝ) + 7) * (2 * (k : ℝ) + 9) ≤
            4 * (((k : ℝ) + 4) * ((k : ℝ) + 4))) := by
        nlinarith
      exact_mod_cast hreal
    · rw [hr] at hdecomp
      rw [hdecomp]
      have hkdiv : (2 * k + 1) / 2 = k := by
        omega
      have hkdiv' : (2 * k + 1 + 3 - 3) / 2 = k := by
        simpa using hkdiv
      have hsub1 : 2 * k + 1 + 3 - k = k + 4 := by
        omega
      rw [hkdiv', hsub1]
      have hreal :
          ((2 * (k : ℝ) + 8) * (2 * (k : ℝ) + 10) ≤
            4 * (((k : ℝ) + 4) * ((k : ℝ) + 5))) := by
        nlinarith
      exact_mod_cast hreal
  have hnat' :
      (T + 4) * (T + 6) ≤ 4 * ((k + 4) * (T - k + 1)) := by
    simpa [k] using hnat
  have hcast :
      ((T + 4 : ℝ) * (T + 6 : ℝ)) ≤
        4 * ((k + 4 : ℝ) * (((T - k + 1 : ℕ) : ℝ))) := by
    exact_mod_cast hnat'
  have hcast' :
      ((T + 4 : ℝ) * (T + 6 : ℝ)) ≤
        4 * ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
    simpa [Nat.cast_sub hkT] using hcast
  nlinarith [hcast']

/-- Theorem 2.25 on the intrinsic real-Hilbert-space owner layer: if `f` is convex on the whole
space, admits the ambient gradient `∇ f` everywhere, has `L`-Lipschitz gradient, and `xStar` is a
global minimizer, then the minimum gradient norm among the first `T + 1` iterates of gradient
descent with step `1 / L` is bounded by
`4 L ‖x₀ - x^*‖ / √((T + 4)(T + 6))` whenever `T ≥ 3`. The textbook `ℝⁿ` statement is recovered
by the finite-dimensional Chapter 2 specialization theorem below. -/
-- Proof sketch: use `gradient_step_value_descent_of_lipschitzGradient`, with differentiability
-- supplied by `fun x ↦ (hgrad x).differentiableAt`, to obtain the reciprocal-`L`
-- sufficient-decrease hypothesis for the owner trajectory. Apply the Chapter 1 owner estimate
-- `minGradientNormAlongIterates_le_sqrt` on a suitable tail window, and combine it with the
-- standard convex reciprocal-gap argument against the minimizer `xStar` to get the explicit
-- denominator `(T + 4) (T + 6)`. In the degenerate case `L = 0`, the Lipschitz-gradient
-- hypothesis and a global minimizer force `∇ f = 0`, so the same bound is immediate.
theorem gradientMethod_min_gradient_norm_le_explicit_sublinear_rate
    (hconv : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) {T : ℕ} (hT : 3 ≤ T) :
    g[f; gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0; 0, T | Nat.zero_le T] ≤
      (4 * (L : ℝ) * ‖x0 - xStar‖) / Real.sqrt ((T + 4 : ℝ) * (T + 6 : ℝ)) := by
  let traj := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0
  by_cases hL0 : (L : ℝ) = 0
  · have hgrad_zero_at_minimizer : ∇ f xStar = 0 := isMinOn_gradient_eq_zero hxStar
    have hgrad_zero : ∀ x : E, ∇ f x = 0 := by
      intro x
      have hdist := hgrad_lipschitz.dist_le_mul x xStar
      have hdist0 : dist (∇ f x) (∇ f xStar) = 0 := by
        apply le_antisymm
        · simpa [hL0] using hdist
        · exact dist_nonneg
      simpa [hgrad_zero_at_minimizer] using eq_of_dist_eq_zero hdist0
    have hwindow_zero : g[f; traj; 0, T | Nat.zero_le T] = 0 := by
      rcases minGradientNormAlongIterates.exists_eq f traj (Nat.zero_le T) with
        ⟨i, -, -, hi⟩
      rw [hi, hgrad_zero (traj i), norm_zero]
    -- In the degenerate `L = 0` case, the gradient field vanishes identically.
    rw [hwindow_zero]
    simp [hL0]
  · have hL : 0 < (L : ℝ) := by
      exact lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hL0)
    let k : ℕ := (T - 3) / 2
    have hkT : k ≤ T := by
      dsimp [k]
      omega
    have hwindow :
        g[f; gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k);
          0, T - k | Nat.zero_le (T - k)] ^ (2 : ℕ) ≤
          (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
      simpa [traj, k] using
        tail_window_min_gradient_sq_le_explicit_bound
          hconv hgrad hgrad_lipschitz xStar hxStar x0 hL hkT
    have hprod :
        ((T + 4 : ℝ) * (T + 6 : ℝ)) / 4 ≤ (k + 4 : ℝ) * (T - k + 1 : ℝ) := by
      simpa [k] using midpoint_window_product_ge_quarter_target (T := T) hT
    let tail := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k)
    have hfull_nonneg : 0 ≤ g[f; traj; 0, T | Nat.zero_le T] := by
      rcases minGradientNormAlongIterates.exists_eq f traj (Nat.zero_le T) with
        ⟨i, -, -, hi⟩
      rw [hi]
      exact norm_nonneg _
    have htail_nonneg : 0 ≤ g[f; tail; 0, T - k | Nat.zero_le (T - k)] := by
      rcases minGradientNormAlongIterates.exists_eq f tail (Nat.zero_le (T - k)) with
        ⟨j, -, -, hj⟩
      rw [hj]
      exact norm_nonneg _
    have hfull_le_tail :
        g[f; traj; 0, T | Nat.zero_le T] ≤
          g[f; tail; 0, T - k | Nat.zero_le (T - k)] := by
      rcases minGradientNormAlongIterates.exists_eq f tail (Nat.zero_le (T - k)) with
        ⟨j, hj0, hjTk, hjEq⟩
      let i : ℕ := k + j
      have hiT : i ≤ T := by
        dsimp [i]
        omega
      have htail :
          tail j = traj i := by
        dsimp [tail, i]
        simpa [traj, add_comm] using
          gradientMethod_restart_eq_tail f (1 / (L : ℝ)) x0 k j
      have hnorm_eq :
          ‖∇ f (traj i)‖ = g[f; tail; 0, T - k | Nat.zero_le (T - k)] := by
        rw [hjEq]
        simp [htail]
      calc
        g[f; traj; 0, T | Nat.zero_le T] ≤ ‖∇ f (traj i)‖ := by
          exact minGradientNormAlongIterates.le f traj (Nat.zero_le T) (Nat.zero_le i) hiT
        _ = g[f; tail; 0, T - k | Nat.zero_le (T - k)] := hnorm_eq
    have hfull_sq_window :
        g[f; traj; 0, T | Nat.zero_le T] ^ (2 : ℕ) ≤
          (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
      exact ((sq_le_sq₀ hfull_nonneg htail_nonneg).2 hfull_le_tail).trans hwindow
    have hfinal_window :
        (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((k + 4 : ℝ) * (T - k + 1 : ℝ)) ≤
          (16 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((T + 4 : ℝ) * (T + 6 : ℝ)) := by
      have hrecip :
          1 / ((k + 4 : ℝ) * (T - k + 1 : ℝ)) ≤
            1 / (((T + 4 : ℝ) * (T + 6 : ℝ)) / 4) :=
        one_div_le_one_div_of_le (by positivity) hprod
      have hnum_nonneg : 0 ≤ 4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_left hrecip hnum_nonneg
      calc
        (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((k + 4 : ℝ) * (T - k + 1 : ℝ)) ≤
          (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) *
            (1 / (((T + 4 : ℝ) * (T + 6 : ℝ)) / 4)) := by
              simpa [div_eq_mul_inv] using hmul
        _ = (16 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
              ((T + 4 : ℝ) * (T + 6 : ℝ)) := by
              field_simp
              ring
    let rhs : ℝ :=
      (4 * (L : ℝ) * ‖x0 - xStar‖) / Real.sqrt ((T + 4 : ℝ) * (T + 6 : ℝ))
    have hrhs_nonneg : 0 ≤ rhs := by
      dsimp [rhs]
      positivity
    have hrhs_sq :
        rhs ^ (2 : ℕ) =
          (16 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((T + 4 : ℝ) * (T + 6 : ℝ)) := by
      dsimp [rhs]
      have hsqrt_mul :
          Real.sqrt ((T + 4 : ℝ) * (T + 6 : ℝ)) *
              Real.sqrt ((T + 4 : ℝ) * (T + 6 : ℝ)) =
            (T + 4 : ℝ) * (T + 6 : ℝ) := by
        simpa [pow_two] using Real.sq_sqrt (by positivity : 0 ≤ (T + 4 : ℝ) * (T + 6 : ℝ))
      rw [div_pow, pow_two, pow_two, hsqrt_mul]
      ring
    have hsq :
        g[f; traj; 0, T | Nat.zero_le T] ^ (2 : ℕ) ≤ rhs ^ (2 : ℕ) := by
      rw [hrhs_sq]
      exact hfull_sq_window.trans hfinal_window
    exact (sq_le_sq₀ hfull_nonneg hrhs_nonneg).1 hsq

end

section

variable [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E

local instance theorem25FiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

/-- Finite-dimensional Chapter 2 specialization of Theorem 2.25: the source-facing notation
`f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` supplies the intrinsic owner hypotheses used by
`gradientMethod_min_gradient_norm_le_explicit_sublinear_rate`. -/
theorem gradientMethod_min_gradient_norm_le_explicit_sublinear_rate_of_mem_F11
    (hf : f ∈ 𝓕[L, p]¹¹)
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) {T : ℕ} (hT : 3 ≤ T) :
    g[f; gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0; 0, T | Nat.zero_le T] ≤
      (4 * (L : ℝ) * ‖x0 - xStar‖) / Real.sqrt ((T + 4 : ℝ) * (T + 6 : ℝ)) :=
  gradientMethod_min_gradient_norm_le_explicit_sublinear_rate
    hf.convexOn hf.hasGradientAt hf.gradient_lipschitz xStar hxStar x0 hT

end

end ConvexC1SeminormSmooth
