/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_6_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SmoothConvex MinGradientNormAlongIterates

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E

local instance theorem24FiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

/- Primary domain: explicit gradient-norm rates for smooth-convex gradient descent on
finite-dimensional real inner-product spaces.

Owner-style declarations sampled before refining this file:
* `gradientMethod` in `Algorithm_2_1`, the chapter recall of the canonical gradient-method
  trajectory;
* `minGradientNormAlongIterates` and `minGradientNormAlongIterates.exists_eq` in
  `Definition_2_23`, the owner `g_{k,T}` object and its attainment lemma;
* `gradient_step_value_descent_of_lipschitzGradient` in `Lemma_2_16`, the reciprocal-`L`
  one-step descent estimate used on tail windows.

Source/core/bridge triage:
* source-facing: Theorem 2.24's existence of an iterate `i ∈ {0, …, T}` with the explicit
  squared-gradient bound;
* core/canonical: the tail-window minimum
  `g[f; gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (x_k); 0, T - k | Nat.zero_le _]`;
* bridge/view: the Chapter 1 tail-window estimate `minGradientNormAlongIterates_le_sqrt`,
  combined with the Chapter 2 objective-gap decay from Theorem 2.15.

Primitive data:
* the smooth-convex owner hypothesis `hf`;
* a minimizer `xStar` with `IsMinOn f Set.univ xStar`;
* the initial point `x0`.

Derived API:
* the minimizer value as the exact infimum of `Set.range f`;
* the stage-`k` objective-gap estimate
  `f(x_k) - f(xStar) ≤ 2 L ‖x0 - xStar‖² / (k + 4)`;
* the tail-window bound for `g_{k,T}`;
* the midpoint-product lower bound used to reach the final constant.

Accordingly, this file keeps the iterate-existence statement as the main public theorem and
implements the source proof directly through the tail-window minimum `g_{k,T}`, rather than by
importing the later Theorem 2.25 bridge. -/

section

variable {L : NNReal} {f : E → ℝ}

namespace ConvexC1SeminormSmooth

/-- Helper for Theorem 2.24: restarting constant-step gradient descent from iterate `k`
reproduces the tail `k + j` of the original trajectory. -/
private theorem gradientMethod_restart_eq_tail
    (f : E → ℝ) (α : ℝ) (x0 : E) (k j : ℕ) :
    gradientMethod (fun _ ↦ α) f (gradientMethod (fun _ ↦ α) f x0 k) j =
      gradientMethod (fun _ ↦ α) f x0 (k + j) := by
  -- Rewrite both trajectories as iterates of the same gradient-step map.
  calc
    gradientMethod (fun _ ↦ α) f (gradientMethod (fun _ ↦ α) f x0 k) j =
        (fun x ↦ x - α • ∇ f x)^[j] (gradientMethod (fun _ ↦ α) f x0 k) := by
          simpa using
            (gradientMethod_const_eq_iterate f α (gradientMethod (fun _ ↦ α) f x0 k) j)
    _ = (fun x ↦ x - α • ∇ f x)^[j] ((fun x ↦ x - α • ∇ f x)^[k] x0) := by
          rw [gradientMethod_const_eq_iterate]
    _ = (fun x ↦ x - α • ∇ f x)^[k + j] x0 := by
          simpa [Nat.add_comm] using
            (Function.iterate_add_apply (fun x ↦ x - α • ∇ f x) j k x0).symm
    _ = gradientMethod (fun _ ↦ α) f x0 (k + j) := by
          symm
          simpa using (gradientMethod_const_eq_iterate f α x0 (k + j))

/-- Helper for Theorem 2.24: a whole-space minimizer realizes the exact infimum of the range of
`f`. -/
private theorem objective_value_isGLB_of_isMinOn
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar) :
    IsGLB (Set.range f) (f xStar) := by
  -- Repackage whole-space minimality as the exact infimum of the value set.
  refine ⟨?_, ?_⟩
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    exact (isMinOn_univ_iff.mp hxStar) z
  · intro b hb
    exact hb ⟨xStar, rfl⟩

/-- Helper for Theorem 2.24: the initial objective gap is bounded by the quadratic tangent-error
upper model at the minimizer. -/
private theorem initial_objective_gap_le_half_lipschitz_sqdist
    (hf : f ∈ 𝓕[L, p]¹¹) (xStar x0 : E)
    (hxStar : IsMinOn f Set.univ xStar) :
    f x0 - f xStar ≤ ((L : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  have hgrad0 : ∇ f xStar = 0 := hf.gradient_eq_zero_of_isMinOn hxStar
  -- Apply the smooth tangent upper bound at the minimizer and remove the vanishing linear term.
  have hupper := (hf.tangentErrorBounds (x := xStar) (y := x0) (by simp) (by simp)).2
  simpa [hgrad0, norm_sub_rev] using hupper

/-- Helper for Theorem 2.24: every stage of gradient descent with stepsize `1 / L` satisfies the
textbook objective-gap estimate `f(x_k) - f(xStar) ≤ 2 L ‖x0 - xStar‖² / (k + 4)` when `L > 0`.
-/
private theorem gradientMethod_objective_gap_le_two_mul_L_sqdist_div_add_four
    (hf : f ∈ 𝓕[L, p]¹¹) (xStar x0 : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (hL : 0 < (L : ℝ)) (k : ℕ) :
    f (gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0 k) - f xStar ≤
      (2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ) := by
  let traj : ℕ → E := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0
  let Δ0 : ℝ := f x0 - f xStar
  let R2 : ℝ := ‖x0 - xStar‖ ^ (2 : ℕ)
  by_cases hx0 : x0 = xStar
  · subst x0
    have hgrad0 : ∇ f xStar = 0 := hf.gradient_eq_zero_of_isMinOn hxStar
    have htraj : ∀ n : ℕ, gradientMethod (fun _ ↦ 1 / (L : ℝ)) f xStar n = xStar := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n hn =>
          -- A trajectory started at a minimizer stays fixed because the gradient vanishes there.
          rw [gradientMethod_succ, hn, hgrad0]
          simp
    -- Collapse the stationary trajectory to turn both sides of the estimate into zero.
    have hgap_zero : f (traj k) - f xStar = 0 := by
      exact sub_eq_zero.mpr <| by simpa [traj] using congrArg f (htraj k)
    have hrhs_zero :
        (2 * (L : ℝ) * ‖xStar - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ) = 0 := by
      simp
    rw [hgap_zero, hrhs_zero]
  · let A : ℝ := ((L : ℝ) / 2) * R2
    let c : ℝ := (k : ℝ) / (L : ℝ)
    have hΔ0_nonneg : 0 ≤ Δ0 := by
      dsimp [Δ0]
      exact sub_nonneg.mpr ((isMinOn_univ_iff.mp hxStar) x0)
    have hR2_pos : 0 < R2 := by
      have hsub_ne : x0 - xStar ≠ 0 := sub_ne_zero.mpr hx0
      have hnorm_pos : 0 < ‖x0 - xStar‖ := norm_pos_iff.mpr hsub_ne
      dsimp [R2]
      positivity
    have hgap0_le : Δ0 ≤ A := by
      -- Source equation `(2.u386)` starts from the standard initial quadratic gap bound.
      simpa [Δ0, R2, A, mul_assoc, mul_left_comm, mul_comm] using
        initial_objective_gap_le_half_lipschitz_sqdist
          (hf := hf) (xStar := xStar) (x0 := x0) hxStar
    have hraw :=
      gradientMethod_objective_gap_le_explicit_rate_of_mem_F11
        (hf := hf) xStar hxStar
        (1 / (L : ℝ)) (by positivity)
        (by
          have htwo : (1 : ℝ) ≤ 2 := by norm_num
          exact div_le_div_of_nonneg_right htwo hL.le)
        x0 k
    have hraw' :
        f (traj k) - f xStar ≤
          (2 * Δ0 * R2) / (2 * R2 + c * Δ0) := by
      -- Specialize Theorem 2.15 to the reciprocal stepsize `h = 1 / L`.
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
      -- Evaluate the rational expression after inserting the initial-gap upper bound.
      dsimp [A, c]
      field_simp [ne_of_gt hL, ne_of_gt hR2_pos]
      ring_nf
    calc
      f (traj k) - f xStar ≤ (2 * Δ0 * R2) / (2 * R2 + c * Δ0) := hraw'
      _ ≤ (2 * A * R2) / (2 * R2 + c * A) := hmono
      _ = (2 * (L : ℝ) * R2) / (k + 4 : ℝ) := hA_eval
      _ = (2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ) := by
            simp [R2]

/-- Helper for Theorem 2.24: on every tail window `k, …, T`, the minimum gradient norm satisfies
the explicit source bound obtained by combining the tail sufficient-decrease estimate with the
stage-`k` objective-gap decay. -/
private theorem tail_window_min_gradient_sq_le_explicit_bound
    (hf : f ∈ 𝓕[L, p]¹¹) (xStar x0 : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (hL : 0 < (L : ℝ)) {k T : ℕ} (hkT : k ≤ T) :
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
          f (tail j) - f (tail (j + 1)) := by
    intro j
    have hdescent :
        f (tail (j + 1)) ≤
          f (tail j) -
            (1 / (2 * (L : ℝ))) * ‖∇ f (tail j)‖ ^ (2 : ℕ) := by
      -- Lemma 2.16 supplies the sufficient decrease on each tail iterate.
      simpa [tail, gradientMethod_succ] using
        gradient_step_value_descent_of_lipschitzGradient
          f hL
          (fun x ↦ (hf.hasGradientAt x).differentiableAt)
          (by simpa using hf.gradient_lipschitz)
          (tail j)
    have hcoeff :
        (((1 / 2 : ℝ) / (L : ℝ)) * ‖∇ f (tail j)‖ ^ (2 : ℕ)) =
          (1 / (2 * (L : ℝ))) * ‖∇ f (tail j)‖ ^ (2 : ℕ) := by
      field_simp [ne_of_gt hL]
    rw [hcoeff]
    linarith
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
      have hden_nonneg : 0 ≤ ((1 / 2 : ℝ) * (T - k + 1 : ℝ)) := by
        have hkT' : (k : ℝ) ≤ T := by
          exact_mod_cast hkT
        nlinarith
      exact div_nonneg (mul_nonneg (by exact_mod_cast L.2) hgapk_nonneg) hden_nonneg
    -- Square the Chapter 1 root estimate to recover the tail-window source bound.
    exact (Real.le_sqrt htail_nonneg hinside_nonneg).1 hroot'
  have hgapk :
      f (traj k) - f xStar ≤
        (2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ) :=
    gradientMethod_objective_gap_le_two_mul_L_sqdist_div_add_four
      (hf := hf) (xStar := xStar) (x0 := x0) hxStar hL k
  have hinside_le :
      ((L : ℝ) * (f (traj k) - f xStar)) / (((1 / 2 : ℝ) * (T - k + 1 : ℝ))) ≤
        (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
    have hden_nonneg : 0 ≤ (T - k + 1 : ℝ) := by
      have hkT' : (k : ℝ) ≤ T := by
        exact_mod_cast hkT
      nlinarith
    -- Insert the stage-`k` gap estimate into the Chapter 1 radicand.
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

/-- Helper for Theorem 2.24: the midpoint-like choice `k = (T - 3) / 2` makes the tail-window
product dominate a quarter of `(T + 4) (T + 6)`. -/
private theorem midpoint_window_product_ge_quarter_target
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
    -- Split on the parity of `T - 3` to evaluate the midpoint choice explicitly.
    rcases hr with hr | hr
    · have hT0 : T = 2 * k + 3 := by
        rw [hr] at hdecomp
        simpa using hdecomp
      rw [hT0]
      have hkdiv0 : (2 * k + 3 - 3) / 2 = k := by
        omega
      have hright0 : 2 * k + 3 - k + 1 = k + 4 := by
        omega
      rw [hkdiv0]
      rw [hright0]
      zify
      nlinarith
    · have hT1 : T = 2 * k + 4 := by
        rw [hr] at hdecomp
        simpa using hdecomp
      rw [hT1]
      have hkdiv1 : (2 * k + 4 - 3) / 2 = k := by
        omega
      have hright1 : 2 * k + 4 - k + 1 = k + 5 := by
        omega
      rw [hkdiv1]
      rw [hright1]
      zify
      nlinarith
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

/-- Theorem 2.24: on a finite-dimensional real inner-product space, for the constant-step
gradient-method trajectory with step `1 / L`, some iterate among `x₀, …, x_T` has squared
gradient norm at most `16 L² ‖x₀ - x^*‖² / ((T + 4) (T + 6))` whenever `T ≥ 3`. The textbook
`ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Route correction: the file now follows the source proof through the tail-window minimum
-- `g_{k,T}` instead of importing the later Theorem 2.25 bridge.
-- Proof sketch: treat the degenerate case `L = 0` separately, where the Lipschitz-gradient
-- hypothesis forces all gradients to vanish. For `L > 0`, choose the midpoint-like window start
-- `k = (T - 3) / 2`, bound the tail minimum `g_{k,T}` by the Chapter 1 finite-window estimate
-- plus the Chapter 2 stage-`k` objective-gap decay, and then use the attainment lemma for
-- `minGradientNormAlongIterates` to extract the desired iterate.
theorem gradientMethod_exists_iterate_with_small_gradient_sq
    (xStar : E) (x0 : E) {T : ℕ}
    (hf : f ∈ 𝓕[L, p]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (hT : 3 ≤ T) :
    ∃ i ≤ T,
      ‖∇ f ((gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0) i)‖ ^ (2 : ℕ) ≤
        (16 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          ((T + 4 : ℝ) * (T + 6 : ℝ)) := by
  let traj : ℕ → E := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0
  by_cases hL0 : (L : ℝ) = 0
  · have hgrad_zero : ∀ x : E, ∇ f x = 0 := by
      intro x
      have hgradStar : ∇ f xStar = 0 := hf.gradient_eq_zero_of_isMinOn hxStar
      have hdist := hf.gradient_lipschitz.dist_le_mul x xStar
      have hdist_eq :
          dist (∇ f x) (∇ f xStar) = 0 := by
        apply le_antisymm
        · simpa [hL0] using hdist
        · exact dist_nonneg
      have hsame : ∇ f x = ∇ f xStar := eq_of_dist_eq_zero hdist_eq
      simpa [hgradStar] using hsame
    -- When `L = 0`, every gradient vanishes, so the zeroth iterate already satisfies the claim.
    refine ⟨0, Nat.zero_le T, ?_⟩
    have hrhs_zero :
        (16 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((T + 4 : ℝ) * (T + 6 : ℝ)) = 0 := by
      simp [hL0]
    simp [hgrad_zero x0, hrhs_zero]
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
          (hf := hf) (xStar := xStar) (x0 := x0) (hxStar := hxStar) hL hkT
    have hprod :
        ((T + 4 : ℝ) * (T + 6 : ℝ)) / 4 ≤ (k + 4 : ℝ) * (T - k + 1 : ℝ) := by
      simpa [k] using midpoint_window_product_ge_quarter_target (T := T) hT
    rcases minGradientNormAlongIterates.exists_eq
        f (gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k)) (Nat.zero_le (T - k)) with
      ⟨j, hj0, hjTk, hjEq⟩
    let i : ℕ := k + j
    have hiT : i ≤ T := by
      dsimp [i]
      omega
    have htail :
        gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k) j = traj i := by
      dsimp [i]
      simpa [traj, add_comm] using
        gradientMethod_restart_eq_tail (f := f) (α := 1 / (L : ℝ)) x0 k j
    have hmid :
        ‖∇ f (traj i)‖ ^ (2 : ℕ) ≤
          (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
      -- Evaluate the tail-window minimum at the attaining index `j`.
      calc
        ‖∇ f (traj i)‖ ^ (2 : ℕ)
            = ‖∇ f (gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k) j)‖ ^ (2 : ℕ) := by
              rw [htail]
        _ = g[f; gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k);
              0, T - k | Nat.zero_le (T - k)] ^ (2 : ℕ) := by
              rw [← hjEq]
        _ ≤ (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
              ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := hwindow
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
            ((k + 4 : ℝ) * (T - k + 1 : ℝ))
            =
            (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) *
              (1 / ((k + 4 : ℝ) * (T - k + 1 : ℝ))) := by
              simp [div_eq_mul_inv]
        _ ≤ (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) *
              (1 / (((T + 4 : ℝ) * (T + 6 : ℝ)) / 4)) := hmul
        _ = (16 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
              ((T + 4 : ℝ) * (T + 6 : ℝ)) := by
              field_simp
              ring
    refine ⟨i, hiT, ?_⟩
    exact hmid.trans hfinal_window

end ConvexC1SeminormSmooth

end
