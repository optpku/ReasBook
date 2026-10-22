/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_6_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Primary domain: smooth convex gradient descent on real Hilbert spaces.

Owner-style declarations sampled before refining this file:
* `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)` in `Chap01/Definition_1_5_2`, the chapter's canonical
  `C^{1,1}_L` owner on real Hilbert spaces;
* `gradientMethod_value_antitone_of_constant_stepsize` in `Proposition_2_8`, the canonical
  constant-step monotonicity theorem on that intrinsic ambient layer;
* `gradientMethod_sqdist_le_geometric_rate` in `Theorem_2_17`, which already states a Chapter 2
  gradient-method rate theorem on the same intrinsic Hilbert-space owner layer;
* `ConvexC1SeminormSmooth.gradient_lipschitz` in `Theorem_2_5`, the finite-dimensional bridge
  from the Chapter 2 notation `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` to the canonical Lipschitz-gradient
  owner hypothesis.

Source/core/bridge triage:
* source-facing: the explicit gradient-descent objective-gap rate of Theorem 2.15;
* core/canonical: `ConvexOn ℝ Set.univ f`, `ContDiff ℝ 1 f`, `LipschitzWith L (∇ f)`,
  `IsMinOn f Set.univ xStar`, and the constant-step trajectory
  `gradientMethod (fun _ ↦ h) f x0`;
* bridge/view: the finite-dimensional Chapter 2 wrapper `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`, whose
  only role here is to recover the intrinsic owner hypotheses.

Primitive data:
* whole-space convexity of `f`;
* `C¹` regularity of `f`;
* the global Lipschitz bound for `∇ f`;
* a global minimizer `xStar` with `IsMinOn f Set.univ xStar`;
* the constant-step bounds `0 ≤ h ≤ 2 / L`;
* the initial point `x0`.

Derived API:
* the Chapter 1 sufficient-decrease and monotonicity estimates for the constant-step trajectory;
* the convex first-order lower bound against the minimizer;
* the specialization from the Chapter 2 smooth-convex notation
  `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`.

Accordingly, the main theorem is stated on the intrinsic real-Hilbert-space owner layer, and the
finite-dimensional Chapter 2 notation `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` is kept only as a thin
specialization bridge rather than as primitive public data. -/

namespace ConvexC1SeminormSmooth

variable {L : NNReal} {f : E → ℝ}

section

variable [CompleteSpace E]

/-- Helper for Theorem 2.15: convexity and an `L`-Lipschitz gradient imply the quadratic lower
tangent estimate that underlies the cocoercivity argument. -/
private theorem gradient_quadratic_lower_bound_of_convex_contDiffOne_lipschitz
    (hconv : ConvexOn ℝ Set.univ f)
    (hf_C1 : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hL : 0 < L)
    (x y : E) :
    f y + inner ℝ (∇ f y) (x - y) +
        (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) ≤
      f x := by
  let d := ∇ f x - ∇ f y
  let z := x - (1 / (L : ℝ)) • d
  have hgradAt : ∀ u : E, HasGradientAt f (∇ f u) u :=
    fun u ↦ (hf_C1.differentiable_one u).hasGradientAt
  -- The smooth upper model at `x` controls the shifted point `z`.
  have hupper :
      f z ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    have h :=
      taylor_upper_bound_of_contDiffOne_withLipschitzGradient hf_C1 hgrad_lipschitz x z
    have hz : z - x = -((1 / (L : ℝ)) • d) := by
      simp [z]
    calc
      f z ≤ f x + inner ℝ (∇ f x) (z - x) + ((L : ℝ) / 2) * ‖z - x‖ ^ (2 : ℕ) := by
        simpa [firstOrderTaylorModelAt_apply] using h
      _ = f x + inner ℝ (∇ f x) (-((1 / (L : ℝ)) • d)) +
            ((L : ℝ) / 2) * ‖-((1 / (L : ℝ)) • d)‖ ^ (2 : ℕ) := by
            rw [hz]
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            ((L : ℝ) / 2) * ((1 / (L : ℝ)) ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ)) := by
            simp [inner_smul_right, norm_smul, sq]
            ring
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
            have hL0 : (L : ℝ) ≠ 0 := by
              exact_mod_cast (ne_of_gt hL)
            field_simp [hL0]
  -- Convexity gives the matching lower tangent bound at `y`.
  have hlower :
      f z ≥
        f y + inner ℝ (∇ f y) (x - y) -
          (1 / (L : ℝ)) * inner ℝ (∇ f y) d := by
    have h :=
      hconv.lower_tangent_plane_of_hasGradientWithinAt
        y (by simp) (∇ f y) ((hasGradientWithinAt_univ).2 (hgradAt y)) z (by simp)
    have hz : z - y = (x - y) - (1 / (L : ℝ)) • d := by
      simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    calc
      f z ≥ f y + inner ℝ (∇ f y) (z - y) := h
      _ = f y + inner ℝ (∇ f y) ((x - y) - (1 / (L : ℝ)) • d) := by
        rw [hz]
      _ = f y + inner ℝ (∇ f y) (x - y) -
            (1 / (L : ℝ)) * inner ℝ (∇ f y) d := by
            rw [inner_sub_right, inner_smul_right]
            ring
  have hinner :
      inner ℝ (∇ f x) d = inner ℝ (∇ f y) d + ‖d‖ ^ (2 : ℕ) := by
    calc
      inner ℝ (∇ f x) d = inner ℝ (d + ∇ f y) d := by
        congr 1
        dsimp [d]
        abel_nf
      _ = inner ℝ d d + inner ℝ (∇ f y) d := by
        rw [inner_add_left]
      _ = inner ℝ (∇ f y) d + ‖d‖ ^ (2 : ℕ) := by
        simp [inner_self_eq_norm_sq_to_K, add_comm]
  have hupper' :
      f z ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    calc
      f z ≤
          f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := hupper
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
            rw [hinner]
            ring
  -- Comparing the lower and upper controls isolates the quadratic remainder.
  have hmid :
      f y + inner ℝ (∇ f y) (x - y) -
          (1 / (L : ℝ)) * inner ℝ (∇ f y) d ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) :=
    le_trans hlower hupper'
  have hmid' :
      f y + inner ℝ (∇ f y) (x - y) ≤
        f x - (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    linarith
  have hfinal :
      f y + inner ℝ (∇ f y) (x - y) +
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) ≤
        f x := by
    linarith
  simpa [d] using hfinal

/-- Helper for Theorem 2.15: specializing the quadratic lower tangent estimate at a minimizer
gives the pairing bound needed for the radius monotonicity argument. -/
private theorem gradient_pairing_with_minimizer_gap_ge_norm_sq_div_local
    (hconv : ConvexOn ℝ Set.univ f)
    (hf_C1 : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x : E) :
    (1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x) (x - xStar) := by
  have hgrad0 : ∇ f xStar = 0 := by
    exact
      (isMinOn_hasGradientAt_zero_of_differentiableAt
        (hf_C1.differentiable_one xStar) hxStar).gradient
  by_cases hL : 0 < L
  · have hxy :=
      gradient_quadratic_lower_bound_of_convex_contDiffOne_lipschitz
        hconv hf_C1 hgrad_lipschitz hL x xStar
    have hyx :=
      gradient_quadratic_lower_bound_of_convex_contDiffOne_lipschitz
        hconv hf_C1 hgrad_lipschitz hL xStar x
    have hxy' :
        f xStar + (1 / (2 * (L : ℝ))) * ‖∇ f x‖ ^ (2 : ℕ) ≤ f x := by
      simpa [hgrad0, sub_zero] using hxy
    have hyx' :
        f x - inner ℝ (∇ f x) (x - xStar) +
            (1 / (2 * (L : ℝ))) * ‖∇ f x‖ ^ (2 : ℕ) ≤
          f xStar := by
      have hsub : xStar - x = -(x - xStar) := by
        abel_nf
      have hyx'' := hyx
      rw [hgrad0, norm_sub_rev, hsub, inner_neg_right, sub_zero] at hyx''
      exact hyx''
    have hsum := add_le_add hxy' hyx'
    ring_nf at hsum ⊢
    linarith
  · have hL0 : L = 0 := le_antisymm (le_of_not_gt hL) bot_le
    have hgrad_eq : ∇ f x = ∇ f xStar := by
      have hdist := hgrad_lipschitz.dist_le_mul x xStar
      have hdist0 : dist (∇ f x) (∇ f xStar) = 0 := by
        apply le_antisymm
        · simpa [hL0] using hdist
        · exact dist_nonneg
      exact eq_of_dist_eq_zero hdist0
    simp [hL0, hgrad_eq, hgrad0]

/-- Theorem 2.15 on the intrinsic real-Hilbert-space owner layer: if `f` is convex on the whole
space, `C¹`, has `L`-Lipschitz gradient, `xStar` is a global minimizer of `f`, and `0 ≤ h ≤ 2 / L`,
then the gradient method with step size `h` satisfies the explicit sublinear objective-gap bound at
every iterate. The textbook `ℝⁿ` formulation is recovered by the finite-dimensional Chapter 2
specialization theorem below. The source strict range `0 < h < 2 / L` is a special case, and at
the endpoints the correction factor `h * (2 - L * h)` vanishes. -/
-- Proof sketch: combine the Chapter 1 constant-step sufficient-decrease / monotonicity API with
-- the convex first-order inequality against the minimizer `xStar`, using `hxStar` to replace
-- `f xStar` by the minimum value. This yields a reciprocal-gap estimate for
-- `Δ_k = f x_k - f xStar` in terms of `‖x0 - xStar‖²`; telescope that estimate over the
-- constant-step trajectory. The Chapter 2 owner notation `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`
-- reappears only in the specialization bridge below.
theorem gradientMethod_objective_gap_le_explicit_rate
    (hconv : ConvexOn ℝ Set.univ f)
    (hf_C1 : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (h : ℝ) (hh_nonneg : 0 ≤ h) (hh_le : h ≤ 2 / (L : ℝ))
    (x0 : E) (k : ℕ) :
    f (gradientMethod (fun _ ↦ h) f x0 k) - f xStar ≤
      (2 * (f x0 - f xStar) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (2 * ‖x0 - xStar‖ ^ (2 : ℕ) +
          h * (2 - (L : ℝ) * h) * (k : ℝ) * (f x0 - f xStar)) := by
  let traj : ℕ → E := gradientMethod (fun _ ↦ h) f x0
  let Δ : ℕ → ℝ := fun i ↦ f (traj i) - f xStar
  let R2 : ℝ := ‖x0 - xStar‖ ^ (2 : ℕ)
  let ω : ℝ := h * (2 - (L : ℝ) * h) / 2
  have hgradAt : ∀ x : E, HasGradientAt f (∇ f x) x :=
    fun x ↦ (hf_C1.differentiable_one x).hasGradientAt
  have hxStar_min : ∀ y : E, f xStar ≤ f y := by
    intro y
    exact (isMinOn_iff.mp hxStar) y (by simp)
  have hΔ_nonneg : ∀ i : ℕ, 0 ≤ Δ i := by
    intro i
    dsimp [Δ, traj]
    exact sub_nonneg.mpr (hxStar_min (traj i))
  have hω_nonneg : 0 ≤ ω := by
    -- The textbook correction factor is nonnegative on the full monotonicity interval.
    by_cases hL0 : (L : ℝ) = 0
    · have hh_nonpos : h ≤ 0 := by
        simpa [hL0] using hh_le
      have hh_zero : h = 0 := by
        linarith
      simp [ω, hh_zero, hL0]
    · have hL_pos : 0 < (L : ℝ) :=
        lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hL0)
      have hmul : (L : ℝ) * h ≤ 2 := by
        simpa [mul_comm] using (le_div_iff₀ hL_pos).mp hh_le
      dsimp [ω]
      nlinarith
  have hmono_f :
      Antitone (fun i ↦ f (traj i)) := by
    refine antitone_nat_of_succ_le ?_
    intro i
    have hstep :=
      gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
        (hf := hf_C1) (hgrad := hgrad) (traj i) h
    have hcoeff_nonneg : 0 ≤ h * (1 - ((L : ℝ) * h) / 2) := by
      dsimp [ω] at hω_nonneg
      nlinarith
    have hdrop_nonneg :
        0 ≤ h * (1 - ((L : ℝ) * h) / 2) * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
      positivity
    simpa [traj, gradientMethod_succ] using le_trans hstep (by linarith)
  have hmono : Antitone Δ := by
    intro i j hij
    dsimp [Δ]
    exact sub_le_sub_right (hmono_f hij) _
  have hsqdist_step :
      ∀ x : E, ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) ≤ ‖x - xStar‖ ^ (2 : ℕ) := by
    intro x
    -- Expand one step and use the local minimizer-pairing inequality.
    have hpair :=
      gradient_pairing_with_minimizer_gap_ge_norm_sq_div_local
        hconv hf_C1 hgrad hxStar x
    have hcoeff_nonpos : h ^ (2 : ℕ) - 2 * h / (L : ℝ) ≤ 0 := by
      by_cases hL0 : (L : ℝ) = 0
      · have hh_nonpos : h ≤ 0 := by
          simpa [hL0] using hh_le
        have hh_zero : h = 0 := by
          linarith
        simp [hh_zero, hL0]
      · have hL_pos : 0 < (L : ℝ) :=
          lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hL0)
        have hsq_le : h ^ (2 : ℕ) ≤ 2 * h / (L : ℝ) := by
          have hh' : h * h ≤ h * (2 / (L : ℝ)) :=
            mul_le_mul_of_nonneg_left hh_le hh_nonneg
          calc
            h ^ (2 : ℕ) = h * h := by ring
            _ ≤ h * (2 / (L : ℝ)) := hh'
            _ = 2 * h / (L : ℝ) := by ring
        linarith
    have hpair' :
        (-2 * h) * inner ℝ (∇ f x) (x - xStar) ≤
          (-2 * h) * ((1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonpos_left hpair (by nlinarith)
    have hexpand :
        ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) =
          ‖x - xStar‖ ^ (2 : ℕ) - 2 * h * inner ℝ (∇ f x) (x - xStar) +
            h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
      calc
        ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) =
            ‖(x - xStar) - h • ∇ f x‖ ^ (2 : ℕ) := by
              abel_nf
        _ = ‖x - xStar‖ ^ (2 : ℕ) - 2 * inner ℝ (x - xStar) (h • ∇ f x) +
              ‖h • ∇ f x‖ ^ (2 : ℕ) := by
              simpa using norm_sub_sq_real (x - xStar) (h • ∇ f x)
        _ = ‖x - xStar‖ ^ (2 : ℕ) - 2 * h * inner ℝ (∇ f x) (x - xStar) +
              h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
              rw [real_inner_smul_right, real_inner_comm]
              simp [norm_smul, Real.norm_of_nonneg hh_nonneg, sq]
              ring
    have hrest_nonpos :
        (-2 * h) * ((1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ)) +
            h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) ≤
          0 := by
      have hnorm_nonneg : 0 ≤ ‖∇ f x‖ ^ (2 : ℕ) := by
        positivity
      have hrewrite :
          (-2 * h) * ((1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ)) +
              h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) =
            (h ^ (2 : ℕ) - 2 * h / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
        ring
      rw [hrewrite]
      exact mul_nonpos_of_nonpos_of_nonneg hcoeff_nonpos hnorm_nonneg
    calc
      ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) =
          ‖x - xStar‖ ^ (2 : ℕ) - 2 * h * inner ℝ (∇ f x) (x - xStar) +
            h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := hexpand
      _ ≤ ‖x - xStar‖ ^ (2 : ℕ) +
            ((-2 * h) * ((1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ)) +
              h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ)) := by
            linarith
      _ ≤ ‖x - xStar‖ ^ (2 : ℕ) := by
            linarith
  have hsqdist_le_initial : ∀ i : ℕ, ‖traj i - xStar‖ ^ (2 : ℕ) ≤ R2 := by
    intro i
    induction i with
    | zero =>
        simp [traj, R2]
    | succ i hi =>
        -- The source invariant `r_(i+1) ≤ r_i ≤ r_0` follows by iterating the one-step estimate.
        have hstep := hsqdist_step (traj i)
        simpa [traj, R2, gradientMethod_succ] using le_trans hstep hi
  have hgap_sq_le : ∀ i : ℕ, (Δ i) ^ (2 : ℕ) ≤ R2 * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
    intro i
    -- Combine the convex lower-tangent inequality with Cauchy-Schwarz and the radius invariant.
    have htangent :=
      hconv.lower_tangent_plane_of_hasGradientWithinAt
        (traj i) (by simp) (∇ f (traj i))
        ((hasGradientWithinAt_univ).2 (hgradAt (traj i)))
        xStar (by simp)
    have hfirst :
        Δ i ≤ inner ℝ (∇ f (traj i)) (traj i - xStar) := by
      have hsub :
          inner ℝ (∇ f (traj i)) (xStar - traj i) =
            -inner ℝ (∇ f (traj i)) (traj i - xStar) := by
        have : xStar - traj i = -(traj i - xStar) := by
          abel_nf
        rw [this, inner_neg_right]
      dsimp [Δ, traj] at *
      rw [hsub] at htangent
      linarith
    have hcs :
        Δ i ≤ ‖∇ f (traj i)‖ * ‖traj i - xStar‖ := by
      exact le_trans (le_trans hfirst (le_abs_self _)) (abs_real_inner_le_norm _ _)
    have hrad :
        ‖traj i - xStar‖ ≤ ‖x0 - xStar‖ := by
      exact
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 <|
          by simpa [R2, pow_two] using hsqdist_le_initial i
    have hcs' :
        Δ i ≤ ‖∇ f (traj i)‖ * ‖x0 - xStar‖ := by
      exact le_trans hcs (mul_le_mul_of_nonneg_left hrad (norm_nonneg _))
    have hsq :=
      (sq_le_sq₀ (hΔ_nonneg i)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hcs'
    simpa [R2, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  by_cases hΔ0_zero : Δ 0 = 0
  · -- If the initial gap vanishes, monotonicity and nonnegativity force every later gap to vanish.
    have hgap0 : f x0 - f xStar = 0 := by
      simpa [Δ, traj, gradientMethod_zero] using hΔ0_zero
    have hΔk_zero : Δ k = 0 := by
      have hk_le_zero : Δ k ≤ 0 := by
        simpa [hΔ0_zero] using hmono (Nat.zero_le k)
      exact le_antisymm hk_le_zero (hΔ_nonneg k)
    simpa [Δ, traj, R2, gradientMethod_zero, hgap0, hΔk_zero]
  · have hΔ0_pos : 0 < Δ 0 :=
        lt_of_le_of_ne (hΔ_nonneg 0) (Ne.symm hΔ0_zero)
    have hR2_nonneg : 0 ≤ R2 := by
      dsimp [R2]
      positivity
    have hR2_pos : 0 < R2 := by
      have hR2_ne : R2 ≠ 0 := by
        intro hR2_zero
        have hnorm_zero : ‖x0 - xStar‖ = 0 := by
          have hsq_zero : ‖x0 - xStar‖ ^ (2 : ℕ) = 0 := by
            simpa [R2] using hR2_zero
          nlinarith [norm_nonneg (x0 - xStar)]
        have hx0_eq : x0 = xStar := by
          exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
        have : Δ 0 = 0 := by
          simpa [Δ, traj, gradientMethod_zero, hx0_eq]
        exact hΔ0_zero this
      exact lt_of_le_of_ne hR2_nonneg hR2_ne.symm
    have hstep_rec :
        ∀ i : ℕ, Δ (i + 1) ≤ Δ i - (ω / R2) * (Δ i) ^ (2 : ℕ) := by
      intro i
      -- Route correction: eliminate the gradient norm using the source quadratic gap estimate.
      have hdrop :=
        gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
          (hf := hf_C1) (hgrad := hgrad) (traj i) h
      have hdrop_step :
          f (traj (i + 1)) ≤
            f (traj i) - h * (1 - ((L : ℝ) * h) / 2) * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
        simpa [traj, gradientMethod_succ] using hdrop
      have hdrop' :
          Δ (i + 1) ≤ Δ i - ω * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
        have hω_eq : h * (1 - ((L : ℝ) * h) / 2) = ω := by
          dsimp [ω]
          ring
        have hdrop_gap :
            f (traj (i + 1)) - f xStar ≤
              (f (traj i) - f xStar) -
                h * (1 - ((L : ℝ) * h) / 2) * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
          linarith
        simpa [Δ, hω_eq] using hdrop_gap
      have hgrad_elim :
          (ω / R2) * (Δ i) ^ (2 : ℕ) ≤ ω * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
        have hdiv :
            (Δ i) ^ (2 : ℕ) / R2 ≤ ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
          exact (div_le_iff₀ hR2_pos).2 <|
            by simpa [mul_assoc, mul_left_comm, mul_comm] using hgap_sq_le i
        have hmul := mul_le_mul_of_nonneg_left hdiv hω_nonneg
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
      linarith
    by_cases hΔk_zero : Δ k = 0
    · have hcoeff_nonneg : 0 ≤ h * (2 - (L : ℝ) * h) := by
        dsimp [ω] at hω_nonneg
        nlinarith
      have hrhs_nonneg :
          0 ≤
            (2 * (f x0 - f xStar) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
              (2 * ‖x0 - xStar‖ ^ (2 : ℕ) +
                h * (2 - (L : ℝ) * h) * (k : ℝ) * (f x0 - f xStar)) := by
        have hgap0_nonneg : 0 ≤ f x0 - f xStar := by
          simpa [Δ, traj, gradientMethod_zero] using hΔ_nonneg 0
        have hden_nonneg :
            0 ≤ 2 * ‖x0 - xStar‖ ^ (2 : ℕ) +
              h * (2 - (L : ℝ) * h) * (k : ℝ) * (f x0 - f xStar) := by
          positivity
        exact div_nonneg (by positivity) hden_nonneg
      simpa [Δ, traj, gradientMethod_zero, hΔk_zero] using hrhs_nonneg
    · have hΔk_pos : 0 < Δ k :=
          lt_of_le_of_ne (hΔ_nonneg k) (Ne.symm hΔk_zero)
      have hΔ_pos_prefix : ∀ {i : ℕ}, i ≤ k → 0 < Δ i := by
        intro i hik
        exact lt_of_lt_of_le hΔk_pos (hmono hik)
      have hrecip_step :
          ∀ i : ℕ, i < k → ω / R2 ≤ 1 / Δ (i + 1) - 1 / Δ i := by
        intro i hik
        have hi1_le : i + 1 ≤ k := Nat.succ_le_of_lt hik
        have hi_le : i ≤ k := Nat.le_trans (Nat.le_succ i) hi1_le
        have hΔi_pos : 0 < Δ i := hΔ_pos_prefix hi_le
        have hΔi1_pos : 0 < Δ (i + 1) := hΔ_pos_prefix hi1_le
        have hmono_step : Δ (i + 1) ≤ Δ i := hmono (Nat.le_succ i)
        have hdiff :
            (ω / R2) * (Δ i) ^ (2 : ℕ) ≤ Δ i - Δ (i + 1) := by
          linarith [hstep_rec i]
        have hmul_sq :
            ω * (Δ i) ^ (2 : ℕ) ≤ R2 * (Δ i - Δ (i + 1)) := by
          have hmul := mul_le_mul_of_nonneg_left hdiff hR2_nonneg
          simpa [div_eq_mul_inv, hR2_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
        have hmul_prod :
            ω * (Δ i * Δ (i + 1)) ≤ R2 * (Δ i - Δ (i + 1)) := by
          have hleft :
              ω * (Δ i * Δ (i + 1)) ≤ ω * ((Δ i) * Δ i) := by
            gcongr
          calc
            ω * (Δ i * Δ (i + 1)) ≤ ω * (Δ i * Δ i) := hleft
            _ = ω * (Δ i) ^ (2 : ℕ) := by ring
            _ ≤ R2 * (Δ i - Δ (i + 1)) := hmul_sq
        have htmp :
            ω ≤ R2 * ((Δ i - Δ (i + 1)) / (Δ i * Δ (i + 1))) := by
          have hprod_pos : 0 < Δ i * Δ (i + 1) := mul_pos hΔi_pos hΔi1_pos
          have htmp' :
              ω ≤ (R2 * (Δ i - Δ (i + 1))) / (Δ i * Δ (i + 1)) := by
            exact (le_div_iff₀ hprod_pos).2 <|
              by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul_prod
          simpa [mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using htmp'
        have hfrac :
            ω / R2 ≤ (Δ i - Δ (i + 1)) / (Δ i * Δ (i + 1)) := by
          exact (div_le_iff₀ hR2_pos).2 <|
            by simpa [mul_assoc, mul_left_comm, mul_comm] using htmp
        have hrewrite :
            (Δ i - Δ (i + 1)) / (Δ i * Δ (i + 1)) =
              1 / Δ (i + 1) - 1 / Δ i := by
          field_simp [hΔi_pos.ne', hΔi1_pos.ne']
        simpa [hrewrite] using hfrac
      have hrecip_lower :
          ∀ n : ℕ, n ≤ k → 1 / Δ n ≥ 1 / Δ 0 + (n : ℝ) * (ω / R2) := by
        intro n
        induction n with
        | zero =>
            intro _
            simpa
        | succ n ihn =>
            intro hnk
            have hn_le : n ≤ k := Nat.le_trans (Nat.le_succ n) hnk
            have hn_lt : n < k := lt_of_lt_of_le (Nat.lt_succ_self n) hnk
            have hprev := ihn hn_le
            have hstep := hrecip_step n hn_lt
            have hsucc_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
              norm_num
            rw [hsucc_cast]
            linarith
      have hk_lower :
          1 / Δ 0 + (k : ℝ) * (ω / R2) ≤ 1 / Δ k := by
        linarith [hrecip_lower k le_rfl]
      have hsum_pos :
          0 < 1 / Δ 0 + (k : ℝ) * (ω / R2) := by
        have hbase_pos : 0 < 1 / Δ 0 := one_div_pos.mpr hΔ0_pos
        have htail_nonneg : 0 ≤ (k : ℝ) * (ω / R2) := by
          positivity
        linarith
      have hk_inv :
          Δ k ≤ 1 / (1 / Δ 0 + (k : ℝ) * (ω / R2)) := by
        simpa [one_div, hΔk_pos.ne', hsum_pos.ne'] using
          (one_div_le_one_div_of_le hsum_pos hk_lower)
      have hden_pos :
          0 < 2 * R2 + h * (2 - (L : ℝ) * h) * (k : ℝ) * (Δ 0) := by
        have hcoeff_nonneg : 0 ≤ h * (2 - (L : ℝ) * h) := by
          dsimp [ω] at hω_nonneg
          nlinarith
        positivity
      have hmid_rewrite :
          1 / (1 / Δ 0 + (k : ℝ) * (ω / R2)) =
            (Δ 0 * R2) / (R2 + ω * (k : ℝ) * Δ 0) := by
        have hmid_den_pos : 0 < R2 + ω * (k : ℝ) * Δ 0 := by
          positivity
        field_simp [hΔ0_pos.ne', hR2_pos.ne', hsum_pos.ne', hmid_den_pos.ne']
      have hfinal_rewrite :
          (Δ 0 * R2) / (R2 + ω * (k : ℝ) * Δ 0) =
            (2 * Δ 0 * R2) /
              (2 * R2 + h * (2 - (L : ℝ) * h) * (k : ℝ) * Δ 0) := by
        have hden_eq :
            R2 + ω * (k : ℝ) * Δ 0 =
              (2 * R2 + h * (2 - (L : ℝ) * h) * (k : ℝ) * Δ 0) / 2 := by
          dsimp [ω]
          ring
        rw [hden_eq]
        field_simp [hden_pos.ne']
      have hk_final :
          Δ k ≤
            (2 * Δ 0 * R2) /
              (2 * R2 + h * (2 - (L : ℝ) * h) * (k : ℝ) * Δ 0) := by
        calc
          Δ k ≤ 1 / (1 / Δ 0 + (k : ℝ) * (ω / R2)) := hk_inv
          _ = (Δ 0 * R2) / (R2 + ω * (k : ℝ) * Δ 0) := hmid_rewrite
          _ = (2 * Δ 0 * R2) /
                (2 * R2 + h * (2 - (L : ℝ) * h) * (k : ℝ) * Δ 0) := hfinal_rewrite
      simpa [Δ, traj, R2, gradientMethod_zero, mul_assoc, mul_left_comm, mul_comm] using hk_final

end

section

variable [FiniteDimensional ℝ E]

local instance finiteDimensionalComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "p" => normSeminorm ℝ E

/-- Finite-dimensional Chapter 2 specialization of Theorem 2.15: the source-facing notation
`f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` supplies the intrinsic Hilbert-space hypotheses used by
`gradientMethod_objective_gap_le_explicit_rate`. -/
theorem gradientMethod_objective_gap_le_explicit_rate_of_mem_F11
    (hf : f ∈ 𝓕[L, p]¹¹)
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (h : ℝ) (hh_nonneg : 0 ≤ h) (hh_le : h ≤ 2 / (L : ℝ))
    (x0 : E) (k : ℕ) :
    f (gradientMethod (fun _ ↦ h) f x0 k) - f xStar ≤
      (2 * (f x0 - f xStar) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (2 * ‖x0 - xStar‖ ^ (2 : ℕ) +
          h * (2 - (L : ℝ) * h) * (k : ℝ) * (f x0 - f xStar)) :=
  gradientMethod_objective_gap_le_explicit_rate
    hf.convexOn hf.contDiff hf.gradient_lipschitz
    xStar hxStar h hh_nonneg hh_le x0 k

end

end ConvexC1SeminormSmooth
