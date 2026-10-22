/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Primary domain: smooth convex objectives on real Hilbert spaces, with a finite-dimensional
Chapter 2 specialization.

Sampled owner-style declarations:
* `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in `Definition_2_2`
* `taylor_upper_bound_of_contDiffOne_withLipschitzGradient` in `Chap01/Lemma_1_5_10`
* `ConvexC1SeminormSmooth.convexOn` / `hasGradientAt` / `gradient_lipschitz` in `Theorem_2_5`
* `gradient_step_value_descent_of_lipschitzGradient` in `Lemma_2_16`

Source/core/bridge triage:
* source-facing: Lemma 2.17, the minimizer-pairing inequality for a smooth convex objective;
* core/canonical: `ConvexOn ℝ Set.univ f`, `∀ x, HasGradientAt f (∇ f x) x`,
  `LipschitzWith L (∇ f)`, and `IsMinOn f Set.univ xStar`;
* bridge/view: the finite-dimensional Chapter 2 notation `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`,
  recovered below as a specialization theorem.

Primitive data:
* whole-space convexity of `f`;
* the ambient gradient witnesses `HasGradientAt f (∇ f x) x`;
* the `L`-Lipschitz bound for `∇ f`;
* a global minimizer `xStar`.

Derived API:
* the local `C¹` bridge from the gradient witness and Lipschitz-gradient hypotheses;
* the quadratic upper tangent bound;
* the gradient quadratic lower bound and its cocoercive consequence;
* the finite-dimensional `𝓕[L, p]¹¹` specialization.

Accordingly, the main public theorem is stated on the intrinsic smooth-convex owner layer
`ConvexOn + HasGradientAt + LipschitzWith`, while `f ∈ 𝓕[L, p]¹¹` is kept only as the direct
finite-dimensional bridge view. -/

namespace ConvexC1SeminormSmooth

section

variable [CompleteSpace E]
variable {L : NNReal} {f : E → ℝ}

private theorem contDiff_one_of_hasGradientAt_lipschitz
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    ContDiff ℝ 1 f := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x ↦ (hgrad x).differentiableAt, ?_⟩
  have hEq : fderiv ℝ f = fun x ↦ InnerProductSpace.toDual ℝ E (∇ f x) := by
    funext x
    simpa using (hgrad x).hasFDerivAt.fderiv
  have hcont : Continuous (fun x ↦ InnerProductSpace.toDual ℝ E (∇ f x)) :=
    (InnerProductSpace.toDual ℝ E).continuous.comp hgrad_lipschitz.continuous
  simpa [hEq] using hcont

private theorem upper_tangent_quadratic_of_hasGradientAt_lipschitz
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (x y : E) :
    f y ≤ f x + inner ℝ (∇ f x) (y - x) + ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  have hfC1 :
      ContDiff ℝ 1 f :=
    contDiff_one_of_hasGradientAt_lipschitz hgrad hgrad_lipschitz
  have hupper :=
    taylor_upper_bound_of_contDiffOne_withLipschitzGradient hfC1 hgrad_lipschitz x y
  simpa [firstOrderTaylorModelAt_apply] using hupper

private theorem gradient_quadratic_lower_bound_of_convex_hasGradientAt_lipschitz
    (hconv : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hL : 0 < L)
    (x y : E) :
    f y + inner ℝ (∇ f y) (x - y) +
        (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) ≤
      f x := by
  let d := ∇ f x - ∇ f y
  let z := x - (1 / (L : ℝ)) • d
  have hupper :
      f z ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    have h :=
      upper_tangent_quadratic_of_hasGradientAt_lipschitz hgrad hgrad_lipschitz x z
    have hz : z - x = -((1 / (L : ℝ)) • d) := by
      simp [z]
    calc
      f z ≤ f x + inner ℝ (∇ f x) (z - x) + ((L : ℝ) / 2) * ‖z - x‖ ^ (2 : ℕ) := h
      _ = f x + inner ℝ (∇ f x) (-((1 / (L : ℝ)) • d)) +
            ((L : ℝ) / 2) * ‖-((1 / (L : ℝ)) • d)‖ ^ (2 : ℕ) := by rw [hz]
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            ((L : ℝ) / 2) * ((1 / (L : ℝ)) ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ)) := by
            simp [inner_smul_right, norm_smul, sq]
            ring
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
            have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
            field_simp [hL0]
  have hlower :
      f z ≥
        f y + inner ℝ (∇ f y) (x - y) -
          (1 / (L : ℝ)) * inner ℝ (∇ f y) d := by
    have h :=
      hconv.lower_tangent_plane_of_hasGradientWithinAt
        y (by simp) (∇ f y) ((hasGradientWithinAt_univ).2 (hgrad y)) z (by simp)
    have hz : z - y = (x - y) - (1 / (L : ℝ)) • d := by
      simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    calc
      f z ≥ f y + inner ℝ (∇ f y) (z - y) := h
      _ = f y + inner ℝ (∇ f y) ((x - y) - (1 / (L : ℝ)) • d) := by rw [hz]
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

/-- Lemma 2.17 on the intrinsic real-Hilbert-space smooth-convex owner layer: if `f` is convex on
the whole space, admits the ambient gradient `∇ f` everywhere, has `L`-Lipschitz gradient, and
`xStar` is a global minimizer, then every point `x` satisfies
`(1 / L) ‖∇ f x‖² ≤ ⟪∇ f x, x - xStar⟫`. The textbook `ℝⁿ` statement is recovered by the
finite-dimensional specialization theorem below. -/
-- Proof sketch: if `0 < L`, first derive the quadratic lower bound `(2.1.10)` from the canonical
-- convex lower-tangent inequality and the quadratic upper Taylor bound coming from the
-- Lipschitz-gradient hypothesis, then add the two orientations to obtain the usual cocoercivity
-- inequality. Since a global minimizer is stationary, specializing that cocoercive bound to
-- `(x, xStar)` yields the result. If `L = 0`, the gradient field is constant, and stationarity at
-- `xStar` forces `∇ f x = 0`.
theorem gradient_pairing_with_minimizer_gap_ge_norm_sq_div
    (hconv : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x : E) :
    (1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x) (x - xStar) := by
  have hgrad0 : ∇ f xStar = 0 := by
    exact
      (isMinOn_hasGradientAt_zero_of_differentiableAt
        (hgrad xStar).differentiableAt hxStar).gradient
  by_cases hL : 0 < L
  · have hxy :=
      gradient_quadratic_lower_bound_of_convex_hasGradientAt_lipschitz
        hconv hgrad hgrad_lipschitz hL x xStar
    have hyx :=
      gradient_quadratic_lower_bound_of_convex_hasGradientAt_lipschitz
        hconv hgrad hgrad_lipschitz hL xStar x
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
    have hpair :
        (1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ) ≤
          inner ℝ (∇ f x) (x - xStar) := by
      have hsum := add_le_add hxy' hyx'
      ring_nf at hsum ⊢
      linarith
    exact hpair
  · have hL0 : L = 0 := le_antisymm (le_of_not_gt hL) bot_le
    have hgrad_eq : ∇ f x = ∇ f xStar := by
      have hdist := hgrad_lipschitz.dist_le_mul x xStar
      have hdist0 : dist (∇ f x) (∇ f xStar) = 0 := by
        apply le_antisymm
        · simpa [hL0] using hdist
        · exact dist_nonneg
      exact eq_of_dist_eq_zero hdist0
    simp [hL0, hgrad_eq, hgrad0]

end

section

variable [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E

local instance lemma17FiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

variable {L : NNReal} {f : E → ℝ}

/-- Finite-dimensional Chapter 2 specialization of Lemma 2.17: the source-facing notation
`f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` supplies the intrinsic owner hypotheses used by
`gradient_pairing_with_minimizer_gap_ge_norm_sq_div`. -/
theorem gradient_pairing_with_minimizer_gap_ge_norm_sq_div_of_mem_F11
    (hf : f ∈ 𝓕[L, p]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x : E) :
    (1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x) (x - xStar) :=
  gradient_pairing_with_minimizer_gap_ge_norm_sq_div
    hf.convexOn hf.hasGradientAt hf.gradient_lipschitz hxStar x

end

end ConvexC1SeminormSmooth
