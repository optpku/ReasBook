/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Owner analysis: this item lies in the projected subgradient / strong-convexity domain on real
inner-product spaces.

Sampled owner-style declarations:
- `IsProjectionPointOn` in `Chap07/Definition_7_3`, the project owner for nearest-point geometry;
- the source-facing notation `∂[Q] f(x)` in `Theorem_3_44`, the chapter owner for real-valued
  relative subgradients;
- `bestFunctionValueUpTo` in `Definition_3_55`, the chapter owner for sampled-prefix minima.

Best owner abstraction:
- source-facing: the projected subgradient complexity bound from the textbook iteration;
- core/canonical: pointwise projection data through `IsProjectionPointOn`, relative
  subgradients through `∂[Q] f(x)`, and sampled best values through `bestFunctionValueUpTo`;
- bridge/view: the explicit total projection map `projQ`, whose values are required to satisfy the
  owner predicate pointwise.

Primitive data:
- the feasible set `Q` and a total update map `projQ`;
- the strongly convex objective `f`, minimizer `xStar`, iterate sequence `xSeq`, and chosen
  subgradient sequence `g`;
- the bounds `μ > 0`, `ε > 0`, the selected-sequence norm bound `‖g_k‖ ≤ M`, and the logarithmic
  budget inequality.

Derived API:
- no local projection wrapper, no local subgradient predicate, and no local sampled-minimum owner;
- the theorem surface is written directly on the chapter/project owners above.

This refinement deletes the parallel local wrappers `IsEuclideanProjectionOn`,
`IsSubgradientWithinAt`, `subdifferentialWithin`, and `sampledBestObjectiveValue`, generalizes the
ambient model from coordinates to the owner-level real inner-product-space setting already used
upstream, and rewrites the theorem to the canonical owner abstractions already present in the
project. -/

/-- Helper for Theorem 3.2.6: a selected relative subgradient is attached to a feasible base
point. -/
lemma mem_of_mem_subdifferentialWithin
    {Q : Set E} {f : E → ℝ} {x g : E}
    (hg : g ∈ ∂[Q] f(x)) :
    x ∈ Q := by
  -- Unpack the owner characterization of relative subgradients to recover feasibility.
  exact (mem_subdifferentialWithin_iff.mp hg).1

/-- Helper for Theorem 3.2.6: strong convexity specialized at a feasible comparison point gives
the textbook gap-plus-quadratic lower bound against a selected subgradient. -/
lemma gap_add_quadratic_le_inner_subgradient_sub
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hf : StrongConvexOn Q μ f)
    {x xStar g : E}
    (hg : g ∈ ∂[Q] f(x))
    (hxStar_mem : xStar ∈ Q) :
    f x - f xStar + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤ inner ℝ g (x - xStar) := by
  -- Specialize the strong-convexity lower bound at the feasible comparison point `xStar`.
  have hbound := hf.lower_bound_of_mem_subdifferentialWithin hg hxStar_mem
  have hinner : inner ℝ g (xStar - x) = -inner ℝ g (x - xStar) := by
    rw [show xStar - x = -(x - xStar) by abel_nf, inner_neg_right]
  have hbound' :
      f xStar ≥ f x - inner ℝ g (x - xStar) + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    simpa [hinner, norm_sub_rev] using hbound
  linarith

/-- Helper for Theorem 3.2.6: the function-value gap is bounded by the subgradient norm times the
distance to the comparison point. -/
lemma gap_le_subgradient_norm_mul_dist
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hf : StrongConvexOn Q μ f)
    {x xStar g : E}
    (hg : g ∈ ∂[Q] f(x))
    (hxStar_mem : xStar ∈ Q) :
    f x - f xStar ≤ ‖g‖ * ‖x - xStar‖ := by
  -- Bound the inner product by Cauchy-Schwarz and discard the nonnegative quadratic term.
  have hgap := gap_add_quadratic_le_inner_subgradient_sub hf hg hxStar_mem
  have hinner : inner ℝ g (x - xStar) ≤ ‖g‖ * ‖x - xStar‖ := by
    simpa using real_inner_le_norm g (x - xStar)
  have hquad_nonneg : 0 ≤ (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    have hsq_nonneg : 0 ≤ ‖x - xStar‖ ^ (2 : ℕ) := by positivity
    nlinarith
  linarith

/-- Helper for Theorem 3.2.6: the strong-convexity gap estimate implies the denominator control
`2 μ gap ≤ ‖g‖²` used in the contraction factor. -/
lemma two_mul_mu_gap_le_subgradient_norm_sq
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hμ : 0 < μ)
    (hf : StrongConvexOn Q μ f)
    {x xStar g : E}
    (hg : g ∈ ∂[Q] f(x))
    (hxStar_mem : xStar ∈ Q) :
    2 * μ * (f x - f xStar) ≤ ‖g‖ ^ (2 : ℕ) := by
  -- First combine the strong-convexity gap estimate with Cauchy-Schwarz.
  have hmain := gap_add_quadratic_le_inner_subgradient_sub hf hg hxStar_mem
  have hinner : inner ℝ g (x - xStar) ≤ ‖g‖ * ‖x - xStar‖ := by
    simpa using real_inner_le_norm g (x - xStar)
  have hbound :
      f x - f xStar + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤
        ‖g‖ * ‖x - xStar‖ := by
    exact hmain.trans hinner
  have hbound' :
      f x - f xStar ≤
        ‖g‖ * ‖x - xStar‖ - (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    linarith
  -- Optimize the quadratic upper envelope `a r - (μ / 2) r² ≤ a² / (2 μ)`.
  have hμ2_nonneg : 0 ≤ 2 * μ := by nlinarith
  have hmul :
      2 * μ * (f x - f xStar) ≤
        2 * μ * (‖g‖ * ‖x - xStar‖ - (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hbound' hμ2_nonneg
  have henvelope :
      2 * μ * (‖g‖ * ‖x - xStar‖ - (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) ≤
        ‖g‖ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (‖g‖ - μ * ‖x - xStar‖)]
  exact hmul.trans henvelope

/-- Helper for Theorem 3.2.6: projection geometry bounds the squared distance after the projected
subgradient step by the squared distance to the explicit pre-projection point. -/
lemma projection_step_sqdist_le_preprojection_sqdist
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    (projQ : E → E)
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x))
    {xStar : E} (hxStar_mem : xStar ∈ Q)
    {xSeq g : ℕ → E} {ε : ℝ}
    (hxSeq_succ :
      ∀ k : ℕ,
        xSeq (k + 1) =
          projQ (xSeq k - ((2 * ε) / ‖g k‖ ^ (2 : ℕ)) • g k))
    (k : ℕ) :
    ‖xSeq (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      ‖(xSeq k - ((2 * ε) / ‖g k‖ ^ (2 : ℕ)) • g k) - xStar‖ ^ (2 : ℕ) := by
  let y : E := xSeq k - ((2 * ε) / ‖g k‖ ^ (2 : ℕ)) • g k
  -- Apply the Pythagorean inequality at the explicit pre-projection point `y`.
  have hpyth :
      ‖xStar - projQ y‖ ^ (2 : ℕ) + ‖projQ y - y‖ ^ (2 : ℕ) ≤
        ‖xStar - y‖ ^ (2 : ℕ) :=
    IsProjectionPointOn.pythagorean_ineq hQ_convex (hproj y) hxStar_mem
  have hdist :
      ‖xStar - projQ y‖ ^ (2 : ℕ) ≤ ‖xStar - y‖ ^ (2 : ℕ) := by
    nlinarith
  -- Rewrite both sides back to the textbook iterate notation.
  simpa [y, hxSeq_succ k, norm_sub_rev] using hdist

/-- Helper for Theorem 3.2.6: whenever the current objective gap is still larger than `ε`, one
projected subgradient step contracts the squared distance to the minimizer by the uniform
exponential factor determined by `μ`, `ε`, and `M`. -/
lemma sqdist_contraction_of_bad_gap
    {Q : Set E} {f : E → ℝ} {μ M ε : ℝ}
    (hμ : 0 < μ) (hε : 0 < ε)
    (hf : StrongConvexOn Q μ f)
    (projQ : E → E)
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x))
    {xStar : E} (hxStar_mem : xStar ∈ Q)
    {xSeq g : ℕ → E}
    (hsubgrad : ∀ k : ℕ, g k ∈ ∂[Q] f((xSeq k)))
    (hsubgrad_norm : ∀ k : ℕ, ‖g k‖ ≤ M)
    (hxSeq_succ :
      ∀ k : ℕ,
        xSeq (k + 1) =
          projQ (xSeq k - ((2 * ε) / ‖g k‖ ^ (2 : ℕ)) • g k))
    (hM_pos : 0 < M)
    {k : ℕ}
    (hbadk : f (xSeq k) > f xStar + ε) :
    ‖xSeq (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      Real.exp (-(2 * μ * ε / M ^ (2 : ℕ))) * ‖xSeq k - xStar‖ ^ (2 : ℕ) := by
  have hg_mem : g k ∈ ∂[Q] f((xSeq k)) := hsubgrad k
  have hdist_le :=
    projection_step_sqdist_le_preprojection_sqdist hf.1 projQ hproj hxStar_mem hxSeq_succ k
  have hgap_quad :
      f (xSeq k) - f xStar + (μ / 2) * ‖xSeq k - xStar‖ ^ (2 : ℕ) ≤
        inner ℝ (xSeq k - xStar) (g k) := by
    -- Rewrite the generic strong-convexity gap inequality into the current iterate orientation.
    simpa [real_inner_comm] using
      gap_add_quadratic_le_inner_subgradient_sub hf hg_mem hxStar_mem
  have hgap_eps : ε < f (xSeq k) - f xStar := by
    linarith
  have hstep_norm_sq_pos : 0 < ‖g k‖ ^ (2 : ℕ) := by
    have hgap_norm :=
      two_mul_mu_gap_le_subgradient_norm_sq hμ hf hg_mem hxStar_mem
    have hgap_pos : 0 < f (xSeq k) - f xStar := by
      linarith
    have hnum_pos : 0 < 2 * μ * (f (xSeq k) - f xStar) := by positivity
    exact lt_of_lt_of_le hnum_pos hgap_norm
  have hstep_norm_sq_ne : ‖g k‖ ^ (2 : ℕ) ≠ 0 := ne_of_gt hstep_norm_sq_pos
  let α : ℝ := (2 * ε) / ‖g k‖ ^ (2 : ℕ)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity
  have hexpand :
      ‖(xSeq k - α • g k) - xStar‖ ^ (2 : ℕ) =
        ‖xSeq k - xStar‖ ^ (2 : ℕ) -
          2 * α * inner ℝ (xSeq k - xStar) (g k) +
          α ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) := by
    -- Expand the explicit squared norm of the pre-projection displacement.
    calc
      ‖(xSeq k - α • g k) - xStar‖ ^ (2 : ℕ)
          = ‖(xSeq k - xStar) - α • g k‖ ^ (2 : ℕ) := by
              congr 1
              abel_nf
      _ = ‖xSeq k - xStar‖ ^ (2 : ℕ) -
            2 * inner ℝ (xSeq k - xStar) (α • g k) +
            ‖α • g k‖ ^ (2 : ℕ) := by
            simpa using norm_sub_sq_real (xSeq k - xStar) (α • g k)
      _ = ‖xSeq k - xStar‖ ^ (2 : ℕ) -
            2 * α * inner ℝ (xSeq k - xStar) (g k) +
            α ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) := by
            rw [real_inner_smul_right]
            rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
            ring
  have hscaled_gap :
      α * μ * ‖xSeq k - xStar‖ ^ (2 : ℕ) +
          α ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) ≤
        2 * α * inner ℝ (xSeq k - xStar) (g k) := by
    have hscaled0 :=
      mul_le_mul_of_nonneg_left hgap_quad (by positivity : 0 ≤ 2 * α)
    have halpha_eps :
        α ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) = 2 * α * ε := by
      dsimp [α]
      field_simp [hstep_norm_sq_ne]
    have hscaled_eps :
        2 * α * ε ≤ 2 * α * (f (xSeq k) - f xStar) := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hgap_eps) (by positivity : 0 ≤ 2 * α)
    rw [halpha_eps]
    linarith
  have hraw_contraction :
      ‖(xSeq k - α • g k) - xStar‖ ^ (2 : ℕ) ≤
        (1 - α * μ) * ‖xSeq k - xStar‖ ^ (2 : ℕ) := by
    rw [hexpand]
    nlinarith [hscaled_gap]
  have hnorm_sq_le : ‖g k‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
    simpa [pow_two] using
      (sq_le_sq₀ (norm_nonneg _) hM_pos.le).2 (hsubgrad_norm k)
  have hcoef_bound :
      2 * μ * ε / M ^ (2 : ℕ) ≤ α * μ := by
    have hrecip :
        1 / M ^ (2 : ℕ) ≤ 1 / ‖g k‖ ^ (2 : ℕ) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact hnorm_sq_le
    have hmul :=
      mul_le_mul_of_nonneg_left hrecip (by positivity : 0 ≤ 2 * μ * ε)
    dsimp [α] at *
    simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hcoef_exp :
      1 - α * μ ≤ Real.exp (-(2 * μ * ε / M ^ (2 : ℕ))) := by
    have hcoef_mono :
        1 - α * μ ≤ 1 - 2 * μ * ε / M ^ (2 : ℕ) := by
      linarith
    exact hcoef_mono.trans (Real.one_sub_le_exp_neg _)
  have hraw_exp :
      ‖(xSeq k - α • g k) - xStar‖ ^ (2 : ℕ) ≤
        Real.exp (-(2 * μ * ε / M ^ (2 : ℕ))) * ‖xSeq k - xStar‖ ^ (2 : ℕ) := by
    have hdist_sq_nonneg : 0 ≤ ‖xSeq k - xStar‖ ^ (2 : ℕ) := by positivity
    exact hraw_contraction.trans <|
      mul_le_mul_of_nonneg_right hcoef_exp hdist_sq_nonneg
  -- Reinsert the projection step after bounding the explicit raw update.
  have hrewrite :
      ‖(xSeq k - α • g k) - xStar‖ ^ (2 : ℕ) =
        ‖(xSeq k - ((2 * ε) / ‖g k‖ ^ (2 : ℕ)) • g k) - xStar‖ ^ (2 : ℕ) := by
    simp [α]
  have hdist_le' :
      ‖xSeq (k + 1) - xStar‖ ^ (2 : ℕ) ≤
        ‖(xSeq k - α • g k) - xStar‖ ^ (2 : ℕ) := by
    simpa [hrewrite] using hdist_le
  exact hdist_le'.trans hraw_exp

/-- Helper for Theorem 3.2.6: if every sampled iterate up to time `N` stays more than `ε` above
the optimum, then the squared distances to the minimizer decay exponentially along that whole bad
prefix. -/
lemma sqdist_exponential_decay_of_bad_prefix
    {Q : Set E} {f : E → ℝ} {μ M ε : ℝ}
    (hμ : 0 < μ) (hε : 0 < ε)
    (hf : StrongConvexOn Q μ f)
    (projQ : E → E)
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x))
    {xStar : E} (hxStar_mem : xStar ∈ Q)
    {xSeq g : ℕ → E}
    (hsubgrad : ∀ k : ℕ, g k ∈ ∂[Q] f((xSeq k)))
    (hsubgrad_norm : ∀ k : ℕ, ‖g k‖ ≤ M)
    (hxSeq_succ :
      ∀ k : ℕ,
        xSeq (k + 1) =
          projQ (xSeq k - ((2 * ε) / ‖g k‖ ^ (2 : ℕ)) • g k))
    {N : ℕ}
    (hM_pos : 0 < M)
    (hbad : ∀ j : Fin (N + 1), f (xSeq j) > f xStar + ε) :
    ∀ m : ℕ, m ≤ N →
      ‖xSeq m - xStar‖ ^ (2 : ℕ) ≤
        Real.exp (-(2 * μ * ε / M ^ (2 : ℕ)) * (m : ℝ)) *
          ‖xSeq 0 - xStar‖ ^ (2 : ℕ) := by
  let c : ℝ := (2 * μ * ε) / M ^ (2 : ℕ)
  intro m hm
  induction m with
  | zero =>
      -- The initial iterate matches the claimed exponential bound because `exp 0 = 1`.
      simp
  | succ m ih =>
      have hmN : m ≤ N := Nat.le_of_succ_le hm
      have hbadm : f (xSeq m) > f xStar + ε :=
        hbad ⟨m, Nat.lt_succ_iff.mpr hmN⟩
      have hstep :
          ‖xSeq (m + 1) - xStar‖ ^ (2 : ℕ) ≤
            Real.exp (-c) * ‖xSeq m - xStar‖ ^ (2 : ℕ) := by
        simpa [c] using
          sqdist_contraction_of_bad_gap hμ hε hf projQ hproj hxStar_mem
            hsubgrad hsubgrad_norm hxSeq_succ hM_pos hbadm
      have hprev' :
          ‖xSeq m - xStar‖ ^ (2 : ℕ) ≤
            Real.exp (-(c * (m : ℝ))) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ) := by
        simpa [c] using ih hmN
      have hprev := ih hmN
      have hcombine :
          ‖xSeq (m + 1) - xStar‖ ^ (2 : ℕ) ≤
            Real.exp (-c) *
              (Real.exp (-(c * (m : ℝ))) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ)) := by
        exact hstep.trans (mul_le_mul_of_nonneg_left hprev' (by positivity : 0 ≤ Real.exp (-c)))
      have hexp_factor :
          Real.exp (-c) * Real.exp (-(c * (m : ℝ))) =
            Real.exp (-(c * ((m + 1 : ℕ) : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
      calc
        ‖xSeq (m + 1) - xStar‖ ^ (2 : ℕ)
            ≤ Real.exp (-c) *
                (Real.exp (-(c * (m : ℝ))) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ)) := hcombine
        _ = (Real.exp (-c) * Real.exp (-(c * (m : ℝ)))) *
              ‖xSeq 0 - xStar‖ ^ (2 : ℕ) := by ring
        _ = Real.exp (-(c * ((m + 1 : ℕ) : ℝ))) *
              ‖xSeq 0 - xStar‖ ^ (2 : ℕ) := by rw [hexp_factor]
        _ = Real.exp (-(2 * μ * ε / M ^ (2 : ℕ)) * (((m + 1 : ℕ) : ℝ))) *
              ‖xSeq 0 - xStar‖ ^ (2 : ℕ) := by
              congr 1
              dsimp [c]
              ring_nf

/-- Helper for Theorem 3.2.6: the logarithmic iteration budget converts the exponential decay
factor into the reciprocal square ratio appearing in the final objective-gap estimate. -/
lemma exp_neg_scaled_budget_le_ratio_sq
    {μ M ε dist : ℝ}
    (hμ : 0 < μ) (hε : 0 < ε) (hM : 0 < M) (hdist : 0 < dist)
    {N : ℕ}
    (hN :
      (N : ℝ) ≥ (M ^ (2 : ℕ)) / (μ * ε) * Real.log (M * dist / ε)) :
    Real.exp (-(((2 * μ * ε) / M ^ (2 : ℕ)) * (N : ℝ))) ≤
      ε ^ (2 : ℕ) / (M ^ (2 : ℕ) * dist ^ (2 : ℕ)) := by
  let c : ℝ := (2 * μ * ε) / M ^ (2 : ℕ)
  let arg : ℝ := M * dist / ε
  have harg_pos : 0 < arg := by
    -- The logarithm and reciprocal-square rewrite need positivity of the initial ratio.
    dsimp [arg]
    positivity
  have hN' :
      (M ^ (2 : ℕ)) / (μ * ε) * Real.log arg ≤ (N : ℝ) := by
    simpa [arg] using hN
  have hbudget_scaled :
      2 * Real.log arg ≤ c * (N : ℝ) := by
    -- Multiply the budget inequality by the contraction coefficient to isolate `2 log arg`.
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      positivity
    have hscaled := mul_le_mul_of_nonneg_left hN' hc_nonneg
    have hleft_eq :
        c * ((M ^ (2 : ℕ)) / (μ * ε) * Real.log arg) = 2 * Real.log arg := by
      dsimp [c]
      field_simp [hμ.ne', hε.ne', hM.ne']
    simpa [hleft_eq, mul_comm] using hscaled
  calc
    Real.exp (-(c * (N : ℝ)))
        ≤ Real.exp (-(2 * Real.log arg)) := by
            -- Monotonicity of `exp` turns the budget bound into an exponential estimate.
            apply Real.exp_le_exp.mpr
            linarith
    _ = ε ^ (2 : ℕ) / (M ^ (2 : ℕ) * dist ^ (2 : ℕ)) := by
          -- Rewrite the exponential of a logarithm into the reciprocal square of the ratio.
          have hexp_arg :
              Real.exp (-(2 * Real.log arg)) = arg⁻¹ ^ (2 : ℕ) := by
            rw [show -(2 * Real.log arg) = ((2 : ℕ) : ℝ) * (-Real.log arg) by ring]
            rw [Real.exp_nat_mul]
            simp [Real.exp_neg, Real.exp_log harg_pos]
          rw [hexp_arg]
          dsimp [arg]
          field_simp [pow_two, hM.ne', hε.ne', hdist.ne']

-- Proof sketch: use the strong-convexity lower bound for subgradients to derive the textbook
-- one-step contraction
-- `‖x_{k+1} - xStar‖² ≤ (1 - 2 * μ * ε / ‖g_k‖²) * ‖x_k - xStar‖²`
-- whenever `f (x_k) > f xStar + ε`. The uniform bound `‖g_k‖ ≤ M` turns this into exponential
-- decay of the distances to `xStar`. If every sampled value up to time `N` were still larger
-- than `f xStar + ε`, the resulting estimate for `f (x_N) - f xStar` would contradict the
-- logarithmic lower bound on `N`, so the sampled minimum must already satisfy the claimed
-- accuracy bound.
/-- Theorem 3.2.6: for the projected subgradient iteration
`x_{k+1} = π_Q (x_k - (2 ε / ‖g_k‖²) • g_k)` on a `μ`-strongly convex objective over the convex
feasible set `Q` in a real inner-product space, if every chosen relative subgradient
`g_k ∈ ∂[Q] f(x_k)` has norm at most `M`
and the iteration budget `N` satisfies
`N ≥ (M² / (μ ε)) log (M ‖xSeq 0 - x*‖ / ε)`, then the sampled best value
`bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N` is at most `ε` above the optimal value
`f xStar`. The minimizer hypothesis is paired with the explicit feasibility assumption
`xStar ∈ Q`; `g_k ∈ ∂[Q] f(x_k)` already forces `x_k ∈ Q`, so no separate feasibility assumption on
`x₀` is needed in the public API. The logarithmic budget is stated directly in terms of the
canonically determined initial iterate `xSeq 0`. -/
theorem bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn
    {Q : Set E} (projQ : E → E)
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x))
    {f : E → ℝ} {μ M ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε)
    (hf : StrongConvexOn Q μ f)
    {xStar : E} (hxStar : IsMinOn f Q xStar)
    (hxStar_mem : xStar ∈ Q)
    (xSeq g : ℕ → E)
    (hsubgrad : ∀ k : ℕ, g k ∈ ∂[Q] f((xSeq k)))
    (hsubgrad_norm : ∀ k : ℕ, ‖g k‖ ≤ M)
    (hxSeq_succ :
      ∀ k : ℕ,
        xSeq (k + 1) =
          projQ (xSeq k - ((2 * ε) / ‖g k‖ ^ (2 : ℕ)) • g k))
    {N : ℕ}
    (hN :
      (N : ℝ) ≥ (M ^ (2 : ℕ)) / (μ * ε) * Real.log (M * ‖xSeq 0 - xStar‖ / ε)) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N ≤ f xStar + ε := by
  by_cases hgood : ∃ j : Fin (N + 1), f (xSeq j) ≤ f xStar + ε
  · -- If one sampled iterate is already good, the sampled minimum is no larger.
    rcases hgood with ⟨j, hj⟩
    exact (bestFunctionValueUpTo_le j).trans hj
  · -- Otherwise every sampled iterate stays bad, so we run the textbook contradiction route.
    have hbad : ∀ j : Fin (N + 1), f (xSeq j) > f xStar + ε := by
      intro j
      have hj_not : ¬ f (xSeq j) ≤ f xStar + ε := by
        intro hj
        exact hgood ⟨j, hj⟩
      exact lt_of_not_ge hj_not
    have hM_nonneg : 0 ≤ M := by
      exact le_trans (norm_nonneg _) (hsubgrad_norm 0)
    have hbad0 : f (xSeq 0) > f xStar + ε := hbad ⟨0, Nat.succ_pos _⟩
    have hgap0_eps : ε < f (xSeq 0) - f xStar := by
      linarith
    have hM_pos : 0 < M := by
      have hgap0_norm :=
        two_mul_mu_gap_le_subgradient_norm_sq hμ hf (hsubgrad 0) hxStar_mem
      have hnorm_sq_le0 : ‖g 0‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
        simpa [pow_two] using
          (sq_le_sq₀ (norm_nonneg _) hM_nonneg).2 (hsubgrad_norm 0)
      have hlower_pos : 0 < 2 * μ * ε := by positivity
      have hupper_pos : 0 < M ^ (2 : ℕ) := by
        have hgap0_pos : 0 < f (xSeq 0) - f xStar := by
          linarith
        have hmid : 0 < 2 * μ * (f (xSeq 0) - f xStar) := by positivity
        have hnorm_sq_pos : 0 < ‖g 0‖ ^ (2 : ℕ) := lt_of_lt_of_le hmid hgap0_norm
        exact lt_of_lt_of_le hnorm_sq_pos hnorm_sq_le0
      nlinarith
    have hgap0_le :
        f (xSeq 0) - f xStar ≤ M * ‖xSeq 0 - xStar‖ := by
      have hgap0 :=
        gap_le_subgradient_norm_mul_dist hμ.le hf (hsubgrad 0) hxStar_mem
      exact hgap0.trans <|
        mul_le_mul_of_nonneg_right (hsubgrad_norm 0) (norm_nonneg _)
    have hdist0_pos : 0 < ‖xSeq 0 - xStar‖ := by
      by_contra hdist0_nonpos
      have hdist0_eq : ‖xSeq 0 - xStar‖ = 0 := by
        exact le_antisymm (le_of_not_gt hdist0_nonpos) (norm_nonneg _)
      have : ε < 0 := by
        exact (lt_of_lt_of_le hgap0_eps hgap0_le).trans_eq (by simp [hdist0_eq])
      linarith
    let c : ℝ := (2 * μ * ε) / M ^ (2 : ℕ)
    have hsqdistN :
        ‖xSeq N - xStar‖ ^ (2 : ℕ) ≤
          Real.exp (-(c * (N : ℝ))) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ) := by
      simpa [c] using
        sqdist_exponential_decay_of_bad_prefix hμ hε hf projQ hproj hxStar_mem
          hsubgrad hsubgrad_norm hxSeq_succ hM_pos hbad N le_rfl
    have hexp_bound :
        Real.exp (-(c * (N : ℝ))) ≤
          ε ^ (2 : ℕ) / (M ^ (2 : ℕ) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ)) := by
      -- Use the extracted scalar helper to convert the logarithmic budget into the final ratio.
      simpa [c] using
        exp_neg_scaled_budget_le_ratio_sq hμ hε hM_pos hdist0_pos hN
    have hxN_mem : xSeq N ∈ Q := mem_of_mem_subdifferentialWithin (hsubgrad N)
    have hgapN_nonneg : 0 ≤ f (xSeq N) - f xStar := by
      exact sub_nonneg.mpr (hxStar hxN_mem)
    have hgapN_le :
        f (xSeq N) - f xStar ≤ M * ‖xSeq N - xStar‖ := by
      have hgapN :=
        gap_le_subgradient_norm_mul_dist hμ.le hf (hsubgrad N) hxStar_mem
      exact hgapN.trans <|
        mul_le_mul_of_nonneg_right (hsubgrad_norm N) (norm_nonneg _)
    have hgapN_sq :
        (f (xSeq N) - f xStar) ^ (2 : ℕ) ≤
          M ^ (2 : ℕ) * ‖xSeq N - xStar‖ ^ (2 : ℕ) := by
      have hsq :=
        (sq_le_sq₀ hgapN_nonneg (mul_nonneg hM_nonneg (norm_nonneg _))).2 hgapN_le
      simpa [pow_two, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hsq
    have hdistN_sq :
        M ^ (2 : ℕ) * ‖xSeq N - xStar‖ ^ (2 : ℕ) ≤
          M ^ (2 : ℕ) *
            (Real.exp (-(c * (N : ℝ))) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hsqdistN (by positivity : 0 ≤ M ^ (2 : ℕ))
    have hbudget_sq :
        M ^ (2 : ℕ) *
            (Real.exp (-(c * (N : ℝ))) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ)) ≤
          ε ^ (2 : ℕ) := by
      have hscaled :=
        mul_le_mul_of_nonneg_left hexp_bound
          (by positivity : 0 ≤ M ^ (2 : ℕ) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ))
      have hright_eq :
          (M ^ (2 : ℕ) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ)) *
              (ε ^ (2 : ℕ) / (M ^ (2 : ℕ) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ))) =
            ε ^ (2 : ℕ) := by
        field_simp [pow_two, hM_pos.ne', hdist0_pos.ne']
      have hleft_eq :
          (M ^ (2 : ℕ) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ)) *
              Real.exp (-(c * (N : ℝ))) =
            M ^ (2 : ℕ) *
              (Real.exp (-(c * (N : ℝ))) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ)) := by
        ring
      calc
        M ^ (2 : ℕ) * (Real.exp (-(c * (N : ℝ))) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ))
            = (M ^ (2 : ℕ) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ)) *
                Real.exp (-(c * (N : ℝ))) := by rw [← hleft_eq]
        _ ≤ (M ^ (2 : ℕ) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ)) *
              (ε ^ (2 : ℕ) / (M ^ (2 : ℕ) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ))) := hscaled
        _ = ε ^ (2 : ℕ) := hright_eq
    have hgapN_sq_le_eps :
        (f (xSeq N) - f xStar) ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) :=
      hgapN_sq.trans (hdistN_sq.trans hbudget_sq)
    have hgapN_le_eps : f (xSeq N) - f xStar ≤ ε := by
      exact (sq_le_sq₀ hgapN_nonneg hε.le).1 (by simpa [pow_two] using hgapN_sq_le_eps)
    have hbadN : f (xSeq N) > f xStar + ε := hbad ⟨N, Nat.lt_succ_self _⟩
    linarith

end
