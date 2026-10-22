/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.3.7 lies in the Chapter 5 self-concordant-barrier / concavity-transform domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div` in `Lemma_5_3_1`, the owner-level
  concavity companion for the exponential transform;
* `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` in `Lemma_5_3_1`, the canonical
  source-facing equivalence between the barrier owner and concavity of `x ↦ exp (-(F x / ν))`;
* `ConvexOn.lower_tangent_plane` in `Chap02/Definition_2_2`, together with mathlib
  `ConcaveOn.neg`, which give the canonical first-order tangent inequality for the concave
  exponential transform by passing to its negative.

Best owner abstraction:
* source-facing: Theorem 5.3.7's logarithmic lower Taylor bound for a standard
  self-concordant function;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div`, followed by the
  first-order tangent inequality for the concave exponential transform.

Primitive data:
* the domain `dom`;
* the function `F`;
* the standard self-concordance owner `hFsc`;
* the positive barrier parameter hypothesis `hν`.

Derived API:
* the barrier owner `IsSelfConcordantBarrierOnWith dom ν F`;
* concavity of `x ↦ exp (-(F x / ν))` on `dom`;
* the source-facing logarithmic lower Taylor bound together with positivity of its logarithm
  argument.

Source/core/bridge triage:
* source-facing: the numbered equivalence in Theorem 5.3.7;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: the exponential-transform concavity criterion from `Lemma_5_3_1`.

This refinement deletes the previous isolated segment-gradient helper lemmas, which had no
downstream users and duplicated the chapter's canonical concavity route. The file now keeps only
the source-facing theorem and states it directly through the existing owner abstraction. -/

-- Proof sketch: apply
-- `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` from Lemma 5.3.1 to replace the
-- barrier condition by concavity of `x ↦ exp (-(F x / ν))`. Pass to the negative function and use
-- the Chapter 2 owner `ConvexOn.lower_tangent_plane` to obtain the affine support bound at `x`;
-- then rewrite the gradient by the chain rule, simplify the exponential factor, and take
-- logarithms after first recording positivity of the logarithm argument. The converse follows by
-- exponentiating the displayed logarithmic inequality to recover the same tangent inequality for
-- the exponential transform, hence concavity, and then invoking the owner equivalence from
-- Lemma 5.3.1.
/-- Helper for Theorem 5.3.7: the negative exponential transform of `F / ν` is `C¹` on the
domain. -/
private lemma neg_exp_neg_div_contDiffOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hFsc : IsStandardSelfConcordantOn dom F) (_hν : 0 < (ν : ℝ)) :
    ContDiffOn ℝ 1 (fun z ↦ -Real.exp (-(F z / (ν : ℝ)))) dom := by
  -- The transform is obtained from `F` by dividing by the positive constant `ν`,
  -- negating, composing with `exp`, and negating again.
  simpa using
    ((((hFsc.contDiffOn.of_le
        (show (1 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞) by norm_num)).div_const (ν : ℝ)).neg).exp).neg

/-- Helper for Theorem 5.3.7: on the open domain, the within-gradient of the negative exponential
transform has the textbook scalar-factor form. -/
private lemma gradientWithin_neg_exp_neg_div_eq
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hFsc : IsStandardSelfConcordantOn dom F) (_hν : 0 < (ν : ℝ))
    {x : E} (hx : x ∈ dom) :
    gradientWithin (fun z ↦ -Real.exp (-(F z / (ν : ℝ)))) dom x =
      ((Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) • ∇ F x) := by
  -- First identify the ambient gradient of the exponential transform by the chain rule.
  have hFx_diff : DifferentiableAt ℝ F x := by
    exact
      (hFsc.contDiffOn.of_le
        (show (1 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞) by norm_num)).contDiffAt
          (hFsc.isOpen_domain.mem_nhds hx) |>.differentiableAt one_ne_zero
  have hgradAt :
      HasGradientAt (fun z ↦ -Real.exp (-(F z / (ν : ℝ))))
        (((Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) • ∇ F x)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hFDeriv :
        HasFDerivAt F (InnerProductSpace.toDual ℝ E (∇ F x)) x := hFx_diff.hasGradientAt.hasFDerivAt
    have hdiv :
        HasFDerivAt (fun z ↦ F z / (ν : ℝ))
          ((1 / (ν : ℝ)) • InnerProductSpace.toDual ℝ E (∇ F x)) x := by
      simpa [div_eq_mul_inv] using hFDeriv.mul_const ((ν : ℝ)⁻¹)
    have hneg_div :
        HasFDerivAt (fun z ↦ -(F z / (ν : ℝ)))
          (-((1 / (ν : ℝ)) • InnerProductSpace.toDual ℝ E (∇ F x))) x := by
      simpa using hdiv.neg
    have hExp :
        HasFDerivAt (fun z ↦ Real.exp (-(F z / (ν : ℝ))))
          (Real.exp (-(F x / (ν : ℝ))) •
            (-((1 / (ν : ℝ)) • InnerProductSpace.toDual ℝ E (∇ F x)))) x := by
      simpa using hneg_div.exp
    -- One final negation turns the derivative into the positive textbook scalar factor.
    simpa [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hExp.neg
  -- On an open domain, the within-gradient agrees with the ambient gradient.
  calc
    gradientWithin (fun z ↦ -Real.exp (-(F z / (ν : ℝ)))) dom x
        = ∇ (fun z ↦ -Real.exp (-(F z / (ν : ℝ)))) x := by
            rw [gradientWithin, gradient]
            congr
            exact fderivWithin_eq_fderiv (hFsc.isOpen_domain.uniqueDiffWithinAt hx)
              hgradAt.differentiableAt
    _ = ((Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) • ∇ F x) := hgradAt.gradient

/-- Helper for Theorem 5.3.7: the tangent-plane inequality for the negative exponential transform
forces positivity of the logarithm argument and yields the logarithmic lower bound. -/
private lemma logarithmic_bound_of_neg_exp_tangent
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hν : 0 < (ν : ℝ)) {x y : E} (_hx : x ∈ dom) (_hy : y ∈ dom)
    (htangent :
      -Real.exp (-(F y / (ν : ℝ))) ≥
        -Real.exp (-(F x / (ν : ℝ))) +
          inner ℝ (((Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) • ∇ F x)) (y - x)) :
    let t := 1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)
    0 < t ∧ F y ≥ F x - (ν : ℝ) * Real.log t := by
  dsimp
  have hν_ne : (ν : ℝ) ≠ 0 := by
    linarith
  have hpair :
      inner ℝ
          (((Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) • ∇ F x)) (y - x) =
        (Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) * inner ℝ (∇ F x) (y - x) := by
    rw [real_inner_smul_left]
  have hfactor :
      Real.exp (-(F x / (ν : ℝ))) *
          (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) =
        Real.exp (-(F x / (ν : ℝ))) -
          (Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) * inner ℝ (∇ F x) (y - x) := by
    field_simp [hν_ne]
  -- Rewrite the tangent inequality as an upper bound on the exponential term at `y`.
  have hraw :
      Real.exp (-(F y / (ν : ℝ))) ≤
        Real.exp (-(F x / (ν : ℝ))) -
          (Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) * inner ℝ (∇ F x) (y - x) := by
    rw [hpair] at htangent
    linarith
  have hexp_le :
      Real.exp (-(F y / (ν : ℝ))) ≤
        Real.exp (-(F x / (ν : ℝ))) *
          (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) := by
    rw [hfactor]
    exact hraw
  -- The positive exponential term forces the logarithm argument to be positive as well.
  have ht_pos :
      0 < 1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x) := by
    by_contra ht_nonpos
    have hprod_nonpos :
        Real.exp (-(F x / (ν : ℝ))) *
            (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) ≤
          0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt ht_nonpos)
    exact (not_le_of_gt (Real.exp_pos _)) (le_trans hexp_le hprod_nonpos)
  -- Taking logarithms now converts the exponential inequality back to the stated bound for `F`.
  refine ⟨ht_pos, ?_⟩
  have hlog :
      -(F y / (ν : ℝ)) ≤
        -(F x / (ν : ℝ)) +
          Real.log (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) := by
    have hlog_raw := Real.log_le_log (Real.exp_pos _) hexp_le
    rw [Real.log_mul (Real.exp_ne_zero _) ht_pos.ne', Real.log_exp] at hlog_raw
    simpa using hlog_raw
  have hfrac :
      F x / (ν : ℝ) -
          Real.log (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) ≤
        F y / (ν : ℝ) := by
    linarith
  have hrewrite :
      (F x - (ν : ℝ) * Real.log
          (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x))) / (ν : ℝ) =
        F x / (ν : ℝ) -
          Real.log (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) := by
    field_simp [hν_ne]
  have hdiv :
      (F x - (ν : ℝ) * Real.log
          (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x))) / (ν : ℝ) ≤
        F y / (ν : ℝ) := by
    rwa [hrewrite]
  exact (div_le_div_iff_of_pos_right hν).mp hdiv

/-- Helper for Theorem 5.3.7: exponentiating the logarithmic lower bound recovers the tangent-plane
inequality for the negative exponential transform. -/
private lemma neg_exp_tangent_of_logarithmic_bound
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hν : 0 < (ν : ℝ)) {x y : E} (_hx : x ∈ dom) (_hy : y ∈ dom)
    (hbound :
      let t := 1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)
      0 < t ∧ F y ≥ F x - (ν : ℝ) * Real.log t) :
    -Real.exp (-(F y / (ν : ℝ))) ≥
      -Real.exp (-(F x / (ν : ℝ))) +
        inner ℝ (((Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) • ∇ F x)) (y - x) := by
  dsimp at hbound ⊢
  rcases hbound with ⟨ht_pos, hFy⟩
  have hν_ne : (ν : ℝ) ≠ 0 := by
    linarith
  have hdiv :
      (F x - (ν : ℝ) * Real.log
          (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x))) / (ν : ℝ) ≤
        F y / (ν : ℝ) := by
    exact div_le_div_of_nonneg_right hFy hν.le
  have hfrac :
      F x / (ν : ℝ) -
          Real.log (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) ≤
        F y / (ν : ℝ) := by
    have hrewrite :
        (F x - (ν : ℝ) * Real.log
            (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x))) / (ν : ℝ) =
          F x / (ν : ℝ) -
            Real.log (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) := by
      field_simp [hν_ne]
    rwa [hrewrite] at hdiv
  have hlog :
      -(F y / (ν : ℝ)) ≤
        -(F x / (ν : ℝ)) +
          Real.log (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) := by
    linarith
  have hexp_le :
      Real.exp (-(F y / (ν : ℝ))) ≤
        Real.exp (-(F x / (ν : ℝ))) *
          (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) := by
    -- Exponentiate the logarithmic inequality to recover the affine support factor.
    calc
      Real.exp (-(F y / (ν : ℝ))) = Real.exp (-(F y / (ν : ℝ))) := by rfl
      _ ≤
          Real.exp
            (-(F x / (ν : ℝ)) +
              Real.log (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x))) := by
            exact Real.exp_le_exp.mpr hlog
      _ =
          Real.exp (-(F x / (ν : ℝ))) *
            (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) := by
            rw [Real.exp_add, Real.exp_log ht_pos]
  have hpair :
      inner ℝ
          (((Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) • ∇ F x)) (y - x) =
        (Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) * inner ℝ (∇ F x) (y - x) := by
    rw [real_inner_smul_left]
  have hfactor :
      Real.exp (-(F x / (ν : ℝ))) *
          (1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)) =
        Real.exp (-(F x / (ν : ℝ))) -
          (Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) * inner ℝ (∇ F x) (y - x) := by
    field_simp [hν_ne]
  rw [hpair]
  have hraw :
      Real.exp (-(F y / (ν : ℝ))) ≤
        Real.exp (-(F x / (ν : ℝ))) -
          (Real.exp (-(F x / (ν : ℝ))) / (ν : ℝ)) * inner ℝ (∇ F x) (y - x) := by
    rw [hfactor] at hexp_le
    exact hexp_le
  linarith

/-- Theorem 5.3.7: for a standard self-concordant function `F`, being a
`ν`-self-concordant barrier is equivalent to the logarithmic lower Taylor bound
`F(y) ≥ F(x) - ν log (1 - ν⁻¹ ⟪∇ F(x), y - x⟫)` on the domain, together with the required
positivity of the logarithm argument. -/
theorem isSelfConcordantBarrierOnWith_iff_logarithmic_taylor_lower_bound
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hFsc : IsStandardSelfConcordantOn dom F) (hν : 0 < (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith dom ν F ↔
      ∀ {x y : E} (hx : x ∈ dom) (hy : y ∈ dom),
        let t := 1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)
        0 < t ∧ F y ≥ F x - (ν : ℝ) * Real.log t := by
  constructor
  · intro hBarrier x y hx hy
    -- Replace the barrier owner by concavity of the exponential transform, then negate it.
    have hconc :
        ConcaveOn ℝ dom (fun z ↦ Real.exp (-(F z / (ν : ℝ)))) :=
      (isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div hFsc hν).1 hBarrier
    have hconv_neg :
        ConvexOn ℝ dom (fun z ↦ -Real.exp (-(F z / (ν : ℝ)))) := by
      refine ⟨hconc.1, ?_⟩
      intro x hx y hy a b ha hb hab
      -- Negating the concave support inequality turns it into convexity of the negative transform.
      have hconc_ineq := hconc.2 hx hy ha hb hab
      simpa [Pi.neg_apply, smul_neg, add_comm, add_left_comm, add_assoc] using
        neg_le_neg hconc_ineq
    have htangent :
        -Real.exp (-(F y / (ν : ℝ))) ≥
          -Real.exp (-(F x / (ν : ℝ))) +
            inner ℝ (gradientWithin (fun z ↦ -Real.exp (-(F z / (ν : ℝ)))) dom x) (y - x) := by
      exact
        hconv_neg.lower_tangent_plane x hx
          ((neg_exp_neg_div_contDiffOn hFsc hν).differentiableOn (by simp) x hx) y hy
    -- Rewrite the within-gradient into the source-side scalar multiple of `∇ F x`.
    rw [gradientWithin_neg_exp_neg_div_eq hFsc hν hx] at htangent
    exact logarithmic_bound_of_neg_exp_tangent hν hx hy htangent
  · intro hbound
    -- Recover the tangent-plane inequality for the negative transform from the logarithmic bound.
    have hconv_neg :
        ConvexOn ℝ dom (fun z ↦ -Real.exp (-(F z / (ν : ℝ)))) := by
      refine
        (convexOn_iff_lower_tangent_plane_of_contDiffOn hFsc.convex_domain
          (neg_exp_neg_div_contDiffOn hFsc hν)).2 ?_
      intro x hx y hy
      have htangent := neg_exp_tangent_of_logarithmic_bound hν hx hy (hbound hx hy)
      rw [gradientWithin_neg_exp_neg_div_eq hFsc hν hx]
      simpa using htangent
    -- Negating back turns convexity of `-exp (-(F/ν))` into the required concavity.
    have hconc :
        ConcaveOn ℝ dom (fun z ↦ Real.exp (-(F z / (ν : ℝ)))) := by
      refine ⟨hconv_neg.1, ?_⟩
      intro x hx y hy a b ha hb hab
      -- Negating the convex inequality for `-exp (-(F/ν))` recovers concavity of `exp (-(F/ν))`.
      have hconv_ineq := hconv_neg.2 hx hy ha hb hab
      simpa [Pi.neg_apply, smul_neg, add_comm, add_left_comm, add_assoc] using
        neg_le_neg hconv_ineq
    exact (isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div hFsc hν).2 hconc

end
