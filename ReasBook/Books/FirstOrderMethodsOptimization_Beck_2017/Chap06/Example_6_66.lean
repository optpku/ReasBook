/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Corollary_6_64
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_54
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Pointwise
open AffineMap

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Example 6.66 is `source-facing`: the textbook computes the proximal operator of the scaled
Huber function `λ H[μ]`. Domain sampling in the chapter identifies the correct owner chain:

- `prox_scaled_moreau_envelope_eq_singleton_of_scaled_prox_eq_singleton` from
  Corollary 6.64 is the `core/canonical` proximal formula for scaled Moreau envelopes;
- `moreau_envelope_norm_penalty_eq_huber_function` from Example 6.54 is the
  `bridge/view` identifying the Huber owner with the Moreau envelope of `norm_penalty 1`;
- `prox_norm_penalty_eq_singleton_shrinkage` from Example 6.19 is the source-facing singleton
  formula for the scaled norm penalty appearing on the right-hand side of Corollary 6.64.

The primitive data are only `μ`, `λ`, and `x`. The Huber identity and the radial shrinkage
formula are already derived upstream, so this file should specialize those owners rather than keep
a parallel local proximal computation. -/

-- Proof sketch: if `λ = 0`, the left side is the proximal mapping of the zero function and the
-- right side simplifies to `{x}`. For `λ > 0`, identify `H[μ]` with the Moreau envelope of the
-- norm from the earlier Huber-envelope computation, then apply the scaled Moreau-envelope
-- proximal formula and the explicit shrinkage formula for the norm penalty. Simplifying the
-- affine combination yields the factor `1 - λ / max ‖x‖ (μ + λ)`.
/-- Example 6.66: if `μ` is positive and `λ ≥ 0`, then the proximal set of the scaled Huber function
`λ H[μ]` at `x` is the singleton obtained by radial shrinkage with denominator
`max ‖x‖ (μ + λ)`. This is the chapter's set-valued rendering of the textbook formula
`prox_{λ H_μ}(x) = (1 - λ / max {‖x‖, μ + λ}) x`, including the endpoint `λ = 0`, in the real
inner-product-space setting where Example 6.19 and Example 6.54 apply. -/
theorem prox_scaled_huber_function_eq_singleton_shrinkage
    (μ : PosReal) (lam : ℝ) (hlam : 0 ≤ lam) (x : E) :
    prox[fun y : E ↦ ((lam * H[μ] y : ℝ) : EReal)] x =
      {(1 - lam / max ‖x‖ (μ + lam)) • x} := by
  by_cases hzero : lam = 0
  · subst hzero
    simpa using prox_zero_eq_singleton x
  · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hzero)
    let lamPos : PosReal := ⟨lam, hlam_pos⟩
    have hnorm_ne_bot : ∀ y : E, norm_penalty 1 y ≠ ⊥ := by
      intro y
      simp [norm_penalty]
    have hnorm_proper : IsProperExtendedRealFunction (norm_penalty 1 : E → EReal) := by
      refine ⟨hnorm_ne_bot, ?_⟩
      refine ⟨0, ?_⟩
      rw [mem_effective_domain]
      simp [norm_penalty]
    have hnorm_closed : LowerSemicontinuous (norm_penalty 1 : E → EReal) := by
      have hclosed_epigraph : IsClosed {p : E × ℝ | ‖p.1‖ ≤ p.2} := by
        exact isClosed_le (continuous_norm.comp continuous_fst) continuous_snd
      have hclosed_realEpigraph : IsClosed (realEpigraph (norm_penalty 1 : E → EReal)) := by
        simpa [realEpigraph, norm_penalty] using hclosed_epigraph
      exact
        (lowerSemicontinuous_iff_isClosed_real_epigraph (norm_penalty 1 : E → EReal)).2
          hclosed_realEpigraph
    have hnorm_convex : is_convex_function (norm_penalty 1 : E → EReal) := by
      rw [is_convex_function]
      -- The real epigraph of `norm_penalty 1` is the ordinary epigraph of the norm.
      have hnorm : ConvexOn ℝ Set.univ (fun y : E ↦ ‖y‖) :=
        convexOn_norm convex_univ
      have hepigraph : Convex ℝ {p : E × ℝ | p.1 ∈ Set.univ ∧ ‖p.1‖ ≤ p.2} :=
        hnorm.convex_epigraph
      simpa [realEpigraph, norm_penalty] using hepigraph
    have hscaled_norm :
        prox[(((μ + lamPos : ℝ) : EReal) • norm_penalty 1)] x =
          {lineMap x 0 (((μ + lamPos : ℝ) / max ‖x‖ (μ + lamPos : ℝ)))} := by
      have hμlam_pos : 0 < (μ + lamPos : ℝ) := add_pos μ.2 lamPos.2
      calc
        prox[(((μ + lamPos : ℝ) : EReal) • norm_penalty 1)] x
            = prox[norm_penalty (μ + lamPos : ℝ)] x := by
                refine congrArg (fun f : E → EReal ↦ prox[f] x) ?_
                ext y
                simp [norm_penalty, smul_eq_mul]
        _ = {(1 - (μ + lamPos : ℝ) / max ‖x‖ (μ + lamPos : ℝ)) • x} := by
              simpa using
                prox_norm_penalty_eq_singleton_shrinkage (μ + lamPos : ℝ) hμlam_pos x
        _ = {lineMap x 0 (((μ + lamPos : ℝ) / max ‖x‖ (μ + lamPos : ℝ)))} := by
              simp [AffineMap.lineMap_apply_module]
    have hscaled_huber :
        prox[fun y : E ↦ ((lam * H[μ] y : ℝ) : EReal)] x =
          prox[((lamPos : ℝ) : EReal) • M[μ, norm_penalty 1]] x := by
      refine congrArg (fun f : E → EReal ↦ prox[f] x) ?_
      ext y
      rw [Pi.smul_apply, show M[μ, norm_penalty 1] y = ((H[μ] y : ℝ) : EReal) from
        congrFun (moreau_envelope_norm_penalty_eq_huber_function μ) y]
      simpa [lamPos, smul_eq_mul] using (EReal.coe_mul lam (H[μ] y))
    calc
      prox[fun y : E ↦ ((lam * H[μ] y : ℝ) : EReal)] x
          = prox[((lamPos : ℝ) : EReal) • M[μ, norm_penalty 1]] x := hscaled_huber
      _ = {lineMap x (lineMap x 0 (((μ + lamPos : ℝ) / max ‖x‖ (μ + lamPos : ℝ))))
            ((lamPos : ℝ) / (μ + lamPos : ℝ))} := by
            exact
              prox_scaled_moreau_envelope_eq_singleton_of_scaled_prox_eq_singleton
                hnorm_proper hnorm_closed hnorm_convex hscaled_norm
      _ = {lineMap x 0 (((lamPos : ℝ) / max ‖x‖ (μ + lamPos : ℝ)))} := by
            rw [Set.singleton_eq_singleton_iff]
            rw [lineMap_lineMap_right]
            congr 1
            have hμlam_ne : (μ + lamPos : ℝ) ≠ 0 := (add_pos μ.2 lamPos.2).ne'
            calc
              ((lamPos : ℝ) / (μ + lamPos : ℝ)) * ((μ + lamPos : ℝ) / max ‖x‖ (μ + lamPos : ℝ))
                  = (((lamPos : ℝ) / (μ + lamPos : ℝ)) * (μ + lamPos : ℝ)) /
                      max ‖x‖ (μ + lamPos : ℝ) := by
                        rw [← mul_div_assoc]
              _ = (lamPos : ℝ) / max ‖x‖ (μ + lamPos : ℝ) := by
                    rw [div_mul_cancel₀ _ hμlam_ne]
      _ = {(1 - lam / max ‖x‖ (μ + lam)) • x} := by
            simp [lamPos, AffineMap.lineMap_apply_module]

end
