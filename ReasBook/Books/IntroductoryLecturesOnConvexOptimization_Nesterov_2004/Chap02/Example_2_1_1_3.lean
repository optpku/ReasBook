/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexC1

/-
Primary domain: first-order convex analysis of scalar functions on real convex domains.

Sampled owner-style declarations in this domain:
* Chapter 2 `ConvexC1On`, the owner abstraction for `𝓕¹(Q)`
* mathlib `Real.contDiff_exp`, the canonical smooth owner for `exp`
* mathlib `contDiff_norm_rpow`, the canonical `C¹` owner for `‖x‖^p`
* mathlib `convexOn_exp` and `convexOn_rpow`
* mathlib `ConvexOn.comp` with `Real.monotoneOn_rpow_Ici_of_exponent_nonneg`

Best owner abstraction:
* the domain-sensitive owner predicate `ConvexC1On Q f` on `ℝ`

Primitive data:
* a convex domain `Q : Set ℝ`
* a scalar function `f : ℝ → ℝ`
* `ContDiffOn ℝ 1 f Q`
* `ConvexOn ℝ Q f`

Derived API:
* `C¹` regularity on `Q` via `convexC1On_contDiffOn`
* convexity on `Q` via `convexC1On_convexOn`

Source/core/bridge triage:
* source-facing: the three textbook scalar examples in `𝓕¹(ℝ)`
* core/canonical: `ConvexC1On Q f`
* bridge/view: projection back to `ContDiffOn` and `ConvexOn`
-/

/-- Example 2.1.1.3 (1): the exponential function belongs to `𝓕¹(ℝ)`. -/
-- Proof sketch: pair mathlib's canonical declarations `Real.contDiff_exp.contDiffOn` and
-- `convexOn_exp`.
theorem exp_convexC1On_univ : Real.exp ∈ 𝓕¹(Set.univ) := by
  refine ⟨?_, ?_⟩
  · have hexp : ContDiff ℝ 1 Real.exp := Real.contDiff_exp.of_le le_top
    exact contDiffOn_univ.mpr hexp
  · simpa using convexOn_exp

/-- Example 2.1.1.3 (2): for every `p > 1`, the scalar function `t ↦ |t|^p` belongs to `𝓕¹(ℝ)`.
-/
-- Proof sketch: use `contDiff_norm_rpow hp` on `ℝ`, rewrite `‖t‖` as `|t|`, and combine
-- `convexOn_rpow hp.le` on `Ici 0` with the canonical convexity of the norm on `ℝ`.
theorem abs_rpow_convexC1On_univ (p : ℝ) (hp : 1 < p) :
    (fun t : ℝ ↦ |t| ^ p) ∈ 𝓕¹(Set.univ) := by
  refine ⟨?_, ?_⟩
  · simpa [contDiffOn_univ] using
      (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun t : ℝ ↦ ‖t‖ ^ p))
  · let g : ℝ → ℝ := fun x ↦ x ^ p
    have habs : ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|) := by
      simpa using (convexOn_norm convex_univ : ConvexOn ℝ Set.univ norm)
    have himage : (fun x : ℝ ↦ |x|) '' Set.univ = Set.Ici 0 := by
      ext y
      constructor
      · rintro ⟨x, -, rfl⟩
        exact abs_nonneg x
      · intro hy
        exact ⟨y, Set.mem_univ y, abs_of_nonneg hy⟩
    have hg : ConvexOn ℝ ((fun x : ℝ ↦ |x|) '' Set.univ) g := by
      simpa [himage] using convexOn_rpow hp.le
    have hmono : MonotoneOn g ((fun x : ℝ ↦ |x|) '' Set.univ) := by
      simpa [himage] using
        Real.monotoneOn_rpow_Ici_of_exponent_nonneg (le_trans zero_le_one hp.le)
    simpa [g] using hg.comp habs hmono

/-- Example 2.1.1.3 (3): the scalar function `t ↦ |t| - log (1 + |t|)` belongs to `𝓕¹(ℝ)`. -/
-- Proof sketch: treat the example as the scalar convex `C¹` function `u ↦ u - log (1 + u)` on
-- `Ici 0` composed with `t ↦ |t|`; smoothness uses the scalar `log` calculus away from `-1`,
-- while convexity uses the same owner-side absolute-value/norm abstraction as in part (2) rather
-- than a coordinate split into `t ≥ 0` and `t ≤ 0`.
theorem abs_sub_log_one_add_abs_convexC1On_univ :
    (fun t : ℝ ↦ |t| - Real.log (1 + |t|)) ∈ 𝓕¹(Set.univ) := by
  let f : ℝ → ℝ := fun t ↦ |t| - Real.log (1 + |t|)
  let f' : ℝ → ℝ := fun x ↦ x / (1 + |x|)
  refine ⟨?_, ?_⟩
  · have hderiv : ∀ x, HasDerivAt f (f' x) x := by
      intro x
      by_cases hx : x = 0
      · subst hx
        have hzero : HasDerivAt (fun t : ℝ ↦ |t| - Real.log (1 + |t|)) 0 0 := by
          rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_zero_iff_norm_tendsto_zero]
          refine @squeeze_zero ℝ
            (fun t : ℝ ↦ ‖t⁻¹ • (|0 + t| - Real.log (1 + |0 + t|) - (|0| - Real.log (1 + |0|)))‖)
            (fun t : ℝ ↦ |t| / 2) (nhdsWithin (0 : ℝ) {0}ᶜ) ?_ ?_ ?_
          · intro t
            exact norm_nonneg _
          · intro t
            by_cases ht : t = 0
            · simp [ht]
            · have ht_abs : 0 < |t| := abs_pos.mpr ht
              have hnonneg : 0 ≤ |t| - Real.log (1 + |t|) := by
                have hlog : Real.log (1 + |t|) ≤ |t| := by
                  simpa using (Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + |t|))
                linarith
              have hlog := Real.le_log_one_add_of_nonneg (abs_nonneg t)
              have hquad : |t| - Real.log (1 + |t|) ≤ |t| ^ 2 / 2 := by
                have hstep : |t| - Real.log (1 + |t|) ≤ |t| - 2 * |t| / (|t| + 2) := by
                  linarith
                have hcalc : |t| - 2 * |t| / (|t| + 2) = |t| ^ 2 / (|t| + 2) := by
                  have hden : |t| + 2 ≠ 0 := by positivity
                  field_simp [hden]
                  ring
                rw [hcalc] at hstep
                have hle : |t| ^ 2 / (|t| + 2) ≤ |t| ^ 2 / 2 := by
                  exact div_le_div_of_nonneg_left (sq_nonneg |t|) (by positivity)
                    (by nlinarith [abs_nonneg t])
                exact hstep.trans hle
              calc
                ‖t⁻¹ • (|0 + t| - Real.log (1 + |0 + t|) - (|0| - Real.log (1 + |0|)))‖
                    = |t⁻¹ * (|t| - Real.log (1 + |t|))| := by simp [smul_eq_mul]
                _ = |t⁻¹| * (|t| - Real.log (1 + |t|)) := by rw [abs_mul, abs_of_nonneg hnonneg]
                _ = (1 / |t|) * (|t| - Real.log (1 + |t|)) := by rw [abs_inv, inv_eq_one_div]
                _ = (|t| - Real.log (1 + |t|)) / |t| := by ring
                _ ≤ |t| ^ 2 / 2 / |t| := by
                  simpa [pow_two] using (div_le_div_of_nonneg_right hquad ht_abs.le)
                _ = |t| / 2 := by field_simp [ht_abs.ne']
          · have hlim0 := by
              simpa [div_eq_mul_inv, mul_comm] using
                ((continuous_abs.continuousAt : ContinuousAt abs (0 : ℝ)).const_mul ((2 : ℝ)⁻¹)).tendsto
            exact hlim0.mono_left (show nhdsWithin (0 : ℝ) {0}ᶜ ≤ nhds (0 : ℝ) from
              nhdsWithin_le_nhds)
        simpa [f, f'] using hzero
      · have habs : HasDerivAt (fun t : ℝ ↦ |t|) (SignType.sign x : ℝ) x := hasDerivAt_abs hx
        have hxlog : 1 + |x| ≠ 0 := by
          have h1 : (0 : ℝ) < 1 := by norm_num
          linarith [abs_nonneg x, h1]
        have hlog : HasDerivAt (fun t : ℝ ↦ Real.log (1 + |t|))
            ((SignType.sign x : ℝ) / (1 + |x|)) x := by
          simpa using ((hasDerivAt_const x 1).add habs).log hxlog
        have hsub := habs.sub hlog
        have hsub' : HasDerivAt (fun t : ℝ ↦ |t| - Real.log (1 + |t|))
            ((SignType.sign x : ℝ) - (SignType.sign x : ℝ) / (1 + |x|)) x := by
          simpa using hsub
        rcases lt_or_gt_of_ne hx with hxneg | hxpos
        · have hval : ((SignType.sign x : ℝ) - (SignType.sign x : ℝ) / (1 + |x|)) = x / (1 + |x|) := by
            have hden : 1 - x ≠ 0 := by linarith
            have hval' : x * (1 - x)⁻¹ = -1 + (1 - x)⁻¹ := by
              field_simp [hden]
              ring
            calc
              ((SignType.sign x : ℝ) - (SignType.sign x : ℝ) / (1 + |x|))
                  = -1 + (1 - x)⁻¹ := by
                    simp [hxneg, abs_of_neg hxneg, div_eq_mul_inv, sub_eq_add_neg]
              _ = x / (1 + |x|) := by
                simpa [hxneg, abs_of_neg hxneg, div_eq_mul_inv, sub_eq_add_neg] using hval'.symm
          simpa [f'] using (hval ▸ hsub')
        · have hval : ((SignType.sign x : ℝ) - (SignType.sign x : ℝ) / (1 + |x|)) = x / (1 + |x|) := by
            have hden : 1 + x ≠ 0 := by linarith
            have hval' : 1 - (1 + x)⁻¹ = x * (1 + x)⁻¹ := by
              field_simp [hden]
              ring
            simpa [hxpos, abs_of_pos hxpos, div_eq_mul_inv] using hval'
          simpa [f'] using (hval ▸ hsub')
    have hcontDiff : ContDiff ℝ 1 f := by
      rw [contDiff_one_iff_deriv]
      refine ⟨?_, ?_⟩
      · intro x
        exact (hderiv x).differentiableAt
      · have hderiv_eq : deriv f = f' := by
          funext x
          exact (hderiv x).deriv
        rw [hderiv_eq]
        simpa [f', div_eq_mul_inv] using
          (continuous_id.mul
            ((continuous_const.add continuous_abs).inv₀
              (fun x ↦ by
                have h1 : (0 : ℝ) < 1 := by norm_num
                have hne : 1 + |x| ≠ 0 := by linarith [abs_nonneg x, h1]
                simpa using hne)))
    simpa [f, contDiffOn_univ] using hcontDiff
  · have habs : ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|) := by
      simpa using (convexOn_norm convex_univ : ConvexOn ℝ Set.univ norm)
    have himageAbs : (fun x : ℝ ↦ |x|) '' Set.univ = Set.Ici 0 := by
      ext y
      constructor
      · rintro ⟨x, -, rfl⟩
        exact abs_nonneg x
      · intro hy
        exact ⟨y, Set.mem_univ y, abs_of_nonneg hy⟩
    have hshiftConcave : ConcaveOn ℝ (Set.Ici 0) (fun u : ℝ ↦ Real.log (u + 1)) := by
      have himageShift : (fun u : ℝ ↦ u + 1) '' Set.Ici 0 = Set.Ici 1 := by
        ext y
        constructor
        · rintro ⟨u, hu, rfl⟩
          simpa using add_le_add_right (show 0 ≤ u from hu) 1
        · intro hy
          refine ⟨y - 1, ?_, by ring⟩
          simpa using sub_nonneg.mpr (show 1 ≤ y from hy)
      have hlogConcave : ConcaveOn ℝ ((fun u : ℝ ↦ u + 1) '' Set.Ici 0) Real.log := by
        simpa [himageShift] using
          (strictConcaveOn_log_Ioi.concaveOn).subset
            (by
              intro y hy
              exact lt_of_lt_of_le zero_lt_one (show 1 ≤ y from hy))
            (convex_Ici 1)
      have hshift : ConcaveOn ℝ (Set.Ici 0) (fun u : ℝ ↦ u + 1) := by
        simpa using (concaveOn_id (convex_Ici (0 : ℝ))).add_const 1
      have hmono : MonotoneOn Real.log ((fun u : ℝ ↦ u + 1) '' Set.Ici 0) := by
        intro a ha b hb hab
        apply Real.strictMonoOn_log.monotoneOn
        · have ha1 : 1 ≤ a := by simpa [himageShift] using ha
          have h1 : (0 : ℝ) < 1 := by norm_num
          simpa using lt_of_lt_of_le h1 ha1
        · have hb1 : 1 ≤ b := by simpa [himageShift] using hb
          have h1 : (0 : ℝ) < 1 := by norm_num
          simpa using lt_of_lt_of_le h1 hb1
        · exact hab
      simpa [Function.comp] using hlogConcave.comp hshift hmono
    have hcore : ConvexOn ℝ (Set.Ici 0) (fun u : ℝ ↦ u - Real.log (u + 1)) := by
      simpa using (convexOn_id (convex_Ici (0 : ℝ))).sub hshiftConcave
    have hcoreContinuous : ContinuousOn (fun u : ℝ ↦ u - Real.log (u + 1)) (Set.Ici 0) := by
      refine continuousOn_id.sub ?_
      refine (continuousOn_id.add continuousOn_const).log ?_
      intro u hu
      have hu0 : 0 ≤ u := hu
      have h1 : (0 : ℝ) < 1 := by norm_num
      have hne : u + 1 ≠ 0 := by linarith
      simpa using hne
    have hmonoCore : MonotoneOn (fun u : ℝ ↦ u - Real.log (u + 1)) (Set.Ici 0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ)) hcoreContinuous
      · intro u hu
        have hu0 : 0 < u := by simpa using hu
        have hderiv :
            HasDerivAt (fun t : ℝ ↦ t - Real.log (t + 1)) (u / (u + 1)) u := by
          have hlog : HasDerivAt (fun t : ℝ ↦ Real.log (t + 1)) ((1 : ℝ) / (u + 1)) u := by
            have h1 : (0 : ℝ) < 1 := by norm_num
            have hne : u + 1 ≠ 0 := by linarith
            simpa using ((hasDerivAt_id u).add_const 1).log hne
          convert (hasDerivAt_id u).sub hlog using 1
          · have hden : u + 1 ≠ 0 := by linarith
            have hval : u / (u + 1) = 1 - (u + 1)⁻¹ := by
              field_simp [hden]
              ring
            simpa using hval
        exact hderiv.hasDerivWithinAt
      · intro u hu
        have hu0 : 0 < u := by simpa using hu
        positivity
    have hcoreOnAbsImage : ConvexOn ℝ ((fun x : ℝ ↦ |x|) '' Set.univ)
        (fun u : ℝ ↦ u - Real.log (u + 1)) := by
      simpa [himageAbs] using hcore
    have hmonoCoreOnAbsImage :
        MonotoneOn (fun u : ℝ ↦ u - Real.log (u + 1)) ((fun x : ℝ ↦ |x|) '' Set.univ) := by
      simpa [himageAbs] using hmonoCore
    simpa [f, Function.comp, add_comm] using hcoreOnAbsImage.comp habs hmonoCoreOnAbsImage

end
