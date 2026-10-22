/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.2.1 lies in the uniformly convex differentiable-analysis domain on real Hilbert
spaces.

Sampled owner-style declarations:
* mathlib `UniformConvexOn`
* `uniformConvexPowerModulus` in `Definition_4_2_8`
* `uniformConvexOn_iff_lower_tangent_power` in `Definition_4_2_8`
* `ConvexOn.of_gradient_monotone` in `Chap02/Theorem_2_3`

Best owner abstraction:
* source-facing: the power-type lower bound on the gradient monotonicity pairing
* core/canonical: `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* bridge/view: this theorem, which upgrades the source monotonicity inequality to the canonical
  owner predicate

Primitive data:
* the feasible set `Q`
* the objective `d`
* the power parameter `p` in the chapter regime `p ≥ 2`, and the modulus parameter `σp`
* the within-set gradient map `gradientWithin d Q`

Derived API:
* ordinary convexity of `d` on `Q`, obtainable from `ConvexOn.of_gradient_monotone`
* the power lower-tangent inequality from `uniformConvexOn_iff_lower_tangent_power`
* the uniform-convexity owner conclusion

This file therefore keeps only the source-facing monotonicity-to-owner bridge, instead of
introducing any parallel local uniform-convexity wrapper around `UniformConvexOn`. -/

section

variable {Q : Set E} {d : E → ℝ} {σp p : ℝ}

local notation "gradQ" => gradientWithin d Q

/-- Helper for Lemma 4.2.1: if the power lower bound has a nonnegative coefficient, then the
source hypothesis already implies ordinary monotonicity of the within-set gradient. -/
private theorem gradient_monotone_of_power_lower_bound_nonneg
    (hσp : 0 ≤ σp)
    (hmono :
      ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
        σp * Real.rpow ‖x - y‖ p ≤ inner ℝ (gradQ x - gradQ y) (x - y)) :
    GradientMonotoneOn Q d := by
  intro x y hx hy
  -- Drop the stronger power remainder term and retain only the nonnegative pairing conclusion.
  have hpair := hmono hx hy
  have hpow_nonneg : 0 ≤ σp * Real.rpow ‖x - y‖ p := by
    exact mul_nonneg hσp (Real.rpow_nonneg (norm_nonneg (x - y)) _)
  exact le_trans hpow_nonneg hpair

/-- Helper for Lemma 4.2.1: once the coefficient in the source pairing bound is nonnegative, the
source hypothesis already forces ordinary convexity on `Q`. -/
private theorem convexOn_of_power_gradient_monotone_nonneg
    (hσp : 0 ≤ σp)
    (hQ : Convex ℝ Q)
    (hd : DifferentiableOn ℝ d Q)
    (hmono :
      ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
        σp * Real.rpow ‖x - y‖ p ≤ inner ℝ (gradQ x - gradQ y) (x - y)) :
    ConvexOn ℝ Q d := by
  -- Route correction: the false negative-`σp` cases disappear after reducing to ordinary
  -- gradient monotonicity, which is the canonical Chapter 2 owner hypothesis for convexity.
  refine ConvexOn.of_gradient_monotone hQ hd ?_
  exact gradient_monotone_of_power_lower_bound_nonneg (hσp := hσp) hmono

/-- Lemma 4.2.1: in the chapter regime `p ≥ 2`, if `d` is differentiable on a convex set `Q`
and its gradient satisfies the monotonicity bound
`⟪∇ d(x) - ∇ d(y), x - y⟫ ≥ σp ‖x - y‖^p`, then `d` is uniformly convex on `Q` with modulus
`r ↦ (1 / p) * σp * r^p`. -/
-- Proof sketch: integrate the monotonicity inequality along the segment from `x` to `y` to
-- recover the degree-`p` support remainder term, then use
-- `uniformConvexOn_iff_lower_tangent_power` to package the result as the canonical owner
-- predicate `UniformConvexOn`.
theorem uniformConvexOn_of_gradient_monotone
    (hp : 2 ≤ p)
    (hQ : Convex ℝ Q)
    (hd : DifferentiableOn ℝ d Q)
    (hmono :
      ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
        σp * Real.rpow ‖x - y‖ p ≤ inner ℝ (gradQ x - gradQ y) (x - y)) :
    UniformConvexOn Q (uniformConvexPowerModulus σp p) d := by
  have hp_nonneg : 0 ≤ p := le_trans (by norm_num) hp
  have hp_one : 1 ≤ p := le_trans (by norm_num) hp
  have hp_ne : p ≠ 0 := by
    linarith
  refine (uniformConvexOn_iff_lower_tangent_power hp hQ hd).2 ?_
  intro x y hx hy
  let disp : E := y - x
  let seg : ℝ → E := AffineMap.lineMap x y
  let ψ : ℝ → ℝ := fun t ↦
    d (seg t) - t * inner ℝ (gradQ x) disp -
      uniformConvexPowerModulus σp p ‖disp‖ * Real.rpow t p
  let ψ' : ℝ → ℝ := fun t ↦
    inner ℝ (gradQ (seg t)) disp - inner ℝ (gradQ x) disp -
      uniformConvexPowerModulus σp p ‖disp‖ * (p * Real.rpow t (p - 1))
  have hseg_mem_Icc : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    exact hQ.lineMap_mem hx hy ht
  have hseg_mem_Ioo : Set.MapsTo seg (Set.Ioo (0 : ℝ) 1) Q := by
    intro t ht
    exact hQ.lineMap_mem hx hy ⟨ht.1.le, ht.2.le⟩
  have hseg_deriv_Icc :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun s ↦ d (seg s))
          (inner ℝ (gradQ (seg t)) disp) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    -- Differentiate the restriction of `d` along the feasible chord from `x` to `y`.
    simpa [seg, disp, InnerProductSpace.toDual_apply_apply] using
      (hd (seg t) (hseg_mem_Icc ht)).hasGradientWithinAt.hasFDerivWithinAt.comp_hasDerivWithinAt t
        AffineMap.hasDerivWithinAt_lineMap hseg_mem_Icc
  have hseg_cont : ContinuousOn (fun t ↦ d (seg t)) (Set.Icc (0 : ℝ) 1) := by
    -- The segment restriction is continuous because it is differentiable at every point of
    -- the compact interval.
    intro t ht
    exact (hseg_deriv_Icc t ht).continuousWithinAt
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    have hlin_cont :
        ContinuousOn (fun t : ℝ ↦ t * inner ℝ (gradQ x) disp) (Set.Icc (0 : ℝ) 1) :=
      (continuous_id'.mul continuous_const).continuousOn
    have hrpow_cont :
        ContinuousOn (fun t : ℝ ↦ uniformConvexPowerModulus σp p ‖disp‖ * Real.rpow t p)
          (Set.Icc (0 : ℝ) 1) := by
      have hcont_rpow : ContinuousOn (fun t : ℝ ↦ Real.rpow t p) (Set.Icc (0 : ℝ) 1) := by
        simpa using
          (continuousOn_id.rpow_const (s := Set.Icc (0 : ℝ) 1) (p := p)
            (fun _ _ ↦ Or.inr hp_nonneg))
      exact continuousOn_const.mul hcont_rpow
    -- The corrected remainder is the difference of three continuous scalar terms.
    simpa [ψ] using (hseg_cont.sub hlin_cont).sub hrpow_cont
  have hψ_deriv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivWithinAt ψ (ψ' t) (Set.Ioo (0 : ℝ) 1) t := by
    intro t ht
    have hcomp :
        HasDerivWithinAt (fun s ↦ d (seg s))
          (inner ℝ (gradQ (seg t)) disp) (Set.Ioo (0 : ℝ) 1) t := by
      -- On the open interior, the same chain rule computes the directional derivative.
      simpa [seg, disp, InnerProductSpace.toDual_apply_apply] using
        (hd (seg t) (hseg_mem_Ioo ht)).hasGradientWithinAt.hasFDerivWithinAt.comp_hasDerivWithinAt
          t AffineMap.hasDerivWithinAt_lineMap hseg_mem_Ioo
    have hlin :
        HasDerivWithinAt (fun s : ℝ ↦ s * inner ℝ (gradQ x) disp)
          (inner ℝ (gradQ x) disp) (Set.Ioo (0 : ℝ) 1) t := by
      simpa only [one_mul] using
        ((hasDerivAt_id' t).mul_const (inner ℝ (gradQ x) disp)).hasDerivWithinAt
    have hrpow :
        HasDerivWithinAt
          (fun s : ℝ ↦ uniformConvexPowerModulus σp p ‖disp‖ * Real.rpow s p)
          (uniformConvexPowerModulus σp p ‖disp‖ * (p * Real.rpow t (p - 1)))
          (Set.Ioo (0 : ℝ) 1) t := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((Real.hasDerivAt_rpow_const (x := t) (p := p) (Or.inr hp_one)).hasDerivWithinAt.mul_const
          (uniformConvexPowerModulus σp p ‖disp‖))
    -- Differentiate the three pieces of `ψ` separately and recombine them.
    convert (hcomp.sub hlin).sub hrpow using 1
  have hψ_nonneg :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ ψ' t := by
    intro t ht
    have hpair :=
      hmono (hseg_mem_Ioo ht) hx
    have hdisp : seg t - x = t • disp := by
      simpa [seg, disp, vsub_eq_sub] using AffineMap.lineMap_vsub_left x y t
    have hnorm :
        ‖seg t - x‖ = t * ‖disp‖ := by
      calc
        ‖seg t - x‖ = ‖t • disp‖ := by rw [hdisp]
        _ = |t| * ‖disp‖ := norm_smul t disp
        _ = t * ‖disp‖ := by simp [abs_of_nonneg ht.1.le]
    have hinner :
        inner ℝ (gradQ (seg t) - gradQ x) (seg t - x) =
          t * inner ℝ (gradQ (seg t) - gradQ x) disp := by
      rw [hdisp, real_inner_smul_right]
    have hrpow_t :
        Real.rpow t p = t * Real.rpow t (p - 1) := by
      have hpow_add :
          Real.rpow t ((p - 1) + 1) = Real.rpow t (p - 1) * Real.rpow t 1 := by
        simpa using Real.rpow_add ht.1 (p - 1) 1
      have hpow_one : Real.rpow t 1 = t := by
        simp
      calc
        Real.rpow t p = Real.rpow t ((p - 1) + 1) := by ring_nf
        _ = Real.rpow t (p - 1) * Real.rpow t 1 := hpow_add
        _ = Real.rpow t (p - 1) * t := by rw [hpow_one]
        _ = t * Real.rpow t (p - 1) := by ring
    have hscaled :
        t * (σp * Real.rpow ‖disp‖ p * Real.rpow t (p - 1)) ≤
          t * inner ℝ (gradQ (seg t) - gradQ x) disp := by
      calc
        t * (σp * Real.rpow ‖disp‖ p * Real.rpow t (p - 1))
            = σp * Real.rpow ‖seg t - x‖ p := by
              have hmulrpow :
                  Real.rpow (t * ‖disp‖) p = Real.rpow t p * Real.rpow ‖disp‖ p := by
                simpa using (Real.mul_rpow (x := t) (y := ‖disp‖) (z := p) ht.1.le
                  (norm_nonneg disp))
              calc
                t * (σp * Real.rpow ‖disp‖ p * Real.rpow t (p - 1))
                    = σp * (t * Real.rpow t (p - 1) * Real.rpow ‖disp‖ p) := by
                        ring
                _ = σp * (Real.rpow t p * Real.rpow ‖disp‖ p) := by
                      rw [← hrpow_t]
                _ = σp * Real.rpow (t * ‖disp‖) p := by
                      rw [hmulrpow]
                _ = σp * Real.rpow ‖seg t - x‖ p := by
                      rw [hnorm]
        _ ≤ inner ℝ (gradQ (seg t) - gradQ x) (seg t - x) := hpair
        _ = t * inner ℝ (gradQ (seg t) - gradQ x) disp := hinner
    have hbound :
        σp * Real.rpow ‖disp‖ p * Real.rpow t (p - 1) ≤
          inner ℝ (gradQ (seg t) - gradQ x) disp := by
      exact le_of_mul_le_mul_left hscaled ht.1
    have hcoeff :
        uniformConvexPowerModulus σp p ‖disp‖ * (p * Real.rpow t (p - 1)) =
          σp * Real.rpow ‖disp‖ p * Real.rpow t (p - 1) := by
      dsimp [uniformConvexPowerModulus]
      field_simp [hp_ne]
    have hbound' :
        uniformConvexPowerModulus σp p ‖disp‖ * (p * Real.rpow t (p - 1)) ≤
          inner ℝ (gradQ (seg t) - gradQ x) disp := by
      rw [hcoeff]
      exact hbound
    have hbound'' :
        uniformConvexPowerModulus σp p ‖disp‖ * (p * Real.rpow t (p - 1)) ≤
          inner ℝ (gradQ (seg t)) disp - inner ℝ (gradQ x) disp := by
      calc
        uniformConvexPowerModulus σp p ‖disp‖ * (p * Real.rpow t (p - 1)) ≤
            inner ℝ (gradQ (seg t) - gradQ x) disp := hbound'
        _ = inner ℝ (gradQ (seg t)) disp - inner ℝ (gradQ x) disp := by
            rw [inner_sub_left]
    -- The source monotonicity hypothesis exactly dominates the derivative correction term.
    dsimp [ψ']
    simpa [sub_eq_add_neg] using sub_nonneg.mpr hbound''
  have hψ_mono : MonotoneOn ψ (Set.Icc (0 : ℝ) 1) := by
    -- A nonnegative derivative on the interior makes the corrected remainder monotone.
    refine monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Icc (0 : ℝ) 1) (f' := ψ')
      (convex_Icc (0 : ℝ) 1) hψ_cont ?_ ?_
    · intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa using ht
      simpa [interior_Icc] using hψ_deriv t ht'
    · intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa using ht
      simpa [interior_Icc] using hψ_nonneg t ht'
  have hendpoint :
      ψ 0 ≤ ψ 1 := hψ_mono (by simp) (by simp) zero_le_one
  have hlower :
      d x ≤ d y - inner ℝ (gradQ x) (y - x) -
        uniformConvexPowerModulus σp p ‖y - x‖ := by
    -- Evaluate the monotone remainder at the endpoints of the segment.
    simpa [ψ, seg, disp, hp_ne, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      hendpoint
  linarith

end
