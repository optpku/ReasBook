/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30

open scoped BigOperators Gradient
open StrongConvexAcceleratedCubicNewton

noncomputable section

universe u

variable {E : Type u}

/- Text 4 2 13 lies in the strongly-convex accelerated cubic-Newton / quadratic-entry domain on
real Hilbert spaces.

Sampled owner declarations:
* `StrongConvexAcceleratedCubicNewton.stageRadius`, `stageLength`, `stageSteps`, and `method` in
  `Algorithm_4_2_4`, the chapter owners for the multistage restart schedule and outer orbit;
* `cubicNewtonQuadraticDecreaseRegion` in `Text_4_2_11`, the nearby source-facing region owner
  for a quadratic regime, written in multiplication form to avoid division-by-zero artifacts;
* `quadraticGradientRegion` in `Text_4_2_12`, the nearby source-facing threshold-region owner for
  Newton dynamics, again written in multiplication form;
* `StrongConvexOn` together with `f ∈ C22[L3]`, the canonical whole-space strong-convexity and
  Hessian-Lipschitz owners used by the surrounding chapter API.

Best owner abstraction:
* source-facing: the quadratic-entry region for the multistage accelerated cubic-Newton orbit and
  the first stage index at which the orbit enters that region;
* core/canonical: `StrongConvexAcceleratedCubicNewton.method` and the region set itself;
* bridge/view: the pointwise membership and least-entry-set expansion.

Primitive data:
* the objective `f`;
* the minimizer `xStar`;
* the strong-convexity modulus `σ₂`;
* the Hessian-Lipschitz constant `L₃`;
* the multistage outer orbit data coming from `StrongConvexAcceleratedCubicNewton.method`.

Derived API:
* the quadratic-entry region inequality, kept in multiplication form
  `8 L₃² (f x - f xStar) ≤ σ₂³`;
* the predicate that stage `k` has entered that region;
* the canonical least-entry witness `IsLeast {k | ...}` and the logarithmic stage bound.

The previous version organized the file around one-off scalar threshold / stage-bound definitions.
This refinement follows the region-style owner pattern already used nearby in Chapter 4: the public
surface is the quadratic-entry region and the corresponding least stage index at which the
multistage orbit enters it, while the displayed scalar inequalities appear only as defining
formulas inside that owner API. -/

/-- The quadratic-entry region for Text 4 2 13, written in multiplication form so that the
degenerate case `L₃ = 0` still gives the intended whole-space threshold region. -/
def strongConvexAcceleratedCubicNewtonQuadraticRegion
    (f : E → ℝ) (xStar : E) (σ2 : ℝ) (L3 : NNReal) : Set E :=
  {x | (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ2 ^ (3 : ℕ)}

-- Proof sketch: unfold `strongConvexAcceleratedCubicNewtonQuadraticRegion`.
/-- Membership in `strongConvexAcceleratedCubicNewtonQuadraticRegion f xStar σ₂ L₃` is exactly
the quadratic-entry inequality `8 L₃² (f x - f xStar) ≤ σ₂³`. -/
theorem mem_strongConvexAcceleratedCubicNewtonQuadraticRegion_iff
    {f : E → ℝ} {xStar x : E} {σ2 : ℝ} {L3 : NNReal} :
    x ∈ strongConvexAcceleratedCubicNewtonQuadraticRegion f xStar σ2 L3 ↔
      (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ2 ^ (3 : ℕ) :=
  Iff.rfl

section

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {L3 : NNReal}

/-- `InStrongConvexAcceleratedCubicNewtonQuadraticRegion xStar innerMethod σ₂ R y₀ k` means that
the `k`th outer-stage iterate of Algorithm 4.2.4 has entered the quadratic region from
Text 4 2 13. -/
def InStrongConvexAcceleratedCubicNewtonQuadraticRegion
    (xStar : E)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (σ2 R : ℝ) (y0 : E) (k : ℕ) : Prop :=
  method innerMethod σ2 R y0 k ∈
    strongConvexAcceleratedCubicNewtonQuadraticRegion f xStar σ2 L3

-- Proof sketch: unfold `InStrongConvexAcceleratedCubicNewtonQuadraticRegion`.
/-- Expanding `InStrongConvexAcceleratedCubicNewtonQuadraticRegion` says exactly that the `k`th
outer iterate satisfies `8 L₃² (f(y_k) - f(x^*)) ≤ σ₂³`. -/
theorem inStrongConvexAcceleratedCubicNewtonQuadraticRegion_iff
    (xStar : E)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (σ2 R : ℝ) (y0 : E) (k : ℕ) :
    InStrongConvexAcceleratedCubicNewtonQuadraticRegion xStar innerMethod σ2 R y0 k ↔
      (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) *
          (f (method innerMethod σ2 R y0 k) - f xStar) ≤
        σ2 ^ (3 : ℕ) :=
  Iff.rfl

/-- Helper for Text 4 2 13: the stage radii satisfy the exact recursion
`R_(k+1) = R_k / 2`. -/
private theorem strongConvexAcceleratedCubicNewton_stageRadius_succ
    (R : ℝ) (k : ℕ) :
    stageRadius R (k + 1) = stageRadius R k / 2 := by
  -- Normalize the textbook definition `R_k = R / 2^k` once and then simplify algebraically.
  rw [stageRadius, stageRadius, pow_succ, div_eq_mul_inv, div_eq_mul_inv]
  field_simp [pow_ne_zero k (show (2 : ℝ) ≠ 0 by norm_num)]

/-- Helper for Text 4 2 13: cubing the source stage length recovers the scalar quantity
`125 * ((L₃ * R_k) / σ₂)`. -/
private theorem strongConvexAcceleratedCubicNewton_stageLength_pow_three
    {σ2 R : ℝ} (hσ2 : 0 < σ2) (k : ℕ)
    (hRk : 0 ≤ stageRadius R k) :
    stageLength σ2 L3 R k ^ (3 : ℕ) =
      125 * (((L3 : ℝ) * stageRadius R k) / σ2) := by
  have hbase : 0 ≤ (((L3 : ℝ) * stageRadius R k) / σ2) := by
    positivity
  -- Rewrite the cubic of `5 * ((L₃ * R_k) / σ₂)^(1/3)` using `Real.rpow_mul_natCast`.
  rw [stageLength, mul_pow]
  rw [show (5 : ℝ) ^ (3 : ℕ) = 125 by norm_num]
  have hrpow :
      ((((L3 : ℝ) * stageRadius R k) / σ2) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) =
        (((L3 : ℝ) * stageRadius R k) / σ2) := by
    rw [← Real.rpow_mul_natCast hbase (1 / 3 : ℝ) 3]
    norm_num
  simpa using congrArg (fun u : ℝ ↦ 125 * u) hrpow

/-- Helper for Text 4 2 13: one restart stage converts a radius bound at stage `k` into the gap
estimate `f(y_(k+1)) - f(x*) ≤ (8 / 125) * σ₂ * R_k²`. -/
private theorem strongConvexAcceleratedCubicNewton_nextGap_le_stageRadiusSq
    {σ2 : ℝ} {xStar y0 : E} {R : ℝ}
    (hσ2 : 0 < σ2) (hL3 : 0 < (L3 : ℝ))
    (hf_strong : StrongConvexOn Set.univ σ2 f)
    (hxStar : IsMinOn f Set.univ xStar)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (k : ℕ)
    (hRk : 0 < stageRadius R k)
    (hk_dist :
      ‖method innerMethod σ2 R y0 k - xStar‖ ≤ stageRadius R k) :
    f (method innerMethod σ2 R y0 (k + 1)) - f xStar ≤
      (8 / 125 : ℝ) * σ2 * (stageRadius R k) ^ (2 : ℕ) := by
  let z := method innerMethod σ2 R y0 k
  let s := stageSteps σ2 L3 R k
  have hs_len_pos : 0 < stageLength σ2 L3 R k := by
    -- The positive branch guarantees a positive stage length, hence at least one inner step.
    dsimp [stageLength]
    positivity
  have hs_pos_real : 0 < (s : ℝ) := by
    exact lt_of_lt_of_le hs_len_pos (stageSteps_lower σ2 L3 R k)
  have hs_pos : 0 < s := by
    exact_mod_cast hs_pos_real
  have hs_one : 1 ≤ s := Nat.succ_le_of_lt hs_pos
  have hconv : ConvexOn ℝ Set.univ f := by
    exact hf_strong.convexOn (fun r ↦ by positivity)
  have hrate :=
    acceleratedCubicRegularization_gap_le_inverse_cubic_rate
      (innerMethod z) hconv hxStar s hs_one
  have hnum_nonneg :
      0 ≤ 8 * (L3 : ℝ) * ‖z - xStar‖ ^ (3 : ℕ) := by
    positivity
  have hnum_le :
      8 * (L3 : ℝ) * ‖z - xStar‖ ^ (3 : ℕ) ≤
        8 * (L3 : ℝ) * (stageRadius R k) ^ (3 : ℕ) := by
    gcongr
  have hs_cube_pos : 0 < (s : ℝ) ^ (3 : ℕ) := by
    positivity
  have hstage_cube_nonneg : 0 ≤ stageLength σ2 L3 R k ^ (3 : ℕ) := by
    positivity
  have hs_cube_ge :
      stageLength σ2 L3 R k ^ (3 : ℕ) ≤ (s : ℝ) ^ (3 : ℕ) := by
    have hs_ge : stageLength σ2 L3 R k ≤ (s : ℝ) := stageSteps_lower σ2 L3 R k
    gcongr
  calc
    f (method innerMethod σ2 R y0 (k + 1)) - f xStar ≤
        (8 * (L3 : ℝ) * ‖z - xStar‖ ^ (3 : ℕ)) /
          ((s : ℝ) * ((s : ℝ) + 1) * ((s : ℝ) + 2)) := by
      simpa [z, s, StrongConvexAcceleratedCubicNewton.method_spec] using hrate
    _ ≤
        (8 * (L3 : ℝ) * ‖z - xStar‖ ^ (3 : ℕ)) / (s : ℝ) ^ (3 : ℕ) := by
      have hden :
          (s : ℝ) ^ (3 : ℕ) ≤
            (s : ℝ) * ((s : ℝ) + 1) * ((s : ℝ) + 2) := by
        nlinarith [hs_pos_real]
      have hprod_pos : 0 < (s : ℝ) * ((s : ℝ) + 1) * ((s : ℝ) + 2) := by positivity
      field_simp [hs_cube_pos.ne', hprod_pos.ne']
      nlinarith
    _ ≤
        (8 * (L3 : ℝ) * (stageRadius R k) ^ (3 : ℕ)) / (s : ℝ) ^ (3 : ℕ) := by
      exact div_le_div_of_nonneg_right hnum_le hs_cube_pos.le
    _ ≤
        (8 * (L3 : ℝ) * (stageRadius R k) ^ (3 : ℕ)) /
          stageLength σ2 L3 R k ^ (3 : ℕ) := by
      have hlen_cube_pos : 0 < stageLength σ2 L3 R k ^ (3 : ℕ) := by positivity
      field_simp [hs_cube_pos.ne', hlen_cube_pos.ne']
      nlinarith [hs_cube_ge]
    _ = (8 / 125 : ℝ) * σ2 * (stageRadius R k) ^ (2 : ℕ) := by
      rw [strongConvexAcceleratedCubicNewton_stageLength_pow_three hσ2 k hRk.le]
      field_simp [hσ2.ne', hL3.ne', hRk.ne']

/-- Helper for Text 4 2 13: the restarted outer iterates stay inside the shrinking radii
`R / 2^k`. -/
private theorem strongConvexAcceleratedCubicNewton_method_dist_le_stageRadius
    {σ2 : ℝ} {xStar y0 : E} {R : ℝ}
    (hσ2 : 0 < σ2) (hL3 : 0 < (L3 : ℝ)) (hR : 0 < R)
    (hf_strong : StrongConvexOn Set.univ σ2 f)
    (hxStar : IsMinOn f Set.univ xStar)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (hy0 : ‖y0 - xStar‖ ≤ R) :
    ∀ k : ℕ,
      ‖method innerMethod σ2 R y0 k - xStar‖ ≤ stageRadius R k
  | 0 => by
      -- The base stage is exactly the initial radius hypothesis.
      simpa [stageRadius] using hy0
  | k + 1 => by
      have ih := strongConvexAcceleratedCubicNewton_method_dist_le_stageRadius
        hσ2 hL3 hR hf_strong hxStar innerMethod hy0 k
      have hRk_pos : 0 < stageRadius R k := by
        dsimp [stageRadius]
        positivity
      have hgap :=
        strongConvexAcceleratedCubicNewton_nextGap_le_stageRadiusSq
          hσ2 hL3 hf_strong hxStar innerMethod k hRk_pos ih
      have hquad :
          f (method innerMethod σ2 R y0 (k + 1)) ≥
            f xStar +
              (σ2 / 2 : ℝ) *
                ‖method innerMethod σ2 R y0 (k + 1) - xStar‖ ^ (2 : ℕ) := by
        -- Strong convexity turns the objective-gap estimate into a distance estimate.
        simpa using
          StrongConvexOn.quadratic_growth_of_isMinOn_of_mem
            hf_strong
            (by simp : xStar ∈ Set.univ)
            hxStar
            (method innerMethod σ2 R y0 (k + 1))
            (by simp : method innerMethod σ2 R y0 (k + 1) ∈ Set.univ)
      have hsq :
          ‖method innerMethod σ2 R y0 (k + 1) - xStar‖ ^ (2 : ℕ) ≤
            (16 / 125 : ℝ) * (stageRadius R k) ^ (2 : ℕ) := by
        nlinarith
      have hhalf :
          ‖method innerMethod σ2 R y0 (k + 1) - xStar‖ ≤ stageRadius R k / 2 := by
        have hcoeff : (16 / 125 : ℝ) ≤ (1 / 4 : ℝ) := by
          norm_num
        nlinarith [hsq, hcoeff, hRk_pos.le, sq_nonneg
          ‖method innerMethod σ2 R y0 (k + 1) - xStar‖]
      simpa [strongConvexAcceleratedCubicNewton_stageRadius_succ] using hhalf

/-- Helper for Text 4 2 13: after stage `k + 1`, the scaled quadratic-region quantity is bounded
by a shifted geometric factor in `4^{-k}`. -/
private theorem strongConvexAcceleratedCubicNewton_scaledGap_le_shiftedGeometric
    {σ2 : ℝ} {xStar y0 : E} {R : ℝ}
    (hσ2 : 0 < σ2) (hL3 : 0 < (L3 : ℝ)) (hR : 0 < R)
    (hf_strong : StrongConvexOn Set.univ σ2 f)
    (hxStar : IsMinOn f Set.univ xStar)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (hy0 : ‖y0 - xStar‖ ≤ R)
    (k : ℕ) :
    (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) *
        (f (method innerMethod σ2 R y0 (k + 1)) - f xStar) ≤
      σ2 ^ (3 : ℕ) *
        ((64 / 125 : ℝ) * ((((L3 : ℝ) * R) / σ2) ^ (2 : ℕ)) / (4 : ℝ) ^ k) := by
  have hdist :=
    strongConvexAcceleratedCubicNewton_method_dist_le_stageRadius
      hσ2 hL3 hR hf_strong hxStar innerMethod hy0 k
  have hRk_pos : 0 < stageRadius R k := by
    dsimp [stageRadius]
    positivity
  have hgap :=
    strongConvexAcceleratedCubicNewton_nextGap_le_stageRadiusSq
      hσ2 hL3 hf_strong hxStar innerMethod k hRk_pos hdist
  -- Rewrite the stage-radius square into the characteristic quantity `((L₃ * R) / σ₂)^2 / 4^k`.
  calc
    (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) *
        (f (method innerMethod σ2 R y0 (k + 1)) - f xStar) ≤
      (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) *
        ((8 / 125 : ℝ) * σ2 * (stageRadius R k) ^ (2 : ℕ)) := by
      gcongr
    _ =
      σ2 ^ (3 : ℕ) *
        ((64 / 125 : ℝ) * ((((L3 : ℝ) * R) / σ2) ^ (2 : ℕ)) / (4 : ℝ) ^ k) := by
      rw [stageRadius]
      field_simp [hσ2.ne', pow_ne_zero k (show (2 : ℝ) ≠ 0 by norm_num)]
      rw [show (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, pow_mul]]
      ring

/-- Helper for Text 4 2 13: there is an explicit stage, bounded by the stated logarithmic
expression, whose outer iterate lies in the quadratic-entry region. -/
private theorem strongConvexAcceleratedCubicNewton_existsQuadraticRegionEntry_le_stageBound
    {σ2 : ℝ} {xStar y0 : E} {R : ℝ}
    (hσ2 : 0 < σ2)
    (hf_strong : StrongConvexOn Set.univ σ2 f)
    (hxStar : IsMinOn f Set.univ xStar)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (hR : 0 ≤ R)
    (hy0 : ‖y0 - xStar‖ ≤ R) :
    ∃ k : ℕ,
      (k : ℝ) ≤
        1 +
          max 0
            (Real.log ((((8 / 3 : ℝ) * (((L3 : ℝ) * R) ^ (3 : ℕ))) / σ2 ^ (3 : ℕ))) /
              Real.log 4) ∧
      InStrongConvexAcceleratedCubicNewtonQuadraticRegion
        xStar innerMethod σ2 R y0 k := by
  by_cases hL3 : L3 = 0
  · -- If `L₃ = 0`, the quadratic region is the whole space, so the least entry stage is `0`.
    refine ⟨0, ?_, ?_⟩
    · have hmax :
          0 ≤
            max 0
              (Real.log ((((8 / 3 : ℝ) * (((L3 : ℝ) * R) ^ (3 : ℕ))) / σ2 ^ (3 : ℕ))) /
                Real.log 4) := le_max_left 0 _
      nlinarith
    · rw [inStrongConvexAcceleratedCubicNewtonQuadraticRegion_iff, method_zero]
      have hL3_real : (L3 : ℝ) = 0 := by simpa using congrArg (fun z : NNReal ↦ (z : ℝ)) hL3
      simpa [hL3_real] using (show 0 ≤ σ2 ^ (3 : ℕ) by positivity)
  by_cases hR0 : R = 0
  · -- If `R = 0`, then the initial point already equals `xStar`, so stage `0` is inside.
    have hy0_eq : y0 = xStar := by
      have hnorm_zero : ‖y0 - xStar‖ = 0 := by
        nlinarith [hy0, norm_nonneg (y0 - xStar)]
      simpa using sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
    refine ⟨0, ?_, ?_⟩
    · have hmax :
          0 ≤
            max 0
              (Real.log ((((8 / 3 : ℝ) * (((L3 : ℝ) * R) ^ (3 : ℕ))) / σ2 ^ (3 : ℕ))) /
                Real.log 4) := le_max_left 0 _
      nlinarith
    · rw [inStrongConvexAcceleratedCubicNewtonQuadraticRegion_iff, method_zero]
      simpa [hy0_eq] using (show 0 ≤ σ2 ^ (3 : ℕ) by positivity)
  have hL3_pos : 0 < (L3 : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hL3)
  have hR_pos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
  let x : ℝ := ((L3 : ℝ) * R) / σ2
  let t : ℝ := (((8 / 3 : ℝ) * (((L3 : ℝ) * R) ^ (3 : ℕ))) / σ2 ^ (3 : ℕ))
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ht_eq : t = (8 / 3 : ℝ) * x ^ (3 : ℕ) := by
    dsimp [t, x]
    field_simp [hσ2.ne']
  by_cases hx_le_one : x ≤ 1
  · -- Small characteristic quantity: the first restarted stage already enters the region.
    refine ⟨1, ?_, ?_⟩
    · have hmax :
          0 ≤
            max 0
              (Real.log ((((8 / 3 : ℝ) * (((L3 : ℝ) * R) ^ (3 : ℕ))) / σ2 ^ (3 : ℕ))) /
                Real.log 4) := le_max_left 0 _
      nlinarith
    · rw [inStrongConvexAcceleratedCubicNewtonQuadraticRegion_iff]
      have hscaled :=
        strongConvexAcceleratedCubicNewton_scaledGap_le_shiftedGeometric
          hσ2 hL3_pos hR_pos hf_strong hxStar innerMethod hy0 0
      have hratio : (64 / 125 : ℝ) * x ^ (2 : ℕ) ≤ 1 := by
        nlinarith [hx_pos.le, hx_le_one]
      have htarget :
          σ2 ^ (3 : ℕ) * ((64 / 125 : ℝ) * x ^ (2 : ℕ) / (4 : ℝ) ^ (0 : ℕ)) ≤
            σ2 ^ (3 : ℕ) := by
        nlinarith [hratio, show 0 ≤ σ2 ^ (3 : ℕ) by positivity]
      simpa [x] using hscaled.trans htarget
  · have hx_gt_one : 1 < x := lt_of_not_ge hx_le_one
    let a : ℝ := Real.log t / Real.log 4
    let m : ℕ := Nat.ceil a
    have ha_pos : 0 < a := by
      dsimp [a]
      have ht_gt_one : 1 < t := by
        rw [ht_eq]
        have hx_cube_gt_one : 1 < x ^ (3 : ℕ) := one_lt_pow₀ hx_gt_one (by norm_num)
        nlinarith
      have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
      exact div_pos (Real.log_pos ht_gt_one) hlog4
    have hm_bound : (m : ℝ) ≤ 1 + max 0 a := by
      have hm_lt : (m : ℝ) < a + 1 := Nat.ceil_lt_add_one ha_pos.le
      have hmax : max 0 a = a := max_eq_right ha_pos.le
      rw [hmax]
      linarith
    have hm_pos : 0 < m := Nat.ceil_pos.mpr ha_pos
    have hm_ne : m ≠ 0 := Nat.ne_zero_of_lt hm_pos
    rcases Nat.exists_eq_succ_of_ne_zero hm_ne with ⟨k, hk⟩
    refine ⟨k + 1, ?_, ?_⟩
    · simpa [a, hk] using hm_bound
    · rw [inStrongConvexAcceleratedCubicNewtonQuadraticRegion_iff]
      have hscaled :=
        strongConvexAcceleratedCubicNewton_scaledGap_le_shiftedGeometric
          hσ2 hL3_pos hR_pos hf_strong hxStar innerMethod hy0 k
      have hcoeff :
          (64 / 125 : ℝ) * x ^ (2 : ℕ) ≤ t / 4 := by
        rw [ht_eq]
        nlinarith [hx_gt_one]
      have hm_ge : a ≤ ((k + 1 : ℕ) : ℝ) := by
        calc
          a ≤ (m : ℝ) := Nat.le_ceil a
          _ = ((k + 1 : ℕ) : ℝ) := by rw [hk]
      have ht_le_pow :
          t ≤ (4 : ℝ) ^ (k + 1) := by
        have hlogb :
            Real.log t / Real.log 4 ≤ ((k + 1 : ℕ) : ℝ) := by
          simpa [a] using hm_ge
        have hbase : 1 < (4 : ℝ) := by norm_num
        have hraw :
            t ≤ (4 : ℝ) ^ (((k + 1 : ℕ) : ℝ)) := by
          exact (Real.logb_le_iff_le_rpow hbase ht_pos).1 (by simpa [Real.logb] using hlogb)
        rw [← Real.rpow_natCast (4 : ℝ) (k + 1)]
        exact hraw
      have hratio :
          (64 / 125 : ℝ) * x ^ (2 : ℕ) / (4 : ℝ) ^ k ≤ 1 := by
        have hk_pos : 0 < (4 : ℝ) ^ k := by positivity
        have hk1_pos : 0 < (4 : ℝ) ^ (k + 1) := by positivity
        have hstep :
            (64 / 125 : ℝ) * x ^ (2 : ℕ) / (4 : ℝ) ^ k ≤
              (t / 4) / (4 : ℝ) ^ k := by
          exact div_le_div_of_nonneg_right hcoeff hk_pos.le
        have hrewrite :
            (t / 4) / (4 : ℝ) ^ k = t / (4 : ℝ) ^ (k + 1) := by
          rw [pow_succ, div_eq_mul_inv, div_eq_mul_inv]
          ring
        have htarget : t / (4 : ℝ) ^ (k + 1) ≤ 1 := by
          rw [div_le_iff₀ hk1_pos]
          simpa using ht_le_pow
        calc
          (64 / 125 : ℝ) * x ^ (2 : ℕ) / (4 : ℝ) ^ k ≤ (t / 4) / (4 : ℝ) ^ k := hstep
          _ = t / (4 : ℝ) ^ (k + 1) := hrewrite
          _ ≤ 1 := htarget
      have htarget :
          σ2 ^ (3 : ℕ) * ((64 / 125 : ℝ) * x ^ (2 : ℕ) / (4 : ℝ) ^ k) ≤
            σ2 ^ (3 : ℕ) := by
        nlinarith [hratio, show 0 ≤ σ2 ^ (3 : ℕ) by positivity]
      simpa [x] using hscaled.trans htarget

-- Proof sketch: prove by induction that `‖method innerMethod σ₂ R y₀ k - xStar‖ ≤ R / 2^k`
-- using strong convexity together with
-- `acceleratedCubicRegularization_gap_le_inverse_cubic_rate` applied to the restarted inner owner
-- `innerMethod (method innerMethod σ₂ R y₀ k)` at the scheduled stage length
-- `stageSteps σ₂ L₃ R k`. The owner lower bound `stageLength σ₂ L₃ R k ≤ stageSteps σ₂ L₃ R k`
-- yields the factor `1 / 2`. Then deduce the gap contraction
-- `f (method innerMethod σ₂ R y₀ (k + 1)) - f xStar ≤
--    (1 / 4) * (f (method innerMethod σ₂ R y₀ k) - f xStar)`,
-- iterate this recurrence from the initial cubic upper bound, and solve the threshold inequality
-- `8 L₃² (f (method innerMethod σ₂ R y₀ N) - f xStar) ≤ σ₂³` for the first entered stage. Since
-- the logarithmic estimate controls the post-stage orbit rather than the initial point `y₀`
-- itself, the natural-number least-entry formulation requires a one-stage safety offset, and the
-- remaining real-valued logarithmic term is clamped below by `0`.
/-- Text 4 2 13 (1): if `f ∈ C22[L₃]` is `σ₂`-strongly convex on `Set.univ`, and the canonical
multistage accelerated cubic-Newton method from Algorithm 4.2.4 started at `y₀` satisfies
`‖y₀ - x^*‖ ≤ R`, then the first stage index `N` whose outer iterate enters the quadratic region
`{x | 8 L₃² (f x - f xStar) ≤ σ₂³}` satisfies
`N ≤ 1 + max 0 ((1 / log 4) * log (((8 / 3) * (L₃ R)^3) / σ₂^3))`. The additive `1` is the
natural-index safety offset needed because the source hypotheses do not force the initial point
`y₀` itself to lie in the quadratic region; `max 0` only clamps the remaining logarithmic term
below by `0`. Here the `C22[L₃]` smoothness owner is supplied by `innerMethod.objective_mem`, so
this remains the canonical-owner reformulation of the textbook Hessian-lower-bound hypothesis. -/
theorem strongConvexAcceleratedCubicNewton_firstQuadraticRegionIndex_le_stageBound
    {σ2 : ℝ} {L3 : NNReal} {f : E → ℝ} {xStar y0 : E}
    (hσ2 : 0 < σ2)
    (hf_strong : StrongConvexOn Set.univ σ2 f)
    (hxStar : IsMinOn f Set.univ xStar)
    -- Verified local API: `(innerMethod y0).objective_mem : f ∈ C22[L3]`.
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    {R : ℝ} (hR : 0 ≤ R)
    (hy0 : ‖y0 - xStar‖ ≤ R)
    {N : ℕ}
    (hN :
      IsLeast
        {k : ℕ |
          InStrongConvexAcceleratedCubicNewtonQuadraticRegion
            xStar innerMethod σ2 R y0 k}
        N) :
    (N : ℝ) ≤
      1 +
        max 0
          (Real.log ((((8 / 3 : ℝ) * (((L3 : ℝ) * R) ^ (3 : ℕ))) / σ2 ^ (3 : ℕ))) /
            Real.log 4) := by
  -- Route correction: rather than force a gap recurrence on the outer stages, produce an
  -- explicit entry witness using the one-stage inverse-cubic estimate plus the shrinking-radius
  -- invariant.
  rcases strongConvexAcceleratedCubicNewton_existsQuadraticRegionEntry_le_stageBound
      (L3 := L3) hσ2 hf_strong hxStar innerMethod hR hy0 with
    ⟨k, hk_bound, hk_mem⟩
  -- Once one admissible stage is explicit, leastness of `N` finishes the argument.
  have hN_le_k : N ≤ k := hN.2 hk_mem
  exact (show (N : ℝ) ≤ (k : ℝ) from by exact_mod_cast hN_le_k).trans hk_bound

private theorem strongConvexAcceleratedCubicNewton_stageLengthRatio_abs_lt_one :
    |((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ)| < 1 := by
  rw [abs_of_pos]
  · have hpow : 1 < Real.rpow (2 : ℝ) (1 / 3 : ℝ) := by
      apply Real.one_lt_rpow
      · norm_num
      · norm_num
    exact inv_lt_one_of_one_lt₀ hpow
  · exact inv_pos.2 (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _)

-- Proof sketch: iterate `stageLength_succ` to express the source schedule
-- `m_k = stageLength σ₂ L₃ R k` as the geometric progression `m_k = m₀ · 2^{-k / 3}`.
/-- For `σ₂ > 0` and `R ≥ 0`, the source stage lengths of Algorithm 4.2.4 form the geometric
progression `m_k = m₀ · 2^{-k / 3}`. -/
theorem strongConvexAcceleratedCubicNewton_stageLength_eq_firstStageLength_mul_ratio_pow
    {σ2 : ℝ} {L3 : NNReal} {R : ℝ}
    (hσ2 : 0 < σ2) (hR : 0 ≤ R) (k : ℕ) :
    stageLength σ2 L3 R k =
      stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k hk =>
      rw [stageLength_succ k hσ2 hR, hk]
      ring_nf

-- Proof sketch: combine the geometric closed form for `stageLength` with the canonical real
-- geometric-series identity `∑' k, ρ^k = (1 - ρ)⁻¹` for `ρ = 2^{-1 / 3}`.
/-- Auxiliary companion theorem: for the source stage schedule `m_k = stageLength σ₂ L₃ R k` of
Algorithm 4.2.4 with `σ₂ > 0` and `R ≥ 0`, the total stage-length budget is summable and equals
`m₀ / (1 - 2^{-1 / 3})`. This is the exact real source-schedule estimate; the discrete Newton
counts used by the algorithm remain `stageSteps σ₂ L₃ R k = ⌈m_k⌉₊`. -/
theorem strongConvexAcceleratedCubicNewton_totalStageLength_eq_geometricFactor_mul_firstStageLength
    {σ2 : ℝ} {L3 : NNReal} {R : ℝ}
    (hσ2 : 0 < σ2) (hR : 0 ≤ R) :
    Summable (stageLength σ2 L3 R) ∧
      ∑' k, stageLength σ2 L3 R k =
        stageLength σ2 L3 R 0 * (1 - (Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹)⁻¹ := by
  have hgeom :
      Summable (fun k : ℕ ↦ ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one
      strongConvexAcceleratedCubicNewton_stageLengthRatio_abs_lt_one
  have hsum :
      Summable
        (fun k : ℕ ↦ stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k) :=
    hgeom.mul_left _
  have hstage :
      stageLength σ2 L3 R =
        fun k : ℕ ↦ stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k := by
    funext k
    exact strongConvexAcceleratedCubicNewton_stageLength_eq_firstStageLength_mul_ratio_pow
      hσ2 hR k
  refine ⟨?_, ?_⟩
  · have h := hsum
    rwa [← hstage] at h
  · have htsum :
        ∑' k, stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k =
          stageLength σ2 L3 R 0 * (1 - ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ))⁻¹ := by
        rw [tsum_mul_left,
          tsum_geometric_of_abs_lt_one
            strongConvexAcceleratedCubicNewton_stageLengthRatio_abs_lt_one]
    have h := htsum
    rwa [← hstage] at h

end

end
