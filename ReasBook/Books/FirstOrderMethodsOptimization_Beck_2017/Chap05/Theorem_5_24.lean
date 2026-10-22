/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_7_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_22
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_23
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_17
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- This file is `source-facing` for the first-order characterization of strong convexity. The
extended-real convex-analysis owners it uses are already upstream: `effective_domain` and
`IsProperExtendedRealFunction` from Definition 2.5, `is_convex_function` from Definition 2.6, and
`subdifferential` from Definition 3.2. This file keeps only the new strong-convexity predicates
and equivalence theorem built on top of those owners. -/

recall subdifferential

/-- The first-order lower quadratic support inequality for an extended-real-valued convex
function. This is the source clause (ii), written with dual pairings `g (y - x)` instead of the
Euclidean inner-product notation. -/
def subgradient_quadratic_lower_bound (f : E → EReal) (σ : ℝ) : Prop :=
  ∀ x : E, ∀ g ∈ ∂ f(x), ∀ y ∈ effective_domain f,
    f y ≥ f x + ((g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal)

/-- A quadratic lower-bound hypothesis may be applied directly to `x`, `g ∈ ∂ f(x)`, and
`y ∈ effective_domain f`. -/
theorem subgradient_quadratic_lower_bound.apply {f : E → EReal} {σ : ℝ}
    (h : subgradient_quadratic_lower_bound f σ) (x : E) {g : Module.Dual ℝ E}
    (hg : g ∈ ∂f(x)) (y : E) (hy : y ∈ effective_domain f) :
    f y ≥ f x + ((g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal) :=
  h x g hg y hy

/-- Unfolding `subgradient_quadratic_lower_bound` gives exactly the displayed quadratic
subgradient lower bound. -/
@[simp] theorem subgradient_quadratic_lower_bound_iff
    {f : E → EReal} {σ : ℝ} :
    subgradient_quadratic_lower_bound f σ ↔
      ∀ x : E, ∀ g ∈ ∂ f(x), ∀ y ∈ effective_domain f,
        f y ≥ f x + ((g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  rfl

/-- The strong monotonicity inequality for the subdifferential of an extended-real-valued convex
function. This is the source clause (iii), written in dual-pairing form. -/
def subdifferential_strong_monotonicity (f : E → EReal) (σ : ℝ) : Prop :=
  ∀ x y : E, ∀ gₓ ∈ ∂ f(x), ∀ gᵧ ∈ ∂ f(y),
    σ * ‖x - y‖ ^ (2 : ℕ) ≤ (gₓ - gᵧ) (x - y)

/-- A strong-monotonicity hypothesis may be applied directly to a pair of points and
subgradients `gₓ ∈ ∂ f(x)`, `gᵧ ∈ ∂ f(y)`. -/
theorem subdifferential_strong_monotonicity.apply {f : E → EReal} {σ : ℝ}
    (h : subdifferential_strong_monotonicity f σ) (x y : E)
    {gₓ gᵧ : Module.Dual ℝ E} (hgₓ : gₓ ∈ ∂f(x)) (hgᵧ : gᵧ ∈ ∂f(y)) :
    σ * ‖x - y‖ ^ (2 : ℕ) ≤ (gₓ - gᵧ) (x - y) :=
  h x y gₓ hgₓ gᵧ hgᵧ

/-- Unfolding `subdifferential_strong_monotonicity` gives exactly the displayed strong
monotonicity inequality for pairs of subgradients. -/
@[simp] theorem subdifferential_strong_monotonicity_iff
    {f : E → EReal} {σ : ℝ} :
    subdifferential_strong_monotonicity f σ ↔
      ∀ x y : E, ∀ gₓ ∈ ∂ f(x), ∀ gᵧ ∈ ∂ f(y),
        σ * ‖x - y‖ ^ (2 : ℕ) ≤ (gₓ - gᵧ) (x - y) := by
  rfl

-- Proof sketch: use the canonical owner-level strong-convexity statement
-- `StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)` for clause (i). For
-- `(i) → (iii)`, apply the strong-convexity support inequality at `x` and `y` and add the two
-- resulting estimates. For `(iii) → (ii)`, restrict `f` to segments from `x` toward relative-
-- interior perturbations of `y`, use the one-dimensional subgradient selection formula from
-- Lemma 5.22 together with the line-segment principle from Lemma 5.23, and integrate the strong
-- monotonicity estimate. For `(ii) → (i)`, apply (ii) at interior convex-combination points along
-- perturbed segments and pass to the endpoint limit using lower semicontinuity of `f`.
/-- Helper for the main strong-convexity equivalence: strong convexity on `effective_domain f`
implies the quadratic lower
support inequality for every ambient subgradient. -/
lemma subgradientQuadraticLowerBound_of_strongConvexOn
    {f : E → EReal} {σ : ℝ} (hσ : 0 < σ) (h_ne_bot : ∀ z, f z ≠ ⊥)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun z ↦ (f z).toReal)) :
    subgradient_quadratic_lower_bound f σ := by
  intro x g hg y hy
  have hx : x ∈ effective_domain f := (mem_subdifferential.mp hg).1
  by_cases hxy : x = y
  · -- When the two points coincide, the quadratic term vanishes and the claim is tautological.
    subst y
    rw [ge_iff_le]
    have hfx :
        f x = (((f x).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hx) (h_ne_bot x)).symm
    rw [hfx]
    simp
  · -- Route correction: prove the lower support estimate directly from `StrongConvexOn` by
    -- comparing the subgradient slope at `x` with the strong-convex Jensen inequality on short
    -- segments from `x` to `y`, then force the endpoint coefficient by a small-parameter
    -- contradiction.
    let fx : ℝ := (f x).toReal
    let fy : ℝ := (f y).toReal
    let q : ℝ := (σ / 2) * ‖x - y‖ ^ (2 : ℕ)
    have hq_pos : 0 < q := by
      dsimp [q]
      have hnorm_pos : 0 < ‖x - y‖ := by
        refine norm_pos_iff.mpr ?_
        exact sub_ne_zero.mpr hxy
      positivity
    have hfx :
        f x = ((fx : ℝ) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hx) (h_ne_bot x)).symm
    have hfy :
        f y = ((fy : ℝ) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hy) (h_ne_bot y)).symm
    have hsub_base :
        g (y - x) ≤ fy - fx :=
      subgradient_eval_le_toReal_sub f x y (fun z _ ↦ h_ne_bot z) hx hy hg
    have hquad_real :
        g (y - x) + q ≤ fy - fx := by
      by_contra hfail
      have hfail' : fy - fx < g (y - x) + q := by
        linarith
      let δ : ℝ := g (y - x) + q - (fy - fx)
      have hδ_pos : 0 < δ := by
        dsimp [δ]
        linarith
      let t : ℝ := min (1 / 2 : ℝ) (δ / (2 * q))
      have ht_pos : 0 < t := by
        dsimp [t]
        refine lt_min ?_ ?_
        · norm_num
        · positivity
      have ht_nonneg : 0 ≤ t := ht_pos.le
      have ht_le_half : t ≤ (1 / 2 : ℝ) := by
        dsimp [t]
        exact min_le_left _ _
      have ht_lt_one : t < 1 := by
        linarith
      have h_one_sub_nonneg : 0 ≤ 1 - t := by
        linarith
      let z : E := (1 - t) • x + t • y
      have hz_mem : z ∈ effective_domain f := by
        refine hstrong.1 hx hy h_one_sub_nonneg ht_nonneg ?_
        linarith
      have hz_sub : z - x = t • (y - x) := by
        dsimp [z]
        calc
          ((1 - t) • x + t • y) - x
              = ((1 - t) • x + t • y) + (-1 : ℝ) • x := by
                  simp [sub_eq_add_neg]
          _ = t • (y - x) := by
                  simp [sub_eq_add_neg, smul_add, add_smul, add_left_comm, add_comm]
      have hsub_z :
          t * g (y - x) ≤ (f z).toReal - fx := by
        have hsub :=
          subgradient_eval_le_toReal_sub f x z (fun z' _ ↦ h_ne_bot z') hx hz_mem hg
        rw [hz_sub, map_smul, smul_eq_mul] at hsub
        simpa [fx] using hsub
      have hstrong_z :
          (f z).toReal ≤
            (1 - t) * fx + t * fy - (1 - t) * t * q := by
        dsimp [z, fx, fy, q]
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          hstrong.2 hx hy h_one_sub_nonneg ht_nonneg (by linarith)
      have hscaled :
          t * g (y - x) ≤ t * (fy - fx) - t * (1 - t) * q := by
        linarith
      have hbound :
          g (y - x) ≤ fy - fx - (1 - t) * q := by
        nlinarith
      have hδ_le_tq : δ ≤ t * q := by
        dsimp [δ]
        linarith
      have ht_le_ratio : t ≤ δ / (2 * q) := by
        dsimp [t]
        exact min_le_right _ _
      have htq_le_halfδ : t * q ≤ δ / 2 := by
        have hmul : t * q ≤ (δ / (2 * q)) * q :=
          mul_le_mul_of_nonneg_right ht_le_ratio hq_pos.le
        calc
          t * q ≤ (δ / (2 * q)) * q := hmul
          _ = δ / 2 := by
            field_simp [hq_pos.ne']
      linarith
    -- Convert the real inequality back to the original `EReal` lower support statement.
    rw [ge_iff_le, hfx, hfy]
    have hsum_real : fx + (g (y - x) + q) ≤ fy := by
      linarith
    have hsum_ereal :
        (((fx + (g (y - x) + q) : ℝ) : EReal)) ≤ ((fy : ℝ) : EReal) :=
      EReal.coe_le_coe hsum_real
    simpa [fx, fy, q, norm_sub_rev, EReal.coe_add, add_assoc] using hsum_ereal

/-- Helper for the main strong-convexity equivalence: the quadratic lower support inequality
implies strong monotonicity
of the subdifferential by applying it once in each direction and adding the results. -/
lemma subdifferentialStrongMonotonicity_of_subgradientQuadraticLowerBound
    {f : E → EReal} {σ : ℝ} (h_ne_bot : ∀ z, f z ≠ ⊥)
    (hquad : subgradient_quadratic_lower_bound f σ) :
    subdifferential_strong_monotonicity f σ := by
  intro x y gₓ hgₓ gᵧ hgᵧ
  have hx : x ∈ effective_domain f := (mem_subdifferential.mp hgₓ).1
  have hy : y ∈ effective_domain f := (mem_subdifferential.mp hgᵧ).1
  have hxy :
      f y ≥
        f x + ((gₓ (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    hquad.apply x hgₓ y hy
  have hyx :
      f x ≥
        f y + ((gᵧ (x - y) + (σ / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    hquad.apply y hgᵧ x hx
  have hfx :
      f x = ((((f x).toReal : ℝ)) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hx) (h_ne_bot x)).symm
  have hfy :
      f y = ((((f y).toReal : ℝ)) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hy) (h_ne_bot y)).symm
  have hxy_real :
      gₓ (y - x) + (σ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤ (f y).toReal - (f x).toReal := by
    rw [ge_iff_le, hfx, hfy] at hxy
    have hxy_real' :
        (f x).toReal + (gₓ (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) ≤ (f y).toReal := by
      exact_mod_cast hxy
    have hxy_real'' :
        gₓ (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) ≤ (f y).toReal - (f x).toReal := by
      linarith
    simpa [norm_sub_rev] using hxy_real''
  have hyx_real :
      gᵧ (x - y) + (σ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤ (f x).toReal - (f y).toReal := by
    rw [ge_iff_le, hfx, hfy] at hyx
    have hyx_real' :
        (f y).toReal + (gᵧ (x - y) + (σ / 2) * ‖x - y‖ ^ (2 : ℕ)) ≤ (f x).toReal := by
      exact_mod_cast hyx
    linarith
  -- Rewrite the two support estimates so the common quadratic term can be added.
  have hxy_shift :
      (σ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤ (f y).toReal - (f x).toReal + gₓ (x - y) := by
    have hgₓ_neg : gₓ (y - x) = -gₓ (x - y) := by
      rw [show y - x = -(x - y) by abel, map_neg]
    rw [hgₓ_neg] at hxy_real
    linarith
  have hyx_shift :
      (σ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤ (f x).toReal - (f y).toReal - gᵧ (x - y) := by
    linarith
  -- The function-value differences cancel after adding the two directional estimates.
  have hpairing :
      σ * ‖x - y‖ ^ (2 : ℕ) ≤ gₓ (x - y) - gᵧ (x - y) := by
    linarith
  simpa [sub_eq_add_neg] using hpairing

/-- Helper for the main strong-convexity equivalence: convexity of `f` keeps every segment between
two effective-domain
points inside the effective domain of the one-dimensional line restriction
`t ↦ f (AffineMap.lineMap x y t)`. -/
lemma lineMap_mem_effectiveDomain
    {f : E → EReal} (hf_convex : is_convex_function f) {x y : E}
    (hx : x ∈ effective_domain f) (hy : y ∈ effective_domain f) :
    Set.Icc (0 : ℝ) 1 ⊆ effective_domain (fun t : ℝ ↦ f (AffineMap.lineMap x y t)) := by
  intro t ht
  -- The effective domain is convex for a convex function, so every line point stays finite.
  have hdom_convex := effective_domain_convex_of_is_convex_function hf_convex
  have hline_mem :
      AffineMap.lineMap x y t ∈ effective_domain f :=
    by
      simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
        hdom_convex hx hy (sub_nonneg.mpr ht.2) ht.1 (by linarith)
  simpa [effective_domain] using hline_mem

/-- Helper for the main strong-convexity equivalence: every ambient subgradient at a segment point
induces the matching
scalar slope in the Euclidean subdifferential of the line restriction. -/
lemma lineSlope_mem_euclideanSubdifferential_of_mem_subdifferential
    {f : E → EReal} {x y : E} {t : ℝ} {g : Module.Dual ℝ E}
    (hg : g ∈ ∂f(AffineMap.lineMap x y t)) :
    g (y - x) ∈ euclideanSubdifferential (fun τ : ℝ ↦ f (AffineMap.lineMap x y τ)) t := by
  rw [real_slope_mem_euclideanSubdifferential_iff]
  have hz : AffineMap.lineMap x y t ∈ effective_domain f := (mem_subdifferential.mp hg).1
  refine ⟨by simpa [effective_domain] using hz, ?_⟩
  intro s
  have hsub := (mem_subdifferential.mp hg).2 (AffineMap.lineMap x y s)
  have hline_sub :
      AffineMap.lineMap x y s - AffineMap.lineMap x y t = (s - t) • (y - x) := by
    -- Normalize the line-map difference to a scalar multiple of the segment direction.
    have hs :
        AffineMap.lineMap x y s - x = s • (y - x) := by
      simpa using AffineMap.lineMap_vsub_left x y s
    have ht :
        AffineMap.lineMap x y t - x = t • (y - x) := by
      simpa using AffineMap.lineMap_vsub_left x y t
    calc
      AffineMap.lineMap x y s - AffineMap.lineMap x y t
          = (AffineMap.lineMap x y s - x) - (AffineMap.lineMap x y t - x) := by
              abel
      _ = s • (y - x) - t • (y - x) := by rw [hs, ht]
      _ = (s - t) • (y - x) := by rw [sub_smul]
  have heval :
      g (AffineMap.lineMap x y s - AffineMap.lineMap x y t) = g (y - x) * (s - t) := by
    rw [hline_sub, map_smul, smul_eq_mul, mul_comm]
  have hevalE :
      ((g (AffineMap.lineMap x y s - AffineMap.lineMap x y t) : ℝ) : EReal) =
        ((g (y - x) * (s - t) : ℝ) : EReal) := by
    exact congrArg (fun r : ℝ ↦ (r : EReal)) heval
  rw [hevalE] at hsub
  simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hsub

/-- Helper for the main strong-convexity equivalence: strong monotonicity compares any ambient
subgradient at the segment
point `AffineMap.lineMap x y t` to a fixed ambient subgradient at `x` through the line direction
`y - x`. -/
lemma lineSlopeGap_of_subdifferentialStrongMonotonicity
    {f : E → EReal} {σ : ℝ} (hmono : subdifferential_strong_monotonicity f σ)
    {x y : E} {t : ℝ} (ht : 0 < t) {g₀ gₜ : Module.Dual ℝ E}
    (hg₀ : g₀ ∈ ∂f(x)) (hgₜ : gₜ ∈ ∂f(AffineMap.lineMap x y t)) :
    σ * t * ‖y - x‖ ^ (2 : ℕ) ≤ gₜ (y - x) - g₀ (y - x) := by
  have hmono' :=
    hmono.apply (AffineMap.lineMap x y t) x hgₜ hg₀
  have hline_sub :
      AffineMap.lineMap x y t - x = t • (y - x) := by
    -- Rewrite the segment displacement from `x` as the obvious scalar multiple of `y - x`.
    simpa using AffineMap.lineMap_vsub_left x y t
  rw [hline_sub, map_smul, smul_eq_mul, LinearMap.sub_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht] at hmono'
  have hmono'' :
      σ * (t * ‖y - x‖) ^ (2 : ℕ) ≤ t * (gₜ (y - x) - g₀ (y - x)) := by
    simpa [pow_two, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc, mul_assoc,
      mul_left_comm, mul_comm] using hmono'
  nlinarith

/-- Helper for Theorem 5.24: a pointwise affine lower bound on the right derivative over
`(0, 1)` integrates to the corresponding endpoint lower bound on `[0, 1]`. -/
lemma lineRestriction_endpointLowerBound_of_rightDerivLowerBound
    {φ : ℝ → EReal} {A B : ℝ}
    (h_ne_bot : ∀ z, φ z ≠ ⊥) (h_closed : LowerSemicontinuous φ)
    (h_convex : is_convex_function φ)
    (hdom : Set.Icc (0 : ℝ) 1 ⊆ effective_domain φ)
    (hderiv_lower :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        A + B * t ≤ derivWithin (fun s ↦ (φ s).toReal) (Set.Ioi t) t) :
    A + B / 2 ≤ (φ 1).toReal - (φ 0).toReal := by
  let g : ℝ → ℝ := fun t ↦ derivWithin (fun s ↦ (φ s).toReal) (Set.Ioi t) t
  have hconv_toReal : ConvexOn ℝ (effective_domain φ) (fun t ↦ (φ t).toReal) :=
    convexOn_toReal_of_is_convex_function h_convex (fun z _ ↦ h_ne_bot z)
  have hint_g :
      IntervalIntegrable g MeasureTheory.volume 0 1 := by
    -- Reuse the one-dimensional convex-analysis integrability package for the right derivative.
    simpa [g] using
      rightDeriv_intervalIntegrableOnIccOfLowerSemicontinuousConvex
        φ h_ne_bot h_closed h_convex (by norm_num) hdom
  have hint_affine :
      IntervalIntegrable (fun t : ℝ ↦ A + B * t) MeasureTheory.volume 0 1 := by
    -- The affine lower-bound model is continuous, hence interval integrable on `[0, 1]`.
    exact (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable 0 1
  have hmono :
      ∫ t in 0..1, (A + B * t) ≤ ∫ t in 0..1, g t := by
    -- Integrate the pointwise derivative lower bound over the interval.
    refine intervalIntegral.integral_mono_on_of_le_Ioo (a := (0 : ℝ)) (b := 1) zero_le_one
      hint_affine hint_g ?_
    intro t ht
    simpa [g] using hderiv_lower t ht
  have hcont :
      ContinuousOn (fun t ↦ (φ t).toReal) (Set.Icc (0 : ℝ) 1) := by
    -- Closed convex one-dimensional restrictions are continuous on every finite interval inside
    -- the effective domain.
    exact
      (continuousOn_toReal_effective_domain_of_lowerSemicontinuous_convex_univariate
        h_closed h_convex (fun z _ ↦ h_ne_bot z)).mono hdom
  have hhasDeriv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivWithinAt (fun s ↦ (φ s).toReal) (g t) (Set.Ioi t) t := by
    intro t ht
    have ht_int : t ∈ interior (effective_domain φ) :=
      mem_interior_effectiveDomain_of_mem_Ioo hdom ht
    -- Interior convex points identify the one-sided derivative with the canonical right
    -- derivative.
    simpa [g] using hconv_toReal.hasDerivWithinAt_rightDeriv_of_mem_interior ht_int
  have hftc :
      ∫ t in 0..1, g t = (φ 1).toReal - (φ 0).toReal := by
    -- Apply the one-sided fundamental theorem of calculus to the right derivative.
    simpa [g] using
      intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
        (show (0 : ℝ) ≤ 1 by norm_num) hcont hhasDeriv hint_g
  have haffine_eval :
      ∫ t in 0..1, (A + B * t) = A + B / 2 := by
    let F : ℝ → ℝ := fun t ↦ A * t + (B / 2) * t ^ (2 : ℕ)
    have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
      exact ((continuous_const.mul continuous_id).add
        (continuous_const.mul (continuous_id.pow 2))).continuousOn
    have hFderiv :
        ∀ t ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivWithinAt F (A + B * t) (Set.Ioi t) t := by
      intro t _ht
      have hpoly :
          HasDerivAt F (A + t * (2 * (B / 2))) t := by
        -- Differentiate the affine-quadratic antiderivative explicitly.
        dsimp [F]
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id t).const_mul A).add
            (((hasDerivAt_id t).pow 2).const_mul (B / 2))
      have hderiv_eq : A + t * (2 * (B / 2)) = A + B * t := by
        ring
      exact hderiv_eq ▸ hpoly.hasDerivWithinAt
    have hftc_affine :
        ∫ t in 0..1, (A + B * t) = F 1 - F 0 := by
      exact
        intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
          (show (0 : ℝ) ≤ 1 by norm_num) hFcont hFderiv hint_affine
    calc
      ∫ t in 0..1, (A + B * t) = F 1 - F 0 := hftc_affine
      _ = A + B / 2 := by
        dsimp [F]
        ring
  -- Compare the integrated affine lower bound with the exact endpoint difference.
  calc
    A + B / 2 = ∫ t in 0..1, (A + B * t) := haffine_eval.symm
    _ ≤ ∫ t in 0..1, g t := hmono
    _ = (φ 1).toReal - (φ 0).toReal := hftc

/-- Helper for Theorem 5.24: a proper convex extended-real-valued function has a point in the
relative interior of its effective domain. -/
lemma intrinsicInterior_effectiveDomain_nonempty_of_proper_convex
    [FiniteDimensional ℝ E] {f : E → EReal} (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) :
    (intrinsicInterior ℝ (effective_domain f)).Nonempty := by
  -- Finite-dimensional convex sets with a nonempty effective domain have nonempty relative
  -- interior.
  exact
    Set.Nonempty.intrinsicInterior
      (effective_domain_convex_of_is_convex_function hf_convex)
      hf_proper.effective_domain_nonempty

/-- Helper for Theorem 5.24: perturbing an effective-domain point toward a relative-interior point
stays in the relative interior of the effective domain. -/
lemma convexCombo_mem_intrinsicInterior_effectiveDomain
    [FiniteDimensional ℝ E] {f : E → EReal} (hf_convex : is_convex_function f)
    {x z : E} (hx : x ∈ effective_domain f)
    (hz : z ∈ intrinsicInterior ℝ (effective_domain f)) {α : ℝ}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) :
    (1 - α) • x + α • z ∈ intrinsicInterior ℝ (effective_domain f) := by
  -- Apply the relative-interior line-segment principle with the interior point as the first
  -- endpoint and the effective-domain point as the closure endpoint.
  have hconv := effective_domain_convex_of_is_convex_function hf_convex
  have hx_closure : x ∈ closure (effective_domain f) := subset_closure hx
  have hmem :
      α • z + (1 - α) • x ∈ intrinsicInterior ℝ (effective_domain f) :=
    hconv.combo_intrinsicInterior_closure_mem_intrinsicInterior
      hz hx_closure hα.1 hα.2
  simpa [add_comm, add_left_comm, add_assoc] using hmem

end

section Euclidean

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Semantic recall: Chapter 5 already provides the source-facing owner
-- `is_strongly_convex_function`, and Chapter 3 already provides the vector-side owner
-- `euclideanSubdifferential`; the dual-pairing predicates above remain companion bridge forms.

/-- The Euclidean/vector-side quadratic lower support inequality from source clause (ii). -/
def euclidean_subgradient_quadratic_lower_bound (f : E → EReal) (σ : ℝ) : Prop :=
  ∀ x : E, ∀ g ∈ euclideanSubdifferential f x, ∀ y ∈ effective_domain f,
    f y ≥ f x + ((inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal)

/-- Unfolding `euclidean_subgradient_quadratic_lower_bound` gives exactly the displayed
first-order lower quadratic support inequality. -/
theorem euclidean_subgradient_quadratic_lower_bound_iff
    {f : E → EReal} {σ : ℝ} :
    euclidean_subgradient_quadratic_lower_bound f σ ↔
      ∀ x : E, ∀ g ∈ euclideanSubdifferential f x, ∀ y ∈ effective_domain f,
        f y ≥ f x + ((inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- This clause is definitionally the displayed Euclidean quadratic support inequality.
  rfl

/-- The Euclidean/vector-side strong monotonicity inequality from source clause (iii). -/
def euclidean_subdifferential_strong_monotonicity (f : E → EReal) (σ : ℝ) : Prop :=
  ∀ x y : E, ∀ gₓ ∈ euclideanSubdifferential f x, ∀ gᵧ ∈ euclideanSubdifferential f y,
    σ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (gₓ - gᵧ) (x - y)

/-- Unfolding `euclidean_subdifferential_strong_monotonicity` gives exactly the displayed
strong monotonicity inequality for Euclidean subgradients. -/
theorem euclidean_subdifferential_strong_monotonicity_iff
    {f : E → EReal} {σ : ℝ} :
    euclidean_subdifferential_strong_monotonicity f σ ↔
      ∀ x y : E, ∀ gₓ ∈ euclideanSubdifferential f x, ∀ gᵧ ∈ euclideanSubdifferential f y,
        σ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (gₓ - gᵧ) (x - y) := by
  -- This clause is definitionally the displayed Euclidean strong-monotonicity inequality.
  rfl

/-- Helper for Theorem 5.24: every owner subgradient has a Euclidean representative with the same
pairings. -/
lemma existsEuclideanSubgradient_of_memSubdifferential
    [FiniteDimensional ℝ E] {f : E → EReal} {x : E} {g : Module.Dual ℝ E}
    (hg : g ∈ ∂f(x)) :
    ∃ w ∈ euclideanSubdifferential f x, ∀ u : E, g u = inner ℝ w u := by
  -- Choose the Riesz vector representing the owner dual witness in the continuous-dual model.
  let gcont : StrongDual ℝ E := LinearMap.toContinuousLinearMap g
  rcases (InnerProductSpace.toDual ℝ E).surjective gcont with
    ⟨w, hw⟩
  refine ⟨w, ?_, ?_⟩
  · -- Rewrite Euclidean membership to the owner subdifferential and recover the original witness.
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential]
    have hw_dual : (((InnerProductSpace.toDualMap ℝ E w : StrongDual ℝ E) : Module.Dual ℝ E)) = g := by
      ext u
      have hu := congrArg (fun h : StrongDual ℝ E ↦ h u) hw
      simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hu
    simpa [hw_dual] using hg
  · -- The chosen Riesz vector reproduces the same pairing as the owner functional at each test
    -- vector.
    intro u
    have hu := congrArg (fun h : StrongDual ℝ E ↦ h u) hw
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply,
      InnerProductSpace.toDualMap_apply_apply] using hu.symm

/-- Helper for Theorem 5.24: on an interval where `φ` is finite and convex, every scalar
Euclidean subgradient at an interior point is bounded above by the canonical right derivative. -/
lemma leRightDeriv_of_memEuclideanSubdifferentialOnIoo
    {φ : ℝ → EReal} {a b t s : ℝ} (h_convex : is_convex_function φ)
    (h_ne_bot : ∀ z, φ z ≠ ⊥) (hdom : Set.Icc a b ⊆ effective_domain φ)
    (ht : t ∈ Set.Ioo a b) (hs : s ∈ euclideanSubdifferential φ t) :
    s ≤ derivWithin (fun x ↦ (φ x).toReal) (Set.Ioi t) t := by
  let g : ℝ → ℝ := fun x ↦ (φ x).toReal
  have hconv : ConvexOn ℝ (effective_domain φ) g :=
    convexOn_toReal_of_is_convex_function h_convex (fun z _ ↦ h_ne_bot z)
  have ht_int : t ∈ interior (effective_domain φ) :=
    mem_interior_effectiveDomain_of_mem_Ioo hdom ht
  have ht_dom : t ∈ effective_domain φ := interior_subset ht_int
  have hs_support :
      ∀ y : ℝ, φ y ≥ φ t + ((s * (y - t) : ℝ) : EReal) :=
    (real_slope_mem_euclideanSubdifferential_iff.mp hs).2
  -- The right derivative is the infimum of the secant slopes to points on the right.
  rw [hconv.rightDeriv_eq_sInf_slope_of_mem_interior ht_int]
  have hnonempty :
      (slope g t '' {y | y ∈ effective_domain φ ∧ t < y}).Nonempty := by
    refine ⟨slope g t b, ?_⟩
    refine ⟨b, ?_, rfl⟩
    exact ⟨hdom ⟨ht.1.le.trans ht.2.le, le_rfl⟩, ht.2⟩
  refine le_csInf hnonempty ?_
  rintro _ ⟨y, ⟨hy_dom, hty⟩, rfl⟩
  have hy_val : φ y = (((φ y).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hy_dom) (h_ne_bot y)).symm
  have ht_val : φ t = (((φ t).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt ht_dom) (h_ne_bot t)).symm
  have hsupportE :
      ((((φ t).toReal + s * (y - t) : ℝ) : EReal)) ≤ (((φ y).toReal : ℝ) : EReal) := by
    -- Rewrite the subgradient support inequality at `y` into the finite real-valued restriction.
    have hsupport := hs_support y
    rw [ge_iff_le, hy_val, ht_val] at hsupport
    simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hsupport
  have hsupport :
      g t + s * (y - t) ≤ g y := by
    exact_mod_cast hsupportE
  have hslope_eq : g y - g t = slope g t y * (y - t) := by
    have hslope_eq' : (y - t) * slope g t y = g y - g t := by
      simpa [smul_eq_mul] using (sub_smul_slope g t y)
    calc
      g y - g t = (y - t) * slope g t y := hslope_eq'.symm
      _ = slope g t y * (y - t) := by ring
  have hmul : s * (y - t) ≤ slope g t y * (y - t) := by
    linarith
  have hty_pos : 0 < y - t := sub_pos.mpr hty
  nlinarith

/-- Helper for Theorem 5.24: strong convexity gives the Euclidean quadratic lower support
inequality by rewriting the owner pairing through the Riesz map. -/
lemma euclideanSubgradientQuadraticLowerBound_of_strongConvexOn
    {f : E → EReal} {σ : ℝ} (hσ : 0 < σ) (h_ne_bot : ∀ z, f z ≠ ⊥)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun z ↦ (f z).toReal)) :
    euclidean_subgradient_quadratic_lower_bound f σ := by
  intro x g hg y hy
  -- Convert the Euclidean witness to the owner subgradient used by the already-proved owner-level
  -- quadratic support estimate.
  have hg_owner : (((InnerProductSpace.toDualMap ℝ E g : StrongDual ℝ E) : Module.Dual ℝ E)) ∈ ∂ f(x) := by
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hg
    exact hg
  have howner :=
    subgradientQuadraticLowerBound_of_strongConvexOn
      hσ h_ne_bot hstrong x
      (g := ((InnerProductSpace.toDualMap ℝ E g : StrongDual ℝ E) : Module.Dual ℝ E))
      hg_owner y hy
  -- Rewrite the owner pairing as the Euclidean inner product supplied by the Riesz map.
  simpa [InnerProductSpace.toDualMap_apply_apply] using howner

/-- Helper for Theorem 5.24: the Euclidean quadratic lower support inequality implies Euclidean
strong monotonicity after adding the two directional estimates. -/
lemma euclideanSubdifferentialStrongMonotonicity_of_euclideanSubgradientQuadraticLowerBound
    {f : E → EReal} {σ : ℝ} (h_ne_bot : ∀ z, f z ≠ ⊥)
    (hquad : euclidean_subgradient_quadratic_lower_bound f σ) :
    euclidean_subdifferential_strong_monotonicity f σ := by
  intro x y gₓ hgₓ gᵧ hgᵧ
  -- Recover the owner-domain memberships of the two base points from the Euclidean witnesses.
  have hgₓ_owner :
      (((InnerProductSpace.toDualMap ℝ E gₓ : StrongDual ℝ E) : Module.Dual ℝ E)) ∈ ∂ f(x) := by
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hgₓ
    exact hgₓ
  have hgᵧ_owner :
      (((InnerProductSpace.toDualMap ℝ E gᵧ : StrongDual ℝ E) : Module.Dual ℝ E)) ∈ ∂ f(y) := by
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hgᵧ
    exact hgᵧ
  have hx : x ∈ effective_domain f := (mem_subdifferential.mp hgₓ_owner).1
  have hy : y ∈ effective_domain f := (mem_subdifferential.mp hgᵧ_owner).1
  have hxy :
      f y ≥
        f x + ((inner ℝ gₓ (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    hquad x gₓ hgₓ y hy
  have hyx :
      f x ≥
        f y + ((inner ℝ gᵧ (x - y) + (σ / 2) * ‖x - y‖ ^ (2 : ℕ) : EReal) : EReal) :=
    hquad y gᵧ hgᵧ x hx
  have hfx :
      f x = ((((f x).toReal : ℝ)) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hx) (h_ne_bot x)).symm
  have hfy :
      f y = ((((f y).toReal : ℝ)) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hy) (h_ne_bot y)).symm
  have hxy_real :
      inner ℝ gₓ (y - x) + (σ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤ (f y).toReal - (f x).toReal := by
    rw [ge_iff_le, hfx, hfy] at hxy
    have hxy_real' :
        (f x).toReal + (inner ℝ gₓ (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) ≤ (f y).toReal := by
      exact_mod_cast hxy
    have hxy_real'' :
        inner ℝ gₓ (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) ≤ (f y).toReal - (f x).toReal := by
      linarith
    simpa [norm_sub_rev] using hxy_real''
  have hyx_real :
      inner ℝ gᵧ (x - y) + (σ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤ (f x).toReal - (f y).toReal := by
    rw [ge_iff_le, hfx, hfy] at hyx
    have hyx_realE :
        (((f y).toReal + (inner ℝ gᵧ (x - y) + (σ / 2) * ‖x - y‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤
          (((f x).toReal : ℝ) : EReal) := by
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hyx
    have hyx_real' :
        (f y).toReal + (inner ℝ gᵧ (x - y) + (σ / 2) * ‖x - y‖ ^ (2 : ℕ)) ≤ (f x).toReal := by
      exact_mod_cast hyx_realE
    linarith
  -- Rewrite the directional pairing so both inequalities use the same vector `x - y`.
  have hxy_shift :
      (σ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤
        (f y).toReal - (f x).toReal + inner ℝ gₓ (x - y) := by
    have hgₓ_neg : inner ℝ gₓ (y - x) = -inner ℝ gₓ (x - y) := by
      rw [show y - x = -(x - y) by abel, inner_neg_right]
    rw [hgₓ_neg] at hxy_real
    linarith
  have hyx_shift :
      (σ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤
        (f x).toReal - (f y).toReal - inner ℝ gᵧ (x - y) := by
    linarith
  -- After the function-value terms cancel, the remaining inequality is exactly strong
  -- monotonicity of the Euclidean subdifferential.
  have hpairing :
      σ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ gₓ (x - y) - inner ℝ gᵧ (x - y) := by
    linarith
  have hpairing' :
      σ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (gₓ - gᵧ) (x - y) := by
    rw [inner_sub_left]
    linarith
  exact hpairing'

/-- Helper for Theorem 5.24: the quadratic correction rewrites the shifted affine support term
into the norm-square difference needed for the half-squared-norm shift. -/
lemma quadraticShiftCorrection_eq
    {x y : E} {σ : ℝ} :
    inner ℝ (σ • x) (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) =
      (σ / 2) * ‖y‖ ^ (2 : ℕ) - (σ / 2) * ‖x‖ ^ (2 : ℕ) := by
  -- Expand the norm square of `y - x` and collect the resulting inner-product terms.
  rw [real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
  have hnorm : ‖y - x‖ ^ (2 : ℕ) = ‖y‖ ^ (2 : ℕ) - 2 * inner ℝ y x + ‖x‖ ^ (2 : ℕ) := by
    simpa using (norm_sub_sq_real y x)
  rw [hnorm, real_inner_comm x y]
  ring

/-- Helper for Theorem 5.24: after subtracting `(σ / 2)‖·‖²`, the Euclidean quadratic lower
support inequality becomes an ordinary affine support inequality. -/
lemma quadraticShiftSupport_of_euclideanSubgradientQuadraticLowerBound
    {f : E → EReal} {σ : ℝ} (h_ne_bot : ∀ z, f z ≠ ⊥)
    (hquad : euclidean_subgradient_quadratic_lower_bound f σ)
    {x y u : E} (hu : u ∈ euclideanSubdifferential f x) (hy : y ∈ effective_domain f) :
    f y - ((((σ / 2) * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal)) ≥
      f x - ((((σ / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal)) +
        ((inner ℝ (u - σ • x) (y - x) : ℝ) : EReal) := by
  have hu_owner :
      (((InnerProductSpace.toDualMap ℝ E u : StrongDual ℝ E) : Module.Dual ℝ E)) ∈ ∂ f(x) := by
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hu
    exact hu
  have hx : x ∈ effective_domain f := (mem_subdifferential.mp hu_owner).1
  have hxy :
      f y ≥
        f x + ((inner ℝ u (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    hquad x u hu y hy
  let fx : ℝ := (f x).toReal
  let fy : ℝ := (f y).toReal
  let qx : ℝ := (σ / 2) * ‖x‖ ^ (2 : ℕ)
  let qy : ℝ := (σ / 2) * ‖y‖ ^ (2 : ℕ)
  have hfx :
      f x = ((fx : ℝ) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hx) (h_ne_bot x)).symm
  have hfy :
      f y = ((fy : ℝ) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hy) (h_ne_bot y)).symm
  have hquad_real :
      inner ℝ u (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) ≤ fy - fx := by
    rw [ge_iff_le, hfx, hfy] at hxy
    have hrealE :
        (((fx + (inner ℝ u (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) : ℝ)) : EReal) ≤
          ((fy : ℝ) : EReal) := by
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hxy
    have hreal :
        fx + (inner ℝ u (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) ≤ fy := by
      exact_mod_cast hrealE
    linarith
  have hshift_real :
      fx - qx + inner ℝ (u - σ • x) (y - x) ≤ fy - qy := by
    have hrewrite :
        inner ℝ u (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) =
          inner ℝ (u - σ • x) (y - x) + (qy - qx) := by
      calc
        inner ℝ u (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)
            = inner ℝ u (y - x) - inner ℝ (σ • x) (y - x) +
                (inner ℝ (σ • x) (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) := by
                  ring
        _ = inner ℝ (u - σ • x) (y - x) + (qy - qx) := by
          rw [inner_sub_left, quadraticShiftCorrection_eq (x := x) (y := y) (σ := σ)]
    rw [hrewrite] at hquad_real
    linarith
  have hx_shift :
      f x - ((qx : ℝ) : EReal) = (((fx - qx : ℝ)) : EReal) := by
    rw [hfx]
    simp [EReal.coe_sub]
  have hy_shift :
      f y - ((qy : ℝ) : EReal) = (((fy - qy : ℝ)) : EReal) := by
    rw [hfy]
    simp [EReal.coe_sub]
  rw [ge_iff_le, hx_shift, hy_shift]
  have hshift_ereal :
      (((fx - qx + inner ℝ (u - σ • x) (y - x) : ℝ)) : EReal) ≤
        (((fy - qy : ℝ)) : EReal) :=
    EReal.coe_le_coe hshift_real
  simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hshift_ereal

/-- Helper for Theorem 5.24: Euclidean strong monotonicity bounds the pairing of any owner
subgradient at an interior segment point against the fixed Euclidean subgradient at the basepoint.
-/
lemma ambientSlopeLowerBound_of_euclideanStrongMonotonicity
    [FiniteDimensional ℝ E] {f : E → EReal} {σ : ℝ}
    (hmono : euclidean_subdifferential_strong_monotonicity f σ)
    {x y : E} {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {g : E} (hg : g ∈ euclideanSubdifferential f x)
    {ξ : Module.Dual ℝ E} (hξ : ξ ∈ ∂f(AffineMap.lineMap x y t)) :
    inner ℝ g (y - x) + σ * t * ‖y - x‖ ^ (2 : ℕ) ≤ ξ (y - x) := by
  rcases existsEuclideanSubgradient_of_memSubdifferential hξ with ⟨w, hw, hw_eval⟩
  have hmono' :
      σ * ‖AffineMap.lineMap x y t - x‖ ^ (2 : ℕ) ≤
        inner ℝ (w - g) (AffineMap.lineMap x y t - x) :=
    hmono (AffineMap.lineMap x y t) x w hw g hg
  have hline_sub : AffineMap.lineMap x y t - x = t • (y - x) := by
    -- Normalize the segment displacement into the scalar-multiple form used by monotonicity.
    simpa using AffineMap.lineMap_vsub_left x y t
  have hmono'' :
      σ * (t * ‖y - x‖) ^ (2 : ℕ) ≤
        t * inner ℝ (w - g) (y - x) := by
    rw [hline_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, inner_smul_right] at hmono'
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmono'
  have hmono''' :
      σ * (t * ‖y - x‖) ^ (2 : ℕ) ≤
        t * (inner ℝ w (y - x) - inner ℝ g (y - x)) := by
    rw [inner_sub_left] at hmono''
    simpa [sub_eq_add_neg, mul_add, mul_assoc, mul_left_comm, mul_comm] using hmono''
  have hξ_eval : ξ (y - x) = inner ℝ w (y - x) := hw_eval (y - x)
  have hgap :
      σ * t * ‖y - x‖ ^ (2 : ℕ) ≤ inner ℝ w (y - x) - inner ℝ g (y - x) := by
    nlinarith [hmono''', ht.1]
  rw [hξ_eval]
  linarith

/-- Helper for Theorem 5.24: Euclidean strong monotonicity along a segment gives the affine lower
bound on the right derivative of the corresponding scalar line restriction. -/
lemma lineRestriction_rightDerivLowerBound_of_euclideanStrongMonotonicity
    [FiniteDimensional ℝ E] {f : E → EReal} {σ : ℝ}
    (hf_proper : IsProperExtendedRealFunction f) (hf_convex : is_convex_function f)
    (hmono : euclidean_subdifferential_strong_monotonicity f σ)
    {x y : E} {g : E} (hg : g ∈ euclideanSubdifferential f x)
    (hy : y ∈ intrinsicInterior ℝ (effective_domain f)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      inner ℝ g (y - x) + σ * t * ‖y - x‖ ^ (2 : ℕ) ≤
        derivWithin (fun s ↦ (f (AffineMap.lineMap x y s)).toReal) (Set.Ioi t) t := by
  let φ : ℝ → EReal := fun s ↦ f (AffineMap.lineMap x y s)
  have hx_owner :
      (((InnerProductSpace.toDualMap ℝ E g : StrongDual ℝ E) : Module.Dual ℝ E)) ∈ ∂ f(x) := by
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hg
    exact hg
  have hx : x ∈ effective_domain f := (mem_subdifferential.mp hx_owner).1
  have hy_dom : y ∈ effective_domain f := intrinsicInterior_subset hy
  have hφ_convex : is_convex_function φ := by
    -- Convexity is preserved by restricting `f` along the affine line through `x` and `y`.
    simpa [φ] using is_convex_function_precompose_affineMap hf_convex (AffineMap.lineMap x y)
  have hφ_dom :
      Set.Icc (0 : ℝ) 1 ⊆ effective_domain φ :=
    lineMap_mem_effectiveDomain hf_convex hx hy_dom
  intro t ht
  have hx_t_ri :
      AffineMap.lineMap x y t ∈ intrinsicInterior ℝ (effective_domain f) := by
    -- The line point is a strict convex combination of the relative-interior endpoint `y`
    -- and the effective-domain endpoint `x`.
    simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
      convexCombo_mem_intrinsicInterior_effectiveDomain
        hf_convex hx hy ⟨ht.1, ht.2.le⟩
  rcases subdifferential_nonempty_at_relativeInterior_point f (AffineMap.lineMap x y t)
      hf_convex hx_t_ri with ⟨ξ, hξ⟩
  have hslope :
      ξ (y - x) ∈ euclideanSubdifferential φ t :=
    lineSlope_mem_euclideanSubdifferential_of_mem_subdifferential hξ
  have hslope_le :
      ξ (y - x) ≤ derivWithin (fun s ↦ (φ s).toReal) (Set.Ioi t) t :=
    leRightDeriv_of_memEuclideanSubdifferentialOnIoo
      hφ_convex (fun z ↦ hf_proper.ne_bot (AffineMap.lineMap x y z)) hφ_dom ht hslope
  have hambient :
      inner ℝ g (y - x) + σ * t * ‖y - x‖ ^ (2 : ℕ) ≤ ξ (y - x) :=
    ambientSlopeLowerBound_of_euclideanStrongMonotonicity hmono ht hg hξ
  simpa [φ] using le_trans hambient hslope_le

/-- Helper for Theorem 5.24: a scalar inequality holding on `(0, 1]` extends to the left endpoint
once both sides are continuous on `[0, 1]`. -/
lemma leftEndpoint_le_of_forall_mem_Ioc_of_continuousOn
    {L R : ℝ → ℝ}
    (hL : ContinuousOn L (Set.Icc (0 : ℝ) 1))
    (hR : ContinuousOn R (Set.Icc (0 : ℝ) 1))
    (hle : ∀ α ∈ Set.Ioc (0 : ℝ) 1, L α ≤ R α) :
    L 0 ≤ R 0 := by
  -- The order relation is closed, so continuity lets the interior inequality pass to `α = 0`.
  have hzero : (0 : ℝ) ∈ closure (Set.Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc (show (0 : ℝ) ≠ 1 by norm_num)]
    simp
  exact
    ContinuousWithinAt.closure_le hzero
      ((hL 0 (by simp)).mono Set.Ioc_subset_Icc_self)
      ((hR 0 (by simp)).mono Set.Ioc_subset_Icc_self)
      hle

/-- Helper for Theorem 5.24: Euclidean strong monotonicity already gives the quadratic lower
support inequality at every relative-interior target point. -/
lemma euclideanSubgradientQuadraticLowerBound_at_intrinsicInterior
    [FiniteDimensional ℝ E] {f : E → EReal} {σ : ℝ}
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (hmono : euclidean_subdifferential_strong_monotonicity f σ)
    {x y g : E} (hg : g ∈ euclideanSubdifferential f x)
    (hy : y ∈ intrinsicInterior ℝ (effective_domain f)) :
    f y ≥ f x + ((inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  let φ : ℝ → EReal := fun t ↦ f (AffineMap.lineMap x y t)
  have hx_owner :
      (((InnerProductSpace.toDualMap ℝ E g : StrongDual ℝ E) : Module.Dual ℝ E)) ∈ ∂ f(x) := by
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hg
    exact hg
  have hx : x ∈ effective_domain f := (mem_subdifferential.mp hx_owner).1
  have hy_dom : y ∈ effective_domain f := intrinsicInterior_subset hy
  have hφ_closed : LowerSemicontinuous φ := by
    -- Restrict the closed function `f` to the affine segment from `x` to `y`.
    simpa [φ, Function.comp] using
      hf_closed.comp (AffineMap.lineMap_continuous (p := x) (q := y))
  have hφ_convex : is_convex_function φ := by
    -- Convexity is preserved by affine precomposition.
    simpa [φ] using is_convex_function_precompose_affineMap hf_convex (AffineMap.lineMap x y)
  have hφ_dom :
      Set.Icc (0 : ℝ) 1 ⊆ effective_domain φ :=
    lineMap_mem_effectiveDomain hf_convex hx hy_dom
  have hderiv_lower :=
    lineRestriction_rightDerivLowerBound_of_euclideanStrongMonotonicity
      hf_proper hf_convex hmono hg hy
  have hendpoint :
      inner ℝ g (y - x) + (σ * ‖y - x‖ ^ (2 : ℕ)) / 2 ≤
        (φ 1).toReal - (φ 0).toReal := by
    -- Integrate the affine lower bound for the right derivative along the full segment.
    refine
      lineRestriction_endpointLowerBound_of_rightDerivLowerBound
        (φ := φ) (A := inner ℝ g (y - x)) (B := σ * ‖y - x‖ ^ (2 : ℕ))
        (fun t ↦ hf_proper.ne_bot (AffineMap.lineMap x y t)) hφ_closed hφ_convex hφ_dom ?_
    intro t ht
    simpa [φ, mul_assoc, mul_left_comm, mul_comm] using hderiv_lower t ht
  have hendpoint' :
      inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) ≤ (f y).toReal - (f x).toReal := by
    -- Normalize the endpoint formula back to the quadratic support coefficient.
    simpa [φ, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hendpoint
  have hfx :
      f x = ((((f x).toReal : ℝ)) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hx) (hf_proper.ne_bot x)).symm
  have hfy :
      f y = ((((f y).toReal : ℝ)) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hy_dom) (hf_proper.ne_bot y)).symm
  have hsupport_real :
      (f x).toReal + (inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) ≤ (f y).toReal := by
    linarith
  have hsupport_ereal :
      ((((f x).toReal +
          (inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) : ℝ)) : EReal) ≤
        ((((f y).toReal : ℝ)) : EReal) :=
    EReal.coe_le_coe hsupport_real
  -- Convert the finite real inequality back to the source `EReal` statement.
  rw [ge_iff_le, hfx, hfy]
  simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hsupport_ereal

-- TODO: complete the perturbed-segment/integration proof of `(iii) → (ii)` directly on the
-- Euclidean surface. The scalar comparison step is now available as
-- `lineRestriction_rightDerivLowerBound_of_euclideanStrongMonotonicity`, and the endpoint FTC
-- packaging is isolated in `lineRestriction_endpointLowerBound_of_rightDerivLowerBound`; the
-- remaining blocker is the endpoint assembly and the `α → 0+` limit back to the boundary point.
/-- Helper for Theorem 5.24: Euclidean strong monotonicity should imply the Euclidean quadratic
lower support inequality. -/
lemma euclideanSubgradientQuadraticLowerBound_of_euclideanSubdifferentialStrongMonotonicity
    [FiniteDimensional ℝ E] {f : E → EReal} {σ : ℝ}
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (hmono : euclidean_subdifferential_strong_monotonicity f σ) :
    euclidean_subgradient_quadratic_lower_bound f σ := by
  intro x g hg y hy
  -- Route correction: stay on the Euclidean surface and prove the boundary case by perturbing `y`
  -- toward one relative-interior point, then close the resulting scalar inequality at `α = 0`.
  have hx_owner :
      (((InnerProductSpace.toDualMap ℝ E g : StrongDual ℝ E) : Module.Dual ℝ E)) ∈ ∂ f(x) := by
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hg
    exact hg
  have hx : x ∈ effective_domain f := (mem_subdifferential.mp hx_owner).1
  rcases intrinsicInterior_effectiveDomain_nonempty_of_proper_convex hf_proper hf_convex with
    ⟨z, hz⟩
  let yα : ℝ → E := AffineMap.lineMap y z
  let L : ℝ → ℝ := fun α ↦
    (f x).toReal +
      (inner ℝ g (yα α - x) + (σ / 2) * ‖yα α - x‖ ^ (2 : ℕ))
  let R : ℝ → ℝ := fun α ↦ (f (yα α)).toReal
  have hyα_cont : Continuous yα := by
    simpa [yα] using AffineMap.lineMap_continuous (p := y) (q := z)
  have hL_cont : ContinuousOn L (Set.Icc (0 : ℝ) 1) := by
    -- The affine/quadratic right-hand side is continuous in the perturbation parameter `α`.
    have hyα_sub_cont : Continuous (fun α : ℝ ↦ yα α - x) := hyα_cont.sub continuous_const
    have hinner_cont : Continuous (fun α : ℝ ↦ inner ℝ g (yα α - x)) := by
      simpa using Continuous.inner continuous_const hyα_sub_cont
    have hnormsq_cont : Continuous (fun α : ℝ ↦ ‖yα α - x‖ ^ (2 : ℕ)) :=
      hyα_sub_cont.norm.pow 2
    have hcont : Continuous L := by
      dsimp [L]
      exact continuous_const.add (hinner_cont.add (continuous_const.mul hnormsq_cont))
    exact hcont.continuousOn
  have hR_cont : ContinuousOn R (Set.Icc (0 : ℝ) 1) := by
    -- The scalar line restriction of a closed convex function is continuous on the whole segment.
    let φ : ℝ → EReal := fun α ↦ f (yα α)
    have hz_dom : z ∈ effective_domain f := intrinsicInterior_subset hz
    have hφ_closed : LowerSemicontinuous φ := by
      simpa [φ, yα, Function.comp] using
        hf_closed.comp (AffineMap.lineMap_continuous (p := y) (q := z))
    have hφ_convex : is_convex_function φ := by
      simpa [φ, yα] using
        is_convex_function_precompose_affineMap hf_convex (AffineMap.lineMap y z)
    have hφ_dom :
        Set.Icc (0 : ℝ) 1 ⊆ effective_domain φ :=
      lineMap_mem_effectiveDomain hf_convex hy hz_dom
    simpa [R, φ, yα] using
      (continuousOn_toReal_effective_domain_of_lowerSemicontinuous_convex_univariate
        hφ_closed hφ_convex (fun α _ ↦ hf_proper.ne_bot (yα α))).mono hφ_dom
  have hinterior_bound : ∀ α ∈ Set.Ioc (0 : ℝ) 1, L α ≤ R α := by
    intro α hα
    have hyα_ri :
        yα α ∈ intrinsicInterior ℝ (effective_domain f) := by
      simpa [yα, AffineMap.lineMap_apply_module] using
        convexCombo_mem_intrinsicInterior_effectiveDomain hf_convex hy hz hα
    have hyα_dom : yα α ∈ effective_domain f := intrinsicInterior_subset hyα_ri
    have hsupport :=
      euclideanSubgradientQuadraticLowerBound_at_intrinsicInterior
        hf_proper hf_closed hf_convex hmono hg hyα_ri
    have hfx :
        f x = ((((f x).toReal : ℝ)) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hx) (hf_proper.ne_bot x)).symm
    have hyα_val :
        f (yα α) = ((((f (yα α)).toReal : ℝ)) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hyα_dom) (hf_proper.ne_bot (yα α))).symm
    have hsupport_real :
        (f x).toReal +
            (inner ℝ g (yα α - x) + (σ / 2) * ‖yα α - x‖ ^ (2 : ℕ)) ≤
          (f (yα α)).toReal := by
      rw [ge_iff_le, hfx, hyα_val] at hsupport
      exact_mod_cast hsupport
    simpa [L, R] using hsupport_real
  have hboundary : L 0 ≤ R 0 :=
    leftEndpoint_le_of_forall_mem_Ioc_of_continuousOn hL_cont hR_cont hinterior_bound
  have hboundary' :
      (f x).toReal + (inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) ≤ (f y).toReal := by
    -- Evaluate the perturbation inequality at `α = 0`.
    simpa [L, R, yα] using hboundary
  have hfx :
      f x = ((((f x).toReal : ℝ)) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hx) (hf_proper.ne_bot x)).symm
  have hfy :
      f y = ((((f y).toReal : ℝ)) : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hy) (hf_proper.ne_bot y)).symm
  have hboundaryE :
      ((((f x).toReal +
          (inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) : ℝ)) : EReal) ≤
        ((((f y).toReal : ℝ)) : EReal) :=
    EReal.coe_le_coe hboundary'
  -- Convert the closed real inequality back to the source quadratic support statement.
  rw [ge_iff_le, hfx, hfy]
  simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hboundaryE

/-- Helper for Theorem 5.24: after subtracting `(σ / 2) ‖·‖²`, the Euclidean quadratic support
inequality yields Jensen's inequality at perturbed interior chord points. -/
lemma shiftedChordJensen_of_quadraticShiftSupport
    [FiniteDimensional ℝ E] {f : E → EReal} {σ : ℝ}
    (hf_proper : IsProperExtendedRealFunction f) (hf_convex : is_convex_function f)
    (hquad : euclidean_subgradient_quadratic_lower_bound f σ)
    {x y z : E} {t α : ℝ}
    (hx : x ∈ effective_domain f) (hy : y ∈ effective_domain f)
    (hz : z ∈ intrinsicInterior ℝ (effective_domain f))
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hα : α ∈ Set.Ioc (0 : ℝ) 1) :
    let ψ := fun p : E ↦ (f p).toReal - (σ / 2) * ‖p‖ ^ (2 : ℕ)
    ψ (AffineMap.lineMap ((1 - α) • x + α • z) y t) ≤
      (1 - t) * ψ ((1 - α) • x + α • z) + t * ψ y := by
  let xα : E := (1 - α) • x + α • z
  let u : E := AffineMap.lineMap xα y t
  let ψ : E → ℝ := fun p ↦ (f p).toReal - (σ / 2) * ‖p‖ ^ (2 : ℕ)
  have hxα_ri : xα ∈ intrinsicInterior ℝ (effective_domain f) := by
    -- Perturb `x` toward the chosen relative-interior point `z`.
    simpa [xα] using
      convexCombo_mem_intrinsicInterior_effectiveDomain hf_convex hx hz hα
  have hxα_dom : xα ∈ effective_domain f := intrinsicInterior_subset hxα_ri
  have h_one_sub_t : 1 - t ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hu_ri : u ∈ intrinsicInterior ℝ (effective_domain f) := by
    -- The strict chord point stays in the relative interior because `xα` is already interior.
    simpa [u, xα, AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
      convexCombo_mem_intrinsicInterior_effectiveDomain hf_convex hy hxα_ri h_one_sub_t
  rcases subdifferential_nonempty_at_relativeInterior_point f u hf_convex hu_ri with ⟨ξ, hξ⟩
  rcases existsEuclideanSubgradient_of_memSubdifferential hξ with ⟨w, hw, _⟩
  have hu_dom : u ∈ effective_domain f := intrinsicInterior_subset hu_ri
  have hshift_value {p : E} (hp : p ∈ effective_domain f) :
      f p - ((((σ / 2) * ‖p‖ ^ (2 : ℕ) : ℝ) : EReal)) = (((ψ p : ℝ)) : EReal) := by
    -- On the effective domain, the quadratic shift is an ordinary finite real subtraction.
    have hp_val :
        f p = ((((f p).toReal : ℝ)) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hp) (hf_proper.ne_bot p)).symm
    rw [hp_val]
    simp [ψ, EReal.coe_sub]
  have hshift_x :=
    quadraticShiftSupport_of_euclideanSubgradientQuadraticLowerBound
      (f := f) (σ := σ) hf_proper.ne_bot hquad
      (x := u) (y := xα) (u := w) hw hxα_dom
  have hshift_y :=
    quadraticShiftSupport_of_euclideanSubgradientQuadraticLowerBound
      (f := f) (σ := σ) hf_proper.ne_bot hquad
      (x := u) (y := y) (u := w) hw hy
  have hshift_x_real :
      ψ u + inner ℝ (w - σ • u) (xα - u) ≤ ψ xα := by
    rw [ge_iff_le, hshift_value hu_dom, hshift_value hxα_dom] at hshift_x
    have hshift_xE :
        (((ψ u + inner ℝ (w - σ • u) (xα - u) : ℝ)) : EReal) ≤
          (((ψ xα : ℝ)) : EReal) := by
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hshift_x
    exact_mod_cast hshift_xE
  have hshift_y_real :
      ψ u + inner ℝ (w - σ • u) (y - u) ≤ ψ y := by
    rw [ge_iff_le, hshift_value hu_dom, hshift_value hy] at hshift_y
    have hshift_yE :
        (((ψ u + inner ℝ (w - σ • u) (y - u) : ℝ)) : EReal) ≤
          (((ψ y : ℝ)) : EReal) := by
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hshift_y
    exact_mod_cast hshift_yE
  have hxα_sub : xα - u = t • (xα - y) := by
    -- Normalize the left displacement from the chord point.
    calc
      xα - u = xα - ((1 - t) • xα + t • y) := by rw [show u = AffineMap.lineMap xα y t by rfl,
        AffineMap.lineMap_apply_module]
      _ = t • (xα - y) := by
        calc
          xα - ((1 - t) • xα + t • y) = (xα - (1 - t) • xα) - t • y := by
            abel
          _ = t • xα - t • y := by
            have hcollect : xα - (1 - t) • xα = t • xα := by
              calc
                xα - (1 - t) • xα = (1 : ℝ) • xα - (1 - t) • xα := by simp
                _ = ((1 : ℝ) - (1 - t)) • xα := by rw [← sub_smul]
                _ = t • xα := by ring_nf
            rw [hcollect]
          _ = t • (xα - y) := by rw [smul_sub]
  have hy_sub : y - u = (1 - t) • (y - xα) := by
    -- Normalize the right displacement from the same chord point.
    calc
      y - u = y - ((1 - t) • xα + t • y) := by rw [show u = AffineMap.lineMap xα y t by rfl,
        AffineMap.lineMap_apply_module]
      _ = (1 - t) • (y - xα) := by
        calc
          y - ((1 - t) • xα + t • y) = (y - t • y) - (1 - t) • xα := by
            abel
          _ = (1 - t) • y - (1 - t) • xα := by
            have hcollect : y - t • y = (1 - t) • y := by
              calc
                y - t • y = (1 : ℝ) • y - t • y := by simp
                _ = ((1 : ℝ) - t) • y := by rw [← sub_smul]
                _ = (1 - t) • y := by ring_nf
            rw [hcollect]
          _ = (1 - t) • (y - xα) := by rw [smul_sub]
  have hcancel :
      (1 - t) * inner ℝ (w - σ • u) (xα - u) +
        t * inner ℝ (w - σ • u) (y - u) = 0 := by
    -- The weighted linear parts cancel because `u` is the affine combination
    -- `(1 - t) • xα + t • y`.
    rw [hxα_sub, hy_sub, inner_smul_right, inner_smul_right]
    have hy_neg : inner ℝ (w - σ • u) (y - xα) = -inner ℝ (w - σ • u) (xα - y) := by
      rw [show y - xα = -(xα - y) by abel, inner_neg_right]
    rw [hy_neg]
    ring
  have h_one_sub_t_nonneg : 0 ≤ 1 - t := by linarith [ht.2]
  have hweighted_x :
      (1 - t) * ψ u + (1 - t) * inner ℝ (w - σ • u) (xα - u) ≤ (1 - t) * ψ xα := by
    nlinarith [hshift_x_real, h_one_sub_t_nonneg]
  have hweighted_y :
      t * ψ u + t * inner ℝ (w - σ • u) (y - u) ≤ t * ψ y := by
    nlinarith [hshift_y_real, ht.1.le]
  have hψ_u :
      ψ u ≤ (1 - t) * ψ xα + t * ψ y := by
    -- Add the two weighted support inequalities and cancel the linear terms.
    nlinarith [hweighted_x, hweighted_y, hcancel]
  simpa [ψ, xα, u] using hψ_u

/-- Helper for Theorem 5.24: the Euclidean quadratic lower support inequality should imply strong
convexity of the extended-real-valued function. -/
lemma isStronglyConvexFunction_of_euclideanSubgradientQuadraticLowerBound
    [FiniteDimensional ℝ E] {f : E → EReal} {σ : ℝ} (hσ : 0 < σ)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (hquad : euclidean_subgradient_quadratic_lower_bound f σ) :
    is_strongly_convex_function f σ := by
  -- Route correction: the quadratic term has now been normalized by
  -- `quadraticShiftSupport_of_euclideanSubgradientQuadraticLowerBound`, so the remaining work is
  -- the convexity proof for the shifted function from Theorem 5.17 rather than the old raw
  -- quadratic perturbed-chord route.
  rw [is_strongly_convex_function_iff_convexOn_toReal_sub_half_sigma_norm_sq
    (f := f) (σ := σ) hσ hf_proper.ne_bot]
  let ψ : E → ℝ := fun p ↦ (f p).toReal - (σ / 2) * ‖p‖ ^ (2 : ℕ)
  rcases intrinsicInterior_effectiveDomain_nonempty_of_proper_convex hf_proper hf_convex with
    ⟨z, hz⟩
  have hz_dom : z ∈ effective_domain f := intrinsicInterior_subset hz
  have hψ_line_cont {p q : E} (hp : p ∈ effective_domain f) (hq : q ∈ effective_domain f) :
      ContinuousOn (fun α : ℝ ↦ ψ (AffineMap.lineMap p q α)) (Set.Icc (0 : ℝ) 1) := by
    let φ : ℝ → EReal := fun α ↦ f (AffineMap.lineMap p q α)
    have hφ_closed : LowerSemicontinuous φ := by
      -- Restrict the closed function `f` to a fixed affine segment.
      simpa [φ, Function.comp] using
        hf_closed.comp (AffineMap.lineMap_continuous (p := p) (q := q))
    have hφ_convex : is_convex_function φ := by
      -- Convexity is preserved by affine precomposition.
      simpa [φ] using is_convex_function_precompose_affineMap hf_convex (AffineMap.lineMap p q)
    have hφ_dom :
        Set.Icc (0 : ℝ) 1 ⊆ effective_domain φ :=
      lineMap_mem_effectiveDomain hf_convex hp hq
    have htoReal_cont :
        ContinuousOn (fun α ↦ (φ α).toReal) (Set.Icc (0 : ℝ) 1) := by
      exact
        (continuousOn_toReal_effective_domain_of_lowerSemicontinuous_convex_univariate
          hφ_closed hφ_convex (fun α _ ↦ hf_proper.ne_bot (AffineMap.lineMap p q α))).mono hφ_dom
    have hquad_cont :
        ContinuousOn (fun α : ℝ ↦ (σ / 2) * ‖AffineMap.lineMap p q α‖ ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) 1) := by
      exact (continuous_const.mul ((AffineMap.lineMap_continuous (p := p) (q := q)).norm.pow 2)).continuousOn
    simpa [ψ, φ] using htoReal_cont.sub hquad_cont
  refine ⟨effective_domain_convex_of_is_convex_function hf_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    subst ha0
    subst hb1
    simp
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    subst hb0
    subst ha1
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
  have hb_strict : b ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact hb_pos
    · linarith
  have ha_eq : a = 1 - b := by linarith
  have hb_le_one : b ≤ 1 := by linarith
  let xα : ℝ → E := AffineMap.lineMap x z
  let L : ℝ → ℝ := fun α ↦ ψ (AffineMap.lineMap (xα α) y b)
  let R : ℝ → ℝ := fun α ↦ (1 - b) * ψ (xα α) + b * ψ y
  have hL_cont : ContinuousOn L (Set.Icc (0 : ℝ) 1) := by
    let p₀ : E := AffineMap.lineMap x y b
    let p₁ : E := AffineMap.lineMap z y b
    let A : E →ᵃ[ℝ] E := (AffineMap.lineMap (AffineMap.id ℝ E) (AffineMap.const ℝ E y)) b
    have hdom_convex := effective_domain_convex_of_is_convex_function hf_convex
    have hp₀ : p₀ ∈ effective_domain f := by
      -- The perturbed left endpoint lies on the original chord from `x` to `y`.
      dsimp [p₀]
      simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
        hdom_convex hx hy (sub_nonneg.mpr hb_le_one) hb (by linarith)
    have hp₁ : p₁ ∈ effective_domain f := by
      -- The perturbed right endpoint lies on the corresponding chord from `z` to `y`.
      dsimp [p₁]
      simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
        hdom_convex hz_dom hy (sub_nonneg.mpr hb_le_one) hb (by linarith)
    have hline_eq_fun :
        (fun β : ℝ ↦ AffineMap.lineMap (xα β) y b) =
          fun β : ℝ ↦ AffineMap.lineMap p₀ p₁ β := by
      funext β
      change A (xα β) = AffineMap.lineMap p₀ p₁ β
      rw [AffineMap.apply_lineMap]
      simp [A, p₀, p₁]
    have hψ_eq_fun :
        (fun β : ℝ ↦ ψ (AffineMap.lineMap (xα β) y b)) =
          fun β : ℝ ↦ ψ (AffineMap.lineMap p₀ p₁ β) :=
      congrArg (fun fline : ℝ → E ↦ fun β : ℝ ↦ ψ (fline β)) hline_eq_fun
    change ContinuousOn (fun β : ℝ ↦ ψ (AffineMap.lineMap (xα β) y b)) (Set.Icc (0 : ℝ) 1)
    simpa [hψ_eq_fun] using hψ_line_cont hp₀ hp₁
  have hR_cont : ContinuousOn R (Set.Icc (0 : ℝ) 1) := by
    have hxα_cont : ContinuousOn (fun α : ℝ ↦ ψ (xα α)) (Set.Icc (0 : ℝ) 1) := by
      simpa [xα] using hψ_line_cont hx hz_dom
    have hconst : ContinuousOn (fun _ : ℝ ↦ b * ψ y) (Set.Icc (0 : ℝ) 1) := continuousOn_const
    simpa [R] using (hxα_cont.const_smul (1 - b)).add hconst
  have hinterior_jensen : ∀ α ∈ Set.Ioc (0 : ℝ) 1, L α ≤ R α := by
    intro α hα
    have hshift :=
      shiftedChordJensen_of_quadraticShiftSupport
        hf_proper hf_convex hquad hx hy hz hb_strict hα
    simpa [L, R, xα, ψ, AffineMap.lineMap_apply_module] using hshift
  have hboundary : L 0 ≤ R 0 :=
    leftEndpoint_le_of_forall_mem_Ioc_of_continuousOn hL_cont hR_cont hinterior_jensen
  -- Evaluate the closed perturbation inequality at `α = 0`.
  simpa [L, R, xα, ψ, ha_eq, AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc]
    using hboundary

/-- Theorem 5.24: on a finite-dimensional real inner-product space, for a proper closed convex
extended-real-valued function and a fixed modulus `σ > 0`, the following are equivalent:
(i) `f` is `σ`-strongly convex in the source-facing Chapter 5 sense,
(ii) every Euclidean subgradient gives the quadratic lower support model, and
(iii) the Euclidean subdifferential is `σ`-strongly monotone. This is the source-facing rendering
of the textbook first-order characterization of strong convexity. -/
theorem strongConvexOn_tfae_subgradient_quadratic_lower_bound_strong_monotonicity
    [FiniteDimensional ℝ E] (f : E → EReal) (σ : ℝ) (hσ : 0 < σ)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    List.TFAE
      [is_strongly_convex_function f σ,
        euclidean_subgradient_quadratic_lower_bound f σ,
        euclidean_subdifferential_strong_monotonicity f σ] := by
  -- Route correction: assemble the theorem from owner-level implications, and keep the Euclidean
  --/dual transport isolated in the bridge lemmas above.
  tfae_have 1 → 2 := by
    intro hstrong
    -- Strong convexity gives the Euclidean quadratic support inequality after one owner rewrite.
    exact
      euclideanSubgradientQuadraticLowerBound_of_strongConvexOn
        hstrong.sigma_pos hstrong.ne_bot
        (strongConvexOn_toReal_of_is_strongly_convex_function hstrong)
  tfae_have 2 → 3 := by
    intro hquad
    -- Add the two Euclidean support inequalities directly.
    exact
      euclideanSubdifferentialStrongMonotonicity_of_euclideanSubgradientQuadraticLowerBound
        hf_proper.ne_bot hquad
  tfae_have 2 → 1 := by
    intro hquad
    -- Recover strong convexity directly from the Euclidean quadratic lower support inequality.
    exact
      isStronglyConvexFunction_of_euclideanSubgradientQuadraticLowerBound
        hσ hf_proper hf_closed hf_convex hquad
  tfae_have 3 → 2 := by
    intro hmono
    -- Use the direct Euclidean converse `(iii) → (ii)`.
    exact
      euclideanSubgradientQuadraticLowerBound_of_euclideanSubdifferentialStrongMonotonicity
        hf_proper hf_closed hf_convex hmono
  tfae_finish

/-- Companion theorem: for a proper closed convex extended-real-valued function on a
finite-dimensional real inner-product space, strong convexity is equivalent to the Euclidean
subgradient quadratic lower-support inequality. -/
theorem is_strongly_convex_function_iff_euclidean_subgradient_quadratic_lower_bound
    [FiniteDimensional ℝ E] {f : E → EReal} {σ : ℝ} (hσ : 0 < σ)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    is_strongly_convex_function f σ ↔ euclidean_subgradient_quadratic_lower_bound f σ := by
  -- Read off the first and second clauses from the assembled TFAE.
  exact
    List.TFAE.out
      (strongConvexOn_tfae_subgradient_quadratic_lower_bound_strong_monotonicity
        f σ hσ hf_proper hf_closed hf_convex)
      0 1
      (by rfl)
      (by rfl)

/-- Companion theorem: for a proper closed convex extended-real-valued function on a
finite-dimensional real inner-product space, strong convexity is equivalent to strong monotonicity
of the Euclidean subdifferential. -/
theorem is_strongly_convex_function_iff_euclidean_subdifferential_strong_monotonicity
    [FiniteDimensional ℝ E] {f : E → EReal} {σ : ℝ} (hσ : 0 < σ)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    is_strongly_convex_function f σ ↔ euclidean_subdifferential_strong_monotonicity f σ := by
  -- Read off the first and third clauses from the assembled TFAE.
  exact
    List.TFAE.out
      (strongConvexOn_tfae_subgradient_quadratic_lower_bound_strong_monotonicity
        f σ hσ hf_proper hf_closed hf_convex)
      0 2
      (by rfl)
      (by rfl)

/-- Companion theorem: for a proper closed convex extended-real-valued function on a
finite-dimensional real inner-product space, the Euclidean subgradient quadratic lower-support
inequality is equivalent to strong monotonicity of the Euclidean subdifferential. -/
theorem
    euclidean_subgradient_quadratic_lower_bound_iff_euclidean_subdifferential_strong_monotonicity
    [FiniteDimensional ℝ E] {f : E → EReal} {σ : ℝ} (hσ : 0 < σ)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    euclidean_subgradient_quadratic_lower_bound f σ ↔
      euclidean_subdifferential_strong_monotonicity f σ := by
  -- Read off the second and third clauses from the assembled TFAE.
  exact
    List.TFAE.out
      (strongConvexOn_tfae_subgradient_quadratic_lower_bound_strong_monotonicity
        f σ hσ hf_proper hf_closed hf_convex)
      1 2
      (by rfl)
      (by rfl)

end Euclidean
