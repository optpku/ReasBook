/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm DikinEllipsoidNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Corollary 5.1.5 lies in the Chapter 5 self-concordance / Hessian-comparison domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the canonical Hessian operator owner;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` in `Chap05/Definition_5_1_1`, the chapter owner
  for the local Hessian norm;
* `IsSelfConcordantOnWith` in `Chap05/Definition_5_1_1`, the quantitative self-concordance owner;
* `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` in `Chap05/Theorem_5_1_5`,
  which derives the domain membership of points satisfying the Dikin-radius hypothesis;
* `IsSelfConcordantOnWith.hessian_loewner_bounds_of_mem_openDikinEllipsoid` in
  `Chap05/Proposition_5_0_15`, the pointwise Hessian comparison theorem in the same domain.

Source/core/bridge triage:
* source-facing: the averaged Hessian along the segment from `x` to `y` and its two comparison
  inequalities;
* core/canonical: `hessian f z`, `‖u‖[f; x]`, the interval integral
  `∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))`, and `IsSelfConcordantOnWith dom Mf f`;
* bridge/view: the Dikin-radius hypothesis, which supplies both `0 < Mf` and the derived
  membership `y ∈ dom` needed for pointwise Hessian comparison along the segment.

Primitive data:
* a complete real inner-product space `E`;
* a domain `dom`, a function `f`, a self-concordance constant `Mf`, and points `x y : E`.

Derived API:
* the averaged Hessian integral `∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))`;
* the admissibility hypothesis `y ∈ W⁰[f; x](1 / (Mf : ℝ))`;
* the individual lower and upper Loewner bounds obtained by projecting the paired comparison.

This file keeps the averaged Hessian as a source-facing integral expression built directly from the
canonical Hessian owner. The primitive owner-level result is the paired Loewner comparison, in
the same shape as `hessian_loewner_bounds_of_mem_openDikinEllipsoid`; the one-sided inequalities
are then exposed as derived projections rather than as parallel primitive wrappers. -/

namespace IsSelfConcordantOnWith

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

/-- Helper for Corollary 5 1 5: every affine parameter `τ ∈ [0,1]` produces the corresponding
segment point `x + τ • (y - x)` inside `segment ℝ x y`. -/
private lemma segment_point_mem_segment
    {x y : E} {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    x + τ • (y - x) ∈ segment ℝ x y := by
  -- Rewrite the affine segment point into the canonical convex-combination form.
  rw [segment_eq_image_lineMap]
  refine ⟨τ, hτ, ?_⟩
  simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Corollary 5 1 5: diagonal scalar quadratic-form bounds upgrade to Loewner bounds
for a symmetric averaged operator. -/
private lemma loewner_bounds_of_scalarized_average_bounds
    {A G : E →L[ℝ] E} {c d : ℝ}
    (hAPos : A.IsPositive) (hGSymm : G.IsSymmetric)
    (hlower : ∀ v : E, c * inner ℝ v (A v) ≤ inner ℝ v (G v))
    (hupper : ∀ v : E, inner ℝ v (G v) ≤ d * inner ℝ v (A v)) :
    c • A ≤ G ∧ G ≤ d • A := by
  constructor
  · -- Rewrite the lower comparison as positivity of `G - c • A`.
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    constructor
    · intro u v
      have hASymm : inner ℝ (A u) v = inner ℝ u (A v) := by
        simpa using hAPos.isSymmetric u v
      have hGSymm' : inner ℝ (G u) v = inner ℝ u (G v) := by
        simpa using hGSymm u v
      calc
        inner ℝ ((G - c • A) u) v = inner ℝ (G u) v - c * inner ℝ (A u) v := by
          simp [inner_sub_left, inner_smul_left]
        _ = inner ℝ u (G v) - c * inner ℝ u (A v) := by
          rw [hGSymm', hASymm]
        _ = inner ℝ u ((G - c • A) v) := by
          simp [inner_sub_right, inner_smul_right]
    · intro u
      have hASymm : inner ℝ (A u) u = inner ℝ u (A u) := by
        simpa using hAPos.isSymmetric u u
      have hGSymm' : inner ℝ (G u) u = inner ℝ u (G u) := by
        simpa using hGSymm u u
      have hrewrite :
          inner ℝ ((G - c • A) u) u = inner ℝ u (G u) - c * inner ℝ u (A u) := by
        calc
          inner ℝ ((G - c • A) u) u = inner ℝ (G u) u - c * inner ℝ (A u) u := by
            simp [inner_sub_left, inner_smul_left]
          _ = inner ℝ u (G u) - c * inner ℝ u (A u) := by
            rw [hGSymm', hASymm]
      rw [hrewrite]
      linarith [hlower u]
  · -- Rewrite the upper comparison as positivity of `d • A - G`.
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    constructor
    · intro u v
      have hASymm : inner ℝ (A u) v = inner ℝ u (A v) := by
        simpa using hAPos.isSymmetric u v
      have hGSymm' : inner ℝ (G u) v = inner ℝ u (G v) := by
        simpa using hGSymm u v
      calc
        inner ℝ ((d • A - G) u) v = d * inner ℝ (A u) v - inner ℝ (G u) v := by
          simp [inner_sub_left, inner_smul_left]
        _ = d * inner ℝ u (A v) - inner ℝ u (G v) := by
          rw [hASymm, hGSymm']
        _ = inner ℝ u ((d • A - G) v) := by
          simp [inner_sub_right, inner_smul_right]
    · intro u
      have hASymm : inner ℝ (A u) u = inner ℝ u (A u) := by
        simpa using hAPos.isSymmetric u u
      have hGSymm' : inner ℝ (G u) u = inner ℝ u (G u) := by
        simpa using hGSymm u u
      have hrewrite :
          inner ℝ ((d • A - G) u) u = d * inner ℝ u (A u) - inner ℝ u (G u) := by
        calc
          inner ℝ ((d • A - G) u) u = d * inner ℝ (A u) u - inner ℝ (G u) u := by
            simp [inner_sub_left, inner_smul_left]
          _ = d * inner ℝ u (A u) - inner ℝ u (G u) := by
            rw [hASymm, hGSymm']
      rw [hrewrite]
      linarith [hupper u]

section

variable [CompleteSpace E]
variable (hself : IsSelfConcordantOnWith dom Mf f) {x y : E} (hx : x ∈ dom)
variable (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))

/-- Helper for Corollary 5 1 5: nonnegative scalar dilations scale the local Hessian norm
linearly at a fixed base point. -/
private theorem hessianLocalNorm_smul_nonneg_at_base
    (hself : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom)
    {u : E} {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖τ • u‖[f; x] = τ * ‖u‖[f; x] := by
  have hquad : 0 ≤ inner ℝ u (hessian f x u) :=
    IsSelfConcordantOnWith.hessian_posSemidef hself hx u
  -- Reduce to the scalar identity `sqrt (τ² q) = τ sqrt q` with `q ≥ 0`.
  calc
    ‖τ • u‖[f; x] = Real.sqrt ((τ * τ) * inner ℝ u (hessian f x u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f x u)) * Real.sqrt (τ * τ) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = τ * ‖u‖[f; x] := by
      rw [show τ * τ = τ ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hτ,
        hessianLocalNorm_def]
      ring

/-- Helper for Corollary 5 1 5: on the self-concordant domain, the Hessian varies continuously. -/
private theorem hessian_continuousOn
    (hself : IsSelfConcordantOnWith dom Mf f) :
    ContinuousOn (hessian f) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hC2 : ContDiffOn ℝ 2 f dom := hself.contDiffOn.of_le (by norm_num)
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ f) dom :=
    hC2.fderiv_of_isOpen hself.isOpen_domain
      (show (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) by norm_num)
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ f) dom := by
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen hself.isOpen_domain
      (show (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞) by norm_num)).continuousOn

/-- Helper for Corollary 5 1 5: each intermediate segment point satisfies the source-faithful
pointwise Hessian comparison with the base point Hessian. -/
private theorem segment_point_hessian_bounds
    (hself : IsSelfConcordantOnWith dom Mf f) {x y : E} (hx : x ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    ((1 - τ * a) ^ (2 : ℕ)) • hessian f x ≤ hessian f z ∧
      hessian f z ≤ ((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian f x := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  have hτ_nonneg : 0 ≤ τ := hτ.1
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg f x (y - x)
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have hy : y ∈ dom :=
    IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset hself hx hxy
  have hz : z ∈ dom := by
    exact
      hself.convex_domain.segment_subset hx hy
        (segment_point_mem_segment (x := x) (y := y) hτ)
  have hz_norm : ‖z - x‖[f; x] = τ * r := by
    simp [z, r, hessianLocalNorm_smul_nonneg_at_base (hself := hself) (hx := hx) hτ_nonneg]
  have hτr_le : τ * r ≤ r := by
    have hmul_le : τ * r ≤ 1 * r := mul_le_mul_of_nonneg_right hτ.2 hr_nonneg
    simpa using hmul_le
  let rmid : ℝ := (r + 1 / (Mf : ℝ)) / 2
  have hr_lt_rmid : r < rmid := by
    dsimp [rmid]
    linarith
  have hrmid_lt : rmid < 1 / (Mf : ℝ) := by
    dsimp [rmid]
    linarith
  have hz_mem_rmid : z ∈ W⁰[f; x](rmid) := by
    rw [mem_openDikinEllipsoid_iff]
    have hz_norm_le_r : ‖z - x‖[f; x] ≤ r := by
      rw [hz_norm]
      simpa using hτr_le
    exact lt_of_le_of_lt hz_norm_le_r hr_lt_rmid
  -- Compare `∇²f(z)` to `∇²f(x)` at the exact segment radius, using `rmid` only to discharge
  -- the strict Dikin-radius side condition.
  simpa [a, hz_norm, mul_assoc, mul_left_comm, mul_comm] using
    IsSelfConcordantOnWith.hessian_loewner_bounds_of_exact_local_radius
      (dom := dom) (Mf := Mf) (f := f) hself (x := x) (y := z) (r := rmid) hx hz hrmid_lt
      hz_mem_rmid

/-- Helper for Corollary 5 1 5: the lower scalar segment factor integrates to the explicit
quadratic polynomial from the source proof. -/
private theorem segment_lower_factor_integral
    (a : ℝ) :
    ∫ τ in (0 : ℝ)..1, (1 - τ * a) ^ (2 : ℕ) =
      1 - a + a ^ (2 : ℕ) / 3 := by
  have hnum :
      ContinuousOn (fun t : ℝ ↦ t - a * t ^ (2 : ℕ) + (a ^ (2 : ℕ) / 3) * t ^ (3 : ℕ))
        (Set.Icc (0 : ℝ) 1) := by
    exact
      (show Continuous
        (fun t : ℝ ↦ t - a * t ^ (2 : ℕ) + (a ^ (2 : ℕ) / 3) * t ^ (3 : ℕ)) by
          continuity).continuousOn
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) MeasureTheory.volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
      (show (0 : ℝ) ≤ 1 by norm_num) ?_
    exact (show ContinuousOn (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) 1) by
      exact (show Continuous (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) by continuity).continuousOn)
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (fun s : ℝ ↦ s - a * s ^ (2 : ℕ) + (a ^ (2 : ℕ) / 3) * s ^ (3 : ℕ))
          ((1 - t * a) ^ (2 : ℕ)) t := by
    intro t ht
    convert
      (((hasDerivAt_id t).sub
          (((hasDerivAt_pow 2 t).const_mul a))).add
        (((hasDerivAt_pow 3 t).const_mul (a ^ (2 : ℕ) / 3)))) using 1
    · ring
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (0 : ℝ) ≤ 1 by norm_num)
      hnum hderiv hint
  calc
    ∫ τ in (0 : ℝ)..1, (1 - τ * a) ^ (2 : ℕ)
        = (1 - a + a ^ (2 : ℕ) / 3) -
            (0 - a * 0 ^ (2 : ℕ) + (a ^ (2 : ℕ) / 3) * 0 ^ (3 : ℕ)) := by
              simpa using hftc
    _ = 1 - a + a ^ (2 : ℕ) / 3 := by ring

/-- Helper for Corollary 5 1 5: the reciprocal-square segment factor integrates to the explicit
upper transport coefficient from the source proof. -/
private theorem segment_upper_factor_integral
    {a : ℝ} (ha : a < 1) :
    ∫ τ in (0 : ℝ)..1, ((1 - τ * a) ^ (2 : ℕ))⁻¹ = 1 / (1 - a) := by
  have hden :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < 1 - t * a := by
    intro t ht
    by_cases ha_nonneg : 0 ≤ a
    · have hta_le_a : t * a ≤ a := by
        have hmul_le : t * a ≤ 1 * a := mul_le_mul_of_nonneg_right ht.2 ha_nonneg
        simpa using hmul_le
      linarith
    · have hta_le_zero : t * a ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos ht.1 (le_of_not_ge ha_nonneg)
      linarith
  have hnum :
      ContinuousOn (fun t : ℝ ↦ t / (1 - t * a)) (Set.Icc (0 : ℝ) 1) := by
    refine continuousOn_id.div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 - t * a) by continuity).continuousOn
    · intro t ht
      exact (hden t ht).ne'
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ ((1 - t * a) ^ (2 : ℕ))⁻¹)
        MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn (fun t : ℝ ↦ ((1 - t * a) ^ (2 : ℕ))⁻¹) (Set.Icc (0 : ℝ) 1) := by
      have hbase :
          ContinuousOn (fun t : ℝ ↦ (1 : ℝ) / (1 - t * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) 1) := by
        refine continuousOn_const.div ?_ ?_
        · exact (show Continuous (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) by continuity).continuousOn
        · intro t ht
          exact pow_ne_zero 2 (hden t ht).ne'
      simpa [one_div] using hbase
    exact
      ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
        (show (0 : ℝ) ≤ 1 by norm_num) hcont
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ ↦ s / (1 - s * a))
          (((1 - t * a) ^ (2 : ℕ))⁻¹) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 - t * a ≠ 0 := (hden t ht').ne'
    have hden_deriv :
        HasDerivAt (fun s : ℝ ↦ 1 - s * a) (-a) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).mul_const a) using 1
      ring
    have hquot := (hasDerivAt_id t).div hden_deriv hden_ne
    have hslope :
        ((1 : ℝ) * (1 - t * a) - t * (-a)) / (1 - t * a) ^ (2 : ℕ) =
          ((1 - t * a) ^ (2 : ℕ))⁻¹ := by
      field_simp [hden_ne]
      ring
    have hquot' :
        HasDerivAt (fun s : ℝ ↦ s / (1 - s * a))
          (((1 : ℝ) * (1 - t * a) - t * (-a)) / (1 - t * a) ^ (2 : ℕ)) t := by
      simpa using hquot
    exact hquot'.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (0 : ℝ) ≤ 1 by norm_num)
      hnum hderiv hint
  calc
    ∫ τ in (0 : ℝ)..1, ((1 - τ * a) ^ (2 : ℕ))⁻¹
        = (1 / (1 - a)) - (0 / (1 - 0 * a)) := by
            simpa [one_div] using hftc
    _ = 1 / (1 - a) := by ring

-- Proof sketch: set `r := ‖y - x‖[f; x]` and
-- `G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))`. Apply the pointwise
-- self-concordant Hessian comparison along the segment `τ ↦ x + τ • (y - x)`, derive `0 < Mf`
-- and `y ∈ dom` from the Dikin-radius hypothesis via Theorem 5.1.5(1), then integrate the
-- resulting Loewner inequalities over `τ ∈ [0, 1]`. The scalar integrals are
-- `∫_0^1 (1 - τ M_f r)^2 dτ = 1 - M_f r + (M_f^2 r^2) / 3` and
-- `∫_0^1 (1 - τ M_f r)⁻² dτ = (1 - M_f r)⁻¹`.
/-- Corollary 5 1 5: if `f` is self-concordant on `dom` with positive parameter `M_f`, `x ∈ dom`,
and `y ∈ W⁰[f; x](1 / (Mf : ℝ))`, then the average Hessian along the segment from `x` to `y` lies
between the two explicit Loewner bounds built from `∇² f(x)`. In the source notation,
`r := ‖y - x‖_x` and `G := ∫_0^1 ∇² f(x + τ (y - x)) dτ`. The positivity of `M_f` and the
membership `y ∈ dom` are consequences of the displayed open-Dikin hypothesis. -/
theorem segmentAverageHessian_bounds
    (hself : IsSelfConcordantOnWith dom Mf f) {x y : E} (hx : x ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))
    :
    let r := ‖y - x‖[f; x]
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    ((1 - (Mf : ℝ) * r + ((Mf : ℝ) ^ (2 : ℕ) * r ^ (2 : ℕ)) / 3) • hessian f x ≤ G) ∧
      (G ≤ (1 / (1 - (Mf : ℝ) * r)) • hessian f x) := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : ℝ → E →L[ℝ] E := fun τ ↦ hessian f (x + τ • (y - x))
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, H τ
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg f x (y - x)
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have hMf_pos : 0 < (Mf : ℝ) := by
    by_contra hMf_nonpos
    have hMf_eq_zero : (Mf : ℝ) = 0 := le_antisymm (le_of_not_gt hMf_nonpos) hMf_nonneg
    have hr_neg : r < 0 := by
      simpa [r, hMf_eq_zero] using hr_lt
    linarith
  have ha_lt_one : a < 1 := by
    have hmul : r * (Mf : ℝ) < 1 := (lt_div_iff₀ hMf_pos).1 hr_lt
    simpa [a, mul_comm] using hmul
  have hy : y ∈ dom := hself.openDikinEllipsoid_inv_constant_subset hx hxy
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hHxPos : (hessian f x).IsPositive := hself.hessian_isPositive hx
  have hH_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • (y - x)) (Set.Icc (0 : ℝ) 1) dom := by
    intro τ hτ
    exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) hτ)
  have hH_cont : ContinuousOn H (Set.Icc (0 : ℝ) 1) := by
    simpa [H] using
      (hessian_continuousOn (hself := hself) (dom := dom) (Mf := Mf) (f := f)).comp
        (show Continuous (fun τ : ℝ ↦ x + τ • (y - x)) by continuity).continuousOn
        hH_maps
  have hH_int : IntervalIntegrable H MeasureTheory.volume 0 1 := by
    exact
      ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
        (show (0 : ℝ) ≤ 1 by norm_num) hH_cont
  have hH_apply_cont (u : E) : ContinuousOn (fun τ : ℝ ↦ H τ u) (Set.Icc (0 : ℝ) 1) := by
    let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E u
    simpa [H, ev] using ev.continuous.comp_continuousOn hH_cont
  have hH_apply_int (u : E) :
      IntervalIntegrable (fun τ : ℝ ↦ H τ u) MeasureTheory.volume 0 1 := by
    exact
      ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
        (show (0 : ℝ) ≤ 1 by norm_num) (hH_apply_cont u)
  have hpair_integral (u v : E) :
      ∫ τ in (0 : ℝ)..1, inner ℝ u (H τ v) = inner ℝ u (G v) := by
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
    calc
      ∫ τ in (0 : ℝ)..1, inner ℝ u (H τ v)
          = ∫ τ in (0 : ℝ)..1, φ (H τ v) := by
              refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro τ hτ
              simp [φ, H, InnerProductSpace.toDual_apply_apply]
      _ = φ (∫ τ in (0 : ℝ)..1, H τ v) := by
            exact ContinuousLinearMap.intervalIntegral_comp_comm (L := φ) (hH_apply_int v)
      _ = inner ℝ u (∫ τ in (0 : ℝ)..1, H τ v) := by
            simp [φ, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ u (G v) := by
            rw [ContinuousLinearMap.intervalIntegral_apply hH_int v]
  have hG_symm : G.IsSymmetric := by
    intro u v
    calc
      inner ℝ (G u) v = inner ℝ v (G u) := real_inner_comm _ _
      _ = ∫ τ in (0 : ℝ)..1, inner ℝ v (H τ u) := (hpair_integral v u).symm
      _ = ∫ τ in (0 : ℝ)..1, inner ℝ u (H τ v) := by
            refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro τ hτ
            have hτIoc : τ ∈ Set.Ioc (0 : ℝ) 1 := by
              simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hτ
            have hτ' : τ ∈ Set.Icc (0 : ℝ) 1 := by
              exact ⟨le_of_lt hτIoc.1, hτIoc.2⟩
            have hz : x + τ • (y - x) ∈ dom := by
              exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) hτ')
            have hzPos : (H τ).IsPositive := by
              simpa [H] using hself.hessian_isPositive hz
            simpa [H, real_inner_comm] using hzPos.isSymmetric u v
      _ = inner ℝ u (G v) := hpair_integral u v
  have hpair_cont (v : E) :
      ContinuousOn (fun τ : ℝ ↦ inner ℝ v (H τ v)) (Set.Icc (0 : ℝ) 1) := by
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) v
    simpa [H, φ, InnerProductSpace.toDual_apply_apply] using
      φ.continuous.comp_continuousOn (hH_apply_cont v)
  have hpair_int (v : E) :
      IntervalIntegrable (fun τ : ℝ ↦ inner ℝ v (H τ v)) MeasureTheory.volume 0 1 := by
    exact
      ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
        (show (0 : ℝ) ≤ 1 by norm_num) (hpair_cont v)
  have hpoint_lower (v : E) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
      ((1 - τ * a) ^ (2 : ℕ)) * inner ℝ v (hessian f x v) ≤ inner ℝ v (H τ v) := by
    have hlower :
        ((1 - τ * a) ^ (2 : ℕ)) • hessian f x ≤ H τ := by
      simpa [H, r, a] using
        (segment_point_hessian_bounds (hself := hself) (hx := hx) (hxy := hxy) (τ := τ) hτ).1
    have hgap_nonneg : 0 ≤ H τ - ((1 - τ * a) ^ (2 : ℕ)) • hessian f x := by
      simpa [ContinuousLinearMap.le_def] using hlower
    have hgap_pos :
        (H τ - ((1 - τ * a) ^ (2 : ℕ)) • hessian f x).IsPositive :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mp hgap_nonneg
    have hquad : 0 ≤ inner ℝ v ((H τ - ((1 - τ * a) ^ (2 : ℕ)) • hessian f x) v) :=
      hgap_pos.inner_nonneg_right v
    have hrewrite :
        inner ℝ v ((H τ - ((1 - τ * a) ^ (2 : ℕ)) • hessian f x) v) =
          inner ℝ v (H τ v) - ((1 - τ * a) ^ (2 : ℕ)) * inner ℝ v (hessian f x v) := by
      simp [inner_sub_right, inner_smul_right]
    rw [hrewrite] at hquad
    linarith
  have hpoint_upper (v : E) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
      inner ℝ v (H τ v) ≤
        ((1 - τ * a) ^ (2 : ℕ))⁻¹ * inner ℝ v (hessian f x v) := by
    have hupper :
        H τ ≤ ((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian f x := by
      simpa [H, r, a] using
        (segment_point_hessian_bounds (hself := hself) (hx := hx) (hxy := hxy) (τ := τ) hτ).2
    have hgap_nonneg : 0 ≤ ((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian f x - H τ := by
      simpa [ContinuousLinearMap.le_def] using hupper
    have hgap_pos :
        ((((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian f x) - H τ).IsPositive :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mp hgap_nonneg
    have hquad :
        0 ≤ inner ℝ v ((((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian f x - H τ) v) :=
      hgap_pos.inner_nonneg_right v
    have hrewrite :
        inner ℝ v ((((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian f x - H τ) v) =
          ((1 - τ * a) ^ (2 : ℕ))⁻¹ * inner ℝ v (hessian f x v) - inner ℝ v (H τ v) := by
      simp [inner_sub_right, inner_smul_right]
    rw [hrewrite] at hquad
    linarith
  have hscalar_lower (v : E) :
      (1 - (Mf : ℝ) * r + ((Mf : ℝ) ^ (2 : ℕ) * r ^ (2 : ℕ)) / 3) *
          inner ℝ v (hessian f x v) ≤
        inner ℝ v (G v) := by
    have hleft_cont :
        ContinuousOn
          (fun τ : ℝ ↦ ((1 - τ * a) ^ (2 : ℕ)) * inner ℝ v (hessian f x v))
          (Set.Icc (0 : ℝ) 1) := by
      exact
        (show Continuous (fun τ : ℝ ↦ ((1 - τ * a) ^ (2 : ℕ)) * inner ℝ v (hessian f x v)) by
          continuity).continuousOn
    have hleft_int :
        IntervalIntegrable
          (fun τ : ℝ ↦ ((1 - τ * a) ^ (2 : ℕ)) * inner ℝ v (hessian f x v))
          MeasureTheory.volume 0 1 := by
      exact
        ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
          (show (0 : ℝ) ≤ 1 by norm_num) hleft_cont
    have hmono :
        ∫ τ in (0 : ℝ)..1, ((1 - τ * a) ^ (2 : ℕ)) * inner ℝ v (hessian f x v) ≤
          ∫ τ in (0 : ℝ)..1, inner ℝ v (H τ v) := by
      exact intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
        hleft_int (hpair_int v) (fun τ hτ ↦ hpoint_lower v hτ)
    calc
      (1 - (Mf : ℝ) * r + ((Mf : ℝ) ^ (2 : ℕ) * r ^ (2 : ℕ)) / 3) *
          inner ℝ v (hessian f x v) = (1 - a + a ^ (2 : ℕ) / 3) *
            inner ℝ v (hessian f x v) := by
              dsimp [a]
              ring
      _ = ∫ τ in (0 : ℝ)..1, ((1 - τ * a) ^ (2 : ℕ)) * inner ℝ v (hessian f x v) := by
            rw [intervalIntegral.integral_mul_const, segment_lower_factor_integral]
      _ ≤ ∫ τ in (0 : ℝ)..1, inner ℝ v (H τ v) := hmono
      _ = inner ℝ v (G v) := hpair_integral v v
  have hscalar_upper (v : E) :
      inner ℝ v (G v) ≤
        (1 / (1 - (Mf : ℝ) * r)) * inner ℝ v (hessian f x v) := by
    have hden :
        ∀ τ ∈ Set.Icc (0 : ℝ) 1, 0 < 1 - τ * a := by
      intro τ hτ
      by_cases ha_nonneg' : 0 ≤ a
      · have hτa_le_a : τ * a ≤ a := by
          have hmul_le : τ * a ≤ 1 * a := mul_le_mul_of_nonneg_right hτ.2 ha_nonneg'
          simpa using hmul_le
        linarith
      · have hτa_le_zero : τ * a ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos hτ.1 (le_of_not_ge ha_nonneg')
        linarith
    have hright_cont :
        ContinuousOn
          (fun τ : ℝ ↦ ((1 - τ * a) ^ (2 : ℕ))⁻¹ * inner ℝ v (hessian f x v))
          (Set.Icc (0 : ℝ) 1) := by
      have hbase :
          ContinuousOn (fun τ : ℝ ↦ (1 : ℝ) / (1 - τ * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) 1) := by
        refine continuousOn_const.div ?_ ?_
        · exact (show Continuous (fun τ : ℝ ↦ (1 - τ * a) ^ (2 : ℕ)) by continuity).continuousOn
        · intro τ hτ
          exact pow_ne_zero 2 (hden τ hτ).ne'
      simpa [one_div] using hbase.mul continuousOn_const
    have hright_int :
        IntervalIntegrable
          (fun τ : ℝ ↦ ((1 - τ * a) ^ (2 : ℕ))⁻¹ * inner ℝ v (hessian f x v))
          MeasureTheory.volume 0 1 := by
      exact
        ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
          (show (0 : ℝ) ≤ 1 by norm_num) hright_cont
    have hmono :
        ∫ τ in (0 : ℝ)..1, inner ℝ v (H τ v) ≤
          ∫ τ in (0 : ℝ)..1, ((1 - τ * a) ^ (2 : ℕ))⁻¹ * inner ℝ v (hessian f x v) := by
      exact intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
        (hpair_int v) hright_int (fun τ hτ ↦ hpoint_upper v hτ)
    calc
      inner ℝ v (G v) = ∫ τ in (0 : ℝ)..1, inner ℝ v (H τ v) := (hpair_integral v v).symm
      _ ≤ ∫ τ in (0 : ℝ)..1, ((1 - τ * a) ^ (2 : ℕ))⁻¹ * inner ℝ v (hessian f x v) := hmono
      _ = (1 / (1 - a)) * inner ℝ v (hessian f x v) := by
            rw [intervalIntegral.integral_mul_const, segment_upper_factor_integral ha_lt_one]
      _ = (1 / (1 - (Mf : ℝ) * r)) * inner ℝ v (hessian f x v) := by
            simp [a]
  -- Reassemble the scalarized bounds into the desired Loewner comparisons.
  simpa [G] using
    loewner_bounds_of_scalarized_average_bounds
      (A := hessian f x)
      (G := G)
      (c := 1 - (Mf : ℝ) * r + ((Mf : ℝ) ^ (2 : ℕ) * r ^ (2 : ℕ)) / 3)
      (d := 1 / (1 - (Mf : ℝ) * r))
      hHxPos hG_symm hscalar_lower hscalar_upper

/-- Corollary 5.1.5 (lower bound): if `f` is self-concordant on `dom` with positive parameter
`M_f`, `x ∈ dom`, and `y ∈ W⁰[f; x](1 / (Mf : ℝ))`, then the average Hessian along the segment
from `x` to `y` dominates the explicit lower Loewner bound built from `∇² f(x)`. The positivity
of `M_f` and the membership `y ∈ dom` are consequences of the displayed open-Dikin hypothesis. -/
theorem segmentAverageHessian_lower_bound
    (hself : IsSelfConcordantOnWith dom Mf f) {x y : E} (hx : x ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))
    :
    let r := ‖y - x‖[f; x]
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    (1 - (Mf : ℝ) * r + ((Mf : ℝ) ^ (2 : ℕ) * r ^ (2 : ℕ)) / 3) • hessian f x ≤ G := by
  simpa using (segmentAverageHessian_bounds (hself := hself) (hx := hx) (hxy := hxy)).1

/-- Corollary 5.1.5 (upper bound): if `f` is self-concordant on `dom` with positive parameter
`M_f`, `x ∈ dom`, and `y ∈ W⁰[f; x](1 / (Mf : ℝ))`, then the average Hessian along the segment
from `x` to `y` is bounded above by the explicit Loewner bound built from `∇² f(x)`. The
positivity of `M_f` and the membership `y ∈ dom` are consequences of the displayed open-Dikin
hypothesis. -/
theorem segmentAverageHessian_upper_bound
    (hself : IsSelfConcordantOnWith dom Mf f) {x y : E} (hx : x ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))
    :
    let r := ‖y - x‖[f; x]
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    G ≤ (1 / (1 - (Mf : ℝ) * r)) • hessian f x := by
  simpa using (segmentAverageHessian_bounds (hself := hself) (hx := hx) (hxy := hxy)).2

end

end IsSelfConcordantOnWith

end
