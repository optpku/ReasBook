module

public import ReasLib.Optimization.DFP.Polar.InterpolationSum
public import ReasLib.Analysis.Calculus.Gradient.HessianHolder
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

public section

noncomputable section

open Set Filter
open scoped Topology InnerProduct BigOperators ContDiff

universe u

namespace DFP.Polar.AffineInterpolation

variable {E : Type u} [NormedAddCommGroup E]

section Normalization

variable [NormedSpace ℝ E]

/-- Helper for sec:center-approach and cm-limiting-scales: normalize the fixed
shifted circle to the unit sphere using its original positive radius. -/
def normalize (C : E) (G : ℝ) (x : E) : E := G⁻¹ • (x - C)

/-- Helper for sec:center-approach: the exact inverse affine coordinate map. -/
def denormalize (C : E) (G : ℝ) (z : E) : E := C + G • z

/-- Helper for sec:center-approach: the original affine normalization formula. -/
theorem normalize_apply (C : E) (G : ℝ) (x : E) :
    normalize C G x = G⁻¹ • (x - C) := by
  rfl

/-- Helper for sec:center-approach: the original inverse affine formula. -/
theorem denormalize_apply (C : E) (G : ℝ) (z : E) :
    denormalize C G z = C + G • z := by
  rfl

/-- Helper for sec:center-approach: normalizing the affine image recovers its coordinate. -/
theorem normalize_denormalize (C : E) {G : ℝ} (hG : G ≠ 0) (z : E) :
    normalize C G (denormalize C G z) = z := by
  simp only [normalize_apply, denormalize_apply, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ hG, one_smul]

/-- Helper for sec:center-approach: the original physical point is recovered exactly. -/
theorem denormalize_normalize (C : E) {G : ℝ} (hG : G ≠ 0) (x : E) :
    denormalize C G (normalize C G x) = x := by
  simp only [denormalize_apply, normalize_apply, smul_smul, mul_inv_cancel₀ hG, one_smul]
  abel

/-- Helper for sec:center-approach: differences from a physical center scale
by exactly G under the inverse coordinate map. -/
theorem denormalize_sub (C : E) {G : ℝ} (hG : G ≠ 0) (z x : E) :
    denormalize C G z - x = G • (z - normalize C G x) := by
  rw [denormalize_apply, normalize_apply, smul_sub, smul_smul, mul_inv_cancel₀ hG, one_smul]
  abel

/-- Helper for sec:center-approach: the normalized norm is the original radial
distance divided by the positive circle radius. -/
theorem norm_normalize (C : E) {G : ℝ} (hG : 0 < G) (x : E) :
    ‖normalize C G x‖ = ‖x - C‖ / G := by
  rw [normalize_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hG.le)]
  ring

/-- Helper for sec:center-approach: the normalized distance has its exact scalar factor. -/
theorem norm_normalize_sub (C : E) {G : ℝ} (hG : 0 < G) (x y : E) :
    ‖normalize C G x - normalize C G y‖ = ‖x - y‖ / G := by
  have hsub : normalize C G x - normalize C G y = G⁻¹ • (x - y) := by
    rw [normalize_apply, normalize_apply, ← smul_sub]
    congr 1
    abel
  rw [hsub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hG.le)]
  ring

/-- Helper for sec:center-approach: the normalized source center sequence. -/
def normalizedCenters (C : E) (G : ℝ) (c : ℕ → E) : ℕ → E := fun k ↦ normalize C G (c k)

/-- Helper for sec:center-approach: the source support radii in normalized coordinates. -/
def normalizedRadii (G : ℝ) (ρ : ℕ → ℝ) : ℕ → ℝ := fun k ↦ ρ k / G

/-- Helper for sec:center-approach: the normalized source affine coefficients. -/
def normalizedCoefficients (G : ℝ) (a : ℕ → E) : ℕ → E := fun k ↦ G⁻¹ • a k

/-- Helper for sec:center-approach: evaluation of normalized centers. -/
theorem normalizedCenters_apply (C : E) (G : ℝ) (c : ℕ → E) (k : ℕ) :
    normalizedCenters C G c k = normalize C G (c k) := by
  rfl

/-- Helper for sec:center-approach: evaluation of normalized radii. -/
theorem normalizedRadii_apply (G : ℝ) (ρ : ℕ → ℝ) (k : ℕ) :
    normalizedRadii G ρ k = ρ k / G := by
  rfl

/-- Helper for sec:center-approach: evaluation of normalized coefficients. -/
theorem normalizedCoefficients_apply (G : ℝ) (a : ℕ → E) (k : ℕ) :
    normalizedCoefficients G a k = G⁻¹ • a k := by
  rfl

/-- Helper for sec:center-approach: normalized coefficient norms have the
same positive inverse-radius factor as normalized support radii. -/
theorem norm_normalizedCoefficients {G : ℝ} (hG : 0 < G) (a : ℕ → E) (k : ℕ) :
    ‖normalizedCoefficients G a k‖ = G⁻¹ * ‖a k‖ := by
  rw [normalizedCoefficients_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hG.le)]

/-- Helper for sec:center-approach: the coefficient-to-radius ratio is
unchanged by the exact circle normalization. -/
theorem normalizedRatio_eq {G : ℝ} (hG : 0 < G)
    (ρ : ℕ → ℝ) (a : ℕ → E) (k : ℕ) :
    ‖normalizedCoefficients G a k‖ / normalizedRadii G ρ k = ‖a k‖ / ρ k := by
  rw [norm_normalizedCoefficients hG, normalizedRadii_apply]
  calc
    _ = (G⁻¹ * G) * (‖a k‖ / ρ k) := by
      rw [div_eq_mul_inv, inv_div]
      ring
    _ = _ := by rw [inv_mul_cancel₀ hG.ne', one_mul]

/-- Helper for sec:center-approach: normalized open balls are exactly the
inverse images of the ORIGINAL physical open balls. -/
theorem mem_normalizedBall_iff (C : E) {G : ℝ} (hG : 0 < G)
    (x z : E) (ρ : ℝ) :
    z ∈ Metric.ball (normalize C G x) (ρ / G) ↔
      denormalize C G z ∈ Metric.ball x ρ := by
  simp only [Metric.mem_ball, dist_eq_norm, denormalize_sub C hG.ne', norm_smul,
    Real.norm_of_nonneg hG.le]
  simpa only [mul_comm] using
    (lt_div_iff₀ hG : ‖z - normalize C G x‖ < ρ / G ↔
      ‖z - normalize C G x‖ * G < ρ)

/-- Helper for sec:center-approach: the manuscript's assumed disjoint OPEN
balls remain disjoint under exact circle normalization. -/
theorem normalizedBalls_disjoint (C : E) {G : ℝ} (hG : 0 < G)
    (c : ℕ → E) (ρ : ℕ → ℝ)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))) :
    Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (normalizedCenters C G c k)
      (normalizedRadii G ρ k)) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hleft : denormalize C G z ∈ Metric.ball (c i) (ρ i) :=
    (mem_normalizedBall_iff C hG (c i) z (ρ i)).mp hzi
  have hright : denormalize C G z ∈ Metric.ball (c j) (ρ j) :=
    (mem_normalizedBall_iff C hG (c j) z (ρ j)).mp hzj
  exact (Set.disjoint_left.mp (hballs hi hj hij)) hleft hright

/-- Helper for sec:center-approach: the scalar affine map is smooth of every
finite order, including the fixed shifted-circle coordinate change. -/
theorem normalize_contDiff (C : E) (G : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (normalize C G) := by
  have hfun : normalize C G = fun x ↦ G⁻¹ • (x - C) := funext (normalize_apply C G)
  rw [hfun]
  exact (contDiff_id.sub contDiff_const).const_smul G⁻¹

/-- Helper for sec:center-approach: the exact scalar derivative of the
normalized coordinate map. -/
theorem normalize_hasFDerivAt (C : E) (G : ℝ) (x : E) :
    HasFDerivAt (normalize C G) (G⁻¹ • (1 : E →L[ℝ] E)) x := by
  have h : HasFDerivAt (fun y : E ↦ G⁻¹ • (y - C)) (G⁻¹ • (1 : E →L[ℝ] E)) x :=
    ((hasFDerivAt_id x).sub_const C).const_smul (G⁻¹ : ℝ)
  simpa only [← normalize_apply] using h

/-- Helper for sec:center-approach: the scalar G² pullback of a normalized
function, matching the exact physical source correction sum. -/
def scaledPullback (C : E) (G : ℝ) (f : E → ℝ) : E → ℝ :=
  fun x ↦ G ^ 2 * f (normalize C G x)

/-- Helper for sec:center-approach: evaluation of the exact scalar pullback. -/
theorem scaledPullback_apply (C : E) (G : ℝ) (f : E → ℝ) (x : E) :
    scaledPullback C G f x = G ^ 2 * f (normalize C G x) := by
  rfl

/-- Helper for sec:center-approach: the scalar pullback preserves C²
regularity once it has been PROVED for the normalized source sum. -/
theorem scaledPullback_contDiff (C : E) (G : ℝ) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (scaledPullback C G f) := by
  have hfun : scaledPullback C G f = fun x ↦ G ^ 2 * f (normalize C G x) :=
    funext (scaledPullback_apply C G f)
  rw [hfun]
  exact contDiff_const.mul (hf.comp (normalize_contDiff C G))

/-- Helper for sec:center-approach: one scalar factor cancels in the first
derivative of G² times the normalized function. -/
theorem fderiv_scaledPullback (C : E) {G : ℝ} (hG : G ≠ 0)
    {f : E → ℝ} (hf : Differentiable ℝ f) (x : E) :
    fderiv ℝ (scaledPullback C G f) x = G • fderiv ℝ f (normalize C G x) := by
  have hraw := (((hf (normalize C G x)).hasFDerivAt).comp x
    (normalize_hasFDerivAt C G x)).const_smul (G ^ 2)
  have hfun : scaledPullback C G f = G ^ 2 • (f ∘ normalize C G) := by
    funext y
    rw [scaledPullback_apply]
    rfl
  rw [hfun, hraw.fderiv]
  have hfactor : G ^ 2 * G⁻¹ = G := by field_simp [hG]
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self,
    map_smul, smul_smul, hfactor]

end Normalization

/-- Helper for cm-limiting-scales: quadratic support radii have precisely the
inverse three-halves power that cancels a cubic source coefficient. -/
theorem quadraticRadiusPower {t κ : ℝ} (ht : 0 < t) (hκ : 0 < κ) :
    (κ * t ^ 2) ^ (-3 / 2 : ℝ) = κ ^ (-3 / 2 : ℝ) * (t ^ 3)⁻¹ := by
  have hexponent : (2 : ℝ) * (-3 / 2) = -3 := by norm_num
  rw [Real.mul_rpow hκ.le (sq_nonneg t), ← Real.rpow_natCast_mul ht.le]
  simp only [Nat.cast_ofNat]
  rw [hexponent, Real.rpow_neg ht.le, Real.rpow_ofNat]

/-- Helper for cm-limiting-scales: cubic coefficients and a quadratic lower
radius bound give the linear, inverse-linear and uniform half-Hölder envelopes. -/
theorem coefficientScaleBounds {t ρ s A κ : ℝ} (ht : 0 < t) (hκ : 0 < κ)
    (hs : 0 ≤ s) (hA : 0 ≤ A) (hρ : κ * t ^ 2 ≤ ρ) (ha : s ≤ A * t ^ 3) :
    s / ρ ≤ (A / κ) * t ∧
      s / ρ ^ 2 ≤ (A / κ ^ 2) * t⁻¹ ∧
      s * ρ ^ (-3 / 2 : ℝ) ≤ A * κ ^ (-3 / 2 : ℝ) := by
  have hlower : 0 < κ * t ^ 2 := mul_pos hκ (sq_pos_of_pos ht)
  have hpositive : 0 < ρ := hlower.trans_le hρ
  refine ⟨?_, ?_, ?_⟩
  · calc
      s / ρ ≤ s / (κ * t ^ 2) := div_le_div_of_nonneg_left hs hlower hρ
      _ ≤ (A * t ^ 3) / (κ * t ^ 2) := div_le_div_of_nonneg_right ha hlower.le
      _ = _ := by field_simp [ht.ne', hκ.ne']
  · have hsquare : (κ * t ^ 2) ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hlower.le hρ 2
    calc
      s / ρ ^ 2 ≤ s / (κ * t ^ 2) ^ 2 :=
        div_le_div_of_nonneg_left hs (sq_pos_of_pos hlower) hsquare
      _ ≤ (A * t ^ 3) / (κ * t ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right ha (sq_nonneg _)
      _ = _ := by field_simp [ht.ne', hκ.ne']
  · have hexponent : (-3 / 2 : ℝ) ≤ 0 := by norm_num
    have hpower := Real.rpow_le_rpow_of_nonpos hlower hρ hexponent
    have hproduct := mul_le_mul ha hpower (Real.rpow_nonneg hpositive.le _)
      (mul_nonneg hA (pow_nonneg ht.le 3))
    apply hproduct.trans_eq
    rw [quadraticRadiusPower ht hκ]
    field_simp [ht.ne']

section Geometry

variable [NormedSpace ℝ E]

/-- Helper for sec:center-approach and cm-limiting-scales: raw linear radial
orders, quadratic radii, cubic coefficients and a small global cap imply every
PURE field of normalized Geometry. No analytic regularity is a premise. -/
theorem normalizedGeometry_of_scaleBounds (C : E) {G : ℝ} (hG : 0 < G)
    (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (t : ℕ → ℝ)
    (radialLower radialUpper κLow κHigh A tCap : ℝ)
    (hLower : 0 < radialLower) (hκLow : 0 < κLow) (hκHigh : 0 < κHigh)
    (hA : 0 ≤ A) (hCap : 0 < tCap)
    (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0)) (htBound : ∀ k, t k ≤ tCap)
    (hradial : ∀ k, radialLower * t k ≤ ‖c k - C‖ - G ∧
      ‖c k - C‖ - G ≤ radialUpper * t k)
    (hradii : ∀ k, κLow * t k ^ 2 ≤ ρ k ∧ ρ k ≤ κHigh * t k ^ 2)
    (hcoefficients : ∀ k, ‖a k‖ ≤ A * t k ^ 3)
    (hsmall : 4 * κHigh * tCap < radialLower)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))) :
    InterpolationSum.Geometry (normalizedCenters C G c) (normalizedRadii G ρ)
      (normalizedCoefficients G a) := by
  have hρ : ∀ k, 0 < ρ k := by
    intro k
    exact (mul_pos hκLow (sq_pos_of_pos (ht k))).trans_le (hradii k).1
  have hgap : ∀ k, 0 ≤ ‖c k - C‖ - G := by
    intro k
    exact (mul_pos hLower (ht k)).le.trans (hradial k).1
  have hupperLimit : Tendsto (fun k ↦ radialUpper * t k) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht0.const_mul radialUpper
  have hgapLimit : Tendsto (fun k ↦ ‖c k - C‖ - G) atTop (𝓝 0) :=
    squeeze_zero hgap (fun k ↦ (hradial k).2) hupperLimit
  have hnormLimit : Tendsto (fun k ↦ ‖c k - C‖) atTop (𝓝 G) := by
    simpa only [sub_add_cancel, zero_add] using hgapLimit.add_const G
  have hnormalizedLimit : Tendsto (fun k ↦ ‖normalizedCenters C G c k‖) atTop (𝓝 1) := by
    simp only [normalizedCenters_apply, norm_normalize C hG]
    simpa only [div_self hG.ne'] using hnormLimit.div_const G
  have hratioBound : ∀ k,
      ‖normalizedCoefficients G a k‖ / normalizedRadii G ρ k ≤ (A / κLow) * t k := by
    intro k
    rw [normalizedRatio_eq hG]
    exact (coefficientScaleBounds (ht k) hκLow (norm_nonneg _) hA
      (hradii k).1 (hcoefficients k)).1
  have hratioNonnegative : ∀ k, 0 ≤
      ‖normalizedCoefficients G a k‖ / normalizedRadii G ρ k := by
    intro k
    rw [normalizedRatio_eq hG]
    exact div_nonneg (norm_nonneg _) (hρ k).le
  have hratioLimit : Tendsto
      (fun k ↦ ‖normalizedCoefficients G a k‖ / normalizedRadii G ρ k) atTop (𝓝 0) := by
    have hupper : Tendsto (fun k ↦ (A / κLow) * t k) atTop (𝓝 0) := by
      simpa only [mul_zero] using ht0.const_mul (A / κLow)
    exact squeeze_zero hratioNonnegative hratioBound hupper
  refine ⟨?_, normalizedBalls_disjoint C hG c ρ hballs, hnormalizedLimit, ?_, hratioLimit⟩
  · intro k
    rw [normalizedRadii_apply]
    exact div_pos (hρ k) hG
  · intro k
    have hcapProduct : 0 ≤ κHigh * tCap := mul_nonneg hκHigh.le hCap.le
    have hcoefficient : 2 * κHigh * t k ≤ radialLower := by
      have hscaled := mul_le_mul_of_nonneg_left (htBound k) (mul_nonneg zero_le_two hκHigh.le)
      nlinarith
    have hmargin : G + 2 * ρ k ≤ ‖c k - C‖ := by
      have hlinear := mul_le_mul_of_nonneg_right hcoefficient (ht k).le
      nlinarith [(hradii k).2, (hradial k).1]
    rw [normalizedCenters_apply, norm_normalize C hG, normalizedRadii_apply]
    calc
      1 + 2 * (ρ k / G) = (G + 2 * ρ k) / G := by field_simp [hG.ne']
      _ ≤ ‖c k - C‖ / G := div_le_div_of_nonneg_right hmargin hG.le

end Geometry

section Cutoff

variable [InnerProductSpace ℝ E]

/-- Helper for sec:center-approach: the SAME original χ correction transforms
by the exact factor G² under the shifted/scaled-circle coordinate map. -/
theorem bump_denormalize (C : E) {G : ℝ} (hG : G ≠ 0)
    (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (k : ℕ) (z : E) :
    InterpolationSum.bump c ρ a k (denormalize C G z) = G ^ 2 *
      InterpolationSum.bump (normalizedCenters C G c) (normalizedRadii G ρ)
        (normalizedCoefficients G a) k z := by
  have hargument : ∀ v : E, (ρ k)⁻¹ • (G • v) = (ρ k / G)⁻¹ • v := by
    intro v
    rw [smul_smul, inv_div, div_eq_mul_inv]
    congr 1
    ring
  have hfactor : G ^ 2 * G⁻¹ = G := by field_simp [hG]
  simp only [InterpolationSum.bump_apply, normalizedCenters_apply, normalizedRadii_apply,
    normalizedCoefficients_apply, denormalize_sub C hG, hargument,
    inner_smul_right, real_inner_smul_left]
  calc
    _ = G * (ExplicitCutoff.chi ((ρ k / G)⁻¹ • (z - normalize C G (c k))) *
        inner ℝ (a k) (z - normalize C G (c k))) := by ring
    _ = (G ^ 2 * G⁻¹) *
        (ExplicitCutoff.chi ((ρ k / G)⁻¹ • (z - normalize C G (c k))) *
          inner ℝ (a k) (z - normalize C G (c k))) := by rw [hfactor]
    _ = _ := by ring

/-- Helper for sec:center-approach: exact affine normalization of the original
pointwise correction sum, with unchanged η/χ and unchanged physical bumps. -/
theorem perturbation_denormalize (C : E) {G : ℝ} (hG : G ≠ 0)
    (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (z : E) :
    InterpolationSum.perturbation c ρ a (denormalize C G z) = G ^ 2 *
      InterpolationSum.perturbation (normalizedCenters C G c) (normalizedRadii G ρ)
        (normalizedCoefficients G a) z := by
  simp only [InterpolationSum.perturbation_apply, bump_denormalize C hG, ← mul_finsum]

/-- Helper for sec:center-approach: the manuscript's normalization is precisely
G⁻² times the physical sum evaluated at C+Gz. -/
theorem normalizedPerturbation_eq (C : E) {G : ℝ} (hG : G ≠ 0)
    (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (z : E) :
    (1 / G ^ 2) * InterpolationSum.perturbation c ρ a (denormalize C G z) =
      InterpolationSum.perturbation (normalizedCenters C G c) (normalizedRadii G ρ)
        (normalizedCoefficients G a) z := by
  rw [perturbation_denormalize C hG, one_div, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 2 hG), one_mul]

/-- Helper for sec:center-approach: the existing generic bump is exactly the
accepted explicit-χ affine correction, without any alteration of its support boundary. -/
theorem bump_eq_correction (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (k : ℕ) :
    InterpolationSum.bump c ρ a k = ExplicitCutoff.correction (c k) (ρ k) (a k) := by
  funext x
  rw [InterpolationSum.bump_apply, ExplicitCutoff.correction_apply]

/-- Helper for sec:center-approach: every derivative of an original bump vanishes
on and outside its TRUE closed support boundary. -/
theorem bump_boundary_jet_zero (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (k n : ℕ) (hρ : 0 < ρ k) {x : E} (hx : ρ k ≤ ‖x - c k‖) :
    iteratedFDeriv ℝ n (InterpolationSum.bump c ρ a k) x = 0 := by
  rw [bump_eq_correction]
  exact InterpolationBounds.iteratedFDeriv_correction_eq_zero_of_radius_le_norm_sub
    n (c k) (ρ k) (a k) x hρ hx

/-- Helper for sec:center-approach: the original function support lies in its
OPEN ball even though its topological support has the closed boundary. -/
theorem bump_support_subset_ball (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (hρ : ∀ k, 0 < ρ k) (k : ℕ) :
    Function.support (InterpolationSum.bump c ρ a k) ⊆ Metric.ball (c k) (ρ k) := by
  intro x hx
  by_contra hout
  have hnorm : ρ k ≤ ‖x - c k‖ := by
    simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hout
  apply hx
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ), bump_boundary_jet_zero c ρ a k 0 (hρ k) hnorm,
    norm_zero]

/-- Helper for sec:center-approach: assumed disjoint original OPEN balls make
the actual source correction family pointwise summable, without any circle margin. -/
theorem summable_bumps_of_disjoint (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (hρ : ∀ k, 0 < ρ k)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))) (x : E) :
    Summable (fun k ↦ InterpolationSum.bump c ρ a k x) := by
  exact summable_of_hasFiniteSupport
    (InterpolationSum.support_apply_subsingleton (InterpolationSum.bump c ρ a) _ hballs
      (bump_support_subset_ball c ρ a hρ) x).finite

/-- Helper for sec:center-approach: the full original pointwise correction sum
is the literal manuscript infinite sum under its explicit disjointness assumption. -/
theorem perturbation_eq_tsum_of_disjoint (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (hρ : ∀ k, 0 < ρ k)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))) (x : E) :
    InterpolationSum.perturbation c ρ a x = ∑' k, InterpolationSum.bump c ρ a k x := by
  rw [InterpolationSum.perturbation_apply]
  exact (tsum_eq_finsum
    (InterpolationSum.support_apply_subsingleton (InterpolationSum.bump c ρ a) _ hballs
      (bump_support_subset_ball c ρ a hρ) x).finite).symm

/-- Helper for sec:center-approach: on an original open support ball the full
source sum equals that ball's own bump, including where the affine factor vanishes. -/
theorem perturbation_eq_bump_on_ball (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (hρ : ∀ k, 0 < ρ k)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k)))
    (k : ℕ) {x : E} (hx : x ∈ Metric.ball (c k) (ρ k)) :
    InterpolationSum.perturbation c ρ a x = InterpolationSum.bump c ρ a k x := by
  rw [InterpolationSum.perturbation_apply]
  apply finsum_eq_single
  intro i hik
  by_contra hne
  exact hik (hballs.elim_set (Set.mem_univ i) (Set.mem_univ k) x
    (bump_support_subset_ball c ρ a hρ i hne) hx)

/-- Helper for sec:center-approach: the full original sum agrees locally with
its own smooth bump at every designated center, without an early-ball margin assumption. -/
theorem perturbation_eventuallyEq_bump (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (hρ : ∀ k, 0 < ρ k)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))) (k : ℕ) :
    InterpolationSum.perturbation c ρ a =ᶠ[𝓝 (c k)] InterpolationSum.bump c ρ a k := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hρ k))] with x hx
  exact perturbation_eq_bump_on_ball c ρ a hρ hballs k hx

/-- Helper for sec:center-approach: the actual finite prefix that is restored
after applying normalized Geometry on a sufficiently late tail. -/
def finiteCorrectionSum (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (N : ℕ) : E → ℝ :=
  fun x ↦ ∑ k ∈ Finset.range N, InterpolationSum.bump c ρ a k x

/-- Helper for sec:center-approach: the finite prefix keeps every original bump. -/
theorem finiteCorrectionSum_apply (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (N : ℕ) (x : E) :
    finiteCorrectionSum c ρ a N x = ∑ k ∈ Finset.range N, InterpolationSum.bump c ρ a k x := by
  rfl

/-- Helper for sec:center-approach: the correction on a reindexed tail is
exactly the corresponding original correction. -/
theorem bump_tail_apply (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (N n : ℕ) (x : E) :
    InterpolationSum.bump (fun k ↦ c (k + N)) (fun k ↦ ρ (k + N))
      (fun k ↦ a (k + N)) n x = InterpolationSum.bump c ρ a (n + N) x := by
  simp only [InterpolationSum.bump_apply]

/-- Helper for sec:center-approach: a tail of the assumed disjoint original
open balls is still disjoint. -/
theorem tailBalls_disjoint {F : Type*} [PseudoMetricSpace F] (c : ℕ → F) (ρ : ℕ → ℝ)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))) (N : ℕ) :
    Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c (k + N)) (ρ (k + N))) := by
  intro i _ j _ hij
  apply hballs (Set.mem_univ _) (Set.mem_univ _)
  intro heq
  exact hij (Nat.add_right_cancel heq)

/-- Helper for sec:center-approach: exact prefix-plus-tail decomposition of the
FULL source sum. Taking a late tail for gluing does not discard any original bump. -/
theorem perturbation_split (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (hρ : ∀ k, 0 < ρ k)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))) (N : ℕ) :
    InterpolationSum.perturbation c ρ a = finiteCorrectionSum c ρ a N +
      InterpolationSum.perturbation (fun k ↦ c (k + N)) (fun k ↦ ρ (k + N))
        (fun k ↦ a (k + N)) := by
  funext x
  simp only [Pi.add_apply, finiteCorrectionSum_apply,
    perturbation_eq_tsum_of_disjoint c ρ a hρ hballs,
    perturbation_eq_tsum_of_disjoint _ _ _ (fun k ↦ hρ (k + N)) (tailBalls_disjoint c ρ hballs N),
    bump_tail_apply]
  exact ((summable_bumps_of_disjoint c ρ a hρ hballs x).sum_add_tsum_nat_add N).symm

/-- Helper for sec:center-approach: every finite prefix of the unchanged original
χ corrections is smooth, independently of its position relative to the limiting circle. -/
theorem finiteCorrectionSum_contDiff (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (N : ℕ) :
    ContDiff ℝ ∞ (finiteCorrectionSum c ρ a N) := by
  have hfun : finiteCorrectionSum c ρ a N =
      fun x ↦ ∑ k ∈ Finset.range N, InterpolationSum.bump c ρ a k x :=
    funext (finiteCorrectionSum_apply c ρ a N)
  rw [hfun]
  exact ContDiff.sum (fun k _ ↦ InterpolationSum.contDiff_bump c ρ a k)

section Calculus

variable [CompleteSpace E]

/-- Helper for sec:center-approach: the normalized-gradient scalar factor
cancels exactly to G for the original G² pullback. -/
theorem gradient_scaledPullback (C : E) {G : ℝ} (hG : G ≠ 0)
    {f : E → ℝ} (hf : Differentiable ℝ f) (x : E) :
    gradient (scaledPullback C G f) x = G • gradient f (normalize C G x) := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient, map_smul, toDual_gradient]
  exact fderiv_scaledPullback C hG hf x

/-- Helper for sec:center-approach: the G² value factor and the two G⁻¹
derivative factors cancel EXACTLY in the canonical Hessian operator. -/
theorem hessian_scaledPullback (C : E) {G : ℝ} (hG : G ≠ 0)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    hessian (scaledPullback C G f) x = hessian f (normalize C G x) := by
  have hdiff : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hgradDiff : Differentiable ℝ (gradient f) :=
    (hf.gradient_succ (n := 1)).differentiable_one
  have hgrad : gradient (scaledPullback C G f) = G • (gradient f ∘ normalize C G) :=
    funext (gradient_scaledPullback C hG hdiff)
  have hraw := ((hgradDiff (normalize C G x)).hasFDerivAt.comp x
    (normalize_hasFDerivAt C G x)).const_smul G
  rw [hessian_def, hgrad, hraw.fderiv, hessian_def]
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self,
    map_smul, smul_smul, mul_inv_cancel₀ hG, one_smul]

/-- Helper for sec:center-approach: the Hessian is the fixed Riesz isometry
applied on the left to the ordinary second derivative. -/
theorem hessian_rieszComp (f : E → ℝ) (x : E) :
    hessian f x = ((InnerProductSpace.toDual ℝ E).symm : StrongDual ℝ E →L[ℝ] E) ∘L
      fderiv ℝ (fderiv ℝ f) x := by
  have hfun : gradient f = (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f := rfl
  rw [hessian_def, hfun]
  exact LinearIsometryEquiv.comp_fderiv (InnerProductSpace.toDual ℝ E).symm

/-- Helper for sec:center-approach: canonical Hessian difference norms equal
ordinary second-derivative difference norms, so the accepted χ estimates transfer exactly. -/
theorem norm_hessianDifference_eq (f : E → ℝ) (x y : E) :
    ‖hessian f x - hessian f y‖ =
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
  rw [hessian_rieszComp, hessian_rieszComp, ← ContinuousLinearMap.comp_sub]
  exact LinearIsometry.norm_toContinuousLinearMap_comp
    (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry

/-- Helper for sec:center-approach: canonical Hessian norms equal ordinary
second-derivative norms under the fixed Riesz isometry. -/
theorem norm_hessian_eq (f : E → ℝ) (x : E) :
    ‖hessian f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  rw [hessian_def, norm_fderiv_gradient_eq_norm_fderiv_fderiv]

/-- Helper for sec:center-approach: gradients add for differentiable scalar
functions, as a direct consequence of the canonical differential/Riesz interface. -/
theorem gradient_add {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : E) :
    gradient (f + g) x = gradient f x + gradient g x := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient, map_add, toDual_gradient, toDual_gradient]
  exact fderiv_add (hf x) (hg x)

/-- Helper for sec:center-approach: the Hessian of a C² finite sum is the sum
of its Hessians, allowing restoration of the original early corrections. -/
theorem hessian_add {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    hessian (f + g) x = hessian f x + hessian g x := by
  have hgrad : gradient (f + g) = gradient f + gradient g :=
    funext (gradient_add (hf.differentiable two_ne_zero) (hg.differentiable two_ne_zero))
  have hdf := (hf.gradient_succ (n := 1)).differentiable_one
  have hdg := (hg.gradient_succ (n := 1)).differentiable_one
  rw [hessian_def, hgrad, fderiv_add (hdf x) (hdg x), hessian_def, hessian_def]

/-- Helper for sec:center-approach: the canonical Hessian of the zero function vanishes. -/
theorem hessian_zero (x : E) : hessian (fun _ : E ↦ (0 : ℝ)) x = 0 := by
  have hderivative : fderiv ℝ (fun _ : E ↦ (0 : ℝ)) = fun _ ↦ (0 : E →L[ℝ] ℝ) := by
    funext y
    exact fderiv_const_apply (0 : ℝ)
  have hsecond : fderiv ℝ (fun _ : E ↦ (0 : E →L[ℝ] ℝ)) x = 0 :=
    fderiv_const_apply (0 : E →L[ℝ] ℝ)
  rw [hessian_rieszComp, hderivative, hsecond, ContinuousLinearMap.comp_zero]

/-- Helper for sec:center-approach: a finite family of C² original corrections
has exactly the finite sum of its Hessian operators. -/
theorem hessian_finiteSum {ι : Type*}
    (s : Finset ι) (f : ι → E → ℝ) :
    (∀ i ∈ s, ContDiff ℝ 2 (f i)) → ∀ x,
      hessian (fun y ↦ ∑ i ∈ s, f i y) x = ∑ i ∈ s, hessian (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _ x
      simpa only [Finset.sum_empty] using hessian_zero (E := E) x
  | @insert i s hi ih =>
      intro hf x
      have hfi := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, ContDiff ℝ 2 (f j) := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hfun : (fun y ↦ ∑ j ∈ insert i s, f j y) =
          f i + (fun y ↦ ∑ j ∈ s, f j y) := by
        funext y
        simp only [Finset.sum_insert hi, Pi.add_apply]
      rw [hfun, hessian_add hfi (ContDiff.sum hfs), ih hfs, Finset.sum_insert hi]

/-- Helper for sec:center-approach: a finite sum of global half-Hölder Hessian
bounds gives the sum of the original constants, with no small-cap assumption. -/
theorem hessian_finiteSum_holder {ι : Type*}
    (s : Finset ι) (f : ι → E → ℝ) (H : ι → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i))
    (hholder : ∀ i ∈ s, ∀ x y, ‖hessian (f i) x - hessian (f i) y‖ ≤
      H i * ‖x - y‖ ^ (1 / 2 : ℝ)) (x y : E) :
    ‖hessian (fun z ↦ ∑ i ∈ s, f i z) x - hessian (fun z ↦ ∑ i ∈ s, f i z) y‖ ≤
      (∑ i ∈ s, H i) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  rw [hessian_finiteSum s f hf, hessian_finiteSum s f hf, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, ‖hessian (f i) x - hessian (f i) y‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, H i * ‖x - y‖ ^ (1 / 2 : ℝ) := Finset.sum_le_sum (fun i hi ↦ hholder i hi x y)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Helper for sec:center-approach: the original explicit-χ correction has
zero value and Hessian and prescribed gradient at its own center. -/
theorem bump_center_jets (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (k : ℕ) (hρ : 0 < ρ k) :
    InterpolationSum.bump c ρ a k (c k) = 0 ∧
      gradient (InterpolationSum.bump c ρ a k) (c k) = a k ∧
      hessian (InterpolationSum.bump c ρ a k) (c k) = 0 := by
  rw [bump_eq_correction]
  refine ⟨ExplicitCutoff.correction_apply_center _ _ _, ?_, ?_⟩
  · apply (InnerProductSpace.toDual ℝ E).injective
    rw [toDual_gradient, ExplicitCutoff.fderiv_correction_center _ _ _ hρ]
    rfl
  · apply norm_eq_zero.mp
    rw [norm_hessian_eq, ExplicitCutoff.secondFDeriv_correction_center _ _ _ hρ, norm_zero]

/-- Helper for sec:center-approach: exact center jets hold for the FULL source
sum from disjointness alone, even if some early balls have no circle margin. -/
theorem perturbation_center_jets (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (hρ : ∀ k, 0 < ρ k)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))) (k : ℕ) :
    InterpolationSum.perturbation c ρ a (c k) = 0 ∧
      gradient (InterpolationSum.perturbation c ρ a) (c k) = a k ∧
      hessian (InterpolationSum.perturbation c ρ a) (c k) = 0 := by
  have hlocal := perturbation_eventuallyEq_bump c ρ a hρ hballs k
  have hjet := bump_center_jets c ρ a k (hρ k)
  have hHessian : hessian (InterpolationSum.perturbation c ρ a) (c k) =
      hessian (InterpolationSum.bump c ρ a k) (c k) := by
    rw [hessian_def, hessian_def]
    exact hlocal.gradient.fderiv_eq
  exact ⟨hlocal.self_of_nhds.trans hjet.1, hlocal.gradient_eq.trans hjet.2.1,
    hHessian.trans hjet.2.2⟩


omit [CompleteSpace E] in
/-- Helper for sec:center-approach: the physical source sum is exactly the
G² pullback of its normalized SAME-χ sum. -/
theorem perturbation_eq_scaledPullback (C : E) {G : ℝ} (hG : G ≠ 0)
    (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) :
    InterpolationSum.perturbation c ρ a = scaledPullback C G
      (InterpolationSum.perturbation (normalizedCenters C G c) (normalizedRadii G ρ)
        (normalizedCoefficients G a)) := by
  funext x
  rw [scaledPullback_apply, ← perturbation_denormalize C hG,
    denormalize_normalize C hG]

variable [FiniteDimensional ℝ E] [Nontrivial E]

omit [CompleteSpace E] in
/-- Helper for sec:center-approach: normalized pure geometry proves C² of
the original shifted-circle sum by the accepted explicit-χ gluing theorem. -/
theorem perturbation_contDiff_of_normalizedGeometry (C : E) {G : ℝ} (hG : G ≠ 0)
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : InterpolationSum.Geometry (normalizedCenters C G c) (normalizedRadii G ρ)
      (normalizedCoefficients G a)) :
    ContDiff ℝ 2 (InterpolationSum.perturbation c ρ a) := by
  rw [perturbation_eq_scaledPullback C hG]
  exact scaledPullback_contDiff C G (InterpolationSum.contDiff_perturbation h)

/-- Helper for sec:center-approach: a global support margin gives a vanishing
two-jet throughout the original closed disk, including its circle boundary. -/
theorem perturbation_disk_jets (C : E) {G : ℝ} (hG : 0 < G)
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : InterpolationSum.Geometry (normalizedCenters C G c) (normalizedRadii G ρ)
      (normalizedCoefficients G a)) {x : E} (hx : ‖x - C‖ ≤ G) :
    InterpolationSum.perturbation c ρ a x = 0 ∧
      gradient (InterpolationSum.perturbation c ρ a) x = 0 ∧
      hessian (InterpolationSum.perturbation c ρ a) x = 0 := by
  have hnormalized : ‖normalize C G x‖ ≤ 1 := by
    rw [norm_normalize C hG]
    exact (div_le_one hG).mpr hx
  have hsmooth := InterpolationSum.contDiff_perturbation h
  rw [perturbation_eq_scaledPullback C hG.ne']
  refine ⟨?_, ?_, ?_⟩
  · rw [scaledPullback_apply,
      InterpolationSum.perturbation_eq_zero_of_norm_le_one h hnormalized, mul_zero]
  · rw [gradient_scaledPullback C hG.ne' (hsmooth.differentiable two_ne_zero),
      InterpolationSum.gradient_perturbation_eq_zero_of_norm_le_one h hnormalized, smul_zero]
  · rw [hessian_scaledPullback C hG.ne' hsmooth, hessian_rieszComp,
      InterpolationSum.secondFDeriv_perturbation_eq_zero_of_norm_le_one h hnormalized,
      ContinuousLinearMap.comp_zero]

/-- Helper for sec:center-approach: the exact affine Hessian cancellation
transports both global size and half-Hölder bounds of the normalized sum. -/
theorem hessianBounds_of_normalizedGeometry (C : E) {G : ℝ} (hG : 0 < G)
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : InterpolationSum.Geometry (normalizedCenters C G c) (normalizedRadii G ρ)
      (normalizedCoefficients G a)) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hsize : ∀ k, ‖normalizedCoefficients G a k‖ / normalizedRadii G ρ k ≤ B)
    (hscaled : ∀ k, ‖normalizedCoefficients G a k‖ *
      (normalizedRadii G ρ k) ^ (-3 / 2 : ℝ) ≤ M) :
    ∃ D H : ℝ, 0 ≤ D ∧ 0 < H ∧
      (∀ x, ‖hessian (InterpolationSum.perturbation c ρ a) x‖ ≤ D * B) ∧
      (∀ x y, ‖hessian (InterpolationSum.perturbation c ρ a) x -
        hessian (InterpolationSum.perturbation c ρ a) y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) := by
  obtain ⟨D, hD, hbound⟩ := InterpolationSum.exists_global_hessian_bounds (E := E)
  have hb := hbound _ _ _ h B M hB hM hsize hscaled
  have hsmooth := InterpolationSum.contDiff_perturbation h
  have hconstant : 0 ≤ 2 * D * M * (G⁻¹) ^ (1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hD) hM)
      (Real.rpow_nonneg (inv_nonneg.mpr hG.le) _)
  refine ⟨D, 2 * D * M * (G⁻¹) ^ (1 / 2 : ℝ) + 1, hD,
    lt_add_of_le_of_pos hconstant zero_lt_one, ?_, ?_⟩
  · intro x
    rw [perturbation_eq_scaledPullback C hG.ne', hessian_scaledPullback C hG.ne' hsmooth,
      norm_hessian_eq]
    exact hb.1 _
  · intro x y
    rw [perturbation_eq_scaledPullback C hG.ne', hessian_scaledPullback C hG.ne' hsmooth,
      hessian_scaledPullback C hG.ne' hsmooth, norm_hessianDifference_eq]
    calc
      _ ≤ 2 * D * M * ‖normalize C G x - normalize C G y‖ ^ (1 / 2 : ℝ) := hb.2 _ _
      _ = (2 * D * M * (G⁻¹) ^ (1 / 2 : ℝ)) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
        rw [norm_normalize_sub C hG, div_eq_mul_inv,
          Real.mul_rpow (norm_nonneg _) (inv_nonneg.mpr hG.le)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Real.rpow_nonneg (norm_nonneg _) _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Helper for cm-limiting-scales: the cubic coefficient and quadratic
radius orders imply a uniform normalized half-Hölder coefficient envelope. -/
theorem normalizedScaledCoefficientBound {G : ℝ} (hG : 0 < G)
    (ρ : ℕ → ℝ) (a : ℕ → E) (t : ℕ → ℝ) {κ A : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (ht : ∀ k, 0 < t k)
    (hρ : ∀ k, κ * t k ^ 2 ≤ ρ k) (ha : ∀ k, ‖a k‖ ≤ A * t k ^ 3) (k : ℕ) :
    ‖normalizedCoefficients G a k‖ * (normalizedRadii G ρ k) ^ (-3 / 2 : ℝ) ≤
      (A / G) * (κ / G) ^ (-3 / 2 : ℝ) := by
  have hlower : (κ / G) * t k ^ 2 ≤ normalizedRadii G ρ k := by
    rw [normalizedRadii_apply, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (hρ k) hG.le
  have hcoeff : ‖normalizedCoefficients G a k‖ ≤ (A / G) * t k ^ 3 := by
    rw [norm_normalizedCoefficients hG]
    calc
      G⁻¹ * ‖a k‖ ≤ G⁻¹ * (A * t k ^ 3) :=
        mul_le_mul_of_nonneg_left (ha k) (inv_nonneg.mpr hG.le)
      _ = _ := by ring
  exact (coefficientScaleBounds (ht k) (div_pos hκ hG) (norm_nonneg _)
    (div_nonneg hA hG.le) hlower hcoeff).2.2

/-- Helper for sec:center-approach and cm-limiting-scales: raw source orders
and a fixed small cap give C², a vanishing two-jet on the closed disk, a full-sum
Hessian bound of order tCap, and a global half-Hölder Hessian. -/
theorem interpolateCircle_of_scaleBounds (C : E) {G : ℝ} (hG : 0 < G)
    (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (t : ℕ → ℝ)
    (radialLower radialUpper κLow κHigh A tCap : ℝ)
    (hLower : 0 < radialLower) (hκLow : 0 < κLow) (hκHigh : 0 < κHigh)
    (hA : 0 ≤ A) (hCap : 0 < tCap)
    (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0)) (htBound : ∀ k, t k ≤ tCap)
    (hradial : ∀ k, radialLower * t k ≤ ‖c k - C‖ - G ∧
      ‖c k - C‖ - G ≤ radialUpper * t k)
    (hradii : ∀ k, κLow * t k ^ 2 ≤ ρ k ∧ ρ k ≤ κHigh * t k ^ 2)
    (hcoefficients : ∀ k, ‖a k‖ ≤ A * t k ^ 3)
    (hsmall : 4 * κHigh * tCap < radialLower)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))) :
    ContDiff ℝ 2 (InterpolationSum.perturbation c ρ a) ∧
      (∀ x, ‖x - C‖ ≤ G → InterpolationSum.perturbation c ρ a x = 0 ∧
        gradient (InterpolationSum.perturbation c ρ a) x = 0 ∧
        hessian (InterpolationSum.perturbation c ρ a) x = 0) ∧
      ∃ D H : ℝ, 0 ≤ D ∧ 0 < H ∧
        (∀ x, ‖hessian (InterpolationSum.perturbation c ρ a) x‖ ≤ D * tCap) ∧
        (∀ x y, ‖hessian (InterpolationSum.perturbation c ρ a) x -
          hessian (InterpolationSum.perturbation c ρ a) y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) := by
  have hgeometry := normalizedGeometry_of_scaleBounds C hG c ρ a t
    radialLower radialUpper κLow κHigh A tCap hLower hκLow hκHigh hA hCap
    ht ht0 htBound hradial hradii hcoefficients hsmall hballs
  have hB : 0 ≤ (A / κLow) * tCap := mul_nonneg (div_nonneg hA hκLow.le) hCap.le
  have hM : 0 ≤ (A / G) * (κLow / G) ^ (-3 / 2 : ℝ) :=
    mul_nonneg (div_nonneg hA hG.le) (Real.rpow_nonneg (div_nonneg hκLow.le hG.le) _)
  have hsize : ∀ k, ‖normalizedCoefficients G a k‖ / normalizedRadii G ρ k ≤
      (A / κLow) * tCap := by
    intro k
    rw [normalizedRatio_eq hG]
    exact (coefficientScaleBounds (ht k) hκLow (norm_nonneg _) hA
      (hradii k).1 (hcoefficients k)).1.trans
      (mul_le_mul_of_nonneg_left (htBound k) (div_nonneg hA hκLow.le))
  obtain ⟨D, H, hD, hH, hsizeSum, hholder⟩ := hessianBounds_of_normalizedGeometry C hG
    hgeometry hB hM hsize
    (normalizedScaledCoefficientBound hG ρ a t hκLow hA ht (fun k ↦ (hradii k).1) hcoefficients)
  refine ⟨perturbation_contDiff_of_normalizedGeometry C hG.ne' hgeometry,
    fun x hx ↦ perturbation_disk_jets C hG hgeometry hx,
    D * (A / κLow), H, mul_nonneg hD (div_nonneg hA hκLow.le), hH, ?_, hholder⟩
  intro x
  simpa only [mul_assoc] using hsizeSum x

omit [Nontrivial E] in
/-- Helper for sec:center-approach: a finite original prefix has a global
half-Hölder Hessian with a finite example-dependent constant, irrespective of
whether its balls have a margin from the limiting circle. -/
theorem finiteCorrectionSum_holder (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (hρ : ∀ k, 0 < ρ k) (N : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x y,
      ‖hessian (finiteCorrectionSum c ρ a N) x - hessian (finiteCorrectionSum c ρ a N) y‖ ≤
        H * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := InterpolationBounds.exists_norm_hessian_correction_sub_le (E := E)
  have hconstants : ∀ k, 0 ≤ K * ‖a k‖ * (ρ k) ^ (-3 / 2 : ℝ) := by
    intro k
    exact mul_nonneg (mul_nonneg hK (norm_nonneg _)) (Real.rpow_nonneg (hρ k).le _)
  refine ⟨∑ k ∈ Finset.range N, K * ‖a k‖ * (ρ k) ^ (-3 / 2 : ℝ),
    Finset.sum_nonneg (fun k _ ↦ hconstants k), ?_⟩
  have hfun : finiteCorrectionSum c ρ a N =
      fun x ↦ ∑ k ∈ Finset.range N, InterpolationSum.bump c ρ a k x :=
    funext (finiteCorrectionSum_apply c ρ a N)
  rw [hfun]
  apply hessian_finiteSum_holder
  · intro k _
    exact (InterpolationSum.contDiff_bump c ρ a k).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  · intro k _ x y
    rw [norm_hessianDifference_eq, bump_eq_correction]
    exact hbound _ _ _ x y (hρ k)


/-- Helper for sec:center-approach and cm-limiting-scales: eventual raw
source orders suffice for C² and a global half-Hölder Hessian of the FULL
original sum. A late tail is normalized; all original early bumps are restored. -/
theorem perturbation_regular_of_eventualBounds (C : E) {G : ℝ} (hG : 0 < G)
    (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (t : ℕ → ℝ)
    (radialLower radialUpper κLow κHigh A : ℝ)
    (hLower : 0 < radialLower) (hUpper : 0 < radialUpper)
    (hκLow : 0 < κLow) (hκHigh : 0 < κHigh) (hA : 0 < A)
    (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0)) (hρ : ∀ k, 0 < ρ k)
    (hOrders : ∀ᶠ k in atTop,
      radialLower * t k ≤ ‖c k - C‖ - G ∧
      ‖c k - C‖ - G ≤ radialUpper * t k ∧
      κLow * t k ^ 2 ≤ ρ k ∧ ρ k ≤ κHigh * t k ^ 2 ∧ ‖a k‖ ≤ A * t k ^ 3)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))) :
    ContDiff ℝ 2 (InterpolationSum.perturbation c ρ a) ∧
      ∃ H : ℝ, 0 < H ∧ ∀ x y,
        ‖hessian (InterpolationSum.perturbation c ρ a) x -
          hessian (InterpolationSum.perturbation c ρ a) y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  let tCap := min radialUpper (radialLower / (8 * κHigh))
  have hdenom : 0 < 8 * κHigh := by positivity
  have hCap : 0 < tCap := lt_min hUpper (div_pos hLower hdenom)
  have hsmall : 4 * κHigh * tCap < radialLower := by
    have hfactor : 0 ≤ 4 * κHigh := by positivity
    have hstrict : 4 * κHigh * (radialLower / (8 * κHigh)) < radialLower := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hdenom).mpr
      nlinarith [mul_pos hLower hκHigh]
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hfactor).trans_lt hstrict
  have heventual : ∀ᶠ k in atTop, t k ≤ tCap ∧
      radialLower * t k ≤ ‖c k - C‖ - G ∧
      ‖c k - C‖ - G ≤ radialUpper * t k ∧
      κLow * t k ^ 2 ≤ ρ k ∧ ρ k ≤ κHigh * t k ^ 2 ∧ ‖a k‖ ≤ A * t k ^ 3 := by
    filter_upwards [hOrders, ht0.eventually_lt_const hCap] with k hk hcap
    exact ⟨hcap.le, hk⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp heventual
  have htail (k : ℕ) := hN (k + N) (Nat.le_add_left N k)
  have htailLimit := ht0.comp (tendsto_add_atTop_nat N)
  obtain ⟨hTailC2, _, D, Htail, _, hHtail, _, hTailHolder⟩ :=
    interpolateCircle_of_scaleBounds C hG
      (fun k ↦ c (k + N)) (fun k ↦ ρ (k + N)) (fun k ↦ a (k + N))
      (fun k ↦ t (k + N)) radialLower radialUpper κLow κHigh A tCap
      hLower hκLow hκHigh hA.le hCap (fun k ↦ ht (k + N)) htailLimit
      (fun k ↦ (htail k).1)
      (fun k ↦ ⟨(htail k).2.1, (htail k).2.2.1⟩)
      (fun k ↦ ⟨(htail k).2.2.2.1, (htail k).2.2.2.2.1⟩)
      (fun k ↦ (htail k).2.2.2.2.2) hsmall (tailBalls_disjoint c ρ hballs N)
  have hPrefixC2 : ContDiff ℝ 2 (finiteCorrectionSum c ρ a N) :=
    (finiteCorrectionSum_contDiff c ρ a N).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨Hprefix, hHprefix, hPrefixHolder⟩ := finiteCorrectionSum_holder c ρ a hρ N
  rw [perturbation_split c ρ a hρ hballs N]
  refine ⟨hPrefixC2.add hTailC2, Hprefix + Htail, add_pos_of_nonneg_of_pos hHprefix hHtail, ?_⟩
  intro x y
  rw [hessian_add hPrefixC2 hTailC2, hessian_add hPrefixC2 hTailC2, add_sub_add_comm]
  calc
    _ ≤ ‖hessian (finiteCorrectionSum c ρ a N) x - hessian (finiteCorrectionSum c ρ a N) y‖ +
        ‖hessian (InterpolationSum.perturbation (fun k ↦ c (k + N))
          (fun k ↦ ρ (k + N)) (fun k ↦ a (k + N))) x -
          hessian (InterpolationSum.perturbation (fun k ↦ c (k + N))
            (fun k ↦ ρ (k + N)) (fun k ↦ a (k + N))) y‖ := norm_add_le _ _
    _ ≤ Hprefix * ‖x - y‖ ^ (1 / 2 : ℝ) + Htail * ‖x - y‖ ^ (1 / 2 : ℝ) :=
      add_le_add (hPrefixHolder x y) (hTailHolder x y)
    _ = _ := (add_mul _ _ _).symm

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Helper for sec:center-approach: the SAME source correction sum added
to the prescribed quadratic centered at the limiting circle center. -/
def shiftedObjective (C : E) (f : E → ℝ) : E → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + f x

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Helper for sec:center-approach: evaluation of the shifted quadratic
background plus the unchanged original correction sum. -/
theorem shiftedObjective_apply (C : E) (f : E → ℝ) (x : E) :
    shiftedObjective C f x = (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + f x := by
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Helper for sec:center-approach: the prescribed quadratic background
preserves the proved C² regularity of the correction. -/
theorem shiftedObjective_contDiff (C : E) {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (shiftedObjective C f) := by
  rw [funext (shiftedObjective_apply C f)]
  exact (contDiff_const.mul ((contDiff_norm_sq ℝ).comp
    (contDiff_id.sub contDiff_const))).add hf

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Helper for sec:center-approach: the exact gradient of the centered
quadratic plus correction is the displacement plus correction gradient. -/
theorem gradient_shiftedObjective (C : E) {f : E → ℝ} (hf : Differentiable ℝ f) (x : E) :
    gradient (shiftedObjective C f) x = x - C + gradient f x := by
  rw [funext (shiftedObjective_apply C f)]
  exact HessianPerturbation.gradient_halfNormSq_sub_add C f x (hf x)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Helper for sec:center-approach: the centered quadratic adds precisely
the identity operator to the correction Hessian. -/
theorem hessian_shiftedObjective (C : E) {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    hessian (shiftedObjective C f) x = 1 + hessian f x := by
  rw [funext (shiftedObjective_apply C f), hessian_def, hessian_def]
  exact HessianPerturbation.fderiv_gradient_halfNormSq_sub_add C f x hf

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Helper for sec:center-approach: the original quadratic background leaves
the global half-Hölder modulus of the Hessian unchanged. -/
theorem shiftedObjective_holder (C : E) {f : E → ℝ} (hf : ContDiff ℝ 2 f) {H : ℝ}
    (hholder : ∀ x y, ‖hessian f x - hessian f y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) (x y : E) :
    ‖hessian (shiftedObjective C f) x - hessian (shiftedObjective C f) y‖ ≤
      H * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  rw [hessian_shiftedObjective C hf, hessian_shiftedObjective C hf, add_sub_add_left_eq_sub]
  exact hholder x y

/-- sec:center-approach (cm-limiting-scales), main.tex 2002–2028: conditional
explicit-χ interpolation for a fixed shifted/scaled circle. Positive radii,
disjoint OPEN balls, t→0 and eventual linear radial, quadratic radius and cubic
coefficient bounds imply C² and global half-Hölder Hessians of the FULL original
sum and centered-quadratic objective, with exact jets at EVERY center. Early
original bumps are retained, without assuming early circle margins. -/
theorem interpolateCircle_of_eventualBounds (C : E) {G : ℝ} (hG : 0 < G)
    (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (t : ℕ → ℝ)
    (radialLower radialUpper κLow κHigh A : ℝ)
    (hLower : 0 < radialLower) (hUpper : 0 < radialUpper)
    (hκLow : 0 < κLow) (hκHigh : 0 < κHigh) (hA : 0 < A)
    (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0)) (hρ : ∀ k, 0 < ρ k)
    (hOrders : ∀ᶠ k in atTop,
      radialLower * t k ≤ ‖c k - C‖ - G ∧
      ‖c k - C‖ - G ≤ radialUpper * t k ∧
      κLow * t k ^ 2 ≤ ρ k ∧ ρ k ≤ κHigh * t k ^ 2 ∧ ‖a k‖ ≤ A * t k ^ 3)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))) :
    ContDiff ℝ 2 (InterpolationSum.perturbation c ρ a) ∧
      ContDiff ℝ 2 (shiftedObjective C (InterpolationSum.perturbation c ρ a)) ∧
      (∃ H : ℝ, 0 < H ∧
        (∀ x y, ‖hessian (InterpolationSum.perturbation c ρ a) x -
          hessian (InterpolationSum.perturbation c ρ a) y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) ∧
        (∀ x y, ‖hessian (shiftedObjective C (InterpolationSum.perturbation c ρ a)) x -
          hessian (shiftedObjective C (InterpolationSum.perturbation c ρ a)) y‖ ≤
            H * ‖x - y‖ ^ (1 / 2 : ℝ))) ∧
      (∀ k, InterpolationSum.perturbation c ρ a (c k) = 0 ∧
        gradient (InterpolationSum.perturbation c ρ a) (c k) = a k ∧
        hessian (InterpolationSum.perturbation c ρ a) (c k) = 0) ∧
      (∀ k, shiftedObjective C (InterpolationSum.perturbation c ρ a) (c k) =
          (1 / 2 : ℝ) * ‖c k - C‖ ^ 2 ∧
        gradient (shiftedObjective C (InterpolationSum.perturbation c ρ a)) (c k) =
          c k - C + a k ∧
        hessian (shiftedObjective C (InterpolationSum.perturbation c ρ a)) (c k) = 1) := by
  obtain ⟨hsmooth, H, hH, hholder⟩ := perturbation_regular_of_eventualBounds C hG c ρ a t
    radialLower radialUpper κLow κHigh A hLower hUpper hκLow hκHigh hA ht ht0 hρ hOrders hballs
  have hjets := perturbation_center_jets c ρ a hρ hballs
  refine ⟨hsmooth, shiftedObjective_contDiff C hsmooth,
    ⟨H, hH, hholder, shiftedObjective_holder C hsmooth hholder⟩, hjets, ?_⟩
  intro k
  refine ⟨?_, ?_, ?_⟩
  · rw [shiftedObjective_apply, (hjets k).1, add_zero]
  · rw [gradient_shiftedObjective C (hsmooth.differentiable two_ne_zero), (hjets k).2.1]
  · rw [hessian_shiftedObjective C hsmooth, (hjets k).2.2, add_zero]

omit [Nontrivial E] in
/-- Helper for cm-limiting-scales: one constant chosen before all bump data
controls the original χ Hessian size, Lipschitz modulus and half-Hölder modulus
by the exact source coefficient/radius expressions. -/
theorem exists_bump_hessian_bounds :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (k : ℕ), 0 < ρ k →
      (∀ x, ‖hessian (InterpolationSum.bump c ρ a k) x‖ ≤ K * (‖a k‖ / ρ k)) ∧
      (∀ x y, ‖hessian (InterpolationSum.bump c ρ a k) x -
        hessian (InterpolationSum.bump c ρ a k) y‖ ≤
          K * (‖a k‖ / ρ k ^ 2) * ‖x - y‖) ∧
      (∀ x y, ‖hessian (InterpolationSum.bump c ρ a k) x -
        hessian (InterpolationSum.bump c ρ a k) y‖ ≤
          K * (‖a k‖ * (ρ k) ^ (-3 / 2 : ℝ)) * ‖x - y‖ ^ (1 / 2 : ℝ)) := by
  obtain ⟨Ksize, hKsize, hsize⟩ := ExplicitCutoff.exists_norm_secondFDeriv_correction_le (E := E)
  obtain ⟨Klip, hKlip, hlip⟩ := InterpolationBounds.exists_norm_hessian_correction_sub_le_lipschitz
    (E := E)
  obtain ⟨Kholder, hKholder, hholder⟩ := InterpolationBounds.exists_norm_hessian_correction_sub_le
    (E := E)
  let K := max Ksize (max Klip Kholder)
  have hK : 0 ≤ K := hKsize.trans (le_max_left _ _)
  have hKsize' : Ksize ≤ K := le_max_left _ _
  have hKlip' : Klip ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKholder' : Kholder ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, hK, ?_⟩
  intro c ρ a k hρ
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [norm_hessian_eq, bump_eq_correction]
    calc
      _ ≤ Ksize * ‖a k‖ / ρ k := hsize _ _ _ x hρ
      _ = Ksize * (‖a k‖ / ρ k) := mul_div_assoc _ _ _
      _ ≤ K * (‖a k‖ / ρ k) :=
        mul_le_mul_of_nonneg_right hKsize' (div_nonneg (norm_nonneg _) hρ.le)
  · intro x y
    rw [norm_hessianDifference_eq, bump_eq_correction]
    calc
      _ ≤ (Klip * ‖a k‖ / ρ k ^ 2) * ‖x - y‖ := hlip _ _ _ x y hρ
      _ = (Klip * (‖a k‖ / ρ k ^ 2)) * ‖x - y‖ := by rw [mul_div_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKlip' (div_nonneg (norm_nonneg _) (sq_nonneg _)))
        (norm_nonneg _)
  · intro x y
    rw [norm_hessianDifference_eq, bump_eq_correction]
    calc
      _ ≤ Kholder * ‖a k‖ * (ρ k) ^ (-3 / 2 : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ) :=
        hholder _ _ _ x y hρ
      _ = Kholder * (‖a k‖ * (ρ k) ^ (-3 / 2 : ℝ)) * ‖x - y‖ ^ (1 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKholder'
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hρ.le _)))
        (Real.rpow_nonneg (norm_nonneg _) _)

omit [Nontrivial E] in
/-- Helper for cm-limiting-scales: cubic coefficients and quadratic radii
derive the source O(t), O(t⁻¹) and uniform half-Hölder estimates of EACH original
bump, with constants independent of its index. -/
theorem bump_hessian_orders (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (t : ℕ → ℝ)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) (ht : ∀ k, 0 < t k)
    (hρ : ∀ k, κ * t k ^ 2 ≤ ρ k) (ha : ∀ k, ‖a k‖ ≤ A * t k ^ 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k,
      (∀ x, ‖hessian (InterpolationSum.bump c ρ a k) x‖ ≤ K * (A / κ) * t k) ∧
      (∀ x y, ‖hessian (InterpolationSum.bump c ρ a k) x -
        hessian (InterpolationSum.bump c ρ a k) y‖ ≤
          K * (A / κ ^ 2) * (t k)⁻¹ * ‖x - y‖) ∧
      (∀ x y, ‖hessian (InterpolationSum.bump c ρ a k) x -
        hessian (InterpolationSum.bump c ρ a k) y‖ ≤
          K * (A * κ ^ (-3 / 2 : ℝ)) * ‖x - y‖ ^ (1 / 2 : ℝ)) := by
  obtain ⟨K, hK, hbound⟩ := exists_bump_hessian_bounds (E := E)
  refine ⟨K, hK, ?_⟩
  intro k
  have hpositive : 0 < ρ k := (mul_pos hκ (sq_pos_of_pos (ht k))).trans_le (hρ k)
  have hscale := coefficientScaleBounds (ht k) hκ (norm_nonneg _) hA (hρ k) (ha k)
  have hb := hbound c ρ a k hpositive
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hscaled : K * (‖a k‖ / ρ k) ≤ K * (A / κ) * t k := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale.1 hK
    exact (hb.1 x).trans hscaled
  · intro x y
    calc
      _ ≤ K * (‖a k‖ / ρ k ^ 2) * ‖x - y‖ := hb.2.1 x y
      _ ≤ (K * ((A / κ ^ 2) * (t k)⁻¹)) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale.2.1 hK) (norm_nonneg _)
      _ = _ := by ring
  · intro x y
    exact (hb.2.2 x y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale.2.2 hK) (Real.rpow_nonneg (norm_nonneg _) _))


omit [Nontrivial E] in
/-- Helper for cm-limiting-scales: eventual cubic and quadratic source bounds
imply eventual O(t) Hessian size, O(t⁻¹) Hessian Lipschitz constants and a
uniform half-Hölder modulus, without any bounds on the finitely many early data. -/
theorem bump_hessian_orders_of_eventualBounds
    (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (t : ℕ → ℝ)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) (ht : ∀ k, 0 < t k)
    (hOrders : ∀ᶠ k in atTop, κ * t k ^ 2 ≤ ρ k ∧ ‖a k‖ ≤ A * t k ^ 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ k in atTop,
      (∀ x, ‖hessian (InterpolationSum.bump c ρ a k) x‖ ≤ K * (A / κ) * t k) ∧
      (∀ x y, ‖hessian (InterpolationSum.bump c ρ a k) x -
        hessian (InterpolationSum.bump c ρ a k) y‖ ≤
          K * (A / κ ^ 2) * (t k)⁻¹ * ‖x - y‖) ∧
      (∀ x y, ‖hessian (InterpolationSum.bump c ρ a k) x -
        hessian (InterpolationSum.bump c ρ a k) y‖ ≤
          K * (A * κ ^ (-3 / 2 : ℝ)) * ‖x - y‖ ^ (1 / 2 : ℝ)) ∧
      ‖a k‖ * (ρ k) ^ (-3 / 2 : ℝ) ≤ A * κ ^ (-3 / 2 : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := exists_bump_hessian_bounds (E := E)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hOrders] with k hk
  have hpositive : 0 < ρ k := (mul_pos hκ (sq_pos_of_pos (ht k))).trans_le hk.1
  have hscale := coefficientScaleBounds (ht k) hκ (norm_nonneg _) hA hk.1 hk.2
  have hb := hbound c ρ a k hpositive
  refine ⟨?_, ?_, ?_, hscale.2.2⟩
  · intro x
    have hscaled : K * (‖a k‖ / ρ k) ≤ K * (A / κ) * t k := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale.1 hK
    exact (hb.1 x).trans hscaled
  · intro x y
    calc
      _ ≤ K * (‖a k‖ / ρ k ^ 2) * ‖x - y‖ := hb.2.1 x y
      _ ≤ (K * ((A / κ ^ 2) * (t k)⁻¹)) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale.2.1 hK) (norm_nonneg _)
      _ = _ := by ring
  · intro x y
    exact (hb.2.2 x y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale.2.2 hK) (Real.rpow_nonneg (norm_nonneg _) _))

end Calculus

end Cutoff

end DFP.Polar.AffineInterpolation
