/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import AlgebraicTopology_May_1999.Chap01.Proposition_1_6_2
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Complex Metric
open scoped ContinuousMap

local notation "D²" => closedBall (0 : ℂ) 1

private def rayIntersectionParameter (y x : D²) : ℝ :=
  let d : ℂ := (x : ℂ) - y
  let a : ℝ := ‖d‖ ^ 2
  let b : ℝ := Complex.re (star (y : ℂ) * d)
  (-b + Real.sqrt (b ^ 2 + a * (1 - ‖(y : ℂ)‖ ^ 2))) / a

/-- Helper for Construction 1.6.3: the squared norm of the affine line through `y` and `x` is a
quadratic polynomial in the line parameter. -/
private lemma lineMap_norm_sq_eq_quadratic (y x : D²) (t : ℝ) :
    ‖AffineMap.lineMap (y : ℂ) x t‖ ^ 2 =
      ‖(y : ℂ)‖ ^ 2 + 2 * t * Complex.re (star (y : ℂ) * (((x : ℂ) - y))) +
        t ^ 2 * ‖((x : ℂ) - y)‖ ^ 2 := by
  -- Rewrite the affine line map as the usual complex affine combination.
  rw [show AffineMap.lineMap (y : ℂ) x t = (y : ℂ) + (t : ℂ) * (((x : ℂ) - y)) by
    rw [AffineMap.lineMap_apply_module']
    change ((t : ℂ) * (((x : ℂ) - y))) + (y : ℂ) = (y : ℂ) + (t : ℂ) * (((x : ℂ) - y))
    ring]
  -- Expand the complex norm square and collect the resulting real coefficients.
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_mul,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
  ring

/-- Helper for Construction 1.6.3: substituting the quadratic-formula parameter into the ray norm
identity produces the equation of the unit circle. -/
private lemma quadratic_formula_solves_unit_norm
    (s a b Δ : ℝ) (ha : a ≠ 0) (hΔ : 0 ≤ Δ) (hΔ_def : Δ = b ^ 2 + a * (1 - s)) :
    s + 2 * (((-b + Real.sqrt Δ) / a)) * b + (((-b + Real.sqrt Δ) / a) ^ 2) * a = 1 := by
  -- Expand the quadratic-formula expression and use `sqrt^2 = Δ`.
  subst hΔ_def
  field_simp [ha]
  calc
    s * a + 2 * b * (-b + Real.sqrt (b ^ 2 + a * (1 - s))) +
        (-b + Real.sqrt (b ^ 2 + a * (1 - s))) ^ 2
      = s * a + 2 * b * (-b + Real.sqrt (b ^ 2 + a * (1 - s))) +
          (b ^ 2 - 2 * b * Real.sqrt (b ^ 2 + a * (1 - s)) +
            (Real.sqrt (b ^ 2 + a * (1 - s))) ^ 2) := by
            ring
    _ = s * a + 2 * b * (-b + Real.sqrt (b ^ 2 + a * (1 - s))) +
          (b ^ 2 - 2 * b * Real.sqrt (b ^ 2 + a * (1 - s)) + (b ^ 2 + a * (1 - s))) := by
            rw [Real.sq_sqrt hΔ]
    _ = a := by
            ring

/-- Helper for Construction 1.6.3: when the endpoint `x` already lies on the boundary, the
quadratic-formula parameter equals `1`. -/
private lemma quadratic_formula_eq_one_of_boundary
    (s a b : ℝ) (ha : a ≠ 0) (ha_nonneg : 0 ≤ a) (hs : 0 ≤ 1 - s)
    (hboundary : s + 2 * b + a = 1) :
    (-b + Real.sqrt (b ^ 2 + a * (1 - s))) / a = 1 := by
  -- On the boundary, the discriminant becomes a square and the positive root is the endpoint.
  have hsum : 0 ≤ a + b := by
    nlinarith [ha_nonneg, hs, hboundary]
  have hdisc : b ^ 2 + a * (1 - s) = (a + b) ^ 2 := by
    nlinarith [hboundary]
  rw [hdisc, Real.sqrt_sq_eq_abs, abs_of_nonneg hsum]
  field_simp [ha]
  ring

/- The explicit quadratic formula computes the boundary point of the ray from `y` through `x`
whenever `y` and `x` are distinct points of the closed unit disk. -/
-- Proof sketch: expand the norm square of `y + t • (x - y)`, where
-- `t = rayIntersectionParameter y x`, and verify from the quadratic formula that this value is
-- `1`. The closed-ball assumptions ensure the discriminant is nonnegative, while `y ≠ x` keeps
-- the denominator nonzero.
private theorem rayIntersectionPoint_norm_eq_one (y x : D²) (hxy : y ≠ x) :
    ‖AffineMap.lineMap (y : ℂ) x (rayIntersectionParameter y x)‖ = 1 := by
  let d : ℂ := (x : ℂ) - y
  let a : ℝ := ‖d‖ ^ 2
  let b : ℝ := Complex.re (star (y : ℂ) * d)
  let Δ : ℝ := b ^ 2 + a * (1 - ‖(y : ℂ)‖ ^ 2)
  have hd_ne : d ≠ 0 := by
    -- Fixed-point freeness of the ray direction keeps the quadratic denominator nonzero.
    intro hd
    apply hxy
    apply Subtype.ext
    have hd' : ((x : ℂ) - y) = 0 := by
      simpa [d] using hd
    exact (sub_eq_zero.mp hd').symm
  have ha_pos : 0 < a := by
    simp [a, d, hd_ne, pow_two]
  let s : ℝ := ‖(y : ℂ)‖ ^ 2
  have hx_sq_le : ‖(x : ℂ)‖ ^ 2 ≤ 1 := by
    have hx_le : ‖(x : ℂ)‖ ≤ 1 := by
      simpa [closedBall, Metric.mem_closedBall, dist_eq_norm] using x.2
    nlinarith [norm_nonneg (x : ℂ)]
  have hx_quad : ‖(x : ℂ)‖ ^ 2 = ‖(y : ℂ)‖ ^ 2 + 2 * b + a := by
    -- Evaluate the quadratic identity at `t = 1`, where the line map lands at `x`.
    simpa [a, b, d] using lineMap_norm_sq_eq_quadratic y x 1
  have haux : a + 2 * b + ‖(y : ℂ)‖ ^ 2 ≤ 1 := by
    nlinarith [hx_sq_le, hx_quad]
  have hΔ_nonneg : 0 ≤ Δ := by
    -- The closed-disk hypothesis ensures the discriminant is nonnegative.
    have hsquare : (a + b) ^ 2 ≤ Δ := by
      nlinarith [haux]
    nlinarith [hsquare]
  have hsq : ‖AffineMap.lineMap (y : ℂ) x (rayIntersectionParameter y x)‖ ^ 2 = 1 := by
    -- Substitute the explicit ray parameter into the quadratic norm formula.
    rw [lineMap_norm_sq_eq_quadratic]
    simpa [rayIntersectionParameter, a, b, d, Δ, s] using
      quadratic_formula_solves_unit_norm s a b Δ ha_pos.ne' hΔ_nonneg rfl
  have hnorm_nonneg :
      0 ≤ ‖AffineMap.lineMap (y : ℂ) x (rayIntersectionParameter y x)‖ := by
    exact norm_nonneg _
  nlinarith

/-- The ray-intersection construction as a point of `Circle`. -/
def rayToCircle (y x : D²) (hxy : y ≠ x) : Circle where
  val := AffineMap.lineMap (y : ℂ) x (rayIntersectionParameter y x)
  property := mem_sphere_zero_iff_norm.2 (rayIntersectionPoint_norm_eq_one y x hxy)

variable (f : C(D², D²)) (hf : ∀ x : D², f x ≠ x)

/-- Composing the ray-to-circle construction with a fixed-point-free self-map of the disk gives a
continuous map to the boundary circle. -/
-- Proof sketch: `rayToCircle` is built from the canonical affine owner `AffineMap.lineMap`
-- together with the explicit quadratic parameter along the ray from `f x` through `x`. That
-- formula is continuous away from the diagonal, and `hf` removes the diagonal.
theorem continuous_rayToCircle_along_fixed_point_free_map :
    Continuous fun x : D² ↦ rayToCircle (f x) x (hf x) := by
  let d : D² → ℂ := fun x ↦ (x : ℂ) - f x
  let a : D² → ℝ := fun x ↦ ‖d x‖ ^ 2
  let b : D² → ℝ := fun x ↦ Complex.re (star (f x : ℂ) * d x)
  have hfcoe : Continuous fun x : D² ↦ ((f x : D²) : ℂ) := by
    exact continuous_subtype_val.comp f.continuous
  have hd : Continuous d := by
    fun_prop
  have ha : Continuous a := by
    fun_prop
  have hb : Continuous b := by
    -- The only nontrivial ingredient is taking the real part after multiplication.
    exact Complex.continuous_re.comp ((continuous_conj.comp hfcoe).mul hd)
  have hy : Continuous fun x : D² ↦ 1 - ‖(f x : ℂ)‖ ^ 2 := by
    exact continuous_const.sub ((continuous_norm.comp hfcoe).pow 2)
  have hdenom : ∀ x, a x ≠ 0 := by
    intro x
    -- Fixed-point freeness removes the diagonal, so division by `a x` is continuous.
    have hsub : d x ≠ 0 := by
      intro hzero
      apply hf x
      apply Subtype.ext
      exact (sub_eq_zero.mp hzero).symm
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hsub)
  have hparam : Continuous fun x : D² ↦ (rayIntersectionParameter (f x) x : ℝ) := by
    -- The quadratic-formula parameter is built from continuous operations away from the diagonal.
    change Continuous fun x : D² ↦
      (-b x + Real.sqrt (b x ^ 2 + a x * (1 - ‖(f x : ℂ)‖ ^ 2))) / a x
    exact ((continuous_neg.comp hb).add ((hb.pow 2).add (ha.mul hy)).sqrt).div ha hdenom
  have hraw : Continuous fun x : D² ↦
      ((rayIntersectionParameter (f x) x : ℝ) : ℂ) * (((x : D²) : ℂ) - f x) + (f x : ℂ) := by
    -- Rewrite the affine line map as a complex affine combination to make continuity explicit.
    have hd' : Continuous fun x : D² ↦ (((x : D²) : ℂ) - f x : ℂ) := by
      fun_prop
    exact (continuous_ofReal.comp hparam).mul hd' |>.add hfcoe
  simpa [rayToCircle, AffineMap.lineMap_apply_module'] using
    hraw.subtype_mk
      (fun x ↦ mem_sphere_zero_iff_norm.2 (rayIntersectionPoint_norm_eq_one (f x) x (hf x)))

/-- Helper for Construction 1.6.3: if the endpoint of the ray already lies on `S¹`, then the
explicit ray parameter is exactly `1`. -/
private theorem rayIntersectionParameter_eq_one_of_boundary (y x : D²) (hxy : y ≠ x)
    (hx : ‖(x : ℂ)‖ = 1) :
    rayIntersectionParameter y x = 1 := by
  let d : ℂ := (x : ℂ) - y
  let a : ℝ := ‖d‖ ^ 2
  let b : ℝ := Complex.re (star (y : ℂ) * d)
  have hd_ne : d ≠ 0 := by
    -- Distinct points determine a genuine ray direction.
    intro hd
    apply hxy
    apply Subtype.ext
    have hd' : ((x : ℂ) - y) = 0 := by
      simpa [d] using hd
    exact (sub_eq_zero.mp hd').symm
  have ha_pos : 0 < a := by
    simp [a, d, hd_ne, pow_two]
  let s : ℝ := ‖(y : ℂ)‖ ^ 2
  have hy_sq_le : ‖(y : ℂ)‖ ^ 2 ≤ 1 := by
    have hy_le : ‖(y : ℂ)‖ ≤ 1 := by
      simpa [closedBall, Metric.mem_closedBall, dist_eq_norm] using y.2
    nlinarith [norm_nonneg (y : ℂ)]
  have hx_sq : ‖(x : ℂ)‖ ^ 2 = 1 := by
    nlinarith [hx]
  have hx_quad : ‖(x : ℂ)‖ ^ 2 = ‖(y : ℂ)‖ ^ 2 + 2 * b + a := by
    -- The same quadratic identity at `t = 1` records that the line map hits `x`.
    simpa [a, b, d] using lineMap_norm_sq_eq_quadratic y x 1
  have hy_gap_nonneg : 0 ≤ 1 - ‖(y : ℂ)‖ ^ 2 := by
    nlinarith [hy_sq_le]
  have hboundary : ‖(y : ℂ)‖ ^ 2 + 2 * b + a = 1 := by
    nlinarith [hx_sq, hx_quad]
  -- The boundary relation turns the quadratic-formula root into the endpoint parameter `1`.
  simpa [rayIntersectionParameter, a, b, d, s] using
    quadratic_formula_eq_one_of_boundary s a b ha_pos.ne' ha_pos.le
      hy_gap_nonneg hboundary

/-- Construction 1.6.3: a fixed-point-free self-map of the closed unit disk `D²` determines a
continuous map to the boundary circle `S¹` by sending `x` to the intersection of `S¹` with the
ray starting at `f x` and passing through `x`. -/
def fixedPointFreeDiskRetraction : C(D², Circle) where
  toFun x := rayToCircle (f x) x (hf x)
  continuous_toFun := continuous_rayToCircle_along_fixed_point_free_map f hf

/-- The ray-intersection map associated to a fixed-point-free disk self-map is a retraction of the
boundary inclusion. -/
-- Proof sketch: for `z ∈ S¹`, the point `circleToClosedUnitDisk z` already lies on the unit
-- circle. The ray from `f z` through `z` therefore meets the boundary again exactly at `z`, so the
-- constructed map restricts to the identity on `S¹`. Apply extensionality for continuous maps.
theorem fixedPointFreeDiskRetraction_comp_circleToClosedUnitDisk :
    (fixedPointFreeDiskRetraction f hf).comp circleToClosedUnitDisk = ContinuousMap.id Circle :=
  by
    ext z
    -- On the boundary, the ray parameter collapses to `1`, so the affine line map returns `z`.
    change
      AffineMap.lineMap ((f (circleToClosedUnitDisk z) : D²) : ℂ) (circleToClosedUnitDisk z)
        (rayIntersectionParameter (f (circleToClosedUnitDisk z)) (circleToClosedUnitDisk z)) = z
    have hz_norm : ‖((circleToClosedUnitDisk z : D²) : ℂ)‖ = 1 := by
      simpa [circleToClosedUnitDisk_apply] using Circle.norm_coe z
    rw [rayIntersectionParameter_eq_one_of_boundary (f (circleToClosedUnitDisk z))
      (circleToClosedUnitDisk z) (hf (circleToClosedUnitDisk z)) hz_norm]
    simpa [circleToClosedUnitDisk_apply] using
      (AffineMap.lineMap_apply_one ((f (circleToClosedUnitDisk z) : D²) : ℂ)
        (circleToClosedUnitDisk z))
