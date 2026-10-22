/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Proposition_1_6_2
import AlgebraicTopology_May_1999.Chap01.Lemma_1_7_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped ContinuousMap CircleDegree unitInterval

local notation "D²" => closedBall (0 : ℂ) 1

/-- The normalization `z / ‖z‖` of a nonzero complex number has norm `1`. -/
-- Proof sketch: use `‖z / ‖z‖‖ = ‖z‖ / ‖‖z‖‖`, then simplify
-- using `hz` to see that the quotient equals `1`.
theorem complexDivNormCircle_norm_eq_one (z : ℂ) (hz : z ≠ 0) :
    ‖z / ‖z‖‖ = 1 := by
  -- Reduce the normalized norm to the scalar quotient `‖z‖ / ‖z‖`.
  rw [norm_div]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  -- The nonvanishing hypothesis exactly rules out the zero denominator.
  exact div_self (norm_ne_zero_iff.2 hz)

/-- The normalized value `z / ‖z‖` of a nonzero complex number, viewed as a point of `Circle`. -/
def complexDivNormCircle (z : ℂ) (hz : z ≠ 0) : Circle where
  val := z / ‖z‖
  property := mem_sphere_zero_iff_norm.2 (complexDivNormCircle_norm_eq_one z hz)

/-- A polynomial that is nonvanishing on the closed unit disk is nonzero at the origin. -/
-- Proof sketch: apply the hypothesis `hf` at `z = 0`, using that the origin belongs to the closed
-- unit disk.
theorem polynomial_eval_zero_ne_zero_of_nonvanishing_closed_unit_disk (f : Polynomial ℂ)
    (hf : ∀ z : ℂ, z ∈ D² → Polynomial.eval z f ≠ 0) :
    Polynomial.eval (0 : ℂ) f ≠ 0 := by
  -- The origin is a point of the closed unit disk.
  exact hf 0 (by
    change dist (0 : ℂ) 0 ≤ 1
    simp)

/-- A polynomial that is nonvanishing on the closed unit disk is nonzero on the unit circle. -/
theorem polynomial_eval_ne_zero_on_circle_of_nonvanishing_closed_unit_disk
    (f : Polynomial ℂ) (hf : ∀ z : ℂ, z ∈ D² → Polynomial.eval z f ≠ 0) (z : Circle) :
    Polynomial.eval (z : ℂ) f ≠ 0 :=
  hf z (circle_mem_closed_unit_disk z)

/-- The normalized boundary map of a polynomial nonvanishing on the unit circle is continuous. -/
-- Proof sketch: `z ↦ Polynomial.eval z f` is continuous on `Circle`; the boundary nonvanishing
-- hypothesis allows division by `‖f(z)‖`, and the result lands in `Circle` by
-- `complexDivNormCircle_norm_eq_one`.
theorem polynomialNormalizedBoundaryMap_continuous (f : Polynomial ℂ)
    (hf : ∀ z : Circle, Polynomial.eval (z : ℂ) f ≠ 0) :
    Continuous fun z : Circle ↦
      complexDivNormCircle (Polynomial.eval (z : ℂ) f) (hf z) :=
  by
  let g : Circle → ℂ := fun z ↦ Polynomial.eval (z : ℂ) f
  -- First record continuity of the polynomial on the circle.
  have hg : Continuous g := (Polynomial.continuous f).comp continuous_subtype_val
  have hnorm : Continuous fun z : Circle ↦ ((‖g z‖ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hg.norm
  -- Then divide by the nonvanishing norm to obtain the normalized complex-valued map.
  have hdiv : Continuous fun z : Circle ↦ g z / ‖g z‖ :=
    hg.div hnorm (fun z ↦ by
      exact_mod_cast norm_ne_zero_iff.2 (hf z))
  -- Finally package the normalized values into the subtype `Circle`.
  simpa [complexDivNormCircle, g] using
    (Continuous.subtype_mk hdiv
      (fun z ↦ mem_sphere_zero_iff_norm.2 (complexDivNormCircle_norm_eq_one (g z) (hf z))))

/-- The normalized boundary map `z ↦ f(z) / |f(z)|` of a polynomial that has no zeros on `S¹`. -/
def polynomialNormalizedBoundaryMap (f : Polynomial ℂ)
    (hf : ∀ z : Circle, Polynomial.eval (z : ℂ) f ≠ 0) : C(Circle, Circle) where
  toFun z := complexDivNormCircle (Polynomial.eval (z : ℂ) f) (hf z)
  continuous_toFun := polynomialNormalizedBoundaryMap_continuous f hf

/-- Evaluating the normalized boundary map gives the normalized polynomial value. -/
@[simp] theorem polynomialNormalizedBoundaryMap_apply (f : Polynomial ℂ)
    (hf : ∀ z : Circle, Polynomial.eval (z : ℂ) f ≠ 0) (z : Circle) :
    polynomialNormalizedBoundaryMap f hf z =
      complexDivNormCircle (Polynomial.eval (z : ℂ) f) (hf z) :=
  rfl

/-- Helper for ProofStep 1.7.6: radially scaling a point of `S¹` by a parameter in `I` keeps it
inside the closed unit disk. -/
theorem unitInterval_mul_circle_mem_closed_unit_disk (t : I) (x : Circle) :
    (((t : ℝ) : ℂ) * (x : ℂ)) ∈ D² := by
  -- Rewrite disk membership as the norm bound coming from `‖x‖ = 1`.
  change dist ((((t : ℝ) : ℂ) * (x : ℂ))) 0 ≤ 1
  rw [dist_eq_norm]
  simp only [sub_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg t.2.1,
    Circle.norm_coe, mul_one]
  exact t.2.2

/-- Helper for ProofStep 1.7.6: `complexDivNormCircle` depends only on the underlying complex
number, not on the chosen nonvanishing proof. -/
theorem complexDivNormCircle_congr {z w : ℂ} (hzw : z = w) (hz : z ≠ 0) (hw : w ≠ 0) :
    complexDivNormCircle z hz = complexDivNormCircle w hw := by
  -- After identifying the complex numbers, the circle points agree by extensionality.
  subst hzw
  ext
  rfl

/-- The normalized boundary map of a polynomial with no zeros in `D²` is homotopic to the constant
map at its normalized value at `0`. -/
-- Proof sketch: use the explicit homotopy `h(x,t) = f(t x) / |f(t x)|`. For `x ∈ S¹` and
-- `t ∈ [0,1]`, the point `t • x` lies in the closed unit disk, so `hf` guarantees the denominator
-- never vanishes. At `t = 1` this is the boundary map, and at `t = 0` it is the constant value
-- `f(0) / |f(0)|`.
theorem polynomialNormalizedBoundaryMap_homotopic_const_of_no_root_closed_unit_disk
    (f : Polynomial ℂ) (hf : ∀ z : ℂ, z ∈ D² → Polynomial.eval z f ≠ 0) :
    (polynomialNormalizedBoundaryMap f
      (polynomial_eval_ne_zero_on_circle_of_nonvanishing_closed_unit_disk f hf)).Homotopic
      (ContinuousMap.const Circle
        (complexDivNormCircle (Polynomial.eval (0 : ℂ) f)
          (polynomial_eval_zero_ne_zero_of_nonvanishing_closed_unit_disk f hf))) := by
  let basepoint :=
    complexDivNormCircle (Polynomial.eval (0 : ℂ) f)
      (polynomial_eval_zero_ne_zero_of_nonvanishing_closed_unit_disk f hf)
  have H : (ContinuousMap.const Circle basepoint).Homotopy
      (polynomialNormalizedBoundaryMap f
        (polynomial_eval_ne_zero_on_circle_of_nonvanishing_closed_unit_disk f hf)) :=
    { toFun := fun p ↦
        complexDivNormCircle
          (Polynomial.eval ((((p.1 : ℝ) : ℂ) * (p.2 : ℂ))) f)
          (hf ((((p.1 : ℝ) : ℂ) * (p.2 : ℂ)))
            (unitInterval_mul_circle_mem_closed_unit_disk p.1 p.2))
      continuous_toFun := by
        let g : I × Circle → ℂ := fun p ↦ Polynomial.eval ((((p.1 : ℝ) : ℂ) * (p.2 : ℂ))) f
        -- The source proof uses the radial contraction `(t, x) ↦ t x`.
        have hradial : Continuous fun p : I × Circle ↦ (((p.1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
          have ht : Continuous fun p : I × Circle ↦ (((p.1 : ℝ) : ℂ)) :=
            Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
          have hx : Continuous fun p : I × Circle ↦ (p.2 : ℂ) :=
            continuous_subtype_val.comp continuous_snd
          exact ht.mul hx
        have hg : Continuous g := (Polynomial.continuous f).comp hradial
        have hnorm : Continuous fun p : I × Circle ↦ ((‖g p‖ : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp hg.norm
        -- The disk nonvanishing hypothesis keeps the normalization denominator away from zero.
        have hdiv : Continuous fun p : I × Circle ↦ g p / ‖g p‖ :=
          hg.div hnorm (fun p : I × Circle ↦ by
            exact_mod_cast norm_ne_zero_iff.2
              (hf ((((p.1 : ℝ) : ℂ) * (p.2 : ℂ)))
                (unitInterval_mul_circle_mem_closed_unit_disk p.1 p.2)))
        simpa [complexDivNormCircle, g] using
          (Continuous.subtype_mk hdiv
            (fun p : I × Circle ↦ mem_sphere_zero_iff_norm.2
              (complexDivNormCircle_norm_eq_one
                (g p)
                (hf ((((p.1 : ℝ) : ℂ) * (p.2 : ℂ)))
                  (unitInterval_mul_circle_mem_closed_unit_disk p.1 p.2)))))
      map_zero_left := by
        intro x
        -- At `t = 0`, the radial contraction collapses everything to the origin.
        change
          complexDivNormCircle
              (Polynomial.eval ((((0 : I) : ℝ) : ℂ) * (x : ℂ)) f)
              (hf ((((0 : I) : ℝ) : ℂ) * (x : ℂ))
                (unitInterval_mul_circle_mem_closed_unit_disk 0 x)) =
            complexDivNormCircle (Polynomial.eval (0 : ℂ) f)
              (polynomial_eval_zero_ne_zero_of_nonvanishing_closed_unit_disk f hf)
        exact complexDivNormCircle_congr (by simp)
          (hf ((((0 : I) : ℝ) : ℂ) * (x : ℂ))
            (unitInterval_mul_circle_mem_closed_unit_disk 0 x))
          (polynomial_eval_zero_ne_zero_of_nonvanishing_closed_unit_disk f hf)
      map_one_left := by
        intro x
        -- At `t = 1`, the homotopy recovers the original boundary map.
        change
          complexDivNormCircle
              (Polynomial.eval ((((1 : I) : ℝ) : ℂ) * (x : ℂ)) f)
              (hf ((((1 : I) : ℝ) : ℂ) * (x : ℂ))
                (unitInterval_mul_circle_mem_closed_unit_disk 1 x)) =
            complexDivNormCircle (Polynomial.eval (x : ℂ) f)
              (polynomial_eval_ne_zero_on_circle_of_nonvanishing_closed_unit_disk f hf x)
        exact complexDivNormCircle_congr (by simp)
          (hf ((((1 : I) : ℝ) : ℂ) * (x : ℂ))
            (unitInterval_mul_circle_mem_closed_unit_disk 1 x))
          (polynomial_eval_ne_zero_on_circle_of_nonvanishing_closed_unit_disk f hf x) }
  -- The explicit contraction runs from the constant map to the boundary map, so we reverse it.
  exact ⟨H.symm⟩

/-- ProofStep 1.7.6: if a complex polynomial has no roots in the closed unit disk, then the
normalized boundary map `z ↦ f(z) / |f(z)|` on `S¹` has degree `0`. -/
-- Proof sketch: the previous helper theorem gives a homotopy from the normalized boundary map to a
-- constant map via `h(x,t) = f(t x) / |f(t x)|`. Degree is invariant under homotopy by
-- `circleDegree_eq_of_homotopic`, and constants have degree `0` by `circleDegree_const`.
theorem circleDegree_polynomialNormalizedBoundaryMap_eq_zero_of_no_root_closed_unit_disk
    (f : Polynomial ℂ) (hf : ∀ z : ℂ, z ∈ D² → Polynomial.eval z f ≠ 0) :
    deg(polynomialNormalizedBoundaryMap f
      (polynomial_eval_ne_zero_on_circle_of_nonvanishing_closed_unit_disk f hf)) = 0 := by
  -- Replace the boundary map by the constant endpoint of the radial homotopy.
  calc
    deg(polynomialNormalizedBoundaryMap f
        (polynomial_eval_ne_zero_on_circle_of_nonvanishing_closed_unit_disk f hf)) =
        deg(ContinuousMap.const Circle
          (complexDivNormCircle (Polynomial.eval (0 : ℂ) f)
            (polynomial_eval_zero_ne_zero_of_nonvanishing_closed_unit_disk f hf))) :=
      circleDegree_eq_of_homotopic _ _
        (polynomialNormalizedBoundaryMap_homotopic_const_of_no_root_closed_unit_disk f hf)
    -- Constant maps have degree zero.
    _ = 0 := circleDegree_const _
