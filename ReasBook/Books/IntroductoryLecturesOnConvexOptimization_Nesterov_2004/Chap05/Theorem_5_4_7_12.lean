/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.12 lies in the chapter's simplex-monomial / directional-derivative domain.

Sampled owner declarations:
* `thirdDirectionalDerivative` in `Definition_5_0_10`, the chapter owner for
  `D³f(x)[h,h,h]`;
* `ambientMonomialXi` and `ξ_[a]` in `Definition_5_4_7_17`, the simplex monomial owner and its
  ambient bridge;
* `quantityS2` in `Definition_5_4_7_18`, the weighted centered second moment;
* `quantityS3` in `Definition_5_4_7_19`, the weighted centered third moment.

Source/core/bridge triage:
* source-facing: the explicit formulas for the third directional derivative of `ξ_a`;
* core/canonical: `thirdDirectionalDerivative (ambientMonomialXi a) x h`;
* bridge/view: the expanded cubic polynomial in the weighted mean and its reformulation in terms
  of `S₂` and `S₃`.

This file therefore keeps the theorem content but uses the chapter owner
`thirdDirectionalDerivative` as the public derivative surface, rather than restating the raw
`iteratedFDerivWithin` expression.
-/

section

variable (a : Δ[n]) (x : Xₙ) (h : Eₙ)

local notation "m" => Finset.univ.centerMass a (δ[x](h))

/-- Helper for Theorem 5.4.7.12: every coordinate of the affine slice `x + t h` stays positive
for all sufficiently small `t`. -/
private theorem coordinate_slice_eventually_pos
    (x : Xₙ) (h : Eₙ) :
    ∀ᶠ t in nhds (0 : ℝ), ∀ i : Fin n, 0 < (x : Eₙ) i + t * h i := by
  -- Control each coordinate separately, then intersect the finitely many neighborhoods.
  refine Filter.eventually_all.2 ?_
  intro i
  have hcont : ContinuousAt (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (x : Eₙ) i) 0).add
        (continuousAt_id.const_mul (h i)))
  exact hcont.eventually (lt_mem_nhds (by simpa using x.2 i))

/-- Helper for Theorem 5.4.7.12: near `t = 0`, the monomial slice equals the exponential of the
weighted logarithmic slice. -/
private theorem monomial_directionalSlice_eventually_eq_exp_logSum
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    directionalSlice (ambientMonomialXi a) x h =ᶠ[nhds (0 : ℝ)]
      fun t : ℝ ↦ Real.exp (∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) := by
  -- Route correction: the identity `x^a = exp (a log x)` is valid only on positive coordinates,
  -- so we restrict to a neighborhood where every affine coordinate stays positive.
  filter_upwards [coordinate_slice_eventually_pos x h] with t ht
  rw [directionalSlice, ambientMonomialXi_apply, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simpa [mul_comm, smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_left_comm, mul_assoc] using
    (Real.rpow_def_of_pos (ht i) (a i))

/-- Helper for Theorem 5.4.7.12: the coordinate affine slice is smooth to every finite order. -/
private theorem coordinate_affine_slice_contDiffAt
    (x : Xₙ) (h : Eₙ) (k : ℕ) (i : Fin n) :
    ContDiffAt ℝ k (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 := by
  -- The affine coordinate slice is the sum of a constant and a linear map.
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    ((contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ ↦ (x : Eₙ) i) 0).add
      (contDiffAt_id.smul_const (h i)))

/-- Helper for Theorem 5.4.7.12: each coordinate logarithmic slice is smooth to every finite
order at the basepoint. -/
private theorem coordinate_log_slice_contDiffAt
    (x : Xₙ) (h : Eₙ) (k : ℕ) (i : Fin n) :
    ContDiffAt ℝ k (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 := by
  -- Compose the smooth logarithm at the positive coordinate `x i` with the affine slice.
  have hlog : ContDiffAt ℝ k (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i) := by
    simpa using
      (Real.contDiffAt_log.2 (x.2 i).ne' : ContDiffAt ℝ k (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i))
  have hlog' : ContDiffAt ℝ k (fun s : ℝ ↦ Real.log s) ((fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0) := by
    simpa using hlog
  simpa using hlog'.comp 0 (coordinate_affine_slice_contDiffAt x h k i)

/-- Helper for Theorem 5.4.7.12: the affine coordinate slice has constant derivative `h i`. -/
private theorem coordinate_affine_slice_deriv
    (x : Xₙ) (h : Eₙ) (i : Fin n) :
    deriv (fun t : ℝ ↦ (x : Eₙ) i + t * h i) = fun _ : ℝ ↦ h i := by
  -- Differentiate the constant-plus-linear affine slice pointwise.
  ext t
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using
    ((((hasDerivAt_id t).mul_const (h i)).const_add ((x : Eₙ) i)).deriv)

/-- Helper for Theorem 5.4.7.12: the second iterated derivative of `log` is `-(x^2)⁻¹`. -/
private theorem log_iteratedDeriv_two (y : ℝ) :
    iteratedDeriv 2 Real.log y = -((y ^ (2 : ℕ))⁻¹) := by
  -- Rewrite the second iterated derivative as the derivative of the inverse function.
  calc
    iteratedDeriv 2 Real.log y = iteratedDeriv 1 (deriv Real.log) y := by
      rw [iteratedDeriv_succ']
    _ = deriv Inv.inv y := by
      rw [Real.deriv_log']
      rw [iteratedDeriv_one]
    _ = -((y ^ (2 : ℕ))⁻¹) := by
      rw [deriv_inv]

/-- Helper for Theorem 5.4.7.12: the third iterated derivative of `log` is `2 (x^3)⁻¹`. -/
private theorem log_iteratedDeriv_three (y : ℝ) :
    iteratedDeriv 3 Real.log y = 2 * ((y ^ (3 : ℕ))⁻¹) := by
  -- Reduce to the second iterated derivative of inversion and evaluate it explicitly.
  calc
    iteratedDeriv 3 Real.log y = iteratedDeriv 2 (deriv Real.log) y := by
      rw [iteratedDeriv_succ']
    _ = iteratedDeriv 2 Inv.inv y := by
      rw [Real.deriv_log']
    _ = deriv^[2] Inv.inv y := by
      rw [← iteratedDeriv_eq_iterate]
    _ = (-1 : ℝ) ^ 2 * (Nat.factorial 2 : ℝ) * y ^ (-1 - 2 : ℤ) := by
      simpa using (iter_deriv_inv 2 y)
    _ = 2 * ((y ^ (3 : ℕ))⁻¹) := by
      rw [show (-1 - 2 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
      norm_num

/-- Helper for Theorem 5.4.7.12: the second derivative of one coordinate logarithmic slice is the
negative square of the corresponding relative-direction coordinate. -/
private theorem coordinate_log_slice_secondDeriv
    (x : Xₙ) (h : Eₙ) (i : Fin n) :
    iteratedDeriv 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 =
      -((δ[x](h) i) ^ (2 : ℕ)) := by
  have hlog : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i) := by
    simpa using
      (Real.contDiffAt_log.2 (x.2 i).ne' : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i))
  have hlog' : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) ((fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0) := by
    simpa using hlog
  have hcomp :
      iteratedDeriv 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 =
        iteratedDeriv 2 Real.log ((x : Eₙ) i) * deriv (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 ^ (2 : ℕ) +
          deriv Real.log ((x : Eₙ) i) * iteratedDeriv 2 (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 := by
    -- Apply the scalar second-order chain rule to `log ∘ affine`.
    simpa [Function.comp] using
      (iteratedDeriv_comp_two
        (x := 0)
        (g := fun s : ℝ ↦ Real.log s)
        (f := fun t : ℝ ↦ (x : Eₙ) i + t * h i)
        hlog'
        (coordinate_affine_slice_contDiffAt x h 2 i))
  -- Collapse the higher affine derivatives and rewrite the remaining factor as `δ_i^2`.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0
        = iteratedDeriv 2 Real.log ((x : Eₙ) i) * (h i) ^ (2 : ℕ) := by
            simpa [coordinate_affine_slice_deriv x h, iteratedDeriv_succ,
              iteratedDeriv_one, mul_comm, mul_left_comm, mul_assoc] using hcomp
    _ = (-(((x : Eₙ) i ^ (2 : ℕ))⁻¹)) * (h i) ^ (2 : ℕ) := by
          rw [log_iteratedDeriv_two]
    _ = -((δ[x](h) i) ^ (2 : ℕ)) := by
          rw [relativeDirection_apply, div_pow]
          field_simp [(x.2 i).ne']

/-- Helper for Theorem 5.4.7.12: the third derivative of one coordinate logarithmic slice is
twice the cube of the corresponding relative-direction coordinate. -/
private theorem coordinate_log_slice_thirdDeriv
    (x : Xₙ) (h : Eₙ) (i : Fin n) :
    iteratedDeriv 3 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 =
      2 * ((δ[x](h) i) ^ (3 : ℕ)) := by
  have hlog : ContDiffAt ℝ 3 (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i) := by
    simpa using
      (Real.contDiffAt_log.2 (x.2 i).ne' : ContDiffAt ℝ 3 (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i))
  have hlog' : ContDiffAt ℝ 3 (fun s : ℝ ↦ Real.log s) ((fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0) := by
    simpa using hlog
  have hcomp :
      iteratedDeriv 3 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 =
        iteratedDeriv 3 Real.log ((x : Eₙ) i) * deriv (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 ^ (3 : ℕ) +
          3 * iteratedDeriv 2 Real.log ((x : Eₙ) i) *
            iteratedDeriv 2 (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 *
            deriv (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 +
          deriv Real.log ((x : Eₙ) i) * iteratedDeriv 3 (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 := by
    -- Apply the scalar third-order chain rule to `log ∘ affine`.
    simpa [Function.comp] using
      (iteratedDeriv_comp_three
        (x := 0)
        (g := fun s : ℝ ↦ Real.log s)
        (f := fun t : ℝ ↦ (x : Eₙ) i + t * h i)
        hlog'
        (coordinate_affine_slice_contDiffAt x h 3 i))
  -- The affine slice has no second or third derivatives, so only the cubic first-derivative term remains.
  calc
    iteratedDeriv 3 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0
        = iteratedDeriv 3 Real.log ((x : Eₙ) i) * (h i) ^ (3 : ℕ) := by
            simpa [coordinate_affine_slice_deriv x h, iteratedDeriv_succ,
              iteratedDeriv_one, mul_comm, mul_left_comm, mul_assoc] using hcomp
    _ = (2 * (((x : Eₙ) i ^ (3 : ℕ))⁻¹)) * (h i) ^ (3 : ℕ) := by
          rw [log_iteratedDeriv_three]
    _ = 2 * ((δ[x](h) i) ^ (3 : ℕ)) := by
          rw [relativeDirection_apply, div_pow]
          field_simp [(x.2 i).ne']

/-- Helper for Theorem 5.4.7.12: the first derivative of the weighted logarithmic slice at `0`
is the simplex-weighted mean of the relative direction. -/
private theorem log_monomial_slice_deriv_at_zero
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    deriv (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0 = m := by
  have hsum :
      HasDerivAt
        (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i))
        (∑ i : Fin n, a i * δ[x](h) i)
        0 := by
    -- Differentiate each coordinate logarithm and sum the weighted contributions.
    simpa using
      (HasDerivAt.fun_sum
        (u := Finset.univ)
        (A := fun i : Fin n => fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i))
        (A' := fun i : Fin n => a i * δ[x](h) i)
        (x := 0)
        (fun i _ ↦ by
          have hlog :
              HasDerivAt
                (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i))
                (δ[x](h) i)
                0 := by
            have hmul : HasDerivAt (fun t : ℝ ↦ t * h i) (h i) 0 := by
              simpa using (hasDerivAt_id 0).mul_const (h i)
            have haff : HasDerivAt (fun t : ℝ ↦ (x : Eₙ) i + t * h i) (h i) 0 := by
              simpa [add_comm] using hmul.const_add ((x : Eₙ) i)
            have hlog0 :
                HasDerivAt
                  Real.log
                  (((x : Eₙ) i + 0 * h i)⁻¹)
                  ((x : Eₙ) i + 0 * h i) := by
              simpa using
                (Real.hasDerivAt_log
                  (show (x : Eₙ) i + 0 * h i ≠ 0 by simpa using (x.2 i).ne'))
            simpa [relativeDirection_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
              (hlog0.comp 0 haff)
          simpa using hlog.const_mul (a i)))
  -- Convert the weighted sum to the center-of-mass notation.
  rw [hsum.deriv]
  simpa [centerMass_relativeDirection_eq_sum, m]

/-- Helper for Theorem 5.4.7.12: the second derivative of the weighted logarithmic slice at `0`
is the negative weighted square sum of the relative direction coordinates. -/
private theorem log_monomial_slice_secondDeriv_at_zero
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    iteratedDeriv 2 (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0 =
      -(a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) := by
  have hcont :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ContDiffAt ℝ 2
          (fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i))
          0 := by
    -- Each weighted coordinate term is `C²` because the underlying coordinate log-slice is.
    intro i hi
    simpa [smul_eq_mul] using
      (coordinate_log_slice_contDiffAt x h 2 i).const_smul (a i)
  -- Differentiate the finite weighted sum termwise and substitute the coordinate formula.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0
        = ∑ i : Fin n,
            iteratedDeriv 2 (fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i)) 0 := by
              simpa using (iteratedDeriv_fun_sum (I := Finset.univ) hcont)
    _ = ∑ i : Fin n,
          a i * iteratedDeriv 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simpa using
            (iteratedDeriv_const_mul_field
              (n := 2)
              (x := 0)
              (c := a i)
              (f := fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)))
    _ = ∑ i : Fin n, a i * (-(δ[x](h) i ^ (2 : ℕ))) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [coordinate_log_slice_secondDeriv x h i]
    _ = -(a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) := by
          rw [show (∑ i : Fin n, a i * (-(δ[x](h) i ^ (2 : ℕ)))) =
              -∑ i : Fin n, a i * (δ[x](h) i ^ (2 : ℕ)) by
                simp_rw [mul_neg]
                rw [Finset.sum_neg_distrib]]
          rfl

/-- Helper for Theorem 5.4.7.12: the third derivative of the weighted logarithmic slice at `0`
is twice the weighted cube sum of the relative direction coordinates. -/
private theorem log_monomial_slice_thirdDeriv_at_zero
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    iteratedDeriv 3 (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0 =
      2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ)) := by
  have hcont :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ContDiffAt ℝ 3
          (fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i))
          0 := by
    -- Each weighted coordinate term is `C³` because the underlying coordinate log-slice is.
    intro i hi
    simpa [smul_eq_mul] using
      (coordinate_log_slice_contDiffAt x h 3 i).const_smul (a i)
  -- Differentiate the finite weighted sum termwise and substitute the coordinate cubic formula.
  calc
    iteratedDeriv 3 (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0
        = ∑ i : Fin n,
            iteratedDeriv 3 (fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i)) 0 := by
              simpa using (iteratedDeriv_fun_sum (I := Finset.univ) hcont)
    _ = ∑ i : Fin n,
          a i * iteratedDeriv 3 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simpa using
            (iteratedDeriv_const_mul_field
              (n := 3)
              (x := 0)
              (c := a i)
              (f := fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)))
    _ = ∑ i : Fin n, a i * (2 * (δ[x](h) i ^ (3 : ℕ))) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [coordinate_log_slice_thirdDeriv x h i]
    _ = 2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ)) := by
          calc
            ∑ i : Fin n, a i * (2 * (δ[x](h) i ^ (3 : ℕ)))
                = ∑ i : Fin n, 2 * (a i * (δ[x](h) i ^ (3 : ℕ))) := by
                    refine Finset.sum_congr rfl fun i _ ↦ ?_
                    ring
            _ = 2 * ∑ i : Fin n, a i * (δ[x](h) i ^ (3 : ℕ)) := by
                  rw [← Finset.mul_sum]
            _ = 2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i ^ (3 : ℕ))) := by
                  rfl

/-- Helper for Theorem 5.4.7.12: `S₂` is the weighted square sum minus the square of the weighted
mean. -/
private theorem quantityS2_eq_weighted_square_sum_sub_centerMass_sq
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    quantityS2 a x h =
      (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) - m ^ (2 : ℕ) := by
  have hm :
      ∑ i : Fin n, a i * δ[x](h) i = m := by
    simp [centerMass_relativeDirection_eq_sum, m]
  -- Expand the centered square and collapse the weighted linear and constant sums.
  rw [quantityS2_eq_sum]
  calc
    ∑ i : Fin n, a i * (δ[x](h) i - m) ^ (2 : ℕ)
        = ∑ i : Fin n,
            (a i * (δ[x](h) i) ^ (2 : ℕ) - 2 * m * (a i * δ[x](h) i) + a i * m ^ (2 : ℕ)) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              ring
    _ = (∑ i : Fin n, a i * (δ[x](h) i) ^ (2 : ℕ)) -
          2 * m * (∑ i : Fin n, a i * δ[x](h) i) +
          (∑ i : Fin n, a i) * m ^ (2 : ℕ) := by
            simp_rw [sub_eq_add_neg]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
            rw [← Finset.mul_sum (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i * δ[x](h) i) (2 * m)]
            rw [← Finset.sum_mul (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i) (m ^ (2 : ℕ))]
    _ = (∑ i : Fin n, a i * (δ[x](h) i) ^ (2 : ℕ)) - m ^ (2 : ℕ) := by
          rw [hm, stdSimplex.sum_eq_one a]
          ring
    _ = (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) - m ^ (2 : ℕ) := by
          rfl

/-- Helper for Theorem 5.4.7.12: `S₃` expands into the weighted cubic polynomial in the relative
direction and its center of mass. -/
private theorem quantityS3_eq_weighted_cube_sub_three_centerMass_mul_weighted_square_add_two_centerMass_cubed
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    quantityS3 a x h =
      (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ)) -
        3 * m * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
        2 * m ^ (3 : ℕ) := by
  have hm :
      ∑ i : Fin n, a i * δ[x](h) i = m := by
    simp [centerMass_relativeDirection_eq_sum, m]
  -- Expand the centered cube and collapse the weighted linear and constant sums.
  rw [quantityS3_eq_sum]
  calc
    ∑ i : Fin n, a i * (δ[x](h) i - m) ^ (3 : ℕ)
        = ∑ i : Fin n,
            (a i * (δ[x](h) i) ^ (3 : ℕ) -
              3 * m * (a i * (δ[x](h) i) ^ (2 : ℕ)) +
              3 * m ^ (2 : ℕ) * (a i * δ[x](h) i) -
              a i * m ^ (3 : ℕ)) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              ring
    _ = (∑ i : Fin n, a i * (δ[x](h) i) ^ (3 : ℕ)) -
          3 * m * (∑ i : Fin n, a i * (δ[x](h) i) ^ (2 : ℕ)) +
          3 * m ^ (2 : ℕ) * (∑ i : Fin n, a i * δ[x](h) i) -
          (∑ i : Fin n, a i) * m ^ (3 : ℕ) := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
            rw [← Finset.mul_sum (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i * (δ[x](h) i) ^ (2 : ℕ)) (3 * m)]
            rw [← Finset.mul_sum (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i * δ[x](h) i) (3 * m ^ (2 : ℕ))]
            rw [← Finset.sum_mul (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i) (m ^ (3 : ℕ))]
    _ = (∑ i : Fin n, a i * (δ[x](h) i) ^ (3 : ℕ)) -
          3 * m * (∑ i : Fin n, a i * (δ[x](h) i) ^ (2 : ℕ)) +
          2 * m ^ (3 : ℕ) := by
            rw [hm, stdSimplex.sum_eq_one a]
            ring
    _ = (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ)) -
          3 * m * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
          2 * m ^ (3 : ℕ) := by
            rfl

/-- Helper for Theorem 5.4.7.12: the combination `2 S₃ + 3 m S₂` equals the cubic polynomial in
the weighted mean, weighted square sum, and weighted cube sum. -/
private theorem two_quantityS3_add_three_mean_quantityS2_eq_cubic_relativeDirection_polynomial
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    2 * quantityS3 a x h + 3 * m * quantityS2 a x h =
      m ^ (3 : ℕ) -
        3 * m * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
        2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ)) := by
  -- Substitute the centered-moment expansions and collect like terms.
  rw [quantityS3_eq_weighted_cube_sub_three_centerMass_mul_weighted_square_add_two_centerMass_cubed,
    quantityS2_eq_weighted_square_sum_sub_centerMass_sq]
  ring

/-- The third directional derivative of the simplex monomial `ξ_a` equals `ξ_a(x)` times the
cubic polynomial in the weighted mean
`m = Finset.univ.centerMass a (δ[x](h)) = ⟪a, δ_x(h)⟫`, the weighted square sum
`⟪a, [δ_x(h)]^2⟫`, and the weighted cube sum `⟪a, [δ_x(h)]^3⟫`. -/
theorem monomialXi_thirdDirectionalDerivative_eq_mul_cubic_relativeDirection_polynomial :
    thirdDirectionalDerivative (ambientMonomialXi a) x h =
        ξ_[a] x *
          (m ^ (3 : ℕ) -
            3 * m * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
            2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ))) := by
  let ψ : ℝ → ℝ :=
    fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)
  have hslice :
      thirdDirectionalDerivative (ambientMonomialXi a) x h =
        iteratedDeriv 3 (fun t : ℝ ↦ Real.exp (ψ t)) 0 := by
    -- Replace the monomial slice by the exponential of the log-slice on a neighborhood of `0`.
    rw [thirdDirectionalDerivative]
    have heq :
        directionalSlice (ambientMonomialXi a) x h =ᶠ[nhds (0 : ℝ)]
          fun t : ℝ ↦ Real.exp (ψ t) := by
      simpa [ψ] using monomial_directionalSlice_eventually_eq_exp_logSum a x h
    exact Filter.EventuallyEq.iteratedDeriv_eq 3 heq
  have hψcont : ContDiffAt ℝ 3 ψ 0 := by
    -- The weighted log-slice is a finite sum of `C³` coordinate logarithmic slices.
    classical
    refine ContDiffAt.sum ?_
    intro i
    simpa [smul_eq_mul] using
      (coordinate_log_slice_contDiffAt x h 3 i).const_smul (a i)
  have hcomp :
      iteratedDeriv 3 (fun t : ℝ ↦ Real.exp (ψ t)) 0 =
        Real.exp (ψ 0) * deriv ψ 0 ^ (3 : ℕ) +
          3 * Real.exp (ψ 0) * iteratedDeriv 2 ψ 0 * deriv ψ 0 +
          Real.exp (ψ 0) * iteratedDeriv 3 ψ 0 := by
    -- Apply the scalar third-order chain rule to `exp ∘ ψ`.
    simpa [Function.comp, iteratedDeriv_succ, Real.deriv_exp] using
      (iteratedDeriv_comp_three
        (x := 0)
        (g := fun s : ℝ ↦ Real.exp s)
        (f := ψ)
        Real.contDiff_exp.contDiffAt
        hψcont)
  have hvalue : Real.exp (ψ 0) = ξ_[a] x := by
    -- Evaluate the exponential log-slice at the basepoint and recover the monomial value.
    rw [show ψ 0 = ∑ i : Fin n, a i * Real.log ((x : Eₙ) i) by simp [ψ], Real.exp_sum]
    calc
      ∏ i : Fin n, Real.exp (a i * Real.log ((x : Eₙ) i))
          = ∏ i : Fin n, Real.rpow ((x : Eₙ) i) (a i) := by
              refine Finset.prod_congr rfl fun i _ ↦ ?_
              symm
              simpa [mul_comm] using (Real.rpow_def_of_pos (x.2 i) (a i))
      _ = ξ_[a] x := by
            simp
  -- Assemble the chain-rule identity with the first, second, and third log-slice derivatives.
  calc
    thirdDirectionalDerivative (ambientMonomialXi a) x h
        = iteratedDeriv 3 (fun t : ℝ ↦ Real.exp (ψ t)) 0 := hslice
    _ = Real.exp (ψ 0) * deriv ψ 0 ^ (3 : ℕ) +
          3 * Real.exp (ψ 0) * iteratedDeriv 2 ψ 0 * deriv ψ 0 +
          Real.exp (ψ 0) * iteratedDeriv 3 ψ 0 := hcomp
    _ = ξ_[a] x *
          (m ^ (3 : ℕ) -
            3 * m * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
            2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ))) := by
          rw [hvalue, log_monomial_slice_deriv_at_zero, log_monomial_slice_secondDeriv_at_zero,
            log_monomial_slice_thirdDeriv_at_zero]
          ring

-- Proof sketch: start from the expanded cubic formula for the third derivative, expand the
-- centered-cube quantity `S₃`, use the definition of `S₂` as the weighted centered square sum,
-- and collect like terms in `m`.
/-- Theorem 5.4.7.12: the third directional derivative of `ξ_a` on the positive orthant equals
`ξ_a(x) (2 S₃ + 3 m S₂)`, where `m = ⟪a, δ_x(h)⟫`,
`S₂ = quantityS2 a x h`, and
`S₃ = quantityS3 a x h`. -/
theorem monomialXi_thirdDirectionalDerivative_eq_mul_two_S3_add_three_mean_S2 :
    thirdDirectionalDerivative (ambientMonomialXi a) x h =
        ξ_[a] x * (2 * quantityS3 a x h + 3 * m * quantityS2 a x h) := by
  -- Rewrite the expanded cubic formula in terms of the centered moments `S₂` and `S₃`.
  calc
    thirdDirectionalDerivative (ambientMonomialXi a) x h
        = ξ_[a] x *
            (m ^ (3 : ℕ) -
              3 * m * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
              2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ))) := by
            exact monomialXi_thirdDirectionalDerivative_eq_mul_cubic_relativeDirection_polynomial
    _ = ξ_[a] x * (2 * quantityS3 a x h + 3 * m * quantityS2 a x h) := by
          rw [two_quantityS3_add_three_mean_quantityS2_eq_cubic_relativeDirection_polynomial]

end

end
