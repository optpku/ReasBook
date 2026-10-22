/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.11 lies in the Chapter 5 simplex-monomial / directional-second-derivative
domain.

Sampled owner declarations:
* `secondDirectionalDerivative` in `Definition_5_0_10`, the chapter owner for `D²f(x)[h,h]`;
* `ambientMonomialXi` and `ξ_[a]` in `Definition_5_4_7_17`, the simplex monomial owner and its
  ambient/source-facing bridge;
* `quantityS2` in `Definition_5_4_7_18`, the source-facing weighted centered second moment of the
  relative direction.

Source/core/bridge triage:
* source-facing: Theorem 5.4.7.11's identity `D² ξ_a(x)[h,h] = -ξ_a(x) S₂`;
* core/canonical: `secondDirectionalDerivative (ambientMonomialXi a) x h`;
* bridge/view: the expanded quadratic polynomial in the weighted mean
  `Finset.univ.centerMass a (δ[x](h))` and weighted square sum
  `a ⬝ᵥ fun i ↦ (δ[x](h) i) ^ (2 : ℕ)`.

The file is therefore downstream from the existing owners `secondDirectionalDerivative`,
`ambientMonomialXi`, `ξ_[a]`, and `quantityS2`. It keeps only the derivative theorem and its
explicit bridge formula, rather than restating any local wrapper for the monomial, the relative
direction, or the centered second moment. -/

/-- Helper for Theorem 5.4.7.11: every coordinate of the affine slice `x + t h` stays positive
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

/-- Helper for Theorem 5.4.7.11: near `t = 0`, the monomial slice equals the exponential of the
weighted logarithmic slice. -/
private theorem monomial_directionalSlice_eventually_eq_exp_logSum
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    directionalSlice (ambientMonomialXi a) x h =ᶠ[nhds (0 : ℝ)]
      fun t : ℝ ↦ Real.exp (∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) := by
  -- Route correction: the identity `x^a = exp (a log x)` is only valid on positive coordinates,
  -- so we enforce it on a neighborhood where every affine coordinate stays in `(0, ∞)`.
  filter_upwards [coordinate_slice_eventually_pos x h] with t ht
  rw [directionalSlice, ambientMonomialXi_apply, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simpa [mul_comm, smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_left_comm, mul_assoc] using
    (Real.rpow_def_of_pos (ht i) (a i))

/-- Helper for Theorem 5.4.7.11: each coordinate logarithmic slice is `C²` at the basepoint. -/
private theorem coordinate_log_slice_contDiffAt
    (x : Xₙ) (h : Eₙ) (i : Fin n) :
    ContDiffAt ℝ 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 := by
  -- Compose the smooth logarithm at the positive coordinate `x i` with the affine slice.
  have hlog : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i) := by
    simpa using (Real.contDiffAt_log.2 (x.2 i).ne')
  have haff : ContDiffAt ℝ 2 (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ ↦ (x : Eₙ) i) 0).add
        (contDiffAt_id.smul_const (h i)))
  have hlog' : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) ((fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0) := by
    simpa using hlog
  simpa using hlog'.comp 0 haff

/-- Helper for Theorem 5.4.7.11: the first derivative of the logarithmic slice at `0` is the
simplex-weighted mean of the relative direction. -/
private theorem log_monomial_slice_deriv_at_zero
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    deriv (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0 =
      Finset.univ.centerMass a (δ[x](h)) := by
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
  -- Convert the weighted sum to the canonical center-of-mass notation.
  rw [hsum.deriv]
  simpa [centerMass_relativeDirection_eq_sum]

/-- Helper for Theorem 5.4.7.11: the second derivative of one coordinate logarithmic slice is the
negative square of the corresponding relative-direction coordinate. -/
private theorem coordinate_log_slice_secondDeriv
    (x : Xₙ) (h : Eₙ) (i : Fin n) :
    iteratedDeriv 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 =
      -((δ[x](h) i) ^ (2 : ℕ)) := by
  have hderiv :
      deriv (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) =
        fun t : ℝ ↦ h i * (((x : Eₙ) i + t * h i)⁻¹) := by
    ext t
    calc
      deriv (fun s : ℝ ↦ Real.log ((x : Eₙ) i + s * h i)) t
          = h i * deriv (fun s : ℝ ↦ Real.log (s + (x : Eₙ) i)) (h i * t) := by
              have hmul :
                  deriv (fun s : ℝ ↦ Real.log (h i * s + (x : Eₙ) i)) t =
                    h i * deriv (fun s : ℝ ↦ Real.log (s + (x : Eₙ) i)) (h i * t) := by
                  simpa [Function.comp, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
                    add_assoc] using
                    deriv_comp_mul_left (h i) (fun s : ℝ ↦ Real.log (s + (x : Eₙ) i)) t
              simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hmul
      _ = h i * deriv Real.log ((h i * t) + (x : Eₙ) i) := by
            rw [deriv_comp_add_const]
      _ = h i * (((h i * t) + (x : Eₙ) i)⁻¹) := by
            rw [Real.deriv_log]
      _ = h i * (((x : Eₙ) i + t * h i)⁻¹) := by
            ring_nf
  -- Differentiate the affine-inverse derivative once more and evaluate at the basepoint.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0
        = deriv (deriv (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i))) 0 := by
            simp [iteratedDeriv_succ]
    _ = deriv (fun t : ℝ ↦ h i * (((x : Eₙ) i + t * h i)⁻¹)) 0 := by
          rw [hderiv]
    _ = h i * deriv (fun t : ℝ ↦ ((x : Eₙ) i + t * h i)⁻¹) 0 := by
          rw [deriv_const_mul_field]
    _ = h i * (h i * deriv (fun t : ℝ ↦ (t + (x : Eₙ) i)⁻¹) (h i * 0)) := by
          have hmul :
              deriv (fun t : ℝ ↦ ((x : Eₙ) i + t * h i)⁻¹) 0 =
                h i * deriv (fun t : ℝ ↦ (t + (x : Eₙ) i)⁻¹) (h i * 0) := by
            simpa [Function.comp, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
              add_assoc] using
              deriv_comp_mul_left (h i) (fun t : ℝ ↦ (t + (x : Eₙ) i)⁻¹) 0
          rw [hmul]
    _ = h i * (h i * deriv Inv.inv ((x : Eₙ) i)) := by
          rw [deriv_comp_add_const]
          simp
    _ = h i * (h i * (-(((x : Eₙ) i) ^ (2 : ℕ))⁻¹)) := by
          rw [deriv_inv]
    _ = -((δ[x](h) i) ^ (2 : ℕ)) := by
          rw [relativeDirection_apply, div_pow]
          field_simp [(x.2 i).ne']

/-- Helper for Theorem 5.4.7.11: the second derivative of the weighted logarithmic slice at `0`
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
    simpa [smul_eq_mul] using (coordinate_log_slice_contDiffAt x h i).const_smul (a i)
  -- Differentiate the finite weighted sum termwise, then substitute the coordinate formula.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0
        = ∑ i : Fin n,
            iteratedDeriv 2 (fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i)) 0 := by
              simpa using (iteratedDeriv_fun_sum (I := Finset.univ) hcont)
    _ = ∑ i : Fin n, a i *
          iteratedDeriv 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 := by
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

-- Proof sketch: differentiate the directional slice of the ambient monomial once more along the
-- repeated direction `h`, rewrite the derivative of each relative coordinate `h i / x i` as
-- `-(h i / x i)^2`, and factor the result into `ξ_a(x)` times the weighted mean square minus the
-- weighted square sum.
/-- The second directional derivative of the simplex monomial `ξ_a` admits the expanded formula
`ξ_a(x) (m^2 - ⟪a, [δ]^2⟫)`, where `δ = δ_x(h)` and
`m = Finset.univ.centerMass a (δ[x](h)) = ⟪a, δ⟫`. -/
theorem monomialXi_secondDirectionalDerivative_eq_mul_quadratic_relativeDirection_polynomial
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    secondDirectionalDerivative (ambientMonomialXi a) x h =
        ξ_[a] x *
          (Finset.univ.centerMass a (δ[x](h)) ^ (2 : ℕ) -
            a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) := by
  let ψ : ℝ → ℝ :=
    fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)
  have hslice :
      secondDirectionalDerivative (ambientMonomialXi a) x h =
        iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (ψ t)) 0 := by
    -- Replace the monomial slice by the exponential of the log-slice on a neighborhood of `0`.
    rw [secondDirectionalDerivative]
    have heq :
        directionalSlice (ambientMonomialXi a) x h =ᶠ[nhds (0 : ℝ)]
          fun t : ℝ ↦ Real.exp (ψ t) := by
      simpa [ψ] using monomial_directionalSlice_eventually_eq_exp_logSum a x h
    exact Filter.EventuallyEq.iteratedDeriv_eq 2 heq
  have hψcont : ContDiffAt ℝ 2 ψ 0 := by
    -- The weighted log-slice is a finite sum of `C²` coordinate logarithmic slices.
    classical
    refine ContDiffAt.sum ?_
    intro i
    simpa [smul_eq_mul] using (coordinate_log_slice_contDiffAt x h i).const_smul (a i)
  have hcomp :
      iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (ψ t)) 0 =
        Real.exp (ψ 0) * deriv ψ 0 ^ (2 : ℕ) +
          Real.exp (ψ 0) * iteratedDeriv 2 ψ 0 := by
    -- Apply the scalar second-order chain rule to `exp ∘ ψ`.
    simpa [Function.comp, iteratedDeriv_succ, Real.deriv_exp] using
      (iteratedDeriv_comp_two
        (g := fun s : ℝ ↦ Real.exp s)
        (f := ψ)
        (x := 0)
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
      _ = ξ_[a] x := by simp
  -- Assemble the chain-rule identity with the first and second log-slice derivatives.
  calc
    secondDirectionalDerivative (ambientMonomialXi a) x h
        = iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (ψ t)) 0 := hslice
    _ = Real.exp (ψ 0) * deriv ψ 0 ^ (2 : ℕ) +
          Real.exp (ψ 0) * iteratedDeriv 2 ψ 0 := hcomp
    _ = ξ_[a] x *
          (Finset.univ.centerMass a (δ[x](h)) ^ (2 : ℕ) -
            a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) := by
          rw [hvalue, log_monomial_slice_deriv_at_zero, log_monomial_slice_secondDeriv_at_zero]
          ring

/-- Helper for Theorem 5.4.7.11: the centered second moment `quantityS2` expands as the weighted
square sum minus the square of the weighted mean. -/
private theorem quantityS2_eq_weighted_square_sum_sub_centerMass_sq
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    quantityS2 a x h =
      (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) -
        Finset.univ.centerMass a (δ[x](h)) ^ (2 : ℕ) := by
  let m : ℝ := Finset.univ.centerMass a (δ[x](h))
  have hm :
      ∑ i : Fin n, a i * δ[x](h) i = m := by
    simp [m, centerMass_relativeDirection_eq_sum]
  -- Expand the centered square and collapse the linear and constant weighted sums.
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
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            rw [Finset.sum_neg_distrib]
            rw [← Finset.mul_sum (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i * δ[x](h) i) (2 * m)]
            rw [← Finset.sum_mul (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i) (m ^ (2 : ℕ))]
    _ = (∑ i : Fin n, a i * (δ[x](h) i) ^ (2 : ℕ)) - m ^ (2 : ℕ) := by
          rw [hm, stdSimplex.sum_eq_one a]
          ring
    _ = (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) -
          Finset.univ.centerMass a (δ[x](h)) ^ (2 : ℕ) := by
            have hdot :
                ∑ i : Fin n, a i * (δ[x](h) i) ^ (2 : ℕ) =
                  a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ) := rfl
            rw [hdot]

-- Proof sketch: combine the expanded second-derivative formula with the identity
-- `quantityS2 a x h = ⟪a, [δ_x(h)]^2⟫ - ⟪a, δ_x(h)⟫^2`, so the bracket equals `-S₂`.
/-- Theorem 5.4.7.11: the second directional derivative of `ξ_a` on the positive orthant equals
`-ξ_a(x) S₂`, where `S₂ = quantityS2 a x h` is the weighted second centered moment of the
relative direction `δ_x(h)`. -/
theorem monomialXi_secondDirectionalDerivative_eq_neg_mul_quantityS2
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    secondDirectionalDerivative (ambientMonomialXi a) x h =
        -(ξ_[a] x * quantityS2 a x h) := by
  -- Substitute the centered-second-moment identity into the expanded quadratic formula.
  calc
    secondDirectionalDerivative (ambientMonomialXi a) x h
        = ξ_[a] x *
            (Finset.univ.centerMass a (δ[x](h)) ^ (2 : ℕ) -
              a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) := by
            exact monomialXi_secondDirectionalDerivative_eq_mul_quadratic_relativeDirection_polynomial a x h
    _ = -((ξ_[a] x) *
            ((a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) -
              Finset.univ.centerMass a (δ[x](h)) ^ (2 : ℕ))) := by
          ring
    _ = -(ξ_[a] x * quantityS2 a x h) := by
          rw [quantityS2_eq_weighted_square_sum_sub_centerMass_sq]

end
