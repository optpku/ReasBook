/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.10 lies in the Chapter 5 simplex-monomial / positive-orthant directional-
derivative domain.

Sampled owner declarations:
* `lineDerivWithin` from mathlib, the canonical owner for within-domain directional derivatives
  along affine lines;
* `ambientMonomialXi` and `ξ_[a]` from `Definition_5_4_7_17`, the ambient/source-facing owners
  for the simplex monomial;
* `lineDerivWithin_log_monomialXi_eq_centerMass_relativeDirection` from `Theorem_5_4_7_9`, the
  adjacent owner-level logarithmic derivative identity this theorem builds on;
* `Finset.centerMass` together with the notation `δ[x](h)` from `Definition_5_4_7_14` and
  `Definition_5_4_7_18`, the canonical weighted-mean owner and the source-facing relative
  direction.

Source/core/bridge triage:
* source-facing: the textbook identity `D ξ_a(x)[h] = ξ_a(x) ⟪a, δ_x(h)⟫`;
* core/canonical: `lineDerivWithin ℝ (ambientMonomialXi a) Xₙ x h`;
* bridge/view: the source-facing value `ξ_[a] x` and the logarithmic derivative theorem from
  `Theorem_5_4_7_9`.

This file therefore stays as a thin bridge theorem over the ambient owner `lineDerivWithin`; it
keeps no parallel logarithmic-derivative wrapper, and it treats Theorem 5.4.7.9 as the upstream
owner-level input rather than restating that API locally.
-/

-- Proof sketch: combine the scalar chain rule for `exp` with the logarithmic derivative identity
-- from `Theorem_5_4_7_9`, using that on the strict positive orthant
-- `ambientMonomialXi a = Real.exp ∘ (Real.log ∘ ambientMonomialXi a)`, and then rewrite the
-- value term by `ambientMonomialXi_eq_monomialXi`.
/-- Helper for Theorem 5.4.7.10: the positive orthant is the preimage of the product of open
positive rays under the canonical Euclidean-space coordinate homeomorphism. -/
private theorem positiveOrthant_eq_preimage_piIoi :
    (Xₙ : Set Eₙ) =
      ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph) ⁻¹'
        Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ)) := by
  -- Reduce orthant membership to the coordinatewise positivity predicate.
  ext x
  simp [EuclideanSpace.positiveOrthant]

/-- Helper for Theorem 5.4.7.10: the strict positive orthant is open in `Eₙ`. -/
private theorem positiveOrthant_isOpen : IsOpen (Xₙ : Set Eₙ) := by
  -- Rewrite the orthant as a preimage of a product of open rays.
  rw [positiveOrthant_eq_preimage_piIoi]
  exact (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi).preimage
    ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.continuous)

/-- Helper for Theorem 5.4.7.10: every coordinate of the affine slice `x + t h` stays positive
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

/-- Helper for Theorem 5.4.7.10: near `t = 0`, the monomial slice equals the exponential of the
weighted logarithmic slice. -/
private theorem monomial_slice_eventually_eq_exp_log_sum
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    (fun t : ℝ ↦ ambientMonomialXi a ((x : Eₙ) + t • h)) =ᶠ[nhds (0 : ℝ)]
      (fun t : ℝ ↦ Real.exp (∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i))) := by
  -- Route correction: the identity `x^a = exp (a log x)` is only valid on positive coordinates,
  -- so we use it only on a neighborhood where every affine coordinate stays positive.
  filter_upwards [coordinate_slice_eventually_pos x h] with t ht
  rw [ambientMonomialXi_apply, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simpa [mul_comm, smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_left_comm, mul_assoc] using
    (Real.rpow_def_of_pos (ht i) (a i))

/-- Helper for Theorem 5.4.7.10: the weighted logarithmic slice has derivative at `0` equal to the
simplex-weighted mean of the relative direction. -/
private theorem log_monomial_slice_hasDerivAt_centerMass
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    HasDerivAt
      (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i))
      (Finset.univ.centerMass a (δ[x](h)))
      0 := by
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
            simpa [relativeDirection_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
              using (hlog0.comp 0 haff)
          simpa using hlog.const_mul (a i)))
  -- Convert the weighted sum to the canonical center-of-mass notation.
  have hcenter :
      Finset.univ.centerMass a (δ[x](h)) =
        ∑ i : Fin n, a i * δ[x](h) i := by
    simpa [smul_eq_mul] using
      (show Finset.univ.centerMass a (δ[x](h)) =
          ∑ i : Fin n, a i • δ[x](h) i from
        Finset.univ.centerMass_eq_of_sum_1 (δ[x](h)) (stdSimplex.sum_eq_one a))
  simpa [hcenter] using hsum

/-- Helper for Theorem 5.4.7.10: evaluating the exponential log-sum slice at `t = 0` recovers the
monomial value `ξ_[a] x`. -/
private theorem exp_log_sum_at_zero_eq_monomialXi
    (a : Δ[n]) (x : Xₙ) :
    Real.exp (∑ i : Fin n, a i * Real.log ((x : Eₙ) i)) = ξ_[a] x := by
  -- Expand `exp` over the finite sum and collapse each factor with the positive-coordinate
  -- `rpow` identity.
  rw [Real.exp_sum]
  calc
    ∏ i : Fin n, Real.exp (a i * Real.log ((x : Eₙ) i))
        = ∏ i : Fin n, Real.rpow ((x : Eₙ) i) (a i) := by
            refine Finset.prod_congr rfl fun i _ ↦ ?_
            symm
            simpa [mul_comm] using (Real.rpow_def_of_pos (x.2 i) (a i))
    _ = ξ_[a] x := by
          simp

/-- Theorem 5.4.7.10: for `a ∈ Δₙ`, the directional derivative of the monomial `ξ_a` at a
strictly positive point `x` along `h` is
`ξ_a(x) Finset.univ.centerMass a (δ_x(h)) = ξ_a(x) ⟪a, δ_x(h)⟫`. -/
theorem lineDerivWithin_monomialXi_eq_monomialXi_mul_centerMass_relativeDirection
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    lineDerivWithin ℝ (ambientMonomialXi a) Xₙ x h =
      ξ_[a] x * Finset.univ.centerMass a (δ[x](h)) := by
  -- Introduce the logarithmic scalar slice used for the chain-rule computation.
  let ψ : ℝ → ℝ :=
    fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)
  calc
    lineDerivWithin ℝ (ambientMonomialXi a) Xₙ x h
        = lineDeriv ℝ (ambientMonomialXi a) x h := by
            -- On the open orthant, the within-derivative is the ordinary line derivative.
            rw [lineDerivWithin_of_isOpen positiveOrthant_isOpen x.2]
    _ = deriv (fun t : ℝ ↦ Real.exp (ψ t)) 0 := by
          -- Replace the monomial slice by the exponential of the log-sum slice near `0`.
          rw [lineDeriv, Filter.EventuallyEq.deriv_eq]
          simpa [ψ, Pi.smul_apply] using monomial_slice_eventually_eq_exp_log_sum a x h
    _ = Real.exp (ψ 0) * Finset.univ.centerMass a (δ[x](h)) := by
          -- Differentiate `exp ∘ ψ` by the scalar chain rule.
          rw [(log_monomial_slice_hasDerivAt_centerMass a x h).exp.deriv]
    _ = ξ_[a] x * Finset.univ.centerMass a (δ[x](h)) := by
          -- Evaluate the value term at the basepoint to recover the monomial.
          rw [show ψ 0 = ∑ i : Fin n, a i * Real.log ((x : Eₙ) i) by simp [ψ]]
          rw [exp_log_sum_at_zero_eq_monomialXi]

end
