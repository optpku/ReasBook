/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.9 lies in the Chapter 5 simplex-monomial / positive-orthant directional-
derivative domain.

Sampled owner declarations:
* `lineDerivWithin` from mathlib, the canonical owner for within-domain directional derivatives
  along affine lines;
* `ambientMonomialXi` from `Definition_5_4_7_17`, the ambient owner whose restriction to
  `positiveOrthant n` is the source-facing monomial `ξ_[a]`;
* `relativeDirection` together with the notation `δ[x](h)` from `Definition_5_4_7_14`, the
  source-facing scaled direction;
* `Finset.centerMass` and `centerMass_relativeDirection_eq_sum` from `Definition_5_4_7_18`, the
  canonical weighted-mean owner and its simplex-specialized bridge for `δ_x(h)`.

Source/core/bridge triage:
* source-facing: the logarithmic derivative identity `D log ξ_a(x)[h] = ⟪a, δ_x(h)⟫`;
* core/canonical: `lineDerivWithin ℝ`;
* bridge/view: the ambient representative `Real.log ∘ ambientMonomialXi a` of `log ξ_a` on the
  strict positive orthant, and the center-of-mass expression for the simplex-weighted mean.

The public theorem is therefore a bridge statement over the canonical owner `lineDerivWithin`;
it should not introduce a parallel owner for the logarithmic derivative or a duplicate wrapper
for the weighted mean. -/

-- Proof sketch: on the positive orthant, rewrite `log ξ_a(y)` as the logarithm of the product
-- defining `ξ_a`; then differentiate along the affine line `x + t • h` inside the orthant and
-- identify `δ[x](h)` with the vector whose `i`-th coordinate is `h i / x i`, so the resulting
-- weighted sum is the canonical simplex center of mass `Finset.univ.centerMass a (δ[x](h))`.
/-- Helper for Theorem 5.4.7.9: the positive orthant is the preimage of the product of open
positive rays under the canonical Euclidean-space coordinate homeomorphism. -/
private theorem positiveOrthant_eq_preimage_piIoi :
    (Xₙ : Set Eₙ) =
      ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph) ⁻¹'
        Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ)) := by
  -- Reduce orthant membership to the coordinatewise positivity predicate.
  ext x
  simp [EuclideanSpace.positiveOrthant]

/-- Helper for Theorem 5.4.7.9: the strict positive orthant is open in `Eₙ`. -/
private theorem positiveOrthant_isOpen : IsOpen (Xₙ : Set Eₙ) := by
  -- Rewrite the orthant as a preimage of a product of open rays.
  rw [positiveOrthant_eq_preimage_piIoi]
  exact (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi).preimage
    ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.continuous)

/-- Helper for Theorem 5.4.7.9: on the positive orthant, `log ξ_a` is the simplex-weighted sum
of the coordinate logarithms. -/
private theorem log_ambientMonomialXi_eq_weighted_sum_log
    (a : Δ[n]) {y : Eₙ} (hy : y ∈ Xₙ) :
    Real.log (ambientMonomialXi a y) =
      ∑ i : Fin n, a i * Real.log (y i) := by
  -- Expand the monomial to a finite product and take logs termwise.
  rw [ambientMonomialXi_apply]
  have hlog :
      Real.log (∏ i : Fin n, Real.rpow (y i) (a i)) =
        ∑ i : Fin n, Real.log (Real.rpow (y i) (a i)) := by
    simpa using
      (Real.log_prod fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
        (Real.rpow_pos_of_pos (hy i) (a i)).ne')
  rw [hlog]
  -- Each logarithm of a real power collapses to the exponent times the coordinate log.
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simpa using (Real.log_rpow (hy i) (a i))

/-- Helper for Theorem 5.4.7.9: the weighted log sum has derivative given by the weighted relative
direction coordinates. -/
private theorem lineDeriv_weighted_sum_log_eq_sum_relativeDirection
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    lineDeriv ℝ (fun y : Eₙ ↦ ∑ i : Fin n, a i * Real.log (y i)) x h =
      ∑ i : Fin n, a i * δ[x](h) i := by
  have hsum :
      HasFDerivAt
        (fun y : Eₙ ↦ ∑ i : Fin n, a i * Real.log (y i))
        (∑ i : Fin n,
          a i •
            (((x : Eₙ) i)⁻¹ •
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)))
        (x : Eₙ) := by
    -- Differentiate the coordinate logs termwise and pull the simplex weights out as constants.
    have hterms :
        ∀ i ∈ (Finset.univ : Finset (Fin n)),
          HasFDerivAt
            (fun y : Eₙ ↦ a i * Real.log (y i))
            (a i •
              (((x : Eₙ) i)⁻¹ •
                (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)))
            (x : Eₙ) := by
      intro i hi
      have happly :
          HasFDerivAt
            (fun y : Eₙ ↦ y i)
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)
            (x : Eₙ) := by
        simpa using PiLp.hasFDerivAt_apply (2 : ENNReal) (x : Eₙ) i
      have hlog :
          HasFDerivAt
            (fun y : Eₙ ↦ Real.log (y i))
            (((x : Eₙ) i)⁻¹ •
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ))
            (x : Eₙ) := by
        simpa using happly.log (ne_of_gt (x.2 i))
      simpa [smul_eq_mul] using hlog.const_mul (a i)
    convert HasFDerivAt.sum hterms using 1
    funext y
    simp
  have hline := hsum.hasLineDerivAt h
  -- Evaluate the resulting continuous linear map on the chosen direction `h`.
  rw [hline.lineDeriv]
  simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, relativeDirection_apply,
    div_eq_mul_inv, mul_assoc, mul_comm]

/-- Theorem 5.4.7.9: for `a ∈ Δₙ`, the directional derivative of `log ξ_a` at a strictly positive
point `x` along the ambient direction `h`, taken within the positive orthant, is the
simplex-weighted mean `Finset.univ.centerMass a (δ_x(h)) = ⟪a, δ_x(h)⟫`. -/
theorem lineDerivWithin_log_monomialXi_eq_centerMass_relativeDirection
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    lineDerivWithin ℝ (Real.log ∘ ambientMonomialXi a) Xₙ x h =
      Finset.univ.centerMass a (δ[x](h)) := by
  -- First replace `log ξ_a` on the orthant by the weighted sum of coordinate logs.
  have hrewrite :
      Set.EqOn
        (Real.log ∘ ambientMonomialXi a)
        (fun y : Eₙ ↦ ∑ i : Fin n, a i * Real.log (y i))
        (Xₙ : Set Eₙ) := by
    intro y hy
    simpa using log_ambientMonomialXi_eq_weighted_sum_log a hy
  calc
    lineDerivWithin ℝ (Real.log ∘ ambientMonomialXi a) Xₙ x h
      = lineDerivWithin ℝ (fun y : Eₙ ↦ ∑ i : Fin n, a i * Real.log (y i)) Xₙ x h := by
          rw [lineDerivWithin_congr' hrewrite x.2]
    _ = lineDeriv ℝ (fun y : Eₙ ↦ ∑ i : Fin n, a i * Real.log (y i)) x h := by
          -- On the open orthant, the within-derivative is the ordinary line derivative.
          rw [lineDerivWithin_of_isOpen positiveOrthant_isOpen x.2]
    _ = ∑ i : Fin n, a i * δ[x](h) i := by
          rw [lineDeriv_weighted_sum_log_eq_sum_relativeDirection]
    _ = Finset.univ.centerMass a (δ[x](h)) := by
          -- The simplex weights sum to `1`, so the weighted sum is exactly the center of mass.
          symm
          simpa [smul_eq_mul] using
            (show Finset.univ.centerMass a (δ[x](h)) =
                ∑ i : Fin n, a i • δ[x](h) i from
              Finset.univ.centerMass_eq_of_sum_1 (δ[x](h)) (stdSimplex.sum_eq_one a))

end
