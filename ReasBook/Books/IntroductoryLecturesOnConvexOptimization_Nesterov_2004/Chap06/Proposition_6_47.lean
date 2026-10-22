/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_25
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_61

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators ConvexAnalysis Gradient WeightSequenceNotation

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/- Proposition 6.47 lies in the Chapter 6 accuracy-certificate / averaged-dual domain.

Mandatory domain-style sampling before refinement:
- `Finset.centerMass` and `ConvexOn.map_centerMass_le`, the canonical owners for normalized finite
  weighted averages and Jensen's inequality on those averages;
- `A[a](t)` in `Chap06/Definition_6_53`, the chapter owner for accumulated weights;
- `localModelAccuracyCertificate` in `Chap06/Definition_6_61`, the source-facing owner `ℓ_t`;
- `smoothedDualObjective` in `Chap06/Proposition_6_25`, whose zero-smoothing specialization is the
  chapter owner for the dual objective `ν ↦ inf_{x ∈ Q} (ψ(x) + A x ν) - g(ν)`;
- `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the canonical bridge from the
  `EReal`-valued dual objective to its displayed real-valued form.

Best owner abstraction:
- source-facing: Proposition 6.47's certificate `ℓ_t`, averaged dual point `ν_t`, and final
  primal-dual gap estimate;
- core/canonical: `localModelAccuracyCertificate`, `A[a](t)`, and the zero-smoothing
  `smoothedDualObjective`;
- bridge/view: the `Finset.centerMass` realization of `ν_t` and the center-mass scalar correction
  term for the sampled dual values.

Primitive data:
- the feasible set `Q`, the regularizer `ψ`, the iterate sequence `xSeq`, and the weights `a`;
- the dual representation data `A`, `g`, and `u`;
- the dualized local-linearization hypothesis along the sampled iterates.

Derived API:
- the canonical certificate value `localModelAccuracyCertificate Q f ψ xSeq a t`;
- the averaged dual point
  `ν_t = (Finset.range (t + 1)).centerMass a (fun k ↦ u (x_k))`;
- the Chapter 6 dual objective
  `extendedRealRealPart (smoothedDualObjective A Q (Function.extend Subtype.val ψ 0) g 0 0)`;
- the scalar center-mass correction term
  `(Finset.range (t + 1)).centerMass a (fun k ↦ g (u (x_k)))`.

Source/core/bridge triage:
- source-facing: the proposition below;
- core/canonical: `localModelAccuracyCertificate` and `smoothedDualObjective`;
- bridge/view: the normalized finite weighted sum defining `ν_t`.

The previous version rebuilt a raw normalized-sum dual iterate and packaged the final result as
one large conjunction. This refinement deletes that duplicate weighted-average surface, exposes
the averaged dual point through `Finset.centerMass`, removes the now-redundant explicit
average-membership hypothesis, and restores the main source-facing conclusion as an
upper-gap theorem plus an interval-valued companion whose left endpoint is supplied internally by
the chapter weak-duality comparison for the zero-smoothing dual objective.
-/

/-- Helper for Proposition 6.47: the scalar center mass of the sampled dual slice
`k ↦ A x (u (x_k)) - g (u (x_k))` splits into the dual slice at the averaged dual point and the
center mass of the sampled `g` values. -/
lemma centerMassDualSliceSub_eq_dualAverage_sub_centerMass
    (Q : Set E) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ F) (g : F → ℝ) (u : E → F) (t : ℕ)
    (x : Q) :
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    let gAvg := (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E)))
    (Finset.range (t + 1)).centerMass a
      (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E))) =
      A (x : E) νt - gAvg := by
  dsimp
  -- Normalize the scalar-valued center masses to the same denominator.
  have hmap :
      A (x : E) ((Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))) =
        (Finset.range (t + 1)).centerMass a (fun k ↦ A (x : E) (u (xSeq k : E))) := by
    rw [Finset.centerMass, Finset.centerMass]
    -- The dual pairing `A (x : E)` is linear in the averaged dual point.
    simp [map_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  calc
    (Finset.range (t + 1)).centerMass a
        (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))
      =
        (Finset.range (t + 1)).centerMass a (fun k ↦ A (x : E) (u (xSeq k : E))) -
          (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E))) := by
            -- Split the scalar center mass into its `A` and `g` pieces.
            rw [Finset.centerMass, Finset.centerMass, Finset.centerMass]
            simp_rw [smul_eq_mul, mul_sub]
            rw [Finset.sum_sub_distrib]
            ring
    _ = A (x : E) ((Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))) -
          (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E))) := by
            rw [← hmap]

/-- Helper for Proposition 6.47: the zero-smoothing primal minimand image is exactly the explicit
dual slice `x ↦ ψ x + A x ν` on the feasible subtype `Q`. -/
lemma smoothedDualObjectiveMinimand_zero_image_eq_dualSliceRange
    (Q : Set E) (ψ : Q → ℝ) (A : E →L[ℝ] StrongDual ℝ F) (ν : F) :
    smoothedDualObjectiveMinimand
        A
        (Function.extend Subtype.val ψ 0)
        (fun _ : E ↦ 0)
        0
        ν '' Q =
      Set.range (fun x : Q ↦ ψ x + A (x : E) ν) := by
  ext z
  constructor
  · rintro ⟨x, hxQ, rfl⟩
    refine ⟨⟨x, hxQ⟩, ?_⟩
    -- On feasible points, `Function.extend Subtype.val ψ 0` reduces to `ψ`.
    rw [smoothedDualObjectiveMinimand_apply, Function.extend_val_apply hxQ]
    simpa [add_comm]
  · rintro ⟨x, rfl⟩
    refine ⟨x, x.property, ?_⟩
    -- Repackage the subtype witness back into the ambient image.
    rw [smoothedDualObjectiveMinimand_apply, Function.extend_val_apply x.property]
    simpa [add_comm]

lemma accuracy_certificate_local_model_eq_dual_average_model
    (Q : Set E) (f : E → ℝ) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ F) (g : F → ℝ) (u : E → F) (t : ℕ)
    (hlocal :
      ∀ (k : ℕ) (x : Q),
        f (xSeq k) + inner ℝ (∇ f (xSeq k : E)) ((x : E) - (xSeq k : E)) =
          A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))
    (hAt : 0 < A[a](t))
    (x : Q) :
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    let gAvg := (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E)))
    accuracyCertificateLocalModel Q f ψ xSeq a t x =
      A[a](t) * (ψ x + A (x : E) νt - gAvg) :=
by
  dsimp
  have hdualSlice :
      (Finset.range (t + 1)).centerMass a
          (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E))) =
        A (x : E) ((Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))) -
          (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E))) := by
    simpa using
      centerMassDualSliceSub_eq_dualAverage_sub_centerMass Q xSeq a A g u t x
  have hsum_center :
      Finset.sum (Finset.range (t + 1))
          (fun k ↦ a k * (A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))) =
        A[a](t) *
          (Finset.range (t + 1)).centerMass a
            (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E))) := by
    -- Recover the unnormalized weighted sum from the scalar center mass.
    rw [Finset.centerMass, accumulatedWeights_apply]
    simp_rw [smul_eq_mul, mul_sub]
    have hsum_ne : ∑ x ∈ Finset.range (t + 1), a x ≠ 0 := by
      simpa [accumulatedWeights_apply] using hAt.ne'
    calc
      ∑ x_1 ∈ Finset.range (t + 1),
          (a x_1 * (A (x : E)) (u (xSeq x_1 : E)) - a x_1 * g (u (xSeq x_1 : E)))
        = (∑ x_1 ∈ Finset.range (t + 1),
            (a x_1 * (A (x : E)) (u (xSeq x_1 : E)) - a x_1 * g (u (xSeq x_1 : E)))) * 1 := by
              ring
      _ =
          (∑ x_1 ∈ Finset.range (t + 1),
              (a x_1 * (A (x : E)) (u (xSeq x_1 : E)) - a x_1 * g (u (xSeq x_1 : E)))) *
            ((∑ x ∈ Finset.range (t + 1), a x) * (∑ x ∈ Finset.range (t + 1), a x)⁻¹) := by
              rw [mul_inv_cancel₀ hsum_ne]
      _ =
          (∑ x ∈ Finset.range (t + 1), a x) *
            ((∑ x ∈ Finset.range (t + 1), a x)⁻¹ *
              ∑ x_1 ∈ Finset.range (t + 1),
                (a x_1 * (A (x : E)) (u (xSeq x_1 : E)) - a x_1 * g (u (xSeq x_1 : E)))) := by
              ring
  have hψ_sum :
      Finset.sum (Finset.range (t + 1)) (fun k ↦ ψ x * a k) = ψ x * A[a](t) := by
    rw [← Finset.mul_sum]
    simp [accumulatedWeights_apply]
  -- Rewrite the local model through the sampled dual slice, then factor the constant `ψ x`.
  rw [accuracyCertificateLocalModel_apply]
  simp_rw [hlocal]
  calc
    Finset.sum (Finset.range (t + 1))
        (fun k ↦ a k * (A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)) + ψ x))
      =
        Finset.sum (Finset.range (t + 1))
          (fun k ↦ a k * (A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))) +
          ψ x * A[a](t) := by
            -- Separate the constant regularizer term from the sampled dual slice.
            calc
              ∑ k ∈ Finset.range (t + 1),
                  a k * (A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)) + ψ x)
                =
                  ∑ k ∈ Finset.range (t + 1),
                    (a k * (A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E))) +
                      ψ x * a k) := by
                        refine Finset.sum_congr rfl ?_
                        intro k hk
                        ring
              _ =
                  ∑ k ∈ Finset.range (t + 1),
                    a k * (A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E))) +
                    ψ x * A[a](t) := by
                        rw [Finset.sum_add_distrib, hψ_sum]
    _ =
        A[a](t) *
          (Finset.range (t + 1)).centerMass a
            (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E))) +
          ψ x * A[a](t) := by rw [hsum_center]
    _ =
        A[a](t) *
          (A (x : E) ((Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))) -
            (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E)))) +
          ψ x * A[a](t) := by
            rw [hdualSlice]
    _ = A[a](t) *
          (ψ x + A (x : E) ((Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))) -
            (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E)))) := by
            ring

/-- Helper for the averaged-dual gap item: after dividing by the positive accumulated weight, the
infimum of
the scaled-and-shifted dual model is exactly the infimum of the unscaled dual slice minus the
scalar correction. -/
lemma sInf_scaled_shifted_dual_model_div_eq
    (Q : Set E) (hq_nonempty : Q.Nonempty) (a : ℕ → ℝ) (t : ℕ) (hAt : 0 < A[a](t))
    (h : Q → ℝ) (hh_bddBelow : BddBelow (Set.range h)) (c : ℝ) :
    sInf (Set.range fun x : Q ↦ A[a](t) * (h x - c)) / A[a](t) =
      sInf (Set.range h) - c :=
by
  have hrange_nonempty : (Set.range h).Nonempty := by
    rcases hq_nonempty with ⟨x, hxQ⟩
    exact ⟨h ⟨x, hxQ⟩, ⟨⟨x, hxQ⟩, rfl⟩⟩
  have hshift_range :
      Set.range (fun x : Q ↦ h x - c) = (fun z : ℝ ↦ z - c) '' Set.range h := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨h x, ⟨x, rfl⟩, by simp⟩
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  have hscaled_range :
      Set.range (fun x : Q ↦ A[a](t) * (h x - c)) =
        (fun z : ℝ ↦ A[a](t) * z) '' Set.range (fun x : Q ↦ h x - c) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨h x - c, ⟨x, rfl⟩, by simp [smul_eq_mul, mul_comm]⟩
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, by simp [smul_eq_mul, mul_comm]⟩
  have hshift_nonempty : ((fun z : ℝ ↦ z - c) '' Set.range h).Nonempty := by
    rcases hrange_nonempty with ⟨y, hy⟩
    exact ⟨y - c, ⟨y, hy, rfl⟩⟩
  have hshift_bddBelow : BddBelow ((fun z : ℝ ↦ z - c) '' Set.range h) := by
    rcases hh_bddBelow with ⟨m, hm⟩
    refine ⟨m - c, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact sub_le_sub_right (hm hy) c
  have hshift :
      sInf (Set.range (fun x : Q ↦ h x - c)) = sInf (Set.range h) - c := by
    rw [hshift_range]
    -- Move the infimum through the additive order isomorphism `z ↦ z - c`.
    simpa [sub_eq_add_neg] using
      ((OrderIso.addRight (-c)).map_csInf' hrange_nonempty hh_bddBelow).symm
  calc
    sInf (Set.range fun x : Q ↦ A[a](t) * (h x - c)) / A[a](t)
      = sInf ((fun z : ℝ ↦ A[a](t) * z) '' Set.range (fun x : Q ↦ h x - c)) / A[a](t) := by
          rw [hscaled_range]
    _ = (A[a](t) * sInf (Set.range (fun x : Q ↦ h x - c))) / A[a](t) := by
          rw [hshift_range]
          simpa using
            congrArg (fun r : ℝ => r / A[a](t))
              ((OrderIso.mulLeft₀ (A[a](t)) hAt).map_csInf'
                hshift_nonempty
                hshift_bddBelow).symm
    _ = sInf (Set.range (fun x : Q ↦ h x - c)) := by
          exact mul_div_cancel_left₀ (sInf (Set.range (fun x : Q ↦ h x - c))) hAt.ne'
    _ = sInf (Set.range h) - c := hshift

/-- If the affine models entering the Chapter 6 certificate `ℓ_t` can be rewritten through the
selected dual values `u(x_k)` and the accumulated weight `A_t = A[a](t)` is positive, then `ℓ_t`
equals the zero-smoothing dual objective at the center-mass dual average, corrected by the
center mass of the sampled dual values `g(u(x_k))`. -/
-- Proof sketch: unfold `localModelAccuracyCertificate`, rewrite the weighted affine models with
-- `hlocal`, and identify the resulting normalized finite sum with the zero-smoothing dual
-- objective evaluated at the center-mass dual average.
theorem localModelAccuracyCertificate_eq_dual_average_correction
    (Q : Set E) (f : E → ℝ) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ F) (g : F → ℝ) (u : E → F) (t : ℕ)
    (hlocal :
      ∀ (k : ℕ) (x : Q),
        f (xSeq k) + inner ℝ (∇ f (xSeq k : E)) ((x : E) - (xSeq k : E)) =
          A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))
    (hAt : 0 < A[a](t))
    (hdualSlice_bddBelow :
      BddBelow
        (Set.range fun x : Q ↦
          ψ x + A (x : E) ((Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))))) :
    let dualObj :=
      extendedRealRealPart
        (smoothedDualObjective
          A
          Q
          (Function.extend Subtype.val ψ 0)
          g
          (fun _ : E ↦ 0)
          0)
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    localModelAccuracyCertificate Q f ψ xSeq a t =
      dualObj νt + g νt -
        (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E))) :=
by
  dsimp
  let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
  let gAvg := (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E)))
  have hq_nonempty : Q.Nonempty := ⟨xSeq 0, (xSeq 0).property⟩
  have hmodel_range :
      Set.range (accuracyCertificateLocalModel Q f ψ xSeq a t) =
        Set.range (fun x : Q ↦ A[a](t) * ((ψ x + A (x : E) νt) - gAvg)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      -- Rewrite the local model through the averaged dual slice.
      simpa [νt, gAvg, sub_eq_add_neg, add_assoc] using
        (accuracy_certificate_local_model_eq_dual_average_model
          Q f ψ xSeq a A g u t hlocal hAt x).symm
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      simpa [νt, gAvg, sub_eq_add_neg, add_assoc] using
        accuracy_certificate_local_model_eq_dual_average_model
          Q f ψ xSeq a A g u t hlocal hAt x
  have hsInf_eq :
      sInf (Set.range (accuracyCertificateLocalModel Q f ψ xSeq a t)) / A[a](t) =
        sInf (Set.range fun x : Q ↦ ψ x + A (x : E) νt) - gAvg := by
    -- Transport the certificate infimum to the normalized dual slice.
    rw [hmodel_range]
    simpa [νt, gAvg] using
      sInf_scaled_shifted_dual_model_div_eq
        Q
        hq_nonempty
        a
        t
        hAt
        (fun x : Q ↦ ψ x + A (x : E) νt)
        hdualSlice_bddBelow
        gAvg
  have hdualObj :
      extendedRealRealPart
          (smoothedDualObjective
            A
            Q
            (Function.extend Subtype.val ψ 0)
            g
            (fun _ : E ↦ 0)
            0) νt =
        sInf (Set.range fun x : Q ↦ ψ x + A (x : E) νt) - g νt := by
    -- Identify the zero-smoothing owner with the same explicit dual slice.
    rw [extendedRealRealPart_eq_toReal, smoothedDualObjective_apply,
      smoothedDualObjectiveMinimand_zero_image_eq_dualSliceRange]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (EReal.toReal_coe
        (-g νt + sInf (Set.range fun x : Q ↦ ψ x + A (x : E) νt)))
  -- Assemble the normalized infimum identity with the zero-smoothing dual objective formula.
  rw [localModelAccuracyCertificate_def]
  calc
    sInf (Set.range (accuracyCertificateLocalModel Q f ψ xSeq a t)) / A[a](t)
      = sInf (Set.range fun x : Q ↦ ψ x + A (x : E) νt) - gAvg := hsInf_eq
    _ =
        extendedRealRealPart
            (smoothedDualObjective
              A
              Q
              (Function.extend Subtype.val ψ 0)
              g
              (fun _ : E ↦ 0)
              0) νt +
          g νt - gAvg := by
            rw [hdualObj]
            ring

/-- Under the convexity of the sampled dual term `g` on the feasible dual set `U`, the
center-mass formula for `ℓ_t` yields the lower bound `ℓ_t ≤ \bar g(ν_t)` at the averaged dual
point `ν_t = (Finset.range (t + 1)).centerMass a (fun k ↦ u (x_k))`. -/
-- Proof sketch: combine
-- `localModelAccuracyCertificate_eq_dual_average_correction` with Jensen's inequality in the
-- `Finset.centerMass` form for `g` on `U`.
theorem localModelAccuracyCertificate_le_dualObjective_of_dual_average
    (Q : Set E) (f : E → ℝ) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ F) (g : F → ℝ) (u : E → F) (U : Set F) (t : ℕ)
    (hlocal :
      ∀ (k : ℕ) (x : Q),
        f (xSeq k) + inner ℝ (∇ f (xSeq k : E)) ((x : E) - (xSeq k : E)) =
          A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))
    (ha_nonneg : ∀ k ∈ Finset.range (t + 1), 0 ≤ a k)
    (hAt : 0 < A[a](t))
    (hdualSlice_bddBelow :
      BddBelow
        (Set.range fun x : Q ↦
          ψ x + A (x : E) ((Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E)))))
    (hu_mapsTo : Set.MapsTo u Q U)
    (hg_convex : ConvexOn ℝ U g) :
    let dualObj :=
      extendedRealRealPart
        (smoothedDualObjective
          A
          Q
          (Function.extend Subtype.val ψ 0)
          g
          (fun _ : E ↦ 0)
          0)
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    localModelAccuracyCertificate Q f ψ xSeq a t ≤ dualObj νt := by
  -- Rewrite `ℓ_t` as the dual objective plus the Jensen correction term.
  dsimp
  let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
  let gAvg := (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E)))
  have heq :
      localModelAccuracyCertificate Q f ψ xSeq a t =
        extendedRealRealPart
            (smoothedDualObjective
              A
              Q
              (Function.extend Subtype.val ψ 0)
              g
              (fun _ : E ↦ 0)
              0) νt +
          g νt - gAvg := by
    simpa [νt, gAvg] using
      localModelAccuracyCertificate_eq_dual_average_correction
        Q f ψ xSeq a A g u t hlocal hAt hdualSlice_bddBelow
  have hu_mem :
      ∀ k ∈ Finset.range (t + 1), u (xSeq k : E) ∈ U := by
    intro k hk
    exact hu_mapsTo (xSeq k).property
  have hsum_pos : 0 < ∑ k ∈ Finset.range (t + 1), a k := by
    simpa [accumulatedWeights_apply] using hAt
  have hjensen : g νt ≤ gAvg := by
    simpa [νt, gAvg] using hg_convex.map_centerMass_le ha_nonneg hsum_pos hu_mem
  calc
    localModelAccuracyCertificate Q f ψ xSeq a t =
        extendedRealRealPart
            (smoothedDualObjective
              A
              Q
              (Function.extend Subtype.val ψ 0)
              g
              (fun _ : E ↦ 0)
              0) νt +
          g νt - gAvg := heq
    _ ≤ extendedRealRealPart
          (smoothedDualObjective
            A
            Q
            (Function.extend Subtype.val ψ 0)
            g
            (fun _ : E ↦ 0)
            0) νt := by
          linarith

/-- Companion `sInf` theorem for the present averaged-dual gap item on the current finite-valued
Chapter 6 surface:
the explicit infimum model `ℓ_t` agrees with the zero-smoothing dual objective at the averaged
dual iterate `ν_t`, up to subtracting the averaged sampled `g` values, and therefore satisfies
`ℓ_t ≤ \bar g(ν_t)`. -/
-- Proof sketch: identify the source-facing `ℓ_t` with the center-mass reformulation of the dual
-- slice, then use Jensen's inequality in the `ConvexOn.map_centerMass_le` form to compare the
-- averaged sampled `g` values to `g(ν_t)`.
theorem localModelAccuracyCertificate_gap_upper_bound_of_dual_average
    (Q : Set E) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ F) (g : F → ℝ) (u : E → F) (U : Set F) (t : ℕ)
    (ha_nonneg : ∀ k ∈ Finset.range (t + 1), 0 ≤ a k)
    (hAt : 0 < A[a](t))
    (hdualSlice_bddBelow :
      BddBelow
        (Set.range fun x : Q ↦
          ψ x + A (x : E) ((Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E)))))
    (hu_mapsTo : Set.MapsTo u Q U)
    (hg_convex : ConvexOn ℝ U g) :
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    let ellt : ℝ :=
      sInf
        (Set.range fun x : Q ↦
          ψ x +
            (Finset.range (t + 1)).centerMass a
              (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E))))
    let barG : F → ℝ :=
      extendedRealRealPart
        (smoothedDualObjective
          A
          Q
          (Function.extend Subtype.val ψ 0)
          g
          (fun _ : E ↦ 0)
          0)
    ellt =
        barG νt + g νt -
          (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E))) ∧
      ellt ≤ barG νt :=
by
  dsimp
  let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
  let gAvg := (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E)))
  let barG : F → ℝ :=
    extendedRealRealPart
      (smoothedDualObjective
        A
        Q
        (Function.extend Subtype.val ψ 0)
        g
        (fun _ : E ↦ 0)
        0)
  have hq_nonempty : Q.Nonempty := ⟨xSeq 0, (xSeq 0).property⟩
  have hellt_eq :
      sInf
          (Set.range fun x : Q ↦
            ψ x +
              (Finset.range (t + 1)).centerMass a
                (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))) =
        barG νt + g νt - gAvg := by
    have hslice_range :
        Set.range
            (fun x : Q ↦
              ψ x +
                (Finset.range (t + 1)).centerMass a
                  (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))) =
          Set.range (fun x : Q ↦ (ψ x + A (x : E) νt) - gAvg) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨x, ?_⟩
        -- Rewrite the center-mass correction through the averaged dual point.
        simpa [νt, gAvg, sub_eq_add_neg, add_assoc] using
          congrArg (fun z : ℝ => ψ x + z)
            (centerMassDualSliceSub_eq_dualAverage_sub_centerMass Q xSeq a A g u t x).symm
      · rintro ⟨x, rfl⟩
        refine ⟨x, ?_⟩
        simpa [νt, gAvg, sub_eq_add_neg, add_assoc] using
          congrArg (fun z : ℝ => ψ x + z)
            (centerMassDualSliceSub_eq_dualAverage_sub_centerMass Q xSeq a A g u t x)
    have hshift_range :
        Set.range (fun x : Q ↦ (ψ x + A (x : E) νt) - gAvg) =
          (fun z : ℝ ↦ z - gAvg) '' Set.range (fun x : Q ↦ ψ x + A (x : E) νt) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨ψ x + A (x : E) νt, ⟨x, rfl⟩, by simp⟩
      · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    have hshift :
        sInf (Set.range (fun x : Q ↦ (ψ x + A (x : E) νt) - gAvg)) =
          sInf (Set.range (fun x : Q ↦ ψ x + A (x : E) νt)) - gAvg := by
      rw [hshift_range]
      -- Transport the infimum through the constant subtraction `z ↦ z - gAvg`.
      simpa [sub_eq_add_neg] using
        ((OrderIso.addRight (-gAvg)).map_csInf'
          (by
            rcases hq_nonempty with ⟨x, hxQ⟩
            exact ⟨ψ ⟨x, hxQ⟩ + A (x : E) νt, ⟨⟨x, hxQ⟩, rfl⟩⟩)
          hdualSlice_bddBelow).symm
    have hdualObj :
        barG νt = sInf (Set.range (fun x : Q ↦ ψ x + A (x : E) νt)) - g νt := by
      -- Identify `barG νt` with the same zero-smoothing dual slice.
      change
        extendedRealRealPart
            (smoothedDualObjective
              A
              Q
              (Function.extend Subtype.val ψ 0)
              g
              (fun _ : E ↦ 0)
              0) νt =
          sInf (Set.range (fun x : Q ↦ ψ x + A (x : E) νt)) - g νt
      rw [extendedRealRealPart_eq_toReal, smoothedDualObjective_apply,
        smoothedDualObjectiveMinimand_zero_image_eq_dualSliceRange]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (EReal.toReal_coe
          (-g νt + sInf (Set.range fun x : Q ↦ ψ x + A (x : E) νt)))
    calc
      sInf
          (Set.range fun x : Q ↦
            ψ x +
              (Finset.range (t + 1)).centerMass a
                (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E))))
        =
          sInf (Set.range (fun x : Q ↦ (ψ x + A (x : E) νt) - gAvg)) := by
            rw [hslice_range]
      _ = sInf (Set.range (fun x : Q ↦ ψ x + A (x : E) νt)) - gAvg := hshift
      _ = barG νt + g νt - gAvg := by
            rw [hdualObj]
            ring
  have hu_mem :
      ∀ k ∈ Finset.range (t + 1), u (xSeq k : E) ∈ U := by
    intro k hk
    exact hu_mapsTo (xSeq k).property
  have hsum_pos : 0 < ∑ k ∈ Finset.range (t + 1), a k := by
    simpa [accumulatedWeights_apply] using hAt
  have hjensen : g νt ≤ gAvg := by
    -- Jensen controls the sampled `g` correction by the value at the averaged dual point.
    simpa [νt, gAvg] using hg_convex.map_centerMass_le ha_nonneg hsum_pos hu_mem
  constructor
  · exact hellt_eq
  · calc
      sInf
          (Set.range fun x : Q ↦
            ψ x +
              (Finset.range (t + 1)).centerMass a
                (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E))))
        = barG νt + g νt - gAvg := hellt_eq
      _ ≤ barG νt := by
            linarith

/-- Companion `sInf` consequence for the present averaged-dual gap item on the current
finite-valued Chapter 6
surface: if the explicit infimum certificate `ℓ_t` satisfies
`\bar f(x_t) - ℓ_t ≤ B_{v,t} / A_t` and the source's weak-duality comparison
`\bar g(ν_t) ≤ \bar f(x_t)` holds at the averaged dual iterate, then the same interval bound
holds for the explicit zero-smoothing dual objective `\bar g(ν_t)`. -/
-- Proof sketch: combine the source-facing identity and lower bound from
-- `localModelAccuracyCertificate_gap_upper_bound_of_dual_average` with the assumed certificate-gap
-- estimate and the explicit weak-duality comparison.
theorem localModelAccuracyCertificate_gap_bound_of_dual_average
    (Q : Set E) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ F) (g : F → ℝ) (u : E → F) (U : Set F) (t : ℕ)
    (Bvt : ℝ)
    (ha_nonneg : ∀ k ∈ Finset.range (t + 1), 0 ≤ a k)
    (hAt : 0 < A[a](t))
    (hdualSlice_bddBelow :
      BddBelow
        (Set.range fun x : Q ↦
          ψ x + A (x : E) ((Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E)))))
    (hu_mapsTo : Set.MapsTo u Q U)
    (hg_convex : ConvexOn ℝ U g)
    (hcertificate :
      let ellt : ℝ :=
        sInf
          (Set.range fun x : Q ↦
            ψ x +
              (Finset.range (t + 1)).centerMass a
                (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E))))
      let barf : Q → ℝ := fun x ↦ ψ x + g (u x)
      barf (xSeq t) - ellt ≤ Bvt / A[a](t))
    (hweak :
      let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
      let barG : F → ℝ :=
        extendedRealRealPart
          (smoothedDualObjective
            A
            Q
            (Function.extend Subtype.val ψ 0)
            g
            (fun _ : E ↦ 0)
            0)
      let barf : Q → ℝ := fun x ↦ ψ x + g (u x)
      barG νt ≤ barf (xSeq t)) :
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    let barG : F → ℝ :=
      extendedRealRealPart
        (smoothedDualObjective
          A
          Q
          (Function.extend Subtype.val ψ 0)
          g
          (fun _ : E ↦ 0)
          0)
    let barf : Q → ℝ := fun x ↦ ψ x + g (u x)
    barf (xSeq t) - barG νt ∈ Set.Icc 0 (Bvt / A[a](t)) := by
  -- Package the explicit `sInf` upper bound together with the assumed certificate estimate.
  dsimp at hcertificate hweak ⊢
  rcases
      localModelAccuracyCertificate_gap_upper_bound_of_dual_average
        Q ψ xSeq a A g u U t ha_nonneg hAt hdualSlice_bddBelow hu_mapsTo hg_convex
    with ⟨hellt_eq, hellt_le⟩
  constructor
  · exact sub_nonneg.mpr hweak
  ·
    have hsub :
        (ψ (xSeq t) + g (u (xSeq t : E))) -
            extendedRealRealPart
              (smoothedDualObjective
                A
                Q
                (Function.extend Subtype.val ψ 0)
                g
                (fun _ : E ↦ 0)
                0) ((Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))) ≤
          (ψ (xSeq t) + g (u (xSeq t : E))) -
            sInf
              (Set.range fun x : Q ↦
                ψ x +
                  (Finset.range (t + 1)).centerMass a
                    (fun k ↦ A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))) := by
      exact sub_le_sub_left hellt_le _
    exact le_trans hsub hcertificate

/-- Proposition 6.47 [Duality-gap bound for averaged dual iterate (method 1)].

For the present finite-valued Chapter 6 surface, the book's minima are formalized by the real
infima
`Φ(ν) = sInf (Set.range fun x : Q ↦ ψ x + A (x : E) ν)`.
The bounded-below hypothesis on the dual slice at the averaged dual iterate `ν_t` is therefore
kept explicit, and the companion theorems
`localModelAccuracyCertificate_gap_upper_bound_of_dual_average` and
`localModelAccuracyCertificate_gap_bound_of_dual_average`
record the corresponding explicit `sInf` / zero-smoothing formulas.
On this finite-valued surface the source's weak-duality comparison `\bar g(ν_t) ≤ \bar f(x_t)` is
also kept explicit. Under that comparison and the certificate bound
`\bar f(x_t) - ℓ_t ≤ B_{v,t} / A_t`, the averaged dual iterate `ν_t` satisfies
`0 ≤ \bar f(x_t) - \bar g(ν_t) ≤ B_{v,t} / A_t`. -/
-- Proof sketch: instantiate the source notation
-- `Φ(ν) = inf_{x ∈ Q} (ψ(x) + ⟪A x, ν⟫)`,
-- `\bar g(ν) = Φ(ν) - g(ν)`, and
-- `ℓ_t = Φ(ν_t) - (1 / A_t) ∑_{k=0}^t a_k g(u(x_k))`,
-- then combine the previous companion theorem with the assumed certificate estimate and
-- weak-duality comparison.
theorem proposition_6_47_dualityGapBoundForAveragedDualIterate
    (Q : Set E) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ F) (g : F → ℝ) (u : E → F) (U : Set F) (t : ℕ)
    (Bvt : ℝ)
    (ha_nonneg : ∀ k ∈ Finset.range (t + 1), 0 ≤ a k)
    (hAt : 0 < A[a](t))
    (hdualSlice_bddBelow :
      BddBelow
        (Set.range fun x : Q ↦
          ψ x + A (x : E) ((Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E)))))
    (hu_mapsTo : Set.MapsTo u Q U)
    (hg_convex : ConvexOn ℝ U g)
    (hcertificate :
      let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
      let Φ : F → ℝ :=
        fun ν ↦
          sInf (Set.range fun x : Q ↦ ψ x + A (x : E) ν)
      let ellt : ℝ :=
        Φ νt -
          (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E)))
      let barf : Q → ℝ := fun x ↦ ψ x + g (u x)
      barf (xSeq t) - ellt ≤ Bvt / A[a](t))
    (hweak :
      let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
      let Φ : F → ℝ :=
        fun ν ↦
          sInf (Set.range fun x : Q ↦ ψ x + A (x : E) ν)
      let barG : F → ℝ := fun ν ↦ Φ ν - g ν
      let barf : Q → ℝ := fun x ↦ ψ x + g (u x)
      barG νt ≤ barf (xSeq t)) :
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    let Φ : F → ℝ :=
      fun ν ↦
          sInf (Set.range fun x : Q ↦ ψ x + A (x : E) ν)
    let barG : F → ℝ := fun ν ↦ Φ ν - g ν
    let barf : Q → ℝ := fun x ↦ ψ x + g (u x)
    barf (xSeq t) - barG νt ∈ Set.Icc 0 (Bvt / A[a](t)) := by
  -- Package the source-facing `Φ(ν_t) - g(ν_t)` gap directly from the assumed bounds.
  dsimp at hcertificate hweak ⊢
  constructor
  · exact sub_nonneg.mpr hweak
  ·
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    let gAvg := (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E)))
    have hu_mem :
        ∀ k ∈ Finset.range (t + 1), u (xSeq k : E) ∈ U := by
      intro k hk
      exact hu_mapsTo (xSeq k).property
    have hsum_pos : 0 < ∑ k ∈ Finset.range (t + 1), a k := by
      simpa [accumulatedWeights_apply] using hAt
    have hjensen : g νt ≤ gAvg := by
      simpa [νt, gAvg] using hg_convex.map_centerMass_le ha_nonneg hsum_pos hu_mem
    have hellt_le_barG :
        sInf (Set.range fun x : Q ↦ ψ x + A (x : E) νt) - gAvg ≤
          sInf (Set.range fun x : Q ↦ ψ x + A (x : E) νt) - g νt := by
      linarith
    have hsub :
        (ψ (xSeq t) + g (u (xSeq t : E))) -
            (sInf (Set.range fun x : Q ↦ ψ x + A (x : E) νt) - g νt) ≤
          (ψ (xSeq t) + g (u (xSeq t : E))) -
            (sInf (Set.range fun x : Q ↦ ψ x + A (x : E) νt) - gAvg) := by
      exact sub_le_sub_left hellt_le_barG _
    exact le_trans hsub hcertificate

end
