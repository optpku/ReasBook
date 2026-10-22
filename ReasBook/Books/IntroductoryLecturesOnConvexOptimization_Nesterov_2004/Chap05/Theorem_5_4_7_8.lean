/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm RelativeDirection
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n
noncomputable local instance instFintypeFinTheorem5478 : Fintype (Fin n) :=
  Fintype.ofFinite (Fin n)

/- Theorem 5.4.7.8 lies in the Chapter 5 positive-orthant barrier / Hessian-local-norm domain.

Sampled owner declarations:
* `standardLogarithmicBarrierAmbient` in `Definition_5_4_3_2`, the ambient bridge for the
  positive-orthant logarithmic barrier;
* `relativeDirection` in `Definition_5_4_7_14`, the source-facing scaled direction `δ_x(h)`;
* `hessianLocalNorm` and the notation `‖h‖[f; x]` in `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `hessianLocalNorm_def` in `Definition_5_1_1`, the bridge expanding that owner to the raw square
  root of the Hessian quadratic form.

Source/core/bridge triage:
* source-facing: the local norm of the orthant logarithmic barrier at `x` applied to `h`;
* core/canonical: `‖h‖[standardLogarithmicBarrierAmbient n; x]`;
* bridge/view: `hessianLocalNorm_def` together with the coordinate formula for
  `relativeDirection x h`.

The previous version kept the bridge formula
`Real.sqrt (inner ℝ h ((fderiv ℝ (∇ F) x) h))` as the main theorem surface. This refinement keeps
the same mathematics, but moves the statement to the chapter owner `hessianLocalNorm`; the raw
Hessian square root is already canonical derived API via `hessianLocalNorm_def`. -/

private theorem standardLogarithmicBarrierAmbient_hasGradientAt_of_nonzero
    (x : Eₙ) (hx : ∀ i : Fin n, x i ≠ 0) :
    HasGradientAt
      (standardLogarithmicBarrierAmbient n)
      (WithLp.toLp 2 fun i ↦ -(x i)⁻¹)
      x := by
  unfold standardLogarithmicBarrierAmbient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hsum :
      HasFDerivAt
        (fun y : Eₙ ↦ ∑ i : Fin n, Real.log (y i))
        (∑ i : Fin n,
          ((x i)⁻¹ : ℝ) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ))
        x := by
    have hterms :
        ∀ i ∈ (Finset.univ : Finset (Fin n)),
          HasFDerivAt
            (fun y : Eₙ ↦ Real.log (y i))
            (((x i)⁻¹ : ℝ) •
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ))
            x := by
      intro i hi
      simpa using ((PiLp.hasFDerivAt_apply (2 : ENNReal) x i).log (hx i))
    convert HasFDerivAt.sum hterms using 1
    funext y
    simp
  have hdual :
      (InnerProductSpace.toDual ℝ Eₙ) (WithLp.toLp 2 fun i ↦ -(x i)⁻¹) =
        -(∑ i : Fin n,
          ((x i)⁻¹ : ℝ) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)) := by
    ext h
    change inner ℝ (WithLp.toLp 2 fun i ↦ -(x i)⁻¹) h = _
    rw [PiLp.inner_apply]
    change (∑ i : Fin n, h i * (-(x i)⁻¹)) = _
    simp [ContinuousLinearMap.neg_apply, Finset.sum_apply, mul_comm]
  have hneg :
      HasFDerivAt
        (fun y : Eₙ ↦ -∑ i : Fin n, Real.log (y i))
        (-(∑ i : Fin n,
          ((x i)⁻¹ : ℝ) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)))
        x := by
    convert hsum.neg using 1
  exact hdual.symm ▸ hneg

private theorem standardLogarithmicBarrierAmbient_hasFDerivAt_gradient
    (x : Xₙ) :
    HasFDerivAt
      (∇ (standardLogarithmicBarrierAmbient n))
      ((
        PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)
      ).symm.toContinuousLinearMap.comp
        (show Eₙ →L[ℝ] (Fin n → ℝ) from
          ContinuousLinearMap.pi fun i : Fin n ↦
            ((((x : Eₙ) i) ^ (2 : ℕ))⁻¹ : ℝ) •
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)))
      (x : Eₙ) := by
  let G : Eₙ → Eₙ := fun y ↦ WithLp.toLp 2 fun i ↦ -(y i)⁻¹
  let H : Eₙ → Fin n → ℝ := fun y i ↦ -(y i)⁻¹
  let H' : Eₙ →L[ℝ] Fin n → ℝ :=
    show Eₙ →L[ℝ] (Fin n → ℝ) from
      ContinuousLinearMap.pi fun i : Fin n ↦
        ((((x : Eₙ) i) ^ (2 : ℕ))⁻¹ : ℝ) •
          (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)
  have hEq : ∇ (standardLogarithmicBarrierAmbient n) =ᶠ[nhds (x : Eₙ)] G := by
    have hpos : {y : Eₙ | ∀ i : Fin n, 0 < y i} ∈ nhds (x : Eₙ) := by
      have hopen : IsOpen {y : Eₙ | ∀ i : Fin n, 0 < y i} := by
        simpa [Set.setOf_forall] using
          (isOpen_iInter_of_finite fun i ↦
            isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i))
      exact hopen.mem_nhds x.2
    filter_upwards [hpos] with y hy
    exact
      (standardLogarithmicBarrierAmbient_hasGradientAt_of_nonzero
        y
        fun i ↦ ne_of_gt (hy i)).gradient
  have hH : HasFDerivAt H H' (x : Eₙ) := by
    rw [hasFDerivAt_pi]
    intro i
    have hproj :
        HasFDerivAt
          (fun y : Eₙ ↦ y i)
          (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)
          (x : Eₙ) := by
      simpa using PiLp.hasFDerivAt_apply (2 : ENNReal) (x : Eₙ) i
    have hinv :
        HasFDerivAt
          (fun y : Eₙ ↦ (y i)⁻¹)
          (-((((x : Eₙ) i) ^ (2 : ℕ))⁻¹ : ℝ) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ))
          (x : Eₙ) := by
      let L : Eₙ →L[ℝ] ℝ :=
        -((((x : Eₙ) i) ^ (2 : ℕ))⁻¹ : ℝ) •
          (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)
      have hcomp :
          HasFDerivAt
            (fun y : Eₙ ↦ (y i)⁻¹)
            (-(((ContinuousLinearMap.mulLeftRight ℝ ℝ) ((x : Eₙ) i)⁻¹) ((x : Eₙ) i)⁻¹).comp
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ))
            (x : Eₙ) := by
        simpa using (hasFDerivAt_inv' (by exact ne_of_gt (x.2 i))).comp (x : Eₙ) hproj
      have hL :
          -(((ContinuousLinearMap.mulLeftRight ℝ ℝ) ((x : Eₙ) i)⁻¹) ((x : Eₙ) i)⁻¹).comp
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ) = L := by
        ext y
        simp [L, ContinuousLinearMap.mulLeftRight_apply, pow_two, mul_comm, mul_left_comm]
      exact hcomp.congr_fderiv hL
    simpa [H, H'] using hinv.neg
  have hToLp :
      HasFDerivAt
        (WithLp.toLp 2 : (Fin n → ℝ) → Eₙ)
        (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
        (H (x : Eₙ)) := by
    simpa using PiLp.hasFDerivAt_toLp (2 : ENNReal) (H (x : Eₙ))
  have hG :
      HasFDerivAt
        G
        ((
          PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)
        ).symm.toContinuousLinearMap.comp H')
        (x : Eₙ) := by
    simpa [G, H] using hToLp.comp (x : Eₙ) hH
  simpa [H'] using hG.congr_of_eventuallyEq hEq

private theorem standardLogarithmicBarrierAmbient_hessian_apply
    (x : Xₙ) (h : Eₙ) :
    hessian (standardLogarithmicBarrierAmbient n) (x : Eₙ) h =
      WithLp.toLp 2 fun i ↦ h i / ((x : Eₙ) i) ^ (2 : ℕ) := by
  have hderiv := standardLogarithmicBarrierAmbient_hasFDerivAt_gradient x
  change fderiv ℝ (∇ (standardLogarithmicBarrierAmbient n)) (x : Eₙ) h = _
  rw [hderiv.fderiv]
  ext i
  simp [div_eq_mul_inv, mul_comm]

private theorem standardLogarithmicBarrierAmbient_hessian_quadratic
    (x : Xₙ) (h : Eₙ) :
    inner ℝ h
        (hessian (standardLogarithmicBarrierAmbient n) (x : Eₙ) h) =
      ‖δ[x](h)‖ ^ (2 : ℕ) := by
  rw [standardLogarithmicBarrierAmbient_hessian_apply]
  calc
    inner ℝ h (WithLp.toLp 2 fun i ↦ h i / ((x : Eₙ) i) ^ (2 : ℕ))
      = ∑ i : Fin n, h i * (h i / ((x : Eₙ) i) ^ (2 : ℕ)) := by
          rw [PiLp.inner_apply]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          change inner ℝ (h i) (h i / ((x : Eₙ) i) ^ (2 : ℕ)) = _
          change (h i / ((x : Eₙ) i) ^ (2 : ℕ)) * h i = _
          ring
    _ = ∑ i : Fin n, (h i / (x : Eₙ) i) ^ (2 : ℕ) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          field_simp [pow_two, ne_of_gt (x.2 i)]
    _ = ‖δ[x](h)‖ ^ (2 : ℕ) := by
          exact (EuclideanSpace.real_norm_sq_eq (δ[x](h))).symm

-- Proof sketch: compute the Hessian local norm of `standardLogarithmicBarrierAmbient n` at the
-- positive point `x` from the diagonal Hessian with entries `(x i)⁻²`; the resulting quadratic
-- form is `∑ i, (h i / x i)^2`, which is exactly `‖δ[x](h)‖^2`.
/-- Theorem 5.4.7.8: for the positive-orthant logarithmic barrier, the local norm induced by the
Hessian at a strictly positive point `x` agrees with the Euclidean norm of the scaled direction
`δ_x(h)`, written in Lean as `δ[x](h)`. -/
theorem positiveOrthantLogarithmicBarrier_localNorm_eq_norm_relativeDirection
    (x : Xₙ) (h : Eₙ) :
    ‖h‖[standardLogarithmicBarrierAmbient n; x] = ‖δ[x](h)‖ := by
  rw [hessianLocalNorm_def]
  rw [standardLogarithmicBarrierAmbient_hessian_quadratic]
  exact (Real.sqrt_sq_eq_abs ‖δ[x](h)‖).trans (abs_of_nonneg (norm_nonneg _))

end
