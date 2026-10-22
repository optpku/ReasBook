/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.Matrix.Order
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_5_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient MatrixOrder

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 1.5.12 is source-facing at the Euclidean matrix view of Hessian-Lipschitz control.

Sampled owner-style declarations:
* `HasLipschitzContinuousHessian M f`, written on the theorem surface as `f ∈ C22[M]`, via
  Definition 1.5.3;
* `hessian f x`, the intrinsic Hessian owner from Definition 1.4.16;
* `hessianMatrix` from Definition 1.4.16;
* `fderiv_gradient_isSymmetric_of_contDiffAt` and `hessianMatrix_isSymm_of_contDiffAt` from
  Theorem 1.4.19;
* `ContinuousLinearMap.isPositive_iff` and `Matrix.isPositive_toEuclideanLin_iff`.

Owner abstraction:
* the Hessian operator `fderiv ℝ (∇ f) x`, with `hessianMatrix f x` as its Euclidean matrix view.

Primitive data:
* `f`
* `M`
* `x`
* `y`

Derived API:
* the operator-norm estimate `HasLipschitzContinuousHessian.norm_sub_le hf y x`
* the intrinsic Loewner bounds on `hessian f x` below;
* the Euclidean matrix Loewner bounds obtained from that intrinsic theorem through
  `hessianMatrix_toEuclideanLin`
-/

/-- If `f` has `M`-Lipschitz Hessian, then the intrinsic Hessians at `x` and `y` differ by at
most `M ‖y - x‖ I` in Loewner order. -/
theorem hessian_loewner_bounds_of_hessian_lipschitz
    {M : NNReal} {f : E → ℝ} (hf : f ∈ C22[M]) (x y : E) :
    let s : ℝ := (M : ℝ) * ‖y - x‖
    hessian f x - s • 1 ≤ hessian f y ∧
      hessian f y ≤ hessian f x + s • 1 := by
  let Δ : E →L[ℝ] E := hessian f y - hessian f x
  let s : ℝ := (M : ℝ) * ‖y - x‖
  have hΔ_symm : Δ.IsSymmetric := by
    dsimp [Δ]
    exact (fderiv_gradient_isSymmetric_of_contDiffAt
      (hf.contDiff.contDiffAt : ContDiffAt ℝ 2 f y)).sub
      (fderiv_gradient_isSymmetric_of_contDiffAt
        (hf.contDiff.contDiffAt : ContDiffAt ℝ 2 f x))
  have hΔ_norm : ‖Δ‖ ≤ s := by
    dsimp [Δ, s]
    exact HasLipschitzContinuousHessian.norm_sub_le hf y x
  have hquad_bound (u : E) :
      |inner ℝ (Δ u) u| ≤ s * ‖u‖ ^ (2 : ℕ) := by
    calc
      |inner ℝ (Δ u) u| ≤ ‖Δ u‖ * ‖u‖ := by
        simpa [real_inner_comm] using abs_real_inner_le_norm (Δ u) u
      _ ≤ (‖Δ‖ * ‖u‖) * ‖u‖ := by
        gcongr
        exact Δ.le_opNorm u
      _ = ‖Δ‖ * ‖u‖ ^ (2 : ℕ) := by ring
      _ ≤ s * ‖u‖ ^ (2 : ℕ) := by
        gcongr
  have hsI_symm : (s • (1 : E →L[ℝ] E)).IsSymmetric := by
    intro u v
    simp [real_inner_smul_left, real_inner_smul_right]
  have hupper_nonneg : 0 ≤ s • (1 : E →L[ℝ] E) - Δ := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff]
    constructor
    · exact hsI_symm.sub hΔ_symm
    · intro u
      have hu : inner ℝ (Δ u) u ≤ s * ‖u‖ ^ (2 : ℕ) := (abs_le.mp (hquad_bound u)).2
      have hrewrite :
          inner ℝ ((s • (1 : E →L[ℝ] E) - Δ) u) u =
            s * ‖u‖ ^ (2 : ℕ) - inner ℝ (Δ u) u := by
        simp [real_inner_smul_left, inner_sub_left]
      rw [hrewrite]
      linarith
  have hlower_nonneg : 0 ≤ s • (1 : E →L[ℝ] E) + Δ := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff]
    constructor
    · exact hsI_symm.add hΔ_symm
    · intro u
      have hu : -(s * ‖u‖ ^ (2 : ℕ)) ≤ inner ℝ (Δ u) u := (abs_le.mp (hquad_bound u)).1
      have hrewrite :
          inner ℝ ((s • (1 : E →L[ℝ] E) + Δ) u) u =
            s * ‖u‖ ^ (2 : ℕ) + inner ℝ (Δ u) u := by
        simp [real_inner_smul_left, inner_add_left]
      rw [hrewrite]
      linarith
  constructor
  · rw [ContinuousLinearMap.le_def]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp <| by
      dsimp [Δ, s] at hlower_nonneg ⊢
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlower_nonneg
  · rw [ContinuousLinearMap.le_def]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp <| by
      dsimp [Δ, s] at hupper_nonneg ⊢
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hupper_nonneg

section Euclidean

variable {n : ℕ}

local notation "EFin" => EuclideanSpace ℝ (Fin n)

/-- Theorem 1.5.12: if `f : ℝⁿ → ℝ` has `M`-Lipschitz Hessian, then `∇² f x` and `∇² f y`
differ by at most `M ‖y - x‖ I` in the Loewner order. -/
-- Proof sketch: apply the intrinsic Hessian comparison theorem above in the Hilbert-space owner
-- `hessian f x`, then transport the two operator inequalities through the Euclidean matrix bridge
-- `hessianMatrix_toEuclideanLin`.
theorem hessianMatrix_loewner_bounds_of_hessian_lipschitz
    {M : NNReal} {f : EFin → ℝ} (hf : f ∈ C22[M]) (x y : EFin) :
    let s : ℝ := (M : ℝ) * ‖y - x‖
    ∇² f x - s • 1 ≤ ∇² f y ∧
      ∇² f y ≤ ∇² f x + s • 1 := by
  let s : ℝ := (M : ℝ) * ‖y - x‖
  have hcore := hessian_loewner_bounds_of_hessian_lipschitz hf x y
  dsimp [s] at hcore ⊢
  rcases hcore with ⟨hlower, hupper⟩
  have hlower_pos :
      (hessian f y - (hessian f x - s • (1 : EFin →L[ℝ] EFin))).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using hlower
  have hupper_pos :
      ((hessian f x + s • (1 : EFin →L[ℝ] EFin)) - hessian f y).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using hupper
  constructor
  · refine sub_nonneg.mp ?_
    rw [Matrix.nonneg_iff_posSemidef, ← Matrix.isPositive_toEuclideanLin_iff]
    change
      (((∇² f y - (∇² f x - s • 1)).toEuclideanLin : EFin →ₗ[ℝ] EFin)).IsPositive
    have hbridge :
        ((∇² f y - (∇² f x - s • 1)).toEuclideanLin : EFin →ₗ[ℝ] EFin) =
          ((hessian f y - (hessian f x - s • (1 : EFin →L[ℝ] EFin))) : EFin →ₗ[ℝ] EFin) := by
      calc
        ((∇² f y - (∇² f x - s • 1)).toEuclideanLin : EFin →ₗ[ℝ] EFin)
            = ((∇² f y).toEuclideanLin : EFin →ₗ[ℝ] EFin) -
                (((∇² f x).toEuclideanLin : EFin →ₗ[ℝ] EFin) - s • LinearMap.id) := by
                    simp
        _ = (hessian f y : EFin →ₗ[ℝ] EFin) -
              ((hessian f x : EFin →ₗ[ℝ] EFin) - s • LinearMap.id) := by
                rw [hessianMatrix_toEuclideanLin, hessianMatrix_toEuclideanLin]
        _ = ((hessian f y - (hessian f x - s • (1 : EFin →L[ℝ] EFin))) : EFin →ₗ[ℝ] EFin) := by
              ext z
              simp
    rw [hbridge]
    exact hlower_pos.toLinearMap
  · refine sub_nonneg.mp ?_
    rw [Matrix.nonneg_iff_posSemidef, ← Matrix.isPositive_toEuclideanLin_iff]
    change
      (((∇² f x + s • 1 - ∇² f y).toEuclideanLin : EFin →ₗ[ℝ] EFin)).IsPositive
    have hbridge :
        ((∇² f x + s • 1 - ∇² f y).toEuclideanLin : EFin →ₗ[ℝ] EFin) =
          (((hessian f x + s • (1 : EFin →L[ℝ] EFin)) - hessian f y) : EFin →ₗ[ℝ] EFin) := by
      calc
        ((∇² f x + s • 1 - ∇² f y).toEuclideanLin : EFin →ₗ[ℝ] EFin)
            = ((∇² f x).toEuclideanLin : EFin →ₗ[ℝ] EFin) +
                s • LinearMap.id - ((∇² f y).toEuclideanLin : EFin →ₗ[ℝ] EFin) := by
                    simp
        _ = (hessian f x : EFin →ₗ[ℝ] EFin) + s • LinearMap.id -
              (hessian f y : EFin →ₗ[ℝ] EFin) := by
                rw [hessianMatrix_toEuclideanLin, hessianMatrix_toEuclideanLin]
        _ = (((hessian f x + s • (1 : EFin →L[ℝ] EFin)) - hessian f y) : EFin →ₗ[ℝ] EFin) := by
              ext z
              simp
    rw [hbridge]
    exact hupper_pos.toLinearMap

end Euclidean

end
