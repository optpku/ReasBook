/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Definition_12_3_extra_1
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

open Filter

section

variable {Point Multiplier Reduced : Type*}
variable [NormedAddCommGroup Point] [InnerProductSpace ℝ Point] [CompleteSpace Point]
variable [NormedAddCommGroup Multiplier] [InnerProductSpace ℝ Multiplier]
  [CompleteSpace Multiplier]

-- Domain sampling:
-- * primary domain: reduced-Hessian local convergence rates for equality-constrained
--   optimization in Hilbert spaces, with reduced-space maps parametrizing `ker(A(x_k)ᵀ)`;
-- * sampled owners in the minimal semantic closure:
--   - Chapter 9 `IsReducedNullMatrix`,
--   - Chapter 13 `IsNullSpaceBasisFor`,
--   - Chapter 12 `HasSuperlinearlyConvergentStep`,
--   - Chapter 01 `HasQSuperlinearConvergenceTo`.
-- * best owner abstraction: the reduced-space maps `Z_k` should be recorded first through the
--   null-space owner pattern "range equals `ker(A(x_k)ᵀ)`", before using `Z_kᵀ` in the reduced
--   Hessian equations; this null-space owner itself only needs a normed reduced coordinate
--   space, while Hilbert-space structure on `Reduced` enters only once `Z_kᵀ` is used in the
--   reduced-Hessian equations. The source-facing conclusion `(12.8.28)` is then a two-step
--   instance of the chapter owner `HasSuperlinearlyConvergentStep`, with step
--   `twoStepDisplacement x k = x (k + 2) - x k`.
-- * primitive data vs derived API:
--   - primitive/source data: `IsReducedNullMap`, `IsReducedHessianStep`,
--     `ReducedHessianSecondOrderSufficientCondition`, the iterate update `x (k + 1) = x k + d k`,
--     and the reduced-Hessian ratio from `(12.8.27)`;
--   - derived/bridge API: `twoStepDisplacement`, `reducedHessianErrorRatio`, and the bridge from
--     the two-step source ratio to Chapter 1 `Q`-superlinear convergence of the even subsequence.
-- * source/core/bridge triage:
--   - source-facing: `IsReducedNullMap`, `IsReducedHessianStep`,
--     `ReducedHessianSecondOrderSufficientCondition`, `twoStepDisplacement`,
--     `reducedHessianErrorRatio`, and the main theorem below stated via
--     `HasSuperlinearlyConvergentStep`;
--   - core/canonical: `HasSuperlinearlyConvergentStep`, `ContinuousLinearMap.adjoint`,
--     `ContinuousLinearMap.IsInvertible`, `ContinuousLinearMap.inverse`, `Function.Injective`,
--     `Tendsto`, and `HasQSuperlinearConvergenceTo`;
--   - bridge/view: the explicit unfold lemmas and the even-subsequence bridge theorem below.

section

variable [NormedAddCommGroup Reduced] [NormedSpace ℝ Reduced]

/-- A reduced-space map `Z` is reduced-null for `A` when it parametrizes `ker(Aᵀ)`: every
reduced vector maps into `ker(Aᵀ)`, and every vector in `ker(Aᵀ)` is `Z u` for some reduced
coordinate `u`. This is the continuous-linear-map analogue of the project's Chapter 9 owner
`IsReducedNullMatrix`. -/
structure IsReducedNullMap
    (A : Multiplier →L[ℝ] Point) (Z : Reduced →L[ℝ] Point) : Prop where
  mem_ker : ∀ u : Reduced, A.adjoint (Z u) = 0
  eq_apply : ∀ p : Point, A.adjoint p = 0 → ∃ u : Reduced, Z u = p

/-- Unfolding `IsReducedNullMap A Z` gives the source kernel-inclusion and kernel-surjectivity
conditions for the reduced-space map `Z`. -/
theorem isReducedNullMap_iff
    (A : Multiplier →L[ℝ] Point) (Z : Reduced →L[ℝ] Point) :
    IsReducedNullMap A Z ↔
      (∀ u : Reduced, A.adjoint (Z u) = 0) ∧
        ∀ p : Point, A.adjoint p = 0 → ∃ u : Reduced, Z u = p := by
  constructor
  · intro h
    exact ⟨h.mem_ker, h.eq_apply⟩
  · rintro ⟨mem_ker, eq_apply⟩
    exact ⟨mem_ker, eq_apply⟩

end

section

variable [NormedAddCommGroup Reduced] [InnerProductSpace ℝ Reduced] [CompleteSpace Reduced]

/-- A direction `d_k` is a reduced-Hessian step for the stage data
`g_k`, `A(x_k)`, `c(x_k)`, `B_k`, and reduced-space map `Z_k` when `Z_k` parametrizes
`ker(A(x_k)ᵀ)`, the reduced-space equation `B_k (Z_kᵀ d_k) = - Z_kᵀ g_k` holds, and the
linearized constraint equation `A(x_k)ᵀ d_k = -c(x_k)` holds, matching `(12.8.26)`. -/
structure IsReducedHessianStep
    (gk : Point) (Ak : Multiplier →L[ℝ] Point) (ck : Multiplier)
    (Bk : Reduced →L[ℝ] Reduced) (Zk : Reduced →L[ℝ] Point) (dk : Point) : Prop where
  reducedNullMap : IsReducedNullMap Ak Zk
  reduced_eq : Bk (Zk.adjoint dk) = -(Zk.adjoint gk)
  constraint_eq : Ak.adjoint dk = -ck

/-- Unfolding `IsReducedHessianStep` gives the reduced-null-space owner for `Z_k` together with
the two equations from `(12.8.26)`. -/
theorem isReducedHessianStep_iff
    (gk : Point) (Ak : Multiplier →L[ℝ] Point) (ck : Multiplier)
    (Bk : Reduced →L[ℝ] Reduced) (Zk : Reduced →L[ℝ] Point) (dk : Point) :
    IsReducedHessianStep gk Ak ck Bk Zk dk ↔
      IsReducedNullMap Ak Zk ∧
        Bk (Zk.adjoint dk) = -(Zk.adjoint gk) ∧
          Ak.adjoint dk = -ck := by
  constructor
  · intro h
    exact ⟨h.reducedNullMap, h.reduced_eq, h.constraint_eq⟩
  · rintro ⟨reducedNullMap, reduced_eq, constraint_eq⟩
    exact ⟨reducedNullMap, reduced_eq, constraint_eq⟩

/-- The reduced-Hessian error ratio from `(12.8.27)`, namely
`‖(B_k - Z(x*)ᵀ W(x*, λ*) Z(x*)) (Z_kᵀ d_k)‖ / ‖d_k‖`. -/
def reducedHessianErrorRatio
    (B : ℕ → Reduced →L[ℝ] Reduced)
    (Z : ℕ → Reduced →L[ℝ] Point)
    (ZStar : Reduced →L[ℝ] Point)
    (WStar : Point →L[ℝ] Point)
    (d : ℕ → Point) : ℕ → ℝ :=
  fun k ↦
    ‖((B k - ZStar.adjoint.comp (WStar.comp ZStar)) ((Z k).adjoint (d k)))‖ /
      ‖d k‖

/-- Unfolding `reducedHessianErrorRatio B Z ZStar WStar d k` gives the displayed ratio
from `(12.8.27)`. -/
theorem reducedHessianErrorRatio_apply
    (B : ℕ → Reduced →L[ℝ] Reduced)
    (Z : ℕ → Reduced →L[ℝ] Point)
    (ZStar : Reduced →L[ℝ] Point)
    (WStar : Point →L[ℝ] Point)
    (d : ℕ → Point) (k : ℕ) :
    reducedHessianErrorRatio B Z ZStar WStar d k =
      ‖((B k - ZStar.adjoint.comp (WStar.comp ZStar)) ((Z k).adjoint (d k)))‖ /
        ‖d k‖ :=
  rfl

/-- The reduced-Hessian second-order sufficient condition at `x*`: every nonzero direction in
the nullspace of `A(x*)ᵀ` has strictly positive curvature with respect to `W(x*, λ*)`. -/
def ReducedHessianSecondOrderSufficientCondition
    (AStar : Multiplier →L[ℝ] Point) (WStar : Point →L[ℝ] Point) : Prop :=
  ∀ p : Point, p ≠ 0 → AStar.adjoint p = 0 → 0 < inner ℝ p (WStar p)

/-- Unfolding `ReducedHessianSecondOrderSufficientCondition AStar WStar` gives the source
nullspace-curvature condition at `x*`. -/
theorem reducedHessianSecondOrderSufficientCondition_iff
    (AStar : Multiplier →L[ℝ] Point) (WStar : Point →L[ℝ] Point) :
    ReducedHessianSecondOrderSufficientCondition AStar WStar ↔
      ∀ p : Point, p ≠ 0 → AStar.adjoint p = 0 → 0 < inner ℝ p (WStar p) :=
  Iff.rfl

section

variable {Step : Type*} [AddGroup Step]

/-- The two-step displacement `x_(k + 2) - x_k` used in the reduced-Hessian convergence claim
`(12.8.28)`, viewed as the step fed to `HasSuperlinearlyConvergentStep`. -/
def twoStepDisplacement
    (x : ℕ → Step) : ℕ → Step :=
  fun k ↦ x (k + 2) - x k

/-- Unfolding `twoStepDisplacement x k` gives the source two-step increment `x_(k + 2) - x_k`.
-/
@[simp] theorem twoStepDisplacement_apply
    (x : ℕ → Step) (k : ℕ) :
    twoStepDisplacement x k = x (k + 2) - x k :=
  rfl

end

namespace HasSuperlinearlyConvergentStep

/-- The even subsequence of a 2-step `Q`-superlinearly convergent reduced-Hessian sequence
converges `Q`-superlinearly in the canonical Chapter 1 sense. This is a bridge/view result:
the source-facing owner remains `HasSuperlinearlyConvergentStep x (twoStepDisplacement x) xStar`.
-/
theorem evenSubsequence_hasQSuperlinearConvergenceTo
    {x : ℕ → Point} {xStar : Point}
    (hx : Tendsto x atTop (nhds xStar))
    (h : HasSuperlinearlyConvergentStep x (twoStepDisplacement x) xStar) :
    HasQSuperlinearConvergenceTo (fun k ↦ x (2 * k)) xStar := sorry

end HasSuperlinearlyConvergentStep

/-- Chapter12 Theorem 12.8.1: let `d_k` be the reduced-Hessian step from `(12.8.26)`, so that
`x_(k + 1) = x_k + d_k`. If `x_k ⟶ x*`, `A(x*)` has full column rank, the reduced-Hessian
second-order sufficient condition holds at `x*` for `W(x*, λ*)`, `‖B_k⁻¹‖` is uniformly
bounded, and the reduced-Hessian error ratio `(12.8.27)` tends to `0`, then the two-step
source ratio `(12.8.28)` holds. The source-facing conclusion is expressed by the chapter owner
`HasSuperlinearlyConvergentStep` applied to the two-step displacement
`twoStepDisplacement x`. -/
theorem reducedHessianMethod_convergesTwoStepQSuperlinearly_of_errorRatio_tendsto_zero
    (x d g : ℕ → Point)
    (c : ℕ → Multiplier)
    (A : Point → Multiplier →L[ℝ] Point)
    (B : ℕ → Reduced →L[ℝ] Reduced)
    (ZAt : Point → Reduced →L[ℝ] Point)
    (W : Point → Multiplier → Point →L[ℝ] Point)
    (xStar : Point)
    (lambdaStar : Multiplier)
    (h_stepDef :
      ∀ k : ℕ, IsReducedHessianStep (g k) (A (x k)) (c k) (B k) (ZAt (x k)) (d k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + d k)
    (hx : Tendsto x atTop (nhds xStar))
    (h_fullColumnRank : Function.Injective (A xStar))
    (h_sosc :
      ReducedHessianSecondOrderSufficientCondition (A xStar) (W xStar lambdaStar))
    (hB_invertible : ∀ k : ℕ, (B k).IsInvertible)
    (h_inverse_bounded : ∃ C > 0, ∀ k : ℕ, ‖(B k).inverse‖ ≤ C)
    (h_ratio :
      Tendsto
        (reducedHessianErrorRatio
          B
          (fun k ↦ ZAt (x k))
          (ZAt xStar)
          (W xStar lambdaStar)
          d)
        atTop
        (nhds (0 : ℝ))) :
    HasSuperlinearlyConvergentStep x (twoStepDisplacement x) xStar := sorry

end
