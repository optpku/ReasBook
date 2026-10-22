/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.WolfeCounterexample.AutomaticMatrixIdentityLiminf
public import ReasLib.LinearAlgebra.Matrix.PosDef.Sqrt
public import ReasLib.Analysis.Calculus.Gradient.HessianHolder
public import ReasLib.Optimization.DFP.Polar.PlanarCounterexample
public import ReasLib.Optimization.DFP.Polar.OrthogonalExtension

public section

noncomputable section

open Filter
open scoped Matrix MatrixOrder Topology InnerProduct

namespace DFP.Polar.IdentityInitialization

/-- Helper for cor:identity-initialization: the original objective composed with
its positive-square-root coordinate map. -/
def pulledObjective {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → ℝ := it.objective ∘ P

/-- Helper for cor:identity-initialization: the exact source pullback objective. -/
theorem pulledObjective_def {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    pulledObjective it P = it.objective ∘ P := by
  rfl

/-- Helper for cor:identity-initialization: the exact inverse-coordinate source points. -/
def pulledPoints {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ P.symm (it.point k)

/-- Helper for cor:identity-initialization: the transformed point sequence as a whole. -/
theorem pulledPoints_def {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    pulledPoints it P = fun k ↦ P.symm (it.point k) := by
  rfl

/-- Helper for cor:identity-initialization: the original point sequence is transformed by P⁻¹. -/
theorem pulledPoints_apply {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    pulledPoints it P k = P.symm (it.point k) := by
  rfl

/-- Helper for cor:identity-initialization: the original gradient sequence transformed by Pᵀ. -/
def pulledGradients {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ P.toContinuousLinearMap.adjoint
      (DFP.gradients it.objective it.point k)

/-- Helper for cor:identity-initialization: the transformed gradient sequence as a whole. -/
theorem pulledGradients_def {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    pulledGradients it P = fun k ↦ P.toContinuousLinearMap.adjoint
      (DFP.gradients it.objective it.point k) := by
  rfl

/-- Helper for cor:identity-initialization: the public exact transformed-gradient formula. -/
theorem pulledGradients_apply {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    pulledGradients it P k = P.toContinuousLinearMap.adjoint
      (DFP.gradients it.objective it.point k) := by
  rfl

/-- Helper for cor:identity-initialization: canonical actual matrices representing
P⁻¹ Hₖ P⁻ᵀ, in the same standard Euclidean coordinates as the source iteration. -/
def pulledInverseHessians {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ℕ → Matrix (Fin n) (Fin n) ℝ :=
  WolfeCounterexample.canonicalMatrixSequence (fun k ↦ P.symm.toContinuousLinearMap.pushforward
    ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (it.inverseHessian k)))

/-- Helper for cor:identity-initialization: the canonical transformed matrix sequence as a whole. -/
theorem pulledInverseHessians_def {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    pulledInverseHessians it P = WolfeCounterexample.canonicalMatrixSequence
      (fun k ↦ P.symm.toContinuousLinearMap.pushforward
        ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (it.inverseHessian k))) := by
  rfl

/-- Helper for cor:identity-initialization: the small explicit matrix representation interface. -/
theorem pulledInverseHessians_apply {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    pulledInverseHessians it P k =
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
          (P.symm.toContinuousLinearMap.pushforward
            ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
              EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
                (it.inverseHessian k))) := by
  rw [pulledInverseHessians, WolfeCounterexample.canonicalMatrixSequence_apply]

/-- Helper for cor:identity-initialization: generic DFP covariance yields the
actual canonical matrix orbit with the same original positive step lengths. -/
theorem pulledOrbit {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (hstep : ∀ k, 0 < it.stepLength k)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    DFP.IsOrbit (pulledObjective it P) it.stepLength (pulledPoints it P)
      (pulledGradients it P) (pulledInverseHessians it P) := by
  have h := ((it.isOrbit hstep).toOperator.pullback P).toMatrix
  simpa only [pulledObjective_def, pulledPoints_def, pulledGradients_def, pulledInverseHessians_def,
    WolfeCounterexample.canonicalMatrixSequence_eq_explicit] using h

/-- Helper for cor:identity-initialization: the transformed prescribed gradients
are the canonical gradients of the exact pulled-back objective and point sequence. -/
theorem pulledGradients_eq {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (hstep : ∀ k, 0 < it.stepLength k)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    DFP.gradients (pulledObjective it P) (pulledPoints it P) = pulledGradients it P :=
  (pulledOrbit it hstep P).gradients_eq

/-- Helper for cor:identity-initialization: an invertible linear coordinate change
transports the full cluster relation in both directions. -/
theorem mapClusterPt_pullback {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E ≃L[ℝ] F) (x : ℕ → F) (z : E) :
    MapClusterPt z atTop (fun k ↦ P.symm (x k)) ↔ MapClusterPt (P z) atTop x := by
  constructor
  · intro h
    simpa only [Function.comp_def, P.apply_symm_apply] using
      h.continuousAt_comp P.continuous.continuousAt
  · intro h
    simpa only [Function.comp_def, P.symm_apply_apply] using
      h.continuousAt_comp P.symm.continuous.continuousAt

/-- Helper for cor:identity-initialization: the transformed cluster set is
exactly the inverse-map image of the original cluster set. -/
theorem clusterSet_pullback {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (P : E ≃L[ℝ] F) (x : ℕ → F) :
    {z | MapClusterPt z atTop (fun k ↦ P.symm (x k))} =
      P.symm '' {v | MapClusterPt v atTop x} := by
  ext z
  constructor
  · intro hz
    exact ⟨P z, (mapClusterPt_pullback P x z).mp hz, P.symm_apply_apply z⟩
  · rintro ⟨v, hv, rfl⟩
    apply (mapClusterPt_pullback P x (P.symm v)).mpr
    simpa only [Set.mem_setOf_eq, P.apply_symm_apply] using hv

/-- Helper for cor:identity-initialization: the inverse square-root image of
the exact source unit circle is the complete centered ellipse cluster set. -/
theorem clusterSet_ellipse (P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ]
    EuclideanSpace ℝ (Fin 2)) (x : ℕ → EuclideanSpace ℝ (Fin 2))
    (hcircle : ∀ v, MapClusterPt v atTop x ↔ ‖v‖ = 1) :
    {z | MapClusterPt z atTop (fun k ↦ P.symm (x k))} =
      P.symm.toLinearMap '' Metric.sphere 0 1 := by
  rw [clusterSet_pullback]
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, hcircle, Metric.mem_sphere, dist_zero_right]

/-- Helper for cor:identity-initialization: an injective linear image of the
Euclidean plane has range dimension exactly two. -/
theorem ellipse_range_finrank {ι : Type*}
    (i : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ ι)
    (hi : Function.Injective i) : Module.finrank ℝ (LinearMap.range i) = 2 := by
  simpa only [finrank_euclideanSpace_fin] using (LinearEquiv.ofInjective i hi).finrank_eq.symm

/-- Helper for cor:identity-initialization: an invertible linear pullback
preserves the original zero value and unique global minimizer at the origin. -/
theorem origin_unique_pullback {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : F → ℝ) (P : E ≃L[ℝ] F)
    (hzero : f 0 = 0) (hunique : ∀ x, (∀ y, f x ≤ f y) ↔ x = 0) :
    (f ∘ P) 0 = 0 ∧ ∀ x, (∀ y, (f ∘ P) x ≤ (f ∘ P) y) ↔ x = 0 := by
  constructor
  · simpa only [Function.comp_apply, map_zero] using hzero
  · intro x
    constructor
    · intro hmin
      have hsource : ∀ y, f (P x) ≤ f y := by
        intro y
        simpa only [Function.comp_apply, P.apply_symm_apply] using hmin (P.symm y)
      have hz := (hunique (P x)).mp hsource
      apply P.injective
      simpa only [map_zero] using hz
    · intro hx
      subst x
      intro y
      have hsource := (hunique 0).mpr rfl
      simpa only [Function.comp_apply, map_zero] using hsource (P y)

/-- Helper for cor:identity-initialization: global half-Hölder Hessian regularity
transforms with the source coordinate factor of order `2+1/2`. -/
theorem halfHolder_pullback {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (P : E ≃L[ℝ] F)
    (C : ℝ) (hC : 0 ≤ C)
    (hholder : ∀ x y, ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ (1 / 2 : ℝ)) :
    ∀ x y, ‖hessian (f ∘ P) x - hessian (f ∘ P) y‖ ≤
      (‖P.toContinuousLinearMap‖ ^ 2 * C * ‖P.toContinuousLinearMap‖ ^ (1 / 2 : ℝ)) *
        ‖x - y‖ ^ (1 / 2 : ℝ) := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  exact hessianHolder_comp_continuousLinearEquiv hf P hC hhalf hholder

/-- Helper for cor:identity-initialization: arbitrary invertible adjoint congruence
preserves positive definiteness of the actual canonical matrix representation. -/
theorem canonicalPushforward_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
        (P.toContinuousLinearMap.pushforward
          ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) A))).PosDef := by
  have hpositive : ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) A).IsPositive :=
    Matrix.isPositive_toEuclideanCLM_iff.mpr hA.posSemidef
  have hcongruent := hpositive.pushforward P.toContinuousLinearMap
  have hstrict : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
      0 < inner ℝ z (P.toContinuousLinearMap.pushforward
        ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) A) z) := by
    intro z hz
    have hadjoint : P.toContinuousLinearMap.adjoint z ≠ 0 := by
      intro hzero
      have h := congrArg P.symm.toContinuousLinearMap.adjoint hzero
      rw [P.adjoint_symm_apply_adjoint, map_zero] at h
      exact hz h
    have hcoordinates : WithLp.ofLp (P.toContinuousLinearMap.adjoint z) ≠ 0 := by
      intro hzero
      apply hadjoint
      exact (WithLp.ofLp_injective 2) hzero
    have hinner : 0 < inner ℝ (P.toContinuousLinearMap.adjoint z)
        (((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) A)
            (P.toContinuousLinearMap.adjoint z)) := by
      simpa only [Matrix.inner_toEuclideanCLM, star_trivial] using
        hA.dotProduct_mulVec_pos hcoordinates
    rw [ContinuousLinearMap.pushforward_apply,
      ← P.toContinuousLinearMap.adjoint_inner_left]
    exact hinner
  have hmatrix := WolfeCounterexample.canonicalMatrix_posDef_of_operatorStrictPositive
    hcongruent.isSelfAdjoint hstrict
  simpa only [WolfeCounterexample.canonicalMatrixSequence_apply] using hmatrix

/-- Helper for cor:identity-initialization: all canonical transformed inverse Hessians
are positive definite, without changing the source matrix sequence. -/
theorem pulledInverseHessians_posDef {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    (pulledInverseHessians it P k).PosDef := by
  rw [pulledInverseHessians_apply]
  exact canonicalPushforward_posDef _ (it.inverseHessianPosDef k) P.symm

/-- Helper for cor:identity-initialization: the same positive alpha transforms
the actual canonical source displacement by the inverse coordinate map. -/
theorem pulledSteps_eq {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (hstep : ∀ k, 0 < it.stepLength k)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    DFP.steps it.stepLength (DFP.directions (pulledInverseHessians it P)
      (pulledGradients it P)) k =
        P.symm (DFP.steps it.stepLength (DFP.directions it.inverseHessian
          (DFP.gradients it.objective it.point)) k) := by
  have hnew := (pulledOrbit it hstep P).pointSucc k
  have hold := (it.isOrbit hstep).pointSucc k
  have hnewStep : DFP.steps it.stepLength (DFP.directions (pulledInverseHessians it P)
      (pulledGradients it P)) k = pulledPoints it P (k + 1) - pulledPoints it P k := by
    rw [hnew]
    abel
  calc
    DFP.steps it.stepLength (DFP.directions (pulledInverseHessians it P)
        (pulledGradients it P)) k = pulledPoints it P (k + 1) - pulledPoints it P k := hnewStep
    _ = P.symm (it.point (k + 1) - it.point k) := by
      rw [pulledPoints_apply, pulledPoints_apply, map_sub]
    _ = P.symm (DFP.steps it.stepLength (DFP.directions it.inverseHessian
        (DFP.gradients it.objective it.point)) k) := by
      rw [hold]
      congr 1
      abel

/-- Helper for cor:identity-initialization: the actual gradient differences
transform by the source adjoint map. -/
theorem pulledGradientChanges_eq {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    DFP.gradientChanges (pulledGradients it P) k = P.toContinuousLinearMap.adjoint
      (DFP.gradientChanges (DFP.gradients it.objective it.point) k) := by
  rw [DFP.gradientChanges_apply, DFP.gradientChanges_apply,
    pulledGradients_apply, pulledGradients_apply, map_sub]

/-- Helper for cor:identity-initialization: real Euclidean scalar products
are exactly the canonical coordinate secant pairings. -/
theorem inner_eq_dot {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ u v = WithLp.ofLp u ⬝ᵥ WithLp.ofLp v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- Helper for cor:identity-initialization: the transformed actual secant
denominator is exactly its original source value. -/
theorem pulledDenominator_eq {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (hstep : ∀ k, 0 < it.stepLength k)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    WithLp.ofLp (DFP.steps it.stepLength (DFP.directions (pulledInverseHessians it P)
      (pulledGradients it P)) k) ⬝ᵥ WithLp.ofLp (DFP.gradientChanges (pulledGradients it P) k) =
    WithLp.ofLp (DFP.steps it.stepLength (DFP.directions it.inverseHessian
      (DFP.gradients it.objective it.point)) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges (DFP.gradients it.objective it.point) k) := by
  rw [pulledSteps_eq it hstep P k, pulledGradientChanges_eq it P k,
    ← inner_eq_dot, DFP.Operator.secantPairing_change, inner_eq_dot]

/-- Helper for cor:identity-initialization: the nonzero original matrix
secant denominators remain nonzero in canonical transformed coordinates. -/
theorem pulledDenominator_ne {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (hstep : ∀ k, 0 < it.stepLength k)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    WithLp.ofLp (DFP.steps it.stepLength (DFP.directions (pulledInverseHessians it P)
      (pulledGradients it P)) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges (pulledGradients it P) k) ≠ 0 := by
  rw [pulledDenominator_eq it hstep P k]
  exact it.secantDenominatorNe k

/-- Helper for cor:identity-initialization: exact source projections for the
canonical transformed actual matrix iteration. -/
structure PullbackData {n : ℕ} (source target : DFP.InverseIteration (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop where
  /-- Helper for cor:identity-initialization: the exact original pulled-back objective. -/
  objective : target.objective = pulledObjective source P
  /-- Helper for cor:identity-initialization: the same original positive alpha sequence. -/
  stepLength : target.stepLength = source.stepLength
  /-- Helper for cor:identity-initialization: the exact inverse-coordinate source points. -/
  point : target.point = pulledPoints source P
  /-- Helper for cor:identity-initialization: actual canonical matrices for P⁻¹ H P⁻ᵀ. -/
  inverseHessian : target.inverseHessian = pulledInverseHessians source P
  /-- Helper for cor:identity-initialization: exact canonical transformed gradients. -/
  gradients : DFP.gradients target.objective target.point = pulledGradients source P

/-- Helper for cor:identity-initialization: generic DFP covariance and canonical
matrix reconstruction preserve every original source sequence exactly. -/
theorem existsPulledIteration {n : ℕ} (it : DFP.InverseIteration (Fin n))
    (hstep : ∀ k, 0 < it.stepLength k)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ target : DFP.InverseIteration (Fin n), PullbackData it target P := by
  have hOrbit := pulledOrbit it hstep P
  have hPos := pulledInverseHessians_posDef it P
  have hDen := pulledDenominator_ne it hstep P
  let target := hOrbit.toInverseIteration hPos hDen
  have hf : target.objective = pulledObjective it P :=
    hOrbit.toInverseIteration_objective hPos hDen
  have hα : target.stepLength = it.stepLength := hOrbit.toInverseIteration_stepLength hPos hDen
  have hx : target.point = pulledPoints it P := hOrbit.toInverseIteration_point_eq hPos hDen
  have hH : target.inverseHessian = pulledInverseHessians it P :=
    hOrbit.toInverseIteration_inverseHessian_eq hPos hDen
  have hg : DFP.gradients target.objective target.point = pulledGradients it P := by
    rw [hf, hx]
    exact hOrbit.gradients_eq
  exact ⟨target, hf, hα, hx, hH, hg⟩

/-- Helper for cor:identity-initialization: the literal positive self-adjoint
matrix square root has fixed positive lower and upper distortion constants. -/
theorem positiveRoot_bounds {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      a • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≤
        hA.sqrtEquiv.toContinuousLinearMap.pullback 1 ∧
      hA.sqrtEquiv.toContinuousLinearMap.pullback 1 ≤
        b • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∧
      a • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≤
        hA.sqrtEquiv.toContinuousLinearMap.pushforward 1 := by
  let Aop := (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) A
  have hpositive : Aop.IsPositive := Matrix.isPositive_toEuclideanCLM_iff.mpr hA.posSemidef
  have hunit : IsUnit Aop := by
    exact (isUnit_map_iff (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) A).mpr hA.isUnit
  obtain ⟨a, ha, hlower⟩ :=
    ContinuousLinearMap.exists_loewner_lowerBound_of_isPositive_isUnit hpositive hunit
  have hupper : Aop ≤ ‖Aop‖ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := ContinuousLinearMap.isPositive_le_norm_smul_one hpositive
  have hdiff : (‖Aop‖ + 1) • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) - ‖Aop‖ • 1 = 1 := by module
  have hnormLe : ‖Aop‖ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) ≤ (‖Aop‖ + 1) • 1 := by
    rw [ContinuousLinearMap.le_def, hdiff]
    exact ContinuousLinearMap.isPositive_one
  have hpull : hA.sqrtEquiv.toContinuousLinearMap.pullback 1 = Aop := by
    rw [ContinuousLinearMap.pullback_one_eq_pushforward_one _ hA.sqrtEquiv_isSelfAdjoint,
      ← hA.sqrtEquiv_pushforward_one]
  have hpush : hA.sqrtEquiv.toContinuousLinearMap.pushforward 1 = Aop :=
    hA.sqrtEquiv_pushforward_one.symm
  have hb : 0 < ‖Aop‖ + 1 := by positivity
  refine ⟨a, ‖Aop‖ + 1, ha, hb, ?_, ?_, ?_⟩
  · rw [hpull]
    exact hlower
  · rw [hpull]
    exact hupper.trans hnormLe
  · rw [hpush]
    exact hlower

/-- Helper for cor:identity-initialization: the actual canonical matrix
initialization under the literal positive square root is exactly the identity. -/
theorem pulledInverseHessians_zero {n : ℕ} (it : DFP.InverseIteration (Fin n)) :
    pulledInverseHessians it (it.inverseHessianPosDef 0).sqrtEquiv 0 =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [pulledInverseHessians_apply, (it.inverseHessianPosDef 0).sqrtEquiv_symm_pushforward,
    map_one]

/-- Helper for cor:identity-initialization: the standard strong Wolfe pair
is preserved on the exact transformed source points and objective. -/
theorem PullbackData.strongWolfe {n : ℕ} {source target : DFP.InverseIteration (Fin n)}
    {P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hdata : PullbackData source target P) {c₁ c₂ : ℝ}
    (hsource : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ source.objective
      (source.point k) (source.point (k + 1) - source.point k)) :
    ∀ k, LineSearch.IsStrongWolfe c₁ c₂ target.objective
      (target.point k) (target.point (k + 1) - target.point k) := by
  intro k
  have h := (hsource k).comp_continuousLinearEquiv P
  simpa only [hdata.objective, hdata.point, pulledObjective_def, pulledPoints_apply,
    map_sub] using h

/-- Helper for cor:identity-initialization: a positive source gradient limit
and positive adjoint distortion give an explicit positive transformed tail and liminf. -/
theorem pulledGradient_liminf {n : ℕ} {c₁ c₂ q : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (hq : 0 < q)
    (hlower : q • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≤
      P.toContinuousLinearMap.pushforward 1) :
    0 < liminf (fun k ↦ ‖pulledGradients c.iteration P k‖) atTop ∧
      ∃ δ > 0, ∀ᶠ k in atTop, δ ≤ ‖pulledGradients c.iteration P k‖ := by
  have hSourceLower : ∀ᶠ k in atTop,
      c.gradientLimit / 2 ≤ ‖DFP.gradients c.iteration.objective c.iteration.point k‖ := by
    have hlt : c.gradientLimit / 2 < c.gradientLimit := by linarith [c.gradientLimitPos]
    exact ((tendsto_order.1 c.gradientNormTendsto).1 _ hlt).mono (fun _ h ↦ h.le)
  have hSourceUpper : ∀ᶠ k in atTop,
      ‖DFP.gradients c.iteration.objective c.iteration.point k‖ ≤ 2 * c.gradientLimit := by
    have hlt : c.gradientLimit < 2 * c.gradientLimit := by linarith [c.gradientLimitPos]
    exact ((tendsto_order.1 c.gradientNormTendsto).2 _ hlt).mono (fun _ h ↦ h.le)
  let δ := Real.sqrt q * (c.gradientLimit / 2)
  have hδ : 0 < δ := mul_pos (Real.sqrt_pos.mpr hq) (half_pos c.gradientLimitPos)
  have hLower : ∀ᶠ k in atTop, δ ≤ ‖pulledGradients c.iteration P k‖ := by
    filter_upwards [hSourceLower] with k hk
    rw [pulledGradients_apply]
    exact (mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg q)).trans
      (P.toContinuousLinearMap.norm_adjoint_lower_bound hq.le hlower _)
  have hUpper : ∀ᶠ k in atTop, ‖pulledGradients c.iteration P k‖ ≤
      ‖P.toContinuousLinearMap.adjoint‖ * (2 * c.gradientLimit) := by
    filter_upwards [hSourceUpper] with k hk
    rw [pulledGradients_apply]
    exact (P.toContinuousLinearMap.adjoint.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hk (norm_nonneg _))
  exact ⟨DFP.positive_liminf_of_eventually_lower_upper hδ hLower hUpper, δ, hδ, hLower⟩

/-- Helper for cor:identity-initialization: a supplied source certificate has an
actual matrix-valued identity-initialized normalization with all source projections intact. -/
theorem existsNormalizedCertificate {n : ℕ} (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂) :
    ∃ (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (m M : ℝ) (d : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n m M c₁ c₂),
      P = (c.iteration.inverseHessianPosDef 0).sqrtEquiv ∧
        PullbackData c.iteration d.iteration P := by
  let P := (c.iteration.inverseHessianPosDef 0).sqrtEquiv
  obtain ⟨a, b, ha, hb, hlower, hupper, hgradient⟩ :=
    positiveRoot_bounds _ (c.iteration.inverseHessianPosDef 0)
  obtain ⟨it, hdata⟩ := existsPulledIteration c.iteration c.stepLengthPos P
  have hhalfPos : (0 : ℝ) < 1 / 2 := by norm_num
  have hm : 0 < (1 / 2 : ℝ) * a := mul_pos hhalfPos ha
  have hab : a ≤ b := WolfeCounterexample.scalar_le_of_identity_loewner_bounds hn
    (hlower.trans hupper)
  have hmM : (1 / 2 : ℝ) * a ≤ (3 / 2 : ℝ) * b := by nlinarith
  have hC2 : ContDiff ℝ 2 it.objective := by
    rw [hdata.objective, pulledObjective_def]
    exact c.objectiveContDiff.comp P.contDiff
  have hstep : ∀ k, 0 < it.stepLength k := by
    rw [hdata.stepLength]
    exact c.stepLengthPos
  have hGradientDiff : Differentiable ℝ (gradient c.iteration.objective) :=
    (c.objectiveContDiff.gradient_succ (n := 1)).differentiable_one
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hthree : (0 : ℝ) ≤ 3 / 2 := by norm_num
  have hBounds : HasHessianBounds ((1 / 2 : ℝ) * a) ((3 / 2 : ℝ) * b) it.objective := by
    rw [hdata.objective, pulledObjective_def]
    exact c.hessianBounds.comp_continuousLinearEquiv P hGradientDiff hhalf hthree hlower hupper
  have hInitial : it.inverseHessian 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hdata.inverseHessian]
    exact pulledInverseHessians_zero c.iteration
  have hGradient := pulledGradient_liminf c P ha hgradient
  have hLiminf : 0 < liminf (fun k ↦ ‖DFP.gradients it.objective it.point k‖) atTop := by
    rw [hdata.gradients]
    exact hGradient.1
  have hTail : ∃ δ > 0, ∀ᶠ k in atTop, δ ≤ ‖DFP.gradients it.objective it.point k‖ := by
    rw [hdata.gradients]
    exact hGradient.2
  let d : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n
      ((1 / 2 : ℝ) * a) ((3 / 2 : ℝ) * b) c₁ c₂ := {
    iteration := it
    c₁_pos := (c.strongWolfe 0).c₁_pos
    c₁_lt_c₂ := (c.strongWolfe 0).c₁_lt_c₂
    c₂_lt_one := (c.strongWolfe 0).c₂_lt_one
    hessianLowerPos := hm
    hessianLowerLeUpper := hmM
    objectiveContDiff := hC2
    stepLengthPos := hstep
    hessianBounds := hBounds
    strongWolfe := hdata.strongWolfe c.strongWolfe
    initialInverseHessian_eq_one := hInitial
    gradientNormLiminfPos := hLiminf
    gradientNormEventuallyPositive := hTail
  }
  have hP : P = (c.iteration.inverseHessianPosDef 0).sqrtEquiv := rfl
  exact ⟨P, (1 / 2 : ℝ) * a, (3 / 2 : ℝ) * b, d, hP, hdata⟩

/-- Helper for cor:identity-initialization: the objective and full centered
ellipse conclusions attached to one actual canonical matrix iteration. -/
structure EllipseObjectiveProperties {ι : Type*} [Fintype ι]
    (it : DFP.InverseIteration ι)
    (i : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ ι) : Prop where
  /-- Helper for cor:identity-initialization: the ellipse map is linear and injective. -/
  injective : Function.Injective i
  /-- Helper for cor:identity-initialization: the containing linear plane has dimension two. -/
  range_finrank : Module.finrank ℝ (LinearMap.range i) = 2
  /-- Helper for cor:identity-initialization: the full point cluster set is the centered ellipse. -/
  cluster : {x | MapClusterPt x atTop it.point} = i '' Metric.sphere 0 1
  /-- Helper for cor:identity-initialization: the normalized objective has global half-Hölder
  Hessian. -/
  half_holder : ∃ C > 0, ∀ x y, ‖hessian it.objective x - hessian it.objective y‖ ≤
    C * ‖x - y‖ ^ (1 / 2 : ℝ)
  /-- Helper for cor:identity-initialization: the original origin value is exactly zero. -/
  origin : it.objective 0 = 0
  /-- Helper for cor:identity-initialization: the origin is the unique global minimizer. -/
  unique_minimizer : ∀ x, (∀ y, it.objective x ≤ it.objective y) ↔ x = 0

/-- Helper for cor:identity-initialization: the supplied planar source certificate's
original circle, Holder regularity and unique origin become the actual centered ellipse package. -/
theorem normalizePlanarWithProperties {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂)
    (hzero : c.iteration.objective 0 = 0)
    (hunique : ∀ x, (∀ y, c.iteration.objective x ≤ c.iteration.objective y) ↔ x = 0)
    (hholder : ∃ C ≥ 0, ∀ x y,
      ‖hessian c.iteration.objective x - hessian c.iteration.objective y‖ ≤
        C * ‖x - y‖ ^ (1 / 2 : ℝ))
    (hcircle : ∀ x, MapClusterPt x atTop c.iteration.point ↔ ‖x‖ = 1) :
    ∃ (P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
      (m M : ℝ) (d : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate 2 m M c₁ c₂),
      P = (c.iteration.inverseHessianPosDef 0).sqrtEquiv ∧ PullbackData c.iteration d.iteration P ∧
        EllipseObjectiveProperties d.iteration P.symm.toLinearMap := by
  have htwo : (2 : ℕ) ≤ 2 := le_rfl
  obtain ⟨P, m, M, d, hP, hdata⟩ := existsNormalizedCertificate htwo c
  have hObjective : d.iteration.objective = c.iteration.objective ∘ P :=
    hdata.objective.trans (pulledObjective_def c.iteration P)
  have horigin := origin_unique_pullback c.iteration.objective P hzero hunique
  have hInjective : Function.Injective P.symm.toLinearMap := P.symm.injective
  have hcluster : {z | MapClusterPt z atTop d.iteration.point} =
      P.symm.toLinearMap '' Metric.sphere 0 1 := by
    rw [hdata.point, pulledPoints_def]
    exact clusterSet_ellipse P c.iteration.point hcircle
  obtain ⟨C, hC, hHolder⟩ := hholder
  let B := ‖P.toContinuousLinearMap‖ ^ 2 * C * ‖P.toContinuousLinearMap‖ ^ (1 / 2 : ℝ)
  have hB : 0 ≤ B := by positivity
  have hPositive : 0 < B + 1 := by linarith
  have hHalf : ∀ x y, ‖hessian d.iteration.objective x - hessian d.iteration.objective y‖ ≤
      (B + 1) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    intro x y
    rw [hObjective]
    have h := halfHolder_pullback c.iteration.objective c.objectiveContDiff P C hC hHolder x y
    have hLe : B ≤ B + 1 := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right hLe (Real.rpow_nonneg (norm_nonneg _) _))
  have hZero : d.iteration.objective 0 = 0 := by
    rw [hObjective]
    exact horigin.1
  have hUnique : ∀ x, (∀ y, d.iteration.objective x ≤ d.iteration.objective y) ↔ x = 0 := by
    rw [hObjective]
    exact horigin.2
  have hHalfPackage : ∃ C > 0, ∀ x y,
      ‖hessian d.iteration.objective x - hessian d.iteration.objective y‖ ≤
        C * ‖x - y‖ ^ (1 / 2 : ℝ) := ⟨B + 1, hPositive, hHalf⟩
  have hProperties : EllipseObjectiveProperties d.iteration P.symm.toLinearMap :=
    ⟨hInjective, ellipse_range_finrank _ hInjective, hcluster, hHalfPackage, hZero, hUnique⟩
  exact ⟨P, m, M, d, hP, hdata, hProperties⟩

/-- Helper for cor:identity-initialization: the actual NEW polar planar witness
admits the literal positive-root normalization with genuine matrix initialization I
and the complete centered ellipse/Holder/unique-origin package. -/
theorem polarPlanarIdentityInitialization (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ∃ νStar > baseAngle, ∃ κ > 0, ∃ j₀ : ℕ, 0 < j₀ ∧
      ∃ source : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
        PlanarCounterexample.SourceIdentity (Parameters.of j₀ νStar) κ source ∧
        ∃ (P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
          (m M : ℝ)
          (d : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate 2 m M c₁ c₂),
          P = (source.iteration.inverseHessianPosDef 0).sqrtEquiv ∧
            PullbackData source.iteration d.iteration P ∧
            EllipseObjectiveProperties d.iteration P.symm.toLinearMap := by
  have hhalfPos : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalfOne : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨νStar, hνStar, κ, hκ, j₀, hj₀, source, hsource, hproperties⟩ :=
    PlanarCounterexample.planarCounterexample c₁ c₂ (1 / 2)
      hc₁ hc₁lim hc₂lim hc₂ hhalfPos hhalfOne
  obtain ⟨P, m, M, d, hP, hdata, hellipse⟩ := normalizePlanarWithProperties source
    hproperties.origin hproperties.unique_minimizer hproperties.half_holder hproperties.cluster
  exact ⟨νStar, hνStar, κ, hκ, j₀, hj₀, source, hsource, P, m, M, d, hP, hdata, hellipse⟩

/-- Helper for cor:identity-initialization: the original identity-block
matrix extension sends the literal identity matrix to the literal identity. -/
theorem orthogonal_matrix_one {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] :
    DFP.OrthogonalSum.matrix (κ := κ) (1 : Matrix ι ι ℝ) =
      (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) := by
  exact DFP.OrthogonalSum.matrix_one

/-- Helper for cor:identity-initialization: isometric coordinate reindexing
preserves the literal canonical identity matrix. -/
theorem isometric_matrix_one {n : ℕ} {ι : Type*} [Fintype ι]
    (Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
        (Q.toContinuousLinearEquiv.symm.toContinuousLinearMap.pushforward 1) =
          (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hmap : Q.toContinuousLinearEquiv.symm.toContinuousLinearMap =
      (Q.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin n)) := by rfl
  have hidentity : Q.toContinuousLinearEquiv.symm.toContinuousLinearMap.pushforward 1 =
      (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    rw [hmap, ContinuousLinearMap.pushforward_one, Q.symm.adjoint_eq_symm]
    apply ContinuousLinearMap.ext
    intro z
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.coe_coe''] using
      Q.symm_apply_apply z
  rw [hidentity, map_one]

/-- Helper for cor:identity-initialization: the exact identity-block extension
and isometric coordinate reindexing data, valid for a matrix liminf certificate. -/
structure DimensionExtensionData (n : ℕ) (hn : 2 ≤ n)
    (source : DFP.InverseIteration (Fin 2)) (target : DFP.InverseIteration (Fin n)) : Prop where
  /-- Helper for cor:identity-initialization: precisely the identity-quadratic complementary
  block. -/
  objective : target.objective =
    EuclideanSpace.OrthogonalSum.Gradient.objective (κ := Fin (n - 2)) source.objective ∘
      OrthogonalExtension.coordinateEquiv n hn
  /-- Helper for cor:identity-initialization: source points have exactly zero complementary
  coordinates. -/
  point : ∀ k, target.point k = OrthogonalExtension.planeEmbedding n hn (source.point k)
  /-- Helper for cor:identity-initialization: all original positive step lengths are unchanged. -/
  stepLength : target.stepLength = source.stepLength
  /-- Helper for cor:identity-initialization: every matrix is the literal source identity-block
  extension. -/
  inverseHessian : ∀ k,
    target.inverseHessian k = OrthogonalExtension.extendedMatrix n hn (source.inverseHessian k)

/-- Helper for cor:identity-initialization: normalization is performed in the
source plane first, then its actual identity-initialized matrix iteration extends
to every larger dimension, with the full ellipse and positive liminf preserved. -/
theorem extendNormalizedPlanar (n : ℕ) (hn : 2 ≤ n) {m M c₁ c₂ : ℝ}
    (d : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate 2 m M c₁ c₂)
    (i : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hproperties : EllipseObjectiveProperties d.iteration i) :
    ∃ result : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n
        (min m 1) (max M 1) c₁ c₂,
      DimensionExtensionData n hn d.iteration result.iteration ∧
        EllipseObjectiveProperties result.iteration
          ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp i) := by
  let Q := OrthogonalExtension.coordinateEquiv n hn
  let itSum := d.iteration.orthogonalSum (κ := Fin (n - 2)) d.stepLengthPos
  have hStepSum : ∀ k, 0 < itSum.stepLength k := by
    simpa only [itSum, DFP.InverseIteration.orthogonalSum_stepLength] using d.stepLengthPos
  let it := itSum.pullback_linearIsometryEquiv hStepSum Q
  have hObjective : it.objective =
      EuclideanSpace.OrthogonalSum.Gradient.objective (κ := Fin (n - 2))
        d.iteration.objective ∘ Q := by
    simp only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_objective, itSum,
      DFP.InverseIteration.orthogonalSum_objective, DFP.OrthogonalSum.objective_eq]
  have hPoint (k : ℕ) : it.point k =
      OrthogonalExtension.planeEmbedding n hn (d.iteration.point k) := by
    simp only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_point, itSum,
      DFP.InverseIteration.orthogonalSum_point, OrthogonalExtension.embed_eq_leftEmbedding,
      OrthogonalExtension.planeEmbedding_apply, Q]
  have hAlpha : it.stepLength = d.iteration.stepLength := by
    simp only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_stepLength, itSum,
      DFP.InverseIteration.orthogonalSum_stepLength]
  have hMatrix (k : ℕ) : it.inverseHessian k =
      OrthogonalExtension.extendedMatrix n hn (d.iteration.inverseHessian k) := by
    simp only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_inverseHessian, itSum,
      DFP.InverseIteration.orthogonalSum_inverseHessian, OrthogonalExtension.extendedMatrix_def, Q]
  have hm : 0 < min m 1 := lt_min d.hessianLowerPos zero_lt_one
  have hmM : min m 1 ≤ max M 1 := (min_le_left _ _).trans
    (d.hessianLowerLeUpper.trans (le_max_left _ _))
  have hC2Sum : ContDiff ℝ 2 itSum.objective := by
    dsimp only [itSum]
    rw [DFP.InverseIteration.orthogonalSum_objective, DFP.OrthogonalSum.objective_eq]
    exact EuclideanSpace.OrthogonalSum.Gradient.contDiff_objective d.objectiveContDiff
  have hC2 : ContDiff ℝ 2 it.objective := by
    dsimp only [it]
    rw [DFP.InverseIteration.pullback_linearIsometryEquiv_objective]
    exact hC2Sum.comp Q.contDiff
  have hStep : ∀ k, 0 < it.stepLength k := by
    rw [hAlpha]
    exact d.stepLengthPos
  have hWide : HasHessianBounds (min m 1) (max M 1) d.iteration.objective :=
    PlanarCounterexample.hessianBounds_mono d.objectiveContDiff d.hessianBounds
      (min_le_left _ _) (le_max_left _ _)
  have hBoundsSum : HasHessianBounds (min m 1) (max M 1) itSum.objective := by
    dsimp only [itSum]
    rw [DFP.InverseIteration.orthogonalSum_objective, DFP.OrthogonalSum.objective_eq]
    exact EuclideanSpace.OrthogonalSum.Gradient.hasHessianBounds_objective
      d.objectiveContDiff hWide (min_le_right _ _) (le_max_right _ _)
  have hGradientDiffSum : Differentiable ℝ (gradient itSum.objective) :=
    (hC2Sum.gradient_succ (n := 1)).differentiable_one
  have hMnonneg : 0 ≤ max M 1 := zero_le_one.trans (le_max_right _ _)
  have hBounds : HasHessianBounds (min m 1) (max M 1) it.objective := by
    dsimp only [it]
    rw [DFP.InverseIteration.pullback_linearIsometryEquiv_objective]
    exact hBoundsSum.comp_linearIsometryEquiv Q hGradientDiffSum hm.le hMnonneg
  have hStrongSum (k : ℕ) : LineSearch.IsStrongWolfe c₁ c₂ itSum.objective
      (itSum.point k) (itSum.point (k + 1) - itSum.point k) := by
    have h := (LineSearch.IsStrongWolfe.orthogonalSum_iff (κ := Fin (n - 2))).mpr
      (d.strongWolfe k)
    simpa only [itSum, DFP.InverseIteration.orthogonalSum_objective,
      DFP.InverseIteration.orthogonalSum_point, DFP.OrthogonalSum.objective_eq,
      OrthogonalExtension.embed_eq_leftEmbedding, OrthogonalExtension.leftEmbedding_apply,
      map_sub] using h
  have hStrong (k : ℕ) : LineSearch.IsStrongWolfe c₁ c₂ it.objective
      (it.point k) (it.point (k + 1) - it.point k) := by
    have h := (hStrongSum k).comp_linearIsometryEquiv Q
    simpa only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_objective,
      DFP.InverseIteration.pullback_linearIsometryEquiv_point, map_sub] using h
  have hInitial : it.inverseHessian 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    dsimp only [it]
    rw [DFP.InverseIteration.pullback_linearIsometryEquiv_inverseHessian]
    dsimp only [itSum]
    rw [DFP.InverseIteration.orthogonalSum_inverseHessian, d.initialInverseHessian_eq_one,
      orthogonal_matrix_one, map_one]
    exact isometric_matrix_one Q
  have hNorm (k : ℕ) : ‖DFP.gradients it.objective it.point k‖ =
      ‖DFP.gradients d.iteration.objective d.iteration.point k‖ := by
    simp only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_gradients,
      Q.symm.norm_map, itSum, DFP.InverseIteration.orthogonalSum_gradients,
      DFP.OrthogonalSum.norm_embed]
  have hLiminf : 0 < liminf (fun k ↦ ‖DFP.gradients it.objective it.point k‖) atTop := by
    simpa only [hNorm] using d.gradientNormLiminfPos
  have hTail : ∃ δ > 0, ∀ᶠ k in atTop, δ ≤ ‖DFP.gradients it.objective it.point k‖ := by
    simpa only [hNorm] using d.gradientNormEventuallyPositive
  have hPointFun : it.point = OrthogonalExtension.planeEmbedding n hn ∘ d.iteration.point := by
    funext k
    exact hPoint k
  have hCluster : {z | MapClusterPt z atTop it.point} =
      ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp i) '' Metric.sphere 0 1 := by
    rw [hPointFun, OrthogonalExtension.clusterSet_isometric_embedding,
      hproperties.cluster, Set.image_image]
    rfl
  have hInjective : Function.Injective
      ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp i) :=
    (OrthogonalExtension.planeEmbedding n hn).injective.comp hproperties.injective
  have hOriginSum := OrthogonalExtension.objective_orthogonal_unique_origin
    (κ := Fin (n - 2)) hproperties.origin hproperties.unique_minimizer
  have hOrigin := OrthogonalExtension.objective_isometric_unique_origin Q
    hOriginSum.1 hOriginSum.2
  have hZero : it.objective 0 = 0 := by
    rw [hObjective]
    exact hOrigin.1
  have hUnique : ∀ x, (∀ y, it.objective x ≤ it.objective y) ↔ x = 0 := by
    rw [hObjective]
    exact hOrigin.2
  obtain ⟨C, hC, hHolder⟩ := hproperties.half_holder
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hHolderSum : ∀ x y,
      ‖hessian (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := Fin (n - 2))
        d.iteration.objective) x -
        hessian (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := Fin (n - 2))
          d.iteration.objective) y‖ ≤ C * ‖x - y‖ ^ (1 / 2 : ℝ) :=
    EuclideanSpace.OrthogonalSum.Gradient.hessianHolder_objective
      d.objectiveContDiff hC.le hhalf hHolder
  have hHolderFinal : ∀ x y, ‖hessian it.objective x - hessian it.objective y‖ ≤
      C * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    rw [hObjective]
    exact OrthogonalExtension.hessian_holder_isometric
      (EuclideanSpace.OrthogonalSum.Gradient.contDiff_objective d.objectiveContDiff) Q hHolderSum
  have hHolderPackage : ∃ C > 0, ∀ x y,
      ‖hessian it.objective x - hessian it.objective y‖ ≤ C * ‖x - y‖ ^ (1 / 2 : ℝ) :=
    ⟨C, hC, hHolderFinal⟩
  have hProperties : EllipseObjectiveProperties it
      ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp i) :=
    ⟨hInjective, ellipse_range_finrank _ hInjective, hCluster, hHolderPackage, hZero, hUnique⟩
  let result : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n
      (min m 1) (max M 1) c₁ c₂ := {
    iteration := it
    c₁_pos := d.c₁_pos
    c₁_lt_c₂ := d.c₁_lt_c₂
    c₂_lt_one := d.c₂_lt_one
    hessianLowerPos := hm
    hessianLowerLeUpper := hmM
    objectiveContDiff := hC2
    stepLengthPos := hStep
    hessianBounds := hBounds
    strongWolfe := hStrong
    initialInverseHessian_eq_one := hInitial
    gradientNormLiminfPos := hLiminf
    gradientNormEventuallyPositive := hTail
  }
  have hIt : result.iteration = it := rfl
  refine ⟨result, ?_, ?_⟩
  · rw [hIt]
    exact ⟨hObjective, hPoint, hAlpha, hMatrix⟩
  · rw [hIt]
    exact hProperties

/-- Helper for cor:identity-initialization: the canonical source matrix root
is a positive operator, as well as self-adjoint and invertible. -/
theorem positiveRoot_isPositive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    hA.sqrtEquiv.toContinuousLinearMap.IsPositive := by
  rw [hA.sqrtEquiv_toContinuousLinearMap]
  exact Matrix.isPositive_toEuclideanCLM_iff.mpr hA.cfcSqrt.posSemidef

/-- cor:identity-initialization: for every source Wolfe pair and every n≥2,
the NEW polar witness is first normalized by its literal positive planar root
P=H₀^(1/2), then extended by the identity quadratic block. The resulting
actual canonical matrix iteration starts at I, obeys the same strong Wolfe
pair and positive original alpha sequence, has positive gradient-norm liminf
and positive global example-dependent Hessian bounds, and its complete
cluster set is the centered injective linear image of the source unit circle.
The objective has global half-Hölder Hessian, unique origin minimum and value zero.
All original source data and both exact transports remain explicit. -/
theorem polarIdentityInitialization (n : ℕ) (hn : 2 ≤ n) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ∃ νStar > baseAngle, ∃ κ > 0, ∃ j₀ : ℕ, 0 < j₀ ∧
      ∃ source : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
        PlanarCounterexample.SourceIdentity (Parameters.of j₀ νStar) κ source ∧
        ∃ (P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
          (m M : ℝ)
          (planar : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate 2 m M c₁ c₂),
          P = (source.iteration.inverseHessianPosDef 0).sqrtEquiv ∧
            PullbackData source.iteration planar.iteration P ∧
            ∃ result : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n
                (min m 1) (max M 1) c₁ c₂,
              DimensionExtensionData n hn planar.iteration result.iteration ∧
                EllipseObjectiveProperties result.iteration
                  ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp
                    P.symm.toLinearMap) := by
  obtain ⟨νStar, hνStar, κ, hκ, j₀, hj₀, source, hsource,
    P, m, M, planar, hP, hdata, hproperties⟩ :=
      polarPlanarIdentityInitialization c₁ c₂ hc₁ hc₁lim hc₂lim hc₂
  obtain ⟨result, hextended, hfinal⟩ := extendNormalizedPlanar n hn planar
    P.symm.toLinearMap hproperties
  exact ⟨νStar, hνStar, κ, hκ, j₀, hj₀, source, hsource,
    P, m, M, planar, hP, hdata, result, hextended, hfinal⟩

/-- Helper for cor:identity-initialization: the standard matrix-certificate
form of the actual source corollary retains the complete centered two-dimensional
ellipse and objective regularity without imposing a transformed gradient limit. -/
theorem existsIdentityInitializedCounterexample (n : ℕ) (hn : 2 ≤ n) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ m ≤ M ∧
      ∃ result : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n m M c₁ c₂,
        ∃ i : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
          EllipseObjectiveProperties result.iteration i := by
  obtain ⟨νStar, _, κ, _, j₀, _, source, _, P, m, M, planar, _, _, result, _, hproperties⟩ :=
    polarIdentityInitialization n hn c₁ c₂ hc₁ hc₁lim hc₂lim hc₂
  have hUpperPos : 0 < max M 1 := result.hessianLowerPos.trans_le result.hessianLowerLeUpper
  exact ⟨min m 1, max M 1, result.hessianLowerPos, hUpperPos, result.hessianLowerLeUpper,
    result, (OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp P.symm.toLinearMap,
    hproperties⟩

end DFP.Polar.IdentityInitialization
