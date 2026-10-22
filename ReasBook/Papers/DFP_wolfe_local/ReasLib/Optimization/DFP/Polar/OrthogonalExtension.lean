/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.StrongWolfeCounterexample
public import ReasLib.Optimization.DFP.Polar.HolderSharpness
public import ReasLib.Optimization.DFP.Polar.PlanarCounterexample

public section

noncomputable section

open Filter
open scoped Topology Matrix

namespace DFP.Polar.OrthogonalExtension

/-- Helper for thm:main: the original left orthogonal embedding as a linear isometry. -/
def leftEmbedding {ι κ : Type*} [Fintype ι] [Fintype κ] :
    EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ (ι ⊕ κ) where
  toLinearMap := EuclideanSpace.OrthogonalSum.inl.toLinearMap
  norm_map' := EuclideanSpace.OrthogonalSum.norm_inl

/-- Helper for thm:main: the isometric left embedding is exactly the original zero-block map. -/
theorem leftEmbedding_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : EuclideanSpace ℝ ι) :
    leftEmbedding (κ := κ) x = EuclideanSpace.OrthogonalSum.inl x := by rfl

/-- Helper for thm:main: the DFP-facing left embedding agrees with the canonical
isometric embedding, without changing the zero complementary coordinates. -/
theorem embed_eq_leftEmbedding {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : EuclideanSpace ℝ ι) :
    (DFP.OrthogonalSum.embed x : EuclideanSpace ℝ (ι ⊕ κ)) = leftEmbedding x := by
  rw [leftEmbedding_apply]
  apply PiLp.ext
  intro i
  cases i with
  | inl i =>
    rw [DFP.OrthogonalSum.embed_apply_inl, EuclideanSpace.OrthogonalSum.inl_apply_inl]
  | inr i =>
    rw [DFP.OrthogonalSum.embed_apply_inr, EuclideanSpace.OrthogonalSum.inl_apply_inr]

/-- Helper for thm:main: the source adjoint congruence under a linear isometry
equivalence acts by inverse isometry, operator, and forward isometry. -/
theorem isometric_pullback_apply
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F) (x : E) :
    Q.toContinuousLinearEquiv.toContinuousLinearMap.pullback A x = Q.symm (A (Q x)) := by
  rw [ContinuousLinearMap.pullback_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Q.adjoint_eq_symm]
  rfl

/-- Helper for thm:main: isometric adjoint congruence preserves the operator norm,
including zero-dimensional complementary coordinate blocks. -/
theorem isometric_pullback_norm
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F) :
    ‖Q.toContinuousLinearEquiv.toContinuousLinearMap.pullback A‖ = ‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro x
    rw [isometric_pullback_apply, Q.symm.norm_map]
    simpa only [Q.norm_map] using A.le_opNorm (Q x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    have hconjugate : A y = Q
        (Q.toContinuousLinearEquiv.toContinuousLinearMap.pullback A (Q.symm y)) := by
      rw [isometric_pullback_apply, Q.apply_symm_apply, Q.apply_symm_apply]
    calc
      ‖A y‖ = ‖Q (Q.toContinuousLinearEquiv.toContinuousLinearMap.pullback A (Q.symm y))‖ :=
        congrArg norm hconjugate
      _ = ‖Q.toContinuousLinearEquiv.toContinuousLinearMap.pullback A (Q.symm y)‖ := Q.norm_map _
      _ ≤ ‖Q.toContinuousLinearEquiv.toContinuousLinearMap.pullback A‖ * ‖Q.symm y‖ :=
        (Q.toContinuousLinearEquiv.toContinuousLinearMap.pullback A).le_opNorm _
      _ = ‖Q.toContinuousLinearEquiv.toContinuousLinearMap.pullback A‖ * ‖y‖ := by
        rw [Q.symm.norm_map]

/-- Helper for thm:main: the Hessian of an isometric reindexing is the original
operator's adjoint congruence, with the function coercions normalized. -/
theorem hessian_isometric_comp
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (Q : E ≃ₗᵢ[ℝ] F) (x : E) :
    hessian (f ∘ Q) x = Q.toContinuousLinearEquiv.toContinuousLinearMap.pullback
      (hessian f (Q x)) := by
  have hdiff : Differentiable ℝ (gradient f) :=
    (hf.gradient_succ (n := 1)).differentiable_one
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
    Q.toContinuousLinearEquiv.comp_right_hessian f x (hdiff _)

/-- Helper for thm:main: the operator Hessian difference norm is unchanged by
the source isometric coordinate reindexing. -/
theorem hessian_isometric_sub_norm
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (Q : E ≃ₗᵢ[ℝ] F) (x y : E) :
    ‖hessian (f ∘ Q) x - hessian (f ∘ Q) y‖ = ‖hessian f (Q x) - hessian f (Q y)‖ := by
  rw [hessian_isometric_comp hf Q x, hessian_isometric_comp hf Q y,
    ← ContinuousLinearMap.pullback_sub, isometric_pullback_norm]

/-- Helper for thm:main: the exact operator distance of the Hessian from identity
is unchanged by the source isometric reindexing. -/
theorem hessian_isometric_sub_identity_norm
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (Q : E ≃ₗᵢ[ℝ] F) (x : E) :
    ‖hessian (f ∘ Q) x - 1‖ = ‖hessian f (Q x) - 1‖ := by
  have hone : Q.toContinuousLinearEquiv.toContinuousLinearMap.pullback 1 = 1 := by
    ext z
    rw [isometric_pullback_apply, one_apply_eq_self, Q.symm_apply_apply, one_apply_eq_self]
  rw [hessian_isometric_comp hf Q x, ← hone,
    ← ContinuousLinearMap.pullback_sub, isometric_pullback_norm]

/-- Helper for thm:main: adjoining the identity quadratic block does not increase
the operator norm of the Hessian's deviation from identity. -/
theorem hessian_orthogonal_sub_identity_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : ContDiff ℝ 2 f)
    (p : EuclideanSpace ℝ (ι ⊕ κ)) :
    ‖hessian (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f) p - 1‖ ≤
      ‖hessian f (EuclideanSpace.OrthogonalSum.Gradient.left p) - 1‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro w
  have hnorm :
      ‖(hessian (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f) p - 1) w‖ =
        ‖(hessian f (EuclideanSpace.OrthogonalSum.Gradient.left p) - 1)
          (EuclideanSpace.OrthogonalSum.Gradient.left w)‖ := by
    have hsquare := EuclideanSpace.OrthogonalSum.Gradient.norm_sq_eq_left_add_right
      ((hessian (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f) p - 1) w)
    simp only [sub_apply,
      EuclideanSpace.OrthogonalSum.Gradient.hessian_objective_apply hf, map_sub,
      EuclideanSpace.OrthogonalSum.Gradient.left_sumEquivProd_symm,
      EuclideanSpace.OrthogonalSum.Gradient.right_sumEquivProd_symm,
      one_apply_eq_self, sub_self, norm_zero, zero_pow two_ne_zero, add_zero] at hsquare
    simpa only [sub_apply, one_apply_eq_self,
      EuclideanSpace.OrthogonalSum.Gradient.hessian_objective_apply hf] using
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare
  rw [hnorm]
  exact ((hessian f (EuclideanSpace.OrthogonalSum.Gradient.left p) - 1).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (EuclideanSpace.OrthogonalSum.Gradient.norm_left_le w)
      (norm_nonneg _))

/-- Helper for thm:main: the source half-Hölder Hessian constant is preserved
exactly by an isometric reindexing. -/
theorem hessian_holder_isometric
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (Q : E ≃ₗᵢ[ℝ] F) {C β : ℝ}
    (h : ∀ x y, ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ β) (x y : E) :
    ‖hessian (f ∘ Q) x - hessian (f ∘ Q) y‖ ≤ C * ‖x - y‖ ^ β := by
  rw [hessian_isometric_sub_norm hf Q]
  simpa only [← map_sub, Q.norm_map] using h (Q x) (Q y)

/-- Helper for eq:counterexample-nonlipschitz: restriction to the original zero
complementary block transfers an initial-level Hölder bound back to the base objective. -/
theorem no_holder_initial_orthogonalSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : ContDiff ℝ 2 f) (x₀ : EuclideanSpace ℝ ι) (β : ℝ)
    (hno : ¬ ∃ C ≥ 0, ∀ x ∈ {x | f x ≤ f x₀}, ∀ y ∈ {x | f x ≤ f x₀},
      ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ β) :
    ¬ ∃ C ≥ 0,
      ∀ X ∈ {X | EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f X ≤
        EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f (leftEmbedding (κ := κ) x₀)},
      ∀ Y ∈ {X | EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f X ≤
        EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f (leftEmbedding (κ := κ) x₀)},
      ‖hessian (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f) X -
        hessian (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f) Y‖ ≤
          C * ‖X - Y‖ ^ β := by
  rintro ⟨C, hC, hholder⟩
  apply hno
  refine ⟨C, hC, ?_⟩
  intro x hx y hy
  have hx' : EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f (leftEmbedding x) ≤
      EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f (leftEmbedding (κ := κ) x₀) := by
    simpa only [Set.mem_setOf_eq, leftEmbedding_apply,
      EuclideanSpace.OrthogonalSum.Gradient.objective_inl] using hx
  have hy' : EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f (leftEmbedding y) ≤
      EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f (leftEmbedding (κ := κ) x₀) := by
    simpa only [Set.mem_setOf_eq, leftEmbedding_apply,
      EuclideanSpace.OrthogonalSum.Gradient.objective_inl] using hy
  have hbound := hholder (leftEmbedding x) hx' (leftEmbedding y) hy'
  have hrestriction := EuclideanSpace.OrthogonalSum.Gradient.norm_hessian_sub_le_objective
    (κ := κ) hf x y
  rw [← leftEmbedding_apply, ← leftEmbedding_apply] at hrestriction
  have hnorm : ‖leftEmbedding (κ := κ) x - leftEmbedding y‖ = ‖x - y‖ := by
    rw [← map_sub, (leftEmbedding (κ := κ)).norm_map]
  exact hrestriction.trans (hnorm ▸ hbound)

/-- Helper for eq:counterexample-nonlipschitz: isometric coordinates preserve
failure of every initial-level Hessian Hölder bound by restriction through the inverse map. -/
theorem no_holder_initial_isometric
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (Q : E ≃ₗᵢ[ℝ] F) (x₀ : F) (β : ℝ)
    (hno : ¬ ∃ C ≥ 0, ∀ x ∈ {x | f x ≤ f x₀}, ∀ y ∈ {x | f x ≤ f x₀},
      ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ β) :
    ¬ ∃ C ≥ 0, ∀ x ∈ {x | (f ∘ Q) x ≤ (f ∘ Q) (Q.symm x₀)},
      ∀ y ∈ {x | (f ∘ Q) x ≤ (f ∘ Q) (Q.symm x₀)},
        ‖hessian (f ∘ Q) x - hessian (f ∘ Q) y‖ ≤ C * ‖x - y‖ ^ β := by
  rintro ⟨C, hC, hholder⟩
  apply hno
  refine ⟨C, hC, ?_⟩
  intro x hx y hy
  have hx' : (f ∘ Q) (Q.symm x) ≤ (f ∘ Q) (Q.symm x₀) := by
    simpa only [Set.mem_setOf_eq, Function.comp_apply, Q.apply_symm_apply] using hx
  have hy' : (f ∘ Q) (Q.symm y) ≤ (f ∘ Q) (Q.symm x₀) := by
    simpa only [Set.mem_setOf_eq, Function.comp_apply, Q.apply_symm_apply] using hy
  have hbound := hholder (Q.symm x) hx' (Q.symm y) hy'
  simpa only [hessian_isometric_sub_norm hf Q, Q.apply_symm_apply, ← map_sub,
    Q.symm.norm_map] using hbound

/-- Helper for thm:main: an isometric embedding of a complete space transports
the existing cluster set exactly to its image. -/
theorem cluster_isometric_embedding
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (i : E →ₗᵢ[ℝ] F) (u : ℕ → E) (z : F) :
    MapClusterPt z atTop (i ∘ u) ↔ ∃ x, MapClusterPt x atTop u ∧ i x = z := by
  constructor
  · intro hz
    obtain ⟨j, hstrict, hj⟩ := hz.tendsto_subseq
    have hclosed := i.isometry.isClosedEmbedding.isClosed_range
    have hmem : z ∈ Set.range i := hclosed.mem_of_tendsto hj
      (Filter.Eventually.of_forall (fun n ↦ ⟨u (j n), rfl⟩))
    obtain ⟨x, rfl⟩ := hmem
    have hbase : Tendsto (u ∘ j) atTop (𝓝 x) := by
      apply i.isometry.tendsto_nhds_iff.mpr
      simpa only [Function.comp_assoc] using hj
    exact ⟨x, MapClusterPt.of_comp hstrict.tendsto_atTop hbase.mapClusterPt, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx.continuousAt_comp i.continuous.continuousAt

/-- Helper for thm:main: adjoining the identity quadratic block preserves the
origin normalization and unique global origin minimizer. -/
theorem objective_orthogonal_unique_origin {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : EuclideanSpace ℝ ι → ℝ} (hzero : f 0 = 0)
    (hunique : ∀ x, (∀ y, f x ≤ f y) ↔ x = 0) :
    EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f 0 = 0 ∧
      ∀ p, (∀ q, EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f p ≤
        EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f q) ↔ p = 0 := by
  have hmin : ∀ y, 0 ≤ f y := by
    have h := (hunique 0).mpr rfl
    simpa only [hzero] using h
  have hzero' : EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f 0 = 0 := by
    rw [EuclideanSpace.OrthogonalSum.Gradient.objective_apply, map_zero, map_zero,
      hzero, norm_zero]
    norm_num
  refine ⟨hzero', ?_⟩
  intro p
  constructor
  · intro hp
    have hle := hp 0
    rw [hzero', EuclideanSpace.OrthogonalSum.Gradient.objective_apply] at hle
    have hright : EuclideanSpace.OrthogonalSum.Gradient.right p = 0 := by
      apply norm_eq_zero.mp
      nlinarith [hmin (EuclideanSpace.OrthogonalSum.Gradient.left p),
        norm_nonneg (EuclideanSpace.OrthogonalSum.Gradient.right p)]
    have hleft : EuclideanSpace.OrthogonalSum.Gradient.left p = 0 := by
      apply (hunique _).mp
      intro y
      have hbase : f (EuclideanSpace.OrthogonalSum.Gradient.left p) ≤ 0 := by
        rw [hright, norm_zero] at hle
        linarith
      exact hbase.trans (hmin y)
    have hsquare := EuclideanSpace.OrthogonalSum.Gradient.norm_sq_eq_left_add_right p
    rw [hleft, hright, norm_zero] at hsquare
    simp only [norm_zero, zero_pow two_ne_zero, zero_add] at hsquare
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg p]
  · rintro rfl q
    rw [hzero', EuclideanSpace.OrthogonalSum.Gradient.objective_apply]
    exact add_nonneg (hmin _) (div_nonneg (sq_nonneg _) zero_le_two)

/-- Helper for thm:main: a reviewed supplied certificate can be placed on any
specified canonical iteration with the same objective and points and a supplied limit. -/
theorem certificateWithIteration {ι : Type*} [Fintype ι] {m M c₁ c₂ g : ℝ}
    (c : DFP.StrongWolfeCounterexample ι m M c₁ c₂) (it : DFP.InverseIteration ι)
    (hobjective : it.objective = c.iteration.objective) (hpoint : it.point = c.iteration.point)
    (hstep : ∀ k, 0 < it.stepLength k) (hg : 0 < g)
    (hlimit : Tendsto (fun k ↦ ‖DFP.gradients it.objective it.point k‖) atTop (𝓝 g)) :
    ∃ d : DFP.StrongWolfeCounterexample ι m M c₁ c₂,
      d.iteration = it ∧ d.gradientLimit = g := by
  have hcontDiff : ContDiff ℝ 2 it.objective := by
    rw [hobjective]
    exact c.objectiveContDiff
  have hbounds : HasHessianBounds m M it.objective := by
    rw [hobjective]
    exact c.hessianBounds
  have hweak : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ it.objective
      (it.point k) (it.point (k + 1) - it.point k) := by
    rw [hobjective, hpoint]
    exact c.weakWolfe
  have hstrong : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ it.objective
      (it.point k) (it.point (k + 1) - it.point k) := by
    rw [hobjective, hpoint]
    exact c.strongWolfe
  let d : DFP.StrongWolfeCounterexample ι m M c₁ c₂ := {
    toWolfeCounterexample := {
      iteration := it
      gradientLimit := g
      objectiveContDiff := hcontDiff
      stepLengthPos := hstep
      hessianBounds := hbounds
      weakWolfe := hweak
      gradientLimitPos := hg
      gradientNormTendsto := hlimit
    }
    strongWolfe := hstrong
  }
  exact ⟨d, rfl, rfl⟩

/-- Helper for thm:main: the reviewed extension certificate has the exact
canonical identity-block iteration, including all original step lengths and matrices. -/
theorem orthogonalSumWithIteration {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {m M c₁ c₂ : ℝ} (c : DFP.StrongWolfeCounterexample ι m M c₁ c₂)
    (hm : m ≤ 1) (hM : 1 ≤ M) :
    ∃ d : DFP.StrongWolfeCounterexample (ι ⊕ κ) m M c₁ c₂,
      d.iteration = c.iteration.orthogonalSum (κ := κ) c.stepLengthPos ∧
        d.gradientLimit = c.gradientLimit := by
  obtain ⟨d₀, hobjective, hpoint⟩ := c.orthogonalSumWithObjective (κ := κ) hm hM
  let it := c.iteration.orthogonalSum (κ := κ) c.stepLengthPos
  have hobjective' : it.objective = d₀.iteration.objective := by
    rw [hobjective]
    exact DFP.InverseIteration.orthogonalSum_objective c.iteration c.stepLengthPos
  have hpoint' : it.point = d₀.iteration.point := by
    funext k
    rw [hpoint]
    exact DFP.InverseIteration.orthogonalSum_point c.iteration c.stepLengthPos k
  have hstep : ∀ k, 0 < it.stepLength k := by
    rw [DFP.InverseIteration.orthogonalSum_stepLength]
    exact c.stepLengthPos
  have hlimit : Tendsto (fun k ↦ ‖DFP.gradients it.objective it.point k‖)
      atTop (𝓝 c.gradientLimit) := by
    rw [DFP.InverseIteration.orthogonalSum_gradients]
    simpa only [DFP.OrthogonalSum.norm_embed] using c.gradientNormTendsto
  exact certificateWithIteration d₀ it hobjective' hpoint' hstep c.gradientLimitPos hlimit

/-- Helper for thm:main: the reviewed isometric certificate can be chosen on
the exact canonical pullback iteration with unchanged step lengths. -/
theorem pullbackWithIteration {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {m M c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample ι m M c₁ c₂)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (hm : 0 ≤ m) (hM : 0 ≤ M) :
    ∃ d : DFP.StrongWolfeCounterexample κ m M c₁ c₂,
      d.iteration = c.iteration.pullback_linearIsometryEquiv c.stepLengthPos Q ∧
        d.gradientLimit = c.gradientLimit := by
  obtain ⟨d₀, hobjective, hpoint⟩ := c.pullbackWithObjective Q hm hM
  let it := c.iteration.pullback_linearIsometryEquiv c.stepLengthPos Q
  have hobjective' : it.objective = d₀.iteration.objective := by
    rw [hobjective]
    exact DFP.InverseIteration.pullback_linearIsometryEquiv_objective
      c.iteration c.stepLengthPos Q
  have hpoint' : it.point = d₀.iteration.point := by
    funext k
    rw [hpoint]
    exact DFP.InverseIteration.pullback_linearIsometryEquiv_point
      c.iteration c.stepLengthPos Q k
  have hstep : ∀ k, 0 < it.stepLength k := by
    rw [DFP.InverseIteration.pullback_linearIsometryEquiv_stepLength]
    exact c.stepLengthPos
  have hlimit : Tendsto (fun k ↦ ‖DFP.gradients it.objective it.point k‖)
      atTop (𝓝 c.gradientLimit) := by
    rw [DFP.InverseIteration.pullback_linearIsometryEquiv_gradients]
    simpa only [Q.symm.norm_map] using c.gradientNormTendsto
  exact certificateWithIteration d₀ it hobjective' hpoint' hstep c.gradientLimitPos hlimit

/-- Helper for thm:main: exact isometric Hessian bounds are preserved even when
the requested lower accuracy bound is negative. -/
theorem hessianBounds_isometric
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (Q : E ≃ₗᵢ[ℝ] F) {m M : ℝ}
    (h : HasHessianBounds m M f) : HasHessianBounds m M (f ∘ Q) := by
  apply HasHessianBounds.of_forall
  intro x
  apply HasHessianBoundsAt.of_quadraticForm
  · exact hessian_isSelfAdjoint (hf.comp Q.contDiff).contDiffAt
  · intro v
    have hquadratic := (h.at (Q x)).quadraticForm (Q v)
    have hinner : inner ℝ (Q.symm (hessian f (Q x) (Q v))) v =
        inner ℝ (hessian f (Q x) (Q v)) (Q v) := by
      simpa only [Q.symm_apply_apply] using
        Q.symm.inner_map_map (hessian f (Q x) (Q v)) (Q v)
    rw [hessian_isometric_comp hf Q, isometric_pullback_apply, hinner]
    simpa only [Q.norm_map] using hquadratic

/-- Helper for thm:main: the gradient of an isometrically reindexed objective
is exactly the inverse isometry applied to the original gradient. -/
theorem gradient_isometric_comp
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (f : F → ℝ) (Q : E ≃ₗᵢ[ℝ] F) (x : E) :
    gradient (f ∘ Q) x = Q.symm (gradient f (Q x)) := by
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, Q.adjoint_eq_symm,
    LinearIsometryEquiv.coe_coe''] using
    Q.toContinuousLinearEquiv.comp_right_gradient f x

/-- Helper for eq:counterexample-nonlipschitz: the source secant remainder norm
is unchanged on the original zero complementary block. -/
theorem norm_gradientRemainder_orthogonalSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : ContDiff ℝ 2 f) (x y : EuclideanSpace ℝ ι) :
    ‖gradient (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f) (leftEmbedding y) -
        gradient (EuclideanSpace.OrthogonalSum.Gradient.objective f) (leftEmbedding x) -
        hessian (EuclideanSpace.OrthogonalSum.Gradient.objective f) (leftEmbedding x)
          (leftEmbedding y - leftEmbedding x)‖ =
      ‖gradient f y - gradient f x - hessian f x (y - x)‖ := by
  have hdiff := hf.differentiable two_ne_zero
  rw [leftEmbedding_apply, leftEmbedding_apply]
  have hsquare := EuclideanSpace.OrthogonalSum.Gradient.norm_sq_eq_left_add_right
    (gradient (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f)
        (EuclideanSpace.OrthogonalSum.inl y) -
      gradient (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f)
        (EuclideanSpace.OrthogonalSum.inl x) -
      hessian (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f)
        (EuclideanSpace.OrthogonalSum.inl x)
        (EuclideanSpace.OrthogonalSum.inl y - EuclideanSpace.OrthogonalSum.inl x))
  simp only [EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl (hdiff x),
    EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl (hdiff y),
    EuclideanSpace.OrthogonalSum.Gradient.hessian_objective_apply hf, map_sub,
    EuclideanSpace.OrthogonalSum.Gradient.left_inl,
    EuclideanSpace.OrthogonalSum.Gradient.right_inl,
    EuclideanSpace.OrthogonalSum.Gradient.left_sumEquivProd_symm,
    EuclideanSpace.OrthogonalSum.Gradient.right_sumEquivProd_symm,
    sub_self, norm_zero, zero_pow two_ne_zero, add_zero] at hsquare
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl (hdiff x),
    EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl (hdiff y),
    EuclideanSpace.OrthogonalSum.Gradient.hessian_objective_apply hf, map_sub,
    EuclideanSpace.OrthogonalSum.Gradient.left_inl,
    EuclideanSpace.OrthogonalSum.Gradient.right_inl, sub_self] using hsquare

/-- Helper for eq:counterexample-nonlipschitz: the norm of the gradient secant
remainder is preserved exactly by the source isometric coordinate reindexing. -/
theorem norm_gradientRemainder_isometric
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (Q : E ≃ₗᵢ[ℝ] F) (x y : F) :
    ‖gradient (f ∘ Q) (Q.symm y) - gradient (f ∘ Q) (Q.symm x) -
        hessian (f ∘ Q) (Q.symm x) (Q.symm y - Q.symm x)‖ =
      ‖gradient f y - gradient f x - hessian f x (y - x)‖ := by
  have hnormalize :
      gradient (f ∘ Q) (Q.symm y) - gradient (f ∘ Q) (Q.symm x) -
        hessian (f ∘ Q) (Q.symm x) (Q.symm y - Q.symm x) =
      Q.symm (gradient f y - gradient f x - hessian f x (y - x)) := by
    simp only [gradient_isometric_comp, hessian_isometric_comp hf Q,
      isometric_pullback_apply, map_sub, Q.apply_symm_apply]
  rw [hnormalize, Q.symm.norm_map]

/-- Helper for thm:main: an isometric change of coordinates preserves the origin
normalization and unique origin minimizer of the supplied objective. -/
theorem objective_isometric_unique_origin
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (Q : E ≃ₗᵢ[ℝ] F) (hzero : f 0 = 0)
    (hunique : ∀ x, (∀ y, f x ≤ f y) ↔ x = 0) :
    (f ∘ Q) 0 = 0 ∧ ∀ x, (∀ y, (f ∘ Q) x ≤ (f ∘ Q) y) ↔ x = 0 := by
  have hzero' : (f ∘ Q) 0 = 0 := by simpa only [Function.comp_apply, map_zero] using hzero
  refine ⟨hzero', ?_⟩
  intro x
  constructor
  · intro hx
    have hbase : ∀ y, f (Q x) ≤ f y := by
      intro y
      simpa only [Function.comp_apply, Q.apply_symm_apply] using hx (Q.symm y)
    have hxzero := (hunique (Q x)).mp hbase
    exact Q.injective (hxzero.trans Q.map_zero.symm)
  · rintro rfl y
    simpa only [Function.comp_apply, map_zero] using (hunique 0).mpr rfl (Q y)

/-- Helper for eq:counterexample-nonlipschitz: the canonical even secant residual
ratio of an arbitrary supplied inverse DFP iteration. -/
def secantResidualRatio {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι)
    (β : ℝ) (j : ℕ) : ℝ :=
  ‖DFP.gradients it.objective it.point (2 * j + 1) -
      DFP.gradients it.objective it.point (2 * j) -
      hessian it.objective (it.point (2 * j)) (it.point (2 * j + 1) - it.point (2 * j))‖ /
    ‖it.point (2 * j + 1) - it.point (2 * j)‖ ^ (1 + β)

/-- Helper for eq:counterexample-nonlipschitz: the canonical even ratio formula. -/
theorem secantResidualRatio_apply {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι)
    (β : ℝ) (j : ℕ) : secantResidualRatio it β j =
      ‖DFP.gradients it.objective it.point (2 * j + 1) -
          DFP.gradients it.objective it.point (2 * j) -
          hessian it.objective (it.point (2 * j)) (it.point (2 * j + 1) - it.point (2 * j))‖ /
        ‖it.point (2 * j + 1) - it.point (2 * j)‖ ^ (1 + β) := by rfl

/-- Helper for eq:counterexample-nonlipschitz: the exact original residual ratio
is unchanged in the canonical identity-block DFP iteration. -/
theorem secantResidualRatio_orthogonalSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (it : DFP.InverseIteration ι) (hstep : ∀ k, 0 < it.stepLength k)
    (hf : ContDiff ℝ 2 it.objective) (β : ℝ) :
    secantResidualRatio (it.orthogonalSum (κ := κ) hstep) β = secantResidualRatio it β := by
  funext j
  simp only [secantResidualRatio_apply, DFP.gradients_apply,
    DFP.InverseIteration.orthogonalSum_objective, DFP.InverseIteration.orthogonalSum_point,
    DFP.OrthogonalSum.objective_eq, embed_eq_leftEmbedding]
  rw [norm_gradientRemainder_orthogonalSum hf, ← map_sub, leftEmbedding.norm_map]

/-- Helper for eq:counterexample-nonlipschitz: isometric reindexing of a canonical
DFP iteration preserves the source even residual ratios exactly. -/
theorem secantResidualRatio_isometric {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (it : DFP.InverseIteration ι)
    (hstep : ∀ k, 0 < it.stepLength k) (hf : ContDiff ℝ 2 it.objective)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (β : ℝ) :
    secantResidualRatio (it.pullback_linearIsometryEquiv hstep Q) β =
      secantResidualRatio it β := by
  funext j
  simp only [secantResidualRatio_apply, DFP.gradients_apply,
    DFP.InverseIteration.pullback_linearIsometryEquiv_objective,
    DFP.InverseIteration.pullback_linearIsometryEquiv_point]
  rw [norm_gradientRemainder_isometric hf, ← map_sub, Q.symm.norm_map]

/-- Helper for thm:main: the image formula for the cluster set under an
isometric embedding of the existing source trajectory. -/
theorem clusterSet_isometric_embedding
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (i : E →ₗᵢ[ℝ] F) (u : ℕ → E) :
    {z | MapClusterPt z atTop (i ∘ u)} = i '' {x | MapClusterPt x atTop u} := by
  ext z
  simpa only [Set.mem_image, Set.mem_setOf_eq] using cluster_isometric_embedding i u z

/-- Helper for thm:main and eq:counterexample-nonlipschitz: the initial level
of a supplied canonical DFP iteration in any finite Euclidean dimension. -/
def initialLevelSet {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι) :
    Set (EuclideanSpace ℝ ι) := {x | it.objective x ≤ it.objective (it.point 0)}

/-- Helper for thm:main: the original initial-level formula in arbitrary dimension. -/
theorem initialLevelSet_def {ι : Type*} [Fintype ι] (it : DFP.InverseIteration ι) :
    initialLevelSet it = {x | it.objective x ≤ it.objective (it.point 0)} := by rfl

/-- Helper for thm:main: all source analytic, geometric, and initial-level
sharpness properties attached to the same supplied certificate and embedded plane. -/
structure CounterexampleProperties {ι : Type*} [Fintype ι] (ε : ℝ) {c₁ c₂ : ℝ}
    (w : DFP.StrongWolfeCounterexample ι (1 / 2) (3 / 2) c₁ c₂)
    (i : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ ι) : Prop where
  /-- Helper for thm:main: the gradient-norm limit field is exactly one. -/
  gradientLimit : w.gradientLimit = 1
  /-- Helper for thm:main: the requested global operator deviation from identity. -/
  near_identity : ∀ x, ‖hessian w.iteration.objective x - 1‖ ≤ ε
  /-- Helper for thm:main: the same global near-identity spectral refinement. -/
  accuracy_bounds : HasHessianBounds (1 - ε) (1 + ε) w.iteration.objective
  /-- Helper for thm:main: global half-Hölder Hessian continuity. -/
  half_holder : ∃ H ≥ 0, ∀ x y,
    ‖hessian w.iteration.objective x - hessian w.iteration.objective y‖ ≤
      H * ‖x - y‖ ^ (1 / 2 : ℝ)
  /-- Helper for thm:main: the exact source normalization at the origin. -/
  origin : w.iteration.objective 0 = 0
  /-- Helper for thm:main: the origin is the unique global objective minimizer. -/
  unique_minimizer : ∀ x,
    (∀ y, w.iteration.objective x ≤ w.iteration.objective y) ↔ x = 0
  /-- Helper for thm:main: exactly the unit circle in the embedded plane is the cluster set. -/
  cluster : {x | MapClusterPt x atTop w.iteration.point} = i '' Metric.sphere 0 1
  /-- Helper for thm:main: no larger source Hölder exponent works on the initial level set. -/
  no_holder_initial : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
    ¬ ∃ L ≥ 0, ∀ x ∈ initialLevelSet w.iteration, ∀ y ∈ initialLevelSet w.iteration,
      ‖hessian w.iteration.objective x - hessian w.iteration.objective y‖ ≤
        L * ‖x - y‖ ^ β
  /-- Helper for eq:counterexample-nonlipschitz: the same actual even residual ratios diverge. -/
  residual_diverges : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
    Tendsto (secantResidualRatio w.iteration β) atTop atTop

/-- Helper for thm:main: the source limit field gives the exact gradient-norm limit one. -/
theorem CounterexampleProperties.gradientNorm_tendsto_one {ι : Type*} [Fintype ι]
    {ε c₁ c₂ : ℝ} {w : DFP.StrongWolfeCounterexample ι (1 / 2) (3 / 2) c₁ c₂}
    {i : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ ι}
    (h : CounterexampleProperties ε w i) :
    Tendsto (fun k ↦ ‖DFP.gradients w.iteration.objective w.iteration.point k‖)
      atTop (𝓝 1) := by
  simpa only [h.gradientLimit] using w.gradientNormTendsto

/-- Helper for thm:main: the exact source direct sum transports all analytic,
cluster, and initial-level sharpness properties of the supplied certificate. -/
theorem CounterexampleProperties.orthogonalSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {ε c₁ c₂ : ℝ}
    {c : DFP.StrongWolfeCounterexample ι (1 / 2) (3 / 2) c₁ c₂}
    {d : DFP.StrongWolfeCounterexample (ι ⊕ κ) (1 / 2) (3 / 2) c₁ c₂}
    {i : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ ι}
    (h : CounterexampleProperties ε c i) (hε : 0 ≤ ε)
    (hd : d.iteration = c.iteration.orthogonalSum (κ := κ) c.stepLengthPos)
    (hlimit : d.gradientLimit = c.gradientLimit) :
    CounterexampleProperties ε d ((leftEmbedding (κ := κ)).comp i) := by
  have hobjective : d.iteration.objective =
      EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) c.iteration.objective := by
    rw [hd, DFP.InverseIteration.orthogonalSum_objective, DFP.OrthogonalSum.objective_eq]
  have hpoint : d.iteration.point = leftEmbedding (κ := κ) ∘ c.iteration.point := by
    funext k
    rw [hd, DFP.InverseIteration.orthogonalSum_point, embed_eq_leftEmbedding]
    rfl
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hlower : 1 - ε ≤ 1 := by linarith
  have hupper : 1 ≤ 1 + ε := by linarith
  have horigin := objective_orthogonal_unique_origin (κ := κ) h.origin h.unique_minimizer
  constructor
  · exact hlimit.trans h.gradientLimit
  · intro x
    rw [hobjective]
    exact (hessian_orthogonal_sub_identity_norm_le c.objectiveContDiff x).trans
      (h.near_identity _)
  · rw [hobjective]
    exact EuclideanSpace.OrthogonalSum.Gradient.hasHessianBounds_objective
      c.objectiveContDiff h.accuracy_bounds hlower hupper
  · obtain ⟨H, hH, hholder⟩ := h.half_holder
    refine ⟨H, hH, ?_⟩
    rw [hobjective]
    exact EuclideanSpace.OrthogonalSum.Gradient.hessianHolder_objective
      c.objectiveContDiff hH hhalf hholder
  · rw [hobjective]
    exact horigin.1
  · rw [hobjective]
    exact horigin.2
  · rw [hpoint, clusterSet_isometric_embedding, h.cluster, Set.image_image]
    rfl
  · intro β hβ
    have hno := h.no_holder_initial β hβ
    rw [initialLevelSet_def] at hno
    rw [initialLevelSet_def, hobjective, hpoint, Function.comp_apply]
    exact no_holder_initial_orthogonalSum (κ := κ) c.objectiveContDiff
      (c.iteration.point 0) β hno
  · intro β hβ
    rw [hd, secantResidualRatio_orthogonalSum _ _ c.objectiveContDiff]
    exact h.residual_diverges β hβ

/-- Helper for thm:main: the exact isometric reindexing transports all source
properties, retaining the same Hölder constant and the same initial-level obstruction. -/
theorem CounterexampleProperties.pullback {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {ε c₁ c₂ : ℝ}
    {c : DFP.StrongWolfeCounterexample ι (1 / 2) (3 / 2) c₁ c₂}
    {d : DFP.StrongWolfeCounterexample κ (1 / 2) (3 / 2) c₁ c₂}
    {i : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ ι}
    (h : CounterexampleProperties ε c i)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hd : d.iteration = c.iteration.pullback_linearIsometryEquiv c.stepLengthPos Q)
    (hlimit : d.gradientLimit = c.gradientLimit) :
    CounterexampleProperties ε d (Q.symm.toLinearIsometry.comp i) := by
  have hobjective : d.iteration.objective = c.iteration.objective ∘ Q := by
    rw [hd, DFP.InverseIteration.pullback_linearIsometryEquiv_objective]
  have hpoint : d.iteration.point = Q.symm ∘ c.iteration.point := by
    funext k
    rw [hd, DFP.InverseIteration.pullback_linearIsometryEquiv_point]
    rfl
  have horigin := objective_isometric_unique_origin Q h.origin h.unique_minimizer
  constructor
  · exact hlimit.trans h.gradientLimit
  · intro x
    rw [hobjective, hessian_isometric_sub_identity_norm c.objectiveContDiff Q]
    exact h.near_identity _
  · rw [hobjective]
    exact hessianBounds_isometric c.objectiveContDiff Q h.accuracy_bounds
  · obtain ⟨H, hH, hholder⟩ := h.half_holder
    refine ⟨H, hH, ?_⟩
    rw [hobjective]
    exact hessian_holder_isometric c.objectiveContDiff Q hholder
  · rw [hobjective]
    exact horigin.1
  · rw [hobjective]
    exact horigin.2
  · have hcluster := clusterSet_isometric_embedding Q.symm.toLinearIsometry c.iteration.point
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at hcluster
    rw [hpoint, hcluster, h.cluster, Set.image_image]
    rfl
  · intro β hβ
    have hno := h.no_holder_initial β hβ
    rw [initialLevelSet_def] at hno
    rw [initialLevelSet_def, hobjective, hpoint, Function.comp_apply]
    exact no_holder_initial_isometric c.objectiveContDiff Q (c.iteration.point 0) β hno
  · intro β hβ
    rw [hd, secantResidualRatio_isometric _ _ c.objectiveContDiff Q]
    exact h.residual_diverges β hβ

/-- Helper for thm:main: widening the requested global spectral interval
preserves Hessian bounds without any sign restriction on its endpoints. -/
theorem hessianBounds_mono
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {m M a b : ℝ} (h : HasHessianBounds m M f)
    (ha : a ≤ m) (hb : M ≤ b) : HasHessianBounds a b f := by
  apply HasHessianBounds.of_forall
  intro x
  apply HasHessianBoundsAt.of_quadraticForm (hessian_isSelfAdjoint hf.contDiffAt)
  intro v
  have hbase := (h.at x).quadraticForm v
  exact ⟨(mul_le_mul_of_nonneg_right ha (sq_nonneg ‖v‖)).trans hbase.1,
    hbase.2.trans (mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖))⟩

/-- Helper for thm:main: the same source example meeting a smaller accuracy
also meets every larger requested near-identity accuracy. -/
theorem CounterexampleProperties.mono {ι : Type*} [Fintype ι] {δ ε c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample ι (1 / 2) (3 / 2) c₁ c₂}
    {i : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ ι}
    (h : CounterexampleProperties δ w i) (hδε : δ ≤ ε) : CounterexampleProperties ε w i := by
  have hnear (x) : ‖hessian w.iteration.objective x - 1‖ ≤ ε :=
    (h.near_identity x).trans hδε
  have hlower : 1 - ε ≤ 1 - δ := by linarith
  have hupper : 1 + δ ≤ 1 + ε := by linarith
  have hbounds := hessianBounds_mono w.objectiveContDiff h.accuracy_bounds hlower hupper
  exact ⟨h.gradientLimit, hnear, hbounds, h.half_holder, h.origin, h.unique_minimizer,
    h.cluster, h.no_holder_initial, h.residual_diverges⟩

/-- Helper for thm:main: the source dimension split remains valid at `n=2`,
where the complementary identity block has zero coordinates. -/
theorem splitDimension (n : ℕ) (hn : 2 ≤ n) : 2 + (n - 2) = n := by omega

/-- Helper for thm:main: the canonical orthogonal coordinate reindexing from
`Fin n` to the original plane and its `n−2` complementary coordinates. -/
def coordinateEquiv (n : ℕ) (hn : 2 ≤ n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2 ⊕ Fin (n - 2)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((finCongr (splitDimension n hn).symm).trans finSumFinEquiv.symm)

/-- Helper for thm:main: the exact canonical finite-coordinate reindexing formula. -/
theorem coordinateEquiv_def (n : ℕ) (hn : 2 ≤ n) :
    coordinateEquiv n hn = LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      ((finCongr (splitDimension n hn).symm).trans finSumFinEquiv.symm) := by rfl

/-- Helper for thm:main: the canonical isometric embedding of the original
two-dimensional source plane into `Fin n` coordinates. -/
def planeEmbedding (n : ℕ) (hn : 2 ≤ n) :
    EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (coordinateEquiv n hn).symm.toLinearIsometry.comp (leftEmbedding (κ := Fin (n - 2)))

/-- Helper for thm:main: the canonical embedded-plane map is zero-block inclusion
followed by the inverse finite-coordinate isometry. -/
theorem planeEmbedding_def (n : ℕ) (hn : 2 ≤ n) :
    planeEmbedding n hn =
      (coordinateEquiv n hn).symm.toLinearIsometry.comp (leftEmbedding (κ := Fin (n - 2))) := by
  rfl

/-- Helper for thm:main: evaluation of the actual canonical embedded-plane map. -/
theorem planeEmbedding_apply (n : ℕ) (hn : 2 ≤ n) (x : EuclideanSpace ℝ (Fin 2)) :
    planeEmbedding n hn x = (coordinateEquiv n hn).symm (leftEmbedding x) := by
  simp only [planeEmbedding_def, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry]

/-- Helper for thm:main: the source embedded circle lies in a subspace of
dimension exactly two, including when the ambient dimension equals two. -/
theorem planeEmbedding_range_finrank (n : ℕ) (hn : 2 ≤ n) :
    Module.finrank ℝ (LinearMap.range (planeEmbedding n hn).toLinearMap) = 2 := by
  rw [LinearMap.finrank_range_of_inj (planeEmbedding n hn).injective]
  exact finrank_euclideanSpace_fin

/-- Helper for thm:main: the actual inverse-Hessian extension is `H⊕I`,
expressed in the target's canonical `Fin n` coordinates. -/
def extendedMatrix (n : ℕ) (hn : 2 ≤ n) (H : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
      ((coordinateEquiv n hn).toContinuousLinearEquiv.symm.toContinuousLinearMap.pushforward
        ((Matrix.toEuclideanCLM :
          Matrix (Fin 2 ⊕ Fin (n - 2)) (Fin 2 ⊕ Fin (n - 2)) ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ (Fin 2 ⊕ Fin (n - 2)) →L[ℝ]
              EuclideanSpace ℝ (Fin 2 ⊕ Fin (n - 2))) (DFP.OrthogonalSum.matrix H)))

/-- Helper for thm:main: the exact identity-block and coordinate-congruence
formula defining the canonical extended matrix. -/
theorem extendedMatrix_def (n : ℕ) (hn : 2 ≤ n) (H : Matrix (Fin 2) (Fin 2) ℝ) :
    extendedMatrix n hn H =
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
          ((coordinateEquiv n hn).toContinuousLinearEquiv.symm.toContinuousLinearMap.pushforward
            ((Matrix.toEuclideanCLM :
              Matrix (Fin 2 ⊕ Fin (n - 2)) (Fin 2 ⊕ Fin (n - 2)) ℝ ≃⋆ₐ[ℝ]
                EuclideanSpace ℝ (Fin 2 ⊕ Fin (n - 2)) →L[ℝ]
                  EuclideanSpace ℝ (Fin 2 ⊕ Fin (n - 2))) (DFP.OrthogonalSum.matrix H))) := by
  rfl

/-- Helper for thm:main: the exact original source extension of a supplied
planar certificate, with the same objective, points, alpha, and matrix recurrence. -/
structure FinExtensionIdentity (n : ℕ) (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂)
    (w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂) : Prop where
  /-- Helper for thm:main: exactly the source orthogonal objective, canonically reindexed. -/
  objective : w.iteration.objective =
    EuclideanSpace.OrthogonalSum.Gradient.objective (κ := Fin (n - 2)) c.iteration.objective ∘
      coordinateEquiv n hn
  /-- Helper for thm:main: the original planar trajectory has zero complementary coordinates. -/
  point : ∀ k, w.iteration.point k = planeEmbedding n hn (c.iteration.point k)
  /-- Helper for thm:main: every original step length is retained exactly. -/
  stepLength : w.iteration.stepLength = c.iteration.stepLength
  /-- Helper for thm:main: every inverse Hessian is the original identity-block extension. -/
  inverseHessian : ∀ k,
    w.iteration.inverseHessian k = extendedMatrix n hn (c.iteration.inverseHessian k)
  /-- Helper for thm:main: restriction of the extended objective recovers the original objective. -/
  objectiveOnPlane : ∀ x,
    w.iteration.objective (planeEmbedding n hn x) = c.iteration.objective x

/-- Helper for thm:main: all dimensions `n≥2` admit the exact source orthogonal
extension of any supplied planar certificate with all its source properties preserved. -/
theorem extendPlanarCertificate (n : ℕ) (hn : 2 ≤ n) {ε c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂)
    (h : CounterexampleProperties ε c LinearIsometry.id)
    (hε : 0 ≤ ε) :
    ∃ w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂,
      FinExtensionIdentity n hn c w ∧ CounterexampleProperties ε w (planeEmbedding n hn) := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hlower : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hupper : (1 : ℝ) ≤ 3 / 2 := by norm_num
  have hthree : (0 : ℝ) ≤ 3 / 2 := by norm_num
  obtain ⟨d, hd, hlimit⟩ := orthogonalSumWithIteration (κ := Fin (n - 2)) c hlower hupper
  have hdProperties := h.orthogonalSum hε hd hlimit
  let Q := coordinateEquiv n hn
  obtain ⟨w, hw, hwlimit⟩ := pullbackWithIteration d Q hhalf hthree
  have hwProperties := hdProperties.pullback Q hw hwlimit
  have hproperties : CounterexampleProperties ε w (planeEmbedding n hn) := by
    rw [planeEmbedding_def]
    simpa only [Q, LinearIsometry.comp_id] using hwProperties
  have hobjective : w.iteration.objective =
      EuclideanSpace.OrthogonalSum.Gradient.objective (κ := Fin (n - 2)) c.iteration.objective ∘
        coordinateEquiv n hn := by
    rw [hw, DFP.InverseIteration.pullback_linearIsometryEquiv_objective, hd,
      DFP.InverseIteration.orthogonalSum_objective, DFP.OrthogonalSum.objective_eq]
  have hpoint (k : ℕ) : w.iteration.point k = planeEmbedding n hn (c.iteration.point k) := by
    rw [hw, DFP.InverseIteration.pullback_linearIsometryEquiv_point, hd,
      DFP.InverseIteration.orthogonalSum_point, embed_eq_leftEmbedding, planeEmbedding_apply]
  have hstep : w.iteration.stepLength = c.iteration.stepLength := by
    rw [hw, DFP.InverseIteration.pullback_linearIsometryEquiv_stepLength, hd,
      DFP.InverseIteration.orthogonalSum_stepLength]
  have hmatrix (k : ℕ) :
      w.iteration.inverseHessian k = extendedMatrix n hn (c.iteration.inverseHessian k) := by
    rw [hw, DFP.InverseIteration.pullback_linearIsometryEquiv_inverseHessian, hd,
      DFP.InverseIteration.orthogonalSum_inverseHessian, extendedMatrix_def]
  have hplane (x : EuclideanSpace ℝ (Fin 2)) :
      w.iteration.objective (planeEmbedding n hn x) = c.iteration.objective x := by
    rw [hobjective, Function.comp_apply, planeEmbedding_apply,
      (coordinateEquiv n hn).apply_symm_apply, leftEmbedding_apply,
      EuclideanSpace.OrthogonalSum.Gradient.objective_inl]
  exact ⟨w, ⟨hobjective, hpoint, hstep, hmatrix, hplane⟩, hproperties⟩

/-- Helper for thm:main: the exact finite extension has the original gradient
sequence embedded into the source plane at every index. -/
theorem FinExtensionIdentity.gradients {n : ℕ} {hn : 2 ≤ n} {c₁ c₂ : ℝ}
    {c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    {w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂}
    (h : FinExtensionIdentity n hn c w) (k : ℕ) :
    DFP.gradients w.iteration.objective w.iteration.point k =
      planeEmbedding n hn (DFP.gradients c.iteration.objective c.iteration.point k) := by
  rw [DFP.gradients_apply, DFP.gradients_apply, h.objective, h.point,
    planeEmbedding_apply, gradient_isometric_comp, (coordinateEquiv n hn).apply_symm_apply,
    leftEmbedding_apply,
    EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl (c.iteration.differentiableAt k),
    planeEmbedding_apply, leftEmbedding_apply]

/-- Helper for thm:main: all actual gradient norms are retained exactly by
the canonical source extension, before taking their common limit one. -/
theorem FinExtensionIdentity.gradient_norm {n : ℕ} {hn : 2 ≤ n} {c₁ c₂ : ℝ}
    {c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    {w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂}
    (h : FinExtensionIdentity n hn c w) (k : ℕ) :
    ‖DFP.gradients w.iteration.objective w.iteration.point k‖ =
      ‖DFP.gradients c.iteration.objective c.iteration.point k‖ := by
  rw [h.gradients, (planeEmbedding n hn).norm_map]

/-- Helper for eq:counterexample-nonlipschitz: the finite-dimensional ratio
interface is the accepted planar source ratio on the original plane. -/
theorem secantResidualRatio_eq_planar (it : DFP.InverseIteration (Fin 2)) (β : ℝ) :
    secantResidualRatio it β = PlanarCounterexample.secantResidualRatio it β := by
  funext j
  rw [secantResidualRatio_apply, PlanarCounterexample.secantResidualRatio_def,
    DFP.gradientChanges_apply]

/-- Helper for thm:main: the initial-level interface retains exactly the
accepted original planar initial level, with no trajectory truncation. -/
theorem initialLevelSet_eq_planar (it : DFP.InverseIteration (Fin 2)) :
    initialLevelSet it = PlanarCounterexample.initialLevelSet it := by
  rw [initialLevelSet_def, PlanarCounterexample.initialLevelSet_def]

/-- Helper for thm:main: the newly proved polar planar properties enter the
dimension-independent source interface with the identity embedding of the plane. -/
theorem counterexampleProperties_of_planar {ε c₁ c₂ : ℝ}
    {c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : PlanarCounterexample.CounterexampleProperties ε c) :
    CounterexampleProperties ε c LinearIsometry.id := by
  constructor
  · exact h.gradientLimit
  · exact h.near_identity
  · exact h.accuracy_bounds
  · exact h.half_holder
  · exact h.origin
  · exact h.unique_minimizer
  · rw [LinearIsometry.coe_id, Set.image_id]
    ext x
    simpa only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right] using h.cluster x
  · intro β hβ
    rw [initialLevelSet_eq_planar]
    exact h.no_holder_initial β hβ
  · intro β hβ
    rw [secantResidualRatio_eq_planar]
    exact h.residual_diverges β hβ

/-- Helper for thm:main: the all-dimensional objective is exactly the original
polar objective plus the identity quadratic block in canonical source coordinates. -/
theorem FinExtensionIdentity.source_objective {n : ℕ} {hn : 2 ≤ n} {p : Parameters}
    {κ c₁ c₂ : ℝ} {c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    {w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂}
    (h : FinExtensionIdentity n hn c w) (hsource : PlanarCounterexample.SourceIdentity p κ c) :
    w.iteration.objective = EuclideanSpace.OrthogonalSum.Gradient.objective
      (κ := Fin (n - 2)) (InterpolationSum.polarObjective p κ) ∘ coordinateEquiv n hn := by
  rw [h.objective, hsource.objective]

/-- Helper for thm:main: the all-dimensional points are exactly the original
polar points embedded in the canonical two-dimensional subspace. -/
theorem FinExtensionIdentity.source_point {n : ℕ} {hn : 2 ≤ n} {p : Parameters}
    {κ c₁ c₂ : ℝ} {c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    {w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂}
    (h : FinExtensionIdentity n hn c w) (hsource : PlanarCounterexample.SourceIdentity p κ c)
    (k : ℕ) : w.iteration.point k = planeEmbedding n hn (p.point k) := by
  rw [h.point, hsource.point]

/-- Helper for thm:main: all original polar step lengths are retained by
the source construction in every dimension. -/
theorem FinExtensionIdentity.source_stepLength {n : ℕ} {hn : 2 ≤ n} {p : Parameters}
    {κ c₁ c₂ : ℝ} {c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    {w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂}
    (h : FinExtensionIdentity n hn c w) (hsource : PlanarCounterexample.SourceIdentity p κ c) :
    w.iteration.stepLength = PhysicalRealization.prescribedStepLength p := by
  rw [h.stepLength, hsource.stepLength]

/-- Helper for thm:main: the actual matrix-valued inverse DFP sequence is
the original polar physical matrix extended by identity and canonically reindexed. -/
theorem FinExtensionIdentity.source_inverseHessian {n : ℕ} {hn : 2 ≤ n} {p : Parameters}
    {κ c₁ c₂ : ℝ} {c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    {w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂}
    (h : FinExtensionIdentity n hn c w) (hsource : PlanarCounterexample.SourceIdentity p κ c)
    (k : ℕ) : w.iteration.inverseHessian k = extendedMatrix n hn (p.inverseHessian k) := by
  rw [h.inverseHessian, hsource.inverseHessian]

/-- Helper for thm:main: the actual polar gradients are embedded without
changing any of their Euclidean norms. -/
theorem FinExtensionIdentity.source_gradients {n : ℕ} {hn : 2 ≤ n} {p : Parameters}
    {κ c₁ c₂ : ℝ} {c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    {w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂}
    (h : FinExtensionIdentity n hn c w) (hsource : PlanarCounterexample.SourceIdentity p κ c)
    (k : ℕ) : DFP.gradients w.iteration.objective w.iteration.point k =
      planeEmbedding n hn (p.gradient k) := by
  rw [h.gradients, hsource.gradients]

/-- Helper for thm:main: one actual new polar family extends into every dimension
at least two, with its source parameter and support chosen before every accuracy and
with one starting threshold before every later fresh initialization and dimension. -/
theorem polarCounterexampleFamily (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ∃ νStar > baseAngle, ∃ κ > 0, ∀ ε : ℝ, 0 < ε →
      ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        ∃ c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
          PlanarCounterexample.SourceIdentity (Parameters.of j₀ νStar) κ c ∧
            CounterexampleProperties ε c LinearIsometry.id ∧
            ∀ n : ℕ, ∀ hn : 2 ≤ n,
              ∃ w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂,
                FinExtensionIdentity n hn c w ∧
                  CounterexampleProperties ε w (planeEmbedding n hn) := by
  obtain ⟨νStar, hνStar, κ, hκ, haccuracy⟩ :=
    PlanarCounterexample.planarCounterexampleFamily c₁ c₂ hc₁ hc₁lim hc₂lim hc₂
  refine ⟨νStar, hνStar, κ, hκ, ?_⟩
  intro ε hε
  let δ := min ε (1 / 2)
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalfOne : (1 / 2 : ℝ) < 1 := by norm_num
  have hδ : 0 < δ := lt_min hε hhalf
  have hδone : δ < 1 := (min_le_right ε (1 / 2)).trans_lt hhalfOne
  have hδε : δ ≤ ε := min_le_left _ _
  obtain ⟨J, hJ, hfamily⟩ := haccuracy δ hδ hδone
  refine ⟨J, hJ, ?_⟩
  intro j₀ hj₀
  obtain ⟨c, hsource, hproperties⟩ := hfamily j₀ hj₀
  have hbase := (counterexampleProperties_of_planar hproperties).mono hδε
  refine ⟨c, hsource, hbase, ?_⟩
  intro n hn
  exact extendPlanarCertificate n hn c hbase hε.le

/-- thm:main and eq:counterexample-nonlipschitz (all dimensions): the newly
constructed polar counterexample extends to every `Fin n`, `n≥2`, by exactly the
source orthogonal objective and identity-block inverse DFP matrices, with unchanged
step lengths. It retains gradient-norm limit one, the fixed global Hessian bounds,
arbitrary requested near-identity accuracy, global half-Hölder Hessian, unique origin
minimum and normalization, the exact embedded unit circle cluster set, and failure of
every larger source Hölder exponent on its original initial level set. -/
theorem polarCounterexample (n : ℕ) (hn : 2 ≤ n) (c₁ c₂ ε : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1)
    (hε : 0 < ε) :
    ∃ w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂,
      CounterexampleProperties ε w (planeEmbedding n hn) ∧
        ∃ νStar > baseAngle, ∃ κ > 0, ∃ j₀ : ℕ, 0 < j₀ ∧
          ∃ c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
            PlanarCounterexample.SourceIdentity (Parameters.of j₀ νStar) κ c ∧
              FinExtensionIdentity n hn c w := by
  obtain ⟨νStar, hνStar, κ, hκ, haccuracy⟩ :=
    polarCounterexampleFamily c₁ c₂ hc₁ hc₁lim hc₂lim hc₂
  obtain ⟨J, hJ, hfamily⟩ := haccuracy ε hε
  obtain ⟨c, hsource, _, hdimensions⟩ := hfamily J le_rfl
  obtain ⟨w, hextension, hproperties⟩ := hdimensions n hn
  exact ⟨w, hproperties, νStar, hνStar, κ, hκ, J, hJ, c, hsource, hextension⟩

end DFP.Polar.OrthogonalExtension
