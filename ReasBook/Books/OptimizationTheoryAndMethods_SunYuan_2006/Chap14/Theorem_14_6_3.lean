/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_21
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_6_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Exercise_14_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_6

noncomputable section

open scoped Subgradient ClarkeDifferential

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ValuePoint" => EuclideanSpace ℝ (Fin m)
local notation "DualValue" => StrongDual ℝ ValuePoint

-- Domain-style sampling:
-- * primary domain: composite nonsmooth optimization problems in Section 14.6;
-- * inspected owner/canonical surfaces: `CompositeNonsmoothOptimizationProblem`,
--   `CompositeNonsmoothOptimizationProblem.objective`,
--   `CompositeNonsmoothOptimizationProblem.coe_apply`, `IsLocalMin`, `subdifferential`;
-- * source-facing layer kept here: the local-minimizer stationarity statement for the
--   Chapter 14.6 composite-problem owner;
-- * core/canonical owners reused here: `CompositeNonsmoothOptimizationProblem`,
--   `IsLocalMin`, `subdifferential`, and `ContinuousLinearMap.adjoint`;
-- * bridge/view companion below: the previous finite-dimensional Hilbert-space formulation;
-- * primitive data are exactly the owner fields of `CompositeNonsmoothOptimizationProblem`,
--   while the objective and Section 14.6 regularity hypotheses are derived API.

/-- Helper for Chapter14 Theorem 14.6.3: the convex subdifferential `∂ g(y)` is an intersection
of closed evaluation halfspaces, hence it is closed. -/
lemma isClosed_subdifferential
    (g : ValuePoint → ℝ) (y : ValuePoint) :
    IsClosed (∂ g y) := by
  -- Rewrite the subdifferential as an intersection of evaluation halfspaces.
  rw [show (∂ g y) = ⋂ z : ValuePoint, {ξ : DualValue | ξ (z - y) ≤ g z - g y} by
    ext ξ
    simp [mem_subdifferential_iff, ge_iff_le, sub_eq_add_neg, add_comm]]
  -- Each evaluation halfspace is closed because evaluation on the dual is continuous.
  refine isClosed_iInter fun z ↦ ?_
  have hcont : Continuous fun ξ : DualValue ↦ ξ (z - y) := by
    continuity
  refine isClosed_le ?_ continuous_const
  exact hcont

/-- Helper for Chapter14 Theorem 14.6.3: the subdifferential `∂ g(y)` is convex because each
defining support inequality is affine in the dual variable. -/
lemma convex_subdifferential
    (g : ValuePoint → ℝ) (y : ValuePoint) :
    Convex ℝ (∂ g y) := by
  -- Rewrite the subdifferential as an intersection of affine halfspaces in the dual variable.
  rw [show (∂ g y) = ⋂ z : ValuePoint, {ξ : DualValue | ξ (z - y) ≤ g z - g y} by
    ext ξ
    simp [mem_subdifferential_iff, ge_iff_le, sub_eq_add_neg, add_comm]]
  -- Each halfspace is convex because evaluation at a fixed vector is linear.
  refine convex_iInter fun z ↦ ?_
  simpa using
    convex_halfSpace_le
      (show IsLinearMap ℝ (fun ξ : DualValue ↦ ξ (z - y)) by
        refine ⟨?_, ?_⟩
        · intro ξ₁ ξ₂
          rfl
        · intro a ξ
          rfl)
      (g z - g y)

/-- Helper for Chapter14 Theorem 14.6.3: under convexity and local Lipschitz regularity, the
subdifferential `∂ g(y)` is nonempty. -/
lemma subdifferential_nonempty_of_convexOn_of_locallyLipschitzAt
    (g : ValuePoint → ℝ) (y : ValuePoint)
    (h_convex : ConvexOn ℝ Set.univ g)
    (h_local : LocallyLipschitzAt g y) :
    (∂ g y).Nonempty := by
  -- Identify the convex subdifferential with the Clarke differential and reuse its nonemptiness.
  simpa [clarkeDifferential_eq_subdifferential_of_convexOn_of_locallyLipschitzAt
    g y h_convex h_local] using
    clarkeDifferential_nonempty_of_locallyLipschitzAt g y h_local

/-- Helper for Chapter14 Theorem 14.6.3: in the finite-dimensional Euclidean codomain, local
Lipschitz control bounds every subgradient norm, so `∂ g(y)` is compact. -/
lemma isCompact_subdifferential_of_convexOn_of_locallyLipschitzAt
    (g : ValuePoint → ℝ) (y : ValuePoint)
    (h_convex : ConvexOn ℝ Set.univ g)
    (h_local : LocallyLipschitzAt g y) :
    IsCompact (∂ g y) := by
  rcases locallyLipschitzAt_iff.mp h_local with ⟨ε, hε, K, hK⟩
  letI : ProperSpace DualValue := FiniteDimensional.proper ℝ DualValue
  have hsubset :
      ∂ g y ⊆ Metric.closedBall (0 : DualValue) (K : ℝ) := by
    intro ξ hξ
    rw [Metric.mem_closedBall, dist_zero_right]
    have hξ_clarke : ξ ∈ (∂ᶜ g) y := by
      rw [clarkeDifferential_eq_subdifferential_of_convexOn_of_locallyLipschitzAt
        g y h_convex h_local]
      exact hξ
    exact norm_le_of_mem_clarkeDifferential_of_closedBallLipschitz
      g y K ⟨ε, hε, hK⟩ hξ_clarke
  -- The subdifferential is a closed subset of a compact closed ball in finite dimension.
  exact (isCompact_closedBall (x := (0 : DualValue)) (r := (K : ℝ))).of_isClosed_subset
    (isClosed_subdifferential g y) hsubset

/-- Helper for Chapter14 Theorem 14.6.3: a convex function on the whole Euclidean codomain is
locally Lipschitz at every point in the chapter's `LocallyLipschitzAt` owner. -/
lemma convexOn_univ_locallyLipschitzAt
    (g : ValuePoint → ℝ) (y : ValuePoint)
    (h_convex : ConvexOn ℝ Set.univ g) :
    LocallyLipschitzAt g y := by
  -- Convert mathlib's neighborhood-Lipschitz statement into the project's closed-ball owner.
  rcases (ConvexOn.locallyLipschitz h_convex) y with ⟨K, s, hs_mem, hK⟩
  rcases Metric.mem_nhds_iff.mp hs_mem with ⟨ε, hε_pos, hε_sub⟩
  refine locallyLipschitzAt_of_closedBall (K := K) ?_
  refine ⟨ε / 2, by linarith, ?_⟩
  exact hK.mono fun z hz ↦ hε_sub ((Metric.closedBall_subset_ball (by linarith)) hz)

/-- Helper for Chapter14 Theorem 14.6.3: vanishing of `lam.comp A` is equivalent to vanishing of
the adjoint applied to the Riesz representative of `lam`. -/
lemma comp_eq_zero_iff_adjoint_riesz_eq_zero
    (A : Point →L[ℝ] ValuePoint) (lam : DualValue) :
    lam.comp A = 0 ↔
      A.adjoint ((InnerProductSpace.toDual ℝ ValuePoint).symm lam) = (0 : Point) := by
  constructor
  · intro h_comp
    -- Push the adjoint equation through the Riesz map and compare the resulting functionals.
    apply (InnerProductSpace.toDual ℝ Point).injective
    ext x
    have hx : lam (A x) = 0 := by
      simpa using congrArg (fun T : Point →L[ℝ] ℝ ↦ T x) h_comp
    rw [InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDual_apply_apply]
    have hleft :
        inner ℝ (A.adjoint ((InnerProductSpace.toDual ℝ ValuePoint).symm lam)) x =
          inner ℝ ((InnerProductSpace.toDual ℝ ValuePoint).symm lam) (A x) := by
      simpa using
        ContinuousLinearMap.adjoint_inner_left
          A x ((InnerProductSpace.toDual ℝ ValuePoint).symm lam)
    have hright :
        inner ℝ ((InnerProductSpace.toDual ℝ ValuePoint).symm lam) (A x) = lam (A x) := by
      exact InnerProductSpace.toDual_symm_apply (x := A x) (y := lam)
    exact hleft.trans (hright.trans (hx.trans (by simp)))
  · intro h_adjoint
    -- Evaluate the adjoint equation on each test vector to recover the vanishing composition.
    apply ContinuousLinearMap.ext
    intro x
    have hright :
        lam (A x) = inner ℝ ((InnerProductSpace.toDual ℝ ValuePoint).symm lam) (A x) := by
      exact (InnerProductSpace.toDual_symm_apply (x := A x) (y := lam)).symm
    have hleft :
        inner ℝ ((InnerProductSpace.toDual ℝ ValuePoint).symm lam) (A x) =
          inner ℝ (A.adjoint ((InnerProductSpace.toDual ℝ ValuePoint).symm lam)) x := by
      simpa using
        (ContinuousLinearMap.adjoint_inner_left
          A x ((InnerProductSpace.toDual ℝ ValuePoint).symm lam)).symm
    exact hright.trans (hleft.trans (by simp [h_adjoint]))

/-- Helper for Chapter14 Theorem 14.6.3: when the inner map is `C¹`, the Chapter 14.1
chain-rule generator set is exactly the weak image of the pushed-forward outer subgradients. -/
lemma chainRuleGeneratorSet_eq_toWeakDual_image_comp_subdifferential
    (problem : CompositeNonsmoothOptimizationProblem n m) (xStar : Point) :
    chainRuleGeneratorSet problem.outerFunction problem.smoothMap xStar =
      StrongDual.toWeakDual ''
        ((fun lamStar : DualValue ↦ lamStar.comp (fderiv ℝ problem.smoothMap xStar)) ''
          (∂ problem.outerFunction (problem.smoothMap xStar))) := by
  let A : Point →L[ℝ] ValuePoint := fderiv ℝ problem.smoothMap xStar
  have h_outer_local :
      LocallyLipschitzAt problem.outerFunction (problem.smoothMap xStar) :=
    convexOn_univ_locallyLipschitzAt
      problem.outerFunction (problem.smoothMap xStar) problem.outerFunction_convex
  have h_outer_clarke :
      (∂ᶜ problem.outerFunction) (problem.smoothMap xStar) =
        ∂ problem.outerFunction (problem.smoothMap xStar) :=
    clarkeDifferential_eq_subdifferential_of_convexOn_of_locallyLipschitzAt
      problem.outerFunction (problem.smoothMap xStar)
      problem.outerFunction_convex h_outer_local
  have h_component_contDiff :
      ∀ i : Fin m, ContDiff ℝ 1 (fun y : Point ↦ problem.smoothMap y i) := by
    intro i
    exact ((contDiff_piLp (p := (2 : ENNReal))).1 problem.smoothMap_contDiff) i
  have h_component_eval :
      ∀ i : Fin m, ∀ d : Point,
        fderiv ℝ (fun y : Point ↦ problem.smoothMap y i) xStar d = (A d) i := by
    intro i d
    have h_diff : DifferentiableAt ℝ problem.smoothMap xStar :=
      problem.smoothMap_contDiff.contDiffAt.differentiableAt
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have hA : HasFDerivAt problem.smoothMap A xStar := by
      simpa [A] using h_diff.hasFDerivAt
    let projCoord : ValuePoint →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp
        ((PiLp.continuousLinearEquiv (p := (2 : ENNReal)) ℝ
          (fun _ : Fin m ↦ ℝ)).toContinuousLinearMap)
    have hproj :
        HasFDerivAt (fun y : Point ↦ problem.smoothMap y i)
          (projCoord.comp A) xStar := by
      have hcoord_fun :
          (fun y : Point ↦ problem.smoothMap y i) =
            fun y : Point ↦ projCoord (problem.smoothMap y) := by
        funext y
        simp [projCoord]
      rw [hcoord_fun]
      exact projCoord.hasFDerivAt.comp xStar hA
    have hAi := congrArg (fun T ↦ T d) hproj.fderiv
    simpa [projCoord, ContinuousLinearMap.comp_apply] using hAi
  ext η
  constructor
  · rintro ⟨⟨lamStar, ξ⟩, hpair, rfl⟩
    rcases hpair with ⟨hlam_clarke, hξ⟩
    have hlam_sub : lamStar ∈ ∂ problem.outerFunction (problem.smoothMap xStar) := by
      rwa [h_outer_clarke] at hlam_clarke
    have hξ_eval :
        ∀ i : Fin m, ∀ d : Point, ξ i d = (A d) i := by
      intro i d
      have hξi :
          ξ i = fderiv ℝ (fun y : Point ↦ problem.smoothMap y i) xStar := by
        exact (mem_clarkeDifferential_iff_eq_fderiv_of_contDiff
          (fun y : Point ↦ problem.smoothMap y i) xStar (ξ i) (h_component_contDiff i)).mp (hξ i)
      have hξid := congrArg (fun T : Point →L[ℝ] ℝ ↦ T d) hξi
      simpa [h_component_eval i d] using hξid
    refine ⟨lamStar.comp A, ⟨lamStar, hlam_sub, rfl⟩, ?_⟩
    exact (StrongDual.toWeakDual_inj _ _).2 <| by
      ext d
      let ev : StrongDual ℝ Point →ₗ[ℝ] ℝ :=
        { toFun := fun ζ ↦ ζ d
          map_add' := by intro ζ₁ ζ₂; rfl
          map_smul' := by intro c ζ; rfl }
      calc
        (lamStar.comp A) d = lamStar (A d) := rfl
        _ = ∑ i : Fin m, (lamStar (EuclideanSpace.single i (1 : ℝ))) * (A d) i := by
              simpa [A] using
                codomainDual_apply_eq_sum_single_coeff (n := m) lamStar (A d)
        _ = ∑ i : Fin m, ev ((lamStar (EuclideanSpace.single i (1 : ℝ))) • ξ i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [ev, hξ_eval i d]
        _ = (∑ i : Fin m, (lamStar (EuclideanSpace.single i (1 : ℝ))) • ξ i) d := by
              change ∑ i : Fin m, ev ((lamStar (EuclideanSpace.single i (1 : ℝ))) • ξ i) =
                ev (∑ i : Fin m, (lamStar (EuclideanSpace.single i (1 : ℝ))) • ξ i)
              symm
              rw [map_sum]
  · rintro ⟨η, ⟨lamStar, hlam_sub, rfl⟩, rfl⟩
    have hlam_clarke : lamStar ∈ (∂ᶜ problem.outerFunction) (problem.smoothMap xStar) := by
      rwa [h_outer_clarke]
    let ξ : Fin m → StrongDual ℝ Point :=
      fun i ↦ fderiv ℝ (fun y : Point ↦ problem.smoothMap y i) xStar
    have hξ :
        ∀ i : Fin m, ξ i ∈ (∂ᶜ (fun y : Point ↦ problem.smoothMap y i)) xStar := by
      intro i
      exact (mem_clarkeDifferential_iff_eq_fderiv_of_contDiff
        (fun y : Point ↦ problem.smoothMap y i) xStar (ξ i) (h_component_contDiff i)).2 rfl
    refine ⟨(lamStar, ξ), ⟨hlam_clarke, hξ⟩, ?_⟩
    exact (StrongDual.toWeakDual_inj _ _).2 <| by
      ext d
      let ev : StrongDual ℝ Point →ₗ[ℝ] ℝ :=
        { toFun := fun ζ ↦ ζ d
          map_add' := by intro ζ₁ ζ₂; rfl
          map_smul' := by intro c ζ; rfl }
      calc
        (∑ i : Fin m, (lamStar (EuclideanSpace.single i (1 : ℝ))) • ξ i) d
            = ∑ i : Fin m, ev ((lamStar (EuclideanSpace.single i (1 : ℝ))) • ξ i) := by
                change ev (∑ i : Fin m, (lamStar (EuclideanSpace.single i (1 : ℝ))) • ξ i) =
                  ∑ i : Fin m, ev ((lamStar (EuclideanSpace.single i (1 : ℝ))) • ξ i)
                rw [map_sum]
        _ = ∑ i : Fin m, (lamStar (EuclideanSpace.single i (1 : ℝ))) * (A d) i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [ev, ξ, h_component_eval i d]
        _ = lamStar (A d) := by
              simpa [A] using
                (codomainDual_apply_eq_sum_single_coeff (n := m) lamStar (A d)).symm
        _ = (lamStar.comp A) d := rfl

/-- Helper for Chapter14 Theorem 14.6.3: the Section 14.6 problem-object formulation of the
stationarity conclusion, stated for `CompositeNonsmoothOptimizationProblem`. -/
theorem exists_subgradient_adjoint_eq_zero_of_isLocalMin
    (problem : CompositeNonsmoothOptimizationProblem n m) (xStar : Point)
    (h_localMin : IsLocalMin problem xStar) :
    ∃ lamStar : DualValue,
      lamStar ∈ ∂ problem.outerFunction (problem.smoothMap xStar) ∧
        (fderiv ℝ problem.smoothMap xStar).adjoint
            ((InnerProductSpace.toDual ℝ ValuePoint).symm lamStar) =
          (0 : Point) := by
  let A : Point →L[ℝ] ValuePoint := fderiv ℝ problem.smoothMap xStar
  let precomp : DualValue →L[ℝ] StrongDual ℝ Point :=
    (ContinuousLinearMap.apply ℝ (Point →L[ℝ] ℝ) A).comp
      (ContinuousLinearMap.compSL Point ValuePoint ℝ (RingHom.id ℝ) (RingHom.id ℝ))
  let T : DualValue → WeakDual ℝ Point := fun lamStar ↦ StrongDual.toWeakDual (precomp lamStar)
  let S : Set (WeakDual ℝ Point) := T '' (∂ problem.outerFunction (problem.smoothMap xStar))
  have h_outer_local :
      LocallyLipschitzAt problem.outerFunction (problem.smoothMap xStar) :=
    convexOn_univ_locallyLipschitzAt
      problem.outerFunction (problem.smoothMap xStar) problem.outerFunction_convex
  have h_local_components :
      ∀ i : Fin m, LocallyLipschitzAt (fun y : Point ↦ problem.smoothMap y i) xStar := by
    intro i
    let hcomp :
        ContDiff ℝ 1 (fun y : Point ↦ problem.smoothMap y i) :=
      ((contDiff_piLp (p := (2 : ENNReal))).1 problem.smoothMap_contDiff) i
    exact hcomp.contDiffAt.locallyLipschitzAt
  have h_local_objective :
      LocallyLipschitzAt problem xStar :=
    locallyLipschitzAt_comp_of_components
      problem.outerFunction problem.smoothMap xStar h_local_components h_outer_local
  have h_zero_mem_clarke :
      (0 : StrongDual ℝ Point) ∈ (∂ᶜ problem) xStar := by
    exact (isClarkeStationaryPoint_iff_zero_mem_clarkeDifferential).mp
      (h_localMin.isClarkeStationaryPoint h_local_objective)
  have h_generator :
      chainRuleGeneratorSet problem.outerFunction problem.smoothMap xStar = S := by
    -- Normalize the opaque Chapter 14.1 generator set to one pushed-forward weak image.
    simpa [A, S, T, precomp, Set.image_image, ContinuousLinearMap.compSL_apply] using
      chainRuleGeneratorSet_eq_toWeakDual_image_comp_subdifferential problem xStar
  have h_zero_mem_hull :
      (0 : WeakDual ℝ Point) ∈ closedConvexHull ℝ S := by
    have h_subset :=
      clarkeDifferential_comp_subset_weakClosedConvexHull
        problem.outerFunction problem.smoothMap xStar h_local_components h_outer_local
    have h_zero_mem_hull_raw :
        (0 : WeakDual ℝ Point) ∈
          closedConvexHull ℝ
            (chainRuleGeneratorSet problem.outerFunction problem.smoothMap xStar) := by
      have h_zero_mem_comp :
          (0 : StrongDual ℝ Point) ∈
            (∂ᶜ (fun y : Point ↦ problem.outerFunction (problem.smoothMap y))) xStar := by
        change (0 : StrongDual ℝ Point) ∈ (∂ᶜ problem) xStar
        exact h_zero_mem_clarke
      exact h_subset ⟨0, h_zero_mem_comp, by simp⟩
    simpa [h_generator] using h_zero_mem_hull_raw
  let L : DualValue →ₗ[ℝ] WeakDual ℝ Point :=
    ((StrongDual.toWeakDual : StrongDual ℝ Point ≃ₗ[ℝ] WeakDual ℝ Point).toLinearMap).comp
      precomp.toLinearMap
  have hS_convex : Convex ℝ S := by
    -- Convexity is inherited from the outer subdifferential through the linear image map.
    simpa [S, T, L] using
      (convex_subdifferential problem.outerFunction (problem.smoothMap xStar)).linear_image L
  have hT_cont : Continuous T := by
    exact NormedSpace.Dual.toWeakDual_continuous.comp precomp.continuous
  have hS_compact : IsCompact S := by
    -- Compactness of the outer subdifferential gives closedness in the weak codomain after
    -- pushforward.
    simpa [S, T] using
      (isCompact_subdifferential_of_convexOn_of_locallyLipschitzAt
        problem.outerFunction (problem.smoothMap xStar)
        problem.outerFunction_convex h_outer_local).image hT_cont
  have hS_closed : IsClosed S := hS_compact.isClosed
  have h_hull_eq : closedConvexHull ℝ S = S := by
    apply le_antisymm
    · exact closedConvexHull_min subset_rfl hS_convex hS_closed
    · exact subset_closedConvexHull (𝕜 := ℝ)
  have h_zero_mem_S : (0 : WeakDual ℝ Point) ∈ S := by
    simpa [h_hull_eq] using h_zero_mem_hull
  rcases h_zero_mem_S with ⟨lamStar, hlamStar, hzero⟩
  have h_precomp_zero : precomp lamStar = 0 := by
    apply (StrongDual.toWeakDual_inj _ _).1
    simpa [T] using hzero
  have h_comp_zero : lamStar.comp A = 0 := by
    simpa [precomp, ContinuousLinearMap.compSL_apply] using h_precomp_zero
  have h_adjoint_zero :
      A.adjoint ((InnerProductSpace.toDual ℝ ValuePoint).symm lamStar) = (0 : Point) :=
    (comp_eq_zero_iff_adjoint_riesz_eq_zero A lamStar).1 h_comp_zero
  exact ⟨lamStar, hlamStar, by simpa [A] using h_adjoint_zero⟩

end

section

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

local notation "CoordE" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
local notation "CoordF" => EuclideanSpace ℝ (Fin (Module.finrank ℝ F))

omit [FiniteDimensional ℝ F] in
/-- Helper for Chapter14 Theorem 14.6.3: precomposing a convex function with the inverse of a
linear isometry equivalence transports subdifferential membership by precomposition of dual
functionals. -/
lemma mem_subdifferential_comp_symm_iff
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : F ≃ₗᵢ[ℝ] G) (h : F → ℝ) (y : F) (lamCoord : StrongDual ℝ G) :
    lamCoord ∈ ∂ (h ∘ e.symm) (e y) ↔ lamCoord.comp (e : F →L[ℝ] G) ∈ ∂ h y := by
  rw [mem_subdifferential_iff, mem_subdifferential_iff]
  constructor
  · intro hmem z
    -- Evaluate the transported support inequality on the coordinate image `e z`.
    simpa [Function.comp, map_sub] using hmem (e z)
  · intro hmem z
    -- Pull a coordinate test point `z` back through `e.symm` to recover the original inequality.
    simpa [Function.comp, map_sub] using hmem (e.symm z)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Helper for Chapter14 Theorem 14.6.3: the derivative of the coordinate-conjugated smooth map is
the corresponding conjugated derivative. -/
lemma fderiv_conjugated_smoothMap
    (eE : E ≃ₗᵢ[ℝ] CoordE) (eF : F ≃ₗᵢ[ℝ] CoordF)
    (smoothMap : E → F) (x : E) :
    fderiv ℝ (eF ∘ smoothMap ∘ eE.symm) (eE x) =
      ((eF : F →L[ℝ] CoordF).comp (fderiv ℝ smoothMap x)).comp (eE.symm : CoordE →L[ℝ] E) := by
  -- Rewrite the conjugated derivative once so the main proof stays in one spelling world.
  calc
    fderiv ℝ (eF ∘ smoothMap ∘ eE.symm) (eE x)
        = (fderiv ℝ (eF ∘ smoothMap) x).comp (eE.symm : CoordE →L[ℝ] E) := by
            have hcoord :
                fderiv ℝ (eF ∘ smoothMap ∘ eE.symm) (eE x) =
                  (fderiv ℝ (eF ∘ smoothMap) x).comp (eE.symm : CoordE →L[ℝ] E) := by
              change fderiv ℝ ((eF ∘ smoothMap) ∘ eE.symm) (eE x) =
                (fderiv ℝ (eF ∘ smoothMap) x).comp (eE.symm : CoordE →L[ℝ] E)
              simpa using
                (ContinuousLinearEquiv.comp_right_fderiv
                  (iso := eE.symm.toContinuousLinearEquiv)
                  (f := eF ∘ smoothMap) (x := eE x))
            exact hcoord
    _ = (((eF : F →L[ℝ] CoordF).comp (fderiv ℝ smoothMap x))).comp
          (eE.symm : CoordE →L[ℝ] E) := by
            rw [LinearIsometryEquiv.comp_fderiv (iso := eF) (f := smoothMap) (x := x)]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Helper for Chapter14 Theorem 14.6.3: vanishing of the coordinate composition is equivalent to
vanishing of the original composition after pulling the dual witness back. -/
lemma comp_eq_zero_conjugate_iff
    (eE : E ≃ₗᵢ[ℝ] CoordE) (eF : F ≃ₗᵢ[ℝ] CoordF)
    (A : E →L[ℝ] F) (lamCoord : StrongDual ℝ CoordF) :
    lamCoord.comp (((eF : F →L[ℝ] CoordF).comp A).comp (eE.symm : CoordE →L[ℝ] E)) = 0 ↔
      (lamCoord.comp (eF : F →L[ℝ] CoordF)).comp A = 0 := by
  constructor
  · intro hcoord
    -- Evaluate the coordinate identity on `eE x` to cancel the inverse chart.
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun T : CoordE →L[ℝ] ℝ ↦ T (eE x)) hcoord
    simpa [ContinuousLinearMap.comp_assoc] using hx
  · intro horig
    -- Evaluate the original identity on `eE.symm z` to recover the coordinate version.
    apply ContinuousLinearMap.ext
    intro z
    have hz := congrArg (fun T : E →L[ℝ] ℝ ↦ T (eE.symm z)) horig
    simpa [ContinuousLinearMap.comp_assoc] using hz

/-- Helper for Chapter14 Theorem 14.6.3: for real finite-dimensional Hilbert spaces, vanishing of
`lam.comp A` is equivalent to vanishing of the adjoint applied to the Riesz representative of
`lam`. -/
lemma comp_eq_zero_iff_adjoint_riesz_eq_zero_hilbert
    (A : E →L[ℝ] F) (lam : StrongDual ℝ F) :
    lam.comp A = 0 ↔
      A.adjoint ((InnerProductSpace.toDual ℝ F).symm lam) = (0 : E) := by
  constructor
  · intro h_comp
    -- Push the adjoint identity through the Riesz map and compare both functionals pointwise.
    apply (InnerProductSpace.toDual ℝ E).injective
    ext x
    have hx : lam (A x) = 0 := by
      simpa using congrArg (fun T : E →L[ℝ] ℝ ↦ T x) h_comp
    rw [InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDual_apply_apply]
    have hleft :
        inner ℝ (A.adjoint ((InnerProductSpace.toDual ℝ F).symm lam)) x =
          inner ℝ ((InnerProductSpace.toDual ℝ F).symm lam) (A x) := by
      simpa using
        ContinuousLinearMap.adjoint_inner_left
          A x ((InnerProductSpace.toDual ℝ F).symm lam)
    have hright :
        inner ℝ ((InnerProductSpace.toDual ℝ F).symm lam) (A x) = lam (A x) := by
      exact InnerProductSpace.toDual_symm_apply (x := A x) (y := lam)
    exact hleft.trans (hright.trans (hx.trans (by simp)))
  · intro h_adjoint
    -- Evaluate the adjoint identity on each vector to recover the vanished composition.
    apply ContinuousLinearMap.ext
    intro x
    have hright :
        lam (A x) = inner ℝ ((InnerProductSpace.toDual ℝ F).symm lam) (A x) := by
      exact (InnerProductSpace.toDual_symm_apply (x := A x) (y := lam)).symm
    have hleft :
        inner ℝ ((InnerProductSpace.toDual ℝ F).symm lam) (A x) =
          inner ℝ (A.adjoint ((InnerProductSpace.toDual ℝ F).symm lam)) x := by
      simpa using
        (ContinuousLinearMap.adjoint_inner_left
          A x ((InnerProductSpace.toDual ℝ F).symm lam)).symm
    exact hright.trans (hleft.trans (by simp [h_adjoint]))

/-- Chapter14 Theorem 14.6.3: if `xStar` is a local minimizer of the composite objective
`outerFunction ∘ smoothMap`, then there exists
`lamStar ∈ ∂ outerFunction (smoothMap xStar)` such that
`(fderiv ℝ smoothMap xStar).adjoint ((InnerProductSpace.toDual ℝ F).symm lamStar) = 0`,
which is the Hilbert-space form of `A(xStar) λStar = 0`. -/
theorem exists_subgradient_adjoint_eq_zero_of_isLocalMin_hilbert
    (smoothMap : E → F) (outerFunction : F → ℝ) (xStar : E)
    (h_contDiff : ContDiff ℝ 1 smoothMap)
    (h_convex : ConvexOn ℝ Set.univ outerFunction)
    (h_localMin : IsLocalMin (outerFunction ∘ smoothMap) xStar) :
    ∃ lamStar : StrongDual ℝ F,
      lamStar ∈ ∂ outerFunction (smoothMap xStar) ∧
        (fderiv ℝ smoothMap xStar).adjoint ((InnerProductSpace.toDual ℝ F).symm lamStar) =
          (0 : E) := by
  -- Route correction: instead of transporting the final adjoint/Riesz equation directly through
  -- coordinates, first transport the simpler identity `lam.comp A = 0`, then recover the adjoint
  -- form only at the end.
  let eE : E ≃ₗᵢ[ℝ] CoordE := (stdOrthonormalBasis ℝ E).repr
  let eF : F ≃ₗᵢ[ℝ] CoordF := (stdOrthonormalBasis ℝ F).repr
  let coordProblem :
      CompositeNonsmoothOptimizationProblem
        (Module.finrank ℝ E) (Module.finrank ℝ F) := {
    smoothMap := eF ∘ smoothMap ∘ eE.symm
    outerFunction := outerFunction ∘ eF.symm
    smoothMap_contDiff := by
      -- The coordinate problem is still `C¹` because the basis equivalences are smooth.
      simpa [Function.comp] using eF.contDiff.comp (h_contDiff.comp eE.symm.contDiff)
    outerFunction_convex := by
      -- Convexity is preserved under precomposition with the inverse linear isometry.
      simpa [Function.comp] using h_convex.comp_linearMap eF.symm.toLinearEquiv.toLinearMap }
  have h_localMin_coord : IsLocalMin coordProblem (eE xStar) := by
    -- The coordinate objective is exactly the original objective precomposed with `eE.symm`.
    have h_localMin_pre :
        IsLocalMin ((outerFunction ∘ smoothMap) ∘ eE.symm) (eE xStar) := by
      refine IsLocalMin.comp_continuous (b := eE xStar) (g := eE.symm) ?_ eE.symm.continuousAt
      simpa using h_localMin
    have h_obj_eq : (coordProblem : CoordE → ℝ) = ((outerFunction ∘ smoothMap) ∘ eE.symm) := by
      funext z
      simp [coordProblem, Function.comp]
    simpa [h_obj_eq] using h_localMin_pre
  rcases
      exists_subgradient_adjoint_eq_zero_of_isLocalMin coordProblem (eE xStar) h_localMin_coord with
    ⟨lamCoord, hlamCoord_mem, hlamCoord_adjoint⟩
  let A : E →L[ℝ] F := fderiv ℝ smoothMap xStar
  have hlamCoord_mem' :
      lamCoord ∈ ∂ (outerFunction ∘ eF.symm) (eF (smoothMap xStar)) := by
    -- Simplify the coordinate evaluation point to the image of `smoothMap xStar`.
    simpa [coordProblem, Function.comp] using hlamCoord_mem
  let lamStar : StrongDual ℝ F := lamCoord.comp (eF : F →L[ℝ] CoordF)
  have hlamStar_mem : lamStar ∈ ∂ outerFunction (smoothMap xStar) := by
    -- Pull the Euclidean witness back through the codomain isometry.
    exact (mem_subdifferential_comp_symm_iff eF outerFunction (smoothMap xStar) lamCoord).1
      hlamCoord_mem'
  have hcoord_comp_zero :
      lamCoord.comp (fderiv ℝ (eF ∘ smoothMap ∘ eE.symm) (eE xStar)) = 0 := by
    -- Convert the Euclidean theorem's adjoint conclusion to the cheaper `lam.comp A = 0` form.
    exact
      (comp_eq_zero_iff_adjoint_riesz_eq_zero
        (fderiv ℝ coordProblem.smoothMap (eE xStar)) lamCoord).2 <| by
          simpa [coordProblem] using hlamCoord_adjoint
  have hcoord_comp_zero' :
      lamCoord.comp (((eF : F →L[ℝ] CoordF).comp A).comp (eE.symm : CoordE →L[ℝ] E)) = 0 := by
    -- Rewrite the transported derivative into its conjugated normal form once.
    rw [fderiv_conjugated_smoothMap eE eF smoothMap xStar] at hcoord_comp_zero
    simpa [A] using hcoord_comp_zero
  have hcomp_zero : lamStar.comp A = 0 := by
    -- Cancel the domain coordinate change and keep only the pulled-back multiplier.
    exact (comp_eq_zero_conjugate_iff eE eF A lamCoord).1 hcoord_comp_zero'
  have h_adjoint_zero :
      A.adjoint ((InnerProductSpace.toDual ℝ F).symm lamStar) = (0 : E) := by
    -- Return from the composition-zero normal form to the requested adjoint equation.
    exact (comp_eq_zero_iff_adjoint_riesz_eq_zero_hilbert A lamStar).1 hcomp_zero
  exact ⟨lamStar, hlamStar_mem, by simpa [A] using h_adjoint_zero⟩

#print axioms exists_subgradient_adjoint_eq_zero_of_isLocalMin

#print axioms exists_subgradient_adjoint_eq_zero_of_isLocalMin_hilbert

end
