/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_2_2.CoreTransport

open scoped Gradient
open MeasureTheory

noncomputable section

universe u

/-- Classical decidability for propositions, used to evaluate the interior-membership branch in the
source-facing ambient universal-barrier formula. -/
local instance {p : Prop} : Decidable p := Classical.propDecidable p

/-- Measurable structure for the local volume-based helpers in PointwiseCore. -/
local instance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    MeasurableSpace E := borel E

/-- Borel structure for the local volume-based helpers in PointwiseCore. -/
local instance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    BorelSpace E := ⟨rfl⟩

namespace IsSelfConcordantBarrierOnWith

/-- Helper for PointwiseCore: restricting a barrier owner to a smaller open convex subdomain keeps
the same barrier parameter and ambient function. -/
theorem restrict
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {dom dom' : Set E} {ν : NNReal} {F : E → ℝ}
    (hbarrier : IsSelfConcordantBarrierOnWith dom ν F)
    (hsubset : dom' ⊆ dom) (hopen : IsOpen dom') (hconvex : Convex ℝ dom') :
    IsSelfConcordantBarrierOnWith dom' ν F := by
  refine
    { toIsStandardSelfConcordantOn := ?_
      barrier_parameter_bound := ?_ }
  · refine
      { isOpen_domain := hopen
        contDiffOn := hbarrier.toIsStandardSelfConcordantOn.contDiffOn.mono hsubset
        convexOn := ?_
        third_deriv_bound := ?_ }
    · refine ⟨hconvex, ?_⟩
      intro x hx y hy a b ha hb hab
      -- The convexity inequality is inherited verbatim from the larger barrier domain.
      exact hbarrier.toIsStandardSelfConcordantOn.convexOn.2 (hsubset hx) (hsubset hy) ha hb hab
    · intro x hx u
      -- The cubic directional-derivative control is also inherited pointwise.
      exact hbarrier.toIsStandardSelfConcordantOn.third_deriv_bound (hsubset hx) u
  · intro x hx u
    -- The barrier-parameter inequality is unchanged after restricting the domain.
    exact hbarrier.barrier_parameter_bound (hsubset hx) u

end IsSelfConcordantBarrierOnWith

/-- Helper for PointwiseCore: along a short interval around `0`, the ambient directional slice
through an interior base point is exactly the intrinsic `c₁ * log V` branch. -/
theorem exists_pos_lineSliceRadius_eq_logVolumeAlongLine
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∈ interior Q) (u : E) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε →
      ∃ hxt : x + t • u ∈ interior Q,
        directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u t =
          c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩) := by
  have hmem :
      {t : ℝ | x + t • u ∈ interior Q} ∈ nhds (0 : ℝ) :=
    lineMap_eventually_mem_interior (Q := Q) hx u
  rw [Metric.mem_nhds_iff] at hmem
  rcases hmem with ⟨ε, hεpos, hsub⟩
  refine ⟨ε, hεpos, ?_⟩
  intro t ht
  have hball : t ∈ Metric.ball (0 : ℝ) ε := by
    -- On `ℝ`, `|t| < ε` is exactly membership in the radius-`ε` ball around `0`.
    simpa [Metric.ball, Real.dist_eq] using ht
  have hxt : x + t • u ∈ interior Q := hsub hball
  refine ⟨hxt, ?_⟩
  -- Inside the short interval, the explicit ambient owner stays on its log-volume branch.
  simp [directionalSlice, explicitUniversalBarrierAmbient, hxt]

/-- Helper for PointwiseCore: an intrinsic interval-local slice formula transports to the ambient
directional slice near `t = 0`. -/
theorem directionalSlice_eventuallyEq_intrinsicLogVolumeLineSlice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∈ interior Q) (u : E)
    {ε : ℝ} (hεpos : 0 < ε) {ψ : ℝ → ℝ}
    (hψeq :
      ∀ t : ℝ, |t| < ε →
        ∃ hxt : x + t • u ∈ interior Q,
          ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) :
    directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u =ᶠ[nhds (0 : ℝ)] ψ := by
  rcases exists_pos_lineSliceRadius_eq_logVolumeAlongLine (c₁ := c₁) (Q := Q) (x := x) hx u with
    ⟨η, hηpos, hηeq⟩
  let δ : ℝ := min ε η
  have hδpos : 0 < δ := by
    -- The common interval must satisfy both the user-provided slice formula and the ambient one.
    exact lt_min hεpos hηpos
  have hδball : ∀ᶠ t : ℝ in nhds (0 : ℝ), t ∈ Metric.ball (0 : ℝ) δ := by
    exact Metric.ball_mem_nhds (0 : ℝ) hδpos
  have hδnhds : ∀ᶠ t : ℝ in nhds (0 : ℝ), |t| < δ := by
    -- On `ℝ`, the metric ball around `0` is the same as `|t| < δ`.
    simpa [Metric.ball, Real.dist_eq] using hδball
  filter_upwards [hδnhds] with t ht
  have htε : |t| < ε := lt_of_lt_of_le ht (min_le_left _ _)
  have htη : |t| < η := lt_of_lt_of_le ht (min_le_right _ _)
  rcases hηeq t htη with ⟨hxt, hslice_t⟩
  rcases hψeq t htε with ⟨hxt', hψt⟩
  have hsub : (⟨x + t • u, hxt⟩ : interior Q) = ⟨x + t • u, hxt'⟩ := by
    ext
    rfl
  -- Both formulas reduce to the same intrinsic `c₁ * log V` branch on the common neighborhood.
  calc
    directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u t
        = explicitUniversalBarrierAmbient c₁ Q (x + t • u) := by
            simp [directionalSlice]
    _ = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩) := hslice_t
    _ = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt'⟩) := by
          simpa using
            congrArg (fun y : interior Q ↦ c₁ * Real.log (universalBarrierVolume Q y)) hsub
    _ = ψ t := hψt.symm

/-- Helper for PointwiseCore: local intrinsic log-volume slice inequalities transport to the
ambient directional slice at `t = 0`. -/
theorem
    directionalSlice_pointwiseCoreAtZero_of_intrinsicLogVolumeLineSlice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {x : E} (hx : x ∈ interior Q) (u : E)
    {ν : NNReal} {ε : ℝ} (hεpos : 0 < ε) {ψ : ℝ → ℝ}
    (hψeq :
      ∀ t : ℝ, |t| < ε →
        ∃ hxt : x + t • u ∈ interior Q,
          ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩))
    (hψsecond : 0 ≤ iteratedDeriv 2 ψ 0)
    (hψthird :
      |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ))
    (hψgradSq :
      (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0) :
    let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
    0 ≤ iteratedDeriv 2 φ 0 ∧
      |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) ∧
      (deriv φ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 φ 0 := by
  let φ : ℝ → ℝ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
  have heq : φ =ᶠ[nhds (0 : ℝ)] ψ :=
    directionalSlice_eventuallyEq_intrinsicLogVolumeLineSlice
      (c₁ := c₁) (Q := Q) (x := x) hx u hεpos hψeq
  -- Transport the scalar derivatives across the neighborhood identity between the two slice owners.
  have hderiv_eq : deriv φ 0 = deriv ψ 0 := by
    simpa [φ] using Filter.EventuallyEq.deriv_eq heq
  have hsecond_eq : iteratedDeriv 2 φ 0 = iteratedDeriv 2 ψ 0 := by
    simpa [φ] using Filter.EventuallyEq.iteratedDeriv_eq 2 heq
  have hthird_eq : iteratedDeriv 3 φ 0 = iteratedDeriv 3 ψ 0 := by
    simpa [φ] using Filter.EventuallyEq.iteratedDeriv_eq 3 heq
  dsimp [φ]
  refine ⟨?_, ?_, ?_⟩
  · -- Rewrite the intrinsic second-derivative lower bound into the ambient directional slice.
    rw [hsecond_eq]
    exact hψsecond
  · -- Rewrite the intrinsic cubic bound into the ambient directional slice.
    rw [hsecond_eq, hthird_eq]
    exact hψthird
  · -- Rewrite the intrinsic gradient-square estimate into the ambient directional slice.
    rw [hderiv_eq, hsecond_eq]
    exact hψgradSq

/-- Helper for PointwiseCore: intrinsic second/third slice bounds transport directly to the
ambient directional slice at `t = 0`. -/
theorem directionalSlice_standardBounds_of_intrinsicLogVolumeLineSlice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {x : E} (hx : x ∈ interior Q) (u : E)
    {ε : ℝ} (hεpos : 0 < ε) {ψ : ℝ → ℝ}
    (hψeq :
      ∀ t : ℝ, |t| < ε →
        ∃ hxt : x + t • u ∈ interior Q,
          ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩))
    (hψsecond : 0 ≤ iteratedDeriv 2 ψ 0)
    (hψthird :
      |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) :
    let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
    0 ≤ iteratedDeriv 2 φ 0 ∧
      |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) := by
  let φ : ℝ → ℝ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
  have heq : φ =ᶠ[nhds (0 : ℝ)] ψ :=
    directionalSlice_eventuallyEq_intrinsicLogVolumeLineSlice
      (c₁ := c₁) (Q := Q) (x := x) hx u hεpos hψeq
  -- Transport only the second- and third-derivative owners across the neighborhood identity.
  have hsecond_eq : iteratedDeriv 2 φ 0 = iteratedDeriv 2 ψ 0 := by
    simpa [φ] using Filter.EventuallyEq.iteratedDeriv_eq 2 heq
  have hthird_eq : iteratedDeriv 3 φ 0 = iteratedDeriv 3 ψ 0 := by
    simpa [φ] using Filter.EventuallyEq.iteratedDeriv_eq 3 heq
  dsimp [φ]
  refine ⟨?_, ?_⟩
  · -- Rewrite the intrinsic second-derivative lower bound into the ambient directional slice.
    rw [hsecond_eq]
    exact hψsecond
  · -- Rewrite the intrinsic cubic bound into the ambient directional slice.
    rw [hsecond_eq, hthird_eq]
    exact hψthird

/-- Helper for PointwiseCore: source-facing intrinsic slice data packages into the standard slice
interface used by the ambient self-concordance assembly. -/
theorem explicitUniversalBarrierAmbient_standardSliceData_of_intrinsicLogVolumeLineSlice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ}
    (hcontAt :
      ∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x)
    (hsliceIntrinsic :
      ∀ x ∈ interior Q, ∀ u,
        ∃ ε > 0, ∃ ψ : ℝ → ℝ,
          (∀ t : ℝ, |t| < ε →
            ∃ hxt : x + t • u ∈ interior Q,
              ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
          0 ≤ iteratedDeriv 2 ψ 0 ∧
            |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) :
    ∀ x ∈ interior Q,
      ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x ∧
        ∀ u,
          let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
          0 ≤ iteratedDeriv 2 φ 0 ∧
            |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) := by
  intro x hx
  refine ⟨hcontAt x hx, ?_⟩
  intro u
  rcases hsliceIntrinsic x hx u with ⟨ε, hεpos, ψ, hψeq, hψsecond, hψthird⟩
  -- The `ContDiffAt` field is already given separately, so only the scalar bounds need transport.
  simpa using
    directionalSlice_standardBounds_of_intrinsicLogVolumeLineSlice
      (Q := Q) (c₁ := c₁) (x := x) hx u hεpos hψeq hψsecond hψthird

/-- Helper for PointwiseCore: every interior based-polar body has positive volume under the proper
convex/no-affine-line hypotheses. -/
theorem pointwiseCore_universalBarrierVolume_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E)
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (x : interior Q) :
    0 < universalBarrierVolume Q x := by
  have hpolar_interior :
      (interior (polarSetAt Q (x : E))).Nonempty :=
    polarSetAt_interior_nonempty hQ_convex hQ_noAffineLine x.property
  have hpolar_pos : 0 < volume (polarSetAt Q (x : E)) :=
    Measure.measure_pos_of_nonempty_interior volume hpolar_interior
  have hpolar_compact :
      IsCompact (polarSetAt Q (x : E)) :=
    (polarSetAt_isCompact_convex x.property).1
  have hpolar_lt_top : volume (polarSetAt Q (x : E)) < ⊤ :=
    hpolar_compact.measure_lt_top
  -- Compactness gives finite volume, so positivity survives the `toReal` projection.
  simpa [universalBarrierVolume] using ENNReal.toReal_pos hpolar_pos.ne' hpolar_lt_top.ne

/-- Helper for PointwiseCore: the ambient volume-power owner matching
`x ↦ exp (-(F x / ν))` on `interior Q`. -/
def explicitUniversalBarrierVolumePowerAmbient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (c₁ : ℝ) (ν : NNReal) (Q : Set E) :
    E → ℝ :=
  fun x ↦
    if hx : x ∈ interior Q then
      (universalBarrierVolume Q ⟨x, hx⟩) ^ (-(c₁ / (ν : ℝ)))
    else
      0

/-- Helper for PointwiseCore: on `interior Q`, the exponential transform of the explicit ambient
owner is exactly the matching volume-power owner. -/
theorem explicitUniversalBarrierAmbient_expNegDiv_eq_volumePowerAmbient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {c₁ : ℝ} {ν : NNReal} {Q : Set E}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) :
    Set.EqOn
      (fun x ↦ Real.exp (-(explicitUniversalBarrierAmbient c₁ Q x / (ν : ℝ))))
      (explicitUniversalBarrierVolumePowerAmbient c₁ ν Q)
      (interior Q) := by
  intro x hx
  have hvol_pos :
      0 < universalBarrierVolume Q ⟨x, hx⟩ :=
    pointwiseCore_universalBarrierVolume_pos Q hQ_convex hQ_noAffineLine ⟨x, hx⟩
  -- On the domain, the explicit ambient owner is literally `c₁ * log V(x)`.
  calc
    Real.exp (-(explicitUniversalBarrierAmbient c₁ Q x / (ν : ℝ)))
        = Real.exp (-(c₁ * Real.log (universalBarrierVolume Q ⟨x, hx⟩) / (ν : ℝ))) := by
            rw [explicitUniversalBarrierAmbient_eq_log_volume hx]
    _ = Real.exp (Real.log (universalBarrierVolume Q ⟨x, hx⟩) * (-(c₁ / (ν : ℝ)))) := by
          congr 1
          ring
    _ = (universalBarrierVolume Q ⟨x, hx⟩) ^ (-(c₁ / (ν : ℝ))) := by
          symm
          simpa [mul_comm] using
            (Real.rpow_def_of_pos hvol_pos (-(c₁ / (ν : ℝ))))
    _ = explicitUniversalBarrierVolumePowerAmbient c₁ ν Q x := by
          simp [explicitUniversalBarrierVolumePowerAmbient, hx]

/-- Helper for PointwiseCore: concavity of the volume-power owner transports directly to the
exponential transform required by the barrier API for `explicitUniversalBarrierAmbient`. -/
theorem explicitUniversalBarrierAmbient_expTransform_concave_of_volumePowerConcave
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hconc :
      ConcaveOn ℝ (interior Q) (explicitUniversalBarrierVolumePowerAmbient c₁ ν Q)) :
    ConcaveOn ℝ (interior Q)
      (fun x ↦ Real.exp (-(explicitUniversalBarrierAmbient c₁ Q x / (ν : ℝ)))) := by
  -- Rewrite the exponential transform once to the source-facing volume-power owner.
  refine hconc.congr ?_
  intro x hx
  simpa using
    (explicitUniversalBarrierAmbient_expNegDiv_eq_volumePowerAmbient
      (Q := Q) (c₁ := c₁) (ν := ν) hQ_convex hQ_noAffineLine hx).symm

/-- Helper for PointwiseCore: a barrier witness for the explicit ambient owner yields concavity of
the matching volume-power owner on `interior Q`. -/
theorem explicitUniversalBarrierVolumePowerAmbient_concave_of_barrierOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hbarrier :
      IsSelfConcordantBarrierOnWith (interior Q) ν (explicitUniversalBarrierAmbient c₁ Q))
    (hν : 0 < (ν : ℝ)) :
    ConcaveOn ℝ (interior Q) (explicitUniversalBarrierVolumePowerAmbient c₁ ν Q) := by
  have hstd :
      IsStandardSelfConcordantOn (interior Q) (explicitUniversalBarrierAmbient c₁ Q) :=
    hbarrier.toIsStandardSelfConcordantOn
  have hconcExp :
      ConcaveOn ℝ (interior Q)
        (fun x ↦ Real.exp (-(explicitUniversalBarrierAmbient c₁ Q x / (ν : ℝ)))) :=
    (isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div hstd hν).1 hbarrier
  -- Rewrite the exponential-transform owner once to the source-facing volume-power owner.
  exact
    hconcExp.congr
      (explicitUniversalBarrierAmbient_expNegDiv_eq_volumePowerAmbient
        (Q := Q) (c₁ := c₁) (ν := ν) hQ_convex hQ_noAffineLine)

/-- Helper for PointwiseCore: the explicit ambient owner is the same function as the chapter's
canonical `universalBarrierAmbient`. -/
@[simp] theorem explicitUniversalBarrierAmbient_eq_universalBarrierAmbient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (c₁ : ℝ) (Q : Set E) :
    explicitUniversalBarrierAmbient c₁ Q = universalBarrierAmbient c₁ Q := by
  funext x
  by_cases hx : x ∈ interior Q
  · -- On the interior, both owners reduce to the same `c₁ * log V` formula.
    simp [explicitUniversalBarrierAmbient, universalBarrierAmbient, universalBarrier, hx]
  · -- Off the interior, both owners take the same fallback value.
    simp [explicitUniversalBarrierAmbient, universalBarrierAmbient, universalBarrier, hx]

/-- Helper for PointwiseCore: a barrier witness for `universalBarrierAmbient` immediately
transports to the explicit ambient owner. -/
theorem explicitUniversalBarrierAmbient_barrierOnInterior_of_universalBarrierAmbient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hbarrier :
      IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q)) :
    IsSelfConcordantBarrierOnWith (interior Q) ν (explicitUniversalBarrierAmbient c₁ Q) := by
  -- Rewrite the owner once; the barrier witness itself needs no further transport.
  simpa [explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using hbarrier

/-- Helper for PointwiseCore: pointwise core data on the explicit ambient owner packages directly
into standard self-concordance on `interior Q`. -/
theorem explicitUniversalBarrierAmbient_isStandardSelfConcordantOn_of_pointwiseCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ}
    (hQ_convex : Convex ℝ Q)
    (hcont :
      ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q))
    (hquad :
      ∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u))
    (hthird :
      ∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) :
    IsStandardSelfConcordantOn (interior Q) (explicitUniversalBarrierAmbient c₁ Q) := by
  have hdom_open : IsOpen (interior Q) := isOpen_interior
  have hdom_convex : Convex ℝ (interior Q) := hQ_convex.interior
  have hC2 :
      ContDiffOn ℝ 2 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) :=
    hcont.of_le (by norm_num)
  -- The explicit ambient owner already satisfies the standard owner fields once the Hessian and
  -- cubic estimates are recorded pointwise.
  refine
    { isOpen_domain := hdom_open
      contDiffOn := hcont
      convexOn := ?_
      third_deriv_bound := ?_ }
  · refine (convexOn_iff_hessian_quadratic_form_nonneg hdom_open hdom_convex hC2).2 ?_
    intro x hx u
    simpa [real_inner_comm] using hquad x hx u
  · intro x hx u
    simpa using hthird x hx u

/-- Helper for PointwiseCore: a barrier witness for the explicit ambient owner packages the local
`C³`/Hessian/cubic/gradient data at each interior point. -/
theorem explicitUniversalBarrierAmbient_pointwiseData_of_barrierOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hbarrier :
      IsSelfConcordantBarrierOnWith (interior Q) ν (explicitUniversalBarrierAmbient c₁ Q)) :
    ∀ x ∈ interior Q,
      ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x ∧
        (∀ u, 0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
        (∀ u,
          |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
            2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
        (∀ u,
          (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
            (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) := by
  intro x hx
  have hstd :
      IsStandardSelfConcordantOn (interior Q) (explicitUniversalBarrierAmbient c₁ Q) :=
    hbarrier.toIsStandardSelfConcordantOn
  have hcontAt :
      ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x :=
    hstd.contDiffOn.contDiffAt (hstd.isOpen_domain.mem_nhds hx)
  have hquad :
      ∀ u, 0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u) := by
    intro u
    exact hstd.hessian_posSemidef hx u
  have hthird :
      ∀ u,
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) := by
    intro u
    simpa [one_mul, hessianLocalNorm] using hstd.third_deriv_bound hx u
  have hgrad :
      ∀ u,
        (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u) := by
    have hPos :
        (hessian (explicitUniversalBarrierAmbient c₁ Q) x).IsPositive :=
      hstd.hessian_isPositive hx
    exact
      (IsSelfConcordantBarrierOnWith.gradient_sq_le_mul_hessian_iff_barrier_bound
        (F := explicitUniversalBarrierAmbient c₁ Q) (x := x) (μ := ν) hPos).1
        (hbarrier.barrier_parameter_bound hx)
  -- Read the pointwise fields directly from the barrier owner.
  exact ⟨hcontAt, hquad, hthird, hgrad⟩

/-- Helper for PointwiseCore: pointwise `C³` control and the standard scalar slice inequalities
package directly into standard self-concordance for the explicit ambient owner. -/
theorem explicitUniversalBarrierAmbient_standardSelfConcordant_of_contDiffAtAndStandardSliceData
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ}
    (hQ_convex : Convex ℝ Q)
    (hcontAt :
      ∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x)
    (hsliceStd :
      ∀ x ∈ interior Q, ∀ u,
        let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
        0 ≤ iteratedDeriv 2 φ 0 ∧
          |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ)) :
    IsStandardSelfConcordantOn (interior Q) (explicitUniversalBarrierAmbient c₁ Q) := by
  have hcont :
      ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) :=
    explicitUniversalBarrierAmbient_contDiffOn_of_pointwiseData hcontAt
  have hquad :
      ∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u) := by
    intro x hx u
    let φ : ℝ → ℝ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
    have hslice_xu := hsliceStd x hx u
    dsimp [φ] at hslice_xu
    rcases
      directionalSliceDerivativesAtZero_eq_ambientOwners
        (F := explicitUniversalBarrierAmbient c₁ Q) (x := x) (u := u) (hcontAt x hx) with
      ⟨_, hsecond, _⟩
    -- The scalar second-derivative lower bound is exactly Hessian quadratic-form nonnegativity.
    rw [← hsecond]
    exact hslice_xu.1
  have hthird :
      ∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) := by
    intro x hx u
    let φ : ℝ → ℝ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
    have hslice_xu := hsliceStd x hx u
    dsimp [φ] at hslice_xu
    rcases
      directionalSliceDerivativesAtZero_eq_ambientOwners
        (F := explicitUniversalBarrierAmbient c₁ Q) (x := x) (u := u) (hcontAt x hx) with
      ⟨_, hsecond, hthird⟩
    -- Rewrite the scalar cubic bound into the explicit ambient local-norm owner.
    calc
      |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u|
          = |iteratedDeriv 3 φ 0| := by
              rw [← hthird]
      _ ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) := hslice_xu.2
      _ = 2 * (Real.sqrt (inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)))
            ^ (3 : ℕ) := by
              rw [hsecond]
      _ = 2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) := by
              rw [hessianLocalNorm_def]
  exact
    explicitUniversalBarrierAmbient_isStandardSelfConcordantOn_of_pointwiseCore
      hQ_convex hcont hquad hthird

/-- Helper for PointwiseCore: standard self-concordance together with concavity of the matching
volume-power owner yields the full explicit ambient pointwise core. -/
theorem explicitUniversalBarrierAmbient_pointwiseCore_of_standardAndVolumeConcaveOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hstd :
      IsStandardSelfConcordantOn (interior Q) (explicitUniversalBarrierAmbient c₁ Q))
    (hconc :
      ConcaveOn ℝ (interior Q) (explicitUniversalBarrierVolumePowerAmbient c₁ ν Q))
    (hν : 0 < (ν : ℝ)) :
    ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) ∧
      (∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
      (∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
      (∀ x ∈ interior Q, ∀ u,
        (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) := by
  have hbarrier :
      IsSelfConcordantBarrierOnWith (interior Q) ν (explicitUniversalBarrierAmbient c₁ Q) :=
    (isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div hstd hν).2
      (explicitUniversalBarrierAmbient_expTransform_concave_of_volumePowerConcave
        (Q := Q) (c₁ := c₁) (ν := ν) hQ_convex hQ_noAffineLine hconc)
  have hpointwise :
      ∀ x ∈ interior Q,
        ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x ∧
          (∀ u, 0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
          (∀ u,
            |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
              2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
          (∀ u,
            (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
              (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) :=
    explicitUniversalBarrierAmbient_pointwiseData_of_barrierOnInterior hbarrier
  have hcont :
      ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) :=
    explicitUniversalBarrierAmbient_contDiffOn_of_pointwiseData (by
      intro x hx
      exact (hpointwise x hx).1)
  refine ⟨hcont, ?_, ?_, ?_⟩
  · -- The Hessian quadratic-form lower bound is already stored pointwise.
    intro x hx u
    exact (hpointwise x hx).2.1 u
  · -- The cubic estimate is the next field of the same pointwise package.
    intro x hx u
    exact (hpointwise x hx).2.2.1 u
  · -- The barrier-parameter estimate is the final projected field.
    intro x hx u
    exact (hpointwise x hx).2.2.2 u

/-- Helper for PointwiseCore: standard self-concordance together with the ambient gradient-square
field packages directly into the canonical universal-barrier owner. -/
private theorem universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_pointwiseCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hstd :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient c₁ Q))
    (hgrad :
      ∀ x ∈ interior Q, ∀ u,
        (inner ℝ (∇ (universalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (universalBarrierAmbient c₁ Q) x u)) :
    IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q) := by
  refine
    { toIsStandardSelfConcordantOn := hstd
      barrier_parameter_bound := ?_ }
  intro x hx u
  have hPos :
      (hessian (universalBarrierAmbient c₁ Q) x).IsPositive := hstd.hessian_isPositive hx
  -- Read the barrier owner from the pointwise gradient-square estimate once Hessian positivity
  -- is available from the standard-self-concordance parent.
  exact
    (IsSelfConcordantBarrierOnWith.gradient_sq_le_mul_hessian_iff_barrier_bound
      (F := universalBarrierAmbient c₁ Q) (x := x) (μ := ν) hPos).2
      (fun v ↦ hgrad x hx v) u

/-- Helper for PointwiseCore: any dependency-closed existence theorem for the explicit ambient
pointwise core already implies the canonical barrier witness on `interior Q`. -/
private theorem
    exists_absolute_constants_universalBarrierBarrierOnInterior_of_explicitPointwiseCore
    (hcore :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          ContDiffOn ℝ 3 F (interior Q) ∧
            (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
            (∀ x ∈ interior Q, ∀ u,
              |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
            (∀ x ∈ interior Q, ∀ u,
              (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
                (ν : ℝ) * inner ℝ u (hessian F x u))) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  rcases hcore with ⟨c₁, c₂, hcore⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hcore' :
      ContDiffOn ℝ 3 F (interior Q) ∧
        (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
        (∀ x ∈ interior Q, ∀ u,
          |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
        (∀ x ∈ interior Q, ∀ u,
          (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
            (ν : ℝ) * inner ℝ u (hessian F x u)) := by
    -- Freeze the explicit ambient owner and the dimension-scaled parameter before packaging the
    -- canonical barrier witness.
    simpa [F, ν] using hcore (Q := Q) hfin hQint hQ_convex hQ_noAffineLine
  rcases hcore' with ⟨hcont, hquad, hthird, hgrad⟩
  have hstdExplicit :
      IsStandardSelfConcordantOn (interior Q) (explicitUniversalBarrierAmbient (c₁ : ℝ) Q) :=
    explicitUniversalBarrierAmbient_isStandardSelfConcordantOn_of_pointwiseCore
      hQ_convex hcont hquad hthird
  have hstdAmbient :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient (c₁ : ℝ) Q) := by
    -- Normalize the source-facing owner to the canonical ambient one once at the standard API.
    simpa [explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using hstdExplicit
  have hgradAmbient :
      ∀ x ∈ interior Q, ∀ u,
        (inner ℝ (∇ (universalBarrierAmbient (c₁ : ℝ) Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (universalBarrierAmbient (c₁ : ℝ) Q) x u) := by
    intro x hx u
    -- The remaining pointwise barrier field transports across the same owner equality.
    simpa [F, ν, explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using
      hgrad x hx u
  exact
    universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_pointwiseCore
      (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν) hstdAmbient hgradAmbient

/-- Helper for PointwiseCore: any dependency-closed existence theorem giving standard
self-concordance of the explicit ambient owner together with concavity of the matching
volume-power owner already implies the canonical barrier witness on `interior Q`. -/
private theorem
    universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_explicitStandardAndVolumeConcaveOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hstd :
      IsStandardSelfConcordantOn (interior Q) (explicitUniversalBarrierAmbient c₁ Q))
    (hconc :
      ConcaveOn ℝ (interior Q) (explicitUniversalBarrierVolumePowerAmbient c₁ ν Q))
    (hν : 0 < (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q) := by
  have hconcExp :
      ConcaveOn ℝ (interior Q)
        (fun x ↦ Real.exp (-(explicitUniversalBarrierAmbient c₁ Q x / (ν : ℝ)))) :=
    -- Route correction: pass from the source-facing volume-power owner directly to the barrier
    -- criterion instead of rebuilding the whole pointwise-core package first.
    explicitUniversalBarrierAmbient_expTransform_concave_of_volumePowerConcave
      (Q := Q) (c₁ := c₁) (ν := ν) hQ_convex hQ_noAffineLine hconc
  have hbarrierExplicit :
      IsSelfConcordantBarrierOnWith (interior Q) ν (explicitUniversalBarrierAmbient c₁ Q) :=
    -- The standard-self-concordance plus transformed concavity criterion is exactly the barrier
    -- API for the explicit ambient owner.
    (isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div hstd hν).2 hconcExp
  -- Normalize the source-facing owner to the canonical ambient owner only once at the end.
  simpa [explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using hbarrierExplicit

/-- Helper for PointwiseCore: multiplying a positive finrank by an `NNRealˣ` constant keeps the
dimension-scaled barrier parameter strictly positive. -/
private theorem nnrealUnit_mul_finrank_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (c : NNRealˣ) (hfin : 0 < Module.finrank ℝ E) :
    (0 : NNReal) < (c : NNReal) * Module.finrank ℝ E := by
  -- Both factors are positive: `c` is a unit in `NNReal`, and the finrank hypothesis is strict.
  exact mul_pos (pos_iff_ne_zero.mpr (Units.ne_zero c)) (by exact_mod_cast hfin)

/-- Helper for PointwiseCore: the same dimension-scaled barrier parameter remains strictly
positive after coercing from `NNReal` to `ℝ`. -/
private theorem nnrealUnit_mul_finrank_pos_coe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (c : NNRealˣ) (hfin : 0 < Module.finrank ℝ E) :
    (0 : ℝ) < (((c : NNReal) * Module.finrank ℝ E : NNReal) : ℝ) := by
  -- Reuse the `NNReal` positivity statement and cast it once to the real target field.
  exact_mod_cast nnrealUnit_mul_finrank_pos (E := E) c hfin

/-- Helper for PointwiseCore: a barrier witness for the explicit ambient owner already contains
the standard self-concordance and volume-power concavity package on `interior Q`. -/
private theorem explicitUniversalBarrierAmbient_standardAndVolumeConcave_of_barrierOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hbarrier :
      IsSelfConcordantBarrierOnWith (interior Q) ν (explicitUniversalBarrierAmbient c₁ Q))
    (hν : 0 < (ν : ℝ)) :
    IsStandardSelfConcordantOn (interior Q) (explicitUniversalBarrierAmbient c₁ Q) ∧
      ConcaveOn ℝ (interior Q) (explicitUniversalBarrierVolumePowerAmbient c₁ ν Q) := by
  refine ⟨hbarrier.toIsStandardSelfConcordantOn, ?_⟩
  -- The barrier-to-volume-power concavity bridge is already proved for the explicit owner.
  exact
    explicitUniversalBarrierVolumePowerAmbient_concave_of_barrierOnInterior
      (Q := Q) (c₁ := c₁) (ν := ν) hQ_convex hQ_noAffineLine hbarrier hν

/-- Helper for PointwiseCore: once the ambient barrier seed itself is available, the weaker
source-facing standard-self-concordance plus volume-power-concavity existence package is only a
downstream projection. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_barrierOnInterior
    (hbarrier :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          IsSelfConcordantBarrierOnWith (interior Q)
            ((c₂ : NNReal) * Module.finrank ℝ E)
            (universalBarrierAmbient (c₁ : ℝ) Q)) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        IsStandardSelfConcordantOn (interior Q) F ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  rcases hbarrier with ⟨c₁, c₂, hbarrier⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hbarrier' :
      IsSelfConcordantBarrierOnWith (interior Q) ν F := by
    -- Transport the canonical ambient barrier owner to the explicit source-facing owner once.
    simpa [F, ν] using
      (explicitUniversalBarrierAmbient_barrierOnInterior_of_universalBarrierAmbient
        (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν)
        (hbarrier (Q := Q) hfin hQint hQ_convex hQ_noAffineLine))
  have hν : 0 < (ν : ℝ) :=
    nnrealUnit_mul_finrank_pos_coe (E := E) c₂ hfin
  -- Route correction: this file now records the easy downstream direction explicitly; only the
  -- converse seed `standard-and-volume => barrier` remains as the unresolved upstream premise.
  simpa [F, ν] using
    (explicitUniversalBarrierAmbient_standardAndVolumeConcave_of_barrierOnInterior
      (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν) hQ_convex hQ_noAffineLine hbarrier' hν)

/-- Helper for PointwiseCore: any dependency-closed existence theorem giving standard
self-concordance of the explicit ambient owner together with concavity of the matching
volume-power owner already implies the canonical barrier witness on `interior Q`. -/
private theorem
    exists_absolute_constants_universalBarrierBarrierOnInterior_of_standardAndVolumeConcaveOnInterior
    (hcore :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          IsStandardSelfConcordantOn (interior Q) F ∧
            ConcaveOn ℝ (interior Q)
              (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q)) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  rcases hcore with ⟨c₁, c₂, hcore⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hcore' :
      IsStandardSelfConcordantOn (interior Q) F ∧
        ConcaveOn ℝ (interior Q)
          (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
    -- Freeze the explicit owner and the dimension-scaled parameter before extracting the barrier
    -- witness from the weaker standard-self-concordance plus concavity package.
    simpa [F, ν] using hcore (Q := Q) hfin hQint hQ_convex hQ_noAffineLine
  rcases hcore' with ⟨hstd, hconc⟩
  have hν_pos : 0 < (ν : ℝ) := by
    -- Read positivity of the dimension-scaled parameter directly in `ℝ`.
    dsimp [ν]
    simpa using nnrealUnit_mul_finrank_pos_coe (E := E) c₂ hfin
  -- Route correction: apply the direct standard-plus-concavity bridge instead of detouring
  -- through the stronger pointwise-core package.
  exact
    universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_explicitStandardAndVolumeConcaveOnInterior
      (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν)
      hQ_convex hQ_noAffineLine (by simpa [F] using hstd) hconc hν_pos

/-- Helper for PointwiseCore: once the ambient explicit pointwise core is available, the
source-facing intrinsic pointwise-slice package follows by choosing the ambient directional slice
itself as the scalar witness on a short interval around `0`. -/
private theorem
    explicitUniversalBarrierAmbient_contDiffAtAndIntrinsicPointwiseSlice_of_pointwiseCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hcore :
      ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) ∧
        (∀ x ∈ interior Q, ∀ u,
          0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
        (∀ x ∈ interior Q, ∀ u,
          |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
            2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
        (∀ x ∈ interior Q, ∀ u,
          (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
            (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u))) :
    (∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x) ∧
      ∀ x ∈ interior Q, ∀ u,
        ∃ ε > 0, ∃ ψ : ℝ → ℝ,
          (∀ t : ℝ, |t| < ε →
            ∃ hxt : x + t • u ∈ interior Q,
              ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
          0 ≤ iteratedDeriv 2 ψ 0 ∧
            |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
            (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
  rcases hcore with ⟨hcont, hquad, hthird, hgrad⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    -- The open-domain `C³` owner immediately yields the pointwise base-point regularity.
    exact hcont.contDiffAt (isOpen_interior.mem_nhds hx)
  · intro x hx u
    rcases exists_pos_lineSliceRadius_eq_logVolumeAlongLine (c₁ := c₁) (Q := Q) (x := x) hx u with
      ⟨ε, hεpos, hεeq⟩
    let ψ : ℝ → ℝ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
    have hcontAt : ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x := by
      -- Reuse the same open-domain regularity when rewriting slice derivatives at `0`.
      exact hcont.contDiffAt (isOpen_interior.mem_nhds hx)
    have hψcore :
        0 ≤ iteratedDeriv 2 ψ 0 ∧
          |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
          (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
      rcases
        directionalSliceDerivativesAtZero_eq_ambientOwners
          (F := explicitUniversalBarrierAmbient c₁ Q) (x := x) (u := u) hcontAt with
        ⟨hderiv, hsecond, hthirdEq⟩
      dsimp [ψ]
      refine ⟨?_, ?_, ?_⟩
      · -- The scalar second derivative at `0` is the ambient Hessian quadratic form.
        rw [hsecond]
        exact hquad x hx u
      · -- The scalar cubic bound is exactly the ambient third-derivative estimate in direction `u`.
        calc
          |iteratedDeriv 3 ψ 0|
              = |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| := by
                  rw [hthirdEq]
          _ ≤ 2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) :=
                hthird x hx u
          _ = 2 * (Real.sqrt
                (inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u))) ^ (3 : ℕ) := by
                  rw [hessianLocalNorm_def]
          _ = 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) := by
                  rw [← hsecond]
      · -- The scalar gradient-square estimate is the ambient barrier-parameter field in disguise.
        calc
          (deriv ψ 0) ^ (2 : ℕ)
              = (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) := by
                  rw [hderiv]
          _ ≤ (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u) :=
                hgrad x hx u
          _ = (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
                rw [← hsecond]
    refine ⟨ε, hεpos, ψ, ?_, hψcore.1, hψcore.2.1, hψcore.2.2⟩
    intro t ht
    -- On the short interval where the ambient owner stays on its interior branch, `ψ` is exactly
    -- the required source-side `c₁ * log V` witness.
    simpa [ψ] using hεeq t ht

/-- Helper for PointwiseCore: any dependency-closed absolute-constants theorem for the ambient
explicit pointwise core already implies the source-facing intrinsic pointwise-slice frontier. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_contDiffAtAndIntrinsicPointwiseSlice_of_pointwiseCore
    (hcore :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          ContDiffOn ℝ 3 F (interior Q) ∧
            (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
            (∀ x ∈ interior Q, ∀ u,
              |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
            (∀ x ∈ interior Q, ∀ u,
              (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
                (ν : ℝ) * inner ℝ u (hessian F x u))) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
          ∀ x ∈ interior Q, ∀ u,
            ∃ ε > 0, ∃ ψ : ℝ → ℝ,
              (∀ t : ℝ, |t| < ε →
                ∃ hxt : x + t • u ∈ interior Q,
                  ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
              0 ≤ iteratedDeriv 2 ψ 0 ∧
                |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
                (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
  rcases hcore with ⟨c₁, c₂, hcore⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hcore' :
      ContDiffOn ℝ 3 F (interior Q) ∧
        (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
        (∀ x ∈ interior Q, ∀ u,
          |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
        (∀ x ∈ interior Q, ∀ u,
          (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
            (ν : ℝ) * inner ℝ u (hessian F x u)) := by
    -- Freeze the explicit owner and the dimension-scaled parameter before extracting the
    -- source-facing intrinsic slice witnesses.
    simpa [F, ν] using hcore (Q := Q) hfin hQint hQ_convex hQ_noAffineLine
  -- The existential bridge is now just the direct pointwise-core-to-intrinsic-slice packaging.
  simpa [F, ν] using
    (explicitUniversalBarrierAmbient_contDiffAtAndIntrinsicPointwiseSlice_of_pointwiseCore
      (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν) hcore')

/-- Helper for PointwiseCore: once an ambient barrier owner on `interior Q` is available, the
source-facing `ContDiffAt` and intrinsic line-slice barrier package follows directly. -/
theorem explicitUniversalBarrierAmbient_contDiffAtAndIntrinsicBarrierSlice_of_barrierOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hbarrier :
      IsSelfConcordantBarrierOnWith (interior Q) ν (explicitUniversalBarrierAmbient c₁ Q)) :
    (∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x) ∧
      ∀ x ∈ interior Q, ∀ u,
        ∃ ε > 0, ∃ ψ : ℝ → ℝ,
          (∀ t : ℝ, |t| < ε →
            ∃ hxt : x + t • u ∈ interior Q,
              ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
          IsSelfConcordantBarrierOnWith (Set.Ioo (-ε) ε) ν ψ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    -- Read the pointwise `C³` owner directly from the ambient barrier package.
    exact (explicitUniversalBarrierAmbient_pointwiseData_of_barrierOnInterior hbarrier x hx).1
  · intro x hx u
    let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x (x + u)
    have hline_apply : ∀ t : ℝ, line t = x + t • u := by
      intro t
      -- Use the affine-line normal form `x + t • ((x + u) - x)` to avoid manual transport.
      simpa [line, AffineMap.lineMap_apply_module', add_comm]
    have hlineFun :
        (explicitUniversalBarrierAmbient c₁ Q) ∘ line =
          directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u := by
      funext t
      simp [Function.comp, directionalSlice, hline_apply t]
    have hlineBarrierComp :
        IsSelfConcordantBarrierOnWith (line ⁻¹' interior Q) ν
          ((explicitUniversalBarrierAmbient c₁ Q) ∘ line) :=
      hbarrier.comp_affineMap line
    have hlineBarrier :
        IsSelfConcordantBarrierOnWith (line ⁻¹' interior Q) ν
          (directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u) := by
      -- Pull the ambient barrier through the scalar line parametrization once.
      rw [hlineFun] at hlineBarrierComp
      exact hlineBarrierComp
    rcases exists_pos_lineSliceRadius_eq_logVolumeAlongLine (c₁ := c₁) (Q := Q) (x := x) hx u with
      ⟨ε, hεpos, hεeq⟩
    refine ⟨ε, hεpos, directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u, hεeq, ?_⟩
    have hsubset : Set.Ioo (-ε) ε ⊆ line ⁻¹' interior Q := by
      intro t ht
      have htabs : |t| < ε := by
        simpa [abs_lt] using ht
      rcases hεeq t htabs with ⟨hxt, _⟩
      simpa [Set.mem_preimage, hline_apply t] using hxt
    -- Restrict the pulled-back barrier to the centered interval furnished by the slice formula.
    exact
      IsSelfConcordantBarrierOnWith.restrict hlineBarrier hsubset isOpen_Ioo
        (convex_Ioo (-ε) ε)

/-- Helper for PointwiseCore: once an ambient barrier owner on `interior Q` is available, the
source-facing ambient `C³` owner and the intrinsic scalar slice inequalities at `t = 0` follow
directly by projecting the interval barrier package to its pointwise-core fields. -/
theorem explicitUniversalBarrierAmbient_contDiffAtAndIntrinsicPointwiseSlice_of_barrierOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hbarrier :
      IsSelfConcordantBarrierOnWith (interior Q) ν (explicitUniversalBarrierAmbient c₁ Q)) :
    (∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x) ∧
      ∀ x ∈ interior Q, ∀ u,
        ∃ ε > 0, ∃ ψ : ℝ → ℝ,
          (∀ t : ℝ, |t| < ε →
            ∃ hxt : x + t • u ∈ interior Q,
              ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
          0 ≤ iteratedDeriv 2 ψ 0 ∧
            |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
            (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
  rcases
    explicitUniversalBarrierAmbient_contDiffAtAndIntrinsicBarrierSlice_of_barrierOnInterior
      hbarrier with ⟨hcontAt, hsliceBarrier⟩
  refine ⟨hcontAt, ?_⟩
  intro x hx u
  rcases hsliceBarrier x hx u with ⟨ε, hεpos, ψ, hψeq, hψbarrier⟩
  rcases slicePointwiseCoreAtZero_of_barrierOnInterval hεpos hψbarrier with
    ⟨_, hψsecond, hψthird, hψgradSq⟩
  -- The interval barrier on the intrinsic slice already contains the exact pointwise inequalities
  -- needed by the ambient pointwise-core bridge.
  exact ⟨ε, hεpos, ψ, hψeq, hψsecond, hψthird, hψgradSq⟩

/-- Helper for PointwiseCore: the remaining blocker has been reduced to the weaker analytic-core
existence theorem giving intrinsic slice bounds plus concavity of the matching volume-power
transform. -/
private theorem
    explicitUniversalBarrierAmbient_standardAndVolumeConcave_of_intrinsicSliceBoundsAndVolumePowerConcaveOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hQ_convex : Convex ℝ Q)
    (hcontAt :
      ∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x)
    (hsliceIntrinsic :
      ∀ x ∈ interior Q, ∀ u,
        ∃ ε > 0, ∃ ψ : ℝ → ℝ,
          (∀ t : ℝ, |t| < ε →
            ∃ hxt : x + t • u ∈ interior Q,
              ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
          0 ≤ iteratedDeriv 2 ψ 0 ∧
            |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ))
    (hconc :
      ConcaveOn ℝ (interior Q) (explicitUniversalBarrierVolumePowerAmbient c₁ ν Q)) :
    IsStandardSelfConcordantOn (interior Q) (explicitUniversalBarrierAmbient c₁ Q) ∧
      ConcaveOn ℝ (interior Q) (explicitUniversalBarrierVolumePowerAmbient c₁ ν Q) := by
  have hsliceStd :
      ∀ x ∈ interior Q,
        ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x ∧
          ∀ u,
            let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
            0 ≤ iteratedDeriv 2 φ 0 ∧
              |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) :=
    explicitUniversalBarrierAmbient_standardSliceData_of_intrinsicLogVolumeLineSlice
      (Q := Q) (c₁ := c₁) hcontAt hsliceIntrinsic
  refine ⟨?_, hconc⟩
  -- Package the transported scalar slice inequalities into standard self-concordance once.
  exact
    explicitUniversalBarrierAmbient_standardSelfConcordant_of_contDiffAtAndStandardSliceData
      (Q := Q) (c₁ := c₁) hQ_convex
      (by
        intro x hx
        exact (hsliceStd x hx).1)
      (by
        intro x hx u
        exact (hsliceStd x hx).2 u)

/-- Helper for PointwiseCore: fixed standard self-concordance together with volume-power
concavity already recovers the weaker intrinsic slice bounds while keeping the same concavity
field. -/
private theorem
    explicitUniversalBarrierAmbient_intrinsicSliceBoundsAndVolumePowerConcave_of_standardAndVolumeConcaveOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hstd :
      IsStandardSelfConcordantOn (interior Q) (explicitUniversalBarrierAmbient c₁ Q))
    (hconc :
      ConcaveOn ℝ (interior Q) (explicitUniversalBarrierVolumePowerAmbient c₁ ν Q))
    (hν : 0 < (ν : ℝ)) :
    (∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x) ∧
      (∀ x ∈ interior Q, ∀ u,
        ∃ ε > 0, ∃ ψ : ℝ → ℝ,
          (∀ t : ℝ, |t| < ε →
            ∃ hxt : x + t • u ∈ interior Q,
              ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
          0 ≤ iteratedDeriv 2 ψ 0 ∧
            |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) ∧
      ConcaveOn ℝ (interior Q) (explicitUniversalBarrierVolumePowerAmbient c₁ ν Q) := by
  have hcore :
      ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) ∧
        (∀ x ∈ interior Q, ∀ u,
          0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
        (∀ x ∈ interior Q, ∀ u,
          |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
            2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
        (∀ x ∈ interior Q, ∀ u,
          (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
            (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) := by
    -- Assemble the full ambient pointwise core once from the standard-plus-concavity package.
    exact
      explicitUniversalBarrierAmbient_pointwiseCore_of_standardAndVolumeConcaveOnInterior
        (Q := Q) (c₁ := c₁) (ν := ν) hQ_convex hQ_noAffineLine hstd hconc hν
  have hsliceStrong :
      (∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x) ∧
        ∀ x ∈ interior Q, ∀ u,
          ∃ ε > 0, ∃ ψ : ℝ → ℝ,
            (∀ t : ℝ, |t| < ε →
              ∃ hxt : x + t • u ∈ interior Q,
                ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
            0 ≤ iteratedDeriv 2 ψ 0 ∧
              |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
              (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
    -- Project the assembled pointwise core to the source-facing intrinsic slice package.
    exact
      explicitUniversalBarrierAmbient_contDiffAtAndIntrinsicPointwiseSlice_of_pointwiseCore
        (Q := Q) (c₁ := c₁) (ν := ν) hcore
  rcases hsliceStrong with ⟨hcontAt, hsliceStrong⟩
  refine ⟨hcontAt, ?_, hconc⟩
  intro x hx u
  rcases hsliceStrong x hx u with ⟨ε, hεpos, ψ, hψeq, hψsecond, hψthird, _hψgradSq⟩
  -- Drop the barrier-parameter field after the stronger intrinsic package has been assembled.
  exact ⟨ε, hεpos, ψ, hψeq, hψsecond, hψthird⟩

/-- Helper for PointwiseCore: any dependency-closed standard-self-concordance plus
volume-power-concavity existence theorem already implies the weaker intrinsic slice-bounds plus
concavity frontier. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_intrinsicSliceBoundsAndVolumePowerConcave_of_standardAndVolumeConcaveOnInterior
    (hcore :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          IsStandardSelfConcordantOn (interior Q) F ∧
            ConcaveOn ℝ (interior Q)
              (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q)) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
          (∀ x ∈ interior Q, ∀ u,
            ∃ ε > 0, ∃ ψ : ℝ → ℝ,
              (∀ t : ℝ, |t| < ε →
                ∃ hxt : x + t • u ∈ interior Q,
                  ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
              0 ≤ iteratedDeriv 2 ψ 0 ∧
                |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  rcases hcore with ⟨c₁, c₂, hcore⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hcore' :
      IsStandardSelfConcordantOn (interior Q) F ∧
        ConcaveOn ℝ (interior Q)
          (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
    -- Freeze the explicit owner and the dimension-scaled parameter before invoking the fixed-
    -- constants intrinsic-slice adapter.
    simpa [F, ν] using hcore (Q := Q) hfin hQint hQ_convex hQ_noAffineLine
  rcases hcore' with ⟨hstd, hconc⟩
  have hν : 0 < (ν : ℝ) :=
    nnrealUnit_mul_finrank_pos_coe (E := E) c₂ hfin
  -- Reuse the fixed-constants bridge to recover the weaker intrinsic-slice existence theorem.
  simpa [F, ν] using
    (explicitUniversalBarrierAmbient_intrinsicSliceBoundsAndVolumePowerConcave_of_standardAndVolumeConcaveOnInterior
      (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν)
      hQ_convex hQ_noAffineLine hstd hconc hν)

/-- Helper for PointwiseCore: once the primitive intrinsic slice-bounds plus volume-power-
concavity seed is available with common absolute constants, the corresponding standard
self-concordance plus volume-power-concavity package follows by the fixed-constants adapter. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_intrinsicSliceBoundsAndVolumePowerConcaveSeed
    (hseed :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E] {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
          (∀ x ∈ interior Q, ∀ u,
            ∃ ε > 0, ∃ ψ : ℝ → ℝ,
              (∀ t : ℝ, |t| < ε →
                ∃ hxt : x + t • u ∈ interior Q,
                  ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
              0 ≤ iteratedDeriv 2 ψ 0 ∧
                |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q)) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        IsStandardSelfConcordantOn (interior Q) F ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  rcases hseed with ⟨c₁, c₂, hseed⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hseed' :
      (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
        (∀ x ∈ interior Q, ∀ u,
          ∃ ε > 0, ∃ ψ : ℝ → ℝ,
            (∀ t : ℝ, |t| < ε →
              ∃ hxt : x + t • u ∈ interior Q,
                ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
            0 ≤ iteratedDeriv 2 ψ 0 ∧
              |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) ∧
        ConcaveOn ℝ (interior Q)
          (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
    -- Freeze the explicit owner and dimension-scaled parameter before invoking the primitive
    -- intrinsic slice seed once.
    simpa [F, ν] using hseed (Q := Q) hfin hQint hQ_convex hQ_noAffineLine
  rcases hseed' with ⟨hcontAt, hsliceIntrinsic, hconc⟩
  -- Package the primitive intrinsic slice witnesses first, then recover the standard
  -- self-concordance-plus-concavity owner through the fixed-constants adapter.
  simpa [F, ν] using
    (explicitUniversalBarrierAmbient_standardAndVolumeConcave_of_intrinsicSliceBoundsAndVolumePowerConcaveOnInterior
      (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν) hQ_convex hcontAt hsliceIntrinsic hconc)

/-- Helper for PointwiseCore: once the primitive intrinsic slice-bounds plus volume-power-
concavity seed is available with common absolute constants, the canonical ambient barrier witness
on `interior Q` follows by the existing intrinsic-to-standard and standard-to-barrier packaging
bridges. -/
private theorem
    exists_absolute_constants_universalBarrierAmbient_barrierOnInterior_of_intrinsicSliceBoundsAndVolumePowerConcaveSeed
    (hseed :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E] {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
          (∀ x ∈ interior Q, ∀ u,
            ∃ ε > 0, ∃ ψ : ℝ → ℝ,
              (∀ t : ℝ, |t| < ε →
                ∃ hxt : x + t • u ∈ interior Q,
                  ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
              0 ≤ iteratedDeriv 2 ψ 0 ∧
                |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q)) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  -- Route correction: collapse the remaining downstream packaging in one place so the unresolved
  -- frontier is exactly the primitive intrinsic-slice seed, not an extra standard/concavity alias.
  exact
    exists_absolute_constants_universalBarrierBarrierOnInterior_of_standardAndVolumeConcaveOnInterior
      (exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_intrinsicSliceBoundsAndVolumePowerConcaveSeed
        hseed)

/-- Helper for PointwiseCore: once a dependency-closed barrier witness on `interior Q` is available,
the weaker intrinsic slice-bounds-plus-volume-concavity frontier is only a downstream projection. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_intrinsicSliceBoundsAndVolumePowerConcave_of_barrierOnInterior
    (hbarrier :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          IsSelfConcordantBarrierOnWith (interior Q)
            ((c₂ : NNReal) * Module.finrank ℝ E)
            (universalBarrierAmbient (c₁ : ℝ) Q)) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
        (∀ x ∈ interior Q, ∀ u,
          ∃ ε > 0, ∃ ψ : ℝ → ℝ,
            (∀ t : ℝ, |t| < ε →
              ∃ hxt : x + t • u ∈ interior Q,
                ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
            0 ≤ iteratedDeriv 2 ψ 0 ∧
              |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) ∧
        ConcaveOn ℝ (interior Q)
          (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  rcases hbarrier with ⟨c₁, c₂, hbarrier⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hbarrier' :
      IsSelfConcordantBarrierOnWith (interior Q) ν F := by
    -- Normalize the canonical ambient barrier owner to the explicit owner before projecting the
    -- source-facing intrinsic slice and concavity data.
    simpa [F, ν] using
      (explicitUniversalBarrierAmbient_barrierOnInterior_of_universalBarrierAmbient
        (Q := Q) (c₁ := (c₁ : ℝ))
        (ν := (c₂ : NNReal) * Module.finrank ℝ E)
        (hbarrier (Q := Q) hfin hQint hQ_convex hQ_noAffineLine))
  have hsliceStrong :
      (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
        (∀ x ∈ interior Q, ∀ u,
          ∃ ε > 0, ∃ ψ : ℝ → ℝ,
            (∀ t : ℝ, |t| < ε →
              ∃ hxt : x + t • u ∈ interior Q,
                ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
            0 ≤ iteratedDeriv 2 ψ 0 ∧
              |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
              (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0) := by
    -- The ambient barrier package already gives the stronger intrinsic pointwise-slice theorem
    -- with the gradient-square estimate included.
    simpa [F, ν] using
      (explicitUniversalBarrierAmbient_contDiffAtAndIntrinsicPointwiseSlice_of_barrierOnInterior
        (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν) hbarrier')
  rcases hsliceStrong with ⟨hcontAt, hsliceStrong⟩
  have hν_pos : 0 < (ν : ℝ) := by
    -- Read positivity of the dimension-scaled barrier parameter directly in `ℝ`.
    dsimp [ν]
    simpa using nnrealUnit_mul_finrank_pos_coe (E := E) c₂ hfin
  have hconc :
      ConcaveOn ℝ (interior Q)
        (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) :=
    explicitUniversalBarrierVolumePowerAmbient_concave_of_barrierOnInterior
      (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν)
      hQ_convex hQ_noAffineLine hbarrier' hν_pos
  refine ⟨hcontAt, ?_, hconc⟩
  intro x hx u
  rcases hsliceStrong x hx u with ⟨ε, hεpos, ψ, hψeq, hψsecond, hψthird, _hψgradSq⟩
  -- Drop the gradient-square field from the stronger intrinsic package and keep the exact
  -- second/third-derivative slice bounds needed by the weaker frontier.
  exact ⟨ε, hεpos, ψ, hψeq, hψsecond, hψthird⟩

/-- Helper for PointwiseCore: the only unresolved upstream seed is now the dependency-closed
absolute-constants barrier witness for `universalBarrierAmbient` on `interior Q`. -/
private theorem exists_absolute_constants_universalBarrierAmbient_barrierOnInteriorSeed :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  -- Route correction: the downstream intrinsic-slice theorem is already a proved projection from a
  -- barrier witness, so the remaining frontier is exactly the barrier seed and not another local
  -- repackaging of its consequences.
  -- TODO: extract an earlier dependency-closed proof of this barrier witness, or move its canonical
  -- owner theorem into a support file that both `PointwiseCore` and `Theorem_5_4_2_2.lean` can
  -- import without creating an import cycle.
  sorry

/-- Helper for PointwiseCore: the upstream frontier is the primitive intrinsic slice-bounds plus
volume-power-concavity seed with common absolute constants. -/
private theorem exists_absolute_constants_explicitUniversalBarrier_intrinsicSliceBoundsAndVolumePowerConcaveSeed :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
        (∀ x ∈ interior Q, ∀ u,
          ∃ ε > 0, ∃ ψ : ℝ → ℝ,
            (∀ t : ℝ, |t| < ε →
              ∃ hxt : x + t • u ∈ interior Q,
                ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
            0 ≤ iteratedDeriv 2 ψ 0 ∧
              |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) ∧
        ConcaveOn ℝ (interior Q)
          (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  -- Route correction: this theorem is now only the fixed projection from the isolated barrier seed
  -- to the weaker intrinsic slice and volume-power package required downstream.
  exact
    exists_absolute_constants_explicitUniversalBarrier_intrinsicSliceBoundsAndVolumePowerConcave_of_barrierOnInterior
      exists_absolute_constants_universalBarrierAmbient_barrierOnInteriorSeed

/-- Helper for PointwiseCore: the weaker intrinsic-slice-plus-concavity seed packages directly
into standard self-concordance of the explicit owner together with the same concavity theorem. -/
private theorem exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcaveSeed :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        IsStandardSelfConcordantOn (interior Q) F ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  -- Route correction: keep the primitive seed owner fixed and reuse the parameterized packaging
  -- theorem, so the only unresolved frontier remains the primitive intrinsic-slice seed itself.
  exact
    exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_intrinsicSliceBoundsAndVolumePowerConcaveSeed
      exists_absolute_constants_explicitUniversalBarrier_intrinsicSliceBoundsAndVolumePowerConcaveSeed

/-- Helper for PointwiseCore: the only unresolved upstream seed is a dependency-closed absolute-
constants theorem making `universalBarrierAmbient` a barrier on `interior Q`. -/
private theorem exists_absolute_constants_universalBarrierAmbient_barrierOnInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  -- The open frontier is already stated at exactly this barrier-seed shape, so this local alias
  -- should reuse it directly rather than re-enter the downstream projection cycle.
  exact exists_absolute_constants_universalBarrierAmbient_barrierOnInteriorSeed

/-- Helper for PointwiseCore: any dependency-closed absolute-constants theorem giving a barrier
owner on `interior Q` already implies the remaining source-facing intrinsic pointwise-slice
frontier. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_contDiffAtAndIntrinsicPointwiseSlice_of_nonemptyInterior_of_barrierOnInterior
    (hbarrier :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          IsSelfConcordantBarrierOnWith (interior Q)
            ((c₂ : NNReal) * Module.finrank ℝ E)
            (universalBarrierAmbient (c₁ : ℝ) Q)) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
          ∀ x ∈ interior Q, ∀ u,
            ∃ ε > 0, ∃ ψ : ℝ → ℝ,
              (∀ t : ℝ, |t| < ε →
                ∃ hxt : x + t • u ∈ interior Q,
                  ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
              0 ≤ iteratedDeriv 2 ψ 0 ∧
                |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
                (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
  rcases hbarrier with ⟨c₁, c₂, hbarrier⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hbarrier' :
      IsSelfConcordantBarrierOnWith (interior Q) ν F := by
    -- First rewrite the canonical ambient barrier witness to the explicit owner used here.
    simpa [F, ν] using
      (explicitUniversalBarrierAmbient_barrierOnInterior_of_universalBarrierAmbient
        (Q := Q) (c₁ := (c₁ : ℝ))
        (ν := (c₂ : NNReal) * Module.finrank ℝ E)
        (hbarrier (Q := Q) hfin hQint hQ_convex hQ_noAffineLine))
  -- Then project the barrier owner directly to the source-facing intrinsic pointwise-slice
  -- package needed by the remaining frontier theorem.
  simpa [F, ν] using
    (explicitUniversalBarrierAmbient_contDiffAtAndIntrinsicPointwiseSlice_of_barrierOnInterior
      (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν) hbarrier')

/-- Helper for PointwiseCore: the weaker standard-self-concordance plus volume-power-concavity
existence package already implies the source-facing intrinsic pointwise-slice frontier. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_contDiffAtAndIntrinsicPointwiseSlice_of_standardAndVolumeConcaveOnInterior
    (hcore :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          IsStandardSelfConcordantOn (interior Q) F ∧
            ConcaveOn ℝ (interior Q)
              (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q)) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
          ∀ x ∈ interior Q, ∀ u,
            ∃ ε > 0, ∃ ψ : ℝ → ℝ,
              (∀ t : ℝ, |t| < ε →
                ∃ hxt : x + t • u ∈ interior Q,
                  ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
              0 ≤ iteratedDeriv 2 ψ 0 ∧
                |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
                (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
  -- Route correction: compose the weaker analytic core with the barrier bridge first, then
  -- project that barrier owner to the source-facing intrinsic slice package.
  exact
    exists_absolute_constants_explicitUniversalBarrier_contDiffAtAndIntrinsicPointwiseSlice_of_nonemptyInterior_of_barrierOnInterior
      (exists_absolute_constants_universalBarrierBarrierOnInterior_of_standardAndVolumeConcaveOnInterior
        hcore)

/-- Helper for PointwiseCore: once the dependency-closed standard-self-concordance plus
volume-power-concavity existence theorem is available, the remaining public intrinsic-slice
theorem is exactly the proved standard-and-volume adapter. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_contDiffAtAndIntrinsicPointwiseSlice_of_standardAndVolumeConcaveExistence
    (hstandardAndVolume :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          IsStandardSelfConcordantOn (interior Q) F ∧
            ConcaveOn ℝ (interior Q)
              (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q)) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
          ∀ x ∈ interior Q, ∀ u,
            ∃ ε > 0, ∃ ψ : ℝ → ℝ,
              (∀ t : ℝ, |t| < ε →
                ∃ hxt : x + t • u ∈ interior Q,
                  ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
              0 ≤ iteratedDeriv 2 ψ 0 ∧
                |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
                (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
  -- Route correction: the public theorem should only consume the weaker analytic-core existence
  -- theorem, leaving no extra existential repackaging work in the final statement.
  exact
    exists_absolute_constants_explicitUniversalBarrier_contDiffAtAndIntrinsicPointwiseSlice_of_standardAndVolumeConcaveOnInterior
      hstandardAndVolume

/-- Helper for PointwiseCore: the only remaining upstream analytic blocker is a dependency-closed
source-facing existence theorem providing ambient `C³` regularity together with the intrinsic
pointwise slice inequalities at `t = 0`. -/
theorem exists_absolute_constants_explicitUniversalBarrier_contDiffAtAndIntrinsicPointwiseSlice_of_nonemptyInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
          ∀ x ∈ interior Q, ∀ u,
            ∃ ε > 0, ∃ ψ : ℝ → ℝ,
              (∀ t : ℝ, |t| < ε →
                ∃ hxt : x + t • u ∈ interior Q,
                  ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
              0 ≤ iteratedDeriv 2 ψ 0 ∧
                |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
                (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
  -- Route correction: the remaining frontier is the upstream barrier theorem itself, so this
  -- public intrinsic-slice theorem is now just the direct barrier-to-slice adapter.
  exact
    exists_absolute_constants_explicitUniversalBarrier_contDiffAtAndIntrinsicPointwiseSlice_of_nonemptyInterior_of_barrierOnInterior
      exists_absolute_constants_universalBarrierAmbient_barrierOnInterior

/-- Helper for PointwiseCore: an intrinsic interval-local barrier witness transports to the ambient
directional-slice interface consumed by `CoreTransport`. -/
theorem explicitUniversalBarrierAmbient_barrierSlice_of_intrinsicLogVolumeLineSlice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal} {x : E} (hx : x ∈ interior Q) (u : E)
    {ε : ℝ} (hεpos : 0 < ε) {ψ : ℝ → ℝ}
    (hψeq :
      ∀ t : ℝ, |t| < ε →
        ∃ hxt : x + t • u ∈ interior Q,
          ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩))
    (hbarrier : IsSelfConcordantBarrierOnWith (Set.Ioo (-ε) ε) ν ψ) :
    ∃ ε' > 0, ∃ ψ' : ℝ → ℝ,
      directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u =ᶠ[nhds (0 : ℝ)] ψ' ∧
        IsSelfConcordantBarrierOnWith (Set.Ioo (-ε') ε') ν ψ' := by
  refine ⟨ε, hεpos, ψ, ?_, hbarrier⟩
  -- The ambient slice owner agrees with the intrinsic log-volume witness on a neighborhood of `0`.
  exact
    directionalSlice_eventuallyEq_intrinsicLogVolumeLineSlice
      (c₁ := c₁) (Q := Q) (x := x) hx u hεpos hψeq

/-- Helper for PointwiseCore: ambient `C³` regularity together with intrinsic scalar slice
inequalities packages directly into the ambient explicit pointwise core. -/
theorem
    explicitUniversalBarrierAmbient_pointwiseCore_of_contDiffAtAndIntrinsicPointwiseSliceData
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hcontAt :
      ∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x)
    (hsliceIntrinsic :
      ∀ x ∈ interior Q, ∀ u,
        ∃ ε > 0, ∃ ψ : ℝ → ℝ,
          (∀ t : ℝ, |t| < ε →
            ∃ hxt : x + t • u ∈ interior Q,
              ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
          0 ≤ iteratedDeriv 2 ψ 0 ∧
            |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
            (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0) :
    ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) ∧
      (∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
      (∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
      (∀ x ∈ interior Q, ∀ u,
        (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) := by
  have hslice :
      ∀ x ∈ interior Q, ∀ u,
        let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
        0 ≤ iteratedDeriv 2 φ 0 ∧
          |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) ∧
          (deriv φ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 φ 0 := by
    intro x hx u
    rcases hsliceIntrinsic x hx u with ⟨ε, hεpos, ψ, hψeq, hψsecond, hψthird, hψgradSq⟩
    -- Transport the intrinsic scalar inequalities across the neighborhood identity of the slices.
    simpa using
      directionalSlice_pointwiseCoreAtZero_of_intrinsicLogVolumeLineSlice
        (Q := Q) (c₁ := c₁) (x := x) hx u (ν := ν) hεpos hψeq hψsecond hψthird hψgradSq
  -- The generic slice-data packaging theorem now finishes the ambient pointwise core.
  exact explicitUniversalBarrierAmbient_pointwiseCore_of_contDiffAtAndSliceData hcontAt hslice

/-- Helper for PointwiseCore: once the ambient owner has pointwise `C³`/Hessian/cubic/gradient
data at each interior point, the full pointwise core is just the open-domain `ContDiffOn`
upgrade plus direct projection of the remaining fields. -/
theorem explicitUniversalBarrierAmbient_pointwiseCore_of_pointwiseData
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hpointwise :
      ∀ x ∈ interior Q,
        ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x ∧
          (∀ u, 0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
          (∀ u,
            |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
              2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
          (∀ u,
            (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
              (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u))) :
    ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) ∧
      (∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
      (∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
      (∀ x ∈ interior Q, ∀ u,
        (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) := by
  have hcontAt :
      ∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x := by
    -- The pointwise package stores the `ContDiffAt` field as its first component.
    intro x hx
    exact (hpointwise x hx).1
  have hcont :
      ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) :=
    -- Upgrade the pointwise `C³` control to the open-domain owner once.
    explicitUniversalBarrierAmbient_contDiffOn_of_pointwiseData hcontAt
  refine ⟨hcont, ?_, ?_, ?_⟩
  · -- The Hessian quadratic-form lower bound is already present pointwise.
    intro x hx u
    exact (hpointwise x hx).2.1 u
  · -- The cubic bound is the next field of the same pointwise package.
    intro x hx u
    exact (hpointwise x hx).2.2.1 u
  · -- The barrier-parameter gradient estimate is the final projected field.
    intro x hx u
    exact (hpointwise x hx).2.2.2 u

/-- Helper for PointwiseCore: any dependency-closed existence theorem giving ambient `C³`
regularity together with the intrinsic pointwise slice inequalities already packages into the
exported ambient pointwise core. -/
private theorem
    exists_absolute_constants_universalBarrier_pointwiseCore_of_intrinsicPointwiseSliceData
    (hslice :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
            ∀ x ∈ interior Q, ∀ u,
              ∃ ε > 0, ∃ ψ : ℝ → ℝ,
                (∀ t : ℝ, |t| < ε →
                  ∃ hxt : x + t • u ∈ interior Q,
                    ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
                0 ≤ iteratedDeriv 2 ψ 0 ∧
                  |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
                  (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        ContDiffOn ℝ 3 F (interior Q) ∧
          (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
          (∀ x ∈ interior Q, ∀ u,
            |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
          (∀ x ∈ interior Q, ∀ u,
            (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
              (ν : ℝ) * inner ℝ u (hessian F x u)) := by
  rcases hslice with ⟨c₁, c₂, hslice⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hslice' :
      (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
        ∀ x ∈ interior Q, ∀ u,
          ∃ ε > 0, ∃ ψ : ℝ → ℝ,
            (∀ t : ℝ, |t| < ε →
              ∃ hxt : x + t • u ∈ interior Q,
                ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
            0 ≤ iteratedDeriv 2 ψ 0 ∧
              |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
              (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
    -- Freeze the explicit owner and the dimension-scaled parameter before applying the intrinsic
    -- slice packaging theorem once.
    simpa [F, ν] using hslice (Q := Q) hfin hQint hQ_convex hQ_noAffineLine
  rcases hslice' with ⟨hcontAt, hsliceIntrinsic⟩
  -- The single-parameter packaging theorem already upgrades the source-facing slice data to the
  -- full ambient pointwise core.
  simpa [F, ν] using
    (explicitUniversalBarrierAmbient_pointwiseCore_of_contDiffAtAndIntrinsicPointwiseSliceData
      (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν) hcontAt hsliceIntrinsic)

/-- Helper for PointwiseCore: a dependency-closed barrier witness on `interior Q` packages
directly into the exported ambient pointwise core. -/
private theorem exists_absolute_constants_universalBarrier_pointwiseCore_of_barrierOnInterior
    (hbarrier :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          IsSelfConcordantBarrierOnWith (interior Q)
            ((c₂ : NNReal) * Module.finrank ℝ E)
            (universalBarrierAmbient (c₁ : ℝ) Q)) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        ContDiffOn ℝ 3 F (interior Q) ∧
          (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
          (∀ x ∈ interior Q, ∀ u,
            |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
          (∀ x ∈ interior Q, ∀ u,
            (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
              (ν : ℝ) * inner ℝ u (hessian F x u)) := by
  rcases hbarrier with ⟨c₁, c₂, hbarrier⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hbarrier' :
      IsSelfConcordantBarrierOnWith (interior Q) ν F := by
    -- Rewrite the canonical ambient barrier witness once to the explicit owner used here.
    simpa [F, ν] using
      (explicitUniversalBarrierAmbient_barrierOnInterior_of_universalBarrierAmbient
        (Q := Q) (c₁ := (c₁ : ℝ))
        (ν := (c₂ : NNReal) * Module.finrank ℝ E)
        (hbarrier (Q := Q) hfin hQint hQ_convex hQ_noAffineLine))
  have hpointwise :
      ∀ x ∈ interior Q,
        ContDiffAt ℝ 3 F x ∧
          (∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
          (∀ u,
            |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
          (∀ u,
            (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
              (ν : ℝ) * inner ℝ u (hessian F x u)) := by
    -- Project the pointwise barrier fields before packaging them back into the open-domain core.
    simpa [F, ν] using
      (explicitUniversalBarrierAmbient_pointwiseData_of_barrierOnInterior
        (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν) hbarrier')
  -- The ambient pointwise package is exactly the input expected by the core assembly lemma.
  simpa [F, ν] using
    (explicitUniversalBarrierAmbient_pointwiseCore_of_pointwiseData
      (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν) hpointwise)

/-- Helper for PointwiseCore: pointwise core data on the explicit ambient owner also recovers the
standard scalar directional-slice inequalities at each interior base point. -/
private theorem explicitUniversalBarrierAmbient_standardSliceData_of_pointwiseCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ}
    (hcont :
      ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q))
    (hquad :
      ∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u))
    (hthird :
      ∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) :
    ∀ x ∈ interior Q,
      ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x ∧
        ∀ u,
          let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
          0 ≤ iteratedDeriv 2 φ 0 ∧
            |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) := by
  intro x hx
  have hcontAt : ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x := by
    -- The open-domain `ContDiffOn` owner gives the pointwise `C³` base point directly.
    exact hcont.contDiffAt (isOpen_interior.mem_nhds hx)
  refine ⟨hcontAt, ?_⟩
  intro u
  -- Rewrite the scalar slice derivatives once to the ambient Hessian and third-derivative owners.
  rcases
    directionalSliceDerivativesAtZero_eq_ambientOwners
      (F := explicitUniversalBarrierAmbient c₁ Q) (x := x) (u := u) hcontAt with
    ⟨_, hsecond, hthirdEq⟩
  dsimp
  refine ⟨?_, ?_⟩
  · -- The scalar second derivative at `0` is the Hessian quadratic form in direction `u`.
    rw [hsecond]
    exact hquad x hx u
  · calc
      |iteratedDeriv 3 (directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u) 0|
          = |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| := by
              rw [hthirdEq]
      _ ≤ 2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) :=
            hthird x hx u
      _ = 2 * (Real.sqrt
            (inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u))) ^ (3 : ℕ) := by
              rw [hessianLocalNorm_def]
      _ = 2 * (Real.sqrt
            (iteratedDeriv 2 (directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u) 0))
            ^ (3 : ℕ) := by
              rw [← hsecond]

-- Route correction: the main theorem now consumes the ambient pointwise package directly instead
-- of rebuilding slice transport from the downstream intrinsic-slice surrogate.
theorem exists_absolute_constants_universalBarrier_pointwiseCore_of_nonemptyInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        ContDiffOn ℝ 3 F (interior Q) ∧
          (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
          (∀ x ∈ interior Q, ∀ u,
            |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
          (∀ x ∈ interior Q, ∀ u,
            (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
              (ν : ℝ) * inner ℝ u (hessian F x u)) := by
  -- Route correction: the exported pointwise core should be recovered from the source-facing
  -- intrinsic-slice package, leaving the barrier seed as an upstream prerequisite only for that
  -- source-facing theorem.
  exact
    exists_absolute_constants_universalBarrier_pointwiseCore_of_intrinsicPointwiseSliceData
      exists_absolute_constants_explicitUniversalBarrier_contDiffAtAndIntrinsicPointwiseSlice_of_nonemptyInterior

/-- Helper for PointwiseCore: once the exported ambient pointwise core is available, the local
interior `C³`/Hessian/cubic/gradient package is recovered by projecting `ContDiffOn` to
`ContDiffAt` and reusing the remaining pointwise fields verbatim. -/
private theorem
    exists_absolute_constants_universalBarrier_pointwiseDataAtInterior_of_pointwiseCore :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        ∀ x ∈ interior Q,
          ContDiffAt ℝ 3 F x ∧
            (∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
            (∀ u,
              |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
            (∀ u,
              (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
                (ν : ℝ) * inner ℝ u (hessian F x u)) := by
  rcases exists_absolute_constants_universalBarrier_pointwiseCore_of_nonemptyInterior with
    ⟨c₁, c₂, hcore⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hcore' :
      ContDiffOn ℝ 3 F (interior Q) ∧
        (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
        (∀ x ∈ interior Q, ∀ u,
          |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
        (∀ x ∈ interior Q, ∀ u,
          (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
            (ν : ℝ) * inner ℝ u (hessian F x u)) := by
    -- Freeze the ambient owner and the dimension-scaled parameter before projecting pointwise.
    simpa [F, ν] using hcore (Q := Q) hfin hQint hQ_convex hQ_noAffineLine
  rcases hcore' with ⟨hcont, hquad, hthird, hgrad⟩
  -- Eliminate the local `let` abbreviations before introducing the pointwise base point.
  dsimp [F, ν]
  intro x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The open-domain `ContDiffOn` owner immediately yields the pointwise `ContDiffAt` field.
    exact hcont.contDiffAt (isOpen_interior.mem_nhds hx)
  · -- The Hessian quadratic-form lower bound is already present in the exported pointwise core.
    intro u
    exact hquad x hx u
  · -- The cubic bound is the next projected field of the same core package.
    intro u
    exact hthird x hx u
  · -- The gradient-square estimate is the final field reused without further transport.
    intro u
    exact hgrad x hx u

/-- Helper for PointwiseCore: after the exported source-facing pointwise core theorem is available,
the canonical barrier witness on `interior Q` is immediate from the existing packaging lemma. This
post-hoc theorem records the correct dependency direction for the pending file-structure repair. -/
private theorem
    exists_absolute_constants_universalBarrierBarrierOnInterior_from_pointwiseCore :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  -- Route correction: the proved pointwise-core export is exactly the missing premise for the
  -- canonical barrier packaging lemma, so the dependency runs from the export to the barrier.
  exact
    exists_absolute_constants_universalBarrierBarrierOnInterior_of_explicitPointwiseCore
      exists_absolute_constants_universalBarrier_pointwiseCore_of_nonemptyInterior

/-- Helper for PointwiseCore: once the exported ambient pointwise core is available, the weaker
standard-slice-data plus volume-power-concavity package is a downstream projection. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_standardSliceDataAndVolumePowerConcave_of_pointwiseCoreData
    (hcore :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          ContDiffOn ℝ 3 F (interior Q) ∧
            (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
            (∀ x ∈ interior Q, ∀ u,
              |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
            (∀ x ∈ interior Q, ∀ u,
              (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
                (ν : ℝ) * inner ℝ u (hessian F x u))) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q,
          ContDiffAt ℝ 3 F x ∧
            ∀ u,
              let φ := directionalSlice F x u
              0 ≤ iteratedDeriv 2 φ 0 ∧
                |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ)) ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  rcases hcore with ⟨c₁, c₂, hcore⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hcore' :
      ContDiffOn ℝ 3 F (interior Q) ∧
        (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
        (∀ x ∈ interior Q, ∀ u,
          |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
        (∀ x ∈ interior Q, ∀ u,
          (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
            (ν : ℝ) * inner ℝ u (hessian F x u)) := by
    -- Freeze the explicit owner and the dimension-scaled parameter before projecting the weaker
    -- downstream package from the supplied pointwise core.
    simpa [F, ν] using hcore (Q := Q) hfin hQint hQ_convex hQ_noAffineLine
  rcases hcore' with ⟨hcont, hquad, hthird, hgrad⟩
  have hsliceStd :
      ∀ x ∈ interior Q,
        ContDiffAt ℝ 3 F x ∧
          ∀ u,
            let φ := directionalSlice F x u
            0 ≤ iteratedDeriv 2 φ 0 ∧
              |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) :=
    explicitUniversalBarrierAmbient_standardSliceData_of_pointwiseCore
      (c₁ := (c₁ : ℝ)) (Q := Q) hcont hquad hthird
  have hstdAmbient :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient (c₁ : ℝ) Q) := by
    have hstdExplicit :
        IsStandardSelfConcordantOn (interior Q) F :=
      explicitUniversalBarrierAmbient_isStandardSelfConcordantOn_of_pointwiseCore
        hQ_convex hcont hquad hthird
    -- Normalize the explicit owner only once when assembling the canonical ambient barrier.
    simpa [F, explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using hstdExplicit
  have hgradAmbient :
      ∀ x ∈ interior Q, ∀ u,
        (inner ℝ (∇ (universalBarrierAmbient (c₁ : ℝ) Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (universalBarrierAmbient (c₁ : ℝ) Q) x u) := by
    intro x hx u
    -- The gradient-square field transports across the same owner equality.
    simpa [F, ν, explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using
      hgrad x hx u
  have hbarrierExplicit :
      IsSelfConcordantBarrierOnWith (interior Q) ν F := by
    have hbarrierAmbient :
        IsSelfConcordantBarrierOnWith (interior Q) ν
          (universalBarrierAmbient (c₁ : ℝ) Q) :=
      universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_pointwiseCore
        (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν) hstdAmbient hgradAmbient
    -- Switch back to the explicit owner only for the source-facing volume-power projection.
    simpa [F, explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using hbarrierAmbient
  have hν_pos : 0 < (ν : ℝ) := by
    -- Read positivity of the dimension-scaled parameter directly in `ℝ`.
    dsimp [ν]
    simpa using nnrealUnit_mul_finrank_pos_coe (E := E) c₂ hfin
  have hconc :
      ConcaveOn ℝ (interior Q)
        (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) :=
    explicitUniversalBarrierVolumePowerAmbient_concave_of_barrierOnInterior
      (Q := Q) (c₁ := (c₁ : ℝ)) (ν := ν)
      hQ_convex hQ_noAffineLine hbarrierExplicit hν_pos
  exact ⟨hsliceStd, hconc⟩

/-- Helper for PointwiseCore: specializing the parameterized pointwise-core-to-standard-slice
projection to the exported pointwise core recovers the existing downstream package. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_standardSliceDataAndVolumePowerConcave_of_pointwiseCore :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q,
          ContDiffAt ℝ 3 F x ∧
            ∀ u,
              let φ := directionalSlice F x u
              0 ≤ iteratedDeriv 2 φ 0 ∧
                |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ)) ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  -- Reuse the parameterized downstream projection on the exported ambient pointwise core.
  exact
    exists_absolute_constants_explicitUniversalBarrier_standardSliceDataAndVolumePowerConcave_of_pointwiseCoreData
      exists_absolute_constants_universalBarrier_pointwiseCore_of_nonemptyInterior

/-- Helper for PointwiseCore: the exported ambient pointwise core also recovers the weaker
standard-self-concordance plus volume-power-concavity package as a downstream projection. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_pointwiseCoreData
    (hcore :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          ContDiffOn ℝ 3 F (interior Q) ∧
            (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
            (∀ x ∈ interior Q, ∀ u,
              |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
            (∀ x ∈ interior Q, ∀ u,
              (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
                (ν : ℝ) * inner ℝ u (hessian F x u))) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        IsStandardSelfConcordantOn (interior Q) F ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  rcases
    exists_absolute_constants_explicitUniversalBarrier_standardSliceDataAndVolumePowerConcave_of_pointwiseCoreData
      hcore with
    ⟨c₁, c₂, hdata⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hdata' :
      (∀ x ∈ interior Q,
        ContDiffAt ℝ 3 F x ∧
          ∀ u,
            let φ := directionalSlice F x u
            0 ≤ iteratedDeriv 2 φ 0 ∧
              |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ)) ∧
        ConcaveOn ℝ (interior Q)
          (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
    -- Freeze the explicit owner and the dimension-scaled parameter before assembling the weaker
    -- standard-self-concordance package.
    simpa [F, ν] using hdata (Q := Q) hfin hQint hQ_convex hQ_noAffineLine
  rcases hdata' with ⟨hsliceStd, hconc⟩
  have hstd :
      IsStandardSelfConcordantOn (interior Q) F :=
    explicitUniversalBarrierAmbient_standardSelfConcordant_of_contDiffAtAndStandardSliceData
      (Q := Q) (c₁ := (c₁ : ℝ)) hQ_convex
      (by
        intro x hx
        exact (hsliceStd x hx).1)
      (by
        intro x hx u
        exact (hsliceStd x hx).2 u)
  exact ⟨hstd, hconc⟩

/-- Helper for PointwiseCore: specializing the parameterized pointwise-core-to-standard-plus-
concavity projection to the exported pointwise core recovers the existing downstream package. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_pointwiseCore :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        IsStandardSelfConcordantOn (interior Q) F ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  -- Reuse the parameterized downstream projection on the exported ambient pointwise core.
  exact
    exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_pointwiseCoreData
      exists_absolute_constants_universalBarrier_pointwiseCore_of_nonemptyInterior

/-- Helper for PointwiseCore: once a dependency-closed intrinsic pointwise-slice theorem is
available, the entire remaining downstream route to the ambient barrier witness is just
intrinsic slices -> explicit pointwise core -> standard plus volume concavity -> barrier. -/
private theorem
    exists_absolute_constants_universalBarrierAmbient_barrierOnInterior_of_intrinsicPointwiseSliceData
    (hslice :
      ∃ c₁ c₂ : NNRealˣ,
        ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
          {Q : Set E},
          0 < Module.finrank ℝ E →
          (interior Q).Nonempty →
          Convex ℝ Q →
          (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
          let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
          let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
          (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
            ∀ x ∈ interior Q, ∀ u,
              ∃ ε > 0, ∃ ψ : ℝ → ℝ,
                (∀ t : ℝ, |t| < ε →
                  ∃ hxt : x + t • u ∈ interior Q,
                    ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
                0 ≤ iteratedDeriv 2 ψ 0 ∧
                  |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
                  (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0) :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  -- Route correction: once the source-facing intrinsic theorem is imported upstream, no further
  -- new analysis is needed in this file; the remaining steps are the already-proved packaging
  -- theorems.
  exact
    exists_absolute_constants_universalBarrierBarrierOnInterior_of_standardAndVolumeConcaveOnInterior
      (exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_pointwiseCoreData
        (exists_absolute_constants_universalBarrier_pointwiseCore_of_intrinsicPointwiseSliceData
          hslice))

/-- Helper for PointwiseCore: once the exported pointwise core is available, the weaker intrinsic
slice-bounds-plus-volume-concavity frontier is a downstream projection. -/
private theorem
    exists_absolute_constants_explicitUniversalBarrier_intrinsicSliceBoundsAndVolumePowerConcave_of_pointwiseCore :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
        (∀ x ∈ interior Q, ∀ u,
          ∃ ε > 0, ∃ ψ : ℝ → ℝ,
            (∀ t : ℝ, |t| < ε →
              ∃ hxt : x + t • u ∈ interior Q,
                ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
            0 ≤ iteratedDeriv 2 ψ 0 ∧
              |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) ∧
        ConcaveOn ℝ (interior Q)
          (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  -- Route correction: go through the already-packaged standard-plus-concavity existence theorem,
  -- then drop only the gradient-square field via the new intrinsic-slice adapter.
  exact
    exists_absolute_constants_explicitUniversalBarrier_intrinsicSliceBoundsAndVolumePowerConcave_of_standardAndVolumeConcaveOnInterior
      (exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_pointwiseCoreData
        exists_absolute_constants_universalBarrier_pointwiseCore_of_nonemptyInterior)

/-- Helper for PointwiseCore: after the exported pointwise core theorem is available, the
canonical barrier witness on `interior Q` is just the existing downstream packaging theorem. -/
theorem exists_absolute_constants_universalBarrierBarrierOnInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  -- Route correction: once the public intrinsic slice theorem is available, expose the barrier
  -- witness through the fully parameterized downstream packaging chain.
  exact
    exists_absolute_constants_universalBarrierAmbient_barrierOnInterior_of_intrinsicPointwiseSliceData
      exists_absolute_constants_explicitUniversalBarrier_contDiffAtAndIntrinsicPointwiseSlice_of_nonemptyInterior

/-- Helper for PointwiseCore: after the exported pointwise core theorem is available, the weaker
intrinsic slice-bounds-plus-volume-concavity frontier is a downstream projection. -/
theorem
    exists_absolute_constants_explicitUniversalBarrier_intrinsicSliceBoundsAndVolumePowerConcave_of_nonemptyInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q, ContDiffAt ℝ 3 F x) ∧
        (∀ x ∈ interior Q, ∀ u,
          ∃ ε > 0, ∃ ψ : ℝ → ℝ,
            (∀ t : ℝ, |t| < ε →
              ∃ hxt : x + t • u ∈ interior Q,
                ψ t = (c₁ : ℝ) * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
            0 ≤ iteratedDeriv 2 ψ 0 ∧
              |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) ∧
        ConcaveOn ℝ (interior Q)
          (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  exact
    exists_absolute_constants_explicitUniversalBarrier_intrinsicSliceBoundsAndVolumePowerConcave_of_pointwiseCore

/-- Helper for PointwiseCore: once the exported pointwise core theorem is available, the weaker
standard-slice-data plus volume-power-concavity package is also just a downstream projection. -/
theorem
    exists_absolute_constants_explicitUniversalBarrier_standardSliceDataAndVolumePowerConcave_of_nonemptyInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q,
          ContDiffAt ℝ 3 F x ∧
            ∀ u,
              let φ := directionalSlice F x u
              0 ≤ iteratedDeriv 2 φ 0 ∧
                |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ)) ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  exact
    exists_absolute_constants_explicitUniversalBarrier_standardSliceDataAndVolumePowerConcave_of_pointwiseCore

/-- Helper for PointwiseCore: once the exported pointwise core theorem is available, the weaker
standard-self-concordance plus volume-power-concavity package is likewise downstream. -/
theorem
    exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_nonemptyInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        IsStandardSelfConcordantOn (interior Q) F ∧
          ConcaveOn ℝ (interior Q)
            (explicitUniversalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  exact exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_pointwiseCore

/-- Helper for PointwiseCore: once the later public standard-self-concordance plus
volume-power-concavity theorem is available, the original ambient barrier seed is recovered
verbatim by the existing bridge. This isolates the unresolved frontier to extracting that weaker
analytic core upstream, not to any missing local packaging theorem. -/
private theorem
    exists_absolute_constants_universalBarrierAmbient_barrierOnInterior_of_standardAndVolumeConcaveExistence :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  -- The later public analytic core has exactly the hypothesis shape consumed by the canonical
  -- barrier packaging theorem proved earlier in this file.
  exact
    exists_absolute_constants_universalBarrierBarrierOnInterior_of_standardAndVolumeConcaveOnInterior
      exists_absolute_constants_explicitUniversalBarrier_standardAndVolumeConcave_of_nonemptyInterior

/-- Helper for PointwiseCore: once the exported pointwise core theorem is available, the ambient
pointwise `C³`/Hessian/cubic/gradient package is a direct downstream projection. -/
theorem exists_absolute_constants_universalBarrier_pointwiseDataAtInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        ∀ x ∈ interior Q,
          ContDiffAt ℝ 3 F x ∧
            (∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
            (∀ u,
              |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
            (∀ u,
              (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
              (ν : ℝ) * inner ℝ u (hessian F x u)) := by
  exact exists_absolute_constants_universalBarrier_pointwiseDataAtInterior_of_pointwiseCore
