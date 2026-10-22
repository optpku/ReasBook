/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Holder
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_21
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_27

open Set
open scoped Interval Topology

-- Domain sampling:
-- * core/canonical owners: `HasFDerivAt`, `HasStrictFDerivAt`
-- * chapter bridge/view owner for Gateaux differentiability:
--   `IsGateauxDerivativeWithinAt` / `SunYuanGateauxDifferentiableWithinAt`
-- * chapter bridge/view owner for linewise within-set continuity:
--   `AlongLineWithinAt`
-- * chapter source-facing owner for Euclidean-valued directional hemicontinuity:
--   `DirectionalHemicontinuousWithinAt`

/-
Canonical recall for the two source definitions from Chapter01 Definition 1.2.28.

Fréchet differentiability at `x` with derivative `A` is formalized by `HasFDerivAt F A x`.
Fréchet differentiability at `x` without a chosen derivative is formalized by
`DifferentiableAt ℝ F x`.
Strong Fréchet differentiability at `x` with derivative `A` is formalized by
`HasStrictFDerivAt F A x`.

The Gateaux bridge owner from the previous item is `SunYuanGateauxDifferentiableWithinAt`, with primitive
directional-derivative data recorded by `IsGateauxDerivativeWithinAt`.

The linewise continuity owner reused below is `AlongLineWithinAt`; the source-facing Euclidean
specialization from Definition 1.2.21 is `DirectionalHemicontinuousWithinAt`.

The remaining numbered source consequences are recorded below using these existing owners.
-/

#check HasFDerivAt
#check DifferentiableAt
#check HasStrictFDerivAt
#check IsGateauxDerivativeWithinAt
#check SunYuanGateauxDifferentiableWithinAt
#check DirectionalHemicontinuousWithinAt

section GenericNormed

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Consequence of Chapter01 Definition 1.2.28 (5): Fréchet differentiability at `x ∈ D` implies
Gateaux differentiability there. This bridge theorem lives at the same generic owner level as
`SunYuanGateauxDifferentiableWithinAt`; the source `ℝⁿ → ℝᵐ` statement is its Euclidean specialization. -/
theorem gateauxDifferentiableWithinAt_of_hasFDerivAt
    {D : Set E} {F : E → G} {A : E →L[𝕜] G} {x : E}
    (hD_open : IsOpen D)
    (hx : x ∈ D)
    (hF : HasFDerivAt F A x) :
    SunYuanGateauxDifferentiableWithinAt 𝕜 D F x := by
  -- Package the Fréchet derivative together with its induced line derivatives.
  refine ⟨hD_open, hx, A, ?_⟩
  intro d
  exact (hF.hasLineDerivAt d).hasLineDerivWithinAt D

/-- Consequence of Chapter01 Definition 1.2.28 (8): whenever both a Gateaux derivative `B`
and a Fréchet derivative `A` exist at `x ∈ D`, they are equal as linear maps. This uniqueness
bridge theorem belongs to the same generic normed-field layer as the Gateaux owner. -/
theorem gateauxDerivative_eq_fderiv
    {D : Set E} {F : E → G} {A B : E →L[𝕜] G} {x : E}
    (hD_open : IsOpen D)
    (hx : x ∈ D)
    (hGateaux : IsGateauxDerivativeWithinAt 𝕜 D F x B)
    (hF : HasFDerivAt F A x) :
    A = B := by
  -- Compare both derivatives on each direction and use uniqueness of the 1D derivative.
  ext d
  exact HasLineDerivAt.unique (hF.hasLineDerivAt d)
    ((hGateaux d).hasLineDerivAt (hD_open.mem_nhds hx))

end GenericNormed

section RealNormed

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Consequence of Chapter01 Definition 1.2.28 (1): continuity at `x` implies
linewise within-set continuity on `Set.univ`; the source's directional
hemi-continuity statement is its Euclidean specialization. -/
theorem alongLineWithinAt_univ_of_continuousAt
    (F : E → G) (x : E) (hF : ContinuousAt F x) :
    AlongLineWithinAt ContinuousWithinAt Set.univ F x := by
  refine ⟨by simp, ?_⟩
  intro d
  -- Compose continuity of `F` at `x` with the ambient line through `x`.
  have hline : ContinuousAt (fun t : ℝ ↦ x + t • d) 0 := by
    fun_prop
  change ContinuousWithinAt (F ∘ fun t : ℝ ↦ x + t • d) Set.univ 0
  simpa using
    (hF.comp_continuousWithinAt_of_eq hline.continuousWithinAt (by simp) :
      ContinuousWithinAt (F ∘ fun t : ℝ ↦ x + t • d) Set.univ 0)

/-- Consequence of Chapter01 Definition 1.2.28 (2): Gateaux differentiability on
the open set `D` at `x` implies linewise within-set continuity there. -/
theorem alongLineWithinAt_of_gateauxDifferentiableWithinAt
    {D : Set E} {F : E → G} {x : E}
    (hG : SunYuanGateauxDifferentiableWithinAt ℝ D F x) :
    AlongLineWithinAt ContinuousWithinAt D F x := by
  rcases hG with ⟨_, hx, A, hA⟩
  refine ⟨hx, ?_⟩
  intro d
  -- A within-set line derivative gives within-set continuity along the same line.
  exact (hA d).continuousWithinAt

/- Chapter01 Definition 1.2.28 (3): Fréchet differentiability at `x` implies continuity
at `x`. -/
#check HasFDerivAt.continuousAt

/- Chapter01 Definition 1.2.28 (4): strong Fréchet differentiability at `x` implies Fréchet
differentiability at `x`. -/
#check HasStrictFDerivAt.hasFDerivAt

/-- Helper for Chapter01 Definition 1.2.28: a point on the affine line through `x` and `y`
can be re-expanded from the base parameter `t` by the displacement `(s - t) • (y - x)`. -/
lemma lineMapApply_eq_baseAdd_smul_sub
    {x y : E} {s t : ℝ} :
    AffineMap.lineMap x y s = AffineMap.lineMap x y t + (s - t) • (y - x) := by
  -- Expand both affine points from the same base point `x` and collect the direction terms.
  have hs : s = t + (s - t) := by ring
  calc
    AffineMap.lineMap x y s = x + s • (y - x) := by
      simp [AffineMap.lineMap_apply_module', add_comm]
    _ = x + (t + (s - t)) • (y - x) := by
      exact congrArg (fun r : E ↦ x + r) (congrArg (fun r : ℝ ↦ r • (y - x)) hs)
    _ = x + (t • (y - x) + (s - t) • (y - x)) := by rw [add_smul]
    _ = (x + t • (y - x)) + (s - t) • (y - x) := by rw [add_assoc]
    _ = AffineMap.lineMap x y t + (s - t) • (y - x) := by
      simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Chapter01 Definition 1.2.28: along a convex segment, the chapter's Gateaux
derivative data turns into an ordinary one-variable derivative for the pulled-back segment map. -/
lemma segmentHasDerivWithinAt_of_isGateauxDerivativeWithinAt
    {D : Set E} {F : E → G} {F' : E → E →L[ℝ] G}
    {x y : E}
    (hD_convex : Convex ℝ D)
    (hGateaux : ∀ z ∈ D, IsGateauxDerivativeWithinAt ℝ D F z (F' z))
    (hx : x ∈ D)
    (hy : y ∈ D) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt
        (fun s ↦ F (AffineMap.lineMap x y s))
        (F' (AffineMap.lineMap x y t) (y - x))
        (Set.Icc (0 : ℝ) 1) t := by
  intro t ht
  -- Route correction: unfold the chapter owner to raw `HasDerivWithinAt` and transport it
  -- along the scalar shift `s ↦ s - t` before rewriting back to the affine segment.
  let z := AffineMap.lineMap x y t
  have hz : z ∈ D := by
    exact hD_convex.mapsTo_lineMap hx hy ht
  have hraw :
      HasDerivWithinAt
        (fun s : ℝ ↦ F (z + s • (y - x)))
        (F' z (y - x))
        ((fun s : ℝ ↦ z + s • (y - x)) ⁻¹' D)
        0 := by
    simpa [z, HasLineDerivWithinAt] using hGateaux z hz (y - x)
  have hshift :
      HasDerivWithinAt (fun s : ℝ ↦ s - t) 1 (Set.Icc (0 : ℝ) 1) t := by
    simpa using ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
  have hmaps :
      MapsTo
        (fun s : ℝ ↦ s - t)
        (Set.Icc (0 : ℝ) 1)
        ((fun s : ℝ ↦ z + s • (y - x)) ⁻¹' D) := by
    intro s hs
    change z + (s - t) • (y - x) ∈ D
    rw [← lineMapApply_eq_baseAdd_smul_sub (x := x) (y := y) (s := s) (t := t)]
    exact hD_convex.mapsTo_lineMap hx hy hs
  have hcomp0 :
      HasDerivWithinAt
        ((fun s : ℝ ↦ F (z + s • (y - x))) ∘ fun s : ℝ ↦ s - t)
        ((1 : ℝ) • F' z (y - x))
        (Set.Icc (0 : ℝ) 1)
        t := by
    exact hraw.scomp_of_eq t hshift hmaps (by simp)
  have hcomp1 :
      HasDerivWithinAt
        (fun s : ℝ ↦ F (z + (s - t) • (y - x)))
        ((1 : ℝ) • F' z (y - x))
        (Set.Icc (0 : ℝ) 1)
        t := by
    refine hcomp0.congr ?_ ?_
    · intro s hs
      rfl
    · rfl
  have hcomp :
      HasDerivWithinAt
        (fun s : ℝ ↦ F (z + (s - t) • (y - x)))
        ((F' z) y - (F' z) x)
        (Set.Icc (0 : ℝ) 1)
        t := by
    simpa [one_smul, map_sub] using hcomp1
  have hsegment :
      HasDerivWithinAt
        (fun s ↦ F (AffineMap.lineMap x y s))
        ((F' z) y - (F' z) x)
        (Set.Icc (0 : ℝ) 1)
        t := by
    -- Rewrite the transported function pointwise back to the affine segment parameterization.
    refine hcomp.congr ?_ ?_
    · intro s hs
      rw [lineMapApply_eq_baseAdd_smul_sub (x := x) (y := y) (s := s) (t := t)]
    · simpa [z] using
        lineMapApply_eq_baseAdd_smul_sub (x := x) (y := y) (s := t) (t := t)
  -- The affine normalization turns the transported raw line map back into the segment pullback.
  simpa [z, map_sub] using hsegment

/-- Helper for Chapter01 Definition 1.2.28: subtracting a fixed continuous linear map shifts
the Gateaux derivative by the same linear map. -/
lemma isGateauxDerivativeWithinAt_sub_clm
    {D : Set E} {F : E → G} {F' : E → E →L[ℝ] G} {z : E}
    (A : E →L[ℝ] G)
    (hGateaux : IsGateauxDerivativeWithinAt ℝ D F z (F' z)) :
    IsGateauxDerivativeWithinAt ℝ D (fun w ↦ F w - A w) z (F' z - A) := by
  intro d
  -- Subtract the fixed linear model once at the line-derivative level.
  exact (hGateaux d).sub (A.hasFDerivWithinAt.hasLineDerivWithinAt d)

/-- Helper for Chapter01 Definition 1.2.28: composing Gateaux derivative data with a fixed
continuous linear map transports the derivative by composition. -/
lemma isGateauxDerivativeWithinAt_comp_clm
    {D : Set E} {F : E → G} {A : E →L[ℝ] G} {z : E}
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : G →L[ℝ] H)
    (hGateaux : IsGateauxDerivativeWithinAt ℝ D F z A) :
    IsGateauxDerivativeWithinAt ℝ D (fun w ↦ L (F w)) z (L.comp A) := by
  intro d
  -- Compose the one-variable pulled-back derivative with the fixed linear functional `L`.
  change HasDerivWithinAt (fun t : ℝ ↦ L (F (z + t • d))) (L (A d)) ((fun t ↦ z + t • d) ⁻¹' D) 0
  have hcomp :
      HasDerivWithinAt
        (⇑L ∘ fun t : ℝ ↦ F (z + t • d))
        (L (A d))
        ((fun t ↦ z + t • d) ⁻¹' D)
        0 :=
    L.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) (hGateaux d)
  convert hcomp using 1
  funext t
  rfl

/-- Helper for Chapter01 Definition 1.2.28: a segment-wise operator norm bound on the Gateaux
derivative yields the standard mean-value estimate for `F y - F x`. -/
lemma segmentNormBoundOfGateauxDerivative
    {D : Set E} {F : E → G} {F' : E → E →L[ℝ] G}
    {x y : E} {C : ℝ}
    (hD_convex : Convex ℝ D)
    (hGateaux : ∀ z ∈ D, IsGateauxDerivativeWithinAt ℝ D F z (F' z))
    (hx : x ∈ D)
    (hy : y ∈ D)
    (hbound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' (AffineMap.lineMap x y t)‖ ≤ C) :
    ‖F y - F x‖ ≤ C * ‖y - x‖ := by
  -- Apply the one-variable mean-value inequality to the segment pullback of `F`.
  set g : ℝ → G := fun t ↦ F (AffineMap.lineMap x y t)
  have hderiv :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt g (F' (AffineMap.lineMap x y t) (y - x)) (Set.Icc (0 : ℝ) 1) t := by
    simpa [g] using
      segmentHasDerivWithinAt_of_isGateauxDerivativeWithinAt hD_convex hGateaux hx hy
  have hbound' :
      ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖F' (AffineMap.lineMap x y t) (y - x)‖ ≤ C * ‖y - x‖ := by
    intro t ht
    calc
      ‖F' (AffineMap.lineMap x y t) (y - x)‖ ≤ ‖F' (AffineMap.lineMap x y t)‖ * ‖y - x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖y - x‖ := by
        gcongr
        exact hbound t (Set.Ico_subset_Icc_self ht)
  have hseg := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := g) hderiv hbound'
  simpa [g] using hseg

/-- Helper for Chapter01 Definition 1.2.28: a segment-wise bound on
`‖F' - F' x‖` controls the linearization remainder along that segment. -/
lemma segmentLinearizationDeviationBound
    {D : Set E} {F : E → G} {F' : E → E →L[ℝ] G}
    {x y z : E} {C : ℝ}
    (hD_convex : Convex ℝ D)
    (hGateaux : ∀ w ∈ D, IsGateauxDerivativeWithinAt ℝ D F w (F' w))
    (hy : y ∈ D)
    (hz : z ∈ D)
    (hbound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' (AffineMap.lineMap z y t) - F' x‖ ≤ C) :
    ‖F y - F z - F' x (y - z)‖ ≤ C * ‖y - z‖ := by
  -- Apply the segment norm bound to the shifted map `w ↦ F w - F' x w`.
  have hshifted :
      ‖(F y - F' x y) - (F z - F' x z)‖ ≤ C * ‖y - z‖ := by
    exact
      segmentNormBoundOfGateauxDerivative
        (D := D)
        (F := fun w ↦ F w - F' x w)
        (F' := fun w ↦ F' w - F' x)
        hD_convex
        (fun w hw ↦ isGateauxDerivativeWithinAt_sub_clm (A := F' x) (hGateaux w hw))
        hz
        hy
        hbound
  have hremainder :
      (F y - F' x y) - (F z - F' x z) = F y - F z - F' x (y - z) := by
    rw [map_sub]
    abel
  -- Rewrite the shifted-map difference into the usual first-order remainder.
  calc
    ‖F y - F z - F' x (y - z)‖ = ‖(F y - F' x y) - (F z - F' x z)‖ := by
      rw [hremainder]
    _ ≤ C * ‖y - z‖ := hshifted

/-- Helper for Chapter01 Definition 1.2.28: an ambient `ContinuousOn` field on `D` supplies the
chapter's linewise within-set continuity owner at each point of `D`. -/
lemma alongLineWithinAt_of_continuousOn
    {D : Set E} {F : E → G} {x : E}
    (hx : x ∈ D)
    (hcont : ContinuousOn F D) :
    AlongLineWithinAt ContinuousWithinAt D F x := by
  refine ⟨hx, ?_⟩
  intro d
  -- Compose ambient continuity on `D` with the line `t ↦ x + t • d`.
  have hline :
      ContinuousWithinAt
        (fun t : ℝ ↦ x + t • d)
        {t : ℝ | x + t • d ∈ D}
        0 := by
    fun_prop
  exact
    (hcont x hx).comp_of_eq hline (by intro t ht; exact ht) (by simp)

/-- Helper for Chapter01 Definition 1.2.28: linewise continuity of the derivative field at each
segment point turns into continuity of the FTC integrand on `Icc (0 : ℝ) 1`. -/
lemma segmentIntegrandContinuousOn_of_alongLine
    {D : Set E} {F' : E → E →L[ℝ] G} {x y : E}
    (hD_convex : Convex ℝ D)
    (hhemi : ∀ z ∈ D, AlongLineWithinAt ContinuousWithinAt D F' z)
    (hx : x ∈ D)
    (hy : y ∈ D) :
    ContinuousOn
      (fun t ↦ F' (x + t • (y - x)) (y - x))
      (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  let z := AffineMap.lineMap x y t
  have hz : z ∈ D := hD_convex.mapsTo_lineMap hx hy ht
  rcases hhemi z hz with ⟨_, hzline⟩
  have hshift :
      ContinuousWithinAt (fun s : ℝ ↦ s - t) (Set.Icc (0 : ℝ) 1) t := by
    fun_prop
  have hmaps :
      MapsTo
        (fun s : ℝ ↦ s - t)
        (Set.Icc (0 : ℝ) 1)
        {s : ℝ | z + s • (y - x) ∈ D} := by
    intro s hs
    change z + (s - t) • (y - x) ∈ D
    rw [← lineMapApply_eq_baseAdd_smul_sub (x := x) (y := y) (s := s) (t := t)]
    exact hD_convex.mapsTo_lineMap hx hy hs
  have hshiftedSegment :
      ContinuousWithinAt
        (fun s : ℝ ↦ F' (z + (s - t) • (y - x)))
        (Set.Icc (0 : ℝ) 1)
        t := by
    -- Shift the chapter owner from parameter `0` at base point `z` to parameter `t` on the segment.
    have hcomp :
        ContinuousWithinAt
          (((fun u : ℝ ↦ F' (z + u • (y - x))) ∘ fun s : ℝ ↦ s - t))
          (Set.Icc (0 : ℝ) 1)
          t := by
      exact (hzline (y - x)).comp_of_eq hshift hmaps (by simp)
    have hcomp' :
        ContinuousWithinAt
          (fun s : ℝ ↦ F' (z + (s - t) • (y - x)))
          (Set.Icc (0 : ℝ) 1)
          t := by
      exact hcomp.congr (fun s hs ↦ rfl) rfl
    exact hcomp'
  have hzsegment :
      ContinuousWithinAt
        (fun s : ℝ ↦ F' (AffineMap.lineMap x y s))
        (Set.Icc (0 : ℝ) 1)
        t := by
    -- Rewrite the shifted parameterization back to the affine segment spelling.
    exact hshiftedSegment.congr
      (fun s hs ↦ by
        rw [lineMapApply_eq_baseAdd_smul_sub (x := x) (y := y) (s := s) (t := t)])
      (by
        simpa [z] using
          lineMapApply_eq_baseAdd_smul_sub (x := x) (y := y) (s := t) (t := t))
  have hconst :
      ContinuousWithinAt (fun _ : ℝ ↦ y - x) (Set.Icc (0 : ℝ) 1) t := by
    fun_prop
  -- Evaluate the continuous linear maps at the fixed vector `y - x`.
  simpa [z, AffineMap.lineMap_apply_module', add_comm] using hzsegment.clm_apply hconst

/-- Consequence of Chapter01 Definition 1.2.28 (7): if the Gateaux derivative is
defined on the open set `D` and varies continuously there, then `F` is Fréchet
differentiable at every point of `D` with derivative `F' x`. -/
theorem hasFDerivAt_of_gateauxDerivative_continuousOn
    {D : Set E} (F : E → G) (F' : E → E →L[ℝ] G)
    (hD_open : IsOpen D)
    (hGateaux : ∀ x ∈ D, IsGateauxDerivativeWithinAt ℝ D F x (F' x))
    (hcont : ContinuousOn F' D) :
    ∀ x ∈ D, HasFDerivAt F (F' x) x := by
  intro x hx
  have hstrict : HasStrictFDerivAt F (F' x) x := by
    -- Route correction: prove a strict derivative on a small convex ball around `x`,
    -- then read off the ordinary Fréchet derivative.
    rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    have hcontx : ContinuousAt F' x := (hcont x hx).continuousAt (hD_open.mem_nhds hx)
    rcases Metric.mem_nhds_iff.mp
        (Filter.inter_mem (hD_open.mem_nhds hx) (hcontx (Metric.ball_mem_nhds _ hc))) with
      ⟨ε, hεpos, hε⟩
    refine Metric.eventually_nhds_iff_ball.mpr ?_
    refine ⟨ε, hεpos, ?_⟩
    intro p hp
    rw [← ball_prod_same, prodMk_mem_set_prod_eq] at hp
    rcases hp with ⟨ha, hb⟩
    have hball_mem :
        ∀ y ∈ Metric.ball x ε, y ∈ D ∧ ‖F' y - F' x‖ < c := by
      intro y hy
      refine ⟨(hε hy).1, ?_⟩
      simpa [Metric.mem_ball, dist_eq_norm] using (hε hy).2
    have hball_subset : Metric.ball x ε ⊆ D := by
      intro y hy
      exact (hball_mem y hy).1
    -- Apply the segment remainder estimate on the convex ball where `F'` stays `c`-close to `F' x`.
    simpa using
      segmentLinearizationDeviationBound
        (D := Metric.ball x ε)
        (F := F)
        (F' := F')
        (x := x)
        (y := p.1)
        (z := p.2)
        (C := c)
        (convex_ball x ε)
        (fun y hy d ↦ (hGateaux y (hball_subset hy) d).mono hball_subset)
        ha
        hb
        (fun t ht ↦
          le_of_lt ((hball_mem (AffineMap.lineMap p.2 p.1 t)
            ((convex_ball x ε).mapsTo_lineMap hb ha ht)).2))
  exact hstrict.hasFDerivAt

/-- Consequence of Chapter01 Definition 1.2.28 (11): on a convex set, any uniform bound `C`
for the derivative norm along the segment from `x` to `y` bounds `‖F y - F x‖`. -/
theorem norm_image_sub_le_of_segment_fderiv_bound
    {D : Set E} (F : E → G) (F' : E → E →L[ℝ] G)
    {x y : E}
    {C : ℝ}
    (hD_convex : Convex ℝ D)
    (hGateaux : ∀ z ∈ D, IsGateauxDerivativeWithinAt ℝ D F z (F' z))
    (hx : x ∈ D)
    (hbound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' (x + t • (y - x))‖ ≤ C)
    (hy : y ∈ D) :
    ‖F y - F x‖ ≤ C * ‖y - x‖ := by
  -- Rewrite the source segment as `AffineMap.lineMap` and reuse the generic helper.
  have hbound' :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' (AffineMap.lineMap x y t)‖ ≤ C := by
    intro t ht
    simpa [AffineMap.lineMap_apply_module', add_comm] using hbound t ht
  simpa [AffineMap.lineMap_apply_module'] using
    segmentNormBoundOfGateauxDerivative
      (F := F) (F' := F') hD_convex hGateaux hx hy hbound'

/-- Consequence of Chapter01 Definition 1.2.28 (12): on a convex set, any uniform bound `C`
for the derivative deviation along the segment from `z` to `y` bounds the deviation of
`F y - F z` from the linearization `F' x (y - z)`. -/
theorem norm_image_sub_sub_le_of_segment_fderiv_deviation_bound
    {D : Set E} (F : E → G) (F' : E → E →L[ℝ] G)
    {x y z : E}
    {C : ℝ}
    (hD_convex : Convex ℝ D)
    (hGateaux : ∀ w ∈ D, IsGateauxDerivativeWithinAt ℝ D F w (F' w))
    (hbound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' (z + t • (y - z)) - F' x‖ ≤ C)
    (hy : y ∈ D)
    (hz : z ∈ D) :
    ‖F y - F z - F' x (y - z)‖ ≤ C * ‖y - z‖ := by
  -- Rewrite the source segment as `AffineMap.lineMap` and reuse the generic helper.
  have hbound' :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' (AffineMap.lineMap z y t) - F' x‖ ≤ C := by
    intro t ht
    simpa [AffineMap.lineMap_apply_module', add_comm] using hbound t ht
  simpa [AffineMap.lineMap_apply_module'] using
    segmentLinearizationDeviationBound
      (F := F) (F' := F') hD_convex hGateaux hy hz hbound'

/-- Consequence of Chapter01 Definition 1.2.28 (13): if the Gateaux derivative is
linewise within-set continuous on the convex set `D`, then `F y - F x` is the
integral of the derivative along the segment from `x` to `y`. The
interval-integral conclusion uses the usual complete codomain hypothesis from
the fundamental theorem of calculus. -/
theorem segmentIntegral_eq_sub
    {D : Set E} (F : E → G) (F' : E → E →L[ℝ] G)
    {x y : E}
    [CompleteSpace G]
    (hD_convex : Convex ℝ D)
    (hGateaux : ∀ z ∈ D, IsGateauxDerivativeWithinAt ℝ D F z (F' z))
    (hhemi : ∀ z ∈ D, AlongLineWithinAt ContinuousWithinAt D F' z)
    (hx : x ∈ D)
    (hy : y ∈ D) :
    F y - F x = ∫ t in 0..1, F' (x + t • (y - x)) (y - x) := by
  set g : ℝ → G := fun t ↦ F (AffineMap.lineMap x y t)
  have hderivWithin :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt g (F' (AffineMap.lineMap x y t) (y - x)) (Set.Icc (0 : ℝ) 1) t := by
    -- Pull the Gateaux derivative back to the affine segment parameter.
    simpa [g] using
      segmentHasDerivWithinAt_of_isGateauxDerivativeWithinAt hD_convex hGateaux hx hy
  have hcont :
      ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    -- The segment pullback is continuous because it has a derivative within the interval.
    exact (hderivWithin t ht).continuousWithinAt
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt g (F' (AffineMap.lineMap x y t) (y - x)) t := by
    intro t ht
    -- Interior points of `[0, 1]` upgrade a within-derivative to an ordinary derivative.
    exact (hderivWithin t (Set.mem_Icc_of_Ioo ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hint :
      IntervalIntegrable
        (fun t ↦ F' (AffineMap.lineMap x y t) (y - x))
        MeasureTheory.volume
        0
        1 := by
    -- The derivative profile is continuous on the whole segment, hence interval integrable.
    exact
      (by
        simpa [AffineMap.lineMap_apply_module', add_comm] using
          (segmentIntegrandContinuousOn_of_alongLine
            (F' := F') hD_convex hhemi hx hy).intervalIntegrable_of_Icc zero_le_one)
  have hFTC :
      ∫ t in 0..1, F' (AffineMap.lineMap x y t) (y - x) = g 1 - g 0 := by
    -- Apply the one-dimensional fundamental theorem of calculus to the segment pullback.
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  -- Rewrite the segment endpoints and switch back to the source spelling `x + t • (y - x)`.
  calc
    F y - F x = g 1 - g 0 := by
      simp [g, AffineMap.lineMap_apply_module', add_comm]
    _ = ∫ t in 0..1, F' (AffineMap.lineMap x y t) (y - x) := by
      symm
      exact hFTC
    _ = ∫ t in 0..1, F' (x + t • (y - x)) (y - x) := by
      simp [AffineMap.lineMap_apply_module', add_comm]

/-- Chapter01 Definition 1.2.28 (14): if the Gateaux derivative is `(γ, p)`-Hölder on the
convex set `D`, then the first-order Taylor remainder is bounded by
`(γ / (p + 1)) * ‖y - x‖ ^ (p + 1)` in `Real.rpow` form. This is the chapter's
core/canonical first-order Hölder remainder owner, stated at the intrinsic real normed-space
level and organized around mathlib's fixed-parameter Hölder owner `HolderOnWith`; the source
`ℝⁿ → ℝᵐ` form is its Euclidean specialization. -/
theorem holderRemainderBound
    {D : Set E} (F : E → G) (F' : E → E →L[ℝ] G)
    {x y : E}
    {γ p : NNReal}
    (hD_convex : Convex ℝ D)
    (hGateaux : ∀ z ∈ D, IsGateauxDerivativeWithinAt ℝ D F z (F' z))
    (hHolder : HolderOnWith γ p F' D)
    (hp : 0 < p)
    (hx : x ∈ D)
    (hy : y ∈ D) :
    ‖F y - F x - F' x (y - x)‖ ≤
      ((γ : ℝ) / ((p : ℝ) + 1)) * Real.rpow ‖y - x‖ ((p : ℝ) + 1) := by
  -- Scalarize the remainder with a dual functional chosen on the final error vector.
  let r : G := F y - F x - F' x (y - x)
  obtain ⟨g, hg_norm, hg_eval⟩ := exists_dual_vector'' (𝕜 := ℝ) r
  let φ : E → ℝ := fun z ↦ g (F z - F' x z)
  let ψ : E → E →L[ℝ] ℝ := fun z ↦ g.comp (F' z - F' x)
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp
  have hF'cont : ContinuousOn F' D := hHolder.continuousOn hp
  have hψcont : ContinuousOn ψ D := by
    -- The scalarized derivative field inherits continuity from `F'` by CLM composition.
    exact ContinuousOn.clm_comp continuousOn_const (hF'cont.sub continuousOn_const)
  have hψhemi : ∀ z ∈ D, AlongLineWithinAt ContinuousWithinAt D ψ z := by
    intro z hz
    -- Convert ambient continuity of the scalarized field into the chapter's linewise owner.
    exact alongLineWithinAt_of_continuousOn hz hψcont
  have hψgateaux : ∀ z ∈ D, IsGateauxDerivativeWithinAt ℝ D φ z (ψ z) := by
    intro z hz
    -- First subtract the frozen linear model, then compose with the chosen scalar functional.
    exact
      isGateauxDerivativeWithinAt_comp_clm
        (L := g)
        (isGateauxDerivativeWithinAt_sub_clm (A := F' x) (hGateaux z hz))
  have hsegment :
      g r = ∫ t in 0..1, ψ (x + t • (y - x)) (y - x) := by
    -- Apply the proved segment FTC theorem to the scalarized shifted map.
    have hFTC :=
      segmentIntegral_eq_sub
        (F := φ)
        (F' := ψ)
        hD_convex
        hψgateaux
        hψhemi
        hx
        hy
    have hleft : φ y - φ x = g r := by
      -- Rewrite the endpoint difference into the usual Taylor remainder.
      change g (F y - F' x y) - g (F x - F' x x) = g (F y - F x - F' x (y - x))
      calc
        g (F y - F' x y) - g (F x - F' x x) =
            (g (F y) - g ((F' x) y)) - (g (F x) - g ((F' x) x)) := by
              rw [map_sub, map_sub]
        _ = g (F y) - g (F x) - g ((F' x) y - (F' x) x) := by
              rw [map_sub]
              ring_nf
        _ = g (F y - F x) - g ((F' x) y - (F' x) x) := by
              rw [← map_sub]
        _ = g (F y - F x - F' x (y - x)) := by
              rw [← map_sub]
              congr 1
              rw [map_sub]
    calc
      g r = φ y - φ x := hleft.symm
      _ = ∫ t in 0..1, ψ (x + t • (y - x)) (y - x) := hFTC
  have hpointwise :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |ψ (x + t • (y - x)) (y - x)| ≤
          (γ : ℝ) * Real.rpow t (p : ℝ) * Real.rpow ‖y - x‖ ((p : ℝ) + 1) := by
    intro t ht
    have ht_nonneg : 0 ≤ t := ht.1
    have hseg_mem : x + t • (y - x) ∈ D := hD_convex.add_smul_sub_mem hx hy ht
    have hholder_t :
        ‖F' (x + t • (y - x)) - F' x‖ ≤
          (γ : ℝ) * dist (x + t • (y - x)) x ^ (p : ℝ) := by
      simpa [dist_eq_norm] using hHolder.dist_le hseg_mem hx
    have hdist :
        dist (x + t • (y - x)) x = t * ‖y - x‖ := by
      calc
        dist (x + t • (y - x)) x = ‖(x + t • (y - x)) - x‖ := by
          rw [dist_eq_norm]
        _ = ‖t • (y - x)‖ := by abel
        _ = t * ‖y - x‖ := by rw [norm_smul, Real.norm_of_nonneg ht_nonneg]
    calc
      |ψ (x + t • (y - x)) (y - x)| =
          ‖g ((F' (x + t • (y - x)) - F' x) (y - x))‖ := by
            simp [ψ, Real.norm_eq_abs]
      _ ≤ ‖g‖ * ‖(F' (x + t • (y - x)) - F' x) (y - x)‖ := by
        simpa using ContinuousLinearMap.le_opNorm g ((F' (x + t • (y - x)) - F' x) (y - x))
      _ ≤ ‖g‖ * (‖F' (x + t • (y - x)) - F' x‖ * ‖y - x‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (‖F' (x + t • (y - x)) - F' x‖ * ‖y - x‖) := by
        gcongr
      _ = ‖F' (x + t • (y - x)) - F' x‖ * ‖y - x‖ := by ring
      _ ≤ ((γ : ℝ) * dist (x + t • (y - x)) x ^ (p : ℝ)) * ‖y - x‖ := by
        gcongr
      _ = (γ : ℝ) * Real.rpow t (p : ℝ) * Real.rpow ‖y - x‖ ((p : ℝ) + 1) := by
        rw [hdist, Real.mul_rpow ht_nonneg (norm_nonneg _)]
        have hnormPow :
            Real.rpow ‖y - x‖ (p : ℝ) * ‖y - x‖ =
              Real.rpow ‖y - x‖ ((p : ℝ) + 1) := by
          by_cases hnorm : ‖y - x‖ = 0
          · have hp1ne : (p : ℝ) + 1 ≠ 0 := by linarith [hpReal]
            simp [hnorm, Real.zero_rpow hp1ne]
          · rw [← Real.rpow_one ‖y - x‖]
            simpa [add_comm, add_left_comm, add_assoc] using
              (Real.rpow_add
                (show 0 < ‖y - x‖ by
                  exact lt_of_le_of_ne (norm_nonneg _) (by simpa [eq_comm] using hnorm))
                (p : ℝ) 1).symm
        calc
          (γ : ℝ) * (Real.rpow t (p : ℝ) * Real.rpow ‖y - x‖ (p : ℝ)) * ‖y - x‖ =
              (γ : ℝ) * Real.rpow t (p : ℝ) * (Real.rpow ‖y - x‖ (p : ℝ) * ‖y - x‖) := by
                ring
          _ = (γ : ℝ) * Real.rpow t (p : ℝ) * Real.rpow ‖y - x‖ ((p : ℝ) + 1) := by
                rw [hnormPow]
  have hpPlusOne_ne : ((p : ℝ) + 1) ≠ 0 := by linarith
  have hIntegralRpow :
      ∫ t in 0..1, Real.rpow t (p : ℝ) = 1 / ((p : ℝ) + 1) := by
    have hnegOne : -1 < (p : ℝ) := by linarith
    calc
      ∫ t in 0..1, Real.rpow t (p : ℝ) =
          (1 ^ ((p : ℝ) + 1) - 0 ^ ((p : ℝ) + 1)) / ((p : ℝ) + 1) := by
            simpa using integral_rpow (a := (0 : ℝ)) (b := 1) (r := (p : ℝ)) (Or.inl hnegOne)
      _ = 1 / ((p : ℝ) + 1) := by
        rw [Real.one_rpow, Real.zero_rpow hpPlusOne_ne, sub_zero]
  let C : ℝ := Real.rpow ‖y - x‖ ((p : ℝ) + 1)
  have hsegmentCont :
      ContinuousOn
        (fun t ↦ ψ (x + t • (y - x)) (y - x))
        (Set.Icc (0 : ℝ) 1) :=
    segmentIntegrandContinuousOn_of_alongLine (F' := ψ) hD_convex hψhemi hx hy
  have habsInt :
      IntervalIntegrable
        (fun t ↦ |ψ (x + t • (y - x)) (y - x)|)
        MeasureTheory.volume
        0
        1 := by
    exact hsegmentCont.abs.intervalIntegrable_of_Icc zero_le_one
  have hupperCont :
      ContinuousOn
        (fun t : ℝ ↦ (γ : ℝ) * Real.rpow t (p : ℝ) * C)
        (Set.Icc (0 : ℝ) 1) := by
    have hrpowCont :
        ContinuousOn (fun t : ℝ ↦ Real.rpow t (p : ℝ)) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_id.rpow_const (fun _ _ ↦ Or.inr hpReal.le)
    intro t ht
    have hγ :
        ContinuousWithinAt (fun _ : ℝ ↦ (γ : ℝ)) (Set.Icc (0 : ℝ) 1) t :=
      continuousOn_const t ht
    have hrpowMulC :
        ContinuousWithinAt (fun s : ℝ ↦ C * Real.rpow s (p : ℝ)) (Set.Icc (0 : ℝ) 1) t :=
      (continuousOn_const.mul hrpowCont) t ht
    have hmul :
        ContinuousWithinAt
          (((fun _ : ℝ ↦ (γ : ℝ)) * fun s : ℝ ↦ C * Real.rpow s (p : ℝ)))
          (Set.Icc (0 : ℝ) 1)
          t :=
      hγ.mul hrpowMulC
    convert hmul using 1
    funext s
    simp [Pi.mul_apply, mul_comm, mul_assoc]
  have hupperInt :
      IntervalIntegrable
        (fun t : ℝ ↦ (γ : ℝ) * Real.rpow t (p : ℝ) * C)
        MeasureTheory.volume
        0
        1 := by
    exact hupperCont.intervalIntegrable_of_Icc zero_le_one
  -- Bound the scalar integral and evaluate the exact `t^p` primitive on `[0,1]`.
  calc
    ‖r‖ = |∫ t in 0..1, ψ (x + t • (y - x)) (y - x)| := by
      have hgr_nonneg : 0 ≤ g r := by simp [hg_eval]
      calc
        ‖r‖ = g r := hg_eval.symm
        _ = |g r| := by symm; exact abs_of_nonneg hgr_nonneg
        _ = |∫ t in 0..1, ψ (x + t • (y - x)) (y - x)| := by rw [hsegment]
    _ ≤ ∫ t in 0..1, |ψ (x + t • (y - x)) (y - x)| := by
      exact intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in 0..1, (γ : ℝ) * Real.rpow t (p : ℝ) * C := by
      exact intervalIntegral.integral_mono_on zero_le_one habsInt hupperInt hpointwise
    _ = ((γ : ℝ) / ((p : ℝ) + 1)) * C := by
      have hconstIntegral :
          ∫ t in 0..1, (γ : ℝ) * Real.rpow t (p : ℝ) * C =
            ((γ : ℝ) / ((p : ℝ) + 1)) * C := by
        have hrewrite :
            (fun t : ℝ ↦ (γ : ℝ) * Real.rpow t (p : ℝ) * C) =
              fun t : ℝ ↦ (γ : ℝ) * (Real.rpow t (p : ℝ) * C) := by
          funext t
          ring
        rw [hrewrite, intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
          hIntegralRpow, div_eq_mul_inv]
        ring
      exact hconstIntegral
    _ = ((γ : ℝ) / ((p : ℝ) + 1)) * Real.rpow ‖y - x‖ ((p : ℝ) + 1) := by rfl

end RealNormed

section Euclidean

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Target" => EuclideanSpace ℝ (Fin m)

/-- Helper for Chapter01 Definition 1.2.28: the standard scalar counterexample whose linewise
pullbacks have derivative `0` at the origin while the map fails to be continuous there. -/
noncomputable def gateauxNotFrechetCounterexampleScalar :
    EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun x ↦
    if x = 0 then 0 else (x 0) ^ 3 * x 1 / ((x 0) ^ 6 + (x 1) ^ 2)

/-- Helper for Chapter01 Definition 1.2.28: along every line through the origin, the scalar
counterexample has ordinary derivative `0` at the base parameter `0`. -/
lemma gateauxCounterexampleScalar_hasDerivAt_zeroAlongLine
    (d : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun t : ℝ ↦ gateauxNotFrechetCounterexampleScalar (t • d)) 0 0 := by
  by_cases hd1 : d 1 = 0
  · -- If the second coordinate vanishes, the pulled-back scalar counterexample is identically `0`.
    have hzero :
        (fun t : ℝ ↦ gateauxNotFrechetCounterexampleScalar (t • d)) = fun _ : ℝ ↦ 0 := by
      funext t
      simp [gateauxNotFrechetCounterexampleScalar, hd1]
    simpa [hzero] using (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
  · -- Otherwise the pullback factors as `t^2` times a differentiable quotient
    -- with nonzero denominator.
    have hrewrite :
        (fun t : ℝ ↦ gateauxNotFrechetCounterexampleScalar (t • d)) =
          fun t : ℝ ↦
            t ^ 2 * (((d 0) ^ 3 * d 1) / (t ^ 4 * (d 0) ^ 6 + (d 1) ^ 2)) := by
      funext t
      by_cases ht : t = 0
      · simp [gateauxNotFrechetCounterexampleScalar, ht]
      · have htd : (t • d : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
          intro htd0
          have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) htd0
          exact hd1 <| (mul_eq_zero.mp (by simpa using hcoord)).resolve_left ht
        have horigden : ((t * d 0) ^ 6 + (t * d 1) ^ 2) ≠ 0 := by
          have hnonneg : 0 ≤ (t * d 0) ^ 6 := by positivity
          have hpos : 0 < (t * d 1) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero ht hd1)
          exact ne_of_gt (by nlinarith)
        have hnewden : (t ^ 4 * (d 0) ^ 6 + (d 1) ^ 2) ≠ 0 := by
          have hnonneg : 0 ≤ t ^ 4 * (d 0) ^ 6 := by positivity
          have hpos : 0 < (d 1) ^ 2 := sq_pos_of_ne_zero hd1
          exact ne_of_gt (by nlinarith)
        simp [gateauxNotFrechetCounterexampleScalar, htd]
        field_simp [horigden, hnewden]
    have hden0 : (0 ^ 4 * (d 0) ^ 6 + (d 1) ^ 2 : ℝ) ≠ 0 := by
      simpa using pow_ne_zero 2 hd1
    have hmodel :
        HasDerivAt
          (fun t : ℝ ↦ t ^ 2 * (((d 0) ^ 3 * d 1) / (t ^ 4 * (d 0) ^ 6 + (d 1) ^ 2)))
          0
          0 := by
      have hsq : HasDerivAt (fun t : ℝ ↦ t ^ 2) 0 0 := by
        simpa using hasDerivAt_pow 2 (0 : ℝ)
      have hquot :
          DifferentiableAt ℝ
            (fun t : ℝ ↦ ((d 0) ^ 3 * d 1) / (t ^ 4 * (d 0) ^ 6 + (d 1) ^ 2))
            0 := by
        have hnum :
            DifferentiableAt ℝ (fun _ : ℝ ↦ (d 0) ^ 3 * d 1) 0 := by
          fun_prop
        have hden :
            DifferentiableAt ℝ (fun t : ℝ ↦ t ^ 4 * (d 0) ^ 6 + (d 1) ^ 2) 0 := by
          fun_prop
        exact hnum.div hden hden0
      have hmul :
          HasDerivAt
            (((fun t : ℝ ↦ t ^ 2) *
              fun t : ℝ ↦ ((d 0) ^ 3 * d 1) / (t ^ 4 * (d 0) ^ 6 + (d 1) ^ 2)))
            0
            0 := by
        simpa using hsq.mul hquot.hasDerivAt
      convert hmul using 1
      ext t
      rfl
    simpa [hrewrite] using hmodel

/-- Helper for Chapter01 Definition 1.2.28: the cubic path used to witness noncontinuity of the
scalar counterexample at the origin. -/
noncomputable def gateauxCounterexampleCubicPath (u : ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  u • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
    (u ^ 3) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/-- Helper for Chapter01 Definition 1.2.28: along the cubic path, the scalar counterexample is
constantly `1 / 2` away from the origin. -/
lemma gateauxCounterexampleScalar_path_eq_half
    {u : ℝ} (hu : u ≠ 0) :
    gateauxNotFrechetCounterexampleScalar (gateauxCounterexampleCubicPath u) = (1 / 2 : ℝ) := by
  have hvec : gateauxCounterexampleCubicPath u ≠ 0 := by
    intro hvec0
    have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hvec0
    simp [gateauxCounterexampleCubicPath, hu] at hcoord
  have hden : (u ^ 6 + (u ^ 3) ^ 2 : ℝ) ≠ 0 := by
    have hpos : 0 < u ^ 6 := by positivity
    nlinarith
  rw [gateauxNotFrechetCounterexampleScalar, if_neg hvec]
  simp [gateauxCounterexampleCubicPath]
  field_simp [hden, hu]
  ring

/-- Consequence of Chapter01 Definition 1.2.28 (6): Gateaux differentiability does not imply Fréchet
differentiability in general. -/
theorem exists_gateauxDifferentiableAt_not_hasFDerivAt :
    ∃ F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 1),
      SunYuanGateauxDifferentiableWithinAt ℝ Set.univ F 0 ∧
      ¬ DifferentiableAt ℝ F 0 := by
  let e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single (0 : Fin 1) (1 : ℝ)
  let F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 1) :=
    fun z ↦ gateauxNotFrechetCounterexampleScalar z • e
  refine ⟨F, ?_, ?_⟩
  · -- The vector-valued counterexample inherits the zero directional
    -- derivatives from the scalar one.
    refine ⟨isOpen_univ, by simp, 0, ?_⟩
    intro d
    have hscalar :
        HasDerivAt (fun t : ℝ ↦ gateauxNotFrechetCounterexampleScalar (t • d)) 0 0 :=
      gateauxCounterexampleScalar_hasDerivAt_zeroAlongLine d
    -- Lift the scalar derivative by multiplying with the fixed codomain vector `e`.
    simpa [F, HasLineDerivWithinAt] using hscalar.smul_const e
  · -- Route correction: refute differentiability by projecting back to the scalar counterexample.
    intro hF
    let proj : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
      PiLp.proj (p := 2) (β := fun _ : Fin 1 => ℝ) 0
    have hscalarDiff :
        DifferentiableAt ℝ gateauxNotFrechetCounterexampleScalar 0 := by
      have hcomp : DifferentiableAt ℝ (fun z ↦ proj (F z)) 0 :=
        proj.hasFDerivAt.differentiableAt.comp 0 hF
      simpa [F, proj, e] using hcomp
    have hpathAt : ContinuousAt gateauxCounterexampleCubicPath 0 := by
      -- The cubic path is a sum of continuous coordinate injections.
      unfold gateauxCounterexampleCubicPath
      exact (continuousAt_id.smul_const _).add
        ((hasDerivAt_pow 3 (0 : ℝ)).continuousAt.smul_const _)
    have hpathZeroVec : gateauxCounterexampleCubicPath 0 = (0 : EuclideanSpace ℝ (Fin 2)) := by
      simp [gateauxCounterexampleCubicPath]
    have hpathCont :
        ContinuousAt
          (fun u : ℝ ↦ gateauxNotFrechetCounterexampleScalar (gateauxCounterexampleCubicPath u))
          0 := by
      -- Compose continuity of the scalar counterexample with the cubic path through the origin.
      have houter :
          ContinuousAt gateauxNotFrechetCounterexampleScalar
            (gateauxCounterexampleCubicPath 0) := by
        simpa [hpathZeroVec] using hscalarDiff.continuousAt
      exact ContinuousAt.comp houter hpathAt
    have hpathZero :
        gateauxNotFrechetCounterexampleScalar (gateauxCounterexampleCubicPath 0) = 0 := by
      simp [gateauxCounterexampleCubicPath, gateauxNotFrechetCounterexampleScalar]
    rcases Metric.mem_nhds_iff.mp
        (hpathCont (by simpa [hpathZero] using
          Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))) with
      ⟨δ, hδpos, hδ⟩
    have hhalf_mem : (δ / 2 : ℝ) ∈ Metric.ball (0 : ℝ) δ := by
      simp [Metric.mem_ball, abs_of_nonneg, hδpos.le, half_lt_self hδpos]
    have himage_mem := hδ hhalf_mem
    have hhalf_ne : (δ / 2 : ℝ) ≠ 0 := by positivity
    have hvalue :
        gateauxNotFrechetCounterexampleScalar (gateauxCounterexampleCubicPath (δ / 2)) =
          (1 / 2 : ℝ) :=
      gateauxCounterexampleScalar_path_eq_half hhalf_ne
    have : (1 / 2 : ℝ) ∈ Metric.ball (0 : ℝ) (1 / 4) := by
      simpa [Metric.mem_ball, hvalue] using himage_mem
    norm_num [Metric.mem_ball, abs_of_nonneg] at this

/-- Consequence of Chapter01 Definition 1.2.28 (9): the common Gateaux/Fréchet derivative at `x`
is represented in the standard Euclidean bases by the Jacobian matrix. -/
theorem jacobianMatrix_eq_gateauxDerivativeMatrix
    {D : Set Point} {F : Point → Target} {A B : Point →L[ℝ] Target} {x : Point}
    (hD_open : IsOpen D)
    (hx : x ∈ D)
    (hGateaux : IsGateauxDerivativeWithinAt ℝ D F x B)
    (hF : HasFDerivAt F A x) :
    LinearMap.toMatrix
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
        A.toLinearMap =
      Matrix.of fun i j ↦ (B ((EuclideanSpace.basisFun (Fin n) ℝ) j)) i := by
  -- First identify the Fréchet and Gateaux derivatives, then evaluate matrix entries.
  rw [gateauxDerivative_eq_fderiv hD_open hx hGateaux hF]
  ext i j
  simp [LinearMap.toMatrix_apply]

/-- Consequence of Chapter01 Definition 1.2.28 (10): for a Gateaux differentiable
map on an open convex set, each component satisfies a mean-value formula at
some parameter `t i ∈ [0, 1]`. -/
theorem meanValue_exists_component_parameters
    {D : Set Point} (F : Point → Target) (F' : Point → Point →L[ℝ] Target)
    {x y : Point}
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hGateaux : ∀ z ∈ D, IsGateauxDerivativeWithinAt ℝ D F z (F' z))
    (hx : x ∈ D)
    (hy : y ∈ D) :
    ∃ t : Fin m → ℝ, (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ i, (F y - F x) i = (F' (x + (t i) • (y - x)) (y - x)) i := by
  let _ := hD_open
  classical
  have hcoord :
      ∀ i : Fin m, ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
        (F y - F x) i = (F' (x + t • (y - x)) (y - x)) i := by
    intro i
    let proj : Target →L[ℝ] ℝ := PiLp.proj (p := 2) (β := fun _ : Fin m => ℝ) i
    let g : ℝ → ℝ := fun s ↦ (F (x + s • (y - x))) i
    have hcont :
        ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      have hseg :
          ContinuousWithinAt
            (fun s : ℝ ↦ F (AffineMap.lineMap x y s))
            (Set.Icc (0 : ℝ) 1)
            t := by
        -- The segment pullback is continuous at every parameter because it has a derivative there.
        exact
          (segmentHasDerivWithinAt_of_isGateauxDerivativeWithinAt
            (F := F) (F' := F') hD_convex hGateaux hx hy t ht).continuousWithinAt
      have hproj :
          ContinuousWithinAt
            (fun s : ℝ ↦ proj (F (AffineMap.lineMap x y s)))
            (Set.Icc (0 : ℝ) 1)
            t := by
        -- Scalarize the segment pullback with the coordinate projection.
        exact proj.continuous.continuousAt.comp_continuousWithinAt hseg
      simpa [g, proj, AffineMap.lineMap_apply_module', add_comm] using hproj
    have hderiv :
        ∀ t ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt g ((F' (x + t • (y - x)) (y - x)) i) t := by
      intro t ht
      have hseg :
          HasDerivAt
            (fun s : ℝ ↦ F (AffineMap.lineMap x y s))
            (F' (AffineMap.lineMap x y t) (y - x))
            t := by
        -- Upgrade the segment derivative to an ordinary derivative at interior parameters.
        exact
          (segmentHasDerivWithinAt_of_isGateauxDerivativeWithinAt
            (F := F) (F' := F') hD_convex hGateaux hx hy t (Set.mem_Icc_of_Ioo ht)).hasDerivAt
            (Icc_mem_nhds ht.1 ht.2)
      have hproj :
          HasDerivAt
            (fun s : ℝ ↦ proj (F (AffineMap.lineMap x y s)))
            ((F' (AffineMap.lineMap x y t) (y - x)) i)
            t := by
        -- Compose the vector-valued derivative with the coordinate projection.
        exact (proj.hasFDerivAt.comp_hasDerivAt t hseg)
      simpa [g, proj, AffineMap.lineMap_apply_module', add_comm] using hproj
    obtain ⟨t, ht, hmvt⟩ :=
      exists_hasDerivAt_eq_slope g
        (fun s ↦ (F' (x + s • (y - x)) (y - x)) i)
        zero_lt_one
        hcont
        hderiv
    refine ⟨t, Set.mem_Icc_of_Ioo ht, ?_⟩
    -- Rewrite the mean-value slope back into the desired component identity.
    simpa [g, AffineMap.lineMap_apply_module', add_comm, sub_eq_add_neg] using hmvt.symm
  choose t ht hEq using hcoord
  refine ⟨t, ht, hEq⟩

end Euclidean
