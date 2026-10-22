/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.UpperHalfSpace
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Exercise_25_4_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Exercise_25_4_1.LocalOneSidedBrownianHitting
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

section HalfSpace

variable (n : ℕ)

local notation "State" => EuclideanSpace ℝ (Fin (n + 1))
local notation "Boundary" => EuclideanSpace ℝ (Fin n)
local notation "VectorProcess" => NNReal → Ω → State

/-- The first exit time of the translated Brownian path `t ↦ x + W_t` from the upper half-space,
encoded as `⊤` if the path never leaves. -/
def upperHalfSpaceExitTime (W : VectorProcess) (x : State) : Ω → WithTop NNReal :=
  hittingAfter (fun t ω ↦ x + W t ω) (upperHalfSpace n)ᶜ 0

/-- The boundary coordinates of the Brownian exit point from the upper half-space; when the exit
time is infinite, this is the boundary projection of the canonical stopped value. -/
def upperHalfSpaceExitLocation (W : VectorProcess) (x : State) : Ω → Boundary :=
  fun ω ↦
    upperHalfSpaceBoundaryProjection n
      (stoppedValue (fun t ω ↦ x + W t ω) (upperHalfSpaceExitTime n W x) ω)

omit [MeasurableSpace Ω] in
/-- Evaluating the exit location returns the horizontal coordinates of the stopped value of
`x + W`. -/
theorem upperHalfSpaceExitLocation_apply (W : VectorProcess) (x : State) (ω : Ω) (i : Fin n) :
    upperHalfSpaceExitLocation n W x ω i =
      (stoppedValue (fun t ω ↦ x + W t ω) (upperHalfSpaceExitTime n W x) ω) (Fin.castSucc i) := by
  simp [upperHalfSpaceExitLocation]

/-- The upper-half-space exit value as a point of `frontier (upperHalfSpace n)`, obtained from the
boundary-coordinate exit map via the inverse of the canonical boundary identification. -/
def upperHalfSpaceExitValue (W : VectorProcess) (x : State) : Ω → frontier (upperHalfSpace n) :=
  fun ω ↦ (upperHalfSpaceFrontierEquiv n).symm (upperHalfSpaceExitLocation n W x ω)

omit [MeasurableSpace Ω] in
/-- Applying the canonical boundary identification to the frontier-valued exit map recovers the
coordinate exit-location map. -/
@[simp] theorem upperHalfSpaceFrontierEquiv_exitValue (W : VectorProcess) (x : State) :
    upperHalfSpaceFrontierEquiv n ∘ upperHalfSpaceExitValue n W x =
      upperHalfSpaceExitLocation n W x := by
  funext ω
  simp [upperHalfSpaceExitValue]

/-- The squared Euclidean distance between the boundary projection of `x` and the boundary point
`y`. -/
def upperHalfSpaceBoundaryDistanceSq (x : State) (y : Boundary) : ℝ :=
  dist (upperHalfSpaceBoundaryProjection n x) y ^ (2 : ℕ)

/-- The Poisson kernel density of the upper half-space `ℝ^n × (0,∞)` evaluated at interior point
`x` and boundary point `y`. -/
def upperHalfSpacePoissonKernel (x : State) (y : Boundary) : ℝ :=
  Real.Gamma (((n + 1 : ℕ) : ℝ) / 2) /
      (Real.pi ^ (((n + 1 : ℕ) : ℝ) / 2)) *
    x (Fin.last n) /
      (upperHalfSpaceBoundaryDistanceSq n x y + x (Fin.last n) ^ (2 : ℕ)) ^
        (((n + 1 : ℕ) : ℝ) / 2)

variable {n}
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : VectorProcess}

/-- Helper for Exercise 25.4.2: probability measures on a subsingleton measurable space are equal.
-/
theorem measure_eq_of_subsingleton_of_isProbabilityMeasure
    {α : Type*} [MeasurableSpace α] [Subsingleton α] {ν₁ ν₂ : Measure α}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    ν₁ = ν₂ := by
  -- Proof comment: every measurable set in a subsingleton space is either `∅` or `Set.univ`, and
  -- probability measures agree on both of those sets.
  refine Measure.ext ?_
  intro s hs
  refine Subsingleton.set_cases ?_ ?_ s
  · simp
  · simp

/-- Helper for Exercise 25.4.2: when `n = 0`, the upper-half-space Poisson kernel is identically
`1` on the unique boundary point. -/
theorem upperHalfSpacePoissonKernel_zero_eq_one
    {x : EuclideanSpace ℝ (Fin (0 + 1))}
    (hx : x ∈ upperHalfSpace 0) (y : EuclideanSpace ℝ (Fin 0)) :
    upperHalfSpacePoissonKernel 0 x y = 1 := by
  have hx_last : 0 < x (Fin.last 0) := by
    simpa [upperHalfSpace] using hx
  have hy : y = 0 := Subsingleton.elim _ _
  subst hy
  have hpi :
      Real.pi ^ (1 / 2 : ℝ) = Real.sqrt Real.pi := by
    -- Proof comment: the zero-dimensional normalization only needs the `r = 1` specialization of
    -- `rpow_div_two_eq_sqrt`.
    simpa using (Real.rpow_div_two_eq_sqrt (x := Real.pi) (r := (1 : ℝ)) Real.pi_nonneg)
  have hxpow :
      ((x (Fin.last 0)) ^ (2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) = x (Fin.last 0) := by
    calc
      ((x (Fin.last 0)) ^ (2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)
          = Real.sqrt (((x (Fin.last 0)) ^ (2 : ℕ) : ℝ)) := by
              simpa using
                (Real.rpow_div_two_eq_sqrt
                  (x := ((x (Fin.last 0)) ^ (2 : ℕ) : ℝ))
                  (r := (1 : ℝ))
                  (sq_nonneg (x (Fin.last 0))))
      _ = x (Fin.last 0) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_pos hx_last]
  have hproj :
      upperHalfSpaceBoundaryProjection 0 x = (0 : EuclideanSpace ℝ (Fin 0)) :=
    Subsingleton.elim _ _
  have hdist :
      upperHalfSpaceBoundaryDistanceSq 0 x (0 : EuclideanSpace ℝ (Fin 0)) = 0 := by
    -- Proof comment: the boundary of the one-dimensional half-space is the singleton `ℝ^0`.
    simpa [upperHalfSpaceBoundaryDistanceSq, hproj]
  -- Proof comment: in dimension `1`, the boundary is a singleton, so the horizontal distance
  -- term vanishes and the Gamma/π prefactor simplifies to `1`.
  calc
    upperHalfSpacePoissonKernel 0 x 0
        = Real.Gamma (1 / 2 : ℝ) / (Real.pi ^ (1 / 2 : ℝ)) * x (Fin.last 0) /
            (((x (Fin.last 0)) ^ (2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by
              simp [upperHalfSpacePoissonKernel, hdist]
    _ = Real.sqrt Real.pi / Real.sqrt Real.pi * x (Fin.last 0) / x (Fin.last 0) := by
          rw [Real.Gamma_one_half_eq, hpi, hxpow]
    _ = 1 := by
          field_simp [Real.pi_ne_zero, hx_last.ne']

/-- Helper for Exercise 25.4.2: in the one-dimensional half-space case, the explicit
Poisson-kernel measure is the Dirac mass at the unique boundary point. -/
theorem upperHalfSpacePoissonKernelMeasure_zero_eq_dirac
    {x : EuclideanSpace ℝ (Fin (0 + 1))}
    (hx : x ∈ upperHalfSpace 0) :
    (volume.withDensity
      (fun y ↦ ENNReal.ofReal (upperHalfSpacePoissonKernel 0 x y)) :
        Measure (EuclideanSpace ℝ (Fin 0))) =
      Measure.dirac 0 := by
  -- Proof comment: the density is constantly `1`, so the candidate measure is just Lebesgue
  -- measure on the zero-dimensional Euclidean space, which is the Dirac mass at `0`.
  calc
    (volume.withDensity
      (fun y ↦ ENNReal.ofReal (upperHalfSpacePoissonKernel 0 x y)) :
        Measure (EuclideanSpace ℝ (Fin 0)))
        = volume.withDensity (fun _ : EuclideanSpace ℝ (Fin 0) ↦ (1 : ENNReal)) := by
            congr
            ext y
            rw [upperHalfSpacePoissonKernel_zero_eq_one hx y, ENNReal.ofReal_one]
    _ = (volume : Measure (EuclideanSpace ℝ (Fin 0))) := by
          simpa using (withDensity_one (μ := (volume : Measure (EuclideanSpace ℝ (Fin 0)))))
    _ = Measure.dirac 0 := by
          simpa using (volume_euclideanSpace_eq_dirac (ι := Fin 0))

/-- Pushing the canonical harmonic measure on `frontier (upperHalfSpace n)` forward along the
boundary identification recovers the boundary-coordinate exit law, provided the canonical
frontier-valued exit map is measurable. -/
theorem map_upperHalfSpaceFrontierEquiv_harmonicMeasure
    (W : VectorProcess) {x : State} (hx : x ∈ upperHalfSpace n)
    (hExitMeas : Measurable (upperHalfSpaceExitValue n W x)) :
    Measure.map (upperHalfSpaceFrontierEquiv n)
        (harmonicMeasure
          (fun _ : State ↦ (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω))
          (upperHalfSpace n)
          (upperHalfSpaceExitValue n W x)
          hExitMeas
          ⟨x, hx⟩ : Measure (frontier (upperHalfSpace n))) =
      Measure.map (upperHalfSpaceExitLocation n W x) μ := by
  -- Push the harmonic measure definition back to the underlying starting law `μ`.
  have hFrontierMeas : Measurable (upperHalfSpaceFrontierEquiv n) := by
    simp [upperHalfSpaceFrontierEquiv]
    fun_prop
  -- Then compose the two pushforwards and use the canonical exit-value identification.
  simpa [harmonicMeasure, upperHalfSpaceFrontierEquiv_exitValue] using
    (Measure.map_map hFrontierMeas hExitMeas : _)

/-- Helper for Exercise 25.4.2: the boundary-coordinate exit law is the canonical harmonic measure
pushed forward along the upper-half-space boundary identification. -/
theorem upperHalfSpaceExitDistribution_eq_mapHarmonicMeasure
    (W : VectorProcess) {x : State} (hx : x ∈ upperHalfSpace n)
    (hExitMeas : Measurable (upperHalfSpaceExitValue n W x)) :
    Measure.map (upperHalfSpaceExitLocation n W x) μ =
      Measure.map (upperHalfSpaceFrontierEquiv n)
        (harmonicMeasure
          (fun _ : State ↦ (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω))
          (upperHalfSpace n)
          (upperHalfSpaceExitValue n W x)
          hExitMeas
          ⟨x, hx⟩ : Measure (frontier (upperHalfSpace n))) := by
  -- Proof comment: this is exactly the previously established harmonic-measure pushforward
  -- identity, read in the reverse direction.
  symm
  exact map_upperHalfSpaceFrontierEquiv_harmonicMeasure
    (μ := μ) (n := n) (W := W) hx hExitMeas

/-- Helper for Exercise 25.4.2: the harmonic measure on `frontier (upperHalfSpace n)` transported
to boundary coordinates. -/
def upperHalfSpaceBoundaryHarmonicMeasure
    (W : VectorProcess) (x : State) (hx : x ∈ upperHalfSpace n)
    (hExitMeas : Measurable (upperHalfSpaceExitValue n W x)) : Measure Boundary :=
  Measure.map (upperHalfSpaceFrontierEquiv n)
    (harmonicMeasure
      (fun _ : State ↦ (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω))
      (upperHalfSpace n)
      (upperHalfSpaceExitValue n W x)
      hExitMeas
      ⟨x, hx⟩ : Measure (frontier (upperHalfSpace n)))

/-- Helper for Exercise 25.4.2: the explicit Poisson-kernel boundary measure on `ℝ^n`. -/
def upperHalfSpacePoissonKernelMeasure (x : State) : Measure Boundary :=
  volume.withDensity (fun y ↦ ENNReal.ofReal (upperHalfSpacePoissonKernel n x y))

/-- Helper for Exercise 25.4.2: if the translated path reaches the complement of the half-space
at some nonnegative time, then the first exit time cannot be `⊤`. -/
theorem upperHalfSpaceExitTime_ne_top_of_exists_mem_compl
    (W : VectorProcess) (x : State) {ω : Ω}
    (hHit :
      ∃ t : NNReal, (0 : NNReal) ≤ t ∧ x + W t ω ∈ (upperHalfSpace n)ᶜ) :
    upperHalfSpaceExitTime n W x ω ≠ ⊤ := by
  intro hExit_top
  rcases hHit with ⟨t, ht0, ht_mem⟩
  have havoid :
      ∀ s : NNReal, (0 : NNReal) ≤ s → x + W s ω ∉ (upperHalfSpace n)ᶜ := by
    -- Proof comment: if `hittingAfter` were `⊤`, the translated path would avoid the complement
    -- at every nonnegative time.
    exact
      (hittingAfter_eq_top_iff (u := fun s ω ↦ x + W s ω)
        (s := (upperHalfSpace n)ᶜ) (n := (0 : NNReal)) (ω := ω)).1 hExit_top
  exact havoid t ht0 ht_mem

/-- Helper for Exercise 25.4.2: a concrete hit of the complement forces the first exit time to be
finite. -/
theorem upperHalfSpaceExitTime_lt_top_of_exists_mem_compl
    (W : VectorProcess) (x : State) {ω : Ω}
    (hHit :
      ∃ t : NNReal, (0 : NNReal) ≤ t ∧ x + W t ω ∈ (upperHalfSpace n)ᶜ) :
    upperHalfSpaceExitTime n W x ω < ⊤ := by
  -- Proof comment: on `WithTop NNReal`, finiteness is exactly non-equality with `⊤`.
  exact
    lt_top_iff_ne_top.mpr
      (upperHalfSpaceExitTime_ne_top_of_exists_mem_compl (n := n) W x hHit)

-- Proof sketch: apply one-dimensional recurrence to the last coordinate
-- `x_{n+1} + W_t^{n+1}`, whose first hit of `(-∞,0]` is almost surely finite; exiting the
-- half-space is equivalent to that last coordinate hitting the boundary.
/-- Exercise 25.4.2 (1): if `x` lies in the upper half-space `ℝ^n × (0,∞)` and the last
coordinate of `W` is a Brownian motion, then the exit time of `x + W` from the half-space is
almost surely finite. -/
theorem upperHalfSpaceExitTime_ae_lt_top
    (hW : IsBrownianMotion μ (fun t ω ↦ W t ω (Fin.last n))) {x : State}
    (hx : x ∈ upperHalfSpace n) :
    ∀ᵐ ω ∂μ, upperHalfSpaceExitTime n W x ω < ⊤ := by
  have hx_last : 0 < x (Fin.last n) := by
    simpa using hx
  let B : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω (Fin.last n)) (-1)
  have hB : IsBrownianMotion μ B := by
    -- Replace the last coordinate by its negative so that hitting the positive level `x_d`
    -- means the translated path has reached the boundary.
    simpa [B, brownianScaling] using
      (IsBrownianMotion.scaling hW (K := (-1 : ℝ)) (by norm_num))
  have hhit_lt_top :
      ∀ᵐ ω ∂μ, brownianLevelHittingTime B (x (Fin.last n)) ω < ⊤ := by
    filter_upwards [brownianLevelHittingTime_ae_ne_top hB hx_last] with ω hω
    exact lt_top_iff_ne_top.mpr hω
  filter_upwards [hhit_lt_top] with ω hω
  have hhit_ne : brownianLevelHittingTime B (x (Fin.last n)) ω ≠ ⊤ := hω.ne
  -- Extract a concrete time at which the negated last coordinate hits the level `x_d`.
  have hhit_exists :
      ∃ t : NNReal, (0 : NNReal) ≤ t ∧ B t ω ∈ ({x (Fin.last n)} : Set ℝ) := by
    by_contra h_exists
    apply hhit_ne
    rw [brownianLevelHittingTime_eq_hittingAfter, hittingAfter_eq_top_iff]
    intro t ht
    exact fun hmem ↦ h_exists ⟨t, ht, hmem⟩
  rcases hhit_exists with ⟨t, ht0, ht_hit⟩
  have ht_last : W t ω (Fin.last n) = -x (Fin.last n) := by
    have ht_hit' : B t ω = x (Fin.last n) := by simpa using ht_hit
    simpa [B, brownianScaling] using ht_hit'
  have ht_exit_mem : x + W t ω ∈ (upperHalfSpace n)ᶜ := by
    -- At the hitting time, the last coordinate of `x + W_t` is exactly `0`.
    simp [upperHalfSpace, ht_last]
  -- Proof comment: once the translated path reaches the boundary complement, the exit time is
  -- finite by the general helper above.
  exact
    upperHalfSpaceExitTime_lt_top_of_exists_mem_compl (n := n) W x
      ⟨t, ht0, ht_exit_mem⟩

-- Proof sketch: identify the boundary-coordinate exit distribution of `x + W` from the half-space
-- with the classical Poisson kernel obtained by Fourier transform in the horizontal variables and
-- the one-dimensional first-hitting analysis in the vertical coordinate; this is equivalently the
-- harmonic measure pushed forward along the canonical boundary identification.
section

/-- Helper for Exercise 25.4.2: the multivariate characteristic function at `t` is the
one-dimensional characteristic function of the scalar projection `y ↦ ⟪y, t⟫` evaluated at
frequency `1`. -/
theorem charFun_eq_charFun_innerProjection
    {ν : Measure Boundary} [IsFiniteMeasure ν] (t : Boundary) :
    charFun ν t = charFun (Measure.map (fun y ↦ inner ℝ y t) ν) 1 := by
  -- Proof comment: rewrite the pushed-forward real characteristic function with
  -- `MeasureTheory.charFun_apply_real`, then transport it back through `integral_map`.
  have hinnerMeas : Measurable (fun y : Boundary ↦ inner ℝ y t) := by
    fun_prop
  have hexpMeas :
      AEStronglyMeasurable
        (fun y : ℝ ↦ Complex.exp ((1 : ℝ) * y * Complex.I))
        (Measure.map (fun y ↦ inner ℝ y t) ν) := by
    fun_prop
  rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply_real]
  rw [integral_map hinnerMeas.aemeasurable hexpMeas]
  congr with y
  simp [mul_assoc, mul_comm]

/-- Helper for Exercise 25.4.2: projecting along a nonzero direction factors through its unit
direction and a scalar dilation by `‖t‖`. -/
theorem map_inner_eq_map_scale_unitProjection
    {ν : Measure Boundary} {t : Boundary} (ht : t ≠ 0) :
    Measure.map (fun y ↦ inner ℝ y t) ν =
      Measure.map (fun z : ℝ ↦ ‖t‖ * z)
        (Measure.map (fun y ↦ inner ℝ y (‖t‖⁻¹ • t)) ν) := by
  have hnorm_ne : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have hcomp :
      (fun y : Boundary ↦ inner ℝ y t) =
        (fun z : ℝ ↦ ‖t‖ * z) ∘ fun y : Boundary ↦ inner ℝ y (‖t‖⁻¹ • t) := by
    -- Proof comment: rewrite the original projection as a projection onto the normalized
    -- direction followed by the scalar dilation `z ↦ ‖t‖ z`.
    funext y
    rw [Function.comp_apply, inner_smul_right]
    field_simp [hnorm_ne]
  -- Proof comment: once the scalar-projection identity is normalized, the measure statement is
  -- just functoriality of `Measure.map`.
  rw [hcomp, Measure.map_map]
  all_goals
    fun_prop

/-- Helper for Exercise 25.4.2: a boundary vector of norm `1` is nonzero. -/
theorem boundaryVector_ne_zero_of_norm_eq_one
    {u : Boundary} (hu : ‖u‖ = 1) :
    u ≠ 0 := by
  -- Proof comment: a zero vector has norm `0`, so a unit vector cannot vanish.
  intro hu0
  have hnorm_ne : ‖u‖ ≠ 0 := by
    simpa [hu]
  exact hnorm_ne (by simpa [hu0])

/-- Helper for Exercise 25.4.2: the existence of a unit boundary vector forces positive boundary
dimension. -/
theorem boundaryDimension_ne_zero_of_norm_eq_one
    {u : Boundary} (hu : ‖u‖ = 1) :
    n ≠ 0 := by
  -- Proof comment: if `n = 0`, then the boundary space is a subsingleton, so every vector is `0`.
  intro hn
  subst hn
  exact boundaryVector_ne_zero_of_norm_eq_one
    (n := 0) hu (Subsingleton.elim _ _)

/-- Helper for Exercise 25.4.2: projecting the transported harmonic measure along `u` is just the
pushforward law of the scalar exit-location observable `ω ↦ ⟪upperHalfSpaceExitLocation ω, u⟫`. -/
theorem map_inner_upperHalfSpaceBoundaryHarmonicMeasure_eq_map_exitProjection
    (W : VectorProcess) {x : State} (hx : x ∈ upperHalfSpace n)
    (hExitMeas : Measurable (upperHalfSpaceExitValue n W x))
    (u : Boundary) :
    Measure.map (fun y ↦ inner ℝ y u)
      (upperHalfSpaceBoundaryHarmonicMeasure (μ := μ) (n := n) W x hx hExitMeas) =
        Measure.map (fun ω ↦ inner ℝ (upperHalfSpaceExitLocation n W x ω) u) μ := by
  -- Proof comment: first replace the transported harmonic measure by the exit-location law, then
  -- compose the scalar projection with that exit map.
  have hExitLocMeas : Measurable (upperHalfSpaceExitLocation n W x) := by
    -- Proof comment: `upperHalfSpaceExitLocation` is the boundary identification applied to the
    -- measurable frontier-valued exit map.
    have hFrontierMeas : Measurable (upperHalfSpaceFrontierEquiv n) := by
      simp [upperHalfSpaceFrontierEquiv]
      fun_prop
    rw [← upperHalfSpaceFrontierEquiv_exitValue (n := n) (W := W) (x := x)]
    exact hFrontierMeas.comp hExitMeas
  rw [upperHalfSpaceBoundaryHarmonicMeasure]
  rw [map_upperHalfSpaceFrontierEquiv_harmonicMeasure
    (μ := μ) (n := n) (W := W) hx hExitMeas]
  rw [Measure.map_map]
  · rfl
  · fun_prop
  · exact hExitLocMeas

/-- Helper for Exercise 25.4.2: the scalar projection of a boundary point is the sum of its
horizontal coordinates weighted by the coordinates of `u`. -/
theorem inner_upperHalfSpaceBoundaryProjection_eq_sum
    (u : Boundary) (z : State) :
    inner ℝ u (upperHalfSpaceBoundaryProjection n z) =
      ∑ i : Fin n, u i * z (Fin.castSucc i) := by
  -- Proof comment: the boundary projection simply forgets the last coordinate, and the Euclidean
  -- inner product on `ℝ^n` is the coordinate sum.
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simpa [upperHalfSpaceBoundaryProjection] using
    (RCLike.inner_apply' (u i) (z (Fin.castSucc i)))

/-- Helper for Exercise 25.4.2: the scalar projection of the exit location is the corresponding
coordinate sum on the stopped Brownian value. -/
theorem inner_upperHalfSpaceExitLocation_eq_stoppedValue_sum
    (W : VectorProcess) (x : State) (u : Boundary) (ω : Ω) :
    inner ℝ (upperHalfSpaceExitLocation n W x ω) u =
      ∑ i : Fin n,
        u i * (stoppedValue (fun t ω ↦ x + W t ω) (upperHalfSpaceExitTime n W x) ω)
          (Fin.castSucc i) := by
  -- Proof comment: expand the exit-location coordinates through
  -- `upperHalfSpaceExitLocation_apply` and then use the previous coordinate-sum lemma.
  rw [real_inner_comm]
  simpa [upperHalfSpaceExitLocation] using
    inner_upperHalfSpaceBoundaryProjection_eq_sum (n := n) u
      (stoppedValue (fun t ω ↦ x + W t ω) (upperHalfSpaceExitTime n W x) ω)

/-- Helper for Exercise 25.4.2: projecting the horizontal Brownian coordinates onto a unit
boundary direction yields a real Brownian motion. -/
theorem unitDirectionHorizontalBrownian_isBrownianMotion
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    {u : Boundary} (hu : ‖u‖ = 1) :
    IsBrownianMotion μ
      (fun t ω ↦ inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u) := by
  let X : NNReal → Ω → ℝ :=
    fun t ω ↦ inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u
  -- Proof comment: verify the centered Gaussian-process characterization for the scalar process
  -- obtained by projecting the horizontal Brownian coordinates onto the unit direction `u`.
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- At time `0`, every coordinate Brownian motion vanishes, so the projection also vanishes.
    funext ω
    rw [real_inner_comm, inner_upperHalfSpaceBoundaryProjection_eq_sum (n := n) u (W 0 ω)]
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp [show W 0 ω (Fin.castSucc i) = 0 by
      simpa using congrFun ((hW.isBrownianMotion (Fin.castSucc i)).zero) ω]
  · -- Each finite-dimensional law is the sum of independent Gaussian coordinate restrictions.
    refine ⟨?_⟩
    intro I
    let Xi : Fin n → Ω → (I → ℝ) := fun i ω t ↦ u i * W (t : NNReal) ω (Fin.castSucc i)
    have hXi_gauss : ∀ i : Fin n, HasGaussianLaw (Xi i) μ := by
      intro i
      let hGi : IsGaussianProcess (fun t ω ↦ u i * W t ω (Fin.castSucc i)) μ := by
        simpa [smul_eq_mul] using
          (ProbabilityTheory.IsGaussianProcess.smul
            (c := fun _ : NNReal ↦ u i)
            (IsBrownianMotion.isGaussianProcess
              (show IsBrownianMotion μ (fun t ω ↦ W t ω (Fin.castSucc i)) from inferInstance)))
      simpa [Xi] using hGi.hasGaussianLaw I
    have hIndepBase :
        iIndepFun (fun i : Fin n ↦ fun ω ↦ fun t : NNReal ↦ W t ω (Fin.castSucc i)) μ := by
      simpa using hW.iIndepFun.precomp (g := Fin.castSucc) (Fin.castSucc_injective n)
    have hXi_indep' :
        iIndepFun
          (fun i ↦ (fun f ↦ fun t : I ↦ u i * f t) ∘ fun ω ↦ fun t : NNReal ↦ W t ω (Fin.castSucc i))
          μ := by
      simpa [Function.comp] using
        hIndepBase.comp (fun i ↦ fun f ↦ fun t : I ↦ u i * f t) (fun i ↦ by fun_prop)
    have hXi_indep : iIndepFun Xi μ := by
      simpa [Xi, Function.comp] using hXi_indep'
    have hgauss_sum : HasGaussianLaw (fun ω ↦ ∑ i : Fin n, Xi i ω) μ :=
      ProbabilityTheory.iIndepFun.hasGaussianLaw_fun_sum hXi_gauss hXi_indep
    refine hgauss_sum.congr (Filter.Eventually.of_forall fun ω ↦ ?_)
    ext t
    simp [X, Xi, real_inner_comm, inner_upperHalfSpaceBoundaryProjection_eq_sum]
  · -- Centeredness is inherited from the coordinate Brownian means.
    intro t
    change ∫ ω, (∑ i : Fin n, u i * W t ω (Fin.castSucc i)) ∂μ = 0
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero ?_
      intro i hi
      rw [integral_const_mul]
      rw [IsBrownianMotion.mean_zero
        (show IsBrownianMotion μ (fun r ω ↦ W r ω (Fin.castSucc i)) from inferInstance) t]
      simp
    · intro i hi
      have hcoord_mem :
          MemLp (fun ω ↦ W t ω (Fin.castSucc i)) 2 μ :=
        brownianEval_memLp_two
          (show IsBrownianMotion μ (fun r ω ↦ W r ω (Fin.castSucc i)) from inferInstance) t
      have hcoord_int :
          Integrable (fun ω ↦ W t ω (Fin.castSucc i)) μ :=
        hcoord_mem.integrable (by norm_num)
      exact hcoord_int.const_mul (u i)
  · -- Expand the covariance of the finite sum and keep only the diagonal Brownian terms.
    intro s t
    let Xs : Fin n → Ω → ℝ := fun i ω ↦ u i * W s ω (Fin.castSucc i)
    let Xt : Fin n → Ω → ℝ := fun i ω ↦ u i * W t ω (Fin.castSucc i)
    have hXs_mem : ∀ i : Fin n, MemLp (Xs i) 2 μ := by
      intro i
      simpa [Xs] using
        (brownianEval_memLp_two
          (show IsBrownianMotion μ (fun r ω ↦ W r ω (Fin.castSucc i)) from inferInstance) s).const_mul
          (u i)
    have hXt_mem : ∀ i : Fin n, MemLp (Xt i) 2 μ := by
      intro i
      simpa [Xt] using
        (brownianEval_memLp_two
          (show IsBrownianMotion μ (fun r ω ↦ W r ω (Fin.castSucc i)) from inferInstance) t).const_mul
          (u i)
    have hcov_offdiag :
        ∀ i j : Fin n, i ≠ j → cov[Xs i, Xt j; μ] = 0 := by
      intro i j hij
      have hij_indepProc :
          (fun ω ↦ fun r : NNReal ↦ W r ω (Fin.castSucc i)) ⟂ᵢ[μ]
            (fun ω ↦ fun r : NNReal ↦ W r ω (Fin.castSucc j)) := by
        exact
          (hW.iIndepFun.precomp (g := Fin.castSucc) (Fin.castSucc_injective n)).indepFun hij
      have hij_indepEval :
          (fun ω ↦ W s ω (Fin.castSucc i)) ⟂ᵢ[μ]
            (fun ω ↦ W t ω (Fin.castSucc j)) := by
        simpa using
          hij_indepProc.comp
            (hφ := measurable_pi_apply s)
            (hψ := measurable_pi_apply t)
      have hs_mem :
          MemLp (fun ω ↦ W s ω (Fin.castSucc i)) 2 μ :=
        brownianEval_memLp_two
          (show IsBrownianMotion μ (fun r ω ↦ W r ω (Fin.castSucc i)) from inferInstance) s
      have ht_mem :
          MemLp (fun ω ↦ W t ω (Fin.castSucc j)) 2 μ :=
        brownianEval_memLp_two
          (show IsBrownianMotion μ (fun r ω ↦ W r ω (Fin.castSucc j)) from inferInstance) t
      calc
        cov[Xs i, Xt j; μ]
            = u i * cov[(fun ω ↦ W s ω (Fin.castSucc i)), Xt j; μ] := by
                rw [show Xs i = fun ω ↦ u i * W s ω (Fin.castSucc i) by rfl,
                  covariance_const_mul_left]
        _ = u i * (u j * cov[(fun ω ↦ W s ω (Fin.castSucc i)),
            (fun ω ↦ W t ω (Fin.castSucc j)); μ]) := by
              rw [show Xt j = fun ω ↦ u j * W t ω (Fin.castSucc j) by rfl,
                covariance_const_mul_right]
        _ = 0 := by
          simp [hij_indepEval.covariance_eq_zero hs_mem ht_mem]
    have hcov_diag :
        ∀ i : Fin n, cov[Xs i, Xt i; μ] = u i ^ (2 : ℕ) * ((s ⊓ t : NNReal) : ℝ) := by
      intro i
      have hcov_i :
          cov[(fun ω ↦ W s ω (Fin.castSucc i)), (fun ω ↦ W t ω (Fin.castSucc i)); μ] =
            ((s ⊓ t : NNReal) : ℝ) := by
        simpa using
          IsBrownianMotion.covariance_eq
            (show IsBrownianMotion μ (fun r ω ↦ W r ω (Fin.castSucc i)) from inferInstance) s t
      calc
        cov[Xs i, Xt i; μ]
            = u i * cov[(fun ω ↦ W s ω (Fin.castSucc i)), Xt i; μ] := by
                rw [show Xs i = fun ω ↦ u i * W s ω (Fin.castSucc i) by rfl,
                  covariance_const_mul_left]
        _ = u i * (u i * cov[(fun ω ↦ W s ω (Fin.castSucc i)),
            (fun ω ↦ W t ω (Fin.castSucc i)); μ]) := by
              rw [show Xt i = fun ω ↦ u i * W t ω (Fin.castSucc i) by rfl,
                covariance_const_mul_right]
        _ = u i ^ (2 : ℕ) * ((s ⊓ t : NNReal) : ℝ) := by
          simp [hcov_i, pow_two, mul_assoc, mul_left_comm, mul_comm]
    have hnorm_sq : ∑ i : Fin n, u i ^ (2 : ℕ) = ‖u‖ ^ (2 : ℕ) := by
      simpa [pow_two] using (EuclideanSpace.real_norm_sq_eq u).symm
    change cov[(fun ω ↦ ∑ i : Fin n, Xs i ω), (fun ω ↦ ∑ i : Fin n, Xt i ω); μ] =
      ((s ⊓ t : NNReal) : ℝ)
    rw [covariance_fun_sum_fun_sum hXs_mem hXt_mem]
    calc
      ∑ i : Fin n, ∑ j : Fin n, cov[Xs i, Xt j; μ]
          = ∑ i : Fin n, u i ^ (2 : ℕ) * ((s ⊓ t : NNReal) : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [Finset.sum_eq_single i]
              · simp [hcov_diag i]
              · intro j hj hij
                simp [hcov_offdiag i j hij.symm]
              · intro hi_not
                exact False.elim (hi_not (by simp))
      _ = (∑ i : Fin n, u i ^ (2 : ℕ)) * ((s ⊓ t : NNReal) : ℝ) := by
            rw [← Finset.sum_mul]
      _ = ((s ⊓ t : NNReal) : ℝ) := by
            rw [hnorm_sq, hu]
            ring
  · -- Almost-sure continuity is preserved under the finite linear combination of coordinates.
    have hcont_coords :
        ∀ᵐ ω ∂μ, ∀ i : Fin n, Continuous (fun t : NNReal ↦ W t ω (Fin.castSucc i)) := by
      refine ae_all_iff.2 ?_
      intro i
      simpa [HasAlmostSurelyContinuousPaths, processPath] using
        (show HasAlmostSurelyContinuousPaths μ (fun t ω ↦ W t ω (Fin.castSucc i)) from
          (show IsBrownianMotion μ (fun t ω ↦ W t ω (Fin.castSucc i)) from inferInstance).continuous_paths)
    filter_upwards [hcont_coords] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath, X, real_inner_comm,
      inner_upperHalfSpaceBoundaryProjection_eq_sum, mul_comm] using
      (continuous_finset_sum Finset.univ
        (fun i _ ↦ (hω i).const_mul (u i)))

/-- Helper for Exercise 25.4.2: the horizontal unit-direction projection process is independent of
the vertical Brownian coordinate process. -/
theorem unitDirectionHorizontalBrownian_indep_verticalBrownian
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    {u : Boundary} (hu : ‖u‖ = 1) :
    IndepFun
      (fun ω ↦ fun t : NNReal ↦ inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u)
      (fun ω ↦ fun t : NNReal ↦ W t ω (Fin.last n))
      μ := by
  let S : Finset (Fin (n + 1)) := Finset.univ.image Fin.castSucc
  let T : Finset (Fin (n + 1)) := {Fin.last n}
  have hST : Disjoint S T := by
    simp [S, T]
  have hcoord_meas :
      ∀ i : Fin (n + 1), AEMeasurable (fun ω ↦ fun t : NNReal ↦ W t ω i) μ := by
    intro i
    exact
      (IsBrownianMotionStartedAt.measurable_processPath
        (show IsBrownianMotionStartedAt μ (fun t ω ↦ W t ω i) 0 from inferInstance)).aemeasurable
  have hIndepTuple :
      IndepFun
        (fun ω (i : S) ↦ fun t : NNReal ↦ W t ω i)
        (fun ω (i : T) ↦ fun t : NNReal ↦ W t ω i)
        μ := by
    exact ProbabilityTheory.iIndepFun.indepFun_finset₀ S T hST hW.iIndepFun hcoord_meas
  let φ : ((i : S) → NNReal → ℝ) → NNReal → ℝ :=
    fun z t ↦ ∑ i : Fin n, u i * z ⟨Fin.castSucc i, by simp [S]⟩ t
  let ψ : ((i : T) → NNReal → ℝ) → NNReal → ℝ :=
    fun z t ↦ z ⟨Fin.last n, by simp [T]⟩ t
  have hφ_meas : Measurable φ := by
    dsimp [φ]
    fun_prop
  have hψ_meas : Measurable ψ := by
    dsimp [ψ]
    fun_prop
  -- Proof comment: separate the horizontal coordinate block from the last coordinate and then
  -- collapse the horizontal tuple by the linear functional determined by `u`.
  simpa [φ, ψ, T, real_inner_comm, inner_upperHalfSpaceBoundaryProjection_eq_sum, mul_comm] using
    hIndepTuple.comp (hφ := hφ_meas) (hψ := hψ_meas)

/-- Helper for Exercise 25.4.2: package two real coordinates as a planar Euclidean vector. -/
private def planarPair (a b : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![a, b]

/-- Helper for Exercise 25.4.2: packaging the unit-direction horizontal projection together with
the vertical coordinate yields a standard planar Brownian motion. -/
theorem unitDirectionPlanarBrownian_isStandardBrownianMotionVector
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    {u : Boundary} (hu : ‖u‖ = 1) :
    IsStandardBrownianMotionVector μ
      (fun t ω ↦
        planarPair
          (inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u)
          (W t ω (Fin.last n))) := by
  let V : NNReal → Ω → EuclideanSpace ℝ (Fin 2) :=
    fun t ω ↦
      planarPair
        (inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u)
        (W t ω (Fin.last n))
  refine
    { isBrownianMotion := ?_
      iIndepFun := ?_ }
  · -- Proof comment: the two planar coordinates are exactly the proved horizontal unit-direction
    -- Brownian motion and the original vertical coordinate Brownian motion.
    intro i
    fin_cases i
    · simpa [V, planarPair] using
        unitDirectionHorizontalBrownian_isBrownianMotion
          (μ := μ) (n := n) (W := W) hW hu
    · simpa [V, planarPair] using
        (show IsBrownianMotion μ (fun t ω ↦ W t ω (Fin.last n)) from inferInstance)
  · have hIndep :
        IndepFun
          (fun ω ↦ fun t : NNReal ↦ inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u)
          (fun ω ↦ fun t : NNReal ↦ W t ω (Fin.last n))
          μ :=
      unitDirectionHorizontalBrownian_indep_verticalBrownian
        (μ := μ) (n := n) (W := W) hW hu
    have hFirstBrownian :
        IsBrownianMotion μ
          (fun t ω ↦ inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u) :=
      unitDirectionHorizontalBrownian_isBrownianMotion
        (μ := μ) (n := n) (W := W) hW hu
    letI :
        IsBrownianMotion μ
          (fun t ω ↦ inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u) :=
      hFirstBrownian
    have hFirstAemeas :
        AEMeasurable
          (fun ω ↦ fun t : NNReal ↦ inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u)
          μ := by
      exact
        (IsBrownianMotionStartedAt.measurable_processPath
          (show IsBrownianMotionStartedAt μ
            (fun t ω ↦ inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u) 0 from
              inferInstance)).aemeasurable
    have hSecondAemeas :
        AEMeasurable (fun ω ↦ fun t : NNReal ↦ W t ω (Fin.last n)) μ := by
      exact
        (IsBrownianMotionStartedAt.measurable_processPath
          (show IsBrownianMotionStartedAt μ
            (fun t ω ↦ W t ω (Fin.last n)) 0 from inferInstance)).aemeasurable
    -- Proof comment: identify the `Fin 2`-valued path law with the product law via
    -- `MeasurableEquiv.piFinTwo`, then invoke the already proved pairwise independence.
    rw [iIndepFun_iff_map_fun_eq_pi_map]
    · let e : (Fin 2 → NNReal → ℝ) ≃ᵐ (NNReal → ℝ) × (NNReal → ℝ) :=
        MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ NNReal → ℝ)
      have hVaemeas :
          AEMeasurable
            (fun ω i t ↦
              (planarPair
                (inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u)
                (W t ω (Fin.last n))) i)
            μ := by
        exact
          aemeasurable_pi_lambda _ fun i : Fin 2 ↦ by
            fin_cases i
            · simpa [planarPair] using hFirstAemeas
            · simpa [planarPair] using hSecondAemeas
      have hpair :
          (fun ω ↦
            (fun t : NNReal ↦ inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u,
              fun t : NNReal ↦ W t ω (Fin.last n))) =
            (e ∘
              fun ω i t ↦
                (planarPair
                  (inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u)
                  (W t ω (Fin.last n))) i) := by
        funext ω
        ext t <;> simp [e, planarPair]
      rw [← e.map_measurableEquiv_injective.eq_iff]
      rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hVaemeas]
      rw [← hpair]
      rw [(indepFun_iff_map_prod_eq_prod_map_map hFirstAemeas hSecondAemeas).1 hIndep]
      simpa [e, V, planarPair] using
        (measurePreserving_piFinTwo (α := fun _ : Fin 2 ↦ NNReal → ℝ)
          (μ := fun i : Fin 2 ↦
            μ.map (fun ω ↦ fun t : NNReal ↦
              (planarPair
                (inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u)
                (W t ω (Fin.last n))) i))).map_eq.symm
    · intro i
      fin_cases i
      · simpa [V, planarPair] using hFirstAemeas
      · simpa [V, planarPair] using hSecondAemeas

/-- Helper for Exercise 25.4.2: the only remaining planar input is the stopped first-coordinate
Cauchy law in dimension `2`. This local placeholder keeps the higher-dimensional file compilable
while the planar proof frontier is repaired separately. -/
private theorem mapWithDensityOfVolumePreservingLocal {α β : Type*}
    [MeasureSpace α] [MeasureSpace β]
    (e : α ≃ᵐ β) (hpres : MeasurePreserving e volume volume)
    (g : α → ENNReal) (hg : Measurable g) :
    Measure.map e (volume.withDensity g) =
      volume.withDensity (fun y : β ↦ g (e.symm y)) := by
  -- Proof comment: compare both measures on measurable sets and move the density through the
  -- volume-preserving equivalence.
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ hs,
    withDensity_apply _ (e.measurable hs)]
  simpa using hpres.setLIntegral_comp_preimage hs (hg.comp e.symm.measurable)

/-- Helper for Exercise 25.4.2: shifting the centered Cauchy density by `x₀` produces the Cauchy
density with location parameter `x₀`. -/
private theorem cauchyPDF_centered_sub_right_local (x₀ : ℝ) (γ : ℝ≥0) :
    (fun y : ℝ ↦ cauchyPDF 0 γ (y - x₀)) = cauchyPDF x₀ γ := by
  -- Proof comment: after unfolding the density, both sides are the same rational function in
  -- `y - x₀`.
  funext y
  rw [cauchyPDF_def, cauchyPDF_def, cauchyPDFReal_def, cauchyPDFReal_def]
  congr 1
  ring_nf

/-- Helper for Exercise 25.4.2: translating the centered Cauchy law by `x₀` yields the Cauchy law
with location parameter `x₀`. -/
private theorem map_add_const_centeredCauchyMeasure_local (x₀ a : ℝ) (ha : 0 < a) :
    Measure.map (fun y : ℝ ↦ y + x₀) (cauchyMeasure 0 (Real.toNNReal a)) =
      cauchyMeasure x₀ (Real.toNNReal a) := by
  have hγ : Real.toNNReal a ≠ 0 := (Real.toNNReal_pos.mpr ha).ne'
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight x₀
  have hpres : MeasurePreserving e (volume : Measure ℝ) volume := by
    -- Proof comment: Lebesgue measure is translation invariant.
    refine ⟨e.measurable, ?_⟩
    simpa [e, MeasurableEquiv.addRight] using
      (map_add_right_eq_self (volume : Measure ℝ) x₀)
  rw [cauchyMeasure_of_scale_ne_zero 0 hγ, cauchyMeasure_of_scale_ne_zero x₀ hγ]
  calc
    Measure.map (fun y : ℝ ↦ y + x₀) (volume.withDensity (cauchyPDF 0 (Real.toNNReal a))) =
        Measure.map e (volume.withDensity (cauchyPDF 0 (Real.toNNReal a))) := by
          rfl
    _ = volume.withDensity (fun y : ℝ ↦ cauchyPDF 0 (Real.toNNReal a) (e.symm y)) := by
          exact
            mapWithDensityOfVolumePreservingLocal
              (e := e) (hpres := hpres) (g := cauchyPDF 0 (Real.toNNReal a))
              (hg := measurable_cauchyPDF 0 (Real.toNNReal a))
    _ = volume.withDensity (cauchyPDF x₀ (Real.toNNReal a)) := by
          congr 1
          funext y
          simpa [e, MeasurableEquiv.addRight] using
            congrFun (cauchyPDF_centered_sub_right_local x₀ (Real.toNNReal a)) y

/-- Helper for Exercise 25.4.2: local adapter that reuses the imported planar centered horizontal
exit law at the first exit time from `upperHalfSpace 1`. -/
theorem upperHalfPlaneExitHorizontal_eq_centeredCauchyMeasure_local
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin 2)}
    (hW : IsStandardBrownianMotionVector μ W) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ upperHalfSpace 1) :
    Measure.map
        (fun ω ↦
          W
            (hittingAfter (fun t ω ↦ x + W t ω) (upperHalfSpace 1)ᶜ (0 : NNReal) ω).untopA
            ω 0)
        μ =
      cauchyMeasure 0 (Real.toNNReal (x 1)) := by
  -- Route correction: the higher-dimensional comparison is now restored below, so the only
  -- remaining blocker is this centered planar exit law.
  -- Proof comment: reuse the earlier planar exit-law theorem from Exercise 25.4.1; this local
  -- theorem is only the adapter needed by the higher-dimensional half-space comparison below.
  simpa using
    upperHalfPlaneExitHorizontal_eq_centeredCauchyMeasure
      (μ := μ) (W := W) hW hx

theorem upperHalfPlaneStoppedFirstCoordinate_eq_cauchyMeasure_local
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin 2)}
    (hW : IsStandardBrownianMotionVector μ W) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ upperHalfSpace 1) :
    Measure.map
        (fun ω ↦
          stoppedValue
            (fun t ω ↦ x + W t ω)
            (hittingAfter (fun t ω ↦ x + W t ω) (upperHalfSpace 1)ᶜ (0 : NNReal))
            ω 0)
        μ =
      cauchyMeasure (x 0) (Real.toNNReal (x 1)) := by
  let τ : Ω → ENNReal := hittingAfter (fun t ω ↦ x + W t ω) (upperHalfSpace 1)ᶜ (0 : NNReal)
  have hx_second : 0 < x 1 := by
    simpa [upperHalfSpace] using hx
  have hcenteredAemeas :
      AEMeasurable (fun ω ↦ W (τ ω).untopA ω 0) μ := by
    -- Proof comment: the centered exit law is nonzero, so the underlying sampled coordinate must
    -- be measurable; otherwise `Measure.map` would collapse to `0`.
    by_contra hnot
    have hmap_zero : Measure.map (fun ω ↦ W (τ ω).untopA ω 0) μ = 0 := by
      simp [hnot]
    have hcauchy_ne_zero : cauchyMeasure 0 (Real.toNNReal (x 1)) ≠ 0 := by
      intro hzero
      have huniv : (cauchyMeasure 0 (Real.toNNReal (x 1)) : Measure ℝ) Set.univ = 0 := by
        simpa [hzero]
      simp at huniv
    exact
      hcauchy_ne_zero <|
        by
          simpa [τ] using
            (upperHalfPlaneExitHorizontal_eq_centeredCauchyMeasure_local
              (μ := μ) (W := W) hW hx).symm.trans hmap_zero
  have hstopped_eq :
      (fun ω ↦
        stoppedValue
          (fun t ω ↦ x + W t ω)
          τ ω 0) =
        (fun ω ↦ x 0 + W (τ ω).untopA ω 0) := by
    -- Proof comment: the first coordinate of the stopped translated path is the deterministic
    -- shift `x 0` plus the stopped horizontal Brownian coordinate.
    funext ω
    simp [τ, stoppedValue]
  calc
    Measure.map
        (fun ω ↦
          stoppedValue
            (fun t ω ↦ x + W t ω)
            τ ω 0)
        μ =
      Measure.map (fun ω ↦ x 0 + W (τ ω).untopA ω 0) μ := by
        exact Measure.map_congr <| Filter.Eventually.of_forall fun ω ↦ by
          simpa [hstopped_eq] using congrFun hstopped_eq ω
    _ =
      Measure.map (fun y : ℝ ↦ y + x 0)
        (Measure.map (fun ω ↦ W (τ ω).untopA ω 0) μ) := by
          rw [show (fun ω ↦ x 0 + W (τ ω).untopA ω 0) =
              (fun y : ℝ ↦ y + x 0) ∘ (fun ω ↦ W (τ ω).untopA ω 0) by
                funext ω
                simp [Function.comp, add_comm]]
          exact
            (AEMeasurable.map_map_of_aemeasurable
              (μ := μ) (f := fun ω ↦ W (τ ω).untopA ω 0)
              (g := fun y : ℝ ↦ y + x 0) (by fun_prop) hcenteredAemeas).symm
    _ = Measure.map (fun y : ℝ ↦ y + x 0) (cauchyMeasure 0 (Real.toNNReal (x 1))) := by
          rw [upperHalfPlaneExitHorizontal_eq_centeredCauchyMeasure_local
            (μ := μ) (W := W) hW hx]
    _ = cauchyMeasure (x 0) (Real.toNNReal (x 1)) := by
          simpa [add_comm] using
            map_add_const_centeredCauchyMeasure_local (x 0) (x 1) hx_second

/-- Helper for Exercise 25.4.2: the unit-direction projection of the transported harmonic measure
is the planar Cauchy law. -/
theorem map_unitDirection_upperHalfSpaceHarmonicMeasure_eq_cauchyMeasure
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfSpace n)
    (hExitMeas : Measurable (upperHalfSpaceExitValue n W x))
    {u : Boundary} (hu : ‖u‖ = 1) :
    Measure.map (fun y ↦ inner ℝ y u)
      (upperHalfSpaceBoundaryHarmonicMeasure (μ := μ) (n := n) W x hx hExitMeas) =
        cauchyMeasure (inner ℝ (upperHalfSpaceBoundaryProjection n x) u)
          (Real.toNNReal (x (Fin.last n))) := by
  have hExitProj :
      Measure.map (fun y ↦ inner ℝ y u)
        (upperHalfSpaceBoundaryHarmonicMeasure (μ := μ) (n := n) W x hx hExitMeas) =
          Measure.map (fun ω ↦ inner ℝ (upperHalfSpaceExitLocation n W x ω) u) μ := by
    simpa using
      map_inner_upperHalfSpaceBoundaryHarmonicMeasure_eq_map_exitProjection
        (μ := μ) (n := n) (W := W) hx hExitMeas u
  -- Route correction: the remaining Brownian blocker is now isolated at unit directions, where
  -- the intended proof packages the horizontal projection and the vertical coordinate into a
  -- planar Brownian motion and invokes the planar stopped-coordinate law from Exercise 25.4.1.
  have hx_last : 0 < x (Fin.last n) := by
    simpa [upperHalfSpace] using hx
  let xPlane : EuclideanSpace ℝ (Fin 2) :=
    planarPair (inner ℝ (upperHalfSpaceBoundaryProjection n x) u) (x (Fin.last n))
  let WPlane : NNReal → Ω → EuclideanSpace ℝ (Fin 2) :=
    fun t ω ↦
      planarPair
        (inner ℝ (upperHalfSpaceBoundaryProjection n (W t ω)) u)
        (W t ω (Fin.last n))
  have hxPlane : xPlane ∈ upperHalfSpace 1 := by
    -- Proof comment: the planar reduction preserves the positive vertical coordinate.
    simp [xPlane, planarPair, upperHalfSpace, hx_last]
  have hWPlane : IsStandardBrownianMotionVector μ WPlane :=
    unitDirectionPlanarBrownian_isStandardBrownianMotionVector
      (μ := μ) (n := n) (W := W) hW hu
  have hExitTime_eq :
      hittingAfter (fun t ω ↦ xPlane + WPlane t ω) (upperHalfSpace 1)ᶜ (0 : NNReal) =
        upperHalfSpaceExitTime n W x := by
    -- Proof comment: both hitting times are determined by the same vertical coordinate process.
    funext ω
    have hmem_eq :
        ∀ t : NNReal,
          xPlane + WPlane t ω ∈ (upperHalfSpace 1)ᶜ ↔
            x + W t ω ∈ (upperHalfSpace n)ᶜ := by
      intro t
      simp [xPlane, WPlane, planarPair, upperHalfSpace]
    have hExists :
        (∃ j : NNReal, (0 : NNReal) ≤ j ∧ xPlane + WPlane j ω ∈ (upperHalfSpace 1)ᶜ) ↔
          ∃ j : NNReal, (0 : NNReal) ≤ j ∧ x + W j ω ∈ (upperHalfSpace n)ᶜ := by
      constructor
      · rintro ⟨j, hj0, hj⟩
        exact ⟨j, hj0, (hmem_eq j).1 hj⟩
      · rintro ⟨j, hj0, hj⟩
        exact ⟨j, hj0, (hmem_eq j).2 hj⟩
    have hSet :
        {j : NNReal | (0 : NNReal) ≤ j ∧ xPlane + WPlane j ω ∈ (upperHalfSpace 1)ᶜ} =
          {j : NNReal | (0 : NNReal) ≤ j ∧ x + W j ω ∈ (upperHalfSpace n)ᶜ} := by
      ext j
      simp [xPlane, WPlane, planarPair, upperHalfSpace]
    rw [upperHalfSpaceExitTime, hittingAfter_def, hittingAfter_def]
    classical
    change
      (if ∃ j : NNReal, (0 : NNReal) ≤ j ∧ xPlane + WPlane j ω ∈ (upperHalfSpace 1)ᶜ then
          ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ xPlane + WPlane i ω ∈ (upperHalfSpace 1)ᶜ} :
            NNReal) : ENNReal)
        else ⊤) =
        (if ∃ j : NNReal, (0 : NNReal) ≤ j ∧ x + W j ω ∈ (upperHalfSpace n)ᶜ then
          ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ x + W i ω ∈ (upperHalfSpace n)ᶜ} :
            NNReal) : ENNReal)
        else ⊤)
    by_cases h :
        ∃ j : NNReal, (0 : NNReal) ≤ j ∧ xPlane + WPlane j ω ∈ (upperHalfSpace 1)ᶜ
    · have h' : ∃ j : NNReal, (0 : NNReal) ≤ j ∧ x + W j ω ∈ (upperHalfSpace n)ᶜ :=
        hExists.mp h
      rw [if_pos h, if_pos h']
      simpa using congrArg (fun s : Set NNReal ↦ ((sInf s : NNReal) : ENNReal)) hSet
    · have h' : ¬ ∃ j : NNReal, (0 : NNReal) ≤ j ∧ x + W j ω ∈ (upperHalfSpace n)ᶜ :=
        mt hExists.mpr h
      rw [if_neg h, if_neg h']
  have hStopped_first :
      (fun ω ↦ inner ℝ (upperHalfSpaceExitLocation n W x ω) u) =
        (fun ω ↦
          stoppedValue
            (fun t ω ↦ xPlane + WPlane t ω)
            (hittingAfter (fun t ω ↦ xPlane + WPlane t ω) (upperHalfSpace 1)ᶜ (0 : NNReal))
            ω 0) := by
    -- Proof comment: after identifying the common hitting time, both observables are exactly the
    -- same stopped horizontal scalar projection.
    funext ω
    rw [hExitTime_eq]
    let τ : NNReal := (upperHalfSpaceExitTime n W x ω).untopA
    calc
      ∑ i : Fin n, u i * (x + W τ ω) (Fin.castSucc i)
          = ∑ i : Fin n, u i * x (Fin.castSucc i) +
              ∑ i : Fin n, u i * W τ ω (Fin.castSucc i) := by
                simp [Finset.sum_add_distrib, mul_add]
      _ = inner ℝ (upperHalfSpaceBoundaryProjection n x) u +
            inner ℝ (upperHalfSpaceBoundaryProjection n (W τ ω)) u := by
              rw [real_inner_comm, inner_upperHalfSpaceBoundaryProjection_eq_sum,
                real_inner_comm, inner_upperHalfSpaceBoundaryProjection_eq_sum]
    <;> simp [τ, xPlane, WPlane, planarPair, stoppedValue,
      inner_upperHalfSpaceExitLocation_eq_stoppedValue_sum]
  calc
    Measure.map (fun y ↦ inner ℝ y u)
        (upperHalfSpaceBoundaryHarmonicMeasure (μ := μ) (n := n) W x hx hExitMeas) =
      Measure.map
        (fun ω ↦
          stoppedValue
            (fun t ω ↦ xPlane + WPlane t ω)
            (hittingAfter (fun t ω ↦ xPlane + WPlane t ω) (upperHalfSpace 1)ᶜ (0 : NNReal))
            ω 0)
        μ := by
          rw [hExitProj, hStopped_first]
    _ = cauchyMeasure (xPlane 0) (Real.toNNReal (xPlane 1)) := by
        exact upperHalfPlaneStoppedFirstCoordinate_eq_cauchyMeasure_local
          (μ := μ) (W := WPlane) hWPlane hxPlane
    _ = cauchyMeasure (inner ℝ (upperHalfSpaceBoundaryProjection n x) u)
          (Real.toNNReal (x (Fin.last n))) := by
          simp [xPlane, planarPair]

/-- Helper for Exercise 25.4.2: rotate only the boundary coordinates of the starting point `x`
through the orthonormal basis representation `b.repr`, while keeping the vertical coordinate
fixed. -/
def rotatedUpperHalfSpaceStart
    (b : OrthonormalBasis (Fin n) ℝ Boundary) (x : State) : State :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm <|
    Fin.snoc (fun i : Fin n ↦ b.repr (upperHalfSpaceBoundaryProjection n x) i) (x (Fin.last n))

/-- Helper for Exercise 25.4.2: the rotated start point has the rotated boundary projection. -/
theorem upperHalfSpaceBoundaryProjection_rotatedUpperHalfSpaceStart
    (b : OrthonormalBasis (Fin n) ℝ Boundary) (x : State) :
    upperHalfSpaceBoundaryProjection n (rotatedUpperHalfSpaceStart (n := n) b x) =
      b.repr (upperHalfSpaceBoundaryProjection n x) := by
  -- Proof comment: `rotatedUpperHalfSpaceStart` was defined by inserting the rotated horizontal
  -- coordinates into the first `n` slots, so the boundary projection reads them back unchanged.
  ext i
  simp [rotatedUpperHalfSpaceStart, upperHalfSpaceBoundaryProjection]

/-- Helper for Exercise 25.4.2: the rotated start point preserves the vertical coordinate. -/
theorem rotatedUpperHalfSpaceStart_last
    (b : OrthonormalBasis (Fin n) ℝ Boundary) (x : State) :
    rotatedUpperHalfSpaceStart (n := n) b x (Fin.last n) = x (Fin.last n) := by
  -- Proof comment: the last coordinate is the `Fin.snoc` tail inserted in the definition.
  simp [rotatedUpperHalfSpaceStart]

/-- Helper for Exercise 25.4.2: rotating only the boundary coordinates keeps the start point in
`upperHalfSpace n`. -/
theorem rotatedUpperHalfSpaceStart_mem_upperHalfSpace
    (b : OrthonormalBasis (Fin n) ℝ Boundary) {x : State} (hx : x ∈ upperHalfSpace n) :
    rotatedUpperHalfSpaceStart (n := n) b x ∈ upperHalfSpace n := by
  -- Proof comment: the defining inequality for `upperHalfSpace n` depends only on the unchanged
  -- vertical coordinate.
  simpa [upperHalfSpace, rotatedUpperHalfSpaceStart_last] using hx

/-- Helper for Exercise 25.4.2: after rewriting through an orthonormal basis representation, the
projection `y ↦ ⟪y, u⟫` becomes the first coordinate. -/
theorem map_inner_eq_map_firstCoordinate_repr
    (b : OrthonormalBasis (Fin n) ℝ Boundary) (i0 : Fin n) {u : Boundary} (hb0 : b i0 = u)
    (ν : Measure Boundary) :
    Measure.map (fun y ↦ inner ℝ y u) ν =
      Measure.map (fun z : Boundary ↦ z i0) (Measure.map b.repr ν) := by
  -- Proof comment: the zeroth coordinate of `b.repr y` is `⟪b 0, y⟫`, so the statement is just
  -- functoriality of `Measure.map`.
  have hproj :
      (fun y : Boundary ↦ inner ℝ y u) = (fun z : Boundary ↦ z i0) ∘ b.repr := by
    funext y
    simp [OrthonormalBasis.repr_apply_apply, hb0, real_inner_comm]
  rw [hproj, Measure.map_map]
  all_goals
    fun_prop

/-- Helper for Exercise 25.4.2: the Poisson kernel is invariant under rotating the boundary
variables and the horizontal starting point by the same orthonormal change of coordinates. -/
theorem upperHalfSpacePoissonKernel_repr_symm
    (b : OrthonormalBasis (Fin n) ℝ Boundary) (x : State) (z : Boundary) :
    upperHalfSpacePoissonKernel n x (b.repr.symm z) =
      upperHalfSpacePoissonKernel n (rotatedUpperHalfSpaceStart (n := n) b x) z := by
  -- Proof comment: orthonormal basis representations preserve distances on the boundary, and the
  -- vertical coordinate of the start point is unchanged by the rotation.
  have hdist :
      dist (upperHalfSpaceBoundaryProjection n x) (b.repr.symm z) =
        dist (b.repr (upperHalfSpaceBoundaryProjection n x)) z := by
    simpa using (b.repr.symm.isometry.dist_eq (b.repr (upperHalfSpaceBoundaryProjection n x)) z)
  simp [upperHalfSpacePoissonKernel, upperHalfSpaceBoundaryDistanceSq,
    upperHalfSpaceBoundaryProjection_rotatedUpperHalfSpaceStart, rotatedUpperHalfSpaceStart_last,
    hdist]

/-- Helper for Exercise 25.4.2: transporting the explicit Poisson-kernel measure by
`b.repr : Boundary ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)` only rotates the horizontal start point. -/
theorem map_repr_upperHalfSpacePoissonKernelMeasure_eq
    (b : OrthonormalBasis (Fin n) ℝ Boundary) (x : State) :
    Measure.map b.repr (upperHalfSpacePoissonKernelMeasure (n := n) x) =
      upperHalfSpacePoissonKernelMeasure (n := n) (rotatedUpperHalfSpaceStart (n := n) b x) := by
  -- Proof comment: transport the density through the measure-preserving equivalence `b.repr` and
  -- then identify the transformed kernel pointwise with the rotated-start kernel.
  let e : Boundary ≃ᵐ EuclideanSpace ℝ (Fin n) := b.repr.toMeasurableEquiv
  ext s hs
  have hpreimage :
      b.repr.symm '' s = b.repr ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp [hz]
    · intro hy
      refine ⟨b.repr y, ?_, by simp⟩
      simpa using hy
  have hrepr_meas : Measurable b.repr := e.measurable
  have hsymm_emb : MeasurableEmbedding b.repr.symm := e.symm.measurableEmbedding
  rw [upperHalfSpacePoissonKernelMeasure, upperHalfSpacePoissonKernelMeasure,
    Measure.map_apply hrepr_meas hs,
    withDensity_apply _ (hs.preimage hrepr_meas), withDensity_apply _ hs, ← hpreimage]
  rw [← (OrthonormalBasis.measurePreserving_repr_symm b).setLIntegral_comp_emb
    hsymm_emb
    (fun y : Boundary ↦ ENNReal.ofReal (upperHalfSpacePoissonKernel n x y)) s]
  refine setLIntegral_congr_fun hs ?_
  intro z hz
  simp [upperHalfSpacePoissonKernel_repr_symm]

/-- Helper for Exercise 25.4.2: a volume-preserving measurable equivalence transports a
`withDensity` measure by precomposing the density with the inverse equivalence. -/
private theorem mapWithDensityOfVolumePreserving {α β : Type*}
    [MeasureSpace α] [MeasureSpace β]
    (e : α ≃ᵐ β) (hpres : MeasurePreserving e volume volume)
    (g : α → ENNReal) (hg : Measurable g) :
    Measure.map e (volume.withDensity g) =
      volume.withDensity (fun y : β ↦ g (e.symm y)) := by
  refine Measure.ext fun s hs ↦ ?_
  -- Proof comment: evaluate both measures on the same measurable set and move the density
  -- through the volume-preserving equivalence once.
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ hs,
    withDensity_apply _ (e.measurable hs)]
  simpa using hpres.setLIntegral_comp_preimage hs (hg.comp e.symm.measurable)

/-- Helper for Exercise 25.4.2: split the first coordinate off a finite-dimensional Euclidean
space as a measurable equivalence. -/
private def euclideanPiFinSuccAbove (m : ℕ) :
    EuclideanSpace ℝ (Fin (m + 1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin m) :=
  (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm.trans <|
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).trans <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin m → ℝ))

/-- Helper for Exercise 25.4.2: the inverse head-tail equivalence recovers the head coordinate in
the zeroth slot. -/
private theorem euclideanPiFinSuccAbove_symm_zero
    (m : ℕ) (s : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    ((euclideanPiFinSuccAbove m).symm (s, z)) 0 = s := by
  rfl

/-- Helper for Exercise 25.4.2: the inverse head-tail equivalence recovers the tail coordinates in
the successor slots. -/
private theorem euclideanPiFinSuccAbove_symm_succ
    (m : ℕ) (s : ℝ) (z : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    ((euclideanPiFinSuccAbove m).symm (s, z)) (Fin.succ i) = z i := by
  rfl

/-- Helper for Exercise 25.4.2: the head-tail Euclidean coordinate split preserves volume. -/
private theorem measurePreserving_euclideanPiFinSuccAbove (m : ℕ) :
    MeasurePreserving (euclideanPiFinSuccAbove m) volume volume := by
  unfold euclideanPiFinSuccAbove
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (m + 1))).trans ?_
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).trans ?_
  simpa [Measure.volume_eq_prod] using
    (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin m))

/-- Helper for Exercise 25.4.2: transporting the boundary law through `piFinSuccAbove` rewrites
the Poisson-kernel measure as a product-space `withDensity`. -/
private theorem mapPiFinSuccAbove_upperHalfSpacePoissonKernelMeasure_eq
    {m : ℕ} (x : EuclideanSpace ℝ (Fin ((m + 1) + 1))) :
    Measure.map (euclideanPiFinSuccAbove m)
      (upperHalfSpacePoissonKernelMeasure (n := m + 1) x) =
        (((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))).withDensity
          (fun p ↦ ENNReal.ofReal (upperHalfSpacePoissonKernel (m + 1) x
            ((euclideanPiFinSuccAbove m).symm p)))) := by
  have hkernelMeas :
      Measurable
        (fun y : EuclideanSpace ℝ (Fin (m + 1)) ↦
          ENNReal.ofReal (upperHalfSpacePoissonKernel (m + 1) x y)) := by
    have hmeas :
        Measurable (fun y : EuclideanSpace ℝ (Fin (m + 1)) ↦
          upperHalfSpacePoissonKernel (m + 1) x y) := by
      dsimp [upperHalfSpacePoissonKernel, upperHalfSpaceBoundaryDistanceSq]
      fun_prop
    exact hmeas.ennreal_ofReal
  -- Proof comment: freeze the `piFinSuccAbove` transport once so the remaining proof can stay in
  -- product coordinates.
  simpa [upperHalfSpacePoissonKernelMeasure, Measure.volume_eq_prod] using
    mapWithDensityOfVolumePreserving
      (e := euclideanPiFinSuccAbove m)
      (hpres := measurePreserving_euclideanPiFinSuccAbove m)
      (g := fun y : EuclideanSpace ℝ (Fin (m + 1)) ↦
        ENNReal.ofReal (upperHalfSpacePoissonKernel (m + 1) x y))
      hkernelMeas

/-- Helper for Exercise 25.4.2: pushing a product-space density forward along `Prod.fst`
integrates out the tail coordinates. -/
private theorem mapFstWithDensityEqWithDensityFiberIntegral {m : ℕ}
    {f : ℝ × EuclideanSpace ℝ (Fin m) → ENNReal} (hf : Measurable f) :
    Measure.map Prod.fst
        ((((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))).withDensity
          f)) =
      (volume : Measure ℝ).withDensity
        (fun s ↦ ∫⁻ z, f (s, z) ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
  refine Measure.ext fun s hs ↦ ?_
  let g : ℝ × EuclideanSpace ℝ (Fin m) → ENNReal := Set.indicator (Prod.fst ⁻¹' s) f
  have hg : Measurable g := hf.indicator (hs.preimage measurable_fst)
  have hinner :
      (fun x ↦ ∫⁻ y, g (x, y) ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))) =
        Set.indicator s
          (fun x ↦ ∫⁻ y, f (x, y) ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
    -- Proof comment: once the first coordinate is fixed, the indicator either keeps the whole
    -- fiber or kills it completely.
    funext x
    by_cases hx : x ∈ s
    · simp [g, hx]
    · simp [g, hx]
  -- Proof comment: rewrite the preimage `Prod.fst ⁻¹' s` and apply Tonelli on the product
  -- Lebesgue measure.
  calc
    Measure.map Prod.fst
        ((((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))).withDensity
          f)) s
        = ((((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))).withDensity
            f)) (Prod.fst ⁻¹' s) := by
              rw [Measure.map_apply measurable_fst hs]
    _ = ∫⁻ z in Prod.fst ⁻¹' s, f z
          ∂(((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m))))) := by
          rw [withDensity_apply _ (hs.preimage measurable_fst)]
    _ = ∫⁻ z, g z
          ∂(((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m))))) := by
          rw [lintegral_indicator (hs.preimage measurable_fst)]
    _ = ∫⁻ x, ∫⁻ y, g (x, y) ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))
          ∂(volume : Measure ℝ) := by
          rw [lintegral_prod _ hg.aemeasurable]
    _ = ∫⁻ x, Set.indicator s
          (fun x ↦ ∫⁻ y, f (x, y) ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))) x
          ∂(volume : Measure ℝ) := by
          simpa [hinner]
    _ = ∫⁻ x in s, ∫⁻ y, f (x, y) ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))
          ∂(volume : Measure ℝ) := by
          rw [lintegral_indicator hs]
    _ = (volume : Measure ℝ).withDensity
          (fun x ↦ ∫⁻ y, f (x, y) ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))) s := by
          rw [withDensity_apply _ hs]

/-- Helper for Exercise 25.4.2: after the `piFinSuccAbove` split, the first-coordinate marginal
of the Poisson-kernel measure is a one-dimensional `withDensity` whose density is the tail fiber
integral. -/
private theorem firstCoordinate_upperHalfSpacePoissonKernelMeasure_eq_withDensityFiberIntegral
    {m : ℕ} (x : EuclideanSpace ℝ (Fin ((m + 1) + 1))) :
    Measure.map (fun y : EuclideanSpace ℝ (Fin (m + 1)) ↦ y 0)
      (upperHalfSpacePoissonKernelMeasure (n := m + 1) x) =
        (volume : Measure ℝ).withDensity
          (fun s ↦ ∫⁻ z,
            ENNReal.ofReal (upperHalfSpacePoissonKernel (m + 1) x
              ((euclideanPiFinSuccAbove m).symm (s, z)))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
  have hf :
      Measurable
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) ↦
          ENNReal.ofReal (upperHalfSpacePoissonKernel (m + 1) x
            ((euclideanPiFinSuccAbove m).symm p))) := by
    have hkernelMeas :
        Measurable
          (fun y : EuclideanSpace ℝ (Fin (m + 1)) ↦
            ENNReal.ofReal (upperHalfSpacePoissonKernel (m + 1) x y)) := by
      dsimp [upperHalfSpacePoissonKernel, upperHalfSpaceBoundaryDistanceSq]
      fun_prop
    exact hkernelMeas.comp (euclideanPiFinSuccAbove m).symm.measurable
  -- Proof comment: first transport the full measure into head-tail coordinates, then extract the
  -- first marginal by a generic `Prod.fst`-integration lemma.
  have hfst :
      Prod.fst ∘ euclideanPiFinSuccAbove m =
        (fun y : EuclideanSpace ℝ (Fin (m + 1)) ↦ y 0) := by
    funext y
    rfl
  calc
    Measure.map (fun y : EuclideanSpace ℝ (Fin (m + 1)) ↦ y 0)
        (upperHalfSpacePoissonKernelMeasure (n := m + 1) x)
        = Measure.map Prod.fst
            (Measure.map (euclideanPiFinSuccAbove m)
              (upperHalfSpacePoissonKernelMeasure (n := m + 1) x)) := by
              rw [Measure.map_map]
              · simpa [hfst]
              · fun_prop
              · fun_prop
    _ = (volume : Measure ℝ).withDensity
          (fun s ↦ ∫⁻ z,
            ENNReal.ofReal (upperHalfSpacePoissonKernel (m + 1) x
              ((euclideanPiFinSuccAbove m).symm (s, z)))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
          rw [mapPiFinSuccAbove_upperHalfSpacePoissonKernelMeasure_eq (m := m) x]
          exact mapFstWithDensityEqWithDensityFiberIntegral hf

  /-- Helper for Exercise 25.4.2: after the `piFinSuccAbove` split, the Poisson kernel separates
  the first boundary coordinate from the shifted tail norm. -/
private theorem poissonKernelFiberIntegrand_eq_shiftedNorm
    {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 3))) (s : ℝ)
    (z : EuclideanSpace ℝ (Fin (k + 1))) :
    upperHalfSpacePoissonKernel (k + 2) x
      ((euclideanPiFinSuccAbove (k + 1)).symm (s, z)) =
        Real.Gamma (((k + 3 : ℕ) : ℝ) / 2) /
            Real.pi ^ (((k + 3 : ℕ) : ℝ) / 2) *
          x (Fin.last (k + 2)) /
            (((s - (upperHalfSpaceBoundaryProjection (k + 2) x) 0) ^ (2 : ℕ) +
                ‖z -
                    WithLp.toLp 2
                      (fun i : Fin (k + 1) ↦
                        (upperHalfSpaceBoundaryProjection (k + 2) x) (Fin.succ i))‖ ^ (2 : ℕ) +
                x (Fin.last (k + 2)) ^ (2 : ℕ)) ^
              (((k + 3 : ℕ) : ℝ) / 2)) := by
  let c : EuclideanSpace ℝ (Fin (k + 1)) :=
    WithLp.toLp 2 fun i ↦ (upperHalfSpaceBoundaryProjection (k + 2) x) (Fin.succ i)
  have hhead :
      ((upperHalfSpaceBoundaryProjection (k + 2) x) 0 - s) ^ (2 : ℕ) =
        (s - (upperHalfSpaceBoundaryProjection (k + 2) x) 0) ^ (2 : ℕ) := by
    -- Proof comment: the first-coordinate contribution is a square, so reversing the subtraction
    -- order does not change the value.
    ring
  have htail :
      (∑ i : Fin (k + 1),
          ((upperHalfSpaceBoundaryProjection (k + 2) x) (Fin.succ i) - z i) ^ (2 : ℕ)) =
        ‖z - c‖ ^ (2 : ℕ) := by
    -- Proof comment: the tail coordinates are exactly the Euclidean norm square of the shifted
    -- tail vector.
    calc
      (∑ i : Fin (k + 1),
          ((upperHalfSpaceBoundaryProjection (k + 2) x) (Fin.succ i) - z i) ^ (2 : ℕ))
          = ‖c - z‖ ^ (2 : ℕ) := by
              simpa [c] using (EuclideanSpace.real_norm_sq_eq (c - z)).symm
      _ = ‖z - c‖ ^ (2 : ℕ) := by
            rw [norm_sub_rev]
  -- Proof comment: expand the boundary distance in head-tail coordinates, then identify the tail
  -- sum with the shifted Euclidean norm.
  rw [upperHalfSpacePoissonKernel, upperHalfSpaceBoundaryDistanceSq, dist_eq_norm,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  have hhead' :
      (upperHalfSpaceBoundaryProjection (k + 2) x -
          ((euclideanPiFinSuccAbove (k + 1)).symm (s, z))) 0 ^ (2 : ℕ) =
        (s - (upperHalfSpaceBoundaryProjection (k + 2) x) 0) ^ (2 : ℕ) := by
    change
      (((upperHalfSpaceBoundaryProjection (k + 2) x) 0 -
          ((euclideanPiFinSuccAbove (k + 1)).symm (s, z)) 0) ^ (2 : ℕ)) =
        (s - (upperHalfSpaceBoundaryProjection (k + 2) x) 0) ^ (2 : ℕ)
    rw [euclideanPiFinSuccAbove_symm_zero]
    simpa using hhead
  have htail' :
      (∑ i : Fin (k + 1),
          (upperHalfSpaceBoundaryProjection (k + 2) x -
              ((euclideanPiFinSuccAbove (k + 1)).symm (s, z))) (Fin.succ i) ^ (2 : ℕ)) =
        ‖z - c‖ ^ (2 : ℕ) := by
    change
      (∑ i : Fin (k + 1),
        (((upperHalfSpaceBoundaryProjection (k + 2) x) (Fin.succ i) -
            ((euclideanPiFinSuccAbove (k + 1)).symm (s, z)) (Fin.succ i)) ^ (2 : ℕ))) =
        ‖z - c‖ ^ (2 : ℕ)
    simpa [euclideanPiFinSuccAbove_symm_succ] using htail
  rw [hhead', htail']

/-- Helper for Exercise 25.4.2: translating the tail variable centers the positive-tail fiber
integral without changing its value. -/
private theorem tailFiberIntegral_eq_centeredTailIntegral
    {k : ℕ} (C A : ℝ) (c : EuclideanSpace ℝ (Fin (k + 1))) :
    ∫⁻ z, ENNReal.ofReal
        (C / (A + ‖z - c‖ ^ (2 : ℕ)) ^ ((((k + 3 : ℕ) : ℝ) / 2)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) =
      ∫⁻ z, ENNReal.ofReal
        (C / (A + ‖z‖ ^ (2 : ℕ)) ^ ((((k + 3 : ℕ) : ℝ) / 2)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
  have hmap :
      Measure.map (fun z : EuclideanSpace ℝ (Fin (k + 1)) ↦ z + c)
          (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) =
        (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
    simpa using
      (map_add_right_eq_self (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) c)
  have hf :
      Measurable
        (fun z : EuclideanSpace ℝ (Fin (k + 1)) ↦
          ENNReal.ofReal (C / (A + ‖z - c‖ ^ (2 : ℕ)) ^ ((((k + 3 : ℕ) : ℝ) / 2)))) := by
    fun_prop
  -- Proof comment: rewrite the original integral against the translated volume measure and then
  -- simplify the shifted norm after one change of variables.
  calc
    ∫⁻ z, ENNReal.ofReal
        (C / (A + ‖z - c‖ ^ (2 : ℕ)) ^ ((((k + 3 : ℕ) : ℝ) / 2)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))
        =
      ∫⁻ z, ENNReal.ofReal
        (C / (A + ‖z - c‖ ^ (2 : ℕ)) ^ ((((k + 3 : ℕ) : ℝ) / 2)))
        ∂(Measure.map (fun z : EuclideanSpace ℝ (Fin (k + 1)) ↦ z + c) volume) := by
          rw [hmap]
    _ =
      ∫⁻ z, ENNReal.ofReal
        (C / (A + ‖(z + c) - c‖ ^ (2 : ℕ)) ^ ((((k + 3 : ℕ) : ℝ) / 2)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
          rw [MeasureTheory.lintegral_map hf]
          fun_prop
    _ =
      ∫⁻ z, ENNReal.ofReal
        (C / (A + ‖z‖ ^ (2 : ℕ)) ^ ((((k + 3 : ℕ) : ℝ) / 2)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
          congr with z
          simp

/-- Helper for Exercise 25.4.2: after centering the tail fiber, a single homothety removes the
remaining parameter `A` from the Euclidean integral. -/
private theorem centeredTailIntegral_eq_ofReal_mul_unitTailIntegral
    {k : ℕ} {C A : ℝ} (hA : 0 < A) (hC : 0 ≤ C) :
    ∫⁻ z, ENNReal.ofReal
        (C / (A + ‖z‖ ^ (2 : ℕ)) ^ ((((k + 3 : ℕ) : ℝ) / 2)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) =
      ENNReal.ofReal
        ((C / A) *
          ∫ z : EuclideanSpace ℝ (Fin (k + 1)),
            ((1 : ℝ) + ‖z‖ ^ (2 : ℕ)) ^ (-((((k + 3 : ℕ) : ℝ) / 2)))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))) := by
  let p : ℝ := (((k + 3 : ℕ) : ℝ) / 2)
  let unitTail : EuclideanSpace ℝ (Fin (k + 1)) → ℝ :=
    fun z ↦ ((1 : ℝ) + ‖z‖ ^ (2 : ℕ)) ^ (-p)
  let scaledTail : EuclideanSpace ℝ (Fin (k + 1)) → ℝ :=
    fun z ↦ (C / A ^ p) * unitTail ((Real.sqrt A)⁻¹ • z)
  have hsqrt_pos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hsqrt_ne : Real.sqrt A ≠ 0 := hsqrt_pos.ne'
  have hApow_ne : A ^ p ≠ 0 := by
    exact (Real.rpow_pos_of_pos hA p).ne'
  have hscaled_eq :
      (fun z : EuclideanSpace ℝ (Fin (k + 1)) ↦
        C / (A + ‖z‖ ^ (2 : ℕ)) ^ p) = scaledTail := by
    -- Proof comment: factor the denominator as `A * (1 + ‖(√A)⁻¹ • z‖²)` so that the
    -- `A`-dependence moves entirely into a constant coefficient.
    funext z
    have hnorm :
        A * ‖(Real.sqrt A)⁻¹ • z‖ ^ (2 : ℕ) = ‖z‖ ^ (2 : ℕ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt_pos), pow_two]
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt hA.le]
    have hbase_pos : 0 < (1 : ℝ) + ‖(Real.sqrt A)⁻¹ • z‖ ^ (2 : ℕ) := by
      positivity
    have hbase_pow_ne : ((1 : ℝ) + ‖(Real.sqrt A)⁻¹ • z‖ ^ (2 : ℕ)) ^ p ≠ 0 := by
      exact (Real.rpow_pos_of_pos hbase_pos p).ne'
    have hfactor :
        A + ‖z‖ ^ (2 : ℕ) = A * ((1 : ℝ) + ‖(Real.sqrt A)⁻¹ • z‖ ^ (2 : ℕ)) := by
      rw [← hnorm]
      ring
    calc
      C / (A + ‖z‖ ^ (2 : ℕ)) ^ p
          = C / (A ^ p * (((1 : ℝ) + ‖(Real.sqrt A)⁻¹ • z‖ ^ (2 : ℕ)) ^ p)) := by
              rw [hfactor, Real.mul_rpow hA.le hbase_pos.le]
      _ = (C / A ^ p) * (((1 : ℝ) + ‖(Real.sqrt A)⁻¹ • z‖ ^ (2 : ℕ)) ^ p)⁻¹ := by
            field_simp [hApow_ne, hbase_pow_ne]
      _ = (C / A ^ p) * (((1 : ℝ) + ‖(Real.sqrt A)⁻¹ • z‖ ^ (2 : ℕ)) ^ (-p)) := by
            rw [← Real.rpow_neg hbase_pos.le]
      _ = scaledTail z := rfl
  have hunitTail_int :
      Integrable unitTail (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
    -- Proof comment: the universal unit-tail kernel is exactly the standard integrable
    -- `((1 + ‖z‖²)^(-r/2))` profile on Euclidean space.
    convert
      (integrable_rpow_neg_one_add_norm_sq
        (E := EuclideanSpace ℝ (Fin (k + 1)))
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))))
        (r := ((k + 3 : ℕ) : ℝ))
        (by
          norm_num [finrank_euclideanSpace])) using 1
    ext z
    simp [unitTail, p]
    ring
  have hscaled_int :
      Integrable scaledTail (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
    -- Proof comment: scaling by `√A` preserves integrability for additive Haar measure, so
    -- only the constant prefactor remains.
    exact
      (hunitTail_int.comp_smul (μ := (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))))
        (R := (Real.sqrt A)⁻¹) (inv_ne_zero hsqrt_ne)).const_mul (C / A ^ p)
  have hscaled_nonneg :
      0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))] scaledTail := by
    refine Eventually.of_forall ?_
    intro z
    simp [scaledTail, unitTail, hC]
    positivity
  have hscaled_eq_ennreal :
      (fun z : EuclideanSpace ℝ (Fin (k + 1)) ↦
        ENNReal.ofReal (C / (A + ‖z‖ ^ (2 : ℕ)) ^ p)) =
        fun z ↦ ENNReal.ofReal (scaledTail z) := by
    funext z
    exact congrArg ENNReal.ofReal (congrFun hscaled_eq z)
  rw [hscaled_eq_ennreal]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hscaled_int hscaled_nonneg]
  congr 1
  have hpow_sqrt :
      A ^ (((k + 1 : ℕ) : ℝ) / 2) = (Real.sqrt A) ^ (k + 1) := by
    calc
      A ^ (((k + 1 : ℕ) : ℝ) / 2)
          = A ^ ((1 / (2 : ℝ)) * ((k + 1 : ℕ) : ℝ)) := by
              congr 1
              ring
      _ = (A ^ (1 / (2 : ℝ))) ^ (((k + 1 : ℕ) : ℝ)) := by
            rw [← Real.rpow_mul hA.le]
      _ = (Real.sqrt A) ^ (((k + 1 : ℕ) : ℝ)) := by
            rw [Real.sqrt_eq_rpow]
      _ = (Real.sqrt A) ^ (k + 1) := by
            rw [Real.rpow_natCast]
  have hpow_split : A ^ p = A * (Real.sqrt A) ^ (k + 1) := by
    -- Proof comment: the exponent `(k + 3) / 2` is exactly `1 + (k + 1) / 2`.
    calc
      A ^ p = A ^ ((((k + 1 : ℕ) : ℝ) / 2) + 1) := by
                simp [p]
                congr 1
                ring
      _ = A ^ (((k + 1 : ℕ) : ℝ) / 2) * A := by
            rw [Real.rpow_add hA]
            simp [Real.rpow_natCast]
      _ = (Real.sqrt A) ^ (k + 1) * A := by
            rw [hpow_sqrt]
      _ = A * (Real.sqrt A) ^ (k + 1) := by
            ring
  calc
    ∫ z : EuclideanSpace ℝ (Fin (k + 1)), scaledTail z
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))
        =
      (C / A ^ p) *
        ∫ z : EuclideanSpace ℝ (Fin (k + 1)),
          unitTail ((Real.sqrt A)⁻¹ • z)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
            rw [integral_const_mul]
    _ = (C / A ^ p) *
        ((Real.sqrt A) ^ (k + 1) *
          ∫ z : EuclideanSpace ℝ (Fin (k + 1)), unitTail z
            ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))) := by
          rw [Measure.integral_comp_inv_smul_of_nonneg
            (μ := (volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))) unitTail hsqrt_pos.le]
          simp [finrank_euclideanSpace]
    _ = ((C / A ^ p) * (Real.sqrt A) ^ (k + 1)) *
        ∫ z : EuclideanSpace ℝ (Fin (k + 1)), unitTail z
          ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
          ring
    _ = (C / A) *
        ∫ z : EuclideanSpace ℝ (Fin (k + 1)), unitTail z
          ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
          have hsqrt_pow_ne : (Real.sqrt A) ^ (k + 1) ≠ 0 := by
            exact pow_ne_zero (k + 1) hsqrt_ne
          rw [hpow_split]
          field_simp [hA.ne', hsqrt_pow_ne]
    _ = (C / A) *
        ∫ z : EuclideanSpace ℝ (Fin (k + 1)),
          ((1 : ℝ) + ‖z‖ ^ (2 : ℕ)) ^ (-p)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
            rfl
    _ = (C / A) *
        ∫ z : EuclideanSpace ℝ (Fin (k + 1)),
          ((1 : ℝ) + ‖z‖ ^ (2 : ℕ)) ^ (-((((k + 3 : ℕ) : ℝ) / 2)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
            simp [p]

/-- Helper for Exercise 25.4.2: the tail-space unit ball has the expected Gamma/π volume
constant. -/
private theorem unitBallVolume_eq_gammaRatio {k : ℕ} :
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1) =
      Real.sqrt Real.pi ^ (k + 1) /
        Real.Gamma ((((k + 1 : ℕ) : ℝ) / 2) + 1) := by
  -- Proof comment: rewrite the unit-ball volume with the explicit Euclidean-space formula and
  -- then take the real part of the resulting finite `ENNReal` value.
  have hgamma_pos : 0 < Real.Gamma ((((k + 1 : ℕ) : ℝ) / 2) + 1) := by
    apply Real.Gamma_pos_of_pos
    positivity
  rw [Measure.real_def]
  rw [EuclideanSpace.volume_ball (ι := Fin (k + 1))
    (x := (0 : EuclideanSpace ℝ (Fin (k + 1)))) (r := (1 : ℝ))]
  have hnonneg :
      0 ≤ Real.sqrt Real.pi ^ (k + 1) / Real.Gamma ((((k + 1 : ℕ) : ℝ) / 2) + 1) := by
    positivity
  simpa [hgamma_pos.ne'] using (ENNReal.toReal_ofReal hnonneg)

/-- Helper for Exercise 25.4.2: once the universal centered tail integral is identified with the
unit-ball volume, the remaining Gamma/π prefactor collapses to `1 / π`. -/
private theorem poissonKernelUnitConstant_eq_invPi {k : ℕ} :
    (Real.Gamma ((((k + 3 : ℕ) : ℝ) / 2)) /
        Real.pi ^ ((((k + 3 : ℕ) : ℝ) / 2))) *
      ((volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1)) =
        1 / Real.pi := by
  have hgamma_arg :
      (((k + 3 : ℕ) : ℝ) / 2) = (((k + 1 : ℕ) : ℝ) / 2) + 1 := by
    calc
      (((k + 3 : ℕ) : ℝ) / 2) = ((k : ℝ) + 3) / 2 := by norm_num
      _ = ((k : ℝ) + 1) / 2 + 1 := by ring
      _ = (((k + 1 : ℕ) : ℝ) / 2) + 1 := by norm_num
  have hpi_split :
      Real.pi ^ ((((k + 1 : ℕ) : ℝ) / 2) + 1) =
        Real.pi * Real.sqrt Real.pi ^ (k + 1) := by
    calc
      Real.pi ^ ((((k + 1 : ℕ) : ℝ) / 2) + 1)
          = Real.pi ^ ((((k + 1 : ℕ) : ℝ) / 2)) * Real.pi := by
            rw [Real.rpow_add Real.pi_pos]
            simp [Real.rpow_natCast]
      _ = Real.sqrt Real.pi ^ (k + 1) * Real.pi := by
            rw [← Real.rpow_natCast]
            rw [Real.rpow_div_two_eq_sqrt (r := ((k + 1 : ℕ) : ℝ)) Real.pi_nonneg]
      _ = Real.pi * Real.sqrt Real.pi ^ (k + 1) := by
            ring
  have hgamma_ne :
      Real.Gamma ((((k + 1 : ℕ) : ℝ) / 2) + 1) ≠ 0 := by
    have harg_pos : 0 < (((k + 1 : ℕ) : ℝ) / 2) + 1 := by
      positivity
    exact (Real.Gamma_pos_of_pos harg_pos).ne'
  -- Proof comment: both Gamma factors are the same after the shift rewrite, and the remaining
  -- `π` powers cancel against the unit-ball constant.
  rw [unitBallVolume_eq_gammaRatio (k := k), hgamma_arg, hpi_split]
  field_simp [Real.pi_ne_zero, hgamma_ne]

/-- Helper for Exercise 25.4.2: the radial antiderivative of the universal tail integrand is the
expected elementary expression on `(0, ∞)`. -/
private theorem radialUnitTailAntiderivative_hasDerivAt {k : ℕ} {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun y : ℝ ↦
        ((k + 1 : ℝ)⁻¹) * y ^ (k + 1) *
          ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-((((k + 1 : ℕ) : ℝ) / 2)))
      )
      (t ^ k * ((1 : ℝ) + t ^ (2 : ℕ)) ^ (-((((k + 3 : ℕ) : ℝ) / 2)))) t := by
  let q : ℝ := (((k + 1 : ℕ) : ℝ) / 2)
  let B : ℝ := (1 : ℝ) + t ^ (2 : ℕ)
  have hpow : HasDerivAt (fun y : ℝ ↦ y ^ (k + 1 : ℕ)) ((k + 1 : ℝ) * t ^ k) t := by
    simpa using (hasDerivAt_id t).pow (k + 1)
  have hbase : HasDerivAt (fun y : ℝ ↦ (1 : ℝ) + y ^ (2 : ℕ)) (2 * t) t := by
    simpa [two_mul] using ((hasDerivAt_id t).pow 2).const_add 1
  have hrpow :
      HasDerivAt
        (fun y : ℝ ↦ ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-q))
        (((-q) * B ^ (-q - 1)) * (2 * t)) t := by
    convert (hbase.rpow_const (by
      left
      positivity)) using 1
    · ring
  have hmul := hpow.mul hrpow
  have hsplit :
      B ^ (-q) = B ^ (-q - 1) * B := by
    rw [show (-q : ℝ) = (-q - 1) + 1 by ring, Real.rpow_add (by positivity : 0 < B)]
    simp
  have hpow_shift : (-q - 1 : ℝ) = -((((k + 3 : ℕ) : ℝ) / 2)) := by
    simp [q]
    ring
  have htpow : t ^ (k + 1 : ℕ) * t = t ^ k * t ^ (2 : ℕ) := by
    rw [pow_succ', pow_succ']
    ring
  convert hmul.const_mul ((k + 1 : ℝ)⁻¹) using 1
  · funext y
    dsimp [q]
    ring
  · rw [hsplit, hpow_shift]
    dsimp [B, q]
    have hk_ne : (k + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hk_ne]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring

/-- Helper for Exercise 25.4.2: the normalized quadratic ratio is `1` minus the reciprocal tail
factor. -/
private theorem radialUnitTailRatio_eq_one_sub_inv (y : ℝ) :
    y ^ (2 : ℕ) / ((1 : ℝ) + y ^ (2 : ℕ)) =
      1 - (((1 : ℝ) + y ^ (2 : ℕ))⁻¹) := by
  have hden : (1 : ℝ) + y ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- Helper for Exercise 25.4.2: the normalized quadratic ratio tends to `1` at `+∞`. -/
private theorem radialUnitTailRatio_tendsto_one :
    Tendsto (fun y : ℝ ↦ y ^ (2 : ℕ) / ((1 : ℝ) + y ^ (2 : ℕ))) atTop (𝓝 1) := by
  have hpow : Tendsto (fun y : ℝ ↦ y ^ (2 : ℕ)) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hadd : Tendsto (fun y : ℝ ↦ (1 : ℝ) + y ^ (2 : ℕ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 hpow
  have hinv : Tendsto (fun y : ℝ ↦ ((1 : ℝ) + y ^ (2 : ℕ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hadd
  rw [show (fun y : ℝ ↦ y ^ (2 : ℕ) / ((1 : ℝ) + y ^ (2 : ℕ))) =
      fun y : ℝ ↦ 1 - (((1 : ℝ) + y ^ (2 : ℕ))⁻¹) by
        funext y
        exact radialUnitTailRatio_eq_one_sub_inv y]
  simpa using tendsto_const_nhds.sub hinv

/-- Helper for Exercise 25.4.2: for positive `y`, the radial antiderivative can be rewritten as a
power of the normalized quadratic ratio. -/
private theorem radialUnitTailCore_eq_ratio {k : ℕ} {y : ℝ} (hy : 0 < y) :
    y ^ (k + 1) * ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-((((k + 1 : ℕ) : ℝ) / 2))) =
      (y ^ (2 : ℕ) / ((1 : ℝ) + y ^ (2 : ℕ))) ^ ((((k + 1 : ℕ) : ℝ) / 2)) := by
  let q : ℝ := (((k + 1 : ℕ) : ℝ) / 2)
  have hy_nonneg : 0 ≤ y := hy.le
  have hy_sq_nonneg : 0 ≤ y ^ (2 : ℕ) := by positivity
  have hbase_nonneg : 0 ≤ (1 : ℝ) + y ^ (2 : ℕ) := by positivity
  have hy_pow :
      (y ^ (2 : ℕ) : ℝ) ^ q = y ^ (k + 1 : ℕ) := by
    calc
      (y ^ (2 : ℕ) : ℝ) ^ q = y ^ (((2 : ℕ) : ℝ) * q) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy_nonneg]
      _ = y ^ (((k + 1 : ℕ) : ℝ)) := by
        simp [q]
        ring
      _ = y ^ (k + 1 : ℕ) := by
        rw [Real.rpow_natCast]
  calc
    y ^ (k + 1) * ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-q)
        = (y ^ (2 : ℕ) : ℝ) ^ q * ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-q) := by
            rw [hy_pow]
    _ = (y ^ (2 : ℕ) : ℝ) ^ q / ((1 : ℝ) + y ^ (2 : ℕ)) ^ q := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hbase_nonneg]
    _ = (y ^ (2 : ℕ) / ((1 : ℝ) + y ^ (2 : ℕ))) ^ q := by
          symm
          rw [Real.div_rpow hy_sq_nonneg hbase_nonneg]
    _ = (y ^ (2 : ℕ) / ((1 : ℝ) + y ^ (2 : ℕ))) ^ ((((k + 1 : ℕ) : ℝ) / 2)) := by
          simp [q]

/-- Helper for Exercise 25.4.2: the antiderivative core tends to `1` at `+∞`. -/
private theorem radialUnitTailCore_tendsto_one {k : ℕ} :
    Tendsto
      (fun y : ℝ ↦
        y ^ (k + 1) * ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-((((k + 1 : ℕ) : ℝ) / 2))))
      atTop (𝓝 1) := by
  let q : ℝ := (((k + 1 : ℕ) : ℝ) / 2)
  have hq_nonneg : 0 ≤ q := by
    simp [q]
    positivity
  have hpowq :
      Tendsto (fun y : ℝ ↦ (y ^ (2 : ℕ) / ((1 : ℝ) + y ^ (2 : ℕ))) ^ q) atTop (𝓝 1) := by
    simpa [q] using radialUnitTailRatio_tendsto_one.rpow_const (Or.inr hq_nonneg)
  have hrewrite :
      ∀ᶠ y in atTop,
        y ^ (k + 1) * ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-q) =
          (y ^ (2 : ℕ) / ((1 : ℝ) + y ^ (2 : ℕ))) ^ q := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with y hy
    simpa [q] using radialUnitTailCore_eq_ratio (k := k) hy
  exact Tendsto.congr' (by
    filter_upwards [hrewrite] with y hy
    exact hy.symm) hpowq

/-- Helper for Exercise 25.4.2: the one-dimensional radial tail integral equals `(k + 1)⁻¹`. -/
private theorem radialUnitTailIntegral_eq_inv {k : ℕ} :
    ∫ y in Set.Ioi (0 : ℝ),
      y ^ k * ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-((((k + 3 : ℕ) : ℝ) / 2))) =
        (k + 1 : ℝ)⁻¹ := by
  let g : ℝ → ℝ := fun y ↦
    ((k + 1 : ℝ)⁻¹) * y ^ (k + 1) *
      ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-((((k + 1 : ℕ) : ℝ) / 2)))
  have hcont : ContinuousWithinAt g (Set.Ici 0) 0 := by
    have hpow : ContinuousAt (fun y : ℝ ↦ y ^ (k + 1 : ℕ)) 0 :=
      (continuousAt_id.pow (k + 1))
    have hbase : ContinuousAt (fun y : ℝ ↦ (1 : ℝ) + y ^ (2 : ℕ)) 0 :=
      continuousAt_const.add (continuousAt_id.pow 2)
    have hrpow :
        ContinuousAt
          (fun y : ℝ ↦ ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-((((k + 1 : ℕ) : ℝ) / 2)))) 0 :=
      hbase.rpow_const (Or.inl (by norm_num : (1 : ℝ) + 0 ^ (2 : ℕ) ≠ 0))
    simpa [g, mul_assoc] using (continuousAt_const.mul (hpow.mul hrpow)).continuousWithinAt
  have hderiv :
      ∀ y ∈ Set.Ioi (0 : ℝ), HasDerivAt g
        (y ^ k * ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-((((k + 3 : ℕ) : ℝ) / 2)))) y := by
    intro y hy
    simpa [g] using radialUnitTailAntiderivative_hasDerivAt (k := k) hy
  have hnonneg :
      ∀ y ∈ Set.Ioi (0 : ℝ),
        0 ≤ y ^ k * ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-((((k + 3 : ℕ) : ℝ) / 2))) := by
    intro y hy
    have hy_nonneg : 0 ≤ y := le_of_lt hy
    positivity
  have hlim : Tendsto g atTop (𝓝 ((k + 1 : ℝ)⁻¹)) := by
    simpa [g, mul_assoc] using
      tendsto_const_nhds.mul (radialUnitTailCore_tendsto_one (k := k))
  simpa [g] using
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg hlim

/-- Helper for Exercise 25.4.2: the universal Euclidean tail integral is exactly the volume of
the unit ball in the tail space. -/
private theorem unitTailIntegral_eq_unitBallVolume {k : ℕ} :
    ∫ z : EuclideanSpace ℝ (Fin (k + 1)),
      ((1 : ℝ) + ‖z‖ ^ (2 : ℕ)) ^ (-((((k + 3 : ℕ) : ℝ) / 2)))
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) =
        (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1) := by
  -- Proof comment: apply the Euclidean radial integration formula and then use the previous
  -- one-dimensional tail computation to collapse the remaining factor `(k + 1)`.
  calc
    ∫ z : EuclideanSpace ℝ (Fin (k + 1)),
        ((1 : ℝ) + ‖z‖ ^ (2 : ℕ)) ^ (-((((k + 3 : ℕ) : ℝ) / 2)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) =
      (k + 1 : ℝ) *
        (((volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1)) *
          ∫ y in Set.Ioi (0 : ℝ),
            y ^ k * ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-((((k + 3 : ℕ) : ℝ) / 2)))) := by
            simpa [smul_eq_mul, finrank_euclideanSpace, mul_assoc, mul_left_comm, mul_comm] using
              (MeasureTheory.integral_fun_norm_addHaar
                (μ := (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))))
                (f := fun y : ℝ ↦ ((1 : ℝ) + y ^ (2 : ℕ)) ^ (-((((k + 3 : ℕ) : ℝ) / 2)))))
    _ = (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1) := by
      rw [radialUnitTailIntegral_eq_inv]
      have hk_ne : (k + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hk_ne]

/-- Helper for Exercise 25.4.2: when the tail fiber is zero-dimensional, the first-coordinate
marginal of the explicit Poisson-kernel measure is the corresponding Cauchy law by direct
simplification. -/
private theorem firstCoordinate_upperHalfSpacePoissonKernelMeasure_eq_cauchyMeasure_finOne
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ upperHalfSpace 1) :
    Measure.map (fun y : EuclideanSpace ℝ (Fin 1) ↦ y 0)
      (upperHalfSpacePoissonKernelMeasure (n := 1) x) =
        cauchyMeasure ((upperHalfSpaceBoundaryProjection 1 x) 0)
          (Real.toNNReal (x (Fin.last 1))) := by
  have hx_last : 0 < x (Fin.last 1) := by
    simpa [upperHalfSpace] using hx
  -- Proof comment: once the `Fin 0` fiber is collapsed to the unique point, the remaining
  -- density is exactly the one-dimensional Cauchy kernel.
  rw [firstCoordinate_upperHalfSpacePoissonKernelMeasure_eq_withDensityFiberIntegral (m := 0) x]
  rw [cauchyMeasure_of_scale_ne_zero ((upperHalfSpaceBoundaryProjection 1 x) 0)
    (Real.toNNReal_pos.mpr hx_last).ne']
  congr 1
  ext s
  rw [volume_euclideanSpace_eq_dirac (ι := Fin 0)]
  simp only [MeasureTheory.lintegral_dirac]
  have hsq :
      ((upperHalfSpaceBoundaryProjection 1 x) 0 - s) ^ (2 : ℕ) =
        (s - (upperHalfSpaceBoundaryProjection 1 x) 0) ^ (2 : ℕ) := by
    ring
  have hdist :
      dist (upperHalfSpaceBoundaryProjection 1 x) ((euclideanPiFinSuccAbove 0).symm (s, 0)) ^
          (2 : ℕ) =
        (s - (upperHalfSpaceBoundaryProjection 1 x) 0) ^ (2 : ℕ) := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    simpa [euclideanPiFinSuccAbove_symm_zero, hsq]
  have hx_max : max (x (Fin.last 1)) 0 = x (Fin.last 1) := max_eq_left hx_last.le
  have hdist' :
      dist (upperHalfSpaceBoundaryProjection 1 x) ((euclideanPiFinSuccAbove 0).symm (s, 0)) ^
          (2 : ℕ) =
        (s - x.ofLp 0) ^ (2 : ℕ) := by
    simpa [upperHalfSpaceBoundaryProjection] using hdist
  have hx_max' : max (x.ofLp 1) 0 = x.ofLp 1 := by
    simpa using hx_max
  -- Proof comment: the unique tail coordinate disappears, and the Poisson kernel matches the
  -- textbook Cauchy density after the symmetric square rewrite.
  have hkernel :
      Real.pi⁻¹ * x.ofLp 1 /
          (dist (upperHalfSpaceBoundaryProjection 1 x) ((euclideanPiFinSuccAbove 0).symm (s, 0)) ^
              (2 : ℕ) +
            x.ofLp 1 ^ (2 : ℕ)) =
        Real.pi⁻¹ * max (x.ofLp 1) 0 *
          ((s - x.ofLp 0) ^ (2 : ℕ) + max (x.ofLp 1) 0 ^ (2 : ℕ))⁻¹ := by
    rw [div_eq_mul_inv, hdist', hx_max']
  simpa [upperHalfSpacePoissonKernel, upperHalfSpaceBoundaryDistanceSq, upperHalfSpaceBoundaryProjection,
    cauchyPDF_def, cauchyPDFReal_def, Real.toNNReal_of_nonneg hx_last.le] using
    congrArg ENNReal.ofReal hkernel

/-- Helper for Exercise 25.4.2: the first-coordinate marginal of the explicit Poisson-kernel
measure is the corresponding one-dimensional Cauchy law. -/
theorem firstCoordinate_upperHalfSpacePoissonKernelMeasure_eq_cauchyMeasure
    {x : State} (hx : x ∈ upperHalfSpace n) (hn : n ≠ 0) :
    Measure.map (fun y : Boundary ↦ y ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
      (upperHalfSpacePoissonKernelMeasure (n := n) x) =
      cauchyMeasure ((upperHalfSpaceBoundaryProjection n x) ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
        (Real.toNNReal (x (Fin.last n))) := by
  have hx_last : 0 < x (Fin.last n) := by
    simpa [upperHalfSpace] using hx
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  -- Route correction: the proof is now normalized to a one-dimensional `withDensity` law on the
  -- first coordinate. The `m = 0` branch is now closed directly, and only the positive-tail
  -- centered radial integral remains.
  cases m with
  | zero =>
      -- Proof comment: with no tail variables left, the theorem is exactly the one-dimensional
      -- Cauchy computation established above.
      simpa using firstCoordinate_upperHalfSpacePoissonKernelMeasure_eq_cauchyMeasure_finOne hx
  | succ k =>
      change Measure.map (fun y : EuclideanSpace ℝ (Fin ((k + 1) + 1)) ↦ y 0)
          (upperHalfSpacePoissonKernelMeasure (n := (k + 1) + 1) x) =
        cauchyMeasure ((upperHalfSpaceBoundaryProjection ((k + 1) + 1) x) 0)
          (Real.toNNReal (x (Fin.last ((k + 1) + 1))))
      rw [firstCoordinate_upperHalfSpacePoissonKernelMeasure_eq_withDensityFiberIntegral
        (m := k + 1) x]
      rw [cauchyMeasure_of_scale_ne_zero ((upperHalfSpaceBoundaryProjection (k + 2) x) 0)
        (Real.toNNReal_pos.mpr hx_last).ne']
      let C : ℝ :=
        Real.Gamma (((k + 3 : ℕ) : ℝ) / 2) /
          Real.pi ^ (((k + 3 : ℕ) : ℝ) / 2) *
            x (Fin.last (k + 2))
      let A : ℝ → ℝ :=
        fun s ↦
          (s - (upperHalfSpaceBoundaryProjection (k + 2) x) 0) ^ (2 : ℕ) +
            x (Fin.last (k + 2)) ^ (2 : ℕ)
      let c : EuclideanSpace ℝ (Fin (k + 1)) :=
        WithLp.toLp 2 fun i ↦ (upperHalfSpaceBoundaryProjection (k + 2) x) (Fin.succ i)
      congr 1
      ext s
      have hkernel :
          (fun z : EuclideanSpace ℝ (Fin (k + 1)) ↦
            ENNReal.ofReal (upperHalfSpacePoissonKernel (k + 2) x
              ((euclideanPiFinSuccAbove (k + 1)).symm (s, z)))) =
            fun z : EuclideanSpace ℝ (Fin (k + 1)) ↦
              ENNReal.ofReal (C / (A s + ‖z - c‖ ^ (2 : ℕ)) ^ (((k + 3 : ℕ) : ℝ) / 2)) := by
        -- Proof comment: the new kernel normal form isolates the head coordinate from the shifted
        -- tail norm, so the remaining analytic step depends only on `A s` and `‖z - c‖`.
        funext z
        exact congrArg ENNReal.ofReal <|
          by
            simpa [C, A, c, add_assoc, add_left_comm, add_comm] using
              poissonKernelFiberIntegrand_eq_shiftedNorm (x := x) s z
      rw [hkernel]
      rw [tailFiberIntegral_eq_centeredTailIntegral (k := k) (C := C) (A := A s) (c := c)]
      have hApos : 0 < A s := by
        -- Proof comment: the centered denominator keeps the positive vertical square term.
        simp [A]
        positivity
      have hCnn : 0 ≤ C := by
        -- Proof comment: the Poisson prefactor is a product of positive Gamma/π factors and the
        -- positive vertical coordinate.
        simp [C]
        positivity
      rw [centeredTailIntegral_eq_ofReal_mul_unitTailIntegral
        (k := k) (A := A s) (C := C) hApos hCnn]
      rw [unitTailIntegral_eq_unitBallVolume (k := k)]
      have hcentered :
          cauchyPDF ((upperHalfSpaceBoundaryProjection (k + 2) x) 0)
              (Real.toNNReal (x (Fin.last (k + 2)))) s =
            cauchyPDF 0 (Real.toNNReal (x (Fin.last (k + 2))))
              (s - (upperHalfSpaceBoundaryProjection (k + 2) x) 0) := by
        simpa using
          congrFun
            (cauchyPDF_centered_sub_right_local
              ((upperHalfSpaceBoundaryProjection (k + 2) x) 0)
              (Real.toNNReal (x (Fin.last (k + 2))))) s |>.symm
      rw [hcentered, cauchyPDF_def]
      have hconst :
          C * (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1) =
            (1 / Real.pi) * x (Fin.last (k + 2)) := by
        -- Proof comment: the Gamma/π constant from the Poisson kernel and the unit-ball volume
        -- collapse to the one-dimensional Cauchy normalization constant.
        calc
          C * (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1)
              = (Real.Gamma (((k + 3 : ℕ) : ℝ) / 2) /
                    Real.pi ^ (((k + 3 : ℕ) : ℝ) / 2) *
                  (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1)) *
                  x (Fin.last (k + 2)) := by
                    dsimp [C]
                    ring
          _ = (1 / Real.pi) * x (Fin.last (k + 2)) := by
                rw [poissonKernelUnitConstant_eq_invPi]
      have hA :
          A s =
            (s - (upperHalfSpaceBoundaryProjection (k + 2) x) 0) ^ (2 : ℕ) +
              (Real.toNNReal (x (Fin.last (k + 2))) : ℝ) ^ (2 : ℕ) := by
        simp [A, Real.toNNReal_of_nonneg hx_last.le]
      have hmain :
          (C / A s) *
              (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1) =
            cauchyPDFReal 0 (Real.toNNReal (x (Fin.last (k + 2))))
              (s - (upperHalfSpaceBoundaryProjection (k + 2) x) 0) := by
        -- Proof comment: after the centered denominator rewrite, the remaining expression is
        -- exactly the centered Cauchy density with scale `x_last`.
        calc
          (C / A s) * (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1)
                  = (C * (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1)) /
                  A s := by
                    field_simp [hApos.ne']
          _ = ((1 / Real.pi) * x (Fin.last (k + 2))) / A s := by rw [hconst]
          _ = cauchyPDFReal 0 (Real.toNNReal (x (Fin.last (k + 2))))
                (s - (upperHalfSpaceBoundaryProjection (k + 2) x) 0) := by
                  rw [cauchyPDFReal_def, hA]
                  rw [div_eq_mul_inv]
                  simp [Real.toNNReal_of_nonneg hx_last.le]
      simpa [hmain]

theorem map_unitDirection_upperHalfSpacePoissonKernelMeasure_eq_cauchyMeasure
    {x : State} (hx : x ∈ upperHalfSpace n)
    {u : Boundary} (hu : ‖u‖ = 1) :
    Measure.map (fun y ↦ inner ℝ y u) (upperHalfSpacePoissonKernelMeasure (n := n) x) =
      cauchyMeasure (inner ℝ (upperHalfSpaceBoundaryProjection n x) u)
        (Real.toNNReal (x (Fin.last n))) := by
  have hn : n ≠ 0 := boundaryDimension_ne_zero_of_norm_eq_one (n := n) hu
  let i0 : Fin n := ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩
  have hcard : Module.finrank ℝ Boundary = Fintype.card (Fin n) := by
    simpa using (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin n))
  have huOrthonormal :
      Orthonormal ℝ (({i0} : Set (Fin n)).restrict fun _ : Fin n ↦ u) := by
    -- Proof comment: on the singleton set `{0}`, orthonormality is exactly the unit-norm
    -- hypothesis on `u`.
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst hij
    simp [hu]
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := Boundary) (ι := Fin n) hcard
      (v := fun _ : Fin n ↦ u) (s := ({i0} : Set (Fin n))) huOrthonormal
  have hb0 : b i0 = u := by
    simpa using hb i0 (by simp)
  let xRot : State := rotatedUpperHalfSpaceStart (n := n) b x
  have hxRot : xRot ∈ upperHalfSpace n :=
    rotatedUpperHalfSpaceStart_mem_upperHalfSpace (n := n) b hx
  -- Route correction: the unit-direction marginal now factors through the rotated first
  -- coordinate, so the only remaining analytic blocker is the axis marginal theorem above.
  calc
    Measure.map (fun y ↦ inner ℝ y u) (upperHalfSpacePoissonKernelMeasure (n := n) x) =
        Measure.map (fun z : Boundary ↦ z i0) (Measure.map b.repr
          (upperHalfSpacePoissonKernelMeasure (n := n) x)) := by
      simpa using map_inner_eq_map_firstCoordinate_repr (n := n) b i0 hb0
        (upperHalfSpacePoissonKernelMeasure (n := n) x)
    _ = Measure.map (fun z : Boundary ↦ z i0)
          (upperHalfSpacePoissonKernelMeasure (n := n) xRot) := by
      rw [map_repr_upperHalfSpacePoissonKernelMeasure_eq (n := n) b x]
    _ = cauchyMeasure ((upperHalfSpaceBoundaryProjection n xRot) i0)
          (Real.toNNReal (xRot (Fin.last n))) := by
      rw [firstCoordinate_upperHalfSpacePoissonKernelMeasure_eq_cauchyMeasure
        (n := n) hxRot hn]
    _ = cauchyMeasure (inner ℝ (upperHalfSpaceBoundaryProjection n x) u)
          (Real.toNNReal (x (Fin.last n))) := by
      simp [xRot, i0, upperHalfSpaceBoundaryProjection_rotatedUpperHalfSpaceStart,
        rotatedUpperHalfSpaceStart_last, OrthonormalBasis.repr_apply_apply, hb0, real_inner_comm]

/-- Helper for Exercise 25.4.2: every nontrivial scalar projection of the transported harmonic
measure should reduce to the planar upper-half-plane Cauchy law. -/
theorem map_inner_upperHalfSpaceHarmonicMeasure_eq_cauchyMeasure_of_ne_zero
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfSpace n)
    (hExitMeas : Measurable (upperHalfSpaceExitValue n W x))
    {t : Boundary} (ht : t ≠ 0) :
    Measure.map (fun y ↦ inner ℝ y t)
      (upperHalfSpaceBoundaryHarmonicMeasure (μ := μ) (n := n) W x hx hExitMeas) =
        Measure.map (fun z : ℝ ↦ ‖t‖ * z)
          (cauchyMeasure
            (inner ℝ (upperHalfSpaceBoundaryProjection n x) (‖t‖⁻¹ • t))
            (Real.toNNReal (x (Fin.last n)))) := by
  let u : Boundary := ‖t‖⁻¹ • t
  let ν : Measure Boundary :=
    upperHalfSpaceBoundaryHarmonicMeasure (μ := μ) (n := n) W x hx hExitMeas
  have hnorm_pos : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hu : ‖u‖ = 1 := by
    -- Proof comment: the normalized direction has unit norm because `t` is nonzero.
    rw [norm_smul]
    simp [Real.norm_eq_abs, abs_of_pos hnorm_pos, hnorm_pos.ne']
  -- Proof comment: factor the arbitrary projection through the unit direction `‖t‖⁻¹ • t`, then
  -- use the unit-direction law as the only remaining Brownian ingredient.
  have hmain :
      Measure.map (fun y ↦ inner ℝ y t) ν =
        Measure.map (fun z : ℝ ↦ ‖t‖ * z)
          (cauchyMeasure
            (inner ℝ (upperHalfSpaceBoundaryProjection n x) u)
            (Real.toNNReal (x (Fin.last n)))) := by
    calc
      Measure.map (fun y ↦ inner ℝ y t) ν =
          Measure.map (fun z : ℝ ↦ ‖t‖ * z)
            (Measure.map (fun y ↦ inner ℝ y u) ν) := by
          simpa [u, ν] using
            map_inner_eq_map_scale_unitProjection (ν := ν) (t := t) ht
      _ = Measure.map (fun z : ℝ ↦ ‖t‖ * z)
          (cauchyMeasure
            (inner ℝ (upperHalfSpaceBoundaryProjection n x) u)
            (Real.toNNReal (x (Fin.last n)))) := by
          -- Proof comment: the unresolved probabilistic work is exactly the unit-direction law.
          rw [map_unitDirection_upperHalfSpaceHarmonicMeasure_eq_cauchyMeasure
            (μ := μ) (n := n) (W := W) (u := u) hW hx hExitMeas hu]
  simpa [u, ν] using hmain

/-- Helper for Exercise 25.4.2: every nontrivial scalar projection of the explicit Poisson-kernel
measure should be the Cauchy law with the matching location and scale. -/
theorem map_inner_upperHalfSpacePoissonKernelMeasure_eq_cauchyMeasure_of_ne_zero
    {x : State} (hx : x ∈ upperHalfSpace n)
    {t : Boundary} (ht : t ≠ 0) :
    Measure.map (fun y ↦ inner ℝ y t) (upperHalfSpacePoissonKernelMeasure (n := n) x) =
      Measure.map (fun z : ℝ ↦ ‖t‖ * z)
        (cauchyMeasure
          (inner ℝ (upperHalfSpaceBoundaryProjection n x) (‖t‖⁻¹ • t))
          (Real.toNNReal (x (Fin.last n)))) := by
  let u : Boundary := ‖t‖⁻¹ • t
  let ν : Measure Boundary := upperHalfSpacePoissonKernelMeasure (n := n) x
  have hnorm_pos : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hu : ‖u‖ = 1 := by
    -- Proof comment: the normalization step on the analytic side uses the same unit vector.
    rw [norm_smul]
    simp [Real.norm_eq_abs, abs_of_pos hnorm_pos, hnorm_pos.ne']
  -- Proof comment: isolate the remaining analytic work at unit norm, where the projected kernel
  -- should reduce to the first-coordinate marginal after an orthogonal change of basis.
  have hmain :
      Measure.map (fun y ↦ inner ℝ y t) ν =
        Measure.map (fun z : ℝ ↦ ‖t‖ * z)
          (cauchyMeasure
            (inner ℝ (upperHalfSpaceBoundaryProjection n x) u)
            (Real.toNNReal (x (Fin.last n)))) := by
    calc
      Measure.map (fun y ↦ inner ℝ y t) ν =
          Measure.map (fun z : ℝ ↦ ‖t‖ * z)
            (Measure.map (fun y ↦ inner ℝ y u) ν) := by
          simpa [u, ν] using
            map_inner_eq_map_scale_unitProjection (ν := ν) (t := t) ht
      _ = Measure.map (fun z : ℝ ↦ ‖t‖ * z)
          (cauchyMeasure
            (inner ℝ (upperHalfSpaceBoundaryProjection n x) u)
            (Real.toNNReal (x (Fin.last n)))) := by
          -- Proof comment: the unresolved analytic work is exactly the unit-direction marginal.
          rw [map_unitDirection_upperHalfSpacePoissonKernelMeasure_eq_cauchyMeasure
            (n := n) (u := u) hx hu]
  simpa [u, ν] using hmain

/-- Helper for Exercise 25.4.2: in positive dimension, the explicit Poisson-kernel boundary
measure is a probability measure. -/
theorem upperHalfSpacePoissonKernelMeasure_isProbability
    (hn : n ≠ 0) {x : State} (hx : x ∈ upperHalfSpace n) :
    IsProbabilityMeasure (upperHalfSpacePoissonKernelMeasure (n := n) x) := by
  let i : Fin n := ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩
  let t : Boundary := EuclideanSpace.single i 1
  let ν : Measure Boundary := upperHalfSpacePoissonKernelMeasure (n := n) x
  have ht : t ≠ 0 := by
    intro ht0
    have hcoord : t i = 0 := by
      simpa [ht0]
    simpa [t] using hcoord
  -- Proof comment: a pushforward measure and its source have the same mass on `Set.univ`, so one
  -- nonzero scalar projection with Cauchy law already forces total mass `1`.
  refine (MeasureTheory.isProbabilityMeasure_iff).2 ?_
  calc
    ν Set.univ = Measure.map (fun y : Boundary ↦ inner ℝ y t) ν Set.univ := by
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
      simp
    _ = 1 := by
      rw [map_inner_upperHalfSpacePoissonKernelMeasure_eq_cauchyMeasure_of_ne_zero
        (n := n) hx ht]
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
      simp

/-- Helper for Exercise 25.4.2: two boundary probability measures agree once all nonzero scalar
projections agree. -/
theorem boundaryMeasure_eq_of_projection_eq
    {ν₁ ν₂ : Measure Boundary} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hProj :
      ∀ ⦃t : Boundary⦄, t ≠ 0 →
        Measure.map (fun y ↦ inner ℝ y t) ν₁ =
          Measure.map (fun y ↦ inner ℝ y t) ν₂) :
    ν₁ = ν₂ := by
  -- Proof comment: characteristic functions are determined by one-dimensional projections, and
  -- probability normalization handles the origin.
  apply Measure.ext_of_charFun
  ext t
  by_cases ht : t = 0
  · subst ht
    simp
  · rw [charFun_eq_charFun_innerProjection, charFun_eq_charFun_innerProjection]
    rw [hProj ht]

/-- Helper for Exercise 25.4.2: transporting the upper-half-space harmonic measure to boundary
coordinates should recover the classical Poisson-kernel density on `ℝ^n`. -/
theorem map_upperHalfSpaceFrontierEquiv_harmonicMeasure_eq_withDensity
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfSpace n)
    (hExitMeas : Measurable (upperHalfSpaceExitValue n W x)) :
    Measure.map (upperHalfSpaceFrontierEquiv n)
        (harmonicMeasure
          (fun _ : State ↦ (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω))
          (upperHalfSpace n)
          (upperHalfSpaceExitValue n W x)
          hExitMeas
          ⟨x, hx⟩ : Measure (frontier (upperHalfSpace n))) =
      (volume.withDensity
        (fun y ↦ ENNReal.ofReal (upperHalfSpacePoissonKernel n x y)) : Measure Boundary) := by
  let νH : Measure Boundary :=
    upperHalfSpaceBoundaryHarmonicMeasure (μ := μ) (n := n) W x hx hExitMeas
  let νP : Measure Boundary := upperHalfSpacePoissonKernelMeasure (n := n) x
  have hEq : νH = νP := by
    by_cases h0 : n = 0
    · subst h0
      -- Proof comment: in the degenerate one-dimensional case the boundary is a singleton, so both
      -- sides are probability measures on a subsingleton space and hence must agree.
      have hFrontierMeas : Measurable (upperHalfSpaceFrontierEquiv 0) := by
        simp [upperHalfSpaceFrontierEquiv]
        fun_prop
      letI : IsProbabilityMeasure νH := by
        haveI :
            IsProbabilityMeasure (Measure.map (upperHalfSpaceExitValue 0 W x) μ) :=
          Measure.isProbabilityMeasure_map hExitMeas.aemeasurable
        dsimp [νH, upperHalfSpaceBoundaryHarmonicMeasure]
        exact Measure.isProbabilityMeasure_map hFrontierMeas.aemeasurable
      have hνP : νP = Measure.dirac 0 := by
        simpa [νP] using upperHalfSpacePoissonKernelMeasure_zero_eq_dirac hx
      rw [hνP]
      exact measure_eq_of_subsingleton_of_isProbabilityMeasure
    · have hFrontierMeas : Measurable (upperHalfSpaceFrontierEquiv n) := by
        simp [upperHalfSpaceFrontierEquiv]
        fun_prop
      letI : IsProbabilityMeasure νH := by
        haveI :
            IsProbabilityMeasure (Measure.map (upperHalfSpaceExitValue n W x) μ) :=
          Measure.isProbabilityMeasure_map hExitMeas.aemeasurable
        -- Proof comment: the canonical harmonic measure is already a probability measure, and the
        -- frontier equivalence preserves this under pushforward.
        dsimp [νH, upperHalfSpaceBoundaryHarmonicMeasure]
        exact Measure.isProbabilityMeasure_map hFrontierMeas.aemeasurable
      letI : IsProbabilityMeasure νP := by
        simpa [νP] using upperHalfSpacePoissonKernelMeasure_isProbability (n := n) h0 hx
      -- Route correction: once the explicit density is known to be a probability measure, it is
      -- enough to compare all characteristic functions through scalar projections.
      exact boundaryMeasure_eq_of_projection_eq (n := n) (ν₁ := νH) (ν₂ := νP)
        (fun {_} ht ↦ by
          -- Proof comment: each nonzero scalar projection is already identified with the same
          -- Cauchy law on both the harmonic and Poisson-kernel sides.
          rw [map_inner_upperHalfSpaceHarmonicMeasure_eq_cauchyMeasure_of_ne_zero
            (μ := μ) (n := n) (W := W) hW hx hExitMeas ht]
          rw [map_inner_upperHalfSpacePoissonKernelMeasure_eq_cauchyMeasure_of_ne_zero
            (n := n) hx ht])
  simpa [νH, νP, upperHalfSpaceBoundaryHarmonicMeasure, upperHalfSpacePoissonKernelMeasure]
    using hEq

/-- The boundary-coordinate exit distribution of `x + W` from the upper half-space is the
pushforward of the harmonic measure along the canonical boundary identification, hence is given by
the classical Poisson kernel, provided the canonical frontier-valued exit map is measurable. -/
theorem upperHalfSpaceExitDistribution_eq_withDensity
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfSpace n)
    (hExitMeas : Measurable (upperHalfSpaceExitValue n W x)) :
    Measure.map (upperHalfSpaceExitLocation n W x) μ =
      (volume.withDensity
        (fun y ↦ ENNReal.ofReal (upperHalfSpacePoissonKernel n x y)) : Measure Boundary) := by
  -- Route correction: the direct exit-law identity is first reduced to the canonical harmonic
  -- measure, so the only remaining work is the analytic Poisson-kernel identification.
  calc
    Measure.map (upperHalfSpaceExitLocation n W x) μ =
        Measure.map (upperHalfSpaceFrontierEquiv n)
          (harmonicMeasure
            (fun _ : State ↦ (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω))
            (upperHalfSpace n)
            (upperHalfSpaceExitValue n W x)
            hExitMeas
            ⟨x, hx⟩ : Measure (frontier (upperHalfSpace n))) :=
      upperHalfSpaceExitDistribution_eq_mapHarmonicMeasure
        (μ := μ) (n := n) (W := W) hx hExitMeas
    _ =
        (volume.withDensity
          (fun y ↦ ENNReal.ofReal (upperHalfSpacePoissonKernel n x y)) : Measure Boundary) :=
      map_upperHalfSpaceFrontierEquiv_harmonicMeasure_eq_withDensity
        (μ := μ) (n := n) (W := W) hW hx hExitMeas

end

end HalfSpace

end ProbabilityTheory
