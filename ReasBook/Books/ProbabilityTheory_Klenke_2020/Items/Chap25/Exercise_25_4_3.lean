/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.BrownianMotionVectorStartedAt
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Exercise_25_4_3.BoundaryTransport
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_68

open Filter MeasureTheory ProbabilityTheory Topology
open scoped Pointwise

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d : ℕ} [NeZero d]

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

-- Local instance justification (decidable membership): the patched Dirichlet owner branches on
-- membership in the open ball and its frontier, and this item file has no constructive decidable
-- API for those set memberships.
attribute [local instance] Classical.propDecidable

/-- Helper for Exercise 25.4.3: radial scaling sends the unit sphere to the sphere of radius
`|r|`. -/
private theorem smul_mem_sphere_absRadius
    (r : ℝ) (y : Metric.sphere (0 : State) 1) :
    |r| • (y : State) ∈ Metric.sphere (0 : State) |r| := by
  -- Proof comment: points on the unit sphere have norm `1`, so scaling by `|r|` lands exactly on
  -- the sphere of radius `|r|`.
  rw [Metric.mem_sphere, dist_eq_norm]
  simp [norm_smul]

/-- Helper for Exercise 25.4.3: the radial scaling map from the unit sphere to the sphere of
radius `|r|`. -/
noncomputable def sphereAbsRadiusScale (r : ℝ) :
    Metric.sphere (0 : State) 1 → Metric.sphere (0 : State) |r| :=
  fun y ↦ ⟨|r| • (y : State), smul_mem_sphere_absRadius r y⟩

/-- Helper for Exercise 25.4.3: the boundary reference measure on the sphere spelling of
`frontier (Metric.ball (0 : State) r)`. The earlier item body that fixed this concrete measure was
lost when the file collapsed to a self-importing stub, so the proof frontier keeps the owner
explicit while the analytic normalization is restored later. -/
noncomputable def openBallBoundaryMeasure (r : ℝ) :
    Measure (Metric.sphere (0 : State) |r|) :=
  let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
    ⟨(volume : Measure State).toSphere, inferInstance⟩
  Measure.map
    (sphereAbsRadiusScale r)
    (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1)))

/-- Helper for Exercise 25.4.3: the transported reference measure on the boundary sphere is a
probability measure. -/
theorem openBallBoundaryMeasure_isProbability (r : ℝ) :
    IsProbabilityMeasure
      ((openBallBoundaryMeasure r) : Measure (Metric.sphere (0 : State) |r|)) := by
  let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
    ⟨(volume : Measure State).toSphere, inferInstance⟩
  have hscaleMeas :
      Measurable
        (sphereAbsRadiusScale r :
          Metric.sphere (0 : State) 1 → Metric.sphere (0 : State) |r|) := by
    -- Proof comment: the radial scaling map is continuous, hence measurable.
    let hscaleCont :
        Continuous
          (sphereAbsRadiusScale r :
            Metric.sphere (0 : State) 1 → Metric.sphere (0 : State) |r|) := by
      simpa [sphereAbsRadiusScale] using
        (Continuous.subtype_mk
          (continuous_const.smul continuous_subtype_val)
          (fun y ↦ smul_mem_sphere_absRadius r y))
    exact hscaleCont.measurable
  have hν_ne : (ν : Measure (Metric.sphere (0 : State) 1)) ≠ 0 := by
    -- Proof comment: the unit sphere measure inherited from volume is nonzero because
    -- `State = EuclideanSpace ℝ (Fin d)` is nontrivial under `NeZero d`.
    letI : Nontrivial State := by infer_instance
    change (volume : Measure State).toSphere ≠ 0
    simp [Measure.toSphere_eq_zero_iff]
  have hν_ne_fin : ν ≠ 0 := by
    intro hν0
    apply hν_ne
    simpa [hν0]
  letI : Nontrivial State := by infer_instance
  have hSphereNonempty : Nonempty (Metric.sphere (0 : State) 1) := by
    exact
      @NormedSpace.sphere_nonempty_rclike ℝ inferInstance State
        inferInstance inferInstance inferInstance 1 zero_le_one
  letI : NeZero (ν : Measure (Metric.sphere (0 : State) 1)) := ⟨hν_ne⟩
  have hνprob : IsProbabilityMeasure (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) := by
    -- Proof comment: normalizing a nonzero finite measure by its total mass yields a probability
    -- measure.
    rw [← @FiniteMeasure.toMeasure_normalize_eq_of_nonzero
      (Metric.sphere (0 : State) 1) hSphereNonempty _ ν hν_ne_fin]
    infer_instance
  let _ : IsProbabilityMeasure (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) := hνprob
  -- Proof comment: pushing a probability measure forward along the sphere scaling map preserves
  -- total mass one.
  show IsProbabilityMeasure
    (Measure.map
      (sphereAbsRadiusScale r)
      (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))))
  exact
    (Measure.isProbabilityMeasure_map
      hscaleMeas.aemeasurable :
        IsProbabilityMeasure
          (Measure.map
            (sphereAbsRadiusScale r)
            (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1)))))

/-- Helper for Exercise 25.4.3: the boundary reference measure has total mass `1`. -/
theorem openBallBoundaryMeasure_univ (r : ℝ) :
    ((openBallBoundaryMeasure r) : Measure (Metric.sphere (0 : State) |r|)) Set.univ = 1 := by
  let _ : IsProbabilityMeasure
      ((openBallBoundaryMeasure r) : Measure (Metric.sphere (0 : State) |r|)) :=
    openBallBoundaryMeasure_isProbability r
  -- Proof comment: this is the defining mass-one property of the preceding probability-measure
  -- theorem.
  simpa using
    (measure_univ :
      ((openBallBoundaryMeasure r) : Measure (Metric.sphere (0 : State) |r|)) Set.univ = 1)

/-- Helper for Exercise 25.4.3: the Poisson-kernel density on the radius-`|r|` sphere, written in
the sphere coordinates supplied by `openBallFrontierHomeomorphAbsSupport`. The recovered proof
frontier treats the exact analytic formula as data to be restored together with the missing
Dirichlet-solution proof. -/
noncomputable def openBallPoissonKernel (r : ℝ) (x : State)
    (y : Metric.sphere (0 : State) |r|) : ℝ :=
  (|r| ^ d * (|r| ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ))) /
    (|r| ^ (2 : ℕ) * dist x (y : State) ^ d)

/-- Helper for Exercise 25.4.3: the explicit Poisson-kernel boundary measure in sphere
coordinates. -/
noncomputable def openBallPoissonKernelMeasure (r : ℝ) (x : State) :
    Measure (Metric.sphere (0 : State) |r|) :=
  (openBallBoundaryMeasure r).withDensity
    (fun y ↦ ENNReal.ofReal (openBallPoissonKernel r x y))

/-- Helper for Exercise 25.4.3: the harmonic measure transported from the frontier spelling of the
open ball to the sphere spelling. -/
noncomputable def openBallBoundaryHarmonicMeasure
    (P : State → ProbabilityMeasure Ω) (r : ℝ) (hr : 0 < r)
    (exitValue : Ω → frontier (Metric.ball (0 : State) r))
    (hExitMeas : Measurable exitValue)
    (x : State) (hx : x ∈ Metric.ball (0 : State) r) :
    Measure (Metric.sphere (0 : State) |r|) :=
  Measure.map (openBallFrontierHomeomorphAbsSupport r hr)
    (harmonicMeasure P (Metric.ball (0 : State) r) exitValue hExitMeas ⟨x, hx⟩ :
      Measure (frontier (Metric.ball (0 : State) r)))

/-- Helper for Exercise 25.4.3: pushing the harmonic measure forward along the frontier-to-sphere
transport is the same as pushing the starting law forward along the composed exit map. -/
theorem map_openBallFrontierHomeomorphAbsSupport_harmonicMeasure
    (P : State → ProbabilityMeasure Ω) (r : ℝ) (hr : 0 < r)
    (exitValue : Ω → frontier (Metric.ball (0 : State) r))
    (hExitMeas : Measurable exitValue)
    {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    Measure.map (openBallFrontierHomeomorphAbsSupport r hr)
        (harmonicMeasure P (Metric.ball (0 : State) r) exitValue hExitMeas ⟨x, hx⟩ :
          Measure (frontier (Metric.ball (0 : State) r))) =
      Measure.map
        ((openBallFrontierHomeomorphAbsSupport r hr) ∘ exitValue)
        (P x : Measure Ω) := by
  have hFrontierMeas :
      Measurable
        (openBallFrontierHomeomorphAbsSupport r hr :
          frontier (Metric.ball (0 : State) r) → Metric.sphere (0 : State) |r|) :=
    (openBallFrontierHomeomorphAbsSupport r hr).continuous.measurable
  -- Proof comment: `harmonicMeasure` is already the pushforward of `P x` along `exitValue`, so
  -- the transported harmonic measure is obtained by one further `Measure.map`.
  simpa [harmonicMeasure, Function.comp_def] using
    (Measure.map_map hFrontierMeas hExitMeas : _)

/-- Helper for Exercise 25.4.3: the transported harmonic measure is the pushforward exit law in
sphere coordinates. -/
theorem openBallBoundaryHarmonicMeasure_eq_map_exitLaw
    (P : State → ProbabilityMeasure Ω) (r : ℝ) (hr : 0 < r)
    (exitValue : Ω → frontier (Metric.ball (0 : State) r))
    (hExitMeas : Measurable exitValue)
    (x : State) (hx : x ∈ Metric.ball (0 : State) r) :
    openBallBoundaryHarmonicMeasure
        P r hr exitValue hExitMeas x hx =
      Measure.map
        ((openBallFrontierHomeomorphAbsSupport r hr) ∘ exitValue)
        (P x : Measure Ω) := by
  -- Proof comment: unfold the transported harmonic-measure owner and reuse the already proved
  -- pushforward identity.
  simpa [openBallBoundaryHarmonicMeasure] using
    map_openBallFrontierHomeomorphAbsSupport_harmonicMeasure
      P r hr exitValue hExitMeas hx

/-- Helper for Exercise 25.4.3: a bounded continuous datum on the boundary sphere, transported
back to the frontier spelling of the open ball. -/
noncomputable def openBallFrontierBoundaryDatum
    (r : ℝ) (hr : 0 < r) (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    BoundedContinuousFunction (frontier (Metric.ball (0 : State) r)) ℝ :=
  g.compContinuous
    ⟨openBallFrontierHomeomorphAbsSupport r hr,
      (openBallFrontierHomeomorphAbsSupport r hr).continuous⟩

/-- Helper for Exercise 25.4.3: the transported frontier datum evaluates by composing `g` with the
frontier-to-sphere homeomorphism. -/
@[simp] theorem openBallFrontierBoundaryDatum_apply
    (r : ℝ) (hr : 0 < r) (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ)
    (z : frontier (Metric.ball (0 : State) r)) :
    openBallFrontierBoundaryDatum r hr g z =
      g (openBallFrontierHomeomorphAbsSupport r hr z) := by
  simp [openBallFrontierBoundaryDatum]

/-- Helper for Exercise 25.4.3: the Poisson extension written in sphere coordinates. -/
noncomputable def openBallPoissonExtension (r : ℝ)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    State → ℝ :=
  fun x ↦ ∫ y, g y ∂ openBallPoissonKernelMeasure r x

/-- Helper for Exercise 25.4.3: an interior point of the open ball cannot coincide with a point on
the boundary sphere of radius `|r|`. -/
theorem dist_ne_zero_of_mem_ball_mem_sphere_absRadius
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r)
    (y : Metric.sphere (0 : State) |r|) :
    dist x (y : State) ≠ 0 := by
  -- Proof comment: points in the open ball have norm `< |r|`, while points on the boundary sphere
  -- have norm exactly `|r|`, so they cannot coincide.
  have hxltR : ‖x‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hxlt : ‖x‖ < |r| := by
    simpa [abs_of_pos hr] using hxltR
  have hyEq : ‖(y : State)‖ = |r| := by
    simpa [Metric.mem_sphere, dist_eq_norm] using y.property
  refine dist_ne_zero.mpr ?_
  intro hxy
  have : ‖x‖ = |r| := by
    simpa [hxy] using hyEq
  exact (ne_of_lt hxlt) this

/-- Helper for Exercise 25.4.3: the closed quarter-gap ball around an interior point stays inside
the open ball and remains uniformly separated from the boundary sphere. -/
private theorem closedBallQuarterGap_mem_ball_and_boundarySeparation
    (r : ℝ) (hr : 0 < r) {x0 : State} (hx0 : x0 ∈ Metric.ball (0 : State) r) :
    let δ : ℝ := (r - ‖x0‖) / 4
    0 < δ ∧
      ∀ {x : State}, x ∈ Metric.closedBall x0 δ →
        x ∈ Metric.ball (0 : State) r ∧
          ∀ y : Metric.sphere (0 : State) |r|, δ ≤ dist x (y : State) := by
  let δ : ℝ := (r - ‖x0‖) / 4
  have hx0_lt : ‖x0‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx0
  have hδ_pos : 0 < δ := by
    -- Proof comment: the quarter-gap radius is positive because `x0` lies strictly inside the
    -- open ball.
    dsimp [δ]
    nlinarith
  refine ⟨hδ_pos, ?_⟩
  intro x hx
  have hxx0 : dist x x0 ≤ δ := by
    simpa [Metric.mem_closedBall] using hx
  have hnorm_x_le : ‖x‖ ≤ δ + ‖x0‖ := by
    -- Proof comment: points in the closed quarter-gap ball stay within `δ` of `x0`, so the
    -- triangle inequality controls their distance from the origin.
    have htri : ‖x‖ ≤ ‖x - x0‖ + ‖x0‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_add_le (x - x0) x0)
    calc
      ‖x‖ ≤ ‖x - x0‖ + ‖x0‖ := htri
      _ = dist x x0 + ‖x0‖ := by simp [dist_eq_norm, norm_sub_rev]
      _ ≤ δ + ‖x0‖ := add_le_add hxx0 le_rfl
  have hsum_lt : δ + ‖x0‖ < r := by
    -- Proof comment: the quarter-gap radius is strictly smaller than the full radial gap
    -- `r - ‖x0‖`.
    dsimp [δ]
    nlinarith
  have hx_ball : x ∈ Metric.ball (0 : State) r := by
    -- Proof comment: combining the previous two inequalities keeps the whole closed quarter-gap
    -- ball inside the open ball.
    simpa [Metric.mem_ball, dist_eq_norm] using lt_of_le_of_lt hnorm_x_le hsum_lt
  refine ⟨hx_ball, ?_⟩
  intro y
  have hy_norm : ‖(y : State)‖ = r := by
    simpa [Metric.mem_sphere, dist_eq_norm, abs_of_pos hr] using y.property
  have hradial_lower : r - ‖x0‖ ≤ dist x0 (y : State) := by
    -- Proof comment: the reverse triangle inequality gives the full radial gap from `x0` to the
    -- boundary sphere.
    calc
      r - ‖x0‖ = |r - ‖x0‖| := by
        exact (abs_of_nonneg (sub_nonneg.mpr hx0_lt.le)).symm
      _ = |‖(y : State)‖ - ‖x0‖| := by rw [hy_norm]
      _ ≤ ‖(y : State) - x0‖ := abs_norm_sub_norm_le (y : State) x0
      _ = dist x0 (y : State) := by simp [dist_eq_norm, norm_sub_rev]
  have hxx0' : dist x0 x ≤ δ := by
    simpa [dist_comm] using hxx0
  have htri : dist x0 (y : State) ≤ dist x0 x + dist x (y : State) := by
    simpa [dist_comm, add_comm, add_left_comm, add_assoc] using
      (dist_triangle_right x0 (y : State) x)
  have hgap : 4 * δ ≤ dist x0 (y : State) := by
    -- Proof comment: rewriting the radial gap in terms of `δ` gives the exact separation scale
    -- used later in the buffered-ball estimates.
    dsimp [δ]
    nlinarith
  have hsep : 3 * δ ≤ dist x (y : State) := by
    -- Proof comment: subtract the closed-ball error `dist x0 x ≤ δ` from the full boundary gap.
    nlinarith
  nlinarith

/-- Helper for Exercise 25.4.3: every interior point has a whole neighborhood on which its
distance to a fixed boundary point stays uniformly away from `0`. This isolates the geometric
part of the Poisson-kernel section PDE from the later harmonic-core input. -/
private theorem exists_boundaryDistanceLowerBound_nhds
    (r : ℝ) (hr : 0 < r)
    (y : Metric.sphere (0 : State) |r|)
    {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ {z : State}, z ∈ Metric.ball x ε →
        dist x (y : State) / 2 ≤ dist z (y : State) := by
  let ε : ℝ := dist x (y : State) / 2
  have hxy_pos : 0 < dist x (y : State) := by
    -- Proof comment: the interior point and the boundary point are distinct, so their distance is
    -- a nonzero nonnegative real.
    exact lt_of_le_of_ne dist_nonneg
      (Ne.symm <| dist_ne_zero_of_mem_ball_mem_sphere_absRadius r hr hx y)
  refine ⟨ε, half_pos hxy_pos, ?_⟩
  intro z hz
  have hzx_lt : dist z x < ε := by
    simpa [ε, Metric.mem_ball, dist_comm] using hz
  have htri : dist x (y : State) ≤ dist x z + dist z (y : State) := by
    simpa [dist_comm, add_comm, add_left_comm, add_assoc] using
      (dist_triangle_right x (y : State) z)
  have hzx_le : dist x z ≤ ε := by
    simpa [dist_comm] using hzx_lt.le
  -- Proof comment: a triangle-inequality comparison turns the small neighborhood radius into a
  -- uniform positive lower bound on the boundary distance.
  dsimp [ε] at hzx_lt hzx_le ⊢
  nlinarith

-- Route correction: extracting the Poisson core into a newly imported support module would
-- require a fresh `.olean`, which this proof-stage run is not allowed to build. The stable
-- rewrite-facing kernel API therefore stays in the target file for now, but it is exposed
-- publicly so the next harmonicity pass can reuse it without reopening the transport layer.
/-- Helper for Exercise 25.4.3: the Poisson kernel is nonnegative on the boundary sphere whenever
the start lies inside the open ball. -/
theorem openBallPoissonKernel_nonneg
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r)
    (y : Metric.sphere (0 : State) |r|) :
    0 ≤ openBallPoissonKernel r x y := by
  -- Proof comment: the interior hypothesis gives `‖x‖ < |r|`, so the Poisson numerator is
  -- nonnegative, while the denominator is a product of nonnegative terms.
  have hxlt : ‖x‖ < |r| := by
    simpa [Metric.mem_ball, dist_eq_norm, abs_of_pos hr] using hx
  have hgap : 0 ≤ |r| ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ) := by
    nlinarith [hxlt, norm_nonneg x, abs_nonneg r]
  have hnum : 0 ≤ |r| ^ d * (|r| ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ)) := by
    exact mul_nonneg (by positivity) hgap
  have hden : 0 ≤ |r| ^ (2 : ℕ) * dist x (y : State) ^ d := by
    positivity
  exact div_nonneg hnum hden

/-- Helper for Exercise 25.4.3: for an interior starting point, the sphere-side Poisson kernel is
continuous in the boundary variable. -/
theorem continuous_openBallPoissonKernel
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    Continuous (openBallPoissonKernel r x) := by
  -- Proof comment: the kernel is a constant numerator divided by a continuous denominator that
  -- never vanishes on the boundary sphere.
  have hnum :
      Continuous
        (fun _ : Metric.sphere (0 : State) |r| ↦
          |r| ^ d * (|r| ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ))) :=
    continuous_const
  have hdist :
      Continuous (fun y : Metric.sphere (0 : State) |r| ↦ dist x (y : State)) :=
    continuous_const.dist continuous_subtype_val
  have hden :
      Continuous
        (fun y : Metric.sphere (0 : State) |r| ↦
          |r| ^ (2 : ℕ) * dist x (y : State) ^ d) :=
    continuous_const.mul (hdist.pow d)
  have hr_ne : |r| ≠ 0 := abs_ne_zero.mpr hr.ne'
  have hden_ne :
      ∀ y : Metric.sphere (0 : State) |r|,
        |r| ^ (2 : ℕ) * dist x (y : State) ^ d ≠ 0 := by
    intro y
    refine mul_ne_zero (pow_ne_zero _ hr_ne) ?_
    exact pow_ne_zero _ (dist_ne_zero_of_mem_ball_mem_sphere_absRadius r hr hx y)
  change Continuous
    (fun y : Metric.sphere (0 : State) |r| ↦
      (|r| ^ d * (|r| ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ))) /
        (|r| ^ (2 : ℕ) * dist x (y : State) ^ d))
  exact hnum.div hden hden_ne

/-- Helper for Exercise 25.4.3: for interior start points, the Poisson extension can be rewritten
as an integral against the fixed boundary reference measure with explicit Poisson-kernel weight. -/
theorem openBallPoissonExtension_eq_integral_boundaryMeasure
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    openBallPoissonExtension r g x =
      ∫ y, openBallPoissonKernel r x y * g y ∂ openBallBoundaryMeasure r := by
  -- Proof comment: unfold the `withDensity` measure once, then rewrite the integral using the
  -- explicit nonnegative density on the boundary sphere.
  rw [openBallPoissonExtension, openBallPoissonKernelMeasure]
  have hmeas : Measurable fun y : Metric.sphere (0 : State) |r| ↦
      ENNReal.ofReal (openBallPoissonKernel r x y) :=
    (continuous_openBallPoissonKernel r hr hx).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul
    hmeas (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards with y
  rw [smul_eq_mul]
  simp [ENNReal.toReal_ofReal, openBallPoissonKernel_nonneg r hr hx y]

/-- Helper for Exercise 25.4.3: integrating a bounded continuous sphere datum against the
transported harmonic measure rewrites as the corresponding Brownian exit expectation. -/
theorem integral_openBallBoundaryHarmonicMeasure_eq_exitIntegral
    (P : State → ProbabilityMeasure Ω) (r : ℝ) (hr : 0 < r)
    (exitValue : Ω → frontier (Metric.ball (0 : State) r))
    (hExitMeas : Measurable exitValue)
    (x : State) (hx : x ∈ Metric.ball (0 : State) r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    ∫ y, g y ∂ openBallBoundaryHarmonicMeasure
        P r hr exitValue hExitMeas x hx =
      ∫ ω, openBallFrontierBoundaryDatum r hr g (exitValue ω) ∂ (P x : Measure Ω) := by
  -- Proof comment: first rewrite the transported harmonic measure as the pushforward exit law.
  rw [openBallBoundaryHarmonicMeasure_eq_map_exitLaw P r hr exitValue hExitMeas x hx]
  -- Proof comment: then `integral_map` turns the pushforward integral into the corresponding
  -- expectation of the transported boundary datum.
  rw [MeasureTheory.integral_map
    (((openBallFrontierHomeomorphAbsSupport r hr).continuous.measurable.comp
      hExitMeas).aemeasurable)
    g.continuous.aestronglyMeasurable]
  simp [openBallFrontierBoundaryDatum]

/-- Helper for Exercise 25.4.3: the transported harmonic measure on the boundary sphere is a
probability measure. -/
theorem openBallBoundaryHarmonicMeasure_isProbability
    (P : State → ProbabilityMeasure Ω) (r : ℝ) (hr : 0 < r)
    (exitValue : Ω → frontier (Metric.ball (0 : State) r))
    (hExitMeas : Measurable exitValue)
    (x : State) (hx : x ∈ Metric.ball (0 : State) r) :
    IsProbabilityMeasure
      (openBallBoundaryHarmonicMeasure P r hr exitValue hExitMeas x hx) := by
  have hFrontierMeas :
      Measurable
        (openBallFrontierHomeomorphAbsSupport r hr :
          frontier (Metric.ball (0 : State) r) → Metric.sphere (0 : State) |r|) :=
    (openBallFrontierHomeomorphAbsSupport r hr).continuous.measurable
  let _ :
      IsProbabilityMeasure
        (harmonicMeasure P (Metric.ball (0 : State) r) exitValue hExitMeas ⟨x, hx⟩ :
          Measure (frontier (Metric.ball (0 : State) r))) := by
    infer_instance
  -- Proof comment: the frontier-valued harmonic measure is already a probability measure, and the
  -- frontier-to-sphere homeomorphism preserves total mass one under `Measure.map`.
  simpa [openBallBoundaryHarmonicMeasure] using
    (Measure.isProbabilityMeasure_map
      hFrontierMeas.aemeasurable :
        IsProbabilityMeasure
          (Measure.map
            (openBallFrontierHomeomorphAbsSupport r hr)
            (harmonicMeasure P (Metric.ball (0 : State) r) exitValue hExitMeas ⟨x, hx⟩ :
              Measure (frontier (Metric.ball (0 : State) r)))))

/-- Helper for Exercise 25.4.3: the Poisson-kernel boundary measure is finite for interior start
points. -/
theorem openBallPoissonKernelMeasure_isFinite
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    IsFiniteMeasure (openBallPoissonKernelMeasure r x) := by
  let _ : IsProbabilityMeasure
      ((openBallBoundaryMeasure r) : Measure (Metric.sphere (0 : State) |r|)) :=
    openBallBoundaryMeasure_isProbability r
  letI : CompactSpace (Metric.sphere (0 : State) |r|) :=
    inferInstance
  let f : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨openBallPoissonKernel r x,
        continuous_openBallPoissonKernel r hr hx⟩
  have hInt :
      Integrable (openBallPoissonKernel r x)
        (openBallBoundaryMeasure r) := by
    -- Proof comment: on the compact boundary sphere the Poisson kernel is bounded and continuous,
    -- hence integrable against the finite reference boundary measure.
    simpa [f] using f.integrable (openBallBoundaryMeasure r)
  -- Proof comment: finiteness of the density integral is exactly the hypothesis needed for the
  -- standard `withDensity` finiteness criterion.
  simpa [openBallPoissonKernelMeasure] using
    (MeasureTheory.isFiniteMeasure_withDensity_ofReal hInt.hasFiniteIntegral)

/-- Helper for Exercise 25.4.3: the real total mass of the Poisson-kernel measure is the
boundary integral of the Poisson kernel against the reference sphere measure. -/
theorem openBallPoissonKernelMeasure_real_univ_eq_integral
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    (openBallPoissonKernelMeasure r x).real Set.univ =
      ∫ y, openBallPoissonKernel r x y ∂ openBallBoundaryMeasure r := by
  let _ : IsFiniteMeasure (openBallPoissonKernelMeasure r x) :=
    openBallPoissonKernelMeasure_isFinite r hr hx
  have hConstMass :
      openBallPoissonExtension r
          (BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) 1) x =
        (openBallPoissonKernelMeasure r x).real Set.univ := by
    -- Proof comment: integrating the constant datum `1` against the Poisson-kernel measure
    -- returns exactly the real total mass of that measure.
    simp [openBallPoissonExtension]
  have hConstIntegral :
      openBallPoissonExtension r
          (BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) 1) x =
        ∫ y, openBallPoissonKernel r x y ∂ openBallBoundaryMeasure r := by
    -- Proof comment: the boundary-measure rewrite turns the same constant extension into the raw
    -- kernel integral.
    simpa using
      openBallPoissonExtension_eq_integral_boundaryMeasure
        r hr hx
        (BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) 1)
  -- Proof comment: both expressions compute the constant-one Poisson extension, so they agree.
  calc
    (openBallPoissonKernelMeasure r x).real Set.univ =
        openBallPoissonExtension r
          (BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) 1) x := by
      symm
      exact hConstMass
    _ = ∫ y, openBallPoissonKernel r x y ∂ openBallBoundaryMeasure r :=
      hConstIntegral

/-- Helper for Exercise 25.4.3: at the centered start `x = 0`, the ball Poisson kernel is the
constant function `1` on the boundary sphere. -/
theorem openBallPoissonKernel_zero_eq_one
    (r : ℝ) (hr : 0 < r)
    (y : Metric.sphere (0 : State) |r|) :
    openBallPoissonKernel r 0 y = 1 := by
  have hrabs_ne : |r| ≠ 0 := abs_ne_zero.mpr hr.ne'
  have hyDist : dist (0 : State) (y : State) = |r| := by
    simpa [Metric.mem_sphere, dist_eq_norm] using y.property
  have hpowd_ne : |r| ^ d ≠ 0 := pow_ne_zero _ hrabs_ne
  have hpow2_ne : |r| ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hrabs_ne
  -- Proof comment: on the boundary sphere the denominator is exactly the same radius factor as
  -- the numerator, so the explicit fraction collapses to `1`.
  calc
    openBallPoissonKernel r 0 y
        = (|r| ^ d * |r| ^ (2 : ℕ)) / (|r| ^ (2 : ℕ) * |r| ^ d) := by
      simp [openBallPoissonKernel, hyDist]
    _ = (|r| ^ d * |r| ^ (2 : ℕ)) / (|r| ^ d * |r| ^ (2 : ℕ)) := by
      rw [mul_comm (|r| ^ (2 : ℕ)) (|r| ^ d)]
    _ = 1 := by
      exact div_self (mul_ne_zero hpowd_ne hpow2_ne)

/-- Helper for Exercise 25.4.3: at the centered start `x = 0`, the Poisson-kernel measure is
exactly the normalized boundary reference measure. -/
theorem openBallPoissonKernelMeasure_zero_eq_boundaryMeasure
    (r : ℝ) (hr : 0 < r) :
    openBallPoissonKernelMeasure r (0 : State) = openBallBoundaryMeasure r := by
  have hdensity :
      (fun y : Metric.sphere (0 : State) |r| ↦
        ENNReal.ofReal (openBallPoissonKernel r (0 : State) y)) = fun _ ↦ (1 : ENNReal) := by
    funext y
    simp [openBallPoissonKernel_zero_eq_one r hr y]
  -- Proof comment: once the centered kernel is pointwise `1`, `withDensity` does nothing.
  simp [openBallPoissonKernelMeasure, hdensity]

/-- Helper for Exercise 25.4.3: the scalar normalization identity already holds at the centered
start `x = 0`. -/
theorem openBallPoissonKernelIntegral_eq_one_zero
    (r : ℝ) (hr : 0 < r) :
    ∫ y, openBallPoissonKernel r (0 : State) y ∂ openBallBoundaryMeasure r = 1 := by
  let _ : IsProbabilityMeasure
      ((openBallBoundaryMeasure r) : Measure (Metric.sphere (0 : State) |r|)) :=
    openBallBoundaryMeasure_isProbability r
  -- Proof comment: the centered kernel is identically `1`, so the integral is just the total
  -- mass of the boundary probability measure.
  calc
    ∫ y, openBallPoissonKernel r (0 : State) y ∂ openBallBoundaryMeasure r =
        ∫ y, (1 : ℝ) ∂ openBallBoundaryMeasure r := by
      refine integral_congr_ae ?_
      filter_upwards with y
      simp [openBallPoissonKernel_zero_eq_one r hr y]
    _ = 1 := by
      simp [openBallBoundaryMeasure_univ]

/-- Helper for Exercise 25.4.3: rescaling an interior start point by `|r|⁻¹` moves it into the
unit ball. -/
private theorem invAbsRadius_smul_mem_unitBall
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    (|r|⁻¹ • x : State) ∈ Metric.ball (0 : State) 1 := by
  have hxlt : ‖x‖ < |r| := by
    simpa [Metric.mem_ball, dist_eq_norm, abs_of_pos hr] using hx
  have hrabs_pos : 0 < |r| := abs_pos.mpr hr.ne'
  have hInvNonneg : 0 ≤ |r|⁻¹ := inv_nonneg.mpr (abs_nonneg r)
  simp [Metric.mem_ball, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hInvNonneg]
  have hscaled :
      |r|⁻¹ * ‖x‖ < |r|⁻¹ * |r| :=
    mul_lt_mul_of_pos_left hxlt (inv_pos.mpr hrabs_pos)
  simpa [hrabs_pos.ne', inv_mul_cancel₀] using hscaled

/-- Helper for Exercise 25.4.3: inverse radial scaling sends the sphere of radius `|r|` back to
the unit sphere. -/
private theorem invAbsRadius_smul_mem_unitSphere
    (r : ℝ) (hr : 0 < r) (y : Metric.sphere (0 : State) |r|) :
    (|r|⁻¹ • (y : State) : State) ∈ Metric.sphere (0 : State) 1 := by
  have hrabs_pos : 0 < |r| := abs_pos.mpr hr.ne'
  have hy_norm : ‖(y : State)‖ = |r| := by
    simpa [Metric.mem_sphere, dist_eq_norm] using y.property
  have hnorm :
      ‖(|r|⁻¹ • (y : State) : State)‖ = 1 := by
    calc
      ‖(|r|⁻¹ • (y : State) : State)‖ = ‖|r|⁻¹‖ * ‖(y : State)‖ := by
        rw [norm_smul]
      _ = |r|⁻¹ * |r| := by
        simp [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrabs_pos), hy_norm]
      _ = 1 := by
        field_simp [hrabs_pos.ne']
  -- Proof comment: the norm computation above is exactly the sphere equation at radius `1`.
  simpa [Metric.mem_sphere, dist_eq_norm] using hnorm

/-- Helper for Exercise 25.4.3: after transporting a boundary point by radial scaling, the
distance to the start pulls back by a factor `|r|`. -/
private theorem dist_sphereAbsRadiusScale_eq_absRadius_mul
    (r : ℝ) (hr : 0 < r) (x : State) (u : Metric.sphere (0 : State) 1) :
    dist x (sphereAbsRadiusScale r u : State) =
      |r| * dist (|r|⁻¹ • x : State) (u : State) := by
  have hrabs_ne : |r| ≠ 0 := abs_ne_zero.mpr hr.ne'
  calc
    dist x (sphereAbsRadiusScale r u : State) = ‖x - |r| • (u : State)‖ := by
      simp [sphereAbsRadiusScale, dist_eq_norm]
    _ = ‖|r| • ((|r|⁻¹ • x : State) - (u : State))‖ := by
      congr 1
      simp [smul_sub, hrabs_ne, smul_smul]
    _ = |r| * ‖(|r|⁻¹ • x : State) - (u : State)‖ := by
      rw [norm_smul]
      simp [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg r)]
    _ = |r| * dist (|r|⁻¹ • x : State) (u : State) := by
      simp [dist_eq_norm]

/-- Helper for Exercise 25.4.3: after transporting the boundary variable to the unit sphere, the
ball Poisson kernel takes the canonical unit-ball normal form. -/
private theorem openBallPoissonKernel_sphereAbsRadiusScale_eq_unitSphereKernel
    (r : ℝ) (hr : 0 < r) (x : State) (u : Metric.sphere (0 : State) 1) :
    openBallPoissonKernel r x (sphereAbsRadiusScale r u) =
      (1 - ‖(|r|⁻¹ • x : State)‖ ^ (2 : ℕ)) /
        dist (|r|⁻¹ • x : State) (u : State) ^ d := by
  let ξ : State := |r|⁻¹ • x
  have hrabs_ne : |r| ≠ 0 := abs_ne_zero.mpr hr.ne'
  have hpowd_ne : |r| ^ d ≠ 0 := pow_ne_zero _ hrabs_ne
  have hpow2_ne : |r| ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hrabs_ne
  have hdist :
      dist x (sphereAbsRadiusScale r u : State) ^ d =
        |r| ^ d * dist ξ (u : State) ^ d := by
    rw [dist_sphereAbsRadiusScale_eq_absRadius_mul r hr x u, mul_pow]
  have hnormsq :
      ‖ξ‖ ^ (2 : ℕ) * |r| ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) := by
    calc
      ‖ξ‖ ^ (2 : ℕ) * |r| ^ (2 : ℕ)
          = ((|r|⁻¹ * ‖x‖) ^ (2 : ℕ)) * |r| ^ (2 : ℕ) := by
              dsimp [ξ]
              rw [norm_smul]
              have hInvNonneg : 0 ≤ |r|⁻¹ := inv_nonneg.mpr (abs_nonneg r)
              simp [Real.norm_eq_abs, abs_of_nonneg hInvNonneg]
      _ = ‖x‖ ^ (2 : ℕ) := by
              field_simp [hrabs_ne]
  have hunit :
      |r| ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ) =
        |r| ^ (2 : ℕ) * (1 - ‖ξ‖ ^ (2 : ℕ)) := by
    rw [← hnormsq]
    ring
  calc
    openBallPoissonKernel r x (sphereAbsRadiusScale r u)
        = (|r| ^ d * (|r| ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ))) /
            (|r| ^ (2 : ℕ) * (|r| ^ d * dist ξ (u : State) ^ d)) := by
      rw [openBallPoissonKernel, hdist]
    _ = (|r| ^ d * (|r| ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ))) /
          (|r| ^ d * (|r| ^ (2 : ℕ) * dist ξ (u : State) ^ d)) := by
      have hden :
          |r| ^ (2 : ℕ) * (|r| ^ d * dist ξ (u : State) ^ d) =
            |r| ^ d * (|r| ^ (2 : ℕ) * dist ξ (u : State) ^ d) := by
        ring
      rw [hden]
    _ = (|r| ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ)) /
          (|r| ^ (2 : ℕ) * dist ξ (u : State) ^ d) := by
      rw [mul_div_mul_left _ _ hpowd_ne]
    _ = (|r| ^ (2 : ℕ) * (1 - ‖ξ‖ ^ (2 : ℕ))) /
          (|r| ^ (2 : ℕ) * dist ξ (u : State) ^ d) := by
      rw [hunit]
    _ = (1 - ‖ξ‖ ^ (2 : ℕ)) / dist ξ (u : State) ^ d := by
      rw [mul_div_mul_left _ _ hpow2_ne]

/-- Helper for Exercise 25.4.3: transporting the boundary integral to the unit sphere isolates the
remaining normalization problem in the canonical unit-ball spelling. -/
private theorem openBallPoissonKernelIntegral_eq_unitSphereIntegral
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    ∫ y, openBallPoissonKernel r x y ∂ openBallBoundaryMeasure r =
      let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
        ⟨(volume : Measure State).toSphere, inferInstance⟩
      ∫ u : Metric.sphere (0 : State) 1,
        (1 - ‖(|r|⁻¹ • x : State)‖ ^ (2 : ℕ)) /
          dist (|r|⁻¹ • x : State) (u : State) ^ d ∂
          (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) := by
  let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
    ⟨(volume : Measure State).toSphere, inferInstance⟩
  have hscaleMeas :
      Measurable
        (sphereAbsRadiusScale r :
          Metric.sphere (0 : State) 1 → Metric.sphere (0 : State) |r|) := by
    -- Proof comment: the radial scaling map is continuous, hence measurable.
    let hscaleCont :
        Continuous
          (sphereAbsRadiusScale r :
            Metric.sphere (0 : State) 1 → Metric.sphere (0 : State) |r|) := by
      simpa [sphereAbsRadiusScale] using
        (Continuous.subtype_mk
          (continuous_const.smul continuous_subtype_val)
          (fun y ↦ smul_mem_sphere_absRadius r y))
    exact hscaleCont.measurable
  have hkernelMeas :
      AEStronglyMeasurable
        (openBallPoissonKernel r x)
        (openBallBoundaryMeasure r) :=
    (continuous_openBallPoissonKernel r hr hx).aestronglyMeasurable
  -- Proof comment: `openBallBoundaryMeasure` is a pushforward of the normalized unit-sphere
  -- measure, so `integral_map` rewrites the integral into the canonical unit-ball kernel spelling.
  rw [openBallBoundaryMeasure, MeasureTheory.integral_map hscaleMeas.aemeasurable hkernelMeas]
  refine integral_congr_ae ?_
  filter_upwards with u
  simpa using openBallPoissonKernel_sphereAbsRadiusScale_eq_unitSphereKernel r hr x u

/-- Helper for Exercise 25.4.3: the unnormalized unit-sphere reference measure has total mass
`d * volume (Metric.ball (0 : State) 1)`. -/
private theorem unitSphereBoundaryFiniteMeasure_mass_eq
    (ν : FiniteMeasure (Metric.sphere (0 : State) 1))
    (hν : (ν : Measure (Metric.sphere (0 : State) 1)) = (volume : Measure State).toSphere) :
    (ν : Measure (Metric.sphere (0 : State) 1)) Set.univ =
      d * volume (Metric.ball (0 : State) 1) := by
  -- Proof comment: this is the ambient `toSphere` total-mass formula specialized to
  -- `State = EuclideanSpace ℝ (Fin d)`.
  rw [hν]
  simpa [finrank_euclideanSpace] using
    (Measure.toSphere_apply_univ (μ := (volume : Measure State)))

/-- Helper for Exercise 25.4.3: evaluating a normalized finite measure on a set is the ambient
inverse total mass times the original set mass. -/
private theorem finiteMeasureNormalize_apply_eq_measureUnivInv_mul
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μ : FiniteMeasure α) (hμ : μ ≠ 0) (s : Set α) :
    (μ.normalize : Measure α) s = ((μ : Measure α) Set.univ)⁻¹ * (μ : Measure α) s := by
  have hmass_ne : μ.mass ≠ 0 := (FiniteMeasure.mass_nonzero_iff μ).2 hμ
  have hmeasure_univ : ((μ : Measure α) Set.univ) = (μ.mass : ENNReal) := by
    simpa using (FiniteMeasure.ennreal_mass (μ := μ)).symm
  -- Proof comment: rewrite the normalized finite measure through `μ.normalize`, then express the
  -- normalization constant in the ambient `Measure` spelling via `Set.univ` before evaluating at
  -- the set `s`.
  have hnorm :
      (μ.normalize : Measure α) = ((μ : Measure α) Set.univ)⁻¹ • (μ : Measure α) := by
    rw [μ.toMeasure_normalize_eq_of_nonzero hμ]
    ext t ht
    rw [Measure.smul_apply, Measure.smul_apply]
    calc
      ((μ.mass⁻¹ : NNReal) : ENNReal) * (μ : Measure α) t =
          ((μ.mass : ENNReal)⁻¹) * (μ : Measure α) t := by
            rw [ENNReal.coe_inv hmass_ne]
      _ = ((μ : Measure α) Set.univ)⁻¹ * (μ : Measure α) t := by
            rw [hmeasure_univ]
  exact congrArg (fun ν : Measure α ↦ ν s) hnorm

/-- Helper for Exercise 25.4.3: the normalized unit-sphere boundary law is explicitly the inverse
of `d * volume (Metric.ball (0 : State) 1)` times the raw `toSphere` measure. -/
private theorem unitSphereNormalizedBoundaryMeasure_eq
    (ν : FiniteMeasure (Metric.sphere (0 : State) 1))
    (hν : (ν : Measure (Metric.sphere (0 : State) 1)) = (volume : Measure State).toSphere) :
    ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1)) =
      (d * volume (Metric.ball (0 : State) 1))⁻¹ • (volume : Measure State).toSphere := by
  letI : Nontrivial State := by infer_instance
  letI : Nonempty (Metric.sphere (0 : State) 1) := by
    exact
      @NormedSpace.sphere_nonempty_rclike ℝ inferInstance State
        inferInstance inferInstance inferInstance 1 zero_le_one
  have hν_measure_ne : (ν : Measure (Metric.sphere (0 : State) 1)) ≠ 0 := by
    rw [hν]
    exact Measure.toSphere_ne_zero (μ := (volume : Measure State))
  have hν_ne : ν ≠ 0 := by
    intro hν0
    exact hν_measure_ne (by simpa [hν0])
  have hmassMeasure :
      (ν : Measure (Metric.sphere (0 : State) 1)) Set.univ =
        d * volume (Metric.ball (0 : State) 1) :=
    unitSphereBoundaryFiniteMeasure_mass_eq ν hν
  -- Proof comment: after rewriting both the owner measure and the normalization constant, the two
  -- scalar multiples agree on every measurable set, but now the normalization scalar is exposed
  -- through `ν.normalize` instead of a fragile coercion comparison.
  ext s hs
  calc
    (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) s
        = ((ν : Measure (Metric.sphere (0 : State) 1)) Set.univ)⁻¹ *
            (ν : Measure (Metric.sphere (0 : State) 1)) s := by
            -- Proof comment: the new normalize-apply bridge rewrites the left owner in the exact
            -- ambient scalar normal form used by the mass computation.
            rw [← ν.toMeasure_normalize_eq_of_nonzero hν_ne]
            exact finiteMeasureNormalize_apply_eq_measureUnivInv_mul ν hν_ne s
    _ = (d * volume (Metric.ball (0 : State) 1))⁻¹ *
          (volume : Measure State).toSphere s := by
            rw [hmassMeasure, hν]
    _ = (((d * volume (Metric.ball (0 : State) 1))⁻¹ •
          (volume : Measure State).toSphere) s) := by
            rw [Measure.smul_apply]
            simp [smul_eq_mul]

/-- Helper for Exercise 25.4.3: the remaining normalization blocker is the canonical mass-one
statement for the unit-ball Poisson kernel on the normalized unit-sphere measure. -/
private theorem unitSphereFinOne_pos :
    (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) :
      EuclideanSpace ℝ (Fin 1)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
  -- Proof comment: the positive coordinate vector has Euclidean norm `1` in the one-dimensional
  -- Euclidean space.
  rw [Metric.mem_sphere, dist_eq_norm]
  simpa using (EuclideanSpace.norm_single (0 : Fin 1) (1 : ℝ))

/-- Helper for Exercise 25.4.3: the negative unit vector belongs to the one-dimensional unit
sphere. -/
private theorem unitSphereFinOne_neg :
    (EuclideanSpace.single (0 : Fin 1) (-1 : ℝ) :
      EuclideanSpace ℝ (Fin 1)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
  -- Proof comment: the negative coordinate vector has the same norm `1` as the positive one.
  rw [Metric.mem_sphere, dist_eq_norm]
  simpa using (EuclideanSpace.norm_single (0 : Fin 1) (-1 : ℝ))

/-- Helper for Exercise 25.4.3: every point on the one-dimensional unit sphere is one of the two
endpoints `±1`. -/
private theorem unitSphereFinOne_eq_pos_or_neg
    (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    u =
        ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), unitSphereFinOne_pos⟩ ∨
      u =
        ⟨EuclideanSpace.single (0 : Fin 1) (-1 : ℝ), unitSphereFinOne_neg⟩ := by
  have hu_norm : ‖(u : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using u.property
  have hu_coord_sq : (u : EuclideanSpace ℝ (Fin 1)) 0 ^ (2 : ℕ) = 1 := by
    have hu_sq :
        ‖(u : EuclideanSpace ℝ (Fin 1))‖ ^ (2 : ℕ) = 1 := by
      simpa [hu_norm] using congrArg (fun t : ℝ ↦ t ^ (2 : ℕ)) hu_norm
    have hnorm_sq :
        ‖(u : EuclideanSpace ℝ (Fin 1))‖ ^ (2 : ℕ) =
          (u : EuclideanSpace ℝ (Fin 1)) 0 ^ (2 : ℕ) := by
      simpa using (EuclideanSpace.real_norm_sq_eq (u : EuclideanSpace ℝ (Fin 1)))
    exact hnorm_sq.symm.trans hu_sq
  have hu_coord :
      (u : EuclideanSpace ℝ (Fin 1)) 0 = 1 ∨
        (u : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
    have hfac :
        (((u : EuclideanSpace ℝ (Fin 1)) 0 - 1) *
            ((u : EuclideanSpace ℝ (Fin 1)) 0 + 1)) = 0 := by
      nlinarith [hu_coord_sq]
    rcases mul_eq_zero.mp hfac with hleft | hright
    · left
      linarith
    · right
      linarith
  rcases hu_coord with hu_coord | hu_coord
  · left
    ext i
    fin_cases i
    simp [hu_coord]
  · right
    ext i
    fin_cases i
    simp [hu_coord]

/-- Helper for Exercise 25.4.3: in dimension `1`, the unit-ball Poisson kernel at the positive
endpoint simplifies to `1 + ξ₀`. -/
private theorem unitSphereKernel_eval_pos_finOne
    (ξ : EuclideanSpace ℝ (Fin 1))
    (hξ : ξ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    (1 - ‖ξ‖ ^ (2 : ℕ)) /
        dist ξ
          (⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), unitSphereFinOne_pos⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) =
      1 + ξ 0 := by
  have hξ_norm : ‖ξ‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hξ
  have hcoord_le : |ξ 0| ≤ ‖ξ‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ (0 : Fin 1)
  have hcoord_lt : ξ 0 < 1 := lt_of_le_of_lt (le_trans (le_abs_self _) hcoord_le) hξ_norm
  have hdist :
      dist ξ
          (⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), unitSphereFinOne_pos⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) =
        1 - ξ 0 := by
    rw [dist_eq_norm]
    have hsub :
        ξ -
            (⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), unitSphereFinOne_pos⟩ :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) =
          EuclideanSpace.single (0 : Fin 1) (ξ 0 - 1) := by
      ext i
      fin_cases i
      simp
    rw [hsub, EuclideanSpace.norm_single]
    have hnonpos : ξ 0 - 1 ≤ 0 := by linarith
    rw [Real.norm_eq_abs, abs_of_nonpos hnonpos]
    ring
  have hnorm_sq :
      ‖ξ‖ ^ (2 : ℕ) = ξ 0 ^ (2 : ℕ) := by
    have : ‖ξ‖ ^ (2 : ℕ) = ∑ i : Fin 1, ξ i ^ (2 : ℕ) := by
      simpa using (EuclideanSpace.real_norm_sq_eq ξ)
    simpa using this
  have hden_ne : 1 - ξ 0 ≠ 0 := by
    linarith
  -- Proof comment: in one dimension, the positive boundary point contributes the textbook factor
  -- `(1 - ξ²) / (1 - ξ) = 1 + ξ`.
  calc
    (1 - ‖ξ‖ ^ (2 : ℕ)) /
        dist ξ
          (⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), unitSphereFinOne_pos⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) =
      (1 - ξ 0 ^ (2 : ℕ)) / (1 - ξ 0) := by
        rw [hdist, hnorm_sq]
    _ = 1 + ξ 0 := by
        field_simp [hden_ne]
        ring

/-- Helper for Exercise 25.4.3: in dimension `1`, the unit-ball Poisson kernel at the negative
endpoint simplifies to `1 - ξ₀`. -/
private theorem unitSphereKernel_eval_neg_finOne
    (ξ : EuclideanSpace ℝ (Fin 1))
    (hξ : ξ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    (1 - ‖ξ‖ ^ (2 : ℕ)) /
        dist ξ
          (⟨EuclideanSpace.single (0 : Fin 1) (-1 : ℝ), unitSphereFinOne_neg⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) =
      1 - ξ 0 := by
  have hξ_norm : ‖ξ‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hξ
  have hcoord_le : |ξ 0| ≤ ‖ξ‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ (0 : Fin 1)
  have hcoord_gt : -1 < ξ 0 := by
    have habs_lt : |ξ 0| < 1 := lt_of_le_of_lt hcoord_le hξ_norm
    exact (abs_lt.mp habs_lt).1
  have hdist :
      dist ξ
          (⟨EuclideanSpace.single (0 : Fin 1) (-1 : ℝ), unitSphereFinOne_neg⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) =
        ξ 0 + 1 := by
    rw [dist_eq_norm]
    have hsub :
        ξ -
            (⟨EuclideanSpace.single (0 : Fin 1) (-1 : ℝ), unitSphereFinOne_neg⟩ :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) =
          EuclideanSpace.single (0 : Fin 1) (ξ 0 + 1) := by
      ext i
      fin_cases i
      simp
    rw [hsub, EuclideanSpace.norm_single]
    have hnonneg : 0 ≤ ξ 0 + 1 := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hnorm_sq :
      ‖ξ‖ ^ (2 : ℕ) = ξ 0 ^ (2 : ℕ) := by
    have : ‖ξ‖ ^ (2 : ℕ) = ∑ i : Fin 1, ξ i ^ (2 : ℕ) := by
      simpa using (EuclideanSpace.real_norm_sq_eq ξ)
    simpa using this
  have hden_ne : ξ 0 + 1 ≠ 0 := by
    linarith
  -- Proof comment: the negative endpoint gives the companion factor
  -- `(1 - ξ²) / (1 + ξ) = 1 - ξ`.
  calc
    (1 - ‖ξ‖ ^ (2 : ℕ)) /
        dist ξ
          (⟨EuclideanSpace.single (0 : Fin 1) (-1 : ℝ), unitSphereFinOne_neg⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) =
      (1 - ξ 0 ^ (2 : ℕ)) / (ξ 0 + 1) := by
        rw [hdist, hnorm_sq]
    _ = 1 - ξ 0 := by
        field_simp [hden_ne]
        ring

/-- Helper for Exercise 25.4.3: the positive endpoint of the one-dimensional unit sphere. -/
private def unitSphereFinOnePosPoint : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), unitSphereFinOne_pos⟩

/-- Helper for Exercise 25.4.3: the negative endpoint of the one-dimensional unit sphere. -/
private def unitSphereFinOneNegPoint : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨EuclideanSpace.single (0 : Fin 1) (-1 : ℝ), unitSphereFinOne_neg⟩

/-- Helper for Exercise 25.4.3: the two endpoints of `S⁰` are distinct. -/
private theorem unitSphereFinOnePosPoint_ne_negPoint :
    unitSphereFinOnePosPoint ≠ unitSphereFinOneNegPoint := by
  -- Proof comment: the endpoint coordinates are `1` and `-1`, so they cannot coincide.
  intro h
  have h0 :
      ((unitSphereFinOnePosPoint : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
          EuclideanSpace ℝ (Fin 1)) 0 =
        ((unitSphereFinOneNegPoint : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
          EuclideanSpace ℝ (Fin 1)) 0 := by
    simpa using congrArg
      (fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ↦
        ((u : EuclideanSpace ℝ (Fin 1)) 0)) h
  simp [unitSphereFinOnePosPoint, unitSphereFinOneNegPoint] at h0
  linarith

/-- Helper for Exercise 25.4.3: every point on `S⁰` is one of the named endpoint atoms. -/
private theorem unitSphereFinOne_eq_posPoint_or_negPoint
    (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    u = unitSphereFinOnePosPoint ∨ u = unitSphereFinOneNegPoint := by
  -- Proof comment: this is the earlier endpoint dichotomy rewritten in the reusable point names.
  simpa [unitSphereFinOnePosPoint, unitSphereFinOneNegPoint] using unitSphereFinOne_eq_pos_or_neg u

/-- Helper for Exercise 25.4.3: on `EuclideanSpace ℝ (Fin 1)`, the Euclidean norm is the absolute
value of the unique coordinate. -/
private theorem euclideanFinOne_norm_eq_absCoord
    (x : EuclideanSpace ℝ (Fin 1)) :
    ‖x‖ = |x 0| := by
  -- Proof comment: in one dimension the Euclidean norm is the square root of a one-term sum, so
  -- it collapses to the absolute value of the unique coordinate.
  calc
    ‖x‖ = Real.sqrt (∑ i : Fin 1, ‖x i‖ ^ (2 : ℕ)) := EuclideanSpace.norm_eq x
    _ = Real.sqrt (|x 0| ^ (2 : ℕ)) := by simp
    _ = |x 0| := by simpa using Real.sqrt_sq_eq_abs (x 0)

/-- Helper for Exercise 25.4.3: in dimension `1`, the unique coordinate projection is harmonic
because its second derivative vanishes identically. -/
private theorem firstCoordinate_harmonicAt_finOne
    (z : EuclideanSpace ℝ (Fin 1)) :
    InnerProductSpace.HarmonicAt (fun w : EuclideanSpace ℝ (Fin 1) ↦ w 0) z := by
  let p : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    show EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ from
      EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0
  have hp : (fun w : EuclideanSpace ℝ (Fin 1) ↦ w 0) = p := by
    funext w
    simp [p]
  rw [hp]
  refine ⟨p.contDiff.contDiffAt, ?_⟩
  have hiter2 : iteratedFDeriv ℝ 2 p = 0 := by
    have hfd : fderiv ℝ (⇑p) = fun _ : EuclideanSpace ℝ (Fin 1) ↦ p := by
      funext x
      exact ContinuousLinearMap.fderiv (f := p) (x := x)
    funext x
    ext m
    rw [iteratedFDeriv_two_apply, hfd, fderiv_const_apply]
    simp
  filter_upwards with x
  -- Proof comment: a linear functional has zero second derivative everywhere, so its Laplacian
  -- vanishes pointwise.
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hiter2]
  simp

/-- Helper for Exercise 25.4.3: the unique coordinate on `EuclideanSpace ℝ (Fin 1)` transports
Lebesgue volume to the ordinary real line. -/
private def euclideanFinOneCoord :
    EuclideanSpace ℝ (Fin 1) → ℝ :=
  (MeasurableEquiv.funUnique (Fin 1) ℝ) ∘ WithLp.ofLp

/-- Helper for Exercise 25.4.3: the unique-coordinate transport preserves volume in dimension
`1`. -/
private theorem euclideanFinOneCoord_measurePreserving :
    MeasurePreserving euclideanFinOneCoord
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) (volume : Measure ℝ) := by
  -- Proof comment: compose the canonical `EuclideanSpace ≃ Fin 1 → ℝ` volume-preserving map with
  -- the unique-coordinate equivalence on `Fin 1 → ℝ`.
  simpa [euclideanFinOneCoord] using
    (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).comp
      (PiLp.volume_preserving_ofLp (Fin 1))

/-- Helper for Exercise 25.4.3: the one-dimensional unit ball has Lebesgue volume `2`. -/
private theorem unitBallVolume_finOne :
    (volume : Measure (EuclideanSpace ℝ (Fin 1)))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) = 2 := by
  have hp := euclideanFinOneCoord_measurePreserving
  have hball :
      euclideanFinOneCoord ⁻¹' Set.Ioo (-1 : ℝ) 1 =
        Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    -- Proof comment: under the unique-coordinate chart, the Euclidean unit ball is exactly the
    -- interval `(-1, 1)`.
    ext x
    constructor
    · intro hx
      have hcoord : |x 0| < 1 := by
        exact abs_lt.mpr (by
          simpa [euclideanFinOneCoord, Set.mem_preimage, Set.mem_Ioo] using hx)
      simpa [Metric.mem_ball, dist_eq_norm, euclideanFinOne_norm_eq_absCoord] using hcoord
    · intro hx
      have hcoord : |x 0| < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm, euclideanFinOne_norm_eq_absCoord] using hx
      exact by
        simpa [euclideanFinOneCoord, Set.mem_preimage, Set.mem_Ioo] using abs_lt.mp hcoord
  have hmap :=
      congrArg (fun μ : Measure ℝ ↦ μ (Set.Ioo (-1 : ℝ) 1)) hp.map_eq
  -- Proof comment: evaluate the mapped volume on `(-1,1)` and read off the real interval volume.
  calc
    (volume : Measure (EuclideanSpace ℝ (Fin 1)))
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1)
        = Measure.map euclideanFinOneCoord
            (volume : Measure (EuclideanSpace ℝ (Fin 1))) (Set.Ioo (-1 : ℝ) 1) := by
            rw [MeasureTheory.Measure.map_apply hp.measurable measurableSet_Ioo]
            simp [hball]
    _ = (volume : Measure ℝ) (Set.Ioo (-1 : ℝ) 1) := hmap
    _ = 2 := by
          norm_num [Real.volume_Ioo]

/-- Helper for Exercise 25.4.3: the positive endpoint cone on `S⁰` is the preimage of `(0,1)`
under the unique-coordinate chart. -/
private theorem unitSphereFinOnePosCone_preimage :
    euclideanFinOneCoord ⁻¹' Set.Ioo (0 : ℝ) 1 =
      Set.Ioo (0 : ℝ) 1 •
        ({((unitSphereFinOnePosPoint :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
            EuclideanSpace ℝ (Fin 1))} :
          Set (EuclideanSpace ℝ (Fin 1))) := by
  -- Proof comment: every positive-coordinate point in the one-dimensional unit ball lies on the
  -- positive ray through the endpoint `+1`, and conversely every such ray point has positive
  -- coordinate.
  ext x
  constructor
  · intro hx
    refine ⟨x 0, ?_,
      ((unitSphereFinOnePosPoint :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
        EuclideanSpace ℝ (Fin 1)),
      by simp, ?_⟩
    · simpa [euclideanFinOneCoord, Set.mem_Ioo] using hx
    · ext i
      fin_cases i
      simp [unitSphereFinOnePosPoint]
  · rintro ⟨t, ht, b, hb, hbx⟩
    have hb' :
        b =
          ((unitSphereFinOnePosPoint :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
            EuclideanSpace ℝ (Fin 1)) := by
      simpa using hb
    subst hb'
    rw [← hbx]
    simpa [euclideanFinOneCoord, unitSphereFinOnePosPoint, Set.mem_Ioo] using ht

/-- Helper for Exercise 25.4.3: the negative endpoint cone on `S⁰` is the preimage of `(-1,0)`
under the unique-coordinate chart. -/
private theorem unitSphereFinOneNegCone_preimage :
    euclideanFinOneCoord ⁻¹' Set.Ioo (-1 : ℝ) 0 =
      Set.Ioo (0 : ℝ) 1 •
        ({((unitSphereFinOneNegPoint :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
            EuclideanSpace ℝ (Fin 1))} :
          Set (EuclideanSpace ℝ (Fin 1))) := by
  -- Proof comment: negative-coordinate points in the unit ball lie on the ray through `-1`, and
  -- the same chart identifies that ray with `(-1,0)`.
  ext x
  constructor
  · intro hx
    have hx' : -1 < x 0 ∧ x 0 < 0 := by
      simpa [euclideanFinOneCoord, Set.mem_preimage, Set.mem_Ioo] using hx
    have ht : 0 < -x 0 ∧ -x 0 < 1 := by
      constructor <;> linarith [hx'.1, hx'.2]
    refine ⟨-x 0, ht,
      ((unitSphereFinOneNegPoint :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
        EuclideanSpace ℝ (Fin 1)),
      by simp, ?_⟩
    ext i
    fin_cases i
    simp [unitSphereFinOneNegPoint]
  · rintro ⟨t, ht, b, hb, hbx⟩
    have hb' :
        b =
          ((unitSphereFinOneNegPoint :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
            EuclideanSpace ℝ (Fin 1)) := by
      simpa using hb
    subst hb'
    rw [← hbx]
    have hx' : -1 < -t ∧ -t < 0 := by
      constructor <;> linarith [ht.1, ht.2]
    simpa [euclideanFinOneCoord, unitSphereFinOneNegPoint, Set.mem_preimage, Set.mem_Ioo]
      using hx'

/-- Helper for Exercise 25.4.3: the unique-coordinate chart converts one-dimensional Euclidean
volume of interval preimages into ordinary interval length. -/
private theorem euclideanFinOne_intervalPreimage_volume_eq
    (a b : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 1)))
        (euclideanFinOneCoord ⁻¹' Set.Ioo a b) =
      (volume : Measure ℝ) (Set.Ioo a b) := by
  have hp := euclideanFinOneCoord_measurePreserving
  -- Proof comment: evaluate the pushforward equality of the volume-preserving chart on the test
  -- interval `Ioo a b`.
  simpa [MeasureTheory.Measure.map_apply hp.measurable measurableSet_Ioo] using
    congrArg (fun μ : Measure ℝ ↦ μ (Set.Ioo a b)) hp.map_eq

/-- Helper for Exercise 25.4.3: the unnormalized `toSphere` measure of `S⁰` assigns mass `1` to
the positive endpoint. -/
private theorem unitSphereFinOnePos_toSphere_singleton :
    ((volume : Measure (EuclideanSpace ℝ (Fin 1))).toSphere)
      {unitSphereFinOnePosPoint} = 1 := by
  have hcone :
      (volume : Measure (EuclideanSpace ℝ (Fin 1)))
          (Set.Ioo (0 : ℝ) 1 •
            ({((unitSphereFinOnePosPoint :
                Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
                EuclideanSpace ℝ (Fin 1))} :
              Set (EuclideanSpace ℝ (Fin 1)))) = 1 := by
    -- Proof comment: the positive endpoint cone is just the interval `(0,1)` in the coordinate
    -- chart, whose volume is `1`.
    simpa [unitSphereFinOnePosCone_preimage] using
      euclideanFinOne_intervalPreimage_volume_eq 0 1
  rw [MeasureTheory.Measure.toSphere_apply'
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 1))))]
  · simpa [Set.image_singleton] using hcone
  · simp

/-- Helper for Exercise 25.4.3: the unnormalized `toSphere` measure of `S⁰` assigns mass `1` to
the negative endpoint. -/
private theorem unitSphereFinOneNeg_toSphere_singleton :
    ((volume : Measure (EuclideanSpace ℝ (Fin 1))).toSphere)
      {unitSphereFinOneNegPoint} = 1 := by
  have hcone :
      (volume : Measure (EuclideanSpace ℝ (Fin 1)))
          (Set.Ioo (0 : ℝ) 1 •
            ({((unitSphereFinOneNegPoint :
                Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
                EuclideanSpace ℝ (Fin 1))} :
              Set (EuclideanSpace ℝ (Fin 1)))) = 1 := by
    -- Proof comment: the negative endpoint cone is the chart pullback of `(-1,0)`, which also
    -- has length `1`.
    have hvol := euclideanFinOne_intervalPreimage_volume_eq (-1) 0
    simpa [unitSphereFinOneNegCone_preimage, Real.volume_Ioo] using hvol
  rw [MeasureTheory.Measure.toSphere_apply'
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 1))))]
  · simpa [Set.image_singleton] using hcone
  · simp

/-- Helper for Exercise 25.4.3: the one-dimensional unit sphere is countable because it has only
the two endpoint atoms `±1`. -/
private theorem unitSphereFinOne_countable :
    Countable (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
  have hUniv :
      (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) =
        insert unitSphereFinOnePosPoint {unitSphereFinOneNegPoint} := by
    ext u
    constructor
    · intro _
      rcases unitSphereFinOne_eq_posPoint_or_negPoint u with rfl | rfl <;> simp
    · intro _
      simp
  have hCount :
      (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).Countable := by
    simpa [hUniv] using
      (Set.Countable.insert unitSphereFinOnePosPoint
        (Set.countable_singleton unitSphereFinOneNegPoint))
  exact Set.countable_univ_iff.mp hCount

/-- Helper for Exercise 25.4.3: the unnormalized `toSphere` measure on `S⁰` is exactly the sum of
the two endpoint dirac masses. -/
private theorem unitSphereFinOne_toSphere_eq_diracSum :
    ((volume : Measure (EuclideanSpace ℝ (Fin 1))).toSphere) =
      Measure.dirac unitSphereFinOnePosPoint +
        Measure.dirac unitSphereFinOneNegPoint := by
  letI : Countable (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    unitSphereFinOne_countable
  apply Measure.ext_of_singleton
  intro u
  rcases unitSphereFinOne_eq_posPoint_or_negPoint u with rfl | rfl
  · -- Proof comment: at the positive endpoint, `toSphere` has mass `1`, and only the positive
    -- dirac contributes on the right-hand side.
    simp [unitSphereFinOnePos_toSphere_singleton, unitSphereFinOnePosPoint_ne_negPoint]
  · -- Proof comment: the negative endpoint computation is the symmetric singleton identity.
    simp [unitSphereFinOneNeg_toSphere_singleton, unitSphereFinOnePosPoint_ne_negPoint]

/-- Helper for Exercise 25.4.3: the canonical finite `toSphere` measure on the one-dimensional
unit sphere. -/
private noncomputable def unitSphereFinOneBoundaryFiniteMeasure :
    FiniteMeasure (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  ⟨(volume : Measure (EuclideanSpace ℝ (Fin 1))).toSphere, inferInstance⟩

/-- Helper for Exercise 25.4.3: the normalized `S⁰` scalar weight `(1 / 2)` written in `NNReal`
matches the endpoint weight `(2 : ENNReal)⁻¹` used by the Dirac-sum normal form. -/
private theorem ennrealHalf_eq_invTwo :
    (((1 / 2 : NNReal) : ENNReal)) = (2 : ENNReal)⁻¹ := by
  -- Proof comment: freeze the `NNReal`-to-`ENNReal` cast once so the singleton-mass comparison
  -- stays in the exact scalar normal form used by the normalized boundary measure.
  norm_num

/-- Helper for Exercise 25.4.3: normalizing the `S⁰` boundary measure turns the two unit endpoint
atoms into the equally weighted reference law. -/
private theorem unitSphereFinOne_normalizedBoundaryMeasure_eq_halfDiracSum :
    (unitSphereFinOneBoundaryFiniteMeasure.mass⁻¹ •
      (unitSphereFinOneBoundaryFiniteMeasure :
        Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))) =
      ((2 : ENNReal)⁻¹) •
        (Measure.dirac unitSphereFinOnePosPoint +
          Measure.dirac unitSphereFinOneNegPoint) := by
  have hMass :
      unitSphereFinOneBoundaryFiniteMeasure.mass = 2 := by
    apply ENNReal.coe_injective
    -- Proof comment: the unnormalized boundary law is exactly the sum of the two endpoint diracs,
    -- so its total mass is `1 + 1 = 2`.
    simpa [FiniteMeasure.ennreal_mass] using
      (show
        ((((unitSphereFinOneBoundaryFiniteMeasure :
            Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))) Set.univ) :
            ENNReal) = 2 by
          simpa [unitSphereFinOneBoundaryFiniteMeasure, unitSphereFinOne_toSphere_eq_diracSum]
            using (show
              ((((Measure.dirac unitSphereFinOnePosPoint +
                  Measure.dirac unitSphereFinOneNegPoint) :
                  Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) Set.univ) :
                  ENNReal) = 2 by
                norm_num))
  have hDiracMass :
      (FiniteMeasure.mass
        (⟨Measure.dirac unitSphereFinOnePosPoint + Measure.dirac unitSphereFinOneNegPoint,
          inferInstance⟩ :
          FiniteMeasure (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))) = 2 := by
    simpa [unitSphereFinOneBoundaryFiniteMeasure, unitSphereFinOne_toSphere_eq_diracSum] using hMass
  letI : Countable (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    unitSphereFinOne_countable
  -- Proof comment: the one-dimensional sphere has only the two endpoint atoms, so equality of the
  -- normalized measures reduces to comparing their singleton masses.
  apply Measure.ext_of_singleton
  intro u
  rcases unitSphereFinOne_eq_posPoint_or_negPoint u with rfl | rfl
  · simp [Measure.smul_apply, unitSphereFinOneBoundaryFiniteMeasure,
      unitSphereFinOne_toSphere_eq_diracSum, hDiracMass, ennrealHalf_eq_invTwo, smul_eq_mul,
      unitSphereFinOnePosPoint_ne_negPoint]
    -- Proof comment: the remaining singleton mass is the trivial scalar identity
    -- `((2 : ENNReal)⁻¹) * 1 = (2 : ENNReal)⁻¹`.
    simpa [ENNReal.smul_def]
  · simp [Measure.smul_apply, unitSphereFinOneBoundaryFiniteMeasure,
      unitSphereFinOne_toSphere_eq_diracSum, hDiracMass, ennrealHalf_eq_invTwo, smul_eq_mul,
      unitSphereFinOnePosPoint_ne_negPoint]
    -- Proof comment: the negative endpoint has the same singleton mass computation.
    simpa [ENNReal.smul_def]

/-- Helper for Exercise 25.4.3: in dimension `1`, the normalized unit-sphere Poisson kernel
integral is the average of the two endpoint evaluations, hence equals `1`. -/
private theorem unitSpherePoissonKernelIntegral_eq_one_finOne
    (ξ : EuclideanSpace ℝ (Fin 1))
    (hξ : ξ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    ∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
      (1 - ‖ξ‖ ^ (2 : ℕ)) / dist ξ (u : EuclideanSpace ℝ (Fin 1)) ^ (1 : ℕ) ∂
        (unitSphereFinOneBoundaryFiniteMeasure.mass⁻¹ •
          (unitSphereFinOneBoundaryFiniteMeasure :
            Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))) = 1 := by
  -- Route correction: keep the one-dimensional branch isolated from the high-dimensional
  -- scalar-pushforward refactor. This should still be proved by rewriting the normalized `S⁰`
  -- boundary law as the half-sum of the two endpoint dirac masses and evaluating both atoms.
  let f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 → ℝ :=
    fun u ↦ (1 - ‖ξ‖ ^ (2 : ℕ)) / dist ξ (u : EuclideanSpace ℝ (Fin 1)) ^ (1 : ℕ)
  have hposEval : f unitSphereFinOnePosPoint = 1 + ξ 0 := by
    -- Proof comment: the positive endpoint contribution is the textbook factor `1 + ξ₀`.
    simpa [f, unitSphereFinOnePosPoint] using unitSphereKernel_eval_pos_finOne ξ hξ
  have hnegEval : f unitSphereFinOneNegPoint = 1 - ξ 0 := by
    -- Proof comment: the negative endpoint contributes the symmetric factor `1 - ξ₀`.
    simpa [f, unitSphereFinOneNegPoint] using unitSphereKernel_eval_neg_finOne ξ hξ
  have hposDirac : Integrable f (Measure.dirac unitSphereFinOnePosPoint) := by
    -- Proof comment: a Dirac integral is integrable as soon as the endpoint evaluation is finite,
    -- and the explicit kernel evaluation gives that finite value.
    refine integrable_dirac (a := unitSphereFinOnePosPoint) (f := f) ?_
    rw [hposEval]
    simp
  have hnegDirac : Integrable f (Measure.dirac unitSphereFinOneNegPoint) := by
    -- Proof comment: the negative endpoint is symmetric, so the same Dirac integrability check
    -- closes after rewriting with the companion kernel evaluation.
    refine integrable_dirac (a := unitSphereFinOneNegPoint) (f := f) ?_
    rw [hnegEval]
    simp
  have hpos :
      Integrable f (((2 : ENNReal)⁻¹) • Measure.dirac unitSphereFinOnePosPoint) := by
    exact hposDirac.smul_measure (by simp)
  have hneg :
      Integrable f (((2 : ENNReal)⁻¹) • Measure.dirac unitSphereFinOneNegPoint) := by
    exact hnegDirac.smul_measure (by simp)
  -- Proof comment: the normalized `S⁰` measure is the average of the two endpoint atoms, so the
  -- integral is the average of the two explicit one-dimensional kernel values.
  rw [unitSphereFinOne_normalizedBoundaryMeasure_eq_halfDiracSum, smul_add]
  rw [integral_add_measure hpos hneg, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  rw [hposEval, hnegEval]
  norm_num
  ring

/-- Helper for Exercise 25.4.3: after rewriting through an orthonormal basis representation, the
scalar observable `y ↦ ⟪y, u⟫` becomes the chosen coordinate. -/
private theorem map_inner_eq_map_firstCoordinate_repr
    (b : OrthonormalBasis (Fin d) ℝ State) (i0 : Fin d) {u : State} (hb0 : b i0 = u)
    (ν : Measure State) :
    Measure.map (fun y : State ↦ inner ℝ y u) ν =
      Measure.map (fun z : State ↦ z i0) (Measure.map b.repr ν) := by
  -- Proof comment: the `i0`-coordinate of `b.repr y` is exactly the inner product with `b i0`,
  -- so the statement is just functoriality of `Measure.map`.
  have hproj :
      (fun y : State ↦ inner ℝ y u) = (fun z : State ↦ z i0) ∘ b.repr := by
    funext y
    simp [OrthonormalBasis.repr_apply_apply, hb0, real_inner_comm]
  rw [hproj, Measure.map_map]
  all_goals
    fun_prop

/-- Helper for Exercise 25.4.3: every unit vector in `State` extends to an orthonormal basis whose
first vector is that unit vector. -/
private theorem exists_orthonormalBasis_first_eq
    {u : State} (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin d) ℝ State,
      b ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ = u := by
  let i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hcard : Module.finrank ℝ State = Fintype.card (Fin d) := by
    simpa using (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin d))
  have huOrthonormal :
      Orthonormal ℝ (({i0} : Set (Fin d)).restrict fun _ : Fin d ↦ u) := by
    -- Proof comment: orthonormality on the singleton `{i0}` is exactly the unit-norm condition.
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst hij
    simp [hu]
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := State) (ι := Fin d) hcard
      (v := fun _ : Fin d ↦ u) (s := ({i0} : Set (Fin d))) huOrthonormal
  refine ⟨b, ?_⟩
  simpa using hb i0 (by simp)

/-- Helper for Exercise 25.4.3: in the orthonormal coordinates determined by `b`, the vector
`ρ • v` becomes the scalar axis vector `ρ eᵢ₀` when `b i0 = v`. -/
private theorem orthonormalBasis_repr_smul_eq_single
    (b : OrthonormalBasis (Fin d) ℝ State) (i0 : Fin d) {v : State}
    (hb0 : b i0 = v) (ρ : ℝ) :
    b.repr (ρ • v) = EuclideanSpace.single i0 ρ := by
  -- Proof comment: the `i0`-coordinate records the component along `v = b i0`, while every
  -- other coordinate vanishes by orthonormality.
  have hv : ‖v‖ = 1 := by
    simpa [hb0] using b.norm_eq_one i0
  ext j
  by_cases hj : j = i0
  · subst hj
    simp [EuclideanSpace.single, OrthonormalBasis.repr_apply_apply, hb0,
      real_inner_self_eq_norm_sq, hv]
  · have hinner : inner ℝ (b j) v = 0 := by
      simpa [hb0] using b.orthonormal.inner_eq_zero hj
    simp [EuclideanSpace.single, OrthonormalBasis.repr_apply_apply, hj, hinner]

/-- Helper for Exercise 25.4.3: the orthonormal basis representation transports the distance to
`ρ • v` to the distance from the standard-axis point `ρ eᵢ₀`. -/
private theorem dist_repr_smul_eq_dist_single
    (b : OrthonormalBasis (Fin d) ℝ State) (i0 : Fin d) {v : State}
    (hb0 : b i0 = v) (ρ : ℝ) (u : State) :
    dist (ρ • v) u =
      dist (EuclideanSpace.single i0 ρ : EuclideanSpace ℝ (Fin d)) (b.repr u) := by
  -- Proof comment: `b.repr` is a linear isometry, so it preserves distances and sends the pole to
  -- the chosen coordinate axis.
  simpa [orthonormalBasis_repr_smul_eq_single (d := d) b i0 hb0 ρ] using
    (b.repr.isometry.dist_eq (ρ • v) u).symm

/-- Helper for Exercise 25.4.3: after freezing `ξ = ρ • v` with `‖v‖ = 1`, the unit-sphere
Poisson integrand becomes the standard-axis kernel in the coordinates of `b`. -/
private theorem unitSpherePoissonIntegrand_eq_axisIntegrand
    (ρ : ℝ) (hρpos : 0 < ρ) {v : State} (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin d) ℝ State) (i0 : Fin d) (hb0 : b i0 = v)
    (u : Metric.sphere (0 : State) 1) :
    (1 - ‖ρ • v‖ ^ (2 : ℕ)) / dist (ρ • v) (u : State) ^ d =
      (1 - ρ ^ (2 : ℕ)) /
        dist (EuclideanSpace.single i0 ρ : EuclideanSpace ℝ (Fin d))
          (b.repr (u : State)) ^ d := by
  -- Proof comment: the numerator simplifies because `v` is a unit vector, and the denominator is
  -- exactly the rotated axis distance from the previous lemma.
  rw [dist_repr_smul_eq_dist_single (d := d) b i0 hb0 ρ (u : State)]
  simp [norm_smul, hv, Real.norm_eq_abs, abs_of_pos hρpos]

/-- Helper for Exercise 25.4.3: an orthonormal basis representation restricts to a measurable
equivalence of the unit sphere. -/
private noncomputable def unitSphereMeasurableEquiv
    (b : OrthonormalBasis (Fin d) ℝ State) :
    Metric.sphere (0 : State) 1 ≃ᵐ Metric.sphere (0 : State) 1 where
  toFun u := ⟨b.repr (u : State), by
    -- Proof comment: `b.repr` is an isometry, so it preserves the unit-sphere equation.
    rw [Metric.mem_sphere, dist_eq_norm]
    simpa using u.property⟩
  invFun u := ⟨b.repr.symm (u : State), by
    -- Proof comment: the inverse orthogonal change of coordinates preserves the same sphere.
    rw [Metric.mem_sphere, dist_eq_norm]
    simpa using u.property⟩
  left_inv u := by
    -- Proof comment: the sphere restriction is built from inverse linear isometries.
    ext
    simp
  right_inv u := by
    -- Proof comment: the inverse sphere restriction is literally the inverse map above.
    ext
    simp
  measurable_toFun := by
    -- Proof comment: the restricted representation map is continuous, hence measurable.
    let hcont :
        Continuous
          (fun u : Metric.sphere (0 : State) 1 ↦
            (⟨b.repr (u : State), by
              rw [Metric.mem_sphere, dist_eq_norm]
              simpa using u.property⟩ :
              Metric.sphere (0 : State) 1)) := by
      simpa using
        (Continuous.subtype_mk
          (b.repr.continuous.comp continuous_subtype_val)
          (fun u ↦ by
            rw [Metric.mem_sphere, dist_eq_norm]
            simpa using u.property))
    exact hcont.measurable
  measurable_invFun := by
    -- Proof comment: the inverse sphere map is continuous for the same reason.
    let hcont :
        Continuous
          (fun u : Metric.sphere (0 : State) 1 ↦
            (⟨b.repr.symm (u : State), by
              rw [Metric.mem_sphere, dist_eq_norm]
              simpa using u.property⟩ :
              Metric.sphere (0 : State) 1)) := by
      simpa using
        (Continuous.subtype_mk
          (b.repr.symm.continuous.comp continuous_subtype_val)
          (fun u ↦ by
            rw [Metric.mem_sphere, dist_eq_norm]
            simpa using u.property))
    exact hcont.measurable

/-- Helper for Exercise 25.4.3: the cone over the `b.repr`-preimage of a sphere set is exactly the
ambient preimage of the corresponding cone. -/
private theorem smul_preimage_unitSphereMeasurableEquiv_eq
    (b : OrthonormalBasis (Fin d) ℝ State)
    (s : Set (Metric.sphere (0 : State) 1)) :
    Set.Ioo (0 : ℝ) 1 •
        ((↑) '' ((unitSphereMeasurableEquiv (d := d) b) ⁻¹' s)) =
      b.repr ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨r, hr, y, hy, rfl⟩
    rcases hy with ⟨u, hu, rfl⟩
    -- Proof comment: applying `b.repr` to a cone point only rotates the spherical factor.
    change b.repr (r • (u : State)) ∈ Set.Ioo (0 : ℝ) 1 • ((↑) '' s)
    refine ⟨r, hr, ((unitSphereMeasurableEquiv (d := d) b u : Metric.sphere (0 : State) 1) :
        State), ?_, ?_⟩
    · exact ⟨unitSphereMeasurableEquiv (d := d) b u, hu, rfl⟩
    · simp [unitSphereMeasurableEquiv, map_smul]
  · intro hx
    change b.repr x ∈ Set.Ioo (0 : ℝ) 1 • ((↑) '' s) at hx
    rcases hx with ⟨r, hr, y, hy, hxy⟩
    rcases hy with ⟨u, hu, rfl⟩
    let u' : Metric.sphere (0 : State) 1 := ⟨b.repr.symm (u : State), by
      -- Proof comment: rotating the sphere point back along `b.repr.symm` keeps norm `1`.
      rw [Metric.mem_sphere, dist_eq_norm]
      simpa using u.property⟩
    refine ⟨r, hr, (u' : State), ?_, ?_⟩
    · refine ⟨u', ?_, rfl⟩
      -- Proof comment: by construction, `u'` maps back to the original sphere point `u ∈ s`.
      change unitSphereMeasurableEquiv (d := d) b u' ∈ s
      simpa [u', unitSphereMeasurableEquiv] using hu
    · -- Proof comment: applying the inverse representation to the cone equation recovers `x`.
      apply_fun b.repr.symm at hxy
      simpa [u'] using hxy

/-- Helper for Exercise 25.4.3: the unit-sphere `toSphere` measure is invariant under orthogonal
changes of coordinates. -/
private theorem unitSphereMeasurableEquiv_map_toSphere
    (b : OrthonormalBasis (Fin d) ℝ State) :
    Measure.map (unitSphereMeasurableEquiv (d := d) b)
        ((volume : Measure State).toSphere) =
      (volume : Measure State).toSphere := by
  refine Measure.ext fun s hs ↦ ?_
  rw [MeasurableEquiv.map_apply (unitSphereMeasurableEquiv (d := d) b) s]
  rw [MeasureTheory.Measure.toSphere_apply'
      (μ := (volume : Measure State))
      (hs := hs.preimage (unitSphereMeasurableEquiv (d := d) b).measurable)]
  rw [MeasureTheory.Measure.toSphere_apply' (μ := (volume : Measure State)) (hs := hs)]
  rw [smul_preimage_unitSphereMeasurableEquiv_eq (d := d) b s]
  -- Proof comment: after identifying the cone preimage, the ambient volume is unchanged because
  -- `b.repr` is a volume-preserving measurable equivalence.
  calc
    ↑(Module.finrank ℝ State) *
        (volume : Measure State) (b.repr ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s))) =
      ↑(Module.finrank ℝ State) *
        (Measure.map b.repr (volume : Measure State))
          (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
            congr 1
            symm
            exact
              MeasurableEmbedding.map_apply
                b.repr.toMeasurableEquiv.measurableEmbedding
                (volume : Measure State)
                (Set.Ioo (0 : ℝ) 1 • ((↑) '' s))
    _ = ↑(Module.finrank ℝ State) *
        (volume : Measure State) (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
          rw [(OrthonormalBasis.measurePreserving_repr b).map_eq]

/-- Helper for Exercise 25.4.3: the normalized unit-sphere boundary law is invariant under the
same orthogonal change of coordinates. -/
private theorem unitSphereMeasurableEquiv_map_normalizedBoundaryMeasure
    (b : OrthonormalBasis (Fin d) ℝ State) :
    let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
      ⟨(volume : Measure State).toSphere, inferInstance⟩
    Measure.map (unitSphereMeasurableEquiv (d := d) b)
        (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) =
      (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) := by
  let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
    ⟨(volume : Measure State).toSphere, inferInstance⟩
  -- Proof comment: once the raw `toSphere` law is invariant, the same is true after the fixed
  -- scalar normalization by total mass.
  simp [ν, Measure.map_smul, unitSphereMeasurableEquiv_map_toSphere]

/-- Helper for Exercise 25.4.3: split the first coordinate off a finite-dimensional Euclidean
space as a measurable equivalence. -/
private def euclideanPiFinSuccAbove (m : ℕ) :
    EuclideanSpace ℝ (Fin (m + 1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin m) :=
  (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm.trans <|
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).trans <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin m → ℝ))

/-- Helper for Exercise 25.4.3: the inverse head-tail equivalence recovers the head coordinate in
the zeroth slot. -/
private theorem euclideanPiFinSuccAbove_symm_zero
    (m : ℕ) (s : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    ((euclideanPiFinSuccAbove m).symm (s, z)) 0 = s := by
  rfl

/-- Helper for Exercise 25.4.3: the inverse head-tail equivalence recovers the tail coordinates in
the successor slots. -/
private theorem euclideanPiFinSuccAbove_symm_succ
    (m : ℕ) (s : ℝ) (z : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    ((euclideanPiFinSuccAbove m).symm (s, z)) (Fin.succ i) = z i := by
  rfl

/-- Helper for Exercise 25.4.3: the head-tail Euclidean coordinate split preserves volume. -/
private theorem measurePreserving_euclideanPiFinSuccAbove (m : ℕ) :
    MeasurePreserving (euclideanPiFinSuccAbove m) volume volume := by
  unfold euclideanPiFinSuccAbove
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (m + 1))).trans ?_
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).trans ?_
  simpa [Measure.volume_eq_prod] using
    (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin m))

/-- Helper for Exercise 25.4.3: a volume-preserving measurable equivalence transports a
`withDensity` measure by precomposing the density with the inverse equivalence. -/
private theorem mapWithDensityOfVolumePreserving {α β : Type*}
    [MeasureSpace α] [MeasureSpace β]
    (e : α ≃ᵐ β) (hpres : MeasurePreserving e volume volume)
    (g : α → ENNReal) (hg : Measurable g) :
    Measure.map e (volume.withDensity g) =
      volume.withDensity (fun y : β ↦ g (e.symm y)) := by
  refine Measure.ext fun s hs ↦ ?_
  -- Proof comment: evaluate both measures on the same measurable set and move the density through
  -- the volume-preserving equivalence once.
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ hs,
    withDensity_apply _ (e.measurable hs)]
  simpa using hpres.setLIntegral_comp_preimage hs (hg.comp e.symm.measurable)

/-- Helper for Exercise 25.4.3: pushing a product-space density forward along the first coordinate
integrates out the tail variables. This is the generic fiber-integration step used in the scalar
marginal reduction for the remaining sphere normalization proof. -/
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
  -- Proof comment: rewrite the preimage `Prod.fst ⁻¹' s` and then apply Tonelli on the product
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

/-- Helper for Exercise 25.4.3: in head-tail coordinates, the squared norm separates into the head
square plus the tail norm square. -/
private theorem norm_euclideanPiFinSuccAbove_symm_sq
    (m : ℕ) (s : ℝ) (z : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖((euclideanPiFinSuccAbove (m + 1)).symm (s, z) :
        EuclideanSpace ℝ (Fin (m + 2)))‖ ^ (2 : ℕ) =
      s ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ) := by
  -- Proof comment: expand the Euclidean norm square and then identify the head and tail
  -- coordinates with the inverse `piFinSuccAbove` formulas.
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  have htail :
      (∑ i : Fin (m + 1),
          (((euclideanPiFinSuccAbove (m + 1)).symm (s, z)) (Fin.succ i) ^ (2 : ℕ))) =
        ‖z‖ ^ (2 : ℕ) := by
    simpa [euclideanPiFinSuccAbove_symm_succ] using (EuclideanSpace.real_norm_sq_eq z).symm
  rw [euclideanPiFinSuccAbove_symm_zero, htail]

/-- Helper for Exercise 25.4.3: in head-tail coordinates, the squared distance from the standard
axis point `ρ e₀` separates into the head displacement square plus the tail norm square. -/
private theorem dist_single_euclideanPiFinSuccAbove_symm_sq
    (m : ℕ) (ρ s : ℝ) (z : EuclideanSpace ℝ (Fin (m + 1))) :
    dist (EuclideanSpace.single (0 : Fin (m + 2)) ρ : EuclideanSpace ℝ (Fin (m + 2)))
        ((euclideanPiFinSuccAbove (m + 1)).symm (s, z)) ^ (2 : ℕ) =
      (s - ρ) ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ) := by
  -- Proof comment: the zeroth coordinate carries the scalar axis displacement, and every
  -- successor coordinate is exactly a tail coordinate of `z`.
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  have hhead :
      ((EuclideanSpace.single (0 : Fin (m + 2)) ρ :
            EuclideanSpace ℝ (Fin (m + 2))) -
          (euclideanPiFinSuccAbove (m + 1)).symm (s, z)) 0 ^ (2 : ℕ) =
        (s - ρ) ^ (2 : ℕ) := by
    change
      (ρ - ((euclideanPiFinSuccAbove (m + 1)).symm (s, z)) 0) ^ (2 : ℕ) =
        (s - ρ) ^ (2 : ℕ)
    rw [euclideanPiFinSuccAbove_symm_zero]
    ring
  have htail :
      (∑ i : Fin (m + 1),
          (((EuclideanSpace.single (0 : Fin (m + 2)) ρ :
                EuclideanSpace ℝ (Fin (m + 2))) -
              (euclideanPiFinSuccAbove (m + 1)).symm (s, z)) (Fin.succ i) ^ (2 : ℕ))) =
        ‖z‖ ^ (2 : ℕ) := by
    calc
      (∑ i : Fin (m + 1),
          (((EuclideanSpace.single (0 : Fin (m + 2)) ρ :
                EuclideanSpace ℝ (Fin (m + 2))) -
              (euclideanPiFinSuccAbove (m + 1)).symm (s, z)) (Fin.succ i) ^ (2 : ℕ)))
          =
        ∑ i : Fin (m + 1), ((-z i) ^ (2 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [euclideanPiFinSuccAbove_symm_succ, EuclideanSpace.single]
      _ = ∑ i : Fin (m + 1), z i ^ (2 : ℕ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = ‖z‖ ^ (2 : ℕ) := by
            simpa using (EuclideanSpace.real_norm_sq_eq z).symm
  rw [hhead, htail]

/-- Helper for Exercise 25.4.3: translating the tail variable centers a fiber integral without
changing its value. This isolates the additive-Haar symmetry that will later remove the shifted
tail vector from the scalar marginal density. -/
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

/-- Helper for Exercise 25.4.3: after centering the tail fiber, one homothety removes the
remaining positive parameter `A` from the Euclidean integral. -/
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
    -- Proof comment: factor the denominator as `A * (1 + ‖(√A)⁻¹ • z‖²)` so every `A`
    -- dependence moves into the constant coefficient.
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
      C / (A + ‖z‖ ^ (2 : ℕ)) ^ p =
          C / (A ^ p * (((1 : ℝ) + ‖(Real.sqrt A)⁻¹ • z‖ ^ (2 : ℕ)) ^ p)) := by
            rw [hfactor, Real.mul_rpow hA.le hbase_pos.le]
      _ = (C / A ^ p) * (((1 : ℝ) + ‖(Real.sqrt A)⁻¹ • z‖ ^ (2 : ℕ)) ^ p)⁻¹ := by
            field_simp [hApow_ne, hbase_pow_ne]
      _ = (C / A ^ p) * (((1 : ℝ) + ‖(Real.sqrt A)⁻¹ • z‖ ^ (2 : ℕ)) ^ (-p)) := by
            rw [← Real.rpow_neg hbase_pos.le]
      _ = scaledTail z := rfl
  have hunitTail_int :
      Integrable unitTail (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) := by
    -- Proof comment: the universal unit-tail profile is the standard integrable
    -- `((1 + ‖z‖²)^(-r/2))` kernel on Euclidean space.
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
    -- Proof comment: additive-Haar invariance under the dilation by `√A` preserves
    -- integrability, so only the constant prefactor remains.
    exact
      (hunitTail_int.comp_smul (μ := (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))))
        (R := (Real.sqrt A)⁻¹) (inv_ne_zero hsqrt_ne)).const_mul (C / A ^ p)
  have hscaled_nonneg :
      0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))] scaledTail := by
    refine Filter.Eventually.of_forall ?_
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
      A ^ (((k + 1 : ℕ) : ℝ) / 2) = A ^ ((1 / (2 : ℝ)) * ((k + 1 : ℕ) : ℝ)) := by
            congr 1
            ring
      _ = (A ^ (1 / (2 : ℝ))) ^ (((k + 1 : ℕ) : ℝ)) := by
            rw [← Real.rpow_mul hA.le]
      _ = (Real.sqrt A) ^ (((k + 1 : ℕ) : ℝ)) := by
            rw [Real.sqrt_eq_rpow]
      _ = (Real.sqrt A) ^ (k + 1) := by
            rw [Real.rpow_natCast]
  have hpow_split : A ^ p = A * (Real.sqrt A) ^ (k + 1) := by
    -- Proof comment: the exponent `(k + 3) / 2` splits as `1 + (k + 1) / 2`.
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
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) =
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

/-- Helper for Exercise 25.4.3: the radial antiderivative of the universal tail integrand is the
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
  -- Proof comment: differentiating the polynomial and the radial denominator separately reduces
  -- the target derivative to a single scalar identity.
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

/-- Helper for Exercise 25.4.3: the normalized quadratic ratio is `1` minus the reciprocal tail
factor. -/
private theorem radialUnitTailRatio_eq_one_sub_inv (y : ℝ) :
    y ^ (2 : ℕ) / ((1 : ℝ) + y ^ (2 : ℕ)) =
      1 - (((1 : ℝ) + y ^ (2 : ℕ))⁻¹) := by
  have hden : (1 : ℝ) + y ^ (2 : ℕ) ≠ 0 := by positivity
  -- Proof comment: this isolates the only asymptotic contribution that survives at infinity.
  field_simp [hden]
  ring

/-- Helper for Exercise 25.4.3: the normalized quadratic ratio tends to `1` at `+∞`. -/
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
  -- Proof comment: once the ratio is rewritten as `1 - (...)⁻¹`, the reciprocal term vanishes at
  -- infinity.
  simpa using tendsto_const_nhds.sub hinv

/-- Helper for Exercise 25.4.3: for positive `y`, the radial antiderivative core is a power of
the normalized quadratic ratio. -/
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
  -- Proof comment: the numerator contributes the exact half-power needed to merge both factors
  -- into a single ratio.
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

/-- Helper for Exercise 25.4.3: the antiderivative core tends to `1` at `+∞`. -/
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
  -- Proof comment: after the eventual rewrite to the normalized ratio, the previous asymptotic
  -- limit gives the endpoint value.
  exact Tendsto.congr' (by
    filter_upwards [hrewrite] with y hy
    exact hy.symm) hpowq

/-- Helper for Exercise 25.4.3: the one-dimensional radial tail integral equals `(k + 1)⁻¹`. -/
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
    -- Proof comment: on the positive half-line, the antiderivative formula is the previous
    -- derivative computation.
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
  -- Proof comment: the fundamental theorem on `(0, ∞)` now evaluates the radial integral.
  simpa [g] using
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg hlim

/-- Helper for Exercise 25.4.3: once the scalar head coordinate is isolated, the centered tail
integral already collapses to the explicit unit-ball volume constant. -/
private theorem unitTailIntegral_eq_unitBallVolume {k : ℕ} :
    ∫ z : EuclideanSpace ℝ (Fin (k + 1)),
      ((1 : ℝ) + ‖z‖ ^ (2 : ℕ)) ^ (-((((k + 3 : ℕ) : ℝ) / 2)))
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) =
        (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1) := by
  -- Proof comment: apply the Euclidean radial integration formula and then collapse the remaining
  -- one-dimensional tail factor with the new antiderivative computation.
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

/-- Helper for Exercise 25.4.3: once the scalar head coordinate is isolated, the centered tail
integral already collapses to the explicit unit-ball volume constant. -/
private theorem centeredTailIntegral_eq_ofReal_mul_unitBallVolume
    {k : ℕ} {C A : ℝ} (hA : 0 < A) (hC : 0 ≤ C) :
    ∫⁻ z, ENNReal.ofReal
        (C / (A + ‖z‖ ^ (2 : ℕ)) ^ ((((k + 3 : ℕ) : ℝ) / 2)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) =
      ENNReal.ofReal
        ((C / A) *
          (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1)) := by
  -- Proof comment: this packages the two radial-calculus steps needed later in the Poisson
  -- normalization endgame into one rewrite-friendly statement.
  rw [centeredTailIntegral_eq_ofReal_mul_unitTailIntegral (k := k) hA hC]
  rw [ProbabilityTheory.unitTailIntegral_eq_unitBallVolume (k := k)]

/-- Helper for Exercise 25.4.3: after the head-tail split, the standard-axis distance denominator
is exactly the quadratic head-tail form raised to the half-dimension exponent. -/
private theorem dist_single_euclideanPiFinSuccAbove_symm_rpow
    (k : ℕ) (ρ s : ℝ) (z : EuclideanSpace ℝ (Fin (k + 1))) :
    dist (EuclideanSpace.single (0 : Fin (k + 2)) ρ : EuclideanSpace ℝ (Fin (k + 2)))
        ((euclideanPiFinSuccAbove (k + 1)).symm (s, z)) ^ (k + 2) =
      ((s - ρ) ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ)) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
  let x : ℝ :=
    dist (EuclideanSpace.single (0 : Fin (k + 2)) ρ : EuclideanSpace ℝ (Fin (k + 2)))
      ((euclideanPiFinSuccAbove (k + 1)).symm (s, z))
  have hx_nonneg : 0 ≤ x := dist_nonneg
  -- Proof comment: convert the natural power to an `rpow`, then use the squared-distance
  -- normal form already proved in head-tail coordinates.
  calc
    x ^ (k + 2) = x ^ (((k + 2 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    _ = (x ^ (2 : ℕ)) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
      rw [← Real.rpow_natCast_mul hx_nonneg 2 ((((k + 2 : ℕ) : ℝ) / 2))]
      congr 1
      ring
    _ = ((s - ρ) ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ)) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
      simp [x, dist_single_euclideanPiFinSuccAbove_symm_sq]

/-- Helper for Exercise 25.4.3: in head-tail coordinates, the standard-axis Poisson kernel uses
only the scalar quadratic denominator `((s - ρ)^2 + ‖z‖^2)^(d / 2)`. -/
private theorem unitSphereZeroAxisKernel_euclideanPiFinSuccAbove_symm
    (k : ℕ) (ρ s : ℝ) (z : EuclideanSpace ℝ (Fin (k + 1))) :
    (1 - ρ ^ (2 : ℕ)) /
        dist
          (EuclideanSpace.single (0 : Fin (k + 2)) ρ : EuclideanSpace ℝ (Fin (k + 2)))
          ((euclideanPiFinSuccAbove (k + 1)).symm (s, z)) ^ (k + 2) =
      (1 - ρ ^ (2 : ℕ)) /
        (((s - ρ) ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ)) ^ (((k + 2 : ℕ) : ℝ) / 2)) := by
  -- Proof comment: once the denominator power is rewritten, the standard-axis integrand becomes a
  -- scalar quadratic form in the head and tail variables.
  rw [dist_single_euclideanPiFinSuccAbove_symm_rpow]

/-- Helper for Exercise 25.4.3: after the head-tail split, the weighted standard-axis kernel is
the explicit scalar quadratic density used by the remaining normalization transport step. -/
private theorem unitSphereZeroAxisKernelHeadTail_eq
    (k : ℕ) (ρ s : ℝ) (z : EuclideanSpace ℝ (Fin (k + 1))) :
    ENNReal.ofReal
        ((1 - ρ ^ (2 : ℕ)) /
          dist
            (EuclideanSpace.single (0 : Fin (k + 2)) ρ : EuclideanSpace ℝ (Fin (k + 2)))
            ((euclideanPiFinSuccAbove (k + 1)).symm (s, z)) ^ (k + 2)) =
      ENNReal.ofReal
        ((1 - ρ ^ (2 : ℕ)) /
          (((s - ρ) ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ)) ^ (((k + 2 : ℕ) : ℝ) / 2))) := by
  -- Proof comment: package the denominator rewrite under `ENNReal.ofReal` so the later
  -- with-density transport can consume it without additional coercion plumbing.
  exact congrArg ENNReal.ofReal <|
    unitSphereZeroAxisKernel_euclideanPiFinSuccAbove_symm k ρ s z

/-- Helper for Exercise 25.4.3: the scalarized standard-axis kernel is measurable on the
head-tail product coordinates. -/
private theorem measurable_unitSphereZeroAxisKernelHeadTail
    (k : ℕ) (ρ : ℝ) :
    Measurable
      (fun p : ℝ × EuclideanSpace ℝ (Fin (k + 1)) ↦
        ENNReal.ofReal
          ((1 - ρ ^ (2 : ℕ)) /
            dist
              (EuclideanSpace.single (0 : Fin (k + 2)) ρ : EuclideanSpace ℝ (Fin (k + 2)))
              ((euclideanPiFinSuccAbove (k + 1)).symm p) ^ (k + 2))) := by
  -- Proof comment: this is the exact measurability input needed for the planned pushforward of
  -- the kernel-weighted normalized sphere law to product coordinates.
  fun_prop

/-- Helper for Exercise 25.4.3: transporting the ambient zero-axis kernel density through the
head-tail measurable equivalence rewrites it into the explicit scalar quadratic form. -/
-- TODO: re-establish the `withDensity` transport by comparing the target product-space volume
-- spelling with the generic `mapWithDensityOfVolumePreserving` output. This is routine measure
-- plumbing and not the main remaining Poisson-kernel blocker.
private theorem mapPiFinSuccAbove_zeroAxisKernelWithDensity_eq
    (k : ℕ) (ρ : ℝ) :
    Measure.map (euclideanPiFinSuccAbove (k + 1))
        (((volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).withDensity
          (fun y ↦
            ENNReal.ofReal
              ((1 - ρ ^ (2 : ℕ)) /
                dist
                  (EuclideanSpace.single (0 : Fin (k + 2)) ρ :
                    EuclideanSpace ℝ (Fin (k + 2)))
                  y ^ (k + 2))))) =
      (((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))).withDensity
        (fun p : ℝ × EuclideanSpace ℝ (Fin (k + 1)) ↦
          ENNReal.ofReal
            ((1 - ρ ^ (2 : ℕ)) /
              (((p.1 - ρ) ^ (2 : ℕ) + ‖p.2‖ ^ (2 : ℕ)) ^
                (((k + 2 : ℕ) : ℝ) / 2))))) := by
  have hkernelMeas :
      Measurable
        (fun y : EuclideanSpace ℝ (Fin (k + 2)) ↦
          ENNReal.ofReal
            ((1 - ρ ^ (2 : ℕ)) /
              dist
                (EuclideanSpace.single (0 : Fin (k + 2)) ρ :
                  EuclideanSpace ℝ (Fin (k + 2)))
                y ^ (k + 2))) := by
    -- Proof comment: the ambient zero-axis kernel density is an explicit measurable scalar
    -- expression on Euclidean space.
    fun_prop
  -- Proof comment: the head-tail equivalence preserves volume, so `withDensity` pushes forward
  -- by precomposing the density with the inverse equivalence and then rewriting that inverse
  -- density using the scalar head-tail formula.
  calc
    Measure.map (euclideanPiFinSuccAbove (k + 1))
        (((volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).withDensity
          (fun y ↦
            ENNReal.ofReal
              ((1 - ρ ^ (2 : ℕ)) /
                dist
                  (EuclideanSpace.single (0 : Fin (k + 2)) ρ :
                    EuclideanSpace ℝ (Fin (k + 2)))
                  y ^ (k + 2))))) =
      (((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))).withDensity
        (fun p : ℝ × EuclideanSpace ℝ (Fin (k + 1)) ↦
          ENNReal.ofReal
            ((1 - ρ ^ (2 : ℕ)) /
              dist
                (EuclideanSpace.single (0 : Fin (k + 2)) ρ :
                  EuclideanSpace ℝ (Fin (k + 2)))
                ((euclideanPiFinSuccAbove (k + 1)).symm p) ^ (k + 2)))) := by
      simpa [Measure.volume_eq_prod] using
        mapWithDensityOfVolumePreserving
          (e := euclideanPiFinSuccAbove (k + 1))
          (hpres := measurePreserving_euclideanPiFinSuccAbove (k + 1))
          (g := fun y : EuclideanSpace ℝ (Fin (k + 2)) ↦
            ENNReal.ofReal
              ((1 - ρ ^ (2 : ℕ)) /
                dist
                  (EuclideanSpace.single (0 : Fin (k + 2)) ρ :
                    EuclideanSpace ℝ (Fin (k + 2)))
                  y ^ (k + 2)))
          hkernelMeas
    _ =
      (((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))).withDensity
        (fun p : ℝ × EuclideanSpace ℝ (Fin (k + 1)) ↦
          ENNReal.ofReal
            ((1 - ρ ^ (2 : ℕ)) /
              (((p.1 - ρ) ^ (2 : ℕ) + ‖p.2‖ ^ (2 : ℕ)) ^
                (((k + 2 : ℕ) : ℝ) / 2))))) := by
      have hdens :
          (fun p : ℝ × EuclideanSpace ℝ (Fin (k + 1)) ↦
            ENNReal.ofReal
              ((1 - ρ ^ (2 : ℕ)) /
                dist
                  (EuclideanSpace.single (0 : Fin (k + 2)) ρ :
                    EuclideanSpace ℝ (Fin (k + 2)))
                  ((euclideanPiFinSuccAbove (k + 1)).symm p) ^ (k + 2))) =
        (fun p : ℝ × EuclideanSpace ℝ (Fin (k + 1)) ↦
          ENNReal.ofReal
            ((1 - ρ ^ (2 : ℕ)) /
              (((p.1 - ρ) ^ (2 : ℕ) + ‖p.2‖ ^ (2 : ℕ)) ^
                (((k + 2 : ℕ) : ℝ) / 2)))) := by
        funext p
        rcases p with ⟨s, z⟩
        exact unitSphereZeroAxisKernelHeadTail_eq k ρ s z
      rw [hdens]

/-- Helper for Exercise 25.4.3: after the ambient head-tail transport, pushing the weighted
zero-axis kernel further to the first coordinate integrates out the tail variables. This isolates
the fully solved ambient scalarization step from the still-missing normalized-sphere owner
comparison. -/
private theorem zeroAxisKernelFirstMarginal_eq_withDensityFiberIntegral
    (k : ℕ) (ρ : ℝ) :
    Measure.map Prod.fst
        (Measure.map (euclideanPiFinSuccAbove (k + 1))
          ((volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).withDensity
            (fun y ↦
              ENNReal.ofReal
                ((1 - ρ ^ (2 : ℕ)) /
                  dist
                    (EuclideanSpace.single (0 : Fin (k + 2)) ρ :
                      EuclideanSpace ℝ (Fin (k + 2)))
                    y ^ (k + 2))))) =
      (volume : Measure ℝ).withDensity
        (fun s ↦
          ∫⁻ z, ENNReal.ofReal
            ((1 - ρ ^ (2 : ℕ)) /
              (((s - ρ) ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ)) ^
                (((k + 2 : ℕ) : ℝ) / 2)))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))) := by
  have hf :
      Measurable
        (fun p : ℝ × EuclideanSpace ℝ (Fin (k + 1)) ↦
          ENNReal.ofReal
            ((1 - ρ ^ (2 : ℕ)) /
              (((p.1 - ρ) ^ (2 : ℕ) + ‖p.2‖ ^ (2 : ℕ)) ^
                (((k + 2 : ℕ) : ℝ) / 2)))) := by
    -- Proof comment: the scalarized head-tail density is measurable, so the generic
    -- first-coordinate fiber-integration lemma applies directly.
    fun_prop
  -- Proof comment: the ambient zero-axis kernel has already been transported to product
  -- coordinates, so the remaining pushforward is exactly the generic `Prod.fst` fiber integral.
  rw [mapPiFinSuccAbove_zeroAxisKernelWithDensity_eq k ρ]
  exact mapFstWithDensityEqWithDensityFiberIntegral hf

/-- Helper for Exercise 25.4.3: the weighted normalized unit-sphere law is finite because its
Poisson density is continuous on the compact sphere. -/
private theorem unitSphereWeightedBoundaryMeasure_isFinite
    (k : ℕ) (ρ : ℝ) (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    let E : Type := EuclideanSpace ℝ (Fin (k + 2))
    let ν : FiniteMeasure (Metric.sphere (0 : E) 1) :=
      ⟨(volume : Measure E).toSphere, inferInstance⟩
    let weighted :
        Measure (Metric.sphere (0 : E) 1) :=
      ((ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))).withDensity
        (fun z ↦
          ENNReal.ofReal
            ((1 - ρ ^ (2 : ℕ)) /
              dist
                (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
                (z : E) ^ (k + 2))))
    IsFiniteMeasure weighted := by
  let E : Type := EuclideanSpace ℝ (Fin (k + 2))
  let ν : FiniteMeasure (Metric.sphere (0 : E) 1) :=
    ⟨(volume : Measure E).toSphere, inferInstance⟩
  let base : Measure (Metric.sphere (0 : E) 1) :=
    ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))
  let density : Metric.sphere (0 : E) 1 → ℝ := fun z ↦
    (1 - ρ ^ (2 : ℕ)) /
      dist
        (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
        (z : E) ^ (k + 2)
  let weighted :
      Measure (Metric.sphere (0 : E) 1) :=
    base.withDensity (fun z ↦ ENNReal.ofReal (density z))
  have hρball :
      (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E) ∈ Metric.ball (0 : E) 1 := by
    -- Proof comment: the axis point has Euclidean norm `ρ`, so the hypothesis `ρ < 1` places it
    -- strictly inside the unit ball.
    have hnorm : ‖(EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)‖ < 1 := by
      simpa [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_pos hρpos] using hρlt
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm
  have hdensityCont : Continuous density := by
    have hdenCont :
        Continuous
          (fun z : Metric.sphere (0 : E) 1 ↦
            dist
              (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
              (z : E) ^ (k + 2)) :=
      (continuous_const.dist continuous_subtype_val).pow (k + 2)
    have hden_ne :
        ∀ z : Metric.sphere (0 : E) 1,
          dist
              (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
              (z : E) ^ (k + 2) ≠ 0 := by
      intro z
      refine pow_ne_zero _ ?_
      exact
        dist_ne_zero_of_mem_ball_mem_sphere_absRadius
          (d := k + 2) (r := 1) zero_lt_one hρball z
    -- Proof comment: the denominator never vanishes on the unit sphere because the pole lies in
    -- the open unit ball.
    simpa [density] using continuous_const.div hdenCont hden_ne
  let f : BoundedContinuousFunction (Metric.sphere (0 : E) 1) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨density, hdensityCont⟩
  have hInt : Integrable density base := by
    -- Proof comment: compactness turns the continuous density into an integrable function against
    -- the finite normalized sphere measure.
    simpa [f, density, base] using f.integrable base
  -- Proof comment: finiteness of the density integral is exactly the criterion needed for the
  -- `withDensity` owner.
  simpa [weighted, density, base, ν] using
    (MeasureTheory.isFiniteMeasure_withDensity_ofReal hInt.hasFiniteIntegral)

/-- Helper for Exercise 25.4.3: the remaining unit-sphere kernel integral is the total mass of
its weighted normalized boundary measure. -/
private theorem unitSphereZeroAxisKernelIntegral_eq_weightedBoundaryMass
    (k : ℕ) (ρ : ℝ) (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    let E : Type := EuclideanSpace ℝ (Fin (k + 2))
    let ν : FiniteMeasure (Metric.sphere (0 : E) 1) :=
      ⟨(volume : Measure E).toSphere, inferInstance⟩
    let weighted :
        Measure (Metric.sphere (0 : E) 1) :=
      ((ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))).withDensity
        (fun z ↦
          ENNReal.ofReal
            ((1 - ρ ^ (2 : ℕ)) /
              dist
                (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
                (z : E) ^ (k + 2))))
    ∫ z : Metric.sphere (0 : E) 1,
      (1 - ρ ^ (2 : ℕ)) /
        dist
          (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
          (z : E) ^ (k + 2) ∂
        (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))) =
      weighted.real Set.univ := by
  let E : Type := EuclideanSpace ℝ (Fin (k + 2))
  let ν : FiniteMeasure (Metric.sphere (0 : E) 1) :=
    ⟨(volume : Measure E).toSphere, inferInstance⟩
  let base : Measure (Metric.sphere (0 : E) 1) :=
    ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))
  let density : Metric.sphere (0 : E) 1 → ℝ := fun z ↦
    (1 - ρ ^ (2 : ℕ)) /
      dist
        (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
        (z : E) ^ (k + 2)
  let weighted :
      Measure (Metric.sphere (0 : E) 1) :=
    base.withDensity (fun z ↦ ENNReal.ofReal (density z))
  let _ : IsFiniteMeasure weighted := by
    simpa [weighted, ν] using
      unitSphereWeightedBoundaryMeasure_isFinite k ρ hρpos hρlt
  have hdensityMeas :
      Measurable (fun z : Metric.sphere (0 : E) 1 ↦ ENNReal.ofReal (density z)) := by
    fun_prop
  -- Proof comment: this is the finite-measure `withDensity` identity specialized to the
  -- normalized unit-sphere owner and the zero-axis Poisson density.
  calc
    ∫ z : Metric.sphere (0 : E) 1, density z ∂ base
        = ∫ z : Metric.sphere (0 : E) 1, density z * 1 ∂ base := by
            simp
    _ = ∫ z : Metric.sphere (0 : E) 1, (1 : ℝ) ∂ weighted := by
          rw [weighted, integral_withDensity_eq_integral_toReal_smul
            hdensityMeas (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
          refine integral_congr_ae ?_
          filter_upwards with z
          have hdensity_nonneg : 0 ≤ density z := by
            -- Proof comment: the numerator is positive because `0 < ρ < 1`, and the distance
            -- power in the denominator is nonnegative.
            have hnum : 0 ≤ 1 - ρ ^ (2 : ℕ) := by
              nlinarith
            exact div_nonneg hnum (by positivity)
          simp [density, ENNReal.toReal_ofReal, hdensity_nonneg]
    _ = weighted.real Set.univ := by
          simp [Measure.real_def]

/-- Helper for Exercise 25.4.3: every point on the unit sphere has first coordinate in
`[-1, 1]`. -/
private theorem unitSphereFirstCoordinate_mem_Icc
    (k : ℕ) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :
    ((z : EuclideanSpace ℝ (Fin (k + 2))) 0) ∈ Set.Icc (-1 : ℝ) 1 := by
  let x : EuclideanSpace ℝ (Fin (k + 2)) := (z : EuclideanSpace ℝ (Fin (k + 2)))
  have hz_norm : ‖(z : EuclideanSpace ℝ (Fin (k + 2)))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using z.property
  have hcoord_le : |x 0| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using
      (PiLp.norm_apply_le x (0 : Fin (k + 2)))
  have habs : |x 0| ≤ 1 := by
    simpa [x, hz_norm] using hcoord_le
  -- Proof comment: each coordinate of a unit vector has absolute value at most the ambient norm,
  -- which is exactly `1` on the unit sphere.
  exact abs_le.mp habs

/-- Helper for Exercise 25.4.3: the unit-sphere kernel integral is the mass of the
interval-supported first-coordinate marginal of the weighted normalized sphere law. -/
private theorem unitSphereZeroAxisKernelIntegral_eq_firstCoordinateMarginalUnitIntervalMass
    (k : ℕ) (ρ : ℝ) (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    let E : Type := EuclideanSpace ℝ (Fin (k + 2))
    let ν : FiniteMeasure (Metric.sphere (0 : E) 1) :=
      ⟨(volume : Measure E).toSphere, inferInstance⟩
    let weighted :
        Measure (Metric.sphere (0 : E) 1) :=
      ((ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))).withDensity
        (fun z ↦
          ENNReal.ofReal
            ((1 - ρ ^ (2 : ℕ)) /
              dist
                (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
                (z : E) ^ (k + 2))))
    ∫ z : Metric.sphere (0 : E) 1,
      (1 - ρ ^ (2 : ℕ)) /
        dist
          (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
          (z : E) ^ (k + 2) ∂
        (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))) =
      (Measure.map (fun z : Metric.sphere (0 : E) 1 ↦ (z : E) 0) weighted).real
        (Set.Icc (-1 : ℝ) 1) := by
  let E : Type := EuclideanSpace ℝ (Fin (k + 2))
  let ν : FiniteMeasure (Metric.sphere (0 : E) 1) :=
    ⟨(volume : Measure E).toSphere, inferInstance⟩
  let weighted :
      Measure (Metric.sphere (0 : E) 1) :=
    ((ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))).withDensity
      (fun z ↦
        ENNReal.ofReal
          ((1 - ρ ^ (2 : ℕ)) /
            dist
              (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
              (z : E) ^ (k + 2))))
  let coord : Metric.sphere (0 : E) 1 → ℝ := fun z ↦ (z : E) 0
  let _ : IsFiniteMeasure weighted := by
    simpa [weighted, ν] using
      unitSphereWeightedBoundaryMeasure_isFinite k ρ hρpos hρlt
  let _ : IsFiniteMeasure (Measure.map coord weighted) := by infer_instance
  have hcoordMeas : Measurable coord := by
    fun_prop
  have hpreimage :
      coord ⁻¹' Set.Icc (-1 : ℝ) 1 = Set.univ := by
    ext z
    constructor
    · intro _
      trivial
    · intro _
      exact unitSphereFirstCoordinate_mem_Icc k z
  have hmapIcc :
      (Measure.map coord weighted) (Set.Icc (-1 : ℝ) 1) = weighted Set.univ := by
    -- Proof comment: the first-coordinate pushforward is fully supported on `[-1,1]`.
    rw [Measure.map_apply hcoordMeas measurableSet_Icc, hpreimage]
  -- Proof comment: after identifying the kernel integral with the total weighted mass, support of
  -- the first-coordinate marginal on `[-1,1]` turns that total mass into the interval mass.
  calc
    ∫ z : Metric.sphere (0 : E) 1,
        (1 - ρ ^ (2 : ℕ)) /
          dist
            (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
            (z : E) ^ (k + 2) ∂
          (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))) =
      weighted.real Set.univ := by
        simpa [weighted, ν] using
          unitSphereZeroAxisKernelIntegral_eq_weightedBoundaryMass
            k ρ hρpos hρlt
    _ = (Measure.map coord weighted).real (Set.Icc (-1 : ℝ) 1) := by
      rw [Measure.real_def, Measure.real_def, hmapIcc]

/-- Helper for Exercise 25.4.3: in head-tail coordinates, the inverse image of the unit ball is
the quadratic condition `s² + ‖z‖² < 1`. -/
private theorem euclideanPiFinSuccAbove_symm_mem_ball_one_iff
    (k : ℕ) (s : ℝ) (z : EuclideanSpace ℝ (Fin (k + 1))) :
    (((euclideanPiFinSuccAbove (k + 1)).symm (s, z) :
        EuclideanSpace ℝ (Fin (k + 2))) ∈ Metric.ball 0 1) ↔
      s ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ) < 1 := by
  let u : EuclideanSpace ℝ (Fin (k + 2)) :=
    (euclideanPiFinSuccAbove (k + 1)).symm (s, z)
  -- Proof comment: the unit-ball condition is `‖u‖ < 1`, and the head-tail norm formula turns
  -- that into the equivalent quadratic inequality.
  rw [Metric.mem_ball, dist_eq_norm, ← norm_euclideanPiFinSuccAbove_symm_sq]
  constructor <;> intro hu
  · have hu_nonneg : 0 ≤ ‖u‖ := norm_nonneg u
    nlinarith
  · have hu_nonneg : 0 ≤ ‖u‖ := norm_nonneg u
    nlinarith

/-- Helper for Exercise 25.4.3: on the interval support `[-1, 1]`, the quadratic slice condition
is equivalent to the tail variable lying in the ball of radius `√(1 - s²)`. -/
private theorem mem_ball_sqrt_one_sub_sq_iff
    (k : ℕ) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (z : EuclideanSpace ℝ (Fin (k + 1))) :
    z ∈ Metric.ball 0 (Real.sqrt (1 - s ^ (2 : ℕ))) ↔
      s ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ) < 1 := by
  have hsq_le : s ^ (2 : ℕ) ≤ 1 := by
    rcases hs with ⟨hs_left, hs_right⟩
    nlinarith
  have hbase_nonneg : 0 ≤ 1 - s ^ (2 : ℕ) := by
    linarith
  rw [Metric.mem_ball, dist_eq_norm]
  constructor
  · intro hz
    have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - s ^ (2 : ℕ)) := Real.sqrt_nonneg _
    have hzsq_lt : ‖z‖ ^ (2 : ℕ) < 1 - s ^ (2 : ℕ) := by
      nlinarith
    -- Proof comment: after squaring the radius bound, the interval hypothesis rewrites the
    -- right-hand side back to the quadratic slice inequality.
    rw [Real.sq_sqrt hbase_nonneg] at hzsq_lt
    nlinarith
  · intro hz
    have hzsq_lt : ‖z‖ ^ (2 : ℕ) < 1 - s ^ (2 : ℕ) := by
      nlinarith
    have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - s ^ (2 : ℕ)) := Real.sqrt_nonneg _
    have hz_lt : ‖z‖ < Real.sqrt (1 - s ^ (2 : ℕ)) := by
      have hsqrt_sq : (Real.sqrt (1 - s ^ (2 : ℕ))) ^ (2 : ℕ) = 1 - s ^ (2 : ℕ) := by
        rw [pow_two]
        exact Real.sq_sqrt hbase_nonneg
      nlinarith
    -- Proof comment: conversely, the squared quadratic inequality recovers the fiber-radius bound.
    simpa using hz_lt

/-- Helper for Exercise 25.4.3: on a unit-sphere slice, the standard-axis denominator depends only
on the first coordinate. -/
private theorem unitSphereZeroAxisSliceDenominator_eq
    (k : ℕ) (ρ s : ℝ) (z : EuclideanSpace ℝ (Fin (k + 1)))
    (hslice : s ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ) = 1) :
    (s - ρ) ^ (2 : ℕ) + ‖z‖ ^ (2 : ℕ) = 1 - 2 * ρ * s + ρ ^ (2 : ℕ) := by
  -- Proof comment: substitute the slice equation `s² + ‖z‖² = 1` into the quadratic head-tail
  -- denominator and expand the remaining square.
  nlinarith

/-- Helper for Exercise 25.4.3: on the scalar support `[-1, 1]`, the head-tail slice denominator
for the zero-axis kernel stays strictly positive. -/
private theorem unitSphereZeroAxisSliceDenominator_pos
    (ρ s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    0 < 1 - 2 * ρ * s + ρ ^ (2 : ℕ) := by
  rcases hs with ⟨hs_left, hs_right⟩
  -- Proof comment: on `[-1,1]`, the slice denominator is bounded below by `(1 - ρ)^2`, which is
  -- strictly positive because `0 < ρ < 1`.
  nlinarith

/-- Helper for Exercise 25.4.3: once the slice denominator is isolated, the centered tail
integral collapses to the explicit unit-ball volume constant. -/
private theorem unitSphereZeroAxisCenteredTailIntegral_eq
    (k : ℕ) (ρ s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    ∫⁻ z, ENNReal.ofReal
        ((1 - ρ ^ (2 : ℕ)) /
          ((1 - 2 * ρ * s + ρ ^ (2 : ℕ)) + ‖z‖ ^ (2 : ℕ)) ^
            ((((k + 3 : ℕ) : ℝ) / 2)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) =
      ENNReal.ofReal
        (((1 - ρ ^ (2 : ℕ)) / (1 - 2 * ρ * s + ρ ^ (2 : ℕ))) *
          (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))).real (Metric.ball 0 1)) := by
  have hA :
      0 < 1 - 2 * ρ * s + ρ ^ (2 : ℕ) :=
    unitSphereZeroAxisSliceDenominator_pos ρ s hs hρpos hρlt
  have hC : 0 ≤ 1 - ρ ^ (2 : ℕ) := by
    -- Proof comment: the Poisson numerator is nonnegative on the interior branch `0 < ρ < 1`.
    nlinarith
  -- Proof comment: the remaining tail integral is exactly the centered radial integral already
  -- evaluated in the previous helper.
  simpa [add_comm, add_left_comm, add_assoc] using
    (centeredTailIntegral_eq_ofReal_mul_unitBallVolume
      (k := k) (A := 1 - 2 * ρ * s + ρ ^ (2 : ℕ)) (C := 1 - ρ ^ (2 : ℕ)) hA hC)

/-- Helper for Exercise 25.4.3: after reducing to `d = k + 2`, the only remaining normalization
frontier is the comparison between the normalized sphere integral and the scalar first-coordinate
mass of the weighted normalized sphere law. -/
private theorem unitSphereZeroAxisKernelIntegral_eq_one_succSucc
    (k : ℕ) (ρ : ℝ) (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    let ν : FiniteMeasure (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
      ⟨(volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).toSphere, inferInstance⟩
    ∫ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1,
      (1 - ρ ^ (2 : ℕ)) /
        dist
          (EuclideanSpace.single (0 : Fin (k + 2)) ρ :
            EuclideanSpace ℝ (Fin (k + 2)))
          (z : EuclideanSpace ℝ (Fin (k + 2))) ^ (k + 2) ∂
        (ν.mass⁻¹ •
          (ν : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1))) = 1 := by
  -- Route correction: the outer theorem no longer mixes the `d = k + 2` dimension reduction with
  -- the live scalarization blocker. This helper now holds the exact remaining frontier.
  let E : Type := EuclideanSpace ℝ (Fin (k + 2))
  let ν : FiniteMeasure (Metric.sphere (0 : E) 1) :=
    ⟨(volume : Measure E).toSphere, inferInstance⟩
  let weighted :
      Measure (Metric.sphere (0 : E) 1) :=
    ((ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))).withDensity
      (fun z ↦
        ENNReal.ofReal
          ((1 - ρ ^ (2 : ℕ)) /
            dist
              (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
              (z : E) ^ (k + 2))))
  let _ := weighted
  -- Route correction: this direct sphere-integral theorem is now the only live normalization
  -- frontier. The old cycle through the first-coordinate marginal has been removed.
  -- TODO: the tail-collapse side is now packaged in
  -- `unitSphereZeroAxisCenteredTailIntegral_eq`. What remains is only the sphere-side
  -- `toSphere` disintegration that rewrites the normalized unit-sphere integral into those
  -- scalar slice integrals.
  sorry

/-- Helper for Exercise 25.4.3: once the direct sphere integral is normalized to mass `1`, the
interval-supported first-coordinate marginal inherits the same mass. -/
private theorem unitSphereZeroAxisFirstCoordinateMarginalUnitIntervalMass_eq_one
    (k : ℕ) (ρ : ℝ) (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    let E : Type := EuclideanSpace ℝ (Fin (k + 2))
    let ν : FiniteMeasure (Metric.sphere (0 : E) 1) :=
      ⟨(volume : Measure E).toSphere, inferInstance⟩
    let weighted :
        Measure (Metric.sphere (0 : E) 1) :=
      ((ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))).withDensity
        (fun z ↦
          ENNReal.ofReal
            ((1 - ρ ^ (2 : ℕ)) /
              dist
                (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
                (z : E) ^ (k + 2))))
    (Measure.map (fun z : Metric.sphere (0 : E) 1 ↦ (z : E) 0) weighted).real
      (Set.Icc (-1 : ℝ) 1) = 1 := by
  let E : Type := EuclideanSpace ℝ (Fin (k + 2))
  let ν : FiniteMeasure (Metric.sphere (0 : E) 1) :=
    ⟨(volume : Measure E).toSphere, inferInstance⟩
  let weighted :
      Measure (Metric.sphere (0 : E) 1) :=
    ((ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))).withDensity
      (fun z ↦
        ENNReal.ofReal
          ((1 - ρ ^ (2 : ℕ)) /
            dist
              (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
              (z : E) ^ (k + 2))))
  have hintervalMass :
      ∫ z : Metric.sphere (0 : E) 1,
          (1 - ρ ^ (2 : ℕ)) /
            dist
              (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
              (z : E) ^ (k + 2) ∂
            (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))) =
        (Measure.map (fun z : Metric.sphere (0 : E) 1 ↦ (z : E) 0) weighted).real
          (Set.Icc (-1 : ℝ) 1) := by
    -- Proof comment: the earlier integral-to-marginal theorem already identifies the exact
    -- weighted sphere integral with the interval mass of the first-coordinate marginal.
    simpa [weighted, ν] using
      unitSphereZeroAxisKernelIntegral_eq_firstCoordinateMarginalUnitIntervalMass
        k ρ hρpos hρlt
  have hkernel :
      ∫ z : Metric.sphere (0 : E) 1,
          (1 - ρ ^ (2 : ℕ)) /
            dist
              (EuclideanSpace.single (0 : Fin (k + 2)) ρ : E)
              (z : E) ^ (k + 2) ∂
            (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : E) 1))) = 1 := by
    -- Proof comment: the new direct normalization theorem is now the only substantive input.
    simpa [weighted, ν] using
      unitSphereZeroAxisKernelIntegral_eq_one_succSucc k ρ hρpos hρlt
  -- Proof comment: composing the integral-to-marginal identity with the direct normalization
  -- theorem turns the first-coordinate interval mass into `1`.
  exact hintervalMass.symm.trans hkernel

/-- Helper for Exercise 25.4.3: in dimensions other than `1`, the normalized unit-sphere Poisson
kernel should be closed by pushing the normalized sphere law to one scalar coordinate after the
pole has been moved to the standard zeroth axis. -/
private theorem unitSphereZeroAxisKernelIntegral_eq_one
    (ρ : ℝ) (hρpos : 0 < ρ) (hρlt : ρ < 1) :
  let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
      ⟨(volume : Measure State).toSphere, inferInstance⟩
    ∫ z : Metric.sphere (0 : State) 1,
      (1 - ρ ^ (2 : ℕ)) /
        dist
          (EuclideanSpace.single
            (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d) ρ :
              EuclideanSpace ℝ (Fin d))
          (z : State) ^ d ∂
        (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) = 1 := by
  by_cases hd1 : d = 1
  · subst hd1
    let ξ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single (0 : Fin 1) ρ
    have hξ : ξ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
      -- Proof comment: in dimension `1`, the zero-axis point is the unique interior point with
      -- Euclidean norm `ρ`, so the unit-ball condition is exactly `ρ < 1`.
      have hnorm : ‖ξ‖ < 1 := by
        simpa [ξ, Real.norm_eq_abs, abs_of_pos hρpos] using hρlt
      simpa [Metric.mem_ball, dist_eq_norm] using hnorm
    -- Proof comment: the one-dimensional branch is exactly the already established `S⁰`
    -- normalization theorem.
    simpa [ξ, unitSphereFinOneBoundaryFiniteMeasure] using
      unitSpherePoissonKernelIntegral_eq_one_finOne ξ hξ
  · have hdim : ∃ k : ℕ, d = k + 2 := by
      have hd0 : d ≠ 0 := NeZero.ne d
      cases d with
      | zero =>
          exact (hd0 rfl).elim
      | succ d' =>
          cases d' with
          | zero =>
              exact (hd1 rfl).elim
          | succ k =>
          exact ⟨k, rfl⟩
    rcases hdim with ⟨k, rfl⟩
    -- Proof comment: after the dimension split, all remaining work is isolated in the dedicated
    -- `d = k + 2` scalarization theorem above.
    exact unitSphereZeroAxisKernelIntegral_eq_one_succSucc k ρ hρpos hρlt

/-- Helper for Exercise 25.4.3: the generic axis parameter is reduced to the standard zeroth-axis
normalization theorem by an orthogonal change of coordinates; the remaining scalar blocker is only
the zero-axis case. -/
private theorem unitSphereAxisKernelIntegral_eq_one
    (ρ : ℝ) (hρpos : 0 < ρ) (hρlt : ρ < 1) (i0 : Fin d) :
  let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
      ⟨(volume : Measure State).toSphere, inferInstance⟩
    ∫ z : Metric.sphere (0 : State) 1,
      (1 - ρ ^ (2 : ℕ)) /
        dist (EuclideanSpace.single i0 ρ : EuclideanSpace ℝ (Fin d)) (z : State) ^ d ∂
        (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) = 1 := by
  by_cases hd1 : d = 1
  · subst hd1
    have hi0 : i0 = (0 : Fin 1) := Subsingleton.elim _ _
    subst hi0
    let ξ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single (0 : Fin 1) ρ
    have hξ : ξ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
      -- Proof comment: the one-dimensional axis point has norm `ρ`, so the radius condition is
      -- exactly the scalar inequality `ρ < 1`.
      have hnorm : ‖ξ‖ < 1 := by
        simpa [ξ, Real.norm_eq_abs, abs_of_pos hρpos] using hρlt
      simpa [Metric.mem_ball, dist_eq_norm] using hnorm
    -- Proof comment: in dimension `1`, the generic axis is the unique endpoint axis, so the
    -- explicit `S⁰` normalization theorem closes the integral directly.
    simpa [ξ, unitSphereFinOneBoundaryFiniteMeasure] using
      unitSpherePoissonKernelIntegral_eq_one_finOne ξ hξ
  · let iFirst : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    let u : State := EuclideanSpace.single i0 1
    have hu : ‖u‖ = 1 := by
      -- Proof comment: the coordinate axis vector has unit norm, so it can be chosen as the
      -- first vector of an orthonormal basis.
      simpa [u] using (EuclideanSpace.norm_single i0 (1 : ℝ))
    obtain ⟨b, hb0⟩ := exists_orthonormalBasis_first_eq (d := d) hu
    let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
      ⟨(volume : Measure State).toSphere, inferInstance⟩
    let μ : Measure (Metric.sphere (0 : State) 1) :=
      ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))
    let e := unitSphereMeasurableEquiv (d := d) b
    let axisKernel : Metric.sphere (0 : State) 1 → ℝ :=
      fun z ↦
        (1 - ρ ^ (2 : ℕ)) /
          dist (EuclideanSpace.single iFirst ρ : EuclideanSpace ℝ (Fin d))
            (z : State) ^ d
    have hsingle : (EuclideanSpace.single i0 ρ : State) = ρ • u := by
      ext j
      by_cases hji : j = i0
      · subst hji
        simp [u, EuclideanSpace.single]
      · simp [u, EuclideanSpace.single, hji]
    have hAxisIntegrand :
        ∀ z : Metric.sphere (0 : State) 1,
          (1 - ρ ^ (2 : ℕ)) / dist (EuclideanSpace.single i0 ρ : State) (z : State) ^ d =
            axisKernel (e z) := by
      intro z
      -- Proof comment: after rewriting the pole as `ρ • u`, the orthonormal basis transport
      -- sends the generic axis to the standard zeroth axis.
      rw [hsingle]
      calc
        (1 - ρ ^ (2 : ℕ)) / dist (ρ • u) (z : State) ^ d
            = (1 - ‖ρ • u‖ ^ (2 : ℕ)) / dist (ρ • u) (z : State) ^ d := by
                congr 1
                simp [norm_smul, hu, Real.norm_eq_abs, abs_of_pos hρpos]
        _ = axisKernel (e z) := by
              simpa [axisKernel, e, unitSphereMeasurableEquiv] using
                (unitSpherePoissonIntegrand_eq_axisIntegrand
                  (d := d) ρ hρpos (v := u) hu b iFirst hb0 z)
    have hmapSphere : Measure.map e μ = μ := by
      -- Proof comment: the normalized unit-sphere boundary law is invariant under orthogonal
      -- coordinate changes.
      simpa [μ, e] using
        unitSphereMeasurableEquiv_map_normalizedBoundaryMeasure (d := d) b
    have htransport :
        ∫ z : Metric.sphere (0 : State) 1,
            (1 - ρ ^ (2 : ℕ)) / dist (EuclideanSpace.single i0 ρ : State) (z : State) ^ d ∂ μ =
          ∫ z : Metric.sphere (0 : State) 1, axisKernel z ∂ μ := by
      -- Proof comment: rewrite the generic axis integrand through the orthogonal coordinates, then
      -- use invariance of the normalized sphere law to remove the coordinate change from the
      -- argument.
      calc
        ∫ z : Metric.sphere (0 : State) 1,
            (1 - ρ ^ (2 : ℕ)) / dist (EuclideanSpace.single i0 ρ : State) (z : State) ^ d ∂ μ =
          ∫ z : Metric.sphere (0 : State) 1, axisKernel (e z) ∂ μ := by
              refine integral_congr_ae ?_
              filter_upwards with z
              simpa using hAxisIntegrand z
        _ = ∫ z : Metric.sphere (0 : State) 1, axisKernel z ∂ Measure.map e μ := by
              symm
              simpa [e] using
                (integral_map_equiv e axisKernel (μ := μ))
        _ = ∫ z : Metric.sphere (0 : State) 1, axisKernel z ∂ μ := by
              rw [hmapSphere]
    -- Proof comment: the generic axis case is now reduced to the single standard-axis scalar
    -- normalization theorem introduced just above.
    simpa [μ, axisKernel] using
      htransport.trans (unitSphereZeroAxisKernelIntegral_eq_one (d := d) ρ hρpos hρlt)

/-- Helper for Exercise 25.4.3: in dimensions other than `1`, the normalized unit-sphere Poisson
kernel reduces to the standard-axis normalization theorem. -/
private theorem unitSpherePoissonKernelIntegral_eq_one_highDim
    (ξ : State) (hξ : ξ ∈ Metric.ball (0 : State) 1) (hd1 : d ≠ 1) :
    let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
      ⟨(volume : Measure State).toSphere, inferInstance⟩
    ∫ u : Metric.sphere (0 : State) 1,
      (1 - ‖ξ‖ ^ (2 : ℕ)) / dist ξ (u : State) ^ d ∂
        (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) = 1 := by
  -- Route correction: replace the failed full-sphere self-map transport by the scalar pushforward
  -- route from the re-plan. The remaining frontier is now one theorem body instead of the former
  -- orthogonal-transport plus axis-integral pair.
  let _ := hd1
  by_cases hξ0 : ξ = 0
  · subst hξ0
    let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
      ⟨(volume : Measure State).toSphere, inferInstance⟩
    letI : Nontrivial State := by infer_instance
    have hν_ne : (ν : Measure (Metric.sphere (0 : State) 1)) ≠ 0 := by
      simpa [ν] using
        (Measure.toSphere_ne_zero (μ := (volume : Measure State)))
    have hν_ne_fin : ν ≠ 0 := by
      intro hν0
      exact hν_ne (by simpa [ν, hν0])
    have hSphereNonempty : Nonempty (Metric.sphere (0 : State) 1) := by
      exact
        @NormedSpace.sphere_nonempty_rclike ℝ inferInstance State
          inferInstance inferInstance inferInstance 1 zero_le_one
    letI : NeZero (ν : Measure (Metric.sphere (0 : State) 1)) := ⟨hν_ne⟩
    have hνprob :
        IsProbabilityMeasure (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) := by
      -- Proof comment: normalizing the nonzero unit-sphere reference measure gives the mass-one
      -- boundary law used throughout the unit-ball reduction.
      rw [← @FiniteMeasure.toMeasure_normalize_eq_of_nonzero
        (Metric.sphere (0 : State) 1) hSphereNonempty _ ν hν_ne_fin]
      infer_instance
    let _ : IsProbabilityMeasure (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) :=
      hνprob
    -- Proof comment: at the centered start the unit-ball kernel is identically `1`, so the
    -- normalized sphere integral is just the total mass of the probability measure.
    calc
      ∫ u : Metric.sphere (0 : State) 1,
          (1 - ‖(0 : State)‖ ^ (2 : ℕ)) / dist (0 : State) (u : State) ^ d ∂
            (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) =
        ∫ _u : Metric.sphere (0 : State) 1, (1 : ℝ) ∂
            (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) := by
          refine integral_congr_ae ?_
          filter_upwards with u
          have hu_dist : dist (0 : State) (u : State) = 1 := by
            simpa [Metric.mem_sphere, dist_eq_norm] using u.property
          simp [hu_dist]
      _ = 1 := by
          simpa using
            (measure_univ :
              (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) Set.univ = 1)
  · let ρ : ℝ := ‖ξ‖
    let v : State := ρ⁻¹ • ξ
    let i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
      ⟨(volume : Measure State).toSphere, inferInstance⟩
    have hρpos : 0 < ρ := by
      -- Proof comment: the nonzero branch forces `‖ξ‖` to be strictly positive.
      exact norm_pos_iff.mpr hξ0
    have hρlt : ρ < 1 := by
      -- Proof comment: interior points of the unit ball have norm strictly less than `1`.
      simpa [ρ, Metric.mem_ball, dist_eq_norm] using hξ
    have hξ_eq : ρ • v = ξ := by
      -- Proof comment: `v` is the normalized direction of `ξ`, so rescaling by `ρ = ‖ξ‖`
      -- recovers `ξ`.
      dsimp [ρ, v]
      rw [smul_smul, mul_inv_cancel₀, one_smul]
      exact norm_ne_zero_iff.mpr hξ0
    have hv : ‖v‖ = 1 := by
      -- Proof comment: taking norms in the normalization identity shows that `v` lies on the
      -- unit sphere.
      have hnorm : ρ * ‖v‖ = ρ := by
        simpa [ρ, Real.norm_eq_abs, abs_of_pos hρpos, norm_smul] using congrArg norm hξ_eq
      nlinarith [hρpos, norm_nonneg v, hnorm]
    obtain ⟨b, hb0⟩ := exists_orthonormalBasis_first_eq (d := d) hv
    have hAxisIntegrand :
        ∀ u : Metric.sphere (0 : State) 1,
          (1 - ‖ξ‖ ^ (2 : ℕ)) / dist ξ (u : State) ^ d =
            (1 - ρ ^ (2 : ℕ)) /
              dist (EuclideanSpace.single i0 ρ : EuclideanSpace ℝ (Fin d))
                (b.repr (u : State)) ^ d := by
      intro u
      -- Proof comment: rewrite `ξ` as `ρ • v` once, then transport the kernel to the standard
      -- axis in the orthonormal coordinates of `b`.
      rw [← hξ_eq]
      simpa using
        unitSpherePoissonIntegrand_eq_axisIntegrand
          (d := d) ρ hρpos hv b i0 hb0 u
    let μ : Measure (Metric.sphere (0 : State) 1) :=
      ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))
    let e := unitSphereMeasurableEquiv (d := d) b
    let axisKernel : Metric.sphere (0 : State) 1 → ℝ :=
      fun z ↦
        (1 - ρ ^ (2 : ℕ)) /
          dist (EuclideanSpace.single i0 ρ : EuclideanSpace ℝ (Fin d))
            (z : State) ^ d
    have hmapSphere : Measure.map e μ = μ := by
      -- Proof comment: the normalized boundary law is invariant under the orthogonal coordinate
      -- change determined by `b`.
      simpa [μ, e] using
        unitSphereMeasurableEquiv_map_normalizedBoundaryMeasure (d := d) b
    have htransport :
        ∫ u : Metric.sphere (0 : State) 1,
            (1 - ‖ξ‖ ^ (2 : ℕ)) / dist ξ (u : State) ^ d ∂ μ =
          ∫ z : Metric.sphere (0 : State) 1, axisKernel z ∂ μ := by
      -- Proof comment: first rewrite the integrand through the orthogonal coordinates, then use
      -- invariance of the normalized sphere law to move `b.repr` off the argument.
      calc
        ∫ u : Metric.sphere (0 : State) 1,
            (1 - ‖ξ‖ ^ (2 : ℕ)) / dist ξ (u : State) ^ d ∂ μ =
          ∫ u : Metric.sphere (0 : State) 1, axisKernel (e u) ∂ μ := by
              refine integral_congr_ae ?_
              filter_upwards with u
              simpa [axisKernel, e, unitSphereMeasurableEquiv] using hAxisIntegrand u
        _ = ∫ z : Metric.sphere (0 : State) 1, axisKernel z ∂ Measure.map e μ := by
              symm
              simpa [e] using
                (integral_map_equiv e axisKernel (μ := μ))
        _ = ∫ z : Metric.sphere (0 : State) 1, axisKernel z ∂ μ := by
              rw [hmapSphere]
    have hAxisIntegral :
        ∫ z : Metric.sphere (0 : State) 1, axisKernel z ∂ μ = 1 := by
      -- Proof comment: the orthogonal-transport work is now finished; the only remaining input is
      -- the standard-axis normalization statement extracted above.
      simpa [μ, axisKernel] using unitSphereAxisKernelIntegral_eq_one (d := d) ρ hρpos hρlt i0
    -- Proof comment: the live frontier has now been reduced to the canonical standard-axis sphere
    -- integral with respect to the unchanged normalized boundary law.
    simpa [μ] using htransport.trans hAxisIntegral

private theorem unitSpherePoissonKernelIntegral_eq_one
    (ξ : State) (hξ : ξ ∈ Metric.ball (0 : State) 1) :
    let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
      ⟨(volume : Measure State).toSphere, inferInstance⟩
    ∫ u : Metric.sphere (0 : State) 1,
      (1 - ‖ξ‖ ^ (2 : ℕ)) / dist ξ (u : State) ^ d ∂
        (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) = 1 := by
  by_cases hd1 : d = 1
  · subst hd1
    -- Proof comment: the `d = 1` normalization is now packaged as the explicit average of the
    -- two endpoint atoms on `S⁰`.
    exact unitSpherePoissonKernelIntegral_eq_one_finOne ξ hξ
  · -- Route correction: the old blocker is now isolated to the genuine positive-dimension case.
    -- The remaining route is now the single scalar-pushforward normalization theorem from the
    -- current plan, so the main theorem body no longer mixes transport and scalarization.
    exact unitSpherePoissonKernelIntegral_eq_one_highDim ξ hξ hd1

/-- Helper for Exercise 25.4.3: the missing normalization statement for the explicit
Poisson-kernel measure on the boundary sphere. -/
theorem openBallPoissonKernelIntegral_eq_one
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    ∫ y, openBallPoissonKernel r x y ∂ openBallBoundaryMeasure r = 1 := by
  by_cases hx0 : x = 0
  · subst hx0
    -- Proof comment: the centered start is already normalized by the preceding constant-kernel
    -- calculation.
    exact openBallPoissonKernelIntegral_eq_one_zero r hr
  · let ξ : State := |r|⁻¹ • x
    have hξ : ξ ∈ Metric.ball (0 : State) 1 :=
      invAbsRadius_smul_mem_unitBall r hr hx
    -- Proof comment: after the new transport lemma, the nonzero branch is reduced to the single
    -- canonical unit-sphere normalization theorem.
    calc
      ∫ y, openBallPoissonKernel r x y ∂ openBallBoundaryMeasure r =
          let ν : FiniteMeasure (Metric.sphere (0 : State) 1) :=
            ⟨(volume : Measure State).toSphere, inferInstance⟩
          ∫ u : Metric.sphere (0 : State) 1,
            (1 - ‖ξ‖ ^ (2 : ℕ)) / dist ξ (u : State) ^ d ∂
              (ν.mass⁻¹ • (ν : Measure (Metric.sphere (0 : State) 1))) := by
        simpa [ξ] using openBallPoissonKernelIntegral_eq_unitSphereIntegral r hr hx
      _ = 1 := by
        simpa [ξ] using unitSpherePoissonKernelIntegral_eq_one ξ hξ

/-- Helper for Exercise 25.4.3: the missing normalization statement for the explicit
Poisson-kernel measure on the boundary sphere. -/
theorem openBallPoissonKernelMeasure_isProbability
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    IsProbabilityMeasure (openBallPoissonKernelMeasure r x) := by
  -- Proof comment: the real mass formula reduces the probability claim to the scalar
  -- normalization identity isolated just above.
  refine (MeasureTheory.isProbabilityMeasure_iff_real.2 ?_)
  rw [openBallPoissonKernelMeasure_real_univ_eq_integral r hr hx]
  exact openBallPoissonKernelIntegral_eq_one r hr hx

/-- Helper for Exercise 25.4.3: the Poisson extension of the zero boundary datum vanishes
identically. -/
theorem openBallPoissonExtension_zero
    (r : ℝ) (x : State) :
    openBallPoissonExtension
        r (0 : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) x = 0 := by
  -- Proof comment: the defining boundary integral has zero integrand.
  simp [openBallPoissonExtension]

/-- Helper for Exercise 25.4.3: for an interior start point, the Poisson extension is additive in
the boundary datum. This is the linearity needed to split the boundary-limit problem into a
constant part and an oscillation part. -/
theorem openBallPoissonExtension_add
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r)
    (g₁ g₂ : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    openBallPoissonExtension r (g₁ + g₂) x =
      openBallPoissonExtension r g₁ x +
        openBallPoissonExtension r g₂ x := by
  let _ : IsFiniteMeasure (openBallPoissonKernelMeasure r x) :=
    openBallPoissonKernelMeasure_isFinite r hr hx
  have hg₁ : Integrable g₁ (openBallPoissonKernelMeasure r x) := by
    -- Proof comment: bounded continuous functions are integrable against the finite
    -- Poisson-kernel measure.
    simpa using g₁.integrable (openBallPoissonKernelMeasure r x)
  have hg₂ : Integrable g₂ (openBallPoissonKernelMeasure r x) := by
    -- Proof comment: the same finiteness argument applies to the second boundary datum.
    simpa using g₂.integrable (openBallPoissonKernelMeasure r x)
  -- Proof comment: linearity of the Lebesgue integral gives the desired Poisson-extension sum
  -- formula.
  simpa [openBallPoissonExtension] using integral_add hg₁ hg₂

/-- Helper for Exercise 25.4.3: for an interior start point, the Poisson extension preserves
subtraction of boundary data. -/
theorem openBallPoissonExtension_sub
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r)
    (g₁ g₂ : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    openBallPoissonExtension r (g₁ - g₂) x =
      openBallPoissonExtension r g₁ x -
        openBallPoissonExtension r g₂ x := by
  let _ : IsFiniteMeasure (openBallPoissonKernelMeasure r x) :=
    openBallPoissonKernelMeasure_isFinite r hr hx
  have hg₁ : Integrable g₁ (openBallPoissonKernelMeasure r x) := by
    -- Proof comment: bounded continuous functions remain integrable against the finite
    -- Poisson-kernel measure.
    simpa using g₁.integrable (openBallPoissonKernelMeasure r x)
  have hg₂ : Integrable g₂ (openBallPoissonKernelMeasure r x) := by
    -- Proof comment: the second integrability input is identical.
    simpa using g₂.integrable (openBallPoissonKernelMeasure r x)
  -- Proof comment: subtraction is the second linearity identity needed for the oscillation split.
  simpa [openBallPoissonExtension] using integral_sub hg₁ hg₂

/-- Helper for Exercise 25.4.3: the raw Poisson-extension owner vanishes on the frontier of the
open ball. This is the reason the Dirichlet package must be built from a patched boundary-aware
owner instead of using `openBallPoissonExtension` itself on `frontier (Metric.ball (0 : State) r)`.
-/
theorem openBallPoissonExtension_eq_zero_of_mem_frontier
    (r : ℝ) (hr : 0 < r) {x : State}
    (hx : x ∈ frontier (Metric.ball (0 : State) r))
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    openBallPoissonExtension r g x = 0 := by
  have hxSphere : x ∈ Metric.sphere (0 : State) |r| := by
    simpa [openBallFrontier_eq_sphereAbs (d := d) r hr] using hx
  have hnorm : ‖x‖ = |r| := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hxSphere
  have hkernel_zero :
      ∀ y : Metric.sphere (0 : State) |r|,
        openBallPoissonKernel r x y = 0 := by
    intro y
    have hnum_zero :
        |r| ^ d * (|r| ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ)) = 0 := by
      rw [hnorm]
      ring_nf
    rw [openBallPoissonKernel, hnum_zero, zero_div]
  have hkernel_zero_enn :
      (fun y : Metric.sphere (0 : State) |r| ↦
        ENNReal.ofReal (openBallPoissonKernel r x y)) = 0 := by
    ext y
    simp [hkernel_zero y]
  have hmeasure_zero : openBallPoissonKernelMeasure r x = 0 := by
    -- Proof comment: once the density is pointwise zero, the with-density measure is the zero
    -- measure.
    simp [openBallPoissonKernelMeasure, hkernel_zero_enn]
  -- Proof comment: on the boundary the Poisson numerator vanishes, so every kernel section is
  -- zero and hence the whole Poisson-kernel measure is zero.
  simp [openBallPoissonExtension, hmeasure_zero]

/-- Helper for Exercise 25.4.3: finite Borel measures on the boundary sphere are determined by
their integrals against bounded continuous functions. -/
theorem boundarySphereMeasure_eq_ofBcfIntegrals
    {μ ν : Measure (Metric.sphere (0 : State) |r|)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h :
      ∀ g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ,
        ∫ y, g y ∂ μ = ∫ y, g y ∂ ν) :
    μ = ν := by
  -- Proof comment: the boundary sphere is a compact metric space, so finite Borel measures are
  -- determined by their bounded-continuous test-function integrals.
  exact MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure h

/-- Helper for Exercise 25.4.3: the open ball is an admissible Dirichlet domain for the Brownian
representation theorem because it is open and its closure is compact. -/
theorem isOpen_isCompact_closure_openBall
    (r : ℝ) (hr : 0 < r) :
    IsOpen (Metric.ball (0 : State) r) ∧ IsCompact (closure (Metric.ball (0 : State) r)) := by
  constructor
  · -- Proof comment: openness is the standard metric-ball fact.
    exact Metric.isOpen_ball
  · -- Proof comment: in finite-dimensional Euclidean space, the closure of a positive-radius ball
    -- is the corresponding closed ball, hence compact.
    simpa [closure_ball (0 : State) hr.ne'] using
      (isCompact_closedBall (0 : State) r)

/-- Helper for Exercise 25.4.3: compact closure forces the frontier to be compact as well. -/
private theorem isCompact_frontier_of_isCompact_closure
    {G : Set State} (hGcpt : IsCompact (closure G)) :
    IsCompact (frontier G) :=
  IsCompact.of_isClosed_subset hGcpt isClosed_frontier frontier_subset_closure

/-- Helper for Exercise 25.4.3: a Dirichlet solution already provides a continuous boundary datum
on the frontier. -/
private theorem continuous_boundaryDatum_of_solvesDirichletProblem
    {G : Set State} {f : frontier G → ℝ} {u : State → ℝ}
    (hu : SolvesDirichletProblem G f u) :
    Continuous f := by
  have hcont_u : Continuous (fun y : frontier G ↦ u y) := by
    -- Proof comment: continuity on `closure G` restricts to continuity on the frontier subtype.
    exact continuousOn_iff_continuous_restrict.mp
      (hu.continuousOn_closure.mono frontier_subset_closure)
  -- Proof comment: on the frontier, the Dirichlet solution already agrees with the boundary datum.
  refine hcont_u.congr ?_
  intro y
  exact hu.boundary_eq y

/-- Helper for Exercise 25.4.3: compactness of the frontier makes the boundary datum strongly
measurable for harmonic measure. -/
private theorem aestronglyMeasurable_boundaryDatum_harmonicMeasure
    (P : State → ProbabilityMeasure Ω) (G : Set State)
    (exitValue : Ω → frontier G) (hExitMeas : Measurable exitValue)
    {f : frontier G → ℝ} {u : State → ℝ}
    (hGcpt : IsCompact (closure G)) (hu : SolvesDirichletProblem G f u) (x : G) :
    AEStronglyMeasurable f
      (harmonicMeasure P G exitValue hExitMeas x : Measure (frontier G)) := by
  letI : CompactSpace (frontier G) :=
    isCompact_iff_compactSpace.mp (isCompact_frontier_of_isCompact_closure hGcpt)
  -- Proof comment: continuous functions on a compact frontier are strongly measurable for every
  -- Borel probability measure, in particular for the harmonic measure.
  exact
    (continuous_boundaryDatum_of_solvesDirichletProblem hu).aestronglyMeasurable_of_compactSpace

/-- Helper for Exercise 25.4.3: once the exit time from `U` is finite, the stage-stopped path is
eventually constant along deterministic integer horizons. -/
private theorem tendsto_stageStoppedProcess_nat_to_stoppedValue
    {W : VectorProcess} {U : Set State} {ω : Ω}
    (hτfin : hittingAfter W Uᶜ 0 ω < ⊤) :
    Filter.Tendsto
      (fun n : ℕ ↦ stoppedProcess W (hittingAfter W Uᶜ 0) n ω)
      Filter.atTop
      (𝓝 (stoppedValue W (hittingAfter W Uᶜ 0) ω)) := by
  have hEventuallyEq :
      (fun n : ℕ ↦ stoppedProcess W (hittingAfter W Uᶜ 0) n ω) =ᶠ[Filter.atTop]
        fun _ ↦ stoppedValue W (hittingAfter W Uᶜ 0) ω := by
    filter_upwards
        [tendsto_natCast_atTop_atTop.eventually_ge_atTop
          ((hittingAfter W Uᶜ 0 ω).untopA)] with n hn
    have hτn : hittingAfter W Uᶜ 0 ω ≤ (n : ENNReal) :=
      (WithTop.untopA_le_iff
        (x := hittingAfter W Uᶜ 0 ω) (hx := ne_top_of_lt hτfin)).1 hn
    -- Proof comment: once the deterministic horizon dominates the finite exit time, the stopped
    -- path has already frozen at the terminal exit value.
    simpa [stoppedValue] using
      (stoppedProcess_eq_of_ge
        (u := W) (τ := hittingAfter W Uᶜ 0) (ω := ω) (i := (n : NNReal)) hτn)
  exact Filter.Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds

/-- Helper for Exercise 25.4.3: composing the stage-stopped path with a continuous function
preserves convergence to the terminal stopped value. -/
private theorem tendsto_stageStoppedExtension_nat_to_stoppedValue
    {W : VectorProcess} {U : Set State} {F : State → ℝ} {ω : Ω}
    (hτfin : hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcont : Continuous F) :
    Filter.Tendsto
      (fun n : ℕ ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) n ω))
      Filter.atTop
      (𝓝 (F (stoppedValue W (hittingAfter W Uᶜ 0) ω))) := by
  -- Proof comment: the stage-stopped path is eventually constant, so continuity of `F`
  -- transports the limit to the terminal stopped value.
  exact hFcont.continuousAt.tendsto.comp <|
    tendsto_stageStoppedProcess_nat_to_stoppedValue (W := W) (U := U) hτfin

/-- Helper for Exercise 25.4.3: once the exit time is finite, the deterministic stopped Dirichlet
values converge to the boundary datum at the exit position. -/
private theorem tendsto_stageStoppedDirichlet_to_boundaryValue
    {G : Set State} {W : VectorProcess} {ω : Ω}
    {exitValue : Ω → frontier G} {f : frontier G → ℝ} {u : State → ℝ}
    (hτ : hittingAfter W Gᶜ 0 ω < ⊤)
    (hExit : (exitValue ω : State) = stoppedValue W (hittingAfter W Gᶜ 0) ω)
    (hu : SolvesDirichletProblem G f u) :
    Filter.Tendsto
      (fun n : ℕ ↦ u (stoppedProcess W (hittingAfter W Gᶜ 0) n ω))
      Filter.atTop
      (𝓝 (f (exitValue ω))) := by
  have hEventuallyEq :
      (fun n : ℕ ↦ u (stoppedProcess W (hittingAfter W Gᶜ 0) n ω)) =ᶠ[Filter.atTop]
        fun _ ↦ u (stoppedValue W (hittingAfter W Gᶜ 0) ω) := by
    filter_upwards
        [tendsto_natCast_atTop_atTop.eventually_ge_atTop
          ((hittingAfter W Gᶜ 0 ω).untopA)] with n hn
    have hτn : hittingAfter W Gᶜ 0 ω ≤ (n : ENNReal) :=
      (WithTop.untopA_le_iff
        (x := hittingAfter W Gᶜ 0 ω) (hx := ne_top_of_lt hτ)).1 hn
    -- Proof comment: once the deterministic horizon dominates the finite exit time, the stopped
    -- path has already frozen at the terminal exit value.
    simpa [stoppedValue] using
      congrArg u
        (stoppedProcess_eq_of_ge
          (u := W) (τ := hittingAfter W Gᶜ 0) (ω := ω) (i := (n : NNReal)) hτn)
  have hLimitToStopped :
      Filter.Tendsto
        (fun n : ℕ ↦ u (stoppedProcess W (hittingAfter W Gᶜ 0) n ω))
        Filter.atTop
        (𝓝 (u (stoppedValue W (hittingAfter W Gᶜ 0) ω))) :=
    Filter.Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
  have hBoundary :
      u (stoppedValue W (hittingAfter W Gᶜ 0) ω) = f (exitValue ω) := by
    calc
      u (stoppedValue W (hittingAfter W Gᶜ 0) ω) = u (exitValue ω : State) := by
        rw [← hExit]
      _ = f (exitValue ω) := hu.boundary_eq (exitValue ω)
  -- Proof comment: finite exit freezes the deterministic stopped path, and the exit-value
  -- identification turns that terminal value into the boundary datum.
  simpa [hBoundary] using hLimitToStopped

/-- Helper for Exercise 25.4.3: if two paths agree at every deterministic time, then their
`hittingAfter` clocks against a fixed target and the corresponding stopped values agree as well.
-/
private theorem hittingAfter_stoppedValue_eq_of_forall_eq
    {A : Set State} {W Wc : VectorProcess} {ω : Ω}
    (hall : ∀ t : NNReal, W t ω = Wc t ω) :
    hittingAfter W A 0 ω = hittingAfter Wc A 0 ω ∧
      stoppedValue W (hittingAfter W A 0) ω =
        stoppedValue Wc (hittingAfter Wc A 0) ω := by
  have hHit :
      hittingAfter W A 0 ω = hittingAfter Wc A 0 ω := by
    classical
    unfold hittingAfter
    by_cases h : ∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ A
    · have h' : ∃ j, (0 : NNReal) ≤ j ∧ Wc j ω ∈ A := by
        rcases h with ⟨j, hj0, hjA⟩
        exact ⟨j, hj0, by simpa [hall j] using hjA⟩
      have hSet :
          {j : NNReal | (0 : NNReal) ≤ j ∧ W j ω ∈ A} =
            {j : NNReal | (0 : NNReal) ≤ j ∧ Wc j ω ∈ A} := by
        ext j
        simp [hall j]
      rw [if_pos h, if_pos h']
      exact congrArg (fun s : Set NNReal ↦ (((sInf s : NNReal) : WithTop NNReal))) hSet
    · have h' : ¬ ∃ j, (0 : NNReal) ≤ j ∧ Wc j ω ∈ A := by
        intro h'
        apply h
        rcases h' with ⟨j, hj0, hjA⟩
        exact ⟨j, hj0, by simpa [hall j] using hjA⟩
      rw [if_neg h, if_neg h']
  refine ⟨hHit, ?_⟩
  calc
    stoppedValue W (hittingAfter W A 0) ω = W (hittingAfter W A 0 ω).untopA ω := rfl
    _ = Wc (hittingAfter W A 0 ω).untopA ω := by simpa using hall _
    _ = Wc (hittingAfter Wc A 0 ω).untopA ω := by rw [hHit]
    _ = stoppedValue Wc (hittingAfter Wc A 0) ω := rfl

/-- Helper for Exercise 25.4.3: the exit clock and exit value agree almost surely between a
Brownian path and a same-space continuous modification that coincides with it at every time
outside one null set. -/
private theorem stageExitStoppedValue_ae_eq_continuousVersion
    {μ : Measure Ω} {W Wc : VectorProcess} {U : Set State}
    (hEq : ∀ᵐ ω ∂μ, ∀ t : NNReal, W t ω = Wc t ω) :
    ∀ᵐ ω ∂μ,
      hittingAfter W Uᶜ 0 ω = hittingAfter Wc Uᶜ 0 ω ∧
        stoppedValue W (hittingAfter W Uᶜ 0) ω =
          stoppedValue Wc (hittingAfter Wc Uᶜ 0) ω := by
  filter_upwards [hEq] with ω hω
  simpa using hittingAfter_stoppedValue_eq_of_forall_eq (A := Uᶜ) hω

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 25.4.3: a continuous path that hits a closed target by finite time lands in
that target at the hitting time. -/
private theorem mem_closedSet_at_hittingAfter_of_lt_top_local
    {A : Set State} {W : VectorProcess} {ω : Ω}
    (hAclosed : IsClosed A)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hτ : hittingAfter W A 0 ω < ⊤) :
    W (hittingAfter W A 0 ω).untopA ω ∈ A := by
  have hτ_ne_top : hittingAfter W A 0 ω ≠ ⊤ := ne_of_lt hτ
  let hitSet : Set NNReal := {t : NNReal | W t ω ∈ A}
  have hHitExists : ∃ t : NNReal, W t ω ∈ A := by
    simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hτ_ne_top
    rcases hτ_ne_top with ⟨t, _, htA⟩
    exact ⟨t, htA⟩
  have hHitNonempty : hitSet.Nonempty := by
    rcases hHitExists with ⟨t, htA⟩
    exact ⟨t, htA⟩
  have hHitClosed : IsClosed hitSet := by
    change IsClosed ((fun t : NNReal ↦ W t ω) ⁻¹' A)
    exact hAclosed.preimage hcont
  have hHitBddBelow : BddBelow hitSet := ⟨0, fun _ _ ↦ bot_le⟩
  have hsInf_mem : sInf hitSet ∈ hitSet :=
    hHitClosed.csInf_mem hHitNonempty hHitBddBelow
  have hτ_eq : (hittingAfter W A 0 ω).untopA = sInf hitSet := by
    rw [hittingAfter]
    rw [if_pos]
    · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ W i ω ∈ A} = hitSet by
            ext t
            simp [hitSet]]
      simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf hitSet))
    · rcases hHitExists with ⟨t, htA⟩
      exact ⟨t, bot_le, htA⟩
  simpa [hitSet, hτ_eq] using hsInf_mem

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 25.4.3: for an open stage `U`, a continuous path started in `U` reaches
the closure of `U` at its finite exit time from `U`. -/
private theorem mem_closure_at_exit_of_lt_top
    {U : Set State} {W : VectorProcess} {ω : Ω}
    (hUo : IsOpen U)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hStart : W 0 ω ∈ U)
    (hτ : hittingAfter W Uᶜ 0 ω < ⊤) :
    W (hittingAfter W Uᶜ 0 ω).untopA ω ∈ closure U := by
  let τU : NNReal := (hittingAfter W Uᶜ 0 ω).untopA
  have hτ_mem : W τU ω ∈ Uᶜ := by
    simpa [τU] using
      mem_closedSet_at_hittingAfter_of_lt_top_local
        (A := Uᶜ)
        (hAclosed := isClosed_compl_iff.mpr hUo)
        hcont
        hτ
  have hτ_pos : 0 < τU := by
    by_contra hτ_pos
    have hτ_zero : τU = 0 := le_antisymm (le_of_not_gt hτ_pos) bot_le
    have hW0_mem : W 0 ω ∈ Uᶜ := by
      simpa [hτ_zero] using hτ_mem
    exact hW0_mem hStart
  have hτ_ne_top : hittingAfter W Uᶜ 0 ω ≠ ⊤ := ne_of_lt hτ
  have hτ_coe : ((τU : NNReal) : WithTop NNReal) = hittingAfter W Uᶜ 0 ω := by
    rw [show τU = (hittingAfter W Uᶜ 0 ω).untopA by rfl]
    rw [WithTop.untopA_eq_untop hτ_ne_top]
    exact WithTop.coe_untop _ _
  have hLeftU : ∀ s : NNReal, s < τU → W s ω ∈ U := by
    intro s hs
    have hs_lt_hit : (s : WithTop NNReal) < hittingAfter W Uᶜ 0 ω := by
      rw [← hτ_coe]
      exact_mod_cast hs
    have hs_not_mem :
        W s ω ∉ Uᶜ :=
      notMem_of_lt_hittingAfter
        (u := W) (s := Uᶜ) (n := (0 : NNReal)) (ω := ω) hs_lt_hit (by simp)
    simpa using hs_not_mem
  rw [mem_closure_iff]
  intro o ho hτo
  have hPreimage : {s : NNReal | W s ω ∈ o} ∈ 𝓝 τU := by
    exact hcont.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds ho hτo)
  rcases mem_nhds_iff.mp hPreimage with ⟨u, hu_subset, hu_open, hτu⟩
  have hτ_leftClosure : τU ∈ closure (Set.Iio τU : Set NNReal) := by
    have hclosureIio : closure (Set.Iio τU : Set NNReal) = Set.Iic τU :=
      closure_Iio' ⟨0, hτ_pos⟩
    rw [hclosureIio]
    simp
  rcases (mem_closure_iff.mp hτ_leftClosure) u hu_open hτu with ⟨s, hs_mem_u, hs_lt⟩
  -- Proof comment: every neighborhood of the exit point contains earlier path values still in
  -- `U`, so the exit point lies in `closure U`.
  exact ⟨W s ω, hu_subset hs_mem_u, hLeftU s hs_lt⟩

/-- Helper for Exercise 25.4.3: under finite exit, the stopped exit value belongs to `closure U`. -/
private theorem stoppedValue_mem_closure_at_exit_of_lt_top
    {U : Set State} {W : VectorProcess} {ω : Ω}
    (hUo : IsOpen U)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hStart : W 0 ω ∈ U)
    (hτ : hittingAfter W Uᶜ 0 ω < ⊤) :
    stoppedValue W (hittingAfter W Uᶜ 0) ω ∈ closure U := by
  have hτ_ne_top : hittingAfter W Uᶜ 0 ω ≠ ⊤ := ne_of_lt hτ
  -- Proof comment: under finite exit, `stoppedValue` is the path value at the concrete exit time.
  simpa [stoppedValue, hτ_ne_top] using
    mem_closure_at_exit_of_lt_top
      (U := U) (W := W) (ω := ω) hUo hcont hStart hτ

/-- Helper for Exercise 25.4.3: if `closure U ⊆ V`, then every deterministic-horizon stop
`W_{R ∧ τ_{Uᶜ}}` stays inside `V`. -/
private theorem stageStoppedProcess_mem_buffer
    {U V : Set State} {W : VectorProcess} {ω : Ω}
    (hUo : IsOpen U)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hStart : W 0 ω ∈ U)
    (hUV : closure U ⊆ V)
    (hτ : hittingAfter W Uᶜ 0 ω < ⊤)
    (R : NNReal) :
    stoppedProcess W (hittingAfter W Uᶜ 0) R ω ∈ V := by
  let τU : NNReal := (hittingAfter W Uᶜ 0 ω).untopA
  have hτ_ne_top : hittingAfter W Uᶜ 0 ω ≠ ⊤ := ne_of_lt hτ
  have hτ_coe : ((τU : NNReal) : WithTop NNReal) = hittingAfter W Uᶜ 0 ω := by
    rw [show τU = (hittingAfter W Uᶜ 0 ω).untopA by rfl]
    rw [WithTop.untopA_eq_untop hτ_ne_top]
    exact WithTop.coe_untop _ _
  by_cases hRτ : R < τU
  · have hStopped :
        stoppedProcess W (hittingAfter W Uᶜ 0) R ω = W R ω := by
      apply stoppedProcess_eq_of_le
      rw [← hτ_coe]
      exact le_of_lt (by exact_mod_cast hRτ)
    have hInside : W R ω ∈ U := by
      have hRt : (R : WithTop NNReal) < hittingAfter W Uᶜ 0 ω := by
        rw [← hτ_coe]
        exact_mod_cast hRτ
      have hNot :
          W R ω ∉ Uᶜ :=
        notMem_of_lt_hittingAfter
          (u := W) (s := Uᶜ) (n := (0 : NNReal)) (ω := ω) hRt (by simp)
      simpa using hNot
    -- Proof comment: before the exit time, the deterministic stop is still inside `U`, hence
    -- inside every buffer containing `closure U`.
    rw [hStopped]
    exact hUV (subset_closure hInside)
  · have hτR : τU ≤ R := le_of_not_gt hRτ
    have hStopped :
        stoppedProcess W (hittingAfter W Uᶜ 0) R ω = W τU ω := by
      apply stoppedProcess_eq_of_ge
      rw [← hτ_coe]
      exact_mod_cast hτR
    have hExitClosure :
        W τU ω ∈ closure U := by
      simpa [τU] using
        mem_closure_at_exit_of_lt_top
          (U := U)
          hUo
          hcont
          hStart
          hτ
    -- Proof comment: once the deterministic cap reaches the exit time, the stopped path is the
    -- actual exit point, which belongs to `closure U ⊆ V`.
    rw [hStopped]
    exact hUV hExitClosure

/-- Helper for Exercise 25.4.3: subtracting the deterministic start from a scalar Brownian motion
started at `x` recenters it at `0`. -/
private theorem brownianStartedAt_sub_const_startedAtZero_local
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) :
    IsBrownianMotionStartedAt μ (fun t ω ↦ B t ω - x) 0 := by
  refine
    { stronglyMeasurable := ?_
      start := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: subtracting a constant preserves strong measurability of each time slice.
    intro t
    exact (hB.stronglyMeasurable t).sub stronglyMeasurable_const
  · -- Proof comment: the recentered time-zero event is exactly the original start event at `x`.
    have hpreimage :
        (fun ω ↦ B 0 ω - x) ⁻¹' ({0} : Set ℝ) = B 0 ⁻¹' ({x} : Set ℝ) := by
      ext ω
      constructor
      · intro hω
        change B 0 ω - x = 0 at hω
        change B 0 ω = x
        linarith
      · intro hω
        have hxω : B 0 ω = x := by
          simpa using hω
        change B 0 ω - x = 0
        simp [hxω]
    rw [hpreimage]
    exact hB.start
  · -- Proof comment: subtracting the same constant from every time slice does not change any
    -- increment.
    intro n t ht
    simpa only [sub_sub_sub_cancel_right] using hB.indepIncrements n t ht
  · -- Proof comment: the same cancellation preserves the stationary-increment law.
    intro r s t
    simpa only [sub_sub_sub_cancel_right] using hB.stationaryIncrements r s t
  · intro t ht
    -- Proof comment: the time-`t` Gaussian marginal is translated from mean `x` to mean `0`.
    simpa [add_comm] using ProbabilityTheory.gaussianReal_sub_const (hB.gaussian_marginal ht) x
  · -- Proof comment: path continuity is preserved under subtraction of a deterministic constant.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.sub continuous_const

/-- Helper for Exercise 25.4.3: covariance is unchanged when both inputs are replaced by
almost-everywhere equal random variables. -/
private theorem covariance_congr_ae_local
    {μ : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIntX : μ[X] = μ[X'] := MeasureTheory.integral_congr_ae hX
  have hIntY : μ[Y] = μ[Y'] := MeasureTheory.integral_congr_ae hY
  rw [ProbabilityTheory.covariance, ProbabilityTheory.covariance]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for Exercise 25.4.3: replacing only the time-zero value of a Brownian motion started
at `0` by the literal constant `0` produces a standard Brownian motion. -/
private theorem pointwiseZeroVersion_isBrownianMotion_local
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotionStartedAt μ B 0) :
    IsBrownianMotion μ (fun t ω ↦ if t = 0 then 0 else B t ω) := by
  let B0 : NNReal → Ω → ℝ := fun t ω ↦ if t = 0 then 0 else B t ω
  have hZeroAe : B 0 =ᵐ[μ] fun _ ↦ 0 :=
    brownianStart_ae_eq_const_of_measurable (hB.stronglyMeasurable 0).measurable hB
  have hmod : ∀ t : NNReal, B0 t =ᵐ[μ] B t := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simpa [B0] using hZeroAe.symm
    · exact Filter.Eventually.of_forall fun ω ↦ by simp [B0, ht]
  have hgauss : IsGaussianProcess B μ :=
    IsBrownianMotionStartedAt.isGaussianProcess_zero hB
  have hgauss0 : IsGaussianProcess B0 μ := hgauss.congr fun t ↦ (hmod t).symm
  have hmean : ∀ t : NNReal, ∫ ω, B t ω ∂ μ = 0 :=
    (isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance μ B).1 hB
      |>.2.2.1
  have hmean0 : ∀ t : NNReal, ∫ ω, B0 t ω ∂ μ = 0 := by
    intro t
    -- Proof comment: the pointwise-zero version is a timewise modification of `B`, so the
    -- centered mean identity transfers slice by slice.
    rw [integral_congr_ae (hmod t), hmean t]
  have hcov0 : ∀ s t : NNReal, cov[B0 s, B0 t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
    intro s t
    -- Proof comment: covariance is invariant under almost-everywhere equality of each time slice.
    rw [covariance_congr_ae_local (hmod s) (hmod t), startedAtZero_covariance_eq hB s t]
  have hcont0 : HasAlmostSurelyContinuousPaths μ B0 := by
    -- Proof comment: on the full-measure start event `B 0 = 0`, the patched path agrees with the
    -- original continuous Brownian path at every time.
    filter_upwards [hB.continuous_paths, hZeroAe] with ω hωcont hω0
    have hEq : (fun t : NNReal ↦ B0 t ω) = fun t : NNReal ↦ B t ω := by
      funext t
      by_cases ht : t = 0
      · subst ht
        simpa [B0] using hω0.symm
      · simp [B0, ht]
    have hPathEq : processPath B0 ω = processPath B ω := by
      simpa [processPath] using hEq
    simpa [HasAlmostSurelyContinuousPaths] using hPathEq ▸ hωcont
  exact
    (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance μ B0).2
      ⟨by
          funext ω
          simp [B0]
        , hgauss0, hmean0, hcov0, hcont0⟩

/-- Helper for Exercise 25.4.3: patching a Brownian motion started at `0` on a measurable null
set by the constant-zero path preserves the Brownian law and makes every sample path continuous.
This is the scalar bridge needed to build a same-space continuous modification of a Brownian
vector started at a deterministic point. -/
private theorem zeroStarted_nullPatch_isBrownianMotion_local
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotionStartedAt μ B 0)
    {N : Set Ω} (hN_meas : MeasurableSet N) (hN_null : μ N = 0)
    (hcont : ∀ ω ∉ N, Continuous fun t : NNReal ↦ B t ω)
    (hzero : ∀ ω ∉ N, B 0 ω = 0) :
    IsBrownianMotion μ (fun t ω ↦ if ω ∈ N then 0 else B t ω) := by
  let Bc : NNReal → Ω → ℝ := fun t ω ↦ if ω ∈ N then 0 else B t ω
  have hOutside : ∀ᵐ ω ∂μ, ω ∉ N := compl_mem_ae_iff.mpr hN_null
  have hmod : ∀ t : NNReal, Bc t =ᵐ[μ] B t := by
    intro t
    filter_upwards [hOutside] with ω hω
    simp [Bc, hω]
  have hgauss : IsGaussianProcess B μ :=
    IsBrownianMotionStartedAt.isGaussianProcess_zero hB
  have hgaussc : IsGaussianProcess Bc μ := hgauss.congr fun t ↦ (hmod t).symm
  have hmean : ∀ t : NNReal, ∫ ω, B t ω ∂μ = 0 :=
    (isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance μ B).1 hB
      |>.2.2.1
  have hmeanc : ∀ t : NNReal, ∫ ω, Bc t ω ∂μ = 0 := by
    intro t
    -- Proof comment: deterministic-time null-set patching preserves the centered mean of each
    -- Brownian slice.
    rw [integral_congr_ae (hmod t), hmean t]
  have hcovc : ∀ s t : NNReal, cov[Bc s, Bc t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
    intro s t
    -- Proof comment: covariance is unchanged when both deterministic-time slices are replaced by
    -- the same null-set patch.
    rw [covariance_congr_ae_local (hmod s) (hmod t), startedAtZero_covariance_eq hB s t]
  have hcontc : HasAlmostSurelyContinuousPaths μ Bc := by
    -- Proof comment: off the chosen null set the path is the original continuous sample path, and
    -- on the null set it is the constant-zero path.
    filter_upwards [hOutside] with ω hω
    by_cases hωN : ω ∈ N
    · have hPathEq : processPath Bc ω = fun _ : NNReal ↦ (0 : ℝ) := by
        funext t
        simp [processPath, Bc, hωN]
      simpa [HasAlmostSurelyContinuousPaths] using
        hPathEq ▸ (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
    · have hPathEq : processPath Bc ω = fun t : NNReal ↦ B t ω := by
        funext t
        simp [processPath, Bc, hωN]
      simpa [HasAlmostSurelyContinuousPaths] using hPathEq ▸ hcont ω hωN
  exact
    (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance μ Bc).2
      ⟨by
          funext ω
          by_cases hω : ω ∈ N
          · simp [Bc, hω]
          · simp [Bc, hω, hzero ω hω]
        , hgaussc, hmeanc, hcovc, hcontc⟩

/-- Helper for Exercise 25.4.3: patch the raw Poisson extension with the prescribed frontier datum.
This is the correct global owner for the Dirichlet problem because the unpatched integral formula
vanishes on the frontier. -/
noncomputable def openBallPoissonDirichletCandidate
    (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    State → ℝ :=
  fun x ↦
    if _hx : x ∈ Metric.ball (0 : State) r then
      openBallPoissonExtension r g x
    else if hz : x ∈ frontier (Metric.ball (0 : State) r) then
      openBallFrontierBoundaryDatum r hr g ⟨x, hz⟩
    else
      0

/-- Helper for Exercise 25.4.3: on interior points, the patched Dirichlet owner agrees with the
raw Poisson extension. -/
theorem openBallPoissonDirichletCandidate_eq_extension_of_mem_ball
    (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ)
    {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    openBallPoissonDirichletCandidate r hr g x =
      openBallPoissonExtension r g x := by
  -- Proof comment: the patched owner chooses the Poisson-integral branch on interior points.
  simp [openBallPoissonDirichletCandidate, hx]

/-- Helper for Exercise 25.4.3: on the frontier, the patched Dirichlet owner is definitionally the
transported boundary datum. -/
theorem openBallPoissonDirichletCandidate_eq_boundary_on_frontier
    (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ)
    (z : frontier (Metric.ball (0 : State) r)) :
    openBallPoissonDirichletCandidate r hr g z =
      openBallFrontierBoundaryDatum r hr g z := by
  have hzSphere : (z : State) ∈ Metric.sphere (0 : State) |r| := by
    simpa [openBallFrontier_eq_sphereAbs (d := d) r hr] using z.property
  have hzEq : ‖(z : State)‖ = |r| := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hzSphere
  have hzNotBall : (z : State) ∉ Metric.ball (0 : State) r := by
    intro hzBall
    have hzlt : ‖(z : State)‖ < |r| := by
      simpa [Metric.mem_ball, dist_eq_norm, abs_of_pos hr] using hzBall
    exact (ne_of_lt hzlt) hzEq
  have hzSubtype :
      (⟨(z : State), z.property⟩ : frontier (Metric.ball (0 : State) r)) = z := by
    ext
    rfl
  -- Proof comment: away from the interior branch, the patched owner uses the frontier datum by
  -- construction.
  simp [openBallPoissonDirichletCandidate, hzNotBall, z.property, hzSubtype]

/-- Helper for Exercise 25.4.3: on an open set, harmonicity transfers across a pointwise equality
there. This packages the local `harmonicAt_congr_nhds` step used to replace the raw Poisson
extension by the patched Dirichlet owner on the interior ball. -/
private theorem harmonicOnNhd_congr_of_eqOn_isOpen
    {G : Set State} (hG : IsOpen G) {f g : State → ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f G) (hfg : Set.EqOn f g G) :
    InnerProductSpace.HarmonicOnNhd g G := by
  intro x hx
  -- Proof comment: openness upgrades the pointwise equality on `G` to a neighborhood equality at
  -- each interior point, so `HarmonicAt` transfers across `harmonicAt_congr_nhds`.
  have hEq : f =ᶠ[𝓝 x] g := by
    filter_upwards [hG.mem_nhds hx] with y hy
    exact hfg hy
  exact (InnerProductSpace.harmonicAt_congr_nhds hEq).1 (hf x hx)

/-- Helper for Exercise 25.4.3: once the raw Poisson extension is harmonic on the interior ball
and the patched owner is continuous on the closed ball, the canonical ball constructor packages the
patched owner as `HarmonicContOnCl`. -/
private theorem openBallPoissonDirichletCandidate_harmonicContOnCl_of_ballPackage
    (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ)
    (hExtension :
      InnerProductSpace.HarmonicOnNhd
        (openBallPoissonExtension r g) (Metric.ball (0 : State) r))
    (hContinuous :
      ContinuousOn
        (openBallPoissonDirichletCandidate r hr g)
        (Metric.closedBall (0 : State) r)) :
    InnerProductSpace.HarmonicContOnCl
      (openBallPoissonDirichletCandidate r hr g)
      (Metric.ball (0 : State) r) := by
  have hCandidateHarm :
      InnerProductSpace.HarmonicOnNhd
        (openBallPoissonDirichletCandidate r hr g)
        (Metric.ball (0 : State) r) := by
    -- Proof comment: inside the open ball the patched owner agrees with the raw Poisson
    -- extension, so the new congruence helper transfers harmonicity to the patched owner.
    refine
      harmonicOnNhd_congr_of_eqOn_isOpen
        Metric.isOpen_ball hExtension ?_
    intro x hx
    symm
    exact openBallPoissonDirichletCandidate_eq_extension_of_mem_ball r hr g hx
  -- Proof comment: on metric balls, mathlib's canonical `mk_ball` constructor packages interior
  -- harmonicity together with continuity on the closed ball into `HarmonicContOnCl`.
  exact InnerProductSpace.HarmonicContOnCl.mk_ball hCandidateHarm hContinuous

/-- Helper for Exercise 25.4.3: on `ℝ²`, precomposing a harmonic function with a real-linear
isometry preserves pointwise harmonicity. -/
private theorem harmonicAt_precomp_complexIsometry
    {f : ℂ → ℝ} {e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ}
    {z : EuclideanSpace ℝ (Fin 2)} :
    InnerProductSpace.HarmonicAt f (e z) →
      InnerProductSpace.HarmonicAt (fun w : EuclideanSpace ℝ (Fin 2) ↦ f (e w)) z := by
  intro h
  refine ⟨h.1.comp z e.contDiff.contDiffAt, ?_⟩
  have hzero :
      ∀ᶠ w in 𝓝 z, Laplacian.laplacian f (e w) = 0 :=
    e.continuousAt.tendsto.eventually h.2
  filter_upwards [hzero] with w hwlap
  -- Proof comment: transport the Laplacian through the linear isometry so both traces are
  -- computed in matching orthonormal bases.
  have hpoint :
      Laplacian.laplacian (fun u : EuclideanSpace ℝ (Fin 2) ↦ f (e u)) w =
        Laplacian.laplacian f (e w) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (f := fun u : EuclideanSpace ℝ (Fin 2) ↦ f (e u))
      (v := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2)))]
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (f := f)
      (v := (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))).map e)]
    simp only [OrthonormalBasis.map_apply]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hiter :
        iteratedFDeriv ℝ 2 (fun u : EuclideanSpace ℝ (Fin 2) ↦ f (e u)) w =
          (iteratedFDeriv ℝ 2 f (e w)).compContinuousLinearMap
            (fun _ : Fin 2 ↦ e.toContinuousLinearEquiv.toContinuousLinearMap) := by
      simpa [Function.comp, iteratedFDerivWithin_univ] using
        (e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right
          (f := f) (s := (Set.univ : Set ℂ)) (x := w) (i := 2) (by simp))
    have hcomp :=
      congrArg
        (fun T :
            ContinuousMultilinearMap ℝ
              (fun _ : Fin 2 ↦ EuclideanSpace ℝ (Fin 2)) ℝ ↦
            T ![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i,
              (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i])
        hiter
    have hvec :
        (fun j : Fin 2 ↦
          e
            (![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i,
              (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i] j)) =
          ![e ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i),
            e ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i)] := by
      ext j
      fin_cases j <;> rfl
    simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, hvec] using hcomp
  rw [hpoint]
  simpa using hwlap

/-- Helper for Exercise 25.4.3: on `ℝ²`, the logarithmic radial profile is harmonic away from
the origin. This isolates the planar harmonic core needed for the remaining Poisson-kernel PDE. -/
private theorem logNorm_harmonicAt_dimTwo_of_ne_zero
    {z : EuclideanSpace ℝ (Fin 2)} (hz : z ≠ 0) :
    InnerProductSpace.HarmonicAt (fun w : EuclideanSpace ℝ (Fin 2) ↦ Real.log ‖w‖) z := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have hez_ne : e z ≠ 0 := by
    intro hez
    apply hz
    exact e.injective (by simpa using hez)
  have hcomplex : InnerProductSpace.HarmonicAt (fun w : ℂ ↦ Real.log ‖w‖) (e z) := by
    -- Proof comment: the complex analytic theorem already gives harmonicity of `log ‖·‖` away
    -- from `0`.
    simpa using
      (AnalyticAt.harmonicAt_log_norm
        (f := fun w : ℂ ↦ w) (z := e z) analyticAt_id hez_ne)
  have hpullback :
      InnerProductSpace.HarmonicAt
        (fun w : EuclideanSpace ℝ (Fin 2) ↦ Real.log ‖e w‖) z :=
    harmonicAt_precomp_complexIsometry
      (f := fun w : ℂ ↦ Real.log ‖w‖) (e := e) (z := z) hcomplex
  have hprofile :
      (fun w : EuclideanSpace ℝ (Fin 2) ↦ Real.log ‖e w‖) =
        (fun w : EuclideanSpace ℝ (Fin 2) ↦ Real.log ‖w‖) := by
    -- Proof comment: the chosen isometry preserves the Euclidean norm exactly.
    funext w
    rw [LinearIsometryEquiv.norm_map]
  exact hprofile ▸ hpullback

/-- Helper for Exercise 25.4.3: for a fixed boundary point, the Poisson kernel should already be
harmonic at each interior point of the open ball. -/
private theorem openBallPoissonKernelSection_harmonicAt
    (r : ℝ) (hr : 0 < r)
    (y : Metric.sphere (0 : State) |r|)
    {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    InnerProductSpace.HarmonicAt
      (fun z : State ↦ openBallPoissonKernel r z y) x := by
  by_cases h1 : d = 1
  · subst h1
    let δ : ℝ := (r - ‖x‖) / 4
    have hδ :
        0 < δ ∧
          ∀ {z : EuclideanSpace ℝ (Fin 1)}, z ∈ Metric.closedBall x δ →
            z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) r ∧
              ∀ y' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) |r|,
                δ ≤ dist z (y' : EuclideanSpace ℝ (Fin 1)) := by
      -- Proof comment: the quarter-gap buffer is reused in both endpoint branches, so package it
      -- once before splitting the `S⁰` boundary point.
      simpa [δ] using
        closedBallQuarterGap_mem_ball_and_boundarySeparation
          (d := 1) r hr (x0 := x) hx
    obtain ⟨hδpos, hδprop⟩ := hδ
    let u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
      ⟨|r|⁻¹ • (y : EuclideanSpace ℝ (Fin 1)),
        invAbsRadius_smul_mem_unitSphere (d := 1) r hr y⟩
    have hu_scale : sphereAbsRadiusScale r u = y := by
      have hrabs_ne : |r| ≠ 0 := abs_ne_zero.mpr hr.ne'
      ext i
      fin_cases i
      change |r| * (|r|⁻¹ * (y : EuclideanSpace ℝ (Fin 1)) 0) =
        (y : EuclideanSpace ℝ (Fin 1)) 0
      field_simp [hrabs_ne]
    rcases unitSphereFinOne_eq_posPoint_or_negPoint u with hu | hu
    · have hy_pos : sphereAbsRadiusScale r unitSphereFinOnePosPoint = y := by
        simpa [hu] using hu_scale
      have hlocal :
          (fun z : EuclideanSpace ℝ (Fin 1) ↦ openBallPoissonKernel r z y) =ᶠ[𝓝 x]
            fun z : EuclideanSpace ℝ (Fin 1) ↦ 1 + |r|⁻¹ * z 0 := by
        filter_upwards [Metric.ball_mem_nhds x hδpos] with z hz
        have hzClosed : z ∈ Metric.closedBall x δ := by
          rw [Metric.mem_closedBall]
          exact
            (show dist z x < δ by
              simpa [Metric.mem_ball, dist_comm] using hz).le
        have hzBall :
            z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) r :=
          (hδprop hzClosed).1
        let ξ : EuclideanSpace ℝ (Fin 1) := |r|⁻¹ • z
        have hξ : ξ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
          invAbsRadius_smul_mem_unitBall r hr hzBall
        have hkernel :
            openBallPoissonKernel r z y = 1 + |r|⁻¹ * z 0 := by
          calc
            openBallPoissonKernel r z y =
                openBallPoissonKernel r z (sphereAbsRadiusScale r unitSphereFinOnePosPoint) := by
                  rw [hy_pos]
            _ =
                (1 - ‖ξ‖ ^ (2 : ℕ)) /
                  dist ξ (unitSphereFinOnePosPoint : EuclideanSpace ℝ (Fin 1)) ^ (1 : ℕ) := by
                  simpa [ξ] using
                    openBallPoissonKernel_sphereAbsRadiusScale_eq_unitSphereKernel
                      r hr z unitSphereFinOnePosPoint
            _ = 1 + ξ 0 := by
                  simpa [unitSphereFinOnePosPoint] using unitSphereKernel_eval_pos_finOne ξ hξ
            _ = 1 + |r|⁻¹ * z 0 := by
                  simp [ξ]
        exact hkernel
      rw [InnerProductSpace.harmonicAt_congr_nhds hlocal]
      have hcoord :
          InnerProductSpace.HarmonicAt
            (fun z : EuclideanSpace ℝ (Fin 1) ↦ z 0) x :=
        firstCoordinate_harmonicAt_finOne x
      have hscaled :
          InnerProductSpace.HarmonicAt
            (fun z : EuclideanSpace ℝ (Fin 1) ↦ |r|⁻¹ * z 0) x := by
        simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using
          hcoord.const_smul (c := |r|⁻¹)
      exact (InnerProductSpace.harmonicAt_const (x := x) (c := (1 : ℝ))).add hscaled
    · have hy_neg : sphereAbsRadiusScale r unitSphereFinOneNegPoint = y := by
        simpa [hu] using hu_scale
      have hlocal :
          (fun z : EuclideanSpace ℝ (Fin 1) ↦ openBallPoissonKernel r z y) =ᶠ[𝓝 x]
            fun z : EuclideanSpace ℝ (Fin 1) ↦ 1 - |r|⁻¹ * z 0 := by
        filter_upwards [Metric.ball_mem_nhds x hδpos] with z hz
        have hzClosed : z ∈ Metric.closedBall x δ := by
          rw [Metric.mem_closedBall]
          exact
            (show dist z x < δ by
              simpa [Metric.mem_ball, dist_comm] using hz).le
        have hzBall :
            z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) r :=
          (hδprop hzClosed).1
        let ξ : EuclideanSpace ℝ (Fin 1) := |r|⁻¹ • z
        have hξ : ξ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
          invAbsRadius_smul_mem_unitBall r hr hzBall
        have hkernel :
            openBallPoissonKernel r z y = 1 - |r|⁻¹ * z 0 := by
          calc
            openBallPoissonKernel r z y =
                openBallPoissonKernel r z (sphereAbsRadiusScale r unitSphereFinOneNegPoint) := by
                  rw [hy_neg]
            _ =
                (1 - ‖ξ‖ ^ (2 : ℕ)) /
                  dist ξ (unitSphereFinOneNegPoint : EuclideanSpace ℝ (Fin 1)) ^ (1 : ℕ) := by
                  simpa [ξ] using
                    openBallPoissonKernel_sphereAbsRadiusScale_eq_unitSphereKernel
                      r hr z unitSphereFinOneNegPoint
            _ = 1 - ξ 0 := by
                  simpa [unitSphereFinOneNegPoint] using unitSphereKernel_eval_neg_finOne ξ hξ
            _ = 1 - |r|⁻¹ * z 0 := by
                  simp [ξ]
        exact hkernel
      rw [InnerProductSpace.harmonicAt_congr_nhds hlocal]
      have hcoord :
          InnerProductSpace.HarmonicAt
            (fun z : EuclideanSpace ℝ (Fin 1) ↦ z 0) x :=
        firstCoordinate_harmonicAt_finOne x
      have hscaled :
          InnerProductSpace.HarmonicAt
            (fun z : EuclideanSpace ℝ (Fin 1) ↦ |r|⁻¹ * z 0) x := by
        simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using
          hcoord.const_smul (c := |r|⁻¹)
      exact (InnerProductSpace.harmonicAt_const (x := x) (c := (1 : ℝ))).sub hscaled
  obtain ⟨ε, hεpos, hεsep⟩ := exists_boundaryDistanceLowerBound_nhds r hr y hx
  have hPoleFree :
      ∀ {z : State}, z ∈ Metric.ball x ε → dist z (y : State) ≠ 0 := by
    intro z hz
    have hlower : dist x (y : State) / 2 ≤ dist z (y : State) := hεsep hz
    have hxy_pos : 0 < dist x (y : State) := by
      exact lt_of_le_of_ne dist_nonneg
        (Ne.symm <| dist_ne_zero_of_mem_ball_mem_sphere_absRadius r hr hx y)
    -- Proof comment: the neighborhood was chosen so every point in it stays at least half the
    -- positive boundary distance away from `y`.
    intro hzy
    have : dist x (y : State) / 2 ≤ 0 := by simpa [hzy] using hlower
    exact (not_le_of_gt (half_pos hxy_pos)) this
  -- Proof comment: the singularity at `y` is now excluded on the explicit neighborhood
  -- `Metric.ball x ε`, so the remaining proof only needs the translated harmonic-core API.
  -- TODO: rewrite the kernel as a translated radial profile away from `y`, use
  -- `dist_ne_zero_of_mem_ball_mem_sphere_absRadius` to avoid the pole, and port the radial-core
  -- harmonicity split from the annulus proof (`d = 1`, `d = 2`, and `d > 2`).
  sorry

/-- Helper for Exercise 25.4.3: the pointwise section-harmonicity theorem packages the Poisson
kernel as harmonic on neighborhoods throughout the open ball. -/
private theorem openBallPoissonKernelSection_harmonicOnNhd
    (r : ℝ) (hr : 0 < r)
    (y : Metric.sphere (0 : State) |r|) :
    InnerProductSpace.HarmonicOnNhd
      (fun x : State ↦ openBallPoissonKernel r x y)
      (Metric.ball (0 : State) r) := by
  -- Proof comment: once the pointwise harmonicity statement is isolated, the neighborhood version
  -- is just the bundled `HarmonicOnNhd` spelling on the open ball.
  intro x hx
  exact openBallPoissonKernelSection_harmonicAt r hr y hx

/-- Helper for Exercise 25.4.3: the missing analytic interior input is harmonicity of the raw
Poisson extension at each interior point of the open ball. -/
private theorem openBallPoissonExtension_harmonicAt_of_mem_ball
    (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ)
    {x0 : State} (hx0 : x0 ∈ Metric.ball (0 : State) r) :
    InnerProductSpace.HarmonicAt (openBallPoissonExtension r g) x0 := by
  let _ := hx0
  -- TODO: combine the pointwise section PDE with the quarter-gap closed-ball separation from
  -- `closedBallQuarterGap_mem_ball_and_boundarySeparation`, then commute the Laplacian through the
  -- boundary integral on that buffered ball.
  sorry

/-- Helper for Exercise 25.4.3: the pointwise interior harmonicity theorem upgrades to
`HarmonicOnNhd` on the whole open ball. -/
theorem openBallPoissonExtension_harmonicOnNhd
    (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    InnerProductSpace.HarmonicOnNhd
      (openBallPoissonExtension r g) (Metric.ball (0 : State) r) := by
  by_cases hg0 : g = 0
  · subst hg0
    -- Proof comment: the zero boundary datum gives the zero Poisson extension, and constant
    -- functions are harmonic on every neighborhood.
    intro x hx
    convert (InnerProductSpace.harmonicAt_const (x := x) (c := (0 : ℝ))) using 1
    ext y
    exact openBallPoissonExtension_zero r y
  -- Proof comment: after isolating the quarter-gap differentiation-under-the-integral step in the
  -- pointwise helper, the neighborhood formulation is immediate.
  intro x hx
  exact openBallPoissonExtension_harmonicAt_of_mem_ball r hr g hx

/-- Helper for Exercise 25.4.3: constant boundary data integrate to the total Poisson-kernel mass
times that constant. This isolates the remaining normalization step from the integral algebra. -/
private theorem openBallPoissonExtension_const_eq_kernelMeasureMass
    (r : ℝ) (x : State) (c : ℝ) :
    openBallPoissonExtension r
        (BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) c) x =
      (openBallPoissonKernelMeasure r x).real Set.univ * c := by
  -- Proof comment: the boundary datum is literally constant, so the Bochner integral is the
  -- total mass of the Poisson-kernel measure multiplied by that constant.
  rw [openBallPoissonExtension]
  simp [MeasureTheory.integral_const, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 25.4.3: constant boundary data should be fixed by the Poisson extension
at interior points. This is the normalization identity needed before taking the frontier limit. -/
theorem openBallPoissonExtension_constEq
    (r : ℝ) (hr : 0 < r) {x : State} (hx : x ∈ Metric.ball (0 : State) r)
    (c : ℝ) :
    openBallPoissonExtension r
        (BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) c) x = c := by
  -- Proof comment: the new helper removes the integral algebra; what remains is exactly the
  -- normalization fact that the Poisson-kernel measure has total mass `1` for interior starts.
  rw [openBallPoissonExtension_const_eq_kernelMeasureMass]
  let _ : IsProbabilityMeasure (openBallPoissonKernelMeasure r x) :=
    openBallPoissonKernelMeasure_isProbability r hr hx
  let _ : IsFiniteMeasure (openBallPoissonKernelMeasure r x) := by infer_instance
  -- Proof comment: once the density measure is normalized to a probability measure, its real mass
  -- on the whole sphere is `1`, so the constant-integral formula collapses immediately.
  have hMass :
      (openBallPoissonKernelMeasure r x).real Set.univ = 1 := by
    exact
      (MeasureTheory.isProbabilityMeasure_iff_real.1
        (openBallPoissonKernelMeasure_isProbability r hr hx))
  simp [hMass]

/-- Helper for Exercise 25.4.3: the constant-boundary atom for the Poisson boundary-limit
package. -/
theorem openBallPoissonExtension_constBoundary_tendsto
    (r : ℝ) (hr : 0 < r) (c : ℝ)
    (z : frontier (Metric.ball (0 : State) r)) :
    Filter.Tendsto
      (fun x ↦
        openBallPoissonExtension r
          (BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) c) x)
      (nhdsWithin (z : State) (Metric.ball (0 : State) r))
      (nhds c) := by
  -- Proof comment: once the interior normalization identity is isolated, the frontier-limit claim
  -- is just eventual equality with the constant function on the punctured approach filter.
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with x hx
  symm
  exact openBallPoissonExtension_constEq r hr hx c

/-- Helper for Exercise 25.4.3: the zero-remainder atom for the Poisson boundary-limit package.
-/
theorem openBallPoissonExtension_zeroAtBoundary_tendsto_zero
    (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ)
    (z : frontier (Metric.ball (0 : State) r))
    (hz :
      openBallFrontierBoundaryDatum r hr g z = 0) :
    Filter.Tendsto
      (fun x ↦ openBallPoissonExtension r g x)
      (nhdsWithin (z : State) (Metric.ball (0 : State) r))
      (nhds 0) := by
  by_cases hg0 : g = 0
  · subst hg0
    -- Proof comment: when the boundary datum itself is zero, the Poisson extension is the
    -- constant zero function, so the boundary-limit statement is immediate.
    simpa [openBallPoissonExtension_zero] using
      (tendsto_const_nhds :
        Filter.Tendsto
          (fun _ : State ↦ (0 : ℝ))
          (nhdsWithin (z : State) (Metric.ball (0 : State) r))
          (nhds 0))
  -- TODO: prove the boundary approximate-identity estimate for boundary data normalized to vanish
  -- at the chosen frontier point.
  sorry

/-- Helper for Exercise 25.4.3: the full frontier boundary-limit theorem is assembled from the
constant and zero-remainder atoms. -/
private theorem openBallPoissonExtension_tendsto_boundaryDatum_at_frontier
    (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ)
    (z : frontier (Metric.ball (0 : State) r)) :
    Filter.Tendsto
      (fun x ↦ openBallPoissonExtension r g x)
      (nhdsWithin (z : State) (Metric.ball (0 : State) r))
      (nhds (openBallFrontierBoundaryDatum r hr g z)) := by
  let c : ℝ := openBallFrontierBoundaryDatum r hr g z
  let gZero :
      BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ :=
    g - BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) c
  have hzZero : openBallFrontierBoundaryDatum r hr gZero z = 0 := by
    -- Proof comment: subtracting the boundary value at `z` reduces the boundary-limit theorem to
    -- the zero-at-`z` remainder case.
    simp [gZero, c]
  have hZero :
      Filter.Tendsto
        (fun x ↦ openBallPoissonExtension r gZero x)
        (nhdsWithin (z : State) (Metric.ball (0 : State) r))
        (nhds 0) :=
    openBallPoissonExtension_zeroAtBoundary_tendsto_zero r hr gZero z hzZero
  have hConst :
      Filter.Tendsto
        (fun x ↦
          openBallPoissonExtension r
            (BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) c) x)
        (nhdsWithin (z : State) (Metric.ball (0 : State) r))
        (nhds c) :=
    openBallPoissonExtension_constBoundary_tendsto r hr c z
  have hSplit :
      (fun x ↦ openBallPoissonExtension r g x) =ᶠ[
        nhdsWithin (z : State) (Metric.ball (0 : State) r)]
        fun x ↦
          openBallPoissonExtension r gZero x +
            openBallPoissonExtension r
              (BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) c) x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    -- Proof comment: inside the ball the Poisson extension is additive, so the centered datum
    -- plus its constant boundary value recombine to `g`.
    have hgZero_add :
        gZero +
            BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) c =
          g := by
      ext y
      simp [gZero, c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    calc
      openBallPoissonExtension r g x =
          openBallPoissonExtension r
            (gZero +
              BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) c) x := by
        rw [hgZero_add]
      _ =
          openBallPoissonExtension r gZero x +
            openBallPoissonExtension r
              (BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) c) x :=
        openBallPoissonExtension_add
          r hr hx
          gZero
          (BoundedContinuousFunction.const (Metric.sphere (0 : State) |r|) c)
  -- Proof comment: the desired frontier limit is now the sum of the zero-remainder limit and the
  -- constant-part limit.
  simpa [c] using Filter.Tendsto.congr' hSplit.symm (hZero.add hConst)

/-- Helper for Exercise 25.4.3: the missing analytic closure input is continuity of the patched
Poisson candidate on the closed ball. -/
private theorem openBallPoissonDirichletCandidate_continuousOn_closedBall
    (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    ContinuousOn
      (openBallPoissonDirichletCandidate r hr g)
      (Metric.closedBall (0 : State) r) := by
  let boundaryBranch : State → ℝ := fun x ↦
    if hz : x ∈ frontier (Metric.ball (0 : State) r) then
      openBallFrontierBoundaryDatum r hr g ⟨x, hz⟩
    else
      0
  have hClosedCompl_eq_frontier :
      Metric.closedBall (0 : State) r ∩ (Metric.ball (0 : State) r)ᶜ =
        frontier (Metric.ball (0 : State) r) := by
    rw [frontier, closure_ball (0 : State) hr.ne', Metric.isOpen_ball.interior_eq]
    ext x
    simp [Set.diff_eq]
  have hClosedInterBall :
      Metric.closedBall (0 : State) r ∩ Metric.ball (0 : State) r =
        Metric.ball (0 : State) r := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨Metric.ball_subset_closedBall hx, hx⟩
  have hExtensionCont :
      ContinuousOn
        (openBallPoissonExtension r g)
        (Metric.closedBall (0 : State) r ∩ Metric.ball (0 : State) r) := by
    -- Proof comment: the harmonicity theorem already gives continuity of the raw Poisson
    -- extension on the interior ball.
    exact
      (openBallPoissonExtension_harmonicOnNhd r hr g).continuousOn.mono
        (by
          intro x hx
          exact hx.2)
  have hBoundaryBranchContFrontier :
      ContinuousOn boundaryBranch (frontier (Metric.ball (0 : State) r)) := by
    rw [continuousOn_iff_continuous_restrict]
    -- Proof comment: on the frontier branch, the ambient helper collapses to the transported
    -- boundary datum itself.
    refine (openBallFrontierBoundaryDatum r hr g).continuous.congr ?_
    intro z'
    simp [boundaryBranch]
  have hBoundaryBranchCont :
      ContinuousOn
        boundaryBranch
        (Metric.closedBall (0 : State) r ∩ (Metric.ball (0 : State) r)ᶜ) := by
    simpa [hClosedCompl_eq_frontier] using hBoundaryBranchContFrontier
  have hPiecewiseCont :
      ContinuousOn
        (Set.piecewise
          (Metric.ball (0 : State) r)
          (openBallPoissonExtension r g)
          boundaryBranch)
        (Metric.closedBall (0 : State) r) := by
    refine ContinuousOn.piecewise' ?_ ?_ hExtensionCont hBoundaryBranchCont
    · intro x hx
      have hxFrontier : x ∈ frontier (Metric.ball (0 : State) r) := hx.2
      have hxNotBall : x ∉ Metric.ball (0 : State) r := by
        have hxSphere : x ∈ Metric.sphere (0 : State) |r| := by
          simpa [openBallFrontier_eq_sphereAbs (d := d) r hr] using hxFrontier
        have hxEq : ‖x‖ = |r| := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hxSphere
        intro hxBall
        have hxlt : ‖x‖ < |r| := by
          simpa [Metric.mem_ball, dist_eq_norm, abs_of_pos hr] using hxBall
        exact (ne_of_lt hxlt) hxEq
      -- Proof comment: approaching a frontier point from the interior ball lands at the boundary
      -- datum by the previously assembled boundary-limit theorem.
      simpa [hClosedInterBall, boundaryBranch, Set.piecewise, hxNotBall, hxFrontier] using
        openBallPoissonExtension_tendsto_boundaryDatum_at_frontier r hr g ⟨x, hxFrontier⟩
    · intro x hx
      have hxFrontier : x ∈ frontier (Metric.ball (0 : State) r) := hx.2
      have hxCompl :
          x ∈ Metric.closedBall (0 : State) r ∩ (Metric.ball (0 : State) r)ᶜ := by
        refine ⟨hx.1, ?_⟩
        have hxSphere : x ∈ Metric.sphere (0 : State) |r| := by
          simpa [openBallFrontier_eq_sphereAbs (d := d) r hr] using hxFrontier
        have hxEq : ‖x‖ = |r| := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hxSphere
        intro hxBall
        have hxlt : ‖x‖ < |r| := by
          simpa [Metric.mem_ball, dist_eq_norm, abs_of_pos hr] using hxBall
        exact (ne_of_lt hxlt) hxEq
      have hxNotBall : x ∉ Metric.ball (0 : State) r := hxCompl.2
      have hBoundaryAt :
          Filter.Tendsto
            boundaryBranch
            (nhdsWithin x (Metric.closedBall (0 : State) r ∩ (Metric.ball (0 : State) r)ᶜ))
            (nhds (boundaryBranch x)) := by
        exact hBoundaryBranchCont x hxCompl
      -- Proof comment: on the exterior branch inside the closed ball, the piecewise target is
      -- just the boundary branch itself, so ordinary frontier continuity supplies the second
      -- pasting condition.
      simpa [boundaryBranch, Set.piecewise, hxNotBall, hxFrontier] using
        hBoundaryAt
  have hCandidateEq :
      Set.EqOn
        (openBallPoissonDirichletCandidate r hr g)
        (Set.piecewise
          (Metric.ball (0 : State) r)
          (openBallPoissonExtension r g)
          boundaryBranch)
        (Metric.closedBall (0 : State) r) := by
    intro x hxClosed
    by_cases hxBall : x ∈ Metric.ball (0 : State) r
    · -- Proof comment: on interior points both spellings choose the raw Poisson extension.
      simp [openBallPoissonDirichletCandidate, Set.piecewise, boundaryBranch, hxBall]
    · have hxFrontier : x ∈ frontier (Metric.ball (0 : State) r) := by
        have hxMem :
            x ∈ Metric.closedBall (0 : State) r ∩ (Metric.ball (0 : State) r)ᶜ :=
          ⟨hxClosed, hxBall⟩
        simpa [hClosedCompl_eq_frontier] using hxMem
      -- Proof comment: on the boundary of the closed ball, the patched candidate and the
      -- piecewise model both evaluate to the transported boundary datum.
      simpa [Set.piecewise, boundaryBranch, hxBall, hxFrontier] using
        openBallPoissonDirichletCandidate_eq_boundary_on_frontier
          r hr g ⟨x, hxFrontier⟩
  -- Proof comment: after the frontier limit is isolated, continuity on the closed ball is just a
  -- clean piecewise pasting argument.
  exact hPiecewiseCont.congr hCandidateEq

/-- Helper for Exercise 25.4.3: once the remaining Poisson-kernel PDE and boundary-limit package
is supplied, the patched Poisson owner is the canonical `HarmonicContOnCl` solution owner on the
open ball. -/
theorem openBallPoissonDirichletCandidate_harmonicContOnCl
    (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    InnerProductSpace.HarmonicContOnCl
      (openBallPoissonDirichletCandidate r hr g)
      (Metric.ball (0 : State) r) := by
  -- Route correction: the raw Poisson integral cannot be the global Dirichlet owner because it
  -- vanishes on the frontier. The remaining analytic work is exactly to show that the patched
  -- owner is harmonic on the open ball and continuous on its closure.
  -- Proof comment: after isolating the missing analytic inputs as a single ball package, the
  -- canonical helper theorem closes the patched-owner `HarmonicContOnCl` goal.
  exact
    openBallPoissonDirichletCandidate_harmonicContOnCl_of_ballPackage
      r hr g
      (openBallPoissonExtension_harmonicOnNhd r hr g)
      (openBallPoissonDirichletCandidate_continuousOn_closedBall r hr g)

/-- Helper for Exercise 25.4.3: a Brownian vector started at a deterministic point has almost
surely continuous sample paths. -/
private theorem brownianVectorStartedAt_aeContinuous
    {μ : Measure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt μ W x) :
    ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ W t ω) := by
  have hcontCoord :
      ∀ i : Fin d, ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ W t ω i) := by
    intro i
    -- Proof comment: each coordinate process already carries the almost-sure continuity owner.
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      (hW.isBrownianMotionStartedAt i).continuous_paths
  have hall :
      ∀ᵐ ω ∂μ, ∀ i : Fin d, Continuous (fun t : NNReal ↦ W t ω i) := by
    rw [ae_all_iff]
    intro i
    exact hcontCoord i
  filter_upwards [hall] with ω hω
  have hcoords : Continuous (fun t : NNReal ↦ fun i : Fin d ↦ W t ω i) :=
    continuous_pi fun i ↦ hω i
  -- Proof comment: continuity of the Euclidean path is equivalent to coordinatewise continuity on
  -- the finite product model for `State`.
  simpa using (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp hcoords

/-- Helper for Exercise 25.4.3: a Brownian vector started at a deterministic point also starts
there almost surely at time `0` as a `State`-valued process. -/
private theorem brownianVectorStart_ae_eq_const
    (μ : ProbabilityMeasure Ω)
    {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x := by
  have hcoords :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ i : Fin d, W 0 ω i = x i := by
    rw [ae_all_iff]
    intro i
    exact
      brownianStart_ae_eq_const_of_measurable
        ((hW.isBrownianMotionStartedAt i).stronglyMeasurable 0).measurable
        (hW.isBrownianMotionStartedAt i)
  -- Proof comment: coordinatewise almost-sure equality upgrades to equality in the Euclidean
  -- state space by extensionality.
  filter_upwards [hcoords] with ω hω
  ext i
  exact hω i

/-- Helper for Exercise 25.4.3: if every sample path is continuous and the exit time from `U` is
almost surely finite, then the exit clock is a stopping time for the natural filtration. -/
private theorem stageExit_isStoppingTime_of_continuous_of_aeExitFinite
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤) :
    IsStoppingTime
      (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
      (hittingAfter W Uᶜ 0) := by
  classical
  let hWsm : ∀ t : NNReal, StronglyMeasurable (W t) :=
    brownianVectorStartedAt_stronglyMeasurable hW
  let D : NNReal → Ω → ℝ := fun t ω ↦ Metric.infDist (W t ω) Uᶜ
  have hUne : U ≠ Set.univ := by
    intro hUuniv
    have hTop :
        ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω = ⊤ := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      simp [hUuniv]
    have hFalse : ∀ᵐ ω ∂(μ : Measure Ω), False := by
      filter_upwards [hExitFinite, hTop] with ω hωfin hωtop
      exact (ne_of_lt hωfin) hωtop
    have hUnivZero : (μ : Measure Ω) Set.univ = 0 := by
      simp [ae_iff] at hFalse
    have hUnivOne : (μ : Measure Ω) Set.univ = 1 := by
      simp
    rw [hUnivZero] at hUnivOne
    norm_num at hUnivOne
  have hUc_nonempty : (Uᶜ : Set State).Nonempty := Set.nonempty_compl.2 hUne
  have hDsm : ∀ t : NNReal, StronglyMeasurable (D t) := by
    intro t
    -- Proof comment: each distance slice is a continuous observable of the Brownian state at
    -- time `t`.
    exact
      ((Metric.continuous_infDist_pt (Uᶜ)).measurable.comp
        (hWsm t).measurable).stronglyMeasurable
  have hWstrong :
      StronglyAdapted (Filtration.natural W hWsm) W :=
    Filtration.stronglyAdapted_natural (u := W) hWsm
  have hDcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ D t ω := by
    intro ω
    -- Proof comment: the distance-to-complement process inherits continuity from the path of
    -- `W`.
    exact (Metric.continuous_infDist_pt (Uᶜ)).comp (hWcont ω)
  have hDadapted : Adapted (Filtration.natural W hWsm) D := by
    intro t
    -- Proof comment: the distance slice at time `t` only depends on the Brownian state at the
    -- same time.
    exact
      ((Metric.continuous_infDist_pt (Uᶜ)).measurable.comp
        (hWstrong.stronglyMeasurable_le (i := t) (j := t) le_rfl).measurable)
  have hDnat :
      Filtration.natural D hDsm ≤ Filtration.natural W hWsm :=
    (adapted_iff_natural_le hDsm).1 hDadapted
  have hτdist :
      IsStoppingTime (Filtration.natural D hDsm) (hittingAfter D ({0} : Set ℝ) 0) := by
    have hpair : ({(0 : ℝ), 0} : Set ℝ) = ({0} : Set ℝ) := by
      ext y
      simp
    -- Proof comment: the exit clock from `U` is the zero-hitting time of the distance process.
    simpa [hpair] using
      twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
        (X := D) hDsm hDcont (a := 0) (b := 0)
  have hEqτ :
      hittingAfter W Uᶜ 0 = hittingAfter D ({0} : Set ℝ) 0 := by
    ext ω
    have hclosedUc : IsClosed (Uᶜ : Set State) := isClosed_compl_iff.mpr hUo
    have hCond :
        (∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ) ↔
          ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := by
      simp [D, Set.mem_singleton_iff, hclosedUc.mem_iff_infDist_zero hUc_nonempty]
    change
      (if ∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ then
          ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ W i ω ∈ Uᶜ} : NNReal) : ENNReal)
        else ⊤) =
        (if ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) then
          ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ D i ω ∈ ({0} : Set ℝ)} : NNReal) :
            ENNReal)
        else ⊤)
    by_cases h : ∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ
    · have h' : ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := hCond.mp h
      rw [if_pos h, if_pos h']
      congr 1
      ext
      simp [D, Set.mem_singleton_iff, hclosedUc.mem_iff_infDist_zero hUc_nonempty]
    · have h' : ¬ ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := mt hCond.mpr h
      rw [if_neg h, if_neg h']
  have hτdistW :
      IsStoppingTime (Filtration.natural W hWsm) (hittingAfter D ({0} : Set ℝ) 0) := by
    intro i
    exact hDnat i _ (hτdist i)
  -- Proof comment: the distance-process hitting time is a stopping time, and the natural
  -- filtration comparison transports that property back to `W`.
  simpa [hEqτ] using hτdistW

/-- Helper for Exercise 25.4.3: stopping a continuous `State`-valued sample path keeps it
continuous. -/
private theorem continuous_stoppedVectorProcess_of_continuous
    {X : VectorProcess} {σ : Ω → ENNReal} {ω : Ω}
    (hXCont : Continuous fun t : NNReal ↦ X t ω) :
    Continuous fun t : NNReal ↦ stoppedProcess X σ t ω := by
  have hfinite : ∀ t : NNReal, min (t : ENNReal) (σ ω) ≠ ⊤ := fun t ↦
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  let clipped : NNReal → {s : ENNReal | s ≠ ⊤} := fun t ↦
    ⟨min (t : ENNReal) (σ ω), hfinite t⟩
  have hClipped : Continuous clipped := by
    -- Proof comment: the stopped path is the original path precomposed with the clipped time map
    -- `t ↦ min (t, σ ω)`.
    exact (ENNReal.continuous_coe.inf continuous_const).subtype_mk hfinite
  have hTime :
      Continuous fun t : NNReal ↦ WithTop.untop (clipped t).1 (clipped t).2 := by
    simpa [clipped] using (WithTop.continuous_untop.comp hClipped)
  have hEq :
      (fun t : NNReal ↦ stoppedProcess X σ t ω) =
        fun t : NNReal ↦ X (WithTop.untop (clipped t).1 (clipped t).2) ω := by
    funext t
    change X ((min (t : ENNReal) (σ ω)).untopA) ω =
      X (WithTop.untop (min (t : ENNReal) (σ ω)) (hfinite t)) ω
    rw [WithTop.untopA_eq_untop (hfinite t)]
    rfl
  -- Proof comment: after normalizing the stopped path to a clipped-time composition, continuity
  -- is inherited from the original path.
  rw [hEq]
  exact hXCont.comp hTime

/-- Helper for Exercise 25.4.3: Brownian motion started inside the open ball exits that ball in
finite time almost surely. -/
private theorem ae_exitTime_lt_top_of_isCompact_closure_startedAt
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {G : Set State} {x : State}
    (hx : x ∈ G)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (_hGo : IsOpen G) (hGcpt : IsCompact (closure G)) :
    ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Gᶜ 0 ω < ⊤ := by
  let i : Fin d := 0
  obtain ⟨R, hRsubset⟩ := hGcpt.isBounded.subset_closedBall (0 : State)
  have hxClosure : x ∈ closure G := subset_closure hx
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hRsubset hxClosure
  have hxi_abs : |x i| ≤ R := by
    calc
      |x i| = ‖x i‖ := by simp
      _ ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
      _ ≤ R := hxR
  let a : ℝ := -(R + 1) - x i
  let b : ℝ := R + 1 - x i
  have ha : a < 0 := by
    have hxi_lower : -R ≤ x i := (abs_le.mp hxi_abs).1
    dsimp [a]
    linarith
  have hb : 0 < b := by
    have hxi_upper : x i ≤ R := (abs_le.mp hxi_abs).2
    dsimp [b]
    linarith
  let B0 : NNReal → Ω → ℝ := fun t ω ↦ if t = 0 then 0 else W t ω i - x i
  have hB0 : IsBrownianMotion (μ : Measure Ω) B0 := by
    let Z : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
    have hZ : IsBrownianMotionStartedAt (μ : Measure Ω) Z 0 := by
      -- Proof comment: recenter the chosen coordinate so the scalar motion starts at `0`.
      simpa [Z] using
        brownianStartedAt_sub_const_startedAtZero_local (hW.isBrownianMotionStartedAt i)
    -- Proof comment: patch the zero-time value to the literal constant `0` so the scalar owner
    -- matches the standard Brownian-motion theorem used for the hitting argument.
    simpa [B0, Z] using
      pointwiseZeroVersion_isBrownianMotion_local
        (μ := (μ : Measure Ω))
        (B := Z)
        hZ
  have hτscalar :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter B0 ({a, b} : Set ℝ) 0 ω ≠ ⊤ :=
    brownianMotion_twoSidedHittingTime_ae_ne_top (hB := hB0) (a := a) (b := b) ha hb
  filter_upwards [hτscalar] with ω hω
  simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hω
  rcases hω with ⟨t, ht_nonneg, hτ_mem⟩
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    have hB0_zero : B0 t ω = 0 := by
      simp [B0, ht0]
    rcases hτ_mem with hτa | hτb
    · have : a = 0 := by rw [← hτa]; exact hB0_zero
      linarith
    · have : b = 0 := by rw [← hτb]; exact hB0_zero
      linarith
  have hcoord_hit :
      W t ω i = -(R + 1) ∨ W t ω i = R + 1 := by
    rcases hτ_mem with hτa | hτb
    · left
      have hEq : W t ω i - x i = a := by
        simpa [B0, ht_ne_zero] using hτa
      dsimp [a] at hEq
      linarith
    · right
      have hEq : W t ω i - x i = b := by
        simpa [B0, ht_ne_zero] using hτb
      dsimp [b] at hEq
      linarith
  have hcoord_abs : |W t ω i| = R + 1 := by
    rcases hcoord_hit with hleft | hright
    · have hRp1_nonneg : 0 ≤ R + 1 := by linarith [hxR]
      rw [hleft, abs_neg, abs_of_nonneg hRp1_nonneg]
    · have hRp1_nonneg : 0 ≤ R + 1 := by linarith [hxR]
      rw [hright, abs_of_nonneg hRp1_nonneg]
  have hnot_closedBall : W t ω ∉ Metric.closedBall (0 : State) R := by
    intro hball
    have hnorm_le : ‖W t ω‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hball
    have hcoord_le : R + 1 ≤ ‖W t ω‖ := by
      calc
        R + 1 = |W t ω i| := hcoord_abs.symm
        _ = ‖W t ω i‖ := by simp
        _ ≤ ‖W t ω‖ := by simpa using PiLp.norm_apply_le (W t ω) i
    linarith
  have hWt_mem : W t ω ∈ Gᶜ := by
    -- Proof comment: once one coordinate reaches magnitude `R + 1`, the whole state leaves the
    -- compact ball containing `closure G`, so it lies outside `G`.
    intro hWtG
    exact hnot_closedBall (hRsubset (subset_closure hWtG))
  have hτ_le : hittingAfter W Gᶜ 0 ω ≤ t := by
    -- Proof comment: after the path reaches `Gᶜ` at time `t`, the exit clock from `G` is no
    -- later than `t`.
    exact
      hittingAfter_le_of_mem
        (u := W) (s := Gᶜ) (n := (0 : NNReal)) (i := t) (ω := ω) ht_nonneg hWt_mem
  exact lt_of_le_of_lt hτ_le (by simpa using (WithTop.coe_lt_top t))

/-- Helper for Exercise 25.4.3: a Brownian vector started at `x` admits a same-space
modification whose sample paths are everywhere continuous and which agrees with the original
process at all deterministic times outside one measurable null set. -/
private theorem existsContinuousBrownianVectorStartedAtModification
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    ∃ Wc : VectorProcess,
      IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω) ∧
      (∀ ω : Ω, Wc 0 ω = x) ∧
      (∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, W t ω = Wc t ω) := by
  have hcont_ae :
      ∀ᵐ ω ∂(μ : Measure Ω), Continuous fun t : NNReal ↦ W t ω :=
    brownianVectorStartedAt_aeContinuous hW
  have hstart_ae :
      ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x :=
    brownianVectorStart_ae_eq_const μ hW
  have hgood :
      ∀ᵐ ω ∂(μ : Measure Ω), (Continuous fun t : NNReal ↦ W t ω) ∧ W 0 ω = x :=
    hcont_ae.and hstart_ae
  let bad : Set Ω := {ω | ¬ ((Continuous fun t : NNReal ↦ W t ω) ∧ W 0 ω = x)}
  have hbad_null : (μ : Measure Ω) bad = 0 := by
    simpa [bad] using (ae_iff.1 hgood)
  obtain ⟨N, hbad_subset, hN_meas, hN_null⟩ := exists_measurable_superset_of_null hbad_null
  have hN_good :
      ∀ ω : Ω, ω ∉ N → (Continuous fun t : NNReal ↦ W t ω) ∧ W 0 ω = x := by
    intro ω hωN
    by_contra hbadω
    exact hωN (hbad_subset hbadω)
  let Wc : VectorProcess := fun t ω ↦ if ω ∈ N then x else W t ω
  have hWc_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simpa [Wc, hω] using (continuous_const : Continuous fun _ : NNReal ↦ x)
    · simpa [Wc, hω] using (hN_good ω hω).1
  have hWc_eq :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, W t ω = Wc t ω := by
    filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hω t
    have hω' : ω ∉ N := by simpa using hω
    simp [Wc, hω']
  have hWc_start : ∀ ω : Ω, Wc 0 ω = x := by
    intro ω
    by_cases hω : ω ∈ N
    · simp [Wc, hω]
    · simpa [Wc, hω] using (hN_good ω hω).2
  have hWc_owner : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x := by
    refine
      { isBrownianMotionStartedAt := ?_
        iIndepFun := ?_ }
    · intro i
      let B : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
      let Bc : NNReal → Ω → ℝ := fun t ω ↦ if ω ∈ N then 0 else B t ω
      have hB : IsBrownianMotionStartedAt (μ : Measure Ω) B 0 := by
        -- Proof comment: recenter the `i`-th coordinate at its deterministic start value.
        simpa [B] using
          brownianStartedAt_sub_const_startedAtZero_local
            (hW.isBrownianMotionStartedAt i)
      have hBc : IsBrownianMotion (μ : Measure Ω) Bc := by
        -- Proof comment: patch the recentered coordinate on the common null set so every sample
        -- path becomes continuous.
        apply zeroStarted_nullPatch_isBrownianMotion_local
          (μ := (μ : Measure Ω)) (B := B) hB hN_meas hN_null
        · intro ω hω
          have hcoord_cont : Continuous fun t : NNReal ↦ Wc t ω i := by
            simpa using
              (continuous_apply i).comp
                ((EuclideanSpace.equiv (Fin d) ℝ).continuous.comp (hWc_cont ω))
          simpa [Wc, hω] using hcoord_cont.sub continuous_const
        · intro ω hω
          have hi : W 0 ω i = x i := by
            simpa [Wc, hω] using congrArg (fun y : State ↦ y i) (hWc_start ω)
          simp [B, hi]
      -- Proof comment: adding the deterministic start value back recovers the patched coordinate
      -- of `Wc`.
      have hTranslated :
          IsBrownianMotionStartedAt
            (μ : Measure Ω) (fun t ω ↦ x i + Bc t ω) (x i) := by
        letI : IsProbabilityMeasure (μ : Measure Ω) := by infer_instance
        refine
          { stronglyMeasurable := fun t ↦ (hBc.stronglyMeasurable t).const_add (x i)
            start := ?_
            indepIncrements := ?_
            stationaryIncrements := ?_
            gaussian_marginal := ?_
            continuous_paths := ?_ }
        · have hpreimage : (fun ω ↦ x i + Bc 0 ω) ⁻¹' ({x i} : Set ℝ) = Set.univ := by
            ext ω
            simp [hBc.zero]
          rw [hpreimage]
          simp
        · rw [hasIndepIncrements_iff_nat]
          intro t ht
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            hBc.indepIncrements.nat (t := t) ht
        · intro r s t
          have hleft :
              (fun ω ↦ (x i + Bc ((s + t) + r) ω) - (x i + Bc (t + r) ω)) =
                (fun ω ↦ Bc ((s + t) + r) ω - Bc (t + r) ω) := by
            funext ω
            ring
          have hright :
              (fun ω ↦ (x i + Bc (s + r) ω) - (x i + Bc r ω)) =
                (fun ω ↦ Bc (s + r) ω - Bc r ω) := by
            funext ω
            ring
          simpa [hleft, hright] using hBc.stationaryIncrements r s t
        · intro t ht
          simpa [add_comm] using ProbabilityTheory.gaussianReal_add_const
            (hBc.gaussian_marginal ht) (x i)
        · filter_upwards [hBc.continuous_paths] with ω hω
          simpa [HasAlmostSurelyContinuousPaths, processPath] using continuous_const.add hω
      convert hTranslated using 1
      funext t ω
      by_cases hω : ω ∈ N <;> simp [Wc, B, Bc, hω, sub_eq_add_neg, add_assoc, add_left_comm]
    · have hcoord_eq :
          ∀ i : Fin d,
            (fun ω ↦ fun t : NNReal ↦ W t ω i) =ᵐ[(μ : Measure Ω)]
              (fun ω ↦ fun t : NNReal ↦ Wc t ω i) := by
        intro i
        filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hω
        have hω' : ω ∉ N := by simpa using hω
        funext t
        simp [Wc, hω']
      -- Proof comment: patching on one common null set preserves independence of the coordinate
      -- path family.
      exact hW.iIndepFun.congr hcoord_eq
  exact ⟨Wc, hWc_owner, hWc_cont, hWc_start, hWc_eq⟩

/-- Helper for Exercise 25.4.3: if a continuous path stays in `G` at all earlier times and is in
`Gᶜ` at time `t > 0`, then the time-`t` value lies on `frontier G`. -/
private theorem memFrontierOfContinuousPathOfLeftMem
    {G : Set State} {W : VectorProcess} {ω : Ω} {t : NNReal}
    (hcont : Continuous fun s : NNReal ↦ W s ω)
    (htPos : 0 < t) (htMem : W t ω ∈ Gᶜ)
    (hleft : ∀ s : NNReal, s < t → W s ω ∈ G) :
    W t ω ∈ frontier G := by
  have hmemClosure : W t ω ∈ closure G := by
    rw [mem_closure_iff]
    intro o ho hWt
    have hPreimage : {s : NNReal | W s ω ∈ o} ∈ 𝓝 t := by
      -- Proof comment: continuity at `t` pulls the neighborhood of `W t ω` back to a
      -- neighborhood of the clock value.
      exact hcont.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds ho hWt)
    rcases mem_nhds_iff.mp hPreimage with ⟨u, huSubset, huOpen, htMemU⟩
    have htClosure : t ∈ closure (Set.Iio t : Set NNReal) := by
      have hclosureIio : closure (Set.Iio t : Set NNReal) = Set.Iic t :=
        closure_Iio' ⟨0, htPos⟩
      rw [hclosureIio]
      simp
    rcases (mem_closure_iff.mp htClosure) u huOpen htMemU with ⟨s, hsMemU, hsLtT⟩
    have hWsMemO : W s ω ∈ o := huSubset hsMemU
    have hWsMemG : W s ω ∈ G := hleft s hsLtT
    -- Proof comment: every neighborhood of `W t ω` contains an earlier path value still inside
    -- `G`, so the exit point belongs to `closure G`.
    exact ⟨W s ω, hWsMemO, hWsMemG⟩
  -- Proof comment: combine the closure information from the left with the actual time-`t`
  -- membership in `Gᶜ`.
  rw [frontier_eq_closure_inter_closure]
  exact ⟨hmemClosure, subset_closure htMem⟩

/-- Helper for Exercise 25.4.3: if a continuous path starts in `G` and has finite exit time, then
the stopped exit value lies on `frontier G`. -/
private theorem stoppedValue_mem_frontier_at_exit_of_continuous
    {G : Set State} {W : VectorProcess} {x0 : State}
    (hx0 : x0 ∈ G) (hG : IsOpen G)
    (hcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hStart : ∀ ω : Ω, W 0 ω = x0)
    {ω : Ω} (hω : hittingAfter W Gᶜ 0 ω < ⊤) :
    stoppedValue W (hittingAfter W Gᶜ 0) ω ∈ frontier G := by
  have hτNeTop : hittingAfter W Gᶜ 0 ω ≠ ⊤ := ne_of_lt hω
  let hitSet : Set NNReal := {t : NNReal | W t ω ∈ Gᶜ}
  have hHitExists : ∃ t : NNReal, W t ω ∈ Gᶜ := by
    -- Proof comment: a finite exit clock gives an actual witness time in the complement.
    simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hτNeTop
    rcases hτNeTop with ⟨t, _, htMem⟩
    exact ⟨t, htMem⟩
  have hHitNonempty : hitSet.Nonempty := by
    rcases hHitExists with ⟨t, htMem⟩
    exact ⟨t, htMem⟩
  have hHitClosed : IsClosed hitSet := by
    have hClosedGc : IsClosed (Gᶜ : Set State) := isClosed_compl_iff.mpr hG
    change IsClosed ((fun t : NNReal ↦ W t ω) ⁻¹' (Gᶜ : Set State))
    exact hClosedGc.preimage (hcont ω)
  have hHitBddBelow : BddBelow hitSet := ⟨0, fun _ _ ↦ bot_le⟩
  have hsInfMem : sInf hitSet ∈ hitSet :=
    hHitClosed.csInf_mem hHitNonempty hHitBddBelow
  have hτEq : (hittingAfter W Gᶜ 0 ω).untopA = sInf hitSet := by
    -- Proof comment: because the lower bound is `0`, the exit clock is the infimum of the raw
    -- hit set.
    rw [hittingAfter]
    rw [if_pos]
    · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ W i ω ∈ Gᶜ} = hitSet by
          ext t
          simp [hitSet]]
      simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf hitSet))
    · rcases hHitExists with ⟨t, htMem⟩
      exact ⟨t, bot_le, htMem⟩
  have hHitMem : W (hittingAfter W Gᶜ 0 ω).untopA ω ∈ Gᶜ := by
    simpa [hitSet, hτEq] using hsInfMem
  have hτUntaggedNeZero : (hittingAfter W Gᶜ 0 ω).untopA ≠ 0 := by
    intro hτZero
    have hZeroMem : W 0 ω ∈ Gᶜ := by
      simpa [hτZero] using hHitMem
    exact hZeroMem (by simpa [hStart ω] using hx0)
  have hτUntaggedPos : 0 < (hittingAfter W Gᶜ 0 ω).untopA :=
    lt_of_le_of_ne bot_le hτUntaggedNeZero.symm
  have hLeft :
      ∀ s : NNReal, s < (hittingAfter W Gᶜ 0 ω).untopA → W s ω ∈ G := by
    intro s hs
    have hsHit : (s : WithTop NNReal) < hittingAfter W Gᶜ 0 ω := by
      lift hittingAfter W Gᶜ 0 ω to NNReal using hτNeTop with t ht
      have hτIdx : (hittingAfter W Gᶜ 0 ω).untopA = t := by
        rw [← ht]
        simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := t))
      have hsT : s < t := by
        simpa [hτIdx] using hs
      have hsCoe : (s : WithTop NNReal) < (t : WithTop NNReal) := by
        exact_mod_cast hsT
      exact ht ▸ hsCoe
    have hNotGc :
        W s ω ∉ Gᶜ :=
      notMem_of_lt_hittingAfter
        (u := W) (s := Gᶜ) (n := (0 : NNReal)) (ω := ω) (k := s) hsHit (by simp)
    simpa using hNotGc
  -- Proof comment: the path stays in `G` before its first exit and lands in `Gᶜ` at that exit,
  -- so continuity forces the stopped value onto `frontier G`.
  simpa [stoppedValue, hτNeTop] using
    memFrontierOfContinuousPathOfLeftMem
      (W := W) (G := G) (ω := ω) (t := (hittingAfter W Gᶜ 0 ω).untopA)
      (hcont ω) hτUntaggedPos hHitMem hLeft

/-- Helper for Exercise 25.4.3: once the exit clock and stopped value are measurable, continuous
paths started in `G` admit a measurable frontier-valued exit map. -/
private theorem existsMeasurableFrontierExitValue_ofContinuousPaths
    {G : Set State} {W : VectorProcess} {x0 : State}
    (hFrontier : (frontier G).Nonempty)
    (hx0 : x0 ∈ G) (hG : IsOpen G)
    (hτmeas : Measurable (hittingAfter W Gᶜ 0))
    (hStoppedMeas : Measurable (stoppedValue W (hittingAfter W Gᶜ 0)))
    (hcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hStart : ∀ ω : Ω, W 0 ω = x0) :
    ∃ exitValue : Ω → frontier G, Measurable exitValue ∧
      (∀ ω : Ω, hittingAfter W Gᶜ 0 ω < ⊤ →
        (exitValue ω : State) = stoppedValue W (hittingAfter W Gᶜ 0) ω) := by
  rcases hFrontier with ⟨z0, hz0⟩
  let rawExit : Ω → State :=
    {ω | hittingAfter W Gᶜ 0 ω < ⊤}.piecewise
      (stoppedValue W (hittingAfter W Gᶜ 0))
      (fun _ ↦ z0)
  have hFiniteMeas :
      MeasurableSet {ω : Ω | hittingAfter W Gᶜ 0 ω < (⊤ : WithTop NNReal)} :=
    hτmeas measurableSet_Iio
  have hRawFrontier : ∀ ω : Ω, rawExit ω ∈ frontier G := by
    intro ω
    by_cases hω : hittingAfter W Gᶜ 0 ω < ⊤
    · -- Proof comment: on the finite-exit branch, the stopped value is already a frontier point.
      simpa [rawExit, hω] using
        stoppedValue_mem_frontier_at_exit_of_continuous
          (G := G) (W := W) hx0 hG hcont hStart hω
    · -- Proof comment: on the infinite branch, the piecewise definition falls back to the fixed
      -- frontier base point.
      simp [rawExit, hω, hz0]
  have hRawMeas : Measurable rawExit :=
    hStoppedMeas.piecewise hFiniteMeas measurable_const
  let exitValue : Ω → frontier G := fun ω ↦ ⟨rawExit ω, hRawFrontier ω⟩
  have hExitMeas : Measurable exitValue :=
    hRawMeas.codRestrict hRawFrontier
  refine ⟨exitValue, hExitMeas, ?_⟩
  intro ω hω
  -- Proof comment: on the finite-exit branch, the packaged frontier value is definitionally the
  -- stopped exit point.
  simp [exitValue, rawExit, hω]

/-- Helper for Exercise 25.4.3: once measurability is available, a continuous Brownian path
started inside the open ball admits a measurable frontier-valued exit map. -/
private theorem existsMeasurableOpenBallFrontierExitValue_ofContinuousPaths
    {W : VectorProcess} (r : ℝ) (hr : 0 < r)
    {x : State} (hx : x ∈ Metric.ball (0 : State) r)
    (hτmeas : Measurable (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0))
    (hStoppedMeas :
      Measurable (stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0)))
    (hcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hStart : ∀ ω : Ω, W 0 ω = x) :
    ∃ exitValue : Ω → frontier (Metric.ball (0 : State) r), Measurable exitValue ∧
      (∀ ω : Ω, hittingAfter W (Metric.ball (0 : State) r)ᶜ 0 ω < ⊤ →
        (exitValue ω : State) =
          stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω) := by
  letI : Nontrivial State := by infer_instance
  have hFrontier :
      (frontier (Metric.ball (0 : State) r)).Nonempty := by
    have hSphere : (Metric.sphere (0 : State) r).Nonempty := by
      let h : (Metric.sphere (0 : State) r).Nonempty ↔ 0 ≤ r :=
        NormedSpace.sphere_nonempty
      exact h.2 hr.le
    simpa [openBallFrontier_eq_sphereAbs (d := d) r hr, abs_of_pos hr] using hSphere
  -- Proof comment: the generic continuous-path exit packager now specializes to the open ball.
  exact
    existsMeasurableFrontierExitValue_ofContinuousPaths
      (G := Metric.ball (0 : State) r) (W := W) hFrontier hx Metric.isOpen_ball
      hτmeas hStoppedMeas hcont hStart

/-- Helper for Exercise 25.4.3: Brownian motion started inside the open ball exits that ball in
finite time almost surely. -/
private theorem openBallExitTime_ae_lt_top
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (r : ℝ) (hr : 0 < r)
    (hW : ∀ z : State, IsBrownianMotionVectorStartedAt (P z : Measure Ω) W z)
    {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    ∀ᵐ ω ∂ (P x : Measure Ω),
      hittingAfter W (Metric.ball (0 : State) r)ᶜ 0 ω < ⊤ := by
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  let B : NNReal → Ω → ℝ := fun t ω ↦ if t = 0 then 0 else W t ω i - x i
  have hxNorm : ‖x‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hxi_lt_r : x i < r := by
    have hcoordNorm : ‖x i‖ ≤ ‖x‖ := by
      simpa using PiLp.norm_apply_le x i
    have hle : x i ≤ ‖x‖ := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hcoordNorm)
    exact lt_of_le_of_lt hle hxNorm
  have hLevelPos : 0 < r - x i := by
    linarith
  have hBstarted :
      IsBrownianMotionStartedAt
        (P x : Measure Ω)
        (fun t ω ↦ W t ω i - x i)
        0 := by
    -- Proof comment: subtracting the deterministic start from one Brownian coordinate recenters it
    -- to the standard started-at-zero spelling.
    exact
      brownianStartedAt_sub_const_startedAtZero_local
        ((hW x).isBrownianMotionStartedAt i)
  let _ : IsProbabilityMeasure (P x : Measure Ω) := hBstarted.isProbabilityMeasure
  have hB : IsBrownianMotion (P x : Measure Ω) B := by
    -- Proof comment: patching the time-zero value to the literal constant `0` upgrades the
    -- recentered coordinate to the standard Brownian owner needed by the level-hitting theorem.
    exact pointwiseZeroVersion_isBrownianMotion_local hBstarted
  filter_upwards
      [brownianLevelHittingTime_ae_ne_top
        (μ := (P x : Measure Ω)) (B := B) hB hLevelPos] with ω hω
  obtain ⟨t, ht_hit⟩ :=
    (brownianLevelHittingTime_ne_top_iff_exists_eq
      (B := B) (b := r - x i) (ω := ω)).1 hω
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    subst ht0
    simp [B] at ht_hit
    linarith
  have hcoord_eq : W t ω i = r := by
    -- Proof comment: hitting the positive recentered level means the chosen Brownian coordinate
    -- itself reaches the boundary value `r`.
    simp [B, ht_ne_zero] at ht_hit
    linarith
  have hnorm_ge : r ≤ ‖W t ω‖ := by
    have hcoordNorm : ‖W t ω i‖ ≤ ‖W t ω‖ := by
      simpa using PiLp.norm_apply_le (W t ω) i
    calc
      r = |W t ω i| := by rw [hcoord_eq, abs_of_pos hr]
      _ ≤ ‖W t ω‖ := by simpa [Real.norm_eq_abs] using hcoordNorm
  have hmemCompl : W t ω ∈ (Metric.ball (0 : State) r)ᶜ := by
    -- Proof comment: one coordinate already has absolute value `r`, so the Euclidean norm cannot
    -- stay strictly below the ball radius.
    change W t ω ∉ Metric.ball (0 : State) r
    intro hball
    have hnorm_lt : ‖W t ω‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hball
    exact (not_lt_of_ge hnorm_ge) hnorm_lt
  have hExit_le :
      hittingAfter W (Metric.ball (0 : State) r)ᶜ 0 ω ≤ (t : ENNReal) :=
    hittingAfter_le_of_mem
      (u := W) (s := (Metric.ball (0 : State) r)ᶜ) (n := (0 : NNReal)) (ω := ω)
      (by simp)
      hmemCompl
  exact lt_of_le_of_lt hExit_le ENNReal.coe_lt_top

/-- Helper for Exercise 25.4.3: the closure of the open ball is compact. This packages the
precompactness input needed by the optional-stopping route on the ball. -/
private theorem isCompact_closure_openBall
    (r : ℝ) (hr : 0 < r) :
    IsCompact (closure (Metric.ball (0 : State) r)) := by
  simpa [closure_ball (0 : State) hr.ne'] using
    (isCompact_closedBall (0 : State) r)

/-- Helper for Exercise 25.4.3: compact closure bounds the absolute value of a continuous
observable on that closure. This is the compactness input later used to dominate stopped-value
integrands in the ball-specialized optional-stopping argument. -/
private theorem existsAbsLeOnCompactClosure_continuous
    {U : Set State} {F : State → ℝ}
    (hUcpt : IsCompact (closure U))
    (hFcont : Continuous F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closure U, |F z| ≤ C := by
  have hImageCompact : IsCompact (F '' closure U) := hUcpt.image hFcont
  rcases hImageCompact.bddBelow with ⟨l, hl⟩
  rcases hImageCompact.bddAbove with ⟨r, hr⟩
  refine ⟨max |l| |r|, by positivity, ?_⟩
  intro z hz
  have hzImage : F z ∈ F '' closure U := ⟨z, hz, rfl⟩
  have hlz : l ≤ F z := hl hzImage
  have hrz : F z ≤ r := hr hzImage
  -- Proof comment: compactness bounds the image interval, so the larger absolute endpoint
  -- controls every value of `F` on `closure U`.
  refine abs_le.mpr ⟨?_, ?_⟩
  · calc
      -max |l| |r| ≤ -|l| := neg_le_neg (le_max_left |l| |r|)
      _ ≤ l := neg_abs_le l
      _ ≤ F z := hlz
  · calc
      F z ≤ r := hrz
      _ ≤ |r| := le_abs_self r
      _ ≤ max |l| |r| := le_max_right |l| |r|

/-- Helper for Exercise 25.4.3: a compact subset of an open set admits an open buffer whose
closure still stays inside the ambient open set. -/
private theorem exists_open_buffer_of_isCompact_subset_open
    {K G : Set State}
    (hKcompact : IsCompact K)
    (hKG : K ⊆ G)
    (hGo : IsOpen G) :
    ∃ T : Set State, IsOpen T ∧ K ⊆ T ∧ closure T ⊆ G := by
  have hGnhds : G ∈ 𝓝ˢ K := hGo.mem_nhdsSet.2 hKG
  rcases hKcompact.exists_isOpen_closure_subset hGnhds with ⟨T, hTo, hKT, hTcl⟩
  -- Proof comment: compactness lets us shrink the neighborhood filter of `K` to one open set
  -- whose closure already lies inside `G`.
  exact ⟨T, hTo, hKT, hTcl⟩

/-- Helper for Exercise 25.4.3: a harmonic function on an open buffer around a precompact stage
admits a global `C²` extension that stays harmonic on the stage and agrees with the original
function there. -/
private theorem existsStageHarmonicExtension
    {V T G : Set State} {u : State → ℝ}
    (hVT : closure V ⊆ T) (hTG : closure T ⊆ G) (hTo : IsOpen T)
    (hu : InnerProductSpace.HarmonicOnNhd u G) :
    ∃ F : State → ℝ,
      ContDiff ℝ 2 F ∧
      InnerProductSpace.HarmonicOnNhd F V ∧
      Set.EqOn F u V := by
  rcases exists_contMDiffMap_one_nhds_of_subset_interior
      (I := modelWithCornersSelf ℝ State) (M := State)
      (n := (2 : ℕ∞)) (s := closure V) (t := T)
      isClosed_closure
      (by simpa [hTo.interior_eq] using hVT) with
    ⟨φ, hOne, hZero, _hRange⟩
  let F : State → ℝ := fun x ↦ φ x * u x
  have hφ : ContDiff ℝ 2 φ := by
    simpa using φ.contMDiff.contDiff
  have hF_contDiff : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ closure T
    · have hxG : x ∈ G := hTG hx
      -- Proof comment: on the closure of the cutoff support, both factors are already `C²`.
      exact (hφ.contDiffAt).mul (hu x hxG).1
    · have hFzero : F =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        have hOutside : (closure T)ᶜ ∈ 𝓝 x :=
          isClosed_closure.isOpen_compl.mem_nhds hx
        filter_upwards [hOutside] with y hy
        have hyT : y ∉ T := fun hyT ↦ hy (subset_closure hyT)
        simp [F, hZero y hyT]
      -- Proof comment: away from the buffer, the cutoff vanishes on a whole neighborhood.
      exact contDiffAt_const.congr_of_eventuallyEq hFzero
  have hF_harmonic : InnerProductSpace.HarmonicOnNhd F V := by
    intro x hxV
    have hxT : x ∈ T := hVT (subset_closure hxV)
    have hxG : x ∈ G := hTG (subset_closure hxT)
    have hφx : ∀ᶠ y in 𝓝 x, φ y = 1 :=
      mem_nhdsSet_iff_forall.mp hOne x (subset_closure hxV)
    have hEq : F =ᶠ[𝓝 x] u := by
      filter_upwards [hφx] with y hy
      simp [F, hy]
    -- Proof comment: near points of `V`, the cutoff is identically `1`, so the extension is
    -- literally the original harmonic function.
    exact (InnerProductSpace.harmonicAt_congr_nhds hEq).2 (hu x hxG)
  have hF_eq : Set.EqOn F u V := by
    intro x hxV
    have hφx : ∀ᶠ y in 𝓝 x, φ y = 1 :=
      mem_nhdsSet_iff_forall.mp hOne x (subset_closure hxV)
    -- Proof comment: evaluating the neighborhood identity at the stage point gives pointwise
    -- agreement on `V`.
    have hx1 : φ x = 1 := hφx.self_of_nhds
    simp [F, hx1]
  exact ⟨F, hF_contDiff, hF_harmonic, hF_eq⟩

/-- Helper for Exercise 25.4.3: starting from a point of an open domain, one can choose an
increasing exhaustion by inner open stages whose closures stay compactly inside the domain. -/
private theorem existsInnerExhaustionStartingAt
    {G : Set State} (hG : IsOpen G) (hGcpt : IsCompact (closure G))
    {x : State} (hx : x ∈ G) :
    ∃ U : ℕ → Set State,
      (∀ n, IsOpen (U n)) ∧
      (∀ n, x ∈ U n) ∧
      (∀ n, IsCompact (closure (U n))) ∧
      (∀ n, closure (U n) ⊆ G) ∧
      Monotone U ∧
      (⋃ n, U n) = G := by
  by_cases hGcempty : Gᶜ = ∅
  · let U : ℕ → Set State := fun _ ↦ G
    have hGuniv : G = Set.univ := by
      ext y
      have hyc : y ∉ Gᶜ := by simpa [hGcempty]
      simpa using hyc
    refine ⟨U, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      simpa [U] using hG
    · intro n
      simpa [U] using hx
    · intro n
      simpa [U, hGcempty, closure_univ] using hGcpt
    · intro n
      simpa [U, hGuniv]
    · intro m n hmn
      simp [U]
    · ext y
      simp [U, hGuniv]
  · have hGcne : (Gᶜ : Set State).Nonempty := Set.nonempty_iff_ne_empty.mpr hGcempty
    let δ : ℝ := Metric.infDist x Gᶜ
    have hδpos : 0 < δ := by
      have hxnot : x ∉ Gᶜ := by simpa using hx
      exact ((isClosed_compl_iff.mpr hG).notMem_iff_infDist_pos hGcne).mp hxnot
    let r : ℕ → ℝ := fun n ↦ min (δ / 2) (1 / ((n + 1 : ℕ) : ℝ))
    let U : ℕ → Set State := fun n ↦ {y | r n < Metric.infDist y Gᶜ}
    have hU_open : ∀ n, IsOpen (U n) := by
      intro n
      -- Proof comment: each stage is a strict superlevel set of the continuous distance-to-
      -- complement map.
      simpa [U] using
        (Metric.continuous_infDist_pt (Gᶜ)).isOpen_preimage (Set.Ioi (r n)) isOpen_Ioi
    have hU_x : ∀ n, x ∈ U n := by
      intro n
      have hrlt : r n < δ := by
        calc
          r n ≤ δ / 2 := min_le_left _ _
          _ < δ := by linarith
      simpa [U, δ] using hrlt
    have hrpos : ∀ n, 0 < r n := by
      intro n
      have hInvPos : 0 < (1 / ((n + 1 : ℕ) : ℝ)) := by
        positivity
      exact lt_min (by linarith) hInvPos
    have hU_closure_subset : ∀ n, closure (U n) ⊆ G := by
      intro n
      let S : Set State := {y | r n ≤ Metric.infDist y Gᶜ}
      have hUsubsetS : U n ⊆ S := by
        intro y hy
        change r n ≤ Metric.infDist y Gᶜ
        exact le_of_lt (by simpa [U] using hy)
      have hSclosed : IsClosed S := by
        -- Proof comment: pass from the open superlevel set to the closed weak superlevel set
        -- before pushing the closure back into `G`.
        simpa [S] using
          (isClosed_le continuous_const (Metric.continuous_infDist_pt (Gᶜ)))
      refine subset_trans (closure_minimal hUsubsetS hSclosed) ?_
      intro y hy
      change r n ≤ Metric.infDist y Gᶜ at hy
      by_contra hyc
      have : Metric.infDist y Gᶜ = 0 := Metric.infDist_zero_of_mem hyc
      have hle : r n ≤ 0 := by simpa [this] using hy
      exact (not_le_of_gt (hrpos n)) hle
    have hU_compact : ∀ n, IsCompact (closure (U n)) := by
      intro n
      refine IsCompact.of_isClosed_subset hGcpt isClosed_closure ?_
      exact subset_trans (hU_closure_subset n) subset_closure
    have hU_mono : Monotone U := by
      intro m n hmn y hy
      have hcast : ((m + 1 : ℕ) : ℝ) ≤ (n + 1 : ℕ) := by
        exact_mod_cast Nat.succ_le_succ hmn
      have hInv :
          (1 / ((n + 1 : ℕ) : ℝ)) ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
        exact one_div_le_one_div_of_le (by positivity) hcast
      have hrmono : r n ≤ r m := min_le_min_left _ hInv
      -- Proof comment: the distance threshold decreases with `n`, so the superlevel sets grow.
      exact lt_of_le_of_lt hrmono hy
    have hUnion : (⋃ n, U n) = G := by
      ext y
      constructor
      · intro hy
        rcases Set.mem_iUnion.mp hy with ⟨n, hyn⟩
        exact hU_closure_subset n (subset_closure hyn)
      · intro hyG
        have hypos : 0 < Metric.infDist y Gᶜ := by
          have hynot : y ∉ Gᶜ := by simpa using hyG
          exact ((isClosed_compl_iff.mpr hG).notMem_iff_infDist_pos hGcne).mp hynot
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hypos
        have hn' : 1 / ((n + 1 : ℕ) : ℝ) < Metric.infDist y Gᶜ := by
          simpa using hn
        refine Set.mem_iUnion.mpr ⟨n, ?_⟩
        have hrlt :
            r n < Metric.infDist y Gᶜ := by
          calc
            r n ≤ 1 / ((n + 1 : ℕ) : ℝ) := min_le_right _ _
            _ < Metric.infDist y Gᶜ := hn'
        exact hrlt
    exact ⟨U, hU_open, hU_x, hU_compact, hU_closure_subset, hU_mono, hUnion⟩

/-- Helper for Exercise 25.4.3: a function continuous on `closure G` admits a global continuous
extension agreeing with the original function on `closure G`. -/
private theorem existsContinuousExtensionOnClosure
    {G : Set State} {u : State → ℝ}
    (hu : ContinuousOn u (closure G)) :
    ∃ U : State → ℝ, Continuous U ∧ Set.EqOn U u (closure G) := by
  let uCl : C(closure G, ℝ) :=
    ⟨fun z ↦ u z, continuousOn_iff_continuous_restrict.mp hu⟩
  rcases
      ContinuousMap.exists_restrict_eq
        (s := closure G)
        isClosed_closure
        uCl with ⟨U, hU⟩
  refine ⟨U, U.continuous, ?_⟩
  intro z hz
  -- Proof comment: the Tietze extension restricts back to the original continuous map on the
  -- closed set `closure G`, so evaluation at `z` recovers the original value.
  have hzEq : U.restrict (closure G) ⟨z, hz⟩ = uCl ⟨z, hz⟩ := by
    exact congrArg (fun f : C(closure G, ℝ) ↦ f ⟨z, hz⟩) hU
  simpa [uCl] using hzEq

/-- Helper for Exercise 25.4.3: once a bounded local martingale is written as a process minus its
initial constant, every deterministic-time slice already has expectation equal to that initial
value. This isolates the pure martingale algebra from the remaining exit-time geometry. -/
private theorem expectation_eq_of_bounded_localMartingale_increment
    {μ : ProbabilityMeasure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} {c : ℝ}
    (hLocal : IsLocalMartingale ℱ (μ : Measure Ω) (fun t ω ↦ M t ω - c))
    (hBounded : BoundedInTimeAe (μ : Measure Ω) (fun t ω ↦ M t ω - c))
    (hInitial : M 0 =ᵐ[(μ : Measure Ω)] fun _ : Ω ↦ c) :
    ∀ n : ℕ, c = ∫ ω, M n ω ∂(μ : Measure Ω) := by
  intro n
  have hMart :
      Martingale (fun t ω ↦ M t ω - c) ℱ (μ : Measure Ω) :=
    martingale_of_bounded_local_martingale hLocal hBounded
  have hZeroIntegral :
      ∫ ω, M n ω - c ∂(μ : Measure Ω) = 0 := by
    have hConstEq :
        ∫ ω, M n ω - c ∂(μ : Measure Ω) =
          ∫ ω, M 0 ω - c ∂(μ : Measure Ω) := by
      -- Proof comment: boundedness upgrades the local martingale to a genuine martingale, so its
      -- deterministic-time expectations are constant.
      simpa [setIntegral_univ] using
        (hMart.setIntegral_eq
          (show (0 : NNReal) ≤ n by exact zero_le _)
          (s := Set.univ)
          MeasurableSet.univ).symm
    have hInitialZero :
        (fun ω ↦ M 0 ω - c) =ᵐ[(μ : Measure Ω)] fun _ : Ω ↦ (0 : ℝ) := by
      filter_upwards [hInitial] with ω hω
      simp [hω]
    calc
      ∫ ω, M n ω - c ∂(μ : Measure Ω) =
          ∫ ω, M 0 ω - c ∂(μ : Measure Ω) :=
        hConstEq
      _ = 0 := by
        rw [integral_congr_ae hInitialZero]
        simp
  have hSliceIntegrable : Integrable (M n) (μ : Measure Ω) := by
    have hAdd :
        Integrable (fun ω ↦ (M n ω - c) + c) (μ : Measure Ω) :=
      (hMart.integrable n).add (integrable_const c)
    have hEq :
        (fun ω ↦ (M n ω - c) + c) = M n := by
      funext ω
      ring
    exact hEq ▸ hAdd
  have hConstIntegrable : Integrable (fun _ : Ω ↦ c) (μ : Measure Ω) :=
    integrable_const c
  have hSub :
      ∫ ω, M n ω - c ∂(μ : Measure Ω) =
        ∫ ω, M n ω ∂(μ : Measure Ω) - ∫ ω, c ∂(μ : Measure Ω) := by
    -- Proof comment: rewrite the increment integral as the difference of the slice integral and
    -- the deterministic starting constant.
    simpa [Pi.sub_apply] using integral_sub hSliceIntegrable hConstIntegrable
  have hConstIntegral : ∫ ω, c ∂(μ : Measure Ω) = c := by
    simp
  linarith [hZeroIntegral, hSub, hConstIntegral]

/-- Helper for Exercise 25.4.3: if a global extension agrees with `u` on `closure U`, then their
deterministic stopped-value integrals over the exit clock from `U` coincide. -/
private theorem integral_stageStopped_eq_of_eqOn_closure
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {u F : State → ℝ}
    (hx : x ∈ U) (hUo : IsOpen U)
    (hWcont :
      ∀ᵐ ω ∂(μ : Measure Ω), Continuous fun t : NNReal ↦ W t ω)
    (hStart :
      ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hEq : Set.EqOn F u (closure U))
    (n : ℕ) :
    ∫ ω, F (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) ∂(μ : Measure Ω) =
      ∫ ω, u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) ∂(μ : Measure Ω) := by
  refine integral_congr_ae ?_
  filter_upwards [hWcont, hStart, hExitFinite] with ω hωcont hωstart hωfin
  have hStartMem : W 0 ω ∈ U := by
    simpa [hωstart] using hx
  have hmem :
      stoppedProcess W (hittingAfter W Uᶜ 0) n ω ∈ closure U :=
    stageStoppedProcess_mem_buffer
      (U := U) (V := closure U) (W := W) (ω := ω)
      hUo hωcont hStartMem (by intro z hz; exact hz) hωfin n
  -- Proof comment: every deterministic stopped value stays on `closure U`, where the extension
  -- and the original solution agree pointwise.
  exact hEq hmem

/-- Helper for Exercise 25.4.3: if a measurable extension agrees with `u` on `closure U`, then
each deterministic stage slice `ω ↦ u(W_{n ∧ τ_U}(ω))` is almost-everywhere strongly measurable.
-/
private theorem stageStopped_eqOnClosure_aestronglyMeasurable_atNat
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {u F : State → ℝ}
    (hx : x ∈ U) (hUo : IsOpen U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hStart : ∀ ω : Ω, W 0 ω = x)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFmeas : Measurable F)
    (hEq : Set.EqOn F u (closure U))
    (n : ℕ) :
    AEStronglyMeasurable
      (fun ω ↦ u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω))
      (μ : Measure Ω) := by
  let hWsm : ∀ t : NNReal, StronglyMeasurable (W t) :=
    brownianVectorStartedAt_stronglyMeasurable hW
  have hτ :
      IsStoppingTime
        (Filtration.natural W hWsm)
        (hittingAfter W Uᶜ 0) :=
    stageExit_isStoppingTime_of_continuous_of_aeExitFinite
      (μ := μ) (W := W) (U := U) (x := x) hW hWcont hUo hExitFinite
  have hWstrong :
      StronglyAdapted (Filtration.natural W hWsm) W :=
    Filtration.stronglyAdapted_natural (u := W) hWsm
  have hWprog :
      ProgMeasurable (Filtration.natural W hWsm) W :=
    hWstrong.progMeasurable_of_continuous hWcont
  have hσ :
      IsStoppingTime
        (Filtration.natural W hWsm)
        (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal)) :=
    hτ.min_const (n : NNReal)
  have hStoppedMeas :
      Measurable
        (stoppedValue W (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal))) :=
    (measurable_stoppedValue hWprog hσ).mono hσ.measurableSpace_le le_rfl
  have hStoppedEq :
      (fun ω ↦ stoppedProcess W (hittingAfter W Uᶜ 0) n ω) =
        stoppedValue W (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal)) := by
    funext ω
    -- Proof comment: the deterministic stage `n` is the stopped value at the clipped clock
    -- `τ_U ∧ n`.
    simpa [min_comm] using
      (stoppedProcess_eq_stoppedValue_apply
        (u := W) (τ := hittingAfter W Uᶜ 0) (i := (n : NNReal)) ω).symm
  have hFStageMeas :
      Measurable
        (fun ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) n ω)) := by
    -- Proof comment: rewrite the deterministic stopped slice through the measurable clipped
    -- stopping time and then compose with the measurable extension.
    simpa [hStoppedEq] using hFmeas.comp hStoppedMeas
  have hStageEq :
      (fun ω ↦ u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω)) =ᵐ[(μ : Measure Ω)]
        fun ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) := by
    filter_upwards [hExitFinite] with ω hωfin
    have hStartMem : W 0 ω ∈ U := by
      simpa [hStart ω] using hx
    have hmem :
        stoppedProcess W (hittingAfter W Uᶜ 0) n ω ∈ closure U :=
      stageStoppedProcess_mem_buffer
        (U := U) (V := closure U) (W := W) (ω := ω)
        hUo (hWcont ω) hStartMem (by intro z hz; exact hz) hωfin n
    -- Proof comment: every deterministic stopped value stays on `closure U`, so the extension
    -- can be rewritten back to `u`.
    exact (hEq hmem).symm
  exact hFStageMeas.aestronglyMeasurable.congr hStageEq.symm

/-- Helper for Exercise 25.4.3: every compact time prefix strictly before the global exit time
lies inside one stage of the inner exhaustion. -/
private theorem innerExhaustion_prefix_subset_stage
    {Wc : VectorProcess} {G : Set State} {U : ℕ → Set State} {ω : Ω} {t : NNReal}
    (hUo : ∀ n, IsOpen (U n))
    (hUmono : Monotone U)
    (hUunion : (⋃ n, U n) = G)
    (hWcCont : Continuous fun s : NNReal ↦ Wc s ω)
    (ht : (t : ENNReal) < hittingAfter Wc Gᶜ 0 ω) :
    ∃ N : ℕ, ∀ s ∈ Set.Icc (0 : NNReal) t, Wc s ω ∈ U N := by
  let K : Set State := (fun s : NNReal ↦ Wc s ω) '' Set.Icc (0 : NNReal) t
  have hKcompact : IsCompact K := by
    -- Proof comment: the path image of the compact interval `[0,t]` is compact by continuity.
    exact isCompact_Icc.image_of_continuousOn hWcCont.continuousOn
  have hKsubset : K ⊆ ⋃ n, U n := by
    intro y hy
    rcases hy with ⟨s, hs, rfl⟩
    have hslt : (s : ENNReal) < hittingAfter Wc Gᶜ 0 ω :=
      lt_of_le_of_lt (by exact_mod_cast hs.2) ht
    have hsG : Wc s ω ∈ G := by
      have hsNotGc :
          Wc s ω ∉ Gᶜ :=
        notMem_of_lt_hittingAfter
          (u := Wc) (s := Gᶜ) (n := (0 : NNReal)) (ω := ω) hslt hs.1
      simpa using hsNotGc
    -- Proof comment: every prefix point stays in `G`, so the exhaustion cover places it in one
    -- stage.
    simpa [hUunion] using hsG
  obtain ⟨N, hKN⟩ :=
    hKcompact.elim_directed_cover U hUo hKsubset hUmono.directed_le
  refine ⟨N, ?_⟩
  intro s hs
  -- Proof comment: after compactness chooses one stage covering the whole prefix image, every
  -- time slice in `[0,t]` lands in that same stage.
  exact hKN (Set.mem_image_of_mem (fun r : NNReal ↦ Wc r ω) hs)

/-- Helper for Exercise 25.4.3: along an increasing inner exhaustion, the stage exit clocks
increase to the global exit clock on every continuous path with finite global exit. -/
private theorem innerExhaustion_hittingAfter_tendsto_exit
    {Wc : VectorProcess} {G : Set State} {U : ℕ → Set State} {ω : Ω}
    (hUo : ∀ n, IsOpen (U n))
    (hUcl : ∀ n, closure (U n) ⊆ G)
    (hUmono : Monotone U)
    (hUunion : (⋃ n, U n) = G)
    (hWcCont : Continuous fun t : NNReal ↦ Wc t ω)
    (hτfin : hittingAfter Wc Gᶜ 0 ω < ⊤) :
    Tendsto
      (fun n : ℕ ↦ hittingAfter Wc (U n)ᶜ 0 ω)
      atTop
      (𝓝 (hittingAfter Wc Gᶜ 0 ω)) := by
  let τ : ENNReal := hittingAfter Wc Gᶜ 0 ω
  let τn : ℕ → ENNReal := fun n ↦ hittingAfter Wc (U n)ᶜ 0 ω
  have hUsub : ∀ n, U n ⊆ G := by
    intro n z hz
    exact hUcl n (subset_closure hz)
  have hτn_mono : Monotone τn := by
    intro m n hmn
    -- Proof comment: larger stages have smaller complements, so their exit times occur later.
    exact
      hittingAfter_anti Wc (0 : NNReal)
        (show (U n)ᶜ ⊆ (U m)ᶜ by
          intro z hz hzm
          exact hz (hUmono hmn hzm))
        ω
  have hτn_le_τ : ∀ n, τn n ≤ τ := by
    intro n
    -- Proof comment: each stage lies in `G`, so exiting the stage cannot happen after exiting
    -- the ambient ball.
    exact
      hittingAfter_anti Wc (0 : NNReal)
        (show Gᶜ ⊆ (U n)ᶜ by
          intro z hz hzn
          exact hz (hUsub n hzn))
        ω
  have hLower : ∀ c : ENNReal, c < τ → ∃ N : ℕ, c < τn N := by
    intro c hc
    have hc_ne_top : c ≠ ⊤ := ne_of_lt (lt_trans hc hτfin)
    let t : NNReal := c.toNNReal
    have hct : (t : ENNReal) = c := by
      exact ENNReal.coe_toNNReal hc_ne_top
    obtain ⟨N, hN⟩ :=
      innerExhaustion_prefix_subset_stage
        (Wc := Wc) (G := G) (U := U) (ω := ω) (t := t)
        hUo hUmono hUunion hWcCont (by simpa [τ, t, hct] using hc)
    have hNotLe : ¬ τn N ≤ c := by
      intro hle
      have hτN_fin : τn N < ⊤ := lt_of_le_of_lt (hτn_le_τ N) hτfin
      have hτN_ne_top : τn N ≠ ⊤ := ne_of_lt hτN_fin
      have hτN_mem :
          Wc (τn N).untopA ω ∈ (U N)ᶜ := by
        exact
          mem_closedSet_at_hittingAfter_of_lt_top_local
            (A := (U N)ᶜ)
            (hAclosed := isClosed_compl_iff.mpr (hUo N))
            hWcCont
            hτN_fin
      have hτN_le_t : (τn N).untopA ≤ t := by
        exact (WithTop.untopA_le_iff (x := τn N) (hx := hτN_ne_top)).2 <|
          by simpa [t, hct] using hle
      have hτN_in : Wc (τn N).untopA ω ∈ U N :=
        hN (τn N).untopA ⟨bot_le, hτN_le_t⟩
      exact hτN_mem hτN_in
    -- Proof comment: if the stage exit were already at or before `c`, some prefix point would
    -- lie in `(U N)ᶜ`, contradicting the compact-prefix containment.
    exact ⟨N, lt_of_not_ge hNotLe⟩
  have hLub : IsLUB (Set.range τn) τ := by
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases hy with ⟨n, rfl⟩
      exact hτn_le_τ n
    · intro b hb
      refine le_of_forall_lt ?_
      intro c hc
      obtain ⟨N, hN⟩ := hLower c hc
      exact lt_of_lt_of_le hN (hb (Set.mem_range_self N))
  -- Proof comment: monotone convergence of the stage exit clocks now gives the desired limit.
  simpa [τ, τn] using tendsto_atTop_isLUB hτn_mono hLub

/-- Helper for Exercise 25.4.3: composing a measurable state observable with a process preserves
strong adaptedness in the natural filtration. -/
private theorem stateComposition_stronglyAdapted_natural_ball
    {W : VectorProcess} (hWsm : ∀ t : NNReal, StronglyMeasurable (W t))
    {F : State → ℝ} (hFmeas : Measurable F) :
    StronglyAdapted (Filtration.natural W hWsm) (fun t ω ↦ F (W t ω)) := by
  intro t
  have hWt :
      StronglyMeasurable[Filtration.natural W hWsm t] (W t) :=
    Filtration.stronglyAdapted_natural (u := W) hWsm t
  -- Proof comment: each deterministic-time slice factors through the current state `W t ω`
  -- followed by the measurable observable `F`.
  simpa using hFmeas.stronglyMeasurable.comp_measurable hWt.measurable

/-- Helper for Exercise 25.4.3: stopping the raw harmonic increment at `τ` is exactly the visibly
stopped increment. -/
private theorem stageStoppedExtension_eq_stoppedRawIncrement_ball
    {W : VectorProcess} {τ : Ω → ENNReal} {F : State → ℝ} {x : State} :
    stoppedProcess (fun t ω ↦ F (W t ω) - F x) τ =
      fun t ω ↦ F (stoppedProcess W τ t ω) - F x := by
  funext t ω
  by_cases hτ : τ ω = ⊤
  · simp [stoppedProcess, hτ]
  · simp [stoppedProcess, hτ]

/-- Helper for Exercise 25.4.3: if every deterministic-horizon stop of a continuous adapted
process is a martingale, then the process is a continuous local martingale. -/
private theorem isContinuousLocalMartingale_of_constStoppedMartingale_ball
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {Y : NNReal → Ω → ℝ}
    (hY_adapted : Adapted ℱ Y)
    (hY_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω)
    (hStopped :
      ∀ T : NNReal, Martingale (stoppedProcess Y (fun _ ↦ (T : ENNReal))) ℱ μ) :
    IsContinuousLocalMartingale ℱ μ Y := by
  refine
    { local_martingale := ?_
      continuous := hY_cont }
  refine (isLocalMartingale_iff ℱ μ Y).2 ⟨hY_adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ Y (fun n _ ↦ (n : ENNReal))).2 ⟨?_, ?_, ?_⟩
  · intro n
    -- Proof comment: deterministic horizons are stopping times.
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    -- Proof comment: the deterministic localizing sequence `n` increases to `∞`.
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    have hMart :
        Martingale (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ :=
      hStopped n
    have hUI :
        UniformIntegrable
          (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          1
          μ := by
      have hDet :
          Martingale
              (stoppedProcess
                (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
                (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ ∧
            UniformIntegrable
              (stoppedProcess
                (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
                (fun _ ↦ ((n : NNReal) : ENNReal))) 1 μ :=
        martingaleUniformIntegrable_stoppedProcessConstTime
          (ℱ := ℱ)
          (μ := μ)
          (X := stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          hMart
          (n : NNReal)
      -- Proof comment: stopping again at the same deterministic horizon does not change the
      -- process, so the uniform integrability descends to the original deterministic stop.
      simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using hDet.2
    exact ⟨hMart, hUI⟩

/-- Helper for Exercise 25.4.3: the stopped harmonic increment is already strongly adapted in the
natural filtration of the Brownian path. -/
private theorem stageStoppedExtension_stronglyAdapted_ball
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcont : Continuous F) :
    StronglyAdapted
      (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
      (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x) := by
  let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  have hτstop : IsStoppingTime ℱW τ := by
    -- Proof comment: the stage exit clock is a stopping time in the natural filtration of the
    -- Brownian path.
    simpa [τ, ℱW] using
      stageExit_isStoppingTime_of_continuous_of_aeExitFinite
        (μ := μ) (W := W) (U := U) (x := x) hW hWcont hUo hExitFinite
  have hRawStrong :
      StronglyAdapted ℱW (fun t ω ↦ F (W t ω) - F x) := by
    intro t
    -- Proof comment: each deterministic-time slice is the measurable observable `F` applied to
    -- the current Brownian state, followed by subtraction of the deterministic base value.
    exact
      ((stateComposition_stronglyAdapted_natural_ball
          (hWsm := brownianVectorStartedAt_stronglyMeasurable hW)
          (hFmeas := hFcont.measurable)) t).sub stronglyMeasurable_const
  have hRawCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ F (W t ω) - F x := by
    intro ω
    -- Proof comment: continuity of the raw increment comes from continuity of the Brownian path
    -- and continuity of `F`.
    simpa using (hFcont.comp (hWcont ω)).sub continuous_const
  have hStoppedStrong :
      StronglyAdapted ℱW (stoppedProcess (fun t ω ↦ F (W t ω) - F x) τ) :=
    hRawStrong.stoppedProcess hRawCont hτstop
  -- Proof comment: rewriting the stopped raw increment yields the visible stopped extension.
  simpa [τ, ℱW, stageStoppedExtension_eq_stoppedRawIncrement_ball
    (W := W) (τ := τ) (F := F) (x := x)] using hStoppedStrong

/-- Helper for Exercise 25.4.3: the stopped harmonic increment inherits path continuity from the
continuous stopped Brownian path and continuity of `F`. -/
private theorem continuous_stageStoppedExtension_ball
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hFcont : Continuous F) :
    ∀ ω : Ω,
      Continuous
        (fun t : NNReal ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x) := by
  intro ω
  have hStoppedCont :
      Continuous fun t : NNReal ↦ stoppedProcess W (hittingAfter W Uᶜ 0) t ω :=
    continuous_stoppedVectorProcess_of_continuous
      (X := W) (σ := hittingAfter W Uᶜ 0) (ω := ω) (hWcont ω)
  -- Proof comment: continuity survives both composition with `F` and subtraction of the
  -- deterministic base value.
  simpa using (hFcont.comp hStoppedCont).sub continuous_const

/-- Helper for Exercise 25.4.3: deterministic stopping preserves strong adaptedness of the
visible stopped harmonic increment. -/
private theorem stageStoppedExtension_constStop_stronglyAdapted_ball
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcont : Continuous F) :
    ∀ T : NNReal,
      StronglyAdapted
        (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)
          (fun _ ↦ (T : ENNReal))) := by
  intro T
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  have hStrong :
      StronglyAdapted ℱW
        (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x) :=
    stageStoppedExtension_stronglyAdapted_ball
      (μ := μ) (W := W) (U := U) (x := x) hW hWcont hUo hExitFinite hFcont
  have hCont :
      ∀ ω : Ω,
        Continuous
          (fun t : NNReal ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x) :=
    continuous_stageStoppedExtension_ball
      (μ := μ) (W := W) (U := U) (x := x) hWcont hFcont
  -- Proof comment: deterministic stopping is just another stopping-time operation on the
  -- already strongly adapted continuous process.
  simpa [ℱW] using hStrong.stoppedProcess hCont (isStoppingTime_const ℱW T)

/-- Helper for Exercise 25.4.3: compactness of `closure U` bounds every deterministic stop of the
visible stopped harmonic increment. -/
private theorem stageStoppedExtension_constStop_boundedInTimeAe_ball
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U))
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcont : Continuous F) :
    ∀ T : NNReal,
      BoundedInTimeAe
        (μ : Measure Ω)
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)
          (fun _ ↦ (T : ENNReal))) := by
  intro T
  rcases existsAbsLeOnCompactClosure_continuous
      (U := U) (F := F) hUcpt hFcont with ⟨C, _hCnonneg, hC⟩
  refine ⟨C + |F x|, ?_⟩
  filter_upwards [hExitFinite, brownianVectorStart_ae_eq_const μ hW] with ω hωfin hωstart t
  have hStartMem : W 0 ω ∈ U := by
    simpa [hωstart] using hx
  have hmem :
      stoppedProcess W (hittingAfter W Uᶜ 0) (min t T) ω ∈ closure U :=
    stageStoppedProcess_mem_buffer
      (U := U) (V := closure U) (W := W) (ω := ω)
      hUo (hWcont ω) hStartMem (by intro z hz; exact hz) hωfin (min t T)
  have hvalue :
      |F (stoppedProcess W (hittingAfter W Uᶜ 0) (min t T) ω) - F x| ≤ C + |F x| := by
    calc
      |F (stoppedProcess W (hittingAfter W Uᶜ 0) (min t T) ω) - F x|
          ≤ |F (stoppedProcess W (hittingAfter W Uᶜ 0) (min t T) ω)| + |F x| := by
            simpa [sub_eq_add_neg, abs_neg] using
              (abs_add_le
                (F (stoppedProcess W (hittingAfter W Uᶜ 0) (min t T) ω))
                (-F x))
      _ ≤ C + |F x| := add_le_add (hC _ hmem) le_rfl
  -- Proof comment: stopping twice at deterministic time `T` only replaces `t` by `min t T`,
  -- and the compact-closure bound then controls the stopped value uniformly in time.
  simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using hvalue

/-- Helper for Exercise 25.4.3: `EqUpTo μ T X Y` records one measurable null set outside which
`X` and `Y` agree at every deterministic time in `[0,T]`. -/
private def EqUpTo {α : Type _} (μ : Measure Ω) (T : NNReal)
    (X Y : NNReal → Ω → α) : Prop :=
  ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
    ∀ ⦃t : NNReal⦄, t ≤ T → {ω | X t ω ≠ Y t ω} ⊆ N

/-- Helper for Exercise 25.4.3: equality up to a horizon composes transitively. -/
private theorem eqUpTo_trans
    {μ : Measure Ω} {α : Type _} {T : NNReal}
    {X Y Z : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) (hYZ : EqUpTo μ T Y Z) :
    EqUpTo μ T X Z := by
  rcases hXY with ⟨NXY, hNXY_meas, hNXY_null, hNXY_sub⟩
  rcases hYZ with ⟨NYZ, hNYZ_meas, hNYZ_null, hNYZ_sub⟩
  refine ⟨NXY ∪ NYZ, hNXY_meas.union hNYZ_meas, ?_, ?_⟩
  · have hUnionLe : μ (NXY ∪ NYZ) ≤ μ NXY + μ NYZ := measure_union_le NXY NYZ
    refine le_antisymm ?_ bot_le
    simpa [hNXY_null, hNYZ_null] using hUnionLe
  · intro t ht ω hω
    by_cases hXYω : X t ω ≠ Y t ω
    · exact Set.mem_union_left NYZ (hNXY_sub ht hXYω)
    · have hEqXY : X t ω = Y t ω := not_ne_iff.mp hXYω
      have hYZω : Y t ω ≠ Z t ω := by
        intro hEqYZ
        exact hω (hEqXY.trans hEqYZ)
      exact Set.mem_union_right NXY (hNYZ_sub ht hYZω)

/-- Helper for Exercise 25.4.3: equality up to a horizon is reflexive. -/
private theorem eqUpTo_rfl
    {μ : Measure Ω} {α : Type _} (T : NNReal) (X : NNReal → Ω → α) :
    EqUpTo μ T X X := by
  -- Proof comment: a process has no disagreement set with itself.
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro t ht ω hω
  simp at hω

/-- Helper for Exercise 25.4.3: equality up to a horizon is symmetric. -/
private theorem eqUpTo_sym
    {μ : Measure Ω} {α : Type _} {T : NNReal} {X Y : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) :
    EqUpTo μ T Y X := by
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro t ht ω hω
  exact hN_sub ht (by
    intro hEq
    exact hω hEq.symm)

/-- Helper for Exercise 25.4.3: one `EqUpTo` witness can be read as equality on `[0,T]` outside a
single measurable null set. -/
private theorem eqUpTo_forall_eq
    {μ : Measure Ω} {α : Type _} {T : NNReal} {X Y : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
      ∀ ⦃t : NNReal⦄, t ≤ T → ∀ ⦃ω : Ω⦄, ω ∉ N → X t ω = Y t ω := by
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro t ht ω hω
  by_contra hneq
  exact hω (hN_sub ht hneq)

/-- Helper for Exercise 25.4.3: finite-horizon equality is stable under addition. -/
private theorem eqUpTo_add
    {μ : Measure Ω} {T : NNReal}
    {X X' Y Y' : NNReal → Ω → ℝ}
    (hX : EqUpTo μ T X X') (hY : EqUpTo μ T Y Y') :
    EqUpTo μ T
      (fun t ω ↦ X t ω + Y t ω)
      (fun t ω ↦ X' t ω + Y' t ω) := by
  rcases hX with ⟨NX, hNX_meas, hNX_null, hNX_sub⟩
  rcases hY with ⟨NY, hNY_meas, hNY_null, hNY_sub⟩
  refine ⟨NX ∪ NY, hNX_meas.union hNY_meas, ?_, ?_⟩
  · have hUnionLe : μ (NX ∪ NY) ≤ μ NX + μ NY := measure_union_le NX NY
    refine le_antisymm ?_ bot_le
    simpa [hNX_null, hNY_null] using hUnionLe
  · intro t ht ω hω
    by_cases hXω : X t ω ≠ X' t ω
    · exact Set.mem_union_left NY (hNX_sub ht hXω)
    · have hEqX : X t ω = X' t ω := not_ne_iff.mp hXω
      have hYω : Y t ω ≠ Y' t ω := by
        intro hEqY
        apply hω
        simpa [hEqX, hEqY]
      exact Set.mem_union_right NX (hNY_sub ht hYω)

/-- Helper for Exercise 25.4.3: one all-times almost-sure identity gives equality up to every
deterministic horizon. -/
private theorem eqUpTo_of_ae_allTimes
    {μ : Measure Ω} {T : NNReal} {X Y : NNReal → Ω → ℝ}
    (hXY : ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = Y t ω) :
    EqUpTo μ T X Y := by
  classical
  let N : Set Ω := {ω | ¬ ∀ t : NNReal, X t ω = Y t ω}
  refine ⟨toMeasurable μ N, measurableSet_toMeasurable _ _, ?_, ?_⟩
  · -- Proof comment: the measurable hull of the exceptional set is still null because the
    -- equality already holds almost surely at every deterministic time.
    rw [measure_toMeasurable]
    simpa [N, ae_iff] using hXY
  · intro t ht ω hω
    exact subset_toMeasurable μ N (by
      change ¬ ∀ s : NNReal, X s ω = Y s ω
      intro hAll
      exact hω (hAll t))

/-- Helper for Exercise 25.4.3: a genuine continuous local martingale is automatically a witness
up to any deterministic horizon. -/
private def IsContinuousLocalMartingaleUpToLocal
    (ℱ : Filtration NNReal ‹MeasurableSpace Ω›) (μ : Measure Ω)
    (T : NNReal) (N : NNReal → Ω → ℝ) : Prop :=
  ∃ N' : NNReal → Ω → ℝ,
    IsContinuousLocalMartingale ℱ μ N' ∧ EqUpTo μ T N N'

/-- Helper for Exercise 25.4.3: a genuine continuous local martingale is automatically a witness
up to any deterministic horizon. -/
private theorem isContinuousLocalMartingaleUpToLocal_of_isContinuousLocalMartingale
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {T : NNReal} {N : NNReal → Ω → ℝ}
    (hN : IsContinuousLocalMartingale ℱ μ N) :
    IsContinuousLocalMartingaleUpToLocal ℱ μ T N := by
  -- Proof comment: keep the same process as the genuine witness and record reflexive equality on
  -- the horizon.
  exact ⟨N, hN, eqUpTo_rfl (μ := μ) T N⟩

/-- Helper for Exercise 25.4.3: finite sums preserve equality up to a deterministic horizon. -/
private theorem eqUpTo_finsetSum
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {μ : Measure Ω} {T : NNReal}
    {X Y : ι → NNReal → Ω → ℝ}
    (hXY : ∀ i ∈ s, EqUpTo μ T (X i) (Y i)) :
    EqUpTo μ T
      (fun t ω ↦ Finset.sum s (fun i ↦ X i t ω))
      (fun t ω ↦ Finset.sum s (fun i ↦ Y i t ω)) := by
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty sums are literally the same zero process.
      simpa using eqUpTo_rfl (μ := μ) T (fun _ _ ↦ (0 : ℝ))
  | @insert a s ha ih =>
      have hsXY : ∀ i ∈ s, EqUpTo μ T (X i) (Y i) := by
        intro i hi
        exact hXY i (by simp [hi])
      -- Proof comment: combine the head witness with the recursive tail witness and rewrite both
      -- finite sums into head-plus-tail normal form.
      simpa [Finset.sum_insert, ha] using eqUpTo_add (hXY a (by simp)) (ih hsXY)

/-- Helper for Exercise 25.4.3: once a finite sum already has a genuine continuous-local-martingale
owner and an `EqUpTo` bridge from the visible sum, it yields the corresponding
`...UpToLocal` witness on the fixed horizon. -/
private theorem finsetSum_isContinuousLocalMartingaleUpToLocal
    (s : Finset (Fin d)) {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {T : NNReal} {N : Fin d → NNReal → Ω → ℝ}
    {Nsum : NNReal → Ω → ℝ}
    (hEq :
      EqUpTo μ T
        (fun t ω ↦ Finset.sum s (fun i ↦ N i t ω))
        Nsum)
    (hNsum : IsContinuousLocalMartingale ℱ μ Nsum) :
    IsContinuousLocalMartingaleUpToLocal ℱ μ T
      (fun t ω ↦ Finset.sum s (fun i ↦ N i t ω)) := by
  -- Proof comment: this helper is only the final packaging step from an explicit continuous local
  -- martingale owner for the finite sum to the fixed-horizon `...UpToLocal` relation.
  exact ⟨Nsum, hNsum, hEq⟩

/-- Helper for Exercise 25.4.3: deterministic stopping turns an `EqUpTo` witness on `[0,T]` into
all-times almost-sure equality of the two deterministic stops. -/
private theorem ae_eq_stoppedProcess_const_of_eqUpTo
    {μ : Measure Ω} {T : NNReal} {X Y : NNReal → Ω → ℝ}
    (hXY : EqUpTo μ T X Y) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      stoppedProcess X (fun _ ↦ (T : ENNReal)) t ω =
        stoppedProcess Y (fun _ ↦ (T : ENNReal)) t ω := by
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hXY with
    ⟨N, hN_meas, hN_null, hN_eq⟩
  have hNae : ∀ᵐ ω ∂μ, ω ∉ N := compl_mem_ae_iff.mpr hN_null
  filter_upwards [hNae] with ω hω t
  -- Proof comment: both deterministic stops are evaluated at the clipped time `min t T`, which
  -- stays inside the horizon controlled by the `EqUpTo` witness.
  simpa [stoppedProcessConstTime_eq_min] using hN_eq (min_le_right t T) hω

/-- Helper for Exercise 25.4.3: a deterministic bound transfers across an all-times almost-sure
equality of processes. -/
private theorem boundedInTimeAe_of_ae_allTimes_eq
    {μ : Measure Ω} {X Y : NNReal → Ω → ℝ}
    (hX : BoundedInTimeAe μ X)
    (hEq : ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = Y t ω) :
    BoundedInTimeAe μ Y := by
  rcases hX with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  filter_upwards [hC, hEq] with ω hωBound hωEq t
  simpa [hωEq t] using hωBound t

/-- Helper for Exercise 25.4.3: deterministic stopping preserves the local-martingale property
for continuous paths on the Brownian path space used in this file. -/
private theorem isLocalMartingale_stoppedProcess_constTime_ball
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ}
    (hM : IsLocalMartingale ℱ μ M)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    (T : NNReal) :
    IsLocalMartingale ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal))) := by
  rcases (isLocalMartingale_iff ℱ μ M).1 hM with ⟨hM_adapted, τSeq, hτSeq⟩
  refine
    (isLocalMartingale_iff ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal)))).2 ⟨?_, τSeq, ?_⟩
  · -- Proof comment: deterministic stopping preserves adaptedness once the source process has
    -- continuous sample paths.
    exact
      (hM_adapted.stronglyAdapted.stoppedProcess hM_cont (isStoppingTime_const ℱ T)).adapted
  · rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨hStopping, hLim, hStopped⟩
    refine
      (isLocalizingSequence_iff ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal))) τSeq).2
        ⟨hStopping, hLim, ?_⟩
    intro n
    obtain ⟨hMart, hUI⟩ := hStopped n
    have hDoubleStop :
        stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
          stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) := by
      have hLeft :
          stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
            stoppedProcess M
              (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))) := by
        simpa [min_comm] using
          (stoppedProcess_stoppedProcess' :
            stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
              stoppedProcess M
                (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))))
      have hRight :
          stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) =
            stoppedProcess M
              (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))) := by
        simpa [min_comm] using
          (stoppedProcess_stoppedProcess' :
            stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) =
              stoppedProcess M
                (fun ω ↦ min (((fun _ ↦ (T : ENNReal)) ω)) ((τSeq n) ω)))
      exact hLeft.trans hRight.symm
    have hStoppedConst :
        Martingale
            (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)))
            ℱ
            μ ∧
          UniformIntegrable
            (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)))
            1
            μ :=
      martingaleUniformIntegrable_stoppedProcessConstTime
        (ℱ := ℱ)
        (μ := μ)
        (X := stoppedProcess M (τSeq n))
        hMart
        T
    -- Proof comment: after swapping the two stops, each doubly stopped slice is just a
    -- deterministic stop of the martingale owner already supplied by the localizing sequence.
    exact hDoubleStop ▸ hStoppedConst

/-- Helper for Exercise 25.4.3: a bounded deterministic stop is a martingale once it agrees on
`[0,T]` with a deterministic-horizon continuous-local-martingale-up-to witness. -/
private theorem martingaleOfConstStoppedEqUpToLocalMartingaleUpTo
    {μ : ProbabilityMeasure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {X N : NNReal → Ω → ℝ} {T : NNReal}
    (hXStrong :
      StronglyAdapted ℱ (stoppedProcess X (fun _ ↦ (T : ENNReal))))
    (hXBounded :
      BoundedInTimeAe (μ : Measure Ω)
        (stoppedProcess X (fun _ ↦ (T : ENNReal))))
    (hXN : EqUpTo (μ : Measure Ω) T X N)
    (hNUpTo : IsContinuousLocalMartingaleUpToLocal ℱ (μ : Measure Ω) T N) :
    Martingale (stoppedProcess X (fun _ ↦ (T : ENNReal))) ℱ (μ : Measure Ω) := by
  rcases hNUpTo with ⟨N', hN', hNN'⟩
  have hOwnerEq :
      EqUpTo (μ : Measure Ω) T N' X :=
    eqUpTo_trans (eqUpTo_sym hNN') (eqUpTo_sym hXN)
  have hOwnerStopEq :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess N' (fun _ ↦ (T : ENNReal)) t ω =
          stoppedProcess X (fun _ ↦ (T : ENNReal)) t ω :=
    ae_eq_stoppedProcess_const_of_eqUpTo hOwnerEq
  have hOwnerStoppedLocal :
      IsLocalMartingale ℱ (μ : Measure Ω)
        (stoppedProcess N' (fun _ ↦ (T : ENNReal))) :=
    isLocalMartingale_stoppedProcess_constTime_ball
      hN'.local_martingale
      hN'.continuous
      T
  have hOwnerStoppedBounded :
      BoundedInTimeAe (μ : Measure Ω)
        (stoppedProcess N' (fun _ ↦ (T : ENNReal))) := by
    have hOwnerStopEq_symm :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          stoppedProcess X (fun _ ↦ (T : ENNReal)) t ω =
            stoppedProcess N' (fun _ ↦ (T : ENNReal)) t ω := by
      filter_upwards [hOwnerStopEq] with ω hω t
      exact (hω t).symm
    exact
      boundedInTimeAe_of_ae_allTimes_eq
        hXBounded
        hOwnerStopEq_symm
  have hOwnerStoppedMart :
      Martingale (stoppedProcess N' (fun _ ↦ (T : ENNReal))) ℱ (μ : Measure Ω) :=
    martingale_of_bounded_local_martingale hOwnerStoppedLocal hOwnerStoppedBounded
  have hTargetStopEq :
      ∀ t : NNReal,
        stoppedProcess N' (fun _ ↦ (T : ENNReal)) t =ᵐ[(μ : Measure Ω)]
          stoppedProcess X (fun _ ↦ (T : ENNReal)) t := by
    intro t
    filter_upwards [hOwnerStopEq] with ω hω
    exact hω t
  -- Proof comment: the owner stop is already a martingale, and the visible deterministic stop
  -- inherits that property through timewise almost-sure equality plus its packaged strong
  -- adaptedness.
  exact martingale_congr_ae hOwnerStoppedMart hXStrong hTargetStopEq

/-- Helper for Exercise 25.4.3: after recentering the Brownian path at `x` and patching only the
time-zero value, adding `x` back recovers the original path at every deterministic time outside
one null set. -/
private theorem stageTranslatedPatchedBrownian_ae_allTimes_eq_original_ball
    (μ : ProbabilityMeasure Ω)
    {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, x + B t ω = W t ω := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x :=
    brownianVectorStart_ae_eq_const μ hW
  filter_upwards [hStartAe] with ω hω t
  by_cases ht : t = 0
  · subst ht
    -- Proof comment: at time `0`, the patched translation is exactly `0`, so adding back `x`
    -- returns the deterministic Brownian start.
    simpa [B, hω]
  · -- Proof comment: away from time `0`, the recentering subtracts `x` and adding `x` back
    -- cancels that translation pointwise.
    simpa [B, ht, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 25.4.3: if `x + B t ω = W t ω` holds at every deterministic time, then the
same translation identity persists after stopping both paths at the same clock. -/
private theorem translatedPatchedBrownian_stopped_eq_original_ball
    {W B : VectorProcess} {τ : Ω → ENNReal} {x : State} {ω : Ω}
    (hEq : ∀ t : NNReal, x + B t ω = W t ω)
    (t : NNReal) :
    x + stoppedProcess B τ t ω = stoppedProcess W τ t ω := by
  by_cases hτ : τ ω = ⊤
  · -- Proof comment: if the stop never occurs, both stopped paths are the raw paths at time `t`.
    simpa [stoppedProcess, hτ] using hEq t
  · let s : NNReal := (τ ω).untopA
    have hs : ((s : NNReal) : ENNReal) = τ ω := by
      dsimp [s]
      rw [WithTop.untopA_eq_untop hτ]
      exact WithTop.coe_untop _ _
    by_cases ht : s ≤ t
    · have hτle : τ ω ≤ (t : ENNReal) := by
        rw [← hs]
        exact_mod_cast ht
      have hBstop :
          stoppedProcess B τ t ω = B s ω := by
        simpa [s] using
          (stoppedProcess_eq_of_ge (u := B) (τ := τ) (ω := ω) (i := t) hτle)
      have hWstop :
          stoppedProcess W τ t ω = W s ω := by
        simpa [s] using
          (stoppedProcess_eq_of_ge (u := W) (τ := τ) (ω := ω) (i := t) hτle)
      -- Proof comment: after the stopping time, both processes are frozen at the same clipped
      -- time `s`.
      simpa [hBstop, hWstop] using hEq s
    · have hτgt : t < s := lt_of_not_ge ht
      have htle : (t : ENNReal) ≤ τ ω := by
        rw [← hs]
        exact le_of_lt (by exact_mod_cast hτgt)
      have hBstop :
          stoppedProcess B τ t ω = B t ω := by
        exact stoppedProcess_eq_of_le (u := B) (τ := τ) (ω := ω) (i := t) htle
      have hWstop :
          stoppedProcess W τ t ω = W t ω := by
        exact stoppedProcess_eq_of_le (u := W) (τ := τ) (ω := ω) (i := t) htle
      -- Proof comment: before the stopping time, both stopped paths still agree with the raw
      -- processes at time `t`.
      simpa [hBstop, hWstop] using hEq t

/-- Helper for Exercise 25.4.3: harmonicity on a buffer implies pointwise vanishing of the
Laplacian on that buffer. -/
private theorem laplacian_eq_zero_on_buffer_ball
    {F : State → ℝ} {V : Set State}
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    {z : State} (hz : z ∈ V) :
    Laplacian.laplacian F z = 0 := by
  -- Proof comment: the harmonic-neighborhood owner gives an eventual identity `ΔF = 0` near `z`,
  -- and evaluating that neighborhood identity at `z` closes the pointwise Laplacian goal.
  exact (hFharm z hz).2.self_of_nhds

/-- Helper for Exercise 25.4.3: every deterministic-horizon stop of the Brownian stage stays in
the harmonic buffer, so the Laplacian of the extension vanishes there almost surely. -/
private theorem stageStoppedLaplacian_eq_zero_ball
    {μ : ProbabilityMeasure Ω}
    {W : VectorProcess} {U V : Set State} {F : State → ℝ} {x : State}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hUV : closure U ⊆ V)
    (hExitFinite : ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      Laplacian.laplacian F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) = 0 := by
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x :=
    brownianVectorStart_ae_eq_const μ hW
  filter_upwards [hExitFinite, hStartAe] with ω hωfin hωstart t
  have hStart : W 0 ω ∈ U := by
    simpa [hωstart] using hx
  have hmemV :
      stoppedProcess W (hittingAfter W Uᶜ 0) t ω ∈ V :=
    stageStoppedProcess_mem_buffer
      (U := U) (V := V) (W := W) (ω := ω)
      hUo
      (hWcont ω)
      hStart
      hUV
      hωfin
      t
  -- Proof comment: once the deterministic stop is known to stay in `V`, harmonicity kills the
  -- Laplacian there pointwise.
  exact laplacian_eq_zero_on_buffer_ball hFharm hmemV

/-- Helper for Exercise 25.4.3: after recentering and patching the Brownian path, the stopped
Laplacian-zero identity transports from the original path to the shifted stopped spelling. -/
private theorem shiftedStoppedExtension_laplacian_eq_zero_ball
    {μ : ProbabilityMeasure Ω}
    {W : VectorProcess} {U V : Set State} {F : State → ℝ} {x : State}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hUV : closure U ⊆ V)
    (hExitFinite : ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      Laplacian.laplacian F (x + stoppedProcess B (hittingAfter W Uᶜ 0) t ω) = 0 := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  have hTranslate :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, x + B t ω = W t ω :=
    stageTranslatedPatchedBrownian_ae_allTimes_eq_original_ball μ hW
  have hStoppedLap :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        Laplacian.laplacian F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) = 0 :=
    stageStoppedLaplacian_eq_zero_ball
      (μ := μ) (W := W) (U := U) (V := V) (F := F) (x := x)
      hx hW hWcont hUo hUV hExitFinite hFharm
  filter_upwards [hTranslate, hStoppedLap] with ω hωTranslate hωLap t
  have hStoppedEq :
      x + stoppedProcess B (hittingAfter W Uᶜ 0) t ω =
        stoppedProcess W (hittingAfter W Uᶜ 0) t ω :=
    translatedPatchedBrownian_stopped_eq_original_ball
      (W := W) (B := B) (τ := hittingAfter W Uᶜ 0) (x := x) (ω := ω)
      hωTranslate
      t
  -- Proof comment: rewrite the shifted stopped point back to the original stopped Brownian path,
  -- where the vanishing-Laplacian statement is already available.
  rw [hStoppedEq]
  exact hωLap t

/-- Helper for Exercise 25.4.3: evaluating `F` on the translated stopped path agrees almost surely
at every deterministic time with evaluating `F` on the original stopped Brownian path. -/
private theorem stageStoppedTranslatedSurface_eq_visibleIncrement_ball
    {μ : ProbabilityMeasure Ω}
    {W : VectorProcess} {U : Set State} {F : State → ℝ} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      F (x + stoppedProcess B (hittingAfter W Uᶜ 0) t ω) - F x =
        F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  have hTranslate :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, x + B t ω = W t ω :=
    stageTranslatedPatchedBrownian_ae_allTimes_eq_original_ball μ hW
  filter_upwards [hTranslate] with ω hω t
  -- Proof comment: rewrite the shifted stopped path back to the original Brownian stop before
  -- evaluating `F`.
  rw [translatedPatchedBrownian_stopped_eq_original_ball
    (W := W) (B := B) (τ := hittingAfter W Uᶜ 0) (x := x) (ω := ω) hω t]

/-- Helper for Exercise 25.4.3: on a fixed deterministic horizon, the visible stopped increment
agrees with the translated stopped surface whose drift term is controlled by harmonicity. -/
private theorem visibleStoppedIncrement_eqUpTo_shiftedTranslatedSurface_ball
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U V : Set State} {x : State}
    {F : State → ℝ}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hUV : closure U ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    (T : NNReal) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    let Y : NNReal → Ω → ℝ := fun t ω ↦
      stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun s ω ↦ Laplacian.laplacian F (x + B s ω))
              τ
              u.toNNReal
              ω
    EqUpTo
      (μ : Measure Ω)
      T
      (fun t ω ↦ F (stoppedProcess W τ t ω) - F x)
      Y := by
  intro B τ Y
  have hSurface :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        Y t ω = F (stoppedProcess W τ t ω) - F x := by
    have hShiftedLap :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          Laplacian.laplacian F (x + stoppedProcess B τ t ω) = 0 := by
      -- Proof comment: harmonicity kills the Laplacian along the translated stopped path.
      simpa [B, τ] using
        shiftedStoppedExtension_laplacian_eq_zero_ball
          (μ := μ) (W := W) (U := U) (V := V) (F := F) (x := x)
          hx hW hWcont hUo hUV hExitFinite hFharm
    have hCutoffDriftZero :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) *
              ProbabilityTheory.processBeforeStoppingTime
                (fun s ω ↦ Laplacian.laplacian F (x + B s ω))
                τ
                u.toNNReal
                ω = 0 := by
      filter_upwards [hShiftedLap] with ω hω t
      have hIntegrandZero :
          (fun s : ℝ ↦
            ((1 : ℝ) / 2) *
              ProbabilityTheory.processBeforeStoppingTime
                (fun u ω ↦ Laplacian.laplacian F (x + B u ω))
                τ
                s.toNNReal
                ω) = fun _ : ℝ ↦ (0 : ℝ) := by
        funext s
        by_cases hs : (s.toNNReal : ENNReal) ≤ τ ω
        · have hStopEq : stoppedProcess B τ s.toNNReal ω = B s.toNNReal ω := by
            exact stoppedProcess_eq_of_le (u := B) (τ := τ) (ω := ω) (i := s.toNNReal) hs
          have hLapAt : Laplacian.laplacian F (x + B s.toNNReal ω) = 0 := by
            simpa [hStopEq] using hω s.toNNReal
          rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos hs]
          simp [hLapAt]
        · rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg hs]
          simp
      -- Proof comment: the cutoff drift vanishes because the integrand is zero before `τ` by
      -- harmonicity and is forced to zero after `τ` by the cutoff itself.
      rw [hIntegrandZero]
      simp
    have hTranslatedVisible :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω =
            F (stoppedProcess W τ t ω) - F x := by
      filter_upwards
          [stageStoppedTranslatedSurface_eq_visibleIncrement_ball
            (μ := μ) (W := W) (U := U) (F := F) (x := x) hW] with ω hω t
      have hStopSurface :
          stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω =
            F (x + stoppedProcess B τ t ω) - F x := by
        -- Proof comment: rewrite the translated stopped surface to the explicit stopped-path
        -- spelling before comparing it with the visible stopped increment.
        simpa using
          congrArg
            (fun Z : NNReal → Ω → ℝ ↦ Z t ω)
            (stageStoppedExtension_eq_stoppedRawIncrement_ball
              (W := B) (τ := τ) (F := fun z : State ↦ F (x + z)) (x := (0 : State)))
      exact hStopSurface.trans (hω t)
    filter_upwards [hTranslatedVisible, hCutoffDriftZero] with ω hωVisible hωDrift t
    calc
      Y t ω =
          stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) *
                ProbabilityTheory.processBeforeStoppingTime
                  (fun s ω ↦ Laplacian.laplacian F (x + B s ω))
                  τ
                  u.toNNReal
                  ω := by
            rfl
      _ = stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω := by
            rw [hωDrift t]
            ring
      _ = F (stoppedProcess W τ t ω) - F x := hωVisible t
  have hSurfaceSymm :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        F (stoppedProcess W τ t ω) - F x = Y t ω := by
    filter_upwards [hSurface] with ω hω t
    exact (hω t).symm
  -- Proof comment: once the translated stopped surface is rewritten back to the visible stopped
  -- increment and the harmonic drift is shown to vanish, the desired horizon-wise equality is an
  -- immediate `EqUpTo` witness.
  exact eqUpTo_of_ae_allTimes hSurfaceSymm

/-- Helper for Exercise 25.4.3: on a fixed deterministic horizon, the translated stopped surface
admits a canonical continuous-local-martingale-up-to owner assembled from the coordinate family. -/
private theorem shiftedTranslatedSurface_constStop_eqUpToCanonicalOwner_ball
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F) :
    ∀ T : NNReal,
      let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
      let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
      let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
        Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
      let Y : NNReal → Ω → ℝ := fun t ω ↦
        stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) *
              ProbabilityTheory.processBeforeStoppingTime
                (fun s ω ↦ Laplacian.laplacian F (x + B s ω))
                τ
                u.toNNReal
                ω
      ∃ Nsum : NNReal → Ω → ℝ,
          EqUpTo (μ : Measure Ω) T Y Nsum ∧
          IsContinuousLocalMartingaleUpToLocal ℱW (μ : Measure Ω) T Nsum := by
  intro T B τ ℱW Y
  -- Route correction: this should remain only the coordinate-owner assembly step.
  -- TODO: port the coordinate family owner theorem from the fixed-horizon Itô expansion and then
  -- sum it with `finsetSum_isContinuousLocalMartingaleUpToLocal`.
  sorry

/-- Helper for Exercise 25.4.3: the only remaining stochastic-core blocker is a deterministic
horizon owner that matches the visible stopped increment on `[0,T]`. -/
private theorem stageStoppedExtension_constStop_eqUpToCanonicalOwner_ball
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U V : Set State} {x : State}
    {F : State → ℝ}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U))
    (hUV : closure U ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ T : NNReal,
      ∃ Nsum : NNReal → Ω → ℝ,
        EqUpTo
          (μ : Measure Ω)
          T
          (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)
          Nsum ∧
        IsContinuousLocalMartingaleUpToLocal
          (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
          (μ : Measure Ω)
          T
          Nsum := by
  intro T
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let Y : NNReal → Ω → ℝ := fun t ω ↦
    stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
      ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        ((1 : ℝ) / 2) *
          ProbabilityTheory.processBeforeStoppingTime
            (fun s ω ↦ Laplacian.laplacian F (x + B s ω))
            τ
            u.toNNReal
            ω
  have hVisible :
      EqUpTo
        (μ : Measure Ω)
        T
        (fun t ω ↦ F (stoppedProcess W τ t ω) - F x)
        Y := by
    -- Proof comment: the visible stopped increment is now separated from the translated owner by
    -- the dedicated visible-to-translated interface theorem.
    simpa [B, τ, Y] using
      visibleStoppedIncrement_eqUpTo_shiftedTranslatedSurface_ball
        (μ := μ) (W := W) (U := U) (V := V) (x := x) (F := F)
        hx hW hWcont hUo hUV hExitFinite hFharm T
  rcases
      shiftedTranslatedSurface_constStop_eqUpToCanonicalOwner_ball
        (μ := μ) (W := W) (U := U) (x := x) (F := F)
        hW hWcont hUo hExitFinite hFcontDiff T with
    ⟨Nsum, hYEq, hNsum⟩
  refine ⟨Nsum, eqUpTo_trans hVisible hYEq, ?_⟩
  -- Proof comment: after the visible-to-translated comparison is isolated, the required
  -- deterministic-horizon owner is exactly the translated-surface owner supplied just above.
  simpa [B, τ, ℱW, Y] using hNsum

/-- Helper for Exercise 25.4.3: the only remaining stochastic-core input is the local-martingale
owner for the stopped harmonic extension on one precompact stage. -/
private theorem stageStoppedExtension_constStop_martingaleFrontier_ball
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U V : Set State} {x : State}
    {F : State → ℝ}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U))
    (hUV : closure U ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ T : NNReal,
      Martingale
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)
          (fun _ ↦ (T : ENNReal)))
        (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
        (μ : Measure Ω) := by
  intro T
  have hXStrong :
      StronglyAdapted
        (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)
          (fun _ ↦ (T : ENNReal))) :=
    stageStoppedExtension_constStop_stronglyAdapted_ball
      (μ := μ) (W := W) (U := U) (x := x) hW hWcont hUo hExitFinite hFcontDiff.continuous T
  have hXBounded :
      BoundedInTimeAe
        (μ : Measure Ω)
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)
          (fun _ ↦ (T : ENNReal))) :=
    stageStoppedExtension_constStop_boundedInTimeAe_ball
      (μ := μ) (W := W) (U := U) (x := x)
      hx hW hWcont hUo hUcpt hExitFinite hFcontDiff.continuous T
  rcases
      stageStoppedExtension_constStop_eqUpToCanonicalOwner_ball
        (μ := μ) (W := W) (U := U) (V := V) (x := x) (F := F)
        hx hW hWcont hUo hUcpt hUV hExitFinite hFcontDiff hFharm T with
    ⟨Nsum, hEq, hUpTo⟩
  -- Proof comment: the deterministic stop is now exactly the generic bounded `EqUpTo` transport
  -- situation, and all process-specific adaptedness and boundedness work has already been
  -- isolated above.
  exact
    martingaleOfConstStoppedEqUpToLocalMartingaleUpTo
      (μ := μ)
      (ℱ := Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
      (X := fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)
      (N := Nsum)
      (T := T)
      hXStrong
      hXBounded
      hEq
      hUpTo

/-- Helper for Exercise 25.4.3: the only remaining stochastic-core input is the local-martingale
owner for the stopped harmonic extension on one precompact stage. -/
private theorem stageStoppedExtension_increment_isLocalMartingale_ball
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U V : Set State} {x : State}
    {F : State → ℝ}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U))
    (hUV : closure U ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    IsLocalMartingale
      (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
      (μ : Measure Ω)
      (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x) := by
  let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let Y : NNReal → Ω → ℝ := fun t ω ↦ F (stoppedProcess W τ t ω) - F x
  have hY_adapted : Adapted ℱW Y := by
    have hYStrong :
        StronglyAdapted ℱW Y := by
      -- Proof comment: the visible stopped increment is already strongly adapted by the dedicated
      -- stopped-extension helper.
      simpa [Y, τ, ℱW] using
        stageStoppedExtension_stronglyAdapted_ball
          (μ := μ) (W := W) (U := U) (x := x)
          hW hWcont hUo hExitFinite hFcontDiff.continuous
    exact hYStrong.adapted
  have hY_cont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω := by
    -- Proof comment: the dedicated continuity helper already isolates the stopped-path
    -- continuity argument.
    simpa [Y, τ] using
      continuous_stageStoppedExtension_ball
        (μ := μ) (W := W) (U := U) (x := x) hWcont hFcontDiff.continuous
  have hStopped :
      ∀ T : NNReal, Martingale (stoppedProcess Y (fun _ ↦ (T : ENNReal))) ℱW (μ : Measure Ω) := by
    intro T
    -- Proof comment: the only remaining stochastic work is exactly the deterministic-horizon
    -- martingale frontier isolated just above.
    simpa [Y, τ, ℱW] using
      stageStoppedExtension_constStop_martingaleFrontier_ball
        (μ := μ) (W := W) (U := U) (V := V) (x := x) (F := F)
        hx hW hWcont hUo hUcpt hUV hExitFinite hFcontDiff hFharm T
  -- Proof comment: once every deterministic stop is a martingale, the continuous-process local
  -- martingale criterion closes the stage increment owner.
  exact
    (isContinuousLocalMartingale_of_constStoppedMartingale_ball
      (μ := (μ : Measure Ω)) (ℱ := ℱW) (Y := Y)
      hY_adapted hY_cont hStopped).local_martingale

/-- Helper for Exercise 25.4.3: on one precompact stage, optional stopping should already give
the deterministic-horizon expectation identity for `u`. -/
private theorem stageStoppedExtension_expectation_eq_atNat_ball
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U V : Set State} {x : State}
    {u F : State → ℝ}
    (hx : x ∈ U) (hUo : IsOpen U) (hUcpt : IsCompact (closure U))
    (hUV : closure U ⊆ V)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hStart : ∀ ω : Ω, W 0 ω = x)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hEq : Set.EqOn F u (closure U))
    (hClosureBound :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closure U, |u z| ≤ C)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ n : ℕ,
      u x = ∫ ω, u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) ∂(μ : Measure Ω) := by
  let M : NNReal → Ω → ℝ := fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω)
  have hxClosure : x ∈ closure U := subset_closure hx
  have hFx : F x = u x := hEq hxClosure
  have hLocal :
      IsLocalMartingale
        (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
        (μ : Measure Ω)
        (fun t ω ↦ M t ω - F x) := by
    -- Proof comment: the stochastic core is now isolated in the dedicated stopped-increment
    -- local-martingale theorem.
    simpa [M] using
      stageStoppedExtension_increment_isLocalMartingale_ball
        (μ := μ) (W := W) (U := U) (V := V) (x := x) (F := F)
        hx hW hWcont hUo hUcpt hUV hExitFinite hFcontDiff hFharm
  have hInitialAe : M 0 =ᵐ[(μ : Measure Ω)] fun _ : Ω ↦ F x := by
    filter_upwards [Filter.Eventually.of_forall hStart] with ω hωstart
    have hStop0 :
        stoppedProcess W (hittingAfter W Uᶜ 0) 0 ω = W 0 ω :=
      stoppedProcess_eq_of_le
        (u := W) (τ := hittingAfter W Uᶜ 0) (ω := ω) (i := 0) bot_le
    -- Proof comment: at time `0`, the stopped path is still the Brownian start.
    simp [M, hStop0, hωstart]
  rcases hClosureBound with ⟨C, _hCnonneg, hC⟩
  have hBounded :
      BoundedInTimeAe (μ : Measure Ω) (fun t ω ↦ M t ω - F x) := by
    refine ⟨C + |F x|, ?_⟩
    filter_upwards [hExitFinite] with ω hωfin t
    have hStartMem : W 0 ω ∈ U := by
      simpa [hStart ω] using hx
    have hmem :
        stoppedProcess W (hittingAfter W Uᶜ 0) t ω ∈ closure U :=
      stageStoppedProcess_mem_buffer
        (U := U) (V := closure U) (W := W) (ω := ω)
        hUo (hWcont ω) hStartMem (by intro z hz; exact hz) hωfin t
    have hEqStage :
        F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) =
          u (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) :=
      hEq hmem
    -- Proof comment: rewrite the stopped extension back to `u` on `closure U`, then use the
    -- closure bound together with the deterministic offset `F x`.
    calc
      |M t ω - F x|
          = |u (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x| := by
              simp [M, hEqStage]
      _ ≤ |u (stoppedProcess W (hittingAfter W Uᶜ 0) t ω)| + |F x| := by
            simpa [sub_eq_add_neg, abs_neg] using
              (abs_add_le
                (u (stoppedProcess W (hittingAfter W Uᶜ 0) t ω))
                (-F x))
      _ ≤ C + |F x| := add_le_add (hC _ hmem) le_rfl
  intro n
  have hStageEqF :
      ∫ ω, M n ω ∂(μ : Measure Ω) =
        ∫ ω, u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) ∂(μ : Measure Ω) := by
    simpa [M] using
      integral_stageStopped_eq_of_eqOn_closure
        (μ := μ) (W := W) (U := U) (x := x)
        (u := u) (F := F) hx hUo
        (Filter.Eventually.of_forall hWcont)
        (Filter.Eventually.of_forall hStart)
        hExitFinite hEq n
  have hExpectationF :
      F x = ∫ ω, M n ω ∂(μ : Measure Ω) :=
    expectation_eq_of_bounded_localMartingale_increment
      (μ := μ)
      (ℱ := Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
      (M := M) (c := F x) hLocal hBounded hInitialAe n
  -- Proof comment: prove the expectation identity for the extension `F`, then rewrite back to
  -- `u` because every deterministic stopped value stays on `closure U`.
  calc
    u x = F x := hFx.symm
    _ = ∫ ω, M n ω ∂(μ : Measure Ω) := hExpectationF
    _ = ∫ ω, u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) ∂(μ : Measure Ω) := hStageEqF

/-- Helper for Exercise 25.4.3: along the inner exhaustion of the open ball, the diagonal stopped
values converge almost surely to the global stopped value of the continuous modification. -/
private theorem tendsto_innerStageStopped_to_globalStoppedValue_ball
    {μ : ProbabilityMeasure Ω}
    {Wc : VectorProcess} {x : State}
    {U : ℕ → Set State} (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ)
    {u : State → ℝ}
    (hx : x ∈ Metric.ball (0 : State) r)
    (hUo : ∀ n, IsOpen (U n))
    (hUx : ∀ n, x ∈ U n)
    (hUcl : ∀ n, closure (U n) ⊆ Metric.ball (0 : State) r)
    (hUmono : Monotone U)
    (hUunion : (⋃ n, U n) = Metric.ball (0 : State) r)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hWcStart : ∀ ω : Ω, Wc 0 ω = x)
    (hExitFiniteWc :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0 ω < ⊤)
    (hu :
      SolvesDirichletProblem
        (Metric.ball (0 : State) r)
        (openBallFrontierBoundaryDatum r hr g)
        u) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      Tendsto
        (fun n : ℕ ↦
          u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω))
        atTop
        (𝓝
          (u
            (stoppedValue Wc
              (hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0) ω))) := by
  filter_upwards [hExitFiniteWc] with ω hτfin
  let τ : ENNReal := hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0 ω
  let τn : ℕ → ENNReal := fun n ↦ hittingAfter Wc (U n)ᶜ 0 ω
  have hτ_ne_top : τ ≠ ⊤ := ne_of_lt hτfin
  have hτn_le_τ : ∀ n, τn n ≤ τ := by
    intro n
    exact
      hittingAfter_anti Wc (0 : NNReal)
        (show (Metric.ball (0 : State) r)ᶜ ⊆ (U n)ᶜ by
          intro z hz hzn
          exact hz (hUcl n (subset_closure hzn)))
        ω
  have hτn_fin : ∀ n, τn n < ⊤ := by
    intro n
    exact lt_of_le_of_lt (hτn_le_τ n) hτfin
  have hτn_tendsto :
      Tendsto τn atTop (𝓝 τ) := by
    simpa [τ, τn] using
      innerExhaustion_hittingAfter_tendsto_exit
        (Wc := Wc) (G := Metric.ball (0 : State) r) (U := U) (ω := ω)
        hUo hUcl hUmono hUunion (hWcCont ω) hτfin
  have hTimeTendsto :
      Tendsto (fun n : ℕ ↦ (τn n).toNNReal) atTop (𝓝 τ.toNNReal) := by
    -- Proof comment: finite stage exit times can be moved from `ENNReal` to `NNReal` because
    -- they all stay below the finite global exit time.
    simpa [τn, Function.comp] using (ENNReal.tendsto_toNNReal hτ_ne_top).comp hτn_tendsto
  have hPathTendsto :
      Tendsto (fun n : ℕ ↦ Wc ((τn n).toNNReal) ω) atTop (𝓝 (Wc τ.toNNReal ω)) := by
    -- Proof comment: continuity of the modified Brownian path turns convergence of exit clocks
    -- into convergence of the exit positions.
    exact (hWcCont ω).continuousAt.tendsto.comp hTimeTendsto
  have hStoppedValueEqStage :
      ∀ n : ℕ,
        stoppedValue Wc (hittingAfter Wc (U n)ᶜ 0) ω = Wc ((τn n).toNNReal) ω := by
    intro n
    have hτn_ne_top : τn n ≠ ⊤ := ne_of_lt (hτn_fin n)
    change Wc ((τn n).untopA) ω = Wc ((τn n).toNNReal) ω
    congr 1
    have hUntop :
        (((τn n).untopA : NNReal) : ENNReal) = τn n := by
      rw [WithTop.untopA_eq_untop hτn_ne_top]
      exact WithTop.coe_untop _ _
    have hToNN :
        (((τn n).toNNReal : NNReal) : ENNReal) = τn n := by
      rw [ENNReal.coe_toNNReal hτn_ne_top]
    exact ENNReal.coe_injective (hUntop.trans hToNN.symm)
  have hStoppedValueEqGlobal :
      stoppedValue Wc (hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0) ω = Wc (τ.toNNReal) ω := by
    change Wc τ.untopA ω = Wc τ.toNNReal ω
    congr 1
    have hUntop : ((τ.untopA : NNReal) : ENNReal) = τ := by
      rw [WithTop.untopA_eq_untop hτ_ne_top]
      exact WithTop.coe_untop _ _
    have hToNN : ((τ.toNNReal : NNReal) : ENNReal) = τ := by
      rw [ENNReal.coe_toNNReal hτ_ne_top]
    exact ENNReal.coe_injective (hUntop.trans hToNN.symm)
  have hPathWithin :
      ∀ᶠ n : ℕ in atTop, Wc ((τn n).toNNReal) ω ∈ closure (Metric.ball (0 : State) r) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hStartMem : Wc 0 ω ∈ U n := by
      simpa [hWcStart ω] using hUx n
    have hStageClosure :
        stoppedValue Wc (hittingAfter Wc (U n)ᶜ 0) ω ∈ closure (U n) := by
      exact
        stoppedValue_mem_closure_at_exit_of_lt_top
          (U := U n) (W := Wc) (ω := ω)
          (hUo n)
          (hWcCont ω)
          hStartMem
          (hτn_fin n)
    have hStageInBall :
        stoppedValue Wc (hittingAfter Wc (U n)ᶜ 0) ω ∈ Metric.ball (0 : State) r :=
      hUcl n hStageClosure
    -- Proof comment: each stage exit point already lies in the open ball, hence also in its
    -- closure.
    exact subset_closure <| by simpa [hStoppedValueEqStage n] using hStageInBall
  have hLimitMem :
      Wc (τ.toNNReal) ω ∈ closure (Metric.ball (0 : State) r) := by
    have hFrontierMem :
        stoppedValue Wc (hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0) ω ∈
          frontier (Metric.ball (0 : State) r) :=
      stoppedValue_mem_frontier_at_exit_of_continuous
        (G := Metric.ball (0 : State) r) (W := Wc) hx Metric.isOpen_ball hWcCont hWcStart hτfin
    -- Proof comment: the global stopped value lies on the frontier, so its concrete path value
    -- lies in the closure of the open ball.
    simpa [hStoppedValueEqGlobal] using frontier_subset_closure hFrontierMem
  have hValueTendsto :
      Tendsto (fun n : ℕ ↦ u (Wc ((τn n).toNNReal) ω)) atTop (𝓝 (u (Wc τ.toNNReal ω))) := by
    apply (hu.continuousOn_closure (Wc τ.toNNReal ω) hLimitMem).tendsto.comp
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hPathTendsto hPathWithin
  have hDiagEventuallyEq :
      (fun n : ℕ ↦ u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω)) =ᶠ[atTop]
        fun n ↦ u (Wc ((τn n).toNNReal) ω) := by
    filter_upwards
        [tendsto_natCast_atTop_atTop.eventually_ge_atTop (τ.toNNReal)] with n hn
    have hτn_le_n : τn n ≤ (n : ENNReal) := by
      calc
        τn n ≤ τ := hτn_le_τ n
        _ = ((τ.toNNReal : NNReal) : ENNReal) := by rw [ENNReal.coe_toNNReal hτ_ne_top]
        _ ≤ n := by exact_mod_cast hn
    have hτn_ne_top : τn n ≠ ⊤ := ne_of_lt (hτn_fin n)
    have hStopEq :
        stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω = Wc ((τn n).toNNReal) ω := by
      have hStopUntop :
          stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω = Wc (τn n).untopA ω := by
        simpa [τn] using
          (stoppedProcess_eq_of_ge
            (u := Wc) (τ := hittingAfter Wc (U n)ᶜ 0) (ω := ω) (i := (n : NNReal)) hτn_le_n)
      have hTimeEq :
          (τn n).untopA = (τn n).toNNReal := by
        have hUntop :
            (((τn n).untopA : NNReal) : ENNReal) = τn n := by
          rw [WithTop.untopA_eq_untop hτn_ne_top]
          exact WithTop.coe_untop _ _
        have hToNN :
            (((τn n).toNNReal : NNReal) : ENNReal) = τn n := by
          rw [ENNReal.coe_toNNReal hτn_ne_top]
        exact ENNReal.coe_injective (hUntop.trans hToNN.symm)
      simpa [hTimeEq] using hStopUntop
    -- Proof comment: once the deterministic horizon dominates the stage exit clock, the diagonal
    -- stop is exactly the stage exit value.
    simpa [hStopEq]
  have hDiagTendsto :
      Tendsto
        (fun n : ℕ ↦ u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω))
        atTop
        (𝓝 (u (Wc τ.toNNReal ω))) :=
    Filter.Tendsto.congr' hDiagEventuallyEq.symm hValueTendsto
  -- Proof comment: the diagonal sequence is eventually the stage exit value, those stage exits
  -- converge to the global stopped point, and continuity on the closure identifies the limit.
  simpa [hStoppedValueEqGlobal] using hDiagTendsto

/-- Helper for Exercise 25.4.3: the stochastic core is the stopped-value expectation formula for
Dirichlet solutions on the open ball. -/
theorem dirichletSolution_eq_stoppedValueExpectation_ball
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (r : ℝ) (hr : 0 < r)
    (hW : ∀ z : State, IsBrownianMotionVectorStartedAt (P z : Measure Ω) W z)
    {x : State} (hx : x ∈ Metric.ball (0 : State) r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ)
    {u : State → ℝ}
    (hu :
      SolvesDirichletProblem
        (Metric.ball (0 : State) r)
        (openBallFrontierBoundaryDatum r hr g)
        u) :
    u x =
      ∫ ω, u (stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω) ∂
        (P x : Measure Ω) := by
  let μ : ProbabilityMeasure Ω := P x
  suffices hGoal :
      u x =
        ∫ ω, u (stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω) ∂
          (μ : Measure Ω) by
    simpa [μ] using hGoal
  have hWx : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x := by
    simpa [μ] using hW x
  have hBallCompact :
      IsCompact (closure (Metric.ball (0 : State) r)) :=
    isCompact_closure_openBall r hr
  have hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W (Metric.ball (0 : State) r)ᶜ 0 ω < ⊤ :=
    openBallExitTime_ae_lt_top P W r hr hW hx
  rcases
      existsContinuousBrownianVectorStartedAtModification
        (μ := μ) (W := W) (x := x) hWx with
    ⟨Wc, hWc, hWcCont, hWcStart, hWcEq⟩
  have hExitEqWc :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W (Metric.ball (0 : State) r)ᶜ 0 ω =
            hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0 ω ∧
          stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω =
            stoppedValue Wc (hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0) ω :=
    stageExitStoppedValue_ae_eq_continuousVersion
      (μ := (μ : Measure Ω)) (W := W) (Wc := Wc) (U := Metric.ball (0 : State) r) hWcEq
  have hExitFiniteWc :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0 ω < ⊤ := by
    filter_upwards [hExitFinite, hExitEqWc] with ω hω hEq
    simpa [hEq.1] using hω
  rcases
      existsInnerExhaustionStartingAt
        (G := Metric.ball (0 : State) r)
        Metric.isOpen_ball
        hBallCompact
        hx with
    ⟨U, hUo, hUx, hUcpt, hUcl, hUmono, hUunion⟩
  obtain ⟨Uext, hUextCont, hUextEq⟩ :=
    existsContinuousExtensionOnClosure
      (G := Metric.ball (0 : State) r) (u := u) hu.continuousOn_closure
  rcases
      existsAbsLeOnCompactClosure_continuous
        (U := Metric.ball (0 : State) r) (F := Uext) hBallCompact hUextCont with
    ⟨C, hCnonneg, hC⟩
  have hClosureBound :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ closure (Metric.ball (0 : State) r), |u z| ≤ C := by
    refine ⟨C, hCnonneg, ?_⟩
    intro z hz
    simpa [hUextEq hz] using hC z hz
  have hExitFiniteStage :
      ∀ n : ℕ,
        ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter Wc (U n)ᶜ 0 ω < ⊤ := by
    intro n
    exact
      ae_exitTime_lt_top_of_isCompact_closure_startedAt
        (x := x) (hx := hUx n) hWc (hUo n) (hUcpt n)
  have hNatIdentity :
      ∀ n : ℕ,
        u x =
          ∫ ω, u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω) ∂(μ : Measure Ω) := by
    intro n
    rcases
        exists_open_buffer_of_isCompact_subset_open
          (K := closure (U n))
          (hKcompact := hUcpt n)
          (hKG := hUcl n)
          (hGo := Metric.isOpen_ball) with
      ⟨Tn, hTn_open, hTn_contains, hTn_closure_subset⟩
    rcases
        existsStageHarmonicExtension
          (V := closure (U n))
          (T := Tn)
          (G := Metric.ball (0 : State) r)
          (hVT := by simpa [closure_closure] using hTn_contains)
          (hTG := hTn_closure_subset)
          (hTo := hTn_open)
          hu.harmonicOnNhd with
      ⟨Fn, hFncontDiff, hFnharm, hFneq⟩
    have hStageClosureBound :
        ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ z ∈ closure (U n), |u z| ≤ Cn := by
      refine ⟨C, hCnonneg, ?_⟩
      intro z hz
      simpa [hUextEq (subset_closure (hUcl n hz))] using
        hC z (subset_closure (hUcl n hz))
    -- Proof comment: the remaining optional-stopping input is now isolated to the dedicated
    -- stage helper, while the stage geometry and harmonic extension data are already explicit.
    exact
      stageStoppedExtension_expectation_eq_atNat_ball
        (μ := μ) (W := Wc) (U := U n) (V := closure (U n)) (x := x) (u := u) (F := Fn)
        (hUx n)
        (hUo n)
        (hUcpt n)
        (by intro z hz; exact hz)
        hWc
        hWcCont
        hWcStart
        (hExitFiniteStage n)
        hFneq
        hStageClosureBound
        hFncontDiff
        hFnharm
        n
  have hMeasNat :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω ↦ u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω))
          (μ : Measure Ω) := by
    intro n
    -- Proof comment: the fixed global continuous extension is measurable, and on each stopped
    -- stage it agrees almost surely with `u`.
    exact
      stageStopped_eqOnClosure_aestronglyMeasurable_atNat
        (μ := μ) (W := Wc) (U := U n) (x := x) (u := u) (F := Uext)
        (hUx n)
        (hUo n)
        hWc
        hWcCont
        hWcStart
        (hExitFiniteStage n)
        hUextCont.measurable
        (fun z hz ↦ hUextEq (subset_closure (hUcl n hz)))
        n
  have hBoundNat :
      ∀ n : ℕ, ∀ᵐ ω ∂(μ : Measure Ω),
        |u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω)| ≤ C := by
    intro n
    filter_upwards [hExitFiniteStage n] with ω hωfin
    have hStartMem : Wc 0 ω ∈ U n := by
      simpa [hWcStart ω] using hUx n
    have hmem :
        stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω ∈ closure (Metric.ball (0 : State) r) := by
      exact
        subset_closure <|
          hUcl n <|
            stageStoppedProcess_mem_buffer
              (U := U n) (V := closure (U n)) (W := Wc) (ω := ω)
              (hUo n)
              (hWcCont ω)
              hStartMem
              (by intro z hz; exact hz)
              hωfin
              n
    simpa [hUextEq hmem] using
      hC (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω) hmem
  have hDiagonalLimit :
      ∀ᵐ ω ∂(μ : Measure Ω),
        Tendsto
          (fun n : ℕ ↦ u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω))
          atTop
          (𝓝
            (u
              (stoppedValue Wc
                (hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0) ω))) := by
    -- Route correction: the diagonal limit is proved directly toward the global stopped value of
    -- `Wc`, so the final transport back to `W` is a separate almost-sure rewrite.
    exact
      tendsto_innerStageStopped_to_globalStoppedValue_ball
        (μ := μ) (Wc := Wc) (x := x) (u := u) (g := g)
        r hr hx hUo hUx hUcl hUmono hUunion hWcCont hWcStart hExitFiniteWc hu
  have hIntegralTendsto :
      Tendsto
        (fun n : ℕ ↦
          ∫ ω, u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω) ∂(μ : Measure Ω))
        atTop
        (𝓝
          (∫ ω,
            u (stoppedValue Wc (hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0) ω) ∂
              (μ : Measure Ω))) := by
    exact
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ ↦ C)
        hMeasNat
        (integrable_const C)
        hBoundNat
        hDiagonalLimit
  have hConstTendsto :
      Tendsto
        (fun n : ℕ ↦
          ∫ ω, u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω) ∂(μ : Measure Ω))
        atTop
        (𝓝 (u x)) := by
    have hSeqEq :
        (fun n : ℕ ↦
          ∫ ω, u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω) ∂(μ : Measure Ω)) =
          fun _ : ℕ ↦ u x := by
      funext n
      exact (hNatIdentity n).symm
    simpa [hSeqEq] using tendsto_const_nhds
  have hStoppedWc :
      u x =
        ∫ ω,
          u (stoppedValue Wc (hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0) ω) ∂
            (μ : Measure Ω) := by
    -- Proof comment: the stagewise optional-stopping identities and the dominated-convergence
    -- setup are now explicit, so uniqueness of limits identifies the continuous-modification
    -- stopped-value expectation.
    exact (tendsto_nhds_unique hIntegralTendsto hConstTendsto).symm
  have hIntegralEq :
      ∫ ω,
        u (stoppedValue Wc (hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0) ω) ∂
          (μ : Measure Ω) =
        ∫ ω,
          u (stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω) ∂
            (μ : Measure Ω) := by
    refine integral_congr_ae ?_
    filter_upwards [hExitEqWc] with ω hEq
    rw [hEq.2]
  calc
    u x =
        ∫ ω,
          u (stoppedValue Wc (hittingAfter Wc (Metric.ball (0 : State) r)ᶜ 0) ω) ∂
            (μ : Measure Ω) :=
      hStoppedWc
    _ =
        ∫ ω,
          u (stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω) ∂
            (μ : Measure Ω) :=
      hIntegralEq

/-- Helper for Exercise 25.4.3: on the open ball, a Dirichlet solution equals the Brownian
exit-value expectation at a fixed start point. This is the ball-specialized fixed-start slice of
the later general representation theorem, kept local so the item does not import later modules. -/
theorem dirichletSolution_eq_exitExpectation_atPoint_ball
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (r : ℝ) (hr : 0 < r)
    (exitValue : Ω → frontier (Metric.ball (0 : State) r))
    (hExitMeas : Measurable exitValue)
    (hW : ∀ z : State, IsBrownianMotionVectorStartedAt (P z : Measure Ω) W z)
    (hExit :
      ∀ ω : Ω, hittingAfter W (Metric.ball (0 : State) r)ᶜ 0 ω < ⊤ →
        (exitValue ω : State) =
          stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω)
    {x : State} (hx : x ∈ Metric.ball (0 : State) r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ)
    {u : State → ℝ}
    (hu :
      SolvesDirichletProblem
        (Metric.ball (0 : State) r)
        (openBallFrontierBoundaryDatum r hr g)
        u) :
    u x =
      ∫ ω, openBallFrontierBoundaryDatum r hr g (exitValue ω) ∂ (P x : Measure Ω) := by
  have hStopped :
      u x =
        ∫ ω, u (stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω) ∂
          (P x : Measure Ω) :=
    dirichletSolution_eq_stoppedValueExpectation_ball
      P W r hr hW hx g hu
  have hExitFinite :
      ∀ᵐ ω ∂ (P x : Measure Ω),
        hittingAfter W (Metric.ball (0 : State) r)ᶜ 0 ω < ⊤ :=
    openBallExitTime_ae_lt_top P W r hr hW hx
  -- Proof comment: once the stopped-value formula is isolated, the final theorem is just the
  -- almost-sure rewrite from the stopped exit point to the chosen frontier-valued exit map.
  calc
    u x =
        ∫ ω, u (stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω) ∂
          (P x : Measure Ω) :=
      hStopped
    _ =
        ∫ ω, openBallFrontierBoundaryDatum r hr g (exitValue ω) ∂ (P x : Measure Ω) := by
      refine integral_congr_ae ?_
      filter_upwards [hExitFinite] with ω hωfin
      have hExitEq :
          (exitValue ω : State) =
            stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω :=
        hExit ω hωfin
      calc
        u (stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω) =
            u (exitValue ω : State) := by
          rw [← hExitEq]
        _ = openBallFrontierBoundaryDatum r hr g (exitValue ω) :=
          hu.boundary_eq (exitValue ω)

/-- Helper for Exercise 25.4.3: any Dirichlet solution on the open ball has the Brownian
exit-expectation representation at a fixed interior start point. -/
theorem openBallDirichletSolution_eq_exitExpectation_startedAt
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (r : ℝ) (hr : 0 < r)
    (exitValue : Ω → frontier (Metric.ball (0 : State) r))
    (hExitMeas : Measurable exitValue)
    (hW : ∀ z : State, IsBrownianMotionVectorStartedAt (P z : Measure Ω) W z)
    (hExit :
      ∀ ω : Ω, hittingAfter W (Metric.ball (0 : State) r)ᶜ 0 ω < ⊤ →
        (exitValue ω : State) =
          stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω)
    {x : State} (hx : x ∈ Metric.ball (0 : State) r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ)
    {u : State → ℝ}
    (hu :
      SolvesDirichletProblem
        (Metric.ball (0 : State) r)
        (openBallFrontierBoundaryDatum r hr g)
        u) :
    u x =
      ∫ ω, openBallFrontierBoundaryDatum r hr g (exitValue ω) ∂ (P x : Measure Ω) := by
  -- Proof comment: this theorem is now just the public item-facing wrapper around the localized
  -- fixed-start exit-representation lemma for the open ball.
  exact
    dirichletSolution_eq_exitExpectation_atPoint_ball
      P W r hr exitValue hExitMeas hW hExit hx g hu

/-- Helper for Exercise 25.4.3: the boundary-aware Poisson candidate solves the Dirichlet problem
once the remaining analytic harmonicity package is proved. -/
theorem openBallPoissonDirichletCandidate_solvesDirichletProblem
    (r : ℝ) (hr : 0 < r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    SolvesDirichletProblem
      (Metric.ball (0 : State) r)
      (openBallFrontierBoundaryDatum r hr g)
      (openBallPoissonDirichletCandidate r hr g) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the analytic burden is isolated in the canonical `HarmonicContOnCl` owner
    -- for the patched Poisson candidate.
    exact openBallPoissonDirichletCandidate_harmonicContOnCl r hr g
  · -- Proof comment: the patched owner already matches the boundary datum on the frontier by
    -- construction.
    intro z
    exact openBallPoissonDirichletCandidate_eq_boundary_on_frontier r hr g z

/-- Helper for Exercise 25.4.3: once the Poisson extension is known to solve the Dirichlet problem
on the open ball, evaluating it at the start point agrees with the Brownian exit expectation of the
transported boundary datum. -/
theorem openBallPoissonExtension_eq_exitExpectation_startedAt
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (r : ℝ) (hr : 0 < r)
    (exitValue : Ω → frontier (Metric.ball (0 : State) r))
    (hExitMeas : Measurable exitValue)
    (hW : ∀ z : State, IsBrownianMotionVectorStartedAt (P z : Measure Ω) W z)
    (hExit :
      ∀ ω : Ω, hittingAfter W (Metric.ball (0 : State) r)ᶜ 0 ω < ⊤ →
        (exitValue ω : State) =
          stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω)
    {x : State} (hx : x ∈ Metric.ball (0 : State) r)
    (g : BoundedContinuousFunction (Metric.sphere (0 : State) |r|) ℝ) :
    openBallPoissonExtension r g x =
      ∫ ω, openBallFrontierBoundaryDatum r hr g (exitValue ω) ∂ (P x : Measure Ω) := by
  -- Proof comment: first package the boundary-aware Poisson candidate as a Dirichlet solution on
  -- the open ball.
  have hDirichlet :
      SolvesDirichletProblem
        (Metric.ball (0 : State) r)
        (openBallFrontierBoundaryDatum r hr g)
        (openBallPoissonDirichletCandidate r hr g) :=
    openBallPoissonDirichletCandidate_solvesDirichletProblem r hr g
  have hCandidate :
      openBallPoissonDirichletCandidate r hr g x =
        ∫ ω, openBallFrontierBoundaryDatum r hr g (exitValue ω) ∂ (P x : Measure Ω) :=
    openBallDirichletSolution_eq_exitExpectation_startedAt
      P W r hr exitValue hExitMeas hW hExit hx g hDirichlet
  -- Proof comment: on interior starting points the patched candidate agrees with the raw Poisson
  -- integral, so the exit-expectation identity transfers back to `openBallPoissonExtension`.
  calc
    openBallPoissonExtension r g x =
        openBallPoissonDirichletCandidate r hr g x := by
      symm
      exact openBallPoissonDirichletCandidate_eq_extension_of_mem_ball r hr g hx
    _ =
        ∫ ω, openBallFrontierBoundaryDatum r hr g (exitValue ω) ∂ (P x : Measure Ω) :=
      hCandidate

-- Route correction: the broken self-importing stub destroyed the original proof body. The
-- executable frontier rebuilt here recovers the transport layer exactly; the remaining analytic
-- blocker is the Poisson-kernel identification of the transported harmonic measure.
/-- Exercise 25.4.3: after transporting `frontier (Metric.ball (0 : State) r)` to the sphere of
radius `|r|`, the Brownian harmonic measure on the open ball is the boundary measure with density
given by the classical Poisson kernel. -/
theorem map_openBallFrontierHomeomorphAbsSupport_harmonicMeasure_eq_withDensity
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (r : ℝ) (hr : 0 < r)
    (exitValue : Ω → frontier (Metric.ball (0 : State) r))
    (hExitMeas : Measurable exitValue)
    (hW : ∀ z : State, IsBrownianMotionVectorStartedAt (P z : Measure Ω) W z)
    (hExit :
      ∀ ω : Ω, hittingAfter W (Metric.ball (0 : State) r)ᶜ 0 ω < ⊤ →
        (exitValue ω : State) =
          stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω)
    {x : State} (hx : x ∈ Metric.ball (0 : State) r) :
    openBallBoundaryHarmonicMeasure
        P r hr exitValue hExitMeas x hx =
      openBallPoissonKernelMeasure r x := by
  let νH :=
    openBallBoundaryHarmonicMeasure P r hr exitValue hExitMeas x hx
  let νP := openBallPoissonKernelMeasure r x
  let _ : IsFiniteMeasure νH := by
    let _ : IsProbabilityMeasure νH := by
      simpa [νH] using
        openBallBoundaryHarmonicMeasure_isProbability
          P r hr exitValue hExitMeas x hx
    infer_instance
  let _ : IsFiniteMeasure νP := by
    simpa [νP] using openBallPoissonKernelMeasure_isFinite r hr hx
  -- Proof comment: finite boundary measures are determined by bounded continuous test-function
  -- integrals, so it suffices to compare both sides against an arbitrary boundary datum `g`.
  apply boundarySphereMeasure_eq_ofBcfIntegrals
  intro g
  calc
    ∫ y, g y ∂ νH =
        ∫ ω, openBallFrontierBoundaryDatum r hr g (exitValue ω) ∂ (P x : Measure Ω) := by
      simpa [νH] using
        integral_openBallBoundaryHarmonicMeasure_eq_exitIntegral
          P r hr exitValue hExitMeas x hx g
    _ = openBallPoissonExtension r g x := by
      symm
      exact
        openBallPoissonExtension_eq_exitExpectation_startedAt
          P W r hr exitValue hExitMeas hW hExit hx g
    _ = ∫ y, g y ∂ νP := by
      simp [νP, openBallPoissonExtension]

end ProbabilityTheory
