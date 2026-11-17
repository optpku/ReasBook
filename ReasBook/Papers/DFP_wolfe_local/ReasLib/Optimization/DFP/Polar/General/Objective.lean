module

public import ReasLib.Optimization.DFP.Polar.General.Realization
public import ReasLib.Optimization.DFP.Polar.General.InterpolationBounds
public import ReasLib.Optimization.DFP.Polar.General.RadiusProducts
public import ReasLib.Optimization.DFP.Polar.General.ActualGeometry
public import ReasLib.Analysis.Convex.HessianPerturbation.Bounds

public section

noncomputable section

open Filter
open scoped Topology ContDiff

namespace DFP.Polar.General.Objective

/-- Helper for eq:polar-endpoint-data: the squared norm of the actual polar
point is the square of its same tail-product radius. -/
theorem norm_point_sq (p : Parameters) (k : ℕ) : ‖p.point k‖ ^ 2 = p.radius k ^ 2 := by
  rw [p.point_def, norm_smul, Real.norm_eq_abs, ActualObjective.norm_polarUnit,
    mul_one, sq_abs]

/-- Helper for eq:polar-endpoint-data: the actual point norm is its positive
tail-product radius. -/
theorem norm_point (p : Parameters) (k : ℕ) (hr : 0 ≤ p.radius k) :
    ‖p.point k‖ = p.radius k := by
  rw [p.point_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
    ActualObjective.norm_polarUnit, mul_one]

/-- Helper for eq:polar-endpoint-data: interpolation at the unchanged actual
points realizes the exact prescribed objective values, gradients and Hessians. -/
theorem objective_endpoints (p : Parameters) (κ : ℝ)
    (hg : InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction) (k : ℕ) :
    p.objective κ (p.point k) = (1 / 2 : ℝ) * p.radius k ^ 2 ∧
      gradient (p.objective κ) (p.point k) = p.gradients k ∧
        hessian (p.objective κ) (p.point k) = 1 := by
  rw [p.objective_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [InterpolationSum.objective_center hg, norm_point_sq]
  · rw [InterpolationSum.gradient_objective_center hg, p.correction_def,
      p.gradients_def, sub_smul, one_smul]
    abel
  · rw [hessian_def]
    exact InterpolationSum.hessian_objective_center hg k

/-- Helper for lem:polar-interpolation: the exact perturbation and its first
two jets vanish on the entire closed unit disk, including the unit circle. -/
theorem perturbation_jets_on_disk (p : Parameters) (κ : ℝ)
    (hg : InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ ≤ 1) :
    InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction x = 0 ∧
      gradient (InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction) x = 0 ∧
        hessian (InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction) x = 0 := by
  refine ⟨InterpolationSum.perturbation_eq_zero_of_norm_le_one hg hx,
    InterpolationSum.gradient_perturbation_eq_zero_of_norm_le_one hg hx, ?_⟩
  apply norm_eq_zero.mp
  rw [hessian_def, norm_fderiv_gradient_eq_norm_fderiv_fderiv,
    InterpolationSum.secondFDeriv_perturbation_eq_zero_of_norm_le_one hg hx, norm_zero]

/-- Helper for eq:polar-objective: an operator-norm bound relative to identity
gives the source uniform Loewner bounds for any twice differentiable objective. -/
theorem hessianBounds_of_identity_norm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {ε : ℝ} (hf : ContDiff ℝ 2 f)
    (hbound : ∀ x, ‖hessian f x - 1‖ ≤ ε) :
    HasHessianBounds (1 - ε) (1 + ε) f := by
  apply HasHessianBounds.of_forall
  intro x
  apply HasHessianBoundsAt.of_quadraticForm
  · exact hessian_isSelfAdjoint hf.contDiffAt
  · intro v
    have hinner := ContinuousLinearMap.inner_apply_bounds_of_norm_le
      (hessian f x - 1) ε (hbound x) v
    rw [sub_apply, one_apply_eq_self, inner_sub_left,
      real_inner_self_eq_norm_sq] at hinner
    constructor
    · linarith [hinner.1]
    · linarith [hinner.2]

/-- Helper for eq:polar-objective: the exact objective's perturbation-free
origin has both value and gradient zero. -/
theorem objective_origin (p : Parameters) (κ : ℝ)
    (hg : InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction) :
    p.objective κ 0 = 0 ∧ gradient (p.objective κ) 0 = 0 := by
  have hzeroNorm : ‖(0 : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 := by
    simp
  have hzeroGradient := (perturbation_jets_on_disk p κ hg hzeroNorm).2.1
  have hdiff := ((InterpolationSum.contDiff_perturbation hg).differentiable
    two_ne_zero).differentiableAt (x := (0 : EuclideanSpace ℝ (Fin 2)))
  constructor
  · rw [p.objective_def]
    exact InterpolationSum.objective_zero hg
  · rw [p.objective_def, funext (InterpolationSum.objective_apply p.point
      (p.supportRadius κ) p.correction)]
    simpa only [sub_zero, hzeroGradient, add_zero] using
      HessianPerturbation.gradient_halfNormSq_sub_add
        (0 : EuclideanSpace ℝ (Fin 2))
        (InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction) 0 hdiff

/-- Helper for lem:polar-interpolation: the complete explicit source-objective
certificate contains conclusions about the same unchanged points and corrections. -/
structure ObjectiveEstimates (p : Parameters) (κ ε H : ℝ) : Prop where
  /-- Helper for lem:polar-interpolation: actual open supports are disjoint,
  retain their radial margin, and have vanishing coefficient-to-radius ratios. -/
  geometry : InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction
  /-- Helper for lem:polar-interpolation: the exact infinite correction sum is `C²`. -/
  perturbation_contDiff :
    ContDiff ℝ 2 (InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction)
  /-- Helper for lem:polar-interpolation: the actual source objective is `C²`. -/
  contDiff : ContDiff ℝ 2 (p.objective κ)
  /-- Helper for eq:polar-interpolation-jets: the source perturbation has the
  prescribed center jets. -/
  center_jets : ∀ k,
    InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction (p.point k) = 0 ∧
      gradient (InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction)
        (p.point k) = p.correction k ∧
      hessian (InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction)
        (p.point k) = 0
  /-- Helper for lem:polar-interpolation: the perturbation jets vanish on the closed unit disk. -/
  disk_jets : ∀ x, ‖x‖ ≤ 1 →
    InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction x = 0 ∧
      gradient (InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction) x = 0 ∧
      hessian (InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction) x = 0
  /-- Helper for eq:polar-endpoint-data: exact interpolation realizes every prescribed endpoint. -/
  endpoints : ∀ k, p.objective κ (p.point k) = (1 / 2 : ℝ) * p.radius k ^ 2 ∧
    gradient (p.objective κ) (p.point k) = p.gradients k ∧
      hessian (p.objective κ) (p.point k) = 1
  /-- Helper for eq:polar-objective: the objective equals the base quadratic on the closed disk. -/
  disk : ∀ x, ‖x‖ ≤ 1 → p.objective κ x = (1 / 2 : ℝ) * ‖x‖ ^ 2
  /-- Helper for thm:main: the objective has source normalization at the origin. -/
  origin : p.objective κ 0 = 0
  /-- Helper for eq:polar-interpolation-bound: the global Hessian is within the
  requested accuracy. -/
  hessian_near_identity : ∀ x, ‖hessian (p.objective κ) x - 1‖ ≤ ε
  /-- Helper for lem:polar-interpolation: the global Hölder constant is nonnegative. -/
  holder_nonneg : 0 ≤ H
  /-- Helper for lem:polar-interpolation: the exact Hessian is globally `p.beta`-Hölder. -/
  hessian_holder : ∀ x y, ‖hessian (p.objective κ) x - hessian (p.objective κ) y‖ ≤
    H * ‖x - y‖ ^ p.beta
  /-- Helper for thm:main: the source objective has the uniform two-sided Hessian bounds. -/
  hessian_bounds : HasHessianBounds (1 - ε) (1 + ε) (p.objective κ)
  /-- Helper for thm:main: the source objective is uniformly strongly convex. -/
  strongConvex : StrongConvexOn Set.univ (1 - ε) (p.objective κ)
  /-- Helper for thm:main: the source objective has positive quadratic growth at the origin. -/
  growth : ∀ x, ((1 - ε) / 2) * ‖x‖ ^ 2 ≤ p.objective κ x
  /-- Helper for thm:main: the origin is the unique global minimizer. -/
  unique_minimizer : ∀ x, (∀ y, p.objective κ x ≤ p.objective κ y) ↔ x = 0

/-- Helper for lem:polar-interpolation: exact cutoff geometry and proved Hessian
bounds imply all source interpolation, convexity and minimizer conclusions. -/
theorem objectiveEstimatesOfBounds (p : Parameters) (κ ε H : ℝ)
    (hg : InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction)
    (hε : ε < 1) (hH : 0 ≤ H)
    (hbound : ∀ x, ‖hessian (p.objective κ) x - 1‖ ≤ ε)
    (hholder : ∀ x y, ‖hessian (p.objective κ) x - hessian (p.objective κ) y‖ ≤
      H * ‖x - y‖ ^ p.beta) : ObjectiveEstimates p κ ε H := by
  have hperturbation := InterpolationSum.contDiff_perturbation hg
  have hregular : ContDiff ℝ 2 (p.objective κ) := by
    rw [p.objective_def]
    exact InterpolationSum.contDiff_objective hg
  have hHessian := hessianBounds_of_identity_norm hregular hbound
  have hpositive : 0 < 1 - ε := sub_pos.mpr hε
  have hlower : ∀ x v, (1 - ε) * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (p.objective κ)) x v) v := by
    intro x v
    simpa only [hessian_def] using ((hHessian.at x).quadraticForm v).1
  have hstrong := ContDiff.strongConvexOnOfHessianLowerBound
    (p.objective κ) (1 - ε) hregular hpositive hlower
  have horigin := objective_origin p κ hg
  have hgrowth : ∀ x, ((1 - ε) / 2) * ‖x‖ ^ 2 ≤ p.objective κ x := by
    intro x
    have hfirst := ContDiff.firstOrderOfHessianLowerBound (p.objective κ) (1 - ε)
      hregular hpositive hlower 0 x
    simpa only [horigin.1, horigin.2, inner_zero_left, sub_zero, zero_add] using hfirst
  refine
    { geometry := hg
      perturbation_contDiff := hperturbation
      contDiff := hregular
      center_jets := ?_
      disk_jets := fun x hx ↦ perturbation_jets_on_disk p κ hg hx
      endpoints := objective_endpoints p κ hg
      disk := ?_
      origin := horigin.1
      hessian_near_identity := hbound
      holder_nonneg := hH
      hessian_holder := hholder
      hessian_bounds := hHessian
      strongConvex := hstrong
      growth := hgrowth
      unique_minimizer := ?_ }
  · intro k
    refine ⟨InterpolationSum.perturbation_center hg k,
      InterpolationSum.gradient_perturbation_center hg k, ?_⟩
    apply norm_eq_zero.mp
    rw [hessian_def, norm_fderiv_gradient_eq_norm_fderiv_fderiv,
      InterpolationSum.secondFDeriv_perturbation_center hg k, norm_zero]
  · intro x hx
    rw [p.objective_def]
    exact InterpolationSum.objective_eq_quadratic_of_norm_le_one hg hx
  · exact ActualObjective.unique_minimizer_of_quadratic_growth
      (half_pos hpositive) horigin.1 hgrowth

/-- Helper for lem:polar-interpolation: the actual
source coefficients and support radii give the complete objective certificate,
with one cutoff constant chosen before all orbit data and starting indices. -/
theorem exists_objectiveEstimates_of_powerScale :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (p : Parameters) (κ A ε : ℝ),
      0 < p.beta → p.beta < 1 → 0 < p.startIndex →
      InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction →
      0 < κ → 0 ≤ A → ε < 1 →
      (∀ k, ‖p.correction k‖ ≤
        A * scale p.beta p.startIndex (k / 2) ^ (1 + p.beta)) →
      Cχ * (A / κ) * scale p.beta p.startIndex 0 ^ p.beta ≤ ε →
      ObjectiveEstimates p κ ε (2 * Cχ * (A * κ ^ (-(1 + p.beta)))) := by
  obtain ⟨Cχ, hCχ, hbounds⟩ :=
    InterpolationBounds.exists_objective_bounds_of_powerScale
      (E := EuclideanSpace ℝ (Fin 2))
  refine ⟨Cχ, hCχ, ?_⟩
  intro p κ A ε hβ hβone hstart hg hκ hA hε hcoefficient hsmall
  have hupper (k : ℕ) :
      scale p.beta p.startIndex (k / 2) ≤ scale p.beta p.startIndex 0 :=
    scale_antitone hβ hstart (Nat.zero_le _)
  obtain ⟨hcont, hbound, hholder⟩ := hbounds p.beta hβ.le hβone.le p.point
    (p.supportRadius κ) p.correction (fun k ↦ scale p.beta p.startIndex (k / 2))
    κ A (scale p.beta p.startIndex 0) hg hκ hA (scale_pos p.beta hstart 0)
    (fun k ↦ scale_pos p.beta hstart (k / 2)) hupper
    (p.supportRadius_def κ) hcoefficient
  have hboundActual : ∀ x, ‖hessian (p.objective κ) x - 1‖ ≤ ε := by
    intro x
    rw [p.objective_def]
    exact (hbound x).trans hsmall
  have hholderActual : ∀ x y,
      ‖hessian (p.objective κ) x - hessian (p.objective κ) y‖ ≤
        (2 * Cχ * (A * κ ^ (-(1 + p.beta)))) * ‖x - y‖ ^ p.beta := by
    rw [p.objective_def]
    exact hholder
  have hH : 0 ≤ 2 * Cχ * (A * κ ^ (-(1 + p.beta))) := by
    positivity
  exact objectiveEstimatesOfBounds p κ ε _ hg hε hH hboundActual hholderActual

/-- Helper for thm:main: after every construction constant is fixed, a single
natural threshold makes `C τ₀^β` smaller than any prescribed positive accuracy. -/
theorem exists_startIndex_power_small {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) (C : ℝ) :
    ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 → C * scale β j0 0 ^ β ≤ ε := by
  have hexponent : 0 < β / (1 + β) := div_pos hβ (add_pos zero_lt_one hβ)
  have hscale : Tendsto (fun j0 : ℕ ↦ scale β j0 0 ^ β) atTop (𝓝 0) := by
    simpa only [scale_rpow, Nat.add_zero, neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop hexponent).comp tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ j0 : ℕ in atTop, C * scale β j0 0 ^ β ≤ ε := by
    have hlimit : Tendsto (fun j0 : ℕ ↦ C * scale β j0 0 ^ β) atTop (𝓝 0) := by
      simpa only [mul_zero] using hscale.const_mul C
    exact (hlimit.eventually (Iio_mem_nhds hε)).mono (fun _ h ↦ h.le)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hbound
  refine ⟨max J 1, ?_, ?_⟩
  · exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right J 1)
  · intro j0 hj0
    exact hJ j0 ((le_max_left J 1).trans hj0)

/-- Helper for lem:polar-interpolation: the actual scalar angular, radial and
coefficient envelopes prove the unchanged objective's cutoff geometry. -/
theorem interpolationGeometry_of_source_scalar_bounds (p : Parameters)
    (hβ : 0 < p.beta) (hstart : 0 < p.startIndex)
    {η a b c κ L A : ℝ} (hη : 0 ≤ η) (hηone : η ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hκ : 0 < κ)
    (hspan : b * η ≤ Real.pi)
    (hsmall : scale p.beta p.startIndex 0 ≤ η / 2)
    (hκsep : 2 * κ ≤ min (a / Real.pi) (c * η / 8))
    (hκmargin : 2 * κ * scale p.beta p.startIndex 0 ^ p.beta ≤ L)
    (hr : ∀ k, 1 ≤ p.radius k) (hradius : Tendsto p.radius atTop (𝓝 1))
    (hlower : ∀ k, a * scale p.beta p.startIndex (k / 2) ≤ p.angleIncrement k)
    (hupper : ∀ k, p.angleIncrement k ≤ b * scale p.beta p.startIndex (k / 2))
    (hdrop : ∀ k, c * scale p.beta p.startIndex (k / 2) ^ 2 ≤
      p.radius k - p.radius (k + 1))
    (hradial : ∀ k, L * scale p.beta p.startIndex (k / 2) ^ (1 - p.beta) ≤
      p.radius k - 1)
    (hcoefficient : ∀ k, ‖p.correction k‖ ≤
      A * scale p.beta p.startIndex (k / 2) ^ (1 + p.beta)) :
    InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction := by
  have hpoint : p.point = Geometry.point p.radius p.angle := by
    funext k
    rw [p.point_def, Geometry.point_def]
  rw [hpoint, funext (p.supportRadius_def κ)]
  have hlower' : ∀ k, a * scale p.beta p.startIndex (k / 2) ≤
      p.angle (k + 1) - p.angle k := by
    simpa only [p.angleIncrement_def] using hlower
  have hupper' : ∀ k, p.angle (k + 1) - p.angle k ≤
      b * scale p.beta p.startIndex (k / 2) := by
    simpa only [p.angleIncrement_def] using hupper
  exact Geometry.interpolationGeometry_of_scalar_bounds hβ hstart hη hηone
    ha hb hc hκ hspan hsmall hκsep hκmargin hr hradius hlower' hupper' hdrop hradial
    hcoefficient

/-- Helper for eq:polar-separation: disjoint positive support balls make the
actual interpolation centers pairwise distinct. -/
theorem points_injective (p : Parameters) (κ : ℝ)
    (hg : InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction) :
    Function.Injective p.point := by
  intro i j hij
  have hi : p.point i ∈ Metric.ball (p.point i) (p.supportRadius κ i) := by
    simpa only [Metric.mem_ball, dist_self] using hg.radius_pos i
  have hj : p.point i ∈ Metric.ball (p.point j) (p.supportRadius κ j) := by
    rw [hij]
    simpa only [Metric.mem_ball, dist_self] using hg.radius_pos j
  exact hg.disjoint_open.elim_set (Set.mem_univ i) (Set.mem_univ j) (p.point i) hi hj

/-- Helper for eq:counterexample-nonlipschitz: consecutive even and odd source
centers have a strictly positive secant length. -/
theorem evenStep_pos (p : Parameters) (κ : ℝ)
    (hg : InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction) (j : ℕ) :
    0 < ‖p.point (2 * j + 1) - p.point (2 * j)‖ := by
  have hindices : 2 * j + 1 ≠ 2 * j := Nat.succ_ne_self _
  have hpoints : p.point (2 * j + 1) ≠ p.point (2 * j) := by
    intro h
    exact hindices (points_injective p κ hg h)
  exact norm_pos_iff.mpr (sub_ne_zero.mpr hpoints)

/-- Helper for eq:counterexample-nonlipschitz: the original initial sublevel
set of the unchanged explicit source objective. -/
def initialLevelSet (p : Parameters) (κ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | p.objective κ x ≤ p.objective κ (p.point 0)}

/-- Helper for eq:counterexample-nonlipschitz: exact membership in the source
objective's original initial sublevel. -/
theorem mem_initialLevelSet (p : Parameters) (κ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ initialLevelSet p κ ↔ p.objective κ x ≤ p.objective κ (p.point 0) := by
  rfl

/-- Helper for eq:counterexample-nonlipschitz: radial monotonicity and the exact
quadratic endpoint values keep the same source orbit in its initial sublevel. -/
theorem ObjectiveEstimates.points_mem_initialLevelSet {p : Parameters} {κ ε H : ℝ}
    (h : ObjectiveEstimates p κ ε H) (hr : ∀ k, 0 ≤ p.radius k)
    (hanti : Antitone p.radius) (k : ℕ) : p.point k ∈ initialLevelSet p κ := by
  rw [mem_initialLevelSet, (h.endpoints k).1, (h.endpoints 0).1]
  have hsquare := pow_le_pow_left₀ (hr k) (hanti (Nat.zero_le k)) 2
  linarith

/-- Helper for eq:counterexample-nonlipschitz: strong convexity makes the source
objective's original initial sublevel convex. -/
theorem ObjectiveEstimates.convex_initialLevelSet {p : Parameters} {κ ε H : ℝ}
    (h : ObjectiveEstimates p κ ε H) (hε : ε < 1) :
    Convex ℝ (initialLevelSet p κ) := by
  have hconvex : ConvexOn ℝ Set.univ (p.objective κ) :=
    strongConvexOn_zero.mp (StrongConvexOn.mono (sub_pos.mpr hε).le h.strongConvex)
  have hsublevel := hconvex.convex_le (p.objective κ (p.point 0))
  simpa only [Set.mem_univ, true_and, initialLevelSet] using hsublevel

/-- Helper for eq:counterexample-nonlipschitz: the exact actual even secant
residual ratio for an arbitrary candidate Hessian exponent. -/
def evenResidualRatio (p : Parameters) (κ β' : ℝ) (j : ℕ) : ℝ :=
  ‖gradient (p.objective κ) (p.point (2 * j + 1)) -
      gradient (p.objective κ) (p.point (2 * j)) -
      hessian (p.objective κ) (p.point (2 * j))
        (p.point (2 * j + 1) - p.point (2 * j))‖ /
    ‖p.point (2 * j + 1) - p.point (2 * j)‖ ^ (1 + β')

/-- Helper for eq:counterexample-nonlipschitz: at every actual even step the
source secant residual is exactly the unchanged odd interpolation coefficient. -/
theorem evenResidualRatio_eq_coefficient (p : Parameters) (κ β' : ℝ)
    (hg : InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction) (j : ℕ) :
    evenResidualRatio p κ β' j = ‖p.correction (2 * j + 1)‖ /
      ‖p.point (2 * j + 1) - p.point (2 * j)‖ ^ (1 + β') := by
  rw [evenResidualRatio, p.objective_def,
    HolderSharpness.gradientRemainder_objective_centers hg (2 * j) (2 * j + 1)
      (p.correction_even j)]

/-- Helper for eq:counterexample-nonlipschitz: the actual even secant
residual ratios diverge for every exponent above `p.beta`, using the same odd
corrections and actual point displacements as the interpolation construction. -/
theorem evenResidualRatio_tendsto_atTop (p : Parameters) (κ : ℝ)
    (hβ : 0 < p.beta) (hstart : 0 < p.startIndex)
    (hg : InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction)
    {c U β' : ℝ} (hc : 0 < c) (hU : 0 < U) (hβ' : p.beta < β')
    (hupper : ∀ j, ‖p.point (2 * j + 1) - p.point (2 * j)‖ ≤
      U * scale p.beta p.startIndex j)
    (hcoefficient : ∀ j, c * scale p.beta p.startIndex j ^ (1 + p.beta) ≤
      ‖p.correction (2 * j + 1)‖) :
    Tendsto (evenResidualRatio p κ β') atTop atTop := by
  have hexponent : 0 ≤ 1 + β' := by
    linarith
  have hratio := HolderSharpness.powerScaleRatio_tendsto_atTop
    (fun j ↦ scale_pos p.beta hstart j) (scale_tendsto_zero hβ p.startIndex)
    hc hU hβ' hexponent (evenStep_pos p κ hg) hcoefficient hupper
  simpa only [funext (evenResidualRatio_eq_coefficient p κ β' hg)] using hratio

/-- Helper for thm:main: the actual
explicit source objective has no Hessian Hölder bound at any exponent larger
than `p.beta` on its unchanged original initial sublevel set. -/
theorem ObjectiveEstimates.no_higherHolder_initialLevelSet {p : Parameters} {κ ε H : ℝ}
    (h : ObjectiveEstimates p κ ε H) (hβ : 0 < p.beta) (hstart : 0 < p.startIndex)
    (hε : ε < 1) (hr : ∀ k, 0 ≤ p.radius k) (hanti : Antitone p.radius)
    {c U β' : ℝ} (hc : 0 < c) (hU : 0 < U) (hβ' : p.beta < β')
    (hupper : ∀ j, ‖p.point (2 * j + 1) - p.point (2 * j)‖ ≤
      U * scale p.beta p.startIndex j)
    (hcoefficient : ∀ j, c * scale p.beta p.startIndex j ^ (1 + p.beta) ≤
      ‖p.correction (2 * j + 1)‖) :
    ¬ ∃ C ≥ 0, ∀ x ∈ initialLevelSet p κ, ∀ y ∈ initialLevelSet p κ,
      ‖hessian (p.objective κ) x - hessian (p.objective κ) y‖ ≤ C * ‖x - y‖ ^ β' := by
  have hβ'nonneg : 0 ≤ β' := (hβ.trans hβ').le
  have hnot := HolderSharpness.not_holderHessianOn_objective_of_powerScaleCoefficients
    h.geometry (h.convex_initialLevelSet hε)
    (fun j ↦ h.points_mem_initialLevelSet hr hanti (2 * j))
    (fun j ↦ h.points_mem_initialLevelSet hr hanti (2 * j + 1))
    (fun j ↦ scale_pos p.beta hstart j) (scale_tendsto_zero hβ p.startIndex)
    hc hU hβ' hβ'nonneg (evenStep_pos p κ h.geometry) hupper p.correction_even hcoefficient
  rwa [← p.objective_def] at hnot

/-- Helper for lem:polar-geometry: the actual source polar points coincide
with the generic geometric points at their unchanged radii and angles. -/
theorem points_eq_geometry (p : Parameters) : p.point = Geometry.point p.radius p.angle := by
  funext k
  rw [p.point_def, Geometry.point_def]

/-- Helper for lem:polar-interpolation: the perturbation Hessian norm equals
the actual objective's Hessian deviation from identity. -/
theorem norm_perturbationHessian_eq (p : Parameters) (κ : ℝ)
    (hg : InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖fderiv ℝ (fderiv ℝ
      (InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction)) x‖ =
      ‖hessian (p.objective κ) x - 1‖ := by
  rw [p.objective_def, hessian_def, InterpolationSum.hessian_objective hg,
    add_sub_cancel_left, norm_fderiv_gradient_eq_norm_fderiv_fderiv]

/-- Helper for lem:polar-geometry and lem:polar-interpolation: the complete
uniform separation, step-size and perturbation-power conclusions for the actual source. -/
structure SourceGeometricData (p : Parameters) (κ s U C : ℝ) : Prop where
  /-- Helper for eq:polar-separation: all distinct actual points are separated
  at the larger scale. -/
  separation : ∀ k m : ℕ, k ≠ m →
    s * max (scale p.beta p.startIndex (k / 2)) (scale p.beta p.startIndex (m / 2)) ≤
      ‖p.point m - p.point k‖
  /-- Helper for eq:polar-orders: actual steps have the linear source lower bound. -/
  step_lower : ∀ k,
    s * scale p.beta p.startIndex (k / 2) ≤ ‖p.point (k + 1) - p.point k‖
  /-- Helper for eq:polar-orders: actual steps have the linear source upper bound. -/
  step_upper : ∀ k,
    ‖p.point (k + 1) - p.point k‖ ≤ U * scale p.beta p.startIndex (k / 2)
  /-- Helper for eq:polar-interpolation-bound: the uniform perturbation Hessian
  is bounded by a fixed constant times the initial scale to power `p.beta`. -/
  perturbation_bound : ∀ x,
    ‖fderiv ℝ (fderiv ℝ
      (InterpolationSum.perturbation p.point (p.supportRadius κ) p.correction)) x‖ ≤
        C * scale p.beta p.startIndex 0 ^ p.beta

/-- Helper for thm:main: complete source data for the exact objective and the
same actual orbit, before its canonical DFP certificate is packaged. -/
structure SourceObjectiveData (p : Parameters) (j0 : ℕ) (N M κ ε H : ℝ) : Prop where
  /-- Helper for lem:polar-geometry: the same actual radius and continuation
  certificate is retained for later sequence comparisons. -/
  radial : ∃ B > 0, ∃ K > 0, ∃ c > 0, ∃ U > 0,
    RadiusProducts.SourceRadialData p j0 N M B K c U
  /-- Helper for lem:polar-geometry: the full proved geometric certificate
  retains the same actual source parameters, starting index and tube widths. -/
  actualGeometry : ∃ B > 0, ∃ K > 0, ∃ c > 0, ∃ U > 0,
    ∃ a > 0, ∃ b > 0, ∃ s > 0, ∃ V > 0,
      ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V
  /-- Helper for eq:polar-physical-step: every actual source stage has positive sine. -/
  sine_pos : ∀ k, 0 < Real.sin ((p.withStartIndex j0).angleIncrement k)
  /-- Helper for lem:polar-interpolation: the exact source objective has all
  requested jets and bounds. -/
  objectiveEstimates : ObjectiveEstimates (p.withStartIndex j0) κ ε H
  /-- Helper for lem:polar-geometry: source point and perturbation power bounds are retained. -/
  geometric : ∃ s > 0, ∃ U > 0, ∃ C ≥ 0,
    SourceGeometricData (p.withStartIndex j0) κ s U C
  /-- Helper for thm:main: the full cluster set of the same actual points is the unit circle. -/
  clusterSet : {x | MapClusterPt x atTop (p.withStartIndex j0).point} = Metric.sphere 0 1
  /-- Helper for thm:main: actual endpoint gradient norms converge to one. -/
  gradientNorm_tendsto : Tendsto
    (fun k ↦ ‖gradient ((p.withStartIndex j0).objective κ) ((p.withStartIndex j0).point k)‖)
    atTop (𝓝 1)
  /-- Helper for thm:main: every higher Hessian Hölder exponent fails on the original sublevel. -/
  no_higherHolder_initialLevelSet : ∀ β' : ℝ, p.beta < β' →
    ¬ ∃ C ≥ 0, ∀ x ∈ initialLevelSet (p.withStartIndex j0) κ,
      ∀ y ∈ initialLevelSet (p.withStartIndex j0) κ,
        ‖hessian ((p.withStartIndex j0).objective κ) x -
          hessian ((p.withStartIndex j0).objective κ) y‖ ≤ C * ‖x - y‖ ^ β'
  /-- Helper for eq:counterexample-nonlipschitz: the same actual even residual ratios diverge. -/
  residual_tendsto : ∀ β' : ℝ, p.beta < β' →
    Tendsto (evenResidualRatio (p.withStartIndex j0) κ β') atTop atTop

/-- Helper for lem:polar-continuation: the complete objective package retains
the original actual trajectory certificate. -/
theorem SourceObjectiveData.trajectory {p : Parameters} {j0 : ℕ} {N M κ ε H : ℝ}
    (h : SourceObjectiveData p j0 N M κ ε H) : Continuation.TrajectoryBounds p j0 N M := by
  obtain ⟨B, hB, K, hK, c, hc, U, hU, hradial⟩ := h.radial
  exact hradial.trajectory

/-- Helper for eq:polar-physical-step: the complete objective package retains
feasibility of every actual raw source stage. -/
theorem SourceObjectiveData.feasible {p : Parameters} {j0 : ℕ} {N M κ ε H : ℝ}
    (h : SourceObjectiveData p j0 N M κ ε H) :
    ∀ k, Continuation.RawFeasible (p.withStartIndex j0) k := by
  obtain ⟨B, hB, K, hK, c, hc, U, hU, hradial⟩ := h.radial
  exact hradial.feasible

/-- Helper for eq:polar-radii: the complete objective package retains
strict positivity of every actual source radius factor. -/
theorem SourceObjectiveData.factors {p : Parameters} {j0 : ℕ} {N M κ ε H : ℝ}
    (h : SourceObjectiveData p j0 N M κ ε H) :
    ∀ k, 1 < (p.withStartIndex j0).radiusRatio k := by
  obtain ⟨B, hB, K, hK, c, hc, U, hU, hradial⟩ := h.radial
  exact hradial.factors

/-- Helper for eq:polar-radii: the complete objective package retains
summability of the actual source cycle logarithms. -/
theorem SourceObjectiveData.logarithms {p : Parameters} {j0 : ℕ} {N M κ ε H : ℝ}
    (h : SourceObjectiveData p j0 N M κ ε H) :
    Summable (fun j ↦ Real.log ((p.withStartIndex j0).radiusRatio (2 * j) *
      (p.withStartIndex j0).radiusRatio (2 * j + 1))) := by
  obtain ⟨B, hB, K, hK, c, hc, U, hU, hradial⟩ := h.radial
  exact hradial.logarithms

/-- Helper for thm:main: prescribed multiplier and radius limits give the
exact actual endpoint gradient-norm limit. -/
theorem gradientNorm_tendsto_one {p : Parameters} {j0 : ℕ} {N M B K c U κ ε H : ℝ}
    (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (hr : RadiusProducts.SourceRadialData p j0 N M B K c U)
    (hobjective : ObjectiveEstimates (p.withStartIndex j0) κ ε H) :
    Tendsto (fun k ↦ ‖gradient ((p.withStartIndex j0).objective κ)
      ((p.withStartIndex j0).point k)‖) atTop (𝓝 1) := by
  have hzeta := hr.trajectory.zeta_tendsto_one hβ hβone
  have hnorm (k : ℕ) :
      ‖gradient ((p.withStartIndex j0).objective κ) ((p.withStartIndex j0).point k)‖ =
        (p.withStartIndex j0).zeta k * (p.withStartIndex j0).radius k := by
    rw [(hobjective.endpoints k).2.1, Parameters.gradients_def, norm_smul,
      Real.norm_eq_abs, abs_of_pos ((p.withStartIndex j0).zeta_pos k),
      norm_point _ k (zero_lt_one.trans (hr.radii.above_one k)).le]
  simpa only [funext hnorm, one_mul] using hzeta.mul hr.radii.tendsto_one

/-- Helper for lem:polar-interpolation: the actual geometric separation and
radial-excess bounds prove the exact cutoff-sum geometry with no regularity premise. -/
theorem interpolationGeometry_of_source_separation (p : Parameters)
    (hβ : 0 < p.beta) (hstart : 0 < p.startIndex)
    {κ s L A : ℝ} (hκ : 0 < κ) (hκsep : 2 * κ ≤ s)
    (hκmargin : 2 * κ * scale p.beta p.startIndex 0 ^ p.beta ≤ L)
    (hr : ∀ k, 1 ≤ p.radius k) (hradius : Tendsto p.radius atTop (𝓝 1))
    (hsep : ∀ k m : ℕ, k ≠ m →
      s * max (scale p.beta p.startIndex (k / 2)) (scale p.beta p.startIndex (m / 2)) ≤
        ‖p.point m - p.point k‖)
    (hradial : ∀ k, L * scale p.beta p.startIndex (k / 2) ^ (1 - p.beta) ≤ p.radius k - 1)
    (hcoefficient : ∀ k, ‖p.correction k‖ ≤
      A * scale p.beta p.startIndex (k / 2) ^ (1 + p.beta)) :
    InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction := by
  have hsepDistance (k m : ℕ) (hkm : k ≠ m) :
      s * max (scale p.beta p.startIndex (k / 2)) (scale p.beta p.startIndex (m / 2)) ≤
        dist (p.point k) (p.point m) := by
    rw [dist_eq_norm, norm_sub_rev]
    exact hsep k m hkm
  constructor
  · intro k
    rw [p.supportRadius_def]
    exact mul_pos hκ (scale_pos p.beta hstart (k / 2))
  · rw [funext (p.supportRadius_def κ)]
    exact Geometry.supportBalls_disjoint_of_separation
      (fun k ↦ scale_nonneg p.beta p.startIndex (k / 2)) hκ.le hκsep hsepDistance
  · exact hradius.congr' (Filter.Eventually.of_forall
      (fun k ↦ (norm_point p k (zero_le_one.trans (hr k))).symm))
  · intro k
    rw [p.supportRadius_def, norm_point p k (zero_le_one.trans (hr k))]
    exact Geometry.radius_margin_of_power_lower hβ hstart hκ.le hκmargin hradial k
  · simp only [p.supportRadius_def]
    exact Geometry.coefficient_div_radius_tendsto_zero
      (fun k ↦ scale_pos p.beta hstart (k / 2))
      ((scale_tendsto_zero hβ p.startIndex).comp AngularGeometry.halfIndex_tendsto)
      hκ hβ hcoefficient

/-- Helper for lem:polar-interpolation: every positive real power of the
initial prescribed scale tends to zero as its starting index increases. -/
theorem scale_start_rpow_tendsto_zero {β q : ℝ} (hβ : 0 < β) (hq : 0 < q) :
    Tendsto (fun j0 : ℕ ↦ scale β j0 0 ^ q) atTop (𝓝 0) := by
  have hexponent := div_pos hq (add_pos zero_lt_one hβ)
  simpa only [scale_rpow, Nat.add_zero, neg_div, Function.comp_def] using
    (tendsto_rpow_neg_atTop hexponent).comp tendsto_natCast_atTop_atTop

/-- Helper for thm:main: the exact interpolation certificate, retained source
radial data and quantitative odd corrections prove the full same-objective package. -/
theorem sourceObjectiveDataOfEstimates (p : Parameters) (j0 : ℕ)
    {N M B K c U κ ε H s Ustep Cobj cCorr : ℝ}
    (hβ : 0 < p.beta) (hβone : p.beta < 1) (hstart : 0 < j0) (hε : ε < 1)
    (hB : 0 < B) (hK : 0 < K) (hc : 0 < c) (hU : 0 < U)
    (hs : 0 < s) (hUstep : 0 < Ustep) (hCobj : 0 ≤ Cobj) (hcCorr : 0 < cCorr)
    (hr : RadiusProducts.SourceRadialData p j0 N M B K c U)
    (hActualGeometry : ∃ B > 0, ∃ K > 0, ∃ c > 0, ∃ U > 0,
      ∃ a > 0, ∃ b > 0, ∃ s > 0, ∃ V > 0,
        ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hsin : ∀ k, 0 < Real.sin ((p.withStartIndex j0).angleIncrement k))
    (hobjective : ObjectiveEstimates (p.withStartIndex j0) κ ε H)
    (hgeometric : SourceGeometricData (p.withStartIndex j0) κ s Ustep Cobj)
    (hcluster : {x | MapClusterPt x atTop (p.withStartIndex j0).point} = Metric.sphere 0 1)
    (hcoefficient : ∀ j, cCorr * scale p.beta j0 j ^ (1 + p.beta) ≤
      ‖(p.withStartIndex j0).correction (2 * j + 1)‖) :
    SourceObjectiveData p j0 N M κ ε H := by
  let q := p.withStartIndex j0
  have hqβ : 0 < q.beta := by
    simpa only [q, p.withStartIndex_beta] using hβ
  have hqstart : 0 < q.startIndex := by
    simpa only [q, p.withStartIndex_startIndex] using hstart
  have hrNonneg (k : ℕ) : 0 ≤ q.radius k := (zero_lt_one.trans (hr.radii.above_one k)).le
  have hupper (j : ℕ) : ‖q.point (2 * j + 1) - q.point (2 * j)‖ ≤
      Ustep * scale q.beta q.startIndex j := by
    have hhalf : 2 * j / 2 = j := by
      omega
    simpa only [hhalf] using hgeometric.step_upper (2 * j)
  have hcoefficientQ (j : ℕ) : cCorr * scale q.beta q.startIndex j ^ (1 + q.beta) ≤
      ‖q.correction (2 * j + 1)‖ := by
    simpa only [q, p.withStartIndex_beta, p.withStartIndex_startIndex] using hcoefficient j
  refine
    { radial := ⟨B, hB, K, hK, c, hc, U, hU, hr⟩
      actualGeometry := hActualGeometry
      sine_pos := hsin
      objectiveEstimates := hobjective
      geometric := ⟨s, hs, Ustep, hUstep, Cobj, hCobj, hgeometric⟩
      clusterSet := hcluster
      gradientNorm_tendsto := gradientNorm_tendsto_one hβ hβone hr hobjective
      no_higherHolder_initialLevelSet := ?_
      residual_tendsto := ?_ }
  · intro β' hβ'
    have hβq' : q.beta < β' := by
      simpa only [q, p.withStartIndex_beta] using hβ'
    exact hobjective.no_higherHolder_initialLevelSet hqβ hqstart hε hrNonneg
      hr.radii.strictAnti.antitone hcCorr hUstep hβq' hupper hcoefficientQ
  · intro β' hβ'
    have hβq' : q.beta < β' := by
      simpa only [q, p.withStartIndex_beta] using hβ'
    exact evenResidualRatio_tendsto_atTop q κ hqβ hqstart hobjective.geometry
      hcCorr hUstep hβq' hupper hcoefficientQ

/-- Helper for lem:polar-interpolation: uniform actual source geometry fixes
one support coefficient and one Hölder constant before the final starting-index
choice. Every sufficiently large start then gives the complete exact objective
and a common separation, step-size and Hessian-power certificate. -/
theorem existsSourceObjectiveData_of_uniformGeometry (p : Parameters)
    (hβ : 0 < p.beta) (hβone : p.beta < 1) {ε N M B K c U s Ustep : ℝ}
    (hεpos : 0 < ε) (hε : ε < 1) (hM : 0 ≤ M) (hB : 0 < B)
    (hK : 0 < K) (hc : 0 < c) (hU : 0 < U) (hs : 0 < s) (hUstep : 0 < Ustep)
    (J0 : ℕ) (hJ0 : 0 < J0)
    (hradial : ∀ j0 : ℕ, J0 ≤ j0 → RadiusProducts.SourceRadialData p j0 N M B K c U)
    (hActualGeometry : ∀ j0 : ℕ, J0 ≤ j0 →
      ∃ B > 0, ∃ K > 0, ∃ c > 0, ∃ U > 0,
        ∃ a > 0, ∃ b > 0, ∃ s > 0, ∃ V > 0,
          ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V)
    (hsin : ∀ j0 : ℕ, J0 ≤ j0 → ∀ k,
      0 < Real.sin ((p.withStartIndex j0).angleIncrement k))
    (hsep : ∀ j0 : ℕ, J0 ≤ j0 → ∀ k m : ℕ, k ≠ m →
      s * max (scale p.beta j0 (k / 2)) (scale p.beta j0 (m / 2)) ≤
        ‖(p.withStartIndex j0).point m - (p.withStartIndex j0).point k‖)
    (hupper : ∀ j0 : ℕ, J0 ≤ j0 → ∀ k,
      ‖(p.withStartIndex j0).point (k + 1) - (p.withStartIndex j0).point k‖ ≤
        Ustep * scale p.beta j0 (k / 2))
    (hcluster : ∀ j0 : ℕ, J0 ≤ j0 →
      {x | MapClusterPt x atTop (p.withStartIndex j0).point} = Metric.sphere 0 1) :
    ∃ κ > 0, ∃ H ≥ 0, ∃ Cobj ≥ 0, ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 →
      SourceObjectiveData p j0 N M κ ε H ∧
        SourceGeometricData (p.withStartIndex j0) κ s Ustep Cobj := by
  obtain ⟨Cχ, hCχ, hcutoff⟩ := InterpolationBounds.exists_objective_bounds_of_powerScale
    (E := EuclideanSpace ℝ (Fin 2))
  obtain ⟨cCorr, hcCorr, A, hA, δ, hδ, hcorrection⟩ :=
    RadiusBounds.correctionBoundsOfActualSlowTube p hβ hβone hM hB
  let κ := s / 4
  let H := 2 * Cχ * (A * κ ^ (-(1 + p.beta)))
  let Cobj := Cχ * (A / κ)
  let L := RadiusProducts.principalCoefficient p.beta
    (RadiusBounds.radiusLimitCoefficient p 0) (RadiusBounds.radiusLimitCoefficient p 1) / 2
  have hfour : (0 : ℝ) < 4 := by
    norm_num
  have hκ : 0 < κ := div_pos hs hfour
  have hκsep : 2 * κ ≤ s := by
    dsimp only [κ]
    linarith only [hs]
  have hH : 0 ≤ H := by
    positivity
  have hCobj : 0 ≤ Cobj := by
    positivity
  have hL : 0 < L := by
    dsimp only [L]
    rw [RadiusProducts.principalCoefficient_def]
    exact half_pos (mul_pos
      (div_pos (add_pos zero_lt_one hβ) (sub_pos.mpr hβone))
      (add_pos (RadiusBounds.radiusLimitCoefficient_pos p hβ 0)
        (RadiusBounds.radiusLimitCoefficient_pos p hβ 1)))
  have hpower := scale_start_rpow_tendsto_zero hβ hβ
  have hslow := scale_start_rpow_tendsto_zero hβ (sub_pos.mpr hβone)
  have hmarginLimit : Tendsto (fun j0 : ℕ ↦ 2 * κ * scale p.beta j0 0 ^ p.beta)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hpower.const_mul (2 * κ)
  have hhessianLimit : Tendsto (fun j0 : ℕ ↦ Cobj * scale p.beta j0 0 ^ p.beta)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hpower.const_mul Cobj
  have heventually : ∀ᶠ j0 : ℕ in atTop, J0 ≤ j0 ∧
      scale p.beta j0 0 ^ (1 - p.beta) < δ ∧
      2 * κ * scale p.beta j0 0 ^ p.beta ≤ L ∧
      Cobj * scale p.beta j0 0 ^ p.beta ≤ ε := by
    filter_upwards [eventually_ge_atTop J0, hslow.eventually (Iio_mem_nhds hδ),
      hmarginLimit.eventually (Iio_mem_nhds hL),
      hhessianLimit.eventually (Iio_mem_nhds hεpos)] with j0 hj0 hc0 hm he
    exact ⟨hj0, hc0, hm.le, he.le⟩
  obtain ⟨J, hJ⟩ := eventually_atTop.mp heventually
  refine ⟨κ, hκ, H, hH, Cobj, hCobj, max J J0, hJ0.trans_le (le_max_right _ _), ?_⟩
  intro j0 hj0
  obtain ⟨hj00, hsmallCorrection, hmargin, hsmallHessian⟩ :=
    hJ j0 ((le_max_left J J0).trans hj0)
  let q := p.withStartIndex j0
  have hstart : 0 < j0 := hJ0.trans_le hj00
  have hqβeq : q.beta = p.beta := p.withStartIndex_beta j0
  have hqStarteq : q.startIndex = j0 := p.withStartIndex_startIndex j0
  have hqβ : 0 < q.beta := hqβeq ▸ hβ
  have hqβone : q.beta < 1 := hqβeq ▸ hβone
  have hqstart : 0 < q.startIndex := hqStarteq ▸ hstart
  have hr := hradial j0 hj00
  have hslowBound (j : ℕ) : |(q.normalizedEvenState j).1 - p.gammaStar| ≤
      M * scale p.beta j0 j ^ (1 - p.beta) := by
    simpa only [Continuation.slowError_def, Continuation.stateAt_def] using
      hr.trajectory.slow_bound j
  have hradiusBound (k : ℕ) : 1 ≤ q.radius k ∧ q.radius k ≤ B :=
    ⟨(hr.radii.above_one k).le, hr.radii.upper k⟩
  obtain ⟨hcoefficient, hcoefficientLower⟩ :=
    hcorrection j0 hstart hsmallCorrection hslowBound hradiusBound
  have hcoefficientQ : ∀ k, ‖q.correction k‖ ≤
      A * scale q.beta q.startIndex (k / 2) ^ (1 + q.beta) := by
    simpa only [hqβeq, hqStarteq] using hcoefficient
  have hsepQ : ∀ k m : ℕ, k ≠ m →
      s * max (scale q.beta q.startIndex (k / 2)) (scale q.beta q.startIndex (m / 2)) ≤
        ‖q.point m - q.point k‖ := by
    simpa only [hqβeq, hqStarteq] using hsep j0 hj00
  have hupperQ : ∀ k, ‖q.point (k + 1) - q.point k‖ ≤
      Ustep * scale q.beta q.startIndex (k / 2) := by
    simpa only [hqβeq, hqStarteq] using hupper j0 hj00
  have hmarginQ : 2 * κ * scale q.beta q.startIndex 0 ^ q.beta ≤ L := by
    simpa only [hqβeq, hqStarteq] using hmargin
  have hradialQ : ∀ k, L * scale q.beta q.startIndex (k / 2) ^ (1 - q.beta) ≤
      q.radius k - 1 := by
    simpa only [hqβeq, hqStarteq] using hr.radii.excess_lower
  have hg := interpolationGeometry_of_source_separation q hqβ hqstart hκ hκsep hmarginQ
    (fun k ↦ (hr.radii.above_one k).le) hr.radii.tendsto_one hsepQ hradialQ hcoefficientQ
  have hscaleUpper (k : ℕ) : scale q.beta q.startIndex (k / 2) ≤
      scale q.beta q.startIndex 0 := scale_antitone hqβ hqstart (Nat.zero_le _)
  obtain ⟨hcont, hHessian, hholder⟩ := hcutoff q.beta hqβ.le hqβone.le q.point
    (q.supportRadius κ) q.correction (fun k ↦ scale q.beta q.startIndex (k / 2)) κ A
    (scale q.beta q.startIndex 0) hg hκ hA.le (scale_pos q.beta hqstart 0)
    (fun k ↦ scale_pos q.beta hqstart (k / 2)) hscaleUpper
    (q.supportRadius_def κ) hcoefficientQ
  have hsmallHessianQ : Cobj * scale q.beta q.startIndex 0 ^ q.beta ≤ ε := by
    simpa only [hqβeq, hqStarteq] using hsmallHessian
  have hboundActual (x : EuclideanSpace ℝ (Fin 2)) : ‖hessian (q.objective κ) x - 1‖ ≤ ε := by
    rw [q.objective_def]
    exact (hHessian x).trans hsmallHessianQ
  have hholderActual (x y : EuclideanSpace ℝ (Fin 2)) :
      ‖hessian (q.objective κ) x - hessian (q.objective κ) y‖ ≤ H * ‖x - y‖ ^ q.beta := by
    rw [q.objective_def]
    simpa only [H, hqβeq] using hholder x y
  have hobjective := objectiveEstimatesOfBounds q κ ε H hg hε hH hboundActual hholderActual
  have hgeometric : SourceGeometricData q κ s Ustep Cobj := by
    refine ⟨hsepQ, ?_, hupperQ, ?_⟩
    · intro k
      have hkm : k ≠ k + 1 := by
        omega
      exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hs.le).trans (hsepQ k (k + 1) hkm)
    · intro x
      rw [norm_perturbationHessian_eq q κ hg x, q.objective_def]
      exact hHessian x
  have hsource := sourceObjectiveDataOfEstimates p j0 hβ hβone hstart hε
    hB hK hc hU hs hUstep hCobj hcCorr hr (hActualGeometry j0 hj00) (hsin j0 hj00)
    hobjective hgeometric (hcluster j0 hj00) hcoefficientLower
  exact ⟨hsource, hgeometric⟩

/-- lem:polar-interpolation. For the actual generalized source trajectory and
any prescribed near-identity accuracy, one fixed explicit cutoff construction
gives all endpoint and disk jets, a globally `p.beta`-Hölder Hessian, uniform
convexity and the unique minimizer at the origin. The same objective and orbit
have the exact initial-sublevel Hölder exponent and divergent even residual
ratios at every larger exponent. All geometric and Hessian-power constants
are fixed before the final starting index, with no feasibility premise. -/
theorem existsSourceObjectiveData (p : Parameters) (hβ : 0 < p.beta)
    (hβone : p.beta < 1) (ε : ℝ) (hεpos : 0 < ε) (hε : ε < 1) :
    ∃ N > 0, ∃ M > 0, ∃ κ > 0, ∃ H ≥ 0, ∃ s > 0, ∃ Ustep > 0, ∃ Cobj ≥ 0,
      ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 →
        SourceObjectiveData p j0 N M κ ε H ∧
          SourceGeometricData (p.withStartIndex j0) κ s Ustep Cobj := by
  obtain ⟨N, hN, M, hM, B, hB, K, hK, c, hc, U, hU,
    a, ha, b, hb, s, hs, V, hV, J0, hJ0, hgeometry⟩ :=
      ActualGeometry.existsSourceGeometry p hβ hβone
  have hcluster (j0 : ℕ) (hj0 : J0 ≤ j0) :
      {x | MapClusterPt x atTop (p.withStartIndex j0).point} = Metric.sphere 0 1 := by
    ext x
    simpa only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right] using
      (hgeometry j0 hj0).cluster x
  obtain ⟨κ, hκ, H, hH, Cobj, hCobj, J, hJ, hsource⟩ :=
    existsSourceObjectiveData_of_uniformGeometry p hβ hβone hεpos hε hM.le hB hK hc hU hs hV
      J0 hJ0 (fun j0 hj0 ↦ (hgeometry j0 hj0).radial)
      (fun j0 hj0 ↦ ⟨B, hB, K, hK, c, hc, U, hU,
        a, ha, b, hb, s, hs, V, hV, hgeometry j0 hj0⟩)
      (fun j0 hj0 ↦ (hgeometry j0 hj0).sine_pos)
      (fun j0 hj0 ↦ (hgeometry j0 hj0).separation)
      (fun j0 hj0 k ↦ ((hgeometry j0 hj0).steps k).2) hcluster
  exact ⟨N, hN, M, hM, κ, hκ, H, hH, s, hs, V, hV, Cobj, hCobj, J, hJ, hsource⟩

end DFP.Polar.General.Objective
