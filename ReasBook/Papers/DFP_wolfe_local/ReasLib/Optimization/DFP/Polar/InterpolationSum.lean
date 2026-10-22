/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.InterpolationBounds
public import ReasLib.Optimization.DFP.Polar.ScaleTails
public import ReasLib.Optimization.DFP.Polar.Realization
public import ReasLib.Analysis.Calculus.ShrinkingSupportFinsum
public import ReasLib.Analysis.Calculus.ContDiff.ZeroExtensionJets.EqOn
public import ReasLib.Analysis.Convex.HessianPerturbation.Interpolation
public import ReasLib.Topology.MetricSpace.Sphere

public section

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace DFP.Polar.InterpolationSum

variable {E : Type*} [NormedAddCommGroup E]

/-- Helper for lem:polar-interpolation and eq:polar-objective: the source
unit sphere, represented by the canonical metric sphere. -/
def unitSphere : Set E := Metric.sphere 0 1

/-- Helper for lem:polar-interpolation and eq:polar-objective: membership in
the source unit sphere is exactly the unit-norm condition. -/
theorem mem_unitSphere (x : E) : x ∈ unitSphere ↔ ‖x‖ = 1 := by
  simp only [unitSphere, Metric.mem_sphere, dist_zero_right]

/-- Helper for lem:polar-interpolation and eq:polar-objective: the unit
sphere is closed. -/
theorem isClosed_unitSphere : IsClosed (unitSphere (E := E)) := by
  exact Metric.isClosed_sphere

/-- Helper for lem:polar-interpolation and eq:polar-objective: approaching
the unit sphere from its complement, in the distance filter used for zero extension. -/
def boundaryFilter : Filter E :=
  Filter.comap (fun x ↦ Metric.infDist x (unitSphere (E := E))) (𝓝 (0 : ℝ)) ⊓
    Filter.principal (unitSphere (E := E))ᶜ

/-- Helper for lem:polar-interpolation and eq:polar-objective: distance to
the sphere tends to zero along the boundary filter. -/
theorem boundaryFilter_infDist_tendsto :
    Tendsto (fun x : E ↦ Metric.infDist x unitSphere) boundaryFilter (𝓝 0) := by
  exact tendsto_inf_left tendsto_comap

/-- Helper for lem:polar-interpolation and eq:polar-objective: the boundary
filter is restricted to points outside the unit sphere. -/
theorem eventually_boundary_compl :
    ∀ᶠ x : E in boundaryFilter, x ∈ (unitSphere (E := E))ᶜ := by
  exact (eventually_principal.mpr (fun x hx ↦ hx)).filter_mono inf_le_right

/-- Helper for lem:polar-interpolation and eq:polar-objective: geometric and
coefficient-decay premises for the exact cutoff correction family. This
certificate contains neither regularity nor any derivative-sum identity. -/
structure Geometry (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) : Prop where
  /-- Helper for lem:polar-interpolation: every exact correction radius is positive. -/
  radius_pos : ∀ k, 0 < ρ k
  /-- Helper for lem:polar-interpolation: the source OPEN support balls are disjoint. -/
  disjoint_open : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (ρ k))
  /-- Helper for lem:polar-interpolation: the center norms converge to the unit sphere. -/
  centers_norm : Tendsto (fun k ↦ ‖c k‖) atTop (𝓝 1)
  /-- Helper for lem:polar-interpolation: closed supports retain a positive radial margin. -/
  margin : ∀ k, 1 + 2 * ρ k ≤ ‖c k‖
  /-- Helper for lem:polar-interpolation: coefficient-to-radius ratios decay to zero. -/
  ratio_decay : Tendsto (fun k ↦ ‖a k‖ / ρ k) atTop (𝓝 0)

/-- Helper for lem:polar-interpolation and eq:polar-objective: the support
margin and radial convergence force the actual support radii to shrink. -/
theorem Geometry.radius_tendsto_zero {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) : Tendsto ρ atTop (𝓝 0) := by
  have hupper : Tendsto (fun k ↦ (‖c k‖ - 1) / 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, zero_div] using (h.centers_norm.sub_const 1).div_const 2
  apply squeeze_zero (fun k ↦ (h.radius_pos k).le) _ hupper
  intro k
  linarith [h.margin k]

/-- Helper for lem:polar-interpolation and eq:polar-objective: every center
cluster point belongs to the source unit sphere. -/
theorem Geometry.cluster_mem_sphere {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) {x : E} (hx : MapClusterPt x atTop c) : x ∈ unitSphere := by
  obtain ⟨s, hs, hlimit⟩ := hx.tendsto_subseq
  have hnorm : Tendsto (fun n ↦ ‖c (s n)‖) atTop (𝓝 ‖x‖) :=
    continuous_norm.continuousAt.tendsto.comp hlimit
  have hunit : Tendsto (fun n ↦ ‖c (s n)‖) atTop (𝓝 1) :=
    h.centers_norm.comp hs.tendsto_atTop
  exact (mem_unitSphere x).mpr (tendsto_nhds_unique hnorm hunit)

/-- Helper for lem:polar-interpolation and eq:polar-objective: every closed
support ball stays outside the unit ball with an additional radial margin ρ. -/
theorem Geometry.closedBall_norm_margin {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) {y : E} (hy : y ∈ Metric.closedBall (c k) (ρ k)) :
    1 + ρ k ≤ ‖y‖ := by
  have hdist : ‖y - c k‖ ≤ ρ k := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
  have hnorm := norm_sub_norm_le (c k) y
  rw [norm_sub_rev (c k) y] at hnorm
  linarith [h.margin k]

/-- Helper for lem:polar-interpolation and eq:polar-objective: every point
inside the unit ball lies outside every correction support sphere. -/
theorem Geometry.radius_le_norm_sub_of_norm_le_one
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a)
    (k : ℕ) {x : E} (hx : ‖x‖ ≤ 1) : ρ k ≤ ‖x - c k‖ := by
  have hnorm := norm_sub_norm_le (c k) x
  rw [norm_sub_rev (c k) x] at hnorm
  linarith [h.margin k, h.radius_pos k]

variable [InnerProductSpace ℝ E]

/-- Helper for lem:polar-interpolation and eq:polar-objective: the exact
source cutoff-times-affine correction, with unchanged center and radius. -/
def bump (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (k : ℕ) : E → ℝ :=
  ExplicitCutoff.correction (c k) (ρ k) (a k)

/-- Helper for lem:polar-interpolation and eq:polar-objective: evaluation of
the exact correction in the source infinite sum. -/
theorem bump_apply (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (k : ℕ) (x : E) :
    bump c ρ a k x = ExplicitCutoff.chi ((ρ k)⁻¹ • (x - c k)) * inner ℝ (a k) (x - c k) := by
  exact ExplicitCutoff.correction_apply (c k) (ρ k) (a k) x

/-- eq:polar-objective (exact generic correction sum). The pointwise finsum
of the manuscript's exact corrections; summability is proved separately. -/
def perturbation (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (x : E) : ℝ :=
  ∑ᶠ k, bump c ρ a k x

/-- Helper for lem:polar-interpolation and eq:polar-objective: the defining
pointwise finite sum of the exact perturbation. -/
theorem perturbation_apply (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (x : E) :
    perturbation c ρ a x = ∑ᶠ k, bump c ρ a k x := by
  rfl

/-- Helper for lem:polar-interpolation and eq:polar-objective: the source
objective is the half squared norm plus the exact correction sum. -/
def objective (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (x : E) : ℝ :=
  (1 / 2 : ℝ) * ‖x‖ ^ 2 + perturbation c ρ a x

/-- Helper for lem:polar-interpolation and eq:polar-objective: evaluation of
the exact quadratic-plus-correction objective. -/
theorem objective_apply (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (x : E) :
    objective c ρ a x = (1 / 2 : ℝ) * ‖x‖ ^ 2 + perturbation c ρ a x := by
  rfl

/-- Helper for lem:polar-interpolation and eq:polar-objective: each exact
bump is smooth of every order. -/
theorem contDiff_bump (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (k : ℕ) :
    ContDiff ℝ ∞ (bump c ρ a k) := by
  exact ExplicitCutoff.contDiff_correction (c k) (ρ k) (a k)

/-- Helper for lem:polar-interpolation and eq:polar-objective: each exact
bump retains its correct CLOSED topological support bound. -/
theorem tsupport_bump_subset_closedBall {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) :
    tsupport (bump c ρ a k) ⊆ Metric.closedBall (c k) (ρ k) := by
  exact ExplicitCutoff.tsupport_correction_subset_closedBall (c k) (ρ k) (a k) (h.radius_pos k)

/-- Helper for lem:polar-interpolation and eq:polar-objective: every bump
and all of its jets vanish on and outside its closed support boundary. -/
theorem iteratedFDeriv_bump_eq_zero {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (n k : ℕ) {x : E} (hx : ρ k ≤ ‖x - c k‖) :
    iteratedFDeriv ℝ n (bump c ρ a k) x = 0 := by
  exact InterpolationBounds.iteratedFDeriv_correction_eq_zero_of_radius_le_norm_sub
    n (c k) (ρ k) (a k) x (h.radius_pos k) hx

/-- Helper for lem:polar-interpolation and eq:polar-objective: the exact
bump value vanishes on and outside its support sphere. -/
theorem bump_eq_zero_of_radius_le {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) {x : E} (hx : ρ k ≤ ‖x - c k‖) : bump c ρ a k x = 0 := by
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ), iteratedFDeriv_bump_eq_zero h 0 k hx, norm_zero]

/-- Helper for lem:polar-interpolation and eq:polar-objective: the exact
bump's first derivative vanishes on and outside its support sphere. -/
theorem fderiv_bump_eq_zero_of_radius_le {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) {x : E} (hx : ρ k ≤ ‖x - c k‖) :
    fderiv ℝ (bump c ρ a k) x = 0 := by
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), iteratedFDeriv_bump_eq_zero h 1 k hx, norm_zero]

/-- Helper for lem:polar-interpolation and eq:polar-objective: the exact
bump's Hessian vanishes on and outside its support sphere. -/
theorem secondFDeriv_bump_eq_zero_of_radius_le {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) {x : E} (hx : ρ k ≤ ‖x - c k‖) :
    fderiv ℝ (fderiv ℝ (bump c ρ a k)) x = 0 := by
  exact InterpolationBounds.hessian_correction_eq_zero_of_radius_le_norm_sub
    (c k) (ρ k) (a k) x (h.radius_pos k) hx

/-- Helper for lem:polar-interpolation and eq:polar-objective: the function
supports of exact bump values lie in their OPEN balls, including boundary flatness. -/
theorem support_bump_subset_ball {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) :
    Function.support (bump c ρ a k) ⊆ Metric.ball (c k) (ρ k) := by
  intro x hx
  by_contra hout
  have hnorm : ρ k ≤ ‖x - c k‖ := by
    simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hout
  exact hx (bump_eq_zero_of_radius_le h k hnorm)

/-- Helper for lem:polar-interpolation and eq:polar-objective: the first-jet
function support lies in the same OPEN ball, although topological support is closed. -/
theorem support_fderiv_bump_subset_ball {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) :
    Function.support (fderiv ℝ (bump c ρ a k)) ⊆ Metric.ball (c k) (ρ k) := by
  intro x hx
  by_contra hout
  have hnorm : ρ k ≤ ‖x - c k‖ := by
    simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hout
  exact hx (fderiv_bump_eq_zero_of_radius_le h k hnorm)

/-- Helper for lem:polar-interpolation and eq:polar-objective: the second-jet
function support lies in the same OPEN ball. -/
theorem support_secondFDeriv_bump_subset_ball {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) :
    Function.support (fderiv ℝ (fderiv ℝ (bump c ρ a k))) ⊆ Metric.ball (c k) (ρ k) := by
  exact InterpolationBounds.support_hessian_correction_subset_ball (c k) (ρ k) (a k)
    (h.radius_pos k)

/-- Helper for lem:polar-interpolation and eq:polar-objective: at any point,
a family with disjoint containing sets has at most one nonzero value. -/
theorem support_apply_subsingleton {X G : Type*} [Zero G] (f : ℕ → X → G)
    (B : ℕ → Set X) (hdisjoint : Set.univ.PairwiseDisjoint B)
    (hsupport : ∀ k, Function.support (f k) ⊆ B k) (x : X) :
    (Function.support (fun k ↦ f k x)).Subsingleton := by
  intro i hi j hj
  exact hdisjoint.elim_set (Set.mem_univ i) (Set.mem_univ j) x
    (hsupport i hi) (hsupport j hj)

/-- Helper for lem:polar-interpolation and eq:polar-objective: the exact
source correction family has pointwise finite support and is summable. -/
theorem summable_bump_apply {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (x : E) : Summable (fun k ↦ bump c ρ a k x) := by
  exact summable_of_hasFiniteSupport
    (support_apply_subsingleton (bump c ρ a) _ h.disjoint_open
      (support_bump_subset_ball h) x).finite

/-- Helper for lem:polar-interpolation and eq:polar-objective: the pointwise
finsum is exactly the manuscript's infinite sum, with finite support proved. -/
theorem perturbation_eq_tsum {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (x : E) :
    perturbation c ρ a x = ∑' k, bump c ρ a k x := by
  exact (tsum_eq_finsum
    (support_apply_subsingleton (bump c ρ a) _ h.disjoint_open
      (support_bump_subset_ball h) x).finite).symm

/-- Helper for lem:polar-interpolation and eq:polar-objective: the perturbation
vanishes everywhere on and inside the unit ball. -/
theorem perturbation_eq_zero_of_norm_le_one {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) {x : E} (hx : ‖x‖ ≤ 1) : perturbation c ρ a x = 0 := by
  have hzero (k : ℕ) : bump c ρ a k x = 0 :=
    bump_eq_zero_of_radius_le h k (h.radius_le_norm_sub_of_norm_le_one k hx)
  simp only [perturbation_apply, hzero, finsum_zero]

section SphereDistance

variable [Nontrivial E]

/-- Helper for lem:polar-interpolation and eq:polar-objective: the source
unit sphere is nonempty in a nontrivial real inner product space. -/
theorem unitSphere_nonempty : (unitSphere (E := E)).Nonempty := by
  exact NormedSpace.sphere_nonempty.mpr zero_le_one

/-- Helper for lem:polar-interpolation and eq:polar-objective: every closed
support ball has distance at least its radius from the unit sphere. -/
theorem Geometry.radius_le_infDist {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) {x : E} (hx : x ∈ Metric.closedBall (c k) (ρ k)) :
    ρ k ≤ Metric.infDist x unitSphere := by
  have hmargin := h.closedBall_norm_margin k hx
  have hnonneg : 0 ≤ ‖x‖ - 1 := by
    linarith [h.radius_pos k]
  rw [unitSphere, Metric.infDist_sphere x 0 1 zero_le_one, dist_zero_right,
    abs_of_nonneg hnonneg]
  linarith

end SphereDistance

section FixedBounds

variable [FiniteDimensional ℝ E]

/-- Helper for lem:polar-interpolation and eq:polar-objective: a derivative
constant chosen for the fixed accepted cutoff before all interpolation data. -/
def derivativeConstant (n : ℕ) : ℝ :=
  Classical.choose (ExplicitCutoff.exists_norm_iteratedFDeriv_correction_le (E := E) n)

/-- Helper for lem:polar-interpolation and eq:polar-objective: every fixed
cutoff derivative constant is nonnegative. -/
theorem derivativeConstant_nonneg (n : ℕ) : 0 ≤ derivativeConstant (E := E) n := by
  exact (Classical.choose_spec
    (ExplicitCutoff.exists_norm_iteratedFDeriv_correction_le (E := E) n)).1

/-- Helper for lem:polar-interpolation and eq:polar-objective: the fixed
cutoff constants control every exact correction at every point and scale. -/
theorem norm_iteratedFDeriv_bump_le (n : ℕ) (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (k : ℕ) (hρ : 0 < ρ k) (x : E) :
    ‖iteratedFDeriv ℝ n (bump c ρ a k) x‖ ≤
      derivativeConstant (E := E) n * ‖a k‖ * ρ k * ((ρ k)⁻¹) ^ n := by
  exact (Classical.choose_spec
    (ExplicitCutoff.exists_norm_iteratedFDeriv_correction_le (E := E) n)).2
      (c k) (ρ k) (a k) x hρ

/-- Helper for lem:polar-interpolation and eq:polar-objective: exact
correction values satisfy the source scale bound with a fixed constant. -/
theorem norm_bump_le (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (k : ℕ) (hρ : 0 < ρ k) (x : E) :
    ‖bump c ρ a k x‖ ≤ derivativeConstant (E := E) 0 * (‖a k‖ / ρ k) * ρ k ^ 2 := by
  have hbound := norm_iteratedFDeriv_bump_le 0 c ρ a k hρ x
  simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one] at hbound
  have hscale : derivativeConstant (E := E) 0 * ‖a k‖ * ρ k =
      derivativeConstant (E := E) 0 * (‖a k‖ / ρ k) * ρ k ^ 2 := by
    field_simp [hρ.ne']
  rwa [hscale] at hbound

/-- Helper for lem:polar-interpolation and eq:polar-objective: exact first
jets satisfy the source scale bound with a fixed constant. -/
theorem norm_fderiv_bump_le (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (k : ℕ) (hρ : 0 < ρ k) (x : E) :
    ‖fderiv ℝ (bump c ρ a k) x‖ ≤ derivativeConstant (E := E) 1 * (‖a k‖ / ρ k) * ρ k := by
  have hbound := norm_iteratedFDeriv_bump_le 1 c ρ a k hρ x
  simp only [norm_iteratedFDeriv_one, pow_one] at hbound
  have hscale : derivativeConstant (E := E) 1 * ‖a k‖ * ρ k * (ρ k)⁻¹ =
      derivativeConstant (E := E) 1 * (‖a k‖ / ρ k) * ρ k := by
    field_simp [hρ.ne']
  rwa [hscale] at hbound

/-- Helper for lem:polar-interpolation and eq:polar-objective: exact Hessians
satisfy the source smallness bound `Cχ ‖a_k‖ / ρ_k` globally. -/
theorem norm_secondFDeriv_bump_le (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E)
    (k : ℕ) (hρ : 0 < ρ k) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (bump c ρ a k)) x‖ ≤ derivativeConstant (E := E) 2 * (‖a k‖ / ρ k) := by
  calc
    ‖fderiv ℝ (fderiv ℝ (bump c ρ a k)) x‖ =
        ‖iteratedFDeriv ℝ 1 (fderiv ℝ (bump c ρ a k)) x‖ :=
      (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ (bump c ρ a k))).symm
    _ = ‖iteratedFDeriv ℝ 2 (bump c ρ a k) x‖ := norm_iteratedFDeriv_fderiv
    _ ≤ derivativeConstant (E := E) 2 * ‖a k‖ * ρ k * ((ρ k)⁻¹) ^ 2 :=
      norm_iteratedFDeriv_bump_le 2 c ρ a k hρ x
    _ = derivativeConstant (E := E) 2 * (‖a k‖ / ρ k) := by
      field_simp [hρ.ne']

end FixedBounds

/-- Helper for lem:polar-interpolation and eq:polar-objective: a locally
finite family of smooth functions has derivative equal to the pointwise
finsum of its derivatives, without any disjointness of closed supports. -/
theorem fderiv_finsum_of_locallyFinite
    {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ℕ → D → G) (hsmooth : ∀ k, Differentiable ℝ (f k)) (x : D)
    (hlocal : ∃ s ∈ 𝓝 x, {k | (tsupport (f k) ∩ s).Nonempty}.Finite) :
    fderiv ℝ (fun y ↦ ∑ᶠ k, f k y) x = ∑ᶠ k, fderiv ℝ (f k) x := by
  obtain ⟨s, hs, hfinite⟩ := hlocal
  let I := hfinite.toFinset
  have hxs : x ∈ s := mem_of_mem_nhds hs
  have hnormal : (fun y ↦ ∑ᶠ k, f k y) =ᶠ[𝓝 x] (fun y ↦ ∑ k ∈ I, f k y) := by
    filter_upwards [hs] with y hy
    apply finsum_eq_sum_of_support_subset
    intro k hk
    exact hfinite.mem_toFinset.mpr ⟨y, subset_tsupport (f k) hk, hy⟩
  have hderivativeSupport : Function.support (fun k ↦ fderiv ℝ (f k) x) ⊆ I := by
    intro k hk
    have hsupport : x ∈ tsupport (f k) := support_fderiv_subset ℝ hk
    exact hfinite.mem_toFinset.mpr ⟨x, hsupport, hxs⟩
  have hderivative := hnormal.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_sum (fun k _ ↦ hsmooth k x)] at hderivative
  rw [finsum_eq_sum_of_support_subset _ hderivativeSupport]
  exact hderivative

/-- Helper for lem:polar-interpolation and eq:polar-objective: away from
the unit sphere the exact infinite sum is smooth to every finite order. -/
theorem contDiffOn_perturbation {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (n : ℕ) :
    ContDiffOn ℝ n (perturbation c ρ a) (unitSphere (E := E))ᶜ := by
  apply contDiffOn_finsum_outside n unitSphere c ρ (bump c ρ a) isClosed_unitSphere
    (fun y hy ↦ h.cluster_mem_sphere hy) h.radius_tendsto_zero
    (tsupport_bump_subset_closedBall h)
  intro k
  exact (contDiff_bump c ρ a k).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

/-- Helper for lem:polar-interpolation and eq:polar-objective: the first
jet of the exact sum off the sphere is its actual pointwise derivative finsum. -/
theorem fderiv_perturbation_off {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) {x : E} (hx : x ∈ (unitSphere (E := E))ᶜ) :
    fderiv ℝ (perturbation c ρ a) x = ∑ᶠ k, fderiv ℝ (bump c ρ a k) x := by
  have horder : (∞ : WithTop ℕ∞) ≠ 0 := by
    simp
  have hsmooth (k : ℕ) : Differentiable ℝ (bump c ρ a k) :=
    (contDiff_bump c ρ a k).differentiable horder
  exact fderiv_finsum_of_locallyFinite (bump c ρ a) hsmooth x
    (locallyFinite_tsupport_outside unitSphere c ρ (bump c ρ a)
      (fun y hy ↦ h.cluster_mem_sphere hy) h.radius_tendsto_zero
      (tsupport_bump_subset_closedBall h) x hx)

/-- Helper for lem:polar-interpolation and eq:polar-objective: derivative
supports inherit the correct closed support balls of the exact bumps. -/
theorem tsupport_fderiv_bump_subset_closedBall {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) :
    tsupport (fderiv ℝ (bump c ρ a k)) ⊆ Metric.closedBall (c k) (ρ k) := by
  exact (tsupport_fderiv_subset ℝ).trans (tsupport_bump_subset_closedBall h k)

/-- Helper for lem:polar-interpolation and eq:polar-objective: second
supports also retain the correct closed support balls. -/
theorem tsupport_secondFDeriv_bump_subset_closedBall
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a) (k : ℕ) :
    tsupport (fderiv ℝ (fderiv ℝ (bump c ρ a k))) ⊆ Metric.closedBall (c k) (ρ k) := by
  exact (tsupport_fderiv_subset ℝ).trans (tsupport_fderiv_bump_subset_closedBall h k)

/-- Helper for lem:polar-interpolation and eq:polar-objective: the Hessian
of the exact sum off the sphere is the proved pointwise Hessian finsum. -/
theorem secondFDeriv_perturbation_off {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) {x : E} (hx : x ∈ (unitSphere (E := E))ᶜ) :
    fderiv ℝ (fderiv ℝ (perturbation c ρ a)) x =
      ∑ᶠ k, fderiv ℝ (fderiv ℝ (bump c ρ a k)) x := by
  have hnormal : fderiv ℝ (perturbation c ρ a) =ᶠ[𝓝 x]
      (fun y ↦ ∑ᶠ k, fderiv ℝ (bump c ρ a k) y) := by
    filter_upwards [isClosed_unitSphere.compl_mem_nhds hx] with y hy
    exact fderiv_perturbation_off h hy
  have hsmooth (k : ℕ) : Differentiable ℝ (fderiv ℝ (bump c ρ a k)) :=
    ((contDiff_bump c ρ a k).fderiv_right
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiable_one
  calc
    fderiv ℝ (fderiv ℝ (perturbation c ρ a)) x =
        fderiv ℝ (fun y ↦ ∑ᶠ k, fderiv ℝ (bump c ρ a k) y) x :=
      hnormal.fderiv_eq
    _ = ∑ᶠ k, fderiv ℝ (fderiv ℝ (bump c ρ a k)) x :=
      fderiv_finsum_of_locallyFinite (fun k ↦ fderiv ℝ (bump c ρ a k)) hsmooth x
        (locallyFinite_tsupport_outside unitSphere c ρ
          (fun k ↦ fderiv ℝ (bump c ρ a k)) (fun y hy ↦ h.cluster_mem_sphere hy)
          h.radius_tendsto_zero (tsupport_fderiv_bump_subset_closedBall h) x hx)

/-- Helper for lem:polar-interpolation and eq:polar-objective: finitely
many positive support radii have a common positive lower bound. -/
theorem exists_prefix_radius_lower (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (K : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k < K, δ ≤ ρ k := by
  induction K with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro k hk
    omega
  | succ K hK =>
    obtain ⟨δ, hδ, hlower⟩ := hK
    refine ⟨min δ (ρ K), lt_min hδ (hρ K), ?_⟩
    intro k hk
    by_cases hlt : k < K
    · exact (min_le_left _ _).trans (hlower k hlt)
    · have heq : k = K := by
        omega
      rw [heq]
      exact min_le_right _ _

/-- Helper for lem:polar-interpolation and eq:polar-objective: a pointwise
finsum with disjoint function supports takes the value of any active summand. -/
theorem finsum_eq_active {X G : Type*} [AddCommMonoid G]
    (f : ℕ → X → G) (B : ℕ → Set X) (hdisjoint : Set.univ.PairwiseDisjoint B)
    (hsupport : ∀ k, Function.support (f k) ⊆ B k) (k : ℕ) {x : X} (hx : f k x ≠ 0) :
    (∑ᶠ i, f i x) = f k x := by
  apply finsum_eq_single
  intro i hik
  by_contra hi
  exact hik (support_apply_subsingleton f B hdisjoint hsupport x hi hx)

variable [Nontrivial E] [FiniteDimensional ℝ E]

/-- Helper for lem:polar-interpolation and eq:polar-objective: distance
scaled value bounds of the exact bumps follow from the margin and fixed cutoff. -/
theorem norm_bump_div_infDist_sq_le {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) {x : E} (hx : x ∈ Metric.closedBall (c k) (ρ k)) :
    ‖bump c ρ a k x‖ / Metric.infDist x unitSphere ^ 2 ≤
      derivativeConstant (E := E) 0 * (‖a k‖ / ρ k) := by
  have hd := h.radius_le_infDist k hx
  have hdpos : 0 < Metric.infDist x unitSphere := (h.radius_pos k).trans_le hd
  have hweight : 0 ≤ derivativeConstant (E := E) 0 * (‖a k‖ / ρ k) :=
    mul_nonneg (derivativeConstant_nonneg 0) (div_nonneg (norm_nonneg _) (h.radius_pos k).le)
  apply (div_le_iff₀ (sq_pos_of_pos hdpos)).mpr
  exact (norm_bump_le c ρ a k (h.radius_pos k) x).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h.radius_pos k).le hd 2) hweight)

/-- Helper for lem:polar-interpolation and eq:polar-objective: distance
scaled first-jet bounds follow from the same support margin. -/
theorem norm_fderiv_bump_div_infDist_le {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) {x : E} (hx : x ∈ Metric.closedBall (c k) (ρ k)) :
    ‖fderiv ℝ (bump c ρ a k) x‖ / Metric.infDist x unitSphere ≤
      derivativeConstant (E := E) 1 * (‖a k‖ / ρ k) := by
  have hd := h.radius_le_infDist k hx
  have hdpos : 0 < Metric.infDist x unitSphere := (h.radius_pos k).trans_le hd
  have hweight : 0 ≤ derivativeConstant (E := E) 1 * (‖a k‖ / ρ k) :=
    mul_nonneg (derivativeConstant_nonneg 1) (div_nonneg (norm_nonneg _) (h.radius_pos k).le)
  apply (div_le_iff₀ hdpos).mpr
  exact (norm_fderiv_bump_le c ρ a k (h.radius_pos k) x).trans
    (mul_le_mul_of_nonneg_left hd hweight)

omit [FiniteDimensional ℝ E] in
/-- Helper for lem:polar-interpolation and eq:polar-objective: disjoint
jet fields with source support-distance bounds inherit vanishing boundary
quotients from the decaying coefficient-to-radius ratios. -/
theorem tendsto_finsum_jet_quotient
    {G : Type*} [NormedAddCommGroup G]
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a)
    (f : ℕ → E → G) (C : ℝ) (q : ℕ)
    (hsupport : ∀ k, tsupport (f k) ⊆ Metric.closedBall (c k) (ρ k))
    (hopen : ∀ k, Function.support (f k) ⊆ Metric.ball (c k) (ρ k))
    (hbound : ∀ k x, x ∈ tsupport (f k) →
      ‖f k x‖ / Metric.infDist x unitSphere ^ q ≤ C * (‖a k‖ / ρ k)) :
    Tendsto (fun x ↦ ‖∑ᶠ k, f k x‖ / Metric.infDist x unitSphere ^ q)
      boundaryFilter (𝓝 0) := by
  have hweight : Tendsto (fun k ↦ C * (‖a k‖ / ρ k)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using h.ratio_decay.const_mul C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hweight.eventually_lt_const hε)
  obtain ⟨δ, hδ, hprefix⟩ := exists_prefix_radius_lower ρ h.radius_pos K
  filter_upwards [boundaryFilter_infDist_tendsto.eventually_lt_const hδ] with x hx
  have hquotient : 0 ≤ ‖∑ᶠ k, f k x‖ / Metric.infDist x unitSphere ^ q :=
    div_nonneg (norm_nonneg _) (pow_nonneg Metric.infDist_nonneg q)
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hquotient]
  by_cases hactive : ∃ k, f k x ≠ 0
  · obtain ⟨k, hk⟩ := hactive
    rw [finsum_eq_active f _ h.disjoint_open hopen k hk]
    have htsupport : x ∈ tsupport (f k) := subset_tsupport (f k) hk
    have hradius := h.radius_le_infDist k (hsupport k htsupport)
    have htail : K ≤ k := by
      by_contra hnot
      have hfinite := hprefix k (Nat.lt_of_not_ge hnot)
      linarith
    exact (hbound k x htsupport).trans_lt (hK k htail)
  · have hzero (k : ℕ) : f k x = 0 := by
      by_contra hk
      exact hactive ⟨k, hk⟩
    simpa only [hzero, finsum_zero, norm_zero, zero_div] using hε

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
sum has quadratic value decay relative to the unit sphere. -/
theorem perturbation_value_decay {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) :
    Tendsto (fun x ↦ ‖perturbation c ρ a x‖ / Metric.infDist x unitSphere ^ 2)
      boundaryFilter (𝓝 0) := by
  apply tendsto_finsum_jet_quotient h (bump c ρ a) (derivativeConstant (E := E) 0) 2
    (tsupport_bump_subset_closedBall h) (support_bump_subset_ball h)
  intro k x hx
  exact norm_bump_div_infDist_sq_le h k (tsupport_bump_subset_closedBall h k hx)

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
first derivative of the sum has linear distance decay at the unit sphere. -/
theorem perturbation_fderiv_decay {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) :
    Tendsto (fun x ↦ ‖fderiv ℝ (perturbation c ρ a) x‖ / Metric.infDist x unitSphere)
      boundaryFilter (𝓝 0) := by
  have hbound (k : ℕ) (x : E) (hx : x ∈ tsupport (fderiv ℝ (bump c ρ a k))) :
      ‖fderiv ℝ (bump c ρ a k) x‖ / Metric.infDist x unitSphere ^ 1 ≤
        derivativeConstant (E := E) 1 * (‖a k‖ / ρ k) := by
    simpa only [pow_one] using norm_fderiv_bump_div_infDist_le h k
      (tsupport_fderiv_bump_subset_closedBall h k hx)
  have hfield := tendsto_finsum_jet_quotient h
    (fun k ↦ fderiv ℝ (bump c ρ a k)) (derivativeConstant (E := E) 1) 1
    (tsupport_fderiv_bump_subset_closedBall h) (support_fderiv_bump_subset_ball h) hbound
  have hnormal : (fun x ↦ ‖fderiv ℝ (perturbation c ρ a) x‖ / Metric.infDist x unitSphere) =ᶠ[
      boundaryFilter] (fun x ↦ ‖∑ᶠ k, fderiv ℝ (bump c ρ a k) x‖ /
        Metric.infDist x unitSphere ^ 1) := by
    filter_upwards [eventually_boundary_compl] with x hx
    rw [fderiv_perturbation_off h hx, pow_one]
  exact hfield.congr' hnormal.symm

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
Hessian of the sum tends to zero at the unit sphere. -/
theorem perturbation_secondFDeriv_decay {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) :
    Tendsto (fun x ↦ ‖fderiv ℝ (fderiv ℝ (perturbation c ρ a)) x‖)
      boundaryFilter (𝓝 0) := by
  have hbound (k : ℕ) (x : E) (_hx : x ∈ tsupport
      (fderiv ℝ (fderiv ℝ (bump c ρ a k)))) :
      ‖fderiv ℝ (fderiv ℝ (bump c ρ a k)) x‖ / Metric.infDist x unitSphere ^ 0 ≤
        derivativeConstant (E := E) 2 * (‖a k‖ / ρ k) := by
    simpa only [pow_zero, div_one] using norm_secondFDeriv_bump_le c ρ a k (h.radius_pos k) x
  have hfield := tendsto_finsum_jet_quotient h
    (fun k ↦ fderiv ℝ (fderiv ℝ (bump c ρ a k))) (derivativeConstant (E := E) 2) 0
    (tsupport_secondFDeriv_bump_subset_closedBall h)
    (support_secondFDeriv_bump_subset_ball h) hbound
  have hnormal : (fun x ↦ ‖fderiv ℝ (fderiv ℝ (perturbation c ρ a)) x‖) =ᶠ[
      boundaryFilter] (fun x ↦ ‖∑ᶠ k, fderiv ℝ (fderiv ℝ (bump c ρ a k)) x‖ /
        Metric.infDist x unitSphere ^ 0) := by
    filter_upwards [eventually_boundary_compl] with x hx
    rw [secondFDeriv_perturbation_off h hx, pow_zero, div_one]
  exact hfield.congr' hnormal.symm

omit [Nontrivial E] [FiniteDimensional ℝ E] in
/-- Helper for lem:polar-interpolation and eq:polar-objective: zero extension
across the sphere is exactly the original pointwise correction sum. -/
theorem indicator_perturbation_eq {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) :
    (unitSphere (E := E))ᶜ.indicator (perturbation c ρ a) = perturbation c ρ a := by
  funext x
  by_cases hx : x ∈ unitSphere
  · have hnot : x ∉ (unitSphere (E := E))ᶜ := by
      simpa only [Set.mem_compl_iff, not_not] using hx
    rw [indicator_of_notMem hnot, perturbation_eq_zero_of_norm_le_one h
      ((mem_unitSphere x).mp hx).le]
  · exact indicator_of_mem hx _

/-- lem:polar-interpolation (generic regularity component). Under the
explicit geometric margin, disjoint OPEN balls and coefficient decay, the
EXACT source infinite correction sum is C² across the unit sphere. The value
and first derivative decay prove differentiability twice; Hessian decay proves
continuity. No regularity or derivative identity is assumed. -/
theorem contDiff_perturbation {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) : ContDiff ℝ 2 (perturbation c ρ a) := by
  have hextension := IsClosed.contDiff_two_indicator_compl unitSphere (perturbation c ρ a)
    isClosed_unitSphere (contDiffOn_perturbation h 2) (perturbation_value_decay h)
    (perturbation_fderiv_decay h) (perturbation_secondFDeriv_decay h)
  rwa [indicator_perturbation_eq h] at hextension

/-- Helper for lem:polar-interpolation and eq:polar-objective: the first
jet of the actual correction sum vanishes on the sphere by differentiable
zero extension, not by a continuity-only argument. -/
theorem fderiv_perturbation_eq_zero_on_sphere {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) {x : E} (hx : x ∈ unitSphere) :
    fderiv ℝ (perturbation c ρ a) x = 0 := by
  have hzero := IsClosed.fderiv_indicator_compl_eq_zero_of_mem unitSphere
    (perturbation c ρ a) isClosed_unitSphere
    ((contDiffOn_perturbation h 2).differentiableOn two_ne_zero)
    (Filter.tendsto_norm_div_infDist_of_sq unitSphere (perturbation c ρ a)
      (perturbation_value_decay h)) hx
  rwa [indicator_perturbation_eq h] at hzero

/-- Helper for lem:polar-interpolation and eq:polar-objective: the second
jet of the actual sum vanishes on the sphere by differentiating the zero-extended
first jet with the proved linear decay. -/
theorem secondFDeriv_perturbation_eq_zero_on_sphere
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a) {x : E}
    (hx : x ∈ unitSphere) : fderiv ℝ (fderiv ℝ (perturbation c ρ a)) x = 0 := by
  have hzero := IsClosed.fderiv_fderiv_indicator_compl_eq_zero_of_mem unitSphere
    (perturbation c ρ a) isClosed_unitSphere (contDiffOn_perturbation h 2)
    (perturbation_value_decay h) (perturbation_fderiv_decay h) hx
  rwa [indicator_perturbation_eq h] at hzero

/-- Helper for lem:polar-interpolation and eq:polar-objective: the exact
sum's first derivative is its pointwise derivative finsum on the entire space,
including the sphere. -/
theorem fderiv_perturbation {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (x : E) :
    fderiv ℝ (perturbation c ρ a) x = ∑ᶠ k, fderiv ℝ (bump c ρ a k) x := by
  by_cases hx : x ∈ unitSphere
  · have hzero (k : ℕ) : fderiv ℝ (bump c ρ a k) x = 0 :=
      fderiv_bump_eq_zero_of_radius_le h k
        (h.radius_le_norm_sub_of_norm_le_one k ((mem_unitSphere x).mp hx).le)
    rw [fderiv_perturbation_eq_zero_on_sphere h hx]
    simp only [hzero, finsum_zero]
  · exact fderiv_perturbation_off h hx

/-- Helper for lem:polar-interpolation and eq:polar-objective: the exact
sum's Hessian is its pointwise Hessian finsum everywhere, including the sphere.
This identity is a conclusion of the gluing proof. -/
theorem secondFDeriv_perturbation {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (x : E) :
    fderiv ℝ (fderiv ℝ (perturbation c ρ a)) x =
      ∑ᶠ k, fderiv ℝ (fderiv ℝ (bump c ρ a k)) x := by
  by_cases hx : x ∈ unitSphere
  · have hzero (k : ℕ) : fderiv ℝ (fderiv ℝ (bump c ρ a k)) x = 0 :=
      secondFDeriv_bump_eq_zero_of_radius_le h k
        (h.radius_le_norm_sub_of_norm_le_one k ((mem_unitSphere x).mp hx).le)
    rw [secondFDeriv_perturbation_eq_zero_on_sphere h hx]
    simp only [hzero, finsum_zero]
  · exact secondFDeriv_perturbation_off h hx

omit [InnerProductSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E] in
/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: a field
supported in the disjoint OPEN correction balls has only its centered term at
each center, regardless of contacts between closed support boundaries. -/
theorem finsum_eq_center {G : Type*} [AddCommMonoid G]
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a)
    (f : ℕ → E → G) (hsupport : ∀ i, Function.support (f i) ⊆ Metric.ball (c i) (ρ i))
    (k : ℕ) : (∑ᶠ i, f i (c k)) = f k (c k) := by
  have hcenter : c k ∈ Metric.ball (c k) (ρ k) := by
    simpa only [Metric.mem_ball, dist_self] using h.radius_pos k
  apply finsum_eq_single
  intro i hik
  by_contra hi
  have heq := h.disjoint_open.elim_set (Set.mem_univ i) (Set.mem_univ k)
    (c k) (hsupport i hi) hcenter
  exact hik heq

omit [Nontrivial E] [FiniteDimensional ℝ E] in
/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the exact
correction sum has zero value at every designated center. -/
theorem perturbation_center {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) : perturbation c ρ a (c k) = 0 := by
  rw [perturbation_apply, finsum_eq_center h (bump c ρ a) (support_bump_subset_ball h)]
  exact ExplicitCutoff.correction_apply_center (c k) (ρ k) (a k)

/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the exact
sum's derivative at a center is the prescribed affine covector. -/
theorem fderiv_perturbation_center {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) :
    fderiv ℝ (perturbation c ρ a) (c k) = innerSL ℝ (a k) := by
  rw [fderiv_perturbation h, finsum_eq_center h
    (fun i ↦ fderiv ℝ (bump c ρ a i)) (support_fderiv_bump_subset_ball h)]
  exact ExplicitCutoff.fderiv_correction_center (c k) (ρ k) (a k) (h.radius_pos k)

/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the exact
sum has zero second derivative at every designated center. -/
theorem secondFDeriv_perturbation_center {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) :
    fderiv ℝ (fderiv ℝ (perturbation c ρ a)) (c k) = 0 := by
  rw [secondFDeriv_perturbation h, finsum_eq_center h
    (fun i ↦ fderiv ℝ (fderiv ℝ (bump c ρ a i))) (support_secondFDeriv_bump_subset_ball h)]
  exact ExplicitCutoff.secondFDeriv_correction_center (c k) (ρ k) (a k) (h.radius_pos k)

/-- Helper for lem:polar-interpolation and eq:polar-objective: the first
jet of the exact sum vanishes on the whole closed unit ball. -/
theorem fderiv_perturbation_eq_zero_of_norm_le_one
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a) {x : E} (hx : ‖x‖ ≤ 1) :
    fderiv ℝ (perturbation c ρ a) x = 0 := by
  rw [fderiv_perturbation h]
  have hzero (k : ℕ) : fderiv ℝ (bump c ρ a k) x = 0 :=
    fderiv_bump_eq_zero_of_radius_le h k (h.radius_le_norm_sub_of_norm_le_one k hx)
  simp only [hzero, finsum_zero]

/-- Helper for lem:polar-interpolation and eq:polar-objective: the second
jet of the exact sum vanishes on the whole closed unit ball. -/
theorem secondFDeriv_perturbation_eq_zero_of_norm_le_one
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a) {x : E} (hx : ‖x‖ ≤ 1) :
    fderiv ℝ (fderiv ℝ (perturbation c ρ a)) x = 0 := by
  rw [secondFDeriv_perturbation h]
  have hzero (k : ℕ) : fderiv ℝ (fderiv ℝ (bump c ρ a k)) x = 0 :=
    secondFDeriv_bump_eq_zero_of_radius_le h k (h.radius_le_norm_sub_of_norm_le_one k hx)
  simp only [hzero, finsum_zero]

/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the
Riesz gradient of the exact sum at a center is its prescribed coefficient. -/
theorem hasGradientAt_perturbation_center {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) : HasGradientAt (perturbation c ρ a) (a k) (c k) := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hderivative := ((contDiff_perturbation h).differentiable two_ne_zero (c k)).hasFDerivAt
  rw [fderiv_perturbation_center h k] at hderivative
  exact hderivative

/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the
canonical gradient of the exact perturbation equals the coefficient at each center. -/
theorem gradient_perturbation_center {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) : gradient (perturbation c ρ a) (c k) = a k := by
  exact (hasGradientAt_perturbation_center h k).gradient

/-- Helper for lem:polar-interpolation and eq:polar-objective: the exact
perturbation gradient vanishes throughout the closed unit ball. -/
theorem gradient_perturbation_eq_zero_of_norm_le_one
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a) {x : E} (hx : ‖x‖ ≤ 1) :
    gradient (perturbation c ρ a) x = 0 := by
  rw [gradient, fderiv_perturbation_eq_zero_of_norm_le_one h hx, map_zero]

/-- Helper for lem:polar-interpolation and eq:polar-objective: the source
quadratic-plus-sum objective is globally C². -/
theorem contDiff_objective {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) : ContDiff ℝ 2 (objective c ρ a) := by
  have hquadratic : ContDiff ℝ 2 (fun x : E ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  rw [funext (objective_apply c ρ a)]
  exact hquadratic.add (contDiff_perturbation h)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the exact
objective takes the unperturbed quadratic value at each designated center. -/
theorem objective_center {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) : objective c ρ a (c k) = (1 / 2 : ℝ) * ‖c k‖ ^ 2 := by
  rw [objective_apply, perturbation_center h k, add_zero]

/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the source
objective has prescribed gradient `c_k+a_k` at every center. -/
theorem hasGradientAt_objective_center {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) :
    HasGradientAt (objective c ρ a) (c k + a k) (c k) := by
  rw [funext (objective_apply c ρ a)]
  simpa only [sub_zero] using HessianPerturbation.hasGradientAt_halfNormSq_sub_add
    (0 : E) (hasGradientAt_perturbation_center h k)

/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the
canonical objective gradient interpolates every prescribed coefficient. -/
theorem gradient_objective_center {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) : gradient (objective c ρ a) (c k) = c k + a k := by
  exact (hasGradientAt_objective_center h k).gradient

/-- Helper for lem:polar-interpolation and eq:polar-objective: the objective
Hessian operator is the identity plus the perturbation Hessian operator. -/
theorem hessian_objective {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (x : E) :
    fderiv ℝ (gradient (objective c ρ a)) x =
      1 + fderiv ℝ (gradient (perturbation c ρ a)) x := by
  rw [funext (objective_apply c ρ a)]
  simpa only [sub_zero] using HessianPerturbation.fderiv_gradient_halfNormSq_sub_add
    (0 : E) (perturbation c ρ a) x (contDiff_perturbation h)

/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the source
objective has identity Hessian at each designated center. -/
theorem hessian_objective_center {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) (k : ℕ) : fderiv ℝ (gradient (objective c ρ a)) (c k) = 1 := by
  have hzero : fderiv ℝ (gradient (perturbation c ρ a)) (c k) = 0 := by
    apply norm_eq_zero.mp
    rw [norm_fderiv_gradient_eq_norm_fderiv_fderiv, secondFDeriv_perturbation_center h k,
      norm_zero]
  rw [hessian_objective h, hzero, add_zero]

omit [Nontrivial E] [FiniteDimensional ℝ E] in
/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the exact
objective equals the half squared norm on the entire closed unit ball. -/
theorem objective_eq_quadratic_of_norm_le_one
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a) {x : E} (hx : ‖x‖ ≤ 1) :
    objective c ρ a x = (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
  rw [objective_apply, perturbation_eq_zero_of_norm_le_one h hx, add_zero]

omit [Nontrivial E] [FiniteDimensional ℝ E] in
/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the exact
objective has the source normalization `f(0)=0`. -/
theorem objective_zero {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : Geometry c ρ a) : objective c ρ a 0 = 0 := by
  have hnorm : ‖(0 : E)‖ ≤ 1 := by
    simp
  rw [objective_eq_quadratic_of_norm_le_one h hnorm, norm_zero, zero_pow two_ne_zero, mul_zero]

/-- Helper for lem:polar-interpolation and eq:polar-objective: a disjoint
pointwise finsum inherits a nonnegative uniform norm bound for every summand. -/
theorem norm_finsum_le_of_disjoint_support {X G : Type*} [NormedAddCommGroup G]
    (f : ℕ → X → G) (B : ℕ → Set X) (hdisjoint : Set.univ.PairwiseDisjoint B)
    (hsupport : ∀ k, Function.support (f k) ⊆ B k) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ k x, ‖f k x‖ ≤ D) (x : X) : ‖∑ᶠ k, f k x‖ ≤ D := by
  by_cases hactive : ∃ k, f k x ≠ 0
  · obtain ⟨k, hk⟩ := hactive
    rw [finsum_eq_active f B hdisjoint hsupport k hk]
    exact hbound k x
  · have hzero (k : ℕ) : f k x = 0 := by
      by_contra hk
      exact hactive ⟨k, hk⟩
    simpa only [hzero, finsum_zero, norm_zero] using hD

/-- Helper for lem:polar-interpolation and eq:polar-objective: a global
coefficient-to-radius bound yields the source global Hessian norm estimate,
with the cutoff constant fixed before all interpolation data. -/
theorem norm_secondFDeriv_perturbation_le
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ k, ‖a k‖ / ρ k ≤ B) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (perturbation c ρ a)) x‖ ≤ derivativeConstant (E := E) 2 * B := by
  rw [secondFDeriv_perturbation h]
  apply norm_finsum_le_of_disjoint_support
    (fun k ↦ fderiv ℝ (fderiv ℝ (bump c ρ a k))) _ h.disjoint_open
    (support_secondFDeriv_bump_subset_ball h) _
    (mul_nonneg (derivativeConstant_nonneg 2) hB)
  intro k y
  exact (norm_secondFDeriv_bump_le c ρ a k (h.radius_pos k) y).trans
    (mul_le_mul_of_nonneg_left (hbound k) (derivativeConstant_nonneg 2))

/-- Helper for lem:polar-interpolation and eq:polar-objective: the proved
Hessian-sum identity transfers the accepted half-Hölder bounds to the actual
infinite correction sum. The constant is chosen before all geometric data. -/
theorem exists_hessian_holder_perturbation :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E),
      Geometry c ρ a → ∀ M : ℝ, 0 ≤ M →
      (∀ k, ‖a k‖ * (ρ k) ^ (-3 / 2 : ℝ) ≤ M) → ∀ x y,
      ‖fderiv ℝ (fderiv ℝ (perturbation c ρ a)) x -
        fderiv ℝ (fderiv ℝ (perturbation c ρ a)) y‖ ≤
        2 * Cχ * M * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨Cχ, hCχ, hholder⟩ :=
    InterpolationBounds.exists_norm_finsum_hessian_correction_sub_le (E := E) (ι := ℕ)
  refine ⟨Cχ, hCχ, ?_⟩
  intro c ρ a h M hM hbound x y
  rw [secondFDeriv_perturbation h, secondFDeriv_perturbation h]
  exact hholder c ρ a M hM h.radius_pos h.disjoint_open hbound x y

/-- Helper for lem:polar-interpolation and eq:polar-objective: the objective
Hessian differs from the identity by at most the fixed cutoff constant times
the coefficient-to-radius envelope. -/
theorem norm_hessian_objective_sub_one_le
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ k, ‖a k‖ / ρ k ≤ B) (x : E) :
    ‖fderiv ℝ (gradient (objective c ρ a)) x - 1‖ ≤ derivativeConstant (E := E) 2 * B := by
  rw [hessian_objective h, add_sub_cancel_left,
    norm_fderiv_gradient_eq_norm_fderiv_fderiv]
  exact norm_secondFDeriv_perturbation_le h hB hbound x

/-- Helper for lem:polar-interpolation and eq:polar-objective: the exact
objective is strongly convex when its proved Hessian perturbation bound is
below one. No convexity or Hessian identity is assumed. -/
theorem strongConvexOn_objective
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E} (h : Geometry c ρ a)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ k, ‖a k‖ / ρ k ≤ B)
    (hsmall : derivativeConstant (E := E) 2 * B < 1) :
    StrongConvexOn Set.univ (1 - derivativeConstant (E := E) 2 * B) (objective c ρ a) := by
  rw [funext (objective_apply c ρ a)]
  simpa only [sub_zero] using
    HessianPerturbation.strongConvexOn_halfNormSq_add_of_secondFDeriv_norm_le
      (0 : E) (perturbation c ρ a) (derivativeConstant (E := E) 2 * B)
      (contDiff_perturbation h) hsmall (norm_secondFDeriv_perturbation_le h hB hbound)

/-- Helper for lem:polar-interpolation and eq:polar-objective: one fixed
cutoff constant controls both the global Hessian size and its half-Hölder
modulus. Its choice precedes all interpolation data and envelopes. -/
theorem exists_global_hessian_bounds :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E),
      Geometry c ρ a → ∀ B M : ℝ, 0 ≤ B → 0 ≤ M →
      (∀ k, ‖a k‖ / ρ k ≤ B) → (∀ k, ‖a k‖ * (ρ k) ^ (-3 / 2 : ℝ) ≤ M) →
      (∀ x, ‖fderiv ℝ (fderiv ℝ (perturbation c ρ a)) x‖ ≤ Cχ * B) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (perturbation c ρ a)) x -
        fderiv ℝ (fderiv ℝ (perturbation c ρ a)) y‖ ≤
          2 * Cχ * M * ‖x - y‖ ^ (1 / 2 : ℝ)) := by
  obtain ⟨Cholder, hCholder, hholder⟩ := exists_hessian_holder_perturbation (E := E)
  have hC : 0 ≤ max (derivativeConstant (E := E) 2) Cholder :=
    (derivativeConstant_nonneg 2).trans (le_max_left _ _)
  refine ⟨max (derivativeConstant (E := E) 2) Cholder, hC, ?_⟩
  intro c ρ a h B M hB hM hsize hscaled
  constructor
  · intro x
    exact (norm_secondFDeriv_perturbation_le h hB hsize x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)
  · intro x y
    apply (hholder c ρ a h M hM hscaled x y).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
    apply mul_le_mul_of_nonneg_right _ hM
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) zero_le_two

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
polar coefficient is exactly the prescribed gradient minus the prescribed point. -/
def polarCoefficient (p : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  p.gradient k - p.point k

/-- Helper for lem:polar-interpolation and eq:polar-objective: evaluation of
the actual source affine coefficient. -/
theorem polarCoefficient_apply (p : Parameters) (k : ℕ) :
    polarCoefficient p k = p.gradient k - p.point k := by
  rfl

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
source radius is κ times the squared prescribed cycle scale, without rescaling χ. -/
def polarSupportRadius (p : Parameters) (κ : ℝ) (k : ℕ) : ℝ :=
  κ * p.scale (k / 2) ^ 2

/-- Helper for lem:polar-interpolation and eq:polar-objective: evaluation of
the exact source support radius. -/
theorem polarSupportRadius_apply (p : Parameters) (κ : ℝ) (k : ℕ) :
    polarSupportRadius p κ k = κ * p.scale (k / 2) ^ 2 := by
  rfl

/-- Helper for lem:polar-interpolation and eq:polar-objective: the even
support radius is precisely κ t_j². -/
theorem polarSupportRadius_even (p : Parameters) (κ : ℝ) (j : ℕ) :
    polarSupportRadius p κ (2 * j) = κ * p.scale j ^ 2 := by
  have hindex : 2 * j / 2 = j := by
    omega
  rw [polarSupportRadius_apply, hindex]

/-- Helper for lem:polar-interpolation and eq:polar-objective: the odd
support radius is the same κ t_j² as the preceding even support radius. -/
theorem polarSupportRadius_odd (p : Parameters) (κ : ℝ) (j : ℕ) :
    polarSupportRadius p κ (2 * j + 1) = κ * p.scale j ^ 2 := by
  have hindex : (2 * j + 1) / 2 = j := by
    omega
  rw [polarSupportRadius_apply, hindex]

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
source polar correction uses exactly the accepted cutoff, point, coefficient
and support radius. -/
def polarBump (p : Parameters) (κ : ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  bump p.point (polarSupportRadius p κ) (polarCoefficient p) k

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
polar correction has the unchanged explicit cutoff-times-affine formula. -/
theorem polarBump_apply (p : Parameters) (κ : ℝ) (k : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    polarBump p κ k x =
      ExplicitCutoff.chi ((κ * p.scale (k / 2) ^ 2)⁻¹ • (x - p.point k)) *
        inner ℝ (p.gradient k - p.point k) (x - p.point k) := by
  exact bump_apply p.point (polarSupportRadius p κ) (polarCoefficient p) k x

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
polar perturbation is the exact source pointwise correction sum. Its regularity
requires the geometric premises of the conditional wrapper below. -/
def polarPerturbation (p : Parameters) (κ : ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  perturbation p.point (polarSupportRadius p κ) (polarCoefficient p)

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
polar perturbation is the generic exact sum with the prescribed source data. -/
theorem polarPerturbation_def (p : Parameters) (κ : ℝ) :
    polarPerturbation p κ = perturbation p.point (polarSupportRadius p κ) (polarCoefficient p) := by
  rfl

/-- Helper for lem:polar-interpolation and eq:polar-objective: evaluation of
the actual polar correction sum. -/
theorem polarPerturbation_apply (p : Parameters) (κ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    polarPerturbation p κ x = ∑ᶠ k, polarBump p κ k x := by
  rfl

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
source objective is the unchanged half squared norm plus the actual polar sum.
The geometric premises for C² and interpolation are not asserted by this definition. -/
def polarObjective (p : Parameters) (κ : ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  objective p.point (polarSupportRadius p κ) (polarCoefficient p)

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
polar objective is the generic exact objective at its prescribed source data. -/
theorem polarObjective_def (p : Parameters) (κ : ℝ) :
    polarObjective p κ = objective p.point (polarSupportRadius p κ) (polarCoefficient p) := by
  rfl

/-- Helper for lem:polar-interpolation and eq:polar-objective: evaluation of
the exact source polar objective. -/
theorem polarObjective_apply (p : Parameters) (κ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    polarObjective p κ x = (1 / 2 : ℝ) * ‖x‖ ^ 2 + polarPerturbation p κ x := by
  rfl

/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: this is a
CONDITIONAL bridge from actual polar data. Actual open-ball separation, radial
margin, center-norm convergence and coefficient decay remain explicit premises
awaiting the polar geometry proofs. No regularity or derivative identity is a premise. -/
theorem polarGeometry_of_hypotheses (p : Parameters) (κ : ℝ)
    (hstart : 0 < p.startIndex) (hκ : 0 < κ)
    (hballs : Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.ball (p.point k) (κ * p.scale (k / 2) ^ 2)))
    (hcenters : Tendsto (fun k ↦ ‖p.point k‖) atTop (𝓝 1))
    (hmargin : ∀ k, 1 + 2 * (κ * p.scale (k / 2) ^ 2) ≤ ‖p.point k‖)
    (hdecay : Tendsto (fun k ↦ ‖p.gradient k - p.point k‖ / (κ * p.scale (k / 2) ^ 2))
      atTop (𝓝 0)) : Geometry p.point (polarSupportRadius p κ) (polarCoefficient p) := by
  constructor
  · intro k
    rw [polarSupportRadius_apply]
    exact mul_pos hκ (sq_pos_of_pos (ScaleTails.scale_pos p hstart (k / 2)))
  · exact hballs
  · exact hcenters
  · exact hmargin
  · exact hdecay

/-- eq:polar-endpoint-data (conditional actual-data interpolation wrapper).
The actual source objective is C² and interpolates the prescribed values,
gradients and identity Hessians once the listed geometric and decay premises
are independently proved. This is not a proof of those polar-geometry premises
or of the full source counterexample. -/
theorem polar_interpolation_of_geometry (p : Parameters) (κ : ℝ)
    (hstart : 0 < p.startIndex) (hκ : 0 < κ)
    (hballs : Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.ball (p.point k) (κ * p.scale (k / 2) ^ 2)))
    (hcenters : Tendsto (fun k ↦ ‖p.point k‖) atTop (𝓝 1))
    (hmargin : ∀ k, 1 + 2 * (κ * p.scale (k / 2) ^ 2) ≤ ‖p.point k‖)
    (hdecay : Tendsto (fun k ↦ ‖p.gradient k - p.point k‖ / (κ * p.scale (k / 2) ^ 2))
      atTop (𝓝 0)) :
    ContDiff ℝ 2 (polarPerturbation p κ) ∧ ContDiff ℝ 2 (polarObjective p κ) ∧
      (∀ k, polarObjective p κ (p.point k) = (1 / 2 : ℝ) * ‖p.point k‖ ^ 2 ∧
        gradient (polarObjective p κ) (p.point k) = p.gradient k ∧
        fderiv ℝ (gradient (polarObjective p κ)) (p.point k) = 1) ∧
      polarObjective p κ 0 = 0 := by
  have h := polarGeometry_of_hypotheses p κ hstart hκ hballs hcenters hmargin hdecay
  rw [polarPerturbation_def, polarObjective_def]
  refine ⟨contDiff_perturbation h, contDiff_objective h, ?_, objective_zero h⟩
  intro k
  refine ⟨objective_center h k, ?_, hessian_objective_center h k⟩
  rw [gradient_objective_center h k, polarCoefficient_apply]
  abel

end DFP.Polar.InterpolationSum
