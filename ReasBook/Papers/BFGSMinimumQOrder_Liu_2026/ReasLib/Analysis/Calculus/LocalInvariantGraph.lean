module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.MetricCutoff
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricInvariantGraph
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiniteSmooth
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.MetricInverse
public import ReasLib.LinearAlgebra.SpectralRadius.ContractingNorm
public import Mathlib.Analysis.Normed.Lp.WithLp

public section

open Filter
open scoped ENNReal
open scoped Topology

universe u

namespace LocalInvariantGraph

/-- The norm on a type copy obtained by evaluating an equivalent seminorm on the
underlying vector. -/
@[reducible]
private def renormedNorm {X : Type u} [AddCommGroup X] [Module ℝ X]
    (p : Seminorm ℝ X) : Norm (WithLp ∞ X) where
  norm x := p x.ofLp

/-- An equivalent seminorm separates points and therefore defines a normed-space core
on the corresponding type copy. -/
private theorem renormedNormCore {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (p : Seminorm ℝ X)
    (hp : p.IsEquivalent (normSeminorm ℝ X)) :
    @NormedSpace.Core ℝ (WithLp ∞ X) inferInstance inferInstance inferInstance
      (renormedNorm p) := by
  -- Local instance justification (renorming): the core fields must evaluate the newly defined
  -- norm, while `WithLp` intentionally supplies no norm instance for an arbitrary carrier.
  letI : Norm (WithLp ∞ X) := renormedNorm p
  rw [Seminorm.isEquivalent_iff] at hp
  obtain ⟨a, b, ha, hb, hp_bound⟩ := hp
  refine {
    norm_nonneg := ?_
    norm_smul := ?_
    norm_triangle := ?_
    norm_eq_zero_iff := ?_ }
  · intro x
    exact apply_nonneg p x.ofLp
  · intro c x
    exact map_smul_eq_mul p c x.ofLp
  · intro x y
    exact map_add_le_add p x.ofLp y.ofLp
  · intro x
    constructor
    · intro hx
      have hlower := (hp_bound x.ofLp).1
      have hnorm : ‖x.ofLp‖ = 0 := by
        change p x.ofLp = 0 at hx
        have ha_real : (0 : ℝ) < a := NNReal.coe_pos.mpr ha
        have hlower_zero : (a : ℝ) * ‖x.ofLp‖ ≤ 0 := by
          simpa only [coe_normSeminorm, hx] using hlower
        nlinarith [norm_nonneg x.ofLp]
      exact WithLp.ofLp_injective (p := ∞) (norm_eq_zero.mp hnorm)
    · intro hx
      subst x
      exact map_zero p

/- The cutoff construction starts from the nonlinear remainder obtained by subtracting the
  center-stable linear part.  These two small interface lemmas expose its zero jet without
  unfolding any cutoff or graph-transform construction. -/

/-- Helper for Infrastructure I.16a: subtracting the center-stable linearization from a map
    fixing the origin gives a remainder that vanishes at the origin. -/
theorem centerStable_remainder_zero {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (F : ℝ × X → ℝ × X) (L : X →L[ℝ] X)
    (hF_zero : F (0, 0) = (0, 0)) :
    (fun x ↦ F x - LocalCutoff.centerStable L x) (0, 0) = (0, 0) := by
  -- The linear center-stable block also sends the origin to the origin, so the
  -- subtraction reduces directly to the assumed fixed-point equation.
  dsimp
  rw [hF_zero]
  simp only [LocalCutoff.centerStable_apply, map_zero, sub_self]
  exact (Prod.mk_zero_zero : ((0, 0) : ℝ × X) = 0).symm

/-- Helper for Infrastructure I.16a: the nonlinear remainder has zero derivative when the
    derivative of the original map is the center-stable linearization. -/
theorem centerStable_remainder_hasFDerivAt_zero {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : ℝ × X → ℝ × X) (L : X →L[ℝ] X)
    (hF_deriv : HasFDerivAt F (LocalCutoff.centerStable L) (0, 0)) :
    HasFDerivAt (F - (LocalCutoff.centerStable L : ℝ × X → ℝ × X))
      (0 : (ℝ × X) →L[ℝ] (ℝ × X)) (0, 0) := by
  -- Differentiate the subtraction and normalize the resulting zero linear map.
  have hsub := hF_deriv.sub (LocalCutoff.centerStable L).hasFDerivAt
  have hprod_add :
      (Prod.instAddCommGroup : AddCommGroup (ℝ × X)) =
        Prod.normedAddCommGroup.toAddCommGroup := by
    with_reducible_and_instances rfl
  have hprod_module :
      (Prod.instModule : Module ℝ (ℝ × X)) =
        Prod.normedSpace.toModule := by
    with_reducible_and_instances rfl
  have hprod_top :
      (instTopologicalSpaceProd : TopologicalSpace (ℝ × X)) =
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    with_reducible_and_instances rfl
  simpa only [hprod_add, hprod_module, hprod_top, Pi.sub_apply, sub_self] using hsub

/- The local smoothness of the original map passes directly to its nonlinear
  remainder after subtracting the fixed linear center-stable block. -/

/-- Helper for Infrastructure I.16a: the nonlinear remainder inherits the
    finite smoothness of the original map at the fixed point. -/
theorem centerStable_remainder_contDiffAt {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (ν : ℕ)
    (F : ℝ × X → ℝ × X) (L : X →L[ℝ] X)
    (hF_smooth : ContDiffAt ℝ ν F (0, 0)) :
    ContDiffAt ℝ ν (fun x ↦ F x - LocalCutoff.centerStable L x) (0, 0) := by
  -- The linear block is smooth everywhere, so subtraction preserves the local
  -- `ContDiffAt` regularity needed for the cutoff construction.
  exact hF_smooth.sub (LocalCutoff.centerStable L).contDiff.contDiffAt

/- The nonlinear remainder is also a canonical algebraic summand of the original map. -/

/-- Every map splits into its center-stable linear part and the corresponding nonlinear remainder. -/
theorem centerStable_remainder_split {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (F : ℝ × X → ℝ × X) (L : X →L[ℝ] X) :
    F = fun x ↦
      LocalCutoff.centerStable L x + (F x - LocalCutoff.centerStable L x) := by
  -- The split is pointwise ring algebra, so it is independent of any regularity assumptions.
  funext x
  abel

/-- Helper for Infrastructure I.16a: finite smoothness at the origin supplies a
    neighborhood on which the nonlinear remainder is `ContDiffOn`. -/
theorem exists_remainder_contDiffOn_nhds {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (ν : ℕ)
    (F : ℝ × X → ℝ × X) (L : X →L[ℝ] X)
    (hF_smooth : ContDiffAt ℝ ν F (0, 0)) :
    ∃ U ∈ 𝓝 (0, 0),
      ContDiffOn ℝ ν (fun x ↦ F x - LocalCutoff.centerStable L x) U := by
  -- First restrict the given local regularity to one neighborhood, then subtract
  -- the globally smooth center-stable linear block on that same set.
  obtain ⟨U, hU, hF_on⟩ := hF_smooth.contDiffOn le_rfl (by simp)
  refine ⟨U, hU, ?_⟩
  exact hF_on.sub (LocalCutoff.centerStable L).contDiff.contDiffOn

/-- Helper for Infrastructure I.16a: a smooth zero-jet germ admits a compactly supported
    smooth representative with any prescribed positive Lipschitz bound and the same zero
    derivative. -/
theorem cutoffRemainderWithZeroDerivative {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (ν : ℕ) (N : X → X) (hν : 1 ≤ ν)
    (hN_smooth : ContDiffAt ℝ ν N 0) (hN_zero : N 0 = 0)
    (hN_deriv : HasFDerivAt N (0 : X →L[ℝ] X) 0)
    {epsilon : NNReal} (hepsilon : 0 < epsilon) :
    ∃ R : X → X,
      ContDiff ℝ ν R ∧ HasCompactSupport R ∧ R 0 = 0 ∧
        LipschitzWith epsilon R ∧
          HasFDerivAt R (0 : X →L[ℝ] X) 0 ∧ R =ᶠ[𝓝 0] N := by
  -- First construct the global cutoff representative using the prescribed
  -- Lipschitz constant.
  obtain ⟨R, hR_smooth, hR_support, hR_zero, hR_lipschitz, hR_germ⟩ :=
    exists_smallLipschitzCutoffRemainder ν hν N hN_smooth hN_zero hN_deriv hepsilon
  -- Its derivative is transported across the germ equality, avoiding any
  -- unfolding of the cutoff construction.
  have hR_deriv : HasFDerivAt R (0 : X →L[ℝ] X) 0 :=
    hN_deriv.congr_of_eventuallyEq hR_germ
  exact ⟨R, hR_smooth, hR_support, hR_zero, hR_lipschitz, hR_deriv, hR_germ⟩

/-- Helper for Infrastructure I.16a: a continuous compactly supported product-valued map
    has a uniform nonnegative bound on its stable coordinate. -/
theorem exists_stableCoordinateBound {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (R : ℝ × X → ℝ × X) (hR_cont : Continuous R)
    (hR_support : HasCompactSupport R) :
    ∃ stableBound : NNReal, ∀ p : ℝ × X, ‖(R p).2‖ ≤ (stableBound : ℝ) := by
  -- Compact support and continuity first bound the full product norm.
  obtain ⟨C, hC⟩ := hR_cont.bounded_above_of_compact_support hR_support
  refine ⟨Real.toNNReal C, ?_⟩
  intro p
  -- Projection decreases the max product norm, and `toNNReal` records a
  -- nonnegative version of the resulting real bound.
  exact (norm_snd_le (R p)).trans ((hC p).trans (Real.le_coe_toNNReal C))

/- The cutoff construction will approximate the nonlinear remainder rather than the
   original map itself.  This bridge records the corresponding germ equality at the
   natural map level, so later graph-transfer proofs need only supply the remainder germ. -/

/-- A germwise nonlinear remainder reconstructs the original map from its center-stable
    linear part. -/
theorem centerStable_remainder_germ {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (F : ℝ × X → ℝ × X) (L : X →L[ℝ] X)
    (R : ℝ × X → ℝ × X)
    (hR : R =ᶠ[𝓝 (0, 0)]
      (fun x ↦ F x - LocalCutoff.centerStable L x)) :
    (fun x ↦ LocalCutoff.centerStable L x + R x) =ᶠ[𝓝 (0, 0)] F := by
  -- Rewrite the remainder on the neighborhood and close the pointwise algebraic split.
  filter_upwards [hR] with x hx
  rw [hx]
  abel

/-- A remainder germ remains a map germ after composition with a graph tending to the fixed point
    (Infrastructure I.16a). -/
theorem centerStable_remainder_germ_comp_graph {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (F : ℝ × X → ℝ × X) (L : X →L[ℝ] X)
    (R : ℝ × X → ℝ × X) (ζ : ℝ → X)
    (hR : R =ᶠ[𝓝 (0, 0)]
      (fun x ↦ F x - LocalCutoff.centerStable L x))
    (hgraph : Tendsto (fun u : ℝ ↦ (u, ζ u)) (𝓝 0) (𝓝 (0, 0))) :
    (fun u ↦ LocalCutoff.centerStable L (u, ζ u) + R (u, ζ u)) =ᶠ[𝓝 0]
      (fun u ↦ F (u, ζ u)) := by
  -- Pull the remainder germ back along the graph and close the pointwise split algebraically.
  filter_upwards [hR.comp_tendsto hgraph] with u hu
  have hu' : R (u, ζ u) = F (u, ζ u) - LocalCutoff.centerStable L (u, ζ u) := by
    simpa only [Function.comp_apply] using hu
  rw [hu']
  abel

/- The metric certificate constructor below keeps the large structure literal and all inverse
  estimates behind one owner-facing adapter. -/

/-- Helper for Infrastructure I.16a (Finite-smooth invariant graph under an explicit stable contraction):
    assemble a metric graph-transform certificate from its quantitative hypotheses. -/
def metricGraphTransformData_of_cutoff
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ν : ℕ) (R : ℝ × X → ℝ × X) (L : X →L[ℝ] X)
    (radius slope epsilon lower linearRate stableBound : NNReal)
    (hν : 2 ≤ ν) (hR_smooth : ContDiff ℝ ν R)
    (hR_support : HasCompactSupport R) (hR_zero : R 0 = 0)
    (hR_lipschitz : LipschitzWith epsilon R) (hslope_one : slope ≤ 1)
    (hlower_pos : 0 < lower) (hlower_add : lower + epsilon = 1)
    (h_center_bijective : ∀ zeta : SmallLipschitzGraph X radius slope,
      Function.Bijective (fun u ↦ u + (R (u, zeta u)).1))
    (h_inverse_lipschitz : ∀ zeta : SmallLipschitzGraph X radius slope,
      LipschitzWith lower⁻¹ (Function.invFun (fun u ↦ u + (R (u, zeta u)).1)))
    (h_inverse_dist : ∀ (zeta eta : SmallLipschitzGraph X radius slope) (ubar : ℝ),
      dist (Function.invFun (fun u ↦ u + (R (u, zeta u)).1) ubar)
        (Function.invFun (fun u ↦ u + (R (u, eta u)).1) ubar) ≤
        (lower⁻¹ : ℝ) * (epsilon : ℝ) * dist zeta eta)
    (hL : ‖L‖ ≤ (linearRate : ℝ)) (hlinearRate : linearRate < 1)
    (hstable_bound : ∀ p, ‖(R p).2‖ ≤ (stableBound : ℝ))
    (hradius : linearRate * radius + stableBound ≤ radius)
    (hslope : (linearRate * slope + epsilon) * lower⁻¹ ≤ slope)
    (hrate : metricGraphTransformRate lower linearRate epsilon slope < 1) :
    MetricGraphTransformData X := {
    nu := ν
    R := R
    L := L
    radius := radius
    slope := slope
    epsilon := epsilon
    lower := lower
    linearRate := linearRate
    stableBound := stableBound
    hnu := hν
    hR_smooth := hR_smooth
    hR_support := hR_support
    hR_zero := hR_zero
    hR_lipschitz := hR_lipschitz
    hslope_one := hslope_one
    hlower_pos := hlower_pos
    hlower_add := hlower_add
    h_center_bijective := h_center_bijective
    h_inverse_lipschitz := h_inverse_lipschitz
    h_inverse_dist := h_inverse_dist
    hL := hL
    hlinearRate := hlinearRate
    hstable_bound := hstable_bound
    hradius := hradius
    hslope := hslope
    hrate := hrate }

/- The canonical parameter selector and fixed-graph regularity theorem live in the
   metric explicit-contraction owner module imported above. -/

/- A post-cutoff stable bound can always be absorbed into a radius when the linear rate is
   strictly below one. -/
/-- For a nonnegative rate below one, a stable bound admits an invariant radius inequality. -/
theorem metricRadius_bound {q stableBound : NNReal} (hq : (q : ℝ) < 1) :
    ∃ radius : NNReal, q * radius + stableBound ≤ radius := by
  refine ⟨stableBound / (1 - q), ?_⟩
  have hqNN : q < 1 := by exact_mod_cast hq
  have hgap : 0 < (1 - q : NNReal) := tsub_pos_iff_lt.mpr hqNN
  change q * (stableBound / (1 - q)) + stableBound ≤ stableBound / (1 - q)
  field_simp [hgap.ne']
  rw [add_tsub_cancel_of_le hqNN.le, mul_one]

/-- A finite-dimensional center-stable map whose stable derivative has norm less than one
admits a finite-smooth local forward-invariant graph tangent to the center axis. -/
theorem existsOfNormLtOne {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] (ν : ℕ) (F : ℝ × X → ℝ × X)
    (L : X →L[ℝ] X) (hν : 2 ≤ ν) (hF_smooth : ContDiffAt ℝ ν F (0, 0))
    (hF_zero : F (0, 0) = (0, 0))
    (hF_deriv : HasFDerivAt F (LocalCutoff.centerStable L) (0, 0)) (hL : ‖L‖ < 1) :
    ∃ ζ : ℝ → X,
      ContDiffAt ℝ ν ζ 0 ∧
        ζ 0 = 0 ∧
            HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
            (fun u ↦ (F (u, ζ u)).2) =ᶠ[𝓝 0] fun u ↦ ζ (F (u, ζ u)).1 := by
  -- Normalize the map into its linear center-stable block and a nonlinear remainder.
  have hN_zero := centerStable_remainder_zero F L hF_zero
  have hN_deriv := centerStable_remainder_hasFDerivAt_zero F L hF_deriv
  have hN_smoothAt := centerStable_remainder_contDiffAt ν F L hF_smooth
  have hν_one : 1 ≤ ν := (by omega)
  -- Route correction: the earlier cutoff-first route created a parameter cycle; select epsilon
  -- before constructing the cutoff, since the selector is independent of the
  -- stable-coordinate bound when instantiated at zero bound.
  have ha : (‖L‖₊ : ℝ) < 1 := by simpa using hL
  obtain ⟨epsilon, lower, linearRate, _, hepsilon, hlower_pos, hlower_add,
      ha_linearRate, hlinearRate, _, hsum_le, hrate, hbunching⟩ :=
    MetricGraphTransformData.exists_metricTransformParameters ν ‖L‖₊ 0 hν ha
  -- Globalize the remainder without changing its germ or first derivative.
  obtain ⟨R, hR_smooth, hR_support, hR_zero, hR_lipschitz, hR_deriv, hR_germ⟩ :=
    cutoffRemainderWithZeroDerivative ν
      (fun x ↦ F x - LocalCutoff.centerStable L x) hν_one hN_smoothAt hN_zero
      hN_deriv hepsilon
  -- Compact support supplies the radius-control bound needed by the metric
  -- graph transform independently of the later parameter choices.
  obtain ⟨stableBound, hstableBound⟩ :=
    exists_stableCoordinateBound R hR_smooth.continuous hR_support
  have hmodel_germ := centerStable_remainder_germ F L R hR_germ
  have hlinearRate_real : (linearRate : ℝ) < 1 := by exact_mod_cast hlinearRate
  obtain ⟨radius, hradius⟩ := metricRadius_bound hlinearRate_real
  have hslope_one : (1 : NNReal) ≤ 1 := le_rfl
  have hepsilon_lt_one : epsilon < 1 := by
    rw [← hlower_add]
    exact lt_add_of_pos_left epsilon hlower_pos
  have hcenter_bijective :
      ∀ zeta : SmallLipschitzGraph X radius 1,
        Function.Bijective (fun u ↦ u + (R (u, zeta u)).1) := by
    intro zeta
    obtain ⟨e, he⟩ := exists_centerProjectionHomeomorph R hR_lipschitz zeta
      hslope_one hepsilon_lt_one
    rw [← he]
    exact e.bijective
  have hinverse_lipschitz :
      ∀ zeta : SmallLipschitzGraph X radius 1,
        LipschitzWith lower⁻¹
          (Function.invFun (fun u ↦ u + (R (u, zeta u)).1)) := by
    intro zeta
    exact lipschitzWith_invFun_centerProjection R hR_lipschitz zeta hslope_one
      lower hlower_pos hlower_add
  have hinverse_dist :
      ∀ (zeta eta : SmallLipschitzGraph X radius 1) (ubar : ℝ),
        dist (Function.invFun (fun u ↦ u + (R (u, zeta u)).1) ubar)
            (Function.invFun (fun u ↦ u + (R (u, eta u)).1) ubar) ≤
          (lower⁻¹ : ℝ) * (epsilon : ℝ) * dist zeta eta := by
    intro zeta eta ubar
    exact dist_invFun_centerProjection_le R hR_lipschitz zeta eta hslope_one
      lower hlower_pos hlower_add ubar
  have hL_bound : ‖L‖ ≤ (linearRate : ℝ) := by
    have hLa : ‖L‖ ≤ (‖L‖₊ : ℝ) := by simp
    exact hLa.trans (by exact_mod_cast ha_linearRate)
  have hslope :
      (linearRate * (1 : NNReal) + epsilon) * lower⁻¹ ≤ (1 : NNReal) := by
    simpa only [mul_one] using hsum_le
  let d : MetricGraphTransformData X := metricGraphTransformData_of_cutoff ν R L
    radius 1 epsilon lower linearRate stableBound hν hR_smooth hR_support hR_zero
    hR_lipschitz hslope_one hlower_pos hlower_add hcenter_bijective hinverse_lipschitz
    hinverse_dist hL_bound hlinearRate hstableBound hradius hslope hrate
  have hbunching_d : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1 := by
    intro r hr1 hrν
    change (metricGraphTransformRate lower linearRate epsilon 1 : ℝ) *
      (lower : ℝ)⁻¹ ^ r < 1
    exact hbunching r hr1 hrν
  have hregular : ∀ ζ : SmallLipschitzGraph X d.radius d.slope,
      d.transform ζ = ζ → ContDiffAt ℝ d.nu (ζ : ℝ → X) 0 := by
    intro ζ hfixed
    exact (metricFixedGraph_contDiff_of_bunching d hbunching_d ζ
      hfixed).contDiffAt
  have hmodel_germ_metric : F =ᶠ[𝓝 (0, 0)] metricCenterStableMap d := by
    filter_upwards [hmodel_germ.symm] with x hx
    rw [metricCenterStableMap_eq]
    simpa only [d, metricGraphTransformData_of_cutoff] using hx
  exact invariantGraph_of_metricFixedPoint_germ d hR_deriv hregular F hmodel_germ_metric

/-- A finite-dimensional center-stable map admits a finite-smooth local forward-invariant
graph when its stable derivative contracts an equivalent seminorm at a rate below one. -/
theorem existsOfEquivalentContractingSeminorm {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] (ν : ℕ) (F : ℝ × X → ℝ × X)
    (L : Module.End ℝ X) (p : Seminorm ℝ X) (r : NNReal) (hν : 2 ≤ ν)
    (hF_smooth : ContDiffAt ℝ ν F (0, 0)) (hF_zero : F (0, 0) = (0, 0))
    (hF_deriv : HasFDerivAt F
      (LocalCutoff.centerStable (Module.End.toContinuousLinearMap X L)) (0, 0))
    (hp : p.IsEquivalent (normSeminorm ℝ X)) (hL : p.IsContracting L r) (hr : r < 1) :
    ∃ ζ : ℝ → X,
      ContDiffAt ℝ ν ζ 0 ∧
        ζ 0 = 0 ∧
          HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
            (fun u ↦ (F (u, ζ u)).2) =ᶠ[𝓝 0] fun u ↦ ζ (F (u, ζ u)).1 := by
  let hcore := renormedNormCore p hp
  -- Local instance justification (renorming): `WithLp` deliberately has no arbitrary norm;
  -- this instance installs exactly the norm represented by `p`.
  letI : Norm (WithLp ∞ X) := renormedNorm p
  -- Local instance justification (renorming): the separated seminorm core supplies the metric
  -- structure needed to run the norm-contraction theorem on the type copy.
  letI : NormedAddCommGroup (WithLp ∞ X) := NormedAddCommGroup.ofCore hcore
  -- Local instance justification (renorming): the same core proves compatibility of the copied
  -- real module structure with the newly installed norm.
  letI : NormedSpace ℝ (WithLp ∞ X) := NormedSpace.ofCore hcore
  rw [Seminorm.isEquivalent_iff] at hp
  obtain ⟨a, b, ha, hb, hp_bound⟩ := hp
  have ha_real : (0 : ℝ) < a := NNReal.coe_pos.mpr ha
  have he_forward (x : WithLp ∞ X) :
      ‖(WithLp.linearEquiv ∞ ℝ X) x‖ ≤ (a : ℝ)⁻¹ * ‖x‖ := by
    change ‖x.ofLp‖ ≤ (a : ℝ)⁻¹ * p x.ofLp
    rw [le_inv_mul_iff₀ ha_real]
    simpa only [coe_normSeminorm] using (hp_bound x.ofLp).1
  have he_inverse (x : X) :
      ‖(WithLp.linearEquiv ∞ ℝ X).symm x‖ ≤ (b : ℝ) * ‖x‖ := by
    change p x ≤ (b : ℝ) * ‖x‖
    simpa only [coe_normSeminorm] using (hp_bound x).2
  let e : WithLp ∞ X ≃L[ℝ] X :=
    LinearEquiv.toContinuousLinearEquivOfBounds (WithLp.linearEquiv ∞ ℝ X)
      (a : ℝ)⁻¹ b he_forward he_inverse
  let P : (ℝ × WithLp ∞ X) ≃L[ℝ] ℝ × X :=
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr e
  let Lp : Module.End ℝ (WithLp ∞ X) := LinearMap.withLpMap ∞ L
  let Lc : WithLp ∞ X →L[ℝ] WithLp ∞ X :=
    Module.End.toContinuousLinearMap (WithLp ∞ X) Lp
  have he_apply (x : WithLp ∞ X) : e x = x.ofLp := rfl
  have he_symm_apply (x : X) : e.symm x = WithLp.toLp ∞ x := rfl
  have hP_apply (x : ℝ × WithLp ∞ X) : P x = (x.1, e x.2) := rfl
  have hP_symm_apply (x : ℝ × X) : P.symm x = (x.1, e.symm x.2) := rfl
  have hLc_apply (x : WithLp ∞ X) : Lc x = WithLp.toLp ∞ (L x.ofLp) := rfl
  rw [Seminorm.isContracting_iff] at hL
  obtain ⟨c, hc_rate, hc_bound⟩ := hL
  have hLc_bound : ‖Lc‖ ≤ (c : ℝ) := by
    apply Lc.opNorm_le_bound c.coe_nonneg
    intro x
    change p (L x.ofLp) ≤ (c : ℝ) * p x.ofLp
    exact hc_bound x.ofLp
  have hc_one : (c : ℝ) < 1 := by
    exact_mod_cast hc_rate.trans hr
  have hLc : ‖Lc‖ < 1 := hLc_bound.trans_lt hc_one
  let Fp : ℝ × WithLp ∞ X → ℝ × WithLp ∞ X := P.symm ∘ F ∘ P
  have hP_zero : P (0, 0) = (0, 0) := map_zero P
  have hP_symm_zero : P.symm (0, 0) = (0, 0) := map_zero P.symm
  have hFp_smooth : ContDiffAt ℝ ν Fp (0, 0) := by
    have hinner : ContDiffAt ℝ ν (F ∘ P) (0, 0) := by
      have htransport :=
        (P.contDiffAt_comp_iff (f := F) (x := (0, 0))).2 hF_smooth
      simpa [hP_symm_zero] using htransport
    have houter := hinner.continuousLinearMap_comp P.symm.toContinuousLinearMap
    simpa [Fp, Function.comp_def] using houter
  have hFp_zero : Fp (0, 0) = (0, 0) := by
    simp only [Fp, Function.comp_apply, hP_zero, hF_zero, hP_symm_zero]
  have hderiv_conjugate :
      P.symm.toContinuousLinearMap.comp
          ((LocalCutoff.centerStable (Module.End.toContinuousLinearMap X L)).comp
            P.toContinuousLinearMap) =
        LocalCutoff.centerStable Lc := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      (P.symm.toContinuousLinearMap.comp
          ((LocalCutoff.centerStable (Module.End.toContinuousLinearMap X L)).comp
            P.toContinuousLinearMap)) x =
          P.symm (LocalCutoff.centerStable (Module.End.toContinuousLinearMap X L) (P x)) := rfl
      _ = (x.1, WithLp.toLp ∞ (L x.2.ofLp)) := by
        rw [hP_apply, LocalCutoff.centerStable_apply, hP_symm_apply, he_apply,
          he_symm_apply]
        rfl
      _ = LocalCutoff.centerStable Lc x := by
        rw [LocalCutoff.centerStable_apply, hLc_apply]
  have hFp_deriv :
      HasFDerivAt Fp (LocalCutoff.centerStable Lc) (0, 0) := by
    have hF_at_P : HasFDerivAt F
        (LocalCutoff.centerStable (Module.End.toContinuousLinearMap X L)) (P (0, 0)) := by
      simpa only [hP_zero] using hF_deriv
    have hinner := hF_at_P.comp (0, 0) P.toContinuousLinearMap.hasFDerivAt
    have houter := P.symm.toContinuousLinearMap.hasFDerivAt.comp (0, 0) hinner
    have hconjugated : HasFDerivAt Fp
        (P.symm.toContinuousLinearMap.comp
          ((LocalCutoff.centerStable (Module.End.toContinuousLinearMap X L)).comp
            P.toContinuousLinearMap)) (0, 0) := by
      simpa [Fp, Function.comp_def] using houter
    exact hconjugated.congr_fderiv hderiv_conjugate
  obtain ⟨ζp, hζp_smooth, hζp_zero, hζp_deriv, hζp_invariant⟩ :=
    existsOfNormLtOne ν Fp Lc hν hFp_smooth hFp_zero hFp_deriv hLc
  refine ⟨fun u ↦ e (ζp u), ?_, ?_, ?_, ?_⟩
  · exact hζp_smooth.continuousLinearMap_comp e.toContinuousLinearMap
  · simp only [hζp_zero, map_zero]
  · have htransport := e.toContinuousLinearMap.hasFDerivAt.comp 0 hζp_deriv
    simpa [Function.comp_def] using htransport
  · filter_upwards [hζp_invariant] with u hu
    have htransport := congrArg e hu
    simpa [Fp, Function.comp_apply, hP_apply, hP_symm_apply, he_apply,
      he_symm_apply] using htransport

/-- A finite-dimensional center-stable map whose stable derivative has complex spectral
radius below one admits a finite-smooth local forward-invariant graph tangent to the center
axis. -/
theorem existsOfComplexSpectralRadiusLtOne {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] (ν : ℕ) (F : ℝ × X → ℝ × X)
    (L : Module.End ℝ X) (hν : 2 ≤ ν) (hF_smooth : ContDiffAt ℝ ν F (0, 0))
    (hF_zero : F (0, 0) = (0, 0))
    (hF_deriv : HasFDerivAt F
      (LocalCutoff.centerStable (Module.End.toContinuousLinearMap X L)) (0, 0))
    (hL : L.complexSpectralRadius < 1) :
    ∃ ζ : ℝ → X,
      ContDiffAt ℝ ν ζ 0 ∧
        ζ 0 = 0 ∧
          HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
            (fun u ↦ (F (u, ζ u)).2) =ᶠ[𝓝 0] fun u ↦ ζ (F (u, ζ u)).1 := by
  obtain ⟨r, hLr, hr_one⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hL
  have hr : r < 1 := by
    exact_mod_cast hr_one
  have hadapted := L.adaptedSeminorm_spec r hLr hr
  exact existsOfEquivalentContractingSeminorm ν F L (L.adaptedSeminorm r) r hν
    hF_smooth hF_zero hF_deriv hadapted.1 hadapted.2 hr

end LocalInvariantGraph
