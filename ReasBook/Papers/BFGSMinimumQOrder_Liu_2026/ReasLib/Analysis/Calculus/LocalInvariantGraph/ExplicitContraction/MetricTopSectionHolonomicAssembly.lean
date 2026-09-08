module

-- Decoupled from the recurrence bridge (developed concurrently) to avoid build races:
-- imports only the Mathlib layers this packaging needs.
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Order.LeftRight

public section

noncomputable section

open scoped NNReal Topology
open Filter Set

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Steps 5–6: from one-sided sublinear envelopes to a two-sided derivative.

The radius envelope produces a sublinear bound `∀ε>0 ∃δ>0 ∀x∈(0,δ), F x ≤ ε·x` only on the
positive side.  Applying it to the defect `g(u₀+t) − g u₀ − t•v` for `t>0` and to its mirror
for `t<0` gives the full two-sided little-o characterization of `HasDerivAt g v u₀`. -/

/-- Step 5–6: a two-sided sublinear bound on the secant defect yields `HasDerivAt`.  The two
hypotheses are exactly the positive- and negative-increment envelope outputs (each phrased as
an eventual bound on the one-sided neighborhood filter). -/
theorem hasDerivAt_of_eventually_le_pos_neg
    (g : ℝ → X) (v : X) (u₀ : ℝ)
    (hpos : ∀ ε > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖g (u₀ + t) - g u₀ - t • v‖ ≤ ε * t)
    (hneg : ∀ ε > 0, ∀ᶠ t in 𝓝[<] (0 : ℝ),
      ‖g (u₀ + t) - g u₀ - t • v‖ ≤ ε * (-t)) :
    HasDerivAt g v u₀ := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  -- Assemble the eventual bound on `𝓝 0` from the two one-sided branches (the point `0` is
  -- absorbed because the defect vanishes there).
  have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      ‖g (u₀ + t) - g u₀ - t • v‖ ≤ c * ‖t‖ := by
    rw [← nhdsLT_sup_nhdsGT, Filter.eventually_sup]
    refine ⟨?_, ?_⟩
    · -- negative side: `‖t‖ = -t`.
      filter_upwards [hneg c hc, self_mem_nhdsWithin] with t ht htneg
      have htlt : t < 0 := htneg
      rw [Real.norm_eq_abs, abs_of_neg htlt]
      exact ht
    · -- positive side: `‖t‖ = t`.
      filter_upwards [hpos c hc, self_mem_nhdsWithin] with t ht htpos
      have htgt : 0 < t := htpos
      rw [Real.norm_eq_abs, abs_of_pos htgt]
      exact ht
  -- Extend from the punctured neighborhood to `𝓝 0`; at `t = 0` the bound is `0 ≤ 0`.
  have hpure : ∀ᶠ t in pure (0 : ℝ),
      ‖g (u₀ + t) - g u₀ - t • v‖ ≤ c * ‖t‖ := by
    simp
  rw [← nhdsNE_sup_pure]
  rw [Filter.eventually_sup]
  exact ⟨hbound, hpure⟩

/-- Helper for Infrastructure I.16a: explicit positive and negative secant radii are
converted into the two one-sided filter bounds needed for a derivative at u₀. -/
theorem hasDerivAt_of_secant_bounds
    (g : ℝ → X) (v : X) (u₀ : ℝ)
    (hpos : ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ‖g (u₀ + t) - g u₀ - t • v‖ ≤ ε * t)
    (hneg : ∀ ε > 0, ∃ δ > 0, ∀ t, -δ < t → t < 0 →
      ‖g (u₀ + t) - g u₀ - t • v‖ ≤ ε * (-t)) :
    HasDerivAt g v u₀ := by
  apply hasDerivAt_of_eventually_le_pos_neg g v u₀
  · intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hpos ε hε
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    exact hbound t ht.1 ht.2
  · intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hneg ε hε
    have hδneg : -δ < (0 : ℝ) := neg_lt_zero.mpr hδ
    filter_upwards [Ioo_mem_nhdsLT hδneg] with t ht
    exact hbound t ht.1 ht.2

/-- Helper for Infrastructure I.16a: convergence of a normalized secant model at zero gives the
derivative once the model agrees with the genuine secant at every nonzero increment. -/
theorem hasDerivAt_of_tendsto_normalized_secant
    (g q : ℝ → X) (v : X) (u : ℝ)
    (hq : Tendsto q (𝓝 0) (𝓝 v))
    (hsecant : ∀ t, t ≠ 0 → q t = t⁻¹ • (g (u + t) - g u)) :
    HasDerivAt g v u := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply Tendsto.congr' _ (hq.mono_left inf_le_left)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hsecant t ht

/-- Helper for Infrastructure I.16a: evaluating a BoundedContinuousFunction-valued map at a
fixed point preserves its filter convergence. -/
theorem tendsto_boundedContinuousFunction_apply
    {I α Y : Type*} [TopologicalSpace I] [TopologicalSpace α]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : I → BoundedContinuousFunction α Y)
    (f : BoundedContinuousFunction α Y) (l : Filter I) (x : α)
    (hF : Tendsto F l (𝓝 f)) :
    Tendsto (fun i ↦ F i x) l (𝓝 (f x)) := by
  exact ((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto f).comp hF

/-- Helper for Infrastructure I.16a: a convergent BoundedContinuousFunction-valued secant,
after fixed-point evaluation and constant scaling, yields the derivative of the underlying map. -/
theorem hasDerivAt_of_tendsto_boundedContinuousFunction_secant
    {α Y : Type*} [TopologicalSpace α]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : ℝ → Y) (sec : ℝ → BoundedContinuousFunction α Y)
    (a : BoundedContinuousFunction α Y) (scale : ℝ) (x : α) (v : Y) (u : ℝ)
    (hsec : Tendsto sec (𝓝 0) (𝓝 a))
    (hscale : ∀ t, t ≠ 0 →
      scale • sec t x = t⁻¹ • (g (u + t) - g u))
    (hvalue : scale • a x = v) :
    HasDerivAt g v u := by
  have heval : Tendsto (fun t ↦ sec t x) (𝓝 0) (𝓝 (a x)) :=
    tendsto_boundedContinuousFunction_apply sec a (𝓝 0) x hsec
  have hscaled : Tendsto (fun t ↦ scale • sec t x) (𝓝 0)
      (𝓝 (scale • a x)) := by
    exact tendsto_const_nhds.smul heval
  rw [hvalue] at hscaled
  exact hasDerivAt_of_tendsto_normalized_secant g (fun t ↦ scale • sec t x) v u
    hscaled hscale

/-- Helper for Infrastructure I.16a: a pointwise derivative field that is continuous upgrades the
underlying scalar map to a globally first-order continuously differentiable map. -/
theorem contDiff_one_of_hasDerivAt_continuous
    (g v : ℝ → X)
    (hderiv : ∀ u, HasDerivAt g (v u) u)
    (hv : Continuous v) :
    ContDiff ℝ 1 g := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro u
    exact (hderiv u).differentiableAt
  · have hderiv_eq : deriv g = v := by
      funext u
      exact (hderiv u).deriv
    rw [hderiv_eq]
    exact hv

/-- Helper for Infrastructure I.16a: a bounded continuous secant family with a continuous limit
field yields first-order continuous differentiability when its scaled evaluations are the genuine
nonzero secants at every base point. -/
theorem contDiff_one_of_tendsto_boundedContinuousFunction_secant
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : ℝ → Y) (sec : ℝ → BoundedContinuousFunction ℝ Y)
    (a : BoundedContinuousFunction ℝ Y) (scale : ℝ) (v : ℝ → Y)
    (hsec : Tendsto sec (𝓝 0) (𝓝 a))
    (hscale : ∀ u t, t ≠ 0 →
      scale • sec t u = t⁻¹ • (g (u + t) - g u))
    (hvalue : ∀ u, scale • a u = v u)
    (hv : Continuous v) :
    ContDiff ℝ 1 g := by
  apply contDiff_one_of_hasDerivAt_continuous g v ?_ hv
  intro u
  apply hasDerivAt_of_tendsto_boundedContinuousFunction_secant
    g sec a scale u (v u) u hsec
  · intro t ht
    exact hscale u t ht
  · exact hvalue u

/-! ## Steps 7–8: curry packaging of a scalar top-jet derivative.

Given a scalar derivative `HasDerivAt (iteratedDeriv m ζ) v u` of the top jet, we package it into
the multilinear holonomic obligation

  `HasFDerivAt (fun y ↦ (ftaylorSeries ℝ ζ y) m) A u`

where `A : ℝ →L[ℝ] (ℝ [×m]→L[ℝ] X)` is the `curryLeft` of a continuous multilinear section value.
This generalizes the order-one bridge `secantCertificateOneSectionValue_*` (which lives in a
cyclic-import file) to arbitrary order `m`. -/

/-- The multilinear section value at order `m` determined by a scalar derivative value `v : X`.
It is the `uncurryLeft` of the linear map `t ↦ t • (piFieldEquiv v)`, so its `curryLeft` recovers
exactly that map. -/
noncomputable def topSectionValue (m : ℕ) (v : X) : (ℝ [×(m + 1)]→L[ℝ] X) :=
  (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
    ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X) v)).uncurryLeft

/-- Step 9: continuity of the section `u ↦ topSectionValue m (v u)` reduces to continuity of `v`.
The map factors as `v ↦ piFieldEquiv v ↦ smulRight 1 (·) ↦ ·.uncurryLeft`, each stage a continuous
(linear) construction. -/
theorem continuous_topSectionValue (m : ℕ) (v : ℝ → X) (hv : Continuous v) :
    Continuous (fun u ↦ topSectionValue m (v u)) := by
  -- Stage 1: `x ↦ piFieldEquiv x` is continuous (a linear isometry equiv).
  have h1 : Continuous (fun x : X ↦ (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X) x) :=
    (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X).continuous
  -- Stage 2: `w ↦ smulRight (1) w = smulRightL ℝ ℝ _ 1 w` is a continuous linear map.
  have h2 : Continuous (fun w : (ℝ [×m]→L[ℝ] X) ↦
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w) := by
    have hcont := (ContinuousLinearMap.smulRightL ℝ ℝ (ℝ [×m]→L[ℝ] X)
      (1 : ℝ →L[ℝ] ℝ)).continuous
    refine hcont.congr ?_
    intro w
    simp [ContinuousLinearMap.smulRightL_apply_apply]
  -- Stage 3: the inverse leg of the curry isometry equiv is continuous.  Compose it (kept in the
  -- equiv's own type language, not restated as a `fun g ↦ uncurryLeft g`, which fails to infer the
  -- multilinear family) with stages 1–2, then identify with `topSectionValue` (defeq via
  -- `(equiv).symm w = w.uncurryLeft`).
  have hsymm := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => ℝ) X).symm.continuous
  have hcomp := hsymm.comp ((h2.comp h1).comp hv)
  refine hcomp.congr ?_
  intro u
  rfl

/-- The `curryLeft` of `topSectionValue m v` is the linear map `t ↦ t • (piFieldEquiv v)`. -/
theorem topSectionValue_curryLeft (m : ℕ) (v : X) :
    (topSectionValue m v).curryLeft =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X) v) := by
  dsimp only [topSectionValue]
  exact ContinuousLinearMap.curry_uncurryLeft _

/-- Step 7–8: a scalar derivative of the top jet upgrades to the multilinear holonomic
obligation.  `A u := (topSectionValue m (v u)).curryLeft` is the required Fréchet derivative of
`y ↦ iteratedFDeriv ℝ m ζ y` at `u`. -/
theorem hasFDerivAt_iteratedFDeriv_of_hasDerivAt
    (m : ℕ) (ζ : ℝ → X) (v : ℝ → X) (u : ℝ)
    (hderiv : HasDerivAt (iteratedDeriv m ζ) (v u) u) :
    HasFDerivAt (fun y ↦ (ftaylorSeries ℝ ζ y) m)
      (topSectionValue m (v u)).curryLeft u := by
  -- Both `ftaylorSeries ℝ ζ` and `piFieldEquiv ∘ iteratedDeriv m ζ` represent the
  -- `m`-th iterated Fréchet derivative.
  have hcomp_eq : (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) m) =
      (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X) ∘ (iteratedDeriv m ζ) := by
    funext y
    -- `ftaylorSeries ℝ ζ y m = iteratedFDeriv ℝ m ζ y` definitionally.
    change iteratedFDeriv ℝ m ζ y = _
    rw [iteratedFDeriv_eq_equiv_comp]
  rw [hcomp_eq]
  -- The linear isometry equiv composes with the scalar `HasFDerivAt`.
  have hlin : HasFDerivAt
      (fun w : X ↦ (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X) w)
      ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X).toContinuousLinearEquiv
        : X →L[ℝ] (ℝ [×m]→L[ℝ] X))
      (iteratedDeriv m ζ u) :=
    (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X).toContinuousLinearEquiv.hasFDerivAt
  have hfd_scalar : HasFDerivAt (iteratedDeriv m ζ)
      (ContinuousLinearMap.toSpanSingleton ℝ (v u)) u :=
    hderiv.hasFDerivAt
  have hcomp := hlin.comp u hfd_scalar
  -- Identify the composed derivative with `(topSectionValue m (v u)).curryLeft`.
  rw [topSectionValue_curryLeft]
  -- `piFieldEquiv.toCLE ∘L toSpanSingleton (v u) = smulRight 1 (piFieldEquiv (v u))`.
  have hmapeq :
      ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X).toContinuousLinearEquiv
          : X →L[ℝ] (ℝ [×m]→L[ℝ] X)) ∘L (ContinuousLinearMap.toSpanSingleton ℝ (v u))
        = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
            ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X) (v u)) := by
    apply ContinuousLinearMap.ext
    intro t
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      map_smul]
  rw [← hmapeq]
  exact hcomp

/-- Helper for Infrastructure I.16a: explicit two-sided secant bounds on the scalar
`m`-th iterated derivative produce the curried Fréchet derivative required by a holonomic
top section. -/
theorem hasFDerivAt_iteratedFDeriv_of_secant_bounds
    (m : ℕ) (ζ : ℝ → X) (v : ℝ → X) (u : ℝ)
    (hpos : ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ‖iteratedDeriv m ζ (u + t) - iteratedDeriv m ζ u - t • v u‖ ≤ ε * t)
    (hneg : ∀ ε > 0, ∃ δ > 0, ∀ t, -δ < t → t < 0 →
      ‖iteratedDeriv m ζ (u + t) - iteratedDeriv m ζ u - t • v u‖ ≤ ε * (-t)) :
    HasFDerivAt (fun y ↦ (ftaylorSeries ℝ ζ y) m)
      (topSectionValue m (v u)).curryLeft u := by
  have hderiv : HasDerivAt (iteratedDeriv m ζ) (v u) u :=
    hasDerivAt_of_secant_bounds (iteratedDeriv m ζ) (v u) u hpos hneg
  exact hasFDerivAt_iteratedFDeriv_of_hasDerivAt m ζ v u hderiv

end LocalInvariantGraph
