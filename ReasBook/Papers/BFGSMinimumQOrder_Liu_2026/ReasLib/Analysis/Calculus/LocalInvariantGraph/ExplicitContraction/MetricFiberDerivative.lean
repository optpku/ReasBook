module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricInvariantGraph
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Operator.Prod

public section

noncomputable section

universe u

/-! ## Fiber derivative of the metric remainder (base order `m = 0`)

The metric fixed-graph equation reads `ζ ∘ φ = L ∘ ζ + g` with `g u = (R (u, ζ u)).2`.
The fiber-contraction cocycle that propagates differentiability from order to order is
`L + ∂₂R`, where `∂₂R` is the derivative of the remainder `R` in its *fiber* (second) slot.
The present file isolates the seed of that cocycle at order `m = 0`: the first-slot
fiber derivative `derivFiber`, the bound `‖derivFiber‖ ≤ ε` (from `R` being `ε`-Lipschitz),
and the concrete value `derivFiber 0 = L` at the origin (from the center-stable germ).

Higher-order Faà-di-Bruno isolation of `∂₂R` (the atomic term of `iteratedDeriv m g`) is
the recursive step and is deferred; only the non-circular seed lives here. -/

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The fiber (second-slot) derivative of the metric remainder `R` at a base point `u`,
viewed as a continuous linear map `X →L[ℝ] X`.  Concretely it is the derivative of the
fiber slice `x ↦ R (u, x)` at `ζ u`, equivalently the second column of the full derivative
`fderiv R (u, ζ u) ∘ inr`. -/
def derivFiber
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) : X →L[ℝ] X :=
  (ContinuousLinearMap.snd ℝ ℝ X).comp
    ((fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp (ContinuousLinearMap.inr ℝ ℝ X))

/-- Application form of `derivFiber`: `derivFiber d ζ u w = (fderiv R (u, ζ u) (0, w)).2`, i.e. the
second-slot column of the full derivative.  Exposed for downstream leaves that cannot unfold the
`derivFiber` definition across the module boundary. -/
theorem derivFiber_apply
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) (w : X) :
    derivFiber d ζ u w = ((fderiv ℝ d.R (u, (ζ : ℝ → X) u)) (0, w)).2 := by
  rw [derivFiber]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.inr_apply]

/-- The fiber derivative is bounded in norm by `ε`: the remainder `R` is `ε`-Lipschitz, so
its full derivative has norm `≤ ε` at every point, and `∂₂R` is a sub-column
(`‖snd‖ ≤ 1` and `‖inr‖ ≤ 1` since both are linear isometries). -/
theorem norm_derivFiber_le
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) :
    ‖derivFiber d ζ u‖ ≤ (d.epsilon : ℝ) := by
  have hR : DifferentiableAt ℝ d.R (u, (ζ : ℝ → X) u) :=
    (d.hR_smooth.of_le (by exact_mod_cast le_trans one_le_two d.hnu)).contDiffAt.differentiableAt
      one_ne_zero
  -- `‖fderiv R‖ ≤ ε` from the Lipschitz bound; `‖snd‖ ≤ 1` and `‖inr‖ ≤ 1`.
  have hfderiv : ‖fderiv ℝ d.R (u, (ζ : ℝ → X) u)‖ ≤ (d.epsilon : ℝ) :=
    norm_fderiv_le_of_lipschitz (𝕜 := ℝ) d.hR_lipschitz
  have hsnd : ‖ContinuousLinearMap.snd ℝ ℝ X‖ ≤ 1 :=
    ContinuousLinearMap.norm_snd_le ℝ ℝ X
  have hinr : ‖ContinuousLinearMap.inr ℝ ℝ X‖ ≤ 1 :=
    ContinuousLinearMap.norm_inr_le_one ℝ ℝ X
  -- `derivFiber = snd ∘ fderiv R ∘ inr`, so its norm is bounded by `‖fderiv R‖`.
  calc
    ‖derivFiber d ζ u‖
      = ‖(ContinuousLinearMap.snd ℝ ℝ X).comp
          ((fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp (ContinuousLinearMap.inr ℝ ℝ X))‖ := rfl
    _ ≤ ‖ContinuousLinearMap.snd ℝ ℝ X‖ *
          ‖(fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp (ContinuousLinearMap.inr ℝ ℝ X)‖ :=
      (ContinuousLinearMap.snd ℝ ℝ X).opNorm_comp_le _
    _ ≤ 1 *
          ‖(fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp (ContinuousLinearMap.inr ℝ ℝ X)‖ :=
      mul_le_mul_of_nonneg_right hsnd (norm_nonneg _)
    _ = ‖(fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp (ContinuousLinearMap.inr ℝ ℝ X)‖ := one_mul _
    _ ≤ ‖fderiv ℝ d.R (u, (ζ : ℝ → X) u)‖ * ‖ContinuousLinearMap.inr ℝ ℝ X‖ :=
      (fderiv ℝ d.R (u, (ζ : ℝ → X) u)).opNorm_comp_le _
    _ ≤ ‖fderiv ℝ d.R (u, (ζ : ℝ → X) u)‖ * 1 :=
      mul_le_mul_of_nonneg_left hinr (norm_nonneg _)
    _ = ‖fderiv ℝ d.R (u, (ζ : ℝ → X) u)‖ := mul_one _
    _ ≤ (d.epsilon : ℝ) := hfderiv

/-- At the origin, the fiber derivative of the remainder equals the stable block `L`: this is
the center-stable germ `F = centerStable L + O(‖x‖²)`, whose derivative at zero is
`centerStable L`, whose second column is exactly `L`. -/
theorem derivFiber_zero
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hR_deriv : HasFDerivAt d.R (LocalCutoff.centerStable d.L) (0, 0)) :
    derivFiber d ζ 0 = d.L := by
  -- `derivFiber d ζ 0 = snd ∘ fderiv R (0, ζ 0) ∘ inr`.  Since `ζ 0 = 0`, this is
  -- `snd ∘ fderiv R (0,0) ∘ inr = snd ∘ centerStable d.L ∘ inr = L`.
  have hζ0 : (ζ : ℝ → X) 0 = 0 := by
    simpa using (SmallLipschitzGraph.zero_apply ζ)
  have hfderiv : fderiv ℝ d.R (0, (ζ : ℝ → X) 0) = LocalCutoff.centerStable d.L := by
    rw [hζ0]
    exact hR_deriv.fderiv
  -- Reduce to the pointwise identity `(snd ∘ centerStable d.L ∘ inr) z = L z`.
  rw [derivFiber, hfderiv, ContinuousLinearMap.ext_iff]
  intro z
  -- `inr z = (0, z)`, `centerStable d.L (0, z) = (0, L z)`, and `snd (0, L z) = L z`.
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    LocalCutoff.centerStable_apply, ContinuousLinearMap.coe_snd', Prod.snd_zero]

/-- Helper for Infrastructure I.16a: along a continuous graph, the fiber derivative of a
`C²` metric remainder varies continuously with the center coordinate. -/
theorem continuous_derivFiber
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) :
    Continuous (fun u => derivFiber d ζ u) := by
  have hν_pos : 0 < d.nu := by
    exact Nat.zero_lt_two.trans_le d.hnu
  have hR_fderiv : Continuous (fderiv ℝ d.R) :=
    d.hR_smooth.continuous_fderiv (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hν_pos))
  have hζ_cont : Continuous (ζ : ℝ → X) := by
    exact ζ.1.continuous
  have hgraph : Continuous (fun u : ℝ => (u, (ζ : ℝ → X) u)) :=
    continuous_id.prodMk hζ_cont
  have hfiber : Continuous
      (fun u : ℝ => fderiv ℝ d.R (u, (ζ : ℝ → X) u)) :=
    hR_fderiv.comp hgraph
  have hinr : Continuous (fun _ : ℝ => ContinuousLinearMap.inr ℝ ℝ X) :=
    continuous_const
  have hinner : Continuous
      (fun u : ℝ => (fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp
        (ContinuousLinearMap.inr ℝ ℝ X)) :=
    hfiber.clm_comp hinr
  have hsnd : Continuous (fun _ : ℝ => ContinuousLinearMap.snd ℝ ℝ X) :=
    continuous_const
  have houter : Continuous
      (fun u : ℝ => (ContinuousLinearMap.snd ℝ ℝ X).comp
        ((fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp
          (ContinuousLinearMap.inr ℝ ℝ X))) :=
    hsnd.clm_comp hinner
  exact houter

/-- Helper for Infrastructure I.16a: the center component of the derivative of the metric
remainder in its fiber slot, viewed as a continuous linear map `X →L[ℝ] ℝ`. -/
def derivCenterFiber
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) : X →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ X).comp
    ((fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp (ContinuousLinearMap.inr ℝ ℝ X))

/-- Helper for Infrastructure I.16a: applying `derivCenterFiber d ζ u` to `w` gives the
center component of `fderiv ℝ d.R (u, ζ u)` in the fiber direction `(0, w)`. -/
theorem derivCenterFiber_apply
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) (w : X) :
    derivCenterFiber d ζ u w = ((fderiv ℝ d.R (u, (ζ : ℝ → X) u)) (0, w)).1 := by
  rw [derivCenterFiber]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.inr_apply]

/-- Helper for Infrastructure I.16a: the center component of the fiber derivative of the
metric remainder has operator norm at most `d.epsilon`. -/
theorem norm_derivCenterFiber_le
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) :
    ‖derivCenterFiber d ζ u‖ ≤ (d.epsilon : ℝ) := by
  have hfderiv : ‖fderiv ℝ d.R (u, (ζ : ℝ → X) u)‖ ≤ (d.epsilon : ℝ) :=
    norm_fderiv_le_of_lipschitz (𝕜 := ℝ) d.hR_lipschitz
  have hfst : ‖ContinuousLinearMap.fst ℝ ℝ X‖ ≤ 1 :=
    ContinuousLinearMap.norm_fst_le ℝ ℝ X
  have hinr : ‖ContinuousLinearMap.inr ℝ ℝ X‖ ≤ 1 :=
    ContinuousLinearMap.norm_inr_le_one ℝ ℝ X
  calc
    ‖derivCenterFiber d ζ u‖
        = ‖(ContinuousLinearMap.fst ℝ ℝ X).comp
            ((fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp
              (ContinuousLinearMap.inr ℝ ℝ X))‖ := rfl
    _ ≤ ‖ContinuousLinearMap.fst ℝ ℝ X‖ *
          ‖(fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp
            (ContinuousLinearMap.inr ℝ ℝ X)‖ :=
      (ContinuousLinearMap.fst ℝ ℝ X).opNorm_comp_le _
    _ ≤ 1 * ‖(fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp
          (ContinuousLinearMap.inr ℝ ℝ X)‖ :=
      mul_le_mul_of_nonneg_right hfst (norm_nonneg _)
    _ = ‖(fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp
          (ContinuousLinearMap.inr ℝ ℝ X)‖ := one_mul _
    _ ≤ ‖fderiv ℝ d.R (u, (ζ : ℝ → X) u)‖ *
          ‖ContinuousLinearMap.inr ℝ ℝ X‖ :=
      (fderiv ℝ d.R (u, (ζ : ℝ → X) u)).opNorm_comp_le _
    _ ≤ ‖fderiv ℝ d.R (u, (ζ : ℝ → X) u)‖ * 1 :=
      mul_le_mul_of_nonneg_left hinr (norm_nonneg _)
    _ = ‖fderiv ℝ d.R (u, (ζ : ℝ → X) u)‖ := mul_one _
    _ ≤ (d.epsilon : ℝ) := hfderiv

/-- Helper for Infrastructure I.16a: along a continuous graph, the center component of the
fiber derivative of a `C²` metric remainder varies continuously with the center coordinate. -/
theorem continuous_derivCenterFiber
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) :
    Continuous (fun u => derivCenterFiber d ζ u) := by
  have hν_pos : 0 < d.nu := by
    exact Nat.zero_lt_two.trans_le d.hnu
  have hR_fderiv : Continuous (fderiv ℝ d.R) :=
    d.hR_smooth.continuous_fderiv (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hν_pos))
  have hζ_cont : Continuous (ζ : ℝ → X) := by
    exact ζ.1.continuous
  have hgraph : Continuous (fun u : ℝ => (u, (ζ : ℝ → X) u)) :=
    continuous_id.prodMk hζ_cont
  have hfiber : Continuous
      (fun u : ℝ => fderiv ℝ d.R (u, (ζ : ℝ → X) u)) :=
    hR_fderiv.comp hgraph
  have hinr : Continuous (fun _ : ℝ => ContinuousLinearMap.inr ℝ ℝ X) :=
    continuous_const
  have hinner : Continuous
      (fun u : ℝ => (fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp
        (ContinuousLinearMap.inr ℝ ℝ X)) :=
    hfiber.clm_comp hinr
  have hfst : Continuous (fun _ : ℝ => ContinuousLinearMap.fst ℝ ℝ X) :=
    continuous_const
  have houter : Continuous
      (fun u : ℝ => (ContinuousLinearMap.fst ℝ ℝ X).comp
        ((fderiv ℝ d.R (u, (ζ : ℝ → X) u)).comp
          (ContinuousLinearMap.inr ℝ ℝ X))) :=
    hfst.clm_comp hinner
  exact houter

end LocalInvariantGraph
