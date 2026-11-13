/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Recovery.Boundedness
public import glowinski_admm_counterexample.GlowinskiADMM.UpdatedTargets

@[expose] public section

open Filter ADMM.ConvergenceProof ADMM.FiniteMemory

namespace ADMM.UnitCircle.Recovery

set_option maxHeartbeats 1000000 in
-- The proof transports several finite-dimensional filter limits and the full EReal conclusion.
/-- Recovery of every reduced conclusion from square summability of the actual
constraint residual. The parameter has no certificate hypothesis: the separate
discounted unit-circle argument is responsible for proving this summability. -/
theorem reducedConclusions_of_residual_summable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {f g : (Fin m → ℝ) → EReal} (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    (hKKT : ∃ q v u, ReducedIsKKT f g q v u) (z : ReducedTrajectory f g γ)
    (hres : Summable (fun k ↦ coordinateSquare (z.q (k + 1) + z.v (k + 1)))) :
    ADMM.UpdatedTargets.ReducedConclusions z := by
  obtain ⟨qStar, vStar, uStar, hfeas, hfStar, hgStar⟩ := hKKT
  let φ := reducedNormalizedObjectives f g qStar vStar uStar
  let η : ℕ → Fin m → ℝ := fun k ↦ -(z.v k - vStar)
  let w : ℕ → Fin m → ℝ := fun k ↦ γ⁻¹ • (z.u k - uStar)
  have hdata := reduced_normalized_data hf hg hfStar hgStar
  have hgraph := reduced_normalized_graph hγ.ne' hf hg z.q z.v z.u
    qStar vStar uStar hfeas z.recurrence z.first z.second
  have hnres : Summable (fun k ↦ coordinateSquare (w (k + 1) - w k)) := by
    apply hres.congr
    intro k
    rw [show w (k + 1) - w k = z.q (k + 1) + z.v (k + 1) from
      scaled_multiplier_difference hγ.ne' z.q z.v z.u uStar z.recurrence k]
  obtain ⟨ηBar, wBar, hη, hw, _⟩ := normalized_converges_of_residual_summable hγ
    φ η w hdata.1 hdata.2 hgraph hnres
  have hv : Tendsto z.v atTop (nhds (vStar - ηBar)) := by
    have hc : Tendsto (fun _ : ℕ ↦ vStar) atTop (nhds vStar) := tendsto_const_nhds
    have h := hc.sub hη
    convert h using 1
    funext k
    dsimp only [η]
    module
  have hu : Tendsto z.u atTop (nhds (γ • wBar + uStar)) := by
    have h := (hw.const_smul γ).add_const uStar
    simpa only [w, smul_smul, mul_inv_cancel₀ hγ.ne', one_smul, sub_add_cancel] using h
  have hr : Tendsto (fun k ↦ z.q (k + 1) + z.v (k + 1)) atTop (nhds 0) := by
    have h := tendsto_zero_of_coordinateSquare hnres.tendsto_atTop_zero
    simpa only [w, scaled_multiplier_difference hγ.ne' z.q z.v z.u uStar z.recurrence]
      using h
  have hqs : Tendsto (fun k ↦ z.q (k + 1)) atTop (nhds (ηBar - vStar)) := by
    have h := hr.sub (hv.comp (tendsto_add_atTop_nat 1))
    have hlim : (0 : Fin m → ℝ) - (vStar - ηBar) = ηBar - vStar := by module
    simpa only [Function.comp_def, add_sub_cancel_right, hlim] using h
  have hq : Tendsto z.q atTop (nhds (ηBar - vStar)) :=
    (tendsto_add_atTop_iff_nat 1).1 hqs
  have hbar : ReducedIsKKT f g (ηBar - vStar) (vStar - ηBar) (γ • wBar + uStar) :=
    reduced_limit_stationary hf hg hγ.ne' z.recurrence z.first z.second hq hv hu
  have hstate := hq.prodMk_nhds (hv.prodMk_nhds hu)
  have htilt := ReducedTrajectory.tilted_values_tendsto_zero z hbar hstate
  exact ⟨ηBar - vStar, vStar - ηBar, γ • wBar + uStar, hbar, hstate,
    ReducedTrajectory.residual_tendsto_zero z hbar hstate, htilt.1, htilt.2⟩

/-- The natural full residual sequence can be used without discarding its
arbitrary initial term. -/
theorem reducedConclusions_of_full_residual_summable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {f g : (Fin m → ℝ) → EReal} (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    (hKKT : ∃ q v u, ReducedIsKKT f g q v u) (z : ReducedTrajectory f g γ)
    (hres : Summable (fun k ↦ coordinateSquare (z.q k + z.v k))) :
    ADMM.UpdatedTargets.ReducedConclusions z := by
  have hs : Summable (fun k : ℕ ↦ coordinateSquare (z.q (k + 1) + z.v (k + 1))) :=
    (summable_nat_add_iff (f := fun k ↦ coordinateSquare (z.q k + z.v k)) 1).2 hres
  exact reducedConclusions_of_residual_summable hγ hf hg hKKT z hs

end ADMM.UnitCircle.Recovery
