/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.UpdatedTargets
public import glowinski_admm_counterexample.GlowinskiADMM.UnitCircleConvergence
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower.EndpointBounds
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.UpperBound

@[expose] public section

/-!
# Assembly of the updated convergence results

The complete unit-circle implication and refined upper certificate are
proved. This assembly interface accepts the lower certificate as an argument.
`GlowinskiADMM.UpdatedResults` supplies its concrete implementation to obtain
the unconditional convergence and endpoint theorems.
-/

namespace ADMM.UpdatedTargets

open Filter FiniteMemory UnitCircle ConvergenceProof

/-- A finite-dimensional injective matrix map reflects convergence of its image,
and closedness of the range provides the compatible limit point. -/
private theorem compatible_limit_of_injective {n m : ℕ}
    (L : Matrix (Fin m) (Fin n) ℝ) (s : ℕ → Fin n → ℝ) (q : Fin m → ℝ)
    (hL : Function.Injective L.mulVec)
    (hlim : Tendsto (fun k ↦ L.mulVec (s k)) atTop (nhds q)) :
    ∃ x, L.mulVec x = q ∧ Tendsto s atTop (nhds x) := by
  have hker : LinearMap.ker L.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    simpa only [Matrix.coe_mulVecLin] using hL
  have hclosed := LinearMap.isClosedEmbedding_of_injective hker
  have hq : q ∈ Set.range L.mulVecLin := by
    apply hclosed.isClosed_range.mem_of_tendsto hlim
    exact Eventually.of_forall fun k ↦ ⟨s k, rfl⟩
  obtain ⟨x, hx⟩ := hq
  refine ⟨x, hx, hclosed.tendsto_nhds_iff.mpr ?_⟩
  simpa [Function.comp_def, hx] using hlim

/-- All original-space conclusions follow from explicit reduced KKT limits.
This transport has no numerical upper bound on the multiplier factor. -/
theorem trajectoryConclusions_of_reduced_limits {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ)
    {qBar vBar uBar : Fin m → ℝ}
    (hred : (P.reduced β).IsKKT qBar vBar uBar)
    (hq : Tendsto (fun k ↦ P.A.mulVec (z.x k)) atTop (nhds qBar))
    (hv : Tendsto (fun k ↦ P.B.mulVec (z.y k) - P.b) atTop (nhds vBar))
    (hu : Tendsto (fun k ↦ β⁻¹ • z.multiplier k) atTop (nhds uBar)) :
    TrajectoryConclusions z := by
  have hgraph := reducedTrajectorySubgradientLaws P hf hg hKKT hβ hγ z
  obtain ⟨hF, hG⟩ := reduced_objectives_tendsto
    (q := fun k ↦ P.A.mulVec (z.x k))
    (v := fun k ↦ P.B.mulVec (z.y k) - P.b)
    (u := fun k ↦ β⁻¹ • z.multiplier k)
    (qBar := qBar) (vBar := vBar) (uBar := uBar)
    (P.reducedFirst_isClosedProperConvex hf hg hKKT hβ hγ z)
    (P.reducedSecond_isClosedProperConvex hf hg hKKT hβ hγ z)
    (fun k ↦ (hgraph k).1) (fun k ↦ (hgraph k).2) hq hv hu
  obtain ⟨hr, hd, hobj, hopt, hcompatible⟩ :=
    reducedOrbitConclusions_from_limits P hf hg hKKT hβ hγ z
      (q := qBar) (v := vBar) (u := uBar) hq hv hu hred hF hG
  have hres : Tendsto z.primalResidual atTop (nhds 0) := by
    apply hr.congr
    intro k
    rw [Trajectory.primalResidual_apply, add_sub_assoc]
  have hinc : Tendsto z.secondIncrement atTop (nhds 0) := by
    apply hd.congr
    intro k
    simp only [Trajectory.secondIncrement, Matrix.mulVec_sub, sub_sub_sub_cancel_right]
  have hobjective : Tendsto (fun k ↦ P.objective (z.x k) (z.y k)) atTop
      (nhds P.optimalValue) := by
    have hscaled := EReal.Tendsto.const_mul hobj
      (Or.inl (EReal.coe_ne_bot β)) (Or.inl (EReal.coe_ne_top β))
    simpa only [EReal.mul_div_cancel (EReal.coe_ne_bot β) (EReal.coe_ne_top β)
      (EReal.coe_ne_zero.mpr hβ.ne')] using hscaled
  have hmult : Tendsto z.multiplier atTop (nhds (β • uBar)) := by
    simpa only [smul_smul, mul_inv_cancel₀ hβ.ne', one_smul] using hu.const_smul β
  have hright : Tendsto (fun k ↦ P.B.mulVec (z.y k)) atTop (nhds (vBar + P.b)) := by
    simpa only [sub_add_cancel] using hv.add_const P.b
  refine ⟨⟨qBar, hq⟩, ⟨vBar + P.b, hright⟩,
    ⟨hres, hinc, hobjective, β • uBar, hopt, hmult⟩, ?_⟩
  intro hA hB
  obtain ⟨xBar, hx, hxs⟩ := compatible_limit_of_injective P.A z.x qBar hA hq
  obtain ⟨yBar, hy, hys⟩ := compatible_limit_of_injective P.B z.y
    (vBar + P.b) hB hright
  refine ⟨xBar, yBar, β • uBar, hcompatible hA hB xBar yBar hx ?_,
    hxs.prodMk_nhds (hys.prodMk_nhds hmult)⟩
  rw [hy, add_sub_cancel_right]

/-- Conditional application of Lemma C.1 to the concrete balanced lag weights.
This reusable interface takes the analytic implication and coercivity certificate
as explicit parameters; `UpdatedResults` supplies their concrete proofs. -/
theorem trajectoryConclusions_of_circle_claim
    (hC1 : UnitCircleConvergenceClaim) {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγone : 1 < γ) (hγtwo : γ < 2)
    (hCircle : HasCoercivityBound paperWeights γ (RefinedEndpoint.Data.kappa : ℝ))
    (z : Trajectory P β γ) : TrajectoryConclusions z := by
  have hγ : 0 < γ := lt_trans (by norm_num) hγone
  let rz := ReducedTrajectory.ofOriginal P hf hg hKKT hβ hγ z
  have hReducedKKT : ∃ q v u, ReducedIsKKT (P.reduced β).f (P.reduced β).g q v u := by
    obtain ⟨qStar, vStar, uStar, hstar⟩ := P.reduced_exists_kkt hf hg hKKT hβ hγ z
    refine ⟨qStar, vStar, uStar, ?_, ?_, ?_⟩
    · simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
        Matrix.one_mulVec] using hstar.feasible
    · simpa [Problem.reduced_A, Matrix.one_mulVec] using hstar.firstStationary
    · simpa [Problem.reduced_B, Matrix.one_mulVec] using hstar.secondStationary
  have hc := hC1 RefinedEndpoint.Data.historyLength paperWeights
    (by norm_num [RefinedEndpoint.Data.historyLength]) hγone hγtwo
    paperWeights_balancedMoments
    ⟨(RefinedEndpoint.Data.kappa : ℝ),
      Rat.cast_pos.mpr RefinedEndpoint.Data.kappa_pos, hCircle⟩
    (P.reduced β).f (P.reduced β).g
    (P.reducedFirst_isClosedProperConvex hf hg hKKT hβ hγ z)
    (P.reducedSecond_isClosedProperConvex hf hg hKKT hβ hγ z) hReducedKKT rz
  obtain ⟨qBar, vBar, uBar, hkkt, hstate, _, _, _⟩ := hc
  have hred : (P.reduced β).IsKKT qBar vBar uBar := by
    refine Problem.IsKKT.ofConditions ?_ ?_ ?_
    · simpa [Problem.reduced_A, Matrix.one_mulVec] using hkkt.2.1
    · simpa [Problem.reduced_B, Matrix.one_mulVec] using hkkt.2.2
    · simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
        Matrix.one_mulVec] using hkkt.1
  exact trajectoryConclusions_of_reduced_limits P hf hg hKKT hβ hγ z hred
    hstate.fst_nhds hstate.snd_nhds.fst_nhds hstate.snd_nhds.snd_nhds

/-- Assemble updated Theorem 2.1 from the analytic unit-circle implication
and the concrete lower certificate, including continuation. -/
theorem mainConvergence_of_circle_claims
    (hC1 : UnitCircleConvergenceClaim) (hC2 : LowerCircleCertificateClaim) :
    MainConvergenceClaim := by
  obtain ⟨δ, hδ, htwo, hbound⟩ := hC2
  intro n₁ n₂ m P hf hg hKKT β γ hβ hγ hγL z
  by_cases hOld : γ ≤ (377 : ℝ) / 200
  · exact retained_trajectory_conclusions P hf hg hKKT hβ hγ hOld z
  · apply trajectoryConclusions_of_circle_claim hC1 P hf hg hKKT hβ
      (by linarith [lt_of_not_ge hOld]) (by linarith) ?_ z
    exact hbound γ (le_of_not_ge hOld) (by linarith)

/-- Conditional strict lower endpoint bound: the positive extension in C.2
provides a valid convergence prefix strictly larger than the displayed `L`. -/
theorem refinedLowerBound_of_circle_claims
    (hC1 : UnitCircleConvergenceClaim) (hC2 : LowerCircleCertificateClaim) :
    RefinedLowerBoundClaim := by
  obtain ⟨δ, hδ, htwo, hbound⟩ := hC2
  have hprefix : RefinedEndpoint.lower + δ ≤ uniformConvergenceEndpoint := by
    rw [uniformConvergenceEndpoint_def]
    apply le_csSup EndpointBounds.prefix_bounded_and_endpoint_lt.1
    refine ⟨by linarith [RefinedEndpoint.lower_pos], ?_⟩
    intro γ hγ hγUpper n₁ n₂ m P hf hg hKKT β hβ z
    have hc : TrajectoryConclusions z := by
      by_cases hOld : γ ≤ (377 : ℝ) / 200
      · exact retained_trajectory_conclusions P hf hg hKKT hβ hγ hOld z
      · apply trajectoryConclusions_of_circle_claim hC1 P hf hg hKKT hβ
          (by linarith [lt_of_not_ge hOld]) (by linarith) ?_ z
        exact hbound γ (le_of_not_ge hOld) hγUpper.le
    exact ⟨hc.2.2.1, hc.2.2.2⟩
  exact (lt_add_of_pos_right RefinedEndpoint.lower hδ).trans_le hprefix

/-- Assemble Corollary 2.3 from the unit-circle criterion, the lower certificate,
and the independent refined upper bound. -/
theorem endpointBounds_of_three_claims
    (hC1 : UnitCircleConvergenceClaim) (hC2 : LowerCircleCertificateClaim)
    (hUpper : RefinedUpperBoundClaim) : EndpointBoundsClaim :=
  endpointBounds_of_two_bounds (refinedLowerBound_of_circle_claims hC1 hC2) hUpper

/-- Updated strict upper bound, discharged by the kernel-checked 1024-phase certificate. -/
theorem refinedUpperBound : RefinedUpperBoundClaim :=
  ConsensusADMM.RefinedEndpoint.Certificate.endpoint_lt_upper

/-- Assemble Corollary 2.3 from the unit-circle criterion and lower certificate,
using the proved refined upper bound. -/
theorem endpointBounds_of_circle_claims
    (hC1 : UnitCircleConvergenceClaim) (hC2 : LowerCircleCertificateClaim) :
    EndpointBoundsClaim :=
  endpointBounds_of_three_claims hC1 hC2 refinedUpperBound

/-- Assemble updated Theorem 2.1 from a lower certificate, using the proved
unit-circle convergence criterion. -/
theorem mainConvergence_of_lower_certificate (hC2 : LowerCircleCertificateClaim) :
    MainConvergenceClaim :=
  mainConvergence_of_circle_claims unitCircleConvergence hC2

/-- The complete analytic implication is discharged in the strict lower bound. -/
theorem refinedLowerBound_of_lower_certificate (hC2 : LowerCircleCertificateClaim) :
    RefinedLowerBoundClaim :=
  refinedLowerBound_of_circle_claims unitCircleConvergence hC2

/-- Assemble the full endpoint enclosure from a lower certificate, using the
proved unit-circle criterion and refined upper bound. `UpdatedResults` supplies
`lowerCircleCertificate` to obtain the unconditional theorem. -/
theorem endpointBounds_of_lower_certificate (hC2 : LowerCircleCertificateClaim) :
    EndpointBoundsClaim :=
  endpointBounds_of_circle_claims unitCircleConvergence hC2

end ADMM.UpdatedTargets
