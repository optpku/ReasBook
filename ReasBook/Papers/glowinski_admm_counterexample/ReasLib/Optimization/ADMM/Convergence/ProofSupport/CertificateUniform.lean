/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.SingleCertificateOrbit

@[expose] public section

set_option maxHeartbeats 500000

open Filter ADMM.FiniteMemory

namespace ADMM.ConvergenceProof

/-- An injective matrix map reflects convergence of a sequence from convergence
of its image, and the image limit lies in the matrix range. -/
private theorem tendstoOfMulVecTendstoOfInjective {n m : ℕ}
    (L : Matrix (Fin m) (Fin n) ℝ) (s : ℕ → Fin n → ℝ) (q : Fin m → ℝ)
    (hL : Function.Injective L.mulVec)
    (hlim : Filter.Tendsto (fun k ↦ L.mulVec (s k)) Filter.atTop (nhds q)) :
    ∃ x, L.mulVec x = q ∧ Filter.Tendsto s Filter.atTop (nhds x) := by
  -- Regard matrix multiplication as a finite-dimensional linear closed embedding.
  have hker : LinearMap.ker L.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    simpa only [Matrix.coe_mulVecLin] using hL
  have hclosed : Topology.IsClosedEmbedding L.mulVecLin :=
    LinearMap.isClosedEmbedding_of_injective hker
  -- Closedness of the range supplies a preimage of the proposed image limit.
  have hq : q ∈ Set.range L.mulVecLin := by
    refine hclosed.isClosed_range.mem_of_tendsto hlim ?_
    exact Filter.Eventually.of_forall fun k ↦ ⟨s k, rfl⟩
  obtain ⟨x, hx⟩ := hq
  refine ⟨x, hx, ?_⟩
  -- The inducing part of the closed embedding reflects convergence to that preimage.
  apply (hclosed.tendsto_nhds_iff).2
  simpa [Function.comp_def, hx] using hlim

/-- A finite-memory certificate implies the full uniform convergence property
at its parameter, including the original objective and multiplier conclusions. -/
theorem uniformConvergenceAt_of_certificate {ℓ : ℕ} {γ : ℝ}
    (c : Certificate ℓ γ) : UniformConvergenceAt γ := by
  intro n₁ n₂ m P hf hg hKKT β hβ z
  have hγ := c.gamma_pos
  obtain ⟨qBar, vBar, uBar, hred, hq, hv, hu⟩ :=
    trajectory_certificate_limits P hf hg hKKT hβ c z
  have hgraph := ADMM.reducedTrajectorySubgradientLaws P hf hg hKKT hβ hγ z
  obtain ⟨hF, hG⟩ := reduced_objectives_tendsto
    (q := fun k ↦ P.A.mulVec (z.x k))
    (v := fun k ↦ P.B.mulVec (z.y k) - P.b)
    (u := fun k ↦ β⁻¹ • z.multiplier k)
    (qBar := qBar) (vBar := vBar) (uBar := uBar)
    (P.reducedFirst_isClosedProperConvex hf hg hKKT hβ hγ z)
    (P.reducedSecond_isClosedProperConvex hf hg hKKT hβ hγ z)
    (fun k ↦ (hgraph k).1) (fun k ↦ (hgraph k).2) hq hv hu
  obtain ⟨hr, hd, hobj, hopt, hcompatible⟩ :=
    reducedOrbitConclusions_from_limits P hf hg hKKT hβ hγ z hq hv hu hred hF hG
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
  refine ⟨⟨hres, hinc, hobjective, β • uBar, hopt, hmult⟩, ?_⟩
  intro hA hB
  have hright : Tendsto (fun k ↦ P.B.mulVec (z.y k)) atTop (nhds (vBar + P.b)) := by
    simpa only [sub_add_cancel] using hv.add_const P.b
  obtain ⟨xBar, hx, hxs⟩ := tendstoOfMulVecTendstoOfInjective P.A z.x qBar hA hq
  obtain ⟨yBar, hy, hys⟩ := tendstoOfMulVecTendstoOfInjective P.B z.y
    (vBar + P.b) hB hright
  refine ⟨xBar, yBar, β • uBar, hcompatible hA hB xBar yBar hx ?_,
    hxs.prodMk_nhds (hys.prodMk_nhds hmult)⟩
  rw [hy, add_sub_cancel_right]

end ADMM.ConvergenceProof
