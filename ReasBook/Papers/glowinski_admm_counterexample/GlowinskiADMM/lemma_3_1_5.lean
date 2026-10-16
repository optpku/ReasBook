module

public import glowinski_admm_counterexample.GlowinskiADMM.lemma_3_1_2
public import glowinski_admm_counterexample.GlowinskiADMM.definition_3_1_4_Certificate
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.SingleCertificateOrbit

@[expose] public section

namespace ADMM.FiniteMemory

/-- Lemma 3.1.5 (1): common finite-memory certificates at two ordered
relaxation endpoints force every intervening reduced image trajectory to
converge to a reduced KKT triple. -/
theorem intervalImage_tendsto_kkt {ℓ n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    {β γMinus γPlus γ : ℝ} (cMinus : Certificate ℓ γMinus)
    (cPlus : Certificate ℓ γPlus) (hEndpoints : γMinus < γPlus)
    (hγMinus : γMinus ≤ γ) (hγPlus : γ ≤ γPlus)
    (hLagMinus : cMinus.lagMinus = cPlus.lagMinus)
    (hLagPlus : cMinus.lagPlus = cPlus.lagPlus)
    (hOmega : cMinus.omega = cPlus.omega)
    (hEpsilon : cMinus.epsilon = cPlus.epsilon)
    (hZeta : cMinus.zeta = cPlus.zeta) (hMu : cMinus.μ = cPlus.μ)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) (hβ : 0 < β)
    (z : Trajectory P β γ) :
    ∃ qBar vBar uBar, (P.reduced β).IsKKT qBar vBar uBar ∧
      Filter.Tendsto
        (fun k ↦ (P.A.mulVec (z.x k), P.B.mulVec (z.y k) - P.b,
          β⁻¹ • z.multiplier k)) Filter.atTop (nhds (qBar, vBar, uBar)) := by
  let c := Certificate.interpolate cMinus cPlus hEndpoints hγMinus hγPlus
    hLagMinus hLagPlus hOmega hEpsilon hZeta hMu
  obtain ⟨qBar, vBar, uBar, hkkt, hq, hv, hu⟩ :=
    ADMM.ConvergenceProof.trajectory_certificate_limits P hf hg hKKT hβ c z
  exact ⟨qBar, vBar, uBar, hkkt, hq.prodMk_nhds (hv.prodMk_nhds hu)⟩

/-- Lemma 3.1.5 (2): under common endpoint certificates, the squared primal
residual norms of every intervening exact trajectory are summable. -/
theorem intervalResidual_sq_summable {ℓ n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    {β γMinus γPlus γ : ℝ} (cMinus : Certificate ℓ γMinus)
    (cPlus : Certificate ℓ γPlus) (hEndpoints : γMinus < γPlus)
    (hγMinus : γMinus ≤ γ) (hγPlus : γ ≤ γPlus)
    (hLagMinus : cMinus.lagMinus = cPlus.lagMinus)
    (hLagPlus : cMinus.lagPlus = cPlus.lagPlus)
    (hOmega : cMinus.omega = cPlus.omega)
    (hEpsilon : cMinus.epsilon = cPlus.epsilon)
    (hZeta : cMinus.zeta = cPlus.zeta) (hMu : cMinus.μ = cPlus.μ)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) (hβ : 0 < β)
    (z : Trajectory P β γ) :
    Summable (fun k ↦ ‖z.primalResidual k‖ ^ 2) := by
  let c := Certificate.interpolate cMinus cPlus hEndpoints hγMinus hγPlus
    hLagMinus hLagPlus hOmega hEpsilon hZeta hMu
  exact (ADMM.ConvergenceProof.trajectory_certificate_square_summable
    P hf hg hKKT hβ c z).1

/-- Lemma 3.1.5 (3): under common endpoint certificates, the squared
second-image increment norms of every intervening exact trajectory are summable. -/
theorem intervalSecondIncrement_sq_summable {ℓ n₁ n₂ m : ℕ}
    (P : Problem n₁ n₂ m) {β γMinus γPlus γ : ℝ}
    (cMinus : Certificate ℓ γMinus) (cPlus : Certificate ℓ γPlus)
    (hEndpoints : γMinus < γPlus) (hγMinus : γMinus ≤ γ)
    (hγPlus : γ ≤ γPlus)
    (hLagMinus : cMinus.lagMinus = cPlus.lagMinus)
    (hLagPlus : cMinus.lagPlus = cPlus.lagPlus)
    (hOmega : cMinus.omega = cPlus.omega)
    (hEpsilon : cMinus.epsilon = cPlus.epsilon)
    (hZeta : cMinus.zeta = cPlus.zeta) (hMu : cMinus.μ = cPlus.μ)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) (hβ : 0 < β)
    (z : Trajectory P β γ) :
    Summable (fun k ↦ ‖z.secondIncrement k‖ ^ 2) := by
  let c := Certificate.interpolate cMinus cPlus hEndpoints hγMinus hγPlus
    hLagMinus hLagPlus hOmega hEpsilon hZeta hMu
  exact (ADMM.ConvergenceProof.trajectory_certificate_square_summable
    P hf hg hKKT hβ c z).2

/-- Lemma 3.1.5 (4): along the reduced-state limit supplied by the interval
certificate, the first reduced objective tilted at its KKT support tends to zero. -/
theorem intervalFirstTilt_tendsto_zero {ℓ n₁ n₂ m : ℕ}
    (P : Problem n₁ n₂ m) {β γMinus γPlus γ : ℝ}
    (cMinus : Certificate ℓ γMinus) (cPlus : Certificate ℓ γPlus)
    (hEndpoints : γMinus < γPlus) (hγMinus : γMinus ≤ γ)
    (hγPlus : γ ≤ γPlus)
    (hLagMinus : cMinus.lagMinus = cPlus.lagMinus)
    (hLagPlus : cMinus.lagPlus = cPlus.lagPlus)
    (hOmega : cMinus.omega = cPlus.omega)
    (hEpsilon : cMinus.epsilon = cPlus.epsilon)
    (hZeta : cMinus.zeta = cPlus.zeta) (hMu : cMinus.μ = cPlus.μ)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) (hβ : 0 < β)
    (z : Trajectory P β γ) (qBar vBar uBar : Fin m → ℝ)
    (hReducedKKT : (P.reduced β).IsKKT qBar vBar uBar)
    (hState : Filter.Tendsto
      (fun k ↦ (P.A.mulVec (z.x k), P.B.mulVec (z.y k) - P.b,
        β⁻¹ • z.multiplier k)) Filter.atTop (nhds (qBar, vBar, uBar))) :
    Filter.Tendsto
      (fun k ↦ (P.reduced β).f (P.A.mulVec (z.x k)) -
        (P.reduced β).f qBar +
          ((dotProduct uBar (P.A.mulVec (z.x k) - qBar) : ℝ) : EReal))
      Filter.atTop (nhds 0) := by
  exact (ADMM.ConvergenceProof.trajectory_tilted_values P hf hg hKKT hβ
    (cMinus.gamma_pos.trans_le hγMinus) z hReducedKKT
    hState.fst_nhds hState.snd_nhds.fst_nhds hState.snd_nhds.snd_nhds).1

/-- Lemma 3.1.5 (5): along the reduced-state limit supplied by the interval
certificate, the second reduced objective tilted at its KKT support tends to zero. -/
theorem intervalSecondTilt_tendsto_zero {ℓ n₁ n₂ m : ℕ}
    (P : Problem n₁ n₂ m) {β γMinus γPlus γ : ℝ}
    (cMinus : Certificate ℓ γMinus) (cPlus : Certificate ℓ γPlus)
    (hEndpoints : γMinus < γPlus) (hγMinus : γMinus ≤ γ)
    (hγPlus : γ ≤ γPlus)
    (hLagMinus : cMinus.lagMinus = cPlus.lagMinus)
    (hLagPlus : cMinus.lagPlus = cPlus.lagPlus)
    (hOmega : cMinus.omega = cPlus.omega)
    (hEpsilon : cMinus.epsilon = cPlus.epsilon)
    (hZeta : cMinus.zeta = cPlus.zeta) (hMu : cMinus.μ = cPlus.μ)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) (hβ : 0 < β)
    (z : Trajectory P β γ) (qBar vBar uBar : Fin m → ℝ)
    (hReducedKKT : (P.reduced β).IsKKT qBar vBar uBar)
    (hState : Filter.Tendsto
      (fun k ↦ (P.A.mulVec (z.x k), P.B.mulVec (z.y k) - P.b,
        β⁻¹ • z.multiplier k)) Filter.atTop (nhds (qBar, vBar, uBar))) :
    Filter.Tendsto
      (fun k ↦ (P.reduced β).g (P.B.mulVec (z.y k) - P.b) -
        (P.reduced β).g vBar +
          ((dotProduct uBar ((P.B.mulVec (z.y k) - P.b) - vBar) : ℝ) : EReal))
      Filter.atTop (nhds 0) := by
  exact (ADMM.ConvergenceProof.trajectory_tilted_values P hf hg hKKT hβ
    (cMinus.gamma_pos.trans_le hγMinus) z hReducedKKT
    hState.fst_nhds hState.snd_nhds.fst_nhds hState.snd_nhds.snd_nhds).2

end ADMM.FiniteMemory
