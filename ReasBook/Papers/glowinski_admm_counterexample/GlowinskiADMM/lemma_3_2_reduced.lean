/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.SingleCertificateOrbit

@[expose] public section

open Filter

namespace ADMM.FiniteMemory

/-- A reduced ADMM trajectory, stated directly through its two proximal
optimality conditions and multiplier update. The initial three vectors are
arbitrary; only generated points have to belong to the objective domains. -/
structure ReducedTrajectory {m : ℕ} (f g : (Fin m → ℝ) → EReal) (γ : ℝ) where
  /-- The first constraint-image sequence. -/
  q : ℕ → Fin m → ℝ
  /-- The second constraint-image sequence. -/
  v : ℕ → Fin m → ℝ
  /-- The scaled multiplier sequence. -/
  u : ℕ → Fin m → ℝ
  /-- Optimality of the first proximal update. -/
  first : ∀ k, IsSubgradientAt f (-v k - u k - q (k + 1)) (q (k + 1))
  /-- Optimality of the second proximal update. -/
  second : ∀ k, IsSubgradientAt g (-q (k + 1) - u k - v (k + 1)) (v (k + 1))
  /-- The relaxed multiplier recurrence. -/
  recurrence : ∀ k, u (k + 1) = u k + γ • (q (k + 1) + v (k + 1))

/-- KKT conditions for the reduced constraint `q + v = 0`. -/
def ReducedIsKKT {m : ℕ} (f g : (Fin m → ℝ) → EReal)
    (q v u : Fin m → ℝ) : Prop :=
  q + v = 0 ∧ IsSubgradientAt f (-u) q ∧ IsSubgradientAt g (-u) v

namespace ReducedTrajectory

open ADMM.ConvergenceProof

/-- An original exact trajectory supplies a reduced trajectory with precisely
the image and multiplier scaling used in the revised paper. -/
noncomputable def ofOriginal {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ) :
    ReducedTrajectory (P.reduced β).f (P.reduced β).g γ where
  q := fun k ↦ P.A.mulVec (z.x k)
  v := fun k ↦ P.B.mulVec (z.y k) - P.b
  u := fun k ↦ β⁻¹ • z.multiplier k
  first := fun k ↦ (ADMM.reducedTrajectorySubgradientLaws P hf hg hKKT hβ hγ z k).1
  second := fun k ↦ (ADMM.reducedTrajectorySubgradientLaws P hf hg hKKT hβ hγ z k).2
  recurrence := Trajectory.scaledMultiplier_imageUpdate P hf hg hKKT hβ hγ z

/-- A single certificate gives a KKT limit directly for any reduced trajectory,
without requiring it to have been extracted from an original problem. -/
theorem certificate_tendsto_kkt {ℓ m : ℕ} {γ : ℝ}
    {f g : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    (hKKT : ∃ q v u, ReducedIsKKT f g q v u)
    (c : Certificate ℓ γ) (z : ReducedTrajectory f g γ) :
    ∃ qBar vBar uBar, ReducedIsKKT f g qBar vBar uBar ∧
      Tendsto (fun k ↦ (z.q k, z.v k, z.u k)) atTop
        (nhds (qBar, vBar, uBar)) := by
  obtain ⟨qStar, vStar, uStar, hfeas, hfStar, hgStar⟩ := hKKT
  obtain ⟨qBar, vBar, uBar, hq, hv, hu⟩ := reduced_orbit_converges c.gamma_pos hf hg
    z.q z.v z.u qStar vStar uStar hfeas hfStar hgStar
    z.recurrence z.first z.second (Or.inr ⟨ℓ, ⟨c⟩⟩)
  exact ⟨qBar, vBar, uBar,
    reduced_limit_stationary hf hg c.gamma_pos.ne'
      z.recurrence z.first z.second hq hv hu,
    hq.prodMk_nhds (hv.prodMk_nhds hu)⟩

/-- A certificate makes the reduced residual and second-image increment
square summable, including arbitrary initial values of the two images. -/
theorem certificate_square_summable {ℓ m : ℕ} {γ : ℝ}
    {f g : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    (hKKT : ∃ q v u, ReducedIsKKT f g q v u)
    (c : Certificate ℓ γ) (z : ReducedTrajectory f g γ) :
    Summable (fun k ↦ ‖z.q k + z.v k‖ ^ 2) ∧
      Summable (fun k ↦ ‖z.v (k + 1) - z.v k‖ ^ 2) := by
  obtain ⟨qStar, vStar, uStar, hfeas, hfStar, hgStar⟩ := hKKT
  let eta := fun k ↦ -(z.v k - vStar)
  let w := fun k ↦ γ⁻¹ • (z.u k - uStar)
  let phi := reducedNormalizedObjectives f g qStar vStar uStar
  have hn := reduced_normalized_graph c.gamma_pos.ne' hf hg z.q z.v z.u
    qStar vStar uStar hfeas z.recurrence z.first z.second
  have hz := (reduced_normalized_data hf hg hfStar hgStar).2
  have hr := finiteMemory_residual_summable c phi eta w hz hn
  have hi := reduced_increment_summable c.gamma_pos eta w
    (generated_pairing_nonneg phi eta w hz hn) hr
  have hrnorm : Summable (fun k ↦ ‖w (k + 1) - w k‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
      (fun _ ↦ norm_sq_le_coordinateSquare _) hr
  have hinorm : Summable (fun k ↦ ‖eta (k + 1) - eta k‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
      (fun _ ↦ norm_sq_le_coordinateSquare _) hi
  constructor
  · apply (summable_nat_add_iff 1).1
    apply hrnorm.congr
    intro k
    rw [show w (k + 1) - w k = z.q (k + 1) + z.v (k + 1) from
      scaled_multiplier_difference c.gamma_pos.ne' z.q z.v z.u uStar z.recurrence k]
  · apply hinorm.congr
    intro k
    have heq : eta (k + 1) - eta k = -(z.v (k + 1) - z.v k) := by
      dsimp only [eta]
      module
    rw [heq, norm_neg]

/-- For any reduced KKT limit, the two individual tilted objective values
tend to zero. The assertion includes extended-real objectives at domain
boundaries and does not assume objective continuity. -/
theorem tilted_values_tendsto_zero {m : ℕ} {γ : ℝ}
    {f g : (Fin m → ℝ) → EReal}
    (z : ReducedTrajectory f g γ)
    {qBar vBar uBar : Fin m → ℝ}
    (hKKT : ReducedIsKKT f g qBar vBar uBar)
    (hState : Tendsto (fun k ↦ (z.q k, z.v k, z.u k)) atTop
      (nhds (qBar, vBar, uBar))) :
    Tendsto (fun k ↦ f (z.q k) - f qBar +
      ((dotProduct uBar (z.q k - qBar) : ℝ) : EReal)) atTop (nhds 0) ∧
    Tendsto (fun k ↦ g (z.v k) - g vBar +
      ((dotProduct uBar (z.v k - vBar) : ℝ) : EReal)) atTop (nhds 0) := by
  obtain ⟨hfeas, hfBar, hgBar⟩ := hKKT
  have hq := hState.fst_nhds
  have hv := hState.snd_nhds.fst_nhds
  have hu := hState.snd_nhds.snd_nhds
  have hqs := hq.comp (tendsto_add_atTop_nat 1)
  have hvs := hv.comp (tendsto_add_atTop_nat 1)
  have hnormalF : -vBar - uBar - qBar = -uBar := by
    rw [eq_neg_of_add_eq_zero_right hfeas]
    module
  have hnormalG : -qBar - uBar - vBar = -uBar := by
    rw [eq_neg_of_add_eq_zero_right hfeas]
    module
  have hF := ereal_tilt_tendsto_zero hfBar z.first hqs
    (by simpa only [hnormalF, Function.comp_apply] using (hv.neg.sub hu).sub hqs)
  have hG := ereal_tilt_tendsto_zero hgBar z.second hvs
    (by simpa only [hnormalG, Function.comp_apply] using (hqs.neg.sub hu).sub hvs)
  constructor
  · apply (tendsto_add_atTop_iff_nat 1).1
    simpa only [neg_dotProduct, EReal.coe_neg, sub_eq_add_neg, neg_neg] using hF
  · apply (tendsto_add_atTop_iff_nat 1).1
    simpa only [neg_dotProduct, EReal.coe_neg, sub_eq_add_neg, neg_neg] using hG

/-- A reduced KKT state limit forces the constraint residual to vanish. -/
theorem residual_tendsto_zero {m : ℕ} {γ : ℝ}
    {f g : (Fin m → ℝ) → EReal} (z : ReducedTrajectory f g γ)
    {qBar vBar uBar : Fin m → ℝ}
    (hKKT : ReducedIsKKT f g qBar vBar uBar)
    (hState : Tendsto (fun k ↦ (z.q k, z.v k, z.u k)) atTop
      (nhds (qBar, vBar, uBar))) :
    Tendsto (fun k ↦ z.q k + z.v k) atTop (nhds 0) := by
  simpa only [hKKT.1] using hState.fst_nhds.add hState.snd_nhds.fst_nhds

/-- Updated Lemma 3.2 (1): common endpoint certificates give a KKT limit for
every reduced trajectory at every intervening fixed multiplier factor. -/
theorem interval_tendsto_kkt {ℓ m : ℕ} {γMinus γPlus γ : ℝ}
    (cMinus : Certificate ℓ γMinus) (cPlus : Certificate ℓ γPlus)
    (hEndpoints : γMinus < γPlus) (hγMinus : γMinus ≤ γ) (hγPlus : γ ≤ γPlus)
    (hLagMinus : cMinus.lagMinus = cPlus.lagMinus)
    (hLagPlus : cMinus.lagPlus = cPlus.lagPlus)
    (hOmega : cMinus.omega = cPlus.omega)
    (hEpsilon : cMinus.epsilon = cPlus.epsilon)
    (hZeta : cMinus.zeta = cPlus.zeta) (hMu : cMinus.μ = cPlus.μ)
    {f g : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    (hKKT : ∃ q v u, ReducedIsKKT f g q v u)
    (z : ReducedTrajectory f g γ) :
    ∃ qBar vBar uBar, ReducedIsKKT f g qBar vBar uBar ∧
      Tendsto (fun k ↦ (z.q k, z.v k, z.u k)) atTop
        (nhds (qBar, vBar, uBar)) := by
  exact certificate_tendsto_kkt hf hg hKKT
    (Certificate.interpolate cMinus cPlus hEndpoints hγMinus hγPlus
      hLagMinus hLagPlus hOmega hEpsilon hZeta hMu) z

/-- Updated Lemma 3.2 (2): the residuals of every intervening reduced
trajectory are square summable. -/
theorem intervalResidual_sq_summable {ℓ m : ℕ} {γMinus γPlus γ : ℝ}
    (cMinus : Certificate ℓ γMinus) (cPlus : Certificate ℓ γPlus)
    (hEndpoints : γMinus < γPlus) (hγMinus : γMinus ≤ γ) (hγPlus : γ ≤ γPlus)
    (hLagMinus : cMinus.lagMinus = cPlus.lagMinus)
    (hLagPlus : cMinus.lagPlus = cPlus.lagPlus)
    (hOmega : cMinus.omega = cPlus.omega)
    (hEpsilon : cMinus.epsilon = cPlus.epsilon)
    (hZeta : cMinus.zeta = cPlus.zeta) (hMu : cMinus.μ = cPlus.μ)
    {f g : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    (hKKT : ∃ q v u, ReducedIsKKT f g q v u)
    (z : ReducedTrajectory f g γ) :
    Summable (fun k ↦ ‖z.q k + z.v k‖ ^ 2) := by
  exact (certificate_square_summable hf hg hKKT
    (Certificate.interpolate cMinus cPlus hEndpoints hγMinus hγPlus
      hLagMinus hLagPlus hOmega hEpsilon hZeta hMu) z).1

/-- Updated Lemma 3.2 (3): second-image increments of every intervening
reduced trajectory are square summable. -/
theorem intervalSecondIncrement_sq_summable {ℓ m : ℕ} {γMinus γPlus γ : ℝ}
    (cMinus : Certificate ℓ γMinus) (cPlus : Certificate ℓ γPlus)
    (hEndpoints : γMinus < γPlus) (hγMinus : γMinus ≤ γ) (hγPlus : γ ≤ γPlus)
    (hLagMinus : cMinus.lagMinus = cPlus.lagMinus)
    (hLagPlus : cMinus.lagPlus = cPlus.lagPlus)
    (hOmega : cMinus.omega = cPlus.omega)
    (hEpsilon : cMinus.epsilon = cPlus.epsilon)
    (hZeta : cMinus.zeta = cPlus.zeta) (hMu : cMinus.μ = cPlus.μ)
    {f g : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    (hKKT : ∃ q v u, ReducedIsKKT f g q v u)
    (z : ReducedTrajectory f g γ) :
    Summable (fun k ↦ ‖z.v (k + 1) - z.v k‖ ^ 2) := by
  exact (certificate_square_summable hf hg hKKT
    (Certificate.interpolate cMinus cPlus hEndpoints hγMinus hγPlus
      hLagMinus hLagPlus hOmega hEpsilon hZeta hMu) z).2

/-- Updated Lemma 3.2, with every conclusion assembled for an arbitrary
reduced trajectory: a KKT state limit, both square-summability assertions,
and vanishing individual tilted objective values. -/
theorem interval_conclusions {ℓ m : ℕ} {γMinus γPlus γ : ℝ}
    (cMinus : Certificate ℓ γMinus) (cPlus : Certificate ℓ γPlus)
    (hEndpoints : γMinus < γPlus) (hγMinus : γMinus ≤ γ) (hγPlus : γ ≤ γPlus)
    (hLagMinus : cMinus.lagMinus = cPlus.lagMinus)
    (hLagPlus : cMinus.lagPlus = cPlus.lagPlus)
    (hOmega : cMinus.omega = cPlus.omega)
    (hEpsilon : cMinus.epsilon = cPlus.epsilon)
    (hZeta : cMinus.zeta = cPlus.zeta) (hMu : cMinus.μ = cPlus.μ)
    {f g : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    (hKKT : ∃ q v u, ReducedIsKKT f g q v u)
    (z : ReducedTrajectory f g γ) :
    ∃ qBar vBar uBar, ReducedIsKKT f g qBar vBar uBar ∧
      Tendsto (fun k ↦ (z.q k, z.v k, z.u k)) atTop
        (nhds (qBar, vBar, uBar)) ∧
      Summable (fun k ↦ ‖z.q k + z.v k‖ ^ 2) ∧
      Summable (fun k ↦ ‖z.v (k + 1) - z.v k‖ ^ 2) ∧
      Tendsto (fun k ↦ f (z.q k) - f qBar +
        ((dotProduct uBar (z.q k - qBar) : ℝ) : EReal)) atTop (nhds 0) ∧
      Tendsto (fun k ↦ g (z.v k) - g vBar +
        ((dotProduct uBar (z.v k - vBar) : ℝ) : EReal)) atTop (nhds 0) := by
  let c := Certificate.interpolate cMinus cPlus hEndpoints hγMinus hγPlus
    hLagMinus hLagPlus hOmega hEpsilon hZeta hMu
  obtain ⟨qBar, vBar, uBar, hbar, hstate⟩ := certificate_tendsto_kkt hf hg hKKT c z
  have hs := certificate_square_summable hf hg hKKT c z
  have ht := tilted_values_tendsto_zero z hbar hstate
  exact ⟨qBar, vBar, uBar, hbar, hstate, hs.1, hs.2, ht.1, ht.2⟩

end ReducedTrajectory

end ADMM.FiniteMemory
