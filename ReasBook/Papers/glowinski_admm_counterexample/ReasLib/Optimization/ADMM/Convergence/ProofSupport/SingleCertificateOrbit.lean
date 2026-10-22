/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UniformConvergence
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.IntervalCertificate

@[expose] public section

set_option maxHeartbeats 500000

open Filter ADMM.FiniteMemory

namespace ADMM.ConvergenceProof

/-- Any single finite-memory certificate gives a reduced KKT limit for every
exact original trajectory, with no numerical restriction on its parameter. -/
theorem trajectory_certificate_limits {ℓ n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (c : Certificate ℓ γ) (z : Trajectory P β γ) :
    ∃ qBar vBar uBar, (P.reduced β).IsKKT qBar vBar uBar ∧
      Tendsto (fun k ↦ P.A.mulVec (z.x k)) atTop (nhds qBar) ∧
      Tendsto (fun k ↦ P.B.mulVec (z.y k) - P.b) atTop (nhds vBar) ∧
      Tendsto (fun k ↦ β⁻¹ • z.multiplier k) atTop (nhds uBar) := by
  have hγ := c.gamma_pos
  have hF := P.reducedFirst_isClosedProperConvex hf hg hKKT hβ hγ z
  have hG := P.reducedSecond_isClosedProperConvex hf hg hKKT hβ hγ z
  obtain ⟨qStar, vStar, uStar, hstar⟩ := P.reduced_exists_kkt hf hg hKKT hβ hγ z
  have hfeas : qStar + vStar = 0 := by
    simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
      Matrix.one_mulVec] using hstar.feasible
  have hfStar : IsSubgradientAt (P.reduced β).f (-uStar) qStar := by
    simpa [Problem.reduced_A, Matrix.one_mulVec] using hstar.firstStationary
  have hgStar : IsSubgradientAt (P.reduced β).g (-uStar) vStar := by
    simpa [Problem.reduced_B, Matrix.one_mulVec] using hstar.secondStationary
  have hgraph := ADMM.reducedTrajectorySubgradientLaws P hf hg hKKT hβ hγ z
  have hrec := Trajectory.scaledMultiplier_imageUpdate P hf hg hKKT hβ hγ z
  obtain ⟨qBar, vBar, uBar, hq, hv, hu⟩ := reduced_orbit_converges hγ hF hG
    (fun k ↦ P.A.mulVec (z.x k)) (fun k ↦ P.B.mulVec (z.y k) - P.b)
    (fun k ↦ β⁻¹ • z.multiplier k) qStar vStar uStar hfeas hfStar hgStar
    hrec (fun k ↦ (hgraph k).1) (fun k ↦ (hgraph k).2) (Or.inr ⟨ℓ, ⟨c⟩⟩)
  obtain ⟨hfeasible, hfbar, hgbar⟩ := reduced_limit_stationary hF hG
    (q := fun k ↦ P.A.mulVec (z.x k))
    (v := fun k ↦ P.B.mulVec (z.y k) - P.b)
    (u := fun k ↦ β⁻¹ • z.multiplier k)
    (qBar := qBar) (vBar := vBar) (uBar := uBar) (γ := γ) hγ.ne' hrec
    (fun k ↦ (hgraph k).1) (fun k ↦ (hgraph k).2) hq hv hu
  refine ⟨qBar, vBar, uBar, ?_, hq, hv, hu⟩
  refine Problem.IsKKT.ofConditions ?_ ?_ ?_
  · simpa [Problem.reduced_A, Matrix.one_mulVec] using hfbar
  · simpa [Problem.reduced_B, Matrix.one_mulVec] using hgbar
  · simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
      Matrix.one_mulVec] using hfeasible

/-- The same certificate gives square summability of the original residual
and second-image increment; finite prefixes do not affect either assertion. -/
theorem trajectory_certificate_square_summable {ℓ n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (c : Certificate ℓ γ) (z : Trajectory P β γ) :
    Summable (fun k ↦ ‖z.primalResidual k‖ ^ 2) ∧
      Summable (fun k ↦ ‖z.secondIncrement k‖ ^ 2) := by
  have hγ := c.gamma_pos
  have hF := P.reducedFirst_isClosedProperConvex hf hg hKKT hβ hγ z
  have hG := P.reducedSecond_isClosedProperConvex hf hg hKKT hβ hγ z
  obtain ⟨qStar, vStar, uStar, hstar⟩ := P.reduced_exists_kkt hf hg hKKT hβ hγ z
  have hfeas : qStar + vStar = 0 := by
    simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
      Matrix.one_mulVec] using hstar.feasible
  have hfStar : IsSubgradientAt (P.reduced β).f (-uStar) qStar := by
    simpa [Problem.reduced_A, Matrix.one_mulVec] using hstar.firstStationary
  have hgStar : IsSubgradientAt (P.reduced β).g (-uStar) vStar := by
    simpa [Problem.reduced_B, Matrix.one_mulVec] using hstar.secondStationary
  let q := fun k ↦ P.A.mulVec (z.x k)
  let v := fun k ↦ P.B.mulVec (z.y k) - P.b
  let u := fun k ↦ β⁻¹ • z.multiplier k
  let eta := fun k ↦ -(v k - vStar)
  let w := fun k ↦ γ⁻¹ • (u k - uStar)
  let phi := reducedNormalizedObjectives (P.reduced β).f (P.reduced β).g qStar vStar uStar
  have hgraph := ADMM.reducedTrajectorySubgradientLaws P hf hg hKKT hβ hγ z
  have hrec := Trajectory.scaledMultiplier_imageUpdate P hf hg hKKT hβ hγ z
  have hn := reduced_normalized_graph hγ.ne' hF hG q v u qStar vStar uStar hfeas
    hrec (fun k ↦ (hgraph k).1) (fun k ↦ (hgraph k).2)
  have hz := (reduced_normalized_data hF hG hfStar hgStar).2
  have hr := finiteMemory_residual_summable c phi eta w hz hn
  have hi := reduced_increment_summable hγ eta w (generated_pairing_nonneg phi eta w hz hn) hr
  have hrnorm : Summable (fun k ↦ ‖w (k + 1) - w k‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) (fun _ ↦ norm_sq_le_coordinateSquare _) hr
  have hinorm : Summable (fun k ↦ ‖eta (k + 1) - eta k‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) (fun _ ↦ norm_sq_le_coordinateSquare _) hi
  constructor
  · apply (summable_nat_add_iff 1).1
    apply hrnorm.congr
    intro k
    rw [show w (k + 1) - w k = q (k + 1) + v (k + 1) from
      scaled_multiplier_difference hγ.ne' q v u uStar hrec k]
    simp only [q, v, Trajectory.primalResidual_apply, add_sub_assoc]
  · apply (summable_nat_add_iff 1).1
    apply hinorm.congr
    intro k
    have heq : eta (k + 1) - eta k = -(z.secondIncrement (k + 1)) := by
      simp only [eta, v, Trajectory.secondIncrement, Nat.add_sub_cancel,
        Matrix.mulVec_sub]
      module
    rw [heq, norm_neg]

/-- The real support-plane squeeze also gives the extended-real tilt limit. -/
theorem ereal_tilt_tendsto_zero {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {xStar pStar : Fin m → ℝ} {x p : ℕ → Fin m → ℝ}
    (hStar : IsSubgradientAt f pStar xStar)
    (hgraph : ∀ k, IsSubgradientAt f (p k) (x k))
    (hx : Tendsto x atTop (nhds xStar)) (hp : Tendsto p atTop (nhds pStar)) :
    Tendsto (fun k ↦ f (x k) - f xStar -
      ((dotProduct pStar (x k - xStar) : ℝ) : EReal)) atTop (nhds 0) := by
  have h := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tiltedValue_tendsto_zero hStar hgraph hx hp)
  change Tendsto (fun k ↦ ((tiltedValue f xStar pStar (x k) : ℝ) : EReal))
    atTop (nhds 0) at h
  apply h.congr
  intro k
  rw [subgradient_value_real (hgraph k), subgradient_value_real hStar,
    ← EReal.coe_sub, ← EReal.coe_sub]
  rfl

/-- Along any convergent reduced trajectory, both objectives tilted at its
KKT limit tend to zero, including extended-real objectives at domain boundaries. -/
theorem trajectory_tilted_values {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ)
    {qBar vBar uBar : Fin m → ℝ} (hred : (P.reduced β).IsKKT qBar vBar uBar)
    (hq : Tendsto (fun k ↦ P.A.mulVec (z.x k)) atTop (nhds qBar))
    (hv : Tendsto (fun k ↦ P.B.mulVec (z.y k) - P.b) atTop (nhds vBar))
    (hu : Tendsto (fun k ↦ β⁻¹ • z.multiplier k) atTop (nhds uBar)) :
    Tendsto (fun k ↦ (P.reduced β).f (P.A.mulVec (z.x k)) -
      (P.reduced β).f qBar +
      ((dotProduct uBar (P.A.mulVec (z.x k) - qBar) : ℝ) : EReal)) atTop (nhds 0) ∧
    Tendsto (fun k ↦ (P.reduced β).g (P.B.mulVec (z.y k) - P.b) -
      (P.reduced β).g vBar +
      ((dotProduct uBar ((P.B.mulVec (z.y k) - P.b) - vBar) : ℝ) : EReal)) atTop (nhds 0) := by
  have hgraph := ADMM.reducedTrajectorySubgradientLaws P hf hg hKKT hβ hγ z
  have hfeas : qBar + vBar = 0 := by
    simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
      Matrix.one_mulVec] using hred.feasible
  have hfbar : IsSubgradientAt (P.reduced β).f (-uBar) qBar := by
    simpa [Problem.reduced_A, Matrix.one_mulVec] using hred.firstStationary
  have hgbar : IsSubgradientAt (P.reduced β).g (-uBar) vBar := by
    simpa [Problem.reduced_B, Matrix.one_mulVec] using hred.secondStationary
  have hqs := hq.comp (tendsto_add_atTop_nat 1)
  have hvs := hv.comp (tendsto_add_atTop_nat 1)
  have hnormalF : -vBar - uBar - qBar = -uBar := by
    have h := eq_neg_of_add_eq_zero_right hfeas
    rw [h]
    module
  have hnormalG : -qBar - uBar - vBar = -uBar := by
    have h := eq_neg_of_add_eq_zero_right hfeas
    rw [h]
    module
  have hF := ereal_tilt_tendsto_zero hfbar (fun k ↦ (hgraph k).1) hqs
    (by simpa only [hnormalF, Function.comp_apply] using (hv.neg.sub hu).sub hqs)
  have hG := ereal_tilt_tendsto_zero hgbar (fun k ↦ (hgraph k).2) hvs
    (by simpa only [hnormalG, Function.comp_apply] using (hqs.neg.sub hu).sub hvs)
  constructor
  · apply (tendsto_add_atTop_iff_nat 1).1
    simpa only [neg_dotProduct, EReal.coe_neg, sub_eq_add_neg, neg_neg] using hF
  · apply (tendsto_add_atTop_iff_nat 1).1
    simpa only [neg_dotProduct, EReal.coe_neg, sub_eq_add_neg, neg_neg] using hG

end ADMM.ConvergenceProof
