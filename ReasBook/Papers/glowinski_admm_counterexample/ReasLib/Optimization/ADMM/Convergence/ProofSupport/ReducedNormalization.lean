/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GraphNormalization
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.OrbitConvergence
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.FiniteMemoryBounds
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.ClassicalConvergence

@[expose] public section

open Filter ADMM.FiniteMemory

namespace ADMM.ConvergenceProof

/-- The two recentered and tilted objectives in certificate coordinates. -/
noncomputable def reducedNormalizedObjectives {m : ℕ}
    (f g : (Fin m → ℝ) → EReal) (qStar vStar uStar : Fin m → ℝ)
    (b : Block) : (Fin m → ℝ) → EReal :=
  match b with
  | .F => normalizedObjective f qStar (-uStar)
  | .J => fun x ↦ normalizedObjective g vStar (-uStar) (-x)

/-- The standard reduced-coordinate scaling preserves the residual. -/
theorem scaled_multiplier_difference {m : ℕ} {γ : ℝ} (hγ : γ ≠ 0)
    (q v u : ℕ → Fin m → ℝ) (uStar : Fin m → ℝ)
    (hrec : ∀ k, u (k + 1) = u k + γ • (q (k + 1) + v (k + 1))) (k : ℕ) :
    γ⁻¹ • (u (k + 1) - uStar) - γ⁻¹ • (u k - uStar) = q (k + 1) + v (k + 1) := by
  rw [← smul_sub]
  have hin : (u (k + 1) - uStar) - (u k - uStar) =
      γ • (q (k + 1) + v (k + 1)) := by rw [hrec]; module
  rw [hin, smul_smul, inv_mul_cancel₀ hγ, one_smul]

/-- Recentered reduced subgradient relations are exactly the graph relations
used by every finite-memory and classical energy estimate. -/
theorem reduced_normalized_graph {m : ℕ} {γ : ℝ} (hγ : γ ≠ 0)
    {f g : (Fin m → ℝ) → EReal} (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    (q v u : ℕ → Fin m → ℝ) (qStar vStar uStar : Fin m → ℝ)
    (hfeas : qStar + vStar = 0)
    (hrec : ∀ k, u (k + 1) = u k + γ • (q (k + 1) + v (k + 1)))
    (hfirst : ∀ k, IsSubgradientAt f (-v k - u k - q (k + 1)) (q (k + 1)))
    (hsecond : ∀ k, IsSubgradientAt g (-q (k + 1) - u k - v (k + 1)) (v (k + 1))) :
    ∀ b k, IsSubgradientAt (reducedNormalizedObjectives f g qStar vStar uStar b)
      (generatedNormal γ (fun k ↦ -(v k - vStar)) (fun k ↦ γ⁻¹ • (u k - uStar)) b k)
      (generatedPosition (fun k ↦ -(v k - vStar)) (fun k ↦ γ⁻¹ • (u k - uStar)) b k) := by
  intro b k
  have hr := scaled_multiplier_difference hγ q v u uStar hrec k
  have hu : γ • (γ⁻¹ • (u k - uStar)) = u k - uStar := by
    rw [smul_smul, mul_inv_cancel₀ hγ, one_smul]
  have hvStar : vStar = -qStar := eq_neg_of_add_eq_zero_right hfeas
  cases b with
  | F =>
    have h := subgradient_normalized hf qStar (-uStar) (hfirst k)
    have hpos : generatedPosition (fun k ↦ -(v k - vStar))
        (fun k ↦ γ⁻¹ • (u k - uStar)) .F k = q (k + 1) - qStar := by
      dsimp only [generatedPosition]
      rw [hr, hvStar]
      module
    have hnormal : generatedNormal γ (fun k ↦ -(v k - vStar))
        (fun k ↦ γ⁻¹ • (u k - uStar)) .F k =
        (-v k - u k - q (k + 1)) - -uStar := by
      dsimp only [generatedNormal]
      rw [hpos, hu, hvStar]
      module
    simpa only [reducedNormalizedObjectives, hnormal, hpos] using h
  | J =>
    have h := subgradient_reflected (subgradient_normalized hg vStar (-uStar) (hsecond k))
    have hnormal : generatedNormal γ (fun k ↦ -(v k - vStar))
        (fun k ↦ γ⁻¹ • (u k - uStar)) .J k =
        -((-q (k + 1) - u k - v (k + 1)) - -uStar) := by
      dsimp only [generatedNormal]
      rw [hu, hr]
      module
    simpa only [reducedNormalizedObjectives, generatedPosition, hnormal] using h

/-- Both recentered objectives retain closed proper convexity and the zero
KKT graph point. -/
theorem reduced_normalized_data {m : ℕ} {f g : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    {qStar vStar uStar : Fin m → ℝ}
    (hfStar : IsSubgradientAt f (-uStar) qStar)
    (hgStar : IsSubgradientAt g (-uStar) vStar) :
    (∀ b, IsClosedProperConvex (reducedNormalizedObjectives f g qStar vStar uStar b)) ∧
      ∀ b, IsSubgradientAt (reducedNormalizedObjectives f g qStar vStar uStar b) 0 0 := by
  constructor
  · intro b
    cases b with
    | F => exact normalizedObjective_closedProperConvex hf hfStar
    | J => exact reflectedObjective_closedProperConvex (normalizedObjective_closedProperConvex hg hgStar)
  · intro b
    cases b with
    | F => exact subgradient_normalized_zero hf hfStar
    | J => simpa only [neg_zero, reducedNormalizedObjectives] using subgradient_reflected (subgradient_normalized_zero hg hgStar)

/-- Reduced ADMM converges whenever its parameter is in the classical range
or admits a finite-memory certificate. The theorem preserves arbitrary
initial states and all original dimensions. -/
theorem reduced_orbit_converges {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {f g : (Fin m → ℝ) → EReal} (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    (q v u : ℕ → Fin m → ℝ) (qStar vStar uStar : Fin m → ℝ)
    (hfeas : qStar + vStar = 0)
    (hfStar : IsSubgradientAt f (-uStar) qStar)
    (hgStar : IsSubgradientAt g (-uStar) vStar)
    (hrec : ∀ k, u (k + 1) = u k + γ • (q (k + 1) + v (k + 1)))
    (hfirst : ∀ k, IsSubgradientAt f (-v k - u k - q (k + 1)) (q (k + 1)))
    (hsecond : ∀ k, IsSubgradientAt g (-q (k + 1) - u k - v (k + 1)) (v (k + 1)))
    (hparameter : γ < 3 / 2 ∨ ∃ ℓ, Nonempty (Certificate ℓ γ)) :
    ∃ qBar vBar uBar, Tendsto q atTop (nhds qBar) ∧
      Tendsto v atTop (nhds vBar) ∧ Tendsto u atTop (nhds uBar) := by
  let φ := reducedNormalizedObjectives f g qStar vStar uStar
  let η : ℕ → Fin m → ℝ := fun k ↦ -(v k - vStar)
  let w : ℕ → Fin m → ℝ := fun k ↦ γ⁻¹ • (u k - uStar)
  have hdata := reduced_normalized_data hf hg hfStar hgStar
  have hgraph := reduced_normalized_graph hγ.ne' hf hg q v u qStar vStar uStar
    hfeas hrec hfirst hsecond
  have hbounds : Summable (fun k ↦ coordinateSquare (w (k + 1) - w k)) ∧
      ∃ C : ℝ, ∀ k, coordinateSquare (η k) + coordinateSquare (w k) ≤ C := by
    rcases hparameter with hsmall | ⟨ℓ, ⟨c⟩⟩
    · exact classical_residual_summable_bounded hγ hsmall φ η w hdata.2 hgraph
    · exact ⟨finiteMemory_residual_summable c φ η w hdata.2 hgraph,
        finiteMemory_state_bounded c φ η w hdata.2 hgraph⟩
  obtain ⟨ηBar, wBar, hη, hw, _⟩ := reduced_converges_of_bounded_summable
    hγ φ η w hdata.1 hdata.2 hgraph hbounds.2 hbounds.1
  have hv : Tendsto v atTop (nhds (vStar - ηBar)) := by
    have hc : Tendsto (fun _ : ℕ ↦ vStar) atTop (nhds vStar) := tendsto_const_nhds
    have h := hc.sub hη
    convert h using 1
    funext k
    dsimp only [η]
    module
  have hu : Tendsto u atTop (nhds (γ • wBar + uStar)) := by
    have h := (hw.const_smul γ).add_const uStar
    simpa only [w, smul_smul, mul_inv_cancel₀ hγ.ne', one_smul, sub_add_cancel] using h
  have hr : Tendsto (fun k ↦ q (k + 1) + v (k + 1)) atTop (nhds 0) := by
    have h := tendsto_zero_of_coordinateSquare hbounds.1.tendsto_atTop_zero
    simpa only [w, scaled_multiplier_difference hγ.ne' q v u uStar hrec] using h
  have hqs : Tendsto (fun k ↦ q (k + 1)) atTop (nhds (ηBar - vStar)) := by
    have h := hr.sub (hv.comp (tendsto_add_atTop_nat 1))
    have hlim : (0 : Fin m → ℝ) - (vStar - ηBar) = ηBar - vStar := by module
    simpa only [Function.comp_def, add_sub_cancel_right, hlim] using h
  exact ⟨ηBar - vStar, vStar - ηBar, γ • wBar + uStar,
    (tendsto_add_atTop_iff_nat 1).1 hqs, hv, hu⟩

end ADMM.ConvergenceProof
