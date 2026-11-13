/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.MeritBound
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.NormalizedStability

@[expose] public section

open ADMM.ConvergenceProof Filter
open scoped BigOperators Topology

namespace ADMM.UnitCircle.Initialized

open Supply

/-- The origin merits of the fixed initial KKT normalization are summable,
with no assumption on the initialized trajectory's boundedness. -/
theorem normalized_originMerit_summable {m ℓ : ℕ} (c : LagWeights ℓ)
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (hbalance : BalancedMoments c) (hcircle : HasCoercivityBound c γ κ)
    (η w : ℕ → Fin m → ℝ) (φ : Fin 2 → (Fin m → ℝ) → EReal)
    (hφ : ∀ b, IsClosedProperConvex (φ b)) (hzero : ∀ b, IsSubgradientAt (φ b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (φ b) (actualNormal γ η w b k) (actualPoint η w b k)) :
    ∀ b, Summable (originMerit γ η w b) := by
  have hstate := Causal.normalized_state_squareSummable_eventually c hγ hκ
    hbalance hcircle η w φ hφ hzero hgraph
  obtain ⟨c₀, δ, hc₀, hδ, hQ⟩ := supplySymbol_discounted_coercivity c hγ hκ hbalance hcircle
  have hα0 : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), 0 < α :=
    (show ∀ᶠ α : ℝ in 𝓝 (1 : ℝ), 0 < α from
      lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hα1 : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), α < 1 := self_mem_nhdsWithin
  have hclose : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), 1 - δ < α :=
    (show ∀ᶠ α : ℝ in 𝓝 (1 : ℝ), 1 - δ < α from
      lt_mem_nhds (show 1 - δ < (1 : ℝ) by linarith)).filter_mono nhdsWithin_le_nhds
  have hcorr := (eventually_discountCorrection_small c).filter_mono
    (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
  have hM0 (b : Fin 2) (k : ℕ) : 0 ≤ originMerit γ η w b k :=
    (graphValue_bounds (hzero b) (hgraph b k)).1.trans
      (graphValue_bounds (hzero b) (hgraph b k)).2
  have hMT0 (k : ℕ) : 0 ≤ totalMerit γ η w k := Finset.sum_nonneg (fun b _ ↦ hM0 b k)
  have hbound : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ),
      Summable (fun k ↦ α ^ (2 * k) *
        (c.epsilon * coordinateSquare (actualResidual w k) + (c.omega / 2) * totalMerit γ η w k)) ∧
      (∑' k, α ^ (2 * k) *
        (c.epsilon * coordinateSquare (actualResidual w k) + (c.omega / 2) * totalMerit γ η w k)) ≤
          initializationError c γ η w := by
    filter_upwards [hstate, hα0, hα1, hclose, hcorr] with α hs ha0 ha1 hac hco
    have hr := weighted_actualResidual_summable w hs.2
    have hm (b : Fin 2) := summable_weighted_dot
      (actualNormal_squareSummable γ η w hs.1 hs.2 b)
      (actualPoint_squareSummable η w hs.1 hs.2 b)
    have hmt : Summable (fun k ↦ timeWeight α k * totalMerit γ η w k) := by
      apply (summable_sum (s := Finset.univ) (fun b _ ↦ hm b)).congr
      intro k
      simp only [totalMerit, originMerit, Finset.mul_sum]
    have hsr := hr.mul_left c.epsilon
    have hsm := hmt.mul_left (c.omega / 2)
    constructor
    · apply (hsr.add hsm).congr
      intro k
      dsimp only [timeWeight]
      ring
    · calc
        _ = c.epsilon * (∑' k, timeWeight α k * coordinateSquare (actualResidual w k)) +
            (c.omega / 2) * (∑' k, timeWeight α k * totalMerit γ η w k) := by
          calc
            _ = ∑' k, (c.epsilon * (timeWeight α k * coordinateSquare (actualResidual w k)) +
                (c.omega / 2) * (timeWeight α k * totalMerit γ η w k)) := by
              apply tsum_congr
              intro k
              dsimp only [timeWeight]
              ring
            _ = _ := by rw [hsr.tsum_add hsm, tsum_mul_left, tsum_mul_left]
        _ ≤ _ := initialized_merit_bound c ha0.le ha1.le hc₀.le (hQ α hac ha1)
          η w φ hzero hgraph hs.1 hs.2 hco
  have hpair := two_dissipations_summable_of_discounted_tsum_le c.epsilon_pos
    (div_pos c.omega_pos (by norm_num))
    (fun k ↦ coordinateSquare_nonneg (actualResidual w k)) hMT0
    (show Tendsto (fun α : ℝ ↦ α) (𝓝[<] (1 : ℝ)) (𝓝 1) from nhdsWithin_le_nhds) hbound
  intro b
  apply Summable.of_nonneg_of_le (hM0 b) (fun k ↦ ?_) hpair.2
  exact Finset.single_le_sum (fun i _ ↦ hM0 i k) (Finset.mem_univ b)

/-- Both tilted graph heights vanish relative to the fixed normalization,
including when the state limit differs from the chosen KKT origin. -/
theorem normalized_graphValue_tendsto_zero {m ℓ : ℕ} (c : LagWeights ℓ)
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (hbalance : BalancedMoments c) (hcircle : HasCoercivityBound c γ κ)
    (η w : ℕ → Fin m → ℝ) (φ : Fin 2 → (Fin m → ℝ) → EReal)
    (hφ : ∀ b, IsClosedProperConvex (φ b)) (hzero : ∀ b, IsSubgradientAt (φ b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (φ b) (actualNormal γ η w b k) (actualPoint η w b k)) :
    ∀ b, Tendsto (fun k ↦ graphValue (φ b) (actualPoint η w b k)) atTop (𝓝 0) := by
  have hm := normalized_originMerit_summable c hγ hκ hbalance hcircle η w φ hφ hzero hgraph
  intro b
  apply squeeze_zero (fun k ↦ (graphValue_bounds (hzero b) (hgraph b k)).1)
    (fun k ↦ (graphValue_bounds (hzero b) (hgraph b k)).2)
    (hm b).tendsto_atTop_zero

/-- Finite subgradient graph values identify the real graph height with the
extended-real objective difference, without a continuity assumption. -/
theorem graphValue_coe_eq {m : ℕ} {f : (Fin m → ℝ) → EReal}
    (hzero : IsSubgradientAt f 0 0) {x g : Fin m → ℝ}
    (hx : IsSubgradientAt f g x) : (graphValue f x : EReal) = f x - f 0 := by
  rw [graphValue, EReal.coe_sub, ← subgradient_value_real hx, ← subgradient_value_real hzero]

/-- The exact tilted objective differences vanish in the extended-real topology
relative to the initially fixed KKT normalization, even at domain boundaries. -/
theorem normalized_erealValue_tendsto_zero {m ℓ : ℕ} (c : LagWeights ℓ)
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (hbalance : BalancedMoments c) (hcircle : HasCoercivityBound c γ κ)
    (η w : ℕ → Fin m → ℝ) (φ : Fin 2 → (Fin m → ℝ) → EReal)
    (hφ : ∀ b, IsClosedProperConvex (φ b)) (hzero : ∀ b, IsSubgradientAt (φ b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (φ b) (actualNormal γ η w b k) (actualPoint η w b k)) :
    ∀ b, Tendsto (fun k ↦ φ b (actualPoint η w b k) - φ b 0) atTop (𝓝 0) := by
  have hv := normalized_graphValue_tendsto_zero c hγ hκ hbalance hcircle
    η w φ hφ hzero hgraph
  intro b
  have h := continuous_coe_real_ereal.continuousAt.tendsto.comp (hv b)
  simpa only [Function.comp_def, graphValue_coe_eq (hzero b) (hgraph b _),
    EReal.coe_zero] using h

end ADMM.UnitCircle.Initialized
