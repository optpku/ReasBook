/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.UnitCircleConvergence
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.MeritSummability

@[expose] public section

open Filter ADMM.ConvergenceProof ADMM.UnitCircle
open scoped Topology

namespace ADMM.FiniteMemory.ReducedTrajectory

/-- The affine tilt is zero at its chosen finite supporting graph point. -/
theorem normalizedObjective_origin_value {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {xStar pStar : Fin m → ℝ} (hStar : IsSubgradientAt f pStar xStar) :
    normalizedObjective f xStar pStar 0 = 0 := by
  simp only [normalizedObjective, zero_add, dotProduct_zero, sub_zero]
  rw [subgradient_value_real hStar, ← EReal.coe_add]
  simp

/-- The two tilted values in Lemma C.1 vanish relative to any KKT triple
fixed before the iteration, even when the trajectory converges to a different
KKT triple. This is the normalization used in the manuscript's graph supplies. -/
theorem circle_fixedAnchor_tiltedValues {m ℓ : ℕ} {γ κ : ℝ}
    {f g : (Fin m → ℝ) → EReal} (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    {qStar vStar uStar : Fin m → ℝ} (hstar : ReducedIsKKT f g qStar vStar uStar)
    (z : ReducedTrajectory f g γ) (c : LagWeights ℓ) (hγ : 0 < γ) (hκ : 0 < κ)
    (hbalance : BalancedMoments c) (hcircle : HasCoercivityBound c γ κ) :
    ∀ b, Tendsto (fun k ↦ reducedNormalizedObjectives f g qStar vStar uStar b
      (generatedPosition (fun j ↦ -(z.v j - vStar))
        (fun j ↦ γ⁻¹ • (z.u j - uStar)) b k)) atTop (𝓝 0) := by
  let η : ℕ → Fin m → ℝ := fun k ↦ -(z.v k - vStar)
  let w : ℕ → Fin m → ℝ := fun k ↦ γ⁻¹ • (z.u k - uStar)
  let φOld := reducedNormalizedObjectives f g qStar vStar uStar
  let φ : Fin 2 → (Fin m → ℝ) → EReal := fun b ↦ if b = 0 then φOld .F else φOld .J
  have hd := reduced_normalized_data hf hg hstar.2.1 hstar.2.2
  have hn := reduced_normalized_graph hγ.ne' hf hg z.q z.v z.u
    qStar vStar uStar hstar.1 z.recurrence z.first z.second
  have hφ : ∀ b, IsClosedProperConvex (φ b) := by
    intro b
    by_cases hb : b = 0
    · simpa only [φ, φOld, if_pos hb] using hd.1 .F
    · simpa only [φ, φOld, if_neg hb] using hd.1 .J
  have hz : ∀ b, IsSubgradientAt (φ b) 0 0 := by
    intro b
    by_cases hb : b = 0
    · simpa only [φ, φOld, if_pos hb] using hd.2 .F
    · simpa only [φ, φOld, if_neg hb] using hd.2 .J
  have hgen : ∀ b k, IsSubgradientAt (φ b)
      (Initialized.actualNormal γ η w b k) (Initialized.actualPoint η w b k) := by
    intro b k
    by_cases hb : b = 0
    · simpa only [φ, φOld, η, w, Initialized.actualNormal, Initialized.actualPoint,
        if_pos hb] using hn .F k
    · simpa only [φ, φOld, η, w, Initialized.actualNormal, Initialized.actualPoint,
        if_neg hb] using hn .J k
  have hv := Initialized.normalized_erealValue_tendsto_zero c hγ hκ hbalance hcircle
    η w φ hφ hz hgen
  intro b
  cases b with
  | F =>
    have hzF : φ 0 0 = 0 := by
      exact normalizedObjective_origin_value hstar.2.1
    simpa only [hzF, sub_zero, φ, φOld, Initialized.actualPoint, ite_true, η, w] using hv 0
  | J =>
    have hzJ : φ 1 0 = 0 := by
      simpa only [φ, φOld, one_ne_zero, ite_false, reducedNormalizedObjectives, neg_zero] using
        normalizedObjective_origin_value hstar.2.2
    simpa only [hzJ, sub_zero, φ, φOld, Initialized.actualPoint,
      one_ne_zero, ite_false, η, w] using hv 1

end ADMM.FiniteMemory.ReducedTrajectory
