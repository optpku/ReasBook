/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.UpdatedTargets
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.NormalizedStability
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.ResidualSummability
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Recovery.ReducedConclusions

@[expose] public section

namespace ADMM.UpdatedTargets

open ConvergenceProof FiniteMemory UnitCircle

/-- Lemma C.1 of the updated manuscript. The actual unit-circle bound yields
all reduced convergence conclusions for every initial state. The discounted
state membership, initialized supply correction, and removal of the discount
are discharged by the preceding analytic and causal theorems. -/
theorem unitCircleConvergence : UnitCircleConvergenceClaim := by
  intro ℓ c γ _hℓ hγone _hγtwo hbalance hcoercive m f g hf hg hKKT z
  have hγ : 0 < γ := lt_trans (by norm_num) hγone
  obtain ⟨κ, hκ, hcircle⟩ := hcoercive
  apply Recovery.reducedConclusions_of_residual_summable hγ hf hg hKKT z
  obtain ⟨qStar, vStar, uStar, hstar⟩ := hKKT
  let η : ℕ → Fin m → ℝ := fun k ↦ -(z.v k - vStar)
  let w : ℕ → Fin m → ℝ := fun k ↦ γ⁻¹ • (z.u k - uStar)
  let φOld := reducedNormalizedObjectives f g qStar vStar uStar
  let φ : Fin 2 → (Fin m → ℝ) → EReal :=
    fun b ↦ if b = 0 then φOld .F else φOld .J
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
  have hgeneration : ∀ b k, IsSubgradientAt (φ b)
      (Initialized.actualNormal γ η w b k) (Initialized.actualPoint η w b k) := by
    intro b k
    by_cases hb : b = 0
    · simpa only [φ, φOld, η, w, Initialized.actualNormal, Initialized.actualPoint,
        if_pos hb] using hn .F k
    · simpa only [φ, φOld, η, w, Initialized.actualNormal, Initialized.actualPoint,
        if_neg hb] using hn .J k
  have hstate := Causal.normalized_state_squareSummable_eventually c hγ hκ
    hbalance hcircle η w φ hφ hz hgeneration
  have hr := Initialized.residual_summable_of_discounted_state c hγ hκ
    hbalance hcircle η w φ hz hgeneration hstate
  apply hr.congr
  intro k
  rw [show w (k + 1) - w k = z.q (k + 1) + z.v (k + 1) from
    scaled_multiplier_difference hγ.ne' z.q z.v z.u uStar z.recurrence k]

end ADMM.UpdatedTargets
