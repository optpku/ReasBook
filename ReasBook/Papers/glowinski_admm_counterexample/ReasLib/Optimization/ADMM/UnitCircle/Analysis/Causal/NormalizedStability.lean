/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.Apriori
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.DiscountedCoercivity
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.InitialData

@[expose] public section

open Filter ADMM.ConvergenceProof
open scoped ENNReal Topology

namespace ADMM.UnitCircle.Causal

/-- The causal convention discounts manuscript time `k+1`. Removing its
single common factor `α` yields the weighted convention used in supply sums. -/
theorem squareSummable_of_shifted_discount_memℓp {m : ℕ} {α : ℝ} (hα : 0 < α)
    (x : ℕ → EuclideanSpace ℝ (Fin m))
    (hx : Memℓp (fun k ↦ α ^ (k + 1) • x (k + 1)) 2) :
    Initialized.SquareSummable α (fun k ↦ WithLp.ofLp (x (k + 1))) := by
  have hx0 : Memℓp (fun k ↦ α ^ k • x (k + 1)) 2 := by
    convert! hx.const_smul α⁻¹ using 1
    funext k
    simp only [Pi.smul_apply, smul_smul, pow_succ]
    rw [mul_comm (α ^ k) α, ← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
  have hs : Summable (fun k ↦ ‖α ^ k • x (k + 1)‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hx0.summable (by norm_num)
  apply hs.congr
  intro k
  rw [← block_square_eq]
  simp only [WithLp.ofLp_smul, Initialized.coordinateSquare_smul,
    Supply.timeWeight, ← pow_mul, Nat.mul_comm k 2]

/-- Every normalized reduced orbit has square-summable discounted states
for all strict discounts close enough to one. All causal and proximal
membership work has been discharged, with arbitrary initial states retained. -/
theorem normalized_state_squareSummable_eventually {m ℓ : ℕ} (c : LagWeights ℓ)
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (hbalance : BalancedMoments c) (hcircle : HasCoercivityBound c γ κ)
    (η w : ℕ → Fin m → ℝ) (φ : Fin 2 → (Fin m → ℝ) → EReal)
    (hφ : ∀ b, IsClosedProperConvex (φ b))
    (hzero : ∀ b, IsSubgradientAt (φ b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (φ b)
      (Initialized.actualNormal γ η w b k) (Initialized.actualPoint η w b k)) :
    ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ),
      Initialized.SquareSummable α (fun k ↦ η (k + 1)) ∧
      Initialized.SquareSummable α (fun k ↦ w (k + 1)) := by
  obtain ⟨c₀, δ, hc₀, hδ, hQ⟩ :=
    supplySymbol_discounted_coercivity c hγ hκ hbalance hcircle
  have hα0 : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), 0 < α :=
    (show ∀ᶠ α : ℝ in 𝓝 (1 : ℝ), 0 < α from
      lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hα1 : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), α < 1 := self_mem_nhdsWithin
  have hclose : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), 1 - δ < α :=
    (show ∀ᶠ α : ℝ in 𝓝 (1 : ℝ), 1 - δ < α from
      lt_mem_nhds (show 1 - δ < (1 : ℝ) by linarith)).filter_mono nhdsWithin_le_nhds
  have hcorr := (Supply.eventually_discountCorrection_small c).filter_mono
    (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
  filter_upwards [hα0, hα1, hclose, hcorr] with α ha0 ha1 hac hco
  obtain ⟨C, hC, hestimate⟩ := discountedInput_apriori c hφ hzero ha0 ha1 hc₀ (hQ α hac ha1) hco
  let ηE : ℕ → EuclideanSpace ℝ (Fin m) := fun k ↦ WithLp.toLp 2 (η k)
  let wE : ℕ → EuclideanSpace ℝ (Fin m) := fun k ↦ WithLp.toLp 2 (w k)
  let q : ℕ → EuclideanSpace ℝ (Fin m) :=
    fun k ↦ WithLp.toLp 2 (η k + (w k - w (k - 1)))
  have hfirst : ∀ k, IsSubgradientAt (φ 0)
      (WithLp.ofLp (ηE k - γ • wE k - q (k + 1))) (WithLp.ofLp (q (k + 1))) := by
    intro k
    simpa [ηE, wE, q, Initialized.actualPoint, Initialized.actualNormal,
      generatedPosition, generatedNormal] using hgraph 0 k
  have hsecond : ∀ k, IsSubgradientAt (φ 1)
      (WithLp.ofLp (q (k + 1) + γ • wE k - ηE (k + 1)))
      (WithLp.ofLp (ηE (k + 1))) := by
    intro k
    have hn : WithLp.ofLp (q (k + 1) + γ • wE k - ηE (k + 1)) =
        Initialized.actualNormal γ η w 1 k := by
      simp [ηE, wE, q, Initialized.actualNormal, generatedNormal]
      module
    have hp : WithLp.ofLp (ηE (k + 1)) = Initialized.actualPoint η w 1 k := by
      simp [ηE, Initialized.actualPoint, generatedPosition]
    rw [hn, hp]
    exact hgraph 1 k
  have hrec : ∀ k, wE (k + 1) = wE k + q (k + 1) - ηE (k + 1) := by
    intro k
    apply WithLp.ofLp_injective
    simp [ηE, wE, q]
    module
  have hs := initialized_discounted_state_memℓp hφ hzero ha0 ha1 γ q ηE wE
    hfirst hsecond hrec hC hestimate
  have hη : Memℓp (fun k ↦ α ^ (k + 1) • ηE (k + 1)) 2 := by
    simpa [discountedOutputs] using hs.1.mono'
      (fun k ↦ norm_le_pi_norm (discountedOutputs α q ηE k) 1)
  constructor
  · simpa only [ηE, WithLp.ofLp_toLp] using
      squareSummable_of_shifted_discount_memℓp ha0 ηE hη
  · simpa only [wE, WithLp.ofLp_toLp] using
      squareSummable_of_shifted_discount_memℓp ha0 wE hs.2

end ADMM.UnitCircle.Causal
