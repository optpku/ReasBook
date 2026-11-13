/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.Proximal
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.GraphData

@[expose] public section

open scoped BigOperators
open ADMM.ConvergenceProof

namespace ADMM.UnitCircle.Causal

/-- Potential values at selected proximal points, centered at the zero graph
point. Subtracting the minimum value accommodates any constant objective tilt. -/
noncomputable def proximalPotential {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (z : Fin m → ℝ) : ℝ :=
  (φ (proximalMap hφ z)).toReal - (φ 0).toReal

/-- Scaling a proximal map by any `τ∈[0,1]` retains convex graph interpolation
data, including the endpoint `τ=0`. The positive quadratic correction is
computed explicitly, so no convexity of an unspecified scaled objective is
assumed. -/
noncomputable def scaledProximalGraphData {m : ℕ}
    {φ : (Fin m → ℝ) → EReal} (hφ : IsClosedProperConvex φ)
    (hzero : IsSubgradientAt φ 0 0) (z : ℕ → Fin m → ℝ)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    Supply.GraphData (fun k ↦ τ • proximalMap hφ (z k))
      (fun k ↦ z k - τ • proximalMap hφ (z k)) where
  value k := τ * proximalPotential hφ (z k) +
    τ * (1 - τ) / 2 * dotProduct (proximalMap hφ (z k)) (proximalMap hφ (z k))
  nonneg k := by
    have h := subgradient_support_real hzero (proximalMap_subgradient hφ (z k))
    simp only [zero_dotProduct, add_zero] at h
    have hp : 0 ≤ proximalPotential hφ (z k) := by
      dsimp [proximalPotential]
      linarith
    have hq : 0 ≤ dotProduct (proximalMap hφ (z k)) (proximalMap hφ (z k)) :=
      Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
    exact add_nonneg (mul_nonneg hτ0 hp)
      (mul_nonneg (div_nonneg (mul_nonneg hτ0 (sub_nonneg.mpr hτ1)) (by norm_num)) hq)
  origin_upper k := by
    let x := proximalMap hφ (z k)
    have h := subgradient_support_real (proximalMap_subgradient hφ (z k)) hzero
    have hb : proximalPotential hφ (z k) ≤ dotProduct (z k - x) x := by
      dsimp [proximalPotential, x]
      simp only [zero_sub, dotProduct_neg] at h
      linarith
    have hbτ := mul_le_mul_of_nonneg_left hb hτ0
    have hq : 0 ≤ dotProduct x x := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
    have hcoef : 0 ≤ τ * (1 - τ) := mul_nonneg hτ0 (sub_nonneg.mpr hτ1)
    change τ * proximalPotential hφ (z k) + τ * (1 - τ) / 2 * dotProduct x x ≤
      dotProduct (z k - τ • x) (τ • x)
    simp only [sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hbτ ⊢
    nlinarith [mul_nonneg hcoef hq]
  support i j := by
    let x := proximalMap hφ (z i)
    let y := proximalMap hφ (z j)
    have h := subgradient_support_real (proximalMap_subgradient hφ (z i))
      (proximalMap_subgradient hφ (z j))
    have hb : proximalPotential hφ (z i) - proximalPotential hφ (z j) ≤
        dotProduct (z i - x) (x - y) := by
      dsimp [proximalPotential, x, y]
      simp only [dotProduct_sub] at h ⊢
      linarith
    have hbτ := mul_le_mul_of_nonneg_left hb hτ0
    have hq : 0 ≤ dotProduct (x - y) (x - y) :=
      Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
    have hcoef : 0 ≤ τ * (1 - τ) := mul_nonneg hτ0 (sub_nonneg.mpr hτ1)
    have hdefect := mul_nonneg hcoef hq
    change (τ * proximalPotential hφ (z i) + τ * (1 - τ) / 2 * dotProduct x x) -
        (τ * proximalPotential hφ (z j) + τ * (1 - τ) / 2 * dotProduct y y) ≤
      dotProduct (z i - τ • x) (τ • x - τ • y)
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      smul_eq_mul] at hbτ hdefect ⊢
    rw [dotProduct_comm y x] at hdefect
    nlinarith

end ADMM.UnitCircle.Causal
