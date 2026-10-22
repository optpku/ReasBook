/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GraphLimits

@[expose] public section

open Filter

namespace ADMM.ConvergenceProof

/-- Real tilted objective value at a finite graph point relative to a KKT
support plane. This definition is only used with explicit subgradient data. -/
noncomputable def tiltedValue {m : ℕ} (f : (Fin m → ℝ) → EReal)
    (xStar pStar x : Fin m → ℝ) : ℝ :=
  (f x).toReal - (f xStar).toReal - dotProduct pStar (x - xStar)

/-- A KKT supporting plane makes every generated tilted value nonnegative. -/
theorem tiltedValue_nonneg {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {xStar pStar x p : Fin m → ℝ}
    (hStar : IsSubgradientAt f pStar xStar) (hx : IsSubgradientAt f p x) :
    0 ≤ tiltedValue f xStar pStar x := by
  have h := subgradient_support_real hStar hx
  dsimp only [tiltedValue]
  linarith

/-- The support inequality toward the KKT point gives an upper bound for the
tilted value by translated graph coordinates. -/
theorem tiltedValue_le_pairing {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {xStar pStar x p : Fin m → ℝ}
    (hStar : IsSubgradientAt f pStar xStar) (hx : IsSubgradientAt f p x) :
    tiltedValue f xStar pStar x ≤ dotProduct (p - pStar) (x - xStar) := by
  have h := subgradient_support_real hx hStar
  simp only [dotProduct_sub] at h
  simp only [tiltedValue, sub_dotProduct, dotProduct_sub]
  linarith

/-- Directed support inequalities are invariant under a common translation
and affine tilt. This supplies the signed lag inequalities of the certificate. -/
theorem tiltedValue_support {m : ℕ} {f : (Fin m → ℝ) → EReal}
    (xStar pStar : Fin m → ℝ) {x y p q : Fin m → ℝ}
    (hx : IsSubgradientAt f p x) (hy : IsSubgradientAt f q y) :
    tiltedValue f xStar pStar y - tiltedValue f xStar pStar x ≤
      dotProduct (q - pStar) ((y - xStar) - (x - xStar)) := by
  have h := subgradient_support_real hy hx
  simp only [dotProduct_sub] at h
  simp only [tiltedValue, sub_dotProduct, dotProduct_sub]
  linarith

/-- The generated tilted values vanish whenever both translated graph
coordinates vanish. This is the value part of the storage recentering proof. -/
theorem tiltedValue_tendsto_zero {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {xStar pStar : Fin m → ℝ} {x p : ℕ → Fin m → ℝ}
    (hStar : IsSubgradientAt f pStar xStar)
    (hgraph : ∀ k, IsSubgradientAt f (p k) (x k))
    (hx : Tendsto x atTop (nhds xStar)) (hp : Tendsto p atTop (nhds pStar)) :
    Tendsto (fun k ↦ tiltedValue f xStar pStar (x k)) atTop (nhds 0) := by
  apply squeeze_zero (fun k ↦ tiltedValue_nonneg hStar (hgraph k))
    (fun k ↦ tiltedValue_le_pairing hStar (hgraph k))
  have hxc : Tendsto (fun _ : ℕ ↦ xStar) atTop (nhds xStar) := tendsto_const_nhds
  have hpc : Tendsto (fun _ : ℕ ↦ pStar) atTop (nhds pStar) := tendsto_const_nhds
  simpa only [sub_self, dotProduct_zero] using
    tendsto_dotProduct (hp.sub hpc) (hx.sub hxc)

end ADMM.ConvergenceProof
