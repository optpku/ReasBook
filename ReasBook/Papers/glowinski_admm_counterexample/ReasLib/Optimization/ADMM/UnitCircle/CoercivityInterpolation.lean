/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Symbol
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped ComplexOrder

namespace ADMM.UnitCircle

/-- The unit-circle inequality at a specified common coefficient. Positivity
of `κ` is imposed when this bound is used as a convergence certificate. -/
def HasCoercivityBound {ℓ : ℕ} (c : LagWeights ℓ) (γ κ : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    (supplySymbol c 1 γ z -
      ((κ * Complex.normSq (delaySymbol 1 z) : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef

/-- A fixed pointwise lower bound is preserved by convex interpolation in
the multiplier factor. The bound can vanish at zero frequency. -/
theorem supplySymbol_coercive_affine {ℓ : ℕ} (c : LagWeights ℓ)
    (γMinus γPlus κ θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (z : ℂ)
    (hMinus : (supplySymbol c 1 γMinus z -
      ((κ * Complex.normSq (delaySymbol 1 z) : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
    (hPlus : (supplySymbol c 1 γPlus z -
      ((κ * Complex.normSq (delaySymbol 1 z) : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef) :
    (supplySymbol c 1 ((1 - θ) * γMinus + θ * γPlus) z -
      ((κ * Complex.normSq (delaySymbol 1 z) : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
  have hcomb :=
    (hMinus.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hθ1))).add
      (hPlus.smul (Complex.zero_le_real.mpr hθ0))
  convert hcomb using 1
  rw [supplySymbol_affine]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The same positive coercivity coefficient at two endpoint factors works
throughout every convex interpolation, with the lag weights fixed. -/
theorem HasCoercivityBound.affine {ℓ : ℕ} {c : LagWeights ℓ}
    {γMinus γPlus κ θ : ℝ}
    (hMinus : HasCoercivityBound c γMinus κ)
    (hPlus : HasCoercivityBound c γPlus κ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    HasCoercivityBound c ((1 - θ) * γMinus + θ * γPlus) κ := by
  intro z hz
  exact supplySymbol_coercive_affine c γMinus γPlus κ θ hθ0 hθ1 z
    (hMinus z hz) (hPlus z hz)

/-- Ordered endpoint bounds cover the closed interval between the endpoints.
This is the parameter-affinity step in Appendix C.2. -/
theorem HasCoercivityBound.on_interval {ℓ : ℕ} {c : LagWeights ℓ}
    {γMinus γPlus γ κ : ℝ}
    (hMinus : HasCoercivityBound c γMinus κ)
    (hPlus : HasCoercivityBound c γPlus κ)
    (hEndpoints : γMinus < γPlus) (hγMinus : γMinus ≤ γ) (hγPlus : γ ≤ γPlus) :
    HasCoercivityBound c γ κ := by
  let θ := (γ - γMinus) / (γPlus - γMinus)
  have hden : 0 < γPlus - γMinus := sub_pos.mpr hEndpoints
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hγMinus) hden.le
  have hθ1 : θ ≤ 1 := by
    exact (div_le_one hden).mpr (sub_le_sub_right hγPlus γMinus)
  have hγ : (1 - θ) * γMinus + θ * γPlus = γ := by
    dsimp [θ]
    field_simp
    ring
  simpa only [hγ] using hMinus.affine hPlus hθ0 hθ1

end ADMM.UnitCircle
