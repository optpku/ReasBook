/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.CoordinateNorms
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.FeedbackOperator
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.Disturbance

@[expose] public section

open scoped BigOperators ENNReal

namespace ADMM.UnitCircle.Causal

/-- Coordinate zero extension commutes exactly with real vector addition. -/
theorem coordinateLp_add {m : ℕ} (v w : ℕ → BlockVector m)
    (hv : Memℓp v 2) (hw : Memℓp w 2) (b : Fin 2) (a : Fin m) :
    coordinateLp (v + w) (hv.add hw) b a = coordinateLp v hv b a + coordinateLp w hw b a := by
  ext k
  cases k with
  | ofNat k => simp [Complex.ofReal_add]
  | negSucc k =>
      change coordinateLp (v + w) (hv.add hw) b a (-(k + 1 : ℤ)) =
        coordinateLp v hv b a (-(k + 1 : ℤ)) + coordinateLp w hw b a (-(k + 1 : ℤ))
      simp only [coordinateLp_negSucc, zero_add]

/-- Coordinate zero extension commutes with real scalar multiplication. -/
theorem coordinateLp_smul {m : ℕ} (v : ℕ → BlockVector m)
    (hv : Memℓp v 2) (r : ℝ) (b : Fin 2) (a : Fin m) :
    coordinateLp (r • v) (hv.const_smul r) b a = (r : ℂ) • coordinateLp v hv b a := by
  ext k
  change coordinateLp (r • v) (hv.const_smul r) b a k =
    (r : ℂ) * coordinateLp v hv b a k
  cases k with
  | ofNat k => simp [Complex.ofReal_mul]
  | negSucc k =>
      change coordinateLp (r • v) (hv.const_smul r) b a (-(k + 1 : ℤ)) =
        (r : ℂ) * coordinateLp v hv b a (-(k + 1 : ℤ))
      simp only [coordinateLp_negSucc, mul_zero]

/-- The actual two-block convex supply in already discounted coordinates. -/
noncomputable def pairedSupply {m ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (v y : ℕ → BlockVector m) (hv : Memℓp v 2) (hy : Memℓp y 2) : ℝ :=
  ∑ b : Fin 2, ∑ a : Fin m,
    (inner ℂ (coordinateLp v hv b a - coordinateLp y hy b a)
      (Fourier.lagOperator c α b (coordinateLp y hy b a))).re

/-- The disturbance contribution uses the same concrete lag operators as
the Parseval and convexity inequalities. -/
noncomputable def forcingPairing {m ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (e y : ℕ → BlockVector m) (he : Memℓp e 2) (hy : Memℓp y 2) : ℝ :=
  ∑ b : Fin 2, ∑ a : Fin m,
    (inner ℂ (coordinateLp e he b a)
      (Fourier.lagOperator c α b (coordinateLp y hy b a))).re

theorem forcingPairing_le {m ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (e y : ℕ → BlockVector m) (he : Memℓp e 2) (hy : Memℓp y 2) :
    forcingPairing c α e y he hy ≤ Fourier.lagUniformBound c α *
      √(coordinateEnergy e he) * √(coordinateEnergy y hy) :=
  Fourier.disturbance_cross_bound_curried c α (coordinateLp e he) (coordinateLp y hy)

/-- Splitting the exact feedback input into the zero-state input and forcing
splits its supply into precisely the two terms used in the small-gain bound. -/
theorem pairedSupply_split {m ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (u e y : ℕ → BlockVector m) (hu : Memℓp u 2) (he : Memℓp e 2) (hy : Memℓp y 2) :
    pairedSupply c α (e + u) y (he.add hu) hy =
      pairedSupply c α u y hu hy + forcingPairing c α e y he hy := by
  unfold pairedSupply forcingPairing
  simp_rw [coordinateLp_add e u he hu]
  simp only [add_sub_assoc, inner_add_left, Complex.add_re, Finset.sum_add_distrib]
  ring

/-- Absorbing the strict output separation produces a bound on the output
energy; this also covers a zero output in any dimension. -/
theorem output_energy_bound_of_supply {m ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (u e y : ℕ → BlockVector m) (hu : Memℓp u 2) (he : Memℓp e 2) (hy : Memℓp y 2)
    {δ : ℝ} (hδ : 0 < δ)
    (hnonneg : 0 ≤ pairedSupply c α (e + u) y (he.add hu) hy)
    (hsep : pairedSupply c α u y hu hy ≤ -δ * coordinateEnergy y hy) :
    √(coordinateEnergy y hy) ≤
      Fourier.lagUniformBound c α / δ * √(coordinateEnergy e he) := by
  rw [pairedSupply_split c α u e y hu he hy] at hnonneg
  have hcross := forcingPairing_le c α e y he hy
  have hey : 0 ≤ coordinateEnergy y hy :=
    (sq_nonneg _).trans (coordinateEnergy_bounds y hy).1
  have hee : 0 ≤ coordinateEnergy e he :=
    (sq_nonneg _).trans (coordinateEnergy_bounds e he).1
  have hs := Real.sq_sqrt hey
  have hsy := Real.sqrt_nonneg (coordinateEnergy y hy)
  have hse := Real.sqrt_nonneg (coordinateEnergy e he)
  have hB := Fourier.lagUniformBound_pos c α
  by_cases hy0 : √(coordinateEnergy y hy) = 0
  · rw [hy0]
    positivity
  · have hyp : 0 < √(coordinateEnergy y hy) := lt_of_le_of_ne hsy (Ne.symm hy0)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hδ).mpr
    by_contra h
    have hp : 0 < δ * √(coordinateEnergy y hy) -
        Fourier.lagUniformBound c α * √(coordinateEnergy e he) := by
      nlinarith
    have hprod := mul_pos hp hyp
    nlinarith

end ADMM.UnitCircle.Causal
