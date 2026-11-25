/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.RadialExpansion
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Sylvester

@[expose] public section

open scoped BigOperators ComplexOrder

namespace ADMM.UnitCircle

/-- Constructed matrix divided difference of the actual discounted supply. -/
noncomputable def supplyRadialRemainder {ℓ : ℕ} (c : LagWeights ℓ)
    (γ α : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j ↦ (supplySymbol_radialExpansion c γ i j).remainder α z

/-- Exact polynomial radial expansion; its remainder is defined also at `α=1`. -/
theorem supplySymbol_radial_identity {ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ) (z : ℂ) :
    supplySymbol c α γ z = supplySymbol c 1 γ z +
      ((1 - α : ℝ) : ℂ) • supplyRadialRemainder c γ α z := by
  ext i j
  exact (supplySymbol_radialExpansion c γ i j).identity α z

/-- The constructed remainder is jointly continuous off the pole `z=0`. -/
theorem supplyRadialRemainder_continuousAt {ℓ : ℕ} (c : LagWeights ℓ)
    (γ : ℝ) (p : ℝ × ℂ) (hp : p.2 ≠ 0) :
    ContinuousAt (fun q : ℝ × ℂ ↦ supplyRadialRemainder c γ q.1 q.2) p := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (supplySymbol_radialExpansion c γ i j).continuous_remainder p hp

/-- Away from `α=1`, the remainder is the usual radial quotient. -/
theorem supplyRadialRemainder_eq_quotient {ℓ : ℕ} (c : LagWeights ℓ)
    (γ α : ℝ) (z : ℂ) (hα : α ≠ 1) (i j : Fin 2) :
    supplyRadialRemainder c γ α z i j =
      (supplySymbol c α γ z i j - supplySymbol c 1 γ z i j) /
        ((1 - α : ℝ) : ℂ) := by
  have ha : ((1 - α : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (Ne.symm hα)
  apply (eq_div_iff ha).mpr
  have h := (supplySymbol_radialExpansion c γ i j).identity α z
  change _ = _ + _ * supplyRadialRemainder c γ α z i j at h
  rw [h]
  ring

/-- Balanced first moments identify the continuous remainder at zero frequency
with the strictly positive first-order diagonal of the actual supply. -/
theorem supplyRadialRemainder_one_one {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ)
    (hbalance : BalancedMoments c) :
    supplyRadialRemainder c γ 1 1 =
      (zeroFrequencyFirstOrder c γ).map (algebraMap ℝ ℂ) := by
  ext i j
  have hc : ContinuousAt (fun α : ℝ ↦ supplyRadialRemainder c γ α 1 i j) 1 :=
    ((supplySymbol_radialExpansion c γ i j).continuous_remainder (1, 1)
      one_ne_zero).comp (f := fun α : ℝ ↦ (α, (1 : ℂ))) (x := (1 : ℝ))
      (continuousAt_id.prodMk continuousAt_const)
  have hEq : (fun α : ℝ ↦ supplyRadialRemainder c γ α 1 i j) =ᶠ[nhdsWithin 1 {1}ᶜ]
      (fun α : ℝ ↦ supplySymbol c α γ 1 i j / ((1 - α : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    have ha : α ≠ 1 := by simpa using hα
    simpa using supplyRadialRemainder_eq_quotient c γ α 1 ha i j
  have hq := tendsto_supplySymbol_zeroFrequency_quotient c γ hbalance i j
  have hr : Filter.Tendsto (fun α : ℝ ↦ supplyRadialRemainder c γ α 1 i j)
      (nhdsWithin 1 {1}ᶜ) (nhds (supplyRadialRemainder c γ 1 1 i j)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hr (hq.congr' hEq.symm)

/-- The remainder is Hermitian whenever its radial quotient is defined. -/
theorem supplyRadialRemainder_isHermitian {ℓ : ℕ} (c : LagWeights ℓ)
    (γ α : ℝ) (z : ℂ) (hα : α ≠ 1) :
    (supplyRadialRemainder c γ α z).IsHermitian := by
  have heq : supplyRadialRemainder c γ α z =
      (((1 - α : ℝ) : ℂ))⁻¹ • (supplySymbol c α γ z - supplySymbol c 1 γ z) := by
    ext i j
    rw [supplyRadialRemainder_eq_quotient c γ α z hα]
    simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  apply ((supplySymbol_isHermitian c α γ z).sub
    (supplySymbol_isHermitian c 1 γ z)).smul
  simp [isSelfAdjoint_iff]

/-- The actual radial remainder has a uniform positive lower bound in a
joint neighborhood of `(1,1)`. The only exclusion is the quotient boundary
`α=1`; the remainder itself remains continuous there. -/
theorem supplyRadialRemainder_locally_coercive {ℓ : ℕ} (c : LagWeights ℓ)
    {γ : ℝ} (hγ : 0 < γ) (hbalance : BalancedMoments c) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ p : ℝ × ℂ in nhds (1, 1), p.1 ≠ 1 →
      (supplyRadialRemainder c γ p.1 p.2 -
        (η : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosDef := by
  let η := min c.omega (c.omega * γ) / 2
  have hm : 0 < min c.omega (c.omega * γ) :=
    lt_min c.omega_pos (mul_pos c.omega_pos hγ)
  have hη : 0 < η := div_pos hm (by norm_num)
  have hηω : η < c.omega := by
    have hmin := min_le_left c.omega (c.omega * γ)
    dsimp [η]
    linarith
  have hηγ : η < c.omega * γ := by
    have hmin := min_le_right c.omega (c.omega * γ)
    dsimp [η]
    linarith
  let A (p : ℝ × ℂ) := supplyRadialRemainder c γ p.1 p.2 -
    (η : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have hc : ContinuousAt A ((1 : ℝ), (1 : ℂ)) :=
    (supplyRadialRemainder_continuousAt c γ (1, 1) one_ne_zero).sub continuousAt_const
  have hc00 : ContinuousAt (fun p ↦ (A p 0 0).re) ((1 : ℝ), (1 : ℂ)) :=
    Complex.continuous_re.continuousAt.comp
      ((continuousAt_pi.mp (continuousAt_pi.mp hc 0)) 0)
  have hcd : ContinuousAt (fun p ↦ (A p).det.re) ((1 : ℝ), (1 : ℂ)) :=
    Complex.continuous_re.continuousAt.comp
      ((continuous_id.matrix_det).continuousAt.comp hc)
  have h00 : 0 < (A (1, 1) 0 0).re := by
    simpa [A, supplyRadialRemainder_one_one c γ hbalance, zeroFrequencyFirstOrder]
      using sub_pos.mpr hηω
  have hd : 0 < (A (1, 1)).det.re := by
    simpa [A, supplyRadialRemainder_one_one c γ hbalance,
      zeroFrequencyFirstOrder, Matrix.det_fin_two]
      using mul_pos (sub_pos.mpr hηω) (sub_pos.mpr hηγ)
  refine ⟨η, hη, ?_⟩
  filter_upwards [hc00.tendsto.eventually_const_lt h00,
    hcd.tendsto.eventually_const_lt hd] with p hp00 hpd
  intro hp
  apply posDef_of_sylvester ?_ hp00 hpd
  apply (supplyRadialRemainder_isHermitian c γ p.1 p.2 hp).sub
  apply Matrix.isHermitian_one.smul
  simp [isSelfAdjoint_iff]

end ADMM.UnitCircle
