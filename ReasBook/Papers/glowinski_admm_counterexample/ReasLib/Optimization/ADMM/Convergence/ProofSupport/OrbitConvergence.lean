/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.OrbitCompactness
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GeneratedHistory

@[expose] public section

open Filter ADMM.FiniteMemory

namespace ADMM.ConvergenceProof

/-- The stationary normal at a feasible reduced state. -/
def stationaryNormal {m : ℕ} (γ : ℝ) (wBar : Fin m → ℝ) (b : Block) : Fin m → ℝ :=
  match b with
  | .F => -γ • wBar
  | .J => γ • wBar

/-- Translating a reduced state translates both generated graph positions. -/
theorem generatedPosition_translate {m : ℕ} (η w : ℕ → Fin m → ℝ)
    (ηBar wBar : Fin m → ℝ) (b : Block) (k : ℕ) :
    generatedPosition (fun j ↦ η j - ηBar) (fun j ↦ w j - wBar) b k =
      generatedPosition η w b k - ηBar := by
  cases b <;> dsimp [generatedPosition] <;> module

/-- Translating a reduced state subtracts its stationary normal. -/
theorem generatedNormal_translate {m : ℕ} (γ : ℝ) (η w : ℕ → Fin m → ℝ)
    (ηBar wBar : Fin m → ℝ) (b : Block) (k : ℕ) :
    generatedNormal γ (fun j ↦ η j - ηBar) (fun j ↦ w j - wBar) b k =
      generatedNormal γ η w b k - stationaryNormal γ wBar b := by
  cases b <;> dsimp [generatedNormal, generatedPosition, stationaryNormal] <;> module

/-- Nonnegative normalized graph pairings follow from monotonicity relative
to the KKT origin. -/
theorem generated_pairing_nonneg {m : ℕ} {γ : ℝ}
    (f : Block → (Fin m → ℝ) → EReal) (η w : ℕ → Fin m → ℝ)
    (hzero : ∀ b, IsSubgradientAt (f b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k)) (k : ℕ) :
    0 ≤ dotProduct (generatedNormal γ η w .F k) (generatedPosition η w .F k) +
      dotProduct (generatedNormal γ η w .J k) (generatedPosition η w .J k) := by
  have hF := subgradient_monotone (hgraph .F k) (hzero .F)
  have hJ := subgradient_monotone (hgraph .J k) (hzero .J)
  simpa only [sub_zero] using add_nonneg hF hJ

/-- A bounded normalized reduced orbit with square-summable residuals
converges to one stationary state. The proof uses a compact cluster point and
an energy with summable errors, avoiding any continuity assumption on the
extended-real objectives. -/
theorem reduced_converges_of_bounded_summable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (f : Block → (Fin m → ℝ) → EReal) (η w : ℕ → Fin m → ℝ)
    (hf : ∀ b, IsClosedProperConvex (f b))
    (hzero : ∀ b, IsSubgradientAt (f b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k))
    (hbound : ∃ C : ℝ, ∀ k, coordinateSquare (η k) + coordinateSquare (w k) ≤ C)
    (hres : Summable (fun k ↦ coordinateSquare (w (k + 1) - w k))) :
    ∃ ηBar wBar, Tendsto η atTop (nhds ηBar) ∧ Tendsto w atTop (nhds wBar) ∧
      (∀ b, IsSubgradientAt (f b) (stationaryNormal γ wBar b) ηBar) := by
  have hpair := generated_pairing_nonneg f η w hzero hgraph
  have hinc := reduced_increment_summable hγ η w hpair hres
  have hr : Tendsto (fun k ↦ w (k + 1) - w k) atTop (nhds 0) :=
    tendsto_zero_of_coordinateSquare hres.tendsto_atTop_zero
  have hd : Tendsto (fun k ↦ η (k + 1) - η k) atTop (nhds 0) :=
    tendsto_zero_of_coordinateSquare hinc.tendsto_atTop_zero
  obtain ⟨ηBar, wBar, σ, hσ, hησ, hwσ⟩ := state_exists_subsequence η w hbound
  have hrσ := hr.comp hσ.tendsto_atTop
  have hdσ := hd.comp hσ.tendsto_atTop
  have hηnext : Tendsto (fun k ↦ η (σ k + 1)) atTop (nhds ηBar) := by
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using hdσ.add hησ
  have hpos : ∀ b, Tendsto (fun k ↦ generatedPosition η w b (σ k)) atTop (nhds ηBar) := by
    intro b
    cases b with
    | F => simpa only [generatedPosition, Function.comp_def, add_zero] using hηnext.add hrσ
    | J => exact hηnext
  have hnormal : ∀ b, Tendsto (fun k ↦ generatedNormal γ η w b (σ k)) atTop
      (nhds (stationaryNormal γ wBar b)) := by
    intro b
    cases b with
    | F =>
      have h := (hησ.sub (hwσ.const_smul γ)).sub (hpos .F)
      have heq : ηBar - γ • wBar - ηBar = -γ • wBar := by module
      simpa only [Function.comp_def, generatedNormal, stationaryNormal, heq] using h
    | J =>
      simpa only [Function.comp_def, generatedNormal, stationaryNormal, add_zero] using
        (hwσ.const_smul γ).add hrσ
  have hlimit : ∀ b, IsSubgradientAt (f b) (stationaryNormal γ wBar b) ηBar := by
    intro b
    exact subgradient_of_tendsto (hf b) (fun k ↦ hgraph b (σ k)) (hpos b) (hnormal b)
  let η' : ℕ → Fin m → ℝ := fun k ↦ η k - ηBar
  let w' : ℕ → Fin m → ℝ := fun k ↦ w k - wBar
  let L : ℕ → ℝ := fun k ↦ γ ^ 2 * coordinateSquare (w' k) +
    γ * coordinateSquare (η' k)
  have hL : ∀ k, 0 ≤ L k := fun k ↦
    add_nonneg (mul_nonneg (sq_nonneg _) (coordinateSquare_nonneg _))
      (mul_nonneg hγ.le (coordinateSquare_nonneg _))
  have hpair' : ∀ k, 0 ≤
      dotProduct (generatedNormal γ η' w' .F k) (generatedPosition η' w' .F k) +
        dotProduct (generatedNormal γ η' w' .J k) (generatedPosition η' w' .J k) := by
    intro k
    have hF := subgradient_monotone (hgraph .F k) (hlimit .F)
    have hJ := subgradient_monotone (hgraph .J k) (hlimit .J)
    simpa only [η', w', generatedPosition_translate, generatedNormal_translate] using
      add_nonneg hF hJ
  have hstep : ∀ k, L (k + 1) ≤ L k + γ ^ 2 * coordinateSquare (w (k + 1) - w k) := by
    intro k
    have he := reduced_energy_descent hγ.le (η' k) (η' (k + 1)) (w' k) (w' (k + 1))
    have hp := mul_nonneg (show 0 ≤ 2 * γ by positivity) (hpair' k)
    have hdpos := mul_nonneg (show 0 ≤ γ / 2 by positivity)
      (coordinateSquare_nonneg (η' (k + 1) - η' k))
    have hrEq : w' (k + 1) - w' k = w (k + 1) - w k := by dsimp [w']; module
    rw [hrEq] at he
    change 0 ≤ 2 * γ * _ at hp
    dsimp only [generatedNormal, generatedPosition] at hp
    rw [hrEq] at hp
    dsimp only [L]
    linarith
  have hLσ : Tendsto (L ∘ σ) atTop (nhds 0) := by
    have hηc : Tendsto (fun _ : ℕ ↦ ηBar) atTop (nhds ηBar) := tendsto_const_nhds
    have hwc : Tendsto (fun _ : ℕ ↦ wBar) atTop (nhds wBar) := tendsto_const_nhds
    have h := ((coordinateSquare_tendsto (hwσ.sub hwc)).const_mul (γ ^ 2)).add
      ((coordinateSquare_tendsto (hησ.sub hηc)).const_mul γ)
    simpa only [L, η', w', Function.comp_def, sub_self, coordinateSquare,
      dotProduct_zero, mul_zero, add_zero] using h
  have hLzero := energy_tendsto_zero_of_subsequence hL
    (fun k ↦ mul_nonneg (sq_nonneg _) (coordinateSquare_nonneg _))
    (hres.mul_left (γ ^ 2)) hstep hσ hLσ
  have hηzero : Tendsto η' atTop (nhds 0) := by
    apply tendsto_zero_of_coordinateSquare
    apply storage_coercive_tendsto_zero hγ (fun k ↦ coordinateSquare_nonneg _) _ hLzero
    intro k
    dsimp only [L]
    linarith [mul_nonneg (sq_nonneg γ) (coordinateSquare_nonneg (w' k))]
  have hwzero : Tendsto w' atTop (nhds 0) := by
    apply tendsto_zero_of_coordinateSquare
    apply storage_coercive_tendsto_zero (sq_pos_of_pos hγ)
      (fun k ↦ coordinateSquare_nonneg _) _ hLzero
    intro k
    dsimp only [L]
    linarith [mul_nonneg hγ.le (coordinateSquare_nonneg (η' k))]
  refine ⟨ηBar, wBar, ?_, ?_, hlimit⟩
  · simpa only [η', sub_add_cancel, zero_add] using hηzero.add_const ηBar
  · simpa only [w', sub_add_cancel, zero_add] using hwzero.add_const wBar

end ADMM.ConvergenceProof
