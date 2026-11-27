/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.MomentLimits
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7
public section
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace TikhonovEstimation
namespace PowerRisk

@[expose] def noiseLevel (σ : ℝ) (n : ℕ) : ℝ := σ ^ 2 / (n : ℝ)

/-- Exact sequence-model risk, with the observational noise normalized by `1/n`.
Only positive candidate parameters and sufficiently large sample sizes are needed. -/
@[expose] def HasPowerRiskModel (objective : ℕ → ℝ → ℝ) (floor : ℕ → ℝ)
    (b c p q σ : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ x, 0 < x → objective n x = floor n +
    SeriesRisk.risk (coeff b q) (eigenvalue c p) (noiseLevel σ n) x

lemma noiseLevel_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ noiseLevel σ n := by
  dsimp [noiseLevel]
  positivity

lemma noiseLevel_eventuallyPos {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ n in atTop, 0 < noiseLevel σ n := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact div_pos (sq_pos_of_pos hσ) (by exact_mod_cast hn)

lemma noiseLevel_tendsto (σ : ℝ) : Tendsto (noiseLevel σ) atTop (𝓝 0) := by
  have ht := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (σ ^ 2)
  change Tendsto (fun n : ℕ ↦ σ ^ 2 / (n : ℝ)) atTop (𝓝 0)
  simpa [Function.comp_def, div_eq_mul_inv] using! ht

lemma stationary_of_optimality {objective : ℕ → ℝ → ℝ} {floor α : ℕ → ℝ}
    {b c p q σ : ℝ} (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q)
    (hmodel : HasPowerRiskModel objective floor b c p q σ)
    (hmin : ParameterChoice.IsOptimalParameterFamily objective admissibleParameters α)
    (hpos : ∀ᶠ n in atTop, 0 < α n) :
    ∀ᶠ n in atTop, α n * biasFactor b c p q 3 (α n) =
      noiseLevel σ n * SeriesRisk.varianceMoment (eigenvalue c p) 3 (α n) := by
  filter_upwards [hmodel, hpos] with n hmn hn
  have ha : ∀ k, 0 ≤ coeff b q k := fun k ↦ by dsimp [coeff]; positivity
  have hd : ∀ k, 0 ≤ eigenvalue c p k := fun k ↦ by dsimp [eigenvalue]; positivity
  have hlocal : IsLocalMin
      (SeriesRisk.risk (coeff b q) (eigenvalue c p) (noiseLevel σ n)) (α n) := by
    change ∀ᶠ x in 𝓝 (α n), _ ≤ _
    filter_upwards [Ioi_mem_nhds hn] with x hx
    have hx0 : 0 < x := hx
    have hm := hmin n ((mem_admissibleParameters n x).2 hx0.le)
    change objective n (α n) ≤ objective n x at hm
    rw [hmn x hx, hmn (α n) hn] at hm
    linarith
  simpa only [biasMoment_eq hc, biasFactor] using
    (SeriesRisk.stationary ha hd (eigenvalue_le hc (by linarith))
      (coeff_summable hq) (eigenvalue_summable hp) hn hlocal)


lemma optimality_tendsto_zero {objective : ℕ → ℝ → ℝ} {floor α : ℕ → ℝ}
    {b c p q σ : ℝ} (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q)
    (hmodel : HasPowerRiskModel objective floor b c p q σ)
    (hmin : ParameterChoice.IsOptimalParameterFamily objective admissibleParameters α)
    (hpos : ∀ᶠ n in atTop, 0 < α n) : Tendsto α atTop (𝓝 0) := by
  have hstat := stationary_of_optimality hb hc hp hq hmodel hmin hpos
  apply SeriesRisk.stationary_tendsto_zero
    (a := coeff b q) (d := eigenvalue c p) (c := c)
    (fun k ↦ by dsimp [coeff]; positivity)
    (fun k ↦ by dsimp [eigenvalue]; positivity)
    (eigenvalue_le hc (by linarith)) (by simpa [coeff] using hb)
    (by simpa [eigenvalue] using hc) (coeff_summable hq) (eigenvalue_summable hp)
    hpos (Eventually.of_forall (noiseLevel_nonneg σ)) (noiseLevel_tendsto σ)
  simpa only [biasMoment_eq hc, biasFactor] using hstat
end PowerRisk
end TikhonovEstimation
