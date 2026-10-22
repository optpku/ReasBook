/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_8.HarmonicDiagonal

public section

open scoped ENNReal Topology

noncomputable section

namespace RealL2

/-- The diagonal operator from Example 2.8 has trivial kernel. -/
theorem harmonicDiagonal_ker_eq_bot : harmonicDiagonal.ker = ⊥ := by
  -- Compare coordinates and cancel the nonzero harmonic weight at each index.
  rw [LinearMap.ker_eq_bot]
  intro f g hfg
  ext n
  have hcoord : harmonicDiagonal f n = harmonicDiagonal g n := by
    exact congrArg (fun u : lp (fun _ : ℕ ↦ ℝ) 2 => u n) hfg
  have hcoord' : (1 / ((n : ℝ) + 1)) * f n = (1 / ((n : ℝ) + 1)) * g n := by
    simpa [harmonicDiagonal_apply] using hcoord
  have hweight : (1 / ((n : ℝ) + 1)) ≠ 0 := by positivity
  exact mul_left_cancel₀ hweight hcoord'

/-- Each basis vector in `deltaSequence` has norm `1`. -/
theorem deltaSequence_norm (n : ℕ) : ‖deltaSequence n‖ = 1 := by
  -- Rewrite `deltaSequence n` as a single supported vector and use the `lp.single` norm formula.
  have hp : 0 < (2 : ℝ≥0∞) := by norm_num
  have hdelta : deltaSequence n = lp.single 2 n (1 : ℝ) := by
    ext j
    by_cases hj : j = n
    · subst hj
      simp [deltaSequence_apply]
    · simp [deltaSequence_apply, lp.single_apply, hj]
  rw [hdelta]
  rw [lp.norm_single (p := (2 : ℝ≥0∞)) (E := fun _ : ℕ ↦ ℝ) hp n (1 : ℝ)]
  norm_num

/-- The image of `deltaSequence n` under the harmonic diagonal has norm
`1 / ((n : ℝ) + 1)`. -/
theorem norm_harmonicDiagonal_deltaSequence (n : ℕ) :
    ‖harmonicDiagonal (deltaSequence n)‖ = 1 / ((n : ℝ) + 1) := by
  -- Reduce to the norm of a single supported vector with coefficient `1 / (n + 1)`.
  rw [harmonicDiagonal_deltaSequence]
  have hp : 0 < (2 : ℝ≥0∞) := by norm_num
  have hnonneg : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  rw [lp.norm_single (p := (2 : ℝ≥0∞)) (E := fun _ : ℕ ↦ ℝ) hp n
    (1 / ((n : ℝ) + 1) : ℝ)]
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]

/-- A preliminary fact for Example 2.8: if `harmonicDiagonal f = harmonicDiagonal g`, then
`f = g`, so a solution to `D f = g` is unique whenever it exists. -/
theorem harmonicDiagonal_injective : Function.Injective harmonicDiagonal := by
  -- The previously computed trivial kernel is exactly the injectivity criterion.
  exact (LinearMap.ker_eq_bot).1 harmonicDiagonal_ker_eq_bot

/-- Helper for Example 2.8: any preimage of `harmonicDatum` under `harmonicDiagonal` has every
coordinate equal to `1`. -/
lemma preimageOfHarmonicDatum_apply_eq_one {f : lp (fun _ : ℕ ↦ ℝ) 2}
    (hf : harmonicDiagonal f = harmonicDatum) (n : ℕ) : f n = 1 := by
  -- Compare the `n`th coordinates and cancel the nonzero diagonal factor.
  have hcoord : harmonicDiagonal f n = harmonicDatum n := by
    exact congrArg (fun u : lp (fun _ : ℕ ↦ ℝ) 2 => u n) hf
  have hcoord' : (1 / ((n : ℝ) + 1)) * f n = (1 / ((n : ℝ) + 1)) * 1 := by
    simpa [harmonicDiagonal_apply, harmonicDatum_apply]
      using hcoord
  have hweight : (1 / ((n : ℝ) + 1)) ≠ 0 := by positivity
  exact mul_left_cancel₀ hweight hcoord'

/-- Example 2.8 (2). The datum `harmonicDatum = (1, 1 / 2, 1 / 3, ...)` belongs to real `ℓ²` but
does not lie in the range of `harmonicDiagonal`. -/
theorem harmonicDatum_not_mem_range : harmonicDatum ∉ Set.range harmonicDiagonal := by
  intro hRange
  rcases hRange with ⟨f, hf⟩
  -- Any hypothetical preimage would have to be the constant-one sequence.
  have hcoord : ∀ n : ℕ, f n = 1 := fun n ↦ preimageOfHarmonicDatum_apply_eq_one hf n
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hsummableNorm : Summable (fun n : ℕ ↦ ‖f n‖ ^ (2 : ℝ)) :=
    (lp.hasSum_norm hp f).summable
  have hsummableOne : Summable (fun _ : ℕ ↦ (1 : ℝ)) := by
    -- Rewrite the summable norm series to the constant series `1`.
    simpa [hcoord] using hsummableNorm
  have hfinite : (Set.univ : Set ℕ).Finite :=
    Set.Finite.of_summable_const (by norm_num : (0 : ℝ) < 1) hsummableOne
  exact Set.infinite_univ.not_finite hfinite

/-- A stability calculation for Example 2.8: the images of the basis-vector sequence under
`harmonicDiagonal` converge to `0` in real `ℓ²`. -/
theorem harmonicDiagonal_tendsto_zero_on_deltaSequence :
    Filter.Tendsto (fun n ↦ harmonicDiagonal (deltaSequence n)) Filter.atTop
      (𝓝 (0 : lp (fun _ : ℕ ↦ ℝ) 2)) := by
  -- Transport the `ℓ²` convergence question to the scalar norm sequence.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [norm_harmonicDiagonal_deltaSequence] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0))

/-- A complementary fact for Example 2.8: the basis-vector sequence `deltaSequence` does not
converge to `0` in real `ℓ²`. -/
theorem deltaSequence_not_tendsto_zero :
    ¬ Filter.Tendsto deltaSequence Filter.atTop (𝓝 (0 : lp (fun _ : ℕ ↦ ℝ) 2)) := by
  intro hdelta
  -- A norm-convergent-to-zero sequence would force the constant sequence `1` to converge to `0`.
  have hnorm : Filter.Tendsto (fun n ↦ ‖deltaSequence n‖) Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_zero_iff_norm_tendsto_zero.1 hdelta
  have honeToZero : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [deltaSequence_norm] using hnorm
  have hone : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hcontra : (1 : ℝ) = 0 := tendsto_nhds_unique hone honeToZero
  norm_num at hcontra

end RealL2
