/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Exercise_6_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

private lemma weighted_sum_eq
    (z : ℕ → ℝ) :
    ∀ n,
      ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * z i) =
        (n : ℝ) * ∑ i ∈ Finset.range n, z i -
          ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, weighted_sum_eq z n,
        Nat.cast_add, Nat.cast_one]
      ring

private lemma weighted_sum_div_eq_sub_cesaro
    (z : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * z i) =
      ∑ i ∈ Finset.range n, z i -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j := by
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  rw [weighted_sum_eq]
  calc
    (n : ℝ)⁻¹ *
        ((n : ℝ) * ∑ i ∈ Finset.range n, z i -
          ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j) =
      (n : ℝ)⁻¹ * ((n : ℝ) * ∑ i ∈ Finset.range n, z i) -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j := by
          ring
    _ = ∑ i ∈ Finset.range n, z i -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j := by
          rw [← mul_assoc, inv_mul_cancel₀ hnR, one_mul]

omit [MeasurableSpace Ω] in
private lemma weighted_sum_div_eq_partialSum_sub_cesaro
    (Z : ℕ → Ω → ℝ) (ω : Ω) {n : ℕ} (hn : 0 < n) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * Z i ω) =
      partialSum Z n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω := by
  let z : ℕ → ℝ := fun i ↦ Z i ω
  calc
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * Z i ω)
        = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * z i) := by
            simp [z]
    _ = ∑ i ∈ Finset.range n, z i -
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j := by
            exact weighted_sum_div_eq_sub_cesaro z hn
    _ = partialSum Z n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω := by
            simp [partialSum, z]

-- Proof sketch: form the martingale with increments `(X (n + 1) - P[X (n + 1)]) / (n + 1)` and use
-- the summability of `Var[X (n + 1); P] / (n + 1)^2` to obtain an `L²`-bounded martingale, hence
-- almost sure convergence by the martingale convergence theorem; then apply Kronecker's lemma to
-- recover the almost sure convergence of the centered empirical averages.
/-- Exercise 11.2.2: the textbook sequence `X₁, X₂, …`, represented by `X 1, X 2, …`, satisfies
the strong law of large numbers whenever its terms are independent, square integrable, and the
series `∑ Var[Xₙ] / n²` is summable. -/
theorem satisfies_strong_law_of_large_numbers_of_iIndep_memLp_two_summable_variance
    (X : ℕ → Ω → ℝ) (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_memLp : ∀ n, MemLp (X (n + 1)) 2 P)
    (hX_var_summable : Summable (fun n : ℕ ↦ Var[X (n + 1); P] / (n + 1 : ℝ) ^ 2)) :
    satisfies_strong_law_of_large_numbers P (fun n ↦ X (n + 1)) := by
  let Z : ℕ → Ω → ℝ :=
    fun n ω ↦ ((n + 1 : ℝ)⁻¹) * (X (n + 1) ω - P[X (n + 1)])
  have hZ_indep : iIndepFun Z P := by
    let g : ℕ → ℝ → ℝ :=
      fun n x ↦ ((n + 1 : ℝ)⁻¹) * (x - P[X (n + 1)])
    simpa [Z, g, Function.comp] using hX_indep.comp g (fun _ ↦ by fun_prop)
  have hZ_memLp : ∀ n, MemLp (Z n) 2 P := by
    intro n
    simpa [Z] using ((hX_memLp n).sub (memLp_const _)).const_mul ((n + 1 : ℝ)⁻¹)
  have hZ_centered : ∀ n, P[Z n] = 0 := by
    intro n
    change P[fun ω ↦ ((n + 1 : ℝ)⁻¹) * (X (n + 1) ω - P[X (n + 1)])] = 0
    rw [integral_const_mul,
      integral_sub ((hX_memLp n).integrable (by norm_num)) (integrable_const _), integral_const]
    simp
  have hZ_var : ∀ n, Var[Z n; P] = Var[X (n + 1); P] / (n + 1 : ℝ) ^ 2 := by
    intro n
    change Var[fun ω ↦ ((n + 1 : ℝ)⁻¹) * (X (n + 1) ω - P[X (n + 1)]); P] = _
    rw [variance_const_mul]
    simp [variance_sub_const (hX_memLp n).aestronglyMeasurable, div_eq_mul_inv, pow_two,
      mul_assoc, mul_comm]
  have hZ_var_summable : Summable (fun n : ℕ ↦ Var[Z n; P]) := by
    simpa [hZ_var] using hX_var_summable
  obtain ⟨Y, _, hY_tendsto⟩ :=
    exists_memLp_two_ae_tendsto_partial_sums_of_iIndepFun_summable_variance
      P Z hZ_indep hZ_memLp hZ_centered hZ_var_summable
  refine ⟨fun n ↦ (hX_memLp n).integrable (by norm_num), ?_⟩
  filter_upwards [hY_tendsto] with ω hω
  have hCesaro :
      Tendsto
        (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω)
        atTop (𝓝 (Y ω)) := by
    simpa [smul_eq_mul] using hω.cesaro
  have hBridge :
      Tendsto
        (fun n : ℕ ↦
          partialSum Z n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω)
        atTop (𝓝 0) := by
    simpa using hω.sub hCesaro
  have hEq :
      (fun n ↦ centered_average P (fun k ↦ X (k + 1)) n ω) =ᶠ[atTop]
        (fun n : ℕ ↦
          partialSum Z n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : 0 < n := Nat.succ_le_iff.mp hn
    have hcentered :
        ∑ i ∈ Finset.range n, (X (i + 1) ω - P[X (i + 1)]) =
          ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * Z i ω) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hiR : (i + 1 : ℝ) ≠ 0 := by positivity
      simp [Z, hiR]
    calc
      centered_average P (fun k ↦ X (k + 1)) n ω
          = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * Z i ω) := by
            rw [centered_average, centered_partial_sum, div_eq_mul_inv, mul_comm, hcentered]
      _ = partialSum Z n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω := by
            exact weighted_sum_div_eq_partialSum_sub_cesaro Z ω hn'
  exact Tendsto.congr' hEq.symm hBridge
