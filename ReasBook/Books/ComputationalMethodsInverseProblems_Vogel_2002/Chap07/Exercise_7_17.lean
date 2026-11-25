/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.ExpectedError
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Exercise 7.17: the saturated bias limit in equation (7.77)

When `2 * p - q < -1`, the second term `T₂` in equation (7.74) satisfies
`T₂ = α² * (‖f_true‖²_{K* K} + o(1))`. The finite sum is indexed by
`k = 0, ..., N - 1`, with book index `i = k + 1`.

We prove dominated convergence for the normalized finite sum as `α → 0`
through eventually nonnegative parameters and `N → ∞`. The singular-value
and Fourier-coefficient decay assumptions identify its limiting power series
with `adjointCompSourceNormSq`; the saturation inequality proves that this
source series is summable. The final theorem gives an explicit vanishing
remainder, expressing precisely the second equality in equation (7.77).

This bias limit does not require the extra coupling condition between `N`
and `α` used for the variance asymptotics elsewhere on the source page.
-/

public section

noncomputable section

open Filter
open scoped Topology BigOperators

private lemma tendsto_damped_partial_sum
    {ι : Type*} {l : Filter ι} {a d : ℕ → ℝ} (hs : Summable a)
    (ha : ∀ k, 0 ≤ a k) (hd : ∀ k, 0 ≤ d k)
    {α : ι → ℝ} {N : ι → ℕ} (hα : Tendsto α l (nhds 0))
    (hα_nonneg : ∀ᶠ x in l, 0 ≤ α x) (hN : Tendsto N l atTop) :
    Tendsto (fun x ↦ ∑ k ∈ Finset.range (N x), a k / (1 + α x * d k) ^ 2)
      l (nhds (∑' k, a k)) := by
  let f : ι → ℕ → ℝ := fun x k ↦ if k < N x then a k / (1 + α x * d k) ^ 2 else 0
  have hlim : ∀ k, Tendsto (fun x ↦ f x k) l (nhds (a k)) := by
    intro k
    have ht : Tendsto (fun x ↦ a k / (1 + α x * d k) ^ 2) l (nhds (a k)) := by
      have hdlim : Tendsto (fun x ↦ (1 + α x * d k) ^ 2) l (nhds (1 : ℝ)) := by
        simpa using (((hα.mul_const (d k)).const_add 1).pow 2)
      simpa only [Pi.div_apply, div_one] using! tendsto_const_nhds.div hdlim one_ne_zero
    apply ht.congr'
    filter_upwards [hN.eventually (eventually_gt_atTop k)] with x hx
    simp [f, hx]
  have hbound : ∀ᶠ x in l, ∀ k, ‖f x k‖ ≤ a k := by
    filter_upwards [hα_nonneg] with x hx k
    by_cases hk : k < N x
    · have hden : 1 ≤ 1 + α x * d k := by nlinarith [hd k]
      have hden_sq : 1 ≤ (1 + α x * d k) ^ 2 := by nlinarith
      have hnonneg : 0 ≤ a k / (1 + α x * d k) ^ 2 :=
        div_nonneg (ha k) (sq_nonneg _)
      simp only [f, if_pos hk, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact div_le_self (ha k) hden_sq
    · simpa only [f, if_neg hk, norm_zero] using ha k
  have ht := tendsto_tsum_of_dominated_convergence hs hlim hbound
  have hfinite (x : ι) : ∑' k, f x k =
      ∑ k ∈ Finset.range (N x), a k / (1 + α x * d k) ^ 2 := by
    rw [tsum_eq_sum (s := Finset.range (N x)) (fun k hk ↦ by
      have hk' : ¬ k < N x := by simpa only [Finset.mem_range] using hk
      simp [f, hk'])]
    apply Finset.sum_congr rfl
    intro k hk
    simp [f, Finset.mem_range.1 hk]
  simpa only [hfinite] using ht

private lemma summable_shifted_rpow {s : ℝ} (hs : s < -1) :
    Summable (fun k : ℕ ↦ ((k : ℝ) + 1) ^ s) := by
  have h := (Real.summable_nat_rpow.2 hs).comp_injective Nat.succ_injective
  simpa only [Function.comp_def, Nat.cast_succ] using h

private lemma scalar_normalized_bias_tendsto
    {ι : Type*} {l : Filter ι} {b c p q : ℝ} (hc : 0 < c)
    (hs : 2 * p - q < -1) {α : ι → ℝ} {N : ι → ℕ}
    (hα : Tendsto α l (nhds 0)) (hα_nonneg : ∀ᶠ x in l, 0 ≤ α x)
    (hN : Tendsto N l atTop) :
    Tendsto (fun x ↦ (b / c ^ 2) * ∑ k ∈ Finset.range (N x),
      ((k : ℝ) + 1) ^ (2 * p - q) / (1 + (α x / c) * ((k : ℝ) + 1) ^ p) ^ 2)
      l (nhds ((b / c ^ 2) * ∑' k : ℕ, ((k : ℝ) + 1) ^ (2 * p - q))) := by
  have h := tendsto_damped_partial_sum (summable_shifted_rpow hs)
    (fun k ↦ Real.rpow_nonneg (by positivity) _) (d := fun k ↦ ((k : ℝ) + 1) ^ p / c)
    (fun k ↦ div_nonneg (Real.rpow_nonneg (by positivity) _) hc.le)
    hα hα_nonneg hN
  have ht := h.const_mul (b / c ^ 2)
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using ht

namespace TikhonovEstimation

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : H →L[ℝ] F}

/-- The two algebraic decay laws identify the `K* K` source-series term
with `(b / c²) * i ^ (2p - q)`. -/
lemma adjointCompSourceSeries_eq_of_algebraicDecay
    (S : ContinuousLinearMap.SingularSystem K) (h_length : S.length = ⊤) (fTrue : H)
    {b c p q : ℝ}
    (h_singular : S.HasAlgebraicSingularValueSquareDecay h_length c p)
    (h_fourier : S.HasAlgebraicFourierCoefficientSquareDecay h_length fTrue b q) (i : ℕ+) :
    adjointCompSourceSeries S h_length fTrue i = (b / c ^ 2) * (i : ℝ) ^ (2 * p - q) := by
  have hi : 0 < (i : ℝ) := by exact_mod_cast i.2
  have hfour : S.singularValueSequence h_length i ^ 4 =
      (c * (i : ℝ) ^ (-p)) ^ (2 : ℕ) := by
    calc
      _ = (S.singularValueSequence h_length i ^ 2) ^ (2 : ℕ) := by ring
      _ = _ := by rw [h_singular i]
  rw [adjointCompSourceSeries_apply, h_fourier i, hfour, mul_pow,
    Real.rpow_neg hi.le p, inv_pow, div_mul_eq_div_div, div_inv_eq_mul]
  calc
    _ = (b / c ^ 2) * (((i : ℝ) ^ (-q) * (i : ℝ) ^ p) * (i : ℝ) ^ p) := by ring
    _ = _ := by
      rw [← Real.rpow_add hi, ← Real.rpow_add hi]
      congr 1
      congr 1
      ring

/-- The source norm in equation (7.77) is the corresponding power-series sum.
Its summability in the saturated regime is proved below. -/
lemma adjointCompSourceNormSq_eq_of_algebraicDecay
    (S : ContinuousLinearMap.SingularSystem K) (h_length : S.length = ⊤) (fTrue : H)
    {b c p q : ℝ}
    (h_singular : S.HasAlgebraicSingularValueSquareDecay h_length c p)
    (h_fourier : S.HasAlgebraicFourierCoefficientSquareDecay h_length fTrue b q) :
    adjointCompSourceNormSq S h_length fTrue =
      (b / c ^ 2) * ∑' k : ℕ, ((k : ℝ) + 1) ^ (2 * p - q) := by
  have hterm :=
    adjointCompSourceSeries_eq_of_algebraicDecay S h_length fTrue h_singular h_fourier
  rw [adjointCompSourceNormSq_def]
  rw [show adjointCompSourceSeries S h_length fTrue =
    (fun i : ℕ+ ↦ (b / c ^ 2) * (i : ℝ) ^ (2 * p - q)) from funext hterm]
  rw [tsum_mul_left]
  congr 1
  simpa using (Equiv.pnatEquivNat.tsum_eq
    (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ)) ^ (2 * p - q)))

/-- The strict saturation inequality makes the defining source-norm series
summable, so the source constant is an actual convergent sum. -/
lemma adjointCompSourceSeries_summable_of_saturation
    (S : ContinuousLinearMap.SingularSystem K) (h_length : S.length = ⊤) (fTrue : H)
    {b c p q : ℝ}
    (h_singular : S.HasAlgebraicSingularValueSquareDecay h_length c p)
    (h_fourier : S.HasAlgebraicFourierCoefficientSquareDecay h_length fTrue b q)
    (hs : 2 * p - q < -1) :
    Summable (adjointCompSourceSeries S h_length fTrue) := by
  have hsum : Summable (fun i : ℕ+ ↦ (i : ℝ) ^ (2 * p - q)) := by
    simpa only [Function.comp_def] using
      (Real.summable_nat_rpow.2 hs).comp_injective PNat.coe_injective
  exact (hsum.mul_left (b / c ^ 2)).congr
    (fun i ↦
      (adjointCompSourceSeries_eq_of_algebraicDecay S h_length fTrue h_singular h_fourier i).symm)

/-- In the saturated regime, the coefficient of `α²` in the bias term `T₂`
converges to the squared `K* K` source norm. Both the parameter and the
truncation may vary along any common filter. -/
theorem normalizedBias_tendsto_of_saturation
    (S : ContinuousLinearMap.SingularSystem K) (h_length : S.length = ⊤) (fTrue : H)
    {b c p q : ℝ} (hc : 0 < c)
    (h_singular : S.HasAlgebraicSingularValueSquareDecay h_length c p)
    (h_fourier : S.HasAlgebraicFourierCoefficientSquareDecay h_length fTrue b q)
    (hs : 2 * p - q < -1) {ι : Type*} {l : Filter ι}
    {α : ι → ℝ} {N : ι → ℕ} (hα : Tendsto α l (nhds 0))
    (hα_nonneg : ∀ᶠ x in l, 0 ≤ α x) (hN : Tendsto N l atTop) :
    Tendsto (fun x ↦ (b / c ^ 2) * ∑ k ∈ Finset.range (N x),
      ((k : ℝ) + 1) ^ (2 * p - q) /
        (1 + (α x / c) * ((k : ℝ) + 1) ^ p) ^ 2)
      l (nhds (adjointCompSourceNormSq S h_length fTrue)) := by
  rw [adjointCompSourceNormSq_eq_of_algebraicDecay S h_length fTrue h_singular h_fourier]
  exact scalar_normalized_bias_tendsto hc hs hα hα_nonneg hN

/-- Exercise 7.17, the second equality in equation (7.77):
`T₂ = α² * (‖f_true‖²_{K* K} + o(1))` when `2p - q < -1`.
The `o(1)` term is represented by a function `r` tending to zero; the displayed
identity holds at every index, including indices where `α = 0`. -/
theorem saturatedBias_eq_sourceNormSq_add_vanishing
    (S : ContinuousLinearMap.SingularSystem K) (h_length : S.length = ⊤) (fTrue : H)
    {b c p q : ℝ} (hc : 0 < c)
    (h_singular : S.HasAlgebraicSingularValueSquareDecay h_length c p)
    (h_fourier : S.HasAlgebraicFourierCoefficientSquareDecay h_length fTrue b q)
    (hs : 2 * p - q < -1) {ι : Type*} {l : Filter ι}
    {α : ι → ℝ} {N : ι → ℕ} (hα : Tendsto α l (nhds 0))
    (hα_nonneg : ∀ᶠ x in l, 0 ≤ α x) (hN : Tendsto N l atTop) :
    ∃ r : ι → ℝ, Tendsto r l (nhds 0) ∧ ∀ x,
      (α x) ^ 2 * (b / c ^ 2) * ∑ k ∈ Finset.range (N x),
        ((k : ℝ) + 1) ^ (2 * p - q) /
          (1 + (α x / c) * ((k : ℝ) + 1) ^ p) ^ 2 =
      (α x) ^ 2 * (adjointCompSourceNormSq S h_length fTrue + r x) := by
  let r : ι → ℝ := fun x ↦ (b / c ^ 2) * ∑ k ∈ Finset.range (N x),
    ((k : ℝ) + 1) ^ (2 * p - q) /
      (1 + (α x / c) * ((k : ℝ) + 1) ^ p) ^ 2 -
        adjointCompSourceNormSq S h_length fTrue
  refine ⟨r, ?_, ?_⟩
  · simpa only [sub_self] using
      (normalizedBias_tendsto_of_saturation S h_length fTrue hc h_singular h_fourier
        hs hα hα_nonneg hN).sub_const (adjointCompSourceNormSq S h_length fTrue)
  · intro x
    dsimp [r]
    ring

end TikhonovEstimation
