/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap04.section02

section Chap04
section Section04

/-- The Cauchy-product coefficient sequence attached to `c, d : ℕ → ℝ`. -/
def cauchyProductCoeff (c d : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), c m * d (n - m)

/-- Helper for Theorem 4.4.1: at any point of `(a-r, a+r)`, the corresponding
power-series terms are absolutely summable. -/
lemma helperForTheorem_4_4_1_absSummable_seriesTerm_at_point
    {a r x : ℝ} (c : ℕ → ℝ)
    (hc :
      ∀ y (hy : y ∈ Set.Ioo (a - r) (a + r)),
        Summable (fun n : ℕ => c n * (y - a) ^ n))
    (hx : x ∈ Set.Ioo (a - r) (a + r)) :
    Summable (fun n : ℕ => |c n * (x - a) ^ n|) := by
  have hs : Summable (fun n : ℕ => c n * (x - a) ^ n) := hc x hx
  have hsNorm : Summable (fun n : ℕ => ‖c n * (x - a) ^ n‖) := by
    simpa using hs.norm
  simpa [Real.norm_eq_abs] using hsNorm

/-- Helper for Theorem 4.4.1: rewrite the inner Cauchy-product finite sum into
`cauchyProductCoeff c d n * t^n`. -/
lemma helperForTheorem_4_4_1_cauchyInnerSum_rewrite
    (c d : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        (c k * t ^ k) * (d (n - k) * t ^ (n - k))) =
      cauchyProductCoeff c d n * t ^ n := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        (c k * t ^ k) * (d (n - k) * t ^ (n - k)))
        = ∑ k ∈ Finset.range (n + 1), (c k * d (n - k)) * t ^ n := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk_le : k ≤ n := by
              exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            calc
              (c k * t ^ k) * (d (n - k) * t ^ (n - k))
                  = (c k * d (n - k)) * (t ^ k * t ^ (n - k)) := by ring
              _ = (c k * d (n - k)) * t ^ (k + (n - k)) := by
                    simp [pow_add]
              _ = (c k * d (n - k)) * t ^ n := by
                    simp [Nat.add_sub_of_le hk_le]
    _ = (∑ k ∈ Finset.range (n + 1), c k * d (n - k)) * t ^ n := by
          rw [Finset.sum_mul]
    _ = cauchyProductCoeff c d n * t ^ n := by
          simp [cauchyProductCoeff]

/-- Helper for Theorem 4.4.1: at each point in `(a-r,a+r)`, the pointwise
product equals the Cauchy-product power-series sum. -/
lemma helperForTheorem_4_4_1_pointwise_product_eq_tsum
    {a r x : ℝ} (hr : 0 < r)
    (f g : Set.Ioo (a - r) (a + r) → ℝ)
    (c d : ℕ → ℝ)
    (hf_series :
      ∀ y (hy : y ∈ Set.Ioo (a - r) (a + r)),
        Summable (fun n : ℕ => c n * (y - a) ^ n) ∧
          f ⟨y, hy⟩ = ∑' n : ℕ, c n * (y - a) ^ n)
    (hg_series :
      ∀ y (hy : y ∈ Set.Ioo (a - r) (a + r)),
        Summable (fun n : ℕ => d n * (y - a) ^ n) ∧
          g ⟨y, hy⟩ = ∑' n : ℕ, d n * (y - a) ^ n)
    (hx : x ∈ Set.Ioo (a - r) (a + r)) :
    f ⟨x, hx⟩ * g ⟨x, hx⟩ =
      ∑' n : ℕ, cauchyProductCoeff c d n * (x - a) ^ n := by
  have hfc : Summable (fun n : ℕ => c n * (x - a) ^ n) := (hf_series x hx).1
  have hgc : Summable (fun n : ℕ => d n * (x - a) ^ n) := (hg_series x hx).1
  have hfcAbs : Summable (fun n : ℕ => |c n * (x - a) ^ n|) :=
    helperForTheorem_4_4_1_absSummable_seriesTerm_at_point c
      (fun y hy => (hf_series y hy).1) hx
  have hgcAbs : Summable (fun n : ℕ => |d n * (x - a) ^ n|) :=
    helperForTheorem_4_4_1_absSummable_seriesTerm_at_point d
      (fun y hy => (hg_series y hy).1) hx
  have hfcNorm : Summable (fun n : ℕ => ‖c n * (x - a) ^ n‖) := by
    simpa [Real.norm_eq_abs] using hfcAbs
  have hgcNorm : Summable (fun n : ℕ => ‖d n * (x - a) ^ n‖) := by
    simpa [Real.norm_eq_abs] using hgcAbs
  have hCauchy :
      (∑' n : ℕ, c n * (x - a) ^ n) * (∑' n : ℕ, d n * (x - a) ^ n) =
        ∑' n : ℕ,
          ∑ k ∈ Finset.range (n + 1),
            (c k * (x - a) ^ k) * (d (n - k) * (x - a) ^ (n - k)) :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfcNorm hgcNorm
  calc
    f ⟨x, hx⟩ * g ⟨x, hx⟩ =
        (∑' n : ℕ, c n * (x - a) ^ n) * (∑' n : ℕ, d n * (x - a) ^ n) := by
          rw [(hf_series x hx).2, (hg_series x hx).2]
    _ =
        ∑' n : ℕ,
          ∑ k ∈ Finset.range (n + 1),
            (c k * (x - a) ^ k) * (d (n - k) * (x - a) ^ (n - k)) :=
          hCauchy
    _ = ∑' n : ℕ, cauchyProductCoeff c d n * (x - a) ^ n := by
          refine congrArg tsum ?_
          funext n
          exact helperForTheorem_4_4_1_cauchyInnerSum_rewrite c d (x - a) n

/-- Theorem 4.4.1: if `f, g : (a-r, a+r) → ℝ` are analytic and have power-series
expansions around `a` with coefficients `c_n` and `d_n` on `(a-r, a+r)`, then
`fg` is analytic on `(a-r, a+r)`, and for every `x` in that interval,
`f(x)g(x) = ∑' n, e_n (x-a)^n` where `e_n = ∑_{m=0}^n c_m d_{n-m}`. -/
theorem realAnalyticOnInterval_mul_eq_cauchyProduct
    {a r : ℝ} (hr : 0 < r)
    (f g : Set.Ioo (a - r) (a + r) → ℝ)
    (hf_analytic : IsRealAnalyticOn (Set.Ioo (a - r) (a + r)) f)
    (hg_analytic : IsRealAnalyticOn (Set.Ioo (a - r) (a + r)) g)
    (c d : ℕ → ℝ)
    (hf_series :
      ∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
        Summable (fun n : ℕ => c n * (x - a) ^ n) ∧
          f ⟨x, hx⟩ = ∑' n : ℕ, c n * (x - a) ^ n)
    (hg_series :
      ∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
        Summable (fun n : ℕ => d n * (x - a) ^ n) ∧
          g ⟨x, hx⟩ = ∑' n : ℕ, d n * (x - a) ^ n) :
    IsRealAnalyticOn (Set.Ioo (a - r) (a + r)) (fun x => f x * g x) ∧
      ∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
        f ⟨x, hx⟩ * g ⟨x, hx⟩ =
          ∑' n : ℕ, cauchyProductCoeff c d n * (x - a) ^ n := by
  constructor
  · let E : Set ℝ := Set.Ioo (a - r) (a + r)
    have hEOpen : IsOpen E := hf_analytic.1
    have hfAnalyticExt : AnalyticOn ℝ (SubtypeExtension E f) E :=
      helperForTheorem_4_2_1_analyticOnSubtypeExtension_of_IsRealAnalyticOn f hf_analytic
    have hgAnalyticExt : AnalyticOn ℝ (SubtypeExtension E g) E :=
      helperForTheorem_4_2_1_analyticOnSubtypeExtension_of_IsRealAnalyticOn g hg_analytic
    have hMulAnalyticExt :
        AnalyticOn ℝ
          (fun x : ℝ => SubtypeExtension E f x * SubtypeExtension E g x)
          E :=
      hfAnalyticExt.mul hgAnalyticExt
    have hEqOn :
        Set.EqOn
          (SubtypeExtension E (fun y : E => f y * g y))
          (fun x : ℝ => SubtypeExtension E f x * SubtypeExtension E g x)
          E := by
      intro x hxE
      simp [SubtypeExtension, hxE]
    have hProdAnalyticExt :
        AnalyticOn ℝ (SubtypeExtension E (fun y : E => f y * g y)) E :=
      hMulAnalyticExt.congr hEqOn
    simpa [E] using
      (helperForTheorem_4_2_1_isRealAnalyticOn_of_analyticOnSubtypeExtension
        (g := fun y : E => f y * g y) hEOpen hProdAnalyticExt)
  · intro x hx
    exact
      helperForTheorem_4_4_1_pointwise_product_eq_tsum hr f g c d hf_series hg_series hx

end Section04
end Chap04
