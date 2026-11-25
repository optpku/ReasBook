/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.ExpectedError
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public section
noncomputable section
open Filter
open scoped Topology BigOperators
namespace TikhonovEstimation
namespace SeriesRisk

@[expose] def risk (a d : ℕ → ℝ) (δ x : ℝ) : ℝ :=
  ∑' k, (x ^ 2 * a k + δ * d k) / (d k + x) ^ 2

@[expose] def biasMoment (a d : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k, a k * d k / (d k + x) ^ 3

@[expose] def varianceMoment (d : ℕ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ∑' k, d k / (d k + x) ^ j

lemma term_hasDerivAt {a d δ x : ℝ} (h : d + x ≠ 0) :
    HasDerivAt (fun y ↦ (y ^ 2 * a + δ * d) / (d + y) ^ 2)
      (2 * (x * a * d - δ * d) / (d + x) ^ 3) x := by
  have ht := (((hasDerivAt_id x).pow 2 |>.mul_const a).add_const (δ * d)).div
    (((hasDerivAt_id x).const_add d).pow 2) (pow_ne_zero 2 h)
  simp only [Pi.pow_apply, id_eq, Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one] at ht
  convert! ht using 1
  field_simp
  ring

lemma summable_terms {a d : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hd : ∀ k, 0 ≤ d k)
    (hsa : Summable a) (hsd : Summable d) {δ x : ℝ} (hx : 0 < x) :
    Summable (fun k ↦ (x ^ 2 * a k + δ * d k) / (d k + x) ^ 2) := by
  apply Summable.of_norm_bounded (hsa.add (hsd.mul_left (|δ| / x ^ 2)))
  intro k
  have hak := ha k
  have hdk := hd k
  have hden : 0 < d k + x := by positivity
  simp only [norm_div, Real.norm_eq_abs, abs_of_pos (pow_pos hden 2)]
  calc
    |x ^ 2 * a k + δ * d k| / (d k + x) ^ 2
        ≤ (x ^ 2 * a k + |δ| * d k) / (d k + x) ^ 2 := by
          gcongr
          calc
            _ ≤ |x ^ 2 * a k| + |δ * d k| := abs_add_le _ _
            _ = _ := by rw [abs_of_nonneg (mul_nonneg (sq_nonneg x) (ha k)),
              abs_mul, abs_of_nonneg (hd k)]
    _ ≤ (x ^ 2 * a k + |δ| * d k) / x ^ 2 := by gcongr; linarith [hd k]
    _ = a k + |δ| / x ^ 2 * d k := by field_simp

lemma hasDerivAt_risk {a d : ℕ → ℝ} {c : ℝ}
    (ha : ∀ k, 0 ≤ a k) (hd : ∀ k, 0 ≤ d k) (hdc : ∀ k, d k ≤ c)
    (hsa : Summable a) (hsd : Summable d) {δ x : ℝ} (hx : 0 < x) :
    HasDerivAt (risk a d δ)
      (∑' k, 2 * (x * a k * d k - δ * d k) / (d k + x) ^ 3) x := by
  have hc : 0 ≤ c := (hd 0).trans (hdc 0)
  let m : ℝ := x / 2
  have hm : 0 < m := by dsimp [m]; positivity
  let u : ℕ → ℝ := fun k ↦
    (4 * x * c / m ^ 3) * a k + (2 * |δ| / m ^ 3) * d k
  have hu : Summable u := (hsa.mul_left _).add (hsd.mul_left _)
  apply hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (x / 2) (2 * x)).isPreconnected
    (g' := fun k y ↦ 2 * (y * a k * d k - δ * d k) / (d k + y) ^ 3)
    (y₀ := x)
  · intro k y hy
    apply term_hasDerivAt
    have : 0 < d k + y := by linarith [hd k, hy.1]
    exact this.ne'
  · intro k y hy
    have hak := ha k
    have hdk := hd k
    have hdkc := hdc k
    have hy0 : 0 < y := hm.trans hy.1
    have hden : 0 < d k + y := by positivity
    simp only [norm_div, Real.norm_eq_abs, abs_of_pos (pow_pos hden 3)]
    calc
      |2 * (y * a k * d k - δ * d k)| / (d k + y) ^ 3
          ≤ (2 * (y * a k * d k + |δ| * d k)) / (d k + y) ^ 3 := by
            gcongr
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            gcongr
            simpa [abs_mul, abs_of_nonneg hy0.le, abs_of_nonneg (ha k),
              abs_of_nonneg (hd k)] using abs_sub (y * a k * d k) (δ * d k)
      _ ≤ (2 * ((2 * x) * a k * c + |δ| * d k)) / m ^ 3 := by
            gcongr <;> dsimp [m] at * <;> linarith [hy.1, hy.2, hd k]
      _ = u k := by dsimp [u]; ring
  · constructor <;> linarith
  · exact summable_terms ha hd hsa hsd hx
  · constructor <;> linarith

lemma summable_biasMoment {a d : ℕ → ℝ} {c x : ℝ}
    (ha : ∀ k, 0 ≤ a k) (hd : ∀ k, 0 ≤ d k) (hdc : ∀ k, d k ≤ c)
    (hsa : Summable a) (hx : 0 < x) :
    Summable (fun k ↦ a k * d k / (d k + x) ^ 3) := by
  apply Summable.of_nonneg_of_le (fun k ↦ div_nonneg (mul_nonneg (ha k) (hd k)) (pow_nonneg (by linarith [hd k]) 3))
    (fun k ↦ ?_) (hsa.mul_left (c / x ^ 3))
  have hc : 0 ≤ c := (hd 0).trans (hdc 0)
  have hak := ha k
  have hdk := hd k
  have hdkc := hdc k
  calc
    _ ≤ a k * c / x ^ 3 := by gcongr; linarith [hd k]
    _ = c / x ^ 3 * a k := by ring

lemma summable_varianceMoment {d : ℕ → ℝ} {x : ℝ}
    (hd : ∀ k, 0 ≤ d k) (hsd : Summable d) (hx : 0 < x) (j : ℕ) :
    Summable (fun k ↦ d k / (d k + x) ^ j) := by
  apply Summable.of_nonneg_of_le (fun k ↦ div_nonneg (hd k) (pow_nonneg (by linarith [hd k]) j))
    (fun k ↦ ?_) (hsd.div_const (x ^ j))
  exact div_le_div_of_nonneg_left (hd k) (pow_pos hx j)
    (pow_le_pow_left₀ hx.le (by linarith [hd k]) j)

lemma stationary {a d : ℕ → ℝ} {c δ x : ℝ}
    (ha : ∀ k, 0 ≤ a k) (hd : ∀ k, 0 ≤ d k) (hdc : ∀ k, d k ≤ c)
    (hsa : Summable a) (hsd : Summable d) (hx : 0 < x)
    (hmin : IsLocalMin (risk a d δ) x) :
    x * biasMoment a d x = δ * varianceMoment d 3 x := by
  have hz := hmin.hasDerivAt_eq_zero (hasDerivAt_risk ha hd hdc hsa hsd hx)
  have hB := summable_biasMoment ha hd hdc hsa hx
  have hV := summable_varianceMoment hd hsd hx 3
  have heq : (∑' k, 2 * (x * a k * d k - δ * d k) / (d k + x) ^ 3) =
      2 * (x * biasMoment a d x - δ * varianceMoment d 3 x) := by
    simp_rw [show ∀ k, 2 * (x * a k * d k - δ * d k) / (d k + x) ^ 3 =
      2 * (x * (a k * d k / (d k + x) ^ 3) - δ * (d k / (d k + x) ^ 3)) by
        intro k; ring]
    rw [tsum_mul_left, (hB.mul_left x).tsum_sub (hV.mul_left δ), tsum_mul_left, tsum_mul_left]
    rfl
  rw [heq] at hz
  linarith
/-- Separate the convergent bias and variance series. -/
lemma risk_eq_split {a d : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hd : ∀ k, 0 ≤ d k)
    (hsa : Summable a) (hsd : Summable d) {δ x : ℝ} (hx : 0 < x) :
    risk a d δ x = x ^ 2 * (∑' k, a k / (d k + x) ^ 2) +
      δ * varianceMoment d 2 x := by
  have hba : Summable (fun k ↦ a k / (d k + x) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun k ↦ div_nonneg (ha k) (sq_nonneg _))
      (fun k ↦ ?_) (hsa.div_const (x ^ 2))
    exact div_le_div_of_nonneg_left (ha k) (sq_pos_of_pos hx)
      (pow_le_pow_left₀ hx.le (by linarith [hd k]) 2)
  unfold risk
  simp_rw [add_div, mul_div_assoc]
  rw [(hba.mul_left (x ^ 2)).tsum_add ((summable_varianceMoment hd hsd hx 2).mul_left δ),
    tsum_mul_left, tsum_mul_left]
  rfl

lemma stationary_tendsto_zero {a d : ℕ → ℝ} {c : ℝ}
    (ha : ∀ k, 0 ≤ a k) (hd : ∀ k, 0 ≤ d k) (hdc : ∀ k, d k ≤ c)
    (ha0 : 0 < a 0) (hd0 : 0 < d 0) (hsa : Summable a) (hsd : Summable d)
    {α δ : ℕ → ℝ} (hα : ∀ᶠ n in atTop, 0 < α n)
    (hδ : ∀ᶠ n in atTop, 0 ≤ δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hstat : ∀ᶠ n in atTop, α n * biasMoment a d (α n) =
      δ n * varianceMoment d 3 (α n)) :
    Tendsto α atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro ε hε
    filter_upwards [hα] with n hn
    exact hε.trans hn
  · intro ε hε
    let L := ε * a 0 * d 0 * (ε / (d 0 + ε)) ^ 3
    have hL : 0 < L := by dsimp [L]; positivity
    have hsmall : ∀ᶠ n in atTop, δ n * (∑' k, d k) < L := by
      have ht : Tendsto (fun n ↦ δ n * (∑' k, d k)) atTop (𝓝 0) := by
        simpa using hδ0.mul_const (∑' k, d k)
      exact ht.eventually (gt_mem_nhds hL)
    filter_upwards [hα, hδ, hstat, hsmall] with n hn hδn hsn hsmalln
    by_contra hnlt
    have hεn : ε ≤ α n := le_of_not_gt hnlt
    have hB : a 0 * d 0 / (d 0 + α n) ^ 3 ≤ biasMoment a d (α n) := by
      exact (summable_biasMoment ha hd hdc hsa hn).le_tsum 0
        (fun k _ ↦ div_nonneg (mul_nonneg (ha k) (hd k))
          (pow_nonneg (by linarith [hd k]) 3))
    have hV : varianceMoment d 3 (α n) ≤ (∑' k, d k) / (α n) ^ 3 := by
      rw [varianceMoment, ← tsum_div_const]
      exact (summable_varianceMoment hd hsd hn 3).tsum_le_tsum
        (fun k ↦ div_le_div_of_nonneg_left (hd k) (pow_pos hn 3)
          (pow_le_pow_left₀ hn.le (by linarith [hd k]) 3)) (hsd.div_const _)
    have hbound : α n * (a 0 * d 0 / (d 0 + α n) ^ 3) ≤
        δ n * ((∑' k, d k) / (α n) ^ 3) := by
      calc
        _ ≤ α n * biasMoment a d (α n) := mul_le_mul_of_nonneg_left hB hn.le
        _ = δ n * varianceMoment d 3 (α n) := hsn
        _ ≤ _ := mul_le_mul_of_nonneg_left hV hδn
    have hr : ε / (d 0 + ε) ≤ α n / (d 0 + α n) := by
      apply (div_le_div_iff₀ (by positivity : 0 < d 0 + ε)
        (by positivity : 0 < d 0 + α n)).2
      nlinarith
    have hLbound : L ≤ α n * a 0 * d 0 * (α n / (d 0 + α n)) ^ 3 := by
      dsimp [L]
      gcongr
    have hbound' : α n * a 0 * d 0 * (α n / (d 0 + α n)) ^ 3 ≤
        δ n * (∑' k, d k) := by
      have hm := mul_le_mul_of_nonneg_right hbound (pow_nonneg hn.le 3)
      convert! hm using 1 <;> field_simp
    exact (not_lt_of_ge (hLbound.trans hbound')) hsmalln

end SeriesRisk
end TikhonovEstimation
