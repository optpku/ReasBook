/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/
module
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Order.Field
public section
noncomputable section
open Filter
open scoped Topology BigOperators
namespace TikhonovExpectedCurve
namespace EnergyBounds

/-- A finite spectral model for the expected solution energy. `coefficient`
is the squared true coefficient and `eigenvalue` the squared singular value. The noise
variance per observed mode is `σ²/n`. `error_lower` allows any nonnegative
unobserved bias or nullspace error in the estimation risk. -/
structure FiniteSpectralModel (S E : ℕ → ℝ → ℝ) (σ M : ℝ) where
  modes : ℕ → ℕ
  eigenvalue : ℕ → ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  eigenvalue_pos : ∀ n i, i < modes n → 0 < eigenvalue n i
  coefficient_nonneg : ∀ n i, i < modes n → 0 ≤ coefficient n i
  source_bound : ∀ n, (∑ i ∈ Finset.range (modes n), coefficient n i) ≤ M
  solution_eq : ∀ n x, 0 < x → S n x =
    ∑ i ∈ Finset.range (modes n),
      ((eigenvalue n i) ^ 2 * coefficient n i + (σ ^ 2 / (n : ℝ)) * eigenvalue n i) /
        (eigenvalue n i + x) ^ 2
  error_lower : ∀ n x, 0 < x →
    (∑ i ∈ Finset.range (modes n),
      (x ^ 2 * coefficient n i + (σ ^ 2 / (n : ℝ)) * eigenvalue n i) /
        (eigenvalue n i + x) ^ 2) ≤ E n x

lemma model_solution_bound {S E : ℕ → ℝ → ℝ} {σ M : ℝ}
    (h : FiniteSpectralModel S E σ M) {n : ℕ} {x : ℝ} (hx : 0 < x) :
    0 ≤ S n x ∧ S n x ≤ M + E n x := by
  have hδ : 0 ≤ σ ^ 2 / (n : ℝ) := by positivity
  rw [h.solution_eq n x hx]
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    have hlam := (h.eigenvalue_pos n i (Finset.mem_range.1 hi)).le
    have ha := h.coefficient_nonneg n i (Finset.mem_range.1 hi)
    positivity
  · calc
      _ ≤ (∑ i ∈ Finset.range (h.modes n), h.coefficient n i) +
          (∑ i ∈ Finset.range (h.modes n),
            (x ^ 2 * h.coefficient n i + (σ ^ 2 / (n : ℝ)) * h.eigenvalue n i) /
              (h.eigenvalue n i + x) ^ 2) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro i hi
        have hlam := (h.eigenvalue_pos n i (Finset.mem_range.1 hi)).le
        have ha := h.coefficient_nonneg n i (Finset.mem_range.1 hi)
        have hden : 0 < (h.eigenvalue n i + x) ^ 2 := by positivity
        apply (div_le_iff₀ hden).2
        field_simp
        simp only [div_eq_mul_inv] at *
        nlinarith [mul_nonneg (mul_nonneg hlam hx.le) ha, mul_nonneg (sq_nonneg x) ha]
      _ ≤ _ := add_le_add (h.source_bound n) (h.error_lower n x hx)

lemma term_hasDerivAt {w lam x : ℝ} (hx : lam + x ≠ 0) :
    HasDerivAt (fun y ↦ w / (lam + y) ^ 2) (-2 * w / (lam + x) ^ 3) x := by
  have ht := (hasDerivAt_const x w).div (((hasDerivAt_id x).const_add lam).pow 2)
    (pow_ne_zero 2 hx)
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, zero_mul, zero_sub] at ht
  change HasDerivAt (fun y : ℝ ↦ w / (lam + y) ^ 2)
    (-(w * (2 * (lam + x))) / ((lam + x) ^ 2) ^ 2) x at ht
  convert! ht using 1
  field_simp [hx]

lemma model_deriv {S E : ℕ → ℝ → ℝ} {σ M : ℝ}
    (h : FiniteSpectralModel S E σ M) {n : ℕ} {x : ℝ} (hx : 0 < x) :
    deriv (S n) x =
      -2 * ∑ i ∈ Finset.range (h.modes n),
        ((h.eigenvalue n i) ^ 2 * h.coefficient n i + (σ ^ 2 / (n : ℝ)) * h.eigenvalue n i) /
          (h.eigenvalue n i + x) ^ 3 := by
  have ht := HasDerivAt.fun_sum (u := Finset.range (h.modes n))
    (fun i hi ↦ term_hasDerivAt (w := (h.eigenvalue n i) ^ 2 * h.coefficient n i +
      (σ ^ 2 / (n : ℝ)) * h.eigenvalue n i) (lam := h.eigenvalue n i) (x := x)
      (by have hlam := h.eigenvalue_pos n i (Finset.mem_range.1 hi); positivity))
  have heq : S n =ᶠ[𝓝 x] fun y ↦ ∑ i ∈ Finset.range (h.modes n),
      ((h.eigenvalue n i) ^ 2 * h.coefficient n i + (σ ^ 2 / (n : ℝ)) * h.eigenvalue n i) /
        (h.eigenvalue n i + y) ^ 2 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact h.solution_eq n y hy
  rw [(ht.congr_of_eventuallyEq heq).deriv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A mode with squared singular value between `α` and `2α` already gives a
lower bound proportional to `(σ²/n)/α²` for the magnitude of the derivative. -/
lemma model_deriv_lower {S E : ℕ → ℝ → ℝ} {σ M : ℝ}
    (h : FiniteSpectralModel S E σ M) {n i : ℕ} {x : ℝ} (hx : 0 < x)
    (hi : i < h.modes n) (hlo : x ≤ h.eigenvalue n i) (hhi : h.eigenvalue n i ≤ 2 * x) :
    (2 / 27 : ℝ) * (σ ^ 2 / (n : ℝ)) / x ^ 2 ≤ -deriv (S n) x := by
  have hδ : 0 ≤ σ ^ 2 / (n : ℝ) := by positivity
  have hlam := h.eigenvalue_pos n i hi
  have ha := h.coefficient_nonneg n i hi
  rw [model_deriv h hx, neg_mul, neg_neg]
  have hterm : (σ ^ 2 / (n : ℝ)) / (27 * x ^ 2) ≤
      ((h.eigenvalue n i) ^ 2 * h.coefficient n i + (σ ^ 2 / (n : ℝ)) * h.eigenvalue n i) /
        (h.eigenvalue n i + x) ^ 3 := by
    calc
      _ = (σ ^ 2 / (n : ℝ)) * x / (3 * x) ^ 3 := by field_simp; ring
      _ ≤ (σ ^ 2 / (n : ℝ)) * h.eigenvalue n i / (h.eigenvalue n i + x) ^ 3 := by
        gcongr
        linarith
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact le_add_of_nonneg_left (by positivity)
  have hsum :
      ((h.eigenvalue n i) ^ 2 * h.coefficient n i + (σ ^ 2 / (n : ℝ)) * h.eigenvalue n i) /
        (h.eigenvalue n i + x) ^ 3 ≤
      ∑ j ∈ Finset.range (h.modes n),
        ((h.eigenvalue n j) ^ 2 * h.coefficient n j + (σ ^ 2 / (n : ℝ)) * h.eigenvalue n j) /
          (h.eigenvalue n j + x) ^ 3 := by
    apply Finset.single_le_sum (f := fun j ↦
      ((h.eigenvalue n j) ^ 2 * h.coefficient n j + (σ ^ 2 / (n : ℝ)) * h.eigenvalue n j) /
        (h.eigenvalue n j + x) ^ 3) (s := Finset.range (h.modes n)) (a := i)
    · intro j hj
      have hlamj := (h.eigenvalue_pos n j (Finset.mem_range.1 hj)).le
      have haj := h.coefficient_nonneg n j (Finset.mem_range.1 hj)
      positivity
    · exact Finset.mem_range.2 hi
  calc
    _ = 2 * ((σ ^ 2 / (n : ℝ)) / (27 * x ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hterm.trans hsum) (by norm_num)

/-- Sufficient spectral and scale conditions for the vanishing profiles.
The residual has a fixed noise floor; the observed spectrum resolves a mode
at the regularization scale, and `n α² → 0` forces the energy derivative to
diverge. These are conditions on the model and parameter scale, not assumptions
on the normalized curvature profiles. -/
structure FlatnessRegime (R S E : ℕ → ℝ → ℝ) (α : ℕ → ℝ) where
  noise : ℝ
  sourceBound : ℝ
  residualFloor : ℝ
  noise_pos : 0 < noise
  residualFloor_pos : 0 < residualFloor
  model : FiniteSpectralModel S E noise sourceBound
  alpha_pos : ∀ n, 0 < α n
  alpha_zero : Tendsto α atTop (𝓝 0)
  residual_lower : ∀ᶠ n in atTop, residualFloor ≤ R n (α n)
  mode : ℕ → ℕ
  mode_mem : ∀ᶠ n in atTop, mode n < model.modes n
  mode_lower : ∀ᶠ n in atTop, α n ≤ model.eigenvalue n (mode n)
  mode_upper : ∀ᶠ n in atTop, model.eigenvalue n (mode n) ≤ 2 * α n
  derivative_scale : Tendsto (fun (n : ℕ) ↦ (n : ℝ) * (α n) ^ 2) atTop (𝓝 0)

lemma derivative_inverse_bound {R S E : ℕ → ℝ → ℝ} {α : ℕ → ℝ}
    (h : FlatnessRegime R S E α) :
    ∀ᶠ n in atTop, |(deriv (S n) (α n))⁻¹| ≤
      (27 / (2 * h.noise ^ 2)) * ((n : ℝ) * (α n) ^ 2) := by
  filter_upwards [h.mode_mem, h.mode_lower, h.mode_upper, eventually_gt_atTop 0] with n hi hlo hhi hn
  have hα := h.alpha_pos n
  have hδ : 0 < h.noise ^ 2 / (n : ℝ) :=
    div_pos (sq_pos_of_pos h.noise_pos) (by exact_mod_cast hn)
  have hbound := model_deriv_lower h.model hα hi hlo hhi
  have hleft : 0 < (2 / 27 : ℝ) * (h.noise ^ 2 / (n : ℝ)) / (α n) ^ 2 := by positivity
  have hd : deriv (S n) (α n) < 0 := by linarith
  rw [abs_inv, abs_of_neg hd, ← one_div]
  calc
    _ ≤ 1 / ((2 / 27 : ℝ) * (h.noise ^ 2 / (n : ℝ)) / (α n) ^ 2) :=
      one_div_le_one_div_of_le hleft hbound
    _ = _ := by field_simp

lemma profiles_tendsto_zero {R S E : ℕ → ℝ → ℝ} {α : ℕ → ℝ}
    (h : FlatnessRegime R S E α)
    (hE : Tendsto (fun n ↦ E n (α n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ α n * S n (α n) / R n (α n)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ (S n (α n)) ^ 2 /
        (R n (α n) * deriv (S n) (α n))) atTop (𝓝 0) := by
  let C : ℝ := |h.sourceBound| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hS : ∀ᶠ n in atTop, 0 ≤ S n (α n) ∧ S n (α n) ≤ C := by
    filter_upwards [hE.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    have hb := model_solution_bound h.model (n := n) (h.alpha_pos n)
    exact ⟨hb.1, hb.2.trans (by dsimp [C]; linarith [le_abs_self h.sourceBound])⟩
  have hR : ∀ᶠ n in atTop, 0 < R n (α n) ∧ (R n (α n))⁻¹ ≤ h.residualFloor⁻¹ := by
    filter_upwards [h.residual_lower] with n hn
    have hpos := lt_of_lt_of_le h.residualFloor_pos hn
    exact ⟨hpos, inv_anti₀ h.residualFloor_pos hn⟩
  constructor
  · have hlim : Tendsto (fun n ↦ α n * (C * h.residualFloor⁻¹)) atTop (𝓝 0) := by
      simpa using h.alpha_zero.mul_const (C * h.residualFloor⁻¹)
    apply squeeze_zero_norm' (a := fun n ↦ α n * (C * h.residualFloor⁻¹)) ?_ hlim
    filter_upwards [hS, hR] with n hsn hrn
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (h.alpha_pos n),
      abs_of_nonneg hsn.1, abs_of_pos hrn.1, div_eq_mul_inv]
    calc
      _ ≤ α n * C * h.residualFloor⁻¹ := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hsn.2 (h.alpha_pos n).le)
          hrn.2 (inv_nonneg.mpr hrn.1.le) (mul_nonneg (h.alpha_pos n).le hC.le)
      _ = _ := by ring
  · have hlim : Tendsto (fun (n : ℕ) ↦ (C ^ 2 * h.residualFloor⁻¹) *
        ((27 / (2 * h.noise ^ 2)) * ((n : ℝ) * (α n) ^ 2))) atTop (𝓝 0) := by
      simpa using (h.derivative_scale.const_mul (27 / (2 * h.noise ^ 2))).const_mul
        (C ^ 2 * h.residualFloor⁻¹)
    apply squeeze_zero_norm' (a := fun (n : ℕ) ↦ (C ^ 2 * h.residualFloor⁻¹) *
      ((27 / (2 * h.noise ^ 2)) * ((n : ℝ) * (α n) ^ 2))) ?_ hlim
    filter_upwards [hS, hR, derivative_inverse_bound h] with n hsn hrn hdn
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_pos hrn.1, div_eq_mul_inv, mul_inv_rev]
    calc
      _ = S n (α n) ^ 2 * (R n (α n))⁻¹ * |(deriv (S n) (α n))⁻¹| := by
        rw [abs_inv]
        ring
      _ ≤ _ := by
        apply mul_le_mul _ hdn (abs_nonneg _) (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr h.residualFloor_pos.le))
        exact mul_le_mul (pow_le_pow_left₀ hsn.1 hsn.2 2) hrn.2
          (inv_nonneg.mpr hrn.1.le) (sq_nonneg C)
end EnergyBounds
end TikhonovExpectedCurve
