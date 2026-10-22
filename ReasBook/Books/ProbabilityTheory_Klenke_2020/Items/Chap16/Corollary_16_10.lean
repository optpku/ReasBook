/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Corollary_16_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Exercise_16_1_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- Helper for Corollary 16.10: reindexing a `ℕ+`-sequence along `Nat.succPNat` preserves its
`atTop` limit. -/
private theorem tendsto_pnat_atTop_iff_succPNat {β : Type*} [TopologicalSpace β]
    {f : ℕ+ → β} {l : Filter β} :
    Tendsto f atTop l ↔ Tendsto (fun n : ℕ ↦ f (Nat.succPNat n)) atTop l := by
  constructor
  · intro hf
    -- Proof comment: compose the `ℕ+`-indexed limit with the order isomorphism `ℕ ≃o ℕ+`.
    simpa [OrderIso.pnatIsoNat_symm_apply] using hf.comp OrderIso.pnatIsoNat.symm.tendsto_atTop
  · intro hf
    -- Proof comment: compose back with `PNat.natPred` to recover the original `ℕ+` indexing.
    have hcomp := hf.comp OrderIso.pnatIsoNat.tendsto_atTop
    convert hcomp using 1
    ext n
    simp [OrderIso.pnatIsoNat_apply]

/-- Helper for Corollary 16.10: an infinitely divisible law on `ℝ` is the time-`1` law of a
convolution semigroup. -/
private theorem existsConvolutionSemigroup_unitTime
    {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    ∃ ν : NNReal → ProbabilityMeasure ℝ,
      IsConvolutionSemigroup ν ∧ ν 1 = μ := by
  classical
  let ρ : ℕ+ → ProbabilityMeasure ℝ := fun n ↦ Classical.choose (hμ.exists_root n)
  have hρpow : ∀ n : ℕ+, ρ n ^ (n : ℕ) = μ := by
    intro n
    exact Classical.choose_spec (hμ.exists_root n)
  have hρcfp :
      ∀ n : ℕ+, IsCFP (fun t : ℝ ↦ charFun (ρ n : Measure ℝ) t) := by
    intro n
    simpa using ProbabilityMeasure.isCFP_charFun (ρ n)
  have hρpowChar :
      ∀ n : ℕ+, ∀ t : ℝ,
        (charFun (ρ n : Measure ℝ) t) ^ (n : ℕ) = charFun (μ : Measure ℝ) t := by
    intro n t
    calc
      (charFun (ρ n : Measure ℝ) t) ^ (n : ℕ) =
          charFun ((ρ n ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t := by
            symm
            simpa using
              congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow (ρ n) (n : ℕ))
      _ = charFun (μ : Measure ℝ) t := by
            simp [hρpow n]
  have hcharCont : Continuous (charFun (μ : Measure ℝ)) := MeasureTheory.continuous_charFun
  have hchar0 : charFun (μ : Measure ℝ) 0 = 1 := by
    simp [MeasureTheory.charFun_zero]
  have hcharNe : ∀ t : ℝ, charFun (μ : Measure ℝ) t ≠ 0 :=
    charFun_ne_zero_of_isInfinitelyDivisible hμ
  obtain ⟨Ψ, hΨ, _⟩ :=
    existsUnique_continuousExpLift
      (φ := charFun (μ : Measure ℝ)) hcharCont hcharNe hchar0
  rcases hΨ with ⟨hΨ0, hΨexp⟩
  let φs : ℕ → ℝ → ℂ := fun n t ↦
    if hn : n = 0 then 1 else charFun (ρ (Nat.toPNat' n) : Measure ℝ) t
  have hφs : ∀ n : ℕ, IsCFP (φs n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      refine ⟨diracProba (0 : ℝ), ?_⟩
      funext t
      simp [φs, MeasureTheory.diracProba, MeasureTheory.charFun_dirac]
    · simpa [φs, hn] using ProbabilityMeasure.isCFP_charFun (ρ (Nat.toPNat' n))
  have hrootFormula :
      ∀ n : ℕ+, ∀ t : ℝ,
        charFun (ρ n : Measure ℝ) t = Complex.exp (Ψ t / (n : ℂ)) := by
    intro n t
    simpa using
      exactRoot_eq_expDivLift
        (φ := charFun (μ : Measure ℝ))
        (φs := fun n t ↦ charFun (ρ n : Measure ℝ) t)
        hρcfp hρpowChar (Ψ := Ψ) hΨ0 hΨexp n t
  have hlin :
      ∀ t : ℝ,
        Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (𝓝 (Ψ t)) := by
    intro t
    let z : ℂ := Ψ t
    have hlinRaw :
        Tendsto
          (fun n : ℕ ↦ (n : ℂ) * (Complex.exp (z / (n : ℂ)) - 1))
          atTop
          (𝓝 z) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      let N : ℕ := max 1 (Nat.ceil ‖z‖)
      have hbound :
          ∀ᶠ n : ℕ in atTop,
            ‖(n : ℂ) * (Complex.exp (z / (n : ℂ)) - 1) - z‖ ≤ ‖z‖ ^ 2 / n := by
        filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0] with n hnN hn0
        have hn0C : (n : ℂ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt hn0
        have hn0R : (n : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt hn0
        have hnpos : (0 : ℝ) < n := by
          exact_mod_cast hn0
        have hzle : ‖z‖ ≤ n := by
          have hceil : ‖z‖ ≤ Nat.ceil ‖z‖ := Nat.le_ceil _
          have hceilN : (Nat.ceil ‖z‖ : ℝ) ≤ N := by
            exact_mod_cast le_max_right 1 (Nat.ceil ‖z‖)
          have hNn : (N : ℝ) ≤ n := by
            exact_mod_cast hnN
          exact le_trans hceil (le_trans hceilN hNn)
        have hnormDiv : ‖z / (n : ℂ)‖ = ‖z‖ / n := by
          rw [norm_div, Complex.norm_natCast]
        have hsmall : ‖z / (n : ℂ)‖ ≤ 1 := by
          rw [hnormDiv]
          have hdiv :
              ‖z‖ / (n : ℝ) ≤ (n : ℝ) / n := by
            exact div_le_div_of_nonneg_right hzle hnpos.le
          simpa [hn0R] using hdiv
        have hrew :
            (n : ℂ) * (Complex.exp (z / (n : ℂ)) - 1) - z =
              (n : ℂ) * (Complex.exp (z / (n : ℂ)) - 1 - z / (n : ℂ)) := by
          field_simp [hn0C]
        rw [hrew, norm_mul]
        calc
          ‖(n : ℂ)‖ * ‖Complex.exp (z / (n : ℂ)) - 1 - z / (n : ℂ)‖
              ≤ ‖(n : ℂ)‖ * ‖z / (n : ℂ)‖ ^ 2 := by
                exact mul_le_mul_of_nonneg_left
                  (Complex.norm_exp_sub_one_sub_id_le hsmall) (norm_nonneg _)
          _ = (n : ℝ) * (‖z‖ / n) ^ 2 := by rw [Complex.norm_natCast, hnormDiv]
          _ = ‖z‖ ^ 2 / n := by
                field_simp [hn0R]
      have hzero :
          Tendsto (fun n : ℕ ↦ ‖z‖ ^ 2 / n) atTop (𝓝 0) := by
        have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
          simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
        simpa [div_eq_mul_inv] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ‖z‖ ^ 2) atTop (𝓝 (‖z‖ ^ 2))).mul hinv
      exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hbound hzero
    have hEventually :
        (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) =ᶠ[atTop]
          fun n : ℕ ↦ (n : ℂ) * (Complex.exp (z / (n : ℂ)) - 1) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hchar :
          charFun (ρ (Nat.toPNat' n) : Measure ℝ) t = Complex.exp (z / (n : ℂ)) := by
        simpa [z, PNat.toPNat'_coe hn] using hrootFormula (Nat.toPNat' n) t
      simp [φs, hn.ne', hchar]
    exact hlinRaw.congr' hEventually.symm
  have hΨ0cont : ContinuousAt (fun t : ℝ ↦ Ψ t) 0 := by
    simpa using Ψ.continuous.continuousAt
  let ν : NNReal → ProbabilityMeasure ℝ := fun t ↦
    if ht : t = 0 then
      diracProba 0
    else
      Classical.choose <|
        levyKhinchin_scaledExponent_isCharacteristicFunction
          (φs := φs) (ψ := fun x : ℝ ↦ Ψ x) hφs hlin hΨ0cont
          (show 0 < (t : ℝ) by
            exact_mod_cast (pos_iff_ne_zero.mpr ht))
  have hνchar :
      ∀ t : NNReal,
        charFun (ν t : Measure ℝ) = fun x : ℝ ↦ Complex.exp (((t : ℝ) : ℂ) * Ψ x) := by
    intro t
    by_cases ht : t = 0
    · subst ht
      funext x
      simp [ν, MeasureTheory.diracProba, MeasureTheory.charFun_dirac]
    · -- Proof comment: for positive times, `ν t` is chosen as a witness for the scaled exponent.
      exact by
        simpa [ν, ht] using
          Classical.choose_spec <|
            levyKhinchin_scaledExponent_isCharacteristicFunction
              (φs := φs) (ψ := fun x : ℝ ↦ Ψ x) hφs hlin hΨ0cont
              (show 0 < (t : ℝ) by
                exact_mod_cast (pos_iff_ne_zero.mpr ht))
  have hsemigroup : IsConvolutionSemigroup ν := by
    refine { convolution_eq := ?_ }
    intro s t
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_charFun
    funext x
    calc
      charFun (ν (s + t) : Measure ℝ) x
          = Complex.exp ((((s + t : NNReal) : ℝ) : ℂ) * Ψ x) := by
              simpa using congrArg (fun f : ℝ → ℂ ↦ f x) (hνchar (s + t))
      _ = Complex.exp ((((s : ℝ) : ℂ) * Ψ x) + (((t : ℝ) : ℂ) * Ψ x)) := by
            congr 1
            norm_num
            ring
      _ = Complex.exp (((s : ℝ) : ℂ) * Ψ x) * Complex.exp (((t : ℝ) : ℂ) * Ψ x) := by
            rw [Complex.exp_add]
      _ = charFun (ν s : Measure ℝ) x * charFun (ν t : Measure ℝ) x := by
            rw [show Complex.exp (((s : ℝ) : ℂ) * Ψ x) = charFun (ν s : Measure ℝ) x by
              simpa using (congrArg (fun f : ℝ → ℂ ↦ f x) (hνchar s)).symm]
            rw [show Complex.exp (((t : ℝ) : ℂ) * Ψ x) = charFun (ν t : Measure ℝ) x by
              simpa using (congrArg (fun f : ℝ → ℂ ↦ f x) (hνchar t)).symm]
      _ = charFun ((ν s * ν t : ProbabilityMeasure ℝ) : Measure ℝ) x := by
            symm
            simpa using MeasureTheory.charFun_conv
              (μ := (ν s : Measure ℝ)) (ν := (ν t : Measure ℝ)) x
  have hνone : ν 1 = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_charFun
    funext x
    calc
      charFun (ν 1 : Measure ℝ) x = Complex.exp (Ψ x) := by
        simpa using congrArg (fun f : ℝ → ℂ ↦ f x) (hνchar 1)
      _ = charFun (μ : Measure ℝ) x := by
        exact hΨexp x
  exact ⟨ν, hsemigroup, hνone⟩

/-- Corollary 16.10, partial semigroup realization: every infinitely divisible probability law on
`ℝ` is the time-`1` marginal of a convolution semigroup. -/
theorem exists_convolutionSemigroup_unitTime
    {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    ∃ ν : NNReal → ProbabilityMeasure ℝ,
      IsConvolutionSemigroup ν ∧ ν 1 = μ :=
  existsConvolutionSemigroup_unitTime hμ

end MeasureTheory.ProbabilityMeasure
