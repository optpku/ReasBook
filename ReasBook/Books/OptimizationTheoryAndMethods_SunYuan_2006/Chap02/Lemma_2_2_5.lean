/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Order.Filter.Extr

open Filter

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced the local-extremum derivative-zero API;
-- this item keeps the book's exact lower-bound statement with the canonical `IsMinOn` owner.

/-- Chapter02 Lemma 2.2.5. If `φ : ℝ → ℝ` is twice continuously differentiable on
`Set.Icc 0 b`, `deriv φ 0 < 0`, `αStar ∈ Set.Ioo 0 b` is a minimizer of `φ` on
`Set.Icc 0 b`, and `iteratedDeriv 2 φ α ≤ M` for every `α ∈ Set.Icc 0 b` with
`0 < M`, then `-deriv φ 0 / M ≤ αStar`. -/
theorem lineSearch_minimizer_ge_neg_deriv_div_secondDerivBound
    {φ : ℝ → ℝ} {b M αStar : ℝ}
    (hC2 : ContDiffOn ℝ 2 φ (Set.Icc (0 : ℝ) b))
    (h_deriv0 : deriv φ 0 < 0)
    (hM : 0 < M)
    (h_secondDeriv :
      ∀ α ∈ Set.Icc (0 : ℝ) b, iteratedDeriv 2 φ α ≤ M)
    (hαStar : αStar ∈ Set.Ioo (0 : ℝ) b)
    (h_min : IsMinOn φ (Set.Icc (0 : ℝ) b) αStar) :
    -deriv φ 0 / M ≤ αStar := by
  have hα0 : 0 < αStar := hαStar.1
  have hαb : αStar < b := hαStar.2
  let s : Set ℝ := Set.Icc (0 : ℝ) αStar
  let g : ℝ → ℝ := derivWithin φ s
  have hs : UniqueDiffOn ℝ s := by
    simpa [s] using uniqueDiffOn_Icc hα0
  have hC2' : ContDiffOn ℝ 2 φ s := by
    simpa [s] using hC2.mono (Set.Icc_subset_Icc_right hαb.le)
  have hg_diff' : DifferentiableOn ℝ (iteratedDerivWithin 1 φ s) s :=
    hC2'.differentiableOn_iteratedDerivWithin (by norm_num) hs
  have hg_diff : DifferentiableOn ℝ g s := by
    simpa [g, iteratedDerivWithin_one] using hg_diff'
  have hg_cont' : ContinuousOn (iteratedDerivWithin 1 φ s) s :=
    hC2'.continuousOn_iteratedDerivWithin (by norm_num) hs
  have hg_cont : ContinuousOn g s := by
    simpa [g, iteratedDerivWithin_one] using hg_cont'
  have h0mem : (0 : ℝ) ∈ s := by simp [s, hα0.le]
  have hαmem : αStar ∈ s := by simp [s, hα0.le]
  have hDiff0 : DifferentiableAt ℝ φ 0 :=
    differentiableAt_of_deriv_ne_zero (by linarith)
  have hDerivWithin0 : g 0 = deriv φ 0 := by
    simpa [g] using hDiff0.derivWithin (hs 0 h0mem)
  have hLocalMin : IsLocalMin φ αStar :=
    h_min.isLocalMin (Icc_mem_nhds hα0 hαb)
  have hDiffAlpha : DifferentiableAt ℝ φ αStar := by
    simpa using (hC2.contDiffAt (Icc_mem_nhds hα0 hαb)).differentiableAt (by norm_num)
  have hDerivWithinAlpha : g αStar = 0 := by
    calc
      g αStar = derivWithin φ s αStar := rfl
      _ = deriv φ αStar := hDiffAlpha.derivWithin (hs αStar hαmem)
      _ = 0 := hLocalMin.deriv_eq_zero
  have hs_right : s ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    refine mem_of_superset (Ioc_mem_nhdsGT hα0) ?_
    intro x hx
    exact ⟨hx.1.le, hx.2⟩
  have hs_left : s ∈ nhdsWithin αStar (Set.Iio αStar) := by
    refine mem_of_superset (Ico_mem_nhdsLT hα0) ?_
    intro x hx
    exact ⟨hx.1, hx.2.le⟩
  have hfa : Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv φ 0)) := by
    simpa [ContinuousWithinAt, hDerivWithin0] using
      (hg_cont.continuousWithinAt h0mem).mono_of_mem_nhdsWithin hs_right
  have hfb : Tendsto g (nhdsWithin αStar (Set.Iio αStar)) (nhds (0 : ℝ)) := by
    simpa [ContinuousWithinAt, hDerivWithinAlpha] using
      (hg_cont.continuousWithinAt hαmem).mono_of_mem_nhdsWithin hs_left
  obtain ⟨ξ, hξ, hMVT⟩ :=
    exists_ratio_deriv_eq_ratio_slope' g hα0 id
      (hg_diff.mono (by intro x hx; exact ⟨hx.1.le, hx.2.le⟩))
      (by
        simpa using
          (differentiableOn_id :
            DifferentiableOn ℝ (fun x : ℝ ↦ x) (Set.Ioo (0 : ℝ) αStar)))
      hfa
      (by simpa [Filter.Tendsto] using
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ)))
      hfb
      (by simpa [Filter.Tendsto] using
        (nhdsWithin_le_nhds : nhdsWithin αStar (Set.Iio αStar) ≤ nhds αStar))
  have hξ_mem : ξ ∈ s := ⟨hξ.1.le, hξ.2.le⟩
  have hξ_mem_b : ξ ∈ Set.Icc (0 : ℝ) b := ⟨le_of_lt hξ.1, hξ.2.le.trans hαb.le⟩
  have hContDiffAtξ : ContDiffAt ℝ 2 φ ξ :=
    hC2.contDiffAt (Icc_mem_nhds hξ.1 (hξ.2.trans hαb))
  have hDerivg : deriv g ξ = iteratedDeriv 2 φ ξ := by
    calc
      deriv g ξ = derivWithin g s ξ := (derivWithin_of_mem_nhds (Icc_mem_nhds hξ.1 hξ.2)).symm
      _ = iteratedDerivWithin 2 φ s ξ := by simp [g, iteratedDerivWithin_succ]
      _ = iteratedDeriv 2 φ ξ := iteratedDerivWithin_eq_iteratedDeriv hs hContDiffAtξ hξ_mem
  have hEq : αStar * iteratedDeriv 2 φ ξ = -deriv φ 0 := by
    simpa [g, hDerivWithin0, hDerivWithinAlpha, hDerivg] using hMVT
  have hBound : -deriv φ 0 ≤ αStar * M := by
    nlinarith [hEq, h_secondDeriv ξ hξ_mem_b, hα0]
  exact (div_le_iff₀ hM).2 (by simpa [mul_comm] using hBound)
