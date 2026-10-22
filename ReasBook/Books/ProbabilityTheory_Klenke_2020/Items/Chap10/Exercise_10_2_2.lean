/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Exercise_10_2_2Core

open MeasureTheory ProbabilityTheory

universe u

noncomputable section

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Y : ℕ → Ω → ℝ} {δ θStar : ℝ} {k₀ : ℕ}

namespace Exercise_10_2_2

/-- Exercise 10.2.2 (7): in the special `±1`-valued case with integer initial capital, the
Cramér-Lundberg inequality is sharp, recovering the classical exact ruin formula with
`r = exp θ⋆`. -/
-- Keep the label-bearing item entry in this file while delegating the detailed proof to the
-- canonical core theorem.
theorem ruinProbability_eq_exp_cgf_root_of_two_point_steps
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0)
    (h_two_point : ∀ n, ∀ᵐ ω ∂μ, Y n ω = -1 ∨ Y n ω = 1) :
    ruinProbability Y μ k₀ = Real.exp (θStar * ((k₀ : ℝ) + 1)) := by
  exact _root_.ruinProbability_eq_exp_cgf_root_of_two_point_steps
    (Y := Y) (μ := μ) (δ := δ) (θStar := θStar) (k₀ := k₀)
    hY_indep hY_ident hY_mean_pos hθStar hroot hθStar_ne h_two_point

end Exercise_10_2_2

end
