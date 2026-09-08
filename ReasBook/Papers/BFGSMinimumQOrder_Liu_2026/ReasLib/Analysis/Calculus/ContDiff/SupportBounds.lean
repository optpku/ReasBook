module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Defs

public section

noncomputable section

open Set

universe u uE uF

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An iterated Fréchet derivative vanishes at every point outside the topological support
of the original function. -/
theorem iteratedFDeriv_eq_zero_of_notMem_tsupport (f : E → F) (n : ℕ) {x : E}
    (hx : x ∉ tsupport f) :
    iteratedFDeriv 𝕜 n f x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  exact fun hx' ↦ hx (tsupport_iteratedFDeriv_subset (𝕜 := 𝕜) n hx')

/-- A nonnegative bound for an iterated derivative on the topological support of the
original function is automatically a global bound. -/
theorem norm_iteratedFDeriv_le_of_tsupport (f : E → F) (n : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hbound : ∀ x ∈ tsupport f, ‖iteratedFDeriv 𝕜 n f x‖ ≤ C) (x : E) :
    ‖iteratedFDeriv 𝕜 n f x‖ ≤ C := by
  by_cases hx : x ∈ tsupport f
  · exact hbound x hx
  · rw [iteratedFDeriv_eq_zero_of_notMem_tsupport f n hx, norm_zero]
    exact hC

namespace HasCompactSupport

/-- Every fixed iterated derivative of a compactly supported `C^n` function admits a
nonnegative global norm bound. -/
theorem exists_norm_iteratedFDeriv_le {f : E → F} {n : ℕ}
    (hcompact : HasCompactSupport f) (hsmooth : ContDiff 𝕜 n f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖_root_.iteratedFDeriv 𝕜 n f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hsmooth.continuous_iteratedFDeriv'.bounded_above_of_compact_support
    (hcompact.iteratedFDeriv n)
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

/-- The first derivative of a compactly supported `C^1` function admits a nonnegative
global operator-norm bound. -/
theorem exists_norm_fderiv_le {f : E → F} (hcompact : HasCompactSupport f)
    (hsmooth : ContDiff 𝕜 1 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv 𝕜 f x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hcompact.exists_norm_iteratedFDeriv_le hsmooth
  refine ⟨C, hC, fun x ↦ ?_⟩
  simpa only [norm_iteratedFDeriv_one] using hbound x

/-- The second derivative of a compactly supported `C^2` function admits a nonnegative
global operator-norm bound. -/
theorem exists_norm_secondFDeriv_le {f : E → F} (hcompact : HasCompactSupport f)
    (hsmooth : ContDiff 𝕜 2 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hcompact.exists_norm_iteratedFDeriv_le hsmooth
  refine ⟨C, hC, fun x ↦ ?_⟩
  calc
    ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ =
        ‖_root_.iteratedFDeriv 𝕜 1 (fderiv 𝕜 f) x‖ :=
      (norm_iteratedFDeriv_one (𝕜 := 𝕜) (fderiv 𝕜 f)).symm
    _ = ‖_root_.iteratedFDeriv 𝕜 2 f x‖ :=
      norm_iteratedFDeriv_fderiv (𝕜 := 𝕜) (f := f) (n := 1)
    _ ≤ C := hbound x

end HasCompactSupport
