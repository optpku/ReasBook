module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

public section

open Filter
open scoped Topology

universe u v

namespace LocalCutoff.GraphTransform

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/- Helper for Infrastructure I.16: an explicit cubic factorization of a derivative
reduces its norm estimate to a bound for the remaining continuous factor. -/
theorem norm_fderiv_le_of_cubic_factorization
    {g : ℝ × E → F} {A : ℝ × E → (ℝ × E) →L[ℝ] F}
    {ε : ℝ} {z : E} {C : ℝ}
    (hfactor : fderiv ℝ g (ε, z) = ε ^ 3 • A (ε, z))
    (hA : ‖A (ε, z)‖ ≤ C) :
    ‖fderiv ℝ g (ε, z)‖ ≤ C * |ε| ^ (3 : ℕ) := by
  rw [hfactor, norm_smul, Real.norm_eq_abs, abs_pow]
  have hpow_nonneg : 0 ≤ |ε| ^ (3 : ℕ) := by positivity
  calc
    |ε| ^ (3 : ℕ) * ‖A (ε, z)‖ ≤ |ε| ^ (3 : ℕ) * C :=
      mul_le_mul_of_nonneg_left hA hpow_nonneg
    _ = C * |ε| ^ (3 : ℕ) := by ring

/- Helper for Infrastructure I.16: local continuity of the cubic factor supplies
a positive neighborhood constant for the derivative bound. -/
theorem eventually_norm_fderiv_le_of_cubic_factorization
    {g : ℝ × E → F} {A : ℝ × E → (ℝ × E) →L[ℝ] F}
    {x₀ : ℝ × E}
    (hfactor : ∀ᶠ x in 𝓝 x₀, fderiv ℝ g x = x.1 ^ 3 • A x)
    (hA : ContinuousAt A x₀) :
    ∃ C > 0, ∀ᶠ x in 𝓝 x₀,
      ‖fderiv ℝ g x‖ ≤ C * |x.1| ^ (3 : ℕ) := by
  let C : ℝ := ‖A x₀‖ + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith [norm_nonneg (A x₀)]
  have hAnorm : Tendsto (fun x : ℝ × E ↦ ‖A x‖) (𝓝 x₀) (𝓝 ‖A x₀‖) :=
    hA.norm
  have hAevent : ∀ᶠ x in 𝓝 x₀, ‖A x‖ < C := by
    have hIio : ‖A x₀‖ < C := by
      dsimp [C]
      linarith
    have hnhds : Set.Iio C ∈ 𝓝 ‖A x₀‖ := Iio_mem_nhds hIio
    exact hAnorm.eventually hnhds
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfactor, hAevent] with x hfx hAx
  exact norm_fderiv_le_of_cubic_factorization hfx hAx.le

end LocalCutoff.GraphTransform
