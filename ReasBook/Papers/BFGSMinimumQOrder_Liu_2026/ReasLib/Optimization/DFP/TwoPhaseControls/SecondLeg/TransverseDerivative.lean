module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

public section

open Filter
open scoped Topology

namespace DFP.SecondLeg

/-!
# Parameterized transverse derivative bounds

The second-leg amplitude proof needs a bound for a derivative in the transverse variables,
while the signed scale is only a parameter.  These lemmas isolate the scalar-cubic factor
and its local bounded quotient from the concrete `gradientFactors` formula.
-/

/-- Helper for Lemma 4.15: a cubic factorization of a transverse derivative gives the
corresponding norm estimate at one parameter value. -/
theorem transverse_fderiv_norm_le_of_cubic_factorization
    {g : ℝ → (ℝ × ℝ) → ℝ}
    {A : ℝ × (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    {x : ℝ × (ℝ × ℝ)} {C : ℝ}
    (hfactor : fderiv ℝ (g x.1) x.2 = x.1 ^ (3 : ℕ) • A x)
    (hA : ‖A x‖ ≤ C) :
    ‖fderiv ℝ (g x.1) x.2‖ ≤ C * ‖x.1 ^ (3 : ℕ)‖ := by
  rw [hfactor, norm_smul]
  calc
    ‖x.1 ^ (3 : ℕ)‖ * ‖A x‖ ≤ ‖x.1 ^ (3 : ℕ)‖ * C :=
      mul_le_mul_of_nonneg_left hA (norm_nonneg _)
    _ = C * ‖x.1 ^ (3 : ℕ)‖ := by ring

/-- Helper for Lemma 4.15: continuity of the cubic quotient turns an eventual transverse
derivative factorization into one uniform local norm bound. -/
theorem eventually_transverse_fderiv_norm_le_of_cubic_factorization
    {g : ℝ → (ℝ × ℝ) → ℝ}
    {A : ℝ × (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    {x₀ : ℝ × (ℝ × ℝ)}
    (hfactor : ∀ᶠ x in 𝓝 x₀,
      fderiv ℝ (g x.1) x.2 = x.1 ^ (3 : ℕ) • A x)
    (hA : ContinuousAt A x₀) :
    ∃ C > 0, ∀ᶠ x in 𝓝 x₀,
      ‖fderiv ℝ (g x.1) x.2‖ ≤ C * ‖x.1 ^ (3 : ℕ)‖ := by
  let C : ℝ := ‖A x₀‖ + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith [norm_nonneg (A x₀)]
  have hAnorm : Tendsto (fun x : ℝ × (ℝ × ℝ) ↦ ‖A x‖) (𝓝 x₀) (𝓝 ‖A x₀‖) :=
    hA.norm
  have hAevent : ∀ᶠ x in 𝓝 x₀, ‖A x‖ < C := by
    have hIio : ‖A x₀‖ < C := by
      dsimp [C]
      linarith
    exact hAnorm.eventually (Iio_mem_nhds hIio)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfactor, hAevent] with x hfx hAx
  exact transverse_fderiv_norm_le_of_cubic_factorization hfx hAx.le

end DFP.SecondLeg
