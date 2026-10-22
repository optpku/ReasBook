/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Theorem_9_39_Helpers

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {ℱ : Filtration ℕ mΩ} {μ : Measure Ω}

/-- Helper for Theorem 9.39: the constant process `1` is predictable. -/
lemma predictableOne : IsPredictable ℱ (fun _ _ ↦ (1 : ℝ)) := by
  refine isPredictable_of_measurable_add_one ?_ ?_
  · simpa using (measurable_const : Measurable[ℱ 0] (fun _ : Ω ↦ (1 : ℝ)))
  · intro n
    simpa using (measurable_const : Measurable[ℱ n] (fun _ : Ω ↦ (1 : ℝ)))

/-- Helper for Theorem 9.39: the constant process `1` is locally bounded. -/
lemma locallyBoundedProcessOne : IsLocallyBoundedProcess (Ω := Ω) (fun _ _ ↦ (1 : ℝ)) := by
  -- Bound the constant stake process uniformly by the radius `1` at every time.
  intro n
  refine ⟨1, zero_le_one, ?_⟩
  intro ω
  simp

/-- Helper for Theorem 9.39: repeating the initial value at every time yields a martingale. -/
lemma initialValueProcess_martingale [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hX_adapted : Adapted ℱ X) (hX0_int : Integrable (X 0) μ) :
    Martingale (fun _ ↦ X 0) ℱ μ := by
  have hX0_meas : StronglyMeasurable[ℱ 0] (X 0) := (hX_adapted 0).stronglyMeasurable
  exact martingale_const_fun ℱ μ hX0_meas hX0_int

/-- Helper for Theorem 9.39: adding back the initial value recovers `X` from the stochastic
integral with constant integrand `1`. -/
lemma stochasticIntegralOne_add_initial (X : ℕ → Ω → ℝ) :
    stochasticIntegral (fun _ _ ↦ (1 : ℝ)) X + (fun _ ↦ X 0) = X := by
  -- Rewrite the stochastic integral with integrand `1` as `X - X₀` and cancel the initial value.
  funext n ω
  simp [Pi.add_apply, stochasticIntegral_one_eq_sub_initial]

/-- Theorem 9.39: a discrete stochastic integral preserves the martingale, submartingale, and
supermartingale properties under locally bounded predictable integrands, and these properties can
be recovered by testing against the constant integrand `1`. -/
theorem stochasticIntegral_stability [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hX_adapted : Adapted ℱ X) (hX0_int : Integrable (X 0) μ) :
    (Martingale X ℱ μ ↔
      ∀ H : ℕ → Ω → ℝ, IsPredictable ℱ H → IsLocallyBoundedProcess H →
        Martingale (stochasticIntegral H X) ℱ μ) ∧
      (Submartingale X ℱ μ ↔
        ∀ H : ℕ → Ω → ℝ, IsPredictable ℱ H → IsLocallyBoundedProcess H →
          (∀ n ω, 0 ≤ H n ω) → Submartingale (stochasticIntegral H X) ℱ μ) ∧
      (Supermartingale X ℱ μ ↔
        ∀ H : ℕ → Ω → ℝ, IsPredictable ℱ H → IsLocallyBoundedProcess H →
          (∀ n ω, 0 ≤ H n ω) → Supermartingale (stochasticIntegral H X) ℱ μ) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hX H hH hH_bdd
      -- The forward martingale direction is exactly the stability result proved in the helpers.
      exact martingale_stochasticIntegral hX hH hH_bdd
    · intro hTransform
      have hIntegral :
          Martingale (stochasticIntegral (fun _ _ ↦ (1 : ℝ)) X) ℱ μ :=
        hTransform (fun _ _ ↦ (1 : ℝ)) predictableOne locallyBoundedProcessOne
      have hInitial : Martingale (fun _ ↦ X 0) ℱ μ :=
        initialValueProcess_martingale hX_adapted hX0_int
      -- The transform with `H = 1` is `X - X₀`, so adding back the initial value recovers `X`.
      simpa [stochasticIntegralOne_add_initial] using hIntegral.add hInitial
  · refine ⟨?_, ?_⟩
    · constructor
      · intro hX H hH hH_bdd hH_nonneg
        -- Nonnegative predictable stakes preserve the submartingale property.
        exact submartingale_stochasticIntegral hX hH hH_bdd hH_nonneg
      · intro hTransform
        have hIntegral :
            Submartingale (stochasticIntegral (fun _ _ ↦ (1 : ℝ)) X) ℱ μ :=
          hTransform (fun _ _ ↦ (1 : ℝ)) predictableOne locallyBoundedProcessOne
            (fun _ _ ↦ zero_le_one)
        have hInitial : Martingale (fun _ ↦ X 0) ℱ μ :=
          initialValueProcess_martingale hX_adapted hX0_int
        -- Add the initial-value martingale to recover the original process.
        simpa [stochasticIntegralOne_add_initial] using hIntegral.add_martingale hInitial
    · constructor
      · intro hX H hH hH_bdd hH_nonneg
        have hIntegralNeg :
            Submartingale (stochasticIntegral H (-X)) ℱ μ :=
          submartingale_stochasticIntegral hX.neg hH hH_bdd hH_nonneg
        -- Negating the transform converts the submartingale conclusion back to a supermartingale.
        simpa [stochasticIntegral_neg_right] using hIntegralNeg.neg
      · intro hTransform
        have hIntegral :
            Supermartingale (stochasticIntegral (fun _ _ ↦ (1 : ℝ)) X) ℱ μ :=
          hTransform (fun _ _ ↦ (1 : ℝ)) predictableOne locallyBoundedProcessOne
            (fun _ _ ↦ zero_le_one)
        have hInitial : Martingale (fun _ ↦ X 0) ℱ μ :=
          initialValueProcess_martingale hX_adapted hX0_int
        -- Add the initial-value martingale to recover the original process.
        simpa [stochasticIntegralOne_add_initial] using hIntegral.add_martingale hInitial

end ProbabilityTheory
