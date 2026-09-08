module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder
public import Mathlib.Analysis.Normed.Operator.Basic

public section

namespace LocalCutoff.GraphTransform

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- First-order Taylor remainders of translated `C¹` functions are uniform
when their translation centers range over a compact set. -/
theorem uniformTranslatedFirstOrderRemainderOn
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ → Y} (hf : ContDiff ℝ 1 f) {K : Set ℝ} (hK : IsCompact K)
    {C : ℝ} (hC : 0 < C) :
    ∃ δ > 0, ∀ u ∈ K, ∀ h : ℝ, ‖h‖ < δ →
      ‖(FiniteTaylorJet.ofFunction ℝ 1 (fun z : ℝ ↦ f (u + z)) 0).remainder
        (fun z : ℝ ↦ f (u + z)) 0 h‖ ≤ C * ‖h‖ := by
  -- Regard translation as a jointly `C¹` family and apply the compact-fiber
  -- Taylor estimate once to obtain a radius uniform in the base point.
  let g : ℝ → ℝ → Y := fun u h ↦ f (u + h)
  have hg : ContDiff ℝ 1 (Function.uncurry g) := by
    have hg' : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ f (p.1 + p.2)) :=
      hf.comp (contDiff_fst.add contDiff_snd)
    convert hg' using 1
    funext p
    rfl
  have huniform := FiniteTaylorJet.uniformRemainderOn_of_contDiff
    1 g 0 K hK hg C hC
  obtain ⟨δ, hδ, hbound⟩ := FiniteTaylorJet.IsUniformRemainderOn.bound huniform
  refine ⟨δ, hδ, ?_⟩
  intro u hu h hh
  simpa [g, pow_one] using hbound u hu h hh

/-- The two-point defect of an affine cocycle splits into its contracted
predecessor defect, the coefficient remainders, and the base-map remainder. -/
theorem affineCocycle_defect_decomposition
    (A₀ A₁ A' : X →L[ℝ] X) (b₀ b₁ b' w₀ w₁ d₀ d₁ : X)
    (f' Δ s : ℝ)
    (hderivative : f' • d₁ = A' w₀ + A₀ d₀ + b') :
    (A₁ w₁ + b₁) - (A₀ w₀ + b₀) - s • d₁ =
      A₁ (w₁ - w₀ - Δ • d₀) +
        (((A₁ - A₀) w₀ - Δ • A' w₀) +
          (A₁ - A₀) (Δ • d₀) +
          (b₁ - b₀ - Δ • b') +
          (f' * Δ - s) • d₁) := by
  -- Expand the linear terms, then substitute the differentiated cocycle so
  -- every first-order contribution cancels in the displayed remainder form.
  simp only [sub_apply, map_sub, map_smul]
  have hscalar : (f' * Δ) • d₁ = Δ • (f' • d₁) := by
    rw [smul_smul, mul_comm]
  rw [sub_smul, hscalar]
  rw [hderivative]
  simp only [smul_add, smul_sub]
  abel

/-- A forcing estimate for the affine-cocycle decomposition yields the raw
defect recurrence with the operator norm of the successor coefficient. -/
theorem affineCocycle_defect_norm_le
    (A₀ A₁ A' : X →L[ℝ] X) (b₀ b₁ b' w₀ w₁ d₀ d₁ : X)
    (f' Δ s p η : ℝ)
    (hderivative : f' • d₁ = A' w₀ + A₀ d₀ + b')
    (hA₁ : ‖A₁‖ ≤ p)
    (hforcing :
      ‖((A₁ - A₀) w₀ - Δ • A' w₀) +
          (A₁ - A₀) (Δ • d₀) +
          (b₁ - b₀ - Δ • b') +
          (f' * Δ - s) • d₁‖ ≤ η * ‖s‖) :
    ‖(A₁ w₁ + b₁) - (A₀ w₀ + b₀) - s • d₁‖ ≤
      p * ‖w₁ - w₀ - Δ • d₀‖ + η * ‖s‖ := by
  -- Rewrite by the exact decomposition, then bound the principal affine term
  -- and the collected first-order forcing separately.
  rw [affineCocycle_defect_decomposition A₀ A₁ A' b₀ b₁ b' w₀ w₁ d₀ d₁
    f' Δ s hderivative]
  calc
    ‖A₁ (w₁ - w₀ - Δ • d₀) +
        (((A₁ - A₀) w₀ - Δ • A' w₀) +
          (A₁ - A₀) (Δ • d₀) +
          (b₁ - b₀ - Δ • b') +
          (f' * Δ - s) • d₁)‖ ≤
        ‖A₁ (w₁ - w₀ - Δ • d₀)‖ +
          ‖((A₁ - A₀) w₀ - Δ • A' w₀) +
            (A₁ - A₀) (Δ • d₀) +
            (b₁ - b₀ - Δ • b') +
            (f' * Δ - s) • d₁‖ := norm_add_le _ _
    _ ≤ ‖A₁‖ * ‖w₁ - w₀ - Δ • d₀‖ + η * ‖s‖ :=
      add_le_add (A₁.le_opNorm _) hforcing
    _ ≤ p * ‖w₁ - w₀ - Δ • d₀‖ + η * ‖s‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hA₁ (norm_nonneg _)) le_rfl

end LocalCutoff.GraphTransform
