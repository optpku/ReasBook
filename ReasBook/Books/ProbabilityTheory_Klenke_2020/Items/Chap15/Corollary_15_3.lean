/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open BoundedContinuousFunction
open MeasureTheory
open scoped Topology

universe u v

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [CompactSpace E] [BorelSpace E]

-- Core bridge: pass from the multiplicative family `𝒞` to the canonical owner
-- `StarAlgebra.adjoin 𝕜 𝒞`, then apply finite-measure extensionality for star subalgebras of
-- bounded continuous functions.
private theorem finiteMeasure_eq_of_forall_mem_integral_eq_of_separating_boundedContinuousFamily_of_starClosed
    {𝕜 : Type v} [RCLike 𝕜] {𝒞 : Set (BoundedContinuousFunction E 𝕜)}
    (hsep :
      Set.SeparatesPoints
        ((fun f : BoundedContinuousFunction E 𝕜 ↦ (f : E → 𝕜)) '' 𝒞))
    (hmul :
      ∀ ⦃f g : BoundedContinuousFunction E 𝕜⦄,
        f ∈ 𝒞 → g ∈ 𝒞 → f * g ∈ 𝒞)
    (hone : (1 : BoundedContinuousFunction E 𝕜) ∈ 𝒞)
    (hstar :
      ∀ ⦃f : BoundedContinuousFunction E 𝕜⦄,
        f ∈ 𝒞 → star f ∈ 𝒞)
    {μ ν : FiniteMeasure E}
    (hint :
      ∀ ⦃f : BoundedContinuousFunction E 𝕜⦄,
        f ∈ 𝒞 →
          ∫ x, (f : E → 𝕜) x ∂(μ : Measure E) =
            ∫ x, (f : E → 𝕜) x ∂(ν : Measure E)) :
    μ = ν := by
  let A : StarSubalgebra 𝕜 (BoundedContinuousFunction E 𝕜) := StarAlgebra.adjoin 𝕜 𝒞
  let Cmul : Submonoid (BoundedContinuousFunction E 𝕜) := {
    carrier := 𝒞
    one_mem' := hone
    mul_mem' := fun hf hg ↦ hmul hf hg
  }
  have hunion : 𝒞 ∪ star 𝒞 = 𝒞 := by
    ext f
    constructor
    · rintro (hf | hf)
      · exact hf
      · simpa using hstar hf
    · intro hf
      exact Or.inl hf
  have hA_span : A.toSubalgebra.toSubmodule = Submodule.span 𝕜 𝒞 := by
    dsimp [A]
    rw [StarAlgebra.adjoin_eq_span]
    have hclosure : Submonoid.closure (𝒞 ∪ star 𝒞) = Cmul := by
      rw [hunion]
      simpa [Cmul] using (Submonoid.closure_eq Cmul)
    simp [hclosure, Cmul]
  have hAsep : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints := by
    intro x y hxy
    rcases hsep hxy with ⟨g, hg, hne⟩
    rcases hg with ⟨f, hf, rfl⟩
    refine ⟨(toContinuousMapStarₐ 𝕜 f : E → 𝕜), ?_, ?_⟩
    · exact ⟨toContinuousMapStarₐ 𝕜 f,
        show toContinuousMapStarₐ 𝕜 f ∈ A.map (toContinuousMapStarₐ 𝕜) from
          StarSubalgebra.mem_map.2 ⟨f, show f ∈ A from StarAlgebra.subset_adjoin 𝕜 𝒞 hf, rfl⟩,
        rfl⟩
    · simpa using hne
  have hAint :
      ∀ ⦃f : BoundedContinuousFunction E 𝕜⦄,
        f ∈ A →
          ∫ x, (f : E → 𝕜) x ∂(μ : Measure E) =
            ∫ x, (f : E → 𝕜) x ∂(ν : Measure E) := by
    have hspan_int :
        ∀ ⦃f : BoundedContinuousFunction E 𝕜⦄,
          f ∈ Submodule.span 𝕜 𝒞 →
            ∫ x, (f : E → 𝕜) x ∂(μ : Measure E) =
              ∫ x, (f : E → 𝕜) x ∂(ν : Measure E) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem g hg =>
          exact hint hg
      | zero =>
          simp
      | add g h _ _ hg hh =>
          calc
            ∫ x, (g + h) x ∂(μ : Measure E) = ∫ x, g x ∂(μ : Measure E) + ∫ x, h x ∂(μ : Measure E) := by
              simpa [Pi.add_apply] using
                integral_add (g.integrable (μ : Measure E)) (h.integrable (μ : Measure E))
            _ = ∫ x, g x ∂(ν : Measure E) + ∫ x, h x ∂(ν : Measure E) := by
              simpa using congrArg₂ (· + ·) hg hh
            _ = ∫ x, (g + h) x ∂(ν : Measure E) := by
              simpa [Pi.add_apply] using
                (integral_add (g.integrable (ν : Measure E)) (h.integrable (ν : Measure E))).symm
      | smul a g _ hg =>
          calc
            ∫ x, (a • g) x ∂(μ : Measure E) = a • ∫ x, g x ∂(μ : Measure E) := by
              simpa [Pi.smul_apply] using integral_smul a (fun x : E ↦ g x)
            _ = a • ∫ x, g x ∂(ν : Measure E) := by
              simpa using congrArg (a • ·) hg
            _ = ∫ x, (a • g) x ∂(ν : Measure E) := by
              simpa [Pi.smul_apply] using (integral_smul a (fun x : E ↦ g x)).symm
    intro f hf
    have hfspan : (f : BoundedContinuousFunction E 𝕜) ∈ Submodule.span 𝕜 𝒞 := by
      have hfA : (f : BoundedContinuousFunction E 𝕜) ∈ A.toSubalgebra.toSubmodule := hf
      rwa [hA_span] at hfA
    exact hspan_int hfspan
  exact FiniteMeasure.toMeasure_injective <|
    ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable hAsep hAint

/-- Corollary 15.3, real-valued version: on a compact metric space, a point-separating
multiplicative family of bounded continuous real-valued functions that contains `1` determines
finite measures by its integrals. In the real case, closure under conjugation is automatic. -/
theorem finiteMeasure_eq_of_forall_mem_integral_eq_of_separating_boundedContinuousFamily
    {𝒞 : Set (BoundedContinuousFunction E ℝ)}
    (hsep :
      Set.SeparatesPoints
        ((fun f : BoundedContinuousFunction E ℝ ↦ (f : E → ℝ)) '' 𝒞))
    (hmul :
      ∀ ⦃f g : BoundedContinuousFunction E ℝ⦄,
        f ∈ 𝒞 → g ∈ 𝒞 → f * g ∈ 𝒞)
    (hone : (1 : BoundedContinuousFunction E ℝ) ∈ 𝒞)
    {μ ν : FiniteMeasure E}
    (hint :
      ∀ ⦃f : BoundedContinuousFunction E ℝ⦄,
        f ∈ 𝒞 →
          ∫ x, (f : E → ℝ) x ∂(μ : Measure E) =
            ∫ x, (f : E → ℝ) x ∂(ν : Measure E)) :
    μ = ν :=
  finiteMeasure_eq_of_forall_mem_integral_eq_of_separating_boundedContinuousFamily_of_starClosed
    hsep hmul hone (fun {_} hf ↦ by simpa using hf) hint

/-- Corollary 15.3, complex-valued version: on a compact metric space, a point-separating
multiplicative family of bounded continuous complex-valued functions that contains `1` and is
closed under complex conjugation determines finite measures by its integrals. -/
theorem finiteMeasure_eq_of_forall_mem_integral_eq_of_separating_boundedContinuousFamily_complex
    {𝒞 : Set (BoundedContinuousFunction E ℂ)}
    (hsep :
      Set.SeparatesPoints
        ((fun f : BoundedContinuousFunction E ℂ ↦ (f : E → ℂ)) '' 𝒞))
    (hmul :
      ∀ ⦃f g : BoundedContinuousFunction E ℂ⦄,
        f ∈ 𝒞 → g ∈ 𝒞 → f * g ∈ 𝒞)
    (hone : (1 : BoundedContinuousFunction E ℂ) ∈ 𝒞)
    (hstar :
      ∀ ⦃f : BoundedContinuousFunction E ℂ⦄,
        f ∈ 𝒞 → star f ∈ 𝒞)
    {μ ν : FiniteMeasure E}
    (hint :
      ∀ ⦃f : BoundedContinuousFunction E ℂ⦄,
        f ∈ 𝒞 →
          ∫ x, (f : E → ℂ) x ∂(μ : Measure E) =
            ∫ x, (f : E → ℂ) x ∂(ν : Measure E)) :
    μ = ν :=
  finiteMeasure_eq_of_forall_mem_integral_eq_of_separating_boundedContinuousFamily_of_starClosed
    hsep hmul hone hstar hint
