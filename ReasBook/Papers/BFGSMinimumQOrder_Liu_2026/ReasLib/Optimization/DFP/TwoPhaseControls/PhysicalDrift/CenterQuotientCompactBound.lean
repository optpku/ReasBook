module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusJet

public section

noncomputable section

open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
The center-residual quotient is intended to be continuous after its denominator is
cleared.  This companion isolates the compactness step: once that `ContinuousOn`
certificate is supplied, the required uniform quotient bound is immediate.
-/

/-- Helper for Appendix Lemma A.6: a quotient continuous on the compact parameter
    tube has a uniform norm bound on every smaller radius interval. -/
theorem exists_uniform_quotient_bound_of_continuousOn
    (β B δ : ℝ)
    (Q : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (hQcont : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ Q z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-δ) δ)) :
    ∃ C > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ → ‖Q θ r‖ ≤ C := by
  have hcompact : IsCompact (parameterSet β B ×ˢ Set.Icc (-δ) δ) :=
    (parameterSet_isCompact β B).prod isCompact_Icc
  have hnorm : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ ‖Q z.1 z.2‖)
      (parameterSet β B ×ˢ Set.Icc (-δ) δ) := hQcont.norm
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hnorm
  refine ⟨max C 1, lt_max_of_lt_right zero_lt_one, ?_⟩
  intro θ hθ r hr
  have hrIcc : r ∈ Set.Icc (-δ) δ := by
    exact ⟨le_of_lt (abs_lt.mp hr).1, le_of_lt (abs_lt.mp hr).2⟩
  have hbound := hC ⟨(θ, r), ⟨hθ, hrIcc⟩, rfl⟩
  exact le_trans hbound (le_max_left _ _)

/-- Helper for Appendix Lemma A.6: continuity of a quotient on some positive
    compact parameter tube supplies the complete local uniform-bound certificate. -/
theorem exists_local_uniform_quotient_bound_of_continuousOn
    (β B : ℝ) (Q : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (hQcont : ∃ δ > 0, ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ Q z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-δ) δ)) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ → ‖Q θ r‖ ≤ C := by
  obtain ⟨δ, hδ, hQcont⟩ := hQcont
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_quotient_bound_of_continuousOn β B δ Q hQcont
  exact ⟨C, hC, δ, hδ, hbound⟩

/-- Helper for Appendix Lemma A.6: a continuous kernel agreeing with the quotient
    on a positive tube yields the quotient's uniform bound on that tube. -/
theorem exists_local_uniform_quotient_bound_of_continuousKernel
    (β B : ℝ) (Q K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (hcertificate : ∃ δ > 0,
      ContinuousOn
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
        (parameterSet β B ×ˢ Set.Icc (-δ) δ) ∧
      (∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ → Q θ r = K θ r)) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ → ‖Q θ r‖ ≤ C := by
  obtain ⟨δ, hδ, hKcont, hQeq⟩ := hcertificate
  obtain ⟨C, hC, hKbound⟩ :=
    exists_uniform_quotient_bound_of_continuousOn β B δ K hKcont
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro θ hθ r hr
  rw [hQeq θ hθ r hr]
  exact hKbound θ hθ r hr

end DFP.TwoLeg.Mixed
