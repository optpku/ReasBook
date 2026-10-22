/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: index the finite set `F` by its subtype and apply
-- `MeasureTheory.uniformIntegrable_finite` at exponent `p = 1`. The assumption that each member of
-- `F` belongs to `L¹(μ)` supplies the required `MemLp` hypotheses.
/-- Theorem 6.18 (1): Item (i). A finite set of integrable real-valued functions is uniformly
integrable. -/
theorem uniformIntegrable_of_finite_integrable_set (μ : Measure Ω) {F : Set (Ω → ℝ)}
    (hF_fin : F.Finite) (hF_int : ∀ f ∈ F, Integrable f μ) :
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ := by
  classical
  letI : Fintype F := hF_fin.fintype
  refine uniformIntegrable_finite le_rfl ?_ ?_
  · simp
  · intro f
    rw [memLp_one_iff_integrable]
    exact hF_int f f.2

-- Proof sketch: pass from the two uniformly integrable families to their underlying uniformly
-- absolutely continuous integral bounds, combine them with Minkowski's inequality for the
-- restricted `L¹` norms, and control the `L¹` norms of the sums by the sum of the individual
-- bounds.
/-- Theorem 6.18 (2): Item (ii). The family of all pairwise sums of two uniformly integrable sets
of real-valued functions is uniformly integrable. -/
theorem uniformIntegrable_add_of_sets (μ : Measure Ω) {F G : Set (Ω → ℝ)}
    (hF : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ)
    (hG : UniformIntegrable ((↑) : G → Ω → ℝ) 1 μ) :
    UniformIntegrable (fun fg : F × G ↦ (fg.1 : Ω → ℝ) + (fg.2 : Ω → ℝ)) 1 μ := by
  have hF_prod : UnifIntegrable (fun fg : F × G ↦ (fg.1 : Ω → ℝ)) 1 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hFδ⟩ := hF.unifIntegrable hε
    exact ⟨δ, hδ, fun fg s hs hμs ↦ hFδ fg.1 s hs hμs⟩
  have hG_prod : UnifIntegrable (fun fg : F × G ↦ (fg.2 : Ω → ℝ)) 1 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hGδ⟩ := hG.unifIntegrable hε
    exact ⟨δ, hδ, fun fg s hs hμs ↦ hGδ fg.2 s hs hμs⟩
  refine ⟨
    fun fg : F × G ↦ (hF.aestronglyMeasurable (fg.1)).add (hG.aestronglyMeasurable (fg.2)),
    hF_prod.add hG_prod le_rfl
      (fun fg : F × G ↦ hF.aestronglyMeasurable (fg.1))
      (fun fg : F × G ↦ hG.aestronglyMeasurable (fg.2)),
    ?_⟩
  obtain ⟨CF, hCF⟩ := hF.2.2
  obtain ⟨CG, hCG⟩ := hG.2.2
  refine ⟨CF + CG, fun fg ↦ ?_⟩
  exact (eLpNorm_add_le (hF.aestronglyMeasurable (fg.1)) (hG.aestronglyMeasurable (fg.2))
    le_rfl).trans <| add_le_add (hCF fg.1) (hCG fg.2)

-- Proof sketch: combine the two uniformly integrable families using the same argument as for sums,
-- after rewriting subtraction as addition with the negated second family. The `L¹` bounds are
-- unchanged by negation.
/-- Theorem 6.18 (3): Item (ii). The family of all pairwise differences of two uniformly
integrable sets of real-valued functions is uniformly integrable. -/
theorem uniformIntegrable_sub_of_sets (μ : Measure Ω) {F G : Set (Ω → ℝ)}
    (hF : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ)
    (hG : UniformIntegrable ((↑) : G → Ω → ℝ) 1 μ) :
    UniformIntegrable (fun fg : F × G ↦ (fg.1 : Ω → ℝ) - (fg.2 : Ω → ℝ)) 1 μ := by
  have hF_prod : UnifIntegrable (fun fg : F × G ↦ (fg.1 : Ω → ℝ)) 1 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hFδ⟩ := hF.unifIntegrable hε
    exact ⟨δ, hδ, fun fg s hs hμs ↦ hFδ fg.1 s hs hμs⟩
  have hG_prod : UnifIntegrable (fun fg : F × G ↦ (fg.2 : Ω → ℝ)) 1 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hGδ⟩ := hG.unifIntegrable hε
    exact ⟨δ, hδ, fun fg s hs hμs ↦ hGδ fg.2 s hs hμs⟩
  refine ⟨
    fun fg : F × G ↦ (hF.aestronglyMeasurable (fg.1)).sub (hG.aestronglyMeasurable (fg.2)),
    hF_prod.sub hG_prod le_rfl
      (fun fg : F × G ↦ hF.aestronglyMeasurable (fg.1))
      (fun fg : F × G ↦ hG.aestronglyMeasurable (fg.2)),
    ?_⟩
  obtain ⟨CF, hCF⟩ := hF.2.2
  obtain ⟨CG, hCG⟩ := hG.2.2
  refine ⟨CF + CG, fun fg ↦ ?_⟩
  simpa [sub_eq_add_neg] using
    (eLpNorm_add_le (hF.aestronglyMeasurable (fg.1)) ((hG.aestronglyMeasurable (fg.2)).neg)
      le_rfl).trans <| by
        rw [eLpNorm_neg]
        exact add_le_add (hCF fg.1) (hCG fg.2)

-- Proof sketch: replace each function by its pointwise absolute value, use that the restricted
-- `L¹` norm of `|f|` agrees with that of `f`, and keep the same uniform absolute continuity and
-- uniform `L¹` bounds.
/-- Theorem 6.18 (4): Item (ii). Taking pointwise absolute values preserves uniform integrability
for a set of real-valued functions. -/
theorem uniformIntegrable_abs_of_set (μ : Measure Ω) {F : Set (Ω → ℝ)}
    (hF : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ) :
    UniformIntegrable (fun f : F ↦ |(f : Ω → ℝ)|) 1 μ := by
  refine ⟨fun f ↦ by simpa [Real.norm_eq_abs] using (hF.aestronglyMeasurable f).norm, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hFδ⟩ := hF.unifIntegrable hε
    refine ⟨δ, hδ, fun f s hs hμs ↦ ?_⟩
    have h_abs :
        eLpNorm (s.indicator |(f : Ω → ℝ)|) 1 μ = eLpNorm (s.indicator (f : Ω → ℝ)) 1 μ :=
      eLpNorm_congr_norm_ae <| Filter.Eventually.of_forall fun x ↦ by
        by_cases hx : x ∈ s <;> simp [hx, Real.norm_eq_abs]
    rw [h_abs]
    exact hFδ f s hs hμs
  · obtain ⟨C, hC⟩ := hF.2.2
    refine ⟨C, fun f ↦ ?_⟩
    have h_abs : eLpNorm |(f : Ω → ℝ)| 1 μ = eLpNorm (f : Ω → ℝ) 1 μ :=
      eLpNorm_congr_norm_ae <| Filter.Eventually.of_forall fun x ↦ by simp [Real.norm_eq_abs]
    rw [h_abs]
    exact hC f

-- Proof sketch: use the domination hypothesis to compare the restricted absolute integrals of
-- members of `G` with those of suitable members of `F`. The uniform absolute continuity and the
-- uniform `L¹` bound of `F` then transfer directly to `G`.
/-- Theorem 6.18 (5): Item (iii). A measurable set of real-valued functions dominated pointwise in
absolute value by a uniformly integrable set is uniformly integrable. -/
theorem uniformIntegrable_of_abs_dominated_set (μ : Measure Ω) {F G : Set (Ω → ℝ)}
    (hF : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ)
    (hG_meas : ∀ g ∈ G, AEStronglyMeasurable g μ)
    (hdom : ∀ g ∈ G, ∃ f ∈ F, ∀ x, |g x| ≤ |f x|) :
    UniformIntegrable ((↑) : G → Ω → ℝ) 1 μ := by
  refine ⟨fun g ↦ hG_meas g g.2, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hFδ⟩ := hF.unifIntegrable hε
    refine ⟨δ, hδ, fun g s hs hμs ↦ ?_⟩
    obtain ⟨f, hfF, hfg⟩ := hdom g g.2
    exact (eLpNorm_mono fun x ↦ by
      by_cases hx : x ∈ s
      · simp [hx, Real.norm_eq_abs, hfg x]
      · simp [hx]).trans <| hFδ ⟨f, hfF⟩ s hs hμs
  · obtain ⟨C, hC⟩ := hF.2.2
    refine ⟨C, fun g ↦ ?_⟩
    obtain ⟨f, hfF, hfg⟩ := hdom g g.2
    exact (eLpNorm_mono fun x ↦ by simpa [Real.norm_eq_abs] using hfg x).trans <| hC ⟨f, hfF⟩
