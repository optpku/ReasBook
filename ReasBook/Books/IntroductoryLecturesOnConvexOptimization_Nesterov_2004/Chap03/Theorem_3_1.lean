/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Jensen
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v w z

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {ι : Type v}
variable {E : Type w} [AddCommGroup E] [Module 𝕜 E]
variable {β : Type z} [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β]
  [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]

local notation "convexCombination" =>
  @ConvexSpace.convexCombination 𝕜 E inferInstance inferInstance inferInstance inferInstance

/- Theorem 3.1 lies in the finite convex-combination / convex-hull maximum-principle domain.

Sampled owner-style declarations:
- `is_convex_combination_of`
- `StdSimplex.convexCombination_map_eq_sum`
- `ConvexOn.exists_ge_of_mem_convexHull`
- `ConvexOn.le_sup_of_mem_convexHull`

Best owner abstraction:
- the chapter owner `is_convex_combination_of 𝕜 points x`, bridged to the canonical convex-hull
  maximum-principle theorems

Primitive data:
- a convex-on-set witness `hf : ConvexOn 𝕜 C f`
- a family `points : ι → E`
- a point `x : E`
- the owner witness `hx : is_convex_combination_of 𝕜 points x`

Derived API:
- the convex-hull membership bridge `hx.mem_convexHull`
- the attainment statement `∃ i, f x ≤ f (points i)`
- the finite maximum bound over `Finset.univ`
- the coefficient bridge `StdSimplex.convexCombination_map_eq_sum`

Source/core/bridge triage:
- source-facing: the maximum principle for the value of a convex function at a finite convex
  combination
- core/canonical: `ConvexOn.exists_ge_of_mem_convexHull` and
  `ConvexOn.le_sup_of_mem_convexHull`
- bridge/view: `is_convex_combination_of.mem_convexHull` and the coefficient-display companion
  theorem

This file therefore centers its public theorem surface on the earlier chapter owner
`is_convex_combination_of`. The coefficient formula remains only as a companion bridge, while the
main proofs reuse the canonical convex-hull maximum principle.
-/

/-- A finite convex combination belongs to the convex hull of the participating family. -/
theorem is_convex_combination_of.mem_convexHull {points : ι → E} {x : E}
    (hx : is_convex_combination_of 𝕜 points x) :
    x ∈ convexHull 𝕜 (Set.range points) := by
  rcases hx with ⟨w, rfl⟩
  let s := w.weights.support
  have hsum : ∑ i ∈ s, w.weights i = 1 := by
    simpa [s, Finsupp.sum] using w.total
  have hcomb : convexCombination (w.map points) = s.centerMass w.weights points := by
    have hs_center : s.centerMass w.weights points = ∑ i ∈ s, w.weights i • points i := by
      rw [Finset.centerMass, hsum]
      simp
    calc
      convexCombination (w.map points) = ∑ i ∈ s, w.weights i • points i := by
        rw [convexCombination_eq_sum, StdSimplex.map]
        rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ add_smul _ _ _)]
        rfl
      _ = s.centerMass w.weights points := by
        simpa using hs_center.symm
  rw [hcomb]
  exact s.centerMass_mem_convexHull
    (fun i _ ↦ w.nonneg i)
    (by
      rw [hsum]
      exact zero_lt_one)
    (fun i _ ↦ ⟨i, rfl⟩)

/-- A nontrivial finite convex combination requires a nonempty index type. -/
theorem is_convex_combination_of.nonempty {points : ι → E} {x : E}
    (hx : is_convex_combination_of 𝕜 points x) : Nonempty ι := by
  rcases hx with ⟨w, _⟩
  have hw : w.weights ≠ 0 := by
    intro hw_zero
    have : (0 : 𝕜) = 1 := by
      simpa [hw_zero] using w.total
    exact zero_ne_one this
  obtain ⟨i, _hi⟩ := Finsupp.support_nonempty_iff.2 hw
  exact ⟨i⟩

/-- Theorem 3.1, owner form: if `x` is a convex combination of `points` and all those points lie in
`C`, then a convex function on `C` takes at `x` a value bounded above by one of the endpoint
values. -/
theorem convexOn_exists_ge_of_convex_combination
    {C : Set E} {f : E → β} (hf : ConvexOn 𝕜 C f) {points : ι → E} {x : E}
    (hx : is_convex_combination_of 𝕜 points x) (hpoints : Set.range points ⊆ C) :
    ∃ i, f x ≤ f (points i) := by
  obtain ⟨y, hy, hxy⟩ := hf.exists_ge_of_mem_convexHull hpoints hx.mem_convexHull
  rcases hy with ⟨i, rfl⟩
  exact ⟨i, hxy⟩

/-- Theorem 3.1: if `x` is a convex combination of a finite family `points` contained in `C`,
then a convex function on `C` takes at `x` a value bounded above by the maximum of its values on
that family. -/
theorem convexOn_value_le_max_of_convex_combination
    [Fintype ι] {C : Set E} {f : E → β} (hf : ConvexOn 𝕜 C f) {points : ι → E} {x : E}
    (hx : is_convex_combination_of 𝕜 points x) (hpoints : ∀ i, points i ∈ C) :
    letI : Nonempty ι := hx.nonempty
    f x ≤ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ f (points i)) := by
  letI : Nonempty ι := hx.nonempty
  obtain ⟨i, hi_le⟩ := convexOn_exists_ge_of_convex_combination hf hx <| by
    rintro _ ⟨j, rfl⟩
    exact hpoints j
  exact hi_le.trans <| Finset.le_sup' (fun j ↦ f (points j)) (Finset.mem_univ i)

section Coefficients

variable [Fintype ι]
variable {C : Set E} {f : E → β} {points : ι → E}

/-- A finite coefficient family with total mass `1` has a nonempty nonzero support. -/
theorem nonzeroWeightSupport_nonempty (α : ι → 𝕜) (hαsum : ∑ i, α i = 1) :
    (Finset.univ.filter fun i ↦ α i ≠ 0).Nonempty := by
  refine Finset.nonempty_iff_ne_empty.mpr ?_
  intro hzero
  have hsum_zero : ∑ i, α i = 0 := by
    rw [← Finset.sum_filter_ne_zero]
    simp [hzero]
  exact one_ne_zero <| by rw [← hαsum, hsum_zero]

/-- Theorem 3.1, coefficient form: a weighted sum with nonnegative coefficients summing to `1`
is bounded above by the maximum of the endpoint values on the nonzero-weight support. -/
theorem convexOn_value_le_max_of_convex_combination_of_coefficients
    (hf : ConvexOn 𝕜 C f) (α : ι → 𝕜)
    (hαnonneg : ∀ i, 0 ≤ α i)
    (hαsum : ∑ i, α i = 1) (hpoints : ∀ i, α i ≠ 0 → points i ∈ C) :
    f (∑ i, α i • points i) ≤
      (Finset.univ.filter fun i ↦ α i ≠ 0).sup'
        (nonzeroWeightSupport_nonempty α hαsum) (fun i ↦ f (points i)) := by
  let w : StdSimplex 𝕜 ι :=
    ⟨Finsupp.equivFunOnFinite.symm α,
      by simpa using hαnonneg,
      by simpa using (Finsupp.equivFunOnFinite_symm_sum α).trans hαsum⟩
  let s := w.weights.support
  have hsupport : w.weights.support = Finset.univ.filter fun i ↦ α i ≠ 0 := by
    ext i
    simp [w]
  have hsum : ∑ i ∈ s, w.weights i = 1 := by
    simpa [s, Finsupp.sum] using w.total
  have hpos : 0 < ∑ i ∈ s, w.weights i := by
    rw [hsum]
    exact zero_lt_one
  have h :
      ∃ i ∈ s, f (convexCombination (w.map points)) ≤ f (points i) := by
    have hcenter :
        ∃ i ∈ s, f (s.centerMass w.weights points) ≤ f (points i) := by
      simpa [s] using
        (hf.exists_ge_of_centerMass
          (fun i _ ↦ w.nonneg i)
          hpos
          (fun i hi ↦
            hpoints i <| by
              have hi' : w.weights i ≠ 0 := by
                simpa [s, Finsupp.mem_support_iff] using hi
              simpa [w] using hi'))
    rcases hcenter with ⟨i, hi, hi_le⟩
    have hcomb : s.centerMass w.weights points = convexCombination (w.map points) := by
      have hs_center : s.centerMass w.weights points = ∑ i ∈ s, w.weights i • points i := by
        rw [Finset.centerMass, hsum]
        simp
      calc
        s.centerMass w.weights points = ∑ i ∈ s, w.weights i • points i :=
          hs_center
        _ = convexCombination (w.map points) := by
          rw [convexCombination_eq_sum, StdSimplex.map]
          rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ add_smul _ _ _)]
          rfl
    exact ⟨i, hi, by simpa [hcomb] using hi_le⟩
  obtain ⟨i, hi, hi_le⟩ := h
  have hmax :
      f (convexCombination (w.map points)) ≤ s.sup' ⟨i, hi⟩ (fun j ↦ f (points j)) :=
    hi_le.trans <| Finset.le_sup' (fun j ↦ f (points j)) hi
  rw [StdSimplex.convexCombination_map_eq_sum 𝕜 w points] at hmax
  simpa [s, hsupport] using hmax

end Coefficients
