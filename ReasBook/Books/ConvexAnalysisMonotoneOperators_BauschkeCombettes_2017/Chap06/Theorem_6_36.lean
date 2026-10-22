/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_32

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Set

section

variable {ι : Type v} {𝓗 : Type u}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

local notation "polarDual" => PointedCone.dual (-innerₗ 𝓗)

private theorem polarCone_eq_polarDual (C : Set 𝓗) :
    Cᵒ⊖ = (polarDual C : Set 𝓗) := by
  ext x
  simp [Set.mem_polarCone_iff_forall_inner_nonpos]

/-- Helper for Theorem 6.36: the pointed cone hull of a finite family is a proper cone because
Proposition 6.8 gives closedness. -/
private def finite_pointedConeHull_as_properCone
    (s : Finset ι) (u : ι → 𝓗) : ProperCone ℝ 𝓗 :=
  { toSubmodule := PointedCone.hull ℝ (u '' (s : Set ι))
    isClosed' := isClosed_pointedConeHull_image_finset s u }

/-- Theorem 6.36: for a finite family `(uᵢ)` indexed by a finite type `ι`,
membership of `v` in the cone `∑ i, ℝ₊ uᵢ`, represented in Lean by
`PointedCone.hull ℝ (range u)`, is equivalent to the
containment `⋂ i, ({uᵢ}ᵒ⊖) ⊆ ({v}ᵒ⊖)`. -/
theorem mem_pointedConeHull_range_iff_iInter_polarCone_singleton_subset
    (hι : Finite ι) {u : ι → 𝓗} {v : 𝓗} :
    v ∈ (PointedCone.hull ℝ (range u) : Set 𝓗) ↔
      (⋂ i, ({u i} : Set 𝓗)ᵒ⊖) ⊆ ({v} : Set 𝓗)ᵒ⊖ := by
  classical
  letI : Finite ι := hι
  letI := Fintype.ofFinite ι
  let U : Submodule ℝ 𝓗 := Submodule.span ℝ (insert v (Set.range u))
  letI : FiniteDimensional ℝ ↥U := by
    dsimp [U]
    exact FiniteDimensional.span_of_finite (K := ℝ) ((Set.finite_range u).insert v)
  letI : NormedAddCommGroup ↥U := inferInstance
  letI : NormedSpace ℝ ↥U := inferInstance
  letI : InnerProductSpace ℝ ↥U := inferInstance
  letI : ProperSpace ↥U := FiniteDimensional.proper ℝ ↥U
  letI : CompleteSpace ↥U := inferInstance
  let uW : ι → ↥U := fun i ↦
    ⟨u i, by
      dsimp [U]
      exact Submodule.subset_span (Set.mem_insert_of_mem v (Set.mem_range_self i))⟩
  let vW : ↥U := ⟨v, by
    dsimp [U]
    exact Submodule.subset_span (by simp)⟩
  let K : ProperCone ℝ ↥U := finite_pointedConeHull_as_properCone (s := Finset.univ) uW
  have hcoeff :
      v ∈ (PointedCone.hull ℝ (Set.range u) : Set 𝓗) ↔
        ∃ a : ι → NNReal, ∑ i, (a i : ℝ) • u i = v := by
    -- Rewrite cone membership through the explicit finite conical-combination formula.
    simpa [Set.image_univ] using
      (mem_pointedConeHull_image_finset_iff
        (s := (Finset.univ : Finset ι)) (x := u) (y := v))
  have hcoeffW :
      vW ∈ (PointedCone.hull ℝ (Set.range uW) : Set ↥U) ↔
        ∃ a : ι → NNReal, ∑ i, (a i : ℝ) • uW i = vW := by
    -- The same coefficient description holds in the finite-dimensional span `W`.
    simpa [Set.image_univ] using
      (mem_pointedConeHull_image_finset_iff
        (s := (Finset.univ : Finset ι)) (x := uW) (y := vW))
  have hlift :
      v ∈ (PointedCone.hull ℝ (Set.range u) : Set 𝓗) ↔
        vW ∈ (PointedCone.hull ℝ (Set.range uW) : Set ↥U) := by
    constructor
    · intro hv
      rcases hcoeff.mp hv with ⟨a, ha⟩
      -- Coefficient representations lift verbatim to the finite-dimensional span.
      refine hcoeffW.mpr ⟨a, ?_⟩
      apply Subtype.ext
      change (Submodule.subtype U) (∑ i, (a i : ℝ) • uW i) = v
      rw [map_sum]
      simpa [uW] using ha
    · intro hv
      rcases hcoeffW.mp hv with ⟨a, ha⟩
      -- Forgetting back to the ambient space recovers the original conical combination.
      refine hcoeff.mpr ⟨a, ?_⟩
      have ha' := congrArg (Submodule.subtype U) ha
      simpa [uW, vW, map_sum] using ha'
  constructor
  · intro hv
    rcases hcoeff.mp hv with ⟨a, ha⟩
    intro x hx
    rw [Set.mem_polarCone_iff_forall_inner_nonpos]
    have hx_singleton (i : ι) : inner (𝕜 := ℝ) (u i) x ≤ 0 := by
      have hxi : x ∈ ({u i} : Set 𝓗)ᵒ⊖ := (Set.mem_iInter.mp hx) i
      exact
        (Set.mem_polarCone_iff_forall_inner_nonpos.mp hxi) (u i) (by simp)
    -- Evaluate the candidate polar vector on the conical-combination formula for `v`.
    have hinner_vx : inner (𝕜 := ℝ) v x ≤ 0 := by
      calc
        inner (𝕜 := ℝ) v x = inner (𝕜 := ℝ) (∑ i, (a i : ℝ) • u i) x := by
          rw [← ha]
        _ = ∑ i, inner (𝕜 := ℝ) ((a i : ℝ) • u i) x := by
          simpa using
            (sum_inner (s := (Finset.univ : Finset ι))
              (f := fun i ↦ (a i : ℝ) • u i) x)
        _ ≤ ∑ i, 0 := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hai : 0 ≤ (a i : ℝ) := by exact_mod_cast (a i).2
              simpa [real_inner_smul_left] using
                mul_le_mul_of_nonneg_left (hx_singleton i) hai
        _ = 0 := by simp
    simpa using hinner_vx
  · intro hsubset
    have hComplete : CompleteSpace ↥U := by infer_instance
    letI : CompleteSpace ↥U := hComplete
    let hcheb : IsChebyshev (K : Set ↥U) :=
      @properConeProjectionChebyshev ↥U _ _ hComplete K
    let p : ↥U :=
      projectionPoint (K : Set ↥U) hcheb vW
    let r : ↥U := vW - p
    have hr_polar : r ∈ (K : Set ↥U)ᵒ⊖ := by
      -- Proposition 6.28 identifies the projection residual with a vector in the polar cone.
      simpa [p, r] using
        (@sub_mem_polarCone_of_eq_projectionPoint_on_properCone
          ↥U _ _ hComplete K (x := vW) (p := p) rfl)
    have hr_inter : (r : 𝓗) ∈ ⋂ i, ({u i} : Set 𝓗)ᵒ⊖ := by
      -- Every generator `u i` belongs to the cone `K`, so the residual lies in each singleton
      -- polar cone.
      rw [Set.mem_iInter]
      intro i
      rw [Set.mem_polarCone_iff_forall_inner_nonpos]
      intro y hy
      have huiK : uW i ∈ K := by
        simpa [K, finite_pointedConeHull_as_properCone, Set.image_univ] using
          (PointedCone.subset_hull (R := ℝ) (s := Set.range uW) (by
            exact Set.mem_range_self i))
      rcases Set.mem_singleton_iff.mp hy with rfl
      simpa [uW, r] using
        (Set.mem_polarCone_iff_forall_inner_nonpos.mp hr_polar) (uW i) huiK
    have hrv : (r : 𝓗) ∈ ({v} : Set 𝓗)ᵒ⊖ := hsubset hr_inter
    have hinner : inner (𝕜 := ℝ) vW (vW - p) ≤ 0 := by
      -- Feed the residual into the assumed singleton-polar inclusion.
      simpa [vW, p, r] using
        (Set.mem_polarCone_iff_forall_inner_nonpos.mp hrv) v (by simp)
    have hvW_mem : vW ∈ K := by
      -- Proposition 6.32 closes the source proof inside the finite-dimensional span `W`.
      simpa [p, hcheb] using
        (@mem_of_inner_sub_projectionPoint_nonpos_of_properCone
          ↥U _ _ hComplete K vW hinner)
    -- Forget the finite-dimensional embedding to recover ambient membership.
    exact hlift.mpr <| by
      simpa [K, finite_pointedConeHull_as_properCone, Set.image_univ] using hvW_mem

-- Proof sketch: specialize Theorem 6.36 to the finite subtype `s`, then rewrite `range` on that
-- subtype back to the image `u '' ↑s`.
/-- Finite-family cone membership in canonical owner form: a vector belongs to the pointed cone
generated by `u '' ↑s` if and only if the intersection of the polar cones of the singleton
generators is contained in the polar cone of the singleton `{v}`. -/
theorem mem_pointedConeHull_image_finset_iff_iInter_polarCone_singleton_subset
    {s : Finset ι} {u : ι → 𝓗} {v : 𝓗} :
    v ∈ (PointedCone.hull ℝ (u '' (s : Set ι)) : Set 𝓗) ↔
      (⋂ i ∈ s, ({u i} : Set 𝓗)ᵒ⊖) ⊆ ({v} : Set 𝓗)ᵒ⊖ := by
  classical
  let uS : s → 𝓗 := fun i ↦ u i
  have himage : Set.range uS = u '' (s : Set ι) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hiInter :
      (⋂ i : s, ({uS i} : Set 𝓗)ᵒ⊖) = ⋂ i ∈ s, ({u i} : Set 𝓗)ᵒ⊖ := by
    ext x
    simp [uS]
  -- Specialize the finite-type theorem to the subtype of indices lying in `s`.
  simpa [Set.image_univ, himage, hiInter] using
    (mem_pointedConeHull_range_iff_iInter_polarCone_singleton_subset
      (ι := s) (𝓗 := 𝓗) (hι := inferInstance) (u := uS) (v := v))

-- Internal finite-duality bridge: once the public finite-family theorem is available, the private
-- double-dual identity is exactly its pointwise reformulation.
/-- Helper for Theorem 6.36: the finite pointed cone hull is the double dual of the finite family
for the negative inner-product pairing. -/
private theorem pointedConeHull_image_finset_eq_polarDual_polarDual
    {s : Finset ι} (u : ι → 𝓗) :
    (polarDual (polarDual (u '' (s : Set ι))) : Set 𝓗) =
      PointedCone.hull ℝ (u '' (s : Set ι)) := by
  ext x
  -- Rewrite double-dual membership as the singleton-polar containment from the public theorem.
  rw [mem_pointedConeHull_image_finset_iff_iInter_polarCone_singleton_subset
    (s := s) (u := u) (v := x)]
  rw [polarCone_eq_polarDual ({x} : Set 𝓗)]
  simp [polarCone_eq_polarDual, PointedCone.mem_dual, Set.subset_def, real_inner_comm]

end

end Set
