/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_16.MinimumNorm
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Operator.Banach

public section

noncomputable section

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- Restrict `K` to `K.kerᗮ` and reinterpret the codomain inside `K.range`. -/
@[expose]
def kerOrthogonalRangeRestrict (K : H₁ →L[𝕜] H₂) : K.kerᗮ →L[𝕜] K.range :=
  K.rangeRestrict.comp K.kerᗮ.subtypeL

section

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-
`kerOrthogonalRangeRestrict` acts by applying `K` and then reinterpreting the value in
`K.range`.
-/
theorem kerOrthogonalRangeRestrict_apply
    (K : H₁ →L[𝕜] H₂) (x : K.kerᗮ) :
    (K.kerOrthogonalRangeRestrict x : H₂) = K x :=
  by
    simp [kerOrthogonalRangeRestrict]

attribute [simp] kerOrthogonalRangeRestrict_apply

end

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Helper for Theorem 2.17: the restriction of `K` to `K.kerᗮ` is injective. -/
theorem kerOrthogonalRangeRestrict_ker_eq_bot
    (K : H₁ →L[𝕜] H₂) :
    K.kerOrthogonalRangeRestrict.ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  have hxy_map : K (x : H₁) = K (y : H₁) := by
    simpa [kerOrthogonalRangeRestrict_apply] using
      congrArg (fun z : K.range ↦ (z : H₂)) hxy
  have hsub : K.kerOrthogonalRangeRestrict (x - y) = 0 := by
    ext
    simp [kerOrthogonalRangeRestrict_apply, hxy_map]
  have hsub_map : K ((x - y : K.kerᗮ) : H₁) = 0 := by
    simpa using congrArg (fun z : K.range ↦ (z : H₂)) hsub
  have hsub_mem :
      (((x - y : K.kerᗮ) : H₁) ∈ (K.ker ⊓ K.kerᗮ : Submodule 𝕜 H₁)) :=
    ⟨LinearMap.mem_ker.mpr hsub_map, (x - y).property⟩
  have hsub_bot : (((x - y : K.kerᗮ) : H₁) ∈ (⊥ : Submodule 𝕜 H₁)) := by
    simpa [(Submodule.orthogonal_disjoint K.ker).eq_bot] using hsub_mem
  have hsub_zero : (x - y : K.kerᗮ) = 0 := by
    ext
    simpa using hsub_bot
  exact sub_eq_zero.mp hsub_zero

omit [CompleteSpace H₂] in
/-- Helper for Theorem 2.17: `K` maps `K.kerᗮ` onto `K.range`. -/
theorem kerOrthogonalRangeRestrict_range_eq_top
    (K : H₁ →L[𝕜] H₂) :
    K.kerOrthogonalRangeRestrict.range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  rcases y.property with ⟨x, hx⟩
  refine ⟨⟨x - K.ker.starProjection x, K.ker.sub_starProjection_mem_orthogonal x⟩, ?_⟩
  ext
  calc
    (K.kerOrthogonalRangeRestrict
        ⟨x - K.ker.starProjection x, K.ker.sub_starProjection_mem_orthogonal x⟩ : H₂)
        = K (x - K.ker.starProjection x) := by
            simp
    _ = K x - K (K.ker.starProjection x) := by
          rw [map_sub]
    _ = K x := by
          have hproj : K (K.ker.starProjection x) = 0 := by
            exact LinearMap.mem_ker.mp (K.ker.starProjection_apply_mem x)
          simp [hproj]
    _ = y := by
          exact hx

omit [CompleteSpace H₂] in
/-- Helper for Theorem 2.17: `K` gives a bijection from `K.kerᗮ` onto `K.range`. -/
theorem kerOrthogonalRangeRestrict_bijective
    (K : H₁ →L[𝕜] H₂) :
    Function.Bijective K.kerOrthogonalRangeRestrict :=
  ⟨LinearMap.ker_eq_bot.1 (K.kerOrthogonalRangeRestrict_ker_eq_bot),
    LinearMap.range_eq_top.1 (K.kerOrthogonalRangeRestrict_range_eq_top)⟩

/-- Helper for Theorem 2.17: when `K.range` is complete, the restriction of `K` to `K.kerᗮ`
is a continuous linear equivalence onto `K.range`. -/
noncomputable def kerOrthogonalRangeContinuousEquiv
    (K : H₁ →L[𝕜] H₂) [CompleteSpace K.range] :
    K.kerᗮ ≃L[𝕜] K.range :=
  ContinuousLinearEquiv.ofBijective K.kerOrthogonalRangeRestrict
    (K.kerOrthogonalRangeRestrict_ker_eq_bot)
    (K.kerOrthogonalRangeRestrict_range_eq_top)

/-- The operator `K` identifies `K.kerᗮ` with its range. -/
@[expose]
noncomputable def kerOrthogonalEquivRange (K : H₁ →L[𝕜] H₂) : K.kerᗮ ≃ₗ[𝕜] K.range :=
  LinearEquiv.ofBijective K.kerOrthogonalRangeRestrict
    (kerOrthogonalRangeRestrict_bijective K)

omit [CompleteSpace H₂] in
/-- `kerOrthogonalEquivRange` acts by applying `K` on `K.kerᗮ`. -/
theorem kerOrthogonalEquivRange_apply
    (K : H₁ →L[𝕜] H₂) (x : K.kerᗮ) :
    K.kerOrthogonalEquivRange x = K.kerOrthogonalRangeRestrict x := by
  simp [kerOrthogonalEquivRange]

omit [CompleteSpace H₂] in
/-- Applying the restricted map to the inverse image recovers the original element of `K.range`. -/
theorem kerOrthogonalEquivRange_symm_apply
    (K : H₁ →L[𝕜] H₂) (y : K.range) :
    K.kerOrthogonalRangeRestrict (K.kerOrthogonalEquivRange.symm y) = y := by
  simpa [K.kerOrthogonalEquivRange_apply] using K.kerOrthogonalEquivRange.apply_symm_apply y

/-- The bounded pseudoinverse obtained by inverting `K` on `K.kerᗮ` and annihilating
`K.rangeᗮ`. -/
@[expose]
noncomputable def pseudoInverse (K : H₁ →L[𝕜] H₂) [CompleteSpace K.range] : H₂ →L[𝕜] H₁ :=
  (K.kerᗮ : Submodule 𝕜 H₁).subtypeL.comp
    ((kerOrthogonalRangeContinuousEquiv K).symm.toContinuousLinearMap.comp
      K.range.orthogonalProjectionOnto)

omit [CompleteSpace H₂] in
/-- Helper for Theorem 2.17: `K.pseudoInverse` applies the inverse of
`kerOrthogonalRangeContinuousEquiv K` to the orthogonal projection onto `K.range`. -/
theorem pseudoInverse_apply
    (K : H₁ →L[𝕜] H₂) [CompleteSpace K.range] (g : H₂) :
    K.pseudoInverse g =
      (((kerOrthogonalRangeContinuousEquiv K).symm (K.range.orthogonalProjectionOnto g) :
        K.kerᗮ) : H₁) :=
  rfl

omit [CompleteSpace H₂] in
/-- Helper for Theorem 2.17: applying `K` to `K.pseudoInverse g` recovers the orthogonal
projection of `g` onto `K.range`. -/
private theorem map_pseudoInverse
    (K : H₁ →L[𝕜] H₂) [CompleteSpace K.range] (g : H₂) :
    K (K.pseudoInverse g) = K.range.orthogonalProjectionOnto g := by
  rw [pseudoInverse_apply]
  rw [← K.kerOrthogonalRangeRestrict_apply]
  exact congrArg (fun y : K.range ↦ (y : H₂))
    ((kerOrthogonalRangeContinuousEquiv K).apply_symm_apply (K.range.orthogonalProjectionOnto g))

omit [CompleteSpace H₂] in
/-- On `K.range`, the bounded pseudoinverse returns the inverse image in `K.kerᗮ`. -/
theorem pseudoInverse_apply_of_mem_range
    (K : H₁ →L[𝕜] H₂) [CompleteSpace K.range] {g : H₂} (hg : g ∈ K.range) :
    K.pseudoInverse g = (K.kerOrthogonalEquivRange.symm ⟨g, hg⟩ : H₁) := by
  have hproj : K.range.orthogonalProjectionOnto g = ⟨g, hg⟩ := by
    simpa using (K.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨g, hg⟩)
  have hpker : K.pseudoInverse g ∈ K.kerᗮ := by
    rw [pseudoInverse_apply]
    exact ((kerOrthogonalRangeContinuousEquiv K).symm (K.range.orthogonalProjectionOnto g)).property
  let x : K.kerᗮ := ⟨K.pseudoInverse g, hpker⟩
  have hx : K.kerOrthogonalRangeRestrict x = ⟨g, hg⟩ := by
    ext
    simpa [x, hproj] using (map_pseudoInverse K g)
  have hx_eq : x = K.kerOrthogonalEquivRange.symm ⟨g, hg⟩ := by
    apply K.kerOrthogonalEquivRange.injective
    calc
      K.kerOrthogonalRangeRestrict x = ⟨g, hg⟩ := hx
      _ = K.kerOrthogonalRangeRestrict (K.kerOrthogonalEquivRange.symm ⟨g, hg⟩) := by
            symm
            exact K.kerOrthogonalEquivRange_symm_apply ⟨g, hg⟩
  exact congrArg (fun z : K.kerᗮ ↦ (z : H₁)) hx_eq

omit [CompleteSpace H₂] in
/-- On `K.rangeᗮ`, the bounded pseudoinverse vanishes. -/
theorem pseudoInverse_apply_of_mem_orthogonal
    (K : H₁ →L[𝕜] H₂) [CompleteSpace K.range] {g : H₂} (hg : g ∈ K.rangeᗮ) :
    K.pseudoInverse g = 0 := by
  have hproj : K.range.orthogonalProjectionOnto g = 0 :=
    K.range.orthogonalProjectionOnto_apply_of_mem_orthogonal hg
  have hpker : K.pseudoInverse g ∈ K.kerᗮ := by
    rw [pseudoInverse_apply]
    exact ((kerOrthogonalRangeContinuousEquiv K).symm (K.range.orthogonalProjectionOnto g)).property
  let x : K.kerᗮ := ⟨K.pseudoInverse g, hpker⟩
  have hx : K.kerOrthogonalRangeRestrict x = 0 := by
    ext
    simpa [x, hproj] using (map_pseudoInverse K g)
  have hx_eq : x = 0 := by
    apply K.kerOrthogonalEquivRange.injective
    calc
      K.kerOrthogonalRangeRestrict x = 0 := hx
      _ = K.kerOrthogonalRangeRestrict (0 : K.kerᗮ) := by simp
  exact congrArg (fun z : K.kerᗮ ↦ (z : H₁)) hx_eq

omit [CompleteSpace H₂] in
/-- The bounded pseudoinverse selects a least-squares minimum-norm solution for each datum. -/
theorem isLeastSquaresMinimumNormSolution_pseudoInverse
    (K : H₁ →L[𝕜] H₂) [CompleteSpace K.range] (g : H₂) :
    K.IsLeastSquaresMinimumNormSolution g (K.pseudoInverse g) := by
  rw [K.isLeastSquaresMinimumNormSolution_iff]
  have hmap : K (K.pseudoInverse g) = K.range.orthogonalProjectionOnto g :=
    map_pseudoInverse K g
  have hls : K.IsLeastSquaresSolution g (K.pseudoInverse g) := by
    rw [K.isLeastSquaresSolution_iff]
    intro h
    have hbdd : BddBelow (Set.range fun s : K.range ↦ ‖g - s‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact norm_nonneg _
    calc
      ‖K (K.pseudoInverse g) - g‖ = ‖g - K.range.starProjection g‖ := by
        rw [hmap, Submodule.starProjection_apply, norm_sub_rev]
      _ = ⨅ s : K.range, ‖g - s‖ := K.range.starProjection_minimal g
      _ ≤ ‖g - (⟨K h, ⟨h, rfl⟩⟩ : K.range)‖ := by
        exact ciInf_le hbdd ⟨K h, ⟨h, rfl⟩⟩
      _ = ‖K h - g‖ := by
        rw [norm_sub_rev]
  refine ⟨hls, ?_⟩
  intro h hh
  have hpker : K.pseudoInverse g ∈ K.kerᗮ := by
    rw [pseudoInverse_apply]
    exact ((kerOrthogonalRangeContinuousEquiv K).symm (K.range.orthogonalProjectionOnto g)).property
  have hmem :
      h ∈ AffineSubspace.mk' (K.pseudoInverse g) K.ker :=
    (K.isLeastSquaresSolution_iff_mem_affineSubspace
      (g := g) (f_ls := K.pseudoInverse g) (f := h) hls).1 hh
  rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.sub_mem_ker_iff] at hmem
  have hkernel : h - K.pseudoInverse g ∈ K.ker := by
    rw [LinearMap.mem_ker, map_sub]
    simp [hmem]
  have hprojection : K.kerᗮ.starProjection h = K.pseudoInverse g := by
    apply Submodule.eq_starProjection_of_mem_orthogonal (K := K.kerᗮ)
    · exact hpker
    · exact K.ker.le_orthogonal_orthogonal hkernel
  calc
    ‖K.pseudoInverse g‖ = ‖K.kerᗮ.starProjection h‖ := by
      rw [hprojection]
    _ ≤ ‖h‖ := K.kerᗮ.norm_starProjection_apply_le h

/- A closed range makes `K.range` into a Banach space. -/
omit [CompleteSpace H₁] in
theorem completeSpaceRangeOfIsClosedRange
    (K : H₁ →L[𝕜] H₂) (hclosed : IsClosed (Set.range K)) : CompleteSpace K.range :=
  hclosed.completeSpace_coe

/-- A closed range makes `K.range` into a Banach space, so the canonical bounded pseudoinverse is
available without additional local instance setup. -/
instance instCompleteSpaceRangeOfIsClosedRange
    (K : H₁ →L[𝕜] H₂) [IsClosed (Set.range K)] : CompleteSpace K.range :=
  completeSpaceRangeOfIsClosedRange K ‹IsClosed (Set.range K)›

/-- The canonical bounded pseudoinverse specialized to the closed-range case. -/
@[expose]
noncomputable def pseudoInverseOfClosedRange
    (K : H₁ →L[𝕜] H₂) (hclosed : IsClosed (Set.range K)) : H₂ →L[𝕜] H₁ :=
  let _ : CompleteSpace K.range := completeSpaceRangeOfIsClosedRange K hclosed
  K.pseudoInverse

/-- On `K.range`, the closed-range bounded pseudoinverse returns the inverse image in `K.kerᗮ`. -/
theorem pseudoInverseOfClosedRange_apply_of_mem_range
    (K : H₁ →L[𝕜] H₂) (hclosed : IsClosed (Set.range K)) {g : H₂} (hg : g ∈ K.range) :
    K.pseudoInverseOfClosedRange hclosed g =
      (K.kerOrthogonalEquivRange.symm ⟨g, hg⟩ : H₁) := by
  let _ : CompleteSpace K.range := completeSpaceRangeOfIsClosedRange K hclosed
  simpa [pseudoInverseOfClosedRange] using
    (pseudoInverse_apply_of_mem_range (K := K) (g := g) hg)

/-- With closed range, the canonical bounded pseudoinverse selects the least-squares
minimum-norm solution for every datum. -/
theorem isLeastSquaresMinimumNormSolution_pseudoInverseOfClosedRange
    (K : H₁ →L[𝕜] H₂) (hclosed : IsClosed (Set.range K)) (g : H₂) :
    K.IsLeastSquaresMinimumNormSolution g (K.pseudoInverseOfClosedRange hclosed g) := by
  let _ : CompleteSpace K.range := completeSpaceRangeOfIsClosedRange K hclosed
  simpa [pseudoInverseOfClosedRange] using
    (isLeastSquaresMinimumNormSolution_pseudoInverse (K := K) g)

end ContinuousLinearMap
