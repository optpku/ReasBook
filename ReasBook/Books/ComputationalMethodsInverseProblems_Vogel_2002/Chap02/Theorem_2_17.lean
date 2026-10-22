/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_17.Pseudoinverse

public section

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Helper for Theorem 2.17: a least-squares solution is characterized by orthogonality of its
residual to `K.range`. -/
lemma isLeastSquaresSolution_iff_residual_mem_rangeOrthogonal
    (K : H₁ →L[𝕜] H₂) (g : H₂) (f : H₁) :
    K.IsLeastSquaresSolution g f ↔ g - K f ∈ K.rangeᗮ := by
  constructor
  · intro hls
    rw [Submodule.mem_orthogonal']
    intro y hy
    -- Rewrite least-squares optimality as the formula for the distance to `K.range`.
    have hresidual_eq : ‖g - K f‖ = ⨅ s : K.range, ‖g - s‖ := by
      rw [K.isLeastSquaresSolution_iff] at hls
      refine le_antisymm ?_ ?_
      · refine le_ciInf fun s ↦ ?_
        rcases s with ⟨s, ⟨h, rfl⟩⟩
        simpa [norm_sub_rev] using hls h
      · have hbdd : BddBelow (Set.range fun s : K.range ↦ ‖g - s‖) := by
          refine ⟨0, ?_⟩
          rintro _ ⟨s, rfl⟩
          exact norm_nonneg _
        exact ciInf_le hbdd ⟨K f, ⟨f, rfl⟩⟩
    exact
      ((K.range.norm_eq_iInf_iff_inner_eq_zero (show K f ∈ K.range from ⟨f, rfl⟩)).1
        hresidual_eq) y hy
  · intro horth
    rw [K.isLeastSquaresSolution_iff]
    intro h
    -- Recover the best-approximation value from the orthogonality hypothesis.
    have hresidual_eq : ‖g - K f‖ = ⨅ s : K.range, ‖g - s‖ := by
      exact
        ((K.range.norm_eq_iInf_iff_inner_eq_zero (show K f ∈ K.range from ⟨f, rfl⟩)).2
          ((Submodule.mem_orthogonal' _ _).1 horth))
    have hbdd : BddBelow (Set.range fun s : K.range ↦ ‖g - s‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact norm_nonneg _
    calc
      ‖K f - g‖ = ‖g - K f‖ := by rw [norm_sub_rev]
      _ = ⨅ s : K.range, ‖g - s‖ := hresidual_eq
      _ ≤ ‖g - K h‖ := ciInf_le hbdd ⟨K h, ⟨h, rfl⟩⟩
      _ = ‖K h - g‖ := by rw [norm_sub_rev]

omit [CompleteSpace H₂] in
/-- Helper for Theorem 2.17: a least-squares minimum-norm solution lies in `K.kerᗮ`. -/
lemma leastSquaresMinimumNormSolution_mem_kerOrthogonal
    (K : H₁ →L[𝕜] H₂) {g : H₂} {f : H₁}
    (hmin : K.IsLeastSquaresMinimumNormSolution g f) :
    f ∈ K.kerᗮ := by
  rw [K.isLeastSquaresMinimumNormSolution_iff] at hmin
  rcases hmin with ⟨hls, hnorm⟩
  -- Project `f` to `K.kerᗮ`; the kernel component is annihilated by `K`.
  have hmap_projection : K (K.kerᗮ.starProjection f) = K f := by
    calc
      K (K.kerᗮ.starProjection f) = K (f - K.ker.starProjection f) := by
        simp [Submodule.starProjection_orthogonal_val]
      _ = K f - K (K.ker.starProjection f) := by rw [map_sub]
      _ = K f := by
        have hker_projection : K (K.ker.starProjection f) = 0 := by
          exact
            LinearMap.mem_ker.mp
              (show K.ker.starProjection f ∈ K.ker from
                Submodule.coe_mem (K.ker.orthogonalProjectionOnto f))
        simp [hker_projection]
  have hls_projection : K.IsLeastSquaresSolution g (K.kerᗮ.starProjection f) := by
    -- The projected vector has the same residual, so it is still least-squares.
    rw [K.isLeastSquaresSolution_iff] at hls ⊢
    intro h
    rw [hmap_projection]
    exact hls h
  have hnorm_projection : ‖f‖ ≤ ‖K.kerᗮ.starProjection f‖ := hnorm _ hls_projection
  have hprojection_norm_le : ‖K.kerᗮ.starProjection f‖ ≤ ‖f‖ :=
    K.kerᗮ.norm_starProjection_apply_le f
  exact
    (Submodule.mem_iff_norm_starProjection (U := K.kerᗮ) f).2
      (le_antisymm hprojection_norm_le hnorm_projection)

omit [CompleteSpace H₂] in
/-- Theorem 2.17 (1). A least-squares minimum-norm solution is exactly the inverse image of the
range component of `g` under `ContinuousLinearMap.kerOrthogonalEquivRange`. -/
theorem leastSquaresMinimumNormSolution_iff_exists_rangeComponent
    (K : H₁ →L[𝕜] H₂) {g : H₂} {f : H₁} :
    K.IsLeastSquaresMinimumNormSolution g f ↔
      ∃ y : K.range, g - y ∈ K.rangeᗮ ∧ f = (K.kerOrthogonalEquivRange.symm y : H₁) := by
  constructor
  · intro hmin
    -- The least-squares residual gives the orthogonal range component of `g`.
    have hls : K.IsLeastSquaresSolution g f := hmin.leastSquares
    have hresidual : g - K f ∈ K.rangeᗮ :=
      (K.isLeastSquaresSolution_iff_residual_mem_rangeOrthogonal g f).1 hls
    have hfker : f ∈ K.kerᗮ :=
      K.leastSquaresMinimumNormSolution_mem_kerOrthogonal hmin
    let y : K.range := ⟨K f, ⟨f, rfl⟩⟩
    have hy_eq : K.kerOrthogonalEquivRange ⟨f, hfker⟩ = y := by
      ext
      simp [y, K.kerOrthogonalEquivRange_apply]
    have hsymm : K.kerOrthogonalEquivRange.symm y = ⟨f, hfker⟩ := by
      simpa using (congrArg K.kerOrthogonalEquivRange.symm hy_eq).symm
    refine ⟨y, ?_, ?_⟩
    · simpa [y] using hresidual
    · simpa using (congrArg (fun x : K.kerᗮ ↦ (x : H₁)) hsymm).symm
  · rintro ⟨y, hresidual, hf_eq⟩
    -- Recover the least-squares property from the orthogonal decomposition of `g`.
    have hfker : f ∈ K.kerᗮ := by
      rw [hf_eq]
      exact (K.kerOrthogonalEquivRange.symm y).property
    have hKf : K f = y := by
      have hrestrict :
          K.kerOrthogonalRangeRestrict (K.kerOrthogonalEquivRange.symm y) = y :=
        K.kerOrthogonalEquivRange_symm_apply y
      have hmap :
          K (((K.kerOrthogonalEquivRange.symm y : K.kerᗮ) : H₁)) = (y : H₂) := by
        simpa using congrArg (fun z : K.range ↦ (z : H₂)) hrestrict
      simpa [hf_eq] using hmap
    have hls_f : K.IsLeastSquaresSolution g f := by
      refine (K.isLeastSquaresSolution_iff_residual_mem_rangeOrthogonal g f).2 ?_
      simpa [hKf] using hresidual
    refine ⟨hls_f, ?_⟩
    intro h hh
    -- Any least-squares competitor has the same range image `y`, hence differs from `f` by
    -- a kernel vector and cannot have smaller norm than the projection onto `K.kerᗮ`.
    have hh_residual : g - K h ∈ K.rangeᗮ :=
      (K.isLeastSquaresSolution_iff_residual_mem_rangeOrthogonal g h).1 hh
    have horth_diff : y - K h ∈ K.rangeᗮ := by
      have hsub : (g - K h) - (g - y) ∈ K.rangeᗮ :=
        Submodule.sub_mem _ hh_residual hresidual
      simpa [sub_sub_sub_cancel_left] using hsub
    have hrange_diff : y - K h ∈ K.range := by
      exact K.range.sub_mem y.property ⟨h, rfl⟩
    have hzero : y - K h = 0 := by
      rw [Submodule.mem_orthogonal'] at horth_diff
      exact inner_self_eq_zero.mp (horth_diff _ hrange_diff)
    have hKh : K h = y := (sub_eq_zero.mp hzero).symm
    have hkernel : h - f ∈ K.ker := by
      rw [LinearMap.mem_ker, map_sub]
      simp [hKh, hKf]
    have hprojection : K.kerᗮ.starProjection h = f := by
      apply Submodule.eq_starProjection_of_mem_orthogonal (K := K.kerᗮ)
      · exact hfker
      · exact K.ker.le_orthogonal_orthogonal hkernel
    calc
      ‖f‖ = ‖K.kerᗮ.starProjection h‖ := by rw [hprojection]
      _ ≤ ‖h‖ := K.kerᗮ.norm_starProjection_apply_le h

/-- Theorem 2.17 (2). A bounded operator selecting the least-squares minimum-norm solution for
every datum exists exactly when `K.range` is closed. In the closed-range direction, the canonical
witness is `ContinuousLinearMap.pseudoInverseOfClosedRange`. -/
theorem exists_bounded_pseudoInverse_iff_isClosed_range
    (K : H₁ →L[𝕜] H₂) :
    (∃ T : H₂ →L[𝕜] H₁, ∀ g : H₂, K.IsLeastSquaresMinimumNormSolution g (T g)) ↔
      IsClosed (Set.range K) := by
  constructor
  · rintro ⟨T, hT⟩
    let P : H₂ →L[𝕜] H₂ := K.comp T
    have hfix_range : ∀ y : H₂, y ∈ K.range → P y = y := by
      intro y hy
      -- The selector theorem forces `P` to fix each vector already in `K.range`.
      rcases (K.leastSquaresMinimumNormSolution_iff_exists_rangeComponent
          (g := y) (f := T y)).1 (hT y) with ⟨yr, hy_residual, hTy⟩
      have hy_minus_yr_range : y - yr ∈ K.range := K.range.sub_mem hy yr.property
      have hy_minus_yr_zero : y - yr = 0 := by
        rw [Submodule.mem_orthogonal'] at hy_residual
        exact inner_self_eq_zero.mp (hy_residual _ hy_minus_yr_range)
      have hyr_eq : yr = ⟨y, hy⟩ := by
        ext
        exact (sub_eq_zero.mp hy_minus_yr_zero).symm
      have hmap_Ty : K (T y) = yr := by
        have hrestrict :
            K.kerOrthogonalRangeRestrict (K.kerOrthogonalEquivRange.symm yr) = yr :=
          K.kerOrthogonalEquivRange_symm_apply yr
        have hmap :
            K (((K.kerOrthogonalEquivRange.symm yr : K.kerᗮ) : H₁)) = (yr : H₂) := by
          simpa using congrArg (fun z : K.range ↦ (z : H₂)) hrestrict
        simpa [hTy] using hmap
      simpa [P, hyr_eq] using hmap_Ty
    have hP_idem : IsIdempotentElem P := by
      -- Idempotence follows because `P g` always lies in `K.range`, where `P` acts as the identity.
      change P.comp P = P
      ext g
      exact hfix_range (P g) ⟨T g, by simp [P]⟩
    have hclosedP : IsClosed (((P.range : Submodule 𝕜 H₂) : Set H₂)) :=
      ContinuousLinearMap.IsIdempotentElem.isClosed_range hP_idem
    have hrange_eq : (((P.range : Submodule 𝕜 H₂) : Set H₂)) = Set.range K := by
      ext y
      change y ∈ Set.range P ↔ y ∈ Set.range K
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨T g, by simp [P]⟩
      · rintro ⟨f, rfl⟩
        exact ⟨K f, hfix_range (K f) ⟨f, rfl⟩⟩
    simpa [hrange_eq] using hclosedP
  · intro hclosed
    exact
      ⟨K.pseudoInverseOfClosedRange hclosed,
        K.isLeastSquaresMinimumNormSolution_pseudoInverseOfClosedRange hclosed⟩

/-- If `K.range` is closed, the canonical bounded selector of least-squares minimum-norm
solutions is `ContinuousLinearMap.pseudoInverseOfClosedRange`. -/
theorem exists_bounded_pseudoInverse_of_isClosed_range
    (K : H₁ →L[𝕜] H₂) (hclosed : IsClosed (Set.range K)) :
    ∃ T : H₂ →L[𝕜] H₁, ∀ g : H₂, K.IsLeastSquaresMinimumNormSolution g (T g) := by
  exact
    ⟨K.pseudoInverseOfClosedRange hclosed,
      K.isLeastSquaresMinimumNormSolution_pseudoInverseOfClosedRange hclosed⟩

/-- If `K.range` is closed, then every datum admits a least-squares minimum-norm solution,
canonically given by `ContinuousLinearMap.pseudoInverseOfClosedRange`. -/
theorem exists_leastSquaresMinimumNormSolution_of_isClosed_range
    (K : H₁ →L[𝕜] H₂) (hclosed : IsClosed (Set.range K)) (g : H₂) :
    ∃ f : H₁, K.IsLeastSquaresMinimumNormSolution g f := by
  exact
    ⟨K.pseudoInverseOfClosedRange hclosed g,
      K.isLeastSquaresMinimumNormSolution_pseudoInverseOfClosedRange hclosed g⟩

end ContinuousLinearMap
