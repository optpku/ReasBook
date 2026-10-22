/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_15
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_17.Pseudoinverse

public section

noncomputable section

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- The natural domain on which `ContinuousLinearMap.partialPseudoInverse` can be defined without
assuming `K.range` is complete. -/
private abbrev partialPseudoInverseDomain
    (K : H₁ →L[𝕜] H₂) : Submodule 𝕜 H₂ :=
  K.range ⊔ K.rangeᗮ

/-- The copy of `K.range` inside the natural domain of `K.partialPseudoInverse`. -/
private abbrev rangeInPartialPseudoInverseDomain
    (K : H₁ →L[𝕜] H₂) : Submodule 𝕜 (partialPseudoInverseDomain K) :=
  K.range.submoduleOf (partialPseudoInverseDomain K)

/-- The copy of `K.rangeᗮ` inside the natural domain of `K.partialPseudoInverse`. -/
private abbrev orthogonalInPartialPseudoInverseDomain
    (K : H₁ →L[𝕜] H₂) : Submodule 𝕜 (partialPseudoInverseDomain K) :=
  K.rangeᗮ.submoduleOf (partialPseudoInverseDomain K)

/-- Inside `K.range ⊔ K.rangeᗮ`, the range and its orthogonal complement form a direct-sum
decomposition. -/
private theorem rangeInPartialPseudoInverseDomain_isCompl
    (K : H₁ →L[𝕜] H₂) :
    IsCompl (rangeInPartialPseudoInverseDomain K) (orthogonalInPartialPseudoInverseDomain K) := by
  refine IsCompl.of_eq ?_ ?_
  · ext x
    constructor
    · intro hx
      have hx' : (x : H₂) ∈ K.range ∧ (x : H₂) ∈ K.rangeᗮ := by
        simpa [partialPseudoInverseDomain, rangeInPartialPseudoInverseDomain,
          orthogonalInPartialPseudoInverseDomain, Submodule.submoduleOf] using hx
      rcases hx' with ⟨hx_range, hx_orthogonal⟩
      have hx :
          (x : H₂) ∈ (K.range ⊓ K.rangeᗮ : Submodule 𝕜 H₂) := ⟨hx_range, hx_orthogonal⟩
      have hx_bot : (x : H₂) ∈ (⊥ : Submodule 𝕜 H₂) := by
        simpa [(Submodule.orthogonal_disjoint K.range).eq_bot] using hx
      simpa using hx_bot
    · intro hx
      have hx_zero : x = 0 := by simpa using hx
      subst x
      simp [partialPseudoInverseDomain, rangeInPartialPseudoInverseDomain,
        orthogonalInPartialPseudoInverseDomain, Submodule.submoduleOf]
  · calc
      rangeInPartialPseudoInverseDomain K ⊔ orthogonalInPartialPseudoInverseDomain K
          = (K.range ⊔ K.rangeᗮ).submoduleOf (partialPseudoInverseDomain K) := by
              symm
              exact Submodule.submoduleOf_sup_of_le le_sup_left le_sup_right
      _ = ⊤ := Submodule.submoduleOf_self (partialPseudoInverseDomain K)

/-- Project the natural domain `K.range ⊔ K.rangeᗮ` to its `K.range` summand. -/
private noncomputable def rangeProjectionOnPartialPseudoInverseDomain
    (K : H₁ →L[𝕜] H₂) : partialPseudoInverseDomain K →ₗ[𝕜] K.range :=
  let e : rangeInPartialPseudoInverseDomain K ≃ₗ[𝕜] K.range :=
    Submodule.submoduleOfEquivOfLe le_sup_left
  e.toLinearMap ∘ₗ
    (rangeInPartialPseudoInverseDomain K).projectionOnto
      (orthogonalInPartialPseudoInverseDomain K)
      (rangeInPartialPseudoInverseDomain_isCompl K)

/-- Helper for Definition 2.1.2-extra-1: the direct-sum projection on
`K.range ⊔ K.rangeᗮ` fixes vectors already lying in `K.range`. -/
private theorem rangeProjectionOnPartialPseudoInverseDomain_apply_of_mem_range
    (K : H₁ →L[𝕜] H₂) {g : H₂} (hg : g ∈ K.range) :
    K.rangeProjectionOnPartialPseudoInverseDomain ⟨g, Submodule.mem_sup_left hg⟩ = ⟨g, hg⟩ := by
  -- The domain projection keeps the range summand unchanged.
  have hx :
      (⟨g, Submodule.mem_sup_left hg⟩ : partialPseudoInverseDomain K) ∈
        rangeInPartialPseudoInverseDomain K := by
    simpa [partialPseudoInverseDomain, rangeInPartialPseudoInverseDomain, Submodule.submoduleOf]
      using hg
  unfold rangeProjectionOnPartialPseudoInverseDomain
  rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_left
    (rangeInPartialPseudoInverseDomain_isCompl K) hx]
  ext
  rfl

/-- Helper for Definition 2.1.2-extra-1: the direct-sum projection on
`K.range ⊔ K.rangeᗮ` kills vectors lying in `K.rangeᗮ`. -/
private theorem rangeProjectionOnPartialPseudoInverseDomain_apply_of_mem_orthogonal
    (K : H₁ →L[𝕜] H₂) {g : H₂} (hg : g ∈ K.rangeᗮ) :
    K.rangeProjectionOnPartialPseudoInverseDomain ⟨g, Submodule.mem_sup_right hg⟩ = 0 := by
  -- The range projection annihilates the orthogonal summand.
  have hx :
      (⟨g, Submodule.mem_sup_right hg⟩ : partialPseudoInverseDomain K) ∈
        orthogonalInPartialPseudoInverseDomain K := by
    simpa [partialPseudoInverseDomain, orthogonalInPartialPseudoInverseDomain,
      Submodule.submoduleOf] using hg
  unfold rangeProjectionOnPartialPseudoInverseDomain
  rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_right
    (rangeInPartialPseudoInverseDomain_isCompl K) hx]
  simp

variable [CompleteSpace H₁] [CompleteSpace H₂]

/-- Definition 2.1.2-extra-1 (1). The pseudo-inverse of `K` on its natural domain
`K.range ⊔ K.rangeᗮ`, with codomain `K.kerᗮ`. -/
noncomputable def partialPseudoInverse
    (K : H₁ →L[𝕜] H₂) : ((K.range ⊔ K.rangeᗮ) : Submodule 𝕜 H₂) →ₗ[𝕜] K.kerᗮ :=
  K.kerOrthogonalEquivRange.symm ∘ₗ K.rangeProjectionOnPartialPseudoInverseDomain

/-- The restriction of `K.partialPseudoInverse` to `K.range`, viewed as an `H₁`-valued linear
map. -/
@[expose]
noncomputable def partialPseudoInverseOnRange
    (K : H₁ →L[𝕜] H₂) : K.range →ₗ[𝕜] H₁ :=
  K.kerᗮ.subtype ∘ₗ (K.partialPseudoInverse ∘ₗ Submodule.inclusion le_sup_left)

/-- Helper for Definition 2.1.2-extra-1: applying `K` to `K.partialPseudoInverse g` recovers the
`K.range` component of `g`. -/
private theorem kerOrthogonalRangeRestrict_partialPseudoInverse
    (K : H₁ →L[𝕜] H₂) (g : ((K.range ⊔ K.rangeᗮ) : Submodule 𝕜 H₂)) :
    K.kerOrthogonalRangeRestrict (K.partialPseudoInverse g) =
      K.rangeProjectionOnPartialPseudoInverseDomain g := by
  -- The restricted map cancels the inverse equivalence used in the definition.
  simpa [ContinuousLinearMap.partialPseudoInverse] using
    K.kerOrthogonalEquivRange_symm_apply (K.rangeProjectionOnPartialPseudoInverseDomain g)

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Helper for Definition 2.1.2-extra-1: on the natural pseudoinverse domain, the direct-sum
projection to `K.range` agrees with the orthogonal projection in `H₂`. -/
private theorem rangeProjectionOnPartialPseudoInverseDomain_eq_orthogonalProjectionOnto
    (K : H₁ →L[𝕜] H₂) [CompleteSpace K.range]
    (g : ((K.range ⊔ K.rangeᗮ) : Submodule 𝕜 H₂)) :
    K.rangeProjectionOnPartialPseudoInverseDomain g =
      K.range.orthogonalProjectionOnto (g : H₂) := by
  -- Decompose `g` into its range and orthogonal parts and compare the two projections there.
  rcases Submodule.mem_sup.1 g.property with ⟨gr, hgr, go, hgo, hg_eq⟩
  have hdom : gr + go ∈ (K.range ⊔ K.rangeᗮ : Submodule 𝕜 H₂) := by
    exact Submodule.mem_sup.2 ⟨gr, hgr, go, hgo, rfl⟩
  have hsplit :
      (⟨gr + go, hdom⟩ :
          ((K.range ⊔ K.rangeᗮ) : Submodule 𝕜 H₂)) =
        ⟨gr, Submodule.mem_sup_left hgr⟩ + ⟨go, Submodule.mem_sup_right hgo⟩ := by
    ext
    simp
  calc
    K.rangeProjectionOnPartialPseudoInverseDomain g
        =
      K.rangeProjectionOnPartialPseudoInverseDomain
          (⟨gr + go, hdom⟩ : ((K.range ⊔ K.rangeᗮ) : Submodule 𝕜 H₂)) := by
            congr
            exact Subtype.ext hg_eq.symm
    _ = K.rangeProjectionOnPartialPseudoInverseDomain ⟨gr, Submodule.mem_sup_left hgr⟩ +
          K.rangeProjectionOnPartialPseudoInverseDomain ⟨go, Submodule.mem_sup_right hgo⟩ := by
            rw [hsplit, map_add]
    _ = ⟨gr, hgr⟩ + 0 := by
          rw [rangeProjectionOnPartialPseudoInverseDomain_apply_of_mem_range (K := K) hgr,
            rangeProjectionOnPartialPseudoInverseDomain_apply_of_mem_orthogonal (K := K) hgo]
    _ = ⟨gr, hgr⟩ := by simp
    _ = K.range.orthogonalProjectionOnto (gr + go) := by
          symm
          rw [Submodule.orthogonalProjectionOnto_apply_eq_projectionOnto, map_add,
            Submodule.projectionOnto_apply_of_mem_left K.range.isCompl_orthogonal hgr,
            Submodule.projectionOnto_apply_of_mem_right K.range.isCompl_orthogonal hgo]
          simp
    _ = K.range.orthogonalProjectionOnto (g : H₂) := by rw [hg_eq]

omit [CompleteSpace H₂] in
/-- On `K.range`, the natural-domain pseudoinverse agrees with the inverse of
`ContinuousLinearMap.kerOrthogonalEquivRange`. -/
theorem partialPseudoInverse_apply_of_mem_range
    (K : H₁ →L[𝕜] H₂) {g : H₂} (hg : g ∈ K.range) :
    K.partialPseudoInverse ⟨g, Submodule.mem_sup_left hg⟩ =
      K.kerOrthogonalEquivRange.symm ⟨g, hg⟩ := by
  -- The range projection keeps a range vector unchanged before applying the inverse equivalence.
  simpa [ContinuousLinearMap.partialPseudoInverse] using
    congrArg K.kerOrthogonalEquivRange.symm
      (rangeProjectionOnPartialPseudoInverseDomain_apply_of_mem_range K hg)

/-- On `K.range`, the restricted natural-domain pseudoinverse is the inverse of
`ContinuousLinearMap.kerOrthogonalEquivRange`, viewed in `H₁`. -/
@[simp] theorem partialPseudoInverseOnRange_apply
    (K : H₁ →L[𝕜] H₂) (g : K.range) :
    K.partialPseudoInverseOnRange g = (K.kerOrthogonalEquivRange.symm g : H₁) := by
  change ((K.partialPseudoInverse (Submodule.inclusion le_sup_left g) : K.kerᗮ) : H₁) =
      (K.kerOrthogonalEquivRange.symm g : H₁)
  have h_apply :
      K.partialPseudoInverse (Submodule.inclusion le_sup_left g) =
        K.kerOrthogonalEquivRange.symm g := by
    change K.partialPseudoInverse ⟨(g : H₂), Submodule.mem_sup_left g.property⟩ =
        K.kerOrthogonalEquivRange.symm g
    simpa using
      partialPseudoInverse_apply_of_mem_range (K := K) (g := (g : H₂)) g.property
  exact congrArg (fun x : K.kerᗮ ↦ (x : H₁))
    h_apply

omit [CompleteSpace H₂] in
/-- On `K.rangeᗮ`, the natural-domain pseudoinverse vanishes. -/
theorem partialPseudoInverse_apply_of_mem_orthogonal
    (K : H₁ →L[𝕜] H₂) {g : H₂} (hg : g ∈ K.rangeᗮ) :
    K.partialPseudoInverse ⟨g, Submodule.mem_sup_right hg⟩ = 0 := by
  -- The orthogonal component is projected away before inverting on the range.
  simpa [ContinuousLinearMap.partialPseudoInverse] using
    congrArg K.kerOrthogonalEquivRange.symm
      (rangeProjectionOnPartialPseudoInverseDomain_apply_of_mem_orthogonal K hg)

/-- Applying `K` to the natural-domain pseudoinverse recovers every datum lying in `K.range`. -/
theorem map_partialPseudoInverse_of_mem_range
    (K : H₁ →L[𝕜] H₂) {g : H₂} (hg : g ∈ K.range) :
    K ((K.partialPseudoInverse ⟨g, Submodule.mem_sup_left hg⟩ : K.kerᗮ) : H₁) = g := by
  -- Applying `K` recovers the range component selected by the direct-sum projection.
  calc
    K ((K.partialPseudoInverse ⟨g, Submodule.mem_sup_left hg⟩ : K.kerᗮ) : H₁)
      = (K.kerOrthogonalRangeRestrict
          (K.partialPseudoInverse ⟨g, Submodule.mem_sup_left hg⟩) : H₂) := by
            symm
            exact K.kerOrthogonalRangeRestrict_apply
              (K.partialPseudoInverse ⟨g, Submodule.mem_sup_left hg⟩)
    _ = (K.rangeProjectionOnPartialPseudoInverseDomain ⟨g, Submodule.mem_sup_left hg⟩ : H₂) := by
          exact congrArg (fun y : K.range ↦ (y : H₂))
            (kerOrthogonalRangeRestrict_partialPseudoInverse K
              ⟨g, Submodule.mem_sup_left hg⟩)
    _ = g := by
          exact congrArg (fun y : K.range ↦ (y : H₂))
            (rangeProjectionOnPartialPseudoInverseDomain_apply_of_mem_range K hg)

omit [CompleteSpace H₂] in
/-- When `K.range` is complete, the natural-domain pseudoinverse coincides with the bounded
everywhere-defined pseudoinverse on `K.range ⊔ K.rangeᗮ`. -/
theorem partialPseudoInverse_eq_pseudoInverse
    (K : H₁ →L[𝕜] H₂) [CompleteSpace K.range]
    (g : ((K.range ⊔ K.rangeᗮ) : Submodule 𝕜 H₂)) :
    ((K.partialPseudoInverse g : K.kerᗮ) : H₁) = K.pseudoInverse g := by
  -- Both pseudoinverses apply the same inverse equivalence to the same range projection.
  simpa [ContinuousLinearMap.partialPseudoInverse, ContinuousLinearMap.pseudoInverse] using
    congrArg (fun y : K.range ↦ ((K.kerOrthogonalEquivRange.symm y : K.kerᗮ) : H₁))
      (rangeProjectionOnPartialPseudoInverseDomain_eq_orthogonalProjectionOnto K g)

variable {K : H₁ →L[𝕜] H₂}

/-- Helper for Definition 2.1.2-extra-1: the `u_j` coefficient of `K f` is the corresponding
singular value times the `v_j` coefficient of `f`. -/
private theorem inner_leftBasis_map_eq_singularValue_mul_inner_rightBasis
    (S : ContinuousLinearMap.SingularSystem K) (f : H₁) (j : S.Index) :
    inner 𝕜 (S.leftBasis j : H₂) (K f) =
      (S.singularValue j : 𝕜) * inner 𝕜 (S.rightBasis j : H₁) f := by
  -- Move `K` to the left by adjointness and then use the singular-system axiom.
  rw [← ContinuousLinearMap.adjoint_inner_left K f (S.leftBasis j : H₂),
    S.adjoint_map_left j, inner_smul_left]
  simp

/-- Helper for Definition 2.1.2-extra-1: the `u_j` coefficient of a datum in
`K.range ⊔ K.rangeᗮ` is the corresponding singular value times the `v_j` coefficient of its
natural-domain pseudoinverse. -/
private theorem inner_leftBasis_eq_singularValue_mul_inner_partialPseudoInverse
    (S : ContinuousLinearMap.SingularSystem K)
    (g : ((K.range ⊔ K.rangeᗮ) : Submodule 𝕜 H₂)) (j : S.Index) :
    inner 𝕜 (S.leftBasis j : H₂) (g : H₂) =
      (S.singularValue j : 𝕜) *
        inner 𝕜 (S.rightBasis j : H₁) ((K.partialPseudoInverse g : K.kerᗮ) : H₁) := by
  -- Split `g` into its range and orthogonal components, then only the range part contributes.
  rcases Submodule.mem_sup.1 g.property with ⟨gr, hgr, go, hgo, hg_eq⟩
  have hsplit :
      g = ⟨gr, Submodule.mem_sup_left hgr⟩ + ⟨go, Submodule.mem_sup_right hgo⟩ := by
    ext
    simp [hg_eq]
  have hproj :
      K.rangeProjectionOnPartialPseudoInverseDomain g = ⟨gr, hgr⟩ := by
    calc
      K.rangeProjectionOnPartialPseudoInverseDomain g
          = K.rangeProjectionOnPartialPseudoInverseDomain ⟨gr, Submodule.mem_sup_left hgr⟩ +
              K.rangeProjectionOnPartialPseudoInverseDomain ⟨go, Submodule.mem_sup_right hgo⟩ := by
                rw [hsplit, map_add]
      _ = ⟨gr, hgr⟩ + 0 := by
            rw [rangeProjectionOnPartialPseudoInverseDomain_apply_of_mem_range (K := K) hgr,
              rangeProjectionOnPartialPseudoInverseDomain_apply_of_mem_orthogonal (K := K) hgo]
      _ = ⟨gr, hgr⟩ := by simp
  have hmap :
      K ((K.partialPseudoInverse g : K.kerᗮ) : H₁) = gr := by
    calc
      K ((K.partialPseudoInverse g : K.kerᗮ) : H₁)
          = (K.kerOrthogonalRangeRestrict (K.partialPseudoInverse g) : H₂) := by
              symm
              exact K.kerOrthogonalRangeRestrict_apply (K.partialPseudoInverse g)
      _ = (K.rangeProjectionOnPartialPseudoInverseDomain g : H₂) := by
            exact congrArg (fun y : K.range ↦ (y : H₂))
              (kerOrthogonalRangeRestrict_partialPseudoInverse K g)
      _ = gr := by
            exact congrArg (fun y : K.range ↦ (y : H₂)) hproj
  have hgo_mem :
      go ∈ K.range.topologicalClosureᗮ := by
    simpa [Submodule.orthogonal_closure] using hgo
  have hinner_go : inner 𝕜 (S.leftBasis j : H₂) go = 0 := by
    exact Submodule.inner_right_of_mem_orthogonal (S.leftBasis j).property hgo_mem
  calc
    inner 𝕜 (S.leftBasis j : H₂) (g : H₂)
        = inner 𝕜 (S.leftBasis j : H₂) (gr + go) := by
            rw [hg_eq]
    _ = inner 𝕜 (S.leftBasis j : H₂) gr + inner 𝕜 (S.leftBasis j : H₂) go := by
          rw [inner_add_right]
    _ = inner 𝕜 (S.leftBasis j : H₂) gr := by
          rw [hinner_go, add_zero]
    _ = inner 𝕜 (S.leftBasis j : H₂) (K ((K.partialPseudoInverse g : K.kerᗮ) : H₁)) := by
          rw [← hmap]
    _ = (S.singularValue j : 𝕜) *
          inner 𝕜 (S.rightBasis j : H₁) ((K.partialPseudoInverse g : K.kerᗮ) : H₁) := by
          simpa using inner_leftBasis_map_eq_singularValue_mul_inner_rightBasis
            S (((K.partialPseudoInverse g : K.kerᗮ) : H₁)) j

namespace SingularSystem

variable {K : H₁ →L[𝕜] H₂}

/-- Definition 2.1.2-extra-1 (2). A singular system expands `K f` as the series
`∑ j, s_j • ⟪v_j, f⟫ • u_j`. -/
theorem hasSum_map
    (S : ContinuousLinearMap.SingularSystem K) (f : H₁) :
    HasSum
      (fun j : S.Index ↦
        (((S.singularValue j : 𝕜) * inner 𝕜 (S.rightBasis j : H₁) f) • (S.leftBasis j : H₂)))
      (K f) := by
  -- Expand `K f` in the left Hilbert basis of `K.range.topologicalClosure`.
  let hf : K.range.topologicalClosure := ⟨K f, K.range.le_topologicalClosure (K.mem_range_self f)⟩
  have hsum :
      HasSum (fun j : S.Index ↦ S.leftBasis.repr hf j • (S.leftBasis j : H₂)) (K f) := by
    simpa using (S.leftBasis.hasSum_repr hf).mapL K.range.topologicalClosure.subtypeL
  -- Rewrite the Hilbert-basis coefficients using the singular-system adjoint relation.
  refine HasSum.congr_fun hsum (fun j ↦ ?_)
  simp [hf, HilbertBasis.repr_apply_apply,
    ContinuousLinearMap.inner_leftBasis_map_eq_singularValue_mul_inner_rightBasis]

/-- Definition 2.1.2-extra-1 (3). A singular system expands `K.partialPseudoInverse g` as the
series `∑ j, (⟪u_j, g⟫ / s_j) • v_j` for `g ∈ K.range ⊔ K.rangeᗮ`. -/
theorem hasSum_partialPseudoInverse
    (S : ContinuousLinearMap.SingularSystem K)
    (g : ((K.range ⊔ K.rangeᗮ) : Submodule 𝕜 H₂)) :
    HasSum
      (fun j : S.Index ↦
        ((inner 𝕜 (S.leftBasis j : H₂) (g : H₂) / (S.singularValue j : 𝕜)) • S.rightBasis j))
      (K.partialPseudoInverse g) := by
  -- Expand `K.partialPseudoInverse g` in the right Hilbert basis of `K.kerᗮ`.
  have hsum := S.rightBasis.hasSum_repr (K.partialPseudoInverse g)
  -- Rewrite the coefficients using the singular-system identity for
  -- the natural-domain pseudoinverse.
  refine HasSum.congr_fun hsum (fun j ↦ ?_)
  have hs_ne : (S.singularValue j : 𝕜) ≠ 0 := by
    exact_mod_cast (ne_of_gt (S.singularValue_pos j))
  rw [HilbertBasis.repr_apply_apply]
  apply congrArg (fun a : 𝕜 ↦ a • S.rightBasis j)
  rw [div_eq_iff hs_ne]
  simpa [mul_comm] using
    ContinuousLinearMap.inner_leftBasis_eq_singularValue_mul_inner_partialPseudoInverse
      S g j

end SingularSystem

end ContinuousLinearMap
