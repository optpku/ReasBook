/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_15

public section

namespace ContinuousLinearMap

universe u v w

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- Exercise 2.9. If `K.adjoint.comp K` has a countable orthonormal eigenfamily with positive
eigenvalues spanning `K.kerᗮ`, then `K` admits a singular system indexed by all of `ℕ` whose
singular values are `Real.sqrt (eigenvalue n)` and whose right singular vectors are the given
`v n`. -/
theorem exists_singularSystem_of_adjoint_comp_self_eigenbasis
    (K : H₁ →L[𝕜] H₂) (eigenvalue : ℕ → ℝ) (v : ℕ → K.kerᗮ)
    (hK : IsCompactOperator K)
    (hv_orthonormal : Orthonormal 𝕜 v)
    (hv_dense : ⊤ ≤ (Submodule.span 𝕜 (Set.range v)).topologicalClosure)
    (h_eigen : ∀ n, (K.adjoint.comp K) (v n : H₁) = (eigenvalue n : 𝕜) • (v n : H₁))
    (h_eigenvalue_pos : ∀ n, 0 < eigenvalue n)
    (h_eigenvalue_antitone : Antitone eigenvalue) :
    ∃ (S : SingularSystem K) (h_length : S.length = ⊤),
      (∀ n : ℕ, S.singularValue (S.natIndex h_length n) = Real.sqrt (eigenvalue n)) ∧
        ∀ n : ℕ, S.rightBasis (S.natIndex h_length n) = v n := by
  classical
  let ι : Type := {j : ℕ∞ // j < (⊤ : ℕ∞)}
  let rightFamilyTop : ι → K.kerᗮ := v ∘ fun j : ι => j.1.toNat
  let singularValueTop : ι → ℝ := fun j => Real.sqrt (eigenvalue j.1.toNat)
  have hindex_injective : Function.Injective (fun j : ι ↦ j.1.toNat) := by
    intro i j hij
    apply Subtype.ext
    -- Two `ℕ∞` indices below `⊤` agree once their `toNat` values agree.
    exact
      (ENat.coe_toNat (ne_of_lt i.2)).symm.trans <|
        (congrArg (fun n : ℕ => (n : ℕ∞)) hij).trans (ENat.coe_toNat (ne_of_lt j.2))
  -- Reindex the given orthonormal eigenfamily to the `ℕ∞`-initial-segment index used by
  -- `SingularSystem`.
  have hright_orthonormal : Orthonormal 𝕜 rightFamilyTop := by
    -- Composing the given orthonormal family with the injective `toNat` reindexing keeps it
    -- orthonormal.
    simpa [rightFamilyTop, Function.comp_def] using
      hv_orthonormal.comp (fun j : ι ↦ j.1.toNat) hindex_injective
  have hright_range : Set.range rightFamilyTop = Set.range v := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.1.toNat, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨⟨n, ENat.coe_lt_top n⟩, rfl⟩
  have hright_dense : ⊤ ≤ (Submodule.span 𝕜 (Set.range rightFamilyTop)).topologicalClosure := by
    simpa [hright_range] using hv_dense
  have hright_orthogonal_bot : (Submodule.span 𝕜 (Set.range rightFamilyTop))ᗮ = ⊥ := by
    -- The dense right span has trivial orthogonal complement.
    rw [← Submodule.topologicalClosure_eq_top_iff]
    exact le_antisymm le_top hright_dense
  -- The positive eigenvalues produce the positive singular values and the inverse scalars needed
  -- to normalize `K (v_j)`.
  have hsingular_pos : ∀ j : ι, 0 < singularValueTop j := by
    intro j
    simpa [singularValueTop] using Real.sqrt_pos.2 (h_eigenvalue_pos j.1.toNat)
  have hsingular_ne : ∀ j : ι, (singularValueTop j : 𝕜) ≠ 0 := by
    intro j
    exact_mod_cast (hsingular_pos j).ne'
  have hsingular_sq : ∀ j : ι, ((singularValueTop j : 𝕜) ^ 2) = (eigenvalue j.1.toNat : 𝕜) := by
    intro j
    -- The singular values are the positive square roots of the given eigenvalues.
    simpa [singularValueTop] using
      congrArg (fun r : ℝ => (r : 𝕜)) <|
        Real.sq_sqrt (le_of_lt (h_eigenvalue_pos j.1.toNat))
  have hleft_mem :
      ∀ j : ι,
        ((singularValueTop j : 𝕜)⁻¹ • K (rightFamilyTop j : H₁)) ∈ K.range.topologicalClosure := by
      intro j
      -- Each normalized image still lies in the closed range because the closed range is a
      -- submodule.
      exact
        K.range.topologicalClosure.smul_mem ((singularValueTop j : 𝕜)⁻¹)
          (subset_closure ⟨(rightFamilyTop j : H₁), rfl⟩)
  let leftFamilyTop : ι → K.range.topologicalClosure := fun j =>
    ⟨(singularValueTop j : 𝕜)⁻¹ • K (rightFamilyTop j : H₁), hleft_mem j⟩
  -- The normalized image vectors satisfy the two singular-vector identities.
  have hmap_right :
      ∀ j : ι, K (rightFamilyTop j : H₁) = (singularValueTop j : 𝕜) • (leftFamilyTop j : H₂) := by
    intro j
    have hs_ne := hsingular_ne j
    calc
      K (rightFamilyTop j : H₁)
          =
            (singularValueTop j : 𝕜) •
              ((singularValueTop j : 𝕜)⁻¹ • K (rightFamilyTop j : H₁)) := by
              simp [hs_ne]
      _ = (singularValueTop j : 𝕜) • (leftFamilyTop j : H₂) := rfl
  have hmap_left :
      ∀ j : ι,
        K.adjoint (leftFamilyTop j : H₂) = (singularValueTop j : 𝕜) • (rightFamilyTop j : H₁) := by
    intro j
    have hs_ne := hsingular_ne j
    calc
      K.adjoint (leftFamilyTop j : H₂)
          = (singularValueTop j : 𝕜)⁻¹ • K.adjoint (K (rightFamilyTop j : H₁)) := by
              simp [leftFamilyTop]
      _ = (singularValueTop j : 𝕜)⁻¹ • ((eigenvalue j.1.toNat : 𝕜) • (rightFamilyTop j : H₁)) := by
            rw [show K.adjoint (K (rightFamilyTop j : H₁)) =
                (eigenvalue j.1.toNat : 𝕜) • (rightFamilyTop j : H₁) by
                  simpa [rightFamilyTop, Function.comp_def] using h_eigen j.1.toNat]
      _ = (((singularValueTop j : 𝕜)⁻¹ * (eigenvalue j.1.toNat : 𝕜)) : 𝕜) •
            (rightFamilyTop j : H₁) := by
            rw [smul_smul]
      _ = (singularValueTop j : 𝕜) • (rightFamilyTop j : H₁) := by
            rw [← hsingular_sq j]
            simp [pow_two, hs_ne]
  have hscaled_left :
      ∀ j : ι, (singularValueTop j : 𝕜) • (leftFamilyTop j : H₂) = K (rightFamilyTop j : H₁) := by
    intro j
    simpa using (hmap_right j).symm
  have hinner_map_right :
      ∀ i j : ι,
        inner 𝕜 (leftFamilyTop i : H₂) (K (rightFamilyTop j : H₁)) =
          (singularValueTop j : 𝕜) * inner 𝕜 (leftFamilyTop i : H₂) (leftFamilyTop j : H₂) := by
    intro i j
    calc
      inner 𝕜 (leftFamilyTop i : H₂) (K (rightFamilyTop j : H₁))
          = inner 𝕜 (leftFamilyTop i : H₂) ((singularValueTop j : 𝕜) • (leftFamilyTop j : H₂)) := by
              rw [hmap_right j]
      _ = (singularValueTop j : 𝕜) * inner 𝕜 (leftFamilyTop i : H₂) (leftFamilyTop j : H₂) := by
            rw [inner_smul_right]
  -- The singular-vector identities transport orthonormality from the right family to the left
  -- family.
  have hinner_relation :
      ∀ i j : ι,
        (singularValueTop j : 𝕜) * inner 𝕜 (leftFamilyTop i : H₂) (leftFamilyTop j : H₂) =
          (singularValueTop i : 𝕜) * inner 𝕜 (rightFamilyTop i : H₁) (rightFamilyTop j : H₁) := by
    intro i j
    calc
      (singularValueTop j : 𝕜) * inner 𝕜 (leftFamilyTop i : H₂) (leftFamilyTop j : H₂)
          = inner 𝕜 (leftFamilyTop i : H₂) (K (rightFamilyTop j : H₁)) := by
              simpa using (hinner_map_right i j).symm
      _ = inner 𝕜 (leftFamilyTop i : H₂) (K (rightFamilyTop j : H₁)) := by
            rfl
      _ = inner 𝕜 (K.adjoint (leftFamilyTop i : H₂)) (rightFamilyTop j : H₁) := by
            rw [K.adjoint_inner_left]
      _ = inner 𝕜 ((singularValueTop i : 𝕜) • (rightFamilyTop i : H₁)) (rightFamilyTop j : H₁) := by
            rw [hmap_left i]
      _ = (singularValueTop i : 𝕜) * inner 𝕜 (rightFamilyTop i : H₁) (rightFamilyTop j : H₁) := by
            simp [inner_smul_left]
  have hleft_orthonormal : Orthonormal 𝕜 leftFamilyTop := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst j
      have hright_self :
          inner 𝕜 (rightFamilyTop i : H₁) (rightFamilyTop i : H₁) = (1 : 𝕜) := by
        simpa using orthonormal_iff_ite.mp hright_orthonormal i i
      have hdiag :
          (singularValueTop i : 𝕜) * inner 𝕜 (leftFamilyTop i : H₂) (leftFamilyTop i : H₂) =
            (singularValueTop i : 𝕜) * (1 : 𝕜) := by
        have hdiag' := hinner_relation i i
        rwa [hright_self] at hdiag'
      have hleft_self :
          inner 𝕜 (leftFamilyTop i : H₂) (leftFamilyTop i : H₂) = (1 : 𝕜) := by
        exact mul_left_cancel₀ (hsingular_ne i) <| by simpa using hdiag
      simpa using hleft_self
    · have hzero :
        (singularValueTop j : 𝕜) * inner 𝕜 (leftFamilyTop i : H₂) (leftFamilyTop j : H₂) = 0 := by
          have hright_zero :
              inner 𝕜 (rightFamilyTop i : H₁) (rightFamilyTop j : H₁) = 0 := by
            exact hright_orthonormal.inner_eq_zero hij
          have hzero' := hinner_relation i j
          rwa [hright_zero, mul_zero] at hzero'
      have hleft_zero :
          inner 𝕜 (leftFamilyTop i : H₂) (leftFamilyTop j : H₂) = 0 :=
        (mul_eq_zero.mp hzero).resolve_left (hsingular_ne j)
      simpa [hij] using hleft_zero
  -- To see that the left family spans `K.range.topologicalClosure`, kill a vector orthogonal to all
  -- normalized images by first showing its adjoint image is orthogonal to the dense right span.
  have hleft_orthogonal_bot : (Submodule.span 𝕜 (Set.range leftFamilyTop))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hy_adjoint_mem : K.adjoint (y : H₂) ∈ K.kerᗮ := by
      -- The adjoint image of a vector in `K.range.topologicalClosure` lies in `K.kerᗮ`.
      rw [K.orthogonal_ker]
      exact subset_closure ⟨(y : H₂), rfl⟩
    let z : K.kerᗮ := ⟨K.adjoint (y : H₂), hy_adjoint_mem⟩
    have hy_right :
        z ∈ (Submodule.span 𝕜 (Set.range rightFamilyTop))ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      have hu_singleton :
          u ∈ (𝕜 ∙ z)ᗮ := by
        refine (Submodule.span_le.mpr ?_) hu
        intro x hx
        rcases hx with ⟨j, rfl⟩
        exact (Submodule.mem_orthogonal_singleton_iff_inner_left).2 <| by
          -- Orthogonality to `leftFamilyTop` transfers to orthogonality against `K† y`.
          have hyj :
              inner 𝕜 (leftFamilyTop j : K.range.topologicalClosure) y = 0 := by
            exact (Submodule.mem_orthogonal _ _).1 hy _ (Submodule.subset_span (Set.mem_range_self j))
          calc
            inner 𝕜 (rightFamilyTop j : H₁) (z : H₁)
                = inner 𝕜 (K (rightFamilyTop j : H₁)) (y : H₂) := by
                    rw [K.adjoint_inner_right]
            _ = inner 𝕜 ((singularValueTop j : 𝕜) • (leftFamilyTop j : H₂)) (y : H₂) := by
                  rw [hmap_right j]
            _ = star (singularValueTop j : 𝕜) * inner 𝕜 (leftFamilyTop j : H₂) (y : H₂) := by
                  simpa using
                    (inner_smul_left (r := (singularValueTop j : 𝕜))
                      (x := (leftFamilyTop j : H₂)) (y := (y : H₂)))
            _ = 0 := by
                  have hyj' : inner 𝕜 (leftFamilyTop j : H₂) (y : H₂) = 0 := by
                    simpa using hyj
                  rw [hyj']
                  simp
      exact (Submodule.mem_orthogonal_singleton_iff_inner_left.mp hu_singleton)
    have hy_adjoint_zero : K.adjoint (y : H₂) = 0 := by
      have hz_zero : z ∈ (⊥ : Submodule 𝕜 K.kerᗮ) := by
        simpa [hright_orthogonal_bot] using hy_right
      have hz_eq_zero : z = 0 := by
        simpa using hz_zero
      simpa [z] using congrArg (fun t : K.kerᗮ => (t : H₁)) hz_eq_zero
    have hy_in_ker : (y : H₂) ∈ K.adjoint.ker := by
      simpa [LinearMap.mem_ker] using hy_adjoint_zero
    have hy_in_ker_orth : (y : H₂) ∈ K.adjoint.kerᗮ := by
      simpa [K.adjoint.orthogonal_ker, ContinuousLinearMap.adjoint_adjoint] using y.2
    have hy_zero : (y : H₂) = 0 := by
      have hy_inf : (y : H₂) ∈ K.adjoint.ker ⊓ K.adjoint.kerᗮ := ⟨hy_in_ker, hy_in_ker_orth⟩
      have : (y : H₂) ∈ (⊥ : Submodule 𝕜 H₂) := by
        simpa [Submodule.inf_orthogonal_eq_bot] using hy_inf
      simpa using this
    exact Subtype.ext hy_zero
  -- The reindexed singular values remain antitone because `toNat` preserves order below `⊤`.
  have hsingular_antitone : Antitone singularValueTop := by
    intro i j hij
    apply Real.sqrt_le_sqrt
    exact h_eigenvalue_antitone <| ENat.toNat_le_toNat hij (ne_of_lt j.2)
  let leftBasisTop : HilbertBasis ι 𝕜 K.range.topologicalClosure :=
    HilbertBasis.mkOfOrthogonalEqBot hleft_orthonormal hleft_orthogonal_bot
  let rightBasisTop : HilbertBasis ι 𝕜 K.kerᗮ :=
    HilbertBasis.mk hright_orthonormal hright_dense
  have hrightBasisTop_apply :
      ∀ j : ι, rightBasisTop j = rightFamilyTop j := by
    intro j
    simpa [rightBasisTop] using
      congrArg (fun f : ι → K.kerᗮ => f j) (HilbertBasis.coe_mk hright_orthonormal hright_dense)
  let S : SingularSystem K := {
    length := ⊤
    leftBasis := leftBasisTop
    rightBasis := rightBasisTop
    singularValue := singularValueTop
    isCompact := hK
    singularValue_pos := hsingular_pos
    singularValue_antitone := hsingular_antitone
    map_right := by
      intro j
      simpa [leftBasisTop, rightBasisTop] using hmap_right j
    adjoint_map_left := by
      intro j
      simpa [leftBasisTop, rightBasisTop] using hmap_left j
  }
  refine ⟨S, rfl, ?_, ?_⟩
  · intro n
    simp [S, singularValueTop]
  · intro n
    have hidx :
        ContinuousLinearMap.SingularSystem.natIndex S rfl n = (⟨n, ENat.coe_lt_top n⟩ : ι) := by
      apply Subtype.ext
      simpa using (ContinuousLinearMap.SingularSystem.coe_natIndex S rfl n)
    calc
      S.rightBasis (ContinuousLinearMap.SingularSystem.natIndex S rfl n)
          = rightBasisTop (ContinuousLinearMap.SingularSystem.natIndex S rfl n) := by
              rfl
      _ = rightBasisTop ⟨n, ENat.coe_lt_top n⟩ := by
            rw [hidx]
      _ = rightFamilyTop ⟨n, ENat.coe_lt_top n⟩ := hrightBasisTop_apply _
      _ = v n := by
            simp [rightFamilyTop]

end ContinuousLinearMap
