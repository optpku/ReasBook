/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Fact 2.28: the sum `A ⊔ B` is the preimage of the range of the projection onto
`Aᗮ` along `A`. -/
private lemma sup_eq_preimage_range_orthogonalProjection
    {A B : Submodule ℝ H} (hA : IsClosed (A : Set H)) :
    ((A ⊔ B : Submodule ℝ H) : Set H) =
      (let proj : H →L[ℝ] Aᗮ :=
        Aᗮ.orthogonalProjection
      proj ⁻¹' (((proj.comp B.subtypeL : B →ₗ[ℝ] Aᗮ).range : Set Aᗮ))) := by
  let proj : H →L[ℝ] Aᗮ := Aᗮ.orthogonalProjection
  have hAA : Aᗮᗮ ≤ A := by
    intro x hx
    have hx' : x ∈ (⟨A, hA⟩ : ClosedSubmodule ℝ H).toSubmodule := by
      simpa using hx
    simpa using hx'
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
    -- Projecting a vector in `A ⊔ B` forgets the `A`-component.
    refine ⟨⟨b, hb⟩, ?_⟩
    change proj b = proj (a + b)
    have hpa : proj a = 0 := by
      exact show Aᗮ.orthogonalProjection a = 0 from
        Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
          (Submodule.le_orthogonal_orthogonal A ha)
    rw [map_add, hpa, zero_add]
  · intro hx
    rcases hx with ⟨b, hb⟩
    change proj b = proj x at hb
    -- Matching projections means the difference lies in the kernel, hence in `A`.
    have hzero : proj (x - b) = 0 := by
      rw [map_sub, hb, sub_self]
    have hxa : x - b ∈ A := by
      exact hAA <| by
        exact (show Aᗮ.orthogonalProjection (x - b) = 0 ↔ x - b ∈ Aᗮᗮ from
          Submodule.orthogonalProjection_eq_zero_iff).mp <| by
            simpa only [proj] using hzero
    exact Submodule.mem_sup.mpr ⟨x - b, hxa, b, b.property, by abel_nf⟩

/-- If `A` is closed and `B` is finite-dimensional, then `A ⊔ B` is closed. -/
theorem isClosed_sup_of_isClosed_of_finiteDimensional_right
    {A B : Submodule ℝ H} (hA : IsClosed (A : Set H)) [FiniteDimensional ℝ B] :
    IsClosed ((A ⊔ B : Submodule ℝ H) : Set H) := by
  let proj : H →L[ℝ] Aᗮ := Aᗮ.orthogonalProjection
  let f : B →ₗ[ℝ] Aᗮ := proj.comp B.subtypeL
  rw [sup_eq_preimage_range_orthogonalProjection hA]
  -- The projected range is finite-dimensional because it is the image of `B`.
  have hclosed_range : IsClosed ((f.range : Submodule ℝ Aᗮ) : Set Aᗮ) := by
    exact Submodule.closed_of_finiteDimensional f.range
  exact hclosed_range.preimage proj.continuous

/-- If `A` is closed and `Aᗮ` is finite-dimensional, then `B ⊔ A` is closed. -/
theorem isClosed_sup_of_isClosed_of_finiteDimensional_orthogonal_right
    {A B : Submodule ℝ H} (hA : IsClosed (A : Set H)) [FiniteDimensional ℝ Aᗮ] :
    IsClosed ((B ⊔ A : Submodule ℝ H) : Set H) := by
  let proj : H →L[ℝ] Aᗮ := Aᗮ.orthogonalProjection
  let f : B →ₗ[ℝ] Aᗮ := proj.comp B.subtypeL
  rw [sup_comm, sup_eq_preimage_range_orthogonalProjection hA]
  -- Here the projected range is closed because it lies in the finite-dimensional space `Aᗮ`.
  have hclosed_range : IsClosed ((f.range : Submodule ℝ Aᗮ) : Set Aᗮ) := by
    exact Submodule.closed_of_finiteDimensional f.range
  exact hclosed_range.preimage proj.continuous

/-- Fact 2.28: if `U` and `V` are closed linear subspaces of a real Hilbert space and `V` is
finite-dimensional or has finite codimension in the sense that `Vᗮ` is finite-dimensional, then
their sum `U ⊔ V` is closed. -/
-- Proof sketch: in the finite-dimensional case, combine the closedness of `U` with the fact that
-- finite-dimensional subspaces are complete and closed. In the finite-codimensional case, use
-- that `Vᗮ` is finite-dimensional, hence closed, so `V` admits a closed complement and one reduces
-- to the previous case via the orthogonal decomposition associated to `V`.
theorem isClosed_sup_of_isClosed_of_finiteDimensional_or_finiteDimensional_orthogonal
    {U V : Submodule ℝ H} (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))
    (hfinite : FiniteDimensional ℝ V ∨ FiniteDimensional ℝ Vᗮ) :
    IsClosed ((U ⊔ V : Submodule ℝ H) : Set H) := by
  rcases hfinite with hV | hVperp
  · haveI : FiniteDimensional ℝ V := hV
    -- In the first branch, project along the closed subspace `U`.
    exact isClosed_sup_of_isClosed_of_finiteDimensional_right hU
  · haveI : FiniteDimensional ℝ Vᗮ := hVperp
    -- In the finite-codimensional branch, project onto the finite-dimensional complement `Vᗮ`.
    exact isClosed_sup_of_isClosed_of_finiteDimensional_orthogonal_right hV
