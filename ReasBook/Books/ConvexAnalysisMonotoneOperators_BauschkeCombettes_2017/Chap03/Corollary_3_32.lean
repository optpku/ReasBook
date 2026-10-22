/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_31

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProductSpace

universe u v

variable {𝓗 : Type u} {𝓚 : Type v}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

private theorem isMoorePenroseInverse_moorePenroseInverseOperator (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    IsMoorePenroseInverse T (moorePenroseInverseOperator T hT_closed) := by
  refine ⟨?_, ?_⟩
  · exact moorePenroseInverse_mem_orthogonalKer T hT_closed
  · exact moorePenroseInverse_normalEquation T hT_closed

private theorem eq_moorePenroseInverseOperator_of_isMoorePenroseInverse
    (T : 𝓗 →L[ℝ] 𝓚) (hT_closed : IsClosed (T.range : Set 𝓚)) (T' : 𝓚 →L[ℝ] 𝓗)
    (hmp : IsMoorePenroseInverse T T') :
    T' = moorePenroseInverseOperator T hT_closed := by
  ext y
  have hy :
      T' y ∈ moorePenroseSolutionSet T y ∩ (T.kerᗮ : Set 𝓗) := by
    refine ⟨?_, hmp.mem_orthogonalKer y⟩
    exact (mem_moorePenroseSolutionSet_iff T y (T' y)).2 (hmp.normalEquation y)
  have hy' :
      T' y ∈ ({moorePenroseInverse T hT_closed y} : Set 𝓗) := by
    rw [← moorePenroseSolutionSet_inter_orthogonalKer_eq_singleton T hT_closed y]
    exact hy
  simpa using Set.mem_singleton_iff.mp hy'

private theorem moorePenroseInverseOperator_range_eq_adjoint_range (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    (moorePenroseInverseOperator T hT_closed).range = (adjoint T).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change moorePenroseInverse T hT_closed y ∈ ((adjoint T).range : Set 𝓗)
    rw [← range_moorePenroseInverse_eq_adjoint_range T hT_closed]
    exact ⟨y, rfl⟩
  · intro hx
    change x ∈ ((adjoint T).range : Set 𝓗) at hx
    rw [← range_moorePenroseInverse_eq_adjoint_range T hT_closed] at hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨y, rfl⟩

private theorem moorePenroseInverseOperator_range_isClosed (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    IsClosed (((moorePenroseInverseOperator T hT_closed).range : Set 𝓗)) := by
  rw [moorePenroseInverseOperator_range_eq_adjoint_range T hT_closed]
  exact adjoint_range_isClosed_of_isClosed_range T hT_closed

private theorem comp_moorePenroseInverseOperator_eq_closedRangeProjection (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    T.comp (moorePenroseInverseOperator T hT_closed) = closedRangeProjection T hT_closed := by
  ext y
  simpa using apply_moorePenroseInverse_eq_rangeProjection T hT_closed y

private theorem closedRangeProjection_adjoint_eq_orthogonalKer_starProjection (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    closedRangeProjection (adjoint T) (adjoint_range_isClosed_of_isClosed_range T hT_closed) =
      T.kerᗮ.starProjection := by
  ext x
  simp [closedRangeProjection, orthogonal_ker_eq_adjoint_range T hT_closed]

private theorem moorePenroseInverseOperator_comp_eq_orthogonalKer_starProjection
    (T : 𝓗 →L[ℝ] 𝓚) (hT_closed : IsClosed (T.range : Set 𝓚)) :
    (moorePenroseInverseOperator T hT_closed).comp T = T.kerᗮ.starProjection := by
  ext x
  calc
    moorePenroseInverseOperator T hT_closed (T x) = closedRangeProjection (adjoint T)
        (adjoint_range_isClosed_of_isClosed_range T hT_closed) x := by
      simpa using apply_moorePenroseInverse_comp_eq_adjointRangeProjection T hT_closed x
    _ = closedRangeProjection (adjoint T)
        (adjoint_range_isClosed_of_isClosed_range T hT_closed) x := rfl
    _ = T.kerᗮ.starProjection x := by
      rw [closedRangeProjection_adjoint_eq_orthogonalKer_starProjection T hT_closed]

private theorem moorePenroseInverseOperator_apply_eq_zero_of_mem_orthogonalRange
    (T : 𝓗 →L[ℝ] 𝓚) (hT_closed : IsClosed (T.range : Set 𝓚)) {y : 𝓚}
    (hy : y ∈ T.rangeᗮ) :
    moorePenroseInverseOperator T hT_closed y = 0 := by
  let Tdag : 𝓚 →L[ℝ] 𝓗 := moorePenroseInverseOperator T hT_closed
  have hTdag_closed : IsClosed ((Tdag.range : Set 𝓗)) :=
    moorePenroseInverseOperator_range_isClosed T hT_closed
  have htfae := isMoorePenroseInverse_tfae_projection_and_orthogonal_conditions T Tdag
    hT_closed hTdag_closed
  have horth : (∀ x ∈ T.kerᗮ, Tdag (T x) = x) ∧ ∀ y ∈ T.rangeᗮ, Tdag y = 0 :=
    (List.TFAE.out htfae 0 2).mp
      (isMoorePenroseInverse_moorePenroseInverseOperator T hT_closed)
  exact horth.2 y hy

private theorem adjoint_moorePenroseInverseOperator_comp_adjoint_eq_closedRangeProjection
    (T : 𝓗 →L[ℝ] 𝓚) (hT_closed : IsClosed (T.range : Set 𝓚)) :
    (moorePenroseInverseOperator T hT_closed).adjoint.comp (adjoint T) =
      closedRangeProjection T hT_closed := by
  calc
    (moorePenroseInverseOperator T hT_closed).adjoint.comp (adjoint T) =
        (T.comp (moorePenroseInverseOperator T hT_closed)).adjoint := by
          simp [adjoint_comp]
    _ = (closedRangeProjection T hT_closed).adjoint := by
      rw [comp_moorePenroseInverseOperator_eq_closedRangeProjection T hT_closed]
    _ = closedRangeProjection T hT_closed := by
      simpa [closedRangeProjection] using
        (isSelfAdjoint_starProjection (T.range : Submodule ℝ 𝓚)).adjoint_eq

private theorem adjoint_moorePenroseInverseOperator_range_eq_range (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    (moorePenroseInverseOperator T hT_closed).adjoint.range = T.range := by
  let Tdag : 𝓚 →L[ℝ] 𝓗 := moorePenroseInverseOperator T hT_closed
  have hTdag_closed : IsClosed ((Tdag.range : Set 𝓗)) :=
    moorePenroseInverseOperator_range_isClosed T hT_closed
  have htfae := isMoorePenroseInverse_tfae_projection_and_orthogonal_conditions T Tdag
    hT_closed hTdag_closed
  have horth : (∀ x ∈ T.kerᗮ, Tdag (T x) = x) ∧ ∀ y ∈ T.rangeᗮ, Tdag y = 0 :=
    (List.TFAE.out htfae 0 2).mp
      (isMoorePenroseInverse_moorePenroseInverseOperator T hT_closed)
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have hy : Tdag.adjoint x ∈ T.rangeᗮᗮ := by
      rw [Submodule.mem_orthogonal']
      intro z hz
      have hz0 : Tdag z = 0 :=
        moorePenroseInverseOperator_apply_eq_zero_of_mem_orthogonalRange T hT_closed hz
      have hinner : ⟪z, Tdag.adjoint x⟫_ℝ = 0 := by
        simpa [hz0] using ContinuousLinearMap.adjoint_inner_right Tdag z x
      simpa [real_inner_comm] using hinner
    simpa [Submodule.orthogonal_orthogonal_eq_closure,
      hT_closed.submodule_topologicalClosure_eq] using hy
  · rintro ⟨x, rfl⟩
    have hself : closedRangeProjection T hT_closed (T x) = T x :=
      closedRangeProjection_eq_self_of_mem_range T hT_closed ⟨x, rfl⟩
    have hproj :=
      congrArg (fun f : 𝓚 →L[ℝ] 𝓚 ↦ f (T x))
        (adjoint_moorePenroseInverseOperator_comp_adjoint_eq_closedRangeProjection T hT_closed)
    refine ⟨adjoint T (T x), ?_⟩
    simpa [hself] using hproj

private theorem adjoint_moorePenroseInverseOperator_range_isClosed (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    IsClosed (((moorePenroseInverseOperator T hT_closed).adjoint.range : Set 𝓚)) := by
  rw [adjoint_moorePenroseInverseOperator_range_eq_range T hT_closed]
  exact hT_closed

private theorem closedRangeProjection_moorePenroseInverseOperator_eq_orthogonalKer_starProjection
    (T : 𝓗 →L[ℝ] 𝓚) (hT_closed : IsClosed (T.range : Set 𝓚)) :
    closedRangeProjection (moorePenroseInverseOperator T hT_closed)
      (moorePenroseInverseOperator_range_isClosed T hT_closed) =
        T.kerᗮ.starProjection := by
  ext x
  simp [closedRangeProjection, moorePenroseInverseOperator_range_eq_adjoint_range,
    orthogonal_ker_eq_adjoint_range T hT_closed]

-- Proof sketch: the projection characterization from Proposition 3.31 shows that `T` itself is
-- the Moore-Penrose inverse of `T†`, and uniqueness identifies `(T†)†` with `T`.
/-- Corollary 3.32 (i): if `T` has closed range, then the Moore-Penrose inverse of `T†` is `T`
itself. -/
theorem moorePenroseInverseOperator_moorePenroseInverseOperator (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    moorePenroseInverseOperator (moorePenroseInverseOperator T hT_closed)
      (moorePenroseInverseOperator_range_isClosed T hT_closed) = T := by
  let Tdag : 𝓚 →L[ℝ] 𝓗 := moorePenroseInverseOperator T hT_closed
  have hTdag_closed : IsClosed ((Tdag.range : Set 𝓗)) :=
    moorePenroseInverseOperator_range_isClosed T hT_closed
  have hproj : Tdag.comp T = closedRangeProjection Tdag hTdag_closed ∧
      T.comp Tdag = closedRangeProjection T hT_closed := by
    refine ⟨?_, comp_moorePenroseInverseOperator_eq_closedRangeProjection T hT_closed⟩
    calc
      Tdag.comp T = T.kerᗮ.starProjection := by
        rw [moorePenroseInverseOperator_comp_eq_orthogonalKer_starProjection T hT_closed]
      _ = closedRangeProjection Tdag hTdag_closed := by
        rw [← closedRangeProjection_moorePenroseInverseOperator_eq_orthogonalKer_starProjection
          T hT_closed]
  have htfae := isMoorePenroseInverse_tfae_projection_and_orthogonal_conditions Tdag T
    hTdag_closed hT_closed
  have hmp : IsMoorePenroseInverse Tdag T :=
    (List.TFAE.out htfae 1 0).mp hproj
  symm
  exact eq_moorePenroseInverseOperator_of_isMoorePenroseInverse Tdag hTdag_closed T hmp

-- Proof sketch: the adjoint of `T†` satisfies the same projection identities as the canonical
-- Moore-Penrose inverse of `T*`, so uniqueness identifies them.
/-- Corollary 3.32 (ii): if `T` has closed range, then `(T†)∗ = (T∗)†`. -/
theorem adjoint_moorePenroseInverseOperator_eq_moorePenroseInverseOperator_adjoint
    (T : 𝓗 →L[ℝ] 𝓚) (hT_closed : IsClosed (T.range : Set 𝓚)) :
    (moorePenroseInverseOperator T hT_closed).adjoint =
      moorePenroseInverseOperator (adjoint T)
        (adjoint_range_isClosed_of_isClosed_range T hT_closed) := by
  let Tdag : 𝓚 →L[ℝ] 𝓗 := moorePenroseInverseOperator T hT_closed
  have hTdagAdj_closed : IsClosed (((Tdag.adjoint).range : Set 𝓚)) :=
    adjoint_moorePenroseInverseOperator_range_isClosed T hT_closed
  have hproj : (adjoint T).comp Tdag.adjoint =
      closedRangeProjection (adjoint T) (adjoint_range_isClosed_of_isClosed_range T hT_closed) ∧
      Tdag.adjoint.comp (adjoint T) = closedRangeProjection Tdag.adjoint hTdagAdj_closed := by
    refine ⟨?_, ?_⟩
    · calc
        (adjoint T).comp Tdag.adjoint = T.kerᗮ.starProjection := by
          calc
            (adjoint T).comp Tdag.adjoint = (Tdag.comp T).adjoint := by
              simp [adjoint_comp]
            _ = (T.kerᗮ.starProjection).adjoint := by
              rw [moorePenroseInverseOperator_comp_eq_orthogonalKer_starProjection T hT_closed]
            _ = T.kerᗮ.starProjection := by
              simpa using (isSelfAdjoint_starProjection (T.kerᗮ : Submodule ℝ 𝓗)).adjoint_eq
        _ = closedRangeProjection (adjoint T)
            (adjoint_range_isClosed_of_isClosed_range T hT_closed) := by
              rw [closedRangeProjection_adjoint_eq_orthogonalKer_starProjection T hT_closed]
    · calc
        Tdag.adjoint.comp (adjoint T) = closedRangeProjection T hT_closed := by
          rw [adjoint_moorePenroseInverseOperator_comp_adjoint_eq_closedRangeProjection T hT_closed]
        _ = closedRangeProjection Tdag.adjoint hTdagAdj_closed := by
          simp [closedRangeProjection, Tdag,
            adjoint_moorePenroseInverseOperator_range_eq_range T hT_closed]
  have htfae := isMoorePenroseInverse_tfae_projection_and_orthogonal_conditions (adjoint T)
    Tdag.adjoint (adjoint_range_isClosed_of_isClosed_range T hT_closed) hTdagAdj_closed
  have hmp : IsMoorePenroseInverse (adjoint T) Tdag.adjoint :=
    (List.TFAE.out htfae 1 0).mp hproj
  exact eq_moorePenroseInverseOperator_of_isMoorePenroseInverse (adjoint T)
    (adjoint_range_isClosed_of_isClosed_range T hT_closed) Tdag.adjoint hmp

-- Proof sketch: rewrite `(T∗)†` by clause (ii), then take adjoints of `T† T = P_(ker T)ᗮ` and
-- use self-adjointness of orthogonal projection.
/-- Corollary 3.32 (iii): if `T` has closed range, then `T∗ (T∗)† = T† T`. -/
theorem adjoint_comp_moorePenroseInverseOperator_adjoint_eq_moorePenroseInverseOperator_comp
    (T : 𝓗 →L[ℝ] 𝓚) (hT_closed : IsClosed (T.range : Set 𝓚)) :
    (adjoint T).comp
        (moorePenroseInverseOperator (adjoint T)
          (adjoint_range_isClosed_of_isClosed_range T hT_closed)) =
      (moorePenroseInverseOperator T hT_closed).comp T := by
  calc
    (adjoint T).comp
        (moorePenroseInverseOperator (adjoint T)
          (adjoint_range_isClosed_of_isClosed_range T hT_closed)) =
        (adjoint T).comp (moorePenroseInverseOperator T hT_closed).adjoint := by
          rw [← adjoint_moorePenroseInverseOperator_eq_moorePenroseInverseOperator_adjoint T
            hT_closed]
    _ = ((moorePenroseInverseOperator T hT_closed).comp T).adjoint := by
      simp [adjoint_comp]
    _ = (moorePenroseInverseOperator T hT_closed).comp T := by
      rw [moorePenroseInverseOperator_comp_eq_orthogonalKer_starProjection T hT_closed]
      simpa using (isSelfAdjoint_starProjection (T.kerᗮ : Submodule ℝ 𝓗)).adjoint_eq

-- Proof sketch: `T† T` is the orthogonal projection onto `(ker T)ᗮ`, and
-- `P_(ker T) = Id - P_(ker T)ᗮ`.
/-- Corollary 3.32 (iv): if `T` has closed range, then `P_(ker T) = Id - T† T`. -/
theorem ker_starProjection_eq_id_sub_moorePenroseInverseOperator_comp (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    T.ker.starProjection =
      ContinuousLinearMap.id ℝ 𝓗 - (moorePenroseInverseOperator T hT_closed).comp T := by
  calc
    T.ker.starProjection = ContinuousLinearMap.id ℝ 𝓗 - T.kerᗮ.starProjection := by
      simpa using ((T.kerᗮ : Submodule ℝ 𝓗).starProjection_orthogonal)
    _ = ContinuousLinearMap.id ℝ 𝓗 - (moorePenroseInverseOperator T hT_closed).comp T := by
      rw [moorePenroseInverseOperator_comp_eq_orthogonalKer_starProjection T hT_closed]
