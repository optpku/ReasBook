/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_27

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open ContinuousLinearMap

universe u v

variable {𝓗 : Type u} {𝓚 : Type v}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

/-- A bounded operator `T' : 𝓚 →L[ℝ] 𝓗` is the Moore-Penrose inverse of `T` when each `T' y`
lies in `(ker T)ᗮ` and solves the normal equation `T* T x = T* y`. -/
class IsMoorePenroseInverse (T : 𝓗 →L[ℝ] 𝓚) (T' : 𝓚 →L[ℝ] 𝓗) : Prop where
  mem_orthogonalKer : ∀ y : 𝓚, T' y ∈ T.kerᗮ
  normalEquation : ∀ y : 𝓚, adjoint T (T (T' y)) = adjoint T y

-- Each point in `range T` has a preimage lying in `(ker T)ᗮ`.
omit [CompleteSpace 𝓚] in
private lemma exists_orthogonalKer_preimage_of_mem_range (T : 𝓗 →L[ℝ] 𝓚) {y : 𝓚}
    (hy : y ∈ T.range) :
    ∃ x ∈ T.kerᗮ, T x = y := by
  rcases hy with ⟨x₀, rfl⟩
  refine ⟨x₀ - T.ker.starProjection x₀, ?_, ?_⟩
  · -- Subtracting the kernel projection removes exactly the kernel component.
    exact T.ker.sub_starProjection_mem_orthogonal x₀
  · -- The removed component lies in `ker T`, so `T` does not change.
    have hk_mem : T.ker.starProjection x₀ ∈ T.ker := by
      exact Submodule.starProjection_apply_mem T.ker x₀
    have hk_zero : T (T.ker.starProjection x₀) = 0 := by
      exact (LinearMap.mem_ker).1 hk_mem
    simpa [map_sub, hk_zero]

-- Under the Moore-Penrose normal equation, `T ∘L T'` is the orthogonal projection onto
-- `range T`.
private lemma comp_apply_eq_closedRangeProjection_of_isMoorePenroseInverse
    (T : 𝓗 →L[ℝ] 𝓚) (T' : 𝓚 →L[ℝ] 𝓗)
    (hT_closed : IsClosed (T.range : Set 𝓚))
    (hmp : IsMoorePenroseInverse T T') (y : 𝓚) :
    T (T' y) = closedRangeProjection T hT_closed y := by
  -- The normal equation is exactly the characterization of the closed-range projection.
  exact
    (eq_closedRangeProjection_iff_normal_equation T hT_closed y (T' y)).2 (hmp.normalEquation y)

-- The projection conditions force `ker T` to be the orthogonal complement of `range T'`.
private lemma ker_eq_orthogonal_tilde_range_of_projection_conditions
    (T : 𝓗 →L[ℝ] 𝓚) (T' : 𝓚 →L[ℝ] 𝓗)
    (hT_closed : IsClosed (T.range : Set 𝓚))
    (hT'_closed : IsClosed (T'.range : Set 𝓗))
    (hproj : T ∘L T' = closedRangeProjection T hT_closed ∧
      T' ∘L T = closedRangeProjection T' hT'_closed) :
    T.ker = T'.rangeᗮ := by
  ext x
  constructor
  · intro hx
    -- Kernel vectors are annihilated by the projector onto `range T'`, hence lie in its
    -- orthogonal complement.
    let S : Submodule ℝ 𝓗 := T'.range
    have hzero : closedRangeProjection T' hT'_closed x = 0 := by
      have hrev :=
        congrArg (fun f : 𝓗 →L[ℝ] 𝓗 ↦ f x) hproj.2
      have hx_zero : T x = 0 := (LinearMap.mem_ker).1 hx
      calc
        closedRangeProjection T' hT'_closed x = T' (T x) := by simpa using hrev.symm
        _ = 0 := by simp [hx_zero]
    simpa [S, closedRangeProjection] using
      (show S.starProjection x = 0 ↔ x ∈ Sᗮ from S.starProjection_apply_eq_zero_iff).1 hzero
  · intro hx
    -- Conversely, if the projector onto `range T'` kills `x`, then `T' (T x) = 0`.
    let S : Submodule ℝ 𝓗 := T'.range
    have hzero' : T' (T x) = 0 := by
      have hz : closedRangeProjection T' hT'_closed x = 0 := by
        simpa [S, closedRangeProjection] using
          (show S.starProjection x = 0 ↔ x ∈ Sᗮ from S.starProjection_apply_eq_zero_iff).2 hx
      have hrev :=
        congrArg (fun f : 𝓗 →L[ℝ] 𝓗 ↦ f x) hproj.2
      exact hrev.trans hz
    -- Evaluating `T ∘L T' = P_{range T}` at `T x` gives the identity `T x = T (T' (T x))`.
    have hTx : T x = T (T' (T x)) := by
      have hcomp :=
        congrArg (fun f : 𝓚 →L[ℝ] 𝓚 ↦ f (T x)) hproj.1
      have hself : closedRangeProjection T hT_closed (T x) = T x := by
        exact closedRangeProjection_eq_self_of_mem_range T hT_closed ⟨x, rfl⟩
      simpa [hself] using hcomp.symm
    have hx_zero : T x = 0 := by
      simpa [hzero'] using hTx
    exact (LinearMap.mem_ker).2 hx_zero

-- Under the projection conditions, `range T'` is exactly `(ker T)ᗮ`.
private lemma range_eq_orthogonal_ker_of_projection_conditions
    (T : 𝓗 →L[ℝ] 𝓚) (T' : 𝓚 →L[ℝ] 𝓗)
    (hT_closed : IsClosed (T.range : Set 𝓚))
    (hT'_closed : IsClosed (T'.range : Set 𝓗))
    (hproj : T ∘L T' = closedRangeProjection T hT_closed ∧
      T' ∘L T = closedRangeProjection T' hT'_closed) :
    T'.range = T.kerᗮ := by
  have hker :
      T.ker = T'.rangeᗮ :=
    ker_eq_orthogonal_tilde_range_of_projection_conditions T T' hT_closed hT'_closed hproj
  ext x
  constructor
  · intro hx
    -- Every vector in `range T'` lies in the double orthogonal of `range T'`.
    rw [hker]
    exact Submodule.le_orthogonal_orthogonal (T'.range : Submodule ℝ 𝓗) hx
  · intro hx
    -- Closedness of `range T'` identifies its double orthogonal with itself.
    rw [hker] at hx
    have hclosure : (T'.range : Submodule ℝ 𝓗).topologicalClosure = T'.range := by
      exact IsClosed.submodule_topologicalClosure_eq hT'_closed
    have hx' : x ∈ (T'.range : Submodule ℝ 𝓗).topologicalClosure := by
      simpa [Submodule.orthogonal_orthogonal_eq_closure, hclosure] using hx
    simpa [hclosure] using hx'

-- Proof sketch: `(i) → (ii)` uses the defining projection identities for a Moore-Penrose inverse;
-- `(ii) → (iii)` combines those projection equalities with the orthogonal decompositions along
-- `T.kerᗮ` and `T.rangeᗮ`; `(iii) → (i)` decomposes each `y` into its `range T` and `range Tᗮ`
-- components and uses the normal-equation characterization in `IsMoorePenroseInverse`.
/-- Proposition 3.31: for bounded operators `T : 𝓗 →L[ℝ] 𝓚` and `T' : 𝓚 →L[ℝ] 𝓗` with closed
ranges, the following are equivalent: (i) `T'` is the Moore-Penrose inverse of `T`; (ii)
`T ∘L T'` and `T' ∘L T` are the orthogonal projections onto `range T` and `range T'`; (iii)
`T' ∘L T` is the identity on `T.kerᗮ` and `T'` vanishes on `T.rangeᗮ`. -/
theorem isMoorePenroseInverse_tfae_projection_and_orthogonal_conditions
    (T : 𝓗 →L[ℝ] 𝓚) (T' : 𝓚 →L[ℝ] 𝓗)
    (hT_closed : IsClosed (T.range : Set 𝓚))
    (hT'_closed : IsClosed (T'.range : Set 𝓗)) :
    List.TFAE
      [IsMoorePenroseInverse T T',
        T ∘L T' = closedRangeProjection T hT_closed ∧
          T' ∘L T = closedRangeProjection T' hT'_closed,
        (∀ x ∈ T.kerᗮ, T' (T x) = x) ∧
          ∀ y ∈ T.rangeᗮ, T' y = 0] := by
  -- The source proof runs through the projection identities, then identifies the relevant
  -- orthogonal complements, and finally reconstructs the normal equation from the projection.
  tfae_have 1 → 2 := by
    intro hmp
    refine ⟨?_, ?_⟩
    · -- Clause `(i) → (ii)`, first projection identity: the normal equation identifies
      -- `T (T' y)` with the orthogonal projection of `y` onto `range T`.
      ext y
      exact comp_apply_eq_closedRangeProjection_of_isMoorePenroseInverse T T' hT_closed hmp y
    · -- Clause `(i) → (ii)`, second projection identity: `T' (T x)` is the orthogonal
      -- projection of `x` onto `range T'`.
      ext x
      have hker_mem : x - T' (T x) ∈ T.ker := by
        have hcompTx :
            T (T' (T x)) = closedRangeProjection T hT_closed (T x) := by
          exact comp_apply_eq_closedRangeProjection_of_isMoorePenroseInverse T T' hT_closed hmp
            (T x)
        have hself : closedRangeProjection T hT_closed (T x) = T x := by
          exact closedRangeProjection_eq_self_of_mem_range T hT_closed ⟨x, rfl⟩
        have hzero : T (x - T' (T x)) = 0 := by
          simpa [map_sub, hself] using congrArg (fun z : 𝓚 ↦ T x - z) hcompTx
        exact (LinearMap.mem_ker).2 hzero
      have hker_orth : x - T' (T x) ∈ T.kerᗮᗮ := by
        exact Submodule.le_orthogonal_orthogonal T.ker hker_mem
      have horth : x - T' (T x) ∈ (T'.range : Submodule ℝ 𝓗)ᗮ := by
        rw [Submodule.mem_orthogonal']
        intro z hz
        rcases hz with ⟨y, rfl⟩
        exact
          (Submodule.mem_orthogonal' (T.kerᗮ) (x - T' (T x))).1 hker_orth
            (T' y) (hmp.mem_orthogonalKer y)
      have hmem : T' (T x) ∈ (T'.range : Submodule ℝ 𝓗) := by
        exact ⟨T x, rfl⟩
      let S : Submodule ℝ 𝓗 := T'.range
      have hproj' : S.starProjection x = T' (T x) := by
        simpa [S] using S.eq_starProjection_of_mem_orthogonal hmem horth
      simpa [S, closedRangeProjection] using hproj'.symm
  tfae_have 2 → 3 := by
    intro hproj
    refine ⟨?_, ?_⟩
    · -- Clause `(ii) → (iii)`: identify `range T'` with `(ker T)ᗮ`, then the projector acts as
      -- the identity there.
      intro x hx
      have hrange : T'.range = T.kerᗮ :=
        range_eq_orthogonal_ker_of_projection_conditions T T' hT_closed hT'_closed hproj
      have hx_range : x ∈ T'.range := by
        simpa [hrange] using hx
      have hself : closedRangeProjection T' hT'_closed x = x := by
        exact closedRangeProjection_eq_self_of_mem_range T' hT'_closed hx_range
      have hrev :=
        congrArg (fun f : 𝓗 →L[ℝ] 𝓗 ↦ f x) hproj.2
      simpa [hself] using hrev
    · -- Clause `(ii) → (iii)`: factor `T'` through the projection onto `range T`.
      intro y hy
      have hy_mem : T' y ∈ T'.range := by
        exact ⟨y, rfl⟩
      have hself' : closedRangeProjection T' hT'_closed (T' y) = T' y := by
        exact closedRangeProjection_eq_self_of_mem_range T' hT'_closed hy_mem
      have hrev :=
        congrArg (fun f : 𝓗 →L[ℝ] 𝓗 ↦ f (T' y)) hproj.2
      have hcomp :=
        congrArg (fun f : 𝓚 →L[ℝ] 𝓚 ↦ f y) hproj.1
      have hcomp' : T (T' y) = closedRangeProjection T hT_closed y := by
        simpa using hcomp
      have hfactor : T' y = T' (closedRangeProjection T hT_closed y) := by
        calc
          T' y = T' (T (T' y)) := by
            simpa [hself'] using hrev.symm
          _ = T' (closedRangeProjection T hT_closed y) := by
            rw [hcomp']
      rw [hfactor, closedRangeProjection_eq_zero_of_mem_orthogonalRange T hT_closed hy, map_zero]
  tfae_have 3 → 1 := by
    intro horth
    have hy : ∀ y : 𝓚,
        T' y ∈ T.kerᗮ ∧ adjoint T (T (T' y)) = adjoint T y := by
      intro y
      let p := closedRangeProjection T hT_closed y
      let S : Submodule ℝ 𝓚 := T.range
      have hp_mem : p ∈ T.range := by
        exact closedRangeProjection_mem_range T hT_closed y
      have hres : y - p ∈ T.rangeᗮ := by
        -- The residual from the orthogonal projection lies in the orthogonal complement of
        -- `range T`.
        simpa [p, closedRangeProjection] using S.sub_starProjection_mem_orthogonal y
      rcases exists_orthogonalKer_preimage_of_mem_range T hp_mem with ⟨x₁, hx₁_orth, hx₁_eq⟩
      have hTp : T' p = x₁ := by
        -- On `(ker T)ᗮ`, the composition `T' ∘L T` is the identity.
        simpa [hx₁_eq] using horth.1 x₁ hx₁_orth
      have hTr : T' (y - p) = 0 := by
        -- On `range Tᗮ`, the operator `T'` vanishes.
        exact horth.2 (y - p) hres
      have hpdecomp : p + (y - p) = y := by
        simp [sub_eq_add_neg, add_left_comm]
      have hsplit : T' y = x₁ := by
        -- Decompose `y` into its projected and orthogonal components and apply the two clauses of
        -- condition `(iii)`.
        calc
          T' y = T' (p + (y - p)) := by rw [hpdecomp]
          _ = T' p + T' (y - p) := by rw [map_add]
          _ = x₁ + 0 := by rw [hTp, hTr]
          _ = x₁ := by simp
      have hproj : T (T' y) = p := by
        simpa [hsplit] using hx₁_eq
      refine ⟨?_, ?_⟩
      · -- The decomposition shows `T' y` lies in `(ker T)ᗮ`.
        simpa [hsplit] using hx₁_orth
      · -- The projection identity recovers the normal equation.
        exact
          (eq_closedRangeProjection_iff_normal_equation T hT_closed y (T' y)).1
            (by simpa [p] using hproj)
    refine ⟨?_, ?_⟩
    · intro y
      exact (hy y).1
    · intro y
      exact (hy y).2
  tfae_finish
