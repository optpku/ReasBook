/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace

section

variable (n : ℕ)

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
/- Lemma 5.4.4.2 lies in the Chapter 5 self-concordant-barrier / positive-semidefinite-cone
domain.

Sampled owner-style declarations:
* `𝕊^n₊₊` from `Definition_5_4_4_5`, the source-facing owner for the strict cone
  `int(𝕊ⁿ₊)`;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the Chapter 5 owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  from `Theorem_5_4_1_2`, the canonical owner theorem behind this lower bound;
* `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone` from
  `Theorem_5_4_4_3`, the chapter barrier instance on the same strict cone.

Best owner abstraction:
* source-facing: the strict cone `𝕊^n₊₊`;
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* bridge/view: `𝕊^n₊₊ = interior (𝕊^n₊)`.

Primitive data:
* `n : ℕ`.

Derived API:
* the barrier-owner hypothesis on `𝕊^n₊₊`;
* the dimension lower bound `(n : ℝ) ≤ (ν : ℝ)`.

This file therefore uses the strict-cone owner already introduced upstream instead of keeping the
raw `interior (𝕊^n₊)` surface in the main statement, and it reuses the Chapter 5 symmetric-space
owner file for the ambient Hilbert-space and completeness structure instead of rebuilding a
parallel local instance tower.
-/

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` to the cone `𝕊^n₊` in the
-- intrinsic symmetric space `𝕊^n`, with base point the identity matrix,
-- recession directions the rank-one matrices `eᵢ eᵢᵀ`, and coefficients `αᵢ = βᵢ = 1`. Then
-- `I - ∑ i, eᵢ eᵢᵀ = 0` lies in the cone, each backward step `I - eᵢ eᵢᵀ` lies on the boundary
-- rather than in the interior, and the left-hand side becomes `∑ i, 1 = n`.
/-- Helper for Lemma 5.4.4.2: the diagonal single-entry projector belongs to the symmetric
subspace `𝕊^n`. -/
private theorem coordinate_projector_diagonal_mem_symmetric_subspace
    (i : Fin n) :
    Matrix.diagonal (Pi.single i (1 : ℝ)) ∈ 𝕊^n := by
  -- A diagonal matrix is symmetric, so it lands in the intrinsic symmetric subspace.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm, Matrix.IsSymm]
  ext j k
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [hjk, eq_comm]

/-- Helper for Lemma 5.4.4.2: the `i`-th coordinate rank-one projector, viewed in `𝕊^n`. -/
private def coordinateProjector
    (n : ℕ) (i : Fin n) : 𝕊^n :=
  ⟨Matrix.diagonal (Pi.single i (1 : ℝ)),
    coordinate_projector_diagonal_mem_symmetric_subspace (n := n) i⟩

/-- Helper for Lemma 5.4.4.2: the coordinate projector is the diagonal matrix with a single `1`
in the `i`-th diagonal position. -/
private theorem coordinate_projector_eq_diagonal_single
    (i : Fin n) :
    ((coordinateProjector n i : 𝕊^n) : Mat) = Matrix.diagonal (Pi.single i (1 : ℝ)) := by
  -- The new projector model is definitionally the diagonal single-entry matrix.
  rfl

/-- Helper for Lemma 5.4.4.2: each coordinate projector is positive semidefinite. -/
private theorem coordinate_projector_posSemidef
    (i : Fin n) :
    (((coordinateProjector n i : 𝕊^n) : Mat)).PosSemidef := by
  -- The projector has nonnegative diagonal entries, so its quadratic form is nonnegative.
  rw [coordinate_projector_eq_diagonal_single (n := n) i]
  exact Matrix.PosSemidef.diagonal <| by
    intro j
    by_cases hji : j = i
    · simp [Pi.single_apply, hji]
    · simp [hji]

/-- Helper for Lemma 5.4.4.2: each coordinate projector is a recession direction of the
positive-semidefinite cone. -/
private theorem coordinate_projector_recession_of_positiveSemidefiniteCone
    (i : Fin n) :
    ∀ ⦃X : 𝕊^n⦄, X ∈ (𝕊^n₊ : Set (𝕊^n)) → ∀ t : ℝ, 0 ≤ t →
      X + t • coordinateProjector n i ∈ (𝕊^n₊ : Set (𝕊^n)) := by
  intro X hX t ht
  -- Adding a nonnegative multiple of a PSD rank-one projector preserves positive semidefiniteness.
  rw [mem_positiveSemidefiniteCone_iff] at hX ⊢
  have hscaled : (t • (((coordinateProjector n i : 𝕊^n) : Mat))).PosSemidef :=
    (coordinate_projector_posSemidef (n := n) i).smul ht
  simpa using hX.add hscaled

/-- Helper for Lemma 5.4.4.2: moving one unit backward along a coordinate projector leaves the
strict cone `𝕊^n₊₊`. -/
private theorem one_sub_coordinate_projector_not_mem_strictPositiveSemidefiniteCone
    (i : Fin n) :
    (1 : 𝕊^n) - coordinateProjector n i ∉ (𝕊^n₊₊ : Set (𝕊^n)) := by
  intro hmem
  -- Route correction: use the boundary witness `eᵢ`, where the quadratic form of `I - eᵢ eᵢᵀ`
  -- vanishes, instead of trying to characterize the boundary abstractly.
  let M : Mat := (((1 : 𝕊^n) - coordinateProjector n i : 𝕊^n) : Mat)
  let u : Fin n → ℝ := Pi.single i (1 : ℝ)
  have hpos : M.PosDef := by
    simpa using
      (strictPositiveSemidefiniteCone_posDef
        (X := ⟨(1 : 𝕊^n) - coordinateProjector n i, hmem⟩))
  have hmul : M *ᵥ u = 0 := by
    -- The `i`-th column of `I - eᵢ eᵢᵀ` is zero.
    rw [Matrix.mulVec_single_one]
    ext j
    by_cases hji : j = i
    · subst hji
      simp [M, coordinate_projector_eq_diagonal_single]
    · simp [M, coordinate_projector_eq_diagonal_single, hji]
  have hu_ne : u ≠ 0 := by
    -- The boundary witness has a nonzero `i`-th coordinate.
    change (Pi.single i (1 : ℝ) : Fin n → ℝ) ≠ 0
    exact (Pi.single_eq_zero_iff (i := i)).not.mpr one_ne_zero
  have hzero_lt : (0 : ℝ) < 0 := by
    -- Positive definiteness on `u` contradicts the vanishing quadratic form.
    have hquad_pos : 0 < dotProduct u (M *ᵥ u) := hpos.dotProduct_mulVec_pos hu_ne
    have hquad_zero : dotProduct u (M *ᵥ u) = 0 := by
      rw [hmul, dotProduct_zero]
    exact hquad_zero.symm ▸ hquad_pos
  exact (lt_irrefl 0) hzero_lt

/-- Helper for Lemma 5.4.4.2: the coordinate projectors sum to the identity matrix. -/
private theorem sum_coordinate_projectors_eq_one :
    ∑ i : Fin n, coordinateProjector n i = (1 : 𝕊^n) := by
  -- Summing the diagonal single-entry projectors reconstructs the identity diagonal.
  apply Subtype.ext
  simpa [coordinate_projector_eq_diagonal_single, Matrix.diagonal_single] using
    (Matrix.sum_single_one : ∑ i : Fin n, Matrix.single i i (1 : ℝ) = (1 : Mat))

/-- Helper for Lemma 5.4.4.2: the strict cone is nonempty because the identity is positive
definite. -/
private theorem one_mem_strictPositiveSemidefiniteCone :
    (1 : 𝕊^n) ∈ (𝕊^n₊₊ : Set (𝕊^n)) := by
  -- The identity matrix is strictly positive definite, hence belongs to the strict cone.
  exact
    mem_strictPositiveSemidefiniteCone_of_posDef
      (X := (1 : 𝕊^n))
      (by simpa using (Matrix.PosDef.one : (1 : Mat).PosDef))

/-- Helper for Lemma 5.4.4.2: freeze the source-facing strict cone as a set so later metric-topology
arguments do not re-expand it with a different `TopologicalSpace` instance. -/
private def strictPositiveSemidefiniteConeSet (n : ℕ) : Set (𝕊^n) :=
  (𝕊^n₊₊ : Set (𝕊^n))

/-- Helper for Lemma 5.4.4.2: every positive-semidefinite point lies in the closure of the strict
cone. -/
private theorem mem_closure_strictPositiveSemidefiniteCone_of_mem_positiveSemidefiniteCone
    {X : 𝕊^n} (hX : X ∈ (𝕊^n₊ : Set (𝕊^n))) :
    X ∈ @closure (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (strictPositiveSemidefiniteConeSet n) := by
  letI : TopologicalSpace (𝕊^n) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  change X ∈ closure (strictPositiveSemidefiniteConeSet n)
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := ε / (‖(1 : 𝕊^n)‖ + 1)
  have hδ_pos : 0 < δ := by
    -- Choose a positive identity shift small enough to fit inside the prescribed metric ball.
    exact div_pos hε (by positivity)
  refine ⟨X + δ • (1 : 𝕊^n), ?_, ?_⟩
  · -- Adding a positive multiple of the identity makes a PSD matrix positive definite.
    rw [mem_positiveSemidefiniteCone_iff] at hX
    refine mem_strictPositiveSemidefiniteCone_of_posDef ?_
    have hδ_posDef : (δ • (1 : Mat)).PosDef :=
      (Matrix.PosDef.one : (1 : Mat).PosDef).smul hδ_pos
    have hstep : (((X + δ • (1 : 𝕊^n) : 𝕊^n) : Mat)).PosDef := by
      simpa [Algebra.smul_def, add_comm, add_left_comm, add_assoc] using
        hδ_posDef.add_posSemidef hX
    simpa [Algebra.smul_def] using hstep
  · -- The identity shift can be chosen with arbitrarily small Frobenius norm.
    have hmul_lt :
        δ * ‖(1 : 𝕊^n)‖ < δ * (‖(1 : 𝕊^n)‖ + 1) := by
      have hnorm_lt : ‖(1 : 𝕊^n)‖ < ‖(1 : 𝕊^n)‖ + 1 := by linarith
      exact mul_lt_mul_of_pos_left hnorm_lt hδ_pos
    have hden_ne : ‖(1 : 𝕊^n)‖ + 1 ≠ 0 := by positivity
    have hsub : X - (X + δ • (1 : 𝕊^n)) = -(δ • (1 : 𝕊^n)) := by
      abel
    calc
      dist X (X + δ • (1 : 𝕊^n)) = ‖δ • (1 : 𝕊^n)‖ := by
        rw [dist_eq_norm, hsub, norm_neg]
      _ = |δ| * ‖(1 : 𝕊^n)‖ := norm_smul _ _
      _ = δ * ‖(1 : 𝕊^n)‖ := by rw [abs_of_pos hδ_pos]
      _ < δ * (‖(1 : 𝕊^n)‖ + 1) := hmul_lt
      _ = ε := by
            rw [show δ = ε / (‖(1 : 𝕊^n)‖ + 1) by rfl]
            field_simp [hden_ne]

/-- Helper for Lemma 5.4.4.2: each coordinate projector is a recession direction of the closure
of the strict cone. -/
private theorem coordinate_projector_recession_of_closure_strictPositiveSemidefiniteCone
    (i : Fin n) :
    ∀ ⦃X : 𝕊^n⦄,
      X ∈ @closure (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (strictPositiveSemidefiniteConeSet n) →
      ∀ t : ℝ, 0 ≤ t →
        X + t • coordinateProjector n i ∈
          @closure (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
            (strictPositiveSemidefiniteConeSet n) := by
  intro X hX t ht
  letI : TopologicalSpace (𝕊^n) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  change X + t • coordinateProjector n i ∈ closure (strictPositiveSemidefiniteConeSet n)
  change X ∈ closure (strictPositiveSemidefiniteConeSet n) at hX
  let shift : 𝕊^n → 𝕊^n := fun Y ↦ Y + t • coordinateProjector n i
  have hshift_cont : Continuous shift := by
    -- Translation by a fixed symmetric matrix is continuous in the Frobenius metric.
    fun_prop
  have hmaps : Set.MapsTo shift (strictPositiveSemidefiniteConeSet n)
      (closure (strictPositiveSemidefiniteConeSet n)) := by
    intro Y hY
    -- Strict-cone points are PSD, and the projector recession step keeps PSD points PSD.
    have hY_strict :
        Y ∈ @interior (𝕊^n) instTopologicalSpaceSubtype (𝕊^n₊ : Set (𝕊^n)) := by
      simpa [strictPositiveSemidefiniteConeSet] using hY
    have hY_psd : Y ∈ (𝕊^n₊ : Set (𝕊^n)) :=
      @interior_subset (𝕊^n) instTopologicalSpaceSubtype (𝕊^n₊ : Set (𝕊^n)) Y hY_strict
    exact
      mem_closure_strictPositiveSemidefiniteCone_of_mem_positiveSemidefiniteCone (n := n) <|
        coordinate_projector_recession_of_positiveSemidefiniteCone (n := n) i hY_psd t ht
  have hshift_mem :
      shift X ∈ closure (closure (strictPositiveSemidefiniteConeSet n)) :=
    map_mem_closure (f := shift) hshift_cont hX hmaps
  simpa [shift, closure_closure] using hshift_mem

/-- Helper for Lemma 5.4.4.2: the remaining metric-topology blocker is to identify the current
Frobenius interior of the current closure of the source strict cone with the source strict cone
itself. -/
private theorem strictPositiveSemidefiniteCone_eq_metricInterior_closure :
    {ν : NNReal} → {F : 𝕊^n → ℝ} →
    IsSelfConcordantBarrierOnWith (𝕊^n₊₊ : Set (𝕊^n)) ν F →
    @interior (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (@closure (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (strictPositiveSemidefiniteConeSet n)) =
      strictPositiveSemidefiniteConeSet n := by
  intro ν F hF
  -- Route correction: specialize the generic self-concordant-domain identity from
  -- `Theorem_5_1_3` instead of rebuilding a PSD-topology bridge.
  simpa [strictPositiveSemidefiniteConeSet] using
    hF.toIsStandardSelfConcordantOn.interior_closure_eq

/-- Lemma 5.4.4.2: every `ν`-self-concordant barrier for the cone `𝕊ⁿ₊` of positive semidefinite
real `n × n` matrices has barrier parameter at least `n`. -/
theorem positiveSemidefiniteCone_barrierParameter_ge_dimension
    {ν : NNReal} {F : 𝕊^n → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (𝕊^n₊₊ : Set (𝕊^n)) ν F) :
    (n : ℝ) ≤ (ν : ℝ) := by
  let Q : Set (𝕊^n) :=
    @closure (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (strictPositiveSemidefiniteConeSet n)
  have hQ_convex : Convex ℝ Q := by
    -- The closure of the self-concordant domain remains convex.
    letI : TopologicalSpace (𝕊^n) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    simpa [Q, strictPositiveSemidefiniteConeSet] using
      hF.toIsStandardSelfConcordantOn.convex_domain.closure
  have hFQ :
      IsSelfConcordantBarrierOnWith
        (@interior (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace Q) ν F := by
    -- Rewrite the barrier domain against the closure-domain owner required by the generic lower
    -- bound.
    change IsSelfConcordantBarrierOnWith
      (@interior (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (@closure (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (strictPositiveSemidefiniteConeSet n))) ν F
    convert hF using 1
    exact strictPositiveSemidefiniteCone_eq_metricInterior_closure (n := n) hF
  have hxBar :
      (1 : 𝕊^n) ∈ @interior (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace Q := by
    -- The identity stays as the interior base point after the same domain rewrite.
    change (1 : 𝕊^n) ∈
      @interior (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (@closure (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (strictPositiveSemidefiniteConeSet n))
    convert one_mem_strictPositiveSemidefiniteCone (n := n) using 1
    exact strictPositiveSemidefiniteCone_eq_metricInterior_closure (n := n) hF
  have hy : (1 : 𝕊^n) - ∑ i : Fin n, (1 : ℝ) • coordinateProjector n i ∈
      Q := by
    -- The chosen recession directions exactly sum to the identity, so the endpoint is `0`, which
    -- lies in the closure of the strict cone because `0` is positive semidefinite.
    have hzero_mem : (0 : 𝕊^n) ∈ Q := by
      change (0 : 𝕊^n) ∈
        @closure (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (strictPositiveSemidefiniteConeSet n)
      exact mem_closure_strictPositiveSemidefiniteCone_of_mem_positiveSemidefiniteCone (n := n) <| by
        rw [mem_positiveSemidefiniteCone_iff]
        simpa using (Matrix.PosSemidef.zero : (0 : Mat).PosSemidef)
    simpa [Q, one_smul, sum_coordinate_projectors_eq_one (n := n)] using hzero_mem
  have hbound :
      ∑ i : Fin n, (1 : ℝ) / 1 ≤ (ν : ℝ) :=
    hFQ.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions
      hQ_convex
      hxBar
      (coordinateProjector n)
      (by
        intro i
        exact coordinate_projector_recession_of_closure_strictPositiveSemidefiniteCone (n := n) i)
      (β := fun _ : Fin n ↦ (1 : ℝ))
      (α := fun _ : Fin n ↦ (1 : ℝ))
      (by
        intro i
        norm_num)
      (by
        intro i
        -- The backward-exit witness is unchanged after rewriting `interior Q` back to the strict
        -- cone.
        simpa [Q, one_smul] using
          (show (1 : 𝕊^n) - coordinateProjector n i ∉
            @interior (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
              (@closure (𝕊^n) PseudoMetricSpace.toUniformSpace.toTopologicalSpace
                (strictPositiveSemidefiniteConeSet n)) from by
            rw [strictPositiveSemidefiniteCone_eq_metricInterior_closure (n := n) hF]
            simpa [strictPositiveSemidefiniteConeSet] using
              one_sub_coordinate_projector_not_mem_strictPositiveSemidefiniteCone (n := n) i))
      (by
        intro i
        norm_num)
      hy
  -- The source lower bound specializes to `n ≤ ν` because the finite sum has `n` unit terms.
  simpa using hbound

end

end
