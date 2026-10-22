/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_33
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Filter
open scoped Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Theorem 3.1.4.2: a frontier point admits a sequence from the complement converging
to it. -/
lemma exists_complement_sequence_tendsto_of_mem_frontier
    {Q : Set E} {x₀ : E} (hx₀ : x₀ ∈ frontier Q) :
    ∃ y : ℕ → E, (∀ n, y n ∉ Q) ∧ Tendsto y atTop (nhds x₀) := by
  -- Rewrite the frontier point as a limit point of the complement.
  have hx₀_closure_compl : x₀ ∈ closure Qᶜ := by
    have hx₀' : x₀ ∈ closure Q ∩ closure Qᶜ := by
      simpa [frontier_eq_closure_inter_closure] using hx₀
    exact hx₀'.2
  -- Sequentialize the closure statement to obtain the desired approximating sequence.
  rcases (mem_closure_iff_seq_limit.mp hx₀_closure_compl) with ⟨y, hy_mem, hy_tendsto⟩
  refine ⟨y, ?_, hy_tendsto⟩
  intro n hyQ
  exact hy_mem n hyQ

/-- Helper for Theorem 3.1.4.2: the Euclidean projection fixes every point already in the feasible
set. -/
lemma euclideanProjection_eq_self_of_mem
    [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x : E} (hx : x ∈ Q) :
    euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x = x := by
  -- The ambient point itself is a valid projection point once it already lies in `Q`.
  have hxproj : IsProjectionPointOn Q x x := by
    refine ⟨hx, ?_⟩
    simp [Metric.infDist_zero_of_mem hx]
  simpa using
    (hxproj.eq_euclideanProjection hQ_nonempty hQ_closed hQ_convex).symm

/-- Helper for Theorem 3.1.4.2: the normalized displacement from an exterior point to its
projection onto `Q` has unit norm. -/
lemma normalized_projection_direction_norm_eq_one
    [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {y : E} (hy : y ∉ Q) :
    let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex y
    let g := ‖y - p‖⁻¹ • (y - p)
    ‖g‖ = 1 := by
  -- The projection point cannot coincide with the exterior point.
  dsimp
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex y
  have hp : IsProjectionPointOn Q y p := by
    simpa [p] using
      euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex y
  have hy_sub_ne : y - p ≠ 0 := by
    intro hzero
    have hyp : y = p := sub_eq_zero.mp hzero
    exact hy (hyp.symm ▸ hp.1)
  have hnorm_ne : ‖y - p‖ ≠ 0 := norm_ne_zero_iff.mpr hy_sub_ne
  -- Normalize the nonzero displacement vector.
  calc
    ‖‖y - p‖⁻¹ • (y - p)‖ = |‖y - p‖⁻¹| * ‖y - p‖ := norm_smul _ _
    _ = ‖y - p‖⁻¹ * ‖y - p‖ := by
      rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    _ = 1 := by
      field_simp [hnorm_ne]

/-- Helper for Theorem 3.1.4.2: the normalized projection displacement defines a supporting
inequality at the projection point. -/
lemma normalized_projection_direction_le_offset
    [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {y x : E} (hx : x ∈ Q) :
    let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex y
    let g := ‖y - p‖⁻¹ • (y - p)
    inner ℝ g x ≤ inner ℝ g p := by
  -- The projection variational inequality gives the correct sign on the displacement.
  dsimp
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex y
  let g := ‖y - p‖⁻¹ • (y - p)
  have hp : IsProjectionPointOn Q y p := by
    simpa [p] using
      euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex y
  have hinner : inner ℝ (y - p) (x - p) ≤ 0 := by
    have hproj : 0 ≤ inner ℝ (p - y) (x - p) :=
      hp.inner_sub_nonneg hQ_convex hx
    have hproj' : 0 ≤ -inner ℝ (y - p) (x - p) := by
      rw [← inner_neg_left]
      simpa [sub_eq_add_neg] using hproj
    exact neg_nonneg.mp hproj'
  have hscaled : inner ℝ g (x - p) ≤ 0 := by
    rw [show g = ‖y - p‖⁻¹ • (y - p) by rfl, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) hinner
  -- Rewrite the left-hand side around the projection point.
  calc
    inner ℝ g x = inner ℝ g ((x - p) + p) := by abel_nf
    _ = inner ℝ g (x - p) + inner ℝ g p := by rw [inner_add_right]
    _ ≤ 0 + inner ℝ g p := by linarith
    _ = inner ℝ g p := by simp

/-- Helper for Theorem 3.1.4.2: projection points onto the same convex set move no faster than
their base points. -/
lemma projectionPoint_dist_le_dist
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x₁ p₁ x₂ p₂ : E}
    (hp₁ : IsProjectionPointOn Q x₁ p₁) (hp₂ : IsProjectionPointOn Q x₂ p₂) :
    dist p₁ p₂ ≤ dist x₁ x₂ := by
  -- Compare each projection point against the other one as a feasible competitor.
  have h₁ : 0 ≤ inner ℝ (p₁ - x₁) (p₂ - p₁) :=
    hp₁.inner_sub_nonneg hQ_convex hp₂.1
  have h₂ : 0 ≤ inner ℝ (p₂ - x₂) (p₁ - p₂) :=
    hp₂.inner_sub_nonneg hQ_convex hp₁.1
  have hpair : p₂ - p₁ = -(p₁ - p₂) := by
    abel
  have h₁' : inner ℝ (p₁ - x₁) (p₁ - p₂) ≤ 0 := by
    rw [hpair, inner_neg_right] at h₁
    linarith
  have haux : 0 ≤ inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₂ - x₂) (p₁ - p₂) - inner ℝ (p₁ - x₁) (p₁ - p₂) := by
      simp [sub_eq_add_neg, inner_add_left, add_comm, add_left_comm, add_assoc]
    rw [hrewrite]
    linarith
  -- Rearranging isolates the squared norm of `p₁ - p₂`.
  have hmain : ‖p₁ - p₂‖ ^ (2 : ℕ) ≤ inner ℝ (p₁ - p₂) (x₁ - x₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₁ - p₂) (x₁ - x₂) - ‖p₁ - p₂‖ ^ (2 : ℕ) := by
      rw [inner_sub_left, real_inner_comm (x₁ - x₂), real_inner_self_eq_norm_sq]
    rw [hrewrite] at haux
    linarith
  have hcs : inner ℝ (p₁ - p₂) (x₁ - x₂) ≤ ‖p₁ - p₂‖ * ‖x₁ - x₂‖ := by
    simpa [Real.norm_eq_abs] using real_inner_le_norm (p₁ - p₂) (x₁ - x₂)
  have hnorm : ‖p₁ - p₂‖ ≤ ‖x₁ - x₂‖ := by
    nlinarith [hmain, hcs, norm_nonneg (p₁ - p₂), norm_nonneg (x₁ - x₂)]
  simpa [dist_eq_norm] using hnorm

/-- Helper for Theorem 3.1.4.2: the Euclidean projection map onto a convex set is nonexpansive. -/
lemma euclideanProjection_lipschitzWith
    [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q) :
    LipschitzWith 1 (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex) := by
  -- Apply the projection-point distance estimate to the chosen projection selector.
  refine LipschitzWith.mk_one ?_
  intro x₁ x₂
  exact projectionPoint_dist_le_dist hQ_convex
    (euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x₁)
    (euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x₂)

/-- Helper for Theorem 3.1.4.2: projecting a sequence converging to a feasible boundary point
still converges to that boundary point. -/
lemma tendsto_projection_of_tendsto_boundary_point
    [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x₀ : E} (hx₀Q : x₀ ∈ Q) {y : ℕ → E}
    (hy : Tendsto y atTop (nhds x₀)) :
    Tendsto (fun n ↦ euclideanProjection Q hQ_nonempty hQ_closed hQ_convex (y n)) atTop (nhds x₀) := by
  -- Compose convergence with the nonexpansive projection map and identify the limit projection.
  have hproj_tendsto :
      Tendsto (fun n ↦ euclideanProjection Q hQ_nonempty hQ_closed hQ_convex (y n))
        atTop
        (nhds (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x₀)) := by
    exact
      (euclideanProjection_lipschitzWith Q hQ_nonempty hQ_closed hQ_convex).continuous.continuousAt.tendsto.comp hy
  simpa [euclideanProjection_eq_self_of_mem Q hQ_nonempty hQ_closed hQ_convex hx₀Q] using
    hproj_tendsto

/- Theorem 3.1.4.2 lies in the chapter's supporting-nesterovHyperplane domain.

Primary domain:
- supporting hyperplanes of closed convex sets in finite-dimensional real inner-product spaces.

Relevant sampled declarations:
- `AffineHyperplane` in `Definition_3_1_4_1`, the owner of a nonzero normal vector and an offset;
- `AffineHyperplane.IsSupporting`, the owner-level support predicate;
- `nesterovHyperplane`, the coordinate carrier used by the textbook statement;
- `IsSupportingHyperplane`, the coordinate bridge spelling of support.

Best owner abstraction:
- `AffineHyperplane`

Source/core/bridge triage:
- source-facing: the existence of a supporting nesterovHyperplane through a boundary point;
- core/canonical: `AffineHyperplane`, whose primitive data are a nonzero normal vector and an
  offset;
- bridge/view: `nesterovHyperplane g γ` together with `IsSupportingHyperplane Q g γ`.

Primitive data:
- the closed convex set `Q` and the boundary point `x₀`.

Derived API:
- the owner-level witness `H : AffineHyperplane E` supporting `Q` through `x₀`;
- the coordinate witness pair `(g, γ)` obtained by unpacking `H`.

The supporting object is intrinsically an `AffineHyperplane`, so this file now exposes that
owner-level theorem directly. The textbook `(g, γ)` statement is kept as a thin bridge companion,
since later files in the chapter still reuse the coordinate witness shape.
-/

/-- Theorem 3.1.4.2 on the owner surface: if `Q` is a closed convex set in a finite-dimensional
real inner-product space and `x₀` is a boundary point of `Q`, then there exists an affine
nesterovHyperplane `H` such that `x₀ ∈ H` and `H` supports `Q`. The textbook `ℝⁿ` statement is the
specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: choose points `y_k ∉ Q` converging to `x₀`, project them to `Q`, and normalize
-- the displacement vectors `y_k - π_Q(y_k)` to unit normals `g_k`. The projection inequality
-- gives supporting affine hyperplanes `H_k`; compactness of the unit sphere and convergence of
-- the projections yield a limit nesterovHyperplane `H` supporting `Q` and passing through `x₀`.
theorem exists_supporting_affineHyperplane_at_boundary_point_of_closed_convex
    [FiniteDimensional ℝ E] (Q : Set E) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x₀ : E} (hx₀ : x₀ ∈ frontier Q) :
    ∃ H : AffineHyperplane E, x₀ ∈ H ∧ H.IsSupporting Q := by
  -- First recover that the boundary point is feasible, hence `Q` is nonempty.
  have hx₀_closure : x₀ ∈ closure Q := by
    have hx₀' : x₀ ∈ closure Q ∩ closure Qᶜ := by
      simpa [frontier_eq_closure_inter_closure] using hx₀
    exact hx₀'.1
  have hx₀Q : x₀ ∈ Q := by
    simpa [hQ_closed.closure_eq] using hx₀_closure
  let hQ_nonempty : Q.Nonempty := ⟨x₀, hx₀Q⟩
  -- Follow the source proof: approach `x₀` from outside `Q`, then project back to `Q`.
  rcases exists_complement_sequence_tendsto_of_mem_frontier hx₀ with ⟨y, hy_out, hy_tendsto⟩
  let p : ℕ → E := fun n ↦ euclideanProjection Q hQ_nonempty hQ_closed hQ_convex (y n)
  let g : ℕ → E := fun n ↦ ‖y n - p n‖⁻¹ • (y n - p n)
  have hp_tendsto : Tendsto p atTop (nhds x₀) := by
    simpa [p] using
      tendsto_projection_of_tendsto_boundary_point Q hQ_nonempty hQ_closed hQ_convex hx₀Q hy_tendsto
  have hg_norm : ∀ n, ‖g n‖ = 1 := by
    intro n
    simpa [p, g] using
      normalized_projection_direction_norm_eq_one Q hQ_nonempty hQ_closed hQ_convex (hy_out n)
  have hg_mem_sphere : ∀ n, g n ∈ Metric.sphere (0 : E) 1 := by
    intro n
    rw [Metric.mem_sphere, dist_zero_right]
    exact hg_norm n
  -- Compactness of the unit sphere yields a convergent subsequence of normalized normals.
  rcases (isCompact_sphere (0 : E) 1).tendsto_subseq hg_mem_sphere with
    ⟨gStar, hgStar_sphere, φ, hφ_mono, hφ_tendsto⟩
  have hgStar_ne_zero : gStar ≠ 0 := by
    intro hgStar_zero
    have hgStar_norm : ‖gStar‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hgStar_sphere
      exact hgStar_sphere
    rw [hgStar_zero] at hgStar_norm
    norm_num at hgStar_norm
  have hp_subseq_tendsto : Tendsto (fun n ↦ p (φ n)) atTop (nhds x₀) :=
    hp_tendsto.comp hφ_mono.tendsto_atTop
  have hsupport : ∀ x ∈ Q, inner ℝ gStar x ≤ inner ℝ gStar x₀ := by
    intro x hx
    -- Pass the pointwise support inequalities to the subsequential limit.
    have hleft :
        Tendsto (fun n ↦ inner ℝ (g (φ n)) x) atTop (nhds (inner ℝ gStar x)) :=
      Filter.Tendsto.inner hφ_tendsto tendsto_const_nhds
    have hright :
        Tendsto (fun n ↦ inner ℝ (g (φ n)) (p (φ n))) atTop (nhds (inner ℝ gStar x₀)) :=
      Filter.Tendsto.inner hφ_tendsto hp_subseq_tendsto
    have hineq : ∀ n, inner ℝ (g (φ n)) x ≤ inner ℝ (g (φ n)) (p (φ n)) := by
      intro n
      simpa [p, g] using
        normalized_projection_direction_le_offset
          Q hQ_nonempty hQ_closed hQ_convex hx
    exact le_of_tendsto_of_tendsto' hleft hright hineq
  -- Package the limit normal into the supporting affine nesterovHyperplane through `x₀`.
  refine ⟨⟨gStar, hgStar_ne_zero, inner ℝ gStar x₀⟩, ?_, ?_⟩
  · simp
  · constructor
    · intro x hx
      simpa [AffineHyperplane.closedLowerHalfspace] using hsupport x hx
    · refine ⟨x₀, hx₀Q, ?_⟩
      simp

/-- Theorem 3.1.4.2 in textbook coordinates: if `Q` is a closed convex set in a finite-dimensional
real inner-product space and `x₀` is a boundary point of `Q`, then there exist a normal vector `g`
and a scalar `γ` such that `x₀` lies on `nesterovHyperplane g γ` and this nesterovHyperplane supports `Q`. The
textbook `ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
theorem exists_supporting_hyperplane_at_boundary_point_of_closed_convex
    [FiniteDimensional ℝ E] (Q : Set E) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x₀ : E} (hx₀ : x₀ ∈ frontier Q) :
    ∃ g : E, ∃ γ : ℝ, x₀ ∈ nesterovHyperplane g γ ∧ IsSupportingHyperplane Q g γ := by
  rcases
      exists_supporting_affineHyperplane_at_boundary_point_of_closed_convex
        Q hQ_closed hQ_convex hx₀ with
    ⟨H, hx₀H, hH⟩
  refine ⟨H.normal, H.offset, ?_, ?_⟩
  · simpa [AffineHyperplane.carrier_eq_hyperplane] using hx₀H
  · simpa using hH

end
