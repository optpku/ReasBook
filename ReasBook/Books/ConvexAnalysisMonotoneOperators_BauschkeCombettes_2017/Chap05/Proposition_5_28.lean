/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Corollary_3_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_14

-- Declarations for this item will be appended below by the statement pipeline.

open EuclideanGeometry
open Filter Function
open scoped Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H_univ" => (Set.univ : Set H)

/-- The fixed-point linear subspace of a continuous linear endomorphism. -/
abbrev fixedSubspace (T : H →L[ℝ] H) : Submodule ℝ H :=
  (T - ContinuousLinearMap.id ℝ H).ker

-- Proof sketch: unfold `fixedSubspace`; membership in the kernel of `T - id` is equivalent to
-- `(T - id) x = 0`, which rearranges to the fixed-point equation `T x = x`.
omit [CompleteSpace H] in
/-- Membership in `fixedSubspace T` means that `x` is a fixed point of `T`. -/
theorem mem_fixedSubspace_iff {T : H →L[ℝ] H} {x : H} :
    x ∈ fixedSubspace T ↔ T x = x := by
  -- Unfold the kernel description of `fixedSubspace T`.
  constructor
  · intro hx
    have hx' : (T - ContinuousLinearMap.id ℝ H) x = 0 := hx
    exact sub_eq_zero.mp hx'
  · intro hx
    change (T - ContinuousLinearMap.id ℝ H) x = 0
    exact sub_eq_zero.mpr hx

/-- Helper for Proposition 5.28: the ambient linear map `T` induces a self-map of `Set.univ`. -/
private def liftUnivMap (T : H →L[ℝ] H) : H_univ → H_univ :=
  fun x ↦ ⟨T x, Set.mem_univ _⟩

omit [CompleteSpace H] in
/-- Helper for Proposition 5.28: coercing the lifted universal self-map back to the ambient space
recovers the original linear map. -/
private theorem liftUnivMap_coe {T : H →L[ℝ] H} (x : H_univ) :
    ((liftUnivMap T x : H_univ) : H) = T (x : H) :=
  rfl

attribute [simp] liftUnivMap_coe

omit [CompleteSpace H] in
/-- Helper for Proposition 5.28: the lifted Picard orbit on `Set.univ` has ambient value
`(T^[n]) x₀`. -/
private theorem lift_univ_iterate_coe {T : H →L[ℝ] H} (x₀ : H) :
    ∀ n : ℕ,
      ((((liftUnivMap T)^[n]) ⟨x₀, Set.mem_univ _⟩ : H_univ) : H) = (T^[n]) x₀
  | 0 => rfl
  | n + 1 => by
      -- Push one iterate through the coercion and then use the induction hypothesis.
      rw [Function.iterate_succ_apply', liftUnivMap_coe, lift_univ_iterate_coe,
        Function.iterate_succ_apply']

/-- Helper for Proposition 5.28: the affine subspace underlying `fixedSubspace T` is nonempty. -/
private instance fixedSubspace_toAffineSubspace_nonempty (T : H →L[ℝ] H) :
    Nonempty (fixedSubspace T).toAffineSubspace := by
  refine ⟨⟨0, ?_⟩⟩
  exact (Submodule.mem_toAffineSubspace).2 (by simp [fixedSubspace])

/-- Helper for Proposition 5.28: the direction of the affine subspace underlying `fixedSubspace T`
has the canonical orthogonal projection. -/
private instance fixedSubspace_toAffineSubspace_hasOrthogonalProjection (T : H →L[ℝ] H) :
    (fixedSubspace T).toAffineSubspace.direction.HasOrthogonalProjection := by
  rw [Submodule.toAffineSubspace_direction]
  infer_instance

omit [CompleteSpace H] in
/-- Helper for Proposition 5.28: the fixed-point subspace of a continuous linear endomorphism is
closed. -/
private theorem fixedSubspace_isClosed (T : H →L[ℝ] H) :
    IsClosed ((fixedSubspace T : Submodule ℝ H) : Set H) := by
  -- The fixed-point subspace is the kernel of the continuous linear map `T - id`.
  simpa [fixedSubspace] using (T - ContinuousLinearMap.id ℝ H).isClosed_ker

/-- Helper for Proposition 5.28: on the affine subspace associated with `fixedSubspace T`, the
metric projection agrees with the orthogonal projection `starProjection`. -/
private theorem projectionPoint_toAffineSubspace_eq_starProjection {T : H →L[ℝ] H}
    (h_nonempty : (((fixedSubspace T).toAffineSubspace : AffineSubspace ℝ H) : Set H).Nonempty)
    (h_closed : IsClosed ((((fixedSubspace T).toAffineSubspace : AffineSubspace ℝ H) : Set H)))
    (x : H) :
    projectionPoint
        (((fixedSubspace T).toAffineSubspace : AffineSubspace ℝ H) : Set H)
        (isChebyshev_of_nonempty_isClosed_convex h_nonempty h_closed
          ((fixedSubspace T).toAffineSubspace).convex) x =
      (fixedSubspace T).starProjection x := by
  -- First identify the metric projector with the affine orthogonal projection.
  calc
    projectionPoint
        (((fixedSubspace T).toAffineSubspace : AffineSubspace ℝ H) : Set H)
        (isChebyshev_of_nonempty_isClosed_convex h_nonempty h_closed
          ((fixedSubspace T).toAffineSubspace).convex) x =
      (orthogonalProjection ((fixedSubspace T).toAffineSubspace) x : H) := by
        rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
          h_nonempty h_closed]
    -- Then use the defining orthogonality characterization of `starProjection`.
    _ = (fixedSubspace T).starProjection x := by
        refine (coe_orthogonalProjection_eq_iff_mem).2 ?_
        constructor
        · exact (Submodule.mem_toAffineSubspace).2
            ((fixedSubspace T).starProjection_apply_mem x)
        · rw [Submodule.toAffineSubspace_direction]
          exact (fixedSubspace T).sub_starProjection_mem_orthogonal x

omit [CompleteSpace H] in
/-- Helper for Proposition 5.28: the Picard orbit of a nonexpansive linear map is Fejér monotone
with respect to its fixed-point subspace. -/
private theorem picard_fejerMonotone_fixedSubspace {T : H →L[ℝ] H}
    (hT : LipschitzWith 1 T) (x₀ : H) :
    FejerMonotone ((fixedSubspace T : Submodule ℝ H) : Set H) (fun n ↦ (T^[n]) x₀) := by
  intro z hz n
  have hz_fix : T z = z := (mem_fixedSubspace_iff).mp hz
  -- Compare the next iterate to the fixed point `z` using nonexpansiveness.
  have hdist :
      dist (T ((T^[n]) x₀)) (T z) ≤ dist ((T^[n]) x₀) z := by
    simpa [one_mul] using hT.dist_le_mul ((T^[n]) x₀) z
  simpa [hz_fix, Function.iterate_succ_apply'] using hdist

/-- Helper for Proposition 5.28: Fejér monotonicity of the Picard orbit forces every shadow
`P_{Fix T} (x_n)` to equal the initial shadow `P_{Fix T} (x₀)`. -/
private theorem starProjection_eq_initial_of_fejerMonotone_fixedSubspace {T : H →L[ℝ] H}
    (x : ℕ → H) (hfejer : FejerMonotone ((fixedSubspace T : Submodule ℝ H) : Set H) x) (n : ℕ) :
    (fixedSubspace T).starProjection (x n) = (fixedSubspace T).starProjection (x 0) := by
  let C : AffineSubspace ℝ H := (fixedSubspace T).toAffineSubspace
  have hC_nonempty : (C : Set H).Nonempty := by
    exact ⟨0, (Submodule.mem_toAffineSubspace).2 (by simp [fixedSubspace])⟩
  have hC_closed : IsClosed (C : Set H) := by
    simpa [C, Submodule.mem_toAffineSubspace] using fixedSubspace_isClosed T
  have hfejer_aff : FejerMonotone (C : Set H) x := by
    simpa [C, Submodule.mem_toAffineSubspace] using hfejer
  -- Apply Proposition 5.9(i) to the affine subspace underlying `fixedSubspace T`.
  calc
    (fixedSubspace T).starProjection (x n) =
        projectionPoint (C : Set H)
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex) (x n) := by
            symm
            exact projectionPoint_toAffineSubspace_eq_starProjection hC_nonempty hC_closed (x n)
    _ =
        projectionPoint (C : Set H)
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex) (x 0) :=
        projectionPoint_eq_initial_of_fejerMonotone_affineSubspace
          hC_nonempty hC_closed x hfejer_aff n
    _ = (fixedSubspace T).starProjection (x 0) :=
        projectionPoint_toAffineSubspace_eq_starProjection hC_nonempty hC_closed (x 0)

-- Proof sketch: if the Picard orbit converges to the orthogonal projection onto `fixedSubspace T`,
-- then consecutive differences converge to `0` by continuity of subtraction. Conversely,
-- linearity makes `T` odd, so Theorem 5.14(ii) gives strong convergence of the orbit from the
-- asymptotic-regularity hypothesis. Proposition 5.9(i) applied to the affine subspace
-- `fixedSubspace T` then identifies the strong limit with the projection of `x₀`.
/-- Proposition 5.28: if `T` is a nonexpansive bounded linear operator on a real Hilbert space,
then the Picard iterates converge strongly to the orthogonal projection of `x₀` onto the fixed-
point subspace `fixedSubspace T = Fix T` if and only if the successive differences converge
strongly to `0`. -/
theorem tendsto_iterates_to_starProjection_fixedSubspace_iff_tendsto_residual_zero_of_nonexpansive
    {T : H →L[ℝ] H} (hT : LipschitzWith 1 T) (x₀ : H) :
    Tendsto (fun n ↦ (T^[n]) x₀) atTop (𝓝 ((fixedSubspace T).starProjection x₀)) ↔
      Tendsto (fun n ↦ (T^[n]) x₀ - (T^[n + 1]) x₀) atTop (𝓝 (0 : H)) := by
  constructor
  · intro hlim
    have hshift :
        Tendsto (fun n ↦ (T^[n + 1]) x₀) atTop (𝓝 ((fixedSubspace T).starProjection x₀)) := by
      -- Shifting a convergent orbit preserves its limit.
      simpa [Nat.add_comm] using hlim.comp (tendsto_add_atTop_nat 1)
    -- Subtract the shifted orbit from the original one and simplify the limit.
    simpa using hlim.sub hshift
  · intro hres
    let x₀u : (Set.univ : Set H) := ⟨x₀, Set.mem_univ _⟩
    have hfejer :
        FejerMonotone ((fixedSubspace T : Submodule ℝ H) : Set H) (fun n ↦ (T^[n]) x₀) :=
      picard_fejerMonotone_fixedSubspace hT x₀
    have hLift : LipschitzWith 1 (liftUnivMap T) := by
      intro x y
      -- The lifted map has the same distance estimate as the ambient linear map.
      simpa [one_mul] using hT.edist_le_mul x y
    have hres_univ :
        Tendsto
          (fun n ↦
            ((((liftUnivMap T)^[n]) x₀u : (Set.univ : Set H)) : H) -
              (liftUnivMap T (((liftUnivMap T)^[n]) x₀u) : H))
          atTop (𝓝 (0 : H)) := by
      -- Rewrite the lifted residual sequence back to the ambient Picard residuals.
      simpa [x₀u, Function.iterate_succ_apply', lift_univ_iterate_coe] using hres
    rcases
        tendsto_iterates_to_fixedPoint_of_residual_tendsto_zero_of_nonexpansive_of_symmetric_of_odd
          (D := (Set.univ : Set H)) isClosed_univ convex_univ
          (T := liftUnivMap T) hLift x₀u hres_univ
          (by
            intro x hx
            simp)
          (by
            intro x
            change T (-(x : H)) = -(T (x : H))
            exact T.map_neg (x : H)) with
      ⟨z, hz_fix, hzlim⟩
    have hz_mem : (z : H) ∈ fixedSubspace T := by
      -- The fixed point returned by Theorem 5.14(ii) is an element of `Fix T`.
      apply (mem_fixedSubspace_iff).mpr
      rw [Function.mem_fixedPoints_iff] at hz_fix
      exact congrArg Subtype.val hz_fix
    have hzlim' : Tendsto (fun n ↦ (T^[n]) x₀) atTop (𝓝 (z : H)) := by
      -- Coerce the lifted strong convergence statement back to the ambient Picard orbit.
      simpa [x₀u, lift_univ_iterate_coe] using hzlim
    have hproj_tendsto :
        Tendsto (fun n ↦ (fixedSubspace T).starProjection ((T^[n]) x₀)) atTop
          (𝓝 ((fixedSubspace T).starProjection (z : H))) := by
      -- Pass the strong convergence through the continuous linear projection.
      exact ((fixedSubspace T).starProjection.continuous.tendsto (z : H)).comp hzlim'
    have hproj_eventually :
        (fun n ↦ (fixedSubspace T).starProjection ((T^[n]) x₀)) =ᶠ[atTop]
          fun _ : ℕ ↦ (fixedSubspace T).starProjection x₀ := by
      -- Proposition 5.9(i) makes every projection shadow equal to the initial one.
      exact Filter.Eventually.of_forall fun n ↦
        starProjection_eq_initial_of_fejerMonotone_fixedSubspace
          (x := fun k ↦ (T^[k]) x₀) hfejer n
    have hproj_eq :
        (fixedSubspace T).starProjection (z : H) = (fixedSubspace T).starProjection x₀ :=
      tendsto_nhds_unique_of_eventuallyEq hproj_tendsto tendsto_const_nhds hproj_eventually
    have hz_eq :
        (z : H) = (fixedSubspace T).starProjection x₀ := by
      -- Because `z ∈ fixedSubspace T`, the projection fixes `z`.
      simpa [((fixedSubspace T).starProjection_eq_self_iff).2 hz_mem] using hproj_eq
    -- Replace the strong limit `z` by the identified projection of the initial point.
    simpa [hz_eq] using hzlim'

end
