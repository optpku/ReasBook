/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9_part2

open scoped BigOperators

section Exercise714

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_14.lean`: a linear functional that is
constant on a set vanishes on the direction of its affine span. -/
private lemma affineSpanDirection_le_ker_of_constant
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {F : Set E} {L : E →ₗ[ℝ] ℝ} {x0 : E} {d : ℝ}
    (hx0 : x0 ∈ F)
    (hlevel : ∀ {x : E}, x ∈ F → L x = d) :
    (affineSpan ℝ F).direction ≤ LinearMap.ker L := by
  have hspanLevel : (affineSpan ℝ F : Set E) ⊆ {x | L x = d} := by
    intro x hx
    refine affineSpan_induction hx ?_ ?_
    · intro y hy
      exact hlevel hy
    · intro c u v w hu hv hw
      have huEq : L u = d := hu
      have hvEq : L v = d := hv
      have hwEq : L w = d := hw
      simp [huEq, hvEq, hwEq, sub_eq_add_neg, add_comm]
  have hx0Aff : x0 ∈ affineSpan ℝ F := subset_affineSpan ℝ _ hx0
  intro v hv
  rw [LinearMap.mem_ker]
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0Aff] at hv
  rcases hv with ⟨x, hxAff, rfl⟩
  have hxEq : L x = d := hspanLevel hxAff
  have hx0Eq : L x0 = d := hlevel hx0
  simp [vsub_eq_sub, hxEq, hx0Eq]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_14.lean`: points in the convex hull of
the single-node flow set retain coordinatewise nonnegativity and the total-flow bound. -/
private lemma singleNodeFlowSet_flowBounds_of_mem_convexHull
    {n : ℕ} (a : Fin n → ℝ) (b : ℝ)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ convexHull ℝ (single_node_flow_set a b)) :
    (∀ i, 0 ≤ p.2 i) ∧ (∑ i, p.2 i) ≤ b := by
  constructor
  · intro i
    -- Enclose the generators in the convex coordinate halfspace and pass to their hull.
    refine (convexHull_min
      (t := {q : (Fin n → ℝ) × (Fin n → ℝ) | 0 ≤ q.2 i}) ?_ ?_) hp
    · intro q hq
      exact ((mem_single_node_flow_set_iff a b q).mp hq).2.1 i
    · intro q hq r hr u v hu hv huv
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        add_nonneg (mul_nonneg hu hq) (mul_nonneg hv hr)
  · -- The total-flow halfspace is convex for the same linear reason.
    refine (convexHull_min
      (t := {q : (Fin n → ℝ) × (Fin n → ℝ) | (∑ i, q.2 i) ≤ b}) ?_ ?_) hp
    · intro q hq
      exact ((mem_single_node_flow_set_iff a b q).mp hq).2.2.1
    · intro q hq r hr u v hu hv huv
      calc
        ∑ i, (u • q + v • r).2 i =
            u * (∑ i, q.2 i) + v * (∑ i, r.2 i) := by
              simp [Pi.add_apply, Pi.smul_apply, Finset.mul_sum,
                Finset.sum_add_distrib]
        _ ≤ u * b + v * b := by
          exact add_le_add (mul_le_mul_of_nonneg_left hq hu) (mul_le_mul_of_nonneg_left hr hv)
        _ = b := by
          rw [← add_mul, huv, one_mul]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_14.lean`: if the cover maximum is no
larger than its excess, every positive-part penalty vanishes. -/
private lemma flowCoverValue_eq_coverFlowSum_of_coverMax_le_excess
    {n : ℕ} (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (hC : C.Nonempty)
    (hmax : C.sup' hC a ≤ flow_cover_excess a b C)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flow_cover_value a b C p = ∑ j ∈ C, p.2 j := by
  rw [flow_cover_value_eq]
  -- Bound each cover coefficient by the maximum before removing the zero penalty sum.
  have hpenalty :
      ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have haj : a j ≤ flow_cover_excess a b C :=
      le_trans (Finset.le_sup' a hj) hmax
    rw [max_eq_right (sub_nonpos.mpr haj), zero_mul]
  rw [hpenalty, add_zero]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_14.lean`: on the equality face, every
flow coordinate outside a cover whose maximum is at most its excess is zero. -/
private lemma flowCoverFace_outsideFlow_eq_zero_of_coverMax_le_excess
    {n : ℕ} (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (hC : C.Nonempty)
    (hmax : C.sup' hC a ≤ flow_cover_excess a b C)
    {i : Fin n} (hi : i ∉ C)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ flow_cover_face a b C) :
    p.2 i = 0 := by
  -- Restate the maximum bound in the canonical input form for the value helper.
  have hmaxForValue : C.sup' hC a ≤ flow_cover_excess a b C := hmax
  have hpData := (mem_flow_cover_face_iff a b C p).mp hp
  have hbounds := singleNodeFlowSet_flowBounds_of_mem_convexHull a b hpData.1
  have hcoverSum : ∑ j ∈ C, p.2 j = b := by
    -- The collapsed face equation makes the cover flow exhaust the total allowance.
    calc
      ∑ j ∈ C, p.2 j = flow_cover_value a b C p :=
        (flowCoverValue_eq_coverFlowSum_of_coverMax_le_excess
          a b C hC hmaxForValue p).symm
      _ = b := hpData.2
  have hinsertLe : ∑ j ∈ insert i C, p.2 j ≤ ∑ j, p.2 j := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun j _ _ ↦ hbounds.1 j)
  -- Adding the outside nonnegative coordinate cannot exceed the already-tight cover sum.
  rw [Finset.sum_insert hi] at hinsertLe
  linarith [hbounds.1 i, hbounds.2]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_14.lean`: a feasible positive flow in
one coordinate gives the corresponding pure-flow direction of the ambient convex hull. -/
private lemma singleNodeFlowCapacityDirection_mem_ambientDirection
    {n : ℕ} (a : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (hai : 0 ≤ a i) (haib : a i ≤ b) :
    ((0 : Fin n → ℝ), Pi.single i (a i)) ∈
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction := by
  classical
  let x : Fin n → ℝ := Pi.single i 1
  let q0 : (Fin n → ℝ) × (Fin n → ℝ) := (x, 0)
  let q1 : (Fin n → ℝ) × (Fin n → ℝ) := (x, Pi.single i (a i))
  have hxBinary : ∀ j, x j = 0 ∨ x j = 1 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [x]
    · left
      simp [x, hji]
  have hq0 : q0 ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    -- The zero-flow point with selector `x` satisfies all flow constraints.
    refine ⟨hxBinary, ?_, ?_, ?_⟩
    · intro j
      simp [q0]
    · simpa [q0] using le_trans hai haib
    · intro j
      have hproduct : 0 ≤ a j * x j := by
        by_cases hji : j = i
        · subst j
          simpa [x] using hai
        · simp [x, hji]
      simpa [q0] using hproduct
  have hq1 : q1 ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    -- Activating only coordinate `i` reaches its capacity and remains within the flow budget.
    refine ⟨hxBinary, ?_, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j
        simpa [q1] using hai
      · simp [q1, hji]
    · simpa [q1] using haib
    · intro j
      by_cases hji : j = i
      · subst j
        simp [q1, x]
      · simp [q1, x, hji]
  have hq0Aff : q0 ∈ affineSpan ℝ (convexHull ℝ (single_node_flow_set a b)) :=
    subset_affineSpan ℝ _ (subset_convexHull ℝ _ hq0)
  have hq1Aff : q1 ∈ affineSpan ℝ (convexHull ℝ (single_node_flow_set a b)) :=
    subset_affineSpan ℝ _ (subset_convexHull ℝ _ hq1)
  -- Their difference is exactly the pure-flow displacement in the statement.
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hq0Aff]
  refine ⟨q1, hq1Aff, ?_⟩
  ext j <;> simp [q0, q1, vsub_eq_sub]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_14.lean`: when all cover penalties
vanish and the cover is proper, its equality face has codimension at least two and is not a
facet. -/
private lemma flowCoverFace_not_isFacet_of_coverMax_le_excess
    {n : ℕ} (b : ℝ) (a : Fin n → ℝ) (C : Finset (Fin n))
    (ha_pos : ∀ j, 0 < a j)
    (ha_lt_rhs : ∀ j, a j < b)
    (hC : C.Nonempty)
    (hCproper : C ⊂ Finset.univ)
    (hmax : C.sup' hC a ≤ flow_cover_excess a b C) :
    ¬ IsFacetOf
      (convexHull ℝ (single_node_flow_set a b))
      (flow_cover_face a b C) := by
  classical
  intro hfacet
  rcases (isFacetOf_iff.mp hfacet) with ⟨hfaceNonempty, _, hfacetDim⟩
  obtain ⟨p0, hp0⟩ := hfaceNonempty
  obtain ⟨i, _, hiC⟩ := Finset.exists_of_ssubset hCproper
  obtain ⟨j, hjC⟩ := hC
  have hij : i ≠ j := by
    intro hij
    exact hiC (hij ▸ hjC)
  let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
  let K : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i).comp (LinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    flowCoverSupportLinearMap a b C
  have hcoeffZero :
      ∀ k ∈ C, flowCoverSupportCoeff a b C k = 0 := by
    intro k hk
    have hak : a k ≤ flow_cover_excess a b C :=
      le_trans (Finset.le_sup' a hk) hmax
    exact max_eq_right (sub_nonpos.mpr hak)
  have hL_eq_sum :
      ∀ q : (Fin n → ℝ) × (Fin n → ℝ), L q = ∑ k ∈ C, q.2 k := by
    intro q
    -- The support functional loses its weighted selector part when every coefficient is zero.
    have hweighted :
        ∑ k ∈ C, flowCoverSupportCoeff a b C k * q.1 k = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      rw [hcoeffZero k hk, zero_mul]
    simp [L, flowCoverSupportLinearMap, hweighted]
  have hfaceSubset :
      flow_cover_face a b C ⊆ convexHull ℝ (single_node_flow_set a b) := by
    intro q hq
    exact ((mem_flow_cover_face_iff a b C q).mp hq).1
  have hdirD :
      (affineSpan ℝ (flow_cover_face a b C)).direction ≤ D := by
    -- Face directions are ambient directions by affine-span monotonicity.
    exact AffineSubspace.direction_le (affineSpan_mono ℝ hfaceSubset)
  have hlevelK :
      ∀ {q : (Fin n → ℝ) × (Fin n → ℝ)},
        q ∈ flow_cover_face a b C → K q = 0 := by
    intro q hq
    simpa [K, LinearMap.proj_apply] using
      flowCoverFace_outsideFlow_eq_zero_of_coverMax_le_excess
        a b C ⟨j, hjC⟩ hmax hiC hq
  have hdirK :
      (affineSpan ℝ (flow_cover_face a b C)).direction ≤ LinearMap.ker K := by
    -- The outside flow coordinate is constant on the entire equality face.
    exact affineSpanDirection_le_ker_of_constant hp0 hlevelK
  have hlevelSupport :
      ∀ {q : (Fin n → ℝ) × (Fin n → ℝ)},
        q ∈ flow_cover_face a b C → L q = b := by
    intro q hq
    have hqData := (mem_flow_cover_face_iff a b C q).mp hq
    calc
      L q = ∑ k ∈ C, q.2 k := hL_eq_sum q
      _ = flow_cover_value a b C q :=
        (flowCoverValue_eq_coverFlowSum_of_coverMax_le_excess
          a b C ⟨j, hjC⟩ hmax q).symm
      _ = b := hqData.2
  have hdirL :
      (affineSpan ℝ (flow_cover_face a b C)).direction ≤ LinearMap.ker L := by
    -- The tight support equation supplies the second kernel inclusion.
    exact affineSpanDirection_le_ker_of_constant hp0 hlevelSupport
  have hdirDouble :
      (affineSpan ℝ (flow_cover_face a b C)).direction ≤
        (D ⊓ LinearMap.ker K) ⊓ LinearMap.ker L := by
    intro v hv
    exact ⟨⟨hdirD hv, hdirK hv⟩, hdirL hv⟩
  let vi : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((0 : Fin n → ℝ), Pi.single i (a i))
  let wi : (Fin n → ℝ) × (Fin n → ℝ) := (a i)⁻¹ • vi
  have hviD : vi ∈ D := by
    simpa [D, vi] using
      singleNodeFlowCapacityDirection_mem_ambientDirection a b i (le_of_lt (ha_pos i))
        (le_of_lt (ha_lt_rhs i))
  have hwiD : wi ∈ D := by
    exact D.smul_mem ((a i)⁻¹) hviD
  have hwiK : K wi = 1 := by
    -- Normalize the outside-coordinate direction to have `K`-value one.
    simp [K, wi, vi, (ha_pos i).ne']
  have hcodimK :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker K) + 1 = Module.finrank ℝ ↥D :=
    submodule_finrank_inf_ker_add_one_of_eval_one D K hwiD hwiK
  let vj : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((0 : Fin n → ℝ), Pi.single j (a j))
  let wj : (Fin n → ℝ) × (Fin n → ℝ) := (a j)⁻¹ • vj
  have hvjD : vj ∈ D := by
    simpa [D, vj] using
      singleNodeFlowCapacityDirection_mem_ambientDirection a b j (le_of_lt (ha_pos j))
        (le_of_lt (ha_lt_rhs j))
  have hwjD : wj ∈ D := by
    exact D.smul_mem ((a j)⁻¹) hvjD
  have hwjK : K wj = 0 := by
    simp [K, wj, vj, hij]
  have hwjCut : wj ∈ D ⊓ LinearMap.ker K := by
    exact ⟨hwjD, LinearMap.mem_ker.mpr hwjK⟩
  have hwjL : L wj = 1 := by
    -- A normalized pure-flow direction at a cover index has support value one.
    rw [hL_eq_sum, Finset.sum_eq_single_of_mem j hjC]
    · simp [wj, vj, (ha_pos j).ne']
    · intro k _ hkj
      simp [wj, vj, hkj]
  have hcodimL :
      Module.finrank ℝ ↥((D ⊓ LinearMap.ker K) ⊓ LinearMap.ker L) + 1 =
        Module.finrank ℝ ↥(D ⊓ LinearMap.ker K) :=
    submodule_finrank_inf_ker_add_one_of_eval_one (D ⊓ LinearMap.ker K) L hwjCut hwjL
  have hfaceRankLe :
      Module.finrank ℝ (affineSpan ℝ (flow_cover_face a b C)).direction ≤
        Module.finrank ℝ ↥((D ⊓ LinearMap.ker K) ⊓ LinearMap.ker L) :=
    Submodule.finrank_mono hdirDouble
  have hcodimTwo :
      Module.finrank ℝ (affineSpan ℝ (flow_cover_face a b C)).direction + 2 ≤
        Module.finrank ℝ ↥D := by
    omega
  have hfacetDimEq :
      Module.finrank ℝ (affineSpan ℝ (flow_cover_face a b C)).direction + 1 =
        Module.finrank ℝ ↥D := by
    simpa [D] using hfacetDim
  -- A facet has codimension one, contradicting the two independent kernel cuts.
  omega

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_14.lean

Exercise 7.14. In the source regime `0 < a_j < b` for all `j`, assume `C` is a strict subset of
the ambient index set and `λ` is the flow-cover excess determined by `∑_{j ∈ C} a_j = b + λ` with
`0 < λ`. If the zero-lifted flow-cover inequality `(7.14)` defines a facet of `conv(T)`, then the
necessary condition `λ < max_{j ∈ C} a_j` holds. The ambient single-node flow set and the
canonical flow-cover owners `flow_cover_value` and `flow_cover_face` are reused from Theorem 7.9,
with the explicit `λ` presentation recovered in Part 2 by
`flow_cover_value_eq_zero_lifted_value`. -/
theorem flow_cover_excess_lt_cover_max_of_facet_defining
    {n : ℕ} (b : ℝ) (a : Fin n → ℝ) (C : Finset (Fin n)) (lam : ℝ)
    (ha_pos : ∀ j, 0 < a j)
    (ha_lt_rhs : ∀ j, a j < b)
    (hC : C.Nonempty)
    (hCproper : C ⊂ Finset.univ)
    (hcover : Finset.sum C a = b + lam)
    (hlampos : 0 < lam)
    (hfacet : flow_cover_inequality_facet_defining a b C) :
    lam < C.sup' hC a := by
  have hexcess : flow_cover_excess a b C = lam :=
    flow_cover_excess_eq_of_sum_eq_add a b lam C hcover
  -- If the desired strict inequality failed, the canonical excess would dominate the cover max.
  by_contra hnot
  have hmax : C.sup' hC a ≤ flow_cover_excess a b C := by
    rw [hexcess]
    calc
      C.sup' hC a ≤ lam := le_of_not_gt hnot
      _ ≤ max lam 0 := le_max_left _ _
      _ = lam := max_eq_left (le_of_lt hlampos)
  exact
    (flowCoverFace_not_isFacet_of_coverMax_le_excess b a C ha_pos ha_lt_rhs hC hCproper hmax)
      hfacet.2

end Exercise714

#print axioms flow_cover_excess_lt_cover_max_of_facet_defining
#print axioms affineSpanDirection_le_ker_of_constant
#print axioms singleNodeFlowSet_flowBounds_of_mem_convexHull
#print axioms flowCoverValue_eq_coverFlowSum_of_coverMax_le_excess
#print axioms flowCoverFace_outsideFlow_eq_zero_of_coverMax_le_excess
#print axioms singleNodeFlowCapacityDirection_mem_ambientDirection
#print axioms flowCoverFace_not_isFacet_of_coverMax_le_excess
