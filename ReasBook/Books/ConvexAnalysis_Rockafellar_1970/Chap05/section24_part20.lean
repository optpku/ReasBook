/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part19

section Chap05
section Section24

open scoped ConvexAnalysis
open scoped Topology
open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- The scalar graph of a one-dimensional multivalued mapping `ρ : ℝ ⇉ ℝ`, obtained by
identifying both the domain and codomain with `ℝ`. -/
def oneDimensionalMultivaluedMappingScalarGraph
    (ρ : (Fin 1 → ℝ) → Set (Fin 1 → ℝ)) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | scalarPoint p.2 ∈ ρ (scalarPoint p.1)}

/-- Helper for Remark 5.24.4: every vector in `Fin 1 → ℝ` is the scalar point determined by its
unique coordinate. -/
lemma helperForRemark_5_24_4_eq_scalarPoint (x : Fin 1 → ℝ) :
    scalarPoint (x 0) = x := by
  -- A `Fin 1` vector has only one coordinate, so extensionality reduces it to that value.
  ext i
  fin_cases i
  simp [scalarPoint]

/-- Helper for Remark 5.24.4: in dimension one, the monotonicity dot product is just the product
of the scalar coordinate differences. -/
lemma helperForRemark_5_24_4_dotProduct_eq_scalarMul
    (x0 x1 x0Star x1Star : Fin 1 → ℝ) :
    dotProduct (x1 - x0) (x1Star - x0Star) =
      (x1 0 - x0 0) * (x1Star 0 - x0Star 0) := by
  -- Expanding the unique coordinate of `Fin 1` collapses the dot product to a scalar product.
  simp [dotProduct]

/-- Helper for Remark 5.24.4: inclusion of scalar graphs is the same as fiberwise inclusion along
the scalar identification `ℝ ≃ Fin 1 → ℝ`. -/
lemma helperForRemark_5_24_4_scalarGraph_subset_iff_pointwiseSubset
    {ρ σ : (Fin 1 → ℝ) → Set (Fin 1 → ℝ)} :
    oneDimensionalMultivaluedMappingScalarGraph ρ ⊆
        oneDimensionalMultivaluedMappingScalarGraph σ ↔
      ∀ x : ℝ, ρ (scalarPoint x) ⊆ σ (scalarPoint x) := by
  constructor
  · intro hsubset x v hv
    -- Read the scalar point as a point of the scalar graph and transport it across the inclusion.
    have hvEq : scalarPoint (v 0) = v := helperForRemark_5_24_4_eq_scalarPoint v
    have hmemGraph : (x, v 0) ∈ oneDimensionalMultivaluedMappingScalarGraph ρ := by
      simpa [oneDimensionalMultivaluedMappingScalarGraph, hvEq] using hv
    have hmemGraph' := hsubset hmemGraph
    simpa [oneDimensionalMultivaluedMappingScalarGraph, hvEq] using hmemGraph'
  · intro hsubset p hp
    -- Conversely, scalar-graph membership is exactly fiber membership at the corresponding scalar.
    have hp' : scalarPoint p.2 ∈ ρ (scalarPoint p.1) := by
      simpa [oneDimensionalMultivaluedMappingScalarGraph] using hp
    have hq' : scalarPoint p.2 ∈ σ (scalarPoint p.1) := hsubset p.1 hp'
    simpa [oneDimensionalMultivaluedMappingScalarGraph] using hq'

/-- Helper for Remark 5.24.4: inclusion of multivalued graphs is equivalent to pointwise fiber
inclusion. -/
lemma helperForRemark_5_24_4_multivaluedMappingGraph_subset_iff_pointwiseSubset
    {ρ σ : (Fin 1 → ℝ) → Set (Fin 1 → ℝ)} :
    multivaluedMappingGraph ρ ⊆ multivaluedMappingGraph σ ↔
      ∀ x : Fin 1 → ℝ, ρ x ⊆ σ x := by
  constructor
  · intro hsubset x v hv
    -- Package fiber membership as graph membership, then apply the graph inclusion.
    have hmemGraph : (x, v) ∈ multivaluedMappingGraph ρ := by
      simpa [multivaluedMappingGraph] using hv
    have hmemGraph' := hsubset hmemGraph
    simpa [multivaluedMappingGraph] using hmemGraph'
  · intro hsubset p hp
    -- Unpacking the graph point recovers exactly the corresponding fiber inclusion.
    have hp' : p.2 ∈ ρ p.1 := by
      simpa [multivaluedMappingGraph] using hp
    have hq' : p.2 ∈ σ p.1 := hsubset p.1 hp'
    simpa [multivaluedMappingGraph] using hq'

/-- Helper for Remark 5.24.4: equality of scalar graphs recovers equality of the underlying
one-dimensional fibers. -/
lemma helperForRemark_5_24_4_fiberEq_of_scalarGraphEq
    {ρ σ : (Fin 1 → ℝ) → Set (Fin 1 → ℝ)}
    (hEq :
      oneDimensionalMultivaluedMappingScalarGraph ρ =
        oneDimensionalMultivaluedMappingScalarGraph σ) :
    ∀ x : Fin 1 → ℝ, ρ x = σ x := by
  intro x
  ext v
  have hx : scalarPoint (x 0) = x := helperForRemark_5_24_4_eq_scalarPoint x
  have hv : scalarPoint (v 0) = v := helperForRemark_5_24_4_eq_scalarPoint v
  constructor
  · intro hvMem
    -- Rewrite the vector pair as a scalar-graph point and move it across the graph equality.
    have hmemGraph :
        (x 0, v 0) ∈ oneDimensionalMultivaluedMappingScalarGraph ρ := by
      simpa [oneDimensionalMultivaluedMappingScalarGraph, hx, hv] using hvMem
    have hmemGraph' :
        (x 0, v 0) ∈ oneDimensionalMultivaluedMappingScalarGraph σ := by
      rw [hEq] at hmemGraph
      exact hmemGraph
    simpa [oneDimensionalMultivaluedMappingScalarGraph, hx, hv] using hmemGraph'
  · intro hvMem
    -- The reverse implication uses the same scalar-graph transport in the opposite direction.
    have hmemGraph :
        (x 0, v 0) ∈ oneDimensionalMultivaluedMappingScalarGraph σ := by
      simpa [oneDimensionalMultivaluedMappingScalarGraph, hx, hv] using hvMem
    have hmemGraph' :
        (x 0, v 0) ∈ oneDimensionalMultivaluedMappingScalarGraph ρ := by
      rw [← hEq] at hmemGraph
      exact hmemGraph
    simpa [oneDimensionalMultivaluedMappingScalarGraph, hx, hv] using hmemGraph'

/-- Helper for Remark 5.24.4: equality of multivalued graphs is equivalent to equality of the
underlying one-dimensional fibers. -/
lemma helperForRemark_5_24_4_fiberEq_of_multivaluedMappingGraphEq
    {ρ σ : (Fin 1 → ℝ) → Set (Fin 1 → ℝ)}
    (hEq : multivaluedMappingGraph ρ = multivaluedMappingGraph σ) :
    ∀ x : Fin 1 → ℝ, ρ x = σ x := by
  intro x
  ext v
  constructor
  · intro hvMem
    -- Move the graph point `(x, v)` across the graph equality.
    have hmemGraph : (x, v) ∈ multivaluedMappingGraph ρ := by
      simpa [multivaluedMappingGraph] using hvMem
    have hmemGraph' : (x, v) ∈ multivaluedMappingGraph σ := by
      rw [hEq] at hmemGraph
      exact hmemGraph
    simpa [multivaluedMappingGraph] using hmemGraph'
  · intro hvMem
    -- The converse direction is symmetric.
    have hmemGraph : (x, v) ∈ multivaluedMappingGraph σ := by
      simpa [multivaluedMappingGraph] using hvMem
    have hmemGraph' : (x, v) ∈ multivaluedMappingGraph ρ := by
      rw [← hEq] at hmemGraph
      exact hmemGraph
    simpa [multivaluedMappingGraph] using hmemGraph'

/-- Helper for Remark 5.24.4: a one-dimensional multivalued mapping is monotone exactly when its
scalar graph is totally ordered by the coordinatewise order on `ℝ²`. -/
lemma helperForRemark_5_24_4_monotone_iff_scalarGraph_coordinatewiseOrdered
    (ρ : (Fin 1 → ℝ) → Set (Fin 1 → ℝ)) :
    IsMonotoneMultivaluedMapping ρ ↔
      IsCoordinatewiseTotallyOrdered (oneDimensionalMultivaluedMappingScalarGraph ρ) := by
  constructor
  · intro hmonotone p hp q hq _hpq
    -- Monotonicity turns the scalar coordinate differences into a nonnegative product.
    have hprod :
        0 ≤ (q.1 - p.1) * (q.2 - p.2) := by
      have hmonoAtPoints :
          0 ≤ dotProduct (scalarPoint q.1 - scalarPoint p.1)
              (scalarPoint q.2 - scalarPoint p.2) :=
        hmonotone hp hq
      rw [helperForRemark_5_24_4_dotProduct_eq_scalarMul
        (scalarPoint p.1) (scalarPoint q.1) (scalarPoint p.2) (scalarPoint q.2)] at hmonoAtPoints
      simpa [scalarPoint] using hmonoAtPoints
    -- A nonnegative scalar product means the two coordinates move in the same order direction.
    rcases mul_nonneg_iff.mp hprod with hsameDirection | hoppositeDirection
    · left
      exact ⟨sub_nonneg.mp hsameDirection.1, sub_nonneg.mp hsameDirection.2⟩
    · right
      exact ⟨sub_nonpos.mp hoppositeDirection.1, sub_nonpos.mp hoppositeDirection.2⟩
  · intro hordered x0 x1 x0Star x1Star hx0Star hx1Star
    let p : ℝ × ℝ := (x0 0, x0Star 0)
    let q : ℝ × ℝ := (x1 0, x1Star 0)
    have hx0Eq : scalarPoint (x0 0) = x0 := helperForRemark_5_24_4_eq_scalarPoint x0
    have hx1Eq : scalarPoint (x1 0) = x1 := helperForRemark_5_24_4_eq_scalarPoint x1
    have hx0StarEq : scalarPoint (x0Star 0) = x0Star := helperForRemark_5_24_4_eq_scalarPoint x0Star
    have hx1StarEq : scalarPoint (x1Star 0) = x1Star := helperForRemark_5_24_4_eq_scalarPoint x1Star
    have hp : p ∈ oneDimensionalMultivaluedMappingScalarGraph ρ := by
      -- Rewrite the first graph point in scalar coordinates.
      simpa [p, oneDimensionalMultivaluedMappingScalarGraph, hx0Eq, hx0StarEq] using hx0Star
    have hq : q ∈ oneDimensionalMultivaluedMappingScalarGraph ρ := by
      -- Rewrite the second graph point in scalar coordinates.
      simpa [q, oneDimensionalMultivaluedMappingScalarGraph, hx1Eq, hx1StarEq] using hx1Star
    by_cases hpq : p = q
    · have hxEq : x0 0 = x1 0 := by
        simpa [p, q] using congrArg Prod.fst hpq
      have hStarEq : x0Star 0 = x1Star 0 := by
        simpa [p, q] using congrArg Prod.snd hpq
      -- Equal scalar graph points give the trivial zero monotonicity inequality.
      rw [helperForRemark_5_24_4_dotProduct_eq_scalarMul]
      simp [hxEq, hStarEq]
    · have hcomp : p ≤ q ∨ q ≤ p := hordered hp hq hpq
      cases hcomp with
      | inl hpqLe =>
          have hprod :
              0 ≤ (x1 0 - x0 0) * (x1Star 0 - x0Star 0) := by
            -- Coordinatewise increase forces both scalar differences to be nonnegative.
            exact
              mul_nonneg (sub_nonneg.mpr hpqLe.1) (sub_nonneg.mpr hpqLe.2)
          rw [helperForRemark_5_24_4_dotProduct_eq_scalarMul]
          exact hprod
      | inr hqpLe =>
          have hprod :
              0 ≤ (x1 0 - x0 0) * (x1Star 0 - x0Star 0) := by
            -- Coordinatewise decrease forces both scalar differences to be nonpositive.
            exact
              mul_nonneg_of_nonpos_of_nonpos
                (sub_nonpos.mpr hqpLe.1) (sub_nonpos.mpr hqpLe.2)
          rw [helperForRemark_5_24_4_dotProduct_eq_scalarMul]
          exact hprod

/-- Helper for Remark 5.24.4: any coordinatewise totally ordered subset of `ℝ²` extends to a
maximal one. -/
lemma helperForRemark_5_24_4_exists_maximalCoordinatewiseExtension
    (Γ : Set (ℝ × ℝ)) (hΓ : IsCoordinatewiseTotallyOrdered Γ) :
    ∃ Δ : Set (ℝ × ℝ), Γ ⊆ Δ ∧ IsMaximalCoordinatewiseTotallyOrdered Δ := by
  have hChain : IsChain (fun p q : ℝ × ℝ => p ≤ q) Γ := by
    -- For the product order on `ℝ²`, coordinatewise total ordering is exactly the chain property.
    simpa [IsCoordinatewiseTotallyOrdered, IsChain] using hΓ
  rcases IsChain.exists_maxChain hChain with ⟨Δ, hΔMaxChain, hsubset⟩
  have hΔMaximal : IsMaximalCoordinatewiseTotallyOrdered Δ := by
    -- A maximal chain for the product order is precisely a maximal coordinatewise totally ordered
    -- subset.
    refine ⟨?_, ?_⟩
    · simpa [IsCoordinatewiseTotallyOrdered, IsChain] using hΔMaxChain.1
    · intro Δ' hΔSubset hΔ'Ordered
      exact (hΔMaxChain.2 (by simpa [IsCoordinatewiseTotallyOrdered, IsChain] using hΔ'Ordered)
        hΔSubset).symm
  exact ⟨Δ, hsubset, hΔMaximal⟩

/-- Helper for Remark 5.24.4: maximal monotonicity of a one-dimensional multivalued mapping is
equivalent to maximal coordinatewise total ordering of its scalar graph. -/
lemma helperForRemark_5_24_4_maximalMonotone_iff_scalarGraph_maximalCoordinatewise
    (ρ : (Fin 1 → ℝ) → Set (Fin 1 → ℝ)) :
    IsMaximalMonotoneMultivaluedMapping ρ ↔
      IsMaximalCoordinatewiseTotallyOrdered (oneDimensionalMultivaluedMappingScalarGraph ρ) := by
  constructor
  · intro hmax
    refine ⟨?_, ?_⟩
    · -- The monotone part of maximality is exactly the first scalar-graph equivalence.
      exact
        (helperForRemark_5_24_4_monotone_iff_scalarGraph_coordinatewiseOrdered ρ).1 hmax.1
    · intro Δ hsubset hΔOrdered
      let σ : (Fin 1 → ℝ) → Set (Fin 1 → ℝ) := fun x => {v | (x 0, v 0) ∈ Δ}
      have hσScalarGraph :
          oneDimensionalMultivaluedMappingScalarGraph σ = Δ := by
        -- The auxiliary mapping `σ` is defined so that its scalar graph is exactly `Δ`.
        ext p
        simp [σ, oneDimensionalMultivaluedMappingScalarGraph, scalarPoint]
      have hσOrdered :
          IsCoordinatewiseTotallyOrdered (oneDimensionalMultivaluedMappingScalarGraph σ) := by
        simpa [hσScalarGraph] using hΔOrdered
      have hσMonotone : IsMonotoneMultivaluedMapping σ := by
        -- Transport the order property back to a monotone mapping.
        exact
          (helperForRemark_5_24_4_monotone_iff_scalarGraph_coordinatewiseOrdered σ).2
            hσOrdered
      have hρσSubset : multivaluedMappingGraph ρ ⊆ multivaluedMappingGraph σ := by
        intro p hp
        rcases p with ⟨x, v⟩
        have hx : scalarPoint (x 0) = x := helperForRemark_5_24_4_eq_scalarPoint x
        have hv : scalarPoint (v 0) = v := helperForRemark_5_24_4_eq_scalarPoint v
        have hmemScalarGraph :
            (x 0, v 0) ∈ oneDimensionalMultivaluedMappingScalarGraph ρ := by
          -- Translate the graph point `(x, v)` to the scalar graph of `ρ`.
          simpa [oneDimensionalMultivaluedMappingScalarGraph, hx, hv] using hp
        have hmemΔ : (x 0, v 0) ∈ Δ := hsubset hmemScalarGraph
        have hmemσ : v ∈ σ x := by
          -- By construction of `σ`, membership in `Δ` is the same as fiber membership in `σ`.
          simpa [σ] using hmemΔ
        simpa [multivaluedMappingGraph] using hmemσ
      have hGraphEq : multivaluedMappingGraph σ = multivaluedMappingGraph ρ :=
        hmax.2 hσMonotone hρσSubset
      have hFiberEq : ∀ x : Fin 1 → ℝ, σ x = ρ x :=
        helperForRemark_5_24_4_fiberEq_of_multivaluedMappingGraphEq hGraphEq
      have hScalarEq :
          oneDimensionalMultivaluedMappingScalarGraph σ =
            oneDimensionalMultivaluedMappingScalarGraph ρ := by
        -- Equality of fibers gives equality of scalar graphs after evaluating on scalar points.
        ext p
        simp [oneDimensionalMultivaluedMappingScalarGraph, hFiberEq (scalarPoint p.1)]
      exact hσScalarGraph.symm.trans hScalarEq
  · intro hmax
    refine ⟨?_, ?_⟩
    · -- The order property of the maximal scalar graph recovers monotonicity of `ρ`.
      exact
        (helperForRemark_5_24_4_monotone_iff_scalarGraph_coordinatewiseOrdered ρ).2 hmax.1
    · intro σ hσMonotone hgraphSubset
      have hσOrdered :
          IsCoordinatewiseTotallyOrdered (oneDimensionalMultivaluedMappingScalarGraph σ) := by
        -- Apply the first equivalence to the comparison mapping `σ`.
        exact
          (helperForRemark_5_24_4_monotone_iff_scalarGraph_coordinatewiseOrdered σ).1
            hσMonotone
      have hPointwiseSubset : ∀ x : Fin 1 → ℝ, ρ x ⊆ σ x :=
        (helperForRemark_5_24_4_multivaluedMappingGraph_subset_iff_pointwiseSubset).1
          hgraphSubset
      have hScalarPointwiseSubset : ∀ x : ℝ, ρ (scalarPoint x) ⊆ σ (scalarPoint x) := by
        -- Restrict the pointwise inclusion to scalar points.
        intro x
        exact hPointwiseSubset (scalarPoint x)
      have hScalarSubset :
          oneDimensionalMultivaluedMappingScalarGraph ρ ⊆
            oneDimensionalMultivaluedMappingScalarGraph σ :=
        (helperForRemark_5_24_4_scalarGraph_subset_iff_pointwiseSubset).2
          hScalarPointwiseSubset
      have hScalarEq :
          oneDimensionalMultivaluedMappingScalarGraph σ =
            oneDimensionalMultivaluedMappingScalarGraph ρ :=
        hmax.2 hScalarSubset hσOrdered
      have hFiberEq : ∀ x : Fin 1 → ℝ, σ x = ρ x :=
        helperForRemark_5_24_4_fiberEq_of_scalarGraphEq hScalarEq
      -- Transport the recovered fiber equality back to ordinary graph equality.
      ext p
      rcases p with ⟨x, v⟩
      simp [multivaluedMappingGraph, hFiberEq x]

/-- Helper for Remark 5.24.4: in one dimension, every monotone multivalued mapping is already
cyclically monotone. -/
lemma helperForRemark_5_24_4_monotone_implies_cyclicallyMonotone
    (ρ : (Fin 1 → ℝ) → Set (Fin 1 → ℝ))
    (hmonotone : IsMonotoneMultivaluedMapping ρ) :
    IsCyclicallyMonotone ρ := by
  have hordered :
      IsCoordinatewiseTotallyOrdered (oneDimensionalMultivaluedMappingScalarGraph ρ) :=
    (helperForRemark_5_24_4_monotone_iff_scalarGraph_coordinatewiseOrdered ρ).1 hmonotone
  rcases
      helperForRemark_5_24_4_exists_maximalCoordinatewiseExtension
        (oneDimensionalMultivaluedMappingScalarGraph ρ) hordered with
    ⟨Δ, hsubset, hΔMaximal⟩
  have hΔCurve : IsCompleteNondecreasingCurve Δ := by
    -- Maximal coordinatewise order is exactly the complete-curve condition from Remark 5.24.3.
    exact
      (isCompleteNondecreasingCurve_iff_isMaximalCoordinatewiseTotallyOrdered Δ).2 hΔMaximal
  have hΔRealized :
      ∃ f : (Fin 1 → ℝ) → EReal,
        ClosedConvexFunction f ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
          oneDimensionalSubdifferentialScalarGraph f = Δ :=
    ((oneDimensional_subdifferentialGraphs_iff_completeNondecreasingCurves_unique_up_to_constant
      Δ).1).1 hΔCurve
  rcases hΔRealized with ⟨f, hclosed, hproper, hGraphEqΔ⟩
  let σ : (Fin 1 → ℝ) → Set (Fin 1 → ℝ) :=
    fun x => ((dotProductEquiv ℝ (Fin 1)) ⁻¹' subdifferentialAt f x)
  have hσScalarGraph :
      oneDimensionalMultivaluedMappingScalarGraph σ = Δ := by
    -- The realized subdifferential mapping has exactly the realized scalar graph.
    simpa [σ, oneDimensionalMultivaluedMappingScalarGraph,
      oneDimensionalSubdifferentialScalarGraph] using hGraphEqΔ
  have hσWitness :
      ∃ g : (Fin 1 → ℝ) → EReal,
        ClosedConvexFunction g ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g ∧
          ∀ x : Fin 1 → ℝ,
            σ x = ((dotProductEquiv ℝ (Fin 1)) ⁻¹' subdifferentialAt g x) := by
    have hσFibers :
        ∀ x : Fin 1 → ℝ,
          σ x = ((dotProductEquiv ℝ (Fin 1)) ⁻¹' subdifferentialAt f x) := by
      -- The definition of `σ` is exactly the realized subdifferential family.
      intro x
      rfl
    exact ⟨f, hclosed, hproper, hσFibers⟩
  have hσMaximalCyclic : IsMaximalCyclicallyMonotone σ := by
    -- Theorem 5.24.12 upgrades the realized subdifferential family to a maximal cyclically
    -- monotone mapping.
    exact
      ((isMaximalCyclicallyMonotone_iff_exists_closedProperConvex_subdifferential_eq_and_unique_up_to_constant
        (ρ := σ)).1).2 hσWitness
  have hρSubsetσ : ∀ x : Fin 1 → ℝ, ρ x ⊆ σ x := by
    intro x v hv
    have hx : scalarPoint (x 0) = x := helperForRemark_5_24_4_eq_scalarPoint x
    have hvEq : scalarPoint (v 0) = v := helperForRemark_5_24_4_eq_scalarPoint v
    have hmemScalarGraph :
        (x 0, v 0) ∈ oneDimensionalMultivaluedMappingScalarGraph ρ := by
      -- Rewrite the original fiber inclusion as membership in the scalar graph of `ρ`.
      simpa [oneDimensionalMultivaluedMappingScalarGraph, hx, hvEq] using hv
    have hmemΔ : (x 0, v 0) ∈ Δ := hsubset hmemScalarGraph
    have hmemσScalarGraph :
        (x 0, v 0) ∈ oneDimensionalMultivaluedMappingScalarGraph σ := by
      rw [hσScalarGraph]
      exact hmemΔ
    -- Reading the scalar-graph inclusion back in vector form gives the desired fiber inclusion.
    simpa [oneDimensionalMultivaluedMappingScalarGraph, hx, hvEq] using hmemσScalarGraph
  -- Cyclic monotonicity descends from the maximal cyclic extension `σ` to the original mapping
  -- `ρ` because the latter sits pointwise inside the former.
  exact
    helperForTheorem_5_24_11_pointwiseSubset_preserves_isCyclicallyMonotone
      hσMaximalCyclic.1 hρSubsetσ

-- Proof sketch: in one dimension, the monotonicity inequality for two graph points is equivalent
-- to coordinatewise comparability, because the product of the coordinate differences is
-- nonnegative exactly when the two coordinates are ordered in the same direction. This identifies
-- monotone graphs with coordinatewise totally ordered subsets of `ℝ²`, and maximal monotone
-- graphs with maximal such subsets, which are the complete non-decreasing curves by Remark
-- 5.24.3. The equivalence between monotone and cyclically monotone mappings in dimension one then
-- follows by combining that curve characterization with Theorem 5.24.5 and the maximal
-- cyclically monotone characterization in Theorem 5.24.12.
/-- Remark 5.24.4: when `n = 1`, monotone mappings are exactly the mappings whose scalar graphs
are totally ordered in `ℝ²` by the coordinatewise partial order. Consequently, maximal monotone
mappings are exactly those whose scalar graphs are complete non-decreasing curves. Moreover, in
one dimension the notions of monotone and cyclically monotone mappings coincide. -/
theorem oneDimensional_monotoneMultivaluedMapping_graph_order_maximality_and_cyclicMonotonicity
    (ρ : (Fin 1 → ℝ) → Set (Fin 1 → ℝ)) :
    (IsMonotoneMultivaluedMapping ρ ↔
      IsCoordinatewiseTotallyOrdered (oneDimensionalMultivaluedMappingScalarGraph ρ)) ∧
      (IsMaximalMonotoneMultivaluedMapping ρ ↔
        IsCompleteNondecreasingCurve (oneDimensionalMultivaluedMappingScalarGraph ρ)) ∧
      (IsMonotoneMultivaluedMapping ρ ↔ IsCyclicallyMonotone ρ) := by
  constructor
  · -- The first clause is exactly the scalar-graph reformulation of monotonicity.
    exact helperForRemark_5_24_4_monotone_iff_scalarGraph_coordinatewiseOrdered ρ
  constructor
  · -- Maximal monotonicity is the same as maximal coordinatewise order, and Remark 5.24.3
    -- identifies the latter with complete non-decreasing curves.
    calc
      IsMaximalMonotoneMultivaluedMapping ρ ↔
          IsMaximalCoordinatewiseTotallyOrdered
            (oneDimensionalMultivaluedMappingScalarGraph ρ) :=
        helperForRemark_5_24_4_maximalMonotone_iff_scalarGraph_maximalCoordinatewise ρ
      _ ↔ IsCompleteNondecreasingCurve (oneDimensionalMultivaluedMappingScalarGraph ρ) := by
        exact
          (isCompleteNondecreasingCurve_iff_isMaximalCoordinatewiseTotallyOrdered
            (oneDimensionalMultivaluedMappingScalarGraph ρ)).symm
  · constructor
    · -- The nontrivial direction is supplied by the maximal-extension and subdifferential route.
      exact helperForRemark_5_24_4_monotone_implies_cyclicallyMonotone ρ
    · intro hcyclic
      -- The reverse implication is Proposition 5.24.4 specialized to dimension one.
      exact hcyclic.isMonotoneMultivaluedMapping

-- Proof sketch: in dimensions `n > 1`, choose a nonzero skew-adjoint linear map on `ℝ^n`, for
-- instance a quarter-turn on a two-dimensional coordinate plane extended by zero on the
-- orthogonal complement. The singleton-valued mapping `x ↦ {L x}` is monotone because the
-- symmetric part of `L` vanishes, but it is not cyclically monotone since cyclic monotonicity of
-- a linear map forces symmetry, which this example fails.


end Section24
end Chap05
