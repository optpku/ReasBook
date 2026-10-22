/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section10_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part7

section Chap05
section Section24

open scoped ConvexAnalysis

attribute [local instance] Classical.propDecidable

/-- Definition 5.24.1: The effective domain of the subdifferential mapping `∂ f` is the set of
points `x` for which `∂ f (x)` is nonempty. -/
def subdifferentialEffectiveDomain {n : ℕ} (f : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | ∂ f (x) ≠ ∅}

/-- Helper for Remark 5.24.1: membership in the effective domain of `∂ f` is equivalent to the
subdifferential being nonempty. -/
lemma helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    x ∈ subdifferentialEffectiveDomain f ↔ Set.Nonempty (∂ f x) := by
  -- Unfold the definition and rewrite nonemptiness of a set as inequality with `∅`.
  simp [subdifferentialEffectiveDomain, Set.nonempty_iff_ne_empty]

/-- Helper for Remark 5.24.1: points in the relative interior of `dom f` have a nonempty
subdifferential. -/
lemma helperForRemark_5_24_1_subdifferentiable_of_mem_relativeInterior {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) {x : Fin n → ℝ}
    (hx :
      x ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    x ∈ subdifferentialEffectiveDomain f := by
  -- The relative-interior clause of Theorem 23.4 gives the required nonempty subdifferential.
  rcases
      subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        f hproper x with
    ⟨_hoff, hri, _hrest⟩
  exact
    (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty f x).2
      ((hri hx).1)

/-- Helper for Remark 5.24.1: a point with nonempty subdifferential lies in `dom f`. -/
lemma helperForRemark_5_24_1_mem_effectiveDomain_of_subdifferentiable {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) {x : Fin n → ℝ}
    (hx : x ∈ subdifferentialEffectiveDomain f) :
    x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
  -- Off the effective domain, Theorem 23.4 says the subdifferential is empty, contradicting `hx`.
  rcases
      subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        f hproper x with
    ⟨hoff, _hri, _hrest⟩
  by_contra hxDom
  have hnonempty : Set.Nonempty (∂ f x) :=
    (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty f x).1 hx
  exact hnonempty.ne_empty (hoff hxDom)

-- Proof sketch: apply Theorem 23.4 at each point `x`. The relative-interior clause gives
-- nonemptiness of `∂ f (x)`, which is exactly membership in `dom ∂ f`, and any nonempty
-- subdifferential forces `f x` to be finite, hence `x ∈ dom f`.
/-- Remark 5.24.1: For a proper convex function, the effective domain of the subdifferential
mapping is squeezed between the relative interior and the effective domain of `f`:
`ri (dom f) ⊆ dom ∂ f ⊆ dom f`. -/
theorem relativeInterior_subset_subdifferentialEffectiveDomain_subset_effectiveDomain {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ⊆
        subdifferentialEffectiveDomain f ∧
      subdifferentialEffectiveDomain f ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
  constructor
  · intro x hx
    -- The left inclusion is exactly the relative-interior helper lemma.
    exact helperForRemark_5_24_1_subdifferentiable_of_mem_relativeInterior f hproper hx
  · intro x hx
    -- The right inclusion follows from the off-domain emptiness clause of Theorem 23.4.
    exact helperForRemark_5_24_1_mem_effectiveDomain_of_subdifferentiable f hproper hx

-- Proof sketch: use the standard counterexample from convex analysis in which `f` is proper and
-- convex but the set of points with nonempty subdifferential is not convex.
/-- A counterexample showing that the effective domain of the subdifferential need not be convex. -/
lemma exists_nonconvex_subdifferentialEffectiveDomain :
    ∃ (n : ℕ) (f : (Fin n → ℝ) → EReal),
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
      ¬ Convex ℝ (subdifferentialEffectiveDomain f) := by
  rcases subdifferentiableSet_nonconvex_for_halfPlaneSquareRootMaxExample with
    ⟨hproper, _hdom, hsubdiff, hnonconvex⟩
  refine ⟨2, nonconvexSubdifferentiabilityExampleFunction, hproper, ?_⟩
  simpa [subdifferentialEffectiveDomain, Set.nonempty_iff_ne_empty] using hnonconvex

/-- Definition 5.24.2: The range of the subdifferential mapping `∂ f` is the union of all
subdifferentials `∂ f (x)` as `x` ranges over `ℝ^n`. -/
def subdifferentialRange {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    Set (Module.Dual ℝ (Fin n → ℝ)) :=
  ⋃ x, ∂ f x

/-- Helper for Remark 5.24.2: membership in the range of `∂ f` is equivalent to membership in
one concrete subdifferential. -/
lemma helperForRemark_5_24_2_mem_subdifferentialRange_iff_exists {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (xDual : Module.Dual ℝ (Fin n → ℝ)) :
    xDual ∈ subdifferentialRange f ↔ ∃ x : Fin n → ℝ, xDual ∈ ∂ f x := by
  -- Unfold the union once so the proof can work with an explicit primal witness.
  simp [subdifferentialRange]

/-- Helper for Remark 5.24.2: points in `dom ∂(f*)` correspond to covectors in `range ∂ f`
under the Euclidean identification. -/
lemma helperForRemark_5_24_2_preimage_subdifferentialRange_of_mem_subdifferentialEffectiveDomain_fenchelConjugate
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ subdifferentialEffectiveDomain (fenchelConjugate n f)) :
    xStar ∈ (dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialRange f := by
  -- Rewrite `xStar ∈ dom ∂(f*)` as existence of a concrete Euclidean subgradient.
  rcases
      (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
        (fenchelConjugate n f) xStar).1 hxStar with
    ⟨xDual, hxDual⟩
  rcases (dotProductEquiv ℝ (Fin n)).surjective xDual with ⟨x, rfl⟩
  -- Corollary 23.5.1 transports that conjugate subgradient witness back to a subgradient of `f`.
  have hxSub : IsEuclideanSubgradientAt f x xStar := by
    exact
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hclosed hproper x xStar).1
        (by simpa [IsEuclideanSubgradientAt] using hxDual)
  -- Unfold the range to package the transported witness.
  change dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialRange f
  rw [helperForRemark_5_24_2_mem_subdifferentialRange_iff_exists]
  exact ⟨x, by simpa [IsEuclideanSubgradientAt] using hxSub⟩

/-- Helper for Remark 5.24.2: a covector in `range ∂ f` yields a point of `dom ∂(f*)` after
transporting it back through Corollary 23.5.1. -/
lemma helperForRemark_5_24_2_mem_subdifferentialEffectiveDomain_fenchelConjugate_of_preimage_subdifferentialRange
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ (dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialRange f) :
    xStar ∈ subdifferentialEffectiveDomain (fenchelConjugate n f) := by
  -- Unfold the preimage and the range to obtain an explicit subgradient of `f`.
  rw [Set.mem_preimage] at hxStar
  rcases
      (helperForRemark_5_24_2_mem_subdifferentialRange_iff_exists
        f (dotProductEquiv ℝ (Fin n) xStar)).1 hxStar with
    ⟨x, hxSub⟩
  -- Corollary 23.5.1 turns that witness into a subgradient of `f*` at `xStar`.
  have hxStarSub : IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x := by
    exact
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hclosed hproper x xStar).2
        (by simpa [IsEuclideanSubgradientAt] using hxSub)
  -- Repackage the transported witness as nonemptiness of `∂(f*) (xStar)`.
  exact
    (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
      (fenchelConjugate n f) xStar).2
      ⟨dotProductEquiv ℝ (Fin n) x, by simpa [IsEuclideanSubgradientAt] using hxStarSub⟩

-- Proof sketch: identify dual vectors with vectors in `ℝ^n` using `dotProductEquiv`. By
-- Corollary 23.5.1, a dual vector lies in `range ∂ f` exactly when the corresponding vector lies
-- in the effective domain of the subdifferential of `f*`. Then apply Remark 5.24.1 to `f*`.
/-- Remark 5.24.2: Under the Euclidean identification of vectors with dual vectors, if `f` is a
closed proper convex function, then the range of `∂ f` is squeezed between the relative interior
and the effective domain of `f*`:
`ri (dom f^*) ⊆ range ∂ f ⊆ dom f^*`, where `f* = fenchelConjugate n f`. -/
theorem relativeInterior_subset_preimage_subdifferentialRange_subset_effectiveDomain_fenchelConjugate
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ⊆
          (dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialRange f ∧
      (dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialRange f ⊆
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
  -- Apply Remark 5.24.1 to `f*`; the remaining work is to identify `dom ∂(f*)` with
  -- the preimage of `range ∂ f` under `dotProductEquiv`.
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hstarDomain :
      euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ⊆
            subdifferentialEffectiveDomain (fenchelConjugate n f) ∧
        subdifferentialEffectiveDomain (fenchelConjugate n f) ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    relativeInterior_subset_subdifferentialEffectiveDomain_subset_effectiveDomain
      (fenchelConjugate n f) hproperStar
  constructor
  · intro xStar hxStar
    -- First enter `dom ∂(f*)` using Remark 5.24.1, then transport the witness back to `range ∂ f`.
    exact
      helperForRemark_5_24_2_preimage_subdifferentialRange_of_mem_subdifferentialEffectiveDomain_fenchelConjugate
        f hclosed hproper (hstarDomain.1 hxStar)
  · intro xStar hxStar
    -- Reverse the transport to recover `xStar ∈ dom ∂(f*)`, then use Remark 5.24.1 again.
    exact
      hstarDomain.2
        (helperForRemark_5_24_2_mem_subdifferentialEffectiveDomain_fenchelConjugate_of_preimage_subdifferentialRange
          f hclosed hproper hxStar)

/-- Definition 5.24.3: The graph of the subdifferential mapping `∂ f` is the set of pairs
`(x, xStar)` such that `xStar ∈ ∂ f (x)`. -/
def subdifferentialGraph {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    Set ((Fin n → ℝ) × Module.Dual ℝ (Fin n → ℝ)) :=
  {p | p.2 ∈ ∂ f (p.1)}

-- Proof sketch: rewrite subgradient membership by Theorem 23.5 as the Fenchel-Young equality
-- `f x + f*(xStar) = ⟪xStar, x⟫`, then pass to the limit along the convergent sequences using
-- closedness of `f` and of `f*`. This shows the limit pair still satisfies the equality, hence
-- lies in the graph of `∂ f`; the closed-graph formulation is the equivalent topological
-- restatement after identifying covectors with vectors by `dotProductEquiv`.
/-- Closed-graph property of the subdifferential: if `f` is a closed proper convex function on
`ℝ^n`, and sequences `xᵢ → x`
and `xᵢ* → x*` satisfy `dotProductEquiv ℝ (Fin n) xᵢ* ∈ ∂ f (xᵢ)` for every `i`, then
`dotProductEquiv ℝ (Fin n) x* ∈ ∂ f (x)`. Equivalently, under the Euclidean identification of
covectors with vectors, the graph of `∂ f` is a closed subset of `ℝ^n × ℝ^n`. -/
theorem subdifferential_limit_mem_and_isClosed_graph {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    (∀ ⦃x xStar : Fin n → ℝ⦄ (xSeq xStarSeq : ℕ → Fin n → ℝ),
      (∀ i : ℕ, dotProductEquiv ℝ (Fin n) (xStarSeq i) ∈ ∂ f (xSeq i)) →
      Filter.Tendsto xSeq Filter.atTop (nhds x) →
      Filter.Tendsto xStarSeq Filter.atTop (nhds xStar) →
      dotProductEquiv ℝ (Fin n) xStar ∈ ∂ f x) ∧
      IsClosed {p : (Fin n → ℝ) × (Fin n → ℝ) |
        dotProductEquiv ℝ (Fin n) p.2 ∈ ∂ f p.1} := by
  -- First prove stability of graph membership under componentwise sequence limits.
  have hlimit_mem :
      ∀ ⦃x xStar : Fin n → ℝ⦄ (xSeq xStarSeq : ℕ → Fin n → ℝ),
        (∀ i : ℕ, dotProductEquiv ℝ (Fin n) (xStarSeq i) ∈ ∂ f (xSeq i)) →
        Filter.Tendsto xSeq Filter.atTop (nhds x) →
        Filter.Tendsto xStarSeq Filter.atTop (nhds xStar) →
        dotProductEquiv ℝ (Fin n) xStar ∈ ∂ f x := by
    intro x xStar xSeq xStarSeq hmem hxTend hxStarTend
    -- Convert each graph-membership hypothesis into the Fenchel-Young inequality at index `i`.
    have hfy : ∀ i : ℕ, FenchelYoungInequalityAt f (xSeq i) (xStarSeq i) := by
      intro i
      have hsub : IsEuclideanSubgradientAt f (xSeq i) (xStarSeq i) := by
        simpa [IsEuclideanSubgradientAt] using hmem i
      exact
        (((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
          f hproper (xSeq i) (xStarSeq i)).1.out 0 2).1 hsub)
    -- Lower semicontinuity of `f` gives the primal liminf lower bound along `xSeq`.
    have hfx_liminf : f x ≤ Filter.liminf (fun i => f (xSeq i)) Filter.atTop := by
      have hfx_nhds : f x ≤ Filter.liminf f (nhds x) := by
        simpa using (hclosed.2.le_liminf x)
      have hmap : Filter.map xSeq Filter.atTop ≤ nhds x := hxTend
      have hfx_map : f x ≤ Filter.liminf f (Filter.map xSeq Filter.atTop) :=
        le_trans hfx_nhds (Filter.liminf_le_liminf_of_le hmap)
      simpa [Filter.liminf, Filter.map_map] using hfx_map
    -- Lower semicontinuity of `f*` gives the conjugate liminf lower bound along `xStarSeq`.
    have hfxStar_liminf :
        fenchelConjugate n f xStar ≤
          Filter.liminf (fun i => fenchelConjugate n f (xStarSeq i)) Filter.atTop := by
      have hconjClosed : LowerSemicontinuous (fenchelConjugate n f) :=
        (fenchelConjugate_closedConvex (n := n) (f := f)).1
      have hfxStar_nhds :
          fenchelConjugate n f xStar ≤
            Filter.liminf (fenchelConjugate n f) (nhds xStar) := by
        simpa using (hconjClosed.le_liminf xStar)
      have hmap : Filter.map xStarSeq Filter.atTop ≤ nhds xStar := hxStarTend
      have hfxStar_map :
          fenchelConjugate n f xStar ≤
            Filter.liminf (fenchelConjugate n f) (Filter.map xStarSeq Filter.atTop) :=
        le_trans hfxStar_nhds (Filter.liminf_le_liminf_of_le hmap)
      simpa [Filter.liminf, Filter.map_map] using hfxStar_map
    -- Add both lower bounds, then use `le_liminf_add` on EReal sequences.
    have hsum_liminf :
        f x + fenchelConjugate n f xStar ≤
          Filter.liminf
            (fun i => f (xSeq i) + fenchelConjugate n f (xStarSeq i))
            Filter.atTop := by
      have hsum :
          Filter.liminf (fun i => f (xSeq i)) Filter.atTop +
              Filter.liminf (fun i => fenchelConjugate n f (xStarSeq i)) Filter.atTop ≤
            Filter.liminf
              (fun i => f (xSeq i) + fenchelConjugate n f (xStarSeq i))
              Filter.atTop := by
        simpa using
          (EReal.le_liminf_add (f := (Filter.atTop : Filter ℕ))
            (u := fun i => f (xSeq i))
            (v := fun i => fenchelConjugate n f (xStarSeq i)))
      exact le_trans (add_le_add hfx_liminf hfxStar_liminf) hsum
    -- Pointwise Fenchel-Young inequalities imply a liminf upper bound by the dot-product liminf.
    have hliminf_le_dot :
        Filter.liminf
            (fun i => f (xSeq i) + fenchelConjugate n f (xStarSeq i))
            Filter.atTop ≤
          Filter.liminf
            (fun i => (((dotProduct (xSeq i) (xStarSeq i) : ℝ) : EReal)))
            Filter.atTop := by
      have hEventually :
          ∀ᶠ i : ℕ in Filter.atTop,
            f (xSeq i) + fenchelConjugate n f (xStarSeq i) ≤
              (((dotProduct (xSeq i) (xStarSeq i) : ℝ) : EReal)) := by
        exact Filter.Eventually.of_forall (fun i => by
          simpa [FenchelYoungInequalityAt] using hfy i)
      exact Filter.liminf_le_liminf hEventually
    -- Continuity of dot product identifies the right liminf with the dot product at the limit pair.
    have hpairTend :
        Filter.Tendsto
          (fun i : ℕ => (xSeq i, xStarSeq i))
          Filter.atTop (nhds (x, xStar)) := by
      simpa [nhds_prod_eq] using hxTend.prodMk hxStarTend
    have hdotTend :
        Filter.Tendsto
          (fun i : ℕ => dotProduct (xSeq i) (xStarSeq i))
          Filter.atTop (nhds (dotProduct x xStar)) := by
      have hcont :
          ContinuousAt (fun p : (Fin n → ℝ) × (Fin n → ℝ) => dotProduct p.1 p.2) (x, xStar) := by
        exact (continuous_fst.dotProduct continuous_snd).continuousAt
      exact hcont.tendsto.comp hpairTend
    have hdotERealTend :
        Filter.Tendsto
          (fun i : ℕ => (((dotProduct (xSeq i) (xStarSeq i) : ℝ) : EReal)))
          Filter.atTop (nhds (((dotProduct x xStar : ℝ) : EReal))) := by
      exact continuous_coe_real_ereal.continuousAt.tendsto.comp hdotTend
    have hdot_liminf :
        Filter.liminf
            (fun i => (((dotProduct (xSeq i) (xStarSeq i) : ℝ) : EReal)))
            Filter.atTop =
          (((dotProduct x xStar : ℝ) : EReal)) := by
      exact hdotERealTend.liminf_eq
    -- The liminf sandwich yields Fenchel-Young at the limit point, hence subgradient membership.
    have hfy_limit : FenchelYoungInequalityAt f x xStar := by
      refine (show f x + fenchelConjugate n f xStar ≤ (((dotProduct x xStar : ℝ) : EReal)) from ?_)
      calc
        f x + fenchelConjugate n f xStar ≤
            Filter.liminf
              (fun i => f (xSeq i) + fenchelConjugate n f (xStarSeq i))
              Filter.atTop := hsum_liminf
        _ ≤ Filter.liminf
              (fun i => (((dotProduct (xSeq i) (xStarSeq i) : ℝ) : EReal)))
              Filter.atTop := hliminf_le_dot
        _ = (((dotProduct x xStar : ℝ) : EReal)) := hdot_liminf
    have hsub_limit : IsEuclideanSubgradientAt f x xStar :=
      (((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        f hproper x xStar).1.out 0 2).2 hfy_limit)
    simpa [IsEuclideanSubgradientAt] using hsub_limit
  constructor
  · exact hlimit_mem
  · -- Sequential closedness on the product space implies topological closedness.
    let G : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
      {p | dotProductEquiv ℝ (Fin n) p.2 ∈ ∂ f p.1}
    have hseqClosed : IsSeqClosed G := by
      intro pSeq p hpSeq hpTend
      -- Extract componentwise convergence from the product convergence.
      have hxTend :
          Filter.Tendsto (fun i : ℕ => (pSeq i).1) Filter.atTop (nhds p.1) :=
        continuous_fst.continuousAt.tendsto.comp hpTend
      have hxStarTend :
          Filter.Tendsto (fun i : ℕ => (pSeq i).2) Filter.atTop (nhds p.2) :=
        continuous_snd.continuousAt.tendsto.comp hpTend
      -- Apply the limit-stability statement proved above to the component sequences.
      have hmemLimit :
          dotProductEquiv ℝ (Fin n) p.2 ∈ ∂ f p.1 :=
        hlimit_mem (x := p.1) (xStar := p.2)
          (fun i => (pSeq i).1) (fun i => (pSeq i).2)
          (by
            intro i
            simpa [G] using hpSeq i)
          hxTend hxStarTend
      simpa [G] using hmemLimit
    exact (isSeqClosed_iff_isClosed).1 hseqClosed

-- Proof sketch: use Theorem 10.8 and Corollary 10.8.1 on small closed balls inside the open
-- convex set `C` to control the pointwise convergence of the difference quotients uniformly near
-- `x`. Passing to `t ↓ 0` yields the limsup inequality for the upper directional derivatives.
-- For the subdifferentials, combine that directional-derivative control with the closedness of
-- the epigraph/support-function description from Chapter 23, then translate the resulting
-- approximate-subgradient estimate into a Euclidean `ε`-neighborhood of `∂ f (x)` under
-- `dotProductEquiv`.
-- Proof sketch: use Theorem 10.8 and Corollary 10.8.1 on small closed balls inside the open
-- convex set `C` to control the pointwise convergence of the difference quotients uniformly near
-- `x`. Passing to `t ↓ 0` yields the limsup inequality for the upper directional derivatives.
-- For the subdifferentials, combine that directional-derivative control with the closedness of
-- the epigraph/support-function description from Chapter 23, then translate the resulting
-- approximate-subgradient estimate into a Euclidean `ε`-neighborhood of `∂ f (x)` under
-- `dotProductEquiv`.
/-- Helper for Theorem 5.24.8: finiteness on a nonempty open set forces a globally convex
function to be proper. -/
lemma helperForTheorem_5_24_8_proper_of_finite_on_open
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCopen : IsOpen C) {f : (Fin n → ℝ) → EReal}
    (hf : ConvexFunction f) {x : Fin n → ℝ} (hx : x ∈ C)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
  have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [ConvexFunction] using hf
  by_cases hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f
  · exact hproper
  · have himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
      exact ⟨hconv, hproper⟩
    have hCsubdom : C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
      intro z hz
      have hzTop : f z ≠ (⊤ : EReal) := (hf_finite z hz).1
      have hzMem :
          z ∈ {u : Fin n → ℝ | u ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f u < (⊤ : EReal)} := by
        exact ⟨by simp, lt_top_iff_ne_top.mpr hzTop⟩
      simpa [effectiveDomain_eq] using hzMem
    have hxInt :
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
      -- The open set `C` sits inside the effective domain because `f` is finite on `C`.
      exact mem_interior_iff_mem_nhds.mpr <|
        Filter.mem_of_superset (hCopen.mem_nhds hx) hCsubdom
    have hxri :
        x ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
      helperForTheorem_23_4_mem_relativeInterior_of_mem_interior hxInt
    have hxriE :
        (EuclideanSpace.equiv (Fin n) ℝ).symm x ∈
          euclideanRelativeInterior n
            ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
      have hxri' :=
        (mem_euclideanRelativeInterior_fin_iff (n := n)
          (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) (x := x)).1 hxri
      rw [helperForTheorem_23_4_preimage_eq_symmImage]
      exact hxri'
    have hbot : f x = (⊥ : EReal) := by
      simpa using
        (improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := f) himproper
          ((EuclideanSpace.equiv (Fin n) ℝ).symm x) hxriE)
    exact False.elim ((hf_finite x hx).2 hbot)

/-- Helper for Theorem 5.24.8: on the finite open set `C`, the functions can be converted to
real-valued convex functions and the pointwise convergence survives taking `toReal`. -/
lemma helperForTheorem_5_24_8_toRealConvexOn_and_pointwiseTendsto
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCconv : Convex ℝ C)
    {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (fSeq : ℕ → (Fin n → ℝ) → EReal) (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal))
    (hpoint : ∀ z ∈ C, Filter.Tendsto (fun i => fSeq i z) Filter.atTop (nhds (f z))) :
    C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
      (∀ i, C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fSeq i)) ∧
      ConvexOn ℝ C (fun z => (f z).toReal) ∧
      (∀ i, ConvexOn ℝ C (fun z => (fSeq i z).toReal)) ∧
      (∀ z ∈ C, Filter.Tendsto (fun i => (fSeq i z).toReal) Filter.atTop
        (nhds ((f z).toReal))) := by
  have hCsubdom : C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    intro z hz
    have hzTop : f z ≠ (⊤ : EReal) := (hf_finite z hz).1
    have hzMem :
        z ∈ {u : Fin n → ℝ | u ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f u < (⊤ : EReal)} := by
      exact ⟨by simp, lt_top_iff_ne_top.mpr hzTop⟩
    simpa [effectiveDomain_eq] using hzMem
  have hCsubdomSeq : ∀ i, C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fSeq i) := by
    intro i z hz
    have hzTop : fSeq i z ≠ (⊤ : EReal) := (hfSeq_finite i z hz).1
    have hzMem :
        z ∈ {u : Fin n → ℝ | u ∈ (Set.univ : Set (Fin n → ℝ)) ∧ fSeq i u < (⊤ : EReal)} := by
      exact ⟨by simp, lt_top_iff_ne_top.mpr hzTop⟩
    simpa [effectiveDomain_eq] using hzMem
  have htoRealConv :
      ConvexOn ℝ C (fun z => (f z).toReal) := by
    refine ⟨hCconv, ?_⟩
    intro u hu v hv a b ha hb hab
    have hb_le_one : b ≤ (1 : ℝ) := by
      linarith
    have h_one_sub_b_nonneg : 0 ≤ 1 - b := by
      linarith
    have h_one_sub_b_sum : (1 - b) + b = 1 := by
      ring
    have huv' : (1 - b) • u + b • v ∈ C :=
      hCconv hu hv h_one_sub_b_nonneg hb h_one_sub_b_sum
    have huvFinite' := hf_finite ((1 - b) • u + b • v) huv'
    have huFinite := hf_finite u hu
    have hvFinite := hf_finite v hv
    have huEq : f u = (((f u).toReal : ℝ) : EReal) := by
      simpa using (EReal.coe_toReal huFinite.1 huFinite.2).symm
    have hvEq : f v = (((f v).toReal : ℝ) : EReal) := by
      simpa using (EReal.coe_toReal hvFinite.1 hvFinite.2).symm
    have hμ : f u ≤ (((f u).toReal : ℝ) : EReal) := le_of_eq huEq
    have hν : f v ≤ (((f v).toReal : ℝ) : EReal) := le_of_eq hvEq
    have hcond :=
      convexFunctionOn_epigraph_condition
        (S := (Set.univ : Set (Fin n → ℝ))) (f := f) (by simpa [ConvexFunction] using hf)
        u (by simp) v (by simp) (f u).toReal (f v).toReal hμ hν b hb hb_le_one
    rcases hcond with ⟨_hmem, hle⟩
    have hab' : a = 1 - b := by
      linarith
    have hreal :
        (f ((1 - b) • u + b • v)).toReal ≤
          (1 - b) * (f u).toReal + b * (f v).toReal := by
      have hrhsTop :
          ¬(1 - (b : EReal)) * ((f u).toReal : EReal) +
              (b : EReal) * ((f v).toReal : EReal) = (⊤ : EReal) := by
        simpa [EReal.coe_mul, EReal.coe_sub] using
          EReal.add_ne_top
            (by
              simpa [EReal.coe_mul, EReal.coe_sub] using
                (EReal.coe_ne_top ((1 - b) * (f u).toReal)))
            (by
              simpa [EReal.coe_mul] using
                (EReal.coe_ne_top (b * (f v).toReal)))
      exact EReal.toReal_le_toReal hle huvFinite'.2 hrhsTop
    simpa [hab', smul_eq_mul, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
      sub_eq_add_neg] using hreal
  have htoRealConvSeq :
      ∀ i, ConvexOn ℝ C (fun z => (fSeq i z).toReal) := by
    intro i
    refine ⟨hCconv, ?_⟩
    intro u hu v hv a b ha hb hab
    have hb_le_one : b ≤ (1 : ℝ) := by
      linarith
    have h_one_sub_b_nonneg : 0 ≤ 1 - b := by
      linarith
    have h_one_sub_b_sum : (1 - b) + b = 1 := by
      ring
    have huv' : (1 - b) • u + b • v ∈ C :=
      hCconv hu hv h_one_sub_b_nonneg hb h_one_sub_b_sum
    have huvFinite' := hfSeq_finite i ((1 - b) • u + b • v) huv'
    have huFinite := hfSeq_finite i u hu
    have hvFinite := hfSeq_finite i v hv
    have huEq : fSeq i u = (((fSeq i u).toReal : ℝ) : EReal) := by
      simpa using (EReal.coe_toReal huFinite.1 huFinite.2).symm
    have hvEq : fSeq i v = (((fSeq i v).toReal : ℝ) : EReal) := by
      simpa using (EReal.coe_toReal hvFinite.1 hvFinite.2).symm
    have hμ : fSeq i u ≤ (((fSeq i u).toReal : ℝ) : EReal) := le_of_eq huEq
    have hν : fSeq i v ≤ (((fSeq i v).toReal : ℝ) : EReal) := le_of_eq hvEq
    have hcond :=
      convexFunctionOn_epigraph_condition
        (S := (Set.univ : Set (Fin n → ℝ))) (f := fSeq i)
        (by simpa [ConvexFunction] using hfSeq i)
        u (by simp) v (by simp) (fSeq i u).toReal (fSeq i v).toReal hμ hν b hb hb_le_one
    rcases hcond with ⟨_hmem, hle⟩
    have hab' : a = 1 - b := by
      linarith
    have hreal :
        (fSeq i ((1 - b) • u + b • v)).toReal ≤
          (1 - b) * (fSeq i u).toReal + b * (fSeq i v).toReal := by
      have hrhsTop :
          ¬(1 - (b : EReal)) * ((fSeq i u).toReal : EReal) +
              (b : EReal) * ((fSeq i v).toReal : EReal) = (⊤ : EReal) := by
        simpa [EReal.coe_mul, EReal.coe_sub] using
          EReal.add_ne_top
            (by
              simpa [EReal.coe_mul, EReal.coe_sub] using
                (EReal.coe_ne_top ((1 - b) * (fSeq i u).toReal)))
            (by
              simpa [EReal.coe_mul] using
                (EReal.coe_ne_top (b * (fSeq i v).toReal)))
      exact EReal.toReal_le_toReal hle huvFinite'.2 hrhsTop
    simpa [hab', smul_eq_mul, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
      sub_eq_add_neg] using hreal
  have htoRealPoint :
      ∀ z ∈ C, Filter.Tendsto (fun i => (fSeq i z).toReal) Filter.atTop
        (nhds ((f z).toReal)) := by
    intro z hz
    have hzFinite := hf_finite z hz
    exact (EReal.tendsto_toReal hzFinite.1 hzFinite.2).comp (hpoint z hz)
  exact ⟨hCsubdom, hCsubdomSeq, htoRealConv, htoRealConvSeq, htoRealPoint⟩

/-- Helper for Theorem 5.24.8: the open set `C` lies inside the effective domains of the limit
and approximating functions, so `x` and each `xᵢ` are interior-domain points. -/
lemma helperForTheorem_5_24_8_mem_interior_effectiveDomain_at_limit_and_sequence
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCopen : IsOpen C) (_hCconv : Convex ℝ C)
    {f : (Fin n → ℝ) → EReal} (_hf : ConvexFunction f)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (fSeq : ℕ → (Fin n → ℝ) → EReal) (_hfSeq : ∀ i, ConvexFunction (fSeq i))
    (hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal))
    {x : Fin n → ℝ} (hx : x ∈ C) (xSeq : ℕ → Fin n → ℝ) (hxSeq : ∀ i, xSeq i ∈ C) :
    x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
      ∀ i, xSeq i ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fSeq i)) := by
  have hCsubdom : C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    intro z hz
    have hzTop : f z ≠ (⊤ : EReal) := (hf_finite z hz).1
    have hzMem :
        z ∈ {u : Fin n → ℝ | u ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f u < (⊤ : EReal)} := by
      exact ⟨by simp, lt_top_iff_ne_top.mpr hzTop⟩
    simpa [effectiveDomain_eq] using hzMem
  have hCsubdomSeq : ∀ i, C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fSeq i) := by
    intro i z hz
    have hzTop : fSeq i z ≠ (⊤ : EReal) := (hfSeq_finite i z hz).1
    have hzMem :
        z ∈ {u : Fin n → ℝ | u ∈ (Set.univ : Set (Fin n → ℝ)) ∧ fSeq i u < (⊤ : EReal)} := by
      exact ⟨by simp, lt_top_iff_ne_top.mpr hzTop⟩
    simpa [effectiveDomain_eq] using hzMem
  constructor
  · -- Open subsets of the effective domain give interior-domain points.
    exact mem_interior_iff_mem_nhds.mpr <|
      Filter.mem_of_superset (hCopen.mem_nhds hx) hCsubdom
  · intro i
    exact mem_interior_iff_mem_nhds.mpr <|
      Filter.mem_of_superset (hCopen.mem_nhds (hxSeq i)) (hCsubdomSeq i)

/-- Helper for Theorem 5.24.8: at the limit point and along the approximating sequence, all upper
directional derivatives are finite because those points lie in the interior of the effective
domains of proper convex functions. -/
lemma helperForTheorem_5_24_8_directionalDerivative_finite_at_limit_and_sequence
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (fSeq : ℕ → (Fin n → ℝ) → EReal) (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal))
    {x : Fin n → ℝ} (hx : x ∈ C) (xSeq : ℕ → Fin n → ℝ) (hxSeq : ∀ i, xSeq i ∈ C) :
    (∀ y : Fin n → ℝ,
      upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) ∧
        upperDirectionalDerivativeAt f x y ≠ (⊥ : EReal)) ∧
      ∀ i : ℕ, ∀ y : Fin n → ℝ,
        upperDirectionalDerivativeAt (fSeq i) (xSeq i) y ≠ (⊤ : EReal) ∧
          upperDirectionalDerivativeAt (fSeq i) (xSeq i) y ≠ (⊥ : EReal) := by
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_5_24_8_proper_of_finite_on_open hCopen hf hx hf_finite
  have hproperSeq :
      ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fSeq i) := by
    intro i
    exact helperForTheorem_5_24_8_proper_of_finite_on_open
      hCopen (hfSeq i) (hxSeq i) (hfSeq_finite i)
  have hinterior :=
    helperForTheorem_5_24_8_mem_interior_effectiveDomain_at_limit_and_sequence
      hCopen hCconv hf hf_finite fSeq hfSeq hfSeq_finite hx xSeq hxSeq
  constructor
  · intro y
    rcases
        subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
          f hproper x with
      ⟨_hoff, _hri, _hiff, hfinite⟩
    exact hfinite hinterior.1 y
  · intro i y
    rcases
        subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
          (fSeq i) (hproperSeq i) (xSeq i) with
      ⟨_hoff, _hri, _hiff, hfinite⟩
    exact hfinite (hinterior.2 i) y

/-- Helper for Theorem 5.24.8: coercing a convergent real sequence into `EReal` preserves its
limit. -/
lemma helperForTheorem_5_24_8_tendsto_coe_of_tendsto
    {u : ℕ → ℝ} {l : ℝ}
    (hu : Filter.Tendsto u Filter.atTop (nhds l)) :
    Filter.Tendsto (fun i => ((u i : ℝ) : EReal)) Filter.atTop (nhds (l : EReal)) := by
  -- Pass to `EReal` through the continuous coercion from the real line.
  exact EReal.tendsto_coe.2 hu

/-- Helper for Theorem 5.24.8: once the stepped values are finite, the `EReal`
directional-difference quotient is exactly the coerced real secant quotient. -/
lemma helperForTheorem_5_24_8_eventually_fixedStepQuotient_eq_toReal
    {n : ℕ} (fSeq : ℕ → (Fin n → ℝ) → EReal)
    (xSeq ySeq : ℕ → Fin n → ℝ)
    {t : ℝ}
    (hxSeqFinite : ∀ i, fSeq i (xSeq i) ≠ (⊤ : EReal) ∧ fSeq i (xSeq i) ≠ (⊥ : EReal))
    (hstepFinite :
      ∀ᶠ i in Filter.atTop,
        fSeq i (xSeq i + t • ySeq i) ≠ (⊤ : EReal) ∧
          fSeq i (xSeq i + t • ySeq i) ≠ (⊥ : EReal)) :
    (fun i => directionalDifferenceQuotientAt (fSeq i) (xSeq i) (ySeq i) t) =ᶠ[Filter.atTop]
      (fun i =>
        ((((fSeq i (xSeq i + t • ySeq i)).toReal - (fSeq i (xSeq i)).toReal) / t : ℝ) : EReal)) := by
  -- Rewrite the quotient pointwise after ruling out `⊤` and `⊥` at both endpoints.
  filter_upwards [hstepFinite] with i hi
  have hxFinite := hxSeqFinite i
  simp [directionalDifferenceQuotientAt, EReal.coe_div, EReal.coe_sub,
    EReal.coe_toReal hi.1 hi.2, EReal.coe_toReal hxFinite.1 hxFinite.2]

/-- Helper for Theorem 5.24.8: if the positive-step quotients converge in `EReal`, then the
limsup of the upper directional derivatives is bounded by that same fixed-step limit. -/
lemma helperForTheorem_5_24_8_limsup_le_fixedStepQuotient
    {n : ℕ} (fSeq : ℕ → (Fin n → ℝ) → EReal)
    (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (xSeq ySeq : ℕ → Fin n → ℝ)
    (hxSeqFinite : ∀ i, fSeq i (xSeq i) ≠ (⊤ : EReal) ∧ fSeq i (xSeq i) ≠ (⊥ : EReal))
    {t q : ℝ} (ht : 0 < t)
    (hquot :
      Filter.Tendsto
        (fun i => directionalDifferenceQuotientAt (fSeq i) (xSeq i) (ySeq i) t)
        Filter.atTop (nhds ((q : ℝ) : EReal))) :
    Filter.limsup (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (ySeq i))
      Filter.atTop ≤ ((q : ℝ) : EReal) := by
  have hEvent :
      ∀ᶠ i in Filter.atTop,
        upperDirectionalDerivativeAt (fSeq i) (xSeq i) (ySeq i) ≤
          directionalDifferenceQuotientAt (fSeq i) (xSeq i) (ySeq i) t := by
    -- Compare each derivative with its `sInf` representation and then evaluate the infimum at `t`.
    refine Filter.Eventually.of_forall ?_
    intro i
    rcases convex_directionalDerivative_monotone_exists_and_sublinear
        (fSeq i) (hfSeq i) (xSeq i) (hxSeqFinite i) with
      ⟨hdirData, _hpos, _hconv, _hzero, _hsymm⟩
    rw [helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients
      (fSeq i) (xSeq i) (ySeq i) (hdirData (ySeq i)).1]
    exact
      csInf_le
        (by
          refine ⟨⊥, ?_⟩
          intro z hz
          simp at hz ⊢)
        ⟨t, ht, rfl⟩
  have hlimsup_le :
      Filter.limsup (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (ySeq i))
        Filter.atTop ≤
        Filter.limsup
          (fun i => directionalDifferenceQuotientAt (fSeq i) (xSeq i) (ySeq i) t)
          Filter.atTop :=
    Filter.limsup_le_limsup hEvent
  have hlimsup_eq :
      Filter.limsup
          (fun i => directionalDifferenceQuotientAt (fSeq i) (xSeq i) (ySeq i) t)
          Filter.atTop =
        ((q : ℝ) : EReal) :=
    Filter.Tendsto.limsup_eq hquot
  calc
    Filter.limsup (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (ySeq i))
        Filter.atTop ≤
      Filter.limsup
        (fun i => directionalDifferenceQuotientAt (fSeq i) (xSeq i) (ySeq i) t)
        Filter.atTop := hlimsup_le
    _ = ((q : ℝ) : EReal) := hlimsup_eq

/-- Helper for Theorem 5.24.8: the real fixed-step secant convergence already suffices for the
fixed-step limsup inequality once the stepped values are eventually finite. -/
lemma helperForTheorem_5_24_8_limsup_le_fixedStepRealQuotient
    {n : ℕ} (fSeq : ℕ → (Fin n → ℝ) → EReal)
    (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (xSeq ySeq : ℕ → Fin n → ℝ)
    (hxSeqFinite : ∀ i, fSeq i (xSeq i) ≠ (⊤ : EReal) ∧ fSeq i (xSeq i) ≠ (⊥ : EReal))
    {t q : ℝ} (ht : 0 < t)
    (hstepFinite :
      ∀ᶠ i in Filter.atTop,
        fSeq i (xSeq i + t • ySeq i) ≠ (⊤ : EReal) ∧
          fSeq i (xSeq i + t • ySeq i) ≠ (⊥ : EReal))
    (hquot :
      Filter.Tendsto
        (fun i =>
          (((fSeq i (xSeq i + t • ySeq i)).toReal - (fSeq i (xSeq i)).toReal) / t : ℝ))
        Filter.atTop (nhds q)) :
    Filter.limsup (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (ySeq i))
      Filter.atTop ≤ ((q : ℝ) : EReal) := by
  have hrewrite :=
    helperForTheorem_5_24_8_eventually_fixedStepQuotient_eq_toReal
      fSeq xSeq ySeq hxSeqFinite hstepFinite
  have hquotEReal :
      Filter.Tendsto
        (fun i =>
          ((((fSeq i (xSeq i + t • ySeq i)).toReal - (fSeq i (xSeq i)).toReal) / t : ℝ) : EReal))
        Filter.atTop (nhds ((q : ℝ) : EReal)) :=
    helperForTheorem_5_24_8_tendsto_coe_of_tendsto hquot
  have hquotTendsto :
      Filter.Tendsto
        (fun i => directionalDifferenceQuotientAt (fSeq i) (xSeq i) (ySeq i) t)
        Filter.atTop (nhds ((q : ℝ) : EReal)) := by
    -- Replace the `EReal` quotient by its eventual real-expression formula.
    exact Filter.Tendsto.congr' hrewrite.symm hquotEReal
  -- Finish with the order-theoretic fixed-step comparison.
  exact
    helperForTheorem_5_24_8_limsup_le_fixedStepQuotient
      fSeq hfSeq xSeq ySeq hxSeqFinite ht hquotTendsto

/-- Helper for Theorem 5.24.8: a convergent real sequence has bounded range. -/
lemma helperForTheorem_5_24_8_boundedRange_of_tendsto_real
    {u : ℕ → ℝ} {l : ℝ}
    (hu : Filter.Tendsto u Filter.atTop (nhds l)) :
    Bornology.IsBounded (Set.range u) := by
  -- Convergence traps the tail in one closed ball, and the finite head is bounded separately.
  have htail : ∀ᶠ n in Filter.atTop, u n ∈ Metric.closedBall l 1 := by
    exact hu (Metric.closedBall_mem_nhds l (by norm_num))
  rcases Filter.eventually_atTop.mp htail with ⟨N, hN⟩
  have hheadFinite : (u '' Set.Iic N).Finite :=
    (Set.finite_Iic N).image u
  have hheadBounded : Bornology.IsBounded (u '' Set.Iic N) :=
    hheadFinite.isBounded
  have htailBounded : Bornology.IsBounded (Metric.closedBall l 1) :=
    Metric.isBounded_closedBall
  have hrangeSubset : Set.range u ⊆ u '' Set.Iic N ∪ Metric.closedBall l 1 := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    by_cases hn : n ≤ N
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr (hN n (Nat.le_of_lt (Nat.lt_of_not_ge hn)))
  exact (hheadBounded.union htailBounded).subset hrangeSubset

/-- Helper for Theorem 5.24.8: on every closed bounded subset of `C`, the realified family
`(fᵢ ·).toReal` admits one common Lipschitz constant. -/
lemma helperForTheorem_5_24_8_realifiedFamily_equiLipschitz_on_closedBoundedSubset
    {n : ℕ} {C S : Set (Fin n → ℝ)} (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (fSeq : ℕ → (Fin n → ℝ) → EReal) (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal))
    (hpoint : ∀ z ∈ C, Filter.Tendsto (fun i => fSeq i z) Filter.atTop (nhds (f z)))
    (hSclosed : IsClosed S) (hSbdd : Bornology.IsBounded S) (hSsubset : S ⊆ C) :
    ∃ K : NNReal, ∀ i {u v : Fin n → ℝ}, u ∈ S → v ∈ S →
      |(fSeq i u).toReal - (fSeq i v).toReal| ≤ (K : ℝ) * dist u v := by
  let CE : Set (EuclideanSpace ℝ (Fin n)) :=
    ((fun zE : EuclideanSpace ℝ (Fin n) => (zE : Fin n → ℝ)) ⁻¹' C)
  let SE : Set (EuclideanSpace ℝ (Fin n)) :=
    ((fun zE : EuclideanSpace ℝ (Fin n) => (zE : Fin n → ℝ)) ⁻¹' S)
  let c : NNReal := (Fintype.card (Fin n) : NNReal) ^ (1 / (2 : ENNReal)).toReal
  let g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun i zE => (fSeq i (zE : Fin n → ℝ)).toReal
  have htoLpLip :
      LipschitzWith c
        (WithLp.toLp (2 : ENNReal) : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by
    simpa [c] using (PiLp.lipschitzWith_toLp (2 : ENNReal) (fun _ : Fin n => ℝ))
  rcases
      helperForTheorem_5_24_8_toRealConvexOn_and_pointwiseTendsto
        hCconv hf hf_finite fSeq hfSeq hfSeq_finite hpoint with
    ⟨_hCsubdom, _hCsubdomSeq, _htoRealConv, htoRealConvSeq, htoRealPoint⟩
  have hCopenE : IsOpen CE := by
    -- Transport the open set from `Fin n → ℝ` to `EuclideanSpace ℝ (Fin n)`.
    simpa [CE] using
      hCopen.preimage (EuclideanSpace.equiv (Fin n) ℝ).continuous
  have hCconvE : Convex ℝ CE := by
    -- Convexity is preserved under the Euclidean coordinate map.
    simpa [CE] using
      hCconv.linear_preimage
        (EuclideanSpace.equiv (Fin n) ℝ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ))
  have hgconv : ∀ i, ConvexOn ℝ CE (g i) := by
    intro i
    -- Compose each realified convex function with the Euclidean equivalence.
    have hconv :=
      (htoRealConvSeq i).comp_linearMap
        (EuclideanSpace.equiv (Fin n) ℝ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ))
    simpa [CE, g] using hconv
  have hgpointwise : Function.PointwiseBoundedOn g CE := by
    intro zE hzE
    -- Pointwise convergence at the fixed Euclidean point gives boundedness of the real range.
    have hz : (zE : Fin n → ℝ) ∈ C := by
      simpa [CE] using hzE
    exact
      helperForTheorem_5_24_8_boundedRange_of_tendsto_real
        (htoRealPoint (zE : Fin n → ℝ) hz)
  have hSclosedE : IsClosed SE := by
    -- Closedness also transports through the Euclidean coordinate map.
    simpa [SE] using
      hSclosed.preimage (EuclideanSpace.equiv (Fin n) ℝ).continuous
  have hSbddE : Bornology.IsBounded SE := by
    -- Boundedness is preserved because `WithLp.toLp 2` is globally Lipschitz.
    rcases hSbdd.subset_closedBall (0 : Fin n → ℝ) with ⟨R, hR⟩
    have hSEsubsetBall :
        SE ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ((c : ℝ) * max R 0) := by
      intro zE hzE
      have hzS : (zE : Fin n → ℝ) ∈ S := by
        simpa [SE] using hzE
      have hzR : dist (zE : Fin n → ℝ) 0 ≤ R := by
        simpa [Metric.mem_closedBall] using hR hzS
      have hzR' : dist (zE : Fin n → ℝ) 0 ≤ max R 0 :=
        le_trans hzR (le_max_left _ _)
      have hzEuclid :
          dist zE (0 : EuclideanSpace ℝ (Fin n)) ≤ (c : ℝ) * dist (zE : Fin n → ℝ) 0 := by
        simpa using htoLpLip.dist_le_mul (zE : Fin n → ℝ) 0
      have hzBall :
          dist zE (0 : EuclideanSpace ℝ (Fin n)) ≤ (c : ℝ) * max R 0 := by
        calc
          dist zE (0 : EuclideanSpace ℝ (Fin n)) ≤ (c : ℝ) * dist (zE : Fin n → ℝ) 0 := hzEuclid
          _ ≤ (c : ℝ) * max R 0 := by
            gcongr
      simpa [Metric.mem_closedBall] using hzBall
    exact
      (Metric.isBounded_closedBall :
        Bornology.IsBounded
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ((c : ℝ) * max R 0))).subset
        hSEsubsetBall
  have hSsubsetE : SE ⊆ CE := by
    intro zE hzE
    exact hSsubset (by simpa [SE] using hzE)
  rcases
      convexOn_family_uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_pointwiseBoundedOn
        hCopenE hCconvE g hgconv hgpointwise hSclosedE hSbddE hSsubsetE with
    ⟨_hubE, hLipE⟩
  rcases hLipE with ⟨K, hK⟩
  refine ⟨K * c, ?_⟩
  intro i u v hu hv
  have huE : WithLp.toLp (2 : ENNReal) u ∈ SE := by
    simpa [SE] using hu
  have hvE : WithLp.toLp (2 : ENNReal) v ∈ SE := by
    simpa [SE] using hv
  have hLip := LipschitzOnWith.norm_sub_le (hK i) huE hvE
  have htoLpDist :
      dist (WithLp.toLp (2 : ENNReal) u) (WithLp.toLp (2 : ENNReal) v) ≤
        (c : ℝ) * dist u v :=
    htoLpLip.dist_le_mul u v
  -- Pull the Euclidean Lipschitz estimate back to the original ambient type.
  calc
    |(fSeq i u).toReal - (fSeq i v).toReal| ≤
        (K : ℝ) * dist (WithLp.toLp (2 : ENNReal) u) (WithLp.toLp (2 : ENNReal) v) := by
          simpa [g, Real.norm_eq_abs] using hLip
    _ ≤ (K : ℝ) * ((c : ℝ) * dist u v) := by
      gcongr
    _ = ((K * c : NNReal) : ℝ) * dist u v := by
      simp [NNReal.coe_mul, mul_assoc]

/-- Helper for Theorem 5.24.8: equi-Lipschitz control on a closed bounded set upgrades pointwise
convergence at a fixed point to convergence along any sequence staying in that set. -/
lemma helperForTheorem_5_24_8_toReal_tendsto_at_movingPoints_of_equiLipschitz
    {n : ℕ} {C S : Set (Fin n → ℝ)} (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (fSeq : ℕ → (Fin n → ℝ) → EReal) (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal))
    (hpoint : ∀ z ∈ C, Filter.Tendsto (fun i => fSeq i z) Filter.atTop (nhds (f z)))
    (hSclosed : IsClosed S) (hSbdd : Bornology.IsBounded S) (hSsubset : S ⊆ C)
    {z : Fin n → ℝ} (hz : z ∈ S)
    (zSeq : ℕ → Fin n → ℝ)
    (hz_tendsto : Filter.Tendsto zSeq Filter.atTop (nhds z))
    (hzSeq_mem : ∀ᶠ i in Filter.atTop, zSeq i ∈ S) :
    Filter.Tendsto (fun i => (fSeq i (zSeq i)).toReal) Filter.atTop (nhds ((f z).toReal)) := by
  rcases
      helperForTheorem_5_24_8_toRealConvexOn_and_pointwiseTendsto
        hCconv hf hf_finite fSeq hfSeq hfSeq_finite hpoint with
    ⟨_hCsubdom, _hCsubdomSeq, _htoRealConv, _htoRealConvSeq, htoRealPoint⟩
  rcases
      helperForTheorem_5_24_8_realifiedFamily_equiLipschitz_on_closedBoundedSubset
        hCopen hCconv hf hf_finite fSeq hfSeq hfSeq_finite hpoint
        hSclosed hSbdd hSsubset with
    ⟨K, hK⟩
  have hzPoint :
      Filter.Tendsto (fun i => (fSeq i z).toReal) Filter.atTop (nhds ((f z).toReal)) :=
    htoRealPoint z (hSsubset hz)
  have hdistZero :
      Filter.Tendsto (fun i => dist (zSeq i) z) Filter.atTop (nhds 0) := by
    simpa using
      hz_tendsto.dist
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => z) Filter.atTop (nhds z))
  have hLipDistZero :
      Filter.Tendsto (fun i => (K : ℝ) * dist (zSeq i) z) Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul (K : ℝ) hdistZero
  have hzPointDiffZero :
      Filter.Tendsto (fun i => (fSeq i z).toReal - (f z).toReal) Filter.atTop (nhds 0) :=
    by
      simpa using
        hzPoint.sub
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => (f z).toReal) Filter.atTop (nhds ((f z).toReal)))
  have hzPointAbsZero :
      Filter.Tendsto (fun i => |(fSeq i z).toReal - (f z).toReal|) Filter.atTop (nhds 0) :=
    by
      simpa using hzPointDiffZero.abs
  have hbound :
      ∀ᶠ i in Filter.atTop,
        |(fSeq i (zSeq i)).toReal - (f z).toReal| ≤
          (K : ℝ) * dist (zSeq i) z + |(fSeq i z).toReal - (f z).toReal| := by
    filter_upwards [hzSeq_mem] with i hi
    have hLip := hK i hi hz
    -- Split the moving-point error into a spatial part and the fixed-point convergence error.
    calc
      |(fSeq i (zSeq i)).toReal - (f z).toReal| =
          |((fSeq i (zSeq i)).toReal - (fSeq i z).toReal) +
              ((fSeq i z).toReal - (f z).toReal)| := by ring_nf
      _ = ‖((fSeq i (zSeq i)).toReal - (fSeq i z).toReal) +
            ((fSeq i z).toReal - (f z).toReal)‖ := by
            simp [Real.norm_eq_abs]
      _ ≤ ‖(fSeq i (zSeq i)).toReal - (fSeq i z).toReal‖ +
            ‖(fSeq i z).toReal - (f z).toReal‖ := norm_add_le _ _
      _ = |(fSeq i (zSeq i)).toReal - (fSeq i z).toReal| +
            |(fSeq i z).toReal - (f z).toReal| := by
            simp [Real.norm_eq_abs]
      _ ≤ (K : ℝ) * dist (zSeq i) z + |(fSeq i z).toReal - (f z).toReal| := by
        gcongr
  have hmajorantZero :
      Filter.Tendsto
        (fun i => (K : ℝ) * dist (zSeq i) z + |(fSeq i z).toReal - (f z).toReal|)
        Filter.atTop (nhds 0) := by
    simpa using hLipDistZero.add hzPointAbsZero
  have hAbsZero :
      Filter.Tendsto (fun i => |(fSeq i (zSeq i)).toReal - (f z).toReal|) Filter.atTop (nhds 0) :=
    squeeze_zero'
      (Filter.Eventually.of_forall fun i => abs_nonneg _)
      hbound
      hmajorantZero
  -- Convergence in absolute value is exactly convergence to the target real number.
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using hAbsZero

/-- Helper for Theorem 5.24.8: the analytic heart of the proof is to show that every admissible
fixed positive step produces convergent real secant quotients along the moving points. -/
lemma helperForTheorem_5_24_8_fixedStepQuotient_tendsto
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (fSeq : ℕ → (Fin n → ℝ) → EReal) (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal))
    {x : Fin n → ℝ} (hx : x ∈ C) (xSeq : ℕ → Fin n → ℝ) (_hxSeq : ∀ i, xSeq i ∈ C)
    (hx_tendsto : Filter.Tendsto xSeq Filter.atTop (nhds x))
    (hpoint : ∀ z ∈ C, Filter.Tendsto (fun i => fSeq i z) Filter.atTop (nhds (f z)))
    {y : Fin n → ℝ} (ySeq : ℕ → Fin n → ℝ)
    (hy_tendsto : Filter.Tendsto ySeq Filter.atTop (nhds y))
    {t : ℝ} (_ht : 0 < t)
    (ht_mem : x + t • y ∈ C)
    (_hstep_mem : ∀ᶠ i in Filter.atTop, xSeq i + t • ySeq i ∈ C) :
    Filter.Tendsto
      (fun i =>
        (((fSeq i (xSeq i + t • ySeq i)).toReal - (fSeq i (xSeq i)).toReal) / t : ℝ))
      Filter.atTop (nhds (((f (x + t • y)).toReal - (f x).toReal) / t)) := by
  -- Route correction: instead of rebuilding a full local uniform-convergence theorem, it is
  -- enough to control the two moving values on one closed bounded set containing both tracks.
  rcases Metric.mem_nhds_iff.mp (hCopen.mem_nhds hx) with ⟨δx, hδx_pos, hδx_sub⟩
  rcases Metric.mem_nhds_iff.mp (hCopen.mem_nhds ht_mem) with ⟨δstep, hδstep_pos, hδstep_sub⟩
  let rx : ℝ := δx / 2
  let rstep : ℝ := δstep / 2
  let S : Set (Fin n → ℝ) := Metric.closedBall x rx ∪ Metric.closedBall (x + t • y) rstep
  have hrx_pos : 0 < rx := by
    dsimp [rx]
    linarith
  have hrstep_pos : 0 < rstep := by
    dsimp [rstep]
    linarith
  have hxBallSubset : Metric.closedBall x rx ⊆ C := by
    intro z hz
    apply hδx_sub
    have hzle : dist z x ≤ rx := by
      simpa [Metric.mem_closedBall] using hz
    have hzlt : dist z x < δx := by
      dsimp [rx] at hzle
      linarith
    simpa [Metric.mem_ball] using hzlt
  have hstepBallSubset : Metric.closedBall (x + t • y) rstep ⊆ C := by
    intro z hz
    apply hδstep_sub
    have hzle : dist z (x + t • y) ≤ rstep := by
      simpa [Metric.mem_closedBall] using hz
    have hzlt : dist z (x + t • y) < δstep := by
      dsimp [rstep] at hzle
      linarith
    simpa [Metric.mem_ball] using hzlt
  have hSclosed : IsClosed S := by
    -- A union of two closed balls is closed.
    dsimp [S]
    exact (isCompact_closedBall x rx).isClosed.union
      (isCompact_closedBall (x + t • y) rstep).isClosed
  have hSbdd : Bornology.IsBounded S := by
    -- The same union is bounded because each closed ball is bounded.
    dsimp [S]
    exact
      (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall x rx)).union
        (Metric.isBounded_closedBall :
          Bornology.IsBounded (Metric.closedBall (x + t • y) rstep))
  have hSsubset : S ⊆ C := by
    intro z hz
    rcases hz with hz | hz
    · exact hxBallSubset hz
    · exact hstepBallSubset hz
  have hx_mem_S : x ∈ S := by
    left
    rw [Metric.mem_closedBall]
    simpa [rx] using (le_of_lt hrx_pos : 0 ≤ rx)
  have hstepPoint_mem_S : x + t • y ∈ S := by
    right
    rw [Metric.mem_closedBall]
    simpa [rstep] using (le_of_lt hrstep_pos : 0 ≤ rstep)
  have hxSeq_mem_S : ∀ᶠ i in Filter.atTop, xSeq i ∈ S := by
    have hxSeq_mem_ball : ∀ᶠ i in Filter.atTop, xSeq i ∈ Metric.closedBall x rx :=
      hx_tendsto (Metric.closedBall_mem_nhds x hrx_pos)
    filter_upwards [hxSeq_mem_ball] with i hi
    exact Or.inl hi
  have hstep_tendsto :
      Filter.Tendsto (fun i => xSeq i + t • ySeq i) Filter.atTop (nhds (x + t • y)) := by
    -- The translated moving points converge to the translated limit point.
    simpa using hx_tendsto.add (hy_tendsto.const_smul t)
  have hstepSeq_mem_S : ∀ᶠ i in Filter.atTop, xSeq i + t • ySeq i ∈ S := by
    have hstep_mem_ball :
        ∀ᶠ i in Filter.atTop, xSeq i + t • ySeq i ∈ Metric.closedBall (x + t • y) rstep :=
      hstep_tendsto (Metric.closedBall_mem_nhds (x + t • y) hrstep_pos)
    filter_upwards [hstep_mem_ball] with i hi
    exact Or.inr hi
  have hxValue_tendsto :
      Filter.Tendsto (fun i => (fSeq i (xSeq i)).toReal) Filter.atTop (nhds ((f x).toReal)) := by
    -- Apply the moving-point lemma at the base point `x`.
    exact
      helperForTheorem_5_24_8_toReal_tendsto_at_movingPoints_of_equiLipschitz
        hCopen hCconv hf hf_finite fSeq hfSeq hfSeq_finite hpoint
        hSclosed hSbdd hSsubset hx_mem_S xSeq hx_tendsto hxSeq_mem_S
  have hstepValue_tendsto :
      Filter.Tendsto
        (fun i => (fSeq i (xSeq i + t • ySeq i)).toReal)
        Filter.atTop (nhds ((f (x + t • y)).toReal)) := by
    -- Apply the same moving-point lemma at the translated point `x + t • y`.
    exact
      helperForTheorem_5_24_8_toReal_tendsto_at_movingPoints_of_equiLipschitz
        hCopen hCconv hf hf_finite fSeq hfSeq hfSeq_finite hpoint
        hSclosed hSbdd hSsubset hstepPoint_mem_S
        (fun i => xSeq i + t • ySeq i) hstep_tendsto hstepSeq_mem_S
  have hnum_tendsto :
      Filter.Tendsto
        (fun i => (fSeq i (xSeq i + t • ySeq i)).toReal - (fSeq i (xSeq i)).toReal)
        Filter.atTop
        (nhds ((f (x + t • y)).toReal - (f x).toReal)) :=
    hstepValue_tendsto.sub hxValue_tendsto
  -- Divide the convergent numerator by the fixed positive step.
  simpa using hnum_tendsto.div_const t

/-- Helper for Theorem 5.24.8: every positive scale contains a smaller admissible step that keeps
the translated point inside the open set `C`. -/
lemma helperForTheorem_5_24_8_exists_small_step_mem_open
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCopen : IsOpen C)
    {x y : Fin n → ℝ} (hx : x ∈ C) {s : ℝ} (hs : 0 < s) :
    ∃ t : ℝ, 0 < t ∧ t ≤ s ∧ x + t • y ∈ C := by
  -- Follow the ray `r ↦ x + r • y`; continuity at `0` lets us choose a small positive time
  -- whose image stays inside the open neighborhood `C` of `x`.
  have hcont : Continuous fun r : ℝ => x + r • y := by
    fun_prop
  have hpre :
      {r : ℝ | x + r • y ∈ C} ∈ nhds (0 : ℝ) := by
    have hmap : Filter.Tendsto (fun r : ℝ => x + r • y) (nhds 0) (nhds x) := by
      simpa using (hcont.continuousAt : ContinuousAt (fun r : ℝ => x + r • y) 0).tendsto
    exact hmap (hCopen.mem_nhds hx)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδpos, hδsub⟩
  let t : ℝ := min s (δ / 2)
  have htpos : 0 < t := by
    dsimp [t]
    exact lt_min hs (by linarith)
  have htle : t ≤ s := by
    dsimp [t]
    exact min_le_left _ _
  have htball : t ∈ Metric.ball (0 : ℝ) δ := by
    have htlt : t < δ := by
      have hle : t ≤ δ / 2 := by
        dsimp [t]
        exact min_le_right _ _
      linarith
    rw [Metric.mem_ball]
    simpa [Real.dist_eq, abs_of_nonneg (le_of_lt htpos)] using htlt
  exact ⟨t, htpos, htle, hδsub htball⟩


end Section24
end Chap05
