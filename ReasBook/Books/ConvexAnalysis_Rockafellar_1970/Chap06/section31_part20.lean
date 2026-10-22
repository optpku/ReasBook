/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part19

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Tucker-style quadratic data for a partial-quadratic program over the nonnegative orthant. -/
structure QuadraticTuckerRepresentation (n : ℕ) (f : (Fin n → ℝ) → EReal) where
  auxDim : ℕ
  encode : (Fin n → ℝ) →ₗ[ℝ] (Fin auxDim → ℝ)
  rhs : Fin auxDim → ℝ
  quadraticPart : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)
  linearPart : Fin n → ℝ
  constantPart : ℝ
  representation :
    ∀ x : Fin n → ℝ,
      f x =
        if ∀ i : Fin auxDim, 0 ≤ encode x i + rhs i then
          ((((dotProduct x (quadraticPart x)) / 2 + dotProduct linearPart x + constantPart : ℝ)) :
            EReal)
        else
          (⊤ : EReal)

/-- The linear-programming application of Corollary 31.4.1, packaged with Tucker
representations of `f` and `f⋆`. -/
def LinearProgrammingDualityApplicationStatement {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  Nonempty (AffineTuckerRepresentation n f) ∧
    Nonempty (AffineTuckerRepresentation n (fenchelConjugate n f)) ∧
      NonnegativeOrthantFenchelApplicationStatement (n := n) f

/-- The quadratic-programming application of Corollary 31.4.1, packaged with Tucker
representations of `f` and `f⋆`. -/
def QuadraticProgrammingDualityApplicationStatement {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  Nonempty (QuadraticTuckerRepresentation n f) ∧
    Nonempty (QuadraticTuckerRepresentation n (fenchelConjugate n f)) ∧
      NonnegativeOrthantFenchelApplicationStatement (n := n) f

/-- A finite directed graph with `n` oriented edges, recorded by its tail and head maps. -/
structure FiniteDirectedGraph (n : ℕ) where
  vertexCount : ℕ
  tail : Fin n → Fin vertexCount
  head : Fin n → Fin vertexCount

/-- The signed incidence coefficient of an oriented edge at a vertex: `+1` at the head, `-1`
at the tail, and `0` elsewhere. -/
def directedGraphIncidenceCoeff {n : ℕ} (G : FiniteDirectedGraph n)
    (v : Fin G.vertexCount) (e : Fin n) : ℝ :=
  (if G.head e = v then (1 : ℝ) else 0) - (if G.tail e = v then (1 : ℝ) else 0)

/-- The incidence map sending an edge-flow to its signed vertex divergence. -/
noncomputable def directedGraphIncidenceMap {n : ℕ} (G : FiniteDirectedGraph n) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin G.vertexCount → ℝ) where
  toFun x v := ∑ e : Fin n, directedGraphIncidenceCoeff G v e * x e
  map_add' x y := by
    ext v
    simp [directedGraphIncidenceCoeff, mul_add, Finset.sum_add_distrib, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc]
  map_smul' a x := by
    ext v
    simp only [Pi.smul_apply]
    trans ∑ e : Fin n, a * (directedGraphIncidenceCoeff G v e * x e)
    · apply Finset.sum_congr rfl
      intro e he
      simp [smul_eq_mul]
      ring_nf
    · simpa [smul_eq_mul, mul_assoc] using
        (Finset.mul_sum (s := Finset.univ)
          (f := fun e : Fin n => directedGraphIncidenceCoeff G v e * x e) a).symm

/-- The cycle space of a finite directed graph, viewed as a subspace of edge-vectors. -/
noncomputable def directedGraphCycleSpace {n : ℕ} (G : FiniteDirectedGraph n) :
    Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (directedGraphIncidenceMap G)

/-- The tension space of a finite directed graph, identified with the orthogonal complement of its
cycle space in the sense used by Corollary 31.4.2. -/
def directedGraphTensionSpace {n : ℕ} (G : FiniteDirectedGraph n) : Set (Fin n → ℝ) :=
  {xStar | ∀ x ∈ (directedGraphCycleSpace G : Set (Fin n → ℝ)), dotProduct xStar x = 0}

/-- The graph specialization of Corollary 31.4.2: for a directed graph `G`, minimize `f` on the
cycle space of `G` and minimize `f⋆` on the corresponding tension space. -/
def GraphCycleTensionFenchelApplicationStatement {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (G : FiniteDirectedGraph n) : Prop :=
  let cycleSpace := directedGraphCycleSpace G
  let tensionSpace := directedGraphTensionSpace G
  let primal : EReal :=
    functionInfimumEReal (fun x => f x + indicatorFunction (cycleSpace : Set (Fin n → ℝ)) x)
  let dual : EReal :=
    functionInfimumEReal
      (fun xStar => fenchelConjugate n f xStar + indicatorFunction tensionSpace xStar)
  ((((∃ x : Fin n → ℝ,
          x ∈ (cycleSpace : Set (Fin n → ℝ)) ∧
            x ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) ∨
        ∃ xStar : Fin n → ℝ,
          xStar ∈ tensionSpace ∧
            xStar ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) →
      primal = -dual) ∧
    ((∃ x : Fin n → ℝ,
        x ∈ (cycleSpace : Set (Fin n → ℝ)) ∧
          x ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) →
      ∃ xStar : Fin n → ℝ,
        xStar ∈ tensionSpace ∧ dual = fenchelConjugate n f xStar) ∧
    ((∃ xStar : Fin n → ℝ,
        xStar ∈ tensionSpace ∧
          xStar ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) →
      ∃ x : Fin n → ℝ, x ∈ (cycleSpace : Set (Fin n → ℝ)) ∧ primal = f x))

-- Proof sketch: for 1., specialize Corollary 31.4.1 to partially affine and partially quadratic
-- convex functions, and package the resulting consequences using the existing
-- linear-/quadratic-programming application predicates together with chosen Tucker
-- representations of `f` and `f⋆`. For 2., specialize Corollary 31.4.2 to
-- `L := directedGraphCycleSpace G`; the corresponding orthogonal system is realized here by
-- `directedGraphTensionSpace G`, yielding the cycle/tension dual extremum problem.
/-- Remark 31.4.4 (Applications of Corollaries 31.4.1 and 31.4.2): 1. If `f` in
Corollary 31.4.1 is partially affine and both `f` and `f⋆` admit Tucker representations, then
one obtains the nonnegative-orthant Fenchel duality statement underlying the Gale-Kuhn-Tucker
duality theorem for linear programming; likewise, if `f` is partial quadratic and both `f` and
`f⋆` admit quadratic Tucker representations, one obtains the corresponding nonnegative-orthant
duality statement for quadratic programming. 2. For Corollary 31.4.2, the subspaces `L` and
`L⊥` encode dual linear systems; in particular, taking `L` to be the cycle space of a directed
graph and `directedGraphTensionSpace G` as the chosen realization of `L⊥` gives the dual
extremum problems of minimizing `f` on cycles and minimizing `f⋆` on tensions. -/
theorem fenchel_duality_corollaries_applications_to_programming_and_subspaces {n : ℕ}
    (f : (Fin n → ℝ) → EReal) :
    (IsPartialAffineConvexFunction n f →
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
      ClosedConvexFunction f →
      Nonempty (AffineTuckerRepresentation n f) →
      Nonempty (AffineTuckerRepresentation n (fenchelConjugate n f)) →
      LinearProgrammingDualityApplicationStatement (n := n) f) ∧
    (IsPartialQuadraticConvexFunction n f →
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
      ClosedConvexFunction f →
      Nonempty (QuadraticTuckerRepresentation n f) →
      Nonempty (QuadraticTuckerRepresentation n (fenchelConjugate n f)) →
      QuadraticProgrammingDualityApplicationStatement (n := n) f) ∧
    (∀ G : FiniteDirectedGraph n,
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
      ClosedConvexFunction f →
      SubspaceFenchelApplicationStatement (n := n) f (directedGraphCycleSpace G) ∧
        GraphCycleTensionFenchelApplicationStatement (n := n) f G) := by
  constructor
  · intro _hPartialAffine hproper hclosed hfTucker hfStarTucker
    refine ⟨hfTucker, hfStarTucker, ?_⟩
    simpa [NonnegativeOrthantFenchelApplicationStatement] using
      (fenchel_duality_nonnegative_orthant_corollary (n := n) f hproper hclosed)
  constructor
  · intro _hPartialQuadratic hproper hclosed hfTucker hfStarTucker
    refine ⟨hfTucker, hfStarTucker, ?_⟩
    simpa [NonnegativeOrthantFenchelApplicationStatement] using
      (fenchel_duality_nonnegative_orthant_corollary (n := n) f hproper hclosed)
  · intro G hproper hclosed
    have hSubspace :
        SubspaceFenchelApplicationStatement (n := n) f (directedGraphCycleSpace G) := by
      simpa [SubspaceFenchelApplicationStatement] using
        (fenchel_duality_subspace_corollary
          (n := n) f hproper hclosed (directedGraphCycleSpace G))
    refine ⟨hSubspace, ?_⟩
    dsimp [GraphCycleTensionFenchelApplicationStatement,
      SubspaceFenchelApplicationStatement, directedGraphTensionSpace] at hSubspace ⊢
    exact ⟨hSubspace.1, hSubspace.2.1, hSubspace.2.2.1⟩

end Section31
end Chap06
