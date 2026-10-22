/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part18

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Helper for Corollary 31.4.1: for coordinatewise nonnegative vectors, vanishing dot product
is equivalent to coordinatewise complementarity. -/
lemma helperForCorollary_31_4_1_zeroDot_iff_coordinatewiseComplementarity {n : ℕ}
    {x xStar : Fin n → ℝ}
    (hx : 0 ≤ x) (hxStar : 0 ≤ xStar) :
    dotProduct x xStar = 0 ↔ ∀ j : Fin n, x j * xStar j = 0 := by
  constructor
  · intro hdot j
    -- A sum of nonnegative coordinate products can vanish only when each term vanishes.
    have hterms_nonneg : ∀ i ∈ Finset.univ, 0 ≤ x i * xStar i := by
      intro i hi
      exact mul_nonneg (hx i) (hxStar i)
    have hzero_sum : ∑ i, x i * xStar i = 0 := by
      simpa [dotProduct] using hdot
    exact (Finset.sum_eq_zero_iff_of_nonneg hterms_nonneg).1 hzero_sum j (by simp)
  · intro hcoord
    -- Coordinatewise complementarity makes every summand in the dot product vanish.
    simpa [dotProduct, hcoord]

/-- Corollary 31.4.1: let `f` be a closed proper convex function on `ℝ^n`. If either (a) there
exists `x ∈ ri (dom f)` with `0 ≤ x`, or (b) there exists `xStar ∈ ri (dom f⋆)` with `0 ≤ xStar`,
then the infimum of `f` over the nonnegative orthant equals the negative of the infimum of `f⋆`
over the nonnegative orthant. Under (a) the dual infimum is attained, while under (b) the primal
infimum is attained. A pair `(x, xStar)` attains these infima with opposite values if and only if
`xStar ∈ ∂ f(x)`, `0 ≤ x`, `0 ≤ xStar`, and `x j * xStar j = 0` for every coordinate `j`. -/
theorem fenchel_duality_nonnegative_orthant_corollary {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f) :
    let K := ConvexCone.positive ℝ (Fin n → ℝ)
    let primal := conePrimalInfimum f K
    let dual := coneDualInfimum (n := n) f K
    (((∃ x : Fin n → ℝ,
          x ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
          0 ≤ x) ∨
        ∃ xStar : Fin n → ℝ,
          xStar ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ∧
          0 ≤ xStar) →
      primal = -dual) ∧
    ((∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
        0 ≤ x) →
      ∃ xStar : Fin n → ℝ, 0 ≤ xStar ∧ dual = fenchelConjugate n f xStar) ∧
    ((∃ xStar : Fin n → ℝ,
        xStar ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ∧
        0 ≤ xStar) →
      ∃ x : Fin n → ℝ, 0 ≤ x ∧ primal = f x) ∧
    (∀ x xStar : Fin n → ℝ,
      (f x = primal ∧
        primal = -dual ∧
        dual = fenchelConjugate n f xStar ∧
        0 ≤ x ∧
        0 ≤ xStar) ↔
          dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x ∧
            0 ≤ x ∧
            0 ≤ xStar ∧
            ∀ j : Fin n, x j * xStar j = 0) := by
  let K : ConvexCone ℝ (Fin n → ℝ) := ConvexCone.positive ℝ (Fin n → ℝ)
  let primal := conePrimalInfimum f K
  let dual := coneDualInfimum (n := n) f K
  -- Route correction: after repairing the local cone-dual sign convention, the positive cone
  -- becomes self-dual, so the textbook specialization of Theorem 31.4 now matches the target.
  have hK_nonempty : Set.Nonempty (K : Set (Fin n → ℝ)) := by
    -- The nonnegative orthant contains the zero vector.
    simpa [K, ConvexCone.positive] using (nonnegOrthant_closed_convex_nonempty (n := n)).1
  have hK_closed : IsClosed (K : Set (Fin n → ℝ)) := by
    -- The nonnegative orthant is closed in the Euclidean topology.
    simpa [K, ConvexCone.positive] using (nonnegOrthant_closed_convex_nonempty (n := n)).2.1
  have hCone :
      (ConeConstraintQualificationA (n := n) f K →
        primal = -dual ∧
          ∃ xStar : Fin n → ℝ, xStar ∈ coneDualFeasibleSet K ∧ dual = fenchelConjugate n f xStar) ∧
      (ConeConstraintQualificationB (n := n) f K →
        primal = -dual ∧
          ∃ x : Fin n → ℝ, x ∈ (K : Set (Fin n → ℝ)) ∧ primal = f x) ∧
      (IsPolyhedralConstraintCone (n := n) K →
        (ConeConstraintQualificationAWithPolyhedralCone (n := n) f K →
          primal = -dual ∧
            ∃ xStar : Fin n → ℝ,
              xStar ∈ coneDualFeasibleSet K ∧ dual = fenchelConjugate n f xStar) ∧
        (ConeConstraintQualificationBWithPolyhedralCone (n := n) f K →
          primal = -dual ∧
            ∃ x : Fin n → ℝ, x ∈ (K : Set (Fin n → ℝ)) ∧ primal = f x)) ∧
      (∀ x xStar : Fin n → ℝ,
        (x ∈ (K : Set (Fin n → ℝ)) ∧
          xStar ∈ coneDualFeasibleSet K ∧
          f x = primal ∧
          primal = -dual ∧
          dual = fenchelConjugate n f xStar) ↔
            dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x ∧
              x ∈ (K : Set (Fin n → ℝ)) ∧
              xStar ∈ coneDualFeasibleSet K ∧
              dotProduct x xStar = 0) := by
    simpa [K, primal, dual] using
      (cone_constrained_fenchel_duality_theorem
        (n := n) (f := f) hf hf_closed K hK_nonempty hK_closed)
  rcases hCone with ⟨hQualA, hQualB, hPoly, hOpt⟩
  have hK_poly : IsPolyhedralConstraintCone (n := n) K := by
    simpa [K] using helperForCorollary_31_4_1_positiveCone_polyhedral (n := n)
  have hPolyBranch := hPoly hK_poly
  rcases hPolyBranch with ⟨hQualA_poly, hQualB_poly⟩
  constructor
  · intro hEither
    rcases hEither with hA | hB
    · rcases hA with ⟨x, hxri, hxnonneg⟩
      -- Hypothesis (a) is exactly the polyhedral qualification `(a)` after rewriting `x ∈ K`.
      have hA' : ConeConstraintQualificationAWithPolyhedralCone (n := n) f K := by
        refine ⟨x, ?_⟩
        exact ⟨hxri, by simpa [K, ConvexCone.positive] using hxnonneg⟩
      exact (hQualA_poly hA').1
    · rcases hB with ⟨xStar, hxStar_ri, hxStar_nonneg⟩
      -- Hypothesis (b) becomes the polyhedral dual qualification using self-duality of `K`.
      have hB' : ConeConstraintQualificationBWithPolyhedralCone (n := n) f K := by
        refine ⟨xStar, ?_⟩
        exact ⟨hxStar_ri,
          (helperForCorollary_31_4_1_positiveCone_dualFeasible_iff_nonneg (n := n)).2
            hxStar_nonneg⟩
      exact (hQualB_poly hB').1
  constructor
  · intro hA
    -- Under hypothesis (a), Theorem 31.4 gives dual attainment on the self-dual positive cone.
    rcases hA with ⟨x, hxri, hxnonneg⟩
    have hA' : ConeConstraintQualificationAWithPolyhedralCone (n := n) f K := by
      refine ⟨x, ?_⟩
      exact ⟨hxri, by simpa [K, ConvexCone.positive] using hxnonneg⟩
    rcases (hQualA_poly hA').2 with ⟨xStar, hxStar_dual, hdual_eq⟩
    exact ⟨xStar,
      (helperForCorollary_31_4_1_positiveCone_dualFeasible_iff_nonneg (n := n)).1 hxStar_dual,
      hdual_eq⟩
  constructor
  · intro hB
    -- Under hypothesis (b), Theorem 31.4 gives primal attainment on the positive cone.
    rcases hB with ⟨xStar, hxStar_ri, hxStar_nonneg⟩
    have hB' : ConeConstraintQualificationBWithPolyhedralCone (n := n) f K := by
      refine ⟨xStar, ?_⟩
      exact ⟨hxStar_ri,
        (helperForCorollary_31_4_1_positiveCone_dualFeasible_iff_nonneg (n := n)).2
          hxStar_nonneg⟩
    rcases (hQualB_poly hB').2 with ⟨x, hxK, hprimal_eq⟩
    exact ⟨x, by simpa [K, ConvexCone.positive] using hxK, hprimal_eq⟩
  · intro x xStar
    constructor
    · rintro ⟨hfx, hprimal_dual, hdual_fxStar, hxnonneg, hxStar_nonneg⟩
      -- Feed the primal-dual optimality equalities into Theorem 31.4, then rewrite the
      -- complementarity scalar equation as coordinatewise complementarity.
      have hxK : x ∈ (K : Set (Fin n → ℝ)) := by
        simpa [K, ConvexCone.positive] using hxnonneg
      have hxStar_dual : xStar ∈ coneDualFeasibleSet K := by
        exact
          (helperForCorollary_31_4_1_positiveCone_dualFeasible_iff_nonneg (n := n)).2
            hxStar_nonneg
      have hOptData :
          x ∈ (K : Set (Fin n → ℝ)) ∧
            xStar ∈ coneDualFeasibleSet K ∧
            f x = primal ∧
            primal = -dual ∧
            dual = fenchelConjugate n f xStar := by
        exact ⟨hxK, hxStar_dual, hfx, hprimal_dual, hdual_fxStar⟩
      rcases (hOpt x xStar).1 hOptData with ⟨hsub, _, _, hdot⟩
      exact ⟨hsub, hxnonneg, hxStar_nonneg,
        (helperForCorollary_31_4_1_zeroDot_iff_coordinatewiseComplementarity
          (n := n) hxnonneg hxStar_nonneg).1 hdot⟩
    · rintro ⟨hsub, hxnonneg, hxStar_nonneg, hcoord⟩
      -- Coordinatewise complementarity reconstructs the zero dot-product condition in
      -- Theorem 31.4, and self-duality rewrites the cone constraints back to `0 ≤ x`, `0 ≤ xStar`.
      have hxK : x ∈ (K : Set (Fin n → ℝ)) := by
        simpa [K, ConvexCone.positive] using hxnonneg
      have hxStar_dual : xStar ∈ coneDualFeasibleSet K := by
        exact
          (helperForCorollary_31_4_1_positiveCone_dualFeasible_iff_nonneg (n := n)).2
            hxStar_nonneg
      have hdot :
          dotProduct x xStar = 0 := by
        exact
          (helperForCorollary_31_4_1_zeroDot_iff_coordinatewiseComplementarity
            (n := n) hxnonneg hxStar_nonneg).2 hcoord
      have hOptData :
          dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x ∧
            x ∈ (K : Set (Fin n → ℝ)) ∧
            xStar ∈ coneDualFeasibleSet K ∧
            dotProduct x xStar = 0 := by
        exact ⟨hsub, hxK, hxStar_dual, hdot⟩
      rcases (hOpt x xStar).2 hOptData with ⟨_, _, hfx, hprimal_dual, hdual_fxStar⟩
      exact ⟨hfx, hprimal_dual, hdual_fxStar, hxnonneg, hxStar_nonneg⟩

-- Proof sketch: specialize `Theorem 31.4` to the convex cone underlying the subspace `L`.
-- For a subspace, the cone is closed, contains `0`, and its dual feasible set is exactly the
-- orthogonal complement `L⊥ = {xStar | ∀ x ∈ L, ⟪xStar, x⟫ = 0}`. The cone-duality theorem then
-- yields the equality of the primal and dual infima under either qualification hypothesis, the
-- corresponding attainment statements, and the optimality criterion. The complementarity term
-- `⟪x, xStar⟫ = 0` becomes automatic from `x ∈ L` and `xStar ∈ L⊥`.
/-- Helper for Corollary 31.4.2: the cone-dual feasible set of a subspace cone is exactly the
orthogonal complement written in the textbook's set form. -/
lemma helperForCorollary_31_4_2_dualFeasible_iff_orthogonal {n : ℕ}
    (L : Submodule ℝ (Fin n → ℝ)) {xStar : Fin n → ℝ} :
    xStar ∈ coneDualFeasibleSet L.toConvexCone ↔
      xStar ∈ {xStar | ∀ x ∈ (L : Set (Fin n → ℝ)), dotProduct xStar x = 0} := by
  constructor
  · intro hxStar
    intro x hx
    -- Dual feasibility applied to `x` and `-x` forces the pairing to vanish.
    have hnonneg : 0 ≤ dotProduct x xStar := hxStar x (by simpa using hx)
    have hneg_nonneg : 0 ≤ dotProduct (-x) xStar := by
      exact hxStar (-x) (by simpa using L.neg_mem hx)
    have hnonpos : dotProduct x xStar ≤ 0 := by
      have : 0 ≤ -(dotProduct x xStar) := by
        simpa using hneg_nonneg
      linarith
    have hzero : dotProduct x xStar = 0 := le_antisymm hnonpos hnonneg
    simpa [dotProduct_comm] using hzero
  · intro hxStar
    intro x hx
    -- Orthogonality immediately gives the nonnegative inequality required by the dual cone.
    have hzero : dotProduct xStar x = 0 := hxStar x (by simpa using hx)
    simpa [dotProduct_comm, hzero]

/-- Helper for Corollary 31.4.2: a submodule has full Euclidean relative interior in itself. -/
lemma helperForCorollary_31_4_2_relativeInterior_submodule_eq_self {n : ℕ}
    (L : Submodule ℝ (Fin n → ℝ)) :
    euclideanRelativeInterior_fin n (L : Set (Fin n → ℝ)) = (L : Set (Fin n → ℝ)) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e : E ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let LE : Set E := e.symm '' (L : Set (Fin n → ℝ))
  have hLE :
      LE = ((L.comap e.toLinearMap : Submodule ℝ E) : Set E) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨e y, by simpa using hy, by simp⟩
  have hriLE : euclideanRelativeInterior n LE = LE := by
    -- Transport the submodule to Euclidean space and use the affine-subspace relative interior
    -- formula there.
    have hri' :
        euclideanRelativeInterior n ((L.comap e.toLinearMap : Submodule ℝ E) : Set E) =
          ((L.comap e.toLinearMap : Submodule ℝ E) : Set E) := by
      simpa using
        (euclideanRelativeInterior_affineSubspace_eq n
          ((L.comap e.toLinearMap).toAffineSubspace))
    rw [hLE]
    exact hri'
  ext x
  constructor
  · intro hx
    -- Membership in the transported relative interior collapses back to plain membership in `L`.
    have hx' :
        (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm x ∈ euclideanRelativeInterior n LE := by
      simpa [LE] using
        (mem_euclideanRelativeInterior_fin_iff (n := n) (C := (L : Set (Fin n → ℝ)))
          (x := x)).1 hx
    have hx'' : e.symm x ∈ LE := by
      simpa [hriLE] using hx'
    rcases hx'' with ⟨y, hy, hyx⟩
    have hxy : y = x := e.symm.injective hyx
    simpa [hxy] using hy
  · intro hx
    -- Conversely, every point of the submodule lies in its relative interior.
    refine (mem_euclideanRelativeInterior_fin_iff (n := n) (C := (L : Set (Fin n → ℝ)))
      (x := x)).2 ?_
    have hx' : e.symm x ∈ LE := by
      exact ⟨x, hx, by simp⟩
    have hx'' : e.symm x ∈ euclideanRelativeInterior n LE := by
      rwa [hriLE]
    simpa [LE] using hx''

/-- Helper for Corollary 31.4.2: the orthogonal complement also equals its own relative
interior. -/
lemma helperForCorollary_31_4_2_relativeInterior_orthogonal_eq_self {n : ℕ}
    (L : Submodule ℝ (Fin n → ℝ)) :
    euclideanRelativeInterior_fin n
        ({xStar | ∀ x ∈ (L : Set (Fin n → ℝ)), dotProduct xStar x = 0} : Set (Fin n → ℝ)) =
      ({xStar | ∀ x ∈ (L : Set (Fin n → ℝ)), dotProduct xStar x = 0} : Set (Fin n → ℝ)) := by
  -- Rewrite the textbook set as the existing submodule `orthogonalComplement n L`.
  simpa [orthogonalComplement] using
    helperForCorollary_31_4_2_relativeInterior_submodule_eq_self (n := n)
      (orthogonalComplement n L)

/-- Helper for Corollary 31.4.2: membership in the orthogonal complement forces the
complementarity pairing to vanish. -/
lemma helperForCorollary_31_4_2_dotProduct_eq_zero_of_mem_orthogonal {n : ℕ}
    (L : Submodule ℝ (Fin n → ℝ)) {x xStar : Fin n → ℝ}
    (hx : x ∈ (L : Set (Fin n → ℝ)))
    (hxStar : xStar ∈ {xStar | ∀ y ∈ (L : Set (Fin n → ℝ)), dotProduct xStar y = 0}) :
    dotProduct x xStar = 0 := by
  -- The theorem's orthogonality hypothesis already encodes the zero pairing.
  have hzero : dotProduct xStar x = 0 := hxStar x hx
  simpa [dotProduct_comm] using hzero

/-- Corollary 31.4.2: let `f` be a closed proper convex function on `ℝ^n`, and let `L` be a
subspace of `ℝ^n`. Then
`inf_{x ∈ L} f x = - inf_{xStar ∈ L⊥} f⋆ xStar` if either of the following conditions holds:
`(a)` `L ∩ ri (dom f) ≠ ∅`; `(b)` `L⊥ ∩ ri (dom f⋆) ≠ ∅`. Under `(a)` the infimum of `f⋆` on
`L⊥` is attained, while under `(b)` the infimum of `f` on `L` is attained. In general, a pair
`(x, xStar)` satisfies
`f x = inf_L f = - inf_{L⊥} f⋆ = -f⋆ xStar` if and only if `x ∈ L`, `xStar ∈ L⊥`, and
`xStar ∈ ∂ f(x)`. -/
theorem fenchel_duality_subspace_corollary {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (L : Submodule ℝ (Fin n → ℝ)) :
    let orthogonal : Set (Fin n → ℝ) :=
      {xStar | ∀ x ∈ (L : Set (Fin n → ℝ)), dotProduct xStar x = 0}
    let primal : EReal :=
      functionInfimumEReal (fun x => f x + indicatorFunction (L : Set (Fin n → ℝ)) x)
    let dual : EReal :=
      functionInfimumEReal
        (fun xStar => fenchelConjugate n f xStar + indicatorFunction orthogonal xStar)
    ((((∃ x : Fin n → ℝ,
            x ∈ (L : Set (Fin n → ℝ)) ∧
              x ∈ euclideanRelativeInterior_fin n
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) ∨
          ∃ xStar : Fin n → ℝ,
            xStar ∈ orthogonal ∧
              xStar ∈ euclideanRelativeInterior_fin n
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) →
        primal = -dual) ∧
      ((∃ x : Fin n → ℝ,
          x ∈ (L : Set (Fin n → ℝ)) ∧
            x ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) →
        ∃ xStar : Fin n → ℝ, xStar ∈ orthogonal ∧ dual = fenchelConjugate n f xStar) ∧
      ((∃ xStar : Fin n → ℝ,
          xStar ∈ orthogonal ∧
            xStar ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) →
        ∃ x : Fin n → ℝ, x ∈ (L : Set (Fin n → ℝ)) ∧ primal = f x) ∧
      (∀ x xStar : Fin n → ℝ,
        (x ∈ (L : Set (Fin n → ℝ)) ∧
          xStar ∈ orthogonal ∧
          f x = primal ∧
          primal = -dual ∧
          dual = fenchelConjugate n f xStar) ↔
            dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x ∧
              x ∈ (L : Set (Fin n → ℝ)) ∧
              xStar ∈ orthogonal)) := by
  let orthogonal : Set (Fin n → ℝ) :=
    {xStar | ∀ x ∈ (L : Set (Fin n → ℝ)), dotProduct xStar x = 0}
  let primal : EReal :=
    functionInfimumEReal (fun x => f x + indicatorFunction (L : Set (Fin n → ℝ)) x)
  let dual : EReal :=
    functionInfimumEReal
      (fun xStar => fenchelConjugate n f xStar + indicatorFunction orthogonal xStar)
  let K : ConvexCone ℝ (Fin n → ℝ) := L.toConvexCone
  have hK_nonempty : Set.Nonempty (K : Set (Fin n → ℝ)) := by
    -- The subspace cone contains the origin.
    refine ⟨0, ?_⟩
    simpa [K] using L.zero_mem
  have hK_closed : IsClosed (K : Set (Fin n → ℝ)) := by
    -- Every finite-dimensional submodule is closed.
    simpa [K] using Submodule.closed_of_finiteDimensional (s := L)
  have hCone :=
    cone_constrained_fenchel_duality_theorem
      (n := n) (f := f) hf hf_closed K hK_nonempty hK_closed
  have hOrth_eq : coneDualFeasibleSet K = orthogonal := by
    ext xStar
    simpa [orthogonal, K] using
      (helperForCorollary_31_4_2_dualFeasible_iff_orthogonal (n := n) (L := L) (xStar := xStar))
  have hKri_eq : euclideanRelativeInterior_fin n (K : Set (Fin n → ℝ)) = (L : Set (Fin n → ℝ)) := by
    simpa [K] using helperForCorollary_31_4_2_relativeInterior_submodule_eq_self (n := n) L
  have hOrthRi_eq : euclideanRelativeInterior_fin n (coneDualFeasibleSet K) = orthogonal := by
    rw [hOrth_eq]
    simpa [orthogonal] using
      helperForCorollary_31_4_2_relativeInterior_orthogonal_eq_self (n := n) L
  rcases hCone with ⟨hQualA, hQualB, _, hOpt⟩
  constructor
  · intro hEither
    rcases hEither with hA | hB
    · rcases hA with ⟨x, hxL, hxri⟩
      -- Hypothesis `(a)` becomes the cone qualification because `ri L = L`.
      have hxriK : x ∈ euclideanRelativeInterior_fin n (K : Set (Fin n → ℝ)) := by
        rw [hKri_eq]
        exact hxL
      have hA' : ConeConstraintQualificationA (n := n) f K := by
        exact ⟨x, hxri, hxriK⟩
      simpa [primal, dual, K, conePrimalInfimum, coneDualInfimum, hOrth_eq] using (hQualA hA').1
    · rcases hB with ⟨xStar, hxStarOrth, hxStarRi⟩
      -- Hypothesis `(b)` becomes the dual cone qualification because `ri L⊥ = L⊥`.
      have hxStarRiK : xStar ∈ euclideanRelativeInterior_fin n (coneDualFeasibleSet K) := by
        rw [hOrthRi_eq]
        exact hxStarOrth
      have hB' : ConeConstraintQualificationB (n := n) f K := by
        exact ⟨xStar, hxStarRi, hxStarRiK⟩
      simpa [primal, dual, K, conePrimalInfimum, coneDualInfimum, hOrth_eq] using (hQualB hB').1
  constructor
  · intro hA
    rcases hA with ⟨x, hxL, hxri⟩
    -- Reuse the same qualification rewrite to obtain dual attainment.
    have hxriK : x ∈ euclideanRelativeInterior_fin n (K : Set (Fin n → ℝ)) := by
      rw [hKri_eq]
      exact hxL
    have hA' : ConeConstraintQualificationA (n := n) f K := by
      exact ⟨x, hxri, hxriK⟩
    rcases (hQualA hA').2 with ⟨xStar, hxStarDual, hdual_eq⟩
    refine ⟨xStar, ?_, ?_⟩
    · have hxStarOrth' : xStar ∈ orthogonal := by
        rwa [← hOrth_eq]
      simpa [orthogonal] using hxStarOrth'
    · simpa [dual, K, coneDualInfimum, hOrth_eq] using hdual_eq
  constructor
  · intro hB
    rcases hB with ⟨xStar, hxStarOrth, hxStarRi⟩
    -- The dual qualification gives primal attainment after the same orthogonal rewrite.
    have hxStarRiK : xStar ∈ euclideanRelativeInterior_fin n (coneDualFeasibleSet K) := by
      rw [hOrthRi_eq]
      exact hxStarOrth
    have hB' : ConeConstraintQualificationB (n := n) f K := by
      exact ⟨xStar, hxStarRi, hxStarRiK⟩
    rcases (hQualB hB').2 with ⟨x, hxK, hprimal_eq⟩
    refine ⟨x, ?_, ?_⟩
    · simpa [K] using hxK
    · simpa [primal, K, conePrimalInfimum] using hprimal_eq
  · intro x xStar
    constructor
    · rintro ⟨hxL, hxStarOrth, hfx, hprimal_dual, hdual_fxStar⟩
      -- Rewrite the textbook constraints into the cone-duality theorem's hypotheses.
      have hxK : x ∈ (K : Set (Fin n → ℝ)) := by
        simpa [K] using hxL
      have hxStarDual : xStar ∈ coneDualFeasibleSet K := by
        rw [hOrth_eq]
        exact hxStarOrth
      have hOptData :
          x ∈ (K : Set (Fin n → ℝ)) ∧
            xStar ∈ coneDualFeasibleSet K ∧
            f x = conePrimalInfimum f K ∧
            conePrimalInfimum f K = -coneDualInfimum (n := n) f K ∧
            coneDualInfimum (n := n) f K = fenchelConjugate n f xStar := by
        refine ⟨hxK, hxStarDual, ?_, ?_, ?_⟩
        · simpa [primal, K, conePrimalInfimum] using hfx
        · simpa [primal, dual, K, conePrimalInfimum, coneDualInfimum, hOrth_eq] using hprimal_dual
        · simpa [dual, K, coneDualInfimum, hOrth_eq] using hdual_fxStar
      rcases (hOpt x xStar).1 hOptData with ⟨hsub, _, _, _⟩
      exact ⟨hsub, hxL, hxStarOrth⟩
    · rintro ⟨hsub, hxL, hxStarOrth⟩
      -- Conversely, orthogonality supplies the zero-pairing condition required by Theorem 31.4.
      have hxK : x ∈ (K : Set (Fin n → ℝ)) := by
        simpa [K] using hxL
      have hxStarDual : xStar ∈ coneDualFeasibleSet K := by
        rw [hOrth_eq]
        exact hxStarOrth
      have hdot : dotProduct x xStar = 0 :=
        helperForCorollary_31_4_2_dotProduct_eq_zero_of_mem_orthogonal
          (n := n) (L := L) hxL hxStarOrth
      have hOptData :
          dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x ∧
            x ∈ (K : Set (Fin n → ℝ)) ∧
            xStar ∈ coneDualFeasibleSet K ∧
            dotProduct x xStar = 0 := by
        exact ⟨hsub, hxK, hxStarDual, hdot⟩
      rcases (hOpt x xStar).2 hOptData with ⟨_, _, hfx, hprimal_dual, hdual_fxStar⟩
      refine ⟨hxL, hxStarOrth, ?_, ?_, ?_⟩
      · simpa [primal, K, conePrimalInfimum] using hfx
      · simpa [primal, dual, K, conePrimalInfimum, coneDualInfimum, hOrth_eq] using hprimal_dual
      · simpa [dual, K, coneDualInfimum, hOrth_eq] using hdual_fxStar

/-- The translated-and-tilted function `x ↦ h (z + x) - ⟪zStar, x⟫` used to derive the duality
between `h` and `h⋆` from the cone-constrained Fenchel duality theorem. -/
noncomputable def translatedTiltedFenchelFunction {n : ℕ}
    (h : (Fin n → ℝ) → EReal) (z zStar : Fin n → ℝ) : (Fin n → ℝ) → EReal :=
  fun x => h (z + x) - ((dotProduct zStar x : ℝ) : EReal)

-- Proof sketch: specialize the affine-change formula of Theorem 12.3 to the translation
-- `x ↦ z + x` and the linear tilt by `-⟪zStar, x⟫`. The conjugate then becomes the translate
-- `h⋆ (zStar + xStar)` together with the affine correction terms
-- `-⟪z, xStar⟫ - ⟪z, zStar⟫`.
/-- Remark 31.4.3: for given vectors `z` and `zStar`, define
`f(x) = h (z + x) - ⟪zStar, x⟫`. Then the conjugate of `f` is
`f⋆(xStar) = h⋆(zStar + xStar) - ⟪z, xStar⟫ - ⟪z, zStar⟫`. Applying
Theorem 31.4 and its corollaries to this translated-and-tilted function yields the usual duality
between `h` and `h⋆`; the book states that duality separately under the additional hypothesis
that both functions are finite everywhere. -/
theorem fenchelConjugate_translatedTiltedFunction {n : ℕ}
    (h : (Fin n → ℝ) → EReal) (z zStar : Fin n → ℝ) :
    fenchelConjugate n (translatedTiltedFenchelFunction h z zStar) =
      fun xStar =>
        fenchelConjugate n h (zStar + xStar) -
          ((dotProduct z xStar : ℝ) : EReal) -
          ((dotProduct z zStar : ℝ) : EReal) := by
  -- Rewrite the translated tilt into the affine-transform normal form used by Theorem 12.3.
  have hfun : translatedTiltedFenchelFunction h z zStar =
      (fun x => -((dotProduct zStar x : ℝ) : EReal) + h (z + x)) := by
    funext x
    simp [translatedTiltedFenchelFunction, sub_eq_add_neg, add_comm]
  rw [hfun]
  -- Apply the affine-change formula with identity linear part, translation by `-z`,
  -- and linear tilt `-⟪zStar, x⟫`.
  have hAffine :=
    (fenchelConjugate_affineTransform (n := n) (h := h)
      (A := LinearEquiv.refl ℝ (Fin n → ℝ))
      (AStar := LinearEquiv.refl ℝ (Fin n → ℝ))
      (hAStar := by
        intro x y
        simp)
      (a := -z) (aStar := -zStar) (α := 0))
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    dotProduct_comm, dotProduct_add, dotProduct_neg, EReal.coe_add, EReal.coe_neg] using
    hAffine

/-- Helper for Corollary 31.4.3: the co-finite hypothesis implies that the real-valued function
`h` is convex on all of `ℝ^n`. -/
lemma helperForCorollary_31_4_3_realConvexOfCofinite {n : ℕ}
    (h : (Fin n → ℝ) → ℝ)
    (h_cofinite : IsCofiniteFiniteConvexFunction h) :
    ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) h := by
  -- Convert convexity of the `EReal` lift into the usual real segment inequality.
  have hhConvE :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun x => (h x : EReal)) := by
    simpa [ConvexFunction] using h_cofinite.1.1
  refine (convexOn_iff_forall_pos).2 ?_
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb_lt_one : b < 1 := by
    linarith
  have hseg :=
    segment_inequality_real_of_ereal (f := h) (hf := hhConvE) x y b hb hb_lt_one
  have ha_eq : a = 1 - b := by
    linarith
  simpa [ha_eq, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hseg

/-- Helper for Corollary 31.4.3: the translated-and-tilted real objective
`x ↦ h (z + x) - ⟪zStar, x⟫` remains convex. -/
lemma helperForCorollary_31_4_3_translatedRealConvex {n : ℕ}
    (h : (Fin n → ℝ) → ℝ)
    (h_cofinite : IsCofiniteFiniteConvexFunction h) (z zStar : Fin n → ℝ) :
    ConvexOn ℝ (Set.univ : Set (Fin n → ℝ))
      (fun x => h (z + x) - dotProduct zStar x) := by
  have hhConv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) h :=
    helperForCorollary_31_4_3_realConvexOfCofinite h h_cofinite
  have hTranslate :
      ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fun x => h (z + x)) := by
    -- Translation preserves the convex-segment inequality after rewriting the midpoint.
    refine (convexOn_iff_forall_pos).2 ?_
    rcases (convexOn_iff_forall_pos).1 hhConv with ⟨_hhSet, hh⟩
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh' := hh (x := z + x) (by simp) (y := z + y) (by simp) ha hb hab
    have hrewrite : z + (a • x + b • y) = a • (z + x) + b • (z + y) := by
      ext i
      calc
        (z + (a • x + b • y)) i = z i + (a * x i + b * y i) := by
          simp [smul_eq_mul, add_assoc]
        _ = (a + b) * z i + (a * x i + b * y i) := by
          rw [hab, one_mul]
        _ = a * z i + a * x i + (b * z i + b * y i) := by
          ring
        _ = (a • (z + x) + b • (z + y)) i := by
          simp [smul_eq_mul, add_assoc]
    simpa [hrewrite, smul_eq_mul, add_assoc, add_left_comm, add_comm] using hh'
  have hLinear :
      ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fun x => -(dotProduct zStar x)) := by
    -- The negative linear functional is affine, hence convex.
    refine (convexOn_iff_forall_pos).2 ?_
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hrewrite :
        -(dotProduct zStar (a • x + b • y)) =
          a • (-(dotProduct zStar x)) + b • (-(dotProduct zStar y)) := by
      simp [dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring
    rw [hrewrite]
  simpa [sub_eq_add_neg] using hTranslate.add hLinear

/-- Helper for Corollary 31.4.3: the `EReal` lift of the translated-and-tilted real objective is
proper, closed convex, and finite everywhere. -/
lemma helperForCorollary_31_4_3_translatedLiftPackage {n : ℕ}
    (h : (Fin n → ℝ) → ℝ)
    (h_cofinite : IsCofiniteFiniteConvexFunction h) (z zStar : Fin n → ℝ) :
    let hE : (Fin n → ℝ) → EReal := fun x => (h x : EReal)
    let translated := translatedTiltedFenchelFunction hE z zStar
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) translated ∧
      ClosedConvexFunction translated ∧
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) translated = Set.univ := by
  intro hE translated
  have hconv :
      ConvexOn ℝ (Set.univ : Set (Fin n → ℝ))
        (fun x => h (z + x) - dotProduct zStar x) :=
    helperForCorollary_31_4_3_translatedRealConvex h h_cofinite z zStar
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) translated := by
    -- Package the finite convex real function as a proper `EReal`-valued function.
    simpa [hE, translated, translatedTiltedFenchelFunction] using
      helperForText_26_5_0_2_properLift
        (f := fun x => h (z + x) - dotProduct zStar x) hconv
  have hclosed : ClosedConvexFunction translated := by
    -- The same finite convexity gives closed convexity of the `EReal` lift.
    simpa [hE, translated, translatedTiltedFenchelFunction] using
      helperForText_26_5_0_2_closedLift
        (f := fun x => h (z + x) - dotProduct zStar x) hconv
  have hdom : effectiveDomain (Set.univ : Set (Fin n → ℝ)) translated = Set.univ := by
    ext x
    constructor
    · intro _hx
      simp
    · intro _hx
      -- Each translated value is still a finite real number, so it lies in the effective domain.
      have hltTop : translated x < (⊤ : EReal) := by
        simpa [hE, translated, translatedTiltedFenchelFunction, sub_eq_add_neg] using
          (EReal.add_lt_top (EReal.coe_ne_top _) (by simp) :
            hE (z + x) + (((-(dotProduct zStar x)) : ℝ) : EReal) < (⊤ : EReal))
      simpa [effectiveDomain_eq] using hltTop
  exact ⟨hproper, hclosed, hdom⟩

/-- Helper for Corollary 31.4.3: the dual-feasible set `K⋆` is convex because the defining
nonnegativity inequalities are preserved under convex combinations. -/
lemma helperForCorollary_31_4_3_dualFeasibleSet_convex {n : ℕ}
    (K : ConvexCone ℝ (Fin n → ℝ)) :
    Convex ℝ (coneDualFeasibleSet K) := by
  intro x hx y hy a b ha hb hab v hv
  -- Evaluate the defining inequalities on `v ∈ K` and combine them linearly.
  have hxv : 0 ≤ dotProduct v x := hx v hv
  have hyv : 0 ≤ dotProduct v y := hy v hv
  have hsum : 0 ≤ a * dotProduct v x + b * dotProduct v y := by
    exact add_nonneg (mul_nonneg ha hxv) (mul_nonneg hb hyv)
  simpa [dotProduct_add, dotProduct_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
    add_comm, add_left_comm, add_assoc] using hsum

/-- Helper for Corollary 31.4.3: the relative interior of the dual-feasible set is nonempty,
because `0 ∈ K⋆` and `K⋆` is convex. -/
lemma helperForCorollary_31_4_3_dualFeasibleSet_ri_nonempty {n : ℕ}
    (K : ConvexCone ℝ (Fin n → ℝ)) :
    (euclideanRelativeInterior_fin n (coneDualFeasibleSet K)).Nonempty := by
  have hconv : Convex ℝ (coneDualFeasibleSet K) :=
    helperForCorollary_31_4_3_dualFeasibleSet_convex K
  have hnonempty : Set.Nonempty (coneDualFeasibleSet K) := by
    -- The zero vector satisfies all dual-feasibility inequalities with equality.
    refine ⟨0, ?_⟩
    intro x hx
    simp
  exact
    helperForTheorem_21_1_riFin_nonempty_of_convex_nonempty
      (coneDualFeasibleSet K) hconv hnonempty

/-- Helper for Corollary 31.4.3: the dual infimum for the translated problem differs from the
textbook dual infimum exactly by the constant `⟪z, zStar⟫`. -/
lemma helperForCorollary_31_4_3_dualInfimum_shift {n : ℕ}
    (h : (Fin n → ℝ) → EReal) (K : ConvexCone ℝ (Fin n → ℝ)) (z zStar : Fin n → ℝ) :
    let translated := translatedTiltedFenchelFunction h z zStar
    let dual : EReal :=
      functionInfimumEReal
        (fun xStar =>
          (fenchelConjugate n h (zStar + xStar) - ((dotProduct z xStar : ℝ) : EReal)) +
            indicatorFunction (coneDualFeasibleSet K) xStar)
    coneDualInfimum translated K + ((dotProduct z zStar : ℝ) : EReal) = dual := by
  intro translated dual
  unfold coneDualInfimum functionInfimumEReal
  rw [fenchelConjugate_translatedTiltedFunction (n := n) (h := h) (z := z) (zStar := zStar)]
  -- Pull the constant `-⟪z, zStar⟫` out of the infimum.
  have hsplit :
      (⨅ xStar : Fin n → ℝ,
          (fenchelConjugate n h (zStar + xStar) - ((dotProduct z xStar : ℝ) : EReal) -
              ((dotProduct z zStar : ℝ) : EReal)) +
            indicatorFunction (coneDualFeasibleSet K) xStar) =
        (⨅ xStar : Fin n → ℝ,
          ((fenchelConjugate n h (zStar + xStar) - ((dotProduct z xStar : ℝ) : EReal)) +
            indicatorFunction (coneDualFeasibleSet K) xStar) +
            (((-(dotProduct z zStar)) : ℝ) : EReal)) := by
    refine iInf_congr ?_
    intro xStar
    simp [sub_eq_add_neg, add_left_comm, add_comm]
  rw [hsplit, helperForTheorem_6_30_22_iInf_add_realConst
    (G := fun xStar : Fin n → ℝ =>
      (fenchelConjugate n h (zStar + xStar) - ((dotProduct z xStar : ℝ) : EReal)) +
        indicatorFunction (coneDualFeasibleSet K) xStar)
    (c := -(dotProduct z zStar))]
  -- Add the constant back on the right to recover the textbook dual quantity.
  have hcancel :=
    EReal.sub_add_cancel
      (a := (⨅ xStar : Fin n → ℝ,
        (fenchelConjugate n h (zStar + xStar) - ((dotProduct z xStar : ℝ) : EReal)) +
          indicatorFunction (coneDualFeasibleSet K) xStar))
      (b := dotProduct z zStar)
  simpa [dual, functionInfimumEReal, sub_eq_add_neg, add_assoc] using hcancel

-- Proof sketch: apply `Theorem 31.4` to the translated-and-tilted function
-- `x ↦ h (z + x) - ⟪zStar, x⟫`. The preceding conjugacy formula rewrites the dual objective as
-- `xStar ↦ h⋆ (zStar + xStar) - ⟪z, xStar⟫ - ⟪z, zStar⟫`, so moving the constant
-- `⟪z, zStar⟫` to the other side yields the displayed identity. Co-finiteness of the
-- real-valued convex function `h` supplies the whole-space finiteness needed to conclude that
-- both infima are finite, and the attainment clauses come from the primal/dual attainment part
-- of `Theorem 31.4`.
/-- Corollary 31.4.3: let `h` be a finite co-finite convex function on `ℝ^n`, let `K` be a
nonempty closed convex cone, and let `Kᵒ`, represented here by `coneDualFeasibleSet K`.
Then for every `z, zStar ∈ ℝ^n`,
`inf_{x ∈ K} (h (z + x) - ⟪zStar, x⟫) + inf_{xStar ∈ K⋆} (h⋆ (zStar + xStar) - ⟪z, xStar⟫)
= ⟪z, zStar⟫`; moreover both infima are finite and are attained. -/
theorem translated_tilted_cone_fenchel_duality_corollary {n : ℕ}
    (h : (Fin n → ℝ) → ℝ)
    (h_cofinite : IsCofiniteFiniteConvexFunction h)
    (K : ConvexCone ℝ (Fin n → ℝ))
    (hK_nonempty : Set.Nonempty (K : Set (Fin n → ℝ)))
    (hK_closed : IsClosed (K : Set (Fin n → ℝ)))
    (z zStar : Fin n → ℝ) :
    let hE : (Fin n → ℝ) → EReal := fun x => (h x : EReal)
    let translated := translatedTiltedFenchelFunction hE z zStar
    let primal := conePrimalInfimum translated K
    let dual : EReal :=
      functionInfimumEReal
        (fun xStar =>
          (fenchelConjugate n hE (zStar + xStar) -
              ((dotProduct z xStar : ℝ) : EReal)) +
            indicatorFunction (coneDualFeasibleSet K) xStar)
    (primal + dual = ((dotProduct z zStar : ℝ) : EReal)) ∧
      primal ≠ (⊤ : EReal) ∧
      primal ≠ (⊥ : EReal) ∧
      dual ≠ (⊤ : EReal) ∧
      dual ≠ (⊥ : EReal) ∧
      (∃ x : Fin n → ℝ,
        x ∈ (K : Set (Fin n → ℝ)) ∧
          primal = translated x) ∧
      ∃ xStar : Fin n → ℝ,
        xStar ∈ coneDualFeasibleSet K ∧
          dual =
            fenchelConjugate n hE (zStar + xStar) -
              ((dotProduct z xStar : ℝ) : EReal) := by
  intro hE translated primal dual
  let dual0 : EReal := coneDualInfimum translated K
  -- First recover the whole-space convexity and co-finiteness data attached to `h`.
  have hhConv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) h :=
    helperForCorollary_31_4_3_realConvexOfCofinite h h_cofinite
  have hcofiniteData :=
    (isCofiniteFiniteConvexFunction_iff_fenchelConjugate_finiteEverywhere
      (f := h) hhConv).1 h_cofinite
  -- Then package the translated objective for Theorem 31.4.
  rcases helperForCorollary_31_4_3_translatedLiftPackage
      (h := h) h_cofinite z zStar with
    ⟨hTranslatedProper, hTranslatedClosed, hTranslatedDom⟩
  have hri_univ : euclideanRelativeInterior_fin n (Set.univ : Set (Fin n → ℝ)) = Set.univ := by
    simpa using
      (helperForCorollary_31_4_2_relativeInterior_submodule_eq_self (n := n)
        (⊤ : Submodule ℝ (Fin n → ℝ)))
  -- Qualification `(a)` comes from `ri K ≠ ∅`, since the translated domain is all of `ℝ^n`.
  have hKri_nonempty :
      (euclideanRelativeInterior_fin n (K : Set (Fin n → ℝ))).Nonempty := by
    exact
      helperForTheorem_21_1_riFin_nonempty_of_convex_nonempty
        (K : Set (Fin n → ℝ)) K.convex hK_nonempty
  rcases hKri_nonempty with ⟨xK, hxKri⟩
  have hxKDomRi :
      xK ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) translated) := by
    rw [hTranslatedDom, hri_univ]
    simp
  have hQualA : ConeConstraintQualificationA (n := n) translated K := by
    exact ⟨xK, hxKDomRi, hxKri⟩
  -- Qualification `(b)` uses that the conjugate domain of the translated function is also all
  -- of `ℝ^n`, so any point of `ri K⋆` works.
  have hTranslatedConjDom :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n translated) = Set.univ := by
    ext xStar
    constructor
    · intro _hx
      simp
    · intro _hx
      have hOrigMem :
          zStar + xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n hE) := by
        rw [hcofiniteData.1]
        simp
      have hOrigLtTop : fenchelConjugate n hE (zStar + xStar) < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using hOrigMem
      have hShiftLtTop :
          fenchelConjugate n hE (zStar + xStar) - ((dotProduct z xStar : ℝ) : EReal) <
            (⊤ : EReal) := by
        rw [sub_eq_add_neg]
        exact EReal.add_lt_top (ne_of_lt hOrigLtTop) (by simp)
      have hconj :
          fenchelConjugate n translated xStar =
            fenchelConjugate n hE (zStar + xStar) -
              ((dotProduct z xStar : ℝ) : EReal) -
              ((dotProduct z zStar : ℝ) : EReal) := by
        simpa using
          congrArg (fun f : (Fin n → ℝ) → EReal => f xStar)
            (fenchelConjugate_translatedTiltedFunction (n := n) (h := hE) z zStar)
      have hTranslatedLtTop : fenchelConjugate n translated xStar < (⊤ : EReal) := by
        rw [hconj]
        simpa [sub_eq_add_neg, add_assoc] using
          (EReal.add_lt_top (ne_of_lt hShiftLtTop) (by simp) :
            (fenchelConjugate n hE (zStar + xStar) -
                ((dotProduct z xStar : ℝ) : EReal)) +
              (((-(dotProduct z zStar)) : ℝ) : EReal) < (⊤ : EReal))
      simpa [effectiveDomain_eq] using hTranslatedLtTop
  have hDualRi_nonempty :
      (euclideanRelativeInterior_fin n (coneDualFeasibleSet K)).Nonempty :=
    helperForCorollary_31_4_3_dualFeasibleSet_ri_nonempty K
  rcases hDualRi_nonempty with ⟨xStarK, hxStarKri⟩
  have hxStarKDomRi :
      xStarK ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n translated)) := by
    rw [hTranslatedConjDom, hri_univ]
    simp
  have hQualB : ConeConstraintQualificationB (n := n) translated K := by
    exact ⟨xStarK, hxStarKDomRi, hxStarKri⟩
  -- Apply Theorem 31.4 to the translated problem and extract primal/dual attainment.
  have hCone :=
    cone_constrained_fenchel_duality_theorem (n := n) (f := translated)
      hTranslatedProper hTranslatedClosed K hK_nonempty hK_closed
  rcases hCone with ⟨hQualATheorem, hQualBTheorem, _, _⟩
  rcases hQualATheorem hQualA with ⟨hprimal_eq_negDual0_raw, xStar0, hxStar0Dual, hdual0_eq_raw⟩
  rcases hQualBTheorem hQualB with ⟨_hEqAgainRaw, x0, hx0K, hprimal_at_raw⟩
  have hprimal_eq_negDual0 : primal = -dual0 := by
    simpa [primal, dual0] using hprimal_eq_negDual0_raw
  have hdual0_eq : dual0 = fenchelConjugate n translated xStar0 := by
    simpa [dual0] using hdual0_eq_raw
  have hprimal_at : primal = translated x0 := by
    simpa [primal] using hprimal_at_raw
  have hDualShift : dual0 + ((dotProduct z zStar : ℝ) : EReal) = dual := by
    simpa [dual0, hE, translated, dual] using
      helperForCorollary_31_4_3_dualInfimum_shift (n := n) (h := hE) K z zStar
  -- The attained primal value is a genuine real number, so it is finite.
  have hprimal_value : primal = ((h (z + x0) - dotProduct zStar x0 : ℝ) : EReal) := by
    simpa [translated, translatedTiltedFenchelFunction] using hprimal_at
  have hprimal_finite : ∃ r : ℝ, primal = (r : EReal) := by
    exact ⟨h (z + x0) - dotProduct zStar x0, hprimal_value⟩
  have hprimal_ne_top : primal ≠ (⊤ : EReal) := by
    rcases hprimal_finite with ⟨r, hr⟩
    rw [hr]
    simp
  have hprimal_ne_bot : primal ≠ (⊥ : EReal) := by
    rcases hprimal_finite with ⟨r, hr⟩
    rw [hr]
    simp
  -- Therefore the translated dual value `dual0` is finite as well.
  have hdual0_ne_top : dual0 ≠ (⊤ : EReal) := by
    intro htop
    have hbot : primal = (⊥ : EReal) := by
      rw [hprimal_eq_negDual0, htop]
      simp
    exact hprimal_ne_bot hbot
  have hdual0_ne_bot : dual0 ≠ (⊥ : EReal) := by
    intro hbot
    have htop : primal = (⊤ : EReal) := by
      rw [hprimal_eq_negDual0, hbot]
      simp
    exact hprimal_ne_top htop
  let r0 : ℝ := dual0.toReal
  have hdual0_real : dual0 = ((r0 : ℝ) : EReal) := by
    simpa [r0] using (EReal.coe_toReal (x := dual0) hdual0_ne_top hdual0_ne_bot).symm
  have hprimal_real : primal = (((-r0 : ℝ)) : EReal) := by
    calc
      primal = -dual0 := hprimal_eq_negDual0
      _ = (((-r0 : ℝ)) : EReal) := by
        rw [hdual0_real]
        simp [r0]
  have hdual_real : dual = (((r0 + dotProduct z zStar : ℝ)) : EReal) := by
    rw [← hDualShift, hdual0_real]
    simp [r0, EReal.coe_add]
  have hdual_finite : ∃ r : ℝ, dual = (r : EReal) := by
    exact ⟨r0 + dotProduct z zStar, hdual_real⟩
  -- Now the textbook identity is just arithmetic on real coercions.
  have hsum : primal + dual = ((dotProduct z zStar : ℝ) : EReal) := by
    rw [hprimal_real, hdual_real]
    have hcancel : -((r0 : ℝ) : EReal) + ((r0 : ℝ) : EReal) = (0 : EReal) := by
      simpa [sub_eq_add_neg] using (EReal.sub_add_cancel (a := (0 : EReal)) (b := r0))
    simpa [EReal.coe_add, add_assoc] using
      congrArg (fun t : EReal => t + ((dotProduct z zStar : ℝ) : EReal)) hcancel
  -- Finally rewrite the attained translated dual value back into the textbook dual objective.
  have hdual_attained :
      dual = fenchelConjugate n hE (zStar + xStar0) - ((dotProduct z xStar0 : ℝ) : EReal) := by
    calc
      dual = dual0 + ((dotProduct z zStar : ℝ) : EReal) := hDualShift.symm
      _ = fenchelConjugate n translated xStar0 + ((dotProduct z zStar : ℝ) : EReal) := by
        rw [hdual0_eq]
      _ = fenchelConjugate n hE (zStar + xStar0) - ((dotProduct z xStar0 : ℝ) : EReal) := by
        have hconj0 :
            fenchelConjugate n translated xStar0 =
              fenchelConjugate n hE (zStar + xStar0) -
                ((dotProduct z xStar0 : ℝ) : EReal) -
                ((dotProduct z zStar : ℝ) : EReal) := by
          simpa using
            congrArg (fun f : (Fin n → ℝ) → EReal => f xStar0)
              (fenchelConjugate_translatedTiltedFunction (n := n) (h := hE) z zStar)
        rw [hconj0]
        have hcancel :=
          EReal.sub_add_cancel
            (a := fenchelConjugate n hE (zStar + xStar0) - ((dotProduct z xStar0 : ℝ) : EReal))
            (b := dotProduct z zStar)
        simpa [sub_eq_add_neg, add_assoc] using hcancel
  refine ⟨hsum, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprimal_real]
    simp
  · rw [hprimal_real]
    simp
  · rcases hdual_finite with ⟨r, hr⟩
    rw [hr]
    simp
  · rcases hdual_finite with ⟨r, hr⟩
    rw [hr]
    simp
  · exact ⟨x0, hx0K, hprimal_at⟩
  · exact ⟨xStar0, hxStar0Dual, hdual_attained⟩

/-- A partial affine convex function in the book's sense: it agrees with an affine function on an
affine set and is `⊤` outside that affine set. -/
def IsPartialAffineConvexFunction (n : ℕ) (f : (Fin n → ℝ) → EReal) : Prop :=
  ∃ (S : AffineSubspace ℝ (Fin n → ℝ)) (g : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
    (∀ x ∈ (S : Set (Fin n → ℝ)), f x = (g x : EReal)) ∧
      ∀ x ∉ (S : Set (Fin n → ℝ)), f x = (⊤ : EReal)

/-- The full nonnegative-orthant duality statement appearing in Corollary 31.4.1. -/
def NonnegativeOrthantFenchelApplicationStatement {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  let K := ConvexCone.positive ℝ (Fin n → ℝ)
  let primal := conePrimalInfimum f K
  let dual := coneDualInfimum (n := n) f K
  (((∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
        0 ≤ x) ∨
      ∃ xStar : Fin n → ℝ,
        xStar ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ∧
        0 ≤ xStar) →
    primal = -dual) ∧
  ((∃ x : Fin n → ℝ,
      x ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
      0 ≤ x) →
    ∃ xStar : Fin n → ℝ, 0 ≤ xStar ∧ dual = fenchelConjugate n f xStar) ∧
  ((∃ xStar : Fin n → ℝ,
      xStar ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ∧
      0 ≤ xStar) →
    ∃ x : Fin n → ℝ, 0 ≤ x ∧ primal = f x) ∧
  (∀ x xStar : Fin n → ℝ,
    (f x = primal ∧
      primal = -dual ∧
      dual = fenchelConjugate n f xStar ∧
      0 ≤ x ∧
      0 ≤ xStar) ↔
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x ∧
          0 ≤ x ∧
          0 ≤ xStar ∧
          ∀ j : Fin n, x j * xStar j = 0)

/-- The full subspace duality statement appearing in Corollary 31.4.2. -/
def SubspaceFenchelApplicationStatement {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (L : Submodule ℝ (Fin n → ℝ)) : Prop :=
  let orthogonal : Set (Fin n → ℝ) :=
    {xStar | ∀ x ∈ (L : Set (Fin n → ℝ)), dotProduct xStar x = 0}
  let primal : EReal :=
    functionInfimumEReal (fun x => f x + indicatorFunction (L : Set (Fin n → ℝ)) x)
  let dual : EReal :=
    functionInfimumEReal
      (fun xStar => fenchelConjugate n f xStar + indicatorFunction orthogonal xStar)
  ((((∃ x : Fin n → ℝ,
          x ∈ (L : Set (Fin n → ℝ)) ∧
            x ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) ∨
        ∃ xStar : Fin n → ℝ,
          xStar ∈ orthogonal ∧
            xStar ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) →
      primal = -dual) ∧
    ((∃ x : Fin n → ℝ,
        x ∈ (L : Set (Fin n → ℝ)) ∧
          x ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) →
      ∃ xStar : Fin n → ℝ, xStar ∈ orthogonal ∧ dual = fenchelConjugate n f xStar) ∧
    ((∃ xStar : Fin n → ℝ,
        xStar ∈ orthogonal ∧
          xStar ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) →
      ∃ x : Fin n → ℝ, x ∈ (L : Set (Fin n → ℝ)) ∧ primal = f x) ∧
    (∀ x xStar : Fin n → ℝ,
      (x ∈ (L : Set (Fin n → ℝ)) ∧
        xStar ∈ orthogonal ∧
        f x = primal ∧
        primal = -dual ∧
        dual = fenchelConjugate n f xStar) ↔
          dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x ∧
            x ∈ (L : Set (Fin n → ℝ)) ∧
            xStar ∈ orthogonal))

/-- Tucker-style affine data for a partial-affine program over the nonnegative orthant. -/
structure AffineTuckerRepresentation (n : ℕ) (f : (Fin n → ℝ) → EReal) where
  auxDim : ℕ
  encode : (Fin n → ℝ) →ₗ[ℝ] (Fin auxDim → ℝ)
  rhs : Fin auxDim → ℝ
  objective : (Fin n → ℝ) →ᵃ[ℝ] ℝ
  representation :
    ∀ x : Fin n → ℝ,
      f x =
        if ∀ i : Fin auxDim, 0 ≤ encode x i + rhs i then
          ((objective x : ℝ) : EReal)
        else
          (⊤ : EReal)
end Section31
end Chap06
