/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part16

section Chap07
section Section33

attribute [local instance] Classical.propDecidable

/-- Definition33.0.27: The conjugate conventions used below are the existing
`convexConjugate` and `concaveConjugate` operations. A concave function `ψ : ℝ^n → EReal`
is closed concave when it equals its concave biconjugate `ψ = ψ_{**}`; equivalently, its
hypograph is closed. This predicate records the biconjugate formulation. -/
def IsFunctionClosedConcave {n : ℕ}
    (ψ : (Fin n → ℝ) → EReal) : Prop :=
  ψ = concaveConjugate (concaveConjugate ψ)

/-- Definition33.0.28: For a convex bifunction `F : ℝ^m → (ℝ^n → EReal)`, meaning that its
graph function `f (u, x) = (F u) x` is convex on `ℝ^(m + n)` as expressed by
`IsGraphConvexBifunction F`, the genuine adjoint `F^* : ℝ^n → (ℝ^m → EReal)` is defined by
`(F^* x^*)(u^*) = inf_{u, x} ((F u) x - ⟪x, x^*⟫ + ⟪u, u^*⟫)`.
The first pairing `⟪F u, x^*⟫ = sup_x (⟪x, x^*⟫ - (F u) x)` is the existing
`convexBifunctionPairing F u xStar`, and the second pairing `⟪u, F^* x^*⟫` is defined
separately below by `genuineConvexBifunctionAdjointPairing`. -/
noncomputable def genuineConvexBifunctionAdjoint {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun xStar uStar =>
    sInf <| Set.range fun ux : (Fin m → ℝ) × (Fin n → ℝ) =>
      (F ux.1 ux.2 - ((dotProduct ux.2 xStar : ℝ) : EReal)) +
        ((dotProduct ux.1 uStar : ℝ) : EReal)

/-- The adjoint-side pairing attached to the genuine bifunction adjoint of a convex
bifunction, defined by
`⟪u, F^* x^*⟫ = inf_{u^*} (⟪u, u^*⟫ - (F^* x^*)(u^*))`. -/
noncomputable def genuineConvexBifunctionAdjointPairing {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) : EReal :=
  sInf <| Set.range fun uStar : Fin m → ℝ =>
    ((dotProduct u uStar : ℝ) : EReal) - genuineConvexBifunctionAdjoint F xStar uStar

/-- Definition33.0.29: For a convex bifunction `F`, `dom F` is the set of parameters `u`
such that the section `F u` is not identically `+∞`, and `dom F^*` is the set of dual
vectors `x^*` such that the genuine adjoint section `F^* x^*` from
Definition33.0.28 is not identically `-∞`. This packages the pair `(dom F, dom F^*)`. -/
def convexBifunctionDomains {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    Set (Fin m → ℝ) × Set (Fin n → ℝ) :=
  (convexBifunctionParameterDomain F,
    {xStar | ∃ uStar : Fin m → ℝ, genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥})

/-- The concave indicator of a point in `ℝ^n`, taking the value `0` at that point and `⊥`
elsewhere. -/
noncomputable def concavePointIndicator {n : ℕ} (x : Fin n → ℝ) : (Fin n → ℝ) → EReal :=
  fun z => if z = x then 0 else ⊥

/-- The indicator bifunction attached to a linear map has a convex graph function. -/
-- Proof sketch: the graph of `u ↦ δ_{A u}` is the indicator of the linear subspace
-- `{(u, x) | x = A u}` in `ℝ^(m+n)`, and indicators of affine subspaces are convex.
theorem pointIndicator_linearMap_isGraphConvexBifunction
    {m n : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    IsGraphConvexBifunction (fun u => pointIndicator (A u)) := by
  let graphSet : Set (Fin (m + n) → ℝ) :=
    {z | (fun j => z (Fin.natAdd m j)) = A (fun i => z (Fin.castAdd n i))}
  -- The graph set is convex because the relation `x = A u` is preserved by convex
  -- combinations.
  have hGraphSetConvex : Convex ℝ graphSet := by
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    change
      (fun j => (a • z₁ + b • z₂) (Fin.natAdd m j)) =
        A (fun i => (a • z₁ + b • z₂) (Fin.castAdd n i))
    have hz₁j :
        ∀ j, z₁ (Fin.natAdd m j) = (A (fun i => z₁ (Fin.castAdd n i))) j :=
      congrFun hz₁
    have hz₂j :
        ∀ j, z₂ (Fin.natAdd m j) = (A (fun i => z₂ (Fin.castAdd n i))) j :=
      congrFun hz₂
    ext j
    calc
      (a • z₁ + b • z₂) (Fin.natAdd m j)
          = a * z₁ (Fin.natAdd m j) + b * z₂ (Fin.natAdd m j) := by simp
      _ = a * (A (fun i => z₁ (Fin.castAdd n i))) j +
            b * (A (fun i => z₂ (Fin.castAdd n i))) j := by rw [hz₁j j, hz₂j j]
      _ = (A (a • (fun i => z₁ (Fin.castAdd n i)) +
            b • (fun i => z₂ (Fin.castAdd n i)))) j := by
            simp [map_add, map_smul]
      _ = (A (fun i => (a • z₁ + b • z₂) (Fin.castAdd n i))) j := by
            rfl
  have hIndicatorConvex :
      ConvexFunction (indicatorFunction graphSet) :=
    convexFunction_indicator_of_convex (C := graphSet) hGraphSetConvex
  have hIndicatorNoBot : ∀ z : Fin (m + n) → ℝ, indicatorFunction graphSet z ≠ ⊥ := by
    intro z
    by_cases hz : z ∈ graphSet
    · simp [indicatorFunction, hz]
    · simp [indicatorFunction, hz]
  have hGraphConvex :
      IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (indicatorFunction graphSet) :=
    helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ
      (f := indicatorFunction graphSet) hIndicatorConvex hIndicatorNoBot
  have hGraphEq :
      graphFunctionOfBifunction (fun u => pointIndicator (A u)) = indicatorFunction graphSet := by
    funext z
    simp [graphFunctionOfBifunction, pointIndicator, indicatorFunction, graphSet]
  -- The graph function of `u ↦ δ_{A u}` is exactly the indicator of the graph set.
  simpa [IsGraphConvexBifunction, hGraphEq] using hGraphConvex

/-- Helper for Lemma33.0.30: on the dual graph `uStar = A* xStar`, the genuine adjoint of the
indicator bifunction takes the value `0`. -/
lemma helperForLemma33_0_30_indicator_linearMap_adjoint_eq_zero_on_graph
    {m n : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (hEq : uStar = coordinateAdjointLinearMap A xStar) :
    genuineConvexBifunctionAdjoint (fun u => pointIndicator (A u)) xStar uStar = 0 := by
  subst hEq
  apply le_antisymm
  · rw [genuineConvexBifunctionAdjoint]
    refine sInf_le ?_
    refine ⟨(0, A 0), ?_⟩
    simp [pointIndicator]
  · rw [genuineConvexBifunctionAdjoint]
    refine le_sInf ?_
    intro a ha
    rcases ha with ⟨⟨u, x⟩, rfl⟩
    by_cases hx : x = A u
    · simp [pointIndicator, hx,
        helperForCorollary_26_3_3_dotProduct_coordinateAdjoint A u xStar, sub_eq_add_neg]
      have hnonneg :
          (0 : EReal) ≤
            ((((dotProduct u (coordinateAdjointLinearMap A xStar) : ℝ) : EReal) -
                (((dotProduct u (coordinateAdjointLinearMap A xStar) : ℝ) : EReal)))) := by
        rw [EReal.sub_self (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simpa [sub_eq_add_neg, add_comm] using hnonneg
    · simp [pointIndicator, hx]

/-- Helper for Lemma33.0.30: evaluating the genuine adjoint on a primal graph point produces the
linear form with coefficient `uStar - A* xStar`. -/
lemma helperForLemma33_0_30_indicator_linearMap_graph_term
    {m n : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (xStar : Fin n → ℝ) (uStar u : Fin m → ℝ) :
    ((pointIndicator (A u) (A u) - ((dotProduct (A u) xStar : ℝ) : EReal)) +
        ((dotProduct u uStar : ℝ) : EReal)) =
      (((dotProduct u (uStar - coordinateAdjointLinearMap A xStar) : ℝ) : EReal)) := by
  calc
    ((pointIndicator (A u) (A u) - ((dotProduct (A u) xStar : ℝ) : EReal)) +
        ((dotProduct u uStar : ℝ) : EReal))
        = (((dotProduct u uStar : ℝ) - dotProduct (A u) xStar : ℝ) : EReal) := by
            simp [pointIndicator, sub_eq_add_neg, add_comm]
    _ = (((dotProduct u uStar : ℝ) -
        dotProduct u (coordinateAdjointLinearMap A xStar) : ℝ) : EReal) := by
          rw [helperForCorollary_26_3_3_dotProduct_coordinateAdjoint A u xStar]
    _ = (((dotProduct u (uStar - coordinateAdjointLinearMap A xStar) : ℝ) : EReal)) := by
          rw [dotProduct_sub]

/-- Helper for Lemma33.0.30: off the dual graph `uStar ≠ A* xStar`, the genuine adjoint of the
indicator bifunction drops to `⊥`. -/
lemma helperForLemma33_0_30_indicator_linearMap_adjoint_eq_bot_off_graph
    {m n : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (hNe : uStar ≠ coordinateAdjointLinearMap A xStar) :
    genuineConvexBifunctionAdjoint (fun u => pointIndicator (A u)) xStar uStar = ⊥ := by
  let graphTerms : Set EReal :=
    Set.range fun u : Fin m → ℝ =>
      (((dotProduct u (uStar - coordinateAdjointLinearMap A xStar) : ℝ) : EReal))
  have hCoeffNe : uStar - coordinateAdjointLinearMap A xStar ≠ 0 := by
    intro hZero
    apply hNe
    exact sub_eq_zero.mp hZero
  have hLinearBot :
      sInf graphTerms = (⊥ : EReal) := by
    simpa [graphTerms] using
      (helperForTheorem_6_30_22_sInf_linear_term_eq_bot_of_ne_zero_with_realConst
        (b := uStar - coordinateAdjointLinearMap A xStar) (r := 0) hCoeffNe)
  have hSubset :
      graphTerms ⊆
        Set.range fun ux : (Fin m → ℝ) × (Fin n → ℝ) =>
          ((pointIndicator (A ux.1) ux.2 - ((dotProduct ux.2 xStar : ℝ) : EReal)) +
            ((dotProduct ux.1 uStar : ℝ) : EReal)) := by
    intro z hz
    rcases hz with ⟨u, rfl⟩
    refine ⟨(u, A u), ?_⟩
    simpa using
      (helperForLemma33_0_30_indicator_linearMap_graph_term A xStar uStar u)
  have hLeBot :
      genuineConvexBifunctionAdjoint (fun u => pointIndicator (A u)) xStar uStar ≤ ⊥ := by
    rw [genuineConvexBifunctionAdjoint]
    calc
      sInf
          (Set.range fun ux : (Fin m → ℝ) × (Fin n → ℝ) =>
            ((pointIndicator (A ux.1) ux.2 - ((dotProduct ux.2 xStar : ℝ) : EReal)) +
              ((dotProduct ux.1 uStar : ℝ) : EReal))) ≤ sInf graphTerms := by
                exact sInf_le_sInf hSubset
      _ = ⊥ := hLinearBot
  exact le_antisymm hLeBot bot_le

-- Proof sketch: use the graph-convex witness from
-- `pointIndicator_linearMap_isGraphConvexBifunction A`. For `F u = δ_{A u}`, the infimum
-- defining the genuine adjoint keeps only the terms with `x = A u`, so `F^* x^*` becomes
-- the concave point indicator at `A* x^*`. The resulting pairing identity is exactly the
-- classical adjoint relation for the coordinate transpose.
/-- Lemma33.0.30 (Indicator case): When `F u` is the convex point indicator at `A u` for a
linear map `A : ℝ^m → ℝ^n`, the genuine adjoint `F^* x^*` is the concave point indicator at
the adjoint image `A^* x^*`. Consequently, the two pairings reduce to the classical adjoint
relation `⟪A u, x^*⟫ = ⟪u, A^* x^*⟫`. -/
theorem genuineConvexBifunctionAdjoint_indicator_linearMap
    {m n : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (∀ xStar : Fin n → ℝ,
      genuineConvexBifunctionAdjoint
          (fun u => pointIndicator (A u)) xStar =
        concavePointIndicator (coordinateAdjointLinearMap A xStar)) ∧
      ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
        dotProduct (A u) xStar =
          dotProduct u (coordinateAdjointLinearMap A xStar) := by
  constructor
  · intro xStar
    funext uStar
    by_cases hEq : uStar = coordinateAdjointLinearMap A xStar
    · simpa [concavePointIndicator, hEq] using
        (helperForLemma33_0_30_indicator_linearMap_adjoint_eq_zero_on_graph A xStar uStar hEq)
    · simpa [concavePointIndicator, hEq] using
        (helperForLemma33_0_30_indicator_linearMap_adjoint_eq_bot_off_graph A xStar uStar hEq)
  · intro u xStar
    exact helperForCorollary_26_3_3_dotProduct_coordinateAdjoint A u xStar

end Section33
end Chap07
