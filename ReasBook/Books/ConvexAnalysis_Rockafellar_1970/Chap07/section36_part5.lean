/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section36_part4

section Chap07
section Section36

/-- Definition 36.4.5: Let `F` be a convex bifunction from `ℝ^m` to `ℝ^n`. The *Lagrangian* of the
associated convex program is the function `L : ℝ^m × ℝ^n → [-∞, +∞]` defined by
`L(u*, x) := inf_{u ∈ ℝ^m} (⟨u*, u⟩ + (F u) x)`. -/
noncomputable def bifunctionLagrangian {m n : ℕ}
    (F :
      {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsEpigraphConvexBifunction (m := m) (n := n) F}) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun uStar x =>
    iInf fun u : Fin m → ℝ => ((finDot (n := m) uStar u : ℝ) : EReal) + F.1 u x

/-- The infimal pairing `⟪uStar, g⟫ := inf_u (⟨uStar, u⟩ - g u)` used in the book for an
extended-real function `g : ℝ^m → [-∞, +∞]`. -/
noncomputable def infPairing {m : ℕ} (uStar : Fin m → ℝ) (g : (Fin m → ℝ) → EReal) : EReal :=
  iInf fun u : Fin m → ℝ => ((finDot (n := m) uStar u : ℝ) : EReal) + (-g u)

/-- Concavity in the first argument `uStar` (pointwise in `x`) for an extended-real bifunction
`L(uStar, x)`. -/
def IsConcaveInFirst {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∀ x : Fin n → ℝ, Convex ℝ {p : (Fin m → ℝ) × ℝ | (p.2 : EReal) ≤ L p.1 x}

/-- Convexity in the second argument `x` (pointwise in `uStar`) for an extended-real bifunction
`L(uStar, x)`. -/
def IsConvexInSecond {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∀ uStar : Fin m → ℝ, Convex ℝ {p : (Fin n → ℝ) × ℝ | L uStar p.1 ≤ (p.2 : EReal)}

/-- Helper for Proposition 36.4.6: `finDot` is linear in its first argument. -/
lemma helperForProposition_36_4_6_finDot_smul_add_left
    {m : ℕ} (uStar₁ uStar₂ u : Fin m → ℝ) (a b : ℝ) :
    finDot (n := m) (a • uStar₁ + b • uStar₂) u =
      a * finDot (n := m) uStar₁ u + b * finDot (n := m) uStar₂ u := by
  simpa [finDot, smul_eq_mul] using
    (show (a • uStar₁ + b • uStar₂) ⬝ᵥ u = a • (uStar₁ ⬝ᵥ u) + b • (uStar₂ ⬝ᵥ u) by
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct])

/-- Helper for Proposition 36.4.6: `finDot` is linear in its second argument. -/
lemma helperForProposition_36_4_6_finDot_smul_add_right
    {m : ℕ} (uStar u₁ u₂ : Fin m → ℝ) (a b : ℝ) :
    finDot (n := m) uStar (a • u₁ + b • u₂) =
      a * finDot (n := m) uStar u₁ + b * finDot (n := m) uStar u₂ := by
  simpa [finDot, smul_eq_mul] using
    (show uStar ⬝ᵥ (a • u₁ + b • u₂) = a • (uStar ⬝ᵥ u₁) + b • (uStar ⬝ᵥ u₂) by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul])

/-- Helper for Proposition 36.4.6: the local `finDot` notation agrees with the standard
`dotProduct`. -/
lemma helperForProposition_36_4_6_finDot_eq_dotProduct
    {m : ℕ} (uStar u : Fin m → ℝ) :
    finDot (n := m) uStar u = dotProduct uStar u := by
  -- Both notations are definitionally the same finite sum on `Fin m`.
  simp [finDot, dotProduct]

/-- Helper for Proposition 36.4.6: the local infimal pairing is exactly the chapter's
concave conjugate. -/
lemma helperForProposition_36_4_6_infPairing_eq_concaveConjugate
    {m : ℕ} (uStar : Fin m → ℝ) (g : (Fin m → ℝ) → EReal) :
    infPairing (m := m) uStar g = concaveConjugate g uStar := by
  -- Rewrite both sides as the same indexed infimum.
  calc
    infPairing (m := m) uStar g
        = iInf (fun u : Fin m → ℝ => (((finDot (n := m) uStar u : ℝ) : EReal) + (-g u))) := rfl
    _ = iInf (fun u : Fin m → ℝ => (((u ⬝ᵥ uStar : ℝ) : EReal) + (-g u))) := by
          refine iInf_congr ?_
          intro u
          rw [helperForProposition_36_4_6_finDot_eq_dotProduct, dotProduct_comm]
    _ = concaveConjugate g uStar := by
          symm
          exact helperForTheorem_6_30_4_concaveConjugate_eq_iInf (g := g) uStar

/-- Helper for Proposition 36.4.6: negate the scalar coordinate while keeping the vector
coordinate fixed. -/
def helperForProposition_36_4_6_negateScalarSecond {m : ℕ} :
    ((Fin m → ℝ) × ℝ) → ((Fin m → ℝ) × ℝ) :=
  fun p => (p.1, -p.2)

/-- Helper for Proposition 36.4.6: negating the scalar coordinate is linear on
`(ℝ^m) × ℝ`. -/
lemma helperForProposition_36_4_6_negateScalarSecond_isLinear {m : ℕ} :
    IsLinearMap ℝ (helperForProposition_36_4_6_negateScalarSecond (m := m)) := by
  constructor
  · intro p q
    -- The map is componentwise identity on vectors and negation on the scalar slot.
    ext <;> simp [helperForProposition_36_4_6_negateScalarSecond, add_comm]
  · intro c p
    -- Scalar multiplication commutes with the scalar negation.
    ext <;> simp [helperForProposition_36_4_6_negateScalarSecond]

/-- Helper for Proposition 36.4.6: the hypograph of `infPairing` is the preimage of the
epigraph of its negation under scalar negation. -/
lemma helperForProposition_36_4_6_infPairing_hypograph_preimage_negEpigraph
    {m : ℕ} (g : (Fin m → ℝ) → EReal) :
    {p : (Fin m → ℝ) × ℝ | (p.2 : EReal) ≤ infPairing (m := m) p.1 g} =
      helperForProposition_36_4_6_negateScalarSecond (m := m) ⁻¹'
        epigraph (Set.univ : Set (Fin m → ℝ)) (fun uStar => -(infPairing (m := m) uStar g)) := by
  ext p
  constructor
  · intro hp
    -- The vector coordinate always belongs to `Set.univ`; the scalar inequality flips by negation.
    change Set.univ p.1 ∧ -(infPairing (m := m) p.1 g) ≤ (((-p.2 : ℝ)) : EReal)
    refine ⟨by trivial, ?_⟩
    simpa using (EReal.neg_le_neg_iff.2 hp)
  · rintro ⟨_, hp⟩
    -- Move the inequality back across scalar negation.
    simpa using (EReal.neg_le_neg_iff.1 hp)

/-- Helper for Proposition 36.4.6: for every function `g`, the map
`uStar ↦ infPairing uStar g` is concave. -/
lemma helperForProposition_36_4_6_infPairing_isConcave
    {m : ℕ} (g : (Fin m → ℝ) → EReal) :
    Convex ℝ {p : (Fin m → ℝ) × ℝ | (p.2 : EReal) ≤ infPairing (m := m) p.1 g} := by
  let A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := (-1 : ℝ) • LinearMap.id
  have hFenchelConvOn :
      ConvexFunctionOn (S := (Set.univ : Set (Fin m → ℝ)))
        (fenchelConjugate m (fun z => -g z)) := by
    -- Fenchel conjugates are convex on the whole space.
    simpa [ConvexFunction] using (fenchelConjugate_closedConvex (n := m) (f := fun z => -g z)).2
  have hPrecomp :
      ConvexFunctionOn (S := (Set.univ : Set (Fin m → ℝ)))
        (fun y => fenchelConjugate m (fun z => -g z) (A y)) := by
    -- Precomposing with the negation linear map preserves convexity.
    exact convexFunctionOn_precomp_linearMap (A := A) (g := fenchelConjugate m (fun z => -g z))
      hFenchelConvOn
  have hNegEq :
      (fun y => -(infPairing (m := m) y g)) =
        fun y => fenchelConjugate m (fun z => -g z) (A y) := by
    funext y
    -- Rewrite `infPairing` as a concave conjugate, then use the standard sign-change identity.
    rw [helperForProposition_36_4_6_infPairing_eq_concaveConjugate]
    have hy :=
      congrArg (fun f => f y)
        (helperForTheorem_6_30_3_neg_concaveConjugate_eq_fenchel_precomp_neg (g := g))
    simpa [A] using hy
  have hConvEpi :
      Convex ℝ
        (epigraph (Set.univ : Set (Fin m → ℝ)) (fun y => -(infPairing (m := m) y g))) := by
    -- The epigraph of a convex function is convex.
    simpa [hNegEq] using convex_epigraph_of_convexFunctionOn (f := fun y =>
      fenchelConjugate m (fun z => -g z) (A y)) (hf := hPrecomp)
  -- The desired hypograph is a linear preimage of that convex epigraph.
  rw [helperForProposition_36_4_6_infPairing_hypograph_preimage_negEpigraph]
  exact hConvEpi.is_linear_preimage
    (helperForProposition_36_4_6_negateScalarSecond_isLinear (m := m))

/-- Helper for Proposition 36.4.6: the graph function of a section-local convex bifunction is a
convex function on the product space. -/
lemma helperForProposition_36_4_6_graphFunction_isConvexFunction
    {m n : ℕ}
    (F :
      {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsEpigraphConvexBifunction (m := m) (n := n) F}) :
    ConvexFunction (graphFunctionOfBifunction F.1) := by
  unfold ConvexFunction ConvexFunctionOn
  intro p hp q hq a b ha hb hab
  rcases p with ⟨z₁, μ₁⟩
  rcases q with ⟨z₂, μ₂⟩
  let u₁ : Fin m → ℝ := fun i => z₁ (Fin.castAdd n i)
  let u₂ : Fin m → ℝ := fun i => z₂ (Fin.castAdd n i)
  let x₁ : Fin n → ℝ := fun j => z₁ (Fin.natAdd m j)
  let x₂ : Fin n → ℝ := fun j => z₂ (Fin.natAdd m j)
  have hz₁Split : Fin.append u₁ x₁ = z₁ := by
    -- Recover the first graph point from its `u` and `x` blocks.
    simpa [u₁, x₁] using helperForLemma33_0_14_append_split_eq z₁
  have hz₂Split : Fin.append u₂ x₂ = z₂ := by
    -- Recover the second graph point in the same way.
    simpa [u₂, x₂] using helperForLemma33_0_14_append_split_eq z₂
  have hp' : ((u₁, x₁), μ₁) ∈ bifunctionEpigraph (m := m) (n := n) F.1 := by
    -- Epigraph membership of the graph function is exactly epigraph membership of `F`.
    simpa [bifunctionEpigraph, graphFunctionOfBifunction, u₁, x₁]
      using (mem_epigraph_univ_iff (f := graphFunctionOfBifunction F.1)).1 hp
  have hq' : ((u₂, x₂), μ₂) ∈ bifunctionEpigraph (m := m) (n := n) F.1 := by
    -- The second endpoint rewrites identically.
    simpa [bifunctionEpigraph, graphFunctionOfBifunction, u₂, x₂]
      using (mem_epigraph_univ_iff (f := graphFunctionOfBifunction F.1)).1 hq
  have hcombo :
      ((a • u₁ + b • u₂, a • x₁ + b • x₂), a * μ₁ + b * μ₂) ∈
        bifunctionEpigraph (m := m) (n := n) F.1 :=
    F.2 hp' hq' ha hb hab
  have hAppend :
      a • z₁ + b • z₂ =
        Fin.append (a • u₁ + b • u₂) (a • x₁ + b • x₂) := by
    -- Weighted combinations split blockwise under `Fin.append`.
    rw [← hz₁Split, ← hz₂Split]
    exact helperForLemma33_0_14_append_weighted a b u₁ u₂ x₁ x₂
  have hineq :
      graphFunctionOfBifunction F.1 (a • z₁ + b • z₂) ≤
        (((a * μ₁ + b * μ₂ : ℝ)) : EReal) := by
    rw [hAppend]
    simpa [bifunctionEpigraph, graphFunctionOfBifunction] using hcombo
  -- Repackage the convexity of `F` back into the epigraph of the graph function.
  exact (mem_epigraph_univ_iff (f := graphFunctionOfBifunction F.1)).2 (by simpa using hineq)

/-- Helper for Proposition 36.4.6: the tilted graph function used for the fixed-`uStar`
sections is convex. -/
lemma helperForProposition_36_4_6_tiltedGraph_isConvexFunction
    {m n : ℕ}
    (F :
      {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsEpigraphConvexBifunction (m := m) (n := n) F})
    (uStar : Fin m → ℝ) :
    ConvexFunction
      (fun z : Fin (m + n) → ℝ =>
        ((finDot (n := m) uStar (projXLinearMap (n := m) (m := n) z) : ℝ) : EReal) +
          graphFunctionOfBifunction F.1 z) := by
  classical
  let g : (Fin (m + n) → ℝ) → EReal := graphFunctionOfBifunction F.1
  let l : (Fin (m + n) → ℝ) → ℝ :=
    fun z => -(finDot (n := m) uStar (projXLinearMap (n := m) (m := n) z))
  let G : (Fin (m + n) → ℝ) → EReal :=
    fun z => g z - ((l z : ℝ) : EReal)
  have hEqFun :
      (fun z : Fin (m + n) → ℝ =>
        ((finDot (n := m) uStar (projXLinearMap (n := m) (m := n) z) : ℝ) : EReal) +
          graphFunctionOfBifunction F.1 z) = G := by
    -- The chosen auxiliary function `G` is just the same tilt written as subtraction of a
    -- negative linear form.
    funext z
    simp [G, g, l, sub_eq_add_neg, add_comm]
  have hConv_g : ConvexFunction g :=
    helperForProposition_36_4_6_graphFunction_isConvexFunction F
  have hConvEpi_g : Convex ℝ (epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g) := by
    -- The untitled graph function is already convex.
    simpa [ConvexFunction] using hConv_g
  have hTiltConv : ConvexFunction G := by
    -- Follow the Section 33 shear argument: subtract the negative linear form and work with
    -- the sheared epigraph directly.
    unfold ConvexFunction ConvexFunctionOn
    intro p hp q hq a b ha hb hab
    rcases p with ⟨z₁, μ₁⟩
    rcases q with ⟨z₂, μ₂⟩
    have hμ₁ : G z₁ ≤ (μ₁ : EReal) := (mem_epigraph_univ_iff (f := G)).1 hp
    have hμ₂ : G z₂ ≤ (μ₂ : EReal) := (mem_epigraph_univ_iff (f := G)).1 hq
    have hz₁ : g z₁ ≤ (μ₁ : EReal) + ((l z₁ : ℝ) : EReal) := by
      -- Move the finite linear term across subtraction at the first epigraph point.
      have hSub : g z₁ - ((l z₁ : ℝ) : EReal) ≤ (μ₁ : EReal) := by
        simpa [G] using hμ₁
      exact
        (EReal.sub_le_iff_le_add
          (a := g z₁) (b := ((l z₁ : ℝ) : EReal)) (c := (μ₁ : EReal))
          (Or.inl (by simp)) (Or.inl (by simp))).1 hSub
    have hz₂ : g z₂ ≤ (μ₂ : EReal) + ((l z₂ : ℝ) : EReal) := by
      -- The same epigraph shear applies to the second graph point.
      have hSub : g z₂ - ((l z₂ : ℝ) : EReal) ≤ (μ₂ : EReal) := by
        simpa [G] using hμ₂
      exact
        (EReal.sub_le_iff_le_add
          (a := g z₂) (b := ((l z₂ : ℝ) : EReal)) (c := (μ₂ : EReal))
          (Or.inl (by simp)) (Or.inl (by simp))).1 hSub
    have hp' : (z₁, μ₁ + l z₁) ∈ epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g := by
      exact (mem_epigraph_univ_iff (f := g)).2 (by simpa [EReal.coe_add, add_assoc] using hz₁)
    have hq' : (z₂, μ₂ + l z₂) ∈ epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g := by
      exact (mem_epigraph_univ_iff (f := g)).2 (by simpa [EReal.coe_add, add_assoc] using hz₂)
    have hr' :
        a • (z₁, μ₁ + l z₁) + b • (z₂, μ₂ + l z₂) ∈
          epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g :=
      hConvEpi_g hp' hq' ha hb hab
    have hlin_l :
        l (a • z₁ + b • z₂) = a * l z₁ + b * l z₂ := by
      -- The tilt depends linearly on the projected `u`-block.
      calc
        l (a • z₁ + b • z₂)
            = -(finDot (n := m) uStar
                (projXLinearMap (n := m) (m := n) (a • z₁ + b • z₂))) := by
                  rfl
        _ = -(finDot (n := m) uStar
              (a • projXLinearMap (n := m) (m := n) z₁ +
                b • projXLinearMap (n := m) (m := n) z₂)) := by
              rw [map_add, map_smul, map_smul]
        _ = -(a * finDot (n := m) uStar (projXLinearMap (n := m) (m := n) z₁) +
              b * finDot (n := m) uStar (projXLinearMap (n := m) (m := n) z₂)) := by
              rw [helperForProposition_36_4_6_finDot_smul_add_right]
        _ = a * l z₁ + b * l z₂ := by
              simp [l]
              ring
    have hEq :
        a • (z₁, μ₁ + l z₁) + b • (z₂, μ₂ + l z₂) =
          (a • z₁ + b • z₂, (a * μ₁ + b * μ₂) + l (a • z₁ + b • z₂)) := by
      ext <;> simp [hlin_l, mul_add, add_assoc, add_left_comm]
    have hz_combo :
        g (a • z₁ + b • z₂) ≤
          (((a * μ₁ + b * μ₂) + l (a • z₁ + b • z₂) : ℝ) : EReal) := by
      -- Convexity of the original graph function propagates through the shear.
      have :
          (a • z₁ + b • z₂, (a * μ₁ + b * μ₂) + l (a • z₁ + b • z₂)) ∈
            epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g := by
        rw [← hEq]
        exact hr'
      exact (mem_epigraph_univ_iff (f := g)).1 this
    have hG_combo :
        G (a • z₁ + b • z₂) ≤ ((a * μ₁ + b * μ₂ : ℝ) : EReal) := by
      -- Move the linear term back across subtraction to recover the tilted epigraph inequality.
      have hz_combo' :
          g (a • z₁ + b • z₂) ≤
            ((a * μ₁ + b * μ₂ : ℝ) : EReal) + ((l (a • z₁ + b • z₂) : ℝ) : EReal) := by
        simpa [EReal.coe_add, add_assoc] using hz_combo
      have :
          g (a • z₁ + b • z₂) - ((l (a • z₁ + b • z₂) : ℝ) : EReal) ≤
            ((a * μ₁ + b * μ₂ : ℝ) : EReal) :=
        (EReal.sub_le_iff_le_add
          (a := g (a • z₁ + b • z₂))
          (b := ((l (a • z₁ + b • z₂) : ℝ) : EReal))
          (c := ((a * μ₁ + b * μ₂ : ℝ) : EReal))
          (Or.inl (by simp)) (Or.inl (by simp))).2 (by simpa [add_comm] using hz_combo')
      simpa [G] using this
    exact (mem_epigraph_univ_iff (f := G)).2 (by simpa using hG_combo)
  simpa [hEqFun] using hTiltConv

/-- Helper for Proposition 36.4.6: for fixed `uStar`, the `x`-section of the Lagrangian is the
fiber infimum of the tilted graph under projection to the `x`-coordinates. -/
lemma helperForProposition_36_4_6_secondSection_eq_projectionInf
    {m n : ℕ}
    (F :
      {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsEpigraphConvexBifunction (m := m) (n := n) F})
    (uStar : Fin m → ℝ) :
    (fun x : Fin n → ℝ => bifunctionLagrangian (m := m) (n := n) F uStar x) =
      imageUnderLinearMap
        (projLamLinearMap (n := m) (m := n))
        (fun z : Fin (m + n) → ℝ =>
          ((finDot (n := m) uStar (projXLinearMap (n := m) (m := n) z) : ℝ) : EReal) +
            graphFunctionOfBifunction F.1 z) := by
  funext x
  let A : (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) := projLamLinearMap (n := m) (m := n)
  let h : (Fin (m + n) → ℝ) → EReal :=
    fun z : Fin (m + n) → ℝ =>
      ((finDot (n := m) uStar (projXLinearMap (n := m) (m := n) z) : ℝ) : EReal) +
        graphFunctionOfBifunction F.1 z
  have hSet :
      {z : EReal | ∃ y : Fin (m + n) → ℝ, A y = x ∧ z = h y} =
        Set.range (fun u : Fin m → ℝ => (((finDot (n := m) uStar u : ℝ) : EReal) + F.1 u x)) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      -- Recover the `u`-block from the witness `y` and rewrite the `x`-block using the fiber
      -- condition `A y = x`.
      refine ⟨projXLinearMap (n := m) (m := n) y, ?_⟩
      have hySplit :
          Fin.append (projXLinearMap (n := m) (m := n) y)
              (projLamLinearMap (n := m) (m := n) y) = y := by
        simpa [projXLinearMap, projLamLinearMap] using helperForLemma33_0_14_append_split_eq y
      have hyEq : y = Fin.append (projXLinearMap (n := m) (m := n) y) x := by
        have hyProj : projLamLinearMap (n := m) (m := n) y = x := by
          simpa [A] using hy
        calc
          y = Fin.append (projXLinearMap (n := m) (m := n) y)
                (projLamLinearMap (n := m) (m := n) y) := hySplit.symm
          _ = Fin.append (projXLinearMap (n := m) (m := n) y) x := by rw [hyProj]
      rw [hyEq]
      simp [h, projXLinearMap, graphFunctionOfBifunction]
    · rintro ⟨u, rfl⟩
      -- Repackage the witness as the appended point whose first block is `u` and second block
      -- is the target section variable `x`.
      refine ⟨Fin.append u x, ?_, ?_⟩
      · ext j
        change Fin.append u x (Fin.natAdd m j) = x j
        exact Fin.append_right (u := u) (v := x) j
      · have hProjX :
            projXLinearMap (n := m) (m := n) (Fin.append u x) = u := by
          ext i
          change Fin.append u x (Fin.castAdd n i) = u i
          exact Fin.append_left (u := u) (v := x) i
        simp [h, graphFunctionOfBifunction, hProjX]
  -- Rewrite the projection fiber as a range, then identify the `sInf` with the defining `iInf`
  -- of the Lagrangian.
  simp [bifunctionLagrangian, imageUnderLinearMap, A, h, hSet, sInf_range]

-- Proof sketch: Unfold `bifunctionLagrangian` and `bifunctionInverse` to rewrite
-- `⟨uStar,u⟩ - (F_* x)(u)` as `⟨uStar,u⟩ + (F u)(x)`. The identification with `infPairing`
-- is then by definition. For the final concavity/convexity claims, use standard stability of
-- convex hypographs/epigraphs under infima of affine perturbations and the convexity of `F`.
/-- Proposition 36.4.6: Let `F` be a convex bifunction from `ℝ^m` to `ℝ^n` with inverse `F_*`, and
let `L` be defined by Definition 36.4.5. Then

`L(uStar, x) = inf_u (⟨uStar, u⟩ - (F_* x)(u)) = ⟪uStar, F_* x⟫`.

In particular, `L` is concave in `uStar` and convex in `x`. -/
theorem bifunctionLagrangian_eq_infPairing_inverse_and_concave_convex
    {m n : ℕ}
    (F :
      {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsEpigraphConvexBifunction (m := m) (n := n) F}) :
    (∀ uStar : Fin m → ℝ, ∀ x : Fin n → ℝ,
        bifunctionLagrangian (m := m) (n := n) F uStar x =
          iInf fun u : Fin m → ℝ =>
            ((finDot (n := m) uStar u : ℝ) : EReal) +
              (-bifunctionInverse F.1 x u)) ∧
      (∀ uStar : Fin m → ℝ, ∀ x : Fin n → ℝ,
        bifunctionLagrangian (m := m) (n := n) F uStar x =
          infPairing (m := m) uStar (bifunctionInverse F.1 x)) ∧
      IsConcaveInFirst (m := m) (n := n) (bifunctionLagrangian (m := m) (n := n) F) ∧
      IsConvexInSecond (m := m) (n := n) (bifunctionLagrangian (m := m) (n := n) F) :=
  by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro uStar x
      -- Unfold the inverse and cancel the double negation in the textbook formula.
      simp [bifunctionLagrangian, bifunctionInverse]
    · intro uStar x
      -- The second displayed equality is just the definition of `infPairing`.
      simp [bifunctionLagrangian, infPairing, bifunctionInverse]
    · intro x
      -- Rewrite the fixed-`x` section through the local infimal pairing.
      have hSection :
          (fun uStar : Fin m → ℝ => bifunctionLagrangian (m := m) (n := n) F uStar x) =
            fun uStar : Fin m → ℝ => infPairing (m := m) uStar (bifunctionInverse F.1 x) := by
        funext uStar
        simp [bifunctionLagrangian, infPairing, bifunctionInverse]
      have hSet :
          {p : (Fin m → ℝ) × ℝ | (p.2 : EReal) ≤ bifunctionLagrangian F p.1 x} =
            {p : (Fin m → ℝ) × ℝ |
              (p.2 : EReal) ≤ infPairing (m := m) p.1 (bifunctionInverse F.1 x)} := by
        ext p
        have hp :
            bifunctionLagrangian (m := m) (n := n) F p.1 x =
              infPairing (m := m) p.1 (bifunctionInverse F.1 x) :=
          congrArg (fun f => f p.1) hSection
        simp [hp]
      rw [hSet]
      exact helperForProposition_36_4_6_infPairing_isConcave (g := bifunctionInverse F.1 x)
    · intro uStar
      have hConv :
          ConvexFunction (fun x : Fin n → ℝ => bifunctionLagrangian (m := m) (n := n) F uStar x) := by
        -- Rewrite the fixed-`uStar` section as the Chapter 2 fiber infimum of the tilted graph.
        rw [helperForProposition_36_4_6_secondSection_eq_projectionInf (F := F) (uStar := uStar)]
        -- Chapter 2 says that infimizing a convex function along linear fibers preserves
        -- convexity of the resulting section.
        simpa [imageUnderLinearMap] using
          convexFunction_linearMap_infimum
            (A := projLamLinearMap (n := m) (m := n))
            (h :=
              fun z : Fin (m + n) → ℝ =>
                ((finDot (n := m) uStar
                    (projXLinearMap (n := m) (m := n) z) : ℝ) : EReal) +
                  graphFunctionOfBifunction F.1 z)
            (helperForProposition_36_4_6_tiltedGraph_isConvexFunction (F := F) uStar)
      have hConvOn :
          ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ)))
            (fun x : Fin n → ℝ => bifunctionLagrangian (m := m) (n := n) F uStar x) := by
        -- `ConvexFunction` is exactly the univ-domain version of `ConvexFunctionOn`.
        simpa [ConvexFunction] using hConv
      have hEpi :
          Convex ℝ
            (epigraph (Set.univ : Set (Fin n → ℝ))
              (fun x : Fin n → ℝ => bifunctionLagrangian (m := m) (n := n) F uStar x)) := by
        -- The epigraph of a convex function is convex.
        exact convex_epigraph_of_convexFunctionOn
          (f := fun x : Fin n → ℝ => bifunctionLagrangian (m := m) (n := n) F uStar x)
          (hf := hConvOn)
      have hSet :
          {p : (Fin n → ℝ) × ℝ | bifunctionLagrangian F uStar p.1 ≤ (p.2 : EReal)} =
            epigraph (Set.univ : Set (Fin n → ℝ))
              (fun x : Fin n → ℝ => bifunctionLagrangian (m := m) (n := n) F uStar x) := by
        ext p
        constructor
        · intro hp
          exact ⟨by trivial, hp⟩
        · rintro ⟨_, hp⟩
          exact hp
      -- Replace the section epigraph by the Chapter 1 epigraph API.
      rw [hSet]
      exact hEpi

/-- Upper closedness in the first argument `uStar` (pointwise in `x`) for an extended-real
function `L(uStar, x)`: for each `x`, the hypograph `{(uStar,t) | t ≤ L(uStar,x)}` is closed. -/
def IsUpperClosedInFirst {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∀ x : Fin n → ℝ, IsClosed {p : (Fin m → ℝ) × ℝ | (p.2 : EReal) ≤ L p.1 x}

/-- Lower closedness in the second argument `x` (pointwise in `uStar`) for an extended-real
function `L(uStar, x)`: for each `uStar`, the epigraph `{(x,t) | L(uStar,x) ≤ t}` is closed. -/
def IsLowerClosedInSecond {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∀ uStar : Fin m → ℝ, IsClosed {p : (Fin n → ℝ) × ℝ | L uStar p.1 ≤ (p.2 : EReal)}

/-- A bundled predicate expressing that `L(uStar, x)` is *upper closed concave-convex* on
`ℝ^m × ℝ^n`: it is upper closed and concave in `uStar`, and lower closed and convex in `x`. -/
def IsUpperClosedConcaveConvex {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsUpperClosedInFirst (m := m) (n := n) L ∧
    IsLowerClosedInSecond (m := m) (n := n) L ∧
      IsConcaveInFirst (m := m) (n := n) L ∧ IsConvexInSecond (m := m) (n := n) L

/-- Helper for Theorem 36.5: a Lagrangian already has the concave-convex orientation from
Proposition 36.4.6. -/
lemma helperForTheorem_36_5_lagrangian_has_concaveConvex_orientation
    {m n : ℕ}
    (F :
      {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsEpigraphConvexBifunction (m := m) (n := n) F}) :
    IsConcaveInFirst (m := m) (n := n) (bifunctionLagrangian (m := m) (n := n) F) ∧
      IsConvexInSecond (m := m) (n := n) (bifunctionLagrangian (m := m) (n := n) F) := by
  -- Proposition 36.4.6 already packages the two orientation statements for the Lagrangian.
  rcases bifunctionLagrangian_eq_infPairing_inverse_and_concave_convex (F := F) with
    ⟨-, -, hConcave, hConvex⟩
  exact ⟨hConcave, hConvex⟩

/-- Helper for Theorem 36.5: every one-variable infimal pairing section is concave-closed. -/
lemma helperForTheorem_36_5_infPairing_isFunctionConcaveClosed
    {m : ℕ} (g : (Fin m → ℝ) → EReal) :
    IsFunctionConcaveClosed (fun uStar : Fin m → ℝ => infPairing (m := m) uStar g) := by
  have hFenchelLsc :
      LowerSemicontinuous (fenchelConjugate m (fun z : Fin m → ℝ => -g z)) := by
    -- Fenchel conjugates are closed convex, so in particular lower semicontinuous.
    simpa [ConvexFunction] using
      (fenchelConjugate_closedConvex (n := m) (f := fun z : Fin m → ℝ => -g z)).1
  have hNegLsc :
      LowerSemicontinuous
        (fun uStar : Fin m → ℝ => -(infPairing (m := m) uStar g)) := by
    -- Rewrite the negated infimal pairing as a Fenchel conjugate precomposed with negation.
    have hPrecompLsc :
        LowerSemicontinuous
          (fun uStar : Fin m → ℝ => fenchelConjugate m (fun z : Fin m → ℝ => -g z) (-uStar)) :=
      hFenchelLsc.comp_continuous continuous_neg
    simpa [helperForProposition_36_4_6_infPairing_eq_concaveConjugate,
      helperForTheorem_6_30_3_neg_concaveConjugate_eq_fenchel_precomp_neg] using hPrecompLsc
  have hNegClosed :
      IsFunctionConvexClosed
        (fun uStar : Fin m → ℝ => -(infPairing (m := m) uStar g)) := by
    -- Lower semicontinuity fixes the negated section under the Section 33 convex closure.
    unfold IsFunctionConvexClosed
    simpa using
      helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hNegLsc
  -- Convert the convex-closedness of the negated section back to concave-closedness.
  exact
    (helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed
      (g := fun uStar : Fin m → ℝ => infPairing (m := m) uStar g)).2 hNegClosed

/-- Helper for Theorem 36.5: upper/lower closedness of an upper closed concave-convex bifunction
already gives the Section 33 one-variable closedness data on every slice. -/
lemma helperForTheorem_36_5_upperClosedSlices_to_functionClosedData
    {m n : ℕ}
    {L : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hL : IsUpperClosedConcaveConvex (m := m) (n := n) L) :
    (∀ x : Fin n → ℝ, IsFunctionConcaveClosed (fun uStar : Fin m → ℝ => L uStar x)) ∧
      (∀ uStar : Fin m → ℝ, IsFunctionConvexClosed (fun x : Fin n → ℝ => L uStar x)) := by
  rcases hL with ⟨hUpper, hLower, -, -⟩
  constructor
  · intro x
    have hClosedUpperLevel :
        ∀ α : ℝ, IsClosed (concaveUpperLevelSet (fun uStar : Fin m → ℝ => L uStar x) α) := by
      intro α
      let freezeHeight : (Fin m → ℝ) → (Fin m → ℝ) × ℝ := fun uStar => (uStar, α)
      have hFreezeHeightCont : Continuous freezeHeight := by
        -- Freezing the height coordinate is a continuous embedding of the section domain.
        change Continuous (fun uStar : Fin m → ℝ => (uStar, α))
        fun_prop
      have hPreimage :
          freezeHeight ⁻¹' {p : (Fin m → ℝ) × ℝ | (p.2 : EReal) ≤ L p.1 x} =
            concaveUpperLevelSet (fun uStar : Fin m → ℝ => L uStar x) α := by
        ext uStar
        simp [freezeHeight, concaveUpperLevelSet]
      -- Each upper level set is a continuous preimage of the fixed-`x` hypograph.
      rw [← hPreimage]
      exact (hUpper x).preimage hFreezeHeightCont
    have hNegLsc :
        LowerSemicontinuous (fun uStar : Fin m → ℝ => -L uStar x) := by
      -- Theorem 6.30.2 converts closed upper level sets into lower semicontinuity of the negated
      -- section.
      exact
        (helperForTheorem_6_30_2_closedUpperLevelSet_iff_neg_lsc
          (g := fun uStar : Fin m → ℝ => L uStar x)).1 hClosedUpperLevel
    have hNegClosed :
        IsFunctionConvexClosed (fun uStar : Fin m → ℝ => -L uStar x) := by
      -- Lower semicontinuity of the negated slice is the closedness clause needed by Section 33.
      unfold IsFunctionConvexClosed
      simpa using
        helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hNegLsc
    -- Flip signs back to recover concave-closedness of the original first-variable slice.
    exact
      (helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed
        (g := fun uStar : Fin m → ℝ => L uStar x)).2 hNegClosed
  · intro uStar
    have hLowerSc : LowerSemicontinuous (fun x : Fin n → ℝ => L uStar x) := by
      -- Closed real-height epigraphs give lower semicontinuity via the Chapter 21 epigraph lemma.
      exact
        helperForTheorem_21_3_lowerSemicontinuous_of_closedEpigraph
          (f := fun x : Fin n → ℝ => L uStar x) (hfClosed := hLower uStar)
    -- Lower semicontinuity fixes the second-variable slice under the Section 33 convex closure.
    unfold IsFunctionConvexClosed
    simpa using
      helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hLowerSc

/-- Helper for Theorem 36.5: upper closedness together with first-variable concavity upgrades each
fixed-`x` slice to a closed concave function in the Chapter 6 sense. -/
lemma helperForTheorem_36_5_sliceClosedConcave_of_upperClosedConcave
    {m n : ℕ}
    {L : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hUpper : IsUpperClosedInFirst (m := m) (n := n) L)
    (hConc : IsConcaveInFirst (m := m) (n := n) L) :
    ∀ x : Fin n → ℝ, ClosedConcaveFunction (fun uStar : Fin m → ℝ => L uStar x) := by
  intro x
  have hConvNeg :
      ConvexFunction (fun uStar : Fin m → ℝ => -(L uStar x)) := by
    have hSet :
        epigraph (Set.univ : Set (Fin m → ℝ)) (fun uStar : Fin m → ℝ => -(L uStar x)) =
          helperForProposition_36_4_6_negateScalarSecond (m := m) ⁻¹'
            {p : (Fin m → ℝ) × ℝ | (p.2 : EReal) ≤ L p.1 x} := by
      ext p
      constructor
      · rintro ⟨_, hp⟩
        change (((-p.2 : ℝ)) : EReal) ≤ L p.1 x
        have hp' : -(L p.1 x) ≤ -((((-p.2 : ℝ)) : EReal)) := by
          simpa using hp
        exact EReal.neg_le_neg_iff.mp hp'
      · intro hp
        change (((-p.2 : ℝ)) : EReal) ≤ L p.1 x at hp
        have hp' : -(L p.1 x) ≤ -((((-p.2 : ℝ)) : EReal)) := by
          exact EReal.neg_le_neg_iff.mpr hp
        refine ⟨by trivial, ?_⟩
        simpa using hp'
    -- The height-negation linear map transports convexity from the hypograph to the epigraph.
    unfold ConvexFunction ConvexFunctionOn
    rw [hSet]
    exact
      (hConc x).is_linear_preimage
        (helperForProposition_36_4_6_negateScalarSecond_isLinear (m := m))
  have hClosedUpperLevels :
      ∀ α : ℝ, IsClosed (concaveUpperLevelSet (fun uStar : Fin m → ℝ => L uStar x) α) := by
    intro α
    let freezeHeight : (Fin m → ℝ) → (Fin m → ℝ) × ℝ := fun uStar => (uStar, α)
    have hFreezeHeightCont : Continuous freezeHeight := by
      change Continuous (fun uStar : Fin m → ℝ => (uStar, α))
      fun_prop
    have hPreimage :
        freezeHeight ⁻¹' {p : (Fin m → ℝ) × ℝ | (p.2 : EReal) ≤ L p.1 x} =
          concaveUpperLevelSet (fun uStar : Fin m → ℝ => L uStar x) α := by
      ext uStar
      simp [freezeHeight, concaveUpperLevelSet]
    -- The frozen-height embedding reads each upper level set off the fixed-`x` hypograph.
    rw [← hPreimage]
    exact (hUpper x).preimage hFreezeHeightCont
  have hNegLsc :
      LowerSemicontinuous (fun uStar : Fin m → ℝ => -L uStar x) := by
    exact
      (helperForTheorem_6_30_2_closedUpperLevelSet_iff_neg_lsc
        (g := fun uStar : Fin m → ℝ => L uStar x)).1 hClosedUpperLevels
  exact ⟨hConvNeg, hNegLsc⟩

/-- Helper for Theorem 36.5: the conjugate reconstruction
`F(u, x) = sup_{u*} (L(u*, x) - ⟨u*, u⟩)` is convex in the epigraph sense whenever the second
sections of `L` are convex. -/
lemma helperForTheorem_36_5_reconstructedBifunction_isEpigraphConvex
    {m n : ℕ}
    {L : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hConv : IsConvexInSecond (m := m) (n := n) L) :
    IsEpigraphConvexBifunction (m := m) (n := n)
      (fun u : Fin m → ℝ => fun x : Fin n → ℝ =>
        iSup fun uStar : Fin m → ℝ =>
          L uStar x + (-((finDot (n := m) uStar u : ℝ) : EReal))) := by
  intro p hp q hq a b ha hb hab
  rcases p with ⟨⟨u₁, x₁⟩, μ₁⟩
  rcases q with ⟨⟨u₂, x₂⟩, μ₂⟩
  rw [bifunctionEpigraph] at hp hq ⊢
  change
    iSup
        (fun uStar : Fin m → ℝ =>
          L uStar x₁ + (-((finDot (n := m) uStar u₁ : ℝ) : EReal))) ≤
      (μ₁ : EReal) at hp
  change
    iSup
        (fun uStar : Fin m → ℝ =>
          L uStar x₂ + (-((finDot (n := m) uStar u₂ : ℝ) : EReal))) ≤
      (μ₂ : EReal) at hq
  change
    iSup
        (fun uStar : Fin m → ℝ =>
          L uStar (a • x₁ + b • x₂) +
            (-((finDot (n := m) uStar (a • u₁ + b • u₂) : ℝ) : EReal))) ≤
      (((a * μ₁ + b * μ₂ : ℝ)) : EReal)
  refine iSup_le ?_
  intro uStar
  have hpTerm :
      L uStar x₁ + (-((finDot (n := m) uStar u₁ : ℝ) : EReal)) ≤ (μ₁ : EReal) :=
    (iSup_le_iff.mp hp) uStar
  have hqTerm :
      L uStar x₂ + (-((finDot (n := m) uStar u₂ : ℝ) : EReal)) ≤ (μ₂ : EReal) :=
    (iSup_le_iff.mp hq) uStar
  have hpShift :
      L uStar x₁ ≤ (((μ₁ + finDot (n := m) uStar u₁ : ℝ)) : EReal) := by
    have hpSub :
        L uStar x₁ - (((finDot (n := m) uStar u₁ : ℝ)) : EReal) ≤ (μ₁ : EReal) := by
      simpa [sub_eq_add_neg] using hpTerm
    exact
      (EReal.sub_le_iff_le_add
        (a := L uStar x₁)
        (b := (((finDot (n := m) uStar u₁ : ℝ)) : EReal))
        (c := (μ₁ : EReal))
        (Or.inl (by simp)) (Or.inl (by simp))).1 hpSub
  have hqShift :
      L uStar x₂ ≤ (((μ₂ + finDot (n := m) uStar u₂ : ℝ)) : EReal) := by
    have hqSub :
        L uStar x₂ - (((finDot (n := m) uStar u₂ : ℝ)) : EReal) ≤ (μ₂ : EReal) := by
      simpa [sub_eq_add_neg] using hqTerm
    exact
      (EReal.sub_le_iff_le_add
        (a := L uStar x₂)
        (b := (((finDot (n := m) uStar u₂ : ℝ)) : EReal))
        (c := (μ₂ : EReal))
        (Or.inl (by simp)) (Or.inl (by simp))).1 hqSub
  have hpMem :
      ((x₁, μ₁ + finDot (n := m) uStar u₁) :
        (Fin n → ℝ) × ℝ) ∈ {p : (Fin n → ℝ) × ℝ | L uStar p.1 ≤ (p.2 : EReal)} := by
    simpa using hpShift
  have hqMem :
      ((x₂, μ₂ + finDot (n := m) uStar u₂) :
        (Fin n → ℝ) × ℝ) ∈ {p : (Fin n → ℝ) × ℝ | L uStar p.1 ≤ (p.2 : EReal)} := by
    simpa using hqShift
  have hcomboMem :
      ((a • x₁ + b • x₂,
          a * (μ₁ + finDot (n := m) uStar u₁) +
            b * (μ₂ + finDot (n := m) uStar u₂)) :
        (Fin n → ℝ) × ℝ) ∈
          {p : (Fin n → ℝ) × ℝ | L uStar p.1 ≤ (p.2 : EReal)} :=
    hConv uStar hpMem hqMem ha hb hab
  have hcombo :
      L uStar (a • x₁ + b • x₂) ≤
        (((a * (μ₁ + finDot (n := m) uStar u₁) +
            b * (μ₂ + finDot (n := m) uStar u₂) : ℝ)) : EReal) := by
    simpa using hcomboMem
  have hdot :
      finDot (n := m) uStar (a • u₁ + b • u₂) =
        a * finDot (n := m) uStar u₁ + b * finDot (n := m) uStar u₂ := by
    exact helperForProposition_36_4_6_finDot_smul_add_right uStar u₁ u₂ a b
  have hshifted :
      L uStar (a • x₁ + b • x₂) ≤
        (((a * μ₁ + b * μ₂ + finDot (n := m) uStar (a • u₁ + b • u₂) : ℝ)) : EReal) := by
    have hEq :
        a * (μ₁ + finDot (n := m) uStar u₁) + b * (μ₂ + finDot (n := m) uStar u₂) =
          a * μ₁ + b * μ₂ + finDot (n := m) uStar (a • u₁ + b • u₂) := by
      rw [hdot]
      ring
    simpa [hEq] using hcombo
  have hSub :
      L uStar (a • x₁ + b • x₂) -
          (((finDot (n := m) uStar (a • u₁ + b • u₂) : ℝ)) : EReal) ≤
        (((a * μ₁ + b * μ₂ : ℝ)) : EReal) := by
    exact
      (EReal.sub_le_iff_le_add
        (a := L uStar (a • x₁ + b • x₂))
        (b := (((finDot (n := m) uStar (a • u₁ + b • u₂) : ℝ)) : EReal))
        (c := (((a * μ₁ + b * μ₂ : ℝ)) : EReal))
        (Or.inl (by simp)) (Or.inl (by simp))).2 (by
          simpa [EReal.coe_add, add_assoc, add_comm, add_left_comm] using hshifted)
  simpa [sub_eq_add_neg] using hSub

/-- Helper for Theorem 36.5: the epigraph of the reconstructed conjugate bifunction is the
intersection of the closed fixed-`uStar` slice epigraphs after shifting the height coordinate by
`⟨uStar, u⟩`. -/
lemma helperForTheorem_36_5_reconstructedBifunction_epigraph_eq_iInter_preimages
    {m n : ℕ}
    {L : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    bifunctionEpigraph (m := m) (n := n)
      (fun u : Fin m → ℝ => fun x : Fin n → ℝ =>
        iSup fun uStar : Fin m → ℝ =>
          L uStar x + (-((finDot (n := m) uStar u : ℝ) : EReal))) =
      ⋂ uStar : Fin m → ℝ,
        (fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ =>
          (p.1.2, p.2 + finDot (n := m) uStar p.1.1)) ⁻¹'
          {q : (Fin n → ℝ) × ℝ | L uStar q.1 ≤ (q.2 : EReal)} := by
  ext p
  constructor
  · intro hp
    refine Set.mem_iInter.2 ?_
    intro uStar
    -- Unpack the reconstructed epigraph pointwise and isolate the chosen `uStar` summand.
    change L uStar p.1.2 ≤ (((p.2 + finDot (n := m) uStar p.1.1 : ℝ)) : EReal)
    have hp' :
        iSup
          (fun vStar : Fin m → ℝ =>
            L vStar p.1.2 + (-((finDot (n := m) vStar p.1.1 : ℝ) : EReal))) ≤ (p.2 : EReal) :=
      hp
    have hterm :
        L uStar p.1.2 + (-((finDot (n := m) uStar p.1.1 : ℝ) : EReal)) ≤ (p.2 : EReal) :=
      (iSup_le_iff.mp hp') uStar
    have hsub :
        L uStar p.1.2 - (((finDot (n := m) uStar p.1.1 : ℝ)) : EReal) ≤ (p.2 : EReal) := by
      simpa [sub_eq_add_neg] using hterm
    -- Move the finite pairing term to the right-hand side to land in the fixed-slice epigraph.
    exact
      (EReal.sub_le_iff_le_add
        (a := L uStar p.1.2)
        (b := (((finDot (n := m) uStar p.1.1 : ℝ)) : EReal))
        (c := (p.2 : EReal))
        (Or.inl (by simp)) (Or.inl (by simp))).1 hsub
  · intro hp
    -- Conversely, intersecting all shifted slice epigraphs bounds every summand of the `iSup`.
    change
      iSup
        (fun uStar : Fin m → ℝ =>
          L uStar p.1.2 + (-((finDot (n := m) uStar p.1.1 : ℝ) : EReal))) ≤ (p.2 : EReal)
    refine iSup_le ?_
    intro uStar
    have hu :
        (p.1.2, p.2 + finDot (n := m) uStar p.1.1) ∈
          {q : (Fin n → ℝ) × ℝ | L uStar q.1 ≤ (q.2 : EReal)} :=
      (Set.mem_iInter.1 hp) uStar
    have hu' : L uStar p.1.2 ≤ (((p.2 + finDot (n := m) uStar p.1.1 : ℝ)) : EReal) := by
      simpa using hu
    have hsub :
        L uStar p.1.2 - (((finDot (n := m) uStar p.1.1 : ℝ)) : EReal) ≤ (p.2 : EReal) :=
      (EReal.sub_le_iff_le_add
        (a := L uStar p.1.2)
        (b := (((finDot (n := m) uStar p.1.1 : ℝ)) : EReal))
        (c := (p.2 : EReal))
        (Or.inl (by simp)) (Or.inl (by simp))).2 hu'
    simpa [sub_eq_add_neg] using hsub

/-- Helper for Theorem 36.5: the same conjugate reconstruction has closed epigraph whenever the
second sections of `L` are lower closed. -/
lemma helperForTheorem_36_5_reconstructedBifunction_isEpigraphClosed
    {m n : ℕ}
    {L : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLower : IsLowerClosedInSecond (m := m) (n := n) L) :
    IsEpigraphClosedConvexBifunction (m := m) (n := n)
      (fun u : Fin m → ℝ => fun x : Fin n → ℝ =>
        iSup fun uStar : Fin m → ℝ =>
          L uStar x + (-((finDot (n := m) uStar u : ℝ) : EReal))) := by
  -- Rewrite the reconstructed epigraph as an intersection of shifted fixed-slice epigraphs.
  rw [IsEpigraphClosedConvexBifunction]
  rw [helperForTheorem_36_5_reconstructedBifunction_epigraph_eq_iInter_preimages (L := L)]
  refine isClosed_iInter ?_
  intro uStar
  let shiftHeight : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ) × ℝ :=
    fun p => (p.1.2, p.2 + finDot (n := m) uStar p.1.1)
  have hShiftHeightCont : Continuous shiftHeight := by
    -- The shift keeps the `x`-coordinate and adds the continuous finite pairing term to the
    -- real height.
    have hDotShiftCont :
        Continuous
          (fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ =>
            (p.1.2, p.2 + dotProduct p.1.1 uStar)) := by
      fun_prop
    simpa [shiftHeight, helperForProposition_36_4_6_finDot_eq_dotProduct, dotProduct_comm] using
      hDotShiftCont
  have hClosedSection :
      IsClosed {q : (Fin n → ℝ) × ℝ | L uStar q.1 ≤ (q.2 : EReal)} :=
    hLower uStar
  -- Closedness of each fixed slice survives under the continuous height-shift preimage.
  simpa [shiftHeight] using hClosedSection.preimage hShiftHeightCont

/-- Helper for Theorem 36.5: combining the previous two facts packages the reconstructed
conjugate bifunction as a closed convex bifunction. -/
lemma helperForTheorem_36_5_reconstructedBifunction_closed_convex
    {m n : ℕ}
    {L : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLower : IsLowerClosedInSecond (m := m) (n := n) L)
    (hConv : IsConvexInSecond (m := m) (n := n) L) :
    IsEpigraphConvexBifunction (m := m) (n := n)
      (fun u : Fin m → ℝ => fun x : Fin n → ℝ =>
        iSup fun uStar : Fin m → ℝ =>
          L uStar x + (-((finDot (n := m) uStar u : ℝ) : EReal))) ∧
      IsEpigraphClosedConvexBifunction (m := m) (n := n)
        (fun u : Fin m → ℝ => fun x : Fin n → ℝ =>
          iSup fun uStar : Fin m → ℝ =>
            L uStar x + (-((finDot (n := m) uStar u : ℝ) : EReal))) := by
  refine ⟨?_, ?_⟩
  · exact helperForTheorem_36_5_reconstructedBifunction_isEpigraphConvex
      (L := L) hConv
  · exact helperForTheorem_36_5_reconstructedBifunction_isEpigraphClosed
      (L := L) hLower

/-- Helper for Theorem 36.5: once each fixed-`x` slice of `L` is closed concave, the
Lagrangian of the reconstructed bifunction recovers `L` pointwise by the concave
biconjugation theorem. -/
lemma helperForTheorem_36_5_reconstructedBifunction_recovers_L
    {m n : ℕ}
    {L : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosedSlices :
      ∀ x : Fin n → ℝ, ClosedConcaveFunction (fun uStar : Fin m → ℝ => L uStar x))
    (hProperSlices :
      ∀ x : Fin n → ℝ, ProperConcaveERealFunction (fun uStar : Fin m → ℝ => L uStar x))
    (hFconv : IsEpigraphConvexBifunction (m := m) (n := n)
      (fun u : Fin m → ℝ => fun x : Fin n → ℝ =>
        iSup fun uStar : Fin m → ℝ =>
          L uStar x + (-((finDot (n := m) uStar u : ℝ) : EReal)))) :
    ∀ uStar : Fin m → ℝ, ∀ x : Fin n → ℝ,
      bifunctionLagrangian (m := m) (n := n)
        ⟨(fun u : Fin m → ℝ => fun x : Fin n → ℝ =>
            iSup fun vStar : Fin m → ℝ =>
              L vStar x + (-((finDot (n := m) vStar u : ℝ) : EReal))), hFconv⟩
          uStar x = L uStar x := by
  intro uStar x
  let g : (Fin m → ℝ) → EReal := fun vStar : Fin m → ℝ => L vStar x
  have hgConc : ConcaveFunction g := (hClosedSlices x).1
  have hClosureEq : concaveClosure g = g :=
    (theorem_6_30_1 (g := g) hgConc (hProperSlices x)).1 (hClosedSlices x)
  have hFrecEq :
      ∀ u : Fin m → ℝ,
        (iSup fun vStar : Fin m → ℝ =>
          L vStar x + (-((finDot (n := m) vStar u : ℝ) : EReal))) =
            -concaveConjugate g u := by
    intro u
    -- Rewrite the defining supremum as the Fenchel conjugate of `-g` evaluated at `-u`.
    calc
      (iSup fun vStar : Fin m → ℝ =>
        L vStar x + (-((finDot (n := m) vStar u : ℝ) : EReal)))
          =
        fenchelConjugate m (fun vStar : Fin m → ℝ => -g vStar) (-u) := by
            rw [fenchelConjugate_eq_iSup]
            refine iSup_congr ?_
            intro vStar
            simp [g, helperForProposition_36_4_6_finDot_eq_dotProduct, dotProduct_comm,
              sub_eq_add_neg, dotProduct_neg, add_comm]
      _ = -concaveConjugate g u := by
            have hSign :=
              helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
                (g := g) (xStar := u)
            simpa using (congrArg Neg.neg hSign).symm
  have hInvEq :
      bifunctionInverse
        (fun u : Fin m → ℝ => fun x : Fin n → ℝ =>
          iSup fun vStar : Fin m → ℝ =>
            L vStar x + (-((finDot (n := m) vStar u : ℝ) : EReal))) x =
        concaveConjugate g := by
    funext u
    rw [bifunctionInverse, hFrecEq]
    simp
  -- The Lagrangian becomes the concave biconjugate of the fixed slice `g`.
  calc
    bifunctionLagrangian (m := m) (n := n)
        ⟨(fun u : Fin m → ℝ => fun x : Fin n → ℝ =>
            iSup fun vStar : Fin m → ℝ =>
              L vStar x + (-((finDot (n := m) vStar u : ℝ) : EReal))), hFconv⟩ uStar x
        =
      iInf (fun u : Fin m → ℝ => ((finDot (n := m) uStar u : ℝ) : EReal) + (-concaveConjugate g u)) := by
          simp [bifunctionLagrangian, hFrecEq]
    _ = infPairing (m := m) uStar (concaveConjugate g) := by
          simp [infPairing]
    _ = concaveConjugate (concaveConjugate g) uStar := by
          exact helperForProposition_36_4_6_infPairing_eq_concaveConjugate
            (uStar := uStar) (g := concaveConjugate g)
    _ = concaveClosure g uStar := by
          simpa using congrFun
            (concaveConjugate_biconjugate_eq_concaveClosure (g := g) hgConc) uStar
    _ = g uStar := by
          simpa using congrFun hClosureEq uStar
    _ = L uStar x := rfl


end Section36
end Chap07
