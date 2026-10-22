/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part21

section Chap07
section Section33

attribute [local instance] Classical.propDecidable

theorem isFullyClosedSaddleFunction_iff_isLowerClosedSaddleFunction_and_isUpperClosedSaddleFunction :
    ∀ {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
      IsFullyClosedSaddleFunction K →
        IsLowerClosedSaddleFunction K ∧ IsUpperClosedSaddleFunction K :=
  fun {m n} {K} => by
    intro hFull
    rcases hFull with hCC | hVC
    · rcases hCC with ⟨hShape, hFirst, hSecond⟩
      rcases
          helperForLemma33_0_43_concaveConvexBranch_packages_lower_and_upper_closed_data
            (K := K) hShape hFirst hSecond with
        ⟨hLower, hUpper⟩
      constructor
      · dsimp [IsLowerClosedSaddleFunction, saddleClosednessPredicates]
        exact Or.inl hLower
      · dsimp [IsUpperClosedSaddleFunction, saddleClosednessPredicates]
        exact Or.inl hUpper
    · rcases hVC with ⟨hShape, hFirst, hSecond⟩
      rcases
          helperForLemma33_0_43_convexConcaveBranch_packages_lower_and_upper_closed_data
            (K := K) hShape hFirst hSecond with
        ⟨hLower, hUpper⟩
      constructor
      · dsimp [IsLowerClosedSaddleFunction, saddleClosednessPredicates]
        exact Or.inr hLower
      · dsimp [IsUpperClosedSaddleFunction, saddleClosednessPredicates]
        exact Or.inr hUpper


/-- Corollary 33.1.2, packaged in its complete convex/concave four-way form. -/
theorem lowerClosedConcaveConvex_and_upperClosedConvexConcave_pairing_correspondence
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsImageClosedConvexBifunction F →
        IsConcaveConvexOn Set.univ Set.univ (convexBifunctionPairing F) ∧
          IsConvexClosedInSecond (convexBifunctionPairing F) ∧
          ∀ u x, convexConjugate (convexBifunctionPairing F u) x = F u x) ∧
      (∀ K : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        IsConcaveConvexOn Set.univ Set.univ K →
        IsConvexClosedInSecond K →
        HasNoTopOrBotValuesBifunction K →
          let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
            fun u x => convexConjugate (K u) x
          IsImageClosedConvexBifunction F ∧
            (∀ u x, F u x = convexConjugate (K u) x) ∧
            ∀ u xStar, convexBifunctionPairing F u xStar = K u xStar) ∧
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsImageClosedConcaveBifunction F →
        IsConvexConcaveOn Set.univ Set.univ (concaveBifunctionPairing F) ∧
          IsConcaveClosedInSecond (concaveBifunctionPairing F) ∧
          ∀ u x, concaveConjugate (concaveBifunctionPairing F u) x = F u x) ∧
      (∀ K : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        IsConvexConcaveOn Set.univ Set.univ K →
        IsConcaveClosedInSecond K →
        HasNoTopOrBotValuesBifunction K →
          let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
            fun u x => concaveConjugate (K u) x
          IsImageClosedConcaveBifunction F ∧
            (∀ u x, F u x = concaveConjugate (K u) x) ∧
            ∀ u xStar, concaveBifunctionPairing F u xStar = K u xStar) := by
  exact closedSaddleFunctions_imageClosedBifunctions_correspondence (m := m) (n := n)

/-- Helper for Corollary33.3.1: the mixed coordinatewise closure identities already force
the announced lower-closedness, upper-closedness, and pointwise order conclusions. -/
lemma helperForCorollary33_3_1_coordinatewise_closure_pair_implies_closedness_and_order
    {m n : ℕ}
    {K Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn Set.univ Set.univ K)
    (hKbar : IsConcaveConvexOn Set.univ Set.univ Kbar)
    (hPair : Kbar = concaveClosureInFirst K ∧ convexClosureInSecond Kbar = K) :
    IsLowerClosedSaddleFunction K ∧
      IsUpperClosedSaddleFunction Kbar ∧
        ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ), K u xStar ≤ Kbar u xStar := by
  rcases hPair with ⟨hFirst, hSecond⟩
  -- Step 1: reuse the earlier closure-pair lemmas to recover the two fixed-point identities
  -- and the pointwise comparison already contained in the textbook hypotheses.
  have hLowerComp :
      convexClosureInSecond (concaveClosureInFirst K) = K :=
    helperForCorollary33_3_1_coordinatewise_closure_pair_implies_lowerClosureComposition
      (K := K) (Kbar := Kbar) hFirst hSecond
  have hUpperComp :
      concaveClosureInFirst (convexClosureInSecond Kbar) = Kbar :=
    helperForCorollary33_3_1_coordinatewise_closure_pair_implies_upperClosureComposition
      (K := K) (Kbar := Kbar) hFirst hSecond
  have hOrder :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ), K u xStar ≤ Kbar u xStar :=
    helperForCorollary33_3_1_coordinatewise_closure_pair_implies_pointwise_le
      (K := K) (Kbar := Kbar) hFirst hSecond
  -- Step 2: package the recovered first fixed-point identity into the lower-closedness
  -- predicate by using its concave-convex branch.
  have hLower : IsLowerClosedSaddleFunction K := by
    dsimp [IsLowerClosedSaddleFunction, saddleClosednessPredicates]
    exact Or.inl ⟨hK, hLowerComp⟩
  -- Step 3: package the recovered second fixed-point identity into the upper-closedness
  -- predicate for `Kbar`, again on the concave-convex branch.
  have hUpper : IsUpperClosedSaddleFunction Kbar := by
    dsimp [IsUpperClosedSaddleFunction, saddleClosednessPredicates]
    exact Or.inl ⟨hKbar, hUpperComp⟩
  exact ⟨hLower, hUpper, hOrder⟩


/-- Helper for Corollary33.3.1: the closure-pair identities already force the primal kernel to
be convex-closed in the second variable. This is the exact kernel-side input needed for the
Section 33 image-closed reconstruction, independent of any graph-closed witness theorem. -/
lemma helperForCorollary33_3_1_coordinatewise_closure_pair_implies_secondClosed
    {m n : ℕ}
    {K Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hPair : Kbar = concaveClosureInFirst K ∧ convexClosureInSecond Kbar = K) :
    IsConvexClosedInSecond K := by
  rcases hPair with ⟨_hFirst, hSecond⟩
  funext u xStar
  calc
    K u xStar = convexClosureInSecond Kbar u xStar := by
      simpa using (congrArg (fun H => H u xStar) hSecond).symm
    _ = convexClosureInSecond (convexClosureInSecond Kbar) u xStar := by
      symm
      exact helperForCorollary33_1_1_convexClosureInSecond_idempotent
        (K := Kbar) (u := u) (v := xStar)
    _ = convexClosureInSecond K u xStar := by
      simpa using congrArg (fun H => H u xStar) (congrArg convexClosureInSecond hSecond)

/-- Helper for Corollary33.3.1: once the closure pair is known and `K` avoids `⊤, ⊥`, the
Section 33 image-closed correspondence already reconstructs the canonical convex witness and its
primal pairing formula. The only remaining extra input for the fully closed witness package is the
graph-function closedness bridge handled separately later. -/
lemma helperForCorollary33_3_1_imageClosedWitness_of_coordinatewise_closure_pair_of_noTopOrBot
    {m n : ℕ}
    {K Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn Set.univ Set.univ K)
    (hPair : Kbar = concaveClosureInFirst K ∧ convexClosureInSecond Kbar = K)
    (hNoTopBot : HasNoTopOrBotValuesBifunction K) :
    let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => convexConjugate (K u) x
    IsImageClosedConvexBifunction F ∧
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
        convexBifunctionPairing F u xStar = K u xStar := by
  let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => convexConjugate (K u) x
  have hNoBot : HasNoBotValuesBifunction K := hNoTopBot.1
  have hSecondClosed : IsConvexClosedInSecond K :=
    helperForCorollary33_3_1_coordinatewise_closure_pair_implies_secondClosed
      (K := K) (Kbar := Kbar) hPair
  have hImageReverse :=
    (closedSaddleFunctions_imageClosedBifunctions_correspondence
      (m := m) (n := n)).2.1 K hK hSecondClosed hNoTopBot
  refine ⟨?_, ?_⟩
  · simpa [F] using hImageReverse.1
  · simpa [F] using hImageReverse.2.2


/-- Helper for Corollary33.3.1: on the zero-dimensional space, a bifunction with no `⊥`
values cannot have primal pairing `⊤` at the unique point. -/
lemma helperForCorollary33_3_1_zeroDimensional_pairing_ne_top_of_noBot
    {F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal}
    (hNoBot : HasNoBotValuesBifunction F) :
    convexBifunctionPairing F 0 0 ≠ (⊤ : EReal) := by
  -- Step 1: the zero-dimensional supremum defining the primal pairing has only one term.
  rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
  have hCollapse :
      iSup (fun x : Fin 0 → ℝ => (((dotProduct x (0 : Fin 0 → ℝ) : ℝ) : EReal) - F 0 x)) =
        (((dotProduct (0 : Fin 0 → ℝ) (0 : Fin 0 → ℝ) : ℝ) : EReal) - F 0 0) := by
    apply le_antisymm
    · refine iSup_le ?_
      intro x
      have hx : x = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
      rw [hx]
    · exact
        le_iSup
          (fun x : Fin 0 → ℝ => (((dotProduct x (0 : Fin 0 → ℝ) : ℝ) : EReal) - F 0 x))
          0
  rw [hCollapse]
  -- Step 2: the unique affine term is not `⊤` because the section value avoids `⊥`.
  have hNeg_ne_top : -(F 0 0) ≠ (⊤ : EReal) := by
    simpa using hNoBot 0 0
  have hSum_ne_top :
      (((dotProduct (0 : Fin 0 → ℝ) (0 : Fin 0 → ℝ) : ℝ) : EReal) + -(F 0 0)) ≠
        (⊤ : EReal) := by
    exact EReal.add_ne_top (EReal.coe_ne_top _) hNeg_ne_top
  simpa [sub_eq_add_neg] using hSum_ne_top

/-- Helper for Corollary33.3.1: the singleton constant-`⊤` kernel satisfies the closure-pair
side, but the witness-side primal pairing equation is already impossible under
`HasNoBotValuesBifunction`. -/
lemma helperForCorollary33_3_1_zeroDimensional_constTop_counterexample :
    let K : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal := fun _ _ => (⊤ : EReal)
    (K = concaveClosureInFirst K ∧ convexClosureInSecond K = K) ∧
      ¬ ∃ F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
          HasNoBotValuesBifunction F ∧
            (∀ (u : Fin 0 → ℝ) (xStar : Fin 0 → ℝ), K u xStar = convexBifunctionPairing F u xStar) := by
  intro K
  refine ⟨?_, ?_⟩
  · constructor
    · -- Step 1: every first-variable ball contains the unique point, so the first closure
      -- stays constantly `⊤`.
      funext u xStar
      unfold concaveClosureInFirst
      change
        (⊤ : EReal) =
          ⨅ (ε : {ε : ℝ // 0 < ε}),
            ⨆ (w : {w : Fin 0 → ℝ // ‖w - u‖ < ε.1}), K w.1 xStar
      apply le_antisymm
      · refine le_iInf ?_
        intro ε
        refine le_iSup (fun w : {w : Fin 0 → ℝ // ‖w - u‖ < ε.1} => K w.1 xStar) ?_
        refine ⟨u, ?_⟩
        simpa using ε.2
      · exact le_top
    · -- Step 2: the same singleton-ball argument fixes the second closure as well.
      funext u xStar
      unfold convexClosureInSecond
      change
        (⨆ (ε : {ε : ℝ // 0 < ε}),
          ⨅ (w : {w : Fin 0 → ℝ // ‖w - xStar‖ < ε.1}), K u w.1) =
            (⊤ : EReal)
      apply le_antisymm
      · exact le_top
      have hε : (0 : ℝ) < 1 := by
        norm_num
      calc
        (⊤ : EReal) ≤ ⨅ (w : {w : Fin 0 → ℝ // ‖w - xStar‖ < (1 : ℝ)}), K u w.1 := by
          refine le_iInf ?_
          intro w
          simp [K]
        _ ≤
            ⨆ (ε : {ε : ℝ // 0 < ε}),
              ⨅ (w : {w : Fin 0 → ℝ // ‖w - xStar‖ < ε.1}), K u w.1 := by
                exact
                  le_iSup
                    (fun ε : {ε : ℝ // 0 < ε} =>
                      ⨅ (w : {w : Fin 0 → ℝ // ‖w - xStar‖ < ε.1}), K u w.1)
                    ⟨1, hε⟩
  · -- Step 3: any claimed witness would force the unique primal pairing value to equal `⊤`,
    -- contradicting the zero-dimensional no-`⊥` pairing bound.
    intro hExists
    rcases hExists with ⟨F, hNoBot, hPairing⟩
    have hEq : (⊤ : EReal) = convexBifunctionPairing F 0 0 := by
      simpa [K] using hPairing 0 0
    exact
      helperForCorollary33_3_1_zeroDimensional_pairing_ne_top_of_noBot
        (F := F) hNoBot hEq.symm

/-- Helper for Corollary33.3.1: in dimension zero, the primal pairing is just the negation
of the unique bifunction value. -/
lemma helperForCorollary33_3_1_zeroDimensional_pairing_eq_neg_value
    (F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal) :
    convexBifunctionPairing F 0 0 = -(F 0 0) := by
  -- Step 1: collapse the defining supremum to the unique zero-dimensional point.
  rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
  have hCollapse :
      iSup (fun x : Fin 0 → ℝ => (((dotProduct x (0 : Fin 0 → ℝ) : ℝ) : EReal) - F 0 x)) =
        (((dotProduct (0 : Fin 0 → ℝ) (0 : Fin 0 → ℝ) : ℝ) : EReal) - F 0 0) := by
    apply le_antisymm
    · refine iSup_le ?_
      intro x
      have hx : x = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
      rw [hx]
    · exact
        le_iSup
          (fun x : Fin 0 → ℝ => (((dotProduct x (0 : Fin 0 → ℝ) : ℝ) : EReal) - F 0 x))
          0
  rw [hCollapse]
  -- Step 2: the remaining dot product vanishes.
  simp

/-- Helper for Corollary33.3.1: in dimension zero, the corrected adjoint pairing has the
same sign as the primal pairing. -/
lemma helperForCorollary33_3_1_zeroDimensional_adjointPairing_eq_neg_value
    (F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal) :
    convexBifunctionCanonicalAdjointPairing F 0 0 = -(F 0 0) := by
  -- Step 1: rewrite the adjoint pairing as the one-point infimum of the fixed-dual adjoint
  -- section, whose value is already controlled by the primal pairing formula above.
  rw [convexBifunctionCanonicalAdjointPairing, helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
  have hPairCollapse :
      ∀ uStar : Fin 0 → ℝ, convexBifunctionAdjointPairing F 0 uStar = F 0 0 := by
    intro uStar
    have huStar : uStar = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
    rw [huStar, convexBifunctionAdjointPairing,
      helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
    have hAll :
        ∀ u : Fin 0 → ℝ, convexBifunctionPairing F u 0 = -(F 0 0) := by
      intro u
      have hu : u = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
      rw [hu]
      exact helperForCorollary33_3_1_zeroDimensional_pairing_eq_neg_value F
    simp_rw [hAll]
    simp
  simp_rw [hPairCollapse]
  -- Step 2: the remaining infimum again has only one term.
  have hCollapse :
      iInf (fun uStar : Fin 0 → ℝ =>
        (((dotProduct uStar (0 : Fin 0 → ℝ) : ℝ) : EReal) + -(F 0 0))) =
        ((((dotProduct (0 : Fin 0 → ℝ) (0 : Fin 0 → ℝ) : ℝ) : EReal) + -(F 0 0))) := by
    apply le_antisymm
    · exact
        iInf_le
          (fun uStar : Fin 0 → ℝ =>
            (((dotProduct uStar (0 : Fin 0 → ℝ) : ℝ) : EReal) + -(F 0 0)))
          0
    · refine le_iInf ?_
      intro uStar
      have huStar : uStar = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
      rw [huStar]
  rw [hCollapse]
  simp

/-- Helper for Corollary33.3.1: the zero-dimensional constant-`⊤` pair satisfies the
coordinatewise closure identities, but no closed convex bifunction can realize both pairing
identities simultaneously. -/
lemma helperForCorollary33_3_1_zeroDimensional_constTop_closedConvex_counterexample :
    let K : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal := fun _ _ => (⊤ : EReal)
    (K = concaveClosureInFirst K ∧ convexClosureInSecond K = K) ∧
      ¬ ∃ F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
          ClosedConvexBifunction F ∧
            HasNoBotValuesBifunction F ∧
            (∀ (u : Fin 0 → ℝ) (xStar : Fin 0 → ℝ),
              K u xStar = convexBifunctionPairing F u xStar) ∧
            ∀ (u : Fin 0 → ℝ) (xStar : Fin 0 → ℝ),
              K u xStar = convexBifunctionCanonicalAdjointPairing F xStar u := by
  intro K
  refine ⟨?_, ?_⟩
  · -- Step 1: reuse the already-proved mixed-closure computation for the constant-`⊤` kernel.
    simpa [K] using (helperForCorollary33_3_1_zeroDimensional_constTop_counterexample).1
  · intro hExists
    rcases hExists with ⟨F, _hClosed, hNoBot, hPair, _hAdj⟩
    -- Step 2: specialize the two pairing identities at the unique point.
    have hTopPair : (⊤ : EReal) = convexBifunctionPairing F 0 0 := by
      simpa [K] using hPair 0 0
    exact
      helperForCorollary33_3_1_zeroDimensional_pairing_ne_top_of_noBot
        (F := F) hNoBot hTopPair.symm



/-- Corollary33.3.1, sound forward direction: a unique closed convex witness gives the
canonical coordinatewise closure pair. -/
theorem closed_convex_bifunction_exists_implies_coordinatewise_closure_pair :
    ∀ {m n : ℕ} {K Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
      (∃! F,
          ClosedConvexBifunction F ∧
            HasNoBotValuesBifunction F ∧
            (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
              K u xStar = convexBifunctionPairing F u xStar) ∧
              ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
                Kbar u xStar = convexBifunctionCanonicalAdjointPairing F xStar u) →
        Kbar = canonicalConcaveClosureInFirst K ∧
          canonicalConvexClosureInSecond Kbar = K := by
  intro m n K Kbar hExists
  rcases hExists with ⟨F, hF, -⟩
  rcases hF with ⟨hClosed, hNoBot, hPair, hAdj⟩
  exact
    helperForCorollary33_3_1_coordinatewise_closure_pair_of_closedConvexWitness
      (K := K) (Kbar := Kbar) (F := F) hClosed hNoBot hPair hAdj

/-- Helper for Corollary33.3.2: an upper semicontinuous section is already fixed by the
one-variable Section 33 concave closure. -/
lemma helperForCorollary33_3_2_functionConcaveClosure_eq_self_of_upperSemicontinuous
    {m : ℕ}
    {g : (Fin m → ℝ) → EReal}
    (hUpper : UpperSemicontinuous g) :
    functionConcaveClosure g = g := by
  -- Step 1: convert upper semicontinuity of `g` into lower semicontinuity of `-g`.
  have hNegLsc : LowerSemicontinuous (fun u => -g u) :=
    (helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg
      (g := g)).1 hUpper
  -- Step 2: the one-variable convex closure therefore fixes the negated section.
  have hNegClosed :
      (fun u => -g u) = functionConvexClosure (fun u' => -g u') :=
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hNegLsc
  -- Step 3: rewrite the Section 33 concave closure through the sign-flip identity and
  -- simplify pointwise.
  funext u
  have hPoint :
      functionConvexClosure (fun u' => -g u') u = -g u :=
    congrArg (fun h => h u) hNegClosed.symm
  calc
    functionConcaveClosure g u
        = -functionConvexClosure (fun u' => -g u') u := by
            exact
              congrArg (fun h => h u)
                (helperForCorollary33_2_1_functionConcaveClosure_eq_neg_functionConvexClosure_neg
                  (g := g))
    _ = -(-g u) := by rw [hPoint]
    _ = g u := by simp

/-- Helper for Corollary33.3.2: sectionwise upper semicontinuity in the first variable forces
the first-variable concave closure to fix the kernel. -/
lemma helperForCorollary33_3_2_concaveClosureInFirst_eq_self_of_sectionUpperSemicontinuous
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hUpper : ∀ xStar : Fin n → ℝ, UpperSemicontinuous (fun u => K u xStar)) :
    concaveClosureInFirst K = K := by
  -- Step 1: freeze the second variable and apply the one-variable fixed-point theorem to the
  -- resulting section.
  funext u xStar
  have hSectionClosed :
      functionConcaveClosure (fun u' => K u' xStar) = fun u' => K u' xStar :=
    helperForCorollary33_3_2_functionConcaveClosure_eq_self_of_upperSemicontinuous
      (g := fun u' => K u' xStar) (hUpper xStar)
  -- Step 2: identify the kernel closure with the frozen section closure at `(u, xStar)`.
  simpa [concaveClosureInFirst, functionConcaveClosure] using
    congrArg (fun h => h u) hSectionClosed

/-- Helper for Corollary33.3.2: sectionwise lower semicontinuity in the second variable forces
the second-variable convex closure to fix the kernel. -/
lemma helperForCorollary33_3_2_convexClosureInSecond_eq_self_of_sectionLowerSemicontinuous
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLower : ∀ u : Fin m → ℝ, LowerSemicontinuous (fun xStar => K u xStar)) :
    convexClosureInSecond K = K := by
  -- Step 1: freeze the first variable and use the standard lower-semicontinuous fixed-point
  -- theorem for the one-variable Section 33 convex closure.
  funext u xStar
  have hSectionClosed :
      (fun xStar' => K u xStar') = functionConvexClosure (fun xStar' => K u xStar') :=
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous (hLower u)
  have hPoint :
      functionConvexClosure (fun xStar' => K u xStar') xStar = K u xStar :=
    congrArg (fun h => h xStar) hSectionClosed.symm
  -- Step 2: translate the one-variable closure equality back to the kernel notation.
  simpa [convexClosureInSecond, functionConvexClosure] using hPoint

/-- Helper for Corollary33.3.2: a simultaneously convex-and-concave section with one `⊥`
value must be identically `⊥`. -/
lemma helperForCorollary33_3_2_section_eq_bot_everywhere_of_exists_bot
    {m : ℕ}
    {g : (Fin m → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin m → ℝ)) g)
    {u0 : Fin m → ℝ}
    (hu0 : g u0 = ⊥) :
    ∀ u : Fin m → ℝ, g u = ⊥ := by
  intro u
  let z : Fin m → ℝ := fun i => 2 * u i - u0 i
  -- Step 1: write `u` as the midpoint of the `⊥` witness `u0` and its reflection `z`.
  have huEq : u = (1 / 2 : ℝ) • u0 + (1 / 2 : ℝ) • z := by
    ext i
    simp [z, smul_eq_mul]
    ring
  -- Step 2: convexity bounds the midpoint value by the weighted average, which already
  -- collapses to `⊥` because one endpoint is exactly `⊥`.
  have hLe :
      g u ≤ ((1 / 2 : ℝ) : EReal) * g u0 + ((1 / 2 : ℝ) : EReal) * g z := by
    have hMid :=
      hConv (x := u0) (y := z) (by simp) (by simp)
        (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num)
        (by simp)
    simpa [huEq] using hMid
  have hLeBot : g u ≤ (⊥ : EReal) := by
    simpa [hu0, EReal.coe_mul_bot_of_pos] using hLe
  exact le_bot_iff.mp hLeBot

/-- Helper for Corollary33.3.2: once `⊥` is excluded, a simultaneously convex-and-concave
section with one `⊤` value must be identically `⊤`. -/
lemma helperForCorollary33_3_2_section_eq_top_everywhere_of_exists_top
    {m : ℕ}
    {g : (Fin m → ℝ) → EReal}
    (hConc : IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) g)
    (hNoBot : ∀ u : Fin m → ℝ, g u ≠ ⊥)
    {u0 : Fin m → ℝ}
    (hu0 : g u0 = ⊤) :
    ∀ u : Fin m → ℝ, g u = ⊤ := by
  intro u
  let z : Fin m → ℝ := fun i => 2 * u i - u0 i
  -- Step 1: again express `u` as the midpoint of the `⊤` witness and its reflection.
  have huEq : u = (1 / 2 : ℝ) • u0 + (1 / 2 : ℝ) • z := by
    ext i
    simp [z, smul_eq_mul]
    ring
  -- Step 2: concavity gives a lower bound by the weighted average. Since `⊥` never occurs,
  -- the `⊤` endpoint forces that weighted average to stay equal to `⊤`.
  have hLe :
      ((1 / 2 : ℝ) : EReal) * g u0 + ((1 / 2 : ℝ) : EReal) * g z ≤ g u := by
    have hMid :=
      hConc (x := u0) (y := z) (by simp) (by simp)
        (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num)
        (by simp)
    simpa [huEq] using hMid
  have hzNeBot : g z ≠ ⊥ := hNoBot z
  have hHalfTop : (((1 / 2 : ℝ) : EReal) * g u0) = ⊤ := by
    simpa [hu0] using
      (EReal.mul_top_of_pos
        (show (0 : EReal) < (((1 / 2 : ℝ) : EReal)) by norm_num))
  have hHalfZNeBot : (((1 / 2 : ℝ) : EReal) * g z) ≠ ⊥ := by
    simpa using
      helperForLemma33_0_5_positiveReal_mul_ne_bot
        (a := (1 / 2 : ℝ)) (by norm_num) hzNeBot
  have hTopLe : (⊤ : EReal) ≤ g u := by
    calc
      (⊤ : EReal)
          = (((1 / 2 : ℝ) : EReal) * g u0) + (((1 / 2 : ℝ) : EReal) * g z) := by
              rw [hHalfTop]
              exact (EReal.top_add_of_ne_bot hHalfZNeBot).symm
      _ ≤ g u := hLe
  exact top_le_iff.mp hTopLe

/-- Helper for Corollary33.3.2: a one-variable section that is both convex and concave on all of
`ℝ^m` is automatically both upper and lower semicontinuous. -/
lemma helperForCorollary33_3_2_upperLowerSemicontinuous_of_simultaneousConvexConcave
    {m : ℕ}
    {g : (Fin m → ℝ) → EReal}
    (hConc : IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) g)
    (hConv : IsERealConvexOn (Set.univ : Set (Fin m → ℝ)) g) :
    UpperSemicontinuous g ∧ LowerSemicontinuous g := by
  by_cases hBot : ∃ u0 : Fin m → ℝ, g u0 = ⊥
  · rcases hBot with ⟨u0, hu0⟩
    have hConstBot :
        ∀ u : Fin m → ℝ, g u = ⊥ :=
      helperForCorollary33_3_2_section_eq_bot_everywhere_of_exists_bot
        (g := g) hConv hu0
    have hConstBotFun : g = fun _ : Fin m → ℝ => (⊥ : EReal) := by
      funext u
      exact hConstBot u
    have hNegConst :
        (fun u : Fin m → ℝ => -g u) = fun _ : Fin m → ℝ => (⊤ : EReal) := by
      funext u
      rw [hConstBot u]
      simp
    -- Step 1: on the constant-`⊥` branch, both semicontinuity statements are immediate.
    constructor
    · have hNegLower :
          LowerSemicontinuous (fun u : Fin m → ℝ => -g u) := by
        simpa [hNegConst] using
          (lowerSemicontinuous_const :
            LowerSemicontinuous (fun _ : Fin m → ℝ => (⊤ : EReal)))
      exact
        (helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg
          (g := g)).2 hNegLower
    · simpa [hConstBotFun] using
        (lowerSemicontinuous_const :
          LowerSemicontinuous (fun _ : Fin m → ℝ => (⊥ : EReal)))
  · have hNoBot : ∀ u : Fin m → ℝ, g u ≠ ⊥ := by
      intro u hu
      exact hBot ⟨u, hu⟩
    by_cases hTop : ∃ u0 : Fin m → ℝ, g u0 = ⊤
    · rcases hTop with ⟨u0, hu0⟩
      have hConstTop :
          ∀ u : Fin m → ℝ, g u = ⊤ :=
        helperForCorollary33_3_2_section_eq_top_everywhere_of_exists_top
          (g := g) hConc hNoBot hu0
      have hConstTopFun : g = fun _ : Fin m → ℝ => (⊤ : EReal) := by
        funext u
        exact hConstTop u
      have hNegConst :
          (fun u : Fin m → ℝ => -g u) = fun _ : Fin m → ℝ => (⊥ : EReal) := by
        funext u
        rw [hConstTop u]
        simp
      -- Step 2: if `⊤` occurs and `⊥` does not, the section is constant `⊤`, so both
      -- semicontinuity statements again reduce to the constant case.
      constructor
      · have hNegLower :
            LowerSemicontinuous (fun u : Fin m → ℝ => -g u) := by
          simpa [hNegConst] using
            (lowerSemicontinuous_const :
              LowerSemicontinuous (fun _ : Fin m → ℝ => (⊥ : EReal)))
        exact
          (helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg
            (g := g)).2 hNegLower
      · simpa [hConstTopFun] using
          (lowerSemicontinuous_const :
            LowerSemicontinuous (fun _ : Fin m → ℝ => (⊤ : EReal)))
    · have hNoTop : ∀ u : Fin m → ℝ, g u ≠ ⊤ := by
        intro u hu
        exact hTop ⟨u, hu⟩
      have hConvFun : ConvexFunction g :=
        helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hConv
      have hHypographConvex :
          Convex ℝ
            {p : (Fin m → ℝ) × ℝ |
              p.1 ∈ (Set.univ : Set (Fin m → ℝ)) ∧ ((p.2 : EReal) ≤ g p.1)} := by
        -- Step 3: the concavity inequality is exactly the convexity of the hypograph.
        refine (convex_iff_forall_pos).2 ?_
        intro p hp q hq s t hs ht hst
        constructor
        · simp
        have hpLe : ((p.2 : ℝ) : EReal) ≤ g p.1 := hp.2
        have hqLe : ((q.2 : ℝ) : EReal) ≤ g q.1 := hq.2
        have hWeighted :
            (((s • p + t • q).2 : ℝ) : EReal) ≤
              ((s : ℝ) : EReal) * g p.1 + ((t : ℝ) : EReal) * g q.1 := by
          calc
            (((s • p + t • q).2 : ℝ) : EReal)
                =
                  ((s : ℝ) : EReal) * ((p.2 : ℝ) : EReal) +
                    ((t : ℝ) : EReal) * ((q.2 : ℝ) : EReal) := by
                        simp [smul_eq_mul, EReal.coe_add, EReal.coe_mul]
            _ ≤ ((s : ℝ) : EReal) * g p.1 + ((t : ℝ) : EReal) * g q.1 := by
                  exact add_le_add
                    (mul_le_mul_of_nonneg_left hpLe
                      (by exact_mod_cast (le_of_lt hs)))
                    (mul_le_mul_of_nonneg_left hqLe
                      (by exact_mod_cast (le_of_lt ht)))
        have hConcSeg :
            ((s : ℝ) : EReal) * g p.1 + ((t : ℝ) : EReal) * g q.1 ≤
              g (s • p.1 + t • q.1) :=
          hConc (x := p.1) (y := q.1) (by simp) (by simp)
            (le_of_lt hs) (le_of_lt ht) hst (by simp)
        calc
          (((s • p + t • q).2 : ℝ) : EReal)
              ≤ ((s : ℝ) : EReal) * g p.1 + ((t : ℝ) : EReal) * g q.1 := hWeighted
          _ ≤ g (s • p.1 + t • q.1) := hConcSeg
      have hAffine :
          AffineFunctionOn (Set.univ : Set (Fin m → ℝ)) g := by
        -- Step 4: after excluding both infinite values, simultaneous convexity and concavity
        -- identify `g` as a finite affine function.
        refine ⟨?_, ?_, hHypographConvex⟩
        · intro u hu
          exact ⟨hNoBot u, hNoTop u⟩
        · simpa [ConvexFunction] using hConvFun
      rcases affineFunctionOn_univ_exists_inner_add_const (f := g) hAffine with
        ⟨a, α, hRep⟩
      let r : (Fin m → ℝ) → ℝ := fun u => Finset.univ.sum (fun i => u i * a i) + α
      have hRepFun : g = fun u : Fin m → ℝ => ((r u : ℝ) : EReal) := by
        funext u
        simpa [r] using hRep u
      have hCont : Continuous r := by
        -- Step 5: the affine real representative is continuous, hence both semicontinuous
        -- after coercion to `EReal`.
        refine (continuous_finset_sum (s := Finset.univ) ?_).add continuous_const
        intro i hi
        exact (continuous_apply i).mul continuous_const
      have hLower : LowerSemicontinuous g := by
        have hLowerCoe :
            LowerSemicontinuous (fun u : Fin m → ℝ => ((r u : ℝ) : EReal)) :=
          lowerSemicontinuous_coe_real_toEReal hCont.lowerSemicontinuous
        simpa [hRepFun] using hLowerCoe
      have hUpper : UpperSemicontinuous g := by
        have hNegRep :
            (fun u : Fin m → ℝ => -g u) =
              fun u : Fin m → ℝ => (((-r u : ℝ)) : EReal) := by
          funext u
          rw [hRepFun]
          simp
        have hNegLower : LowerSemicontinuous (fun u : Fin m → ℝ => -g u) := by
          have hLowerNegCoe :
              LowerSemicontinuous (fun u : Fin m → ℝ => (((-r u : ℝ)) : EReal)) :=
            lowerSemicontinuous_coe_real_toEReal hCont.neg.lowerSemicontinuous
          simpa [hNegRep] using hLowerNegCoe
        exact
          (helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg
            (g := g)).2 hNegLower
      exact ⟨hUpper, hLower⟩

/-- Helper for Corollary33.3.2: under the concave-convex hypothesis, the lower-closed
predicate reduces to the aligned identity `cl₂ (cl₁ K) = K`. -/
lemma helperForCorollary33_3_2_simultaneousOrientations_fix_concaveClosureInFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn Set.univ Set.univ K)
    (hVC : IsConvexConcaveOn Set.univ Set.univ K) :
    concaveClosureInFirst K = K := by
  -- Step 1: reduce the kernel-level fixed-point statement to upper semicontinuity of each
  -- frozen first-variable section.
  apply
    helperForCorollary33_3_2_concaveClosureInFirst_eq_self_of_sectionUpperSemicontinuous
      (K := K)
  intro xStar
  have hConcSection :
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u xStar) :=
    hK.1 xStar (by simp)
  have hConvSection :
      IsERealConvexOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u xStar) :=
    hVC.1 xStar (by simp)
  -- Step 2: simultaneous convexity and concavity make the frozen section affine up to the
  -- constant `⊥/⊤` exceptional branches, so it is automatically upper semicontinuous.
  exact
    (helperForCorollary33_3_2_upperLowerSemicontinuous_of_simultaneousConvexConcave
      (g := fun u => K u xStar) hConcSection hConvSection).1


end Section33
end Chap07
