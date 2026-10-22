/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part13
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part16
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part23
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part13
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part16
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part1

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Corollary 37.1.2: Theorem 34.2 already upgrades the Section 34 adjoint to a
graph-function concave-closed bifunction. -/
lemma helperForCorollary_37_1_2_section34Adjoint_graphConcaveClosed
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    IsFunctionConcaveClosed (graphFunctionOfBifunction (section34ConcaveBifunctionAdjoint F)) := by
  exact (hGlobal.qualification F hF).adjoint_graphClosed
/-
  let G := section34ConcaveBifunctionAdjoint F
  let Kpair : SaddleFunction m n := section34ConcaveBifunctionAdjointPairing F
  let Kswap : (Fin n → ℝ) → (Fin m → ℝ) → EReal := fun xStar u => Kpair u xStar
  have hQ := hGlobal.qualification F hF
  have hKernelEq0 := hQ.adjointPairing_eq
  have hKernelInOmega := (section34_theorem34_2 F hF).2.2
  have hKernelData :=
    hQ.closedRepresentativeData (convexBifunctionClosedKernel F) hKernelInOmega
      hQ.canonicalKernel_closed
  have hKernelEq :
      convexBifunctionClosedKernel F = Kpair := by
    simpa [Kpair] using hKernelEq0
  have hKernelPartials :
      partialClosure₁ (convexBifunctionClosedKernel F) = convexBifunctionClosedKernel F ∧
        partialClosure₂ (convexBifunctionClosedKernel F) = convexBifunctionClosedKernel F := by
    -- The canonical Section 34 kernel is already fixed by both mixed partial closures.
    exact ⟨hKernelData.1, hKernelData.2.1⟩
  have hKernelConcaveConvex :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (convexBifunctionClosedKernel F) := by
    -- Closed convex bifunctions produce the canonical concave-convex kernel from Section 33.
    exact
      ((closedSaddleFunctions_imageClosedBifunctions_correspondence
        (m := m) (n := n)).1 F hF).1.1
  have hKernelConcaveClosedInFirst :
      IsConcaveClosedInFirst (convexBifunctionClosedKernel F) := by
    -- Read the first partial-closure fixed-point identity as first-variable concave closedness.
    unfold IsConcaveClosedInFirst
    simpa [partialClosure₁] using hKernelPartials.1.symm
  have hKernelConvexClosedInSecond :
      IsConvexClosedInSecond (convexBifunctionClosedKernel F) := by
    -- Read the second partial-closure fixed-point identity as second-variable convex closedness.
    unfold IsConvexClosedInSecond
    simpa [partialClosure₂] using hKernelPartials.2.symm
  have hKpairConcaveConvex :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) Kpair := by
    rw [← hKernelEq]
    exact hKernelConcaveConvex
  have hKpairConcaveClosedInFirst : IsConcaveClosedInFirst Kpair := by
    rw [← hKernelEq]
    exact hKernelConcaveClosedInFirst
  have hKpairConvexClosedInSecond : IsConvexClosedInSecond Kpair := by
    rw [← hKernelEq]
    exact hKernelConvexClosedInSecond
  have hKswapConvexConcave :
      IsConvexConcaveOn (Set.univ : Set (Fin n → ℝ)) (Set.univ : Set (Fin m → ℝ)) Kswap := by
    -- Swapping the canonical Section 34 kernel flips the saddle orientation.
    simpa [Kswap] using
      helperForCorollary33_1_1_swap_preserves_concaveConvex
        (K := Kpair) hKpairConcaveConvex
  have hKswapConvexClosedInFirst :
      IsConvexClosedInFirst Kswap := by
    -- The swapped kernel inherits first-variable convex closedness from the original
    -- second-variable convex closedness.
    simpa [Kswap] using
      helperForCorollary33_1_1_swap_convexClosedInSecond_to_convexClosedInFirst
        (K := Kpair) hKpairConvexClosedInSecond
  have hKswapConcaveClosedInSecond :
      IsConcaveClosedInSecond Kswap := by
    -- The same swap turns first-variable concave closedness into second-variable concave
    -- closedness.
    simpa [Kswap] using
      helperForCorollary33_1_1_swap_concaveClosedInFirst_to_concaveClosedInSecond
        (K := Kpair) hKpairConcaveClosedInFirst
  have hKswapUpperClosed : IsUpperClosedSaddleFunction Kswap := by
    -- Once both swapped coordinatewise closures are fixed, the Section 33 saddle predicate
    -- upgrades to the upper-closed branch needed for the reverse pairing correspondence.
    have hKswapFullyClosed : IsFullyClosedSaddleFunction Kswap := by
      exact Or.inr ⟨hKswapConvexConcave, hKswapConvexClosedInFirst, hKswapConcaveClosedInSecond⟩
    exact
      (isFullyClosedSaddleFunction_iff_isLowerClosedSaddleFunction_and_isUpperClosedSaddleFunction
        (K := Kswap) hKswapFullyClosed).2
  have hGImageClosed : IsImageClosedConcaveBifunction G :=
    concaveBifunctionAdjoint_isImageClosedConcave F hF
  have hKswapNoTop : HasNoTopValuesBifunction Kswap := by
    -- The forward concave pairing correspondence packages the swapped adjoint kernel as a
    -- no-`⊤` convex-concave kernel.
    simpa [G, Kswap, Kpair, section34ConcaveBifunctionAdjointPairing] using
      ((closedSaddleFunctions_imageClosedBifunctions_correspondence
        (m := n) (n := m)).2.2.1 G hGImageClosed).1.2.2
  have hKpairNoBot : HasNoBotValuesBifunction Kpair := by
    simpa [Kpair, hKernelEq] using
      ((closedSaddleFunctions_imageClosedBifunctions_correspondence
        (m := m) (n := n)).1 F hF).1.2.2
  have hKswapNoBot : HasNoBotValuesBifunction Kswap := by
    intro xStar u
    simpa [Kswap] using hKpairNoBot u xStar
  have hKswapNoTopBot : HasNoTopOrBotValuesBifunction Kswap :=
    ⟨hKswapNoBot, hKswapNoTop⟩
  let Gneg : (Fin n → ℝ) → (Fin m → ℝ) → EReal := fun xStar uStar =>
    convexConjugate (fun u => -Kswap xStar u) uStar
  have hGnegPkg :=
    upperClosed_convexConcave_yields_graphClosed_negatedConvexCanonicalWitness_of_noTopOrBot
      (m := n) (n := m) (K := Kswap)
      hKswapConvexConcave hKswapUpperClosed hKswapNoTopBot
  have hGraphClosedGneg : IsFunctionConvexClosed (graphFunctionOfBifunction Gneg) :=
    hGnegPkg.1.2.2
  let negSecondBlock : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) :=
    fun z => Fin.append (fun i => z (Fin.castAdd m i)) (fun j => -z (Fin.natAdd n j))
  have hNegGraphEq :
      (fun z => -graphFunctionOfBifunction G z) =
        fun z => graphFunctionOfBifunction Gneg (negSecondBlock z) := by
    funext z
    let xStar : Fin n → ℝ := fun i => z (Fin.castAdd m i)
    let uStar : Fin m → ℝ := fun j => z (Fin.natAdd n j)
    have hSliceEq :
        Kswap xStar = fun u => convexBifunctionPairing F u xStar := by
      funext u
      exact (congrArg (fun H : SaddleFunction m n => H u xStar) hKernelEq).symm
    have hConj0 :
        concaveConjugate (Kswap xStar) uStar =
          -convexConjugate (fun u => -Kswap xStar u) (-uStar) := by
      simpa [convexConjugate] using
        helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
          (g := Kswap xStar) uStar
    have hConj :
        concaveConjugate (fun u => convexBifunctionPairing F u xStar) uStar =
          -convexConjugate (fun u => -Kswap xStar u) (-uStar) := by
      simpa [hSliceEq] using hConj0
    have hPoint :
        -G xStar uStar = Gneg xStar (-uStar) := by
      simpa [G, Gneg, section34ConcaveBifunctionAdjoint] using congrArg Neg.neg hConj
    simpa [negSecondBlock, graphFunctionOfBifunction, xStar, uStar] using hPoint
  have hGraphLscGneg : LowerSemicontinuous (graphFunctionOfBifunction Gneg) := by
    have hClosureLsc :
        LowerSemicontinuous (functionConvexClosure (graphFunctionOfBifunction Gneg)) :=
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
        (f := graphFunctionOfBifunction Gneg)
    exact hGraphClosedGneg ▸ hClosureLsc
  have hNegSecondBlockCont : Continuous negSecondBlock := by
    apply continuous_pi
    intro i
    by_cases hi : i.1 < n
    · let i' : Fin n := ⟨i.1, hi⟩
      have hiEq : Fin.castAdd m i' = i := by
        ext
        simp [i']
      rw [← hiEq]
      simpa [negSecondBlock] using
        (continuous_apply (i := Fin.castAdd m i'))
    · have hge : n ≤ i.1 := Nat.le_of_not_gt hi
      let j : Fin m := ⟨i.1 - n, by omega⟩
      have hjEq : Fin.natAdd n j = i := by
        ext
        simp [j]
        omega
      rw [← hjEq]
      simpa [negSecondBlock] using
        (continuous_apply (i := Fin.natAdd n j)).neg
  have hNegGraphLsc :
      LowerSemicontinuous (fun z => -graphFunctionOfBifunction G z) := by
    rw [hNegGraphEq]
    exact hGraphLscGneg.comp_continuous hNegSecondBlockCont
  have hNegGraphClosed : IsFunctionConvexClosed (fun z => -graphFunctionOfBifunction G z) :=
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hNegGraphLsc
  have hGraphClosedG : IsFunctionConcaveClosed (graphFunctionOfBifunction G) := by
    funext z
    have hClosedPoint :
        -graphFunctionOfBifunction G z =
          functionConvexClosure
            (fun z' : Fin (n + m) → ℝ => -graphFunctionOfBifunction G z') z :=
      congrArg (fun f => f z) hNegGraphClosed
    have hRewrite :
        functionConcaveClosure (graphFunctionOfBifunction G) z =
          -functionConvexClosure
            (fun z' : Fin (n + m) → ℝ => -graphFunctionOfBifunction G z') z := by
      exact
        congrArg
          (fun f : (Fin (n + m) → ℝ) → EReal => f z)
          (_root_.helperForCorollary33_2_1_functionConcaveClosure_eq_neg_functionConvexClosure_neg
            (g := graphFunctionOfBifunction G))
    have hPoint :
        graphFunctionOfBifunction G z =
          functionConcaveClosure (graphFunctionOfBifunction G) z := by
      have hRewriteNeg :
          -functionConcaveClosure (graphFunctionOfBifunction G) z =
            functionConvexClosure
              (fun z' : Fin (n + m) → ℝ => -graphFunctionOfBifunction G z') z := by
        simpa using congrArg Neg.neg hRewrite
      have hNegPoint :
          -graphFunctionOfBifunction G z =
            -functionConcaveClosure (graphFunctionOfBifunction G) z := by
        calc
          -graphFunctionOfBifunction G z =
              functionConvexClosure
                (fun z' : Fin (n + m) → ℝ => -graphFunctionOfBifunction G z') z :=
            hClosedPoint
          _ = -functionConcaveClosure (graphFunctionOfBifunction G) z := by
                symm
                exact hRewriteNeg
      simpa using congrArg Neg.neg hNegPoint
    exact hPoint
  simpa [G] using hGraphClosedG
-/

/-- Helper for Corollary 37.1.2: the inverse graph is obtained by swapping the two coordinate
blocks before evaluating the negated graph of the original bifunction. -/
def helperForCorollary_37_1_2_swapBlock
    (z : Fin (m + n) → ℝ) : Fin (n + m) → ℝ :=
  Fin.append (fun i => z (Fin.natAdd m i)) (fun j => z (Fin.castAdd n j))

/-- Helper for Corollary 37.1.2: negating a Rockafellar concave bifunction produces a
Rockafellar convex bifunction on the same ambient product space. -/
lemma helperForCorollary_37_1_2_negatedConcaveBifunction_isRockafellarConvex
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hRockG : IsRockafellarConcaveBifunction G)
    (hNoTopG : HasNoTopValuesBifunction G) :
    IsRockafellarConvexBifunction (fun x u => -G x u) := by
  rcases hRockG with ⟨hConcG, hPairG⟩
  refine ⟨?_, ?_⟩
  · -- Negating each concave section turns the second-variable Jensen lower bound into the
    -- convex Jensen upper bound required for the inverse route.
    intro x u₁ u₂ hu₁ hu₂ a b ha hb hab hu12
    have hJensen :
        (a : EReal) * G x u₁ + (b : EReal) * G x u₂ ≤
          G x (a • u₁ + b • u₂) :=
      hConcG x hu₁ hu₂ ha hb hab hu12
    have hTerm1_ne_top : (a : EReal) * G x u₁ ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inl ?_, Or.inl (EReal.coe_ne_top a), ?_⟩
      · exact_mod_cast ha
      · by_cases hZero : a = 0
        · left
          simp [hZero]
        · right
          exact hNoTopG x u₁
    have hTerm2_ne_top : (b : EReal) * G x u₂ ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      refine ⟨Or.inl (EReal.coe_ne_bot b), Or.inl ?_, Or.inl (EReal.coe_ne_top b), ?_⟩
      · exact_mod_cast hb
      · by_cases hZero : b = 0
        · left
          simp [hZero]
        · right
          exact hNoTopG x u₂
    have hNegJensen :
        -(G x (a • u₁ + b • u₂)) ≤
          -((a : EReal) * G x u₁ + (b : EReal) * G x u₂) := by
      simpa using hJensen
    have hNegAdd :
        -((a : EReal) * G x u₁ + (b : EReal) * G x u₂) =
          -((a : EReal) * G x u₁) - ((b : EReal) * G x u₂) :=
      EReal.neg_add (Or.inr hTerm2_ne_top) (Or.inl hTerm1_ne_top)
    calc
      -(G x (a • u₁ + b • u₂))
          ≤ -((a : EReal) * G x u₁ + (b : EReal) * G x u₂) := hNegJensen
      _ = (a : EReal) * (-G x u₁) + (b : EReal) * (-G x u₂) := by
            simpa [sub_eq_add_neg] using hNegAdd
  · intro uStar
    -- The parameterwise convexity of the concave pairing becomes parameterwise concavity of
    -- the convex pairing after one sign flip.
    have hNegPair :
        IsERealConcaveOn (Set.univ : Set (Fin n → ℝ))
          (fun x => -concaveBifunctionPairing G x (-uStar)) :=
      helperForLemma33_0_5_convexNegation_isConcave (hPairG (-uStar))
    have hRewrite :
        (fun x => -concaveBifunctionPairing G x (-uStar)) =
          fun x => convexBifunctionPairing (fun x' u => -G x' u) x uStar := by
      funext x
      -- Rewrite the concave pairing of `G` as the negative of the convex pairing of `-G`.
      have hPoint :
          concaveBifunctionPairing G x (-uStar) =
            -convexBifunctionPairing (fun x' u => -G x' u) x uStar := by
        simpa using
          _root_.helperForCorollary33_2_1_concavePairing_eq_neg_convexPairing_of_neg
            (F := G) x (-uStar)
      simpa using congrArg Neg.neg hPoint
    simpa [hRewrite] using hNegPair

/-- Helper for Corollary 37.1.2: negating a graph-function-closed concave bifunction turns the
graph function into a convex-closed one. -/
lemma helperForCorollary_37_1_2_negatedGraph_isFunctionConvexClosed
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hGraphClosedG : IsFunctionConcaveClosed (graphFunctionOfBifunction G)) :
    IsFunctionConvexClosed (graphFunctionOfBifunction (fun x u => -G x u)) := by
  funext z
  -- Evaluate the concave-closure fixed-point identity at `z` and flip signs to recover the
  -- convex-closure fixed-point identity for the negated graph.
  have hClosedPoint :
      graphFunctionOfBifunction G z =
        functionConcaveClosure (graphFunctionOfBifunction G) z :=
    congrArg (fun f => f z) hGraphClosedG
  have hClosureRewrite :
      functionConcaveClosure (graphFunctionOfBifunction G) z =
        -functionConvexClosure
          (fun z' : Fin (n + m) → ℝ => -graphFunctionOfBifunction G z') z :=
    congrArg
      (fun f : (Fin (n + m) → ℝ) → EReal => f z)
      (_root_.helperForCorollary33_2_1_functionConcaveClosure_eq_neg_functionConvexClosure_neg
        (g := graphFunctionOfBifunction G))
  have hNegClosed :
      -graphFunctionOfBifunction G z =
        functionConvexClosure
          (fun z' : Fin (n + m) → ℝ => -graphFunctionOfBifunction G z') z := by
    have hPoint :
        graphFunctionOfBifunction G z =
          -functionConvexClosure
            (fun z' : Fin (n + m) → ℝ => -graphFunctionOfBifunction G z') z :=
      hClosedPoint.trans hClosureRewrite
    simpa using congrArg Neg.neg hPoint
  simpa [graphFunctionOfBifunction] using hNegClosed

/-- Helper for Corollary 37.1.2: the graph of the inverse bifunction is exactly the graph of
the negated original bifunction precomposed with the block-swap map. -/
lemma helperForCorollary_37_1_2_inverse_graphFunction_eq_blockSwap_negatedGraph
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal) :
    graphFunctionOfBifunction (bifunctionInverse G) =
      fun z => graphFunctionOfBifunction (fun x u => -G x u)
        (helperForCorollary_37_1_2_swapBlock (m := m) (n := n) z) := by
  -- Unfold the inverse and the two graph functions; the coordinate split is exactly the block
  -- swap built into `helperForCorollary_37_1_2_swapBlock`.
  funext z
  simp [graphFunctionOfBifunction, bifunctionInverse,
    helperForCorollary_37_1_2_swapBlock]

/-- Helper for Corollary 37.1.2: precomposing a convex graph function with the block-swap map
preserves convexity. -/
lemma helperForCorollary_37_1_2_blockSwap_precomp_preserves_graphConvex
    {f : (Fin (n + m) → ℝ) → EReal}
    (hf : IsERealConvexOn (Set.univ : Set (Fin (n + m) → ℝ)) f) :
    IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
      (fun z => f (helperForCorollary_37_1_2_swapBlock (m := m) (n := n) z)) := by
  intro z₁ z₂ hz₁ hz₂ a b ha hb hab hz
  -- The block-swap map is affine, so Jensen for `f` can be applied after swapping the
  -- coordinates of the two endpoints.
  have hSwapAffine :
      helperForCorollary_37_1_2_swapBlock (m := m) (n := n) (a • z₁ + b • z₂) =
        a • helperForCorollary_37_1_2_swapBlock (m := m) (n := n) z₁ +
          b • helperForCorollary_37_1_2_swapBlock (m := m) (n := n) z₂ := by
    funext i
    by_cases hi : i.1 < n
    · let i' : Fin n := ⟨i.1, hi⟩
      have hiEq : Fin.castAdd m i' = i := by
        ext
        simp [i']
      rw [← hiEq]
      simp [helperForCorollary_37_1_2_swapBlock, Pi.smul_apply, Pi.add_apply]
    · have hge : n ≤ i.1 := Nat.le_of_not_gt hi
      let j : Fin m := ⟨i.1 - n, by omega⟩
      have hjEq : Fin.natAdd n j = i := by
        ext
        simp [j]
        omega
      rw [← hjEq]
      simp [helperForCorollary_37_1_2_swapBlock, Pi.smul_apply, Pi.add_apply]
  have hJensen :=
    hf (x := helperForCorollary_37_1_2_swapBlock (m := m) (n := n) z₁)
      (y := helperForCorollary_37_1_2_swapBlock (m := m) (n := n) z₂)
      (by trivial) (by trivial) ha hb hab (by trivial)
  simpa [hSwapAffine] using hJensen

/-- Helper for Corollary 37.1.2: once a concave bifunction is graph-function closed, its inverse
only still needs the swap-negate graph-closure transport to become a closed convex bifunction. -/
lemma helperForCorollary_37_1_2_inverseClosedConcave_to_closedConvex
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hRockG : IsRockafellarConcaveBifunction G)
    (hNoTopG : HasNoTopValuesBifunction G)
    (hGraphClosedG : IsFunctionConcaveClosed (graphFunctionOfBifunction G)) :
    IsClosedConvexBifunction (bifunctionInverse G) := by
  let H := bifunctionInverse G
  let Gneg : (Fin n → ℝ) → (Fin m → ℝ) → EReal := fun x u => -G x u
  -- Route correction: instead of commuting the full inverse transform with closure operators
  -- directly, first pass to the negated same-order bifunction `Gneg`, then transport only by
  -- the pure block swap on graph coordinates.
  have hRockGneg : IsRockafellarConvexBifunction Gneg :=
    helperForCorollary_37_1_2_negatedConcaveBifunction_isRockafellarConvex
      (G := G) hRockG hNoTopG
  have hNoBotGneg : HasNoBotValuesBifunction Gneg := by
    -- Negation turns the no-`⊤` hypothesis on `G` into the no-`⊥` hypothesis on `Gneg`.
    intro x u
    simpa [Gneg, EReal.neg_eq_bot_iff] using hNoTopG x u
  have hGraphClosedGneg :
      IsFunctionConvexClosed (graphFunctionOfBifunction Gneg) :=
    helperForCorollary_37_1_2_negatedGraph_isFunctionConvexClosed
      (G := G) hGraphClosedG
  have hSectionClosedGneg : ∀ x : Fin n → ℝ, IsFunctionConvexClosed (Gneg x) :=
    helperForLemma33_0_22_section_isFunctionConvexClosed hGraphClosedGneg
  have hClosedGneg : IsClosedConvexBifunction Gneg :=
    ⟨hRockGneg, hNoBotGneg, hSectionClosedGneg⟩
  have hGraphConvexGneg : IsGraphConvexBifunction Gneg :=
    helperForCorollary_37_1_1_closedConvex_isGraphConvex (F := Gneg) (hF := hClosedGneg)
  have hGraphConvexH :
      IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction H) := by
    -- Rewrite the inverse graph as a swapped negated graph and pull convexity back along the
    -- affine block-swap map.
    rw [helperForCorollary_37_1_2_inverse_graphFunction_eq_blockSwap_negatedGraph (G := G)]
    exact helperForCorollary_37_1_2_blockSwap_precomp_preserves_graphConvex
      (m := m) (n := n) (f := graphFunctionOfBifunction Gneg)
      (by simpa [IsGraphConvexBifunction] using hGraphConvexGneg)
  have hRockH : IsRockafellarConvexBifunction H := by
    -- Graph convexity recovers the Rockafellar convex package for the inverse itself.
    simpa [H, helperForLemma33_0_14_bifunctionOfGraphFunction_graphFunctionOfBifunction_eq] using
      (helperForLemma33_0_14_backwardHalf_of_graphConvex
        (f := graphFunctionOfBifunction H) hGraphConvexH).1
  have hNoBotH : HasNoBotValuesBifunction H := by
    -- The inverse is pointwise the negation of `G` with swapped variables.
    intro u x
    simpa [H, bifunctionInverse, EReal.neg_eq_bot_iff] using hNoTopG x u
  have hGraphLscGneg : LowerSemicontinuous (graphFunctionOfBifunction Gneg) := by
    -- A graph function fixed by the raw convex closure is lower semicontinuous.
    have hClosureLsc :
        LowerSemicontinuous (functionConvexClosure (graphFunctionOfBifunction Gneg)) :=
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
        (f := graphFunctionOfBifunction Gneg)
    exact hGraphClosedGneg ▸ hClosureLsc
  have hSwapCont :
      Continuous (helperForCorollary_37_1_2_swapBlock (m := m) (n := n)) := by
    -- Each swapped coordinate is one of the original coordinate projections.
    apply continuous_pi
    intro i
    by_cases hi : i.1 < n
    · let i' : Fin n := ⟨i.1, hi⟩
      have hiEq : Fin.castAdd m i' = i := by
        ext
        simp [i']
      rw [← hiEq]
      simpa [helperForCorollary_37_1_2_swapBlock] using
        (continuous_apply (i := Fin.natAdd m i'))
    · have hge : n ≤ i.1 := Nat.le_of_not_gt hi
      let j : Fin m := ⟨i.1 - n, by omega⟩
      have hjEq : Fin.natAdd n j = i := by
        ext
        simp [j]
        omega
      rw [← hjEq]
      simpa [helperForCorollary_37_1_2_swapBlock] using
        (continuous_apply (i := Fin.castAdd n j))
  have hGraphClosedH : IsFunctionConvexClosed (graphFunctionOfBifunction H) := by
    -- Lower semicontinuity survives continuous precomposition by the block-swap map, so the
    -- swapped graph is again fixed by the raw convex closure.
    rw [helperForCorollary_37_1_2_inverse_graphFunction_eq_blockSwap_negatedGraph (G := G)]
    exact
      helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
        (hGraphLscGneg.comp_continuous hSwapCont)
  have hSectionClosedH : ∀ u : Fin m → ℝ, IsFunctionConvexClosed (H u) :=
    helperForLemma33_0_22_section_isFunctionConvexClosed hGraphClosedH
  -- The inverse now satisfies the exact Section 34 closed-convex package: Rockafellar
  -- convexity, no `⊥` values, and convex-closed sections.
  exact ⟨hRockH, hNoBotH, hSectionClosedH⟩

/-- Helper for Corollary 37.1.2: the dual inverse `F_*` should inherit image-closed convexity
from the image-closed concavity of the adjoint `F^*`. -/
lemma helperForCorollary_37_1_2_dualAdjointInverse_isClosedConvex
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    IsClosedConvexBifunction
      (bifunctionInverse (section34ConcaveBifunctionAdjoint F)) := by
  let G := section34ConcaveBifunctionAdjoint F
  have hGimg : IsImageClosedConcaveBifunction G :=
    (hGlobal.qualification F hF).adjoint_imageClosed
  have hGraphClosedG : IsFunctionConcaveClosed (graphFunctionOfBifunction G) :=
    helperForCorollary_37_1_2_section34Adjoint_graphConcaveClosed
      (F := F) (hF := hF) hGlobal
  -- Reduce the dual-inverse claim to the general swap-negate transport for graph-closed
  -- concave bifunctions.
  exact helperForCorollary_37_1_2_inverseClosedConcave_to_closedConvex
    (G := G) hGimg.1 hGimg.2.1 hGraphClosedG

/-- Helper for Corollary 37.1.2: the convex pairing of the dual inverse `F_*` is exactly the
`infPairing` of the original inverse slice. -/
lemma helperForCorollary_37_1_2_dualInversePairing_eq_originalInverseInfPairing
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hFStar :
      IsClosedConvexBifunction
        (bifunctionInverse (section34ConcaveBifunctionAdjoint F)))
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
    infPairing uStar (bifunctionInverse F x) = convexBifunctionPairing FStar uStar x := by
  let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
  have hPairingEqFStar := (hGlobal.qualification FStar hFStar).adjointPairing_eq
  have hDoubleRecovery :
      bifunctionInverse (section34ConcaveBifunctionAdjoint FStar) = F := by
    let FDouble := bifunctionInverse (section34ConcaveBifunctionAdjoint FStar)
    have hFDouble : IsClosedConvexBifunction FDouble :=
      helperForCorollary_37_1_2_dualAdjointInverse_isClosedConvex
        (F := FStar) (hF := hFStar) hGlobal
    have hPairEq :
        ∀ u xStar,
          convexBifunctionPairing FDouble u xStar = convexBifunctionPairing F u xStar := by
      intro u xStar
      -- First identify the doubled transform with the one-variable convex closure of the
      -- original kernel slice.
      have hClosure :
          convexBifunctionPairing FDouble u xStar =
            functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar := by
        simpa [FStar, FDouble] using
          helperForCorollary_37_1_1_upperRecoveredKernel_eq_functionConvexClosure
            (F := F) (hF := hF) hGlobal (u := u) (xStar := xStar)
      -- Then collapse that closure because the original slice is already convex-closed.
      have hCollapse :
          functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar =
            convexBifunctionPairing F u xStar :=
        helperForCorollary_37_1_1_originalKernelSlice_functionConvexClosure_eq_self
          (F := F) (hF := hF) (u := u) (xStar := xStar)
      exact hClosure.trans hCollapse
    have hRecoverDouble :=
      (closedSaddleFunctions_imageClosedBifunctions_correspondence (m := m) (n := n)).1
        FDouble hFDouble
    have hRecoverF :=
      (closedSaddleFunctions_imageClosedBifunctions_correspondence (m := m) (n := n)).1
        F hF
    -- Recover pointwise equality of the bifunctions by taking convex conjugates of the equal
    -- pairing sections.
    ext u x
    have hSectionFun :
        (fun y => convexBifunctionPairing FDouble u y) =
          (fun y => convexBifunctionPairing F u y) := by
      funext y
      exact hPairEq u y
    have hConjEq :
        convexConjugate (fun y => convexBifunctionPairing FDouble u y) x =
          convexConjugate (fun y => convexBifunctionPairing F u y) x := by
      exact congrArg (fun g => convexConjugate g x) hSectionFun
    calc
      FDouble u x = convexConjugate (fun y => convexBifunctionPairing FDouble u y) x := by
        symm
        simpa using hRecoverDouble.2.2 u x
      _ = convexConjugate (fun y => convexBifunctionPairing F u y) x := hConjEq
      _ = F u x := by
        simpa using hRecoverF.2.2 u x
  have hAdjointSlice :
      section34ConcaveBifunctionAdjoint FStar x = bifunctionInverse F x := by
    funext u
    -- Evaluate the doubled-transform identity at `(u, x)` and rewrite the inverse explicitly.
    have hPoint : bifunctionInverse (section34ConcaveBifunctionAdjoint FStar) u x = F u x :=
      congrArg (fun H => H u x) hDoubleRecovery
    simpa [bifunctionInverse] using congrArg Neg.neg hPoint
  -- Replace the original inverse slice by the recovered Section 34 adjoint slice of `F_*`,
  -- then collapse the adjoint pairing with Theorem 34.2 for `F_*`.
  calc
    infPairing uStar (bifunctionInverse F x) =
        infPairing uStar (section34ConcaveBifunctionAdjoint FStar x) := by
          rw [hAdjointSlice]
    _ = section34ConcaveBifunctionAdjointPairing FStar uStar x := by
          simp [section34ConcaveBifunctionAdjointPairing, concaveBifunctionPairing,
            bifunctionPairingNotation, conjugatePairingNotation, infPairing, sInf_range,
            finDot, dotProduct, sub_eq_add_neg, mul_comm]
    _ = convexBifunctionClosedKernel FStar uStar x := by
          exact congrArg (fun H : SaddleFunction m n => H uStar x) hPairingEqFStar |>.symm
    _ = convexBifunctionPairing FStar uStar x := by
          rfl

/-- Helper for Corollary 37.1.2: once the dual inverse `F_*` is known to be closed convex, the
upper conjugate of `K` should be the Section 34 upper pairing attached to `F_*`. -/
lemma helperForCorollary_37_1_2_upperConjugate_eq_dualUpperKernel
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (K : SaddleFunction m n)
    (hK : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩)
    (hFStar :
      IsClosedConvexBifunction
        (bifunctionInverse (section34ConcaveBifunctionAdjoint F)))
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    ∀ uStar x,
      theorem37ValueInfSup K uStar x =
        section34ConcaveBifunctionAdjointPairing
          (bifunctionInverse (section34ConcaveBifunctionAdjoint F)) uStar x := by
  let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
  have hSection37 :=
    section37_theorem37_1 F hF K hK (convexBifunctionClosedKernel FStar) hFStar
      (by
        have hSection34FStar := section34_theorem34_2 FStar hFStar
        have hOmega :
            convexBifunctionClosedKernel FStar ∈ omegaClassOfConvexBifunction FStar :=
          hSection34FStar.2.2
        have hEquivKernel :
            convexBifunctionClosedKernel FStar ∈
              {L | saddleEquivalent L (convexBifunctionClosedKernel FStar)} := by
          rw [← hSection34FStar.2.1]
          exact hOmega
        simpa [EquivalenceClassGeneratedByConvexBifunction, convexBifunctionClosedKernel] using
          hEquivKernel)
      hGlobal
  have hPairingEqFStar := (hGlobal.qualification FStar hFStar).adjointPairing_eq
  intro uStar x
  have hPairEq :
      infPairing uStar (bifunctionInverse F x) = convexBifunctionPairing FStar uStar x := by
    simpa [FStar] using
      helperForCorollary_37_1_2_dualInversePairing_eq_originalInverseInfPairing
        (F := F) (hF := hF) (hFStar := hFStar) hGlobal
          (uStar := uStar) (x := x)
  -- First rewrite the upper conjugate as the `infPairing` formula from Theorem 37.1.
  calc
    theorem37ValueInfSup K uStar x = infPairing uStar (bifunctionInverse F x) := by
      exact hSection37.1 uStar x
    _ = convexBifunctionPairing FStar uStar x := hPairEq
    _ = section34ConcaveBifunctionAdjointPairing FStar uStar x := by
      -- Theorem 34.2 identifies the canonical dual lower and upper kernels.
      exact congrArg (fun H : SaddleFunction m n => H uStar x) hPairingEqFStar

/-- Helper for Proposition 37.1.3: a point in the saddle effective domain of the canonical dual
kernel projects to points in the corresponding first and second effective domains. -/
lemma helperForProposition_37_1_3_kernelDomainNonempty_of_saddleDomain
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (saddleEffectiveDomain (convexBifunctionClosedKernel F)).Nonempty →
      (convexBifunctionDomain F).Nonempty ∧
        (convexBifunctionKernelAdjointDomain F).Nonempty := by
  rintro ⟨⟨u, x⟩, hux⟩
  -- Split the product witness into its first-coordinate and second-coordinate domain data.
  refine ⟨?_, ?_⟩
  · refine ⟨u, ?_⟩
    simpa [convexBifunctionDomain, saddleEffectiveDomain] using (Set.mem_prod.mp hux).1
  · refine ⟨x, ?_⟩
    simpa [convexBifunctionKernelAdjointDomain, saddleEffectiveDomain] using
      (Set.mem_prod.mp hux).2

/-- Corollary 37.1.2: the lower and upper conjugates of a closed proper saddle-function admit a
common nonempty convex effective domain on which the usual closure and relative-interior
conclusions of Section 34 are expected to hold. -/
theorem corollary37_1_2_lower_upper_conjugates_structure
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    let KLowerStar : SaddleFunction m n := fun uStar x => theorem37ValueSupInf K uStar x
    let KUpperStar : SaddleFunction m n := fun uStar x => theorem37ValueInfSup K uStar x
    ∃ CStar : Set (Fin m → ℝ), ∃ DStar : Set (Fin n → ℝ),
      CStar.Nonempty ∧
        DStar.Nonempty ∧
        Convex ℝ CStar ∧
        Convex ℝ DStar ∧
        effectiveDomain₁ KLowerStar = CStar ∧
        effectiveDomain₂ KLowerStar = DStar ∧
        effectiveDomain₁ KUpperStar = CStar ∧
        effectiveDomain₂ KUpperStar = DStar ∧
        partialClosure₁ KLowerStar = KUpperStar ∧
        partialClosure₂ KUpperStar = KLowerStar ∧
        ∀ uStar x,
          uStar ∈ intrinsicInterior ℝ CStar ∨ x ∈ intrinsicInterior ℝ DStar →
            KLowerStar uStar x = KUpperStar uStar x := by
  dsimp
  -- Recover a proper closed convex representative of the original closed equivalence class.
  rcases helperForCorollary_37_1_2_closedProperRepresentative K hKclosed hKproper hGlobal with
    ⟨F, hF, hFproper, hKGenerated⟩
  let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
  have hFStarClosed : IsClosedConvexBifunction FStar :=
    helperForCorollary_37_1_2_dualAdjointInverse_isClosedConvex
      (F := F) (hF := hF) hGlobal
  have hDualInverseProper :
      IsProperConvexBifunction FStar :=
    helperForCorollary_37_1_2_dualAdjointInverse_isProperConvex
      (F := F) (hF := hF) (hFproper := hFproper)
  have hLowerKernel :
      ∀ uStar x,
        theorem37ValueSupInf K uStar x =
          convexBifunctionClosedKernel FStar uStar x := by
    intro uStar x
    -- The lower conjugate is already the canonical dual lower kernel once `F_*` is closed.
    simpa [FStar, convexBifunctionClosedKernel] using
      helperForCorollary_37_1_2_lowerConjugate_eq_dualLowerKernel
        (F := F) (hF := hF) (K := K) (hK := hKGenerated)
          (hFStar := hFStarClosed) hGlobal uStar x
  have hUpperKernel :
      ∀ uStar x,
        theorem37ValueInfSup K uStar x =
          section34ConcaveBifunctionAdjointPairing FStar uStar x := by
    intro uStar x
    -- The upper conjugate should match the dual upper kernel attached to the same `F_*`.
    simpa [FStar] using
      helperForCorollary_37_1_2_upperConjugate_eq_dualUpperKernel
        (F := F) (hF := hF) (K := K) (hK := hKGenerated)
          (hFStar := hFStarClosed) hGlobal uStar x
  have hLowerEq :
      (fun uStar x => theorem37ValueSupInf K uStar x) = convexBifunctionClosedKernel FStar := by
    funext uStar x
    exact hLowerKernel uStar x
  have hUpperEq :
      (fun uStar x => theorem37ValueInfSup K uStar x) =
        section34ConcaveBifunctionAdjointPairing FStar := by
    funext uStar x
    exact hUpperKernel uStar x
  have hPairEqFStar :
      convexBifunctionClosedKernel FStar =
        section34ConcaveBifunctionAdjointPairing FStar :=
    (hGlobal.qualification FStar hFStarClosed).adjointPairing_eq
  have hUpperEqKernel :
      (fun uStar x => theorem37ValueInfSup K uStar x) = convexBifunctionClosedKernel FStar := by
    exact hUpperEq.trans hPairEqFStar.symm
  have hOmegaKernel :
      convexBifunctionClosedKernel FStar ∈ omegaClassOfConvexBifunction FStar :=
    (section34_theorem34_2 FStar hFStarClosed).2.2
  have hKernelGenerated :
      convexBifunctionClosedKernel FStar ∈
        EquivalenceClassGeneratedByConvexBifunction ⟨FStar, hFStarClosed⟩ := by
    have hEquivKernel :
        convexBifunctionClosedKernel FStar ∈
          {L | saddleEquivalent L (convexBifunctionClosedKernel FStar)} := by
      rw [← (section34_theorem34_2 FStar hFStarClosed).2.1]
      exact hOmegaKernel
    simpa [EquivalenceClassGeneratedByConvexBifunction, convexBifunctionClosedKernel] using
      hEquivKernel
  have hKernelProper :
      IsProperSaddleFunction (convexBifunctionClosedKernel FStar) :=
    proper_convex_bifunction_has_proper_generated_saddle_functions
      FStar hFStarClosed hDualInverseProper (convexBifunctionClosedKernel FStar) hKernelGenerated
        (hGlobal.qualification FStar hFStarClosed)
  have hKernelData :=
    (section34_theorem34_2_qualified FStar hFStarClosed
      (hGlobal.qualification FStar hFStarClosed)).2.2.2.2
        (convexBifunctionClosedKernel FStar) hOmegaKernel
  rcases hKernelData with
    ⟨hCl1Kernel, hCl2Kernel, -, -, -, hAgreeKernel⟩
  have hKernelCC : IsConcaveConvex (convexBifunctionClosedKernel FStar) :=
    hOmegaKernel.1
  have hKernelDomainsConvex :=
    section34_text_34_1_6 (K := convexBifunctionClosedKernel FStar) hKernelCC
  have hKernelDomainNonempty :
      (saddleEffectiveDomain (convexBifunctionClosedKernel FStar)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hKernelProper
  have hProjectedDomainNonempty :
      (convexBifunctionDomain FStar).Nonempty ∧
        (convexBifunctionKernelAdjointDomain FStar).Nonempty :=
    helperForProposition_37_1_3_kernelDomainNonempty_of_saddleDomain
      (F := FStar) hKernelDomainNonempty
  refine ⟨convexBifunctionDomain FStar,
    convexBifunctionKernelAdjointDomain FStar,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The nonempty saddle domain of the canonical kernel produces a point in `dom F_*`.
    exact hProjectedDomainNonempty.1
  · -- The same witness also supplies a point in the adjoint domain of `F_*`.
    exact hProjectedDomainNonempty.2
  · -- Convexity of the first effective domain is part of Text 34.1.6.
    simpa [convexBifunctionDomain] using hKernelDomainsConvex.1
  · -- Convexity of the second effective domain is the dual half of the same theorem.
    simpa [convexBifunctionKernelAdjointDomain] using hKernelDomainsConvex.2.1
  · -- The lower conjugate and the canonical dual kernel have the same first effective domain.
    simp [convexBifunctionDomain, hLowerEq]
  · -- The lower conjugate and the canonical dual kernel have the same second effective domain.
    simp [convexBifunctionKernelAdjointDomain,
      hLowerEq]
  · -- The upper conjugate lands in the same first effective domain after the upper-kernel rewrite.
    simp [convexBifunctionDomain, hUpperEqKernel]
  · -- The upper conjugate lands in the same second effective domain after the upper-kernel rewrite.
    simp [convexBifunctionKernelAdjointDomain,
      hUpperEqKernel]
  · -- The canonical dual lower kernel is already first-variable closed.
    simpa [hLowerEq, hUpperEqKernel] using hCl1Kernel
  · -- The same canonical kernel is also second-variable closed.
    simpa [hLowerEq, hUpperEqKernel] using hCl2Kernel
  · intro uStar x hInterior
    have hInteriorKernel :
        uStar ∈ intrinsicInterior ℝ (convexBifunctionDomain FStar) ∨
          x ∈ intrinsicInterior ℝ (convexBifunctionKernelAdjointDomain FStar) := by
      simpa only [convexBifunctionDomain, convexBifunctionKernelAdjointDomain] using hInterior
    -- Both conjugates have been rewritten to the same canonical dual kernel, so the
    -- relative-interior agreement from Theorem 34.2 becomes immediate.
    calc
      theorem37ValueSupInf K uStar x = convexBifunctionClosedKernel FStar uStar x :=
        hLowerKernel uStar x
      _ = convexBifunctionClosedKernel FStar uStar x := by
        exact hAgreeKernel uStar x hInteriorKernel
      _ = theorem37ValueInfSup K uStar x := by
        exact (congrFun (congrFun hUpperEqKernel uStar) x).symm

/-- Helper for Proposition 37.1.3: the zero affine tilt in the upper conjugate leaves only the
plain negated kernel inside the `inf_u sup_v` expression. -/
lemma helperForProposition_37_1_3_zeroTiltUpperConjugate
    (K : SaddleFunction m n) :
    theorem37ValueInfSup K 0 0 =
      iInf (fun u : Fin m → ℝ => iSup (fun x : Fin n → ℝ => -K u x)) := by
  -- At `(0, 0)` both dot products vanish, so the Section 37 value is just the nested infimum of
  -- negated kernel values.
  simp [theorem37ValueInfSup, finDot]

/-- Helper for Proposition 37.1.3: the zero affine tilt in the lower conjugate leaves only the
plain negated kernel inside the `sup_v inf_u` expression. -/
lemma helperForProposition_37_1_3_zeroTiltLowerConjugate
    (K : SaddleFunction m n) :
    theorem37ValueSupInf K 0 0 =
      iSup (fun x : Fin n → ℝ => iInf (fun u : Fin m → ℝ => -K u x)) := by
  -- The same zero-tilt simplification applies to the dual ordering of infimum and supremum.
  simp [theorem37ValueSupInf, finDot]

/-- Helper for Proposition 37.1.3: evaluating the lower conjugate at the origin recovers the
plain `inf_v sup_u` value of `K`. -/
lemma helperForProposition_37_1_3_zeroLowerConjugateValue
    (K : SaddleFunction m n) :
    -theorem37ValueSupInf K 0 0 =
      iInf (fun x : Fin n → ℝ => iSup (fun u : Fin m → ℝ => K u x)) := by
  -- First remove the affine tilt, which vanishes at `(0, 0)`.
  calc
    -theorem37ValueSupInf K 0 0
        = -(iSup (fun x : Fin n → ℝ => iInf (fun u : Fin m → ℝ => -K u x))) := by
            rw [helperForProposition_37_1_3_zeroTiltLowerConjugate (K := K)]
    _ = -(iSup (fun x : Fin n → ℝ => -(iSup (fun u : Fin m → ℝ => K u x)))) := by
          -- Rewrite each inner `inf` of negated terms as the negative of the corresponding
          -- supremum of the original kernel values.
          refine congrArg (fun φ : (Fin n → ℝ) → EReal => -(iSup φ)) ?_
          funext x
          simpa using
            congrArg Neg.neg
              (helperForLemma33_0_5_neg_iInf_neg_eq_iSup (f := fun u : Fin m → ℝ => K u x))
    _ = iInf (fun x : Fin n → ℝ => iSup (fun u : Fin m → ℝ => K u x)) := by
          -- The outer negated supremum is exactly the indexed infimum from the proposition.
          simpa using
            (helperForLemma33_0_5_neg_iSup_neg_eq_iInf
              (f := fun x : Fin n → ℝ => iSup (fun u : Fin m → ℝ => K u x)))

/-- Helper for Proposition 37.1.3: evaluating the upper conjugate at the origin recovers the
plain `sup_u inf_v` value of `K`. -/
lemma helperForProposition_37_1_3_zeroUpperConjugateValue
    (K : SaddleFunction m n) :
    -theorem37ValueInfSup K 0 0 =
      iSup (fun u : Fin m → ℝ => iInf (fun x : Fin n → ℝ => K u x)) := by
  -- First remove the affine tilt, which vanishes at `(0, 0)`.
  calc
    -theorem37ValueInfSup K 0 0
        = -(iInf (fun u : Fin m → ℝ => iSup (fun x : Fin n → ℝ => -K u x))) := by
            rw [helperForProposition_37_1_3_zeroTiltUpperConjugate (K := K)]
    _ = -(iInf (fun u : Fin m → ℝ => -(iInf (fun x : Fin n → ℝ => K u x)))) := by
          -- Rewrite each inner `sup` of negated terms as the negative of the corresponding
          -- infimum of the original kernel values.
          refine congrArg (fun φ : (Fin m → ℝ) → EReal => -(iInf φ)) ?_
          funext u
          simpa using
            congrArg Neg.neg
              (helperForLemma33_0_5_neg_iSup_neg_eq_iInf (f := fun x : Fin n → ℝ => K u x))
    _ = iSup (fun u : Fin m → ℝ => iInf (fun x : Fin n → ℝ => K u x)) := by
          -- The outer negated infimum is exactly the indexed supremum from the proposition.
          simpa using
            (helperForLemma33_0_5_neg_iInf_neg_eq_iSup
              (f := fun u : Fin m → ℝ => iInf (fun x : Fin n → ℝ => K u x)))

/-- Helper for Proposition 37.1.3: rewriting the lower zero-tilt identity isolates the origin
conjugate value itself as the negative minimax value. -/
lemma helperForProposition_37_1_3_zeroLowerConjugate_eq_neg_minimaxValue
    (K : SaddleFunction m n) :
    theorem37ValueSupInf K 0 0 =
      - minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
  -- The already-proved origin identity becomes the stated formula after rewriting the minimax
  -- value and then cancelling the outer negation.
  have hNeg :
      -theorem37ValueSupInf K 0 0 =
        minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
    simpa [minimaxValue] using
      helperForProposition_37_1_3_zeroLowerConjugateValue (K := K)
  exact neg_injective (by simpa using hNeg)

/-- Helper for Proposition 37.1.3: rewriting the upper zero-tilt identity isolates the origin
conjugate value itself as the negative maximin value. -/
lemma helperForProposition_37_1_3_zeroUpperConjugate_eq_neg_maximinValue
    (K : SaddleFunction m n) :
    theorem37ValueInfSup K 0 0 =
      - maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
  -- The companion origin identity is handled in the same way for the maximin ordering.
  have hNeg :
      -theorem37ValueInfSup K 0 0 =
        maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
    simpa [maximinValue] using
      helperForProposition_37_1_3_zeroUpperConjugateValue (K := K)
  exact neg_injective (by simpa using hNeg)

/-- Helper for Proposition 37.1.3: Corollary 37.1.2 already provides a common product effective
domain for the lower and upper conjugates. -/
lemma helperForProposition_37_1_3_commonSaddleEffectiveDomain
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    ∃ CStar : Set (Fin m → ℝ), ∃ DStar : Set (Fin n → ℝ),
      saddleEffectiveDomain (fun uStar x => theorem37ValueSupInf K uStar x) = CStar ×ˢ DStar ∧
      saddleEffectiveDomain (fun uStar x => theorem37ValueInfSup K uStar x) = CStar ×ˢ DStar := by
  rcases corollary37_1_2_lower_upper_conjugates_structure K hKclosed hKproper hGlobal with
    ⟨CStar, DStar, _, _, _, _, hLower1, hLower2, hUpper1, hUpper2, _, _, _⟩
  refine ⟨CStar, DStar, ?_, ?_⟩
  · -- The lower conjugate domain is the product of the two effective domains identified there.
    simp [saddleEffectiveDomain, hLower1, hLower2]
  · -- The upper conjugate domain is the same product after the corresponding rewrites.
    simp [saddleEffectiveDomain, hUpper1, hUpper2]

/-- Helper for Proposition 37.1.3: the lower and upper conjugates therefore share the same
effective domain. -/
lemma helperForProposition_37_1_3_lowerUpperSaddleEffectiveDomain_eq
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    saddleEffectiveDomain (fun uStar x => theorem37ValueSupInf K uStar x) =
      saddleEffectiveDomain (fun uStar x => theorem37ValueInfSup K uStar x) := by
  rcases helperForProposition_37_1_3_commonSaddleEffectiveDomain
      (K := K) hKclosed hKproper hGlobal with ⟨CStar, DStar, hLowerDom, hUpperDom⟩
  -- Both effective domains have already been rewritten to the same product `C* × D*`.
  rw [hLowerDom, hUpperDom]

/-- Helper for Proposition 37.1.3: the two zero-tilt conjugate evaluations already package the
textbook minimax and maximin identities. -/
lemma helperForProposition_37_1_3_originValueEqualities
    (K : SaddleFunction m n) :
    minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
        -theorem37ValueSupInf K 0 0 ∧
      maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
        -theorem37ValueInfSup K 0 0 := by
  constructor
  · -- The new helper isolates the lower origin conjugate value itself as the negated minimax
    -- quantity; negating that equality moves the sign onto the conjugate side.
    have hNegated :
        -theorem37ValueSupInf K 0 0 =
          minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
      simpa using
        congrArg Neg.neg
          (helperForProposition_37_1_3_zeroLowerConjugate_eq_neg_minimaxValue (K := K))
    simpa using hNegated.symm
  · -- The companion helper does the same for the upper origin conjugate and the maximin value.
    have hNegated :
        -theorem37ValueInfSup K 0 0 =
          maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
      simpa using
        congrArg Neg.neg
          (helperForProposition_37_1_3_zeroUpperConjugate_eq_neg_maximinValue (K := K))
    simpa using hNegated.symm

/-- Proposition 37.1.3: the minimax and maximin values of `K` are the negatives of the lower and
upper conjugates at the origin, and these two conjugates share the same product effective domain
`C* × D*`. -/
theorem proposition37_1_3_minimax_maximin_and_commonDomain
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    ∃ CStar : Set (Fin m → ℝ), ∃ DStar : Set (Fin n → ℝ),
      minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
        -theorem37ValueSupInf K 0 0 ∧
      maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
        -theorem37ValueInfSup K 0 0 ∧
      saddleEffectiveDomain (fun uStar x => theorem37ValueSupInf K uStar x) = CStar ×ˢ DStar ∧
      saddleEffectiveDomain (fun uStar x => theorem37ValueInfSup K uStar x) = CStar ×ˢ DStar := by
  -- First package the textbook minimax and maximin quantities as zero-tilt conjugate values.
  rcases helperForProposition_37_1_3_originValueEqualities (K := K) with
    ⟨hLowerValue, hUpperValue⟩
  -- Then package the common domain conclusion using the product-domain description from
  -- Corollary 37.1.2.
  rcases helperForProposition_37_1_3_commonSaddleEffectiveDomain
      (K := K) hKclosed hKproper hGlobal with ⟨CStar, DStar, hLowerDom, hUpperDom⟩
  exact ⟨CStar, DStar, hLowerValue, hUpperValue, hLowerDom, hUpperDom⟩

end Section37
end Chap07
