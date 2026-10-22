/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part12

section Chap06
section Section30

/-- Helper for Theorem 6.30.17: under global properness, polyhedrality of the dual adjoint
transports back across the biadjoint correspondence to polyhedrality of the original primal
bifunction. -/
lemma helperForTheorem_6_30_17_polyhedralDual_implies_polyhedralPrimal_of_globalProperness
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1)
    (hPolyDual :
      PolyhedralConcaveBifunction (m := n) (n := m)
        (adjointOfConvexBifunction ⟨F.1, F.2.1⟩)) :
    PolyhedralConvexBifunction F.1 := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  rcases
      (adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality
        (F := adjointOfConvexBifunction FCvx)).2
        (adjointOfConvexBifunctionAsConcave FCvx).2 with
    ⟨_hClosedAdj, _hProperIff, _hBiadjointEq, _hFixedPoint, _hClosedProper, hPolyTransport⟩
  have hClosureFixed : convexBifunctionClosure F.1 = F.1 := by
    -- Closed proper convex bifunctions are fixed by the canonical convex closure.
    exact
      helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed_proper
        (hClosed := F.2) (hProper := hProper)
  have hBiadjointSelf :
      biadjointOfConvexBifunction FCvx = F.1 := by
    -- The biadjoint collapses back to `F` in the closed proper branch.
    exact
      helperForTheorem_6_30_11_convex_biadjoint_eq_self_of_closure_eq_self
        (hF := F.2.1) hClosureFixed
  have hBiadjointPoly :
      PolyhedralConvexBifunction (m := m) (n := n)
        (adjointOfConcaveBifunction (adjointOfConvexBifunctionAsConcave FCvx)) :=
    hPolyTransport hPolyDual
  -- Rewriting the transported biadjoint polyhedrality along `F** = F` finishes the transport.
  simpa [biadjointOfConvexBifunction] using (hBiadjointSelf ▸ hBiadjointPoly)

/-- Helper for Theorem 6.30.17: the finite polyhedral dual branch is a Chapter 29 generalized
convex program for the negated adjoint bifunction, and its generalized Kuhn--Tucker vector is
exactly a Chapter 30 dual Kuhn--Tucker vector. -/
lemma helperForTheorem_6_30_17_dualKuhnTucker_of_polyhedral_negAdjoint_and_finiteDualValue
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1)
    (hPolyDual :
      PolyhedralConcaveBifunction (m := n) (n := m)
        (adjointOfConvexBifunction ⟨F.1, F.2.1⟩))
    (hFiniteDual : HasFiniteDualOptimalValueOfConvexProgram ⟨F.1, F.2.1⟩) :
    ∃ x : Fin n → ℝ, IsKuhnTuckerVectorForDualProgram ⟨F.1, F.2.1⟩ x := by
  let gDual : (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
    fun xStar : Fin n → ℝ => fun uStar : Fin m → ℝ =>
      -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar uStar
  have hGConv30 : ConvexBifunction gDual := by
    -- Negating the concave adjoint graph yields a convex bifunction in the Chapter 30 sense.
    simpa [gDual, ConvexBifunction, ConcaveBifunction, bifunctionGraphFunction] using hPolyDual.1
  have hAdjProper :
      ProperConcaveBifunction (m := n) (n := m)
        (adjointOfConvexBifunction ⟨F.1, F.2.1⟩) := by
    -- Global properness transports to the adjoint via Theorem 6.30.11.
    exact
      (helperForTheorem_6_30_11_convex_branch_except_closed_fixed_point
        (F := F.1) (hF := F.2.1)).2.1.2 hProper
  have hNoGraphBotG :
      ∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ, gDual xStar uStar ≠ (⊥ : EReal) := by
    intro xStar uStar
    have hAdjNeTop :
        adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar uStar ≠ (⊤ : EReal) := by
      simpa [ProperConcaveERealFunction, bifunctionGraphFunction] using
        hAdjProper.2.1.1 (Fin.append xStar uStar)
    simpa [gDual] using hAdjNeTop
  let G : BundledConvexBifunction n m :=
    ⟨gDual,
      helperForTheorem_6_30_17_isConvexBifunction_of_convexBifunction
        hGConv30 hNoGraphBotG⟩
  have hGraphPoly :
      IsPolyhedralConvexFunction (n + m)
        (helperForCorollary_6_29_7_coordinateGraphFunction G) := by
    -- The polyhedral graph hypothesis is already phrased on the same negated adjoint graph.
    simpa [helperForCorollary_6_29_7_coordinateGraphFunction, bifunctionGraphFunction, G, gDual]
      using hPolyDual.2
  have hPertEq :
      generalizedConvexProgramPerturbationFunction G =
        fun xStar : Fin n → ℝ =>
          -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar := by
    funext xStar
    -- The perturbation of `G` is the infimum of the negated adjoint slice, hence the negative
    -- of the original dual perturbation supremum.
    calc
      generalizedConvexProgramPerturbationFunction G xStar
          = sInf (Set.range (gDual xStar)) := by
              rfl
      _ = sInf (Set.range fun uStar : Fin m → ℝ =>
            -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar uStar) := by
            rfl
      _ = -sSup (Set.range fun uStar : Fin m → ℝ =>
            adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar uStar) := by
            simpa [sInf_range, sSup_range] using
              (congrArg Neg.neg
                (ereal_iSup_neg_eq_neg_iInf
                  (g := fun uStar : Fin m → ℝ =>
                    -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar uStar))).symm
      _ = -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar := by
            simp [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith]
  have hOptEq :
      generalizedConvexProgramOptimalValue G =
        -(dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) := by
    -- Evaluating the perturbation identity at the origin identifies the generalized optimal
    -- value of `G` with the negative dual optimum.
    calc
      generalizedConvexProgramOptimalValue G
          = generalizedConvexProgramPerturbationFunction G 0 := by
              simpa using helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero G
      _ = -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 := by
            simpa using congrFun hPertEq (0 : Fin n → ℝ)
      _ = -(dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) := by
            simp [dualProgramOfConvexProgram]
  have hFiniteGeneral : IsFiniteEReal (generalizedConvexProgramOptimalValue G) := by
    -- Negation preserves finiteness of the dual optimal value.
    rw [hOptEq]
    constructor
    · intro hTop
      exact hFiniteDual.2 (by simpa using congrArg Neg.neg hTop)
    · intro hBot
      exact hFiniteDual.1 (by simpa using congrArg Neg.neg hBot)
  rcases
      helperForCorollary_6_29_7_exists_kuhnTuckerVector_of_polyhedralGraph_and_finiteOptimalValue
        G hGraphPoly hFiniteGeneral with
    ⟨x, hx⟩
  rcases hx with ⟨_hOptNeTop, _hOptNeBot, hLower⟩
  have hTermLeDual :
      ∀ xStar : Fin n → ℝ,
        ((((-x) ⬝ᵥ xStar : ℝ) : EReal) +
          dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar) ≤
            dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
    intro xStar
    have hLower' := hLower xStar
    have hLower'' :
        (-dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar) +
            (((x ⬝ᵥ xStar : ℝ) : EReal)) ≥
          -(dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) := by
      simpa [hPertEq, hOptEq] using hLower'
    have hLowerOrdered :
        -(dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) ≤
          (((x ⬝ᵥ xStar : ℝ) : EReal) +
            -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar) := by
      simpa [add_comm] using hLower''
    have hNeg :
        -((((x ⬝ᵥ xStar : ℝ) : EReal) +
            -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar)) ≤
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
      simpa using (EReal.neg_le_neg_iff.mpr hLowerOrdered)
    have hNegAdd :
        -((((x ⬝ᵥ xStar : ℝ) : EReal) +
            -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar)) =
          -(((x ⬝ᵥ xStar : ℝ) : EReal)) -
            (-dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar) := by
      exact
        EReal.neg_add
          (x := (((x ⬝ᵥ xStar : ℝ) : EReal)))
          (y := -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar)
          (Or.inl (by simp))
          (Or.inl (by simp))
    calc
      ((((-x) ⬝ᵥ xStar : ℝ) : EReal) +
          dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar)
          = -((((x ⬝ᵥ xStar : ℝ) : EReal) +
              -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar)) := by
                rw [hNegAdd]
                simp [sub_eq_add_neg]
      _ ≤ dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := hNeg
  have hObjectiveEqDual :
      sSup (Set.range fun xStar : Fin n → ℝ =>
          ((((-x) ⬝ᵥ xStar : ℝ) : EReal) +
            dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar)) =
        dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
    apply le_antisymm
    · -- Each affine-dual term is bounded above by the dual optimum.
      refine sSup_le ?_
      rintro _ ⟨xStar, rfl⟩
      exact hTermLeDual xStar
    · -- Evaluating at `xStar = 0` recovers the dual optimum exactly.
      exact le_sSup ⟨(0 : Fin n → ℝ), by simp [dualProgramOfConvexProgram]⟩
  refine ⟨-x, ?_⟩
  unfold IsKuhnTuckerVectorForDualProgram
  dsimp
  refine ⟨?_, ?_, hObjectiveEqDual⟩
  · -- Equality with the finite dual optimum rules out `⊤`.
    intro hTop
    exact hFiniteDual.1 (hObjectiveEqDual.symm.trans hTop)
  · -- The same equality rules out `⊥`.
    intro hBot
    exact hFiniteDual.2 (hObjectiveEqDual.symm.trans hBot)

/-- Helper for Theorem 6.30.17: the two bounded dual branches share the same remaining
transport problem from bounded Chapter 27 data for
`uStar ↦ fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar)` to primal strict
consistency. -/
lemma helperForTheorem_6_30_17_dualConjugateObjective_eq_negAdjointZeroSlice
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    (fun uStar : Fin m → ℝ =>
      fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar)) =
      (fun uStar : Fin m → ℝ =>
        -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  funext uStar
  have hDualSlice :
      concaveConjugate
          (fun u : Fin m → ℝ => -(convexProgramAssociatedWith F.1 u)) uStar =
        adjointOfConvexBifunction FCvx 0 uStar := by
    -- The dual zero slice is the concave conjugate of the negated primal perturbation.
    simpa [FCvx] using
      congrFun (dualObjectiveSlice_and_primalObjectiveSlice_are_conjugates (F := FCvx)).1 uStar
  -- Negating that identity rewrites the same slice as the conjugate objective `u* ↦ p*(-u*)`.
  calc
    fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar)
        =
          -(concaveConjugate
            (fun u : Fin m → ℝ => -(convexProgramAssociatedWith F.1 u)) uStar) := by
              simpa using
                (congrFun
                  (helperForTheorem_6_30_15_neg_concaveConjugate_eq_fenchel_precomp_neg
                    (g := fun u : Fin m → ℝ => -(convexProgramAssociatedWith F.1 u)))
                  uStar).symm
    _ = -adjointOfConvexBifunction FCvx 0 uStar := by
          rw [hDualSlice]

/-- Helper for Theorem 6.30.17: if the primal optimal set is nonempty and bounded but the
primal value is still non-finite, then the only remaining case is the `+∞` corner. In positive
dimension that forces the minimum set to be all of space, contradicting boundedness; in
dimension `0` the closed-slice identity rewrites the singleton primal value directly to the dual
value, so the existing value-equality normality sink applies. -/
lemma helperForTheorem_6_30_17_boundedPrimalOptimalSet_nonfiniteCorner
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1)
    (hMin : HasNonemptyBoundedPrimalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩)
    (hx : ∃ x : Fin n → ℝ, F.1 0 x = convexProgramAssociatedWith F.1 0)
    (hNotFinite : ¬ HasFinitePrimalOptimalValueOfConvexProgram ⟨F.1, F.2.1⟩) :
    IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
      IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let f : (Fin n → ℝ) → EReal := fun x : Fin n → ℝ => F.1 0 x
  have hPrimalNeBot :
      convexProgramAssociatedWith F.1 0 ≠ (⊥ : EReal) := by
    rcases hx with ⟨x, hx⟩
    intro hBot
    have hxBot : F.1 0 x = (⊥ : EReal) := by rw [hx, hBot]
    exact hProper.2.1.1 (Fin.append (0 : Fin m → ℝ) x) (by simpa [bifunctionGraphFunction] using hxBot)
  have hPrimalTop :
      convexProgramAssociatedWith F.1 0 = (⊤ : EReal) := by
    by_cases hTop : convexProgramAssociatedWith F.1 0 = (⊤ : EReal)
    · exact hTop
    · exfalso
      exact hNotFinite ⟨hTop, hPrimalNeBot⟩
  have hAllTop : ∀ y : Fin n → ℝ, f y = (⊤ : EReal) := by
    intro y
    have hyge : (⊤ : EReal) ≤ f y := by
      calc
        (⊤ : EReal) = convexProgramAssociatedWith F.1 0 := hPrimalTop.symm
        _ = functionInfimumEReal f := by rfl
        _ ≤ f y := by
              simpa [functionInfimumEReal] using (iInf_le (fun z : Fin n → ℝ => f z) y)
    exact top_unique hyge
  have hMinUniv : minimumSetEReal f = (Set.univ : Set (Fin n → ℝ)) := by
    ext y
    simp [minimumSetEReal, functionInfimumEReal, hAllTop]
  by_cases hnZero : n = 0
  · subst hnZero
    let q : (Fin 0 → ℝ) → EReal :=
      fun xStar : Fin 0 → ℝ =>
        -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar
    have hSliceEq :
        fenchelConjugate 0 q = (fun x : Fin 0 → ℝ => F.1 0 x) :=
      helperForTheorem_6_30_17_closed_primalSlice_eq_negDualConjugate_of_globalProperness
        (F := F) hProper
    have hFenchelZero :
        fenchelConjugate 0 q 0 = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
      -- In the zero-dimensional primal space the Fenchel conjugate at `0` collapses to the dual
      -- program value itself.
      unfold q dualProgramOfConvexProgram
      have hRange :
          Set.range (fun x : Fin m → ℝ => adjointOfConvexBifunction ⟨F.1, F.2.1⟩ default x) =
            Set.range (fun x : Fin m → ℝ => adjointOfConvexBifunction ⟨F.1, F.2.1⟩ (![] : Fin 0 → ℝ) x) := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          refine ⟨x, ?_⟩
          simp [Subsingleton.elim (default : Fin 0 → ℝ) (![] : Fin 0 → ℝ)]
        · rintro ⟨x, rfl⟩
          refine ⟨x, ?_⟩
          simp [Subsingleton.elim (default : Fin 0 → ℝ) (![] : Fin 0 → ℝ)]
      simpa [fenchelConjugate_eq_iSup, dualPerturbationFunctionOfConvexProgram,
        concaveProgramAssociatedWith] using congrArg sSup hRange
    have hValue :
        convexProgramAssociatedWith F.1 0 = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
      -- Route correction: once `n = 0`, the closed-slice identity can be evaluated directly at the
      -- unique primal point, so no separate contradiction argument is needed.
      calc
        convexProgramAssociatedWith F.1 0 = F.1 0 0 := by
          rw [convexProgramAssociatedWith]
          have hRange :
              Set.range (fun x : Fin 0 → ℝ => F.1 0 x) = {F.1 0 0} := by
            ext y
            constructor
            · rintro ⟨x, rfl⟩
              have hx : x = 0 := Subsingleton.elim _ _
              simp [hx]
            · intro hy
              simp at hy
              rcases hy with rfl
              refine ⟨0, ?_⟩
              have hZero : (0 : Fin 0 → ℝ) = ![] := Subsingleton.elim _ _
              simpa [hZero]
          rw [hRange]
          simp
        _ = fenchelConjugate 0 q 0 := by
              simpa [q] using (congrFun hSliceEq (0 : Fin 0 → ℝ)).symm
        _ = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := hFenchelZero
    have hDualCons :
        IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
      intro hDualBot
      exact hPrimalNeBot (hValue.trans hDualBot)
    exact
      helperForTheorem_6_30_17_normality_of_valueEquality_and_dualConsistency
        (F := F) hValue hDualCons
  · have hOptUniv :
        primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ =
          (Set.univ : Set (Fin n → ℝ)) := by
      simpa [f, primalOptimalSolutionSetOfConvexProgram] using hMinUniv
    have hNotBoundedUniv :
        ¬ Bornology.IsBounded (Set.univ : Set (Fin n → ℝ)) := by
      intro hbounded
      have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
      let i : Fin n := ⟨0, hnPos⟩
      have hboundedEval :
          Bornology.IsBounded (Function.eval i '' (Set.univ : Set (Fin n → ℝ))) := by
        simpa using
          (Bornology.IsBounded.image_eval
            (s := (Set.univ : Set (Fin n → ℝ))) hbounded i)
      have hEval :
          Function.eval i '' (Set.univ : Set (Fin n → ℝ)) = (Set.univ : Set ℝ) := by
        ext r
        constructor
        · intro _hr
          trivial
        · intro _hr
          refine ⟨Function.update 0 i r, trivial, ?_⟩
          simp [i]
      have hboundedUniv : Bornology.IsBounded (Set.univ : Set ℝ) := by
        simpa [hEval] using hboundedEval
      exact (NormedSpace.unbounded_univ (𝕜 := ℝ) (E := ℝ)) hboundedUniv
    -- In positive dimension the `+∞` corner makes every point a minimizer, contradicting the
    -- boundedness assumption on the optimal set.
    exact False.elim (hNotBoundedUniv (by simpa [hOptUniv] using hMin.2))

/-- Helper for Theorem 6.30.17: the two bounded dual branches share the same remaining
transport problem from bounded Chapter 27 data for
`uStar ↦ fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar)` to primal strict
consistency. -/
lemma helperForTheorem_6_30_17_boundedDualConjugateData_implies_primalStrictConsistency
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1)
    (hData :
      (∃ α : ℝ,
        (sublevelSetEReal
            (fun uStar : Fin m → ℝ =>
              fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))
            α).Nonempty ∧
          Bornology.IsBounded
            (sublevelSetEReal
              (fun uStar : Fin m → ℝ =>
                fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))
              α) ∧
          IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) ∨
      ((minimumSetEReal
          (fun uStar : Fin m → ℝ =>
            fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))).Nonempty ∧
        Bornology.IsBounded
          (minimumSetEReal
            (fun uStar : Fin m → ℝ =>
              fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))) ∧
        ∃ uStar : Fin m → ℝ,
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar =
            dualProgramOfConvexProgram ⟨F.1, F.2.1⟩)) :
    IsStrictlyConsistentConvexProgram ⟨F.1, F.2.1⟩ := by
  by_cases hmZero : m = 0
  · subst hmZero
    have hPrimalCons :
        IsConsistentConvexProgram ⟨F.1, F.2.1⟩ := by
      intro hTop
      have hAllTop : ∀ x : Fin n → ℝ, F.1 0 x = (⊤ : EReal) := by
        intro x
        have hLe : convexProgramAssociatedWith F.1 0 ≤ F.1 0 x := by
          exact sInf_le ⟨x, rfl⟩
        rw [hTop] at hLe
        exact top_unique hLe
      rcases hProper.2.1.2 with ⟨z, hz⟩
      have hTopGraph : bifunctionGraphFunction F.1 z = (⊤ : EReal) := by
        change F.1 (fun i : Fin 0 => z (Fin.castAdd n i)) (fun j : Fin n => z (Fin.natAdd 0 j)) =
            (⊤ : EReal)
        have hLeft : (fun i : Fin 0 => z (Fin.castAdd n i)) = (0 : Fin 0 → ℝ) :=
          Subsingleton.elim _ _
        rw [hLeft]
        exact hAllTop _
      exact hz hTopGraph
    have hDomUniv :
        effectiveDomain (Set.univ : Set (Fin 0 → ℝ)) (convexProgramAssociatedWith F.1) =
          Set.univ := by
      ext u
      have hu : u = 0 := Subsingleton.elim u 0
      constructor
      · intro _huMem
        trivial
      · intro _huMem
        simpa [effectiveDomain_eq, hu] using (lt_top_iff_ne_top.mpr hPrimalCons)
    -- In the zero-dimensional parameter space, primal consistency already makes the origin an
    -- interior point of the effective domain.
    exact ⟨hPrimalCons, by simpa [hDomUniv]⟩
  · let p : (Fin m → ℝ) → EReal := convexProgramAssociatedWith F.1
    let g : (Fin m → ℝ) → EReal :=
      fun uStar : Fin m → ℝ => fenchelConjugate m p (-uStar)
    have hpConv : ConvexFunction p := by
      -- The primal perturbation function is convex before any conjugation or boundedness input.
      simpa [p] using helperForTheorem_6_30_15_primalValueFunction_is_convex (F := ⟨F.1, F.2.1⟩)
    have hgEq :
        g =
          (fun uStar : Fin m → ℝ =>
            -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) :=
      helperForTheorem_6_30_17_dualConjugateObjective_eq_negAdjointZeroSlice (F := F)
    have hFenchelClosed :=
      fenchelConjugate_closedConvex (n := m) (f := fun u : Fin m → ℝ => p (-u))
    have hgClosed : ClosedConvexFunction g := by
      have hgPrecomp :
          fenchelConjugate m (fun u : Fin m → ℝ => p (-u)) = g := by
        simpa [g, p] using
          helperForTheorem_21_4_fenchelConjugate_precomp_neg (n := m) (g := p)
      refine ⟨?_, ?_⟩
      · simpa [hgPrecomp] using hFenchelClosed.2
      · simpa [hgPrecomp] using hFenchelClosed.1
    have hAdjProper :
        ProperConcaveBifunction (m := n) (n := m)
          (adjointOfConvexBifunction ⟨F.1, F.2.1⟩) := by
      -- Global properness of `F` transports to the adjoint through Theorem 6.30.11.
      exact
        (helperForTheorem_6_30_11_convex_branch_except_closed_fixed_point
          (F := F.1) (hF := F.2.1)).2.1.2 hProper
    have hgNeBot : ∀ uStar : Fin m → ℝ, g uStar ≠ (⊥ : EReal) := by
      intro uStar
      have hAdjNeTop :
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar ≠ (⊤ : EReal) := by
        simpa [ProperConcaveERealFunction, bifunctionGraphFunction] using
          hAdjProper.2.1.1 (Fin.append (0 : Fin n → ℝ) uStar)
      have hPointEq : g uStar = -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar := by
        simpa [g] using congrFun hgEq uStar
      simpa [hPointEq] using hAdjNeTop
    have hgProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) g := by
      refine ⟨?_, ?_, ?_⟩
      · -- `g` is a Fenchel conjugate, hence closed convex.
        simpa [ConvexFunction] using hgClosed.1
      · rcases hData with hSublevel | hMinimum
        · rcases hSublevel with ⟨α, hNonempty, _hBounded, _hDualCons⟩
          rcases hNonempty with ⟨uStar, huStar⟩
          -- A bounded nonempty sublevel set gives a concrete finite epigraph point.
          refine ⟨(uStar, α), ?_⟩
          constructor
          · exact Set.mem_univ uStar
          · simpa [g, sublevelSetEReal] using huStar
        · rcases hMinimum with ⟨_hNonemptyMin, hBoundedMin, huStar⟩
          rcases huStar with ⟨uStar, huStarEq⟩
          have huStarMin :
              uStar ∈ minimumSetEReal g := by
            have huStarDual :
                uStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ := huStarEq
            rw [(helperForTheorem_6_30_17_dualBoundedBranches_rewrite_as_primalConjugateData
              (F := F)).2] at huStarDual
            simpa [g] using huStarDual
          have hDualCons :
              IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
            intro hDualBot
            have huStarTop : g uStar = (⊤ : EReal) := by
              calc
                g uStar = -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar := by
                  simpa [g] using congrFun hgEq uStar
                _ = -(dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) := by rw [huStarEq]
                _ = (⊤ : EReal) := by simp [hDualBot]
            have hInfTop : functionInfimumEReal g = (⊤ : EReal) := by
              rw [minimumSetEReal] at huStarMin
              exact huStarMin.symm.trans huStarTop
            have hAllTop : ∀ v : Fin m → ℝ, g v = (⊤ : EReal) := by
              intro v
              have hvge : (⊤ : EReal) ≤ g v := by
                calc
                  (⊤ : EReal) = functionInfimumEReal g := hInfTop.symm
                  _ ≤ g v := by
                        simpa [functionInfimumEReal] using
                          (iInf_le (fun z : Fin m → ℝ => g z) v)
              exact top_unique hvge
            have hMinUniv : minimumSetEReal g = (Set.univ : Set (Fin m → ℝ)) := by
              ext v
              simp [minimumSetEReal, functionInfimumEReal, hAllTop]
            have hNotBoundedUniv :
                ¬ Bornology.IsBounded (Set.univ : Set (Fin m → ℝ)) := by
              intro hbounded
              have hmPos : 0 < m := Nat.pos_of_ne_zero hmZero
              let i : Fin m := ⟨0, hmPos⟩
              have hboundedEval :
                  Bornology.IsBounded (Function.eval i '' (Set.univ : Set (Fin m → ℝ))) := by
                simpa using
                  (Bornology.IsBounded.image_eval
                    (s := (Set.univ : Set (Fin m → ℝ))) hbounded i)
              have hEval :
                  Function.eval i '' (Set.univ : Set (Fin m → ℝ)) = (Set.univ : Set ℝ) := by
                ext r
                constructor
                · intro _hr
                  trivial
                · intro _hr
                  refine ⟨Function.update 0 i r, trivial, ?_⟩
                  simp [i]
              have hboundedUniv : Bornology.IsBounded (Set.univ : Set ℝ) := by
                simpa [hEval] using hboundedEval
              exact (NormedSpace.unbounded_univ (𝕜 := ℝ) (E := ℝ)) hboundedUniv
            have hBoundedMinG : Bornology.IsBounded (minimumSetEReal g) := by
              simpa [g] using hBoundedMin
            have hBoundedUniv : Bornology.IsBounded (Set.univ : Set (Fin m → ℝ)) := by
              simpa [hMinUniv] using hBoundedMinG
            exact hNotBoundedUniv hBoundedUniv
          have huStarNeTop : g uStar ≠ (⊤ : EReal) := by
            intro huStarTop
            have hEqNeg :
                g uStar = -(dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) := by
              calc
                g uStar = -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar := by
                  simpa [g] using congrFun hgEq uStar
                _ = -(dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) := by rw [huStarEq]
            have hDualBot : dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal) := by
              have : -(dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) = (⊤ : EReal) := by
                calc
                  -(dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) = g uStar := hEqNeg.symm
                  _ = (⊤ : EReal) := huStarTop
              have := congrArg Neg.neg this
              simpa using this
            exact hDualCons hDualBot
          refine ⟨(uStar, (g uStar).toReal), ?_⟩
          refine (mem_epigraph_univ_iff (f := g)).2 ?_
          have hToReal : (((g uStar).toReal : ℝ) : EReal) = g uStar := by
            simpa using (EReal.coe_toReal (x := g uStar) huStarNeTop (hgNeBot uStar))
          exact le_of_eq hToReal.symm
      · intro uStar _huStar
        exact hgNeBot uStar
    have hInteriorFenchel :
        (0 : Fin m → ℝ) ∈
          interior (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fenchelConjugate m g)) := by
      rcases hData with hSublevel | hMinimum
      · rcases hSublevel with ⟨α, hNonempty, hBounded, _hDualCons⟩
        rcases closedProperConvexFunction_minimum_characterizations g hgClosed hgProper with
          ⟨_hA, _hB, _hC, hD, _hE, hF, _hG, _hH, _hI⟩
        have hSubClosed : IsClosed (sublevelSetEReal g α) := by
          -- Closedness of `g` makes its real sublevel sets closed.
          exact (lowerSemicontinuous_iff_closed_sublevel (f := g)).1 hgClosed.2 α
        have hSubConvex : Convex ℝ (sublevelSetEReal g α) := by
          -- Convexity of `g` makes each sublevel set convex.
          simpa [sublevelSetEReal] using
            (convexFunction_level_sets_convex
              (f := g) hgClosed.1 (α := ((α : ℝ) : EReal))).2
        have hSubRecZero :
            Set.recessionCone (sublevelSetEReal g α) = ({0} : Set (Fin m → ℝ)) := by
          -- A nonempty bounded convex level set has trivial recession cone.
          exact
            (helperForText_21_3_3_bounded_iff_recessionCone_eq_singleton_zero_fin
              (S := sublevelSetEReal g α) hNonempty hSubClosed hSubConvex).1 hBounded
        have hNoRecession : HasNoRecessionDirections g := by
          intro y hy
          have hyRec : y ∈ recessionConeEReal (F := Fin m → ℝ) g := by
            simpa [recessionConeEReal, IsRecessionDirection, recessionFunctionEReal,
              recessionFunction, erealDom, effectiveDomain_eq] using hy
          have hySub :
              y ∈ Set.recessionCone (sublevelSetEReal g α) := by
            rw [hF.2.2.1 α hNonempty]
            exact hyRec
          have hyZero : y ∈ ({0} : Set (Fin m → ℝ)) := by
            simpa [hSubRecZero] using hySub
          simpa using hyZero
        exact hD.2.2 hNoRecession
      · have hMinData :
            (minimumSetEReal g).Nonempty ∧
              Bornology.IsBounded (minimumSetEReal g) := by
          rcases hMinimum with ⟨hNonemptyMin, hBoundedMin, _huStar⟩
          exact ⟨by simpa [g] using hNonemptyMin, by simpa [g] using hBoundedMin⟩
        exact
          (helperForTheorem_6_27_1_minimumSet_nonempty_bounded_iff_zero_mem_interior_dom_conjugate
            g hgClosed hgProper).1 hMinData
    have hpStarProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fenchelConjugate m p) := by
      refine ⟨?_, ?_, ?_⟩
      · -- `p*` is convex because it is a Fenchel conjugate.
        simpa [ConvexFunction] using (fenchelConjugate_closedConvex (n := m) (f := p)).2
      · rcases hgProper.2.1 with ⟨pt, hpt⟩
        rcases pt with ⟨uStar, t⟩
        refine ⟨(-uStar, t), ?_⟩
        constructor
        · trivial
        · have hle : g uStar ≤ (t : EReal) := (mem_epigraph_univ_iff (f := g)).1 hpt
          simpa [g, p] using hle
      · intro uStar _huStar
        simpa [g, p] using hgProper.2.2 (-uStar) (by trivial)
    have hpProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p := by
      -- Properness of `g(u*) = p*(-u*)` transports back to `p` through Fenchel duality.
      exact
        (fenchelConjugate_closedConvex_proper_iff_and_biconjugate
          (n := m) (f := p) hpConv).2.1.mp hpStarProper
    have hClosureInterior :
        (0 : Fin m → ℝ) ∈
          interior
            (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (convexClosure p)) := by
      have hBiconj :
          fenchelConjugate m (fenchelConjugate m p) = convexClosure p := by
        simpa [convexClosure] using
          (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
            (n := m) (f := p) hpConv)
      have hFenchelEq :
          fenchelConjugate m g = (fun u : Fin m → ℝ => convexClosure p (-u)) := by
        calc
          fenchelConjugate m g
              = fun u : Fin m → ℝ => fenchelConjugate m (fenchelConjugate m p) (-u) := by
                  simpa [g, p] using
                    (helperForTheorem_21_4_fenchelConjugate_precomp_neg
                      (n := m) (g := fenchelConjugate m p))
          _ = (fun u : Fin m → ℝ => convexClosure p (-u)) := by
                funext u
                simpa using congrFun hBiconj (-u)
      have hSetEq :
          effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fenchelConjugate m g) =
            (fun u : Fin m → ℝ => -u) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) (convexClosure p) := by
        ext u
        simp [effectiveDomain_eq, hFenchelEq]
      have hPreimageInterior :
          (0 : Fin m → ℝ) ∈
            interior
              ((fun u : Fin m → ℝ => -u) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin m → ℝ)) (convexClosure p)) := by
        simpa [hSetEq] using hInteriorFenchel
      have hInteriorNeg :
          (0 : Fin m → ℝ) ∈
            interior
              (-(effectiveDomain (Set.univ : Set (Fin m → ℝ)) (convexClosure p))) := by
        simpa using hPreimageInterior
      have hImageInterior :
          interior (-(effectiveDomain (Set.univ : Set (Fin m → ℝ)) (convexClosure p))) =
            -(interior
              (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (convexClosure p))) := by
        simpa using
          (Homeomorph.image_interior (Homeomorph.neg (Fin m → ℝ))
            (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (convexClosure p))).symm
      have hNegMem :
          (0 : Fin m → ℝ) ∈
            -(interior
              (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (convexClosure p))) := by
        simpa [hImageInterior] using hInteriorNeg
      simpa using hNegMem
    have hActualInterior :
        (0 : Fin m → ℝ) ∈
          interior (effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) :=
      helperForCorollary_25_1_2_mem_interior_effectiveDomain_of_closure_mem_interior
        hpProper hClosureInterior
    exact ⟨by
      -- Interior points lie in the effective domain, so primal consistency comes for free.
      have h0Mem : (0 : Fin m → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ)) p :=
        interior_subset hActualInterior
      simpa [p, effectiveDomain_eq, IsConsistentConvexProgram, lt_top_iff_ne_top] using h0Mem,
      hActualInterior⟩

/-- Helper for Theorem 6.30.17: the remaining primal-side terminal branches are exactly the
polyhedral primal branch `(e)` together with the bounded primal sublevel and bounded primal
optimal-set branches `(g)` and `(i)`. -/
lemma helperForTheorem_6_30_17_primalPolyhedralOrBoundedBranches_imply_normality
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1)
    (hPrimalTerminal :
      (PolyhedralConvexBifunction F.1 ∧ IsConsistentConvexProgram ⟨F.1, F.2.1⟩) ∨
        (∃ α : ℝ, (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α).Nonempty ∧
          Bornology.IsBounded (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α)) ∨
        HasNonemptyBoundedPrimalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) :
    IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
      IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  rcases hPrimalTerminal with hPolyPrimal | hPrimalBounded
  · -- Branch `(e)` is now fully discharged by the polyhedral Chapter 29 Kuhn--Tucker route and
    -- the residual `-∞` case handled by weak duality.
    exact
      helperForTheorem_6_30_17_normality_of_polyhedralPrimal_and_consistency
        (F := F) hPolyPrimal.1 hPolyPrimal.2
  have hPrimalBoundedData :
      (∃ α : ℝ,
        (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α).Nonempty ∧
          Bornology.IsBounded (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α) ∧
          IsConsistentConvexProgram ⟨F.1, F.2.1⟩) ∨
      (HasNonemptyBoundedPrimalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
        ∃ x : Fin n → ℝ, F.1 0 x = convexProgramAssociatedWith F.1 0) :=
    helperForTheorem_6_30_17_primalBoundedTerminal_extract_bridgeData
      (F := F) hPrimalBounded
  have hPrimalSliceEq :
      fenchelConjugate n
          (fun xStar : Fin n → ℝ =>
            -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar) =
        (fun x : Fin n → ℝ => F.1 0 x) :=
    helperForTheorem_6_30_17_closed_primalSlice_eq_negDualConjugate_of_globalProperness
      (F := F) hProper
  rcases hPrimalBoundedData with hBoundedSublevel | hBoundedOptimal
  · rcases hBoundedSublevel with ⟨α, hNonempty, hBounded, hPrimalCons⟩
    let f : (Fin n → ℝ) → EReal := fun x : Fin n → ℝ => F.1 0 x
    have hfProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
      refine ⟨?_, ?_, ?_⟩
      · -- The primal zero slice is convex because it is the Fenchel conjugate of `q`.
        let q : (Fin n → ℝ) → EReal :=
          fun xStar : Fin n → ℝ =>
            -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar
        have hFenchelClosed := fenchelConjugate_closedConvex (n := n) (f := q)
        simpa [ConvexFunction, f] using (hPrimalSliceEq ▸ hFenchelClosed.2)
      · -- The bounded sublevel witness gives one finite point on the zero slice.
        rcases hNonempty with ⟨x, hx⟩
        refine ⟨(x, α), ?_⟩
        constructor
        · exact Set.mem_univ x
        · simpa [f, primalSublevelSetOfConvexProgram, sublevelSetEReal] using hx
      · -- Global properness rules out graph-level `⊥`, hence also `⊥` on the zero slice.
        intro x _hx
        simpa [f, bifunctionGraphFunction] using
          hProper.2.1.1 (Fin.append (0 : Fin m → ℝ) x)
    have hClosedDualInterior :
        (0 : Fin n → ℝ) ∈
          interior
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fun xStar : Fin n → ℝ =>
                -(concaveClosure
                  (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) xStar))) :=
      helperForTheorem_6_30_17_boundedPrimalSublevel_implies_interior_closedDualDomain
        (F := F) hProper hNonempty hBounded
    have hClosedBranch :=
      (dualObjectiveSlice_and_primalObjectiveSlice_are_conjugates
        (F := ⟨F.1, F.2.1⟩)).2.2 ⟨F.2, hProper⟩
    have hInteriorConjugate :
        (0 : Fin n → ℝ) ∈
          interior
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
      -- Rewrite the closed dual-domain interior statement back to the conjugate of the zero
      -- slice so the generic transport helper can finish the argument.
      simpa [f] using (hClosedBranch.2.symm ▸ hClosedDualInterior)
    have hDualStrict :
        IsStrictlyConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_dualStrictConsistency_of_zeroSliceProper_and_interior_conjugate
        (F := F) hProper hfProper hInteriorConjugate
    have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_valueEquality_of_dualStrongOrStrictConsistency
        (F := F) hProper (Or.inr hDualStrict)
    -- The primal bounded-sublevel branch now lands in the existing primal-consistency sink.
    exact
      helperForTheorem_6_30_17_normality_of_valueEquality_and_primalConsistency
        (F := F) hValue hPrimalCons
  · -- The bounded minimum-set branch is still waiting on the same closure-to-actual-domain
    -- transport, but the transport itself is now factored out above. The finite-value subcase is
    -- already enough to recover properness of the zero slice and hence the Section 27 interior
    -- criterion; only the non-finite corner remains isolated below.
    rcases hBoundedOptimal with ⟨hMin, hx⟩
    let f : (Fin n → ℝ) → EReal := fun x : Fin n → ℝ => F.1 0 x
    have hClosedBranch :=
      (dualObjectiveSlice_and_primalObjectiveSlice_are_conjugates
        (F := ⟨F.1, F.2.1⟩)).2.2 ⟨F.2, hProper⟩
    have hfClosed : ClosedConvexFunction f := by
      let q : (Fin n → ℝ) → EReal :=
        fun xStar : Fin n → ℝ =>
          -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar
      have hFenchelClosed := fenchelConjugate_closedConvex (n := n) (f := q)
      refine ⟨?_, ?_⟩
      · simpa [ConvexFunction, f] using (hPrimalSliceEq ▸ hFenchelClosed.2)
      · simpa [f] using (hPrimalSliceEq ▸ hFenchelClosed.1)
    by_cases hFinite : HasFinitePrimalOptimalValueOfConvexProgram ⟨F.1, F.2.1⟩
    · have hfProper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
        refine ⟨?_, ?_, ?_⟩
        · -- Convexity on `Set.univ` is the restricted form of the closed-convex slice.
          simpa [ConvexFunction, f] using hfClosed.1
        · -- Route correction: in the finite-value subcase, a finite zero-slice witness gives the
          -- required epigraph point directly, so no extra transport lemma is needed here.
          rcases
              helperForTheorem_6_30_17_exists_finite_zeroSliceValue_of_finitePrimalValue
                (F := F) hFinite with
            ⟨x0, hx0NeTop, hx0NeBot⟩
          refine ⟨(x0, (F.1 0 x0).toReal), ?_⟩
          exact
            (mem_epigraph_univ_iff (f := f)).2
              (by simp [f, EReal.coe_toReal hx0NeTop hx0NeBot])
        · -- Global properness still removes every graph-level `⊥`, hence also `⊥` on the zero
          -- slice.
          intro x _hx
          simpa [f, bifunctionGraphFunction] using
            hProper.2.1.1 (Fin.append (0 : Fin m → ℝ) x)
      have hMinData :
          (minimumSetEReal f).Nonempty ∧ Bornology.IsBounded (minimumSetEReal f) := by
        simpa [f, primalOptimalSolutionSetOfConvexProgram, convexProgramAssociatedWith,
          minimumSetEReal, functionInfimumEReal] using hMin
      have hInteriorConjugate :
          (0 : Fin n → ℝ) ∈
            interior
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
        exact
          (helperForTheorem_6_27_1_minimumSet_nonempty_bounded_iff_zero_mem_interior_dom_conjugate
            f hfClosed hfProper).1 hMinData
      have hDualStrict :
          IsStrictlyConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
        helperForTheorem_6_30_17_dualStrictConsistency_of_zeroSliceProper_and_interior_conjugate
          (F := F) hProper hfProper (by simpa [f] using hInteriorConjugate)
      have hValue :
          convexProgramAssociatedWith F.1 0 =
            dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
        helperForTheorem_6_30_17_valueEquality_of_dualStrongOrStrictConsistency
          (F := F) hProper (Or.inr hDualStrict)
      -- Once the primal value is finite, value equality alone already yields both normality
      -- identities.
      exact
        helperForTheorem_6_30_17_normality_of_finiteValueEquality
          (F := F) hFinite hValue
    · let _ := hMin
      let _ := hx
      let _ := hfClosed
      let _ := hClosedBranch
      -- Route correction: the residual `¬ hFinite` branch is the isolated `+∞` corner. Once that
      -- corner is classified, the bounded optimal-set package either contradicts positive
      -- dimensionality or reduces the singleton `n = 0` case to direct primal-dual value
      -- equality.
      exact
        helperForTheorem_6_30_17_boundedPrimalOptimalSet_nonfiniteCorner
          (F := F) hProper hMin hx hFinite

/-- Helper for Theorem 6.30.17: the remaining dual-side terminal branches are exactly the
polyhedral dual branch `(f)` together with the bounded dual superlevel and bounded dual
optimal-set branches `(h)` and `(j)`. -/
lemma helperForTheorem_6_30_17_dualPolyhedralOrBoundedBranches_imply_normality
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1)
    (hDualTerminal :
      (PolyhedralConcaveBifunction (m := n) (n := m)
          (adjointOfConvexBifunction ⟨F.1, F.2.1⟩) ∧
        IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) ∨
        (∃ β : ℝ, (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β).Nonempty ∧
          Bornology.IsBounded (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β)) ∨
        HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) :
    IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
      IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  rcases hDualTerminal with hPolyDual | hDualBounded
  · have hPolyPrimal :
      PolyhedralConvexBifunction F.1 :=
    helperForTheorem_6_30_17_polyhedralDual_implies_polyhedralPrimal_of_globalProperness
      (F := F) hProper hPolyDual.1
    by_cases hFiniteDual :
        HasFiniteDualOptimalValueOfConvexProgram ⟨F.1, F.2.1⟩
    · -- Route correction: the finite polyhedral dual branch now closes by extracting a Chapter 30
      -- dual Kuhn--Tucker vector from the generalized Kuhn--Tucker theorem for `- adjoint(F)`.
      have hKT :
          ∃ x : Fin n → ℝ, IsKuhnTuckerVectorForDualProgram ⟨F.1, F.2.1⟩ x :=
        helperForTheorem_6_30_17_dualKuhnTucker_of_polyhedral_negAdjoint_and_finiteDualValue
          (F := F) hProper hPolyDual.1 hFiniteDual
      have hValue :
          convexProgramAssociatedWith F.1 0 =
            dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
        helperForTheorem_6_30_17_valueEquality_of_finiteDualValue_and_dualKuhnTuckerVector
          (F := F) hFiniteDual hKT
      exact
        helperForTheorem_6_30_17_normality_of_valueEquality_and_dualConsistency
          (F := F) hValue hPolyDual.2
    · have hDualTop :
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊤ : EReal) := by
        by_cases hDualNeTop :
            dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊤ : EReal)
        · exact hDualNeTop
        · exfalso
          exact hFiniteDual ⟨hDualNeTop, hPolyDual.2⟩
      have hDualLePrimal :
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ≤ convexProgramAssociatedWith F.1 0 := by
        -- Weak duality still bounds the dual value above by the primal value at the origin.
        simpa [dualProgramOfConvexProgram, dualPerturbationFunctionOfConvexProgram,
          concaveProgramAssociatedWith, convexProgramAssociatedWith] using
          helperForCorollary_6_30_2_weakDuality_at_zero (F := F)
      have hPrimalTop :
          convexProgramAssociatedWith F.1 0 = (⊤ : EReal) := by
        -- Once the dual value is `⊤`, weak duality forces the primal value to be `⊤` as well.
        exact top_unique (by simpa [hDualTop] using hDualLePrimal)
      have hValue :
          convexProgramAssociatedWith F.1 0 =
            dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
        hPrimalTop.trans hDualTop.symm
      exact
        helperForTheorem_6_30_17_normality_of_valueEquality_and_dualConsistency
          (F := F) hValue hPolyDual.2
  rcases hDualBounded with hBoundedSuperlevel | hBoundedOptimal
  · rcases hBoundedSuperlevel with ⟨β, hNonempty, hBounded⟩
    have hConjugateBounded :
        (∃ α : ℝ,
          (sublevelSetEReal
              (fun uStar : Fin m → ℝ =>
                fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))
              α).Nonempty ∧
            Bornology.IsBounded
              (sublevelSetEReal
                (fun uStar : Fin m → ℝ =>
                  fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))
                α)) := by
      exact
        helperForTheorem_6_30_17_dualBoundedSuperlevel_implies_conjugateSublevelData
          (F := F) ⟨β, hNonempty, hBounded⟩
    have hDualWitnessBounded :
        ∃ β : ℝ, (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β).Nonempty ∧
          Bornology.IsBounded (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β) ∧
          IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
      refine ⟨β, hNonempty, hBounded, ?_⟩
      exact
        helperForTheorem_6_30_17_dualSuperlevel_nonempty_implies_dualConsistency
          (F := F) hNonempty
    have hPrimalStrict :
        IsStrictlyConsistentConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_boundedDualConjugateData_implies_primalStrictConsistency
        (F := F) hProper (Or.inl <| by
          rcases hConjugateBounded with ⟨α, hNonempty', hBounded'⟩
          rcases hDualWitnessBounded with ⟨_, _, _, hDualCons⟩
          exact ⟨α, hNonempty', hBounded', hDualCons⟩)
    have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_valueEquality_of_primalStrongOrStrictConsistency
        (F := F) (Or.inr hPrimalStrict)
    exact
      helperForTheorem_6_30_17_normality_of_valueEquality_and_primalConsistency
        (F := F) hValue hPrimalStrict.1
  · have hConjugateBounded :
        (minimumSetEReal
            (fun uStar : Fin m → ℝ =>
              fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))).Nonempty ∧
          Bornology.IsBounded
            (minimumSetEReal
              (fun uStar : Fin m → ℝ =>
                fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))) :=
      helperForTheorem_6_30_17_dualBoundedOptimalSet_implies_conjugateMinimumData
        (F := F) hBoundedOptimal
    have hDualWitnessBounded :
        HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
          ∃ uStar : Fin m → ℝ,
            adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar =
              dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
      refine ⟨hBoundedOptimal, ?_⟩
      exact
        helperForTheorem_6_30_17_exists_dualZeroSlice_attaining_dualValue
          (F := F) hBoundedOptimal.1
    have hPrimalStrict :
        IsStrictlyConsistentConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_boundedDualConjugateData_implies_primalStrictConsistency
        (F := F) hProper (Or.inr <| by
          rcases hConjugateBounded with ⟨hNonempty', hBounded'⟩
          rcases hDualWitnessBounded with ⟨_, hWitness⟩
          exact ⟨hNonempty', hBounded', hWitness⟩)
    have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_valueEquality_of_primalStrongOrStrictConsistency
        (F := F) (Or.inr hPrimalStrict)
    exact
      helperForTheorem_6_30_17_normality_of_valueEquality_and_primalConsistency
        (F := F) hValue hPrimalStrict.1

end Section30
end Chap06
