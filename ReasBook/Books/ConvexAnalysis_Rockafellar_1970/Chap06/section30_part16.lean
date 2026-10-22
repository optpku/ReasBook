/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part15

section Chap06
section Section30

-- Proof sketch: apply Theorem 6.30.17 to the strong-consistency hypothesis to obtain normality
-- of the primal-dual pair. Then use the attainment criterion encoded in Theorem 6.30.19 to
-- identify optimal solutions with Kuhn--Tucker vectors, and conclude existence of a primal
-- optimizer from primal consistency plus strong dual consistency, and dually for the dual
-- optimizer from dual consistency plus strong primal consistency.
/-- Helper for Corollary 6.30.5: primal consistency together with strong dual consistency yields
a Chapter 30 dual Kuhn--Tucker vector by applying Corollary 6.29.4 to the generalized program
with perturbation `x* ↦ - sup_{u*} F*(x*, u*)`. -/
lemma helperForCorollary_6_30_5_exists_dualKuhnTucker_of_primalConsistency_and_strongDualConsistency
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hP : IsConsistentConvexProgram ⟨F.1, F.2.1⟩)
    (hPStarStrong : IsStronglyConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) :
    ∃ x : Fin n → ℝ, IsKuhnTuckerVectorForDualProgram ⟨F.1, F.2.1⟩ x := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  have hDualCons : IsConsistentDualProgramOfConvexProgram FCvx := hPStarStrong.1
  have hDualLePrimal :
      dualProgramOfConvexProgram FCvx ≤ convexProgramAssociatedWith F.1 0 := by
    -- Weak duality controls the dual value by the primal zero-slice infimum.
    simpa [FCvx, dualProgramOfConvexProgram, dualPerturbationFunctionOfConvexProgram,
      concaveProgramAssociatedWith, convexProgramAssociatedWith] using
      helperForCorollary_6_30_2_weakDuality_at_zero (F := F)
  have hDualNeTop : dualProgramOfConvexProgram FCvx ≠ (⊤ : EReal) := by
    -- Primal consistency excludes `+∞` for the primal value, hence also for the dual value.
    intro hDualTop
    have hPrimalTop : convexProgramAssociatedWith F.1 0 = (⊤ : EReal) := by
      have hTopLe : (⊤ : EReal) ≤ convexProgramAssociatedWith F.1 0 := by
        simpa [hDualTop] using hDualLePrimal
      exact top_unique hTopLe
    exact hP hPrimalTop
  have hPrimalNeBot : convexProgramAssociatedWith F.1 0 ≠ (⊥ : EReal) := by
    -- Dual consistency excludes `-∞` for the dual value, so weak duality rules out primal `-∞`.
    intro hPrimalBot
    have hDualBot : dualProgramOfConvexProgram FCvx = (⊥ : EReal) := by
      have hDualLeBot : dualProgramOfConvexProgram FCvx ≤ (⊥ : EReal) := by
        simpa [hPrimalBot] using hDualLePrimal
      exact le_antisymm hDualLeBot bot_le
    exact hDualCons hDualBot
  have hFiniteDual : HasFiniteDualOptimalValueOfConvexProgram FCvx := ⟨hDualNeTop, hDualCons⟩
  have hFinitePrimal : HasFinitePrimalOptimalValueOfConvexProgram FCvx := ⟨hP, hPrimalNeBot⟩
  have hProper : ProperConvexBifunction F.1 :=
    helperForTheorem_6_30_17_properConvexBifunction_of_finitePrimalValue
      (F := F) hFinitePrimal
  let gDual : (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
    fun xStar : Fin n → ℝ => fun uStar : Fin m → ℝ =>
      -adjointOfConvexBifunction FCvx xStar uStar
  have hGConv30 : ConvexBifunction gDual := by
    -- The negated adjoint is convex because the adjoint itself is concave.
    simpa [gDual, ConvexBifunction, ConcaveBifunction, bifunctionGraphFunction] using
      (adjointOfConvexBifunctionAsConcave FCvx).2
  have hAdjProper :
      ProperConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction FCvx) := by
    -- Global properness transports to the adjoint via Theorem 6.30.11.
    exact
      (helperForTheorem_6_30_11_convex_branch_except_closed_fixed_point
        (F := F.1) (hF := F.2.1)).2.1.2 hProper
  have hNoGraphBotG :
      ∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ, gDual xStar uStar ≠ (⊥ : EReal) := by
    intro xStar uStar
    have hAdjNeTop :
        adjointOfConvexBifunction FCvx xStar uStar ≠ (⊤ : EReal) := by
      simpa [ProperConcaveERealFunction, bifunctionGraphFunction] using
        hAdjProper.2.1.1 (Fin.append xStar uStar)
    simpa [gDual] using hAdjNeTop
  let G : BundledConvexBifunction n m :=
    ⟨gDual,
      helperForTheorem_6_30_17_isConvexBifunction_of_convexBifunction
        hGConv30 hNoGraphBotG⟩
  have hPertEq :
      generalizedConvexProgramPerturbationFunction G =
        fun xStar : Fin n → ℝ =>
          -dualPerturbationFunctionOfConvexProgram FCvx xStar := by
    funext xStar
    -- The generalized perturbation of `G` is the negative dual perturbation of `F`.
    calc
      generalizedConvexProgramPerturbationFunction G xStar
          = sInf (Set.range (gDual xStar)) := by
              rfl
      _ = sInf (Set.range fun uStar : Fin m → ℝ =>
            -adjointOfConvexBifunction FCvx xStar uStar) := by
            rfl
      _ = -sSup (Set.range fun uStar : Fin m → ℝ =>
            adjointOfConvexBifunction FCvx xStar uStar) := by
            simpa [sInf_range, sSup_range] using
              (congrArg Neg.neg
                (ereal_iSup_neg_eq_neg_iInf
                  (g := fun uStar : Fin m → ℝ =>
                    -adjointOfConvexBifunction FCvx xStar uStar))).symm
      _ = -dualPerturbationFunctionOfConvexProgram FCvx xStar := by
            simp [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith]
  have hOptEq :
      generalizedConvexProgramOptimalValue G = -(dualProgramOfConvexProgram FCvx) := by
    -- Evaluating at `0` identifies the generalized optimal value with the negated dual optimum.
    calc
      generalizedConvexProgramOptimalValue G
          = generalizedConvexProgramPerturbationFunction G 0 := by
              simpa using helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero G
      _ = -dualPerturbationFunctionOfConvexProgram FCvx 0 := by
            simpa using congrFun hPertEq (0 : Fin n → ℝ)
      _ = -(dualProgramOfConvexProgram FCvx) := by
            simp [dualProgramOfConvexProgram]
  have hFiniteGeneral : IsFiniteEReal (generalizedConvexProgramOptimalValue G) := by
    -- Negation preserves finiteness.
    rw [hOptEq]
    constructor
    · intro hTop
      have hDualBot : dualProgramOfConvexProgram FCvx = (⊥ : EReal) := by
        simpa using congrArg Neg.neg hTop
      exact hFiniteDual.2 hDualBot
    · intro hBot
      have hDualTop : dualProgramOfConvexProgram FCvx = (⊤ : EReal) := by
        simpa using congrArg Neg.neg hBot
      exact hFiniteDual.1 hDualTop
  have hriPerturbation :
      (0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (generalizedConvexProgramPerturbationFunction G)) := by
    -- Rewrite the strong-dual-consistency relative interior into the perturbation domain of `G`.
    rw [hPertEq]
    rw [helperForTheorem_6_30_17_effectiveDomain_negDualPerturbation (F := F)]
    simpa [FCvx] using hPStarStrong.2
  have hdomPerturbation :
      effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (generalizedConvexProgramPerturbationFunction G) =
        bifunctionEffectiveDomain G.1 := by
    calc
      effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (generalizedConvexProgramPerturbationFunction G)
          = erealDom (generalizedConvexProgramPerturbationFunction G) := by
              ext xStar
              simp [effectiveDomain_eq, erealDom]
      _ = bifunctionEffectiveDomain G.1 :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker G).2.1
  have hStrongGeneral : generalizedConvexProgramStronglyConsistent G := by
    -- This is exactly the Section 29 strong-consistency condition for `G`.
    unfold generalizedConvexProgramStronglyConsistent
    rw [← hdomPerturbation]
    exact hriPerturbation
  have hKTGeneral :=
    generalizedConvexProgram_exists_kuhnTuckerVector_and_originDirectionalDerivative_eq_neg_sInf
      G hFiniteGeneral (Or.inl hStrongGeneral)
  rcases hKTGeneral.1 with ⟨x, hx⟩
  rcases hx with ⟨_hOptNeTop, _hOptNeBot, hLower⟩
  have hTermLeDual :
      ∀ xStar : Fin n → ℝ,
        ((((-x) ⬝ᵥ xStar : ℝ) : EReal) +
          dualPerturbationFunctionOfConvexProgram FCvx xStar) ≤
            dualProgramOfConvexProgram FCvx := by
    intro xStar
    have hLower' := hLower xStar
    have hLower'' :
        (-dualPerturbationFunctionOfConvexProgram FCvx xStar) +
            (((x ⬝ᵥ xStar : ℝ) : EReal)) ≥
          -(dualProgramOfConvexProgram FCvx) := by
      simpa [hPertEq, hOptEq] using hLower'
    have hLowerOrdered :
        -(dualProgramOfConvexProgram FCvx) ≤
          (((x ⬝ᵥ xStar : ℝ) : EReal) +
            -dualPerturbationFunctionOfConvexProgram FCvx xStar) := by
      simpa [add_comm] using hLower''
    have hNeg :
        -((((x ⬝ᵥ xStar : ℝ) : EReal) +
            -dualPerturbationFunctionOfConvexProgram FCvx xStar)) ≤
          dualProgramOfConvexProgram FCvx := by
      simpa using (EReal.neg_le_neg_iff.mpr hLowerOrdered)
    have hNegAdd :
        -((((x ⬝ᵥ xStar : ℝ) : EReal) +
            -dualPerturbationFunctionOfConvexProgram FCvx xStar)) =
          -(((x ⬝ᵥ xStar : ℝ) : EReal)) -
            (-dualPerturbationFunctionOfConvexProgram FCvx xStar) := by
      have hLeftNeBot : (((x ⬝ᵥ xStar : ℝ) : EReal)) ≠ (⊥ : EReal) := by
        simp
      have hLeftNeTop : (((x ⬝ᵥ xStar : ℝ) : EReal)) ≠ (⊤ : EReal) := by
        simp
      exact
        EReal.neg_add
          (x := (((x ⬝ᵥ xStar : ℝ) : EReal)))
          (y := -dualPerturbationFunctionOfConvexProgram FCvx xStar)
          (Or.inl hLeftNeBot)
          (Or.inl hLeftNeTop)
    calc
      ((((-x) ⬝ᵥ xStar : ℝ) : EReal) +
          dualPerturbationFunctionOfConvexProgram FCvx xStar)
          = -((((x ⬝ᵥ xStar : ℝ) : EReal) +
              -dualPerturbationFunctionOfConvexProgram FCvx xStar)) := by
                rw [hNegAdd]
                simp [sub_eq_add_neg]
      _ ≤ dualProgramOfConvexProgram FCvx := hNeg
  have hObjectiveEqDual :
      sSup (Set.range fun xStar : Fin n → ℝ =>
          ((((-x) ⬝ᵥ xStar : ℝ) : EReal) +
            dualPerturbationFunctionOfConvexProgram FCvx xStar)) =
        dualProgramOfConvexProgram FCvx := by
    apply le_antisymm
    · -- Every affine-dual term lies below the dual optimum.
      refine sSup_le ?_
      rintro _ ⟨xStar, rfl⟩
      exact hTermLeDual xStar
    · -- The term at `xStar = 0` equals the dual optimum.
      have hMem :
          ((((-x) ⬝ᵥ (0 : Fin n → ℝ) : ℝ) : EReal) +
              dualPerturbationFunctionOfConvexProgram FCvx (0 : Fin n → ℝ)) ∈
            Set.range (fun xStar : Fin n → ℝ =>
              ((((-x) ⬝ᵥ xStar : ℝ) : EReal) +
                dualPerturbationFunctionOfConvexProgram FCvx xStar)) := by
        exact ⟨(0 : Fin n → ℝ), rfl⟩
      calc
        dualProgramOfConvexProgram FCvx
            = ((((-x) ⬝ᵥ (0 : Fin n → ℝ) : ℝ) : EReal) +
                dualPerturbationFunctionOfConvexProgram FCvx (0 : Fin n → ℝ)) := by
                  simp [dualProgramOfConvexProgram]
        _ ≤ sSup (Set.range fun xStar : Fin n → ℝ =>
              ((((-x) ⬝ᵥ xStar : ℝ) : EReal) +
                dualPerturbationFunctionOfConvexProgram FCvx xStar)) :=
            le_sSup hMem
  refine ⟨-x, ?_⟩
  unfold IsKuhnTuckerVectorForDualProgram
  dsimp
  refine ⟨?_, ?_, hObjectiveEqDual⟩
  · -- Equality with the finite dual optimum excludes `⊤`.
    intro hTop
    exact hFiniteDual.1 (hObjectiveEqDual.symm.trans hTop)
  · -- Equality with the finite dual optimum excludes `⊥`.
    intro hBot
    exact hFiniteDual.2 (hObjectiveEqDual.symm.trans hBot)

/-- Helper for Corollary 6.30.5: strong primal consistency together with dual consistency yields
a dual optimal solution through a generalized Kuhn--Tucker witness for `F`. -/
lemma helperForCorollary_6_30_5_exists_dualOptimalSolution_of_strongPrimalConsistency
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hPStrong : IsStronglyConsistentConvexProgram ⟨F.1, F.2.1⟩)
    (hPStar : IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) :
    ∃ uStar : Fin m → ℝ, uStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  have hDualLePrimal :
      dualProgramOfConvexProgram FCvx ≤ convexProgramAssociatedWith F.1 0 := by
    -- Weak duality controls the dual optimum by the primal value at the origin.
    simpa [FCvx, dualProgramOfConvexProgram, dualPerturbationFunctionOfConvexProgram,
      concaveProgramAssociatedWith, convexProgramAssociatedWith] using
      helperForCorollary_6_30_2_weakDuality_at_zero (F := F)
  have hPrimalNeBot : convexProgramAssociatedWith F.1 0 ≠ (⊥ : EReal) := by
    -- Dual consistency excludes primal `-∞` by weak duality.
    intro hPrimalBot
    have hDualBot : dualProgramOfConvexProgram FCvx = (⊥ : EReal) := by
      have hDualLeBot : dualProgramOfConvexProgram FCvx ≤ (⊥ : EReal) := by
        simpa [hPrimalBot] using hDualLePrimal
      exact le_antisymm hDualLeBot bot_le
    exact hPStar hDualBot
  have hFinitePrimal : HasFinitePrimalOptimalValueOfConvexProgram FCvx :=
    ⟨hPStrong.1, hPrimalNeBot⟩
  have hProper : ProperConvexBifunction F.1 :=
    helperForTheorem_6_30_17_properConvexBifunction_of_finitePrimalValue
      (F := F) hFinitePrimal
  have hNoGraphBot : ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ, F.1 u x ≠ (⊥ : EReal) := by
    intro u x
    simpa [bifunctionGraphFunction] using hProper.2.1.1 (Fin.append u x)
  let G : BundledConvexBifunction m n :=
    ⟨F.1,
      helperForTheorem_6_30_17_isConvexBifunction_of_convexBifunction
        F.2.1 hNoGraphBot⟩
  have hFiniteGeneral : IsFiniteEReal (generalizedConvexProgramOptimalValue G) := by
    -- For `G.1 = F.1`, the Chapter 29 optimal value is the Chapter 30 primal value at `0`.
    simpa [G, HasFinitePrimalOptimalValueOfConvexProgram, generalizedConvexProgramOptimalValue,
      generalizedConvexProgramObjective, convexProgramAssociatedWith] using hFinitePrimal
  have hriPerturbation :
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (effectiveDomain (Set.univ : Set (Fin m → ℝ))
            (generalizedConvexProgramPerturbationFunction G)) := by
    -- For `G.1 = F.1`, this is exactly the relative-interior component of strong consistency.
    simpa [G, convexProgramAssociatedWith] using hPStrong.2
  have hdomPerturbation :
      effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (generalizedConvexProgramPerturbationFunction G) =
        bifunctionEffectiveDomain G.1 := by
    calc
      effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (generalizedConvexProgramPerturbationFunction G)
          = erealDom (generalizedConvexProgramPerturbationFunction G) := by
              ext u
              simp [effectiveDomain_eq, erealDom]
      _ = bifunctionEffectiveDomain G.1 :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker G).2.1
  have hStrongGeneral : generalizedConvexProgramStronglyConsistent G := by
    -- Translate the relative-interior statement to the Section 29 domain formulation.
    unfold generalizedConvexProgramStronglyConsistent
    rw [← hdomPerturbation]
    exact hriPerturbation
  have hKTGeneral :=
    generalizedConvexProgram_exists_kuhnTuckerVector_and_originDirectionalDerivative_eq_neg_sInf
      G hFiniteGeneral (Or.inl hStrongGeneral)
  rcases hKTGeneral.1 with ⟨v, hv⟩
  have hPrimalKT : IsKuhnTuckerVectorForConvexProgram FCvx (-v) := by
    -- Convert the Chapter 29 generalized Kuhn--Tucker witness into the Chapter 30 predicate.
    exact
      helperForTheorem_6_30_17_primalKuhnTucker_of_generalizedKuhnTucker
        (F := F) hFinitePrimal G rfl hv
  have hDualNeg : -(-v) ∈ dualOptimalSolutionSetOfConvexProgram FCvx := by
    -- The sign-correct forward implication from Theorem 6.30.19 gives dual optimality.
    exact
      helperForTheorem_6_30_19_neg_dualOptimalSolution_of_primalKuhnTucker
        (F := F) hPrimalKT
  refine ⟨v, ?_⟩
  simpa using hDualNeg

/-- Corollary 6.30.5 (Corollary 30.5.2): let `F` be a closed convex bifunction from `ℝ^m` to
`ℝ^n`, and let `(P)` be the convex program associated with `F`. If `(P)` is consistent and
`(P*)` is strongly consistent, then `(P)` has an optimal solution. Dually, if `(P)` is strongly
consistent and `(P*)` is consistent, then `(P*)` has an optimal solution. -/
theorem consistent_and_stronglyConsistent_primal_dual_programs_have_optimalSolutions {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    (IsConsistentConvexProgram ⟨F.1, F.2.1⟩ →
      IsStronglyConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ →
      ∃ x : Fin n → ℝ, x ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) ∧
    (IsStronglyConsistentConvexProgram ⟨F.1, F.2.1⟩ →
      IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ →
      ∃ uStar : Fin m → ℝ, uStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) := by
  constructor
  · intro hP hPStarStrong
    -- First produce a dual Kuhn--Tucker vector from the strong-dual-consistency route.
    rcases
        helperForCorollary_6_30_5_exists_dualKuhnTucker_of_primalConsistency_and_strongDualConsistency
          (F := F) hP hPStarStrong with
      ⟨x, hxKT⟩
    -- Then convert that Kuhn--Tucker witness into primal optimal attainment.
    refine ⟨x, ?_⟩
    exact
      helperForTheorem_6_30_19_primalOptimalSolution_of_dualKuhnTucker
        (F := F) hxKT
  · intro hPStrong hPStar
    -- The dual-attainment branch is packaged as a dedicated helper following Corollary 6.29.4.
    exact
      helperForCorollary_6_30_5_exists_dualOptimalSolution_of_strongPrimalConsistency
        (F := F) hPStrong hPStar

/-- The feasible set of the perturbed ordinary convex program with perturbation vector `u`. -/
def ordinaryConvexProgramFeasibleSet {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) (u : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i : Fin m, f i x ≤ (((u i : ℝ) : EReal))}

/-- The convex bifunction associated with an ordinary convex program: `F_u(x) = f₀(x)` on the
constraint set `fᵢ(x) ≤ uᵢ` and `+∞` outside it. -/
noncomputable def ordinaryConvexProgramBifunction {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x => f0 x + indicatorFunction (ordinaryConvexProgramFeasibleSet f u) x

/-- The weighted objective `x ↦ f₀(x) + ∑ᵢ uᵢ* fᵢ(x)` appearing in the adjoint formula for an
ordinary convex program. -/
noncomputable def ordinaryConvexProgramWeightedObjective {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal) (uStar : Fin m → ℝ) :
    (Fin n → ℝ) → EReal :=
  fun x => f0 x + ∑ i : Fin m, (((uStar i : ℝ) : EReal) * f i x)

/-- Helper for Theorem 6.30.20: coercion from `ℝ` to `EReal` commutes with finite sums of
coordinatewise products. -/
lemma helperForTheorem_6_30_20_coe_sum_mul_eq_sum_coe_mul
    {m : ℕ} (a b : Fin m → ℝ) :
    (∑ i : Fin m, (((a i : ℝ) : EReal) * (((b i : ℝ) : EReal)))) =
      (((∑ i : Fin m, a i * b i : ℝ) : EReal)) := by
  classical
  let termE : Fin m → EReal := fun i => (((a i : ℝ) : EReal) * (((b i : ℝ) : EReal)))
  let termR : Fin m → ℝ := fun i => a i * b i
  change (Finset.univ.sum termE) = (((Finset.univ.sum termR : ℝ) : EReal))
  have hEqOnSet :
      ∀ s : Finset (Fin m), s.sum termE = (((s.sum termR : ℝ) : EReal)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp [termE, termR]
    · intro i s his hs
      calc
        (insert i s).sum termE = termE i + s.sum termE := by
          simp [Finset.sum_insert, his]
        _ = (((termR i : ℝ) : EReal)) + (((s.sum termR : ℝ) : EReal)) := by
          rw [hs]
          simp [termE, termR, EReal.coe_mul]
        _ = (((termR i + s.sum termR : ℝ) : EReal)) := by
          simp [EReal.coe_add]
        _ = (((insert i s).sum termR : ℝ) : EReal) := by
          simp [Finset.sum_insert, his]
  simpa using hEqOnSet Finset.univ

/-- Helper for Theorem 6.30.20: for a feasible pair `(u, x)` and nonnegative multipliers
`u*`, the weighted constraint sum is bounded above by `⟪u, u*⟫`. -/
lemma helperForTheorem_6_30_20_dotProduct_ge_weightedSum_of_feasible
    {m n : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (uStar : Fin m → ℝ) (hnonneg : ∀ i : Fin m, 0 ≤ uStar i)
    {u : Fin m → ℝ} {x : Fin n → ℝ}
    (hx : x ∈ ordinaryConvexProgramFeasibleSet f u) :
    (∑ i : Fin m, (((uStar i : ℝ) : EReal) * f i x)) ≤ (((u ⬝ᵥ uStar : ℝ) : EReal)) := by
  -- Compare each summand using feasibility `fᵢ(x) ≤ uᵢ` and multiplier nonnegativity.
  have hsumLe :
      (∑ i : Fin m, (((uStar i : ℝ) : EReal) * f i x)) ≤
        ∑ i : Fin m, (((uStar i : ℝ) : EReal) * (((u i : ℝ) : EReal))) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hMulNonnegE : (0 : EReal) ≤ (((uStar i : ℝ) : EReal)) := by
      exact_mod_cast hnonneg i
    exact mul_le_mul_of_nonneg_left (hx i) hMulNonnegE
  -- Rewrite the right-hand sum as the `EReal` coercion of the real dot product.
  have hdot :
      (∑ i : Fin m, (((uStar i : ℝ) : EReal) * (((u i : ℝ) : EReal)))) =
        (((u ⬝ᵥ uStar : ℝ) : EReal)) := by
    calc
      (∑ i : Fin m, (((uStar i : ℝ) : EReal) * (((u i : ℝ) : EReal))))
          = (((∑ i : Fin m, uStar i * u i : ℝ) : EReal)) := by
              simpa using
                helperForTheorem_6_30_20_coe_sum_mul_eq_sum_coe_mul (a := uStar) (b := u)
      _ = (((u ⬝ᵥ uStar : ℝ) : EReal)) := by
            simp [dotProduct, mul_comm]
  calc
    (∑ i : Fin m, (((uStar i : ℝ) : EReal) * f i x))
        ≤ ∑ i : Fin m, (((uStar i : ℝ) : EReal) * (((u i : ℝ) : EReal))) := hsumLe
    _ = (((u ⬝ᵥ uStar : ℝ) : EReal)) := hdot

/-- Helper for Theorem 6.30.20: if each `fᵢ(x)` is finite above (`≠ ⊤`), one can choose a
feasible perturbation vector `u` with coordinates `uᵢ = (fᵢ(x)).toReal`, and this choice realizes
`⟪u, u*⟫ = ∑ᵢ uᵢ* fᵢ(x)` in `EReal`. -/
lemma helperForTheorem_6_30_20_exists_feasible_u_of_finite_constraints
    {m n : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i : Fin m, ProperConvexERealFunction (F := (Fin n → ℝ)) (f i))
    (uStar : Fin m → ℝ) (x : Fin n → ℝ)
    (hfinite : ∀ i : Fin m, f i x ≠ ⊤) :
    ∃ uX : Fin m → ℝ,
      x ∈ ordinaryConvexProgramFeasibleSet f uX ∧
      (((uX ⬝ᵥ uStar : ℝ) : EReal) =
        ∑ i : Fin m, (((uStar i : ℝ) : EReal) * f i x)) := by
  classical
  let uX : Fin m → ℝ := fun i : Fin m => (f i x).toReal
  refine ⟨uX, ?_, ?_⟩
  · -- The chosen perturbation coordinates dominate `fᵢ(x)` by `toReal`-coercion.
    intro i
    have hfiTop : f i x ≠ ⊤ := hfinite i
    simpa [uX] using (EReal.le_coe_toReal (x := f i x) hfiTop)
  · -- Replace each `fᵢ(x)` by its real coercion and evaluate the dot product.
    have hfiCoe : ∀ i : Fin m, (((uX i : ℝ) : EReal)) = f i x := by
      intro i
      have hfiTop : f i x ≠ ⊤ := hfinite i
      have hfiBot : f i x ≠ ⊥ := (hf i).1.1 x
      have hEq : ((f i x).toReal : EReal) = f i x := EReal.coe_toReal hfiTop hfiBot
      simpa [uX] using hEq
    calc
      (((uX ⬝ᵥ uStar : ℝ) : EReal))
          = ∑ i : Fin m, (((uStar i : ℝ) : EReal) * (((uX i : ℝ) : EReal))) := by
              calc
                (((uX ⬝ᵥ uStar : ℝ) : EReal))
                    = (((∑ i : Fin m, uStar i * uX i : ℝ) : EReal)) := by
                        simp [dotProduct, mul_comm]
                _ = (∑ i : Fin m, (((uStar i : ℝ) : EReal) * (((uX i : ℝ) : EReal)))) := by
                      symm
                      simpa using
                        helperForTheorem_6_30_20_coe_sum_mul_eq_sum_coe_mul
                          (a := uStar) (b := uX)
      _ = ∑ i : Fin m, (((uStar i : ℝ) : EReal) * f i x) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hfiCoe i]

/-- Helper for Theorem 6.30.20: if `f₀(x)` is finite above (`≠ ⊤`), the standing domain
assumptions imply each `fᵢ(x)` is finite above, hence there exists a feasible perturbation vector
realizing `⟪u, u*⟫ = ∑ᵢ uᵢ* fᵢ(x)`. -/
lemma helperForTheorem_6_30_20_exists_feasible_u_achieving_weightedSum
    {m n : ℕ} (C : Set (Fin n → ℝ))
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexERealFunction (F := (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexERealFunction (F := (Fin n → ℝ)) (f i))
    (hdom_f0 : effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0 = C)
    (hdom_f : ∀ i : Fin m, C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
    (uStar : Fin m → ℝ) (x : Fin n → ℝ) (hx0 : f0 x ≠ ⊤) :
    ∃ uX : Fin m → ℝ,
      x ∈ ordinaryConvexProgramFeasibleSet f uX ∧
      (((uX ⬝ᵥ uStar : ℝ) : EReal) =
        ∑ i : Fin m, (((uStar i : ℝ) : EReal) * f i x)) := by
  -- `f₀(x) ≠ ⊤` places `x` in `C` via the effective-domain identity.
  have hxDomF0 : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0 := by
    rw [effectiveDomain_eq]
    refine ⟨?_, ?_⟩
    · simp
    · exact (lt_top_iff_ne_top).2 hx0
  have hxC : x ∈ C := by
    simpa [hdom_f0] using hxDomF0
  -- Then each `fᵢ(x)` is finite above by `C ⊆ dom fᵢ`.
  have hfinite : ∀ i : Fin m, f i x ≠ ⊤ := by
    intro i
    have hxDomFi : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := hdom_f i hxC
    have hxDomFi' : x ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f i x < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hxDomFi
    exact (lt_top_iff_ne_top).1 hxDomFi'.2
  -- Invoke the finite-constraint helper with these finiteness facts.
  exact
    helperForTheorem_6_30_20_exists_feasible_u_of_finite_constraints
      (f := f) (hf := hf) (uStar := uStar) (x := x) hfinite

/-- Helper for Theorem 6.30.20: the infimum of
`x ↦ ordinaryConvexProgramWeightedObjective f₀ f u*(x) - ⟪x, x*⟫` equals the negative Fenchel
conjugate of the weighted objective at `x*`. -/
lemma helperForTheorem_6_30_20_sInf_range_weightedObjective_sub_dot_eq_neg_fenchelConjugate
    {m n : ℕ} (f0 : (Fin n → ℝ) → EReal)
    (f : Fin m → (Fin n → ℝ) → EReal)
    (uStar : Fin m → ℝ) (xStar : Fin n → ℝ) :
    sInf (Set.range fun x : Fin n → ℝ =>
      ordinaryConvexProgramWeightedObjective f0 f uStar x -
        (((x ⬝ᵥ xStar : ℝ) : EReal))) =
      -fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) xStar := by
  let g : (Fin n → ℝ) → EReal :=
    fun x : Fin n → ℝ =>
      ordinaryConvexProgramWeightedObjective f0 f uStar x - (((x ⬝ᵥ xStar : ℝ) : EReal))
  change sInf (Set.range g) =
    -fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) xStar
  -- Convert the infimum to a negative supremum of pointwise negations.
  have hInfAsNegSup : sInf (Set.range g) = -(iSup fun x => -g x) := by
    simpa using
      (helperForTheorem_6_30_9_neg_iSup_pair_eq_sInf_range_adjointIntegrand (g := g)).symm
  calc
    sInf (Set.range g) = -(iSup fun x => -g x) := hInfAsNegSup
    _ = -fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) xStar := by
          -- Identify each negated integrand with the Fenchel-conjugate integrand.
          congr 1
          rw [fenchelConjugate_eq_iSup]
          refine iSup_congr ?_
          intro x
          dsimp [g]
          have hNegYNeTop : -(((x ⬝ᵥ xStar : ℝ) : EReal)) ≠ ⊤ := by
            simp
          have hNegYNeBot : -(((x ⬝ᵥ xStar : ℝ) : EReal)) ≠ ⊥ := by
            simp
          have hNegAdd :
              -(ordinaryConvexProgramWeightedObjective f0 f uStar x +
                  -(((x ⬝ᵥ xStar : ℝ) : EReal))) =
                -(ordinaryConvexProgramWeightedObjective f0 f uStar x) -
                  (-(((x ⬝ᵥ xStar : ℝ) : EReal))) := by
            exact
              EReal.neg_add
                (x := ordinaryConvexProgramWeightedObjective f0 f uStar x)
                (y := -(((x ⬝ᵥ xStar : ℝ) : EReal)))
                (Or.inr hNegYNeTop)
                (Or.inr hNegYNeBot)
          calc
            -(ordinaryConvexProgramWeightedObjective f0 f uStar x -
                (((x ⬝ᵥ xStar : ℝ) : EReal))
                ) = -(ordinaryConvexProgramWeightedObjective f0 f uStar x +
                    -(((x ⬝ᵥ xStar : ℝ) : EReal))) := by
                      simp [sub_eq_add_neg]
            _ = -(ordinaryConvexProgramWeightedObjective f0 f uStar x) -
                  (-(((x ⬝ᵥ xStar : ℝ) : EReal))) := hNegAdd
            _ = (((x ⬝ᵥ xStar : ℝ) : EReal) -
                  ordinaryConvexProgramWeightedObjective f0 f uStar x) := by
                    simp [sub_eq_add_neg, add_comm]

/-- Helper for Theorem 6.30.20: in the nonnegative-multiplier branch, every adjoint-integrand
value dominates the `x`-only integrand, so
`sInf_x (weightedObjective - ⟪x, x*⟫) ≤ adjointOfConvexBifunction F x* u*`. -/
lemma helperForTheorem_6_30_20_sInf_range_weightedObjective_sub_dot_le_adjoint_of_nonnegative
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (hF : F.1 = ordinaryConvexProgramBifunction f0 f)
    (hf0 : ProperConvexERealFunction (F := (Fin n → ℝ)) f0)
    (uStar : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hnonneg : ∀ i : Fin m, 0 ≤ uStar i) :
    sInf (Set.range (fun x : Fin n → ℝ =>
      ordinaryConvexProgramWeightedObjective f0 f uStar x - (((x ⬝ᵥ xStar : ℝ) : EReal))) ) ≤
      adjointOfConvexBifunction F xStar uStar := by
  -- Unfold the adjoint and lower-bound each element of its range by the `x`-only infimum.
  rw [adjointOfConvexBifunction]
  refine le_sInf ?_
  rintro y ⟨⟨u, x⟩, rfl⟩
  by_cases hfeas : x ∈ ordinaryConvexProgramFeasibleSet f u
  · -- In the feasible case, `δ = 0`, and nonnegative multipliers bound the weighted sum by
    -- `⟪u, u*⟫`.
    have hsumLe :
        (∑ i : Fin m, (((uStar i : ℝ) : EReal) * f i x)) ≤ (((u ⬝ᵥ uStar : ℝ) : EReal)) :=
      helperForTheorem_6_30_20_dotProduct_ge_weightedSum_of_feasible
        (f := f) (uStar := uStar) (hnonneg := hnonneg) (x := x) (u := u) hfeas
    have hobjLe :
        ordinaryConvexProgramWeightedObjective f0 f uStar x ≤
          f0 x + (((u ⬝ᵥ uStar : ℝ) : EReal)) := by
      unfold ordinaryConvexProgramWeightedObjective
      calc
        f0 x + ∑ i : Fin m, (((uStar i : ℝ) : EReal) * f i x)
            = (∑ i : Fin m, (((uStar i : ℝ) : EReal) * f i x)) + f0 x := by
                simp [add_assoc, add_left_comm, add_comm]
        _ ≤ (((u ⬝ᵥ uStar : ℝ) : EReal)) + f0 x := by
              exact add_le_add_left hsumLe (f0 x)
        _ = f0 x + (((u ⬝ᵥ uStar : ℝ) : EReal)) := by
              simp [add_assoc, add_left_comm, add_comm]
    have hobjLeSub :
        ordinaryConvexProgramWeightedObjective f0 f uStar x - (((x ⬝ᵥ xStar : ℝ) : EReal)) ≤
          (f0 x + (((u ⬝ᵥ uStar : ℝ) : EReal))) - (((x ⬝ᵥ xStar : ℝ) : EReal)) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        add_le_add_right hobjLe (-(((x ⬝ᵥ xStar : ℝ) : EReal)))
    have hMem :
        ordinaryConvexProgramWeightedObjective f0 f uStar x - (((x ⬝ᵥ xStar : ℝ) : EReal)) ∈
          Set.range (fun x : Fin n → ℝ =>
            ordinaryConvexProgramWeightedObjective f0 f uStar x -
              (((x ⬝ᵥ xStar : ℝ) : EReal))) := by
      exact ⟨x, rfl⟩
    have hInfLe :
        sInf (Set.range (fun x : Fin n → ℝ =>
          ordinaryConvexProgramWeightedObjective f0 f uStar x -
            (((x ⬝ᵥ xStar : ℝ) : EReal))) ) ≤
          ordinaryConvexProgramWeightedObjective f0 f uStar x - (((x ⬝ᵥ xStar : ℝ) : EReal)) :=
      sInf_le hMem
    have hEval :
        (f0 x + (((u ⬝ᵥ uStar : ℝ) : EReal))) - (((x ⬝ᵥ xStar : ℝ) : EReal)) =
          F.1 u x - (((x ⬝ᵥ xStar : ℝ) : EReal)) + (((u ⬝ᵥ uStar : ℝ) : EReal)) := by
      rw [hF]
      simp [ordinaryConvexProgramBifunction, indicatorFunction, hfeas, sub_eq_add_neg, add_assoc,
        add_left_comm, add_comm]
    have hLeToEval :
        sInf (Set.range (fun x : Fin n → ℝ =>
          ordinaryConvexProgramWeightedObjective f0 f uStar x -
            (((x ⬝ᵥ xStar : ℝ) : EReal))) ) ≤
          (f0 x + (((u ⬝ᵥ uStar : ℝ) : EReal))) - (((x ⬝ᵥ xStar : ℝ) : EReal)) :=
      (hInfLe.trans hobjLeSub)
    exact hLeToEval.trans_eq hEval
  · -- In the infeasible case, `δ = ⊤`, so the adjoint integrand is `⊤` and the bound is
    -- immediate.
    have hTop :
        F.1 u x - (((x ⬝ᵥ xStar : ℝ) : EReal)) + (((u ⬝ᵥ uStar : ℝ) : EReal)) = (⊤ : EReal) := by
      rw [hF]
      simp [ordinaryConvexProgramBifunction, indicatorFunction, hfeas, hf0.1.1 x, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]
    have hTop' :
        (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          F.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) (u, x) =
          (⊤ : EReal) := by
      simpa using hTop
    exact hTop' ▸ le_top

/-- Helper for Theorem 6.30.20: in the nonnegative-multiplier branch, for every fixed `x`,
one can produce an adjoint witness matching the value
`weightedObjective(x) - ⟪x, x*⟫`, hence
`adjointOfConvexBifunction F x* u* ≤ sInf_x (weightedObjective - ⟪x, x*⟫)`. -/
lemma helperForTheorem_6_30_20_adjoint_le_sInf_range_weightedObjective_sub_dot_of_nonnegative
    {m n : ℕ} (C : Set (Fin n → ℝ))
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (hF : F.1 = ordinaryConvexProgramBifunction f0 f)
    (hf0 : ProperConvexERealFunction (F := (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexERealFunction (F := (Fin n → ℝ)) (f i))
    (hdom_f0 : effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0 = C)
    (hdom_f : ∀ i : Fin m, C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
    (uStar : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hnonneg : ∀ i : Fin m, 0 ≤ uStar i) :
    adjointOfConvexBifunction F xStar uStar ≤
      sInf (Set.range (fun x : Fin n → ℝ =>
        ordinaryConvexProgramWeightedObjective f0 f uStar x - (((x ⬝ᵥ xStar : ℝ) : EReal))) ) := by
  -- Unfold the adjoint and prove the upper bound pointwise on each `x`.
  rw [adjointOfConvexBifunction]
  refine le_sInf ?_
  rintro y ⟨x, rfl⟩
  by_cases hx0 : f0 x = ⊤
  · -- If `f₀(x)=⊤`, then the `x`-integrand is `⊤`.
    have hsumNeBot :
        (∑ i : Fin m, (((uStar i : ℝ) : EReal) * f i x)) ≠ (⊥ : EReal) := by
      refine sum_ne_bot_of_ne_bot (s := Finset.univ)
          (f := fun i : Fin m => (((uStar i : ℝ) : EReal) * f i x)) ?_
      intro i hi
      rw [EReal.mul_ne_bot]
      refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inr ((hf i).1.1 x),
        Or.inl (EReal.coe_ne_top _), ?_⟩
      left
      exact_mod_cast hnonneg i
    have hTopObj : ordinaryConvexProgramWeightedObjective f0 f uStar x = (⊤ : EReal) := by
      unfold ordinaryConvexProgramWeightedObjective
      rw [hx0]
      simpa using (EReal.top_add_of_ne_bot hsumNeBot)
    have hTopG :
        ordinaryConvexProgramWeightedObjective f0 f uStar x - (((x ⬝ᵥ xStar : ℝ) : EReal)) =
          (⊤ : EReal) := by
      rw [hTopObj]
      simp
    have hTopG' :
        (fun x : Fin n → ℝ =>
          ordinaryConvexProgramWeightedObjective f0 f uStar x - (((x ⬝ᵥ xStar : ℝ) : EReal))) x =
          (⊤ : EReal) := by
      simpa using hTopG
    exact hTopG' ▸ le_top
  · -- If `f₀(x)` is finite above, build a feasible perturbation `uX` that realizes the weighted
    -- sum exactly.
    rcases helperForTheorem_6_30_20_exists_feasible_u_achieving_weightedSum
        (C := C) (f0 := f0) (f := f) (hf0 := hf0) (hf := hf)
        (hdom_f0 := hdom_f0) (hdom_f := hdom_f)
        (uStar := uStar) (x := x) hx0 with
      ⟨uX, huXFeas, huXDot⟩
    have hAdjLeWitness :
        sInf
            (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
              F.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) ≤
          F.1 uX x - (((x ⬝ᵥ xStar : ℝ) : EReal)) + (((uX ⬝ᵥ uStar : ℝ) : EReal)) := by
      exact sInf_le ⟨(uX, x), rfl⟩
    have hEval :
        F.1 uX x - (((x ⬝ᵥ xStar : ℝ) : EReal)) + (((uX ⬝ᵥ uStar : ℝ) : EReal)) =
          ordinaryConvexProgramWeightedObjective f0 f uStar x - (((x ⬝ᵥ xStar : ℝ) : EReal)) := by
      rw [hF]
      rw [ordinaryConvexProgramBifunction]
      have hIndicatorZero :
          indicatorFunction (ordinaryConvexProgramFeasibleSet f uX) x = (0 : EReal) := by
        simp [indicatorFunction, huXFeas]
      rw [hIndicatorZero]
      rw [huXDot]
      simp [ordinaryConvexProgramWeightedObjective, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm]
    have hGoal :
        sInf
            (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
              F.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) ≤
          ordinaryConvexProgramWeightedObjective f0 f uStar x - (((x ⬝ᵥ xStar : ℝ) : EReal)) := by
      exact hAdjLeWitness.trans (le_of_eq hEval)
    exact hGoal

/-- Helper for Theorem 6.30.20: along the feasible ray `u(t) = u₀ + t e_{i₀}` at fixed `x₀`,
the adjoint integrand is affine in `t` with slope `u* i₀`. -/
lemma helperForTheorem_6_30_20_negativeMultiplierRayWitnessValue
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (u0 : Fin m → ℝ) (x0 : Fin n → ℝ)
    (hu0Feas : x0 ∈ ordinaryConvexProgramFeasibleSet f u0)
    (i0 : Fin m) (t : ℝ) (ht : 0 ≤ t) :
    let u : Fin m → ℝ := u0 + (Pi.single i0 t : Fin m → ℝ)
    ordinaryConvexProgramBifunction f0 f u x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
        (((u ⬝ᵥ uStar : ℝ) : EReal)) =
      (f0 x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) + (((u0 ⬝ᵥ uStar : ℝ) : EReal))) +
        (((t * uStar i0 : ℝ) : EReal)) := by
  -- Feasibility is preserved when increasing one perturbation coordinate along a nonnegative ray.
  dsimp
  have hfeas : x0 ∈ ordinaryConvexProgramFeasibleSet f (u0 + (Pi.single i0 t : Fin m → ℝ)) := by
    intro j
    by_cases hj : j = i0
    · have hincReal : u0 j ≤ u0 j + t := by
        linarith
      have hincE : (((u0 j : ℝ) : EReal)) ≤ (((u0 j + t : ℝ) : EReal)) := by
        exact_mod_cast hincReal
      have hbase : f j x0 ≤ (((u0 j : ℝ) : EReal)) := hu0Feas j
      have hgoal : f j x0 ≤ (((u0 j + t : ℝ) : EReal)) := le_trans hbase hincE
      simpa [hj] using hgoal
    · simpa [Pi.single_eq_of_ne hj] using (hu0Feas j)
  have hdot :
      ((u0 + (Pi.single i0 t : Fin m → ℝ)) ⬝ᵥ uStar : ℝ) =
        (u0 ⬝ᵥ uStar : ℝ) + t * uStar i0 := by
    rw [add_dotProduct, single_dotProduct]
  -- Evaluate the bifunction at a feasible pair and simplify the resulting affine expression.
  rw [ordinaryConvexProgramBifunction]
  have hIndicatorZero :
      indicatorFunction (ordinaryConvexProgramFeasibleSet f (u0 + (Pi.single i0 t : Fin m → ℝ))) x0 =
        (0 : EReal) := by
    simp [indicatorFunction, hfeas]
  rw [hIndicatorZero]
  rw [hdot]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 6.30.20: if one multiplier coordinate is negative, the adjoint value is
`-∞` (by sending that perturbation coordinate to `+∞` along a feasible ray). -/
lemma helperForTheorem_6_30_20_adjoint_eq_bot_of_exists_negativeMultiplier
    {m n : ℕ} (C : Set (Fin n → ℝ))
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (hF : F.1 = ordinaryConvexProgramBifunction f0 f)
    (hf0 : ProperConvexERealFunction (F := (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexERealFunction (F := (Fin n → ℝ)) (f i))
    (hdom_f0 : effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0 = C)
    (hdom_f : ∀ i : Fin m, C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
    (uStar : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hneg : ∃ i0 : Fin m, uStar i0 < 0) :
    adjointOfConvexBifunction F xStar uStar = (⊥ : EReal) := by
  -- Show the adjoint is below every real number by evaluating along a feasible ray.
  rw [adjointOfConvexBifunction, EReal.eq_bot_iff_forall_lt]
  intro y
  rcases hneg with ⟨i0, hi0neg⟩
  rcases hf0.1.2 with ⟨x0, hx0top⟩
  rcases helperForTheorem_6_30_20_exists_feasible_u_achieving_weightedSum
      (C := C) (f0 := f0) (f := f) (hf0 := hf0) (hf := hf)
      (hdom_f0 := hdom_f0) (hdom_f := hdom_f)
      (uStar := uStar) (x := x0) hx0top with
    ⟨u0, hu0Feas, _hu0Dot⟩
  let base : ℝ := (f0 x0).toReal - (x0 ⬝ᵥ xStar : ℝ) + (u0 ⬝ᵥ uStar : ℝ)
  let t : ℝ := |((base - y) / (-uStar i0))| + 1
  have hden : 0 < -uStar i0 := by
    linarith
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hratio :
      ((base - y) / (-uStar i0)) < t := by
    dsimp [t]
    refine lt_of_le_of_lt (le_abs_self ((base - y) / (-uStar i0))) ?_
    linarith [abs_nonneg ((base - y) / (-uStar i0))]
  have hmul :
      (base - y) < t * (-uStar i0) := by
    exact (div_lt_iff₀ hden).mp hratio
  have hreal : base + t * uStar i0 < y := by
    linarith
  have hcoex0 : (((f0 x0).toReal : ℝ) : EReal) = f0 x0 := by
    exact EReal.coe_toReal hx0top (hf0.1.1 x0)
  have hwitnessEval :
      F.1 (u0 + (Pi.single i0 t : Fin m → ℝ)) x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
          ((((u0 + (Pi.single i0 t : Fin m → ℝ)) ⬝ᵥ uStar : ℝ) : EReal)) =
        (f0 x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) + (((u0 ⬝ᵥ uStar : ℝ) : EReal))) +
          (((t * uStar i0 : ℝ) : EReal)) := by
    rw [hF]
    simpa using
      helperForTheorem_6_30_20_negativeMultiplierRayWitnessValue
        (f0 := f0) (f := f) (xStar := xStar) (uStar := uStar)
        (u0 := u0) (x0 := x0) (hu0Feas := hu0Feas) (i0 := i0) (t := t) ht
  have hwitnessLe :
      sInf
          (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
            F.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) ≤
        (f0 x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) + (((u0 ⬝ᵥ uStar : ℝ) : EReal))) +
          (((t * uStar i0 : ℝ) : EReal)) := by
    have hLePair :
        sInf
            (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
              F.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) ≤
          F.1 (u0 + (Pi.single i0 t : Fin m → ℝ)) x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
            ((((u0 + (Pi.single i0 t : Fin m → ℝ)) ⬝ᵥ uStar : ℝ) : EReal)) := by
      exact sInf_le ⟨(u0 + (Pi.single i0 t : Fin m → ℝ), x0), rfl⟩
    exact hLePair.trans (le_of_eq hwitnessEval)
  have htargetEq :
      (f0 x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) + (((u0 ⬝ᵥ uStar : ℝ) : EReal))) +
          (((t * uStar i0 : ℝ) : EReal)) =
        (((base + t * uStar i0 : ℝ) : EReal)) := by
    dsimp [base]
    rw [← hcoex0]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hltTarget :
      (((base + t * uStar i0 : ℝ) : EReal)) < ((y : ℝ) : EReal) := by
    exact_mod_cast hreal
  have hltWitness :
      (f0 x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) + (((u0 ⬝ᵥ uStar : ℝ) : EReal))) +
          (((t * uStar i0 : ℝ) : EReal)) < ((y : ℝ) : EReal) := by
    rw [htargetEq]
    exact hltTarget
  exact lt_of_le_of_lt hwitnessLe hltWitness

-- Proof sketch: unfold the adjoint as the infimum of
-- `f₀(x) + δ({x | fᵢ(x) ≤ uᵢ}) - ⟪x, x*⟫ + ⟪u, u*⟫`. If `u* ≥ 0`, minimizing first in the
-- perturbation variable yields the Lagrangian term `f₀ + ∑ᵢ uᵢ* fᵢ`, so the remaining infimum is
-- the negative Fenchel conjugate of that weighted objective. If some multiplier is negative, the
-- infimum over the corresponding perturbation coordinate is `-∞`.
/-- Theorem 6.30.20: for the ordinary convex program
`min_x f₀(x)` subject to `fᵢ(x) ≤ 0`, where `f₀, …, f_m` are proper convex and
`dom f₀ = C`, `C ⊆ dom fᵢ`, `ri C ⊆ ri (dom fᵢ)`, let `F` be the associated convex bifunction
`F_u(x) = f₀(x) + δ(x | fᵢ(x) ≤ uᵢ)`. Then the adjoint satisfies
`F*(x*, u*) = -(f₀ + ∑ᵢ uᵢ* fᵢ)^*(x*)` for `u* ≥ 0`, and `F*(x*, u*) = -∞` otherwise. -/
theorem adjointOfOrdinaryConvexProgramBifunction_eq_neg_fenchelConjugate_weightedObjective
    {m n : ℕ} (C : Set (Fin n → ℝ))
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (hF : F.1 = ordinaryConvexProgramBifunction f0 f)
    (hf0 : ProperConvexERealFunction (F := (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexERealFunction (F := (Fin n → ℝ)) (f i))
    (hdom_f0 : effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0 = C)
    (hdom_f : ∀ i : Fin m, C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
    (hri_f : ∀ i : Fin m,
      euclideanRelativeInterior_fin n C ⊆
        euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (uStar : Fin m → ℝ) (xStar : Fin n → ℝ) :
    adjointOfConvexBifunction F xStar uStar =
      if ∀ i : Fin m, 0 ≤ uStar i then
        -fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) xStar
      else
        (⊥ : EReal) := by
  by_cases hnonneg : ∀ i : Fin m, 0 ≤ uStar i
  · -- Nonnegative multipliers: reduce to a one-variable infimum over `x`.
    rw [if_pos hnonneg]
    let g : (Fin n → ℝ) → EReal := fun x : Fin n → ℝ =>
      ordinaryConvexProgramWeightedObjective f0 f uStar x - (((x ⬝ᵥ xStar : ℝ) : EReal))
    -- Prove the collapse `adjoint = sInf (range g)` by two monotone comparisons.
    have hLe :
        adjointOfConvexBifunction F xStar uStar ≤ sInf (Set.range g) := by
      simpa [g] using
        helperForTheorem_6_30_20_adjoint_le_sInf_range_weightedObjective_sub_dot_of_nonnegative
          (C := C) (f0 := f0) (f := f) (F := F) (hF := hF)
          (hf0 := hf0) (hf := hf) (hdom_f0 := hdom_f0) (hdom_f := hdom_f)
          (uStar := uStar) (xStar := xStar) hnonneg
    have hGe :
        sInf (Set.range g) ≤ adjointOfConvexBifunction F xStar uStar := by
      simpa [g] using
        helperForTheorem_6_30_20_sInf_range_weightedObjective_sub_dot_le_adjoint_of_nonnegative
          (f0 := f0) (f := f) (F := F) (hF := hF) (hf0 := hf0)
          (uStar := uStar) (xStar := xStar) hnonneg
    have hCollapse : adjointOfConvexBifunction F xStar uStar = sInf (Set.range g) := by
      exact le_antisymm hLe hGe
    calc
      adjointOfConvexBifunction F xStar uStar = sInf (Set.range g) := hCollapse
      _ = -fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) xStar := by
          simpa [g] using
            helperForTheorem_6_30_20_sInf_range_weightedObjective_sub_dot_eq_neg_fenchelConjugate
              (f0 := f0) (f := f) (uStar := uStar) (xStar := xStar)
  · -- Route correction: isolate the negative-multiplier branch as a separate infimum-ray argument.
    rw [if_neg hnonneg]
    have hnegCoord : ∃ i : Fin m, uStar i < 0 := by
      push_neg at hnonneg
      exact hnonneg
    exact
      helperForTheorem_6_30_20_adjoint_eq_bot_of_exists_negativeMultiplier
        (C := C) (f0 := f0) (f := f) (F := F) (hF := hF) (hf0 := hf0)
        (hf := hf) (hdom_f0 := hdom_f0) (hdom_f := hdom_f)
        (uStar := uStar) (xStar := xStar) hnegCoord

end Section30
end Chap06
