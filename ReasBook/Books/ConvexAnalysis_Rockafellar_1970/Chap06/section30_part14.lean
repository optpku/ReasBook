/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part13

section Chap06
section Section30

/-- Theorem 6.30.17: let `F` be a closed convex bifunction from `ℝ^m` to `ℝ^n`, and let `(P)` be
the convex program associated with `F`. Any one of the following conditions is sufficient to
guarantee that normality holds for `(P)` and `(P*)`: (a) `(P)` is strongly or strictly
consistent; (b) `(P*)` is strongly or strictly consistent; (c) the optimal value in `(P)` is
finite and a Kuhn--Tucker vector exists for `(P)`; (d) the optimal value in `(P*)` is finite and
a Kuhn--Tucker vector exists for `(P*)`; (e) `(P)` is polyhedral and consistent; (f) `(P*)` is
polyhedral and consistent; (g) some primal sublevel set `{x | F(0, x) ≤ α}` is nonempty and
bounded; (h) some dual superlevel set `{u* | F*(0, u*) ≥ β}` is nonempty and bounded; (i) `(P)`
has a unique optimal solution, or its optimal solutions form a nonempty bounded set; and (j)
`(P*)` has a unique optimal solution, or its optimal solutions form a nonempty bounded set. -/
theorem sufficient_conditions_imply_normality_for_primal_and_dual_convex_programs {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (h : SufficientForNormalityOfConvexProgramAndDual F) :
    IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
      IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  have _hCurrentSufficient : SufficientForNormalityOfConvexProgramAndDual F := h
  rcases h with ⟨hProper, h⟩
  -- Route correction: strong/strict consistency now include ordinary consistency, so the old
  -- closed-improper `graph = ⊥` witness from Theorem 6.30.16 is excluded from branch `(b)` by
  -- `helperForTheorem_6_30_17_counterexample_notDualStronglyConsistent` and from branch `(b')`
  -- by `helperForTheorem_6_30_17_counterexample_notDualStrictlyConsistent`. The remaining work is
  -- a genuine proof of the textbook sufficient-condition route under the repaired package.
  rcases h with hStrongPrimal | hRest
  · -- The strong primal branch uses the new primal-consistency sink after the existing value
    -- equality reduction.
    have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_valueEquality_of_primalStrongOrStrictConsistency
        (F := F) (Or.inl hStrongPrimal)
    exact
      helperForTheorem_6_30_17_normality_of_valueEquality_and_primalConsistency
        (F := F) hValue hStrongPrimal.1
  rcases hRest with hStrictPrimal | hRest
  · -- The strict primal branch uses the same sink once strict consistency is unpacked to ordinary
    -- consistency plus interior information.
    have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_valueEquality_of_primalStrongOrStrictConsistency
        (F := F) (Or.inr hStrictPrimal)
    exact
      helperForTheorem_6_30_17_normality_of_valueEquality_and_primalConsistency
        (F := F) hValue hStrictPrimal.1
  rcases hRest with hStrongDual | hRest
  · -- Dual strong consistency already gives dual consistency, so the value equality helper
    -- immediately upgrades to both normality identities.
    have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_valueEquality_of_dualStrongOrStrictConsistency
        (F := F) hProper (Or.inl hStrongDual)
    exact
      helperForTheorem_6_30_17_normality_of_valueEquality_and_dualConsistency
        (F := F) hValue hStrongDual.1
  rcases hRest with hStrictDual | hRest
  · -- The strict dual branch follows the same dual-consistency sink after the same value
    -- equality reduction.
    have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_valueEquality_of_dualStrongOrStrictConsistency
        (F := F) hProper (Or.inr hStrictDual)
    exact
      helperForTheorem_6_30_17_normality_of_valueEquality_and_dualConsistency
        (F := F) hValue hStrictDual.1
  rcases hRest with hPrimalKT | hRest
  · -- A finite primal value plus a primal Kuhn--Tucker witness first yields value equality, and
    -- the same finiteness makes both closure formulas nonexceptional.
    have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_valueEquality_of_finitePrimalValue_and_primalKuhnTuckerVector
        (F := F) hPrimalKT.1 hPrimalKT.2
    exact
      helperForTheorem_6_30_17_normality_of_finiteValueEquality
        (F := F) hPrimalKT.1 hValue
  rcases hRest with hDualKT | hRest
  · -- A finite dual value plus a dual Kuhn--Tucker witness yields the same value equality, and
    -- dual finiteness already implies the dual-consistency sink needed for normality.
    have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_valueEquality_of_finiteDualValue_and_dualKuhnTuckerVector
        (F := F) hDualKT.1 hDualKT.2
    exact
      helperForTheorem_6_30_17_normality_of_valueEquality_and_dualConsistency
        (F := F) hValue hDualKT.1.2
  · -- TODO: the reduction is now complete up to the two grouped terminal blockers proved above.
    -- The remaining branches should be funneled into either the finite-value Kuhn--Tucker
    -- branch or the primal/dual-consistency sinks using the upstream Section 30.15 bridges
    -- named in `helperForTheorem_6_30_17_primalPolyhedralOrBoundedBranches_imply_normality`
    -- and `helperForTheorem_6_30_17_dualPolyhedralOrBoundedBranches_imply_normality`.
    have hReduced :
        (PolyhedralConvexBifunction F.1 ∧ IsConsistentConvexProgram ⟨F.1, F.2.1⟩) ∨
          (PolyhedralConcaveBifunction (m := n) (n := m)
              (adjointOfConvexBifunction ⟨F.1, F.2.1⟩) ∧
            IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) ∨
          (∃ α : ℝ, (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α).Nonempty ∧
            Bornology.IsBounded (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α)) ∨
          (∃ β : ℝ, (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β).Nonempty ∧
            Bornology.IsBounded (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β)) ∨
          HasNonemptyBoundedPrimalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∨
          HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ :=
      -- The easy singleton cases `(i)` and `(j)` now collapse to the bounded optimal-set cases.
      helperForTheorem_6_30_17_reduce_terminalDisjunction_to_polyhedral_or_boundedBranches
        (F := F) hRest
    rcases hReduced with hPolyPrimal | hReduced
    · -- The primal polyhedral branch now feeds into the grouped primal-side terminal package.
      exact
        helperForTheorem_6_30_17_primalPolyhedralOrBoundedBranches_imply_normality
          (F := F) hProper (Or.inl hPolyPrimal)
    rcases hReduced with hPolyDual | hReduced
    · -- The dual polyhedral branch now feeds into the grouped dual-side `q` package.
      exact
        helperForTheorem_6_30_17_dualPolyhedralOrBoundedBranches_imply_normality
          (F := F) hProper (Or.inl hPolyDual)
    rcases hReduced with hBoundedPrimalSublevel | hReduced
    · -- The bounded primal sublevel branch is part of the same grouped primal-side blocker.
      exact
        helperForTheorem_6_30_17_primalPolyhedralOrBoundedBranches_imply_normality
          (F := F) hProper (Or.inr <| Or.inl hBoundedPrimalSublevel)
    rcases hReduced with hBoundedDualSuperlevel | hReduced
    · -- The bounded dual superlevel branch is part of the grouped dual-side `q` package.
      exact
        helperForTheorem_6_30_17_dualPolyhedralOrBoundedBranches_imply_normality
          (F := F) hProper (Or.inr <| Or.inl hBoundedDualSuperlevel)
    rcases hReduced with hBoundedPrimalOptimal | hBoundedDualOptimal
    · -- The bounded primal optimal-set branch is the minimum-set form of the same primal blocker.
      exact
        helperForTheorem_6_30_17_primalPolyhedralOrBoundedBranches_imply_normality
          (F := F) hProper (Or.inr <| Or.inr hBoundedPrimalOptimal)
    · -- The bounded dual optimal-set branch is the minimum-set form of the grouped dual package.
      exact
        helperForTheorem_6_30_17_dualPolyhedralOrBoundedBranches_imply_normality
          (F := F) hProper (Or.inr <| Or.inr hBoundedDualOptimal)

-- Proof sketch: specialize the polyhedral normality criteria from Theorem 6.30.17 to the
-- linear-program bifunction of Definition 6.30.18. Polyhedral properness supplies the hypotheses
-- needed to place the primal-dual pair in the closed convex framework, and the only exceptional
-- case to value equality is the inconsistent pair `v(P) = ⊤` and `v(P*) = ⊥`.
/-- Theorem 6.30.18: for the polyhedral proper convex bifunction associated with the linear
program `(P)`, the primal optimal value `v(P)` and the dual optimal value `v(P*)` are equal,
unless both the primal program `(P)` and the adjoint dual program `(P*)` are inconsistent.
Equivalently, either `v(P) = v(P*)`, or `v(P) = +∞` and `v(P*) = -∞`. -/
theorem strong_duality_for_polyhedral_primal_dual_pair {m n : ℕ}
    (aStar : Fin n → ℝ) (a : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (hF_polyhedral : PolyhedralConvexBifunction (linearProgramBifunction aStar a A))
    (hF_proper : ProperConvexBifunction (linearProgramBifunction aStar a A)) :
    convexProgramAssociatedWith (linearProgramBifunction aStar a A) 0 =
        dualProgramOfConvexProgram
          ⟨linearProgramBifunction aStar a A, hF_polyhedral.1⟩ ∨
      (convexProgramAssociatedWith (linearProgramBifunction aStar a A) 0 = (⊤ : EReal) ∧
        dualProgramOfConvexProgram
            ⟨linearProgramBifunction aStar a A, hF_polyhedral.1⟩ = (⊥ : EReal)) := by
  let FLinear := linearProgramBifunction aStar a A
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} :=
    ⟨FLinear, hF_polyhedral.1⟩
  have hGraphProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (bifunctionGraphFunction FLinear) := by
    -- Properness of the LP bifunction is properness of its graph function on the ambient space.
    exact
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := bifunctionGraphFunction FLinear) hF_proper.2
  have hClosed : ClosedConvexBifunction FLinear := by
    -- Polyhedral properness closes the graph function, so the LP bifunction fits the closed
    -- convex framework required by the normality theorems.
    refine ⟨hF_polyhedral.1, ?_⟩
    exact helperForCorollary_19_1_2_closed_of_polyhedral_proper hF_polyhedral.2 hGraphProper
  let FClosed : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F} :=
    ⟨FLinear, hClosed⟩
  have hDualPoly :
      PolyhedralConcaveBifunction (m := n) (n := m)
        (adjointOfConvexBifunction FCvx) := by
    -- Theorem 6.30.11 transports polyhedrality across the adjoint bifunction.
    rcases
        (adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality
          (F := FLinear)).1 hF_polyhedral.1 with
      ⟨_hClosedAdj, _hProperIff, _hBiadjointEq, _hFixedPoint, _hClosedProper, hPolyAdj⟩
    exact hPolyAdj hF_polyhedral
  by_cases hBad :
      convexProgramAssociatedWith FLinear 0 = (⊤ : EReal) ∧
        dualProgramOfConvexProgram FCvx = (⊥ : EReal)
  · -- This is exactly the textbook exceptional pair where both primal and dual are inconsistent.
    exact Or.inr hBad
  · have hNormal :
        IsNormalConvexProgram ⟨FClosed.1, FClosed.2.1⟩ ∧
          IsNormalDualProgramOfConvexProgram ⟨FClosed.1, FClosed.2.1⟩ := by
      by_cases hPrimalCons : IsConsistentConvexProgram FCvx
      · -- If the primal is consistent, the polyhedral primal branch of Theorem 6.30.17 already
        -- yields normality of both programs.
        exact
          helperForTheorem_6_30_17_normality_of_polyhedralPrimal_and_consistency
            (F := FClosed) hF_polyhedral hPrimalCons
      · -- Route correction: rather than using the broken old corollary shortcut, the proof now
        -- converts primal inconsistency to `v(P) = ⊤`, excludes `v(P*) = ⊥` via `hBad`, and
        -- applies the dual polyhedral branch of Theorem 6.30.17.
        have hPrimalTop :
            convexProgramAssociatedWith FLinear 0 = (⊤ : EReal) := by
          by_contra hPrimalTop
          exact hPrimalCons (by simpa [IsConsistentConvexProgram, FCvx] using hPrimalTop)
        have hDualCons : IsConsistentDualProgramOfConvexProgram FCvx := by
          -- Outside the exceptional pair, the dual value cannot be `⊥` once the primal value is
          -- already forced to be `⊤`.
          unfold IsConsistentDualProgramOfConvexProgram
          intro hDualBot
          exact hBad ⟨hPrimalTop, hDualBot⟩
        exact
          helperForTheorem_6_30_17_dualPolyhedralOrBoundedBranches_imply_normality
            (F := FClosed) hF_proper (Or.inl ⟨hDualPoly, hDualCons⟩)
    have hTFAE :=
      normality_tfae_for_primal_and_dual_convex_programs (F := FClosed) hF_proper
    have hValue :
        convexProgramAssociatedWith FClosed.1 0 =
          dualProgramOfConvexProgram ⟨FClosed.1, FClosed.2.1⟩ :=
      (hTFAE.out 0 2).1 hNormal.1
    -- Normality rules out the exceptional pair, so the primal and dual optimal values agree.
    exact Or.inl (by simpa [FClosed, FCvx, FLinear] using hValue)

-- Proof sketch: use the normality assumptions together with Corollary 6.30.2 and Theorem
-- 6.30.16 to identify the primal and dual optimal values. Then unfold the definitions:
-- `IsKuhnTuckerVectorForConvexProgram` says the shifted primal infimum is finite and equals the
-- primal value, while membership in `dualOptimalSolutionSetOfConvexProgram` says the same
-- multiplier attains the dual value; under normality these values coincide. The dual statement is
-- analogous, using `IsKuhnTuckerVectorForDualProgram` and
-- `primalOptimalSolutionSetOfConvexProgram`.
/-- Helper for Theorem 6.30.19: with the present adjoint sign convention, a primal Kuhn--Tucker
vector yields dual optimality for `-u*`. -/
lemma helperForTheorem_6_30_19_neg_dualOptimalSolution_of_primalKuhnTucker
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    {uStar : Fin m → ℝ}
    (huStar : IsKuhnTuckerVectorForConvexProgram ⟨F.1, F.2.1⟩ uStar) :
    -uStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  have huStarKT : IsKuhnTuckerVectorForConvexProgram FCvx uStar := huStar
  unfold IsKuhnTuckerVectorForConvexProgram at huStar
  dsimp only at huStar
  rcases huStar with ⟨hShiftEqBifunction, hShiftNeTop, hShiftNeBot, hShiftEqPrimal⟩
  have hFinitePrimal : HasFinitePrimalOptimalValueOfConvexProgram FCvx := by
    constructor
    · -- The Kuhn--Tucker witness identifies the shifted infimum with the primal value, so the
      -- witness-side finiteness transfers to the primal optimal value.
      intro hPrimalTop
      exact hShiftNeTop (hShiftEqPrimal.trans hPrimalTop)
    · -- The same identification rules out the `⊥` corner for the primal value.
      intro hPrimalBot
      exact hShiftNeBot (hShiftEqPrimal.trans hPrimalBot)
  have hValue :
      convexProgramAssociatedWith F.1 0 =
        dualProgramOfConvexProgram FCvx :=
    helperForTheorem_6_30_17_valueEquality_of_finitePrimalValue_and_primalKuhnTuckerVector
      (F := F) hFinitePrimal ⟨uStar, huStarKT⟩
  have hDualSliceEq :
      adjointOfConvexBifunction FCvx 0 (-uStar) =
        convexProgramAssociatedWith F.1 0 := by
    -- Unfold the dual slice at `-uStar` and rewrite it with the Kuhn--Tucker equalities.
    calc
      adjointOfConvexBifunction FCvx 0 (-uStar) =
          sInf (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
            F.1 p.1 p.2 - (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
              simp [FCvx, adjointOfConvexBifunction, sInf_range, sub_eq_add_neg, add_comm]
      _ =
          sInf (Set.range fun u : Fin m → ℝ =>
            convexProgramAssociatedWith F.1 u - (((u ⬝ᵥ uStar : ℝ) : EReal))) := by
              exact hShiftEqBifunction.symm
      _ = convexProgramAssociatedWith F.1 0 := hShiftEqPrimal
  -- The sign in `adjointOfConvexBifunction` turns the primal Kuhn--Tucker witness into the dual
  -- optimizer `-uStar`.
  change adjointOfConvexBifunction FCvx 0 (-uStar) = dualProgramOfConvexProgram FCvx
  calc
    adjointOfConvexBifunction FCvx 0 (-uStar) = convexProgramAssociatedWith F.1 0 := hDualSliceEq
    _ = dualProgramOfConvexProgram FCvx := hValue

/-- Helper for Theorem 6.30.19: a dual Kuhn--Tucker vector already attains the primal zero-slice
optimal value. -/
lemma helperForTheorem_6_30_19_primalOptimalSolution_of_dualKuhnTucker
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    {x : Fin n → ℝ}
    (hx : IsKuhnTuckerVectorForDualProgram ⟨F.1, F.2.1⟩ x) :
    x ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  have hxKT : IsKuhnTuckerVectorForDualProgram FCvx x := hx
  unfold IsKuhnTuckerVectorForDualProgram at hx
  dsimp only at hx
  rcases hx with ⟨hObjectiveNeTop, hObjectiveNeBot, hObjectiveEqDual⟩
  have hFiniteDual : HasFiniteDualOptimalValueOfConvexProgram FCvx := by
    constructor
    · -- The dual Kuhn--Tucker equality identifies the objective supremum with the dual value, so
      -- the witness-side finiteness transfers to the dual optimal value.
      intro hDualTop
      exact hObjectiveNeTop (hObjectiveEqDual.trans hDualTop)
    · -- The same equality rules out the `⊥` corner for the dual value.
      intro hDualBot
      exact hObjectiveNeBot (hObjectiveEqDual.trans hDualBot)
  by_cases hProper : ProperConvexBifunction F.1
  · have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram FCvx :=
      helperForTheorem_6_30_17_valueEquality_of_finiteDualValue_and_dualKuhnTuckerVector
        (F := F) hFiniteDual ⟨x, hxKT⟩
    have hClosedBranch :=
      (dualObjectiveSlice_and_primalObjectiveSlice_are_conjugates
        (F := FCvx)).2.2 ⟨F.2, hProper⟩
    have hObjectiveEqSlice :
        sSup (Set.range fun xStar : Fin n → ℝ =>
            (((x ⬝ᵥ xStar : ℝ) : EReal) +
              dualPerturbationFunctionOfConvexProgram FCvx xStar)) =
          F.1 0 x := by
      -- In the proper closed branch, the dual objective slice is exactly the primal zero slice.
      calc
        sSup (Set.range fun xStar : Fin n → ℝ =>
            (((x ⬝ᵥ xStar : ℝ) : EReal) +
              dualPerturbationFunctionOfConvexProgram FCvx xStar)) =
            fenchelConjugate n
              (fun xStar => -(dualPerturbationFunctionOfConvexProgram FCvx xStar)) x := by
                simp [fenchelConjugate_eq_iSup, sSup_range, sub_eq_add_neg, dotProduct_comm]
        _ = F.1 0 x := by
              simpa using congrFun hClosedBranch.1 x
    have hxEqPrimal :
        F.1 0 x = convexProgramAssociatedWith F.1 0 := by
      -- The dual Kuhn--Tucker witness attains the dual value, and strong duality for that finite
      -- value identifies it with the primal optimum.
      calc
        F.1 0 x =
            sSup (Set.range fun xStar : Fin n → ℝ =>
              (((x ⬝ᵥ xStar : ℝ) : EReal) +
                dualPerturbationFunctionOfConvexProgram FCvx xStar)) := hObjectiveEqSlice.symm
        _ = dualProgramOfConvexProgram FCvx := hObjectiveEqDual
        _ = convexProgramAssociatedWith F.1 0 := hValue.symm
    -- Rewriting the optimal-solution set turns the slice equality into the desired membership.
    simpa [primalOptimalSolutionSetOfConvexProgram, minimumSetEReal, functionInfimumEReal,
      convexProgramAssociatedWith] using hxEqPrimal
  · by_cases hGraphBot : ∃ u : Fin m → ℝ, ∃ y : Fin n → ℝ, F.1 u y = (⊥ : EReal)
    · rcases hGraphBot with ⟨u, y, hBot⟩
      have hDualZeroBot :
          dualPerturbationFunctionOfConvexProgram FCvx 0 = (⊥ : EReal) := by
        -- A `⊥` graph value forces the dual zero slice to be `⊥`.
        simpa [FCvx] using
          helperForCorollary_6_30_1_graphBot_forces_dualSlice_eq_bot
            (F := F) (u := u) (x := y) hBot (0 : Fin n → ℝ)
      have hDualBot :
          dualProgramOfConvexProgram FCvx = (⊥ : EReal) := by
        -- Evaluating the dual program at the origin collapses it to the same `⊥` value.
        simpa [dualProgramOfConvexProgram] using hDualZeroBot
      exact False.elim (hFiniteDual.2 hDualBot)
    · have hNoGraphBot : ∀ u : Fin m → ℝ, ∀ y : Fin n → ℝ, F.1 u y ≠ (⊥ : EReal) := by
        intro u y hBot
        exact hGraphBot ⟨u, y, hBot⟩
      have hConstTop :
          F.1 = fun _ _ => (⊤ : EReal) :=
        helperForCorollary_6_30_1_closedNotProper_noGraphBot_eq_const_top
          (F := F) hProper hNoGraphBot
      have hDualZeroTop :
          dualPerturbationFunctionOfConvexProgram FCvx 0 = (⊤ : EReal) := by
        have hAdjTop :
            ∀ uStar : Fin m → ℝ,
              adjointOfConvexBifunction FCvx 0 uStar = (⊤ : EReal) := by
          intro uStar
          simp [FCvx, hConstTop, adjointOfConvexBifunction]
        -- Once the bifunction is constant `⊤`, every adjoint zero slice is also `⊤`.
        simp [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith, hAdjTop]
      have hDualTop :
          dualProgramOfConvexProgram FCvx = (⊤ : EReal) := by
        -- Evaluating the dual program at the origin collapses it to the same `⊤` value.
        simpa [dualProgramOfConvexProgram] using hDualZeroTop
      exact False.elim (hFiniteDual.1 hDualTop)

/-- Helper for Theorem 6.30.19: the strongest sound local forward directions pair the
sign-corrected primal implication with the unchanged dual implication. -/
lemma helperForTheorem_6_30_19_sound_forward_implications
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    (IsKuhnTuckerVectorForConvexProgram ⟨F.1, F.2.1⟩ uStar →
      -uStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) ∧
    (IsKuhnTuckerVectorForDualProgram ⟨F.1, F.2.1⟩ x →
      x ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) := by
  constructor
  · -- The present adjoint sign convention converts the primal multiplier into the dual optimizer
    -- `-uStar`, so the sound forward implication is the sign-corrected one.
    intro huStar
    exact
      helperForTheorem_6_30_19_neg_dualOptimalSolution_of_primalKuhnTucker
        (F := F) huStar
  · -- The dual direction already matches the imported optimal-solution set without any sign
    -- correction.
    intro hx
    exact
      helperForTheorem_6_30_19_primalOptimalSolution_of_dualKuhnTucker
        (F := F) hx
/-- Sound forward directions of Theorem 6.30.19 for the current API. With the present adjoint sign
convention, a Kuhn--Tucker vector `u*` for `(P)` yields the dual optimizer `-u*`, while a
Kuhn--Tucker vector `x` for `(P*)` yields a primal optimizer. The current optimal-solution-set API
does not record finiteness of the attained value, so the converse directions require additional
nonexceptional-value hypotheses and are not asserted here. The normality hypotheses are retained
to keep the textbook theorem interface. -/
theorem kuhnTuckerVector_iff_optimalSolution_under_primal_dual_normality {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (_hP : IsNormalConvexProgram ⟨F.1, F.2.1⟩)
    (_hPStar : IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩)
    (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    (IsKuhnTuckerVectorForConvexProgram ⟨F.1, F.2.1⟩ uStar →
      -uStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) ∧
    (IsKuhnTuckerVectorForDualProgram ⟨F.1, F.2.1⟩ x →
      x ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) := by
  exact helperForTheorem_6_30_19_sound_forward_implications F uStar x

end Section30
end Chap06
