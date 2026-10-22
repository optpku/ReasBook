/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part11

section Chap06
section Section30

/-- Helper for Theorem 6.30.17: a unique primal optimal solution immediately gives a nonempty
bounded primal optimal-solution set, since a singleton is bounded. -/
lemma helperForTheorem_6_30_17_uniquePrimalOptimalSolution_implies_nonemptyBounded
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hUnique :
      HasUniquePrimalOptimalSolutionOfConvexProgram ⟨F.1, F.2.1⟩) :
    HasNonemptyBoundedPrimalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ := by
  rcases hUnique with ⟨x, hxSingleton⟩
  constructor
  · -- Rewriting the optimal-solution set as a singleton supplies a canonical witness.
    refine ⟨x, ?_⟩
    rw [hxSingleton]
    simp
  · -- A singleton subset of Euclidean space is automatically bounded.
    rw [hxSingleton]
    exact (Bornology.isBounded_singleton : Bornology.IsBounded ({x} : Set (Fin n → ℝ)))

/-- Helper for Theorem 6.30.17: a unique dual optimal solution immediately gives a nonempty
bounded dual optimal-solution set, since a singleton is bounded. -/
lemma helperForTheorem_6_30_17_uniqueDualOptimalSolution_implies_nonemptyBounded
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hUnique :
      HasUniqueDualOptimalSolutionOfConvexProgram ⟨F.1, F.2.1⟩) :
    HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ := by
  rcases hUnique with ⟨uStar, huSingleton⟩
  constructor
  · -- Rewriting the optimal-solution set as a singleton supplies a canonical witness.
    refine ⟨uStar, ?_⟩
    rw [huSingleton]
    simp
  · -- A singleton subset of Euclidean space is automatically bounded.
    rw [huSingleton]
    exact (Bornology.isBounded_singleton : Bornology.IsBounded ({uStar} : Set (Fin m → ℝ)))

/-- Helper for Theorem 6.30.17: a nonempty primal optimal-solution set produces a point on the
primal zero-slice attaining the primal optimal value. -/
lemma helperForTheorem_6_30_17_exists_primalZeroSlice_attaining_primalValue
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hNonempty :
      (primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩).Nonempty) :
    ∃ x : Fin n → ℝ,
      F.1 0 x = convexProgramAssociatedWith F.1 0 := by
  rcases hNonempty with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  -- Unfolding the optimal-solution set rewrites membership as attainment of the primal infimum.
  simpa [primalOptimalSolutionSetOfConvexProgram, minimumSetEReal, convexProgramAssociatedWith,
    functionInfimumEReal] using hx

/-- Helper for Theorem 6.30.17: a nonempty dual optimal-solution set produces a multiplier whose
adjoint zero-slice attains the dual optimal value. -/
lemma helperForTheorem_6_30_17_exists_dualZeroSlice_attaining_dualValue
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hNonempty :
      (dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩).Nonempty) :
    ∃ uStar : Fin m → ℝ,
      adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar =
        dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  rcases hNonempty with ⟨uStar, huStar⟩
  -- Unfolding the dual optimal-solution set rewrites membership as attainment of the dual
  -- supremum.
  exact ⟨uStar, huStar⟩

/-- Helper for Theorem 6.30.17: after the easy singleton reductions, the terminal disjunction
`(e)` through `(j)` only retains the genuinely hard polyhedral and bounded-set branches. -/
lemma helperForTheorem_6_30_17_reduce_terminalDisjunction_to_polyhedral_or_boundedBranches
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hTerminal :
      (PolyhedralConvexBifunction F.1 ∧ IsConsistentConvexProgram ⟨F.1, F.2.1⟩) ∨
        (PolyhedralConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F.1, F.2.1⟩) ∧
          IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) ∨
        (∃ α : ℝ, (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α).Nonempty ∧
          Bornology.IsBounded (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α)) ∨
        (∃ β : ℝ, (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β).Nonempty ∧
          Bornology.IsBounded (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β)) ∨
        HasUniquePrimalOptimalSolutionOfConvexProgram ⟨F.1, F.2.1⟩ ∨
        HasNonemptyBoundedPrimalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∨
        HasUniqueDualOptimalSolutionOfConvexProgram ⟨F.1, F.2.1⟩ ∨
        HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) :
    (PolyhedralConvexBifunction F.1 ∧ IsConsistentConvexProgram ⟨F.1, F.2.1⟩) ∨
      (PolyhedralConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F.1, F.2.1⟩) ∧
        IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) ∨
      (∃ α : ℝ, (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α).Nonempty ∧
        Bornology.IsBounded (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α)) ∨
      (∃ β : ℝ, (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β).Nonempty ∧
        Bornology.IsBounded (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β)) ∨
      HasNonemptyBoundedPrimalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∨
      HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ := by
  rcases hTerminal with hPolyPrimal | hTerminal
  · -- Branch `(e)` is already one of the reduced terminal alternatives.
    exact Or.inl hPolyPrimal
  rcases hTerminal with hPolyDual | hTerminal
  · -- Branch `(f)` is already one of the reduced terminal alternatives.
    exact Or.inr <| Or.inl hPolyDual
  rcases hTerminal with hBoundedSublevel | hTerminal
  · -- Branch `(g)` is already one of the reduced terminal alternatives.
    exact Or.inr <| Or.inr <| Or.inl hBoundedSublevel
  rcases hTerminal with hBoundedSuperlevel | hTerminal
  · -- Branch `(h)` is already one of the reduced terminal alternatives.
    exact Or.inr <| Or.inr <| Or.inr <| Or.inl hBoundedSuperlevel
  rcases hTerminal with hUniquePrimal | hTerminal
  · -- Branch `(i)` reduces to the bounded optimal-set form by the singleton argument above.
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inl
        (helperForTheorem_6_30_17_uniquePrimalOptimalSolution_implies_nonemptyBounded
          (F := F) hUniquePrimal)
  rcases hTerminal with hBoundedPrimal | hTerminal
  · -- The bounded primal optimal-set branch is already terminal after the reduction.
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hBoundedPrimal
  rcases hTerminal with hUniqueDual | hBoundedDual
  · -- Branch `(j)` reduces to the bounded dual optimal-set form by the singleton argument above.
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      (helperForTheorem_6_30_17_uniqueDualOptimalSolution_implies_nonemptyBounded
        (F := F) hUniqueDual)
  · -- The bounded dual optimal-set branch is already terminal after the reduction.
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr hBoundedDual

/-- Helper for Theorem 6.30.17: rewriting the dual bounded branches in terms of the convex
zero-slice `q u* = -F*(0, u*)` turns dual superlevel and optimal-solution sets into the Chapter
27 sublevel/minimum sets of a single convex function. -/
lemma helperForTheorem_6_30_17_dualBoundedBranches_rewrite_q_data
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    let q : (Fin m → ℝ) → EReal :=
      fun uStar : Fin m → ℝ => -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar
    dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = -functionInfimumEReal q ∧
      (∀ β : ℝ,
        dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β = sublevelSetEReal q (-β)) ∧
      dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ = minimumSetEReal q := by
  let q : (Fin m → ℝ) → EReal :=
    fun uStar : Fin m → ℝ => -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar
  have hDualEq :
      dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = -functionInfimumEReal q := by
    -- Rewrite the dual program as a supremum and then use `sup (-q) = - inf q`.
    calc
      dualProgramOfConvexProgram ⟨F.1, F.2.1⟩
          = sSup (Set.range fun uStar : Fin m → ℝ =>
              adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) :=
            helperForCorollary_6_30_2_dualSlice_eq_sSup_at_zero (F := F)
      _ = -functionInfimumEReal q := by
            simpa [q, functionInfimumEReal, sSup_range] using
              (ereal_iSup_neg_eq_neg_iInf (g := q))
  have hNegDualEq :
      -(dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) = functionInfimumEReal q := by
    -- Negating the previous identity turns the dual optimum into the actual infimum of `q`.
    simpa using congrArg Neg.neg hDualEq
  refine ⟨hDualEq, ?_⟩
  refine ⟨?_, ?_⟩
  · intro β
    ext uStar
    constructor
    · intro huStar
      -- Negating the dual superlevel inequality gives the corresponding sublevel inequality for
      -- `q`.
      change ((β : EReal) ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) at huStar
      change q uStar ≤ (((-β : ℝ) : EReal))
      simpa [q] using (EReal.neg_le_neg_iff.2 huStar)
    · intro huStar
      -- Reversing the same sign change recovers the original dual superlevel inequality.
      change q uStar ≤ (((-β : ℝ) : EReal)) at huStar
      change ((β : EReal) ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar)
      simpa [q] using (EReal.neg_le_neg_iff.1 huStar)
  · ext uStar
    constructor
    · intro huStar
      rw [minimumSetEReal]
      -- Negating the dual optimality equation turns it into the minimum-set equation for `q`.
      calc
        q uStar = -(adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) := rfl
        _ = -(dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) := by simpa [huStar]
        _ = functionInfimumEReal q := hNegDualEq
    · intro huStar
      rw [minimumSetEReal] at huStar
      -- Reversing the same negation rewrite recovers attainment of the dual optimum.
      have hNeg :
          -q uStar = -(functionInfimumEReal q) := congrArg Neg.neg huStar
      calc
        adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar = -q uStar := by simp [q]
        _ = -(functionInfimumEReal q) := hNeg
        _ = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := hDualEq.symm

/-- Helper for Theorem 6.30.17: the same dual bounded-branch rewrite can be expressed directly in
terms of the Fenchel conjugate of the primal perturbation function, precomposed with negation. -/
lemma helperForTheorem_6_30_17_dualBoundedBranches_rewrite_as_primalConjugateData
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    (∀ β : ℝ,
      dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β =
        sublevelSetEReal
          (fun uStar : Fin m → ℝ =>
            fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))
          (-β)) ∧
      dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ =
        minimumSetEReal
          (fun uStar : Fin m → ℝ =>
            fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar)) := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  let q0 : (Fin m → ℝ) → EReal :=
    fun uStar : Fin m → ℝ => -adjointOfConvexBifunction FCvx 0 uStar
  have hq0Eq :
      q0 =
        (fun uStar : Fin m → ℝ =>
          fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar)) := by
    funext uStar
    have hDualSlice :
        concaveConjugate
            (fun u : Fin m → ℝ => -(convexProgramAssociatedWith F.1 u)) uStar =
          adjointOfConvexBifunction FCvx 0 uStar := by
      -- The zero dual slice is the concave conjugate of the negated primal perturbation.
      simpa [FCvx] using
        congrFun (dualObjectiveSlice_and_primalObjectiveSlice_are_conjugates (F := FCvx)).1 uStar
    -- Negating that identity turns the dual zero slice into the Fenchel conjugate of the primal
    -- perturbation, precomposed by `uStar ↦ -uStar`.
    calc
      q0 uStar = -(adjointOfConvexBifunction FCvx 0 uStar) := rfl
      _ =
          -(concaveConjugate
            (fun u : Fin m → ℝ => -(convexProgramAssociatedWith F.1 u)) uStar) := by
              exact congrArg Neg.neg hDualSlice.symm
      _ = fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar) := by
            simpa using
              congrFun
                (helperForTheorem_6_30_15_neg_concaveConjugate_eq_fenchel_precomp_neg
                  (g := fun u : Fin m → ℝ => -(convexProgramAssociatedWith F.1 u)))
                uStar
  have hQData :=
    helperForTheorem_6_30_17_dualBoundedBranches_rewrite_q_data (F := F)
  constructor
  · intro β
    -- Replace the auxiliary zero-slice function `q0` by its conjugate-of-primal expression.
    calc
      dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β = sublevelSetEReal q0 (-β) :=
        hQData.2.1 β
      _ =
          sublevelSetEReal
            (fun uStar : Fin m → ℝ =>
              fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))
            (-β) := by
              ext uStar
              simp [sublevelSetEReal, hq0Eq]
  · -- The same replacement identifies the dual optimal set with the minimum set of that
    -- conjugate function.
    calc
      dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ = minimumSetEReal q0 := hQData.2.2
      _ =
          minimumSetEReal
            (fun uStar : Fin m → ℝ =>
              fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar)) := by
              ext uStar
              simp [minimumSetEReal, hq0Eq]

/-- Helper for Theorem 6.30.17: a bounded dual superlevel branch is exactly bounded nonempty
sublevel data for the conjugate of the primal perturbation function precomposed with negation. -/
lemma helperForTheorem_6_30_17_dualBoundedSuperlevel_implies_conjugateSublevelData
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hBoundedSuperlevel :
      ∃ β : ℝ, (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β).Nonempty ∧
        Bornology.IsBounded (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β)) :
    ∃ α : ℝ,
      (sublevelSetEReal
          (fun uStar : Fin m → ℝ =>
            fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))
          α).Nonempty ∧
        Bornology.IsBounded
          (sublevelSetEReal
            (fun uStar : Fin m → ℝ =>
              fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))
            α) := by
  rcases hBoundedSuperlevel with ⟨β, hNonempty, hBounded⟩
  have hRewrite :=
    (helperForTheorem_6_30_17_dualBoundedBranches_rewrite_as_primalConjugateData (F := F)).1 β
  -- The dual superlevel branch is just the corresponding conjugate sublevel branch at `α = -β`.
  refine ⟨-β, ?_⟩
  rw [← hRewrite]
  exact ⟨hNonempty, hBounded⟩

/-- Helper for Theorem 6.30.17: a bounded dual optimal-solution branch is exactly bounded
nonempty minimum-set data for the same conjugate-of-primal function. -/
lemma helperForTheorem_6_30_17_dualBoundedOptimalSet_implies_conjugateMinimumData
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hBoundedOptimal :
      HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) :
    (minimumSetEReal
        (fun uStar : Fin m → ℝ =>
          fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))).Nonempty ∧
      Bornology.IsBounded
        (minimumSetEReal
          (fun uStar : Fin m → ℝ =>
            fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))) := by
  have hRewrite :=
    (helperForTheorem_6_30_17_dualBoundedBranches_rewrite_as_primalConjugateData (F := F)).2
  -- Rewriting the dual optimal set through the conjugate model transports the bounded-minimum
  -- data unchanged.
  rw [← hRewrite]
  exact hBoundedOptimal

/-- Helper for Theorem 6.30.17: a nonempty primal sublevel set already bounds the primal value at
`u = 0` above by a real number, so the primal program is consistent. -/
lemma helperForTheorem_6_30_17_primalSublevel_nonempty_implies_primalConsistency
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    {α : ℝ}
    (hNonempty :
      (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α).Nonempty) :
    IsConsistentConvexProgram ⟨F.1, F.2.1⟩ := by
  rcases hNonempty with ⟨x, hx⟩
  unfold IsConsistentConvexProgram
  have hValueLe :
      convexProgramAssociatedWith F.1 0 ≤ (α : EReal) := by
    -- Evaluate the primal infimum at the sublevel witness `x`.
    calc
      convexProgramAssociatedWith F.1 0
          = sInf (Set.range fun y : Fin n → ℝ => F.1 0 y) :=
            helperForCorollary_6_30_2_primalSlice_eq_sInf_at_zero (F := F)
      _ ≤ F.1 0 x := sInf_le ⟨x, rfl⟩
      _ ≤ (α : EReal) := by
            simpa [primalSublevelSetOfConvexProgram, sublevelSetEReal] using hx
  intro hTop
  have hTopLe : (⊤ : EReal) ≤ (α : EReal) := by
    rw [hTop] at hValueLe
    exact hValueLe
  have hTopNotLe : ¬ ((⊤ : EReal) ≤ (α : EReal)) := by simp
  exact hTopNotLe hTopLe

/-- Helper for Theorem 6.30.17: a nonempty dual superlevel set already gives one adjoint slice
strictly above `-∞`, hence rules out dual inconsistency. -/
lemma helperForTheorem_6_30_17_dualSuperlevel_nonempty_implies_dualConsistency
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    {β : ℝ}
    (hNonempty :
      (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β).Nonempty) :
    IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  rcases hNonempty with ⟨uStar, huStar⟩
  unfold IsConsistentDualProgramOfConvexProgram
  have hSliceLeDual :
      adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar ≤
        dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
    -- Any slice value is bounded above by the supremum defining the dual program.
    calc
      adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar ≤
          sSup (Set.range fun v : Fin m → ℝ =>
            adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 v) := by
              exact le_sSup ⟨uStar, rfl⟩
      _ = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
        (helperForCorollary_6_30_2_dualSlice_eq_sSup_at_zero (F := F)).symm
  have hSliceNeBot :
      adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar ≠ (⊥ : EReal) := by
    -- A real lower bound `β` cannot hold at the value `⊥`.
    intro hBot
    have hLower :
        ((β : EReal) ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) := by
      simpa [dualSuperlevelSetOfConvexProgram] using huStar
    rw [hBot] at hLower
    simp at hLower
  intro hBot
  apply hSliceNeBot
  exact le_antisymm (by simpa [hBot] using hSliceLeDual) bot_le

/-- Helper for Theorem 6.30.17: a finite primal value produces a zero-slice point where the graph
value is finite. -/
lemma helperForTheorem_6_30_17_exists_finite_zeroSliceValue_of_finitePrimalValue
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hFinite : HasFinitePrimalOptimalValueOfConvexProgram ⟨F.1, F.2.1⟩) :
    ∃ x : Fin n → ℝ, F.1 0 x ≠ (⊤ : EReal) ∧ F.1 0 x ≠ (⊥ : EReal) := by
  rcases hFinite with ⟨hPrimalNeTop, hPrimalNeBot⟩
  have hExistsNotTop : ∃ x : Fin n → ℝ, F.1 0 x ≠ (⊤ : EReal) := by
    by_contra hNo
    have hAllTop : ∀ x : Fin n → ℝ, F.1 0 x = (⊤ : EReal) := by
      intro x
      by_contra hx
      exact hNo ⟨x, hx⟩
    have hPrimalTop : convexProgramAssociatedWith F.1 0 = (⊤ : EReal) := by
      -- If every zero-slice value is `⊤`, their infimum is `⊤` as well.
      unfold convexProgramAssociatedWith
      refine (sInf_eq_top).2 ?_
      rintro _ ⟨x, rfl⟩
      exact hAllTop x
    exact hPrimalNeTop hPrimalTop
  rcases hExistsNotTop with ⟨x0, hx0NeTop⟩
  have hx0NeBot : F.1 0 x0 ≠ (⊥ : EReal) := by
    intro hx0Bot
    have hPrimalLe : convexProgramAssociatedWith F.1 0 ≤ F.1 0 x0 := by
      exact sInf_le ⟨x0, rfl⟩
    rw [hx0Bot] at hPrimalLe
    exact hPrimalNeBot (le_antisymm hPrimalLe bot_le)
  exact ⟨x0, hx0NeTop, hx0NeBot⟩

/-- Helper for Theorem 6.30.17: a finite primal value rules out the closed-improper dichotomy, so
the graph function is proper. -/
lemma helperForTheorem_6_30_17_properConvexBifunction_of_finitePrimalValue
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hFinite : HasFinitePrimalOptimalValueOfConvexProgram ⟨F.1, F.2.1⟩) :
    ProperConvexBifunction F.1 := by
  rcases
      helperForTheorem_6_30_17_exists_finite_zeroSliceValue_of_finitePrimalValue
        (F := F) hFinite with
    ⟨x0, hx0NeTop, hx0NeBot⟩
  by_contra hNotProper
  have hTopOrBot :=
    helperForTheorem_6_30_11_convexGraph_values_top_or_bot_of_closed_not_proper
      (F := F.1) F.2 hNotProper (Fin.append 0 x0)
  rcases hTopOrBot with hTop | hBot
  · exact hx0NeTop (by simpa [bifunctionGraphFunction] using hTop)
  · exact hx0NeBot (by simpa [bifunctionGraphFunction] using hBot)

/-- Helper for Theorem 6.30.17: once the graph never takes the value `⊥`, the Chapter 30
convex-bifunction predicate yields the Chapter 29 product-coordinate convexity inequality. -/
lemma helperForTheorem_6_30_17_isConvexBifunction_of_convexBifunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : ConvexBifunction F)
    (hNoGraphBot : ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ, F u x ≠ (⊥ : EReal)) :
    IsConvexBifunction F := by
  have hConvOn :
      ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (bifunctionGraphFunction F) := by
    simpa [ConvexBifunction, ConvexFunction] using hF
  have hSeg :=
    (convexFunctionOn_iff_segment_inequality
      (C := (Set.univ : Set (Fin (m + n) → ℝ))) (f := bifunctionGraphFunction F)
      (hC := convex_univ)
      (hnotbot := by
        intro z hz
        simpa [bifunctionGraphFunction] using
          hNoGraphBot
            (fun i => z (Fin.castAdd n i))
            (fun j => z (Fin.natAdd m j)))).1 hConvOn
  intro p q a b ha hb hab
  by_cases hb0 : b = 0
  · subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simp [graphFunction]
  by_cases hb1 : b = 1
  · subst hb1
    have ha0 : a = 0 := by linarith
    subst ha0
    simp [graphFunction]
  have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hbLt : b < 1 := lt_of_le_of_ne (by linarith : b ≤ 1) hb1
  have haEq : a = 1 - b := by linarith
  -- Apply the segment inequality to the packed graph points and then unpack the coordinates.
  have hPacked :=
    hSeg (Fin.append p.1 p.2) (by simp) (Fin.append q.1 q.2) (by simp) b hbPos hbLt
  simpa [IsConvexBifunction, graphFunction, bifunctionGraphFunction, haEq,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hPacked

/-- Helper for Theorem 6.30.17: shifting a primal slice by a real linear term commutes with the
infimum over the primal variable. -/
lemma helperForTheorem_6_30_17_shiftedPrimalSlice_eq_shiftedPointwiseInfimum
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (uStar : Fin m → ℝ) (u : Fin m → ℝ) :
    convexProgramAssociatedWith F.1 u - (((u ⬝ᵥ uStar : ℝ) : EReal)) =
      sInf (Set.range fun x : Fin n → ℝ =>
        F.1 u x - (((u ⬝ᵥ uStar : ℝ) : EReal))) := by
  let c : ℝ := -(u ⬝ᵥ uStar : ℝ)
  -- Rewrite the shifted slice as addition by a finite real constant, then commute that constant
  -- across the infimum.
  calc
    convexProgramAssociatedWith F.1 u - (((u ⬝ᵥ uStar : ℝ) : EReal)) =
        ((c : EReal) + sInf (Set.range fun x : Fin n → ℝ => F.1 u x)) := by
          simp [convexProgramAssociatedWith, c, sub_eq_add_neg, add_comm]
    _ = (c : EReal) + iInf (fun x : Fin n → ℝ => F.1 u x) := by rw [sInf_range]
    _ = iInf (fun x : Fin n → ℝ => (c : EReal) + F.1 u x) := by
          rw [helperForTheorem_6_30_15_real_add_iInf]
    _ = sInf (Set.range fun x : Fin n → ℝ => (c : EReal) + F.1 u x) := by rw [sInf_range]
    _ = sInf (Set.range fun x : Fin n → ℝ =>
          F.1 u x - (((u ⬝ᵥ uStar : ℝ) : EReal))) := by
          congr 1
          ext x
          simp [c, sub_eq_add_neg, add_comm]

/-- Helper for Theorem 6.30.17: after a finite primal value is known, a Chapter 29
Kuhn--Tucker vector yields the Chapter 30 shifted-infimum witness used by the value-equality
branch. -/
lemma helperForTheorem_6_30_17_primalKuhnTucker_of_generalizedKuhnTucker
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hFinite : HasFinitePrimalOptimalValueOfConvexProgram ⟨F.1, F.2.1⟩)
    (G : BundledConvexBifunction m n)
    (hG : G.1 = F.1)
    {v : Fin m → ℝ}
    (hv : IsKuhnTuckerVector G v) :
    IsKuhnTuckerVectorForConvexProgram ⟨F.1, F.2.1⟩ (-v) := by
  let G' : BundledConvexBifunction m n := G
  cases G with
  | mk g hg =>
      dsimp at hG
      subst hG
      have hfiniteGeneral : IsFiniteEReal (generalizedConvexProgramOptimalValue G') := by
        -- The Chapter 29 optimal value is exactly the primal value at `u = 0`.
        simpa [HasFinitePrimalOptimalValueOfConvexProgram, generalizedConvexProgramOptimalValue,
          generalizedConvexProgramObjective, convexProgramAssociatedWith] using hFinite
      rcases hv with ⟨_hOptNeTop, _hOptNeBot, hLower⟩
      unfold IsKuhnTuckerVectorForConvexProgram
      dsimp
      have hShiftEqPrimal :
          sInf (Set.range fun u : Fin m → ℝ =>
            convexProgramAssociatedWith F.1 u - (((u ⬝ᵥ (-v) : ℝ) : EReal))) =
              convexProgramAssociatedWith F.1 0 := by
        apply le_antisymm
        · -- Evaluating the shifted family at `u = 0` gives the upper bound on the infimum.
          simpa using sInf_le
            (s := Set.range fun u : Fin m → ℝ =>
              convexProgramAssociatedWith F.1 u - (((u ⬝ᵥ (-v) : ℝ) : EReal)))
            ⟨(0 : Fin m → ℝ), by simp⟩
        · -- The Chapter 29 supporting inequality says every shifted slice stays above the optimal
          -- value, so the infimum of those shifted slices is still at least the primal value.
          refine le_sInf ?_
          intro y hy
          rcases hy with ⟨u, rfl⟩
          have hLower' := hLower u
          simpa [generalizedConvexProgramPerturbationFunction, generalizedConvexProgramOptimalValue,
            generalizedConvexProgramObjective, convexProgramAssociatedWith, dotProduct_comm,
            sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hLower'
      have hShiftEqBifunction :
          sInf (Set.range fun u : Fin m → ℝ =>
            convexProgramAssociatedWith F.1 u - (((u ⬝ᵥ (-v) : ℝ) : EReal))) =
              sInf (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
                F.1 p.1 p.2 - (((p.1 ⬝ᵥ (-v) : ℝ) : EReal))) := by
        have hSliceRewrite :
            (fun u : Fin m → ℝ =>
              convexProgramAssociatedWith F.1 u - (((u ⬝ᵥ (-v) : ℝ) : EReal))) =
              fun u : Fin m → ℝ =>
                sInf (Set.range fun x : Fin n → ℝ =>
                  F.1 u x - (((u ⬝ᵥ (-v) : ℝ) : EReal))) := by
          funext u
          exact
            helperForTheorem_6_30_17_shiftedPrimalSlice_eq_shiftedPointwiseInfimum
              (F := F) (-v) u
        calc
          sInf (Set.range fun u : Fin m → ℝ =>
            convexProgramAssociatedWith F.1 u - (((u ⬝ᵥ (-v) : ℝ) : EReal))) =
              sInf (Set.range fun u : Fin m → ℝ =>
                sInf (Set.range fun x : Fin n → ℝ =>
                  F.1 u x - (((u ⬝ᵥ (-v) : ℝ) : EReal)))) := by
                rw [hSliceRewrite]
          _ = sInf (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
                F.1 p.1 p.2 - (((p.1 ⬝ᵥ (-v) : ℝ) : EReal))) := by
                -- Flatten the iterated infimum over `u` and `x` into a single infimum over
                -- pairs.
                apply le_antisymm
                · refine le_sInf ?_
                  rintro _ ⟨⟨u, x⟩, rfl⟩
                  exact le_trans (sInf_le ⟨u, rfl⟩) (sInf_le ⟨x, rfl⟩)
                · refine le_sInf ?_
                  rintro _ ⟨u, rfl⟩
                  refine le_sInf ?_
                  rintro _ ⟨x, rfl⟩
                  exact sInf_le ⟨(u, x), rfl⟩
      refine ⟨hShiftEqBifunction, ?_, ?_, hShiftEqPrimal⟩
      · -- The shifted infimum is the finite primal value, so it cannot be `⊤`.
        intro hTop
        exact hfiniteGeneral.1 (hShiftEqPrimal.symm.trans hTop)
      · -- The same identification excludes the value `⊥`.
        intro hBot
        exact hfiniteGeneral.2 (hShiftEqPrimal.symm.trans hBot)

/-- Helper for Theorem 6.30.17: the primal polyhedral consistency branch `(e)` already yields
normality, splitting into the finite-value Kuhn--Tucker case and the `-∞` case. -/
lemma helperForTheorem_6_30_17_normality_of_polyhedralPrimal_and_consistency
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hPoly : PolyhedralConvexBifunction F.1)
    (hCons : IsConsistentConvexProgram ⟨F.1, F.2.1⟩) :
    IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
      IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  by_cases hFinite : HasFinitePrimalOptimalValueOfConvexProgram ⟨F.1, F.2.1⟩
  · have hProper :
        ProperConvexBifunction F.1 :=
      helperForTheorem_6_30_17_properConvexBifunction_of_finitePrimalValue
        (F := F) hFinite
    have hNoGraphBot : ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ, F.1 u x ≠ (⊥ : EReal) := by
      intro u x
      simpa [bifunctionGraphFunction] using hProper.2.1.1 (Fin.append u x)
    let G : BundledConvexBifunction m n :=
      ⟨F.1,
        helperForTheorem_6_30_17_isConvexBifunction_of_convexBifunction
          F.2.1 hNoGraphBot⟩
    have hGraphPoly :
        IsPolyhedralConvexFunction (m + n)
          (helperForCorollary_6_29_7_coordinateGraphFunction G) := by
      -- The Chapter 29 coordinate graph is exactly the polyhedral graph function of `F`.
      simpa [helperForCorollary_6_29_7_coordinateGraphFunction, bifunctionGraphFunction] using
        hPoly.2
    have hfiniteGeneral : IsFiniteEReal (generalizedConvexProgramOptimalValue G) := by
      -- The Chapter 29 optimal value is still the primal value at the origin.
      simpa [HasFinitePrimalOptimalValueOfConvexProgram, generalizedConvexProgramOptimalValue,
        generalizedConvexProgramObjective, convexProgramAssociatedWith] using hFinite
    rcases
        helperForCorollary_6_29_7_exists_kuhnTuckerVector_of_polyhedralGraph_and_finiteOptimalValue
          G hGraphPoly hfiniteGeneral with
      ⟨v, hv⟩
    have hKT :
        ∃ uStar : Fin m → ℝ,
          IsKuhnTuckerVectorForConvexProgram ⟨F.1, F.2.1⟩ uStar := by
      -- Convert the Chapter 29 multiplier into the Chapter 30 shifted-infimum formulation.
      exact
        ⟨-v,
          helperForTheorem_6_30_17_primalKuhnTucker_of_generalizedKuhnTucker
            (F := F) hFinite G rfl hv⟩
    have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      helperForTheorem_6_30_17_valueEquality_of_finitePrimalValue_and_primalKuhnTuckerVector
        (F := F) hFinite hKT
    -- Once the value equality is known in the finite branch, the normality sink already proved
    -- above applies directly.
    exact helperForTheorem_6_30_17_normality_of_finiteValueEquality (F := F) hFinite hValue
  · have hPrimalNotTop : convexProgramAssociatedWith F.1 0 ≠ (⊤ : EReal) := hCons
    have hPrimalBot : convexProgramAssociatedWith F.1 0 = (⊥ : EReal) := by
      -- Consistency rules out `⊤`, so the only non-finite possibility is `⊥`.
      by_cases hBot : convexProgramAssociatedWith F.1 0 = (⊥ : EReal)
      · exact hBot
      · exfalso
        exact hFinite ⟨hPrimalNotTop, hBot⟩
    have hDualLePrimal :
        dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ≤ convexProgramAssociatedWith F.1 0 := by
      -- Weak duality still bounds the dual value above by the primal value at the origin.
      simpa [dualProgramOfConvexProgram, dualPerturbationFunctionOfConvexProgram,
        concaveProgramAssociatedWith, convexProgramAssociatedWith] using
        helperForCorollary_6_30_2_weakDuality_at_zero (F := F)
    have hDualBot : dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal) := by
      -- Once the primal value is `-∞`, weak duality forces the dual value to be `-∞` as well.
      exact le_antisymm (by simpa [hPrimalBot] using hDualLePrimal) bot_le
    have hValue :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ :=
      hPrimalBot.trans hDualBot.symm
    -- The `-∞` branch already lies in the primal-consistency normality sink.
    exact
      helperForTheorem_6_30_17_normality_of_valueEquality_and_primalConsistency
        (F := F) hValue hCons

/-- Helper for Theorem 6.30.17: the bounded primal terminal branches provide exactly the
Section 30.15 input package consisting of either bounded nonempty primal sublevel data together
with primal consistency, or bounded optimal-set data together with an explicit minimizing
zero-slice witness. -/
lemma helperForTheorem_6_30_17_primalBoundedTerminal_extract_bridgeData
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hPrimalBounded :
      (∃ α : ℝ, (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α).Nonempty ∧
        Bornology.IsBounded (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α)) ∨
        HasNonemptyBoundedPrimalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) :
    (∃ α : ℝ,
      (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α).Nonempty ∧
        Bornology.IsBounded (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α) ∧
        IsConsistentConvexProgram ⟨F.1, F.2.1⟩) ∨
      (HasNonemptyBoundedPrimalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
        ∃ x : Fin n → ℝ, F.1 0 x = convexProgramAssociatedWith F.1 0) := by
  -- Split the bounded primal terminal package into the bounded-sublevel and bounded-minimum
  -- alternatives advertised in branches `(g)` and `(i)`.
  rcases hPrimalBounded with hBoundedSublevel | hBoundedOptimal
  · rcases hBoundedSublevel with ⟨α, hNonempty, hBounded⟩
    -- A nonempty primal sublevel set already forces ordinary primal consistency.
    refine Or.inl ⟨α, hNonempty, hBounded, ?_⟩
    exact
      helperForTheorem_6_30_17_primalSublevel_nonempty_implies_primalConsistency
        (F := F) hNonempty
  · -- A bounded nonempty optimal set carries an explicit minimizer of the zero slice.
    refine Or.inr ⟨hBoundedOptimal, ?_⟩
    exact
      helperForTheorem_6_30_17_exists_primalZeroSlice_attaining_primalValue
        (F := F) hBoundedOptimal.1

/-- Helper for Theorem 6.30.17: the dual terminal branches rewrite to the exact conjugate
sublevel/minimum package needed by the remaining Section 30.15 bridge. -/
lemma helperForTheorem_6_30_17_dualTerminal_extract_conjugateBridgeData
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hDualTerminal :
      (PolyhedralConcaveBifunction (m := n) (n := m)
          (adjointOfConvexBifunction ⟨F.1, F.2.1⟩) ∧
        IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) ∨
        (∃ β : ℝ, (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β).Nonempty ∧
          Bornology.IsBounded (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β)) ∨
        HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) :
    (PolyhedralConcaveBifunction (m := n) (n := m)
        (adjointOfConvexBifunction ⟨F.1, F.2.1⟩) ∧
      IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) ∨
      (∃ α : ℝ,
        (sublevelSetEReal
            (fun uStar : Fin m → ℝ =>
              fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))
            α).Nonempty ∧
          Bornology.IsBounded
            (sublevelSetEReal
              (fun uStar : Fin m → ℝ =>
                fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))
              α)) ∨
      ((minimumSetEReal
          (fun uStar : Fin m → ℝ =>
            fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar))).Nonempty ∧
        Bornology.IsBounded
          (minimumSetEReal
            (fun uStar : Fin m → ℝ =>
              fenchelConjugate m (convexProgramAssociatedWith F.1) (-uStar)))) := by
  -- Rewrite each bounded dual terminal branch into Chapter 27 data for the conjugate
  -- `uStar ↦ (convexProgramAssociatedWith F.1)^*(-uStar)`.
  rcases hDualTerminal with hPolyDual | hDualBounded
  · exact Or.inl hPolyDual
  rcases hDualBounded with hBoundedSuperlevel | hBoundedOptimal
  · -- Branch `(h)` becomes bounded sublevel data for the conjugate objective.
    exact Or.inr <| Or.inl
      (helperForTheorem_6_30_17_dualBoundedSuperlevel_implies_conjugateSublevelData
        (F := F) hBoundedSuperlevel)
  · -- Branch bounded `(j)` becomes bounded minimum-set data for the same conjugate objective.
    exact Or.inr <| Or.inr
      (helperForTheorem_6_30_17_dualBoundedOptimalSet_implies_conjugateMinimumData
        (F := F) hBoundedOptimal)

/-- Helper for Theorem 6.30.17: the same dual terminal branches also provide the local
dual-consistency or dual-attainment witnesses that the remaining Section 30.15 bridge still
needs. -/
lemma helperForTheorem_6_30_17_dualTerminal_extract_witnessBridgeData
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hDualTerminal :
      (PolyhedralConcaveBifunction (m := n) (n := m)
          (adjointOfConvexBifunction ⟨F.1, F.2.1⟩) ∧
        IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) ∨
        (∃ β : ℝ, (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β).Nonempty ∧
          Bornology.IsBounded (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β)) ∨
        HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) :
    (PolyhedralConcaveBifunction (m := n) (n := m)
        (adjointOfConvexBifunction ⟨F.1, F.2.1⟩) ∧
      IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) ∨
      (∃ β : ℝ, (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β).Nonempty ∧
        Bornology.IsBounded (dualSuperlevelSetOfConvexProgram ⟨F.1, F.2.1⟩ β) ∧
        IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) ∨
      (HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
        ∃ uStar : Fin m → ℝ,
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar =
            dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) := by
  -- Attach the extra local dual witness needed in the bounded-superlevel and bounded-optimal
  -- branches.
  rcases hDualTerminal with hPolyDual | hDualBounded
  · exact Or.inl hPolyDual
  rcases hDualBounded with hBoundedSuperlevel | hBoundedOptimal
  · rcases hBoundedSuperlevel with ⟨β, hNonempty, hBounded⟩
    -- Nonemptiness of the dual superlevel set still implies ordinary dual consistency.
    refine Or.inr <| Or.inl ⟨β, hNonempty, hBounded, ?_⟩
    exact
      helperForTheorem_6_30_17_dualSuperlevel_nonempty_implies_dualConsistency
        (F := F) hNonempty
  · -- A bounded nonempty dual optimal set gives an explicit maximizing zero slice.
    refine Or.inr <| Or.inr ⟨hBoundedOptimal, ?_⟩
    exact
      helperForTheorem_6_30_17_exists_dualZeroSlice_attaining_dualValue
        (F := F) hBoundedOptimal.1

/-- Helper for Theorem 6.30.17: global properness removes the graph-`⊥` obstruction, so the
closed branch of Theorem 6.30.15 can be specialized directly to the primal zero slice. -/
lemma helperForTheorem_6_30_17_closed_primalSlice_eq_negDualConjugate_of_globalProperness
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1) :
    fenchelConjugate n
        (fun xStar : Fin n → ℝ =>
          -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar) =
      (fun x : Fin n → ℝ => F.1 0 x) := by
  -- Properness of the graph rules out every graph-level `⊥`, so the repaired closed-slice
  -- identity from Theorem 6.30.15 is available without any extra case split.
  have hGraphNeBot :
      ∀ z : Fin (m + n) → ℝ, bifunctionGraphFunction F.1 z ≠ (⊥ : EReal) := by
    intro z
    exact hProper.2.1.1 z
  exact
    helperForTheorem_6_30_15_closed_primalSlice_eq_fenchelConjugate_negDualPerturbation_of_graph_ne_bot
      (F := ⟨F.1, F.2.1⟩) F.2 hGraphNeBot

/-- Helper for Theorem 6.30.17: a bounded nonempty primal sublevel already forces the origin into
the interior of the effective domain of the closed dual objective
`x* ↦ - cl (sup F*)(x*)`. This is the Chapter 27 conclusion available before the remaining
closure-to-actual-domain transport step. -/
lemma helperForTheorem_6_30_17_boundedPrimalSublevel_implies_interior_closedDualDomain
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1)
    {α : ℝ}
    (hNonempty :
      (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α).Nonempty)
    (hBounded :
      Bornology.IsBounded (primalSublevelSetOfConvexProgram ⟨F.1, F.2.1⟩ α)) :
    (0 : Fin n → ℝ) ∈
      interior
        (effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun xStar : Fin n → ℝ =>
            -(concaveClosure
              (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) xStar))) := by
  let f : (Fin n → ℝ) → EReal := fun x => F.1 0 x
  let q : (Fin n → ℝ) → EReal :=
    fun xStar : Fin n → ℝ =>
      -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar
  have hSliceEq :
      fenchelConjugate n q = f :=
    helperForTheorem_6_30_17_closed_primalSlice_eq_negDualConjugate_of_globalProperness
      (F := F) hProper
  have hfClosed : ClosedConvexFunction f := by
    -- The primal zero slice is the Fenchel conjugate of the actual negated dual perturbation.
    have hFenchelClosed := fenchelConjugate_closedConvex (n := n) (f := q)
    refine ⟨?_, ?_⟩
    · simpa [f, hSliceEq] using hFenchelClosed.2
    · simpa [f, hSliceEq] using hFenchelClosed.1
  have hfProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    refine ⟨?_, ?_, ?_⟩
    · -- Convexity on `Set.univ` is the restricted form of the closed-convex statement above.
      simpa [ConvexFunction, f] using hfClosed.1
    · -- The bounded nonempty sublevel provides a finite epigraph witness for the primal slice.
      rcases hNonempty with ⟨x, hx⟩
      refine ⟨(x, α), ?_⟩
      constructor
      · exact Set.mem_univ x
      · simpa [f, primalSublevelSetOfConvexProgram, sublevelSetEReal] using hx
    · -- Global properness rules out graph-level `⊥`, hence also `⊥` on the zero slice.
      intro x _hx
      simpa [f, bifunctionGraphFunction] using
        hProper.2.1.1 (Fin.append (0 : Fin m → ℝ) x)
  rcases closedProperConvexFunction_minimum_characterizations f hfClosed hfProper with
    ⟨_hA, _hB, _hC, hD, _hE, hF, _hG, _hH, _hI⟩
  have hSubClosed : IsClosed (sublevelSetEReal f α) := by
    -- Lower semicontinuity of the closed slice makes every real sublevel closed.
    exact (lowerSemicontinuous_iff_closed_sublevel (f := f)).1 hfClosed.2 α
  have hSubConvex : Convex ℝ (sublevelSetEReal f α) := by
    -- Convexity of the primal slice makes its real sublevel sets convex.
    simpa [sublevelSetEReal] using
      (convexFunction_level_sets_convex (f := f) hfClosed.1 (α := ((α : ℝ) : EReal))).2
  have hSubRecZero :
      Set.recessionCone (sublevelSetEReal f α) = ({0} : Set (Fin n → ℝ)) := by
    -- A nonempty bounded convex set has trivial recession cone.
    exact
      (helperForText_21_3_3_bounded_iff_recessionCone_eq_singleton_zero_fin
        (S := sublevelSetEReal f α) hNonempty hSubClosed hSubConvex).1 hBounded
  have hNoRecession : HasNoRecessionDirections f := by
    intro y hy
    have hyRec : y ∈ recessionConeEReal (F := Fin n → ℝ) f := by
      simpa [recessionConeEReal, IsRecessionDirection, recessionFunctionEReal,
        recessionFunction, erealDom, effectiveDomain_eq] using hy
    have hySub :
        y ∈ Set.recessionCone (sublevelSetEReal f α) := by
      rw [hF.2.2.1 α hNonempty]
      exact hyRec
    have hyZero : y ∈ ({0} : Set (Fin n → ℝ)) := by
      simpa [hSubRecZero] using hySub
    simpa using hyZero
  have hInteriorConjugate :
      (0 : Fin n → ℝ) ∈
        interior
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) :=
    hD.2.2 hNoRecession
  have hClosedBranch :=
    (dualObjectiveSlice_and_primalObjectiveSlice_are_conjugates
      (F := ⟨F.1, F.2.1⟩)).2.2 ⟨F.2, hProper⟩
  -- Rewrite the conjugate of the primal slice as the negated concave closure of the dual
  -- perturbation function.
  simpa [f] using (hClosedBranch.2 ▸ hInteriorConjugate)

/-- Helper for Theorem 6.30.17: once the primal zero slice is already known to be proper and the
origin lies in the interior of the effective domain of its Fenchel conjugate, the closed dual
interior criterion from Theorem 6.30.15 transports to strict consistency of the actual dual
program. -/
lemma helperForTheorem_6_30_17_dualStrictConsistency_of_zeroSliceProper_and_interior_conjugate
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1)
    (hZeroSliceProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun x : Fin n → ℝ => F.1 0 x))
    (hInteriorConjugate :
      (0 : Fin n → ℝ) ∈
        interior
          (effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (fenchelConjugate n (fun x : Fin n → ℝ => F.1 0 x)))) :
    IsStrictlyConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let f : (Fin n → ℝ) → EReal := fun x : Fin n → ℝ => F.1 0 x
  let q : (Fin n → ℝ) → EReal :=
    fun xStar : Fin n → ℝ =>
      -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar
  have hPrimalSliceEq :
      fenchelConjugate n q = f :=
    helperForTheorem_6_30_17_closed_primalSlice_eq_negDualConjugate_of_globalProperness
      (F := F) hProper
  have hClosedDualInterior :
      (0 : Fin n → ℝ) ∈
        interior
          (effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (fun xStar : Fin n → ℝ =>
              -(concaveClosure
                (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) xStar))) := by
    have hClosedBranch :=
      (dualObjectiveSlice_and_primalObjectiveSlice_are_conjugates
        (F := ⟨F.1, F.2.1⟩)).2.2 ⟨F.2, hProper⟩
    -- Rewrite the conjugate of the zero slice as the closed dual objective slice.
    simpa [f] using (hClosedBranch.2 ▸ hInteriorConjugate)
  have hqConv : ConvexFunction q := by
    -- Negating the dual perturbation puts the dual objective into the convex Fenchel framework.
    simpa [q] using
      helperForCorollary_6_30_3_negDualPerturbation_is_convex (F := F)
  have hqProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q := by
    -- Properness transfers across Fenchel conjugation because the closed primal slice is `q*`.
    have hProperIff :=
      (fenchelConjugate_closedConvex_proper_iff_and_biconjugate
        (n := n) (f := q) hqConv).2.1
    exact hProperIff.mp (by simpa [f] using (hPrimalSliceEq.symm ▸ hZeroSliceProper))
  have hClosedDualInterior' :
      (0 : Fin n → ℝ) ∈
        interior
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (convexFunctionClosure q)) := by
    -- Rewrite `- cl (sup F*)` as the convex closure of `q = - sup F*`.
    simpa [convexClosure, concaveClosure_eq_neg_convexClosure_neg, q] using
      hClosedDualInterior
  have hActualDualInteriorQ :
      (0 : Fin n → ℝ) ∈
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) :=
    helperForCorollary_25_1_2_mem_interior_effectiveDomain_of_closure_mem_interior
      hqProper hClosedDualInterior'
  have hActualDualInterior :
      (0 : Fin n → ℝ) ∈
        interior
          (extendedRealEffectiveDomain
            (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩)) := by
    -- Translate the convex effective domain of `q` back to the Chapter 30 dual effective domain.
    simpa [q, helperForTheorem_6_30_17_effectiveDomain_negDualPerturbation (F := F)] using
      hActualDualInteriorQ
  have hDualCons :
      IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
    -- Interior membership in the actual dual domain already rules out the value `-∞`.
    unfold IsConsistentDualProgramOfConvexProgram
    have h0Mem :
        (0 : Fin n → ℝ) ∈
          extendedRealEffectiveDomain
            (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) :=
      interior_subset hActualDualInterior
    simpa [extendedRealEffectiveDomain, dualProgramOfConvexProgram, bot_lt_iff_ne_bot] using
      h0Mem
  exact ⟨hDualCons, hActualDualInterior⟩
end Section30
end Chap06
