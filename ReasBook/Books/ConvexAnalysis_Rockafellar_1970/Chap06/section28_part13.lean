/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part12

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- Helper for Theorem 6.28.6: the dual minimax value is always the primal optimal value. -/
lemma helperForTheorem_6_28_6_lagrangianMinimax_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    P.lagrangianMinimax = P.optimalValue := by
  apply le_antisymm
  · -- Feasible points realize the dual supremum as the primal objective, so the minimax cannot exceed `optimalValue`.
    rw [BookOrdinaryConvexProgram.optimalValue]
    refine le_sInf ?_
    rintro _ ⟨x, hxFeasible, rfl⟩
    have hminimax_le_sup :
        P.lagrangianMinimax ≤ sSup (Set.range fun u : Fin m → ℝ => P.lagrangian u x) := by
      rw [BookOrdinaryConvexProgram.lagrangianMinimax]
      exact sInf_le ⟨x, rfl⟩
    calc
      P.lagrangianMinimax ≤ sSup (Set.range fun u : Fin m → ℝ => P.lagrangian u x) :=
        hminimax_le_sup
      _ = ((P.objective x : ℝ) : EReal) :=
        helperForTheorem_6_28_6_lagrangianDualSup_eq_objective_of_feasible P hxFeasible
  · -- At feasible points the dual supremum is the objective, and at nonfeasible points it is `⊤`.
    rw [BookOrdinaryConvexProgram.lagrangianMinimax]
    refine le_sInf ?_
    rintro _ ⟨x, rfl⟩
    by_cases hxFeasible : x ∈ P.feasibleSet
    · have hopt_le_obj : P.optimalValue ≤ ((P.objective x : ℝ) : EReal) := by
        rw [BookOrdinaryConvexProgram.optimalValue]
        exact sInf_le ⟨x, hxFeasible, rfl⟩
      calc
        P.optimalValue ≤ ((P.objective x : ℝ) : EReal) := hopt_le_obj
        _ = sSup (Set.range fun u : Fin m → ℝ => P.lagrangian u x) := by
              symm
              exact helperForTheorem_6_28_6_lagrangianDualSup_eq_objective_of_feasible P hxFeasible
    · have hsup_top :
          sSup (Set.range fun u : Fin m → ℝ => P.lagrangian u x) = (⊤ : EReal) :=
        helperForTheorem_6_28_6_lagrangianDualSup_eq_top_of_not_feasible P hxFeasible
      simpa [hsup_top] using (le_top : P.optimalValue ≤ (⊤ : EReal))

/-- Helper for Theorem 6.28.6: the primal maximin is always bounded above by the dual minimax. -/
lemma helperForTheorem_6_28_6_lagrangianMaximin_le_lagrangianMinimax
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    P.lagrangianMaximin ≤ P.lagrangianMinimax := by
  -- Fix `x`, dominate every `inf_x L(u, x)` by `sup_u L(u, x)`, and then infimize over `x`.
  rw [BookOrdinaryConvexProgram.lagrangianMaximin, BookOrdinaryConvexProgram.lagrangianMinimax]
  refine le_sInf ?_
  rintro _ ⟨x, rfl⟩
  refine sSup_le ?_
  rintro _ ⟨u, rfl⟩
  calc
    P.lagrangianPrimalInf u ≤ P.lagrangian u x :=
      helperForTheorem_6_28_6_lagrangianPrimalInf_le_lagrangian P u x
    _ ≤ sSup (Set.range fun u' : Fin m → ℝ => P.lagrangian u' x) := le_sSup ⟨u, rfl⟩

/-- Helper for Theorem 6.28.6: a Kuhn--Tucker vector identifies the fixed-multiplier primal
infimum with `P.optimalValue`. -/
lemma helperForTheorem_6_28_6_lagrangianPrimalInf_eq_optimalValue_of_isKuhnTuckerVector
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {uStar : Fin m → ℝ}
    (hKT : P.IsKuhnTuckerVector uStar) :
    P.lagrangianPrimalInf uStar = P.optimalValue := by
  rcases hKT with ⟨hu_nonneg, v, hvInf, hvOpt⟩
  have huStar : uStar ∈ P.lagrangeMultiplierSet := by
    simpa [BookOrdinaryConvexProgram.lagrangeMultiplierSet] using hu_nonneg
  apply le_antisymm
  · -- Restricting the Lagrangian range to `constraintSet` recovers the Kuhn--Tucker infimum.
    rw [BookOrdinaryConvexProgram.lagrangianPrimalInf]
    calc
      sInf (Set.range fun x : Fin n → ℝ => P.lagrangian uStar x) ≤
          sInf ((fun x : Fin n → ℝ => ((P.kuhnTuckerObjective uStar x : ℝ) : EReal)) ''
            P.constraintSet) := by
            refine sInf_le_sInf ?_
            rintro _ ⟨x, hxC, rfl⟩
            refine ⟨x, ?_⟩
            simp [BookOrdinaryConvexProgram.lagrangian, hxC, huStar]
      _ = (v : EReal) := hvInf
      _ = P.optimalValue := hvOpt.symm
  · -- The Kuhn--Tucker infimum is a lower bound for every Lagrangian value at `uStar`.
    rw [hvOpt, BookOrdinaryConvexProgram.lagrangianPrimalInf]
    refine le_sInf ?_
    rintro _ ⟨x, rfl⟩
    by_cases hxC : x ∈ P.constraintSet
    · have hLag_eq : P.lagrangian uStar x = (P.kuhnTuckerObjective uStar x : EReal) := by
        simp [BookOrdinaryConvexProgram.lagrangian, hxC, huStar]
      calc
        (v : EReal) =
            sInf ((fun x : Fin n → ℝ => ((P.kuhnTuckerObjective uStar x : ℝ) : EReal)) ''
              P.constraintSet) := hvInf.symm
        _ ≤ ((P.kuhnTuckerObjective uStar x : ℝ) : EReal) := sInf_le ⟨x, hxC, rfl⟩
        _ = P.lagrangian uStar x := hLag_eq.symm
    · have hLag_eq : P.lagrangian uStar x = (⊤ : EReal) := by
        simp [BookOrdinaryConvexProgram.lagrangian, hxC]
      have hv_le_top : (v : EReal) ≤ (⊤ : EReal) := by
        simp
      simpa [hLag_eq] using hv_le_top

/-- Helper for Theorem 6.28.6: when `P.constraintSet = ∅`, the fixed-multiplier primal infimum is
`⊤` because the Lagrangian is constantly `⊤`. -/
lemma helperForTheorem_6_28_6_lagrangianPrimalInf_eq_top_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    P.lagrangianPrimalInf uStar = (⊤ : EReal) := by
  -- With `P.constraintSet = ∅`, the Lagrangian range is the singleton `{⊤}`.
  simp [BookOrdinaryConvexProgram.lagrangianPrimalInf,
    helperForTheorem_6_28_4_lagrangian_eq_top_of_constraintSet_eq_empty, hconstraint]

/-- Helper for Theorem 6.28.6: when `P.constraintSet = ∅`, the maximin value is `⊤` because every
fixed-multiplier primal infimum is already `⊤`. -/
lemma helperForTheorem_6_28_6_lagrangianMaximin_eq_top_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    P.lagrangianMaximin = (⊤ : EReal) := by
  -- Every point in the supremum range is `⊤`.
  simp [BookOrdinaryConvexProgram.lagrangianMaximin,
    BookOrdinaryConvexProgram.lagrangianPrimalInf,
    helperForTheorem_6_28_4_lagrangian_eq_top_of_constraintSet_eq_empty, hconstraint]

/-- Helper for Theorem 6.28.6: when `P.constraintSet = ∅`, the minimax value is `⊤` because every
Lagrangian value is `⊤`. -/
lemma helperForTheorem_6_28_6_lagrangianMinimax_eq_top_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    P.lagrangianMinimax = (⊤ : EReal) := by
  -- The inner supremum and outer infimum both reduce to the singleton `{⊤}`.
  simp [BookOrdinaryConvexProgram.lagrangianMinimax,
    helperForTheorem_6_28_4_lagrangian_eq_top_of_constraintSet_eq_empty, hconstraint]

/-- Helper for Theorem 6.28.6: the minmax chain on the right-hand side of the theorem is true on
the empty-constraint-set branch, which is exactly the degenerate case that breaks the
equivalence. -/
lemma helperForTheorem_6_28_6_minmax_chain_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
      P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
      P.lagrangianMaximin = P.lagrangianMinimax := by
  constructor
  · -- All three quantities are `⊤`, so the strict lower bound by `-∞` is automatic.
    simpa [helperForTheorem_6_28_6_lagrangianPrimalInf_eq_top_of_constraintSet_eq_empty P uStar
      hconstraint] using (bot_lt_top : (⊥ : EReal) < (⊤ : EReal))
  · constructor
    · -- The primal infimum and maximin both collapse to `⊤`.
      rw [helperForTheorem_6_28_6_lagrangianPrimalInf_eq_top_of_constraintSet_eq_empty P uStar
        hconstraint,
        helperForTheorem_6_28_6_lagrangianMaximin_eq_top_of_constraintSet_eq_empty P hconstraint]
    · -- The maximin and minimax also collapse to `⊤`.
      rw [helperForTheorem_6_28_6_lagrangianMaximin_eq_top_of_constraintSet_eq_empty P
        hconstraint,
        helperForTheorem_6_28_6_lagrangianMinimax_eq_top_of_constraintSet_eq_empty P hconstraint]

/-- Helper for Theorem 6.28.6: the middle equivalence in the current Lean statement fails on the
empty-constraint-set branch. -/
lemma helperForTheorem_6_28_6_not_middle_iff_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    ¬ (P.IsKuhnTuckerVector uStar ↔
        (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
          P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
          P.lagrangianMaximin = P.lagrangianMinimax) := by
  -- The right-hand chain is true by the previous lemma, but no Kuhn--Tucker vector can exist.
  intro hiff
  have hchain :
      (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
        P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
        P.lagrangianMaximin = P.lagrangianMinimax :=
    helperForTheorem_6_28_6_minmax_chain_of_constraintSet_eq_empty P uStar hconstraint
  have hKT : P.IsKuhnTuckerVector uStar := hiff.mpr hchain
  exact helperForTheorem_6_28_4_not_isKuhnTuckerVector_of_constraintSet_eq_empty P uStar
    hconstraint hKT

/-- Helper for Theorem 6.28.6: the middle equivalence forces the constraint set to be nonempty. -/
lemma helperForTheorem_6_28_6_constraintSet_ne_empty_of_middle_iff
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
    (hmiddle :
      P.IsKuhnTuckerVector uStar ↔
        (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
          P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
          P.lagrangianMaximin = P.lagrangianMinimax) :
    P.constraintSet ≠ (∅ : Set (Fin n → ℝ)) := by
  -- On the empty-constraint-set branch the right-hand chain holds but no Kuhn--Tucker vector can
  -- exist, contradicting the assumed equivalence.
  intro hconstraint
  exact
    helperForTheorem_6_28_6_not_middle_iff_of_constraintSet_eq_empty P uStar hconstraint hmiddle

/-- Helper for Theorem 6.28.6: on the empty-constraint-set branch, the reverse implication in the
current Lean statement is itself false. -/
lemma helperForTheorem_6_28_6_not_reverse_implication_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    ¬ (((⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
          P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
          P.lagrangianMaximin = P.lagrangianMinimax) →
        P.IsKuhnTuckerVector uStar) := by
  -- The empty-constraint-set chain is true, so the reverse implication would produce a
  -- Kuhn--Tucker vector contradicting Theorem 6.28.4's empty-constraint lemma.
  intro hreverse
  have hchain :
      (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
        P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
        P.lagrangianMaximin = P.lagrangianMinimax :=
    helperForTheorem_6_28_6_minmax_chain_of_constraintSet_eq_empty P uStar hconstraint
  have hKT : P.IsKuhnTuckerVector uStar := hreverse hchain
  exact helperForTheorem_6_28_4_not_isKuhnTuckerVector_of_constraintSet_eq_empty P uStar
    hconstraint hKT

/-- Helper for Theorem 6.28.6: any proof of the reverse implication in the current Lean statement
forces the ambient constraint set to be nonempty, because the implication already fails on the
empty-constraint-set branch. -/
lemma helperForTheorem_6_28_6_constraintSet_ne_empty_of_reverse_implication
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
    (hreverse :
      ((⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
          P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
          P.lagrangianMaximin = P.lagrangianMinimax) →
        P.IsKuhnTuckerVector uStar) :
    P.constraintSet ≠ (∅ : Set (Fin n → ℝ)) := by
  -- The dedicated empty-branch contradiction shows that any valid reverse implication must
  -- exclude `P.constraintSet = ∅`.
  intro hconstraint
  exact
    helperForTheorem_6_28_6_not_reverse_implication_of_constraintSet_eq_empty
      P uStar hconstraint hreverse

/-- Helper for Theorem 6.28.6: the reverse implication from the minmax chain to a Kuhn--Tucker
vector is inconsistent with the already-proved empty-constraint-set branch lemmas. -/
lemma helperForTheorem_6_28_6_false_of_reverse_implication
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ)))
    (hreverse :
      ((⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
          P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
          P.lagrangianMaximin = P.lagrangianMinimax) →
        P.IsKuhnTuckerVector uStar) :
    False := by
  -- On `P.constraintSet = ∅`, the minmax chain holds for every `uStar`, but no Kuhn--Tucker vector
  -- can exist; thus any such `hreverse` yields a contradiction.
  have hcontra :
      ¬ (((⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
            P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
            P.lagrangianMaximin = P.lagrangianMinimax) →
          P.IsKuhnTuckerVector uStar) :=
    helperForTheorem_6_28_6_not_reverse_implication_of_constraintSet_eq_empty P uStar hconstraint
  exact hcontra hreverse

/-- Helper for Theorem 6.28.6: the empty-constraint-set construction from Theorem 6.28.4 gives
an explicit witness where the minmax chain holds but no Kuhn--Tucker vector exists. -/
lemma helperForTheorem_6_28_6_exists_counterexample_to_reverse_implication :
    ∃ (P : BookOrdinaryConvexProgram 1 0 0) (uStar : Fin 0 → ℝ),
      ((⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
          P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
          P.lagrangianMaximin = P.lagrangianMinimax) ∧
        ¬ P.IsKuhnTuckerVector uStar := by
  -- Use the in-file empty-constraint-set program from Theorem 6.28.4 as the concrete witness.
  refine ⟨helperForTheorem_6_28_4_counterexampleProgram 1, fun i : Fin 0 => Fin.elim0 i, ?_⟩
  constructor
  · -- The minmax chain collapses to `⊤ = ⊤ = ⊤` on the empty-constraint-set branch.
    exact
      helperForTheorem_6_28_6_minmax_chain_of_constraintSet_eq_empty
        (P := helperForTheorem_6_28_4_counterexampleProgram 1)
        (uStar := fun i : Fin 0 => Fin.elim0 i) rfl
  · -- The corresponding Kuhn--Tucker vector cannot exist on that same branch.
    exact
      helperForTheorem_6_28_4_not_isKuhnTuckerVector_of_constraintSet_eq_empty
        (P := helperForTheorem_6_28_4_counterexampleProgram 1)
        (uStar := fun i : Fin 0 => Fin.elim0 i) rfl

/-- Helper for Theorem 6.28.6: the reverse implication is not valid uniformly across all ordinary
convex programs, because the explicit empty-constraint-set counterexample already refutes it. -/
lemma helperForTheorem_6_28_6_reverse_implication_not_universally_valid :
    ¬ (∀ {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ),
          ((⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
              P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
              P.lagrangianMaximin = P.lagrangianMinimax) →
            P.IsKuhnTuckerVector uStar) := by
  intro hall
  -- Extract the concrete witness where the antecedent holds but the conclusion fails.
  rcases helperForTheorem_6_28_6_exists_counterexample_to_reverse_implication with
    ⟨P, uStar, hchain, hnotKT⟩
  -- Applying the alleged universal implication to that witness contradicts `hnotKT`.
  exact hnotKT (hall (P := P) (uStar := uStar) hchain)

/-- Helper for Theorem 6.28.6: the full three-part conclusion in the current Lean statement fails
on the empty-constraint-set branch because its middle equivalence already fails there. -/
lemma helperForTheorem_6_28_6_not_conclusion_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
    (xBar : Fin n → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    ¬ ((((P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution xBar) →
          P.lagrangian uStar xBar = P.optimalValue) ∧
        (P.IsKuhnTuckerVector uStar ↔
          (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
            P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
            P.lagrangianMaximin = P.lagrangianMinimax) ∧
        (P.IsKuhnTuckerVector uStar →
          P.lagrangianPrimalInf uStar = P.optimalValue ∧
            P.lagrangianMaximin = P.optimalValue ∧
            P.lagrangianMinimax = P.optimalValue))) := by
  intro hconclusion
  -- The second component of the conjunction is exactly the middle equivalence.
  have hmiddle :
      P.IsKuhnTuckerVector uStar ↔
        (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
          P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
          P.lagrangianMaximin = P.lagrangianMinimax :=
    hconclusion.2.1
  -- Apply the dedicated contradiction for the empty feasible-set branch.
  exact
    helperForTheorem_6_28_6_not_middle_iff_of_constraintSet_eq_empty P uStar hconstraint hmiddle

/-- Helper for Theorem 6.28.6: the full three-part conclusion already forces the constraint set to
be nonempty, because its middle equivalence cannot hold on the empty branch. -/
lemma helperForTheorem_6_28_6_constraintSet_ne_empty_of_full_conclusion
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
    (xBar : Fin n → ℝ)
    (hfull :
      (((P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution xBar) →
            P.lagrangian uStar xBar = P.optimalValue) ∧
          (P.IsKuhnTuckerVector uStar ↔
            (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
              P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
              P.lagrangianMaximin = P.lagrangianMinimax) ∧
          (P.IsKuhnTuckerVector uStar →
            P.lagrangianPrimalInf uStar = P.optimalValue ∧
              P.lagrangianMaximin = P.optimalValue ∧
              P.lagrangianMinimax = P.optimalValue))) :
    P.constraintSet ≠ (∅ : Set (Fin n → ℝ)) := by
  -- Extract the middle equivalence from the theorem conclusion; that component alone excludes
  -- `P.constraintSet = ∅`.
  exact helperForTheorem_6_28_6_constraintSet_ne_empty_of_middle_iff P uStar hfull.2.1

/-- Helper for Theorem 6.28.6: the empty-constraint-set counterexample from Theorem 6.28.4 also
refutes the full three-part conclusion stated here. -/
lemma helperForTheorem_6_28_6_counterexample_instance :
    ¬ ((((helperForTheorem_6_28_4_counterexampleProgram 1).IsKuhnTuckerVector
            (fun i : Fin 0 => Fin.elim0 i) ∧
          (helperForTheorem_6_28_4_counterexampleProgram 1).IsOptimalSolution
            (fun _ : Fin 1 => 0)) →
          (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangian
            (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => 0) =
              (helperForTheorem_6_28_4_counterexampleProgram 1).optimalValue) ∧
        ((helperForTheorem_6_28_4_counterexampleProgram 1).IsKuhnTuckerVector
            (fun i : Fin 0 => Fin.elim0 i) ↔
          (⊥ : EReal) <
              (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianPrimalInf
                (fun i : Fin 0 => Fin.elim0 i) ∧
            (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianPrimalInf
                (fun i : Fin 0 => Fin.elim0 i) =
              (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMaximin ∧
            (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMaximin =
              (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMinimax) ∧
        ((helperForTheorem_6_28_4_counterexampleProgram 1).IsKuhnTuckerVector
            (fun i : Fin 0 => Fin.elim0 i) →
          (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianPrimalInf
              (fun i : Fin 0 => Fin.elim0 i) =
            (helperForTheorem_6_28_4_counterexampleProgram 1).optimalValue ∧
            (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMaximin =
              (helperForTheorem_6_28_4_counterexampleProgram 1).optimalValue ∧
            (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMinimax =
              (helperForTheorem_6_28_4_counterexampleProgram 1).optimalValue)) := by
  -- The new full-conclusion helper already forces the constraint set to be nonempty, but the
  -- in-file counterexample has empty constraint set by construction.
  intro hfull
  have hnonempty :
      (helperForTheorem_6_28_4_counterexampleProgram 1).constraintSet ≠
        (∅ : Set (Fin 1 → ℝ)) :=
    helperForTheorem_6_28_6_constraintSet_ne_empty_of_full_conclusion
      (P := helperForTheorem_6_28_4_counterexampleProgram 1)
      (uStar := fun i : Fin 0 => Fin.elim0 i)
      (xBar := fun _ : Fin 1 => 0)
      hfull
  exact hnonempty rfl

/-- Helper for Theorem 6.28.6: the current unconditional Lean statement is false, as witnessed by
the empty-constraint-set counterexample program from Theorem 6.28.4. -/
lemma helperForTheorem_6_28_6_statement_false :
    ¬ (∀ {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
        (xBar : Fin n → ℝ),
        (((P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution xBar) →
              P.lagrangian uStar xBar = P.optimalValue) ∧
            (P.IsKuhnTuckerVector uStar ↔
              (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
                P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
                P.lagrangianMaximin = P.lagrangianMinimax) ∧
            (P.IsKuhnTuckerVector uStar →
              P.lagrangianPrimalInf uStar = P.optimalValue ∧
                P.lagrangianMaximin = P.optimalValue ∧
                P.lagrangianMinimax = P.optimalValue))) := by
  intro hall
  -- Specialize the alleged universal theorem statement to the explicit empty-set counterexample.
  have hcounter :
      ((((helperForTheorem_6_28_4_counterexampleProgram 1).IsKuhnTuckerVector
              (fun i : Fin 0 => Fin.elim0 i) ∧
            (helperForTheorem_6_28_4_counterexampleProgram 1).IsOptimalSolution
              (fun _ : Fin 1 => 0)) →
            (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangian
              (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => 0) =
                (helperForTheorem_6_28_4_counterexampleProgram 1).optimalValue) ∧
          ((helperForTheorem_6_28_4_counterexampleProgram 1).IsKuhnTuckerVector
              (fun i : Fin 0 => Fin.elim0 i) ↔
            (⊥ : EReal) <
                (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianPrimalInf
                  (fun i : Fin 0 => Fin.elim0 i) ∧
              (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianPrimalInf
                  (fun i : Fin 0 => Fin.elim0 i) =
                (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMaximin ∧
              (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMaximin =
                (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMinimax) ∧
          ((helperForTheorem_6_28_4_counterexampleProgram 1).IsKuhnTuckerVector
              (fun i : Fin 0 => Fin.elim0 i) →
            (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianPrimalInf
                (fun i : Fin 0 => Fin.elim0 i) =
              (helperForTheorem_6_28_4_counterexampleProgram 1).optimalValue ∧
              (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMaximin =
                (helperForTheorem_6_28_4_counterexampleProgram 1).optimalValue ∧
              (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMinimax =
                (helperForTheorem_6_28_4_counterexampleProgram 1).optimalValue)) :=
    hall (P := helperForTheorem_6_28_4_counterexampleProgram 1)
      (uStar := fun i : Fin 0 => Fin.elim0 i) (xBar := fun _ : Fin 1 => 0)
  -- The specialized statement contradicts the dedicated counterexample lemma above.
  exact helperForTheorem_6_28_6_counterexample_instance hcounter

/-- Helper for Theorem 6.28.6: a Kuhn--Tucker vector and an optimal solution identify the saddle
value with `P.optimalValue`. -/
lemma helperForTheorem_6_28_6_saddleValue_eq_optimalValue_of_isKuhnTuckerVector_and_optimalSolution
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {uStar : Fin m → ℝ} {xBar : Fin n → ℝ}
    (hKT : P.IsKuhnTuckerVector uStar) (hxOpt : P.IsOptimalSolution xBar) :
    P.lagrangian uStar xBar = P.optimalValue := by
  -- Feasibility places `xBar` in the finite branch of the Lagrangian.
  have hxC : xBar ∈ P.constraintSet := hxOpt.1.1
  -- A Kuhn--Tucker vector belongs to the multiplier cone.
  have huStar : uStar ∈ P.lagrangeMultiplierSet := by
    simpa [BookOrdinaryConvexProgram.lagrangeMultiplierSet] using hKT.1
  have hLag_eq : P.lagrangian uStar xBar = (P.kuhnTuckerObjective uStar xBar : EReal) := by
    -- On the feasible branch and inside the multiplier cone, the Lagrangian is the
    -- Kuhn--Tucker objective.
    simp [BookOrdinaryConvexProgram.lagrangian, hxC, huStar]
  -- Optimality turns the Kuhn--Tucker objective back into the primal objective.
  have hkuhn_eq_obj : P.kuhnTuckerObjective uStar xBar = P.objective xBar :=
    helperForTheorem_6_28_1_optimal_has_kuhnTuckerObjective_eq_objective P uStar hxOpt hKT
  have hkuhn_eq_obj' :
      (P.kuhnTuckerObjective uStar xBar : EReal) = ((P.objective xBar : ℝ) : EReal) := by
    exact_mod_cast hkuhn_eq_obj
  have hopt_eq : P.optimalValue = ((P.objective xBar : ℝ) : EReal) :=
    helperForTheorem_6_28_4_optimalValue_eq_objective_of_optimalSolution P hxOpt
  calc
    P.lagrangian uStar xBar = (P.kuhnTuckerObjective uStar xBar : EReal) := hLag_eq
    _ = ((P.objective xBar : ℝ) : EReal) := hkuhn_eq_obj'
    _ = P.optimalValue := hopt_eq.symm

/-- Helper for Theorem 6.28.6: a Kuhn--Tucker vector identifies the three extremal Lagrangian
values with `P.optimalValue`. -/
lemma helperForTheorem_6_28_6_extremalValues_eq_optimalValue_of_isKuhnTuckerVector
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {uStar : Fin m → ℝ}
    (hKT : P.IsKuhnTuckerVector uStar) :
    P.lagrangianPrimalInf uStar = P.optimalValue ∧
      P.lagrangianMaximin = P.optimalValue ∧
      P.lagrangianMinimax = P.optimalValue := by
  -- First identify the fixed-multiplier infimum with the optimal value.
  have hprimalInf_eq : P.lagrangianPrimalInf uStar = P.optimalValue :=
    helperForTheorem_6_28_6_lagrangianPrimalInf_eq_optimalValue_of_isKuhnTuckerVector P hKT
  -- Weak duality bounds the maximin value above by the optimal value.
  have hmaximin_upper : P.lagrangianMaximin ≤ P.optimalValue := by
    rw [BookOrdinaryConvexProgram.lagrangianMaximin]
    refine sSup_le ?_
    rintro _ ⟨u, rfl⟩
    exact helperForTheorem_6_28_6_lagrangianPrimalInf_le_optimalValue P u
  -- The Kuhn--Tucker multiplier itself gives the matching lower bound.
  have hmaximin_lower : P.optimalValue ≤ P.lagrangianMaximin := by
    calc
      P.optimalValue = P.lagrangianPrimalInf uStar := hprimalInf_eq.symm
      _ ≤ P.lagrangianMaximin := by
        rw [BookOrdinaryConvexProgram.lagrangianMaximin]
        exact le_sSup ⟨uStar, rfl⟩
  have hmaximin_eq : P.lagrangianMaximin = P.optimalValue := by
    exact le_antisymm hmaximin_upper hmaximin_lower
  -- The general maximin-minimax inequality provides the lower minimax bound.
  have hminimax_lower : P.optimalValue ≤ P.lagrangianMinimax := by
    calc
      P.optimalValue = P.lagrangianMaximin := hmaximin_eq.symm
      _ ≤ P.lagrangianMinimax :=
        helperForTheorem_6_28_6_lagrangianMaximin_le_lagrangianMinimax P
  -- Feasible points recover the objective from the dual supremum, yielding the upper bound.
  have hminimax_upper : P.lagrangianMinimax ≤ P.optimalValue := by
    rw [BookOrdinaryConvexProgram.optimalValue]
    refine le_sInf ?_
    rintro _ ⟨x, hxFeasible, rfl⟩
    have hminimax_le_sup :
        P.lagrangianMinimax ≤ sSup (Set.range fun u : Fin m → ℝ => P.lagrangian u x) := by
      rw [BookOrdinaryConvexProgram.lagrangianMinimax]
      exact sInf_le ⟨x, rfl⟩
    have hxSup_eq :
        sSup (Set.range fun u : Fin m → ℝ => P.lagrangian u x) = ((P.objective x : ℝ) : EReal) :=
      helperForTheorem_6_28_6_lagrangianDualSup_eq_objective_of_feasible P hxFeasible
    calc
      P.lagrangianMinimax ≤ sSup (Set.range fun u : Fin m → ℝ => P.lagrangian u x) :=
        hminimax_le_sup
      _ = ((P.objective x : ℝ) : EReal) := hxSup_eq
  have hminimax_eq : P.lagrangianMinimax = P.optimalValue := by
    exact le_antisymm hminimax_upper hminimax_lower
  exact ⟨hprimalInf_eq, hmaximin_eq, hminimax_eq⟩

/-- Helper for Theorem 6.28.6: a Kuhn--Tucker vector gives the forward minmax chain appearing on
the right-hand side of the theorem. -/
lemma helperForTheorem_6_28_6_minmax_chain_of_isKuhnTuckerVector
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {uStar : Fin m → ℝ}
    (hKT : P.IsKuhnTuckerVector uStar) :
    (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
      P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
      P.lagrangianMaximin = P.lagrangianMinimax := by
  -- The three extremal values all equal `P.optimalValue`.
  have hext :
      P.lagrangianPrimalInf uStar = P.optimalValue ∧
        P.lagrangianMaximin = P.optimalValue ∧
        P.lagrangianMinimax = P.optimalValue :=
    helperForTheorem_6_28_6_extremalValues_eq_optimalValue_of_isKuhnTuckerVector P hKT
  rcases hext with ⟨hprimalInf_eq, hmaximin_eq, hminimax_eq⟩
  rcases hKT with ⟨_hu_nonneg, v, _hvInf, hvOpt⟩
  have hbot_lt_opt : (⊥ : EReal) < P.optimalValue := by
    -- `P.optimalValue = (v : EReal)` is strictly above `⊥`.
    simpa [hvOpt] using (bot_lt_coe (r := v))
  have hbot_lt_inf : (⊥ : EReal) < P.lagrangianPrimalInf uStar := by
    simpa [hprimalInf_eq] using hbot_lt_opt
  refine And.intro hbot_lt_inf ?_
  refine And.intro ?_ ?_
  · -- The primal infimum and maximin coincide because both equal `P.optimalValue`.
    exact hprimalInf_eq.trans hmaximin_eq.symm
  · -- The maximin and minimax coincide because both equal `P.optimalValue`.
    exact hmaximin_eq.trans hminimax_eq.symm

/-- Helper for Theorem 6.28.6: on the nonempty branch, if a point `xBar` attains both the
fixed-multiplier primal infimum and the dual supremum at the common minmax value, then
`(uStar, xBar)` is a saddle pair and hence yields the Kuhn--Tucker certificate from Theorem
6.28.4. -/
lemma helperForTheorem_6_28_6_kuhnTuckerVector_and_optimalSolution_of_constraintSet_nonempty_and_attained_common_value
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hconstraint_nonempty : P.constraintSet.Nonempty) (uStar : Fin m → ℝ) (xBar : Fin n → ℝ)
    (hprimal_attain : P.lagrangian uStar xBar = P.lagrangianPrimalInf uStar)
    (hminimax_attain :
      sSup (Set.range fun u : Fin m → ℝ => P.lagrangian u xBar) = P.lagrangianMinimax)
    (hchain :
      P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
        P.lagrangianMaximin = P.lagrangianMinimax) :
    P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution xBar := by
  rcases hchain with ⟨hprimal_eq_maximin, hmaximin_eq_minimax⟩
  -- First turn the attainment hypotheses into the two saddle inequalities at `(uStar, xBar)`.
  have hsaddle : P.IsLagrangianSaddlePoint uStar xBar := by
    constructor
    · intro u
      -- Every Lagrangian value at `xBar` lies below the dual supremum attained there.
      calc
        P.lagrangian u xBar ≤ sSup (Set.range fun v : Fin m → ℝ => P.lagrangian v xBar) := by
          exact le_sSup ⟨u, rfl⟩
        _ = P.lagrangianMinimax := hminimax_attain
        _ = P.lagrangianMaximin := hmaximin_eq_minimax.symm
        _ = P.lagrangianPrimalInf uStar := hprimal_eq_maximin.symm
        _ = P.lagrangian uStar xBar := hprimal_attain.symm
    · intro z
      -- The attained primal infimum is automatically bounded above by every value at `uStar`.
      calc
        P.lagrangian uStar xBar = P.lagrangianPrimalInf uStar := hprimal_attain
        _ ≤ P.lagrangian uStar z :=
          helperForTheorem_6_28_6_lagrangianPrimalInf_le_lagrangian P uStar z
  -- On `P.constraintSet.Nonempty`, Theorem 6.28.4 converts saddle pairs into the desired data.
  exact
    (helperForTheorem_6_28_4_kuhnTuckerVector_and_optimalSolution_iff_lagrangianSaddlePoint
      P hconstraint_nonempty uStar xBar).2 hsaddle

/-- Helper for Theorem 6.28.6: on the nonempty-constraint branch, a strict lower bound
`⊥ < inf_x L(uStar, x)` forces `uStar` into the Lagrange multiplier cone. -/
lemma helperForTheorem_6_28_6_mem_lagrangeMultiplierSet_of_bot_lt_lagrangianPrimalInf
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hconstraint_nonempty : P.constraintSet.Nonempty) {uStar : Fin m → ℝ}
    (hbot_lt : (⊥ : EReal) < P.lagrangianPrimalInf uStar) :
    uStar ∈ P.lagrangeMultiplierSet := by
  by_contra huStar
  rcases hconstraint_nonempty with ⟨x0, hx0C⟩
  -- A point of `constraintSet` witnesses the `-∞` branch of the Lagrangian for inadmissible multipliers.
  have hLag_eq : P.lagrangian uStar x0 = (⊥ : EReal) := by
    simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x0, hx0C, huStar] using
      (helperForTheorem_6_28_4_lagrangian_simp P uStar x0).2.1 hx0C huStar
  have hInf_le_bot : P.lagrangianPrimalInf uStar ≤ (⊥ : EReal) := by
    simpa [hLag_eq] using helperForTheorem_6_28_6_lagrangianPrimalInf_le_lagrangian P uStar x0
  have hInf_eq_bot : P.lagrangianPrimalInf uStar = (⊥ : EReal) :=
    le_antisymm hInf_le_bot bot_le
  simpa [hInf_eq_bot] using hbot_lt

/-- Helper for Theorem 6.28.6: once `uStar` is an admissible multiplier, the fixed-multiplier
Lagrangian infimum is exactly the Kuhn--Tucker infimum over `constraintSet`. -/
lemma helperForTheorem_6_28_6_kuhnTuckerInf_eq_lagrangianPrimalInf_of_mem_lagrangeMultiplierSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {uStar : Fin m → ℝ}
    (huStar : uStar ∈ P.lagrangeMultiplierSet) :
    sInf ((fun x : Fin n → ℝ => ((P.kuhnTuckerObjective uStar x : ℝ) : EReal)) '' P.constraintSet) =
      P.lagrangianPrimalInf uStar := by
  apply le_antisymm
  · -- Every Lagrangian value is bounded below by the constrained Kuhn--Tucker infimum.
    rw [BookOrdinaryConvexProgram.lagrangianPrimalInf]
    refine le_sInf ?_
    rintro _ ⟨x, rfl⟩
    by_cases hxC : x ∈ P.constraintSet
    · have hLag_eq : P.lagrangian uStar x = (P.kuhnTuckerObjective uStar x : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x, hxC, huStar] using
          (helperForTheorem_6_28_4_lagrangian_simp P uStar x).2.2 hxC huStar
      calc
        sInf ((fun x : Fin n → ℝ => ((P.kuhnTuckerObjective uStar x : ℝ) : EReal)) ''
            P.constraintSet) ≤ ((P.kuhnTuckerObjective uStar x : ℝ) : EReal) := sInf_le ⟨x, hxC, rfl⟩
        _ = P.lagrangian uStar x := hLag_eq.symm
    · have hLag_eq : P.lagrangian uStar x = (⊤ : EReal) := by
        exact (helperForTheorem_6_28_4_lagrangian_simp P uStar x).1 hxC
      simpa [hLag_eq] using
        (le_top :
          sInf ((fun x : Fin n → ℝ => ((P.kuhnTuckerObjective uStar x : ℝ) : EReal)) ''
            P.constraintSet) ≤ (⊤ : EReal))
  · -- Restricting the Lagrangian range to `constraintSet` recovers the Kuhn--Tucker infimum.
    rw [BookOrdinaryConvexProgram.lagrangianPrimalInf]
    refine le_sInf ?_
    rintro _ ⟨x, hxC, rfl⟩
    have hLag_eq : P.lagrangian uStar x = (P.kuhnTuckerObjective uStar x : EReal) := by
      simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x, hxC, huStar] using
        (helperForTheorem_6_28_4_lagrangian_simp P uStar x).2.2 hxC huStar
    calc
      sInf (Set.range fun x : Fin n → ℝ => P.lagrangian uStar x) ≤ P.lagrangian uStar x :=
        sInf_le ⟨x, rfl⟩
      _ = ((P.kuhnTuckerObjective uStar x : ℝ) : EReal) := hLag_eq

/-- Helper for Theorem 6.28.6: specializing the reverse implication to the explicit
empty-constraint-set counterexample already yields a contradiction. -/
lemma helperForTheorem_6_28_6_false_of_reverse_implication_for_counterexampleProgram
    (hreverse :
      ((⊥ : EReal) <
            (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianPrimalInf
              (fun i : Fin 0 => Fin.elim0 i) ∧
          (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianPrimalInf
              (fun i : Fin 0 => Fin.elim0 i) =
            (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMaximin ∧
          (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMaximin =
            (helperForTheorem_6_28_4_counterexampleProgram 1).lagrangianMinimax) →
        (helperForTheorem_6_28_4_counterexampleProgram 1).IsKuhnTuckerVector
          (fun i : Fin 0 => Fin.elim0 i)) :
    False := by
  -- Reuse the general empty-constraint contradiction on the concrete witness from Theorem 6.28.4.
  exact
    helperForTheorem_6_28_6_false_of_reverse_implication
      (P := helperForTheorem_6_28_4_counterexampleProgram 1)
      (uStar := fun i : Fin 0 => Fin.elim0 i)
      (hconstraint := rfl) hreverse

/-- Helper for Theorem 6.28.6: the remaining reverse implication from the minmax chain to a
Kuhn--Tucker vector holds once the empty-constraint-set obstruction has been excluded. -/
lemma helperForTheorem_6_28_6_reverse_implication_from_minmax_chain
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hconstraint_nonempty : P.constraintSet.Nonempty) (uStar : Fin m → ℝ) :
    ((⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
        P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
        P.lagrangianMaximin = P.lagrangianMinimax) →
      P.IsKuhnTuckerVector uStar := by
  intro hchain
  rcases hchain with ⟨hbot_lt, hprimal_eq_maximin, hmaximin_eq_minimax⟩
  -- Route correction: on the repaired nonempty branch, the converse is proved by value identities
  -- rather than by trying to extract an attained saddle pair.
  have huStar : uStar ∈ P.lagrangeMultiplierSet :=
    helperForTheorem_6_28_6_mem_lagrangeMultiplierSet_of_bot_lt_lagrangianPrimalInf
      P hconstraint_nonempty hbot_lt
  have hprimal_eq_opt : P.lagrangianPrimalInf uStar = P.optimalValue := by
    calc
      P.lagrangianPrimalInf uStar = P.lagrangianMaximin := hprimal_eq_maximin
      _ = P.lagrangianMinimax := hmaximin_eq_minimax
      _ = P.optimalValue := helperForTheorem_6_28_6_lagrangianMinimax_eq_optimalValue P
  have hkuhnInf :
      sInf ((fun x : Fin n → ℝ => ((P.kuhnTuckerObjective uStar x : ℝ) : EReal)) ''
          P.constraintSet) = P.lagrangianPrimalInf uStar :=
    helperForTheorem_6_28_6_kuhnTuckerInf_eq_lagrangianPrimalInf_of_mem_lagrangeMultiplierSet
      P huStar
  rcases hconstraint_nonempty with ⟨x0, hx0C⟩
  -- A point of `constraintSet` bounds the fixed-multiplier infimum strictly below `⊤`.
  have hInf_lt_top : P.lagrangianPrimalInf uStar < (⊤ : EReal) := by
    have hLag_eq : P.lagrangian uStar x0 = (P.kuhnTuckerObjective uStar x0 : EReal) := by
      simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x0, hx0C, huStar] using
        (helperForTheorem_6_28_4_lagrangian_simp P uStar x0).2.2 hx0C huStar
    calc
      P.lagrangianPrimalInf uStar ≤ P.lagrangian uStar x0 :=
        helperForTheorem_6_28_6_lagrangianPrimalInf_le_lagrangian P uStar x0
      _ = (P.kuhnTuckerObjective uStar x0 : EReal) := hLag_eq
      _ < (⊤ : EReal) := EReal.coe_lt_top _
  have hInf_ne_top : P.lagrangianPrimalInf uStar ≠ (⊤ : EReal) :=
    (lt_top_iff_ne_top).1 hInf_lt_top
  have hInf_ne_bot : P.lagrangianPrimalInf uStar ≠ (⊥ : EReal) :=
    (bot_lt_iff_ne_bot).1 hbot_lt
  lift P.lagrangianPrimalInf uStar to ℝ using ⟨hInf_ne_top, hInf_ne_bot⟩ with v hv
  refine ⟨?_, v, ?_, ?_⟩
  · -- Membership in the multiplier cone is exactly nonnegativity of the inequality coordinates.
    simpa [BookOrdinaryConvexProgram.lagrangeMultiplierSet] using huStar
  · -- Rewrite the constrained Kuhn--Tucker infimum to the fixed-multiplier primal infimum.
    exact hkuhnInf
  · -- The common minmax value is exactly the same finite real number.
    exact hprimal_eq_opt.symm

-- Proof sketch: use Theorem 6.28.4 to convert between Kuhn--Tucker vectors, optimal solutions,
-- and saddle points of `P.lagrangian`. A saddle point forces the fixed-multiplier infimum, the
-- maximin value, and the minimax value to coincide with the saddle value, while the Kuhn--Tucker
-- characterization identifies that common value with `P.optimalValue` and excludes `-∞`.
/-- Theorem 6.28.6: Let `P` be an ordinary convex program with Lagrangian `P.lagrangian`. If
`uStar` is a Kuhn--Tucker vector for `P` and `xBar` is an optimal solution of `P`, then the
saddle value `P.lagrangian uStar xBar` is the optimal value of `P`. More generally, once the
constraint set is nonempty, `uStar` is a Kuhn--Tucker vector for `P` if and only if
`-∞ < inf_x L(uStar, x) = sup_u inf_x L(u, x) = inf_x sup_u L(u, x)`, and in that case the
common extremum value is `P.optimalValue`. -/
theorem isKuhnTuckerVector_iff_lagrangianPrimalInf_eq_maximin_eq_minimax_and_saddleValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hconstraint_nonempty : P.constraintSet.Nonempty)
    (uStar : Fin m → ℝ) (xBar : Fin n → ℝ) :
    (((P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution xBar) →
        P.lagrangian uStar xBar = P.optimalValue) ∧
      (P.IsKuhnTuckerVector uStar ↔
        (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
          P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
          P.lagrangianMaximin = P.lagrangianMinimax) ∧
      (P.IsKuhnTuckerVector uStar →
        P.lagrangianPrimalInf uStar = P.optimalValue ∧
          P.lagrangianMaximin = P.optimalValue ∧
          P.lagrangianMinimax = P.optimalValue)) := by
  -- The empty-constraint-set counterexample has been excluded by `hconstraint_nonempty`.
  constructor
  · intro hKTOpt
    rcases hKTOpt with ⟨hKT, hxOpt⟩
    -- Reuse the dedicated saddle-value helper for the first part of the theorem.
    exact
      helperForTheorem_6_28_6_saddleValue_eq_optimalValue_of_isKuhnTuckerVector_and_optimalSolution
        P hKT hxOpt
  constructor
  · -- Middle equivalence: the forward direction is provable from the Kuhn--Tucker optimality
    -- facts already formalized above; the reverse direction is exactly the (false) direction on
    -- the empty-constraint-set branch.
    constructor
    · intro hKT
      -- The forward implication is the positive direction of the theorem and is fully proved.
      exact helperForTheorem_6_28_6_minmax_chain_of_isKuhnTuckerVector P hKT
    · -- On the nonempty branch, the reverse implication is the repaired converse.
      intro hchain
      -- The repaired local helper proves the converse by identifying the common value with the
      -- finite Kuhn--Tucker infimum.
      exact
        helperForTheorem_6_28_6_reverse_implication_from_minmax_chain
          P hconstraint_nonempty uStar hchain
  · intro hKT
    -- The third implication is the common-value statement already extracted above.
    exact helperForTheorem_6_28_6_extremalValues_eq_optimalValue_of_isKuhnTuckerVector P hKT


end Section28
end Chap06
