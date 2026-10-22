/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part1

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- Helper for Corollary 6.28.1: nonnegative inequality multipliers preserve convexity of the
weighted Kuhn--Tucker objective on the ambient constraint set. -/
lemma helperForCorollary_6_28_1_kuhnTuckerObjective_convexOn_of_multiplier_nonneg
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i) :
    ConvexOn ℝ P.constraintSet (P.kuhnTuckerObjective lambda) := by
  -- The inequality part stays convex because each coefficient is nonnegative.
  have hineq_term :
      ∀ i : Fin r,
        ConvexOn ℝ P.constraintSet
          (fun x => P.inequalityMultipliers lambda i * P.inequalityConstraint i x) := by
    intro i
    simpa [smul_eq_mul] using
      (ConvexOn.smul (c := P.inequalityMultipliers lambda i)
        (hc := hlambda_nonneg i) (P.inequalityConstraint_convexOn i))
  have hineq_sum :
      ConvexOn ℝ P.constraintSet
        (fun x => ∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x) := by
    classical
    have hs :
        ∀ s : Finset (Fin r),
          ConvexOn ℝ P.constraintSet
            (fun x => Finset.sum s (fun i => P.inequalityMultipliers lambda i * P.inequalityConstraint i x)) := by
      intro s
      induction s using Finset.induction with
      | empty =>
          simpa using (convexOn_const (s := P.constraintSet) (c := (0 : ℝ)) P.convex_constraintSet)
      | @insert i s hi hs =>
          simpa [Finset.sum_insert hi] using ConvexOn.add (hineq_term i) hs
    simpa using hs Finset.univ
  -- The equality part stays affine, hence convex, even without a sign restriction.
  have hequality_term :
      ∀ i : Fin (m - r),
        ConvexOn ℝ P.constraintSet
          (fun x => P.equalityMultipliers lambda i * P.equalityConstraint i x) := by
    intro i
    rcases P.equalityConstraint_affineOn i with ⟨a, ha⟩
    have hscaled_affine_raw :
        ConvexOn ℝ P.constraintSet ((P.equalityMultipliers lambda i) • a) := by
      refine ⟨P.convex_constraintSet, ?_⟩
      intro x hx y hy α β hα hβ hαβ
      exact
        le_of_eq
          (Convex.combo_affine_apply
            (x := x) (y := y) (a := α) (b := β)
            (f := (P.equalityMultipliers lambda i) • a) hαβ)
    have hscaled_affine :
        ConvexOn ℝ P.constraintSet (fun x => P.equalityMultipliers lambda i * a x) := by
      simpa [smul_eq_mul] using hscaled_affine_raw
    refine hscaled_affine.congr ?_
    intro x hx
    simp [ha hx]
  have hequality_sum :
      ConvexOn ℝ P.constraintSet
        (fun x => ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x) := by
    classical
    have hs :
        ∀ s : Finset (Fin (m - r)),
          ConvexOn ℝ P.constraintSet
            (fun x => Finset.sum s (fun i => P.equalityMultipliers lambda i * P.equalityConstraint i x)) := by
      intro s
      induction s using Finset.induction with
      | empty =>
          simpa using (convexOn_const (s := P.constraintSet) (c := (0 : ℝ)) P.convex_constraintSet)
      | @insert i s hi hs =>
          simpa [Finset.sum_insert hi] using ConvexOn.add (hequality_term i) hs
    simpa using hs Finset.univ
  -- Adding the objective, the weighted inequality sum, and the weighted equality sum
  -- reconstructs the full Kuhn--Tucker objective.
  have hconstraint_correction :
      ConvexOn ℝ P.constraintSet
        (fun x =>
          (∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x) +
            ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x) :=
    ConvexOn.add hineq_sum hequality_sum
  have hall :
      ConvexOn ℝ P.constraintSet
        (fun x =>
          P.objective x +
            ((∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x) +
              ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x)) :=
    ConvexOn.add P.objective_convexOn hconstraint_correction
  -- The definition is the same sum with left-associated addition.
  convert hall using 1
  funext x
  unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
  ring_nf

/-- Helper for Corollary 6.28.1: if the ambient constraint set is closed, then the
indicator-extended Kuhn--Tucker objective is a closed convex function on `ℝ^n`. -/
lemma helperForCorollary_6_28_1_closedExtendedKuhnTuckerObjective_of_closedConstraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i)
    (hobjective_closed : LowerSemicontinuous P.objective)
    (hinequality_closed : ∀ i : Fin r, LowerSemicontinuous (P.inequalityConstraint i))
    (hconstraint_closed : IsClosed P.constraintSet) :
    ClosedConvexFunction (P.extendedKuhnTuckerObjective lambda) := by
  classical
  choose a ha using P.equalityConstraint_affineOn
  let equalityBranch : (Fin n → ℝ) → ℝ :=
    fun x => ∑ i : Fin (m - r), P.equalityMultipliers lambda i * a i x
  let finiteBranch : (Fin n → ℝ) → ℝ :=
    fun x =>
      P.objective x +
        (∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x) +
        equalityBranch x
  -- Convexity is the same `if-top` packaging used for properness of the extension.
  have hkuhn_conv :
      ConvexOn ℝ P.constraintSet (P.kuhnTuckerObjective lambda) :=
    helperForCorollary_6_28_1_kuhnTuckerObjective_convexOn_of_multiplier_nonneg
      P lambda hlambda_nonneg
  have hextended_conv :
      ConvexFunction (P.extendedKuhnTuckerObjective lambda) := by
    simpa [ConvexFunction, BookOrdinaryConvexProgram.extendedKuhnTuckerObjective] using
      (convexFunctionOn_univ_if_top (C := P.constraintSet) (g := P.kuhnTuckerObjective lambda)
        hkuhn_conv)
  -- The weighted inequality terms remain lower semicontinuous because their coefficients are
  -- nonnegative.
  have hineq_term_lsc :
      ∀ i : Fin r,
        LowerSemicontinuous
          (fun x => P.inequalityMultipliers lambda i * P.inequalityConstraint i x) := by
    intro i
    let scale : ℝ → ℝ := fun t => P.inequalityMultipliers lambda i * t
    have hscale_cont : Continuous scale := by
      dsimp [scale]
      continuity
    have hscale_mon : Monotone scale := by
      intro s t hst
      dsimp [scale]
      exact mul_le_mul_of_nonneg_left hst (hlambda_nonneg i)
    simpa [scale] using
      hscale_cont.comp_lowerSemicontinuous (hinequality_closed i) hscale_mon
  have hineq_sum_lsc :
      LowerSemicontinuous
        (fun x => ∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x) := by
    exact lowerSemicontinuous_sum fun i _hi => hineq_term_lsc i
  -- On the ambient set `C`, the equality constraints agree with affine maps, so their weighted
  -- sum is continuous after replacing them by those affine representatives.
  have hequality_cont : Continuous equalityBranch := by
    dsimp [equalityBranch]
    refine continuous_finset_sum _ ?_
    intro i _hi
    exact (continuous_const.mul (AffineMap.continuous_of_finiteDimensional (a i)))
  have hfiniteBranch_lsc : LowerSemicontinuous finiteBranch := by
    dsimp [finiteBranch]
    exact hobjective_closed.add hineq_sum_lsc |>.add hequality_cont.lowerSemicontinuous
  have hfiniteBranch_ereal_lsc :
      LowerSemicontinuous (fun x : Fin n → ℝ => ((finiteBranch x : ℝ) : EReal)) :=
    lowerSemicontinuous_coe_real_toEReal (h := finiteBranch) hfiniteBranch_lsc
  -- Closed sublevels of the real-valued branch become closed sublevels of the extension after
  -- intersecting with the closed ambient constraint set.
  have hextended_lsc : LowerSemicontinuous (P.extendedKuhnTuckerObjective lambda) := by
    refine (lowerSemicontinuous_iff_closed_sublevel
      (f := P.extendedKuhnTuckerObjective lambda)).2 ?_
    intro α
    have hsublevel_eq :
        {x : Fin n → ℝ | P.extendedKuhnTuckerObjective lambda x ≤ (α : EReal)} =
          P.constraintSet ∩ {x : Fin n → ℝ | ((finiteBranch x : ℝ) : EReal) ≤ (α : EReal)} := by
      ext x
      by_cases hx : x ∈ P.constraintSet
      · have heqBranch :
            equalityBranch x =
              ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x := by
          dsimp [equalityBranch]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [ha i hx]
        have hfinite_eq :
            finiteBranch x = P.kuhnTuckerObjective lambda x := by
          dsimp [finiteBranch]
          simp [BookOrdinaryConvexProgram.kuhnTuckerObjective, heqBranch]
        simp [BookOrdinaryConvexProgram.extendedKuhnTuckerObjective, hx, hfinite_eq]
      · simp [BookOrdinaryConvexProgram.extendedKuhnTuckerObjective, hx]
    have hfinite_closed :
        IsClosed {x : Fin n → ℝ | ((finiteBranch x : ℝ) : EReal) ≤ (α : EReal)} := by
      simpa using
        (lowerSemicontinuous_iff_closed_sublevel
          (f := fun x : Fin n → ℝ => ((finiteBranch x : ℝ) : EReal))).1
          hfiniteBranch_ereal_lsc α
    rw [hsublevel_eq]
    exact hconstraint_closed.inter hfinite_closed
  exact ⟨hextended_conv, hextended_lsc⟩

/-- Helper for Corollary 6.28.1: once the ambient constraint set is known to be nonempty, the
indicator-extended Kuhn--Tucker objective is already a proper convex function on `ℝ^n`. -/
lemma helperForCorollary_6_28_1_properExtendedKuhnTuckerObjective_of_multiplier_nonneg
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i)
    (hconstraint_nonempty : P.constraintSet.Nonempty) :
    ProperConvexFunctionOn
      (Set.univ : Set (Fin n → ℝ))
      (P.extendedKuhnTuckerObjective lambda) := by
  -- First package convexity of the finite branch on the ambient set `C = P.constraintSet`.
  have hkuhn_conv :
      ConvexOn ℝ P.constraintSet (P.kuhnTuckerObjective lambda) :=
    helperForCorollary_6_28_1_kuhnTuckerObjective_convexOn_of_multiplier_nonneg
      P lambda hlambda_nonneg
  have hextended_conv :
      ConvexFunctionOn
        (Set.univ : Set (Fin n → ℝ))
        (P.extendedKuhnTuckerObjective lambda) := by
    simpa [BookOrdinaryConvexProgram.extendedKuhnTuckerObjective] using
      (convexFunctionOn_univ_if_top (C := P.constraintSet) (g := P.kuhnTuckerObjective lambda)
        hkuhn_conv)
  rcases hconstraint_nonempty with ⟨x0, hx0C⟩
  -- A point of `constraintSet` gives a finite epigraph witness for the extension.
  have hnonempty_epigraph :
      Set.Nonempty
        (epigraph
          (Set.univ : Set (Fin n → ℝ))
          (P.extendedKuhnTuckerObjective lambda)) := by
    refine ⟨(x0, P.kuhnTuckerObjective lambda x0), ?_⟩
    refine (mem_epigraph_univ_iff (f := P.extendedKuhnTuckerObjective lambda)).2 ?_
    simp [BookOrdinaryConvexProgram.extendedKuhnTuckerObjective, hx0C]
  -- The extension takes only finite real values or `⊤`, so it never reaches `⊥`.
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)),
        P.extendedKuhnTuckerObjective lambda x ≠ (⊥ : EReal) := by
    intro x _hx
    by_cases hxC : x ∈ P.constraintSet
    · simp [BookOrdinaryConvexProgram.extendedKuhnTuckerObjective, hxC]
    · simp [BookOrdinaryConvexProgram.extendedKuhnTuckerObjective, hxC]
  exact ⟨hextended_conv, hnonempty_epigraph, hnotbot⟩

/-- Helper for Corollary 6.28.1: once the ambient constraint set is closed, the existing
closed/proper bridge proves that the unique minimizer of the indicator-extended Kuhn--Tucker
objective is the unique optimal solution of the program. -/
lemma helperForCorollary_6_28_1_uniqueOptimalSolution_of_closedConstraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hobjective_closed : LowerSemicontinuous P.objective)
    (hinequality_closed : ∀ i : Fin r, LowerSemicontinuous (P.inequalityConstraint i))
    (hequality_closed : ∀ i : Fin (m - r), LowerSemicontinuous (P.equalityConstraint i))
    (hconstraint_closed : IsClosed P.constraintSet)
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    P.IsOptimalSolution xbar ∧ ∀ y, P.IsOptimalSolution y → y = xbar := by
  rcases hKT with ⟨hlambda_nonneg, v, hv, hopt⟩
  have hKT' : P.IsKuhnTuckerVector lambda := ⟨hlambda_nonneg, v, hv, hopt⟩
  -- The finite Kuhn--Tucker infimum still supplies a point of `constraintSet`.
  have hconstraint_nonempty : P.constraintSet.Nonempty :=
    helperForCorollary_6_28_1_constraintSet_nonempty P lambda hKT'
  -- Closedness of `constraintSet` upgrades the extension to a closed convex function.
  have hclosedExtended :
      ClosedConvexFunction (P.extendedKuhnTuckerObjective lambda) :=
    helperForCorollary_6_28_1_closedExtendedKuhnTuckerObjective_of_closedConstraintSet
      P lambda hlambda_nonneg hobjective_closed hinequality_closed hconstraint_closed
  -- Nonemptiness of `constraintSet` gives the properness input for the Section 27 theorem.
  have hproperExtended :
      ProperConvexFunctionOn
        (Set.univ : Set (Fin n → ℝ))
        (P.extendedKuhnTuckerObjective lambda) :=
    helperForCorollary_6_28_1_properExtendedKuhnTuckerObjective_of_multiplier_nonneg
      P lambda hlambda_nonneg hconstraint_nonempty
  -- The closed/proper bridge converts the unique minimizer into an optimal solution.
  have hoptimal :
      P.IsOptimalSolution xbar :=
    helperForCorollary_6_28_1_isOptimalSolution_of_closedProperExtendedObjective
      P lambda xbar hKT' hobjective_closed hinequality_closed hequality_closed
      hclosedExtended hproperExtended hxbar_min hunique
  -- Theorem 6.28.1 already turns any other optimal solution into the same minimizer `xbar`.
  have hoptimal_unique :
      ∀ y, P.IsOptimalSolution y → y = xbar :=
    helperForCorollary_6_28_1_optimalSolution_eq_xbar P lambda xbar hKT' hunique
  exact ⟨hoptimal, hoptimal_unique⟩

/-- Helper for Corollary 6.28.1: once the ambient constraint set is closed, the unique minimizer
`xbar` supplied by the corollary is already an explicit optimal-solution witness. -/
lemma helperForCorollary_6_28_1_existsOptimalSolution_of_closedConstraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hobjective_closed : LowerSemicontinuous P.objective)
    (hinequality_closed : ∀ i : Fin r, LowerSemicontinuous (P.inequalityConstraint i))
    (hequality_closed : ∀ i : Fin (m - r), LowerSemicontinuous (P.equalityConstraint i))
    (hconstraint_closed : IsClosed P.constraintSet)
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    ∃ y, P.IsOptimalSolution y := by
  -- The closed-constraint-set bridge already proves that the distinguished minimizer is optimal.
  refine ⟨xbar, ?_⟩
  exact
    (helperForCorollary_6_28_1_uniqueOptimalSolution_of_closedConstraintSet
      P lambda xbar hKT hobjective_closed hinequality_closed hequality_closed
      hconstraint_closed hxbar_min hunique).1

/-- Helper for Corollary 6.28.1: once some optimal solution exists, Theorem 6.28.1 already
identifies that witness with the unique global minimizer `xbar`, so `xbar` is optimal. -/
lemma helperForCorollary_6_28_1_isOptimalSolution_of_existsOptimalSolution
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    (∃ y, P.IsOptimalSolution y) →
      P.IsOptimalSolution xbar := by
  intro hexistsOptimal
  rcases hexistsOptimal with ⟨y0, hy0Optimal⟩
  -- Theorem 6.28.1 identifies any optimal solution with the unique minimizer `xbar`.
  have hy0_eq_xbar : y0 = xbar :=
    helperForCorollary_6_28_1_optimalSolution_eq_xbar P lambda xbar hKT hunique y0 hy0Optimal
  -- Rewriting the witness along that equality transfers optimality to `xbar`.
  simpa [hy0_eq_xbar] using hy0Optimal

/-- Helper for Corollary 6.28.1: once some optimal solution of `(P)` is known to exist, Theorem
6.28.1 and uniqueness of the global minimizer already force that optimal solution to equal `xbar`,
so `xbar` is itself the unique optimal solution. -/
lemma helperForCorollary_6_28_1_uniqueOptimalSolution_of_existsOptimalSolution
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    (∃ y, P.IsOptimalSolution y) →
      P.IsOptimalSolution xbar ∧ ∀ y, P.IsOptimalSolution y → y = xbar := by
  intro hexistsOptimal
  have hxbarOptimal : P.IsOptimalSolution xbar :=
    helperForCorollary_6_28_1_isOptimalSolution_of_existsOptimalSolution
      P lambda xbar hKT hunique hexistsOptimal
  have hoptimal_unique :
      ∀ y, P.IsOptimalSolution y → y = xbar :=
    helperForCorollary_6_28_1_optimalSolution_eq_xbar P lambda xbar hKT hunique
  exact ⟨hxbarOptimal, hoptimal_unique⟩

/-- Helper for Corollary 6.28.1: a feasible point whose objective value realizes
`P.optimalValue` is already an optimal solution. -/
lemma helperForCorollary_6_28_1_isOptimalSolution_of_feasible_objective_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {y : Fin n → ℝ}
    (hyFeasible : y ∈ P.feasibleSet)
    (hyValue : ((P.objective y : ℝ) : EReal) = P.optimalValue) :
    P.IsOptimalSolution y := by
  refine ⟨hyFeasible, ?_⟩
  intro z hzFeasible
  -- The optimal value is the infimum over all feasible objective values, so every feasible point
  -- has objective at least `P.optimalValue`.
  have hzLower :
      P.optimalValue ≤ ((P.objective z : ℝ) : EReal) := by
    rw [BookOrdinaryConvexProgram.optimalValue]
    exact sInf_le ⟨z, hzFeasible, rfl⟩
  have hy_le_hz :
      ((P.objective y : ℝ) : EReal) ≤ ((P.objective z : ℝ) : EReal) := by
    calc
      ((P.objective y : ℝ) : EReal) = P.optimalValue := hyValue
      _ ≤ ((P.objective z : ℝ) : EReal) := hzLower
  -- Comparing two finite real values in `EReal` gives the desired real inequality.
  exact EReal.coe_le_coe_iff.1 hy_le_hz

/-- Helper for Corollary 6.28.1: every optimal solution attains the primal optimal value. -/
lemma helperForCorollary_6_28_1_objective_eq_optimalValue_of_isOptimalSolution
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {y : Fin n → ℝ}
    (hyOptimal : P.IsOptimalSolution y) :
    ((P.objective y : ℝ) : EReal) = P.optimalValue := by
  rcases hyOptimal with ⟨hyFeasible, hyMin⟩
  -- Feasibility gives one side of the infimum comparison immediately.
  have hoptimal_le :
      P.optimalValue ≤ ((P.objective y : ℝ) : EReal) := by
    rw [BookOrdinaryConvexProgram.optimalValue]
    exact sInf_le ⟨y, hyFeasible, rfl⟩
  -- Optimality makes `P.objective y` a lower bound for every feasible objective value.
  have hobjective_le :
      ((P.objective y : ℝ) : EReal) ≤ P.optimalValue := by
    rw [BookOrdinaryConvexProgram.optimalValue]
    refine le_sInf ?_
    rintro _ ⟨z, hzFeasible, rfl⟩
    exact EReal.coe_le_coe_iff.2 (hyMin z hzFeasible)
  exact le_antisymm hobjective_le hoptimal_le

/-- Helper for Corollary 6.28.1: an existing optimal solution can be repackaged as a feasible
point whose objective realizes `P.optimalValue`. -/
lemma helperForCorollary_6_28_1_exists_feasible_objective_eq_optimalValue_of_existsOptimalSolution
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    (∃ y, P.IsOptimalSolution y) →
      ∃ y, y ∈ P.feasibleSet ∧ ((P.objective y : ℝ) : EReal) = P.optimalValue := by
  intro hexistsOptimal
  rcases hexistsOptimal with ⟨y, hyOptimal⟩
  -- Unpack the optimal witness into feasibility and exact attainment of the infimum.
  refine ⟨y, hyOptimal.1, ?_⟩
  exact helperForCorollary_6_28_1_objective_eq_optimalValue_of_isOptimalSolution P hyOptimal

/-- Helper for Corollary 6.28.1: primal optimal-solution existence is equivalent to the
attainment of `P.optimalValue` by some feasible point. -/
lemma helperForCorollary_6_28_1_existsOptimalSolution_iff_exists_feasible_objective_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    (∃ y, P.IsOptimalSolution y) ↔
      ∃ y, y ∈ P.feasibleSet ∧ ((P.objective y : ℝ) : EReal) = P.optimalValue := by
  constructor
  · intro hexistsOptimal
    -- Any optimal witness already realizes the primal infimum.
    exact
      helperForCorollary_6_28_1_exists_feasible_objective_eq_optimalValue_of_existsOptimalSolution
        P hexistsOptimal
  · intro hexistsValueAttainer
    rcases hexistsValueAttainer with ⟨y, hyFeasible, hyValue⟩
    -- Conversely, a feasible point at the infimum is already optimal.
    exact ⟨y,
      helperForCorollary_6_28_1_isOptimalSolution_of_feasible_objective_eq_optimalValue
        P hyFeasible hyValue⟩

/-- Helper for Corollary 6.28.1: whenever the closed-constraint-set route is available, the
distinguished minimizer `xbar` yields the feasible primal value-attainer needed by the local
endgame. -/
lemma helperForCorollary_6_28_1_exists_feasible_objective_eq_optimalValue_of_closedConstraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hobjective_closed : LowerSemicontinuous P.objective)
    (hinequality_closed : ∀ i : Fin r, LowerSemicontinuous (P.inequalityConstraint i))
    (hequality_closed : ∀ i : Fin (m - r), LowerSemicontinuous (P.equalityConstraint i))
    (hconstraint_closed : IsClosed P.constraintSet)
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    ∃ y, y ∈ P.feasibleSet ∧ ((P.objective y : ℝ) : EReal) = P.optimalValue := by
  have hexistsOptimal : ∃ y, P.IsOptimalSolution y :=
    helperForCorollary_6_28_1_existsOptimalSolution_of_closedConstraintSet
      P lambda xbar hKT hobjective_closed hinequality_closed hequality_closed
      hconstraint_closed hxbar_min hunique
  -- The closed-constraint-set bridge supplies exactly the primal attainment statement used later.
  exact
    (helperForCorollary_6_28_1_existsOptimalSolution_iff_exists_feasible_objective_eq_optimalValue
      P).1 hexistsOptimal

/-- Helper for Corollary 6.28.1: once a feasible point attains `P.optimalValue`, the earlier
optimal-witness helper identifies that point with the unique minimizer `xbar`. -/
lemma helperForCorollary_6_28_1_uniqueOptimalSolution_of_exists_feasible_objective_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    (∃ y, y ∈ P.feasibleSet ∧ ((P.objective y : ℝ) : EReal) = P.optimalValue) →
      P.IsOptimalSolution xbar ∧ ∀ y, P.IsOptimalSolution y → y = xbar := by
  intro hexistsValueAttainer
  rcases hexistsValueAttainer with ⟨y0, hy0Feasible, hy0Value⟩
  -- Convert the attained primal value into the optimal witness required by the uniqueness helper.
  have hy0Optimal : P.IsOptimalSolution y0 :=
    helperForCorollary_6_28_1_isOptimalSolution_of_feasible_objective_eq_optimalValue
      P hy0Feasible hy0Value
  -- The earlier helper now finishes exactly as before.
  exact
    helperForCorollary_6_28_1_uniqueOptimalSolution_of_existsOptimalSolution
      P lambda xbar hKT hunique ⟨y0, hy0Optimal⟩

/-- Helper for Corollary 6.28.1: once some feasible point realizes `P.optimalValue`, the unique
global minimizer `xbar` itself becomes a feasible value-attainer. -/
lemma helperForCorollary_6_28_1_xbar_feasible_objective_eq_optimalValue_of_exists_feasible_objective_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    (∃ y, y ∈ P.feasibleSet ∧ ((P.objective y : ℝ) : EReal) = P.optimalValue) →
      xbar ∈ P.feasibleSet ∧ ((P.objective xbar : ℝ) : EReal) = P.optimalValue := by
  intro hexistsValueAttainer
  -- The earlier uniqueness helper first upgrades `xbar` to an optimal solution.
  have hxbarOptimal : P.IsOptimalSolution xbar :=
    (helperForCorollary_6_28_1_uniqueOptimalSolution_of_exists_feasible_objective_eq_optimalValue
      P lambda xbar hKT hunique hexistsValueAttainer).1
  constructor
  · exact hxbarOptimal.1
  -- Every optimal solution attains the primal optimal value, so `xbar` does as well.
  · exact helperForCorollary_6_28_1_objective_eq_optimalValue_of_isOptimalSolution P hxbarOptimal

/-- Helper for Corollary 6.28.1: under the unique-minimizer hypothesis, the corollary conclusion
is equivalent to the existence of a feasible point attaining `P.optimalValue`. -/
lemma helperForCorollary_6_28_1_uniqueOptimalSolution_iff_exists_feasible_objective_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    (P.IsOptimalSolution xbar ∧ ∀ y, P.IsOptimalSolution y → y = xbar) ↔
      ∃ y, y ∈ P.feasibleSet ∧ ((P.objective y : ℝ) : EReal) = P.optimalValue := by
  constructor
  · intro hxbarUnique
    -- The claimed unique optimal solution already supplies the required primal value-attainer.
    exact
      helperForCorollary_6_28_1_exists_feasible_objective_eq_optimalValue_of_existsOptimalSolution
        P ⟨xbar, hxbarUnique.1⟩
  · intro hexistsValueAttainer
    -- Conversely, an attained optimal value feeds directly into the existing uniqueness endgame.
    exact
      helperForCorollary_6_28_1_uniqueOptimalSolution_of_exists_feasible_objective_eq_optimalValue
        P lambda xbar hKT hunique hexistsValueAttainer

/-- Helper for Corollary 6.28.1: the global minimizer `xbar` already lies in the ambient
constraint set and attains the common extended Kuhn--Tucker value `P.optimalValue`. -/
lemma helperForCorollary_6_28_1_xbar_mem_constraintSet_and_extendedObjective_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y) :
    xbar ∈ P.constraintSet ∧
      P.extendedKuhnTuckerObjective lambda xbar = P.optimalValue := by
  rcases hKT with ⟨hlambda_nonneg, v, hv, hopt⟩
  have hKT' : P.IsKuhnTuckerVector lambda := ⟨hlambda_nonneg, v, hv, hopt⟩
  -- Global minimality and the finite Kuhn--Tucker value force `xbar` into `constraintSet`.
  have hxbarC : xbar ∈ P.constraintSet :=
    helperForCorollary_6_28_1_xbar_mem_constraintSet P lambda xbar hKT' hxbar_min
  have hconstraint_nonempty : P.constraintSet.Nonempty :=
    helperForCorollary_6_28_1_constraintSet_nonempty P lambda hKT'
  -- Once `xbar` is in `constraintSet`, its finite Kuhn--Tucker value is exactly `v`.
  have hxbar_kuhn_eq_v :
      ((P.kuhnTuckerObjective lambda xbar : ℝ) : EReal) = (v : EReal) :=
    helperForCorollary_6_28_1_xbar_kuhnTuckerObjective_eq_kuhnTuckerValue
      P lambda xbar hv hxbarC hxbar_min hconstraint_nonempty
  refine ⟨hxbarC, ?_⟩
  -- Rewriting the extended objective on `constraintSet` identifies its value with `P.optimalValue`.
  calc
    P.extendedKuhnTuckerObjective lambda xbar =
        ((P.kuhnTuckerObjective lambda xbar : ℝ) : EReal) :=
      helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda hxbarC
    _ = (v : EReal) := hxbar_kuhn_eq_v
    _ = P.optimalValue := hopt.symm

/-- Helper for Corollary 6.28.1: once a near-optimal feasible sequence converges to a point
already known to lie in the ambient constraint set, the closed-data hypotheses force that limit
point to be a feasible point attaining `P.optimalValue`. -/
lemma helperForCorollary_6_28_1_feasible_objective_eq_optimalValue_of_tendsto_nearOptimal_feasibleSequence
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (xbar : Fin n → ℝ) {v : ℝ}
    (hobjective_closed : LowerSemicontinuous P.objective)
    (hinequality_closed : ∀ i : Fin r, LowerSemicontinuous (P.inequalityConstraint i))
    (hxbarC : xbar ∈ P.constraintSet)
    (hopt : P.optimalValue = (v : EReal))
    (xSeq : ℕ → Fin n → ℝ)
    (hxSeqFeas : ∀ k, xSeq k ∈ P.feasibleSet)
    (hxSeqNear : ∀ k, P.objective (xSeq k) ≤ v + 1 / ((k : ℝ) + 1))
    (hxSeq_tendsto : Filter.Tendsto xSeq Filter.atTop (nhds xbar)) :
    xbar ∈ P.feasibleSet ∧ ((P.objective xbar : ℝ) : EReal) = P.optimalValue := by
  -- Convergence preserves the closed inequality sublevel sets.
  have hineq_feasible :
      ∀ i : Fin r, P.inequalityConstraint i xbar ≤ 0 := by
    intro i
    have hclosedSublevel :
        IsClosed {x : Fin n → ℝ | P.inequalityConstraint i x ≤ 0} := by
      have hlsc_ereal :
          LowerSemicontinuous
            (fun x : Fin n → ℝ => ((P.inequalityConstraint i x : ℝ) : EReal)) :=
        lowerSemicontinuous_coe_real_toEReal (h := fun x : Fin n → ℝ =>
          P.inequalityConstraint i x) (hinequality_closed i)
      simpa using
        (lowerSemicontinuous_iff_closed_sublevel
          (f := fun x : Fin n → ℝ => ((P.inequalityConstraint i x : ℝ) : EReal))).1
          hlsc_ereal 0
    have hmem_eventually :
        ∀ᶠ k : ℕ in Filter.atTop,
          xSeq k ∈ {x : Fin n → ℝ | P.inequalityConstraint i x ≤ 0} := by
      exact Filter.Eventually.of_forall fun k => (hxSeqFeas k).2.1 i
    have hxbar_mem_sublevel :
        xbar ∈ {x : Fin n → ℝ | P.inequalityConstraint i x ≤ 0} :=
      IsClosed.mem_of_tendsto hclosedSublevel hxSeq_tendsto hmem_eventually
    exact hxbar_mem_sublevel
  -- Affine representatives of the equality constraints pass exact vanishing to the limit.
  have heq_feasible :
      ∀ i : Fin (m - r), P.equalityConstraint i xbar = 0 := by
    intro i
    rcases P.equalityConstraint_affineOn i with ⟨a, ha⟩
    have ha_tendsto :
        Filter.Tendsto (fun k : ℕ => a (xSeq k)) Filter.atTop (nhds (a xbar)) := by
      exact (AffineMap.continuous_of_finiteDimensional a).continuousAt.tendsto.comp hxSeq_tendsto
    have ha_zero_tendsto :
        Filter.Tendsto (fun k : ℕ => a (xSeq k)) Filter.atTop (nhds (0 : ℝ)) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      refine Filter.Eventually.of_forall ?_
      intro k
      have hxkEq : P.equalityConstraint i (xSeq k) = 0 := (hxSeqFeas k).2.2 i
      simpa [ha (hxSeqFeas k).1] using hxkEq.symm
    have haxbar_zero : a xbar = 0 := tendsto_nhds_unique ha_tendsto ha_zero_tendsto
    simpa [ha hxbarC] using haxbar_zero
  have hxbarFeasible : xbar ∈ P.feasibleSet := by
    -- Ambient membership is known separately, and the limit argument supplies the constraint data.
    exact ⟨hxbarC, hineq_feasible, heq_feasible⟩
  -- The near-optimal objective envelope passes to the limit by lower semicontinuity of `f₀`.
  have hxbar_objective_le_v : P.objective xbar ≤ v := by
    by_contra hnot_le
    have hv_lt_obj : v < P.objective xbar := lt_of_not_ge hnot_le
    let ε : ℝ := (P.objective xbar - v) / 2
    have hεpos : 0 < ε := by
      dsimp [ε]
      linarith
    have honeDiv_eventually :
        ∀ᶠ k : ℕ in Filter.atTop, 1 / ((k : ℝ) + 1) < ε := by
      have honeDiv_tendsto :
          Filter.Tendsto
            (fun k : ℕ => 1 / ((k : ℝ) + 1))
            Filter.atTop
            (nhds (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact (tendsto_order.1 honeDiv_tendsto).2 ε hεpos
    have hclosedSublevel :
        IsClosed
          {x : Fin n → ℝ | ((P.objective x : ℝ) : EReal) ≤ (((v + ε : ℝ) : ℝ) : EReal)} := by
      have hobjective_closed_ereal :
          LowerSemicontinuous (fun x : Fin n → ℝ => ((P.objective x : ℝ) : EReal)) :=
        lowerSemicontinuous_coe_real_toEReal (h := fun x : Fin n → ℝ => P.objective x)
          hobjective_closed
      exact
        (lowerSemicontinuous_iff_closed_sublevel
          (f := fun x : Fin n → ℝ => ((P.objective x : ℝ) : EReal))).1
          hobjective_closed_ereal (v + ε)
    have hmem_eventually :
        ∀ᶠ k : ℕ in Filter.atTop,
          xSeq k ∈
            {x : Fin n → ℝ | ((P.objective x : ℝ) : EReal) ≤ (((v + ε : ℝ) : ℝ) : EReal)} := by
      filter_upwards [honeDiv_eventually] with k hk
      exact EReal.coe_le_coe_iff.2 <| by
        have hxkNear' := hxSeqNear k
        linarith
    have hxbar_mem_sublevel :
        xbar ∈
          {x : Fin n → ℝ | ((P.objective x : ℝ) : EReal) ≤ (((v + ε : ℝ) : ℝ) : EReal)} :=
      IsClosed.mem_of_tendsto hclosedSublevel hxSeq_tendsto hmem_eventually
    have hxbar_obj_le_vε : P.objective xbar ≤ v + ε :=
      EReal.coe_le_coe_iff.1 hxbar_mem_sublevel
    have hvε_lt_obj : v + ε < P.objective xbar := by
      dsimp [ε]
      linarith
    exact (not_le_of_gt hvε_lt_obj) hxbar_obj_le_vε
  have hobj_le_opt :
      ((P.objective xbar : ℝ) : EReal) ≤ P.optimalValue := by
    calc
      ((P.objective xbar : ℝ) : EReal) ≤ (v : EReal) := EReal.coe_le_coe_iff.2 hxbar_objective_le_v
      _ = P.optimalValue := hopt.symm
  have hopt_le_obj :
      P.optimalValue ≤ ((P.objective xbar : ℝ) : EReal) := by
    rw [BookOrdinaryConvexProgram.optimalValue]
    exact sInf_le ⟨xbar, hxbarFeasible, rfl⟩
  exact ⟨hxbarFeasible, le_antisymm hobj_le_opt hopt_le_obj⟩

/-- Helper for Corollary 6.28.1: once `xbar` itself is already known to be feasible and to
realize `P.optimalValue`, the required convergent near-optimal feasible sequence is the constant
sequence at `xbar`. -/
lemma helperForCorollary_6_28_1_exists_convergentNearOptimal_feasibleSequence_of_xbar_feasible_objective_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (xbar : Fin n → ℝ) {v : ℝ}
    (hopt : P.optimalValue = (v : EReal))
    (hxbarFeasible : xbar ∈ P.feasibleSet)
    (hxbarValue : ((P.objective xbar : ℝ) : EReal) = P.optimalValue) :
    ∃ xSeq : ℕ → Fin n → ℝ,
      (∀ k, xSeq k ∈ P.feasibleSet) ∧
      (∀ k, P.objective (xSeq k) ≤ v + 1 / ((k : ℝ) + 1)) ∧
      Filter.Tendsto xSeq Filter.atTop (nhds xbar) := by
  have hxbarObjectiveEqV :
      P.objective xbar = v := by
    -- The attained optimal value is finite, so the `EReal` equality descends to `ℝ`.
    apply EReal.coe_eq_coe_iff.1
    calc
      ((P.objective xbar : ℝ) : EReal) = P.optimalValue := hxbarValue
      _ = (v : EReal) := hopt
  refine ⟨fun _ => xbar, ?_, ?_, ?_⟩
  · -- The constant sequence stays feasible because every term is exactly `xbar`.
    intro k
    simpa using hxbarFeasible
  · -- The explicit `1 / (k + 1)` margin is positive, so equality with `v` is enough.
    intro k
    have hmargin_nonneg : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
    calc
      P.objective xbar = v := hxbarObjectiveEqV
      _ ≤ v + 1 / ((k : ℝ) + 1) := by
        exact le_add_of_nonneg_right hmargin_nonneg
  · -- A constant sequence converges to its constant value.
    exact tendsto_const_nhds

/-- Helper for Corollary 6.28.1: under the closed-data limit argument already proved above,
asking for a convergent near-optimal feasible sequence is equivalent to asking directly that
`xbar` be feasible and attain `P.optimalValue`. -/
lemma helperForCorollary_6_28_1_exists_convergentNearOptimal_feasibleSequence_iff_xbar_feasible_objective_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (xbar : Fin n → ℝ) {v : ℝ}
    (hobjective_closed : LowerSemicontinuous P.objective)
    (hinequality_closed : ∀ i : Fin r, LowerSemicontinuous (P.inequalityConstraint i))
    (hxbarC : xbar ∈ P.constraintSet)
    (hopt : P.optimalValue = (v : EReal)) :
    (∃ xSeq : ℕ → Fin n → ℝ,
        (∀ k, xSeq k ∈ P.feasibleSet) ∧
        (∀ k, P.objective (xSeq k) ≤ v + 1 / ((k : ℝ) + 1)) ∧
        Filter.Tendsto xSeq Filter.atTop (nhds xbar)) ↔
      xbar ∈ P.feasibleSet ∧ ((P.objective xbar : ℝ) : EReal) = P.optimalValue := by
  constructor
  · rintro ⟨xSeq, hxSeqFeas, hxSeqNear, hxSeq_tendsto⟩
    -- The already-proved closed-data limit argument reads feasibility and value attainment from
    -- any convergent near-optimal feasible sequence.
    exact
      helperForCorollary_6_28_1_feasible_objective_eq_optimalValue_of_tendsto_nearOptimal_feasibleSequence
        P xbar hobjective_closed hinequality_closed hxbarC hopt xSeq hxSeqFeas hxSeqNear
        hxSeq_tendsto
  · intro hxbarValueAttainer
    -- Conversely, once `xbar` itself attains the optimal value, the constant sequence suffices.
    exact
      helperForCorollary_6_28_1_exists_convergentNearOptimal_feasibleSequence_of_xbar_feasible_objective_eq_optimalValue
        P xbar hopt hxbarValueAttainer.1 hxbarValueAttainer.2

/-- Helper for Corollary 6.28.1: once the corollary conclusion itself is known, `xbar` is already
feasible and its objective value realizes `P.optimalValue`. -/
lemma helperForCorollary_6_28_1_xbar_feasible_objective_eq_optimalValue_of_uniqueOptimalSolution
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (xbar : Fin n → ℝ)
    (hxbarUnique : P.IsOptimalSolution xbar ∧ ∀ y, P.IsOptimalSolution y → y = xbar) :
    xbar ∈ P.feasibleSet ∧ ((P.objective xbar : ℝ) : EReal) = P.optimalValue := by
  -- The corollary conclusion already contains optimality of `xbar`.
  have hxbarOptimal : P.IsOptimalSolution xbar := hxbarUnique.1
  refine ⟨hxbarOptimal.1, ?_⟩
  -- The existing optimal-value lemma then reads off the realized primal value at `xbar`.
  exact helperForCorollary_6_28_1_objective_eq_optimalValue_of_isOptimalSolution P hxbarOptimal

/-- Helper for Corollary 6.28.1: if the corollary conclusion is already known, the constant
sequence at `xbar` is a convergent near-optimal feasible sequence. -/
lemma helperForCorollary_6_28_1_exists_convergentNearOptimal_feasibleSequence_of_uniqueOptimalSolution
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (xbar : Fin n → ℝ) {v : ℝ}
    (hopt : P.optimalValue = (v : EReal))
    (hxbarUnique : P.IsOptimalSolution xbar ∧ ∀ y, P.IsOptimalSolution y → y = xbar) :
    ∃ xSeq : ℕ → Fin n → ℝ,
      (∀ k, xSeq k ∈ P.feasibleSet) ∧
      (∀ k, P.objective (xSeq k) ≤ v + 1 / ((k : ℝ) + 1)) ∧
      Filter.Tendsto xSeq Filter.atTop (nhds xbar) := by
  have hxbarValueAttainer :
      xbar ∈ P.feasibleSet ∧ ((P.objective xbar : ℝ) : EReal) = P.optimalValue :=
    helperForCorollary_6_28_1_xbar_feasible_objective_eq_optimalValue_of_uniqueOptimalSolution
      P xbar hxbarUnique
  -- Once `xbar` is known to realize the optimal value, the earlier constant-sequence
  -- construction supplies the required convergent near-optimal feasible sequence.
  exact
    helperForCorollary_6_28_1_exists_convergentNearOptimal_feasibleSequence_of_xbar_feasible_objective_eq_optimalValue
      P xbar hopt hxbarValueAttainer.1 hxbarValueAttainer.2

/-- Helper for Corollary 6.28.1: the remaining closed-data bridge can be stated directly as
feasibility of `xbar` together with equality of its objective value and `P.optimalValue`. -/
lemma helperForCorollary_6_28_1_xbar_feasible_objective_eq_optimalValue_of_closedData
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hobjective_closed : LowerSemicontinuous P.objective)
    (hinequality_closed : ∀ i : Fin r, LowerSemicontinuous (P.inequalityConstraint i))
    (hequality_closed : ∀ i : Fin (m - r), LowerSemicontinuous (P.equalityConstraint i))
    (hconstraint_closed : IsClosed P.constraintSet)
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    xbar ∈ P.feasibleSet ∧ ((P.objective xbar : ℝ) : EReal) = P.optimalValue := by
  -- Route correction: in this formalization, "closed data" already includes
  -- `IsClosed P.constraintSet`, so the earlier closed-constraint-set corollary route applies
  -- directly instead of rebuilding the abandoned sequence-based bridge.
  have hxbarUnique :
      P.IsOptimalSolution xbar ∧ ∀ y, P.IsOptimalSolution y → y = xbar :=
    helperForCorollary_6_28_1_uniqueOptimalSolution_of_closedConstraintSet
      P lambda xbar hKT hobjective_closed hinequality_closed hequality_closed
      hconstraint_closed hxbar_min hunique
  -- Once `xbar` is known to be the unique optimal solution, feasibility and exact attainment of
  -- `P.optimalValue` follow from the previously established optimal-value identity.
  exact
    helperForCorollary_6_28_1_xbar_feasible_objective_eq_optimalValue_of_uniqueOptimalSolution
      P xbar hxbarUnique

/-- Helper for Corollary 6.28.1: once `xbar` itself is known to be feasible and to realize
`P.optimalValue`, the corollary conclusion follows from the existing optimality and uniqueness
bridges. -/
lemma helperForCorollary_6_28_1_uniqueOptimalSolution_of_xbar_feasible_objective_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar)
    (hxbarFeasible : xbar ∈ P.feasibleSet)
    (hxbarValue : ((P.objective xbar : ℝ) : EReal) = P.optimalValue) :
    P.IsOptimalSolution xbar ∧ ∀ y, P.IsOptimalSolution y → y = xbar := by
  -- First turn direct feasibility and value attainment into optimality of `xbar`.
  have hxbarOptimal : P.IsOptimalSolution xbar :=
    helperForCorollary_6_28_1_isOptimalSolution_of_feasible_objective_eq_optimalValue
      P hxbarFeasible hxbarValue
  -- Then the existing minimizer-set argument already identifies every optimal point with `xbar`.
  have hoptimal_unique :
      ∀ y, P.IsOptimalSolution y → y = xbar :=
    helperForCorollary_6_28_1_optimalSolution_eq_xbar P lambda xbar hKT hunique
  exact ⟨hxbarOptimal, hoptimal_unique⟩

/-- Helper for Corollary 6.28.1: the closed-data hypotheses already force the unique minimizer
`xbar` to be an optimal solution of the primal problem. -/
lemma helperForCorollary_6_28_1_isOptimalSolution_of_closedData
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hobjective_closed : LowerSemicontinuous P.objective)
    (hinequality_closed : ∀ i : Fin r, LowerSemicontinuous (P.inequalityConstraint i))
    (hequality_closed : ∀ i : Fin (m - r), LowerSemicontinuous (P.equalityConstraint i))
    (hconstraint_closed : IsClosed P.constraintSet)
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    P.IsOptimalSolution xbar := by
  -- The closed-data bridge first shows that `xbar` is feasible and that its objective value is
  -- exactly the primal optimal value.
  have hxbarValueAttainer :
      xbar ∈ P.feasibleSet ∧ ((P.objective xbar : ℝ) : EReal) = P.optimalValue :=
    helperForCorollary_6_28_1_xbar_feasible_objective_eq_optimalValue_of_closedData
      P lambda xbar hKT hobjective_closed hinequality_closed hequality_closed
      hconstraint_closed hxbar_min hunique
  -- A feasible point attaining `P.optimalValue` is already an optimal solution.
  exact
    helperForCorollary_6_28_1_isOptimalSolution_of_feasible_objective_eq_optimalValue
      P hxbarValueAttainer.1 hxbarValueAttainer.2


end Section28
end Chap06
