/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part1

section Chap06
section Section29

local notation "ConvexBifunction" => BundledConvexBifunction

/-- Lemma 6.29.5: Let `(P)` be an ordinary convex program and let `F` be its associated
bifunction. If the objective `f₀` and the inequality constraint functions
`f₁, …, f_r` are closed, while the remaining constraint functions are affine as in the
definition of an ordinary convex program, then the associated bifunction `F` is closed. -/
theorem ordinaryConvexProgramAssociatedBifunction_closed {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n)
    (hObjectiveClosed : ClosedConvexFunction P.objective)
    (hInequalityClosed :
      ∀ i : Fin m, (i : ℕ) < P.inequalityCount →
        ClosedConvexFunction (fun x => (P.constraint i x : EReal))) :
    IsClosedBifunction (ordinaryConvexProgramAssociatedBifunction P) := by
  classical
  let objectiveEpigraph :
      Set (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) :=
    {p | P.objective p.1.2 ≤ (p.2 : EReal)}
  let feasibleGraph :
      Set (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) :=
    {p | p.1.2 ∈ ordinaryConvexProgramConstraintSet P p.1.1}
  have hObjectiveEpigraphClosed : IsClosed objectiveEpigraph :=
    helperForLemma_6_29_5_objectiveEpigraph_closed P hObjectiveClosed
  have hFeasibleGraphEq :
      feasibleGraph =
        ⋂ i : Fin m,
          {p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ |
            if (i : ℕ) < P.inequalityCount then
              P.constraint i p.1.2 ≤ p.1.1 i
            else
              P.constraint i p.1.2 = p.1.1 i} := by
    -- Unfold the constraint set so feasibility becomes one closed condition for each index.
    ext p
    constructor
    · intro hp
      refine Set.mem_iInter.2 ?_
      intro i
      simpa [feasibleGraph, ordinaryConvexProgramConstraintSet] using hp i
    · intro hp
      intro i
      have hi :
          p ∈
            {p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ |
              if (i : ℕ) < P.inequalityCount then
                P.constraint i p.1.2 ≤ p.1.1 i
              else
                P.constraint i p.1.2 = p.1.1 i} :=
        Set.mem_iInter.1 hp i
      simpa [feasibleGraph, ordinaryConvexProgramConstraintSet] using hi
  have hFeasibleGraphClosed : IsClosed feasibleGraph := by
    rw [hFeasibleGraphEq]
    refine isClosed_iInter ?_
    intro i
    by_cases hi : (i : ℕ) < P.inequalityCount
    · -- Closed inequality constraints contribute closed epigraph slices.
      simpa [hi] using
        helperForLemma_6_29_5_inequalityConstraintSlice_closed P hInequalityClosed i hi
    · have hi' : P.inequalityCount ≤ (i : ℕ) := le_of_not_gt hi
      -- Closed equality constraints come from affine graphs.
      simpa [hi] using helperForLemma_6_29_5_equalityConstraintSlice_closed P i hi'
  have hEpigraphEq :
      {p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ |
          graphFunction (ordinaryConvexProgramAssociatedBifunction P) p.1 ≤ (p.2 : EReal)} =
        objectiveEpigraph ∩ feasibleGraph := by
    -- The associated epigraph is the intersection of the objective epigraph and feasibility graph.
    ext p
    simpa [objectiveEpigraph, feasibleGraph] using
      helperForLemma_6_29_5_mem_associatedEpigraph_iff P p
  -- Intersect the two closed pieces to conclude that the associated bifunction is closed.
  rw [IsClosedBifunction, hEpigraphEq]
  exact hObjectiveEpigraphClosed.inter hFeasibleGraphClosed

/-- Definition 6.29.13: For a convex bifunction `F`, the objective function `F₀` of the
generalized convex program associated with `F` is the convex section at zero perturbation,
defined by `F₀ x = F 0 x` for `x ∈ ℝ^n`. -/
abbrev generalizedConvexProgramObjective {m n : ℕ} (F : ConvexBifunction m n) :
    (Fin n → ℝ) → EReal :=
  F.1 0

-- Proof sketch: view `generalizedConvexProgramObjective F` as the `u = 0` section of the
-- convex bifunction `F`, then apply Proposition 6.29.1 to that fixed perturbation.
/-- The zero-perturbation objective extracted from a convex bifunction is a convex
extended-real-valued function on `ℝ^n`. -/
theorem generalizedConvexProgramObjective_convex {m n : ℕ} (F : ConvexBifunction m n) :
    ConvexFunction (generalizedConvexProgramObjective F) := by
  -- Prove convexity of the zero-perturbation epigraph directly from the section inequality.
  rw [ConvexFunction, ConvexFunctionOn]
  intro p hp q hq a b ha hb hab
  have hp' : generalizedConvexProgramObjective F p.1 ≤ (p.2 : EReal) := by
    simpa [epigraph, generalizedConvexProgramObjective] using hp.2
  have hq' : generalizedConvexProgramObjective F q.1 ≤ (q.2 : EReal) := by
    simpa [epigraph, generalizedConvexProgramObjective] using hq.2
  have hsection :
      generalizedConvexProgramObjective F (a • p.1 + b • q.1) ≤
        ((a : ℝ) : EReal) * generalizedConvexProgramObjective F p.1 +
          ((b : ℝ) : EReal) * generalizedConvexProgramObjective F q.1 :=
    proposition_29_1 (F := F.1) F.2 (0 : Fin m → ℝ) p.1 q.1 a b ha hb hab
  have hmul1 :
      ((a : ℝ) : EReal) * generalizedConvexProgramObjective F p.1 ≤
        ((a * p.2 : ℝ) : EReal) := by
    have hmul1' :
        ((a : ℝ) : EReal) * generalizedConvexProgramObjective F p.1 ≤
          ((a : ℝ) : EReal) * (p.2 : EReal) :=
      mul_le_mul_of_nonneg_left hp' (by exact_mod_cast ha)
    simpa [EReal.coe_mul] using hmul1'
  have hmul2 :
      ((b : ℝ) : EReal) * generalizedConvexProgramObjective F q.1 ≤
        ((b * q.2 : ℝ) : EReal) := by
    have hmul2' :
        ((b : ℝ) : EReal) * generalizedConvexProgramObjective F q.1 ≤
          ((b : ℝ) : EReal) * (q.2 : EReal) :=
      mul_le_mul_of_nonneg_left hq' (by exact_mod_cast hb)
    simpa [EReal.coe_mul] using hmul2'
  have hrhs :
      ((a : ℝ) : EReal) * generalizedConvexProgramObjective F p.1 +
          ((b : ℝ) : EReal) * generalizedConvexProgramObjective F q.1 ≤
        ((a * p.2 + b * q.2 : ℝ) : EReal) := by
    calc
      ((a : ℝ) : EReal) * generalizedConvexProgramObjective F p.1 +
          ((b : ℝ) : EReal) * generalizedConvexProgramObjective F q.1
          ≤ ((a * p.2 : ℝ) : EReal) + ((b * q.2 : ℝ) : EReal) :=
            add_le_add hmul1 hmul2
      _ = ((a * p.2 + b * q.2 : ℝ) : EReal) := by
        rw [EReal.coe_add]
  refine ⟨by simpa using (show (a • p.1 + b • q.1) ∈ (Set.univ : Set (Fin n → ℝ)) from by simp), ?_⟩
  -- The endpoint bounds on the epigraph coordinates propagate to the convex combination.
  simpa [epigraph, generalizedConvexProgramObjective, smul_eq_mul, add_assoc, add_comm,
    add_left_comm] using hsection.trans hrhs

/-- Definition 6.29.14: For the generalized convex program associated with a convex
bifunction `F`, the convex function `F₀` is called the objective function for the
unperturbed problem `(P)`. -/
abbrev generalizedConvexProgramPrimalObjective {m n : ℕ} (F : ConvexBifunction m n) :
    (Fin n → ℝ) → EReal :=
  (generalizedConvexProgramPrimal F).objective

/-- Definition 6.29.15: The optimal value in the unperturbed generalized convex
program `(P)` associated with a convex bifunction `F` is the infimum of the objective
function `F₀` over `ℝ^n`. -/
noncomputable def generalizedConvexProgramOptimalValue {m n : ℕ} (F : ConvexBifunction m n) :
    EReal :=
  sInf (Set.range (generalizedConvexProgramObjective F))

/-- Definition 6.29.16: The feasible solutions to the unperturbed generalized convex
program `(P)` associated with a convex bifunction `F` are the vectors in the convex set
`dom F₀`, i.e. the effective domain of the objective function `F₀`. -/
def generalizedConvexProgramFeasibleSet {m n : ℕ} (F : ConvexBifunction m n) :
    Set (Fin n → ℝ) :=
  erealDom (generalizedConvexProgramObjective F)

/-- Definition 6.29.17: The unperturbed generalized convex program `(P)` associated with
a convex bifunction `F` is consistent when it has at least one feasible solution, i.e.
when the feasible set `dom F₀` is nonempty. -/
def generalizedConvexProgramConsistent {m n : ℕ} (F : ConvexBifunction m n) : Prop :=
  Set.Nonempty (generalizedConvexProgramFeasibleSet F)

-- Proof sketch: unfold consistency as nonemptiness of the feasible set `dom F₀`.
-- Then compare this with the definition of the optimal value as the infimum of the range
-- of `F₀`: the infimum is `< +∞` exactly when some objective value is `< +∞`.
/-- Helper for Lemma 6.29.6: consistency is exactly the existence of a feasible point
whose objective value is finite. -/
lemma helperForLemma_6_29_6_consistent_iff_exists_finiteObjectiveValue {m n : ℕ}
    (F : ConvexBifunction m n) :
    generalizedConvexProgramConsistent F ↔
      ∃ x : Fin n → ℝ, generalizedConvexProgramObjective F x < ⊤ := by
  -- Unfold consistency and the feasible-set definition so the witness is exactly a point
  -- where the zero-perturbation objective is finite.
  simp [generalizedConvexProgramConsistent, generalizedConvexProgramFeasibleSet, erealDom,
    Set.Nonempty]

/-- Helper for Lemma 6.29.6: the infimum of the objective-value range is finite exactly
when some objective value is finite. -/
lemma helperForLemma_6_29_6_exists_finiteObjectiveValue_iff_optimalValue_lt_top {m n : ℕ}
    (F : ConvexBifunction m n) :
    (∃ x : Fin n → ℝ, generalizedConvexProgramObjective F x < ⊤) ↔
      generalizedConvexProgramOptimalValue F < ⊤ := by
  constructor
  · intro hx
    rcases hx with ⟨x, hx⟩
    have hx_mem :
        generalizedConvexProgramObjective F x ∈
          Set.range (generalizedConvexProgramObjective F) :=
      ⟨x, rfl⟩
    -- Compare the infimum with the displayed range element and then use its finiteness.
    have hsInf_le :
        generalizedConvexProgramOptimalValue F ≤ generalizedConvexProgramObjective F x := by
      exact sInf_le hx_mem
    exact lt_of_le_of_lt hsInf_le hx
  · intro hOptimal
    -- A strict upper bound on the infimum produces a range element that is already `< ⊤`.
    rcases
        (sInf_lt_iff.mp (by
          simpa [generalizedConvexProgramOptimalValue] using hOptimal)) with
      ⟨y, hy_mem, hy_lt⟩
    rcases hy_mem with ⟨x, rfl⟩
    exact ⟨x, hy_lt⟩

/-- Lemma 6.29.6: The unperturbed generalized convex program `(P)` associated with a
convex bifunction `F` is consistent if and only if its optimal value is `< +∞`. -/
theorem generalizedConvexProgramConsistent_iff_optimalValue_lt_top {m n : ℕ}
    (F : ConvexBifunction m n) :
    generalizedConvexProgramConsistent F ↔ generalizedConvexProgramOptimalValue F < ⊤ := by
  -- First rewrite consistency as existence of a point with finite objective value.
  rw [helperForLemma_6_29_6_consistent_iff_exists_finiteObjectiveValue]
  -- Then identify that existential condition with finiteness of the optimal value.
  exact helperForLemma_6_29_6_exists_finiteObjectiveValue_iff_optimalValue_lt_top F

/-- The optimal-solution set of the unperturbed generalized convex program associated with `F`
consists of the feasible vectors `x` for which `F₀ x` attains the optimal value and is not
`-∞`. -/
def generalizedConvexProgramOptimalSolutionSet {m n : ℕ} (F : ConvexBifunction m n) :
    Set (Fin n → ℝ) :=
  {x | x ∈ generalizedConvexProgramFeasibleSet F ∧
    generalizedConvexProgramObjective F x = generalizedConvexProgramOptimalValue F ∧
    generalizedConvexProgramObjective F x ≠ (⊥ : EReal)}

/-- Helper for Lemma 6.29.7: an improper objective either attains `-∞` somewhere or is
identically `+∞`. -/
lemma helperForLemma_6_29_7_improper_objective_cases {m n : ℕ} (F : ConvexBifunction m n)
    (hnotproper : ¬ ProperERealFunction (generalizedConvexProgramObjective F)) :
    (∃ x : Fin n → ℝ, generalizedConvexProgramObjective F x = (⊥ : EReal)) ∨
      (∀ x : Fin n → ℝ, generalizedConvexProgramObjective F x = (⊤ : EReal)) := by
  -- Unfold properness so the negation becomes exactly the two obstruction cases.
  rw [ProperERealFunction] at hnotproper
  push_neg at hnotproper
  by_cases hbot :
      ∃ x : Fin n → ℝ, generalizedConvexProgramObjective F x = (⊥ : EReal)
  · exact Or.inl hbot
  · right
    -- If the objective never equals `⊥`, the failure of properness can only come from being
    -- identically `⊤`.
    have hnoBot : ∀ x : Fin n → ℝ, generalizedConvexProgramObjective F x ≠ (⊥ : EReal) := by
      intro x hx
      exact hbot ⟨x, hx⟩
    exact hnotproper hnoBot

/-- Helper for Lemma 6.29.7: if the objective is everywhere `+∞`, then there are no optimal
solutions because there are no feasible points. -/
lemma helperForLemma_6_29_7_optimalSolutionSet_eq_empty_of_objective_eq_top_everywhere
    {m n : ℕ} (F : ConvexBifunction m n)
    (htop : ∀ x : Fin n → ℝ, generalizedConvexProgramObjective F x = (⊤ : EReal)) :
    generalizedConvexProgramOptimalSolutionSet F = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  -- Any optimal solution is feasible, so its objective value must be `< ⊤`.
  have hx_feasible : generalizedConvexProgramObjective F x < ⊤ := hx.1
  have hx_top : generalizedConvexProgramObjective F x = (⊤ : EReal) := htop x
  rw [hx_top] at hx_feasible
  exact not_lt_of_ge le_rfl hx_feasible

/-- Helper for Lemma 6.29.7: if the objective attains `-∞`, then the optimal value is `-∞`. -/
lemma helperForLemma_6_29_7_optimalValue_eq_bot_of_exists_objective_eq_bot {m n : ℕ}
    (F : ConvexBifunction m n)
    (hbot : ∃ x : Fin n → ℝ, generalizedConvexProgramObjective F x = (⊥ : EReal)) :
    generalizedConvexProgramOptimalValue F = (⊥ : EReal) := by
  rcases hbot with ⟨x, hx⟩
  have hbot_mem :
      (⊥ : EReal) ∈ Set.range (generalizedConvexProgramObjective F) := ⟨x, hx⟩
  -- Compare the infimum with the displayed range element and use minimality of `⊥`.
  have hle_bot : generalizedConvexProgramOptimalValue F ≤ (⊥ : EReal) := by
    simpa [generalizedConvexProgramOptimalValue] using sInf_le hbot_mem
  exact le_antisymm hle_bot bot_le

/-- Helper for Lemma 6.29.7: if the optimal value is `-∞`, then no point can satisfy the
definition of an optimal solution, which explicitly excludes objective value `-∞`. -/
lemma helperForLemma_6_29_7_optimalSolutionSet_eq_empty_of_optimalValue_eq_bot {m n : ℕ}
    (F : ConvexBifunction m n)
    (hOptimalValue : generalizedConvexProgramOptimalValue F = (⊥ : EReal)) :
    generalizedConvexProgramOptimalSolutionSet F = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  -- Membership forces the objective to equal the optimal value and simultaneously differ from `⊥`.
  have hx_eq_bot : generalizedConvexProgramObjective F x = (⊥ : EReal) := by
    simpa [hOptimalValue] using hx.2.1
  exact hx.2.2 hx_eq_bot

-- Proof sketch: if `F₀` is not proper, either it never takes a finite value or it attains `⊥`
-- somewhere. In the first case there are no feasible points, hence no optimal solutions. In the
-- second case the optimal value is `⊥`, so no feasible point with objective different from `⊥`
-- can realize it.
/-- Lemma 6.29.7: The set of all optimal solutions to `(P)` is empty unless `F₀` is proper. -/
theorem generalizedConvexProgramOptimalSolutionSet_eq_empty_of_objective_not_proper {m n : ℕ}
    (F : ConvexBifunction m n)
    (hnotproper : ¬ ProperERealFunction (generalizedConvexProgramObjective F)) :
    generalizedConvexProgramOptimalSolutionSet F = ∅ := by
  rcases helperForLemma_6_29_7_improper_objective_cases F hnotproper with hbot | htop
  · -- If `F₀` attains `-∞`, then the infimum is `-∞`, which excludes optimal solutions.
    have hOptimalValue :
        generalizedConvexProgramOptimalValue F = (⊥ : EReal) :=
      helperForLemma_6_29_7_optimalValue_eq_bot_of_exists_objective_eq_bot F hbot
    exact helperForLemma_6_29_7_optimalSolutionSet_eq_empty_of_optimalValue_eq_bot F
      hOptimalValue
  · -- If `F₀` is everywhere `+∞`, then the feasible set is empty.
    exact
      helperForLemma_6_29_7_optimalSolutionSet_eq_empty_of_objective_eq_top_everywhere F htop

-- Proof sketch: if `F₀` is proper, then its infimum is attained exactly on the minimum set,
-- and properness rules out the `-∞` values excluded in the definition of optimal solutions.
-- Convexity of the zero-perturbation objective makes the minimum set convex, and every minimizer
-- has finite objective value, so it lies in the feasible set `dom F₀`.
/-- Helper for Lemma 6.29.8: the program-specific optimal value is the usual infimum of the
zero-perturbation objective. -/
lemma helperForLemma_6_29_8_optimalValue_eq_functionInfimumEReal {m n : ℕ}
    (F : ConvexBifunction m n) :
    generalizedConvexProgramOptimalValue F =
      functionInfimumEReal (generalizedConvexProgramObjective F) := by
  -- Unfold both infimum constructions and identify them with `sInf (range ...)`.
  rw [generalizedConvexProgramOptimalValue, functionInfimumEReal, sInf_range]

/-- Helper for Lemma 6.29.8: a point minimizes an `EReal`-valued function exactly when its
value is a pointwise lower bound. -/
lemma helperForLemma_6_29_8_mem_minimumSetEReal_iff_pointwiseLowerBound {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    x ∈ minimumSetEReal f ↔ ∀ z : Fin n → ℝ, f x ≤ f z := by
  -- Rewrite minimizer membership as equality with the infimum and then compare with every value.
  rw [minimumSetEReal, functionInfimumEReal]
  constructor
  · intro hx z
    rw [hx]
    exact iInf_le (fun y => f y) z
  · intro hx
    exact le_antisymm (le_iInf hx) (iInf_le (fun y => f y) x)

/-- Helper for Lemma 6.29.8: properness guarantees that every minimizer lies in the effective
domain. -/
lemma helperForLemma_6_29_8_minimumSet_subset_erealDom_of_proper {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hproper : ProperERealFunction f) :
    minimumSetEReal f ⊆ erealDom f := by
  intro x hx
  rcases hproper.2 with ⟨y, hy_ne_top⟩
  have hy_lt_top : f y < ⊤ := lt_top_iff_ne_top.mpr hy_ne_top
  -- A minimizer lies below every displayed value, so it inherits finiteness from a proper witness.
  have hx_le : f x ≤ f y :=
    (helperForLemma_6_29_8_mem_minimumSetEReal_iff_pointwiseLowerBound f x).1 hx y
  exact lt_of_le_of_lt hx_le hy_lt_top

/-- Helper for Lemma 6.29.8: for a proper convex objective, the minimum set is convex. -/
lemma helperForLemma_6_29_8_minimumSet_convex_of_proper_convex {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (_hproper : ProperERealFunction f) (hconv : ConvexFunction f) :
    Convex ℝ (minimumSetEReal f) := by
  have hminimum_eq_sublevel :
      minimumSetEReal f = {x : Fin n → ℝ | f x ≤ functionInfimumEReal f} := by
    ext x
    constructor
    · intro hx
      simpa [Set.mem_setOf_eq, minimumSetEReal] using hx.le
    · intro hx
      rw [minimumSetEReal]
      -- Any point below the infimum must actually attain it, since the infimum is a lower bound.
      exact le_antisymm hx (by simpa [functionInfimumEReal] using iInf_le (fun y => f y) x)
  have hsublevel_convex :
      Convex ℝ {x : Fin n → ℝ | f x ≤ functionInfimumEReal f} :=
    (convexFunction_level_sets_convex hconv (functionInfimumEReal f)).2
  -- Replace the minimum set by the infimum sublevel set and invoke convexity of level sets.
  rw [hminimum_eq_sublevel]
  exact hsublevel_convex

/-- Lemma 6.29.8: When the unperturbed objective `F₀` is proper, the set of all optimal
solutions to `(P)` is the minimum set of `F₀`, a possibly empty convex subset of the
set of all feasible solutions to `(P)`. -/
theorem generalizedConvexProgramOptimalSolutionSet_eq_minimumSet_of_objective_proper
    {m n : ℕ} (F : ConvexBifunction m n)
    (hproper : ProperERealFunction (generalizedConvexProgramObjective F)) :
    generalizedConvexProgramOptimalSolutionSet F =
      minimumSetEReal (generalizedConvexProgramObjective F) ∧
    Convex ℝ (minimumSetEReal (generalizedConvexProgramObjective F)) ∧
    minimumSetEReal (generalizedConvexProgramObjective F) ⊆
      generalizedConvexProgramFeasibleSet F := by
  have hsubset_feasible :
      minimumSetEReal (generalizedConvexProgramObjective F) ⊆
        generalizedConvexProgramFeasibleSet F := by
    -- Properness makes every minimizer finite, so minimizers are feasible by definition.
    simpa [generalizedConvexProgramFeasibleSet] using
      helperForLemma_6_29_8_minimumSet_subset_erealDom_of_proper
        (f := generalizedConvexProgramObjective F) hproper
  have heq :
      generalizedConvexProgramOptimalSolutionSet F =
        minimumSetEReal (generalizedConvexProgramObjective F) := by
    ext x
    constructor
    · intro hx
      -- An optimal solution already attains the objective infimum, hence belongs to the minimum set.
      rw [minimumSetEReal]
      have hx_value :
          generalizedConvexProgramObjective F x = generalizedConvexProgramOptimalValue F := hx.2.1
      rw [helperForLemma_6_29_8_optimalValue_eq_functionInfimumEReal F] at hx_value
      exact hx_value
    · intro hx
      have hx_feasible : x ∈ generalizedConvexProgramFeasibleSet F := hsubset_feasible hx
      have hx_eq_inf :
          generalizedConvexProgramObjective F x =
            functionInfimumEReal (generalizedConvexProgramObjective F) := by
        simpa [minimumSetEReal] using hx
      -- Route correction: instead of a closedness-based minimum characterization, use the direct
      -- minimum-set equality and properness to discharge the feasibility and `≠ ⊥` fields.
      refine ⟨hx_feasible, ?_, ?_⟩
      · calc
          generalizedConvexProgramObjective F x =
              functionInfimumEReal (generalizedConvexProgramObjective F) := hx_eq_inf
          _ = generalizedConvexProgramOptimalValue F := by
            symm
            exact helperForLemma_6_29_8_optimalValue_eq_functionInfimumEReal F
      · exact hproper.1 x
  have hconvex :
      Convex ℝ (minimumSetEReal (generalizedConvexProgramObjective F)) :=
    helperForLemma_6_29_8_minimumSet_convex_of_proper_convex
      (f := generalizedConvexProgramObjective F) hproper
      (generalizedConvexProgramObjective_convex F)
  -- Combine the three textbook conclusions: equality of optimal-solution and minimum sets,
  -- convexity of that minimum set, and its inclusion in the feasible set.
  exact ⟨heq, hconvex, hsubset_feasible⟩

end Section29
end Chap06
