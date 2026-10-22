/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section12_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section12_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section04_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.ordinary_convex_program_core

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- A real-valued function on `ℝ^n` is affine on `C` if it agrees there with an affine map. -/
def IsAffineOnFiniteDimensional
    {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ a : (Fin n → ℝ) →ᵃ[ℝ] ℝ, Set.EqOn f a C

/-- Definition 6.28.2: The feasible solutions to an ordinary convex program `(P)` form the
possibly empty convex set `C₀ = C ∩ C₁ ∩ ⋯ ∩ Cₘ`, where `Cᵢ = {x | fᵢ(x) ≤ 0}` for the first
`r` constraints and `Cᵢ = {x | fᵢ(x) = 0}` for the remaining `m - r` constraints. -/
def BookOrdinaryConvexProgram.feasibleSet {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    Set (Fin n → ℝ) :=
  {x | x ∈ P.constraintSet ∧
    (∀ i : Fin r, P.inequalityConstraint i x ≤ 0) ∧
    (∀ i : Fin (m - r), P.equalityConstraint i x = 0)}

/-- The first `r` components of a multiplier vector, corresponding to the inequality constraints. -/
def BookOrdinaryConvexProgram.inequalityMultipliers {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) : Fin r → ℝ :=
  lambda ∘ Fin.castLE P.inequalityCount_le_constraintCount

/-- The remaining `m - r` components of a multiplier vector, corresponding to the equality
constraints. -/
def BookOrdinaryConvexProgram.equalityMultipliers {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) : Fin (m - r) → ℝ :=
  lambda ∘ Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount) ∘ Fin.natAdd r

/-- The weighted objective `f₀ + λ₁ f₁ + ⋯ + λ_m f_m` attached to a multiplier vector. -/
def BookOrdinaryConvexProgram.kuhnTuckerObjective {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x =>
    P.objective x +
      (∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x) +
      ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x

/-- The extended-real version of the Kuhn--Tucker objective, obtained by adjoining the indicator
of the ambient convex constraint set `C`. This models the book's convention that the infimum of
`h = f₀ + λ₁ f₁ + ⋯ + λ_m f_m` is taken over all of `ℝ^n`, while points outside `C` contribute
`+∞`. -/
noncomputable def BookOrdinaryConvexProgram.extendedKuhnTuckerObjective {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) : (Fin n → ℝ) → EReal :=
  fun x =>
    open scoped Classical in
    if x ∈ P.constraintSet then
      (P.kuhnTuckerObjective lambda x : EReal)
    else
      (⊤ : EReal)

/-- The optimal value of an ordinary convex program, expressed as an infimum in `EReal`. -/
noncomputable def BookOrdinaryConvexProgram.optimalValue {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    EReal :=
  sInf ((fun x => ((P.objective x : ℝ) : EReal)) '' P.feasibleSet)

/-- Definition 6.28.3: A vector `lambda ∈ ℝ^m` is a Kuhn--Tucker vector for an ordinary convex
program `(P)` if its inequality coefficients are nonnegative and the infimum of the weighted
objective `f₀ + λ₁ f₁ + ⋯ + λ_m f_m`, taken over the constraint set `C`, is a finite real number
equal to the optimal value of `(P)`. -/
noncomputable def BookOrdinaryConvexProgram.IsKuhnTuckerVector {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) : Prop :=
  (∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i) ∧
  ∃ v : ℝ,
    sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) =
      (v : EReal) ∧
    P.optimalValue = (v : EReal)

/-- A point is an optimal solution of `P` if it is feasible and minimizes the objective over the
feasible set. -/
def BookOrdinaryConvexProgram.IsOptimalSolution {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) (x : Fin n → ℝ) : Prop :=
  x ∈ P.feasibleSet ∧ ∀ y ∈ P.feasibleSet, P.objective x ≤ P.objective y

-- Proof sketch: Let `D` be the set of global minimizers of the indicator-extended
-- Kuhn--Tucker objective on `ℝ^n`, so that this Lean statement realizes the book's minimizer set
-- for `h = f₀ + λ₁ f₁ + ⋯ + λ_m f_m` while forcing points outside `C = P.constraintSet` to have
-- value `+∞`. Split the inequality indices into `I = {i | λᵢ = 0}` and its complement, adjoin
-- the equality constraints, and obtain the book's set `D₀`. The Kuhn--Tucker equality of the
-- infimum of `h` with the optimal value then shows that `D₀` is exactly the optimal-solution
-- set.
/-- Helper for Theorem 6.28.1: on the ambient constraint set, the indicator-extended
Kuhn--Tucker objective agrees with the real-valued Kuhn--Tucker objective. -/
lemma helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ P.constraintSet) :
    P.extendedKuhnTuckerObjective lambda x = ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) := by
  -- On `constraintSet`, the defining `if` of the extended objective selects the finite branch.
  simp [BookOrdinaryConvexProgram.extendedKuhnTuckerObjective, hx]

/-- Helper for Theorem 6.28.1: every feasible point makes the Kuhn--Tucker objective no larger
than the original objective when the inequality multipliers are nonnegative. -/
lemma helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ P.feasibleSet)
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i) :
    P.kuhnTuckerObjective lambda x ≤ P.objective x := by
  rcases hx with ⟨_, hxIneq, hxEq⟩
  -- Each weighted inequality term is nonpositive at a feasible point.
  have hineq_sum_nonpos :
      ∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hlambda_nonneg i) (hxIneq i)
  -- Each equality term vanishes because feasibility imposes exact equality.
  have heq_sum_zero :
      ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp [hxEq i]
  -- After expanding `h`, only a nonpositive correction to `f₀` remains.
  unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
  linarith

/-- Helper for Theorem 6.28.1: a sum of nonpositive weighted terms can be zero only if every term
with nonzero nonnegative weight already vanishes. -/
lemma helperForTheorem_6_28_1_nonpos_weighted_sum_eq_zero_forces_zero_of_nonzero_weight
    {r : ℕ} {a b : Fin r → ℝ}
    (ha_nonneg : ∀ i, 0 ≤ a i) (hb_nonpos : ∀ i, b i ≤ 0)
    (hsum : ∑ i : Fin r, a i * b i = 0) :
    ∀ i : Fin r, a i ≠ 0 → b i = 0 := by
  intro i hai
  by_contra hbi
  -- A nonzero nonnegative weight is strictly positive.
  have ha_pos : 0 < a i := by
    exact lt_of_le_of_ne (ha_nonneg i) (by simpa [eq_comm] using hai)
  -- A nonzero nonpositive constraint value is strictly negative.
  have hb_neg : b i < 0 := by
    exact lt_of_le_of_ne (hb_nonpos i) hbi
  have hterm_neg : a i * b i < 0 := mul_neg_of_pos_of_neg ha_pos hb_neg
  -- All remaining weighted terms are still nonpositive.
  have hrest_nonpos :
      (Finset.sum (Finset.univ.erase i) fun j : Fin r => a j * b j) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro j hj
    exact mul_nonpos_of_nonneg_of_nonpos (ha_nonneg j) (hb_nonpos j)
  have hsplit :
      (∑ j : Fin r, a j * b j) =
        a i * b i + Finset.sum (Finset.univ.erase i) (fun j : Fin r => a j * b j) := by
    rw [add_comm]
    exact
      (Finset.sum_erase_add (s := Finset.univ) (a := i) (f := fun j : Fin r => a j * b j)
        (Finset.mem_univ i)).symm
  have hsum_lt : ∑ j : Fin r, a j * b j < 0 := by
    rw [hsplit]
    linarith
  -- This contradicts the hypothesis that the full sum is exactly zero.
  rw [hsum] at hsum_lt
  exact (lt_irrefl (0 : ℝ)) hsum_lt

/-- Helper for Theorem 6.28.1: at an optimal solution, the Kuhn--Tucker objective already equals
the original objective. -/
lemma helperForTheorem_6_28_1_optimal_has_kuhnTuckerObjective_eq_objective
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    {x : Fin n → ℝ} (hx : P.IsOptimalSolution x) (hKT : P.IsKuhnTuckerVector lambda) :
    P.kuhnTuckerObjective lambda x = P.objective x := by
  rcases hKT with ⟨hlambda_nonneg, v, hv, hopt⟩
  rcases hx with ⟨hxFeas, hxOptimal⟩
  have hkuhn_le_obj :
      P.kuhnTuckerObjective lambda x ≤ P.objective x :=
    helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible P lambda hxFeas
      hlambda_nonneg
  -- Optimality identifies the feasible infimum with the objective value at `x`.
  have hoptimalValue_eq_obj :
      P.optimalValue = ((P.objective x : ℝ) : EReal) := by
    apply le_antisymm
    · rw [BookOrdinaryConvexProgram.optimalValue]
      exact sInf_le ⟨x, hxFeas, rfl⟩
    · rw [BookOrdinaryConvexProgram.optimalValue]
      refine le_sInf ?_
      rintro _ ⟨y, hyFeas, rfl⟩
      exact EReal.coe_le_coe_iff.2 (hxOptimal y hyFeas)
  -- The Kuhn--Tucker infimum is bounded below by its value at `x`.
  have hv_le :
      (v : EReal) ≤ ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) := by
    rw [← hv]
    exact sInf_le ⟨x, hxFeas.1, rfl⟩
  -- Feasibility gives the opposite inequality through the common optimal value.
  have hkuhn_le_v :
      ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) ≤ (v : EReal) := by
    calc
      ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) ≤ ((P.objective x : ℝ) : EReal) := by
        exact EReal.coe_le_coe_iff.2 hkuhn_le_obj
      _ = P.optimalValue := hoptimalValue_eq_obj.symm
      _ = (v : EReal) := hopt
  have hkuhn_eq_v :
      ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) = (v : EReal) :=
    le_antisymm hkuhn_le_v hv_le
  have hobj_eq_v :
      ((P.objective x : ℝ) : EReal) = (v : EReal) := by
    calc
      ((P.objective x : ℝ) : EReal) = P.optimalValue := hoptimalValue_eq_obj.symm
      _ = (v : EReal) := hopt
  -- Equal finite values in `EReal` come from equal real numbers.
  exact EReal.coe_eq_coe_iff.1 <| by
    calc
      ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) = (v : EReal) := hkuhn_eq_v
      _ = ((P.objective x : ℝ) : EReal) := hobj_eq_v.symm

/-- Theorem 6.28.1: Let `λ` be a Kuhn--Tucker vector for an ordinary convex program `(P)`, and
let `h = f₀ + λ₁ f₁ + ⋯ + λ_m f_m`. Let `D` be the set of points where the
indicator-extended objective `h + δ_C` attains its infimum over `ℝ^n`, let `I` be the set of
inequality indices `i ∈ {1, …, r}` with `λᵢ = 0`, and let `J` be its complement in
`{1, …, m}`. Then the set `D₀` of points `x ∈ D` such that `fᵢ(x) = 0` for every
`i ∈ J` and `fᵢ(x) ≤ 0` for every `i ∈ I` is exactly the set of optimal solutions of `(P)`. -/
theorem kuhnTuckerMinimizerSet_eq_optimalSolutionSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda) :
    {x |
        x ∈ P.constraintSet ∧
        (∀ y : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda x ≤ P.extendedKuhnTuckerObjective lambda y) ∧
        (∀ i : Fin r,
          P.inequalityMultipliers lambda i = 0 → P.inequalityConstraint i x ≤ 0) ∧
        (∀ i : Fin r,
          P.inequalityMultipliers lambda i ≠ 0 → P.inequalityConstraint i x = 0) ∧
        (∀ i : Fin (m - r), P.equalityConstraint i x = 0)} =
      {x | P.IsOptimalSolution x} := by
  rcases hKT with ⟨hlambda_nonneg, v, hv, hopt⟩
  have hKT' : P.IsKuhnTuckerVector lambda := ⟨hlambda_nonneg, v, hv, hopt⟩
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxC, hxMin, hzeroCase, hnonzeroCase, heqCase⟩
    -- The split conditions on zero and nonzero multipliers reconstruct feasibility.
    have hxFeas : x ∈ P.feasibleSet := by
      refine ⟨hxC, ?_, heqCase⟩
      intro i
      by_cases hzero : P.inequalityMultipliers lambda i = 0
      · exact hzeroCase i hzero
      · rw [hnonzeroCase i hzero]
    -- Under these split conditions, every added constraint term vanishes at `x`.
    have hkuhn_eq_obj : P.kuhnTuckerObjective lambda x = P.objective x := by
      have hineq_sum_zero :
          ∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        by_cases hzero : P.inequalityMultipliers lambda i = 0
        · simp [hzero]
        · simp [hnonzeroCase i hzero]
      have heq_sum_zero :
          ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        simp [heqCase i]
      -- With all constraint contributions equal to zero, `h(x) = f₀(x)`.
      unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
      simp [hineq_sum_zero, heq_sum_zero]
    refine ⟨hxFeas, ?_⟩
    intro y hyFeas
    have hyC : y ∈ P.constraintSet := hyFeas.1
    have hxyE := hxMin y
    rw [helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda hxC,
      helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda hyC] at hxyE
    have hxy :
        P.kuhnTuckerObjective lambda x ≤ P.kuhnTuckerObjective lambda y :=
      EReal.coe_le_coe_iff.1 hxyE
    have hy_le_obj :
        P.kuhnTuckerObjective lambda y ≤ P.objective y :=
      helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible P lambda hyFeas
        hlambda_nonneg
    -- Minimizing `h + δ_C` on `C` therefore minimizes `f₀` on the feasible set.
    calc
      P.objective x = P.kuhnTuckerObjective lambda x := hkuhn_eq_obj.symm
      _ ≤ P.kuhnTuckerObjective lambda y := hxy
      _ ≤ P.objective y := hy_le_obj
  · intro hxOptimal
    rcases hxOptimal with ⟨hxFeas, hxOptimal⟩
    have hxC : x ∈ P.constraintSet := hxFeas.1
    have hkuhn_eq_obj :
        P.kuhnTuckerObjective lambda x = P.objective x :=
      helperForTheorem_6_28_1_optimal_has_kuhnTuckerObjective_eq_objective P lambda
        ⟨hxFeas, hxOptimal⟩ hKT'
    -- Optimality likewise identifies the program infimum with `f₀(x)`.
    have hoptimalValue_eq_obj :
        P.optimalValue = ((P.objective x : ℝ) : EReal) := by
      apply le_antisymm
      · rw [BookOrdinaryConvexProgram.optimalValue]
        exact sInf_le ⟨x, hxFeas, rfl⟩
      · rw [BookOrdinaryConvexProgram.optimalValue]
        refine le_sInf ?_
        rintro _ ⟨y, hyFeas, rfl⟩
        exact EReal.coe_le_coe_iff.2 (hxOptimal y hyFeas)
    have hkuhn_eq_v :
        ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) = (v : EReal) := by
      calc
        ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) = ((P.objective x : ℝ) : EReal) := by
          simp [hkuhn_eq_obj]
        _ = P.optimalValue := hoptimalValue_eq_obj.symm
        _ = (v : EReal) := hopt
    have heq_sum_zero :
        ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [hxFeas.2.2 i]
    -- Subtracting the equality-constraint contribution shows the weighted inequality sum is zero.
    have hweighted_eq_zero :
        ∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x = 0 := by
      have hmain :
          P.objective x +
              (∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x) +
                ∑ i : Fin (m - r),
                  P.equalityMultipliers lambda i * P.equalityConstraint i x =
            P.objective x := by
        simpa [BookOrdinaryConvexProgram.kuhnTuckerObjective] using hkuhn_eq_obj
      rw [heq_sum_zero, add_zero] at hmain
      linarith
    have hcomplementary :
        ∀ i : Fin r,
          P.inequalityMultipliers lambda i ≠ 0 → P.inequalityConstraint i x = 0 :=
      helperForTheorem_6_28_1_nonpos_weighted_sum_eq_zero_forces_zero_of_nonzero_weight
        (a := P.inequalityMultipliers lambda)
        (b := fun i => P.inequalityConstraint i x)
        hlambda_nonneg (fun i => hxFeas.2.1 i) hweighted_eq_zero
    refine ⟨hxC, ?_, ?_, ?_, hxFeas.2.2⟩
    · intro y
      by_cases hyC : y ∈ P.constraintSet
      · -- Inside `constraintSet`, both extended values are compared through the same infimum `v`.
        have hyInf :
            (v : EReal) ≤ ((P.kuhnTuckerObjective lambda y : ℝ) : EReal) := by
          rw [← hv]
          exact sInf_le ⟨y, hyC, rfl⟩
        calc
          P.extendedKuhnTuckerObjective lambda x
              = ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) :=
                helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda
                  hxC
          _ = (v : EReal) := hkuhn_eq_v
          _ ≤ ((P.kuhnTuckerObjective lambda y : ℝ) : EReal) := hyInf
          _ = P.extendedKuhnTuckerObjective lambda y :=
            (helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda
              hyC).symm
      · -- Outside `constraintSet`, the extended objective is `⊤`.
        rw [helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda hxC,
          BookOrdinaryConvexProgram.extendedKuhnTuckerObjective, if_neg hyC]
        exact le_top
    · intro i hiZero
      exact hxFeas.2.1 i
    · intro i hiNonzero
      exact hcomplementary i hiNonzero

-- Proof sketch: Use the closedness assumptions to work with the indicator-extended
-- Kuhn--Tucker objective on all of `ℝ^n`. A unique point where this extended objective attains
-- its infimum belongs to the minimizer set from the preceding theorem, so that theorem identifies
-- it with the unique optimal solution of the program.
/-- Helper for Corollary 6.28.1: a Kuhn--Tucker vector forces the ambient constraint set to be
nonempty, because the corresponding infimum is a finite real number. -/
lemma helperForCorollary_6_28_1_constraintSet_nonempty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda) :
    P.constraintSet.Nonempty := by
  rcases hKT with ⟨_hlambda_nonneg, v, hv, _hopt⟩
  -- A finite `sInf` cannot come from the empty image set.
  by_contra hEmpty
  have hImageEmpty :
      ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) = ∅ := by
    simp [Set.not_nonempty_iff_eq_empty.mp hEmpty]
  rw [hImageEmpty, sInf_empty] at hv
  exact (EReal.coe_ne_top v) hv.symm

/-- Helper for Corollary 6.28.1: the unique minimizer of the indicator-extended
Kuhn--Tucker objective must lie in the ambient constraint set, because points outside it have
value `⊤` while the Kuhn--Tucker hypothesis provides a finite comparison point. -/
lemma helperForCorollary_6_28_1_xbar_mem_constraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (xbar : Fin n → ℝ) (hKT : P.IsKuhnTuckerVector lambda)
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y) :
    xbar ∈ P.constraintSet := by
  rcases helperForCorollary_6_28_1_constraintSet_nonempty P lambda hKT with ⟨y, hyC⟩
  -- Compare `xbar` to a point of finite extended objective value.
  have hxy := hxbar_min y
  by_contra hxbarC
  have hxbarTop :
      P.extendedKuhnTuckerObjective lambda xbar = (⊤ : EReal) := by
    simp [BookOrdinaryConvexProgram.extendedKuhnTuckerObjective, hxbarC]
  rw [hxbarTop,
    helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda hyC] at hxy
  exact (not_top_le_coe (P.kuhnTuckerObjective lambda y)) hxy

/-- Helper for Corollary 6.28.1: once the optimal value is identified with a finite real `v`,
one can choose a feasible sequence whose objective values approach `v` from above. -/
lemma helperForCorollary_6_28_1_exists_nearOptimal_feasibleSequence
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ}
    (hopt : P.optimalValue = (v : EReal)) :
    ∃ xSeq : ℕ → (Fin n → ℝ),
      (∀ k : ℕ, xSeq k ∈ P.feasibleSet) ∧
      ∀ k : ℕ, P.objective (xSeq k) ≤ v + 1 / ((k : ℝ) + 1) := by
  have hImageNonempty :
      (((fun x => ((P.objective x : ℝ) : EReal)) '' P.feasibleSet) : Set EReal).Nonempty := by
    -- If the feasible image were empty, the optimal value would be `⊤`, not a finite real.
    by_contra hEmpty
    have hImageEmpty :
        ((fun x => ((P.objective x : ℝ) : EReal)) '' P.feasibleSet) = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hEmpty
    rw [BookOrdinaryConvexProgram.optimalValue, hImageEmpty, sInf_empty] at hopt
    exact (EReal.coe_ne_top v) hopt.symm
  have hApprox :
      ∀ k : ℕ, ∃ x : Fin n → ℝ,
        x ∈ P.feasibleSet ∧ P.objective x ≤ v + 1 / ((k : ℝ) + 1) := by
    intro k
    have hklt :
        P.optimalValue < ((v + 1 / ((k : ℝ) + 1) : ℝ) : EReal) := by
      rw [hopt]
      exact EReal.coe_lt_coe_iff.2 <| by
        have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    rw [BookOrdinaryConvexProgram.optimalValue] at hklt
    obtain ⟨μ, hμmem, hμlt⟩ := exists_lt_of_csInf_lt hImageNonempty hklt
    rcases hμmem with ⟨x, hxFeas, rfl⟩
    refine ⟨x, hxFeas, ?_⟩
    exact le_of_lt (EReal.coe_lt_coe_iff.1 hμlt)
  classical
  choose xSeq hxSeqFeas hxSeqNear using hApprox
  -- Package the pointwise choices into the desired near-optimal feasible sequence.
  exact ⟨xSeq, hxSeqFeas, hxSeqNear⟩

/-- Helper for Corollary 6.28.1: if a feasible point has objective value at most `ε` above the
optimal value `v`, then the Kuhn--Tucker correction term at that point is trapped between `0` and
`ε`. -/
lemma helperForCorollary_6_28_1_objective_sub_kuhnTuckerObjective_nonneg_and_le_of_nearOptimal_feasible
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    {v ε : ℝ} {y : Fin n → ℝ}
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i)
    (hv :
      sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) =
        (v : EReal))
    (hyFeasible : y ∈ P.feasibleSet)
    (hyNear : P.objective y ≤ v + ε) :
    0 ≤ P.objective y - P.kuhnTuckerObjective lambda y ∧
      P.objective y - P.kuhnTuckerObjective lambda y ≤ ε := by
  -- Feasibility makes the Kuhn--Tucker correction nonnegative because `h(y) ≤ f₀(y)`.
  have hkuhn_le_obj :
      P.kuhnTuckerObjective lambda y ≤ P.objective y :=
    helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible
      P lambda hyFeasible hlambda_nonneg
  -- The same feasible point also bounds the Kuhn--Tucker infimum from above by its finite value.
  have hv_le_hykuhn :
      v ≤ P.kuhnTuckerObjective lambda y := by
    have hyInf :
        (v : EReal) ≤ ((P.kuhnTuckerObjective lambda y : ℝ) : EReal) := by
      rw [← hv]
      exact sInf_le ⟨y, hyFeasible.1, rfl⟩
    exact EReal.coe_le_coe_iff.1 hyInf
  constructor
  · linarith
  · linarith

/-- Helper for Corollary 6.28.1: the canonical near-optimal feasible sequence produced from the
finite optimal value also has Kuhn--Tucker correction terms converging to zero at the same
explicit rate. -/
lemma helperForCorollary_6_28_1_exists_nearOptimal_feasibleSequence_with_smallKuhnTuckerGap
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) {v : ℝ}
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i)
    (hv :
      sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) =
        (v : EReal))
    (hopt : P.optimalValue = (v : EReal)) :
    ∃ xSeq : ℕ → (Fin n → ℝ),
      (∀ k : ℕ, xSeq k ∈ P.feasibleSet) ∧
      (∀ k : ℕ, P.objective (xSeq k) ≤ v + 1 / ((k : ℝ) + 1)) ∧
      (∀ k : ℕ, 0 ≤ P.objective (xSeq k) - P.kuhnTuckerObjective lambda (xSeq k)) ∧
      (∀ k : ℕ,
        P.objective (xSeq k) - P.kuhnTuckerObjective lambda (xSeq k) ≤
          1 / ((k : ℝ) + 1)) := by
  obtain ⟨xSeq, hxSeqFeas, hxSeqNear⟩ :=
    helperForCorollary_6_28_1_exists_nearOptimal_feasibleSequence P hopt
  -- Apply the pointwise gap estimate to each term of the near-optimal feasible sequence.
  refine ⟨xSeq, hxSeqFeas, hxSeqNear, ?_, ?_⟩
  · intro k
    exact
      (helperForCorollary_6_28_1_objective_sub_kuhnTuckerObjective_nonneg_and_le_of_nearOptimal_feasible
        P lambda hlambda_nonneg hv (hxSeqFeas k) (hxSeqNear k)).1
  · intro k
    exact
      (helperForCorollary_6_28_1_objective_sub_kuhnTuckerObjective_nonneg_and_le_of_nearOptimal_feasible
        P lambda hlambda_nonneg hv (hxSeqFeas k) (hxSeqNear k)).2

/-- Helper for Corollary 6.28.1: every optimal solution already lies in the minimizer set from
Theorem 6.28.1, so uniqueness of the global minimizer forces it to equal `xbar`. -/
lemma helperForCorollary_6_28_1_optimalSolution_eq_xbar
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (xbar : Fin n → ℝ) (hKT : P.IsKuhnTuckerVector lambda)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    ∀ y : Fin n → ℝ, P.IsOptimalSolution y → y = xbar := by
  intro y hyOptimal
  have hyLeft :
      y ∈
        {x |
          x ∈ P.constraintSet ∧
            (∀ z : Fin n → ℝ,
              P.extendedKuhnTuckerObjective lambda x ≤ P.extendedKuhnTuckerObjective lambda z) ∧
            (∀ i : Fin r,
              P.inequalityMultipliers lambda i = 0 → P.inequalityConstraint i x ≤ 0) ∧
            (∀ i : Fin r,
              P.inequalityMultipliers lambda i ≠ 0 → P.inequalityConstraint i x = 0) ∧
            (∀ i : Fin (m - r), P.equalityConstraint i x = 0)} := by
    -- Rewrite the optimality predicate through Theorem 6.28.1 to recover global minimality.
    rw [kuhnTuckerMinimizerSet_eq_optimalSolutionSet P lambda hKT]
    exact hyOptimal
  rcases hyLeft with ⟨_hyC, hyMin, _hyZero, _hyNonzero, _hyEq⟩
  exact hunique y hyMin

/-- Helper for Corollary 6.28.1: a global minimizer of the indicator-extended Kuhn--Tucker
objective is a point of its minimum set in the sense of Section 27. -/
lemma helperForCorollary_6_28_1_mem_minimumSet_of_global_minimizer
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (xbar : Fin n → ℝ)
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y) :
    xbar ∈ minimumSetEReal (P.extendedKuhnTuckerObjective lambda) := by
  -- Compare the value at `xbar` with the global infimum from both sides.
  rw [minimumSetEReal]
  refine le_antisymm ?_ ?_
  · -- Global minimality makes the value at `xbar` a lower bound for the whole function.
    rw [functionInfimumEReal]
    exact le_iInf hxbar_min
  · -- The infimum is always below the value at the chosen point.
    simpa [functionInfimumEReal] using
      (iInf_le (fun y : Fin n → ℝ => P.extendedKuhnTuckerObjective lambda y) xbar)

/-- Helper for Corollary 6.28.1: the unique minimizer hypothesis identifies the Section 27
minimum set of the indicator-extended Kuhn--Tucker objective with the singleton `{xbar}`. -/
lemma helperForCorollary_6_28_1_extended_minimumSet_eq_singleton
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (xbar : Fin n → ℝ)
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    minimumSetEReal (P.extendedKuhnTuckerObjective lambda) =
      ({xbar} : Set (Fin n → ℝ)) := by
  ext y
  constructor
  · intro hyMin
    -- Any point of the minimum set is itself a global minimizer.
    have hy_global :
        ∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤
            P.extendedKuhnTuckerObjective lambda z := by
      intro z
      rw [minimumSetEReal] at hyMin
      calc
        P.extendedKuhnTuckerObjective lambda y =
            functionInfimumEReal (P.extendedKuhnTuckerObjective lambda) := hyMin
        _ ≤ P.extendedKuhnTuckerObjective lambda z := by
          simpa [functionInfimumEReal] using
            (iInf_le (fun w : Fin n → ℝ => P.extendedKuhnTuckerObjective lambda w) z)
    rw [Set.mem_singleton_iff]
    exact hunique y hy_global
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    -- The distinguished minimizer belongs to the minimum set by direct comparison with the infimum.
    exact
      helperForCorollary_6_28_1_mem_minimumSet_of_global_minimizer
        P lambda xbar hxbar_min

/-- Helper for Corollary 6.28.1: the unique global minimizer of the indicator-extended
Kuhn--Tucker objective realizes the same finite value `v` that appears in the Kuhn--Tucker
vector hypothesis. -/
lemma helperForCorollary_6_28_1_xbar_kuhnTuckerObjective_eq_kuhnTuckerValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    {v : ℝ} (xbar : Fin n → ℝ)
    (hv :
      sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) =
        (v : EReal))
    (hxbarC : xbar ∈ P.constraintSet)
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y)
    (hconstraint_nonempty : P.constraintSet.Nonempty) :
    ((P.kuhnTuckerObjective lambda xbar : ℝ) : EReal) = (v : EReal) := by
  -- Restrict the global minimizer comparison to the ambient constraint set.
  have hxbar_min_on_constraintSet :
      ∀ y ∈ P.constraintSet,
        P.kuhnTuckerObjective lambda xbar ≤ P.kuhnTuckerObjective lambda y := by
    intro y hyC
    have hxy := hxbar_min y
    rw [helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda hxbarC,
      helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda hyC] at hxy
    exact EReal.coe_le_coe_iff.1 hxy
  -- Compare `xbar` with the constraint-set infimum from both sides.
  apply le_antisymm
  · rw [← hv]
    refine le_csInf ?_ ?_
    · rcases hconstraint_nonempty with ⟨y, hyC⟩
      exact ⟨_, ⟨y, hyC, rfl⟩⟩
    · intro a ha
      rcases ha with ⟨y, hyC, rfl⟩
      exact EReal.coe_le_coe_iff.2 (hxbar_min_on_constraintSet y hyC)
  · rw [← hv]
    exact sInf_le ⟨xbar, hxbarC, rfl⟩

/-- Helper for Corollary 6.28.1: the feasible sequence whose objective values approach `v`
also gives a Section 27 near-minimizing sequence for the indicator-extended Kuhn--Tucker
objective. -/
lemma helperForCorollary_6_28_1_extendedObjective_value_tendsto_infimum
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    {v : ℝ} (xbar : Fin n → ℝ)
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i)
    (hv :
      sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) =
        (v : EReal))
    (hxbarC : xbar ∈ P.constraintSet)
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y)
    (hxbar_kuhn_eq_v :
      ((P.kuhnTuckerObjective lambda xbar : ℝ) : EReal) = (v : EReal))
    (xSeq : ℕ → (Fin n → ℝ))
    (hxSeqFeas : ∀ k : ℕ, xSeq k ∈ P.feasibleSet)
    (hxSeqNear : ∀ k : ℕ, P.objective (xSeq k) ≤ v + 1 / ((k : ℝ) + 1)) :
    Filter.Tendsto
      (fun k : ℕ => P.extendedKuhnTuckerObjective lambda (xSeq k))
      Filter.atTop
      (nhds (functionInfimumEReal (P.extendedKuhnTuckerObjective lambda))) := by
  -- First squeeze the real Kuhn--Tucker values between `v` and the explicit upper envelope.
  have hUpperTendsto :
      Filter.Tendsto
        (fun k : ℕ => v + 1 / ((k : ℝ) + 1))
        Filter.atTop
        (nhds v) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto
          (fun k : ℕ => v + 1 / ((k : ℝ) + 1))
          Filter.atTop
          (nhds (v + 0)))
  have hLowerBound :
      ∀ k : ℕ, v ≤ P.kuhnTuckerObjective lambda (xSeq k) := by
    intro k
    have hxkC : xSeq k ∈ P.constraintSet := (hxSeqFeas k).1
    have hxk_ge :
        (v : EReal) ≤ ((P.kuhnTuckerObjective lambda (xSeq k) : ℝ) : EReal) := by
      rw [← hv]
      exact sInf_le ⟨xSeq k, hxkC, rfl⟩
    exact EReal.coe_le_coe_iff.1 hxk_ge
  have hUpperBound :
      ∀ k : ℕ, P.kuhnTuckerObjective lambda (xSeq k) ≤ v + 1 / ((k : ℝ) + 1) := by
    intro k
    exact le_trans
      (helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible
        P lambda (hxSeqFeas k) hlambda_nonneg)
      (hxSeqNear k)
  have hKuhnTendsto :
      Filter.Tendsto
        (fun k : ℕ => P.kuhnTuckerObjective lambda (xSeq k))
        Filter.atTop
        (nhds v) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (f := fun k : ℕ => P.kuhnTuckerObjective lambda (xSeq k))
      (g := fun _ : ℕ => v)
      (h := fun k : ℕ => v + 1 / ((k : ℝ) + 1))
      tendsto_const_nhds
      hUpperTendsto
      ?_
      ?_
    · intro k
      exact hLowerBound k
    · intro k
      exact hUpperBound k
  -- Then transport that real convergence through the coercion into `EReal`.
  have hcoeContinuous : Continuous fun t : ℝ => ((t : ℝ) : EReal) := by
    simpa using (EReal.continuous_coe_iff (f := fun t : ℝ => t)).2 continuous_id
  have hExtendedTendsto_v :
      Filter.Tendsto
        (fun k : ℕ => P.extendedKuhnTuckerObjective lambda (xSeq k))
        Filter.atTop
        (nhds (v : EReal)) := by
    have hKuhnERealTendsto :
        Filter.Tendsto
          (fun k : ℕ => ((P.kuhnTuckerObjective lambda (xSeq k) : ℝ) : EReal))
          Filter.atTop
          (nhds (v : EReal)) :=
      hcoeContinuous.continuousAt.tendsto.comp hKuhnTendsto
    refine Filter.Tendsto.congr' ?_ hKuhnERealTendsto
    refine Filter.Eventually.of_forall ?_
    intro k
    exact
      helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet
        P lambda (hxSeqFeas k).1 |>.symm
  -- Finally identify the limiting value with the Section 27 infimum.
  have hxbar_mem_minimumSet :
      xbar ∈ minimumSetEReal (P.extendedKuhnTuckerObjective lambda) :=
    helperForCorollary_6_28_1_mem_minimumSet_of_global_minimizer
      P lambda xbar hxbar_min
  have hInfEq :
      functionInfimumEReal (P.extendedKuhnTuckerObjective lambda) = (v : EReal) := by
    rw [minimumSetEReal] at hxbar_mem_minimumSet
    calc
      functionInfimumEReal (P.extendedKuhnTuckerObjective lambda) =
          P.extendedKuhnTuckerObjective lambda xbar := hxbar_mem_minimumSet.symm
      _ = ((P.kuhnTuckerObjective lambda xbar : ℝ) : EReal) :=
        helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda hxbarC
      _ = (v : EReal) := hxbar_kuhn_eq_v
  simpa [hInfEq] using hExtendedTendsto_v

/-- Helper for Corollary 6.28.1: once the indicator-extended Kuhn--Tucker objective is known to
be closed and proper, the book's near-optimal feasible sequence can be upgraded to a sequence
converging to the unique global minimizer `xbar`. -/
lemma helperForCorollary_6_28_1_exists_nearOptimal_feasibleSequence_tendsto_globalMinimizer
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (xbar : Fin n → ℝ) {v : ℝ}
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i)
    (hv :
      sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) =
        (v : EReal))
    (hopt : P.optimalValue = (v : EReal))
    (hclosedExtended : ClosedConvexFunction (P.extendedKuhnTuckerObjective lambda))
    (hproperExtended :
      ProperConvexFunctionOn
        (Set.univ : Set (Fin n → ℝ))
        (P.extendedKuhnTuckerObjective lambda))
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    ∃ xSeq : ℕ → Fin n → ℝ,
      (∀ k, xSeq k ∈ P.feasibleSet) ∧
      (∀ k, P.objective (xSeq k) ≤ v + 1 / ((k : ℝ) + 1)) ∧
      Filter.Tendsto xSeq Filter.atTop (nhds xbar) := by
  have hKT : P.IsKuhnTuckerVector lambda := ⟨hlambda_nonneg, v, hv, hopt⟩
  -- First recover the unique minimizer's finite value and the canonical near-optimal sequence.
  have hxbarC :
      xbar ∈ P.constraintSet :=
    helperForCorollary_6_28_1_xbar_mem_constraintSet P lambda xbar hKT hxbar_min
  obtain ⟨xSeq, hxSeqFeas, hxSeqNear⟩ :=
    helperForCorollary_6_28_1_exists_nearOptimal_feasibleSequence P hopt
  have hconstraint_nonempty : P.constraintSet.Nonempty :=
    helperForCorollary_6_28_1_constraintSet_nonempty P lambda hKT
  have hxbar_kuhn_eq_v :
      ((P.kuhnTuckerObjective lambda xbar : ℝ) : EReal) = (v : EReal) :=
    helperForCorollary_6_28_1_xbar_kuhnTuckerObjective_eq_kuhnTuckerValue
      P lambda xbar hv hxbarC hxbar_min hconstraint_nonempty
  have hminimumSetSingleton :
      minimumSetEReal (P.extendedKuhnTuckerObjective lambda) =
        ({xbar} : Set (Fin n → ℝ)) :=
    helperForCorollary_6_28_1_extended_minimumSet_eq_singleton
      P lambda xbar hxbar_min hunique
  -- Then the Section 27 convergence theorem sends that sequence to the unique minimizer.
  have hnearMin :
      Filter.Tendsto
        (fun k : ℕ => P.extendedKuhnTuckerObjective lambda (xSeq k))
        Filter.atTop
        (nhds (functionInfimumEReal (P.extendedKuhnTuckerObjective lambda))) :=
    helperForCorollary_6_28_1_extendedObjective_value_tendsto_infimum
      P lambda xbar hlambda_nonneg hv hxbarC hxbar_min hxbar_kuhn_eq_v
      xSeq hxSeqFeas hxSeqNear
  have hxSeq_tendsto :
      Filter.Tendsto xSeq Filter.atTop (nhds xbar) :=
    nearMinimizingSequence_tendsto_of_unique_minimizer
      (f := P.extendedKuhnTuckerObjective lambda)
      hclosedExtended hproperExtended xbar hminimumSetSingleton xSeq hnearMin
  exact ⟨xSeq, hxSeqFeas, hxSeqNear, hxSeq_tendsto⟩

/-- Helper for Corollary 6.28.1: once the indicator-extended Kuhn--Tucker objective is known to
be closed and proper, the Section 27 convergence theorem turns the near-optimal feasible sequence
into an optimality proof for the unique minimizer `xbar`. -/
lemma helperForCorollary_6_28_1_isOptimalSolution_of_closedProperExtendedObjective
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (xbar : Fin n → ℝ)
    (hKT : P.IsKuhnTuckerVector lambda)
    (hobjective_closed : LowerSemicontinuous P.objective)
    (hinequality_closed : ∀ i : Fin r, LowerSemicontinuous (P.inequalityConstraint i))
    (_hequality_closed : ∀ i : Fin (m - r), LowerSemicontinuous (P.equalityConstraint i))
    (hclosedExtended : ClosedConvexFunction (P.extendedKuhnTuckerObjective lambda))
    (hproperExtended :
      ProperConvexFunctionOn
        (Set.univ : Set (Fin n → ℝ))
        (P.extendedKuhnTuckerObjective lambda))
    (hxbar_min :
      ∀ y : Fin n → ℝ,
        P.extendedKuhnTuckerObjective lambda xbar ≤ P.extendedKuhnTuckerObjective lambda y)
    (hunique :
      ∀ y : Fin n → ℝ,
        (∀ z : Fin n → ℝ,
          P.extendedKuhnTuckerObjective lambda y ≤ P.extendedKuhnTuckerObjective lambda z) →
        y = xbar) :
    P.IsOptimalSolution xbar := by
  rcases hKT with ⟨hlambda_nonneg, v, hv, hopt⟩
  have hKT' : P.IsKuhnTuckerVector lambda := ⟨hlambda_nonneg, v, hv, hopt⟩
  -- First recover the convergent near-optimal feasible sequence supplied by the closed/proper
  -- bridge, then read feasibility of the limit from the closed constraint data.
  obtain ⟨xSeq, hxSeqFeas, hxSeqNear, hxSeq_tendsto⟩ :=
    helperForCorollary_6_28_1_exists_nearOptimal_feasibleSequence_tendsto_globalMinimizer
      P lambda xbar hlambda_nonneg hv hopt hclosedExtended hproperExtended hxbar_min hunique
  have hxbarC :
      xbar ∈ P.constraintSet :=
    helperForCorollary_6_28_1_xbar_mem_constraintSet P lambda xbar hKT' hxbar_min
  have hconstraint_nonempty : P.constraintSet.Nonempty :=
    helperForCorollary_6_28_1_constraintSet_nonempty P lambda hKT'
  have hxbar_kuhn_eq_v :
      ((P.kuhnTuckerObjective lambda xbar : ℝ) : EReal) = (v : EReal) :=
    helperForCorollary_6_28_1_xbar_kuhnTuckerObjective_eq_kuhnTuckerValue
      P lambda xbar hv hxbarC hxbar_min hconstraint_nonempty
  -- Convergence lets the closed sublevel sets of the inequality constraints pass to the limit.
  have hineq_feasible :
      ∀ i : Fin r, P.inequalityConstraint i xbar ≤ 0 := by
    intro i
    have hclosedSublevel :
        IsClosed {x : Fin n → ℝ | P.inequalityConstraint i x ≤ 0} :=
      by
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
  -- The affine representatives of the equality constraints are continuous on all of `ℝ^n`.
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
    -- The ambient constraint membership was proved earlier, and convergence supplies the rest.
    exact ⟨hxbarC, hineq_feasible, heq_feasible⟩
  -- The lower semicontinuity of `f₀` and the explicit upper envelope force `f₀(xbar) ≤ v`.
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
          {x : Fin n → ℝ | ((P.objective x : ℝ) : EReal) ≤ (((v + ε : ℝ) : ℝ) : EReal)} :=
      by
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
  have hxbar_kuhn_eq_v_real :
      P.kuhnTuckerObjective lambda xbar = v :=
    EReal.coe_eq_coe_iff.1 hxbar_kuhn_eq_v
  have hxbar_min_on_constraintSet :
      ∀ y ∈ P.constraintSet,
        P.kuhnTuckerObjective lambda xbar ≤ P.kuhnTuckerObjective lambda y := by
    intro y hyC
    have hxy := hxbar_min y
    rw [helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda hxbarC,
      helperForTheorem_6_28_1_extendedKuhnTuckerObjective_eq_on_constraintSet P lambda hyC] at hxy
    exact EReal.coe_le_coe_iff.1 hxy
  refine ⟨hxbarFeasible, ?_⟩
  intro y hyFeasible
  have hy_kuhn_ge_v :
      v ≤ P.kuhnTuckerObjective lambda y := by
    have hxy := hxbar_min_on_constraintSet y hyFeasible.1
    simpa [hxbar_kuhn_eq_v_real] using hxy
  have hy_objective_ge_v :
      v ≤ P.objective y := by
    exact le_trans hy_kuhn_ge_v
      (helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible
        P lambda hyFeasible hlambda_nonneg)
  exact le_trans hxbar_objective_le_v hy_objective_ge_v


end Section28
end Chap06
