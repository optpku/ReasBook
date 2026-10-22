/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part5

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- Corollary 6.28.1: Let `(P)` be an ordinary convex program, and let `λ` be a Kuhn--Tucker
vector for `(P)`. Assume that the functions `fᵢ` are all closed. If the infimum of
`h = f₀ + λ₁ f₁ + ⋯ + λ_m f_m`, viewed as the indicator-extended Kuhn--Tucker objective on
`ℝ^n`, is attained at a unique point `x̄`, then `x̄` is the unique optimal solution of `(P)`.
In this formalization the ambient constraint set `C` is primitive program data, so the closed-data
assumption is represented by lower semicontinuity of the program data together with
`IsClosed P.constraintSet`. -/
theorem unique_optimalSolution_of_unique_kuhnTuckerObjective_minimizer
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
  -- First use the closed-data bridge to show that the unique minimizer `xbar` is already a
  -- primal optimal solution.
  have hxbarOptimal : P.IsOptimalSolution xbar :=
    helperForCorollary_6_28_1_isOptimalSolution_of_closedData
      P lambda xbar hKT hobjective_closed hinequality_closed hequality_closed
      hconstraint_closed hxbar_min hunique
  -- Then Theorem 6.28.1 identifies every optimal solution with the same minimizer `xbar`.
  have hoptimal_unique :
      ∀ y, P.IsOptimalSolution y → y = xbar :=
    helperForCorollary_6_28_1_optimalSolution_eq_xbar P lambda xbar hKT hunique
  exact ⟨hxbarOptimal, hoptimal_unique⟩

-- Proof sketch: work in the Section 6.28 setup of an ordinary convex program. The
-- Kuhn--Tucker objective is the strictly convex term `f₀` plus the weighted constraint terms
-- from the program data; by the convex-program hypotheses, the inequality-constraint terms are
-- convex once their coefficients are nonnegative, while the equality-constraint terms remain
-- affine. Adding convex and affine terms to a strictly convex function preserves strict
-- convexity on `C = P.constraintSet`, and a strictly convex function on a convex set has at most
-- one minimizer there.
/-- A point attains the infimum of the Kuhn--Tucker objective over the ambient constraint set
`C = P.constraintSet`. -/
def BookOrdinaryConvexProgram.IsKuhnTuckerObjectiveMinimizer
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  x ∈ P.constraintSet ∧
    ∀ z ∈ P.constraintSet, P.kuhnTuckerObjective lambda x ≤ P.kuhnTuckerObjective lambda z

/-- Helper for Corollary 6.28.2: the weighted sum of the equality-constraint terms is convex on
the ambient constraint set because each equality constraint is affine there. -/
lemma helperForCorollary_6_28_2_weightedEqualitySum_convexOn
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) :
    ConvexOn ℝ P.constraintSet
      (fun x => ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x) := by
  -- Each weighted equality constraint is convex because affine functions stay affine after
  -- scalar multiplication.
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
  -- Summing finitely many convex equality terms preserves convexity.
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
  exact hequality_sum

/-- Helper for Corollary 6.28.2: the weighted constraint-correction term in the Kuhn--Tucker
objective is convex on the ambient constraint set when the inequality multipliers are
nonnegative. -/
lemma helperForCorollary_6_28_2_constraintCorrection_convexOn
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i) :
    ConvexOn ℝ P.constraintSet
      (fun x =>
        (∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x) +
          ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x) := by
  -- The inequality terms are convex because convexity is preserved by nonnegative scaling.
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
  -- The equality contribution is convex by the affine-on argument above.
  have hequality_sum :
      ConvexOn ℝ P.constraintSet
        (fun x => ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x) :=
    helperForCorollary_6_28_2_weightedEqualitySum_convexOn P lambda
  -- Adding the two convex pieces yields the full constraint correction.
  exact ConvexOn.add hineq_sum hequality_sum

/-- Helper for Corollary 6.28.2: a Kuhn--Tucker objective minimizer is exactly a global minimizer
of that objective on the ambient constraint set. -/
lemma helperForCorollary_6_28_2_isMinOn_of_minimizer
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (x : Fin n → ℝ)
    (hx : P.IsKuhnTuckerObjectiveMinimizer lambda x) :
    IsMinOn (P.kuhnTuckerObjective lambda) P.constraintSet x := by
  -- The minimizer predicate was defined with the same pointwise inequality as `IsMinOn`.
  simpa [BookOrdinaryConvexProgram.IsKuhnTuckerObjectiveMinimizer, isMinOn_iff] using hx.2

-- Proof sketch: use strict convexity of `f₀` on `C`, the convexity of the inequality
-- constraints built into `P`, the affinity of the equality constraints, and the nonnegativity of
-- the inequality coefficients of `lambda`. This makes `h` strictly convex on `C`, and strict
-- convexity on the convex set `C` forces any minimizer of `h` on `C` to be unique.
/-- Corollary 6.28.2: Let `(P)` be an ordinary convex program and let `lambda` have nonnegative
inequality coefficients. If `f₀` is strictly convex on `C`, then the function
`h = f₀ + λ₁ f₁ + ⋯ + λ_m f_m = P.kuhnTuckerObjective lambda` is strictly convex on `C`, so the
infimum of `h` is attained at a unique point if attained at all. -/
theorem kuhnTuckerObjective_strictConvexOn_and_minimizers_unique
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i)
    (hstrict : StrictConvexOn ℝ P.constraintSet P.objective) :
    StrictConvexOn ℝ P.constraintSet (P.kuhnTuckerObjective lambda) ∧
      ((∃ x, P.IsKuhnTuckerObjectiveMinimizer lambda x) →
        ∃! x, P.IsKuhnTuckerObjectiveMinimizer lambda x) := by
  -- First package the weighted constraint terms into a single convex correction on `C`.
  have hconstraint_correction :
      ConvexOn ℝ P.constraintSet
        (fun x =>
          (∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x) +
            ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x) :=
    helperForCorollary_6_28_2_constraintCorrection_convexOn P lambda hlambda_nonneg
  -- Adding a convex correction to the strictly convex objective keeps strict convexity.
  have hstrict_with_correction :
      StrictConvexOn ℝ P.constraintSet
        (fun x =>
          P.objective x +
            ((∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x) +
              ∑ i : Fin (m - r), P.equalityMultipliers lambda i * P.equalityConstraint i x)) := by
    simpa using hstrict.add_convexOn hconstraint_correction
  -- This left-associated sum is exactly the Kuhn--Tucker objective.
  have hstrict_kuhn :
      StrictConvexOn ℝ P.constraintSet (P.kuhnTuckerObjective lambda) := by
    refine hstrict_with_correction.congr ?_
    intro x hx
    unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
    ring_nf
  constructor
  · exact hstrict_kuhn
  · intro hex
    rcases hex with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    -- Repackage both minimizer witnesses as `IsMinOn` hypotheses on `P.constraintSet`.
    have hx_min :
        IsMinOn (P.kuhnTuckerObjective lambda) P.constraintSet x :=
      helperForCorollary_6_28_2_isMinOn_of_minimizer P lambda x hx
    have hy_min :
        IsMinOn (P.kuhnTuckerObjective lambda) P.constraintSet y :=
      helperForCorollary_6_28_2_isMinOn_of_minimizer P lambda y hy
    -- Strict convexity on `C` gives uniqueness of a global minimizer once attainment is known.
    exact (hstrict_kuhn.eq_of_isMinOn hx_min hy_min hx.1 hy.1).symm

/-- The first `r` components of a perturbation vector, corresponding to the inequality
constraints. -/
def BookOrdinaryConvexProgram.inequalityPerturbation {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) (u : Fin m → ℝ) : Fin r → ℝ :=
  u ∘ Fin.castLE P.inequalityCount_le_constraintCount

/-- The remaining `m - r` components of a perturbation vector, corresponding to the equality
constraints. -/
def BookOrdinaryConvexProgram.equalityPerturbation {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) (u : Fin m → ℝ) : Fin (m - r) → ℝ :=
  u ∘ Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount) ∘ Fin.natAdd r

-- Proof sketch: subtracting a fixed real constant from a convex function preserves convexity on
-- the same convex set, so each shifted inequality constraint remains convex on `P.constraintSet`.
/-- Shifting an inequality constraint by a perturbation component preserves convexity on the
ambient constraint set. -/
lemma BookOrdinaryConvexProgram.perturbed_inequalityConstraint_convexOn
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (u : Fin m → ℝ) :
    ∀ i : Fin r,
      ConvexOn ℝ P.constraintSet
        (fun x => P.inequalityConstraint i x - P.inequalityPerturbation u i) := by
  intro i
  -- Subtracting a fixed perturbation component is just addition of a constant, so convexity is
  -- preserved on the same ambient constraint set.
  simpa [sub_eq_add_neg] using
    (P.inequalityConstraint_convexOn i).add_const (-P.inequalityPerturbation u i)

-- Proof sketch: an affine function remains affine after subtracting a constant scalar, so each
-- shifted equality constraint is still affine on `P.constraintSet`.
/-- Shifting an equality constraint by a perturbation component preserves affinity on the ambient
constraint set. -/
lemma BookOrdinaryConvexProgram.perturbed_equalityConstraint_affineOn
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (u : Fin m → ℝ) :
    ∀ i : Fin (m - r),
      IsAffineOnFiniteDimensional P.constraintSet
        (fun x => P.equalityConstraint i x - P.equalityPerturbation u i) := by
  intro i
  rcases P.equalityConstraint_affineOn i with ⟨a, ha⟩
  -- Subtract the constant perturbation from the affine representative witnessing affinity on
  -- `P.constraintSet`.
  refine ⟨a - AffineMap.const ℝ (Fin n → ℝ) (P.equalityPerturbation u i), ?_⟩
  intro x hx
  simp [ha hx]

/-- Definition 6.28.4: For each perturbation vector `u = (v₁, …, vₘ) ∈ ℝ^m`, the perturbed
problem `(P_u)` is the ordinary convex program with the same objective `f₀` and ambient set `C`,
but whose constraints are `fᵢ(x) ≤ vᵢ` for `i = 1, …, r` and `fᵢ(x) = vᵢ` for
`i = r + 1, …, m`, encoded by shifting the corresponding constraint functions by the components
of `u`. -/
def BookOrdinaryConvexProgram.perturbedProblem {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) (u : Fin m → ℝ) : BookOrdinaryConvexProgram n m r :=
  { constraintSet := P.constraintSet
    objective := P.objective
    inequalityConstraint := fun i x => P.inequalityConstraint i x - P.inequalityPerturbation u i
    equalityConstraint := fun i x => P.equalityConstraint i x - P.equalityPerturbation u i
    inequalityCount_le_constraintCount := P.inequalityCount_le_constraintCount
    convex_constraintSet := P.convex_constraintSet
    objective_convexOn := P.objective_convexOn
    inequalityConstraint_convexOn := P.perturbed_inequalityConstraint_convexOn u
    equalityConstraint_affineOn := P.perturbed_equalityConstraint_affineOn u }

/-- Definition 6.28.5: The perturbation function of an ordinary convex program `(P)` sends a
perturbation vector `u = (v₁, …, vₘ)` to the optimal value of the perturbed problem `(P_u)`,
equivalently to the infimum of `f₀(x)` over `x ∈ C` satisfying `fᵢ(x) ≤ vᵢ` for `i = 1, …, r`
and `fᵢ(x) = vᵢ` for `i = r + 1, …, m`, with value `+∞` when the constraints are infeasible. -/
noncomputable def BookOrdinaryConvexProgram.perturbationFunction {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) : (Fin m → ℝ) → EReal :=
  fun u => (P.perturbedProblem u).optimalValue

/-- Helper for Theorem 6.28.2: the zero perturbation recovers the original optimal value. -/
lemma helperForTheorem_6_28_2_perturbationFunction_zero_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    P.perturbationFunction 0 = P.optimalValue := by
  -- Unfolding the zero perturbation identifies the perturbed feasible set with the original one.
  simp [BookOrdinaryConvexProgram.perturbationFunction, BookOrdinaryConvexProgram.optimalValue,
    BookOrdinaryConvexProgram.perturbedProblem, BookOrdinaryConvexProgram.feasibleSet,
    BookOrdinaryConvexProgram.inequalityPerturbation, BookOrdinaryConvexProgram.equalityPerturbation]

/-- Helper for Theorem 6.28.2: split the perturbation pairing into its inequality and equality
coordinates. -/
lemma helperForTheorem_6_28_2_pairing_split
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda u : Fin m → ℝ) :
    (∑ i : Fin m, lambda i * u i) =
      (∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityPerturbation u i) +
        ∑ j : Fin (m - r), P.equalityMultipliers lambda j * P.equalityPerturbation u j := by
  -- Reindex the full pairing along `m = r + (m - r)` so `Fin.sum_univ_add` can split it into
  -- the head inequality block and the tail equality block.
  let h : r + (m - r) = m := Nat.add_sub_of_le P.inequalityCount_le_constraintCount
  let g : Fin (r + (m - r)) → ℝ := fun k => lambda (Fin.cast h k) * u (Fin.cast h k)
  have hcastsum :
      (∑ k : Fin (r + (m - r)), g k) = ∑ i : Fin m, lambda i * u i := by
    refine Fintype.sum_equiv (Fin.castOrderIso h).toEquiv g
      (fun i : Fin m => lambda i * u i) ?_
    intro k
    simp [g]
  have hsum :
      (∑ i : Fin m, lambda i * u i) =
        (∑ i : Fin r, g (Fin.castAdd (m - r) i)) +
          ∑ j : Fin (m - r), g (Fin.natAdd r j) := by
    calc
      ∑ i : Fin m, lambda i * u i = ∑ k : Fin (r + (m - r)), g k := hcastsum.symm
      _ = (∑ i : Fin r, g (Fin.castAdd (m - r) i)) +
            ∑ j : Fin (m - r), g (Fin.natAdd r j) := Fin.sum_univ_add g
  -- Unfolding the head and tail coordinates identifies the two summands with the perturbation
  -- components defined from `lambda` and `u`.
  simpa [h, BookOrdinaryConvexProgram.inequalityMultipliers,
    BookOrdinaryConvexProgram.equalityMultipliers,
    BookOrdinaryConvexProgram.inequalityPerturbation,
    BookOrdinaryConvexProgram.equalityPerturbation, Function.comp] using hsum

/-- Helper for Theorem 6.28.2: a single-inequality relaxation leaves every equality perturbation
coordinate equal to zero. -/
lemma helperForTheorem_6_28_2_equalityPerturbation_eq_zero_of_singleInequalityRelaxation
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (i : Fin r) (t : ℝ) :
    let u : Fin m → ℝ :=
      fun k => if k = Fin.castLE P.inequalityCount_le_constraintCount i then t else 0
    ∀ j : Fin (m - r), P.equalityPerturbation u j = 0 := by
  intro u j
  -- Tail indices land at values at least `r`, whereas the selected inequality index is strictly
  -- less than `r`; this makes the defining equality test impossible.
  have hneq :
      Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount) (Fin.natAdd r j) ≠
        Fin.castLE P.inequalityCount_le_constraintCount i := by
    intro hEq
    have hge :
        r ≤ (Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount)
          (Fin.natAdd r j)).1 := by
      simp [Fin.coe_natAdd]
    have hlt : (Fin.castLE P.inequalityCount_le_constraintCount i).1 < r := by
      simpa using i.is_lt
    rw [hEq] at hge
    exact not_le_of_gt hlt hge
  -- After unfolding the equality perturbation, the impossible branch disappears and the value is
  -- exactly zero.
  simpa [BookOrdinaryConvexProgram.equalityPerturbation, u, Function.comp, hneq]

/-- Helper for Theorem 6.28.2: the pairing of a single-coordinate inequality relaxation picks out
exactly the corresponding inequality multiplier. -/
lemma helperForTheorem_6_28_2_pairing_of_singleInequalityRelaxation
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (i : Fin r) (t : ℝ) :
    let u : Fin m → ℝ :=
      fun k => if k = Fin.castLE P.inequalityCount_le_constraintCount i then t else 0
    (∑ k : Fin m, lambda k * u k) = P.inequalityMultipliers lambda i * t := by
  intro u
  -- First split the full pairing into its inequality and equality blocks.
  rw [helperForTheorem_6_28_2_pairing_split P lambda u]
  have hineq :
      (∑ j : Fin r, P.inequalityMultipliers lambda j * P.inequalityPerturbation u j) =
        P.inequalityMultipliers lambda i * t := by
    -- On the inequality block, only the `i`-th perturbation coordinate is nonzero.
    rw [Finset.sum_eq_single i]
    · simp [BookOrdinaryConvexProgram.inequalityMultipliers,
        BookOrdinaryConvexProgram.inequalityPerturbation, u, Function.comp]
    · intro j _hj hji
      have hcast :
          Fin.castLE P.inequalityCount_le_constraintCount j ≠
            Fin.castLE P.inequalityCount_le_constraintCount i := by
        intro hEq
        apply hji
        exact Fin.castLE_injective P.inequalityCount_le_constraintCount hEq
      simp [BookOrdinaryConvexProgram.inequalityPerturbation, u, Function.comp, hji, hcast]
    · simp [BookOrdinaryConvexProgram.inequalityPerturbation, u, Function.comp]
  have heq :
      ∑ j : Fin (m - r), P.equalityMultipliers lambda j * P.equalityPerturbation u j = 0 := by
    -- The equality block vanishes because the relaxation changed only one inequality coordinate.
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [helperForTheorem_6_28_2_equalityPerturbation_eq_zero_of_singleInequalityRelaxation
      P i t j]
    ring
  linarith

/-- Helper for Theorem 6.28.2: perturbed feasibility bounds the Kuhn--Tucker objective by the
original objective plus the perturbation pairing. -/
lemma helperForTheorem_6_28_2_kuhnTuckerObjective_le_objective_plus_pairing_of_perturbedFeasible
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    {u : Fin m → ℝ} {x : Fin n → ℝ} (hx : x ∈ (P.perturbedProblem u).feasibleSet)
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i) :
    ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) ≤
      (((P.objective x + ∑ i : Fin m, lambda i * u i) : ℝ) : EReal) := by
  rcases hx with ⟨_, hxIneq, hxEq⟩
  -- Rewrite perturbed feasibility into bounds on the original constraint functions.
  have hxIneq' : ∀ i : Fin r, P.inequalityConstraint i x ≤ P.inequalityPerturbation u i := by
    intro i
    exact sub_nonpos.mp (by simpa [BookOrdinaryConvexProgram.perturbedProblem] using hxIneq i)
  have hxEq' : ∀ j : Fin (m - r), P.equalityConstraint j x = P.equalityPerturbation u j := by
    intro j
    exact sub_eq_zero.mp (by simpa [BookOrdinaryConvexProgram.perturbedProblem] using hxEq j)
  -- The inequality contribution is monotone under the nonnegative multipliers.
  have hineq_sum_le :
      ∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x ≤
        ∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityPerturbation u i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact mul_le_mul_of_nonneg_left (hxIneq' i) (hlambda_nonneg i)
  -- The equality contribution matches the perturbation coordinates exactly.
  have heq_sum_eq :
      ∑ j : Fin (m - r), P.equalityMultipliers lambda j * P.equalityConstraint j x =
        ∑ j : Fin (m - r), P.equalityMultipliers lambda j * P.equalityPerturbation u j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [hxEq' j]
  -- Split the full pairing into the inequality and equality coordinates.
  have hpairing_split :
      (∑ i : Fin m, lambda i * u i) =
        (∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityPerturbation u i) +
          ∑ j : Fin (m - r), P.equalityMultipliers lambda j * P.equalityPerturbation u j := by
    exact helperForTheorem_6_28_2_pairing_split P lambda u
  -- After expanding the definition, only these two constraint sums need comparison.
  have hreal :
      P.kuhnTuckerObjective lambda x ≤ P.objective x + ∑ i : Fin m, lambda i * u i := by
    unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
    rw [hpairing_split]
    linarith
  exact_mod_cast hreal

/-- Helper for Theorem 6.28.2: relaxing a single inequality constraint cannot increase the
perturbation value. -/
lemma helperForTheorem_6_28_2_perturbationFunction_le_zero_of_singleInequalityRelaxation
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (i : Fin r) (t : ℝ) (ht : 0 ≤ t) :
    let u : Fin m → ℝ :=
      fun k => if k = Fin.castLE P.inequalityCount_le_constraintCount i then t else 0
    P.perturbationFunction u ≤ P.perturbationFunction 0 := by
  intro u
  -- Every original feasible point stays feasible after relaxing one inequality coordinate.
  have hsubset : P.feasibleSet ⊆ (P.perturbedProblem u).feasibleSet := by
    intro x hx
    rcases hx with ⟨hxC, hxIneq, hxEq⟩
    refine ⟨hxC, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst hji
        simp [BookOrdinaryConvexProgram.perturbedProblem,
          BookOrdinaryConvexProgram.inequalityPerturbation, u]
        exact le_trans (hxIneq j) ht
      · have hcast : Fin.castLE P.inequalityCount_le_constraintCount j ≠
            Fin.castLE P.inequalityCount_le_constraintCount i := by
          intro h
          apply hji
          exact Fin.castLE_injective P.inequalityCount_le_constraintCount h
        have huj_zero : P.inequalityPerturbation u j = 0 := by
          simp [BookOrdinaryConvexProgram.inequalityPerturbation, u, hcast]
        simpa [BookOrdinaryConvexProgram.perturbedProblem, huj_zero] using hxIneq j
    · intro j
      have huj_zero : P.equalityPerturbation u j = 0 := by
        simpa using
          helperForTheorem_6_28_2_equalityPerturbation_eq_zero_of_singleInequalityRelaxation P i t j
      simpa [BookOrdinaryConvexProgram.perturbedProblem, huj_zero] using hxEq j
  -- The relaxed feasible image contains the original feasible image, so its infimum is no larger.
  rw [helperForTheorem_6_28_2_perturbationFunction_zero_eq_optimalValue P,
    BookOrdinaryConvexProgram.perturbationFunction, BookOrdinaryConvexProgram.optimalValue]
  refine sInf_le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hsubset hx, rfl⟩

/-- Helper for Theorem 6.28.2: a global perturbation lower support gives a pointwise lower bound
for the Kuhn--Tucker objective on the ambient constraint set. -/
lemma helperForTheorem_6_28_2_perturbationLowerBound_implies_kuhnTuckerObjective_lowerBound_on_constraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (hbound : ∀ u : Fin m → ℝ,
      P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) ≥
        P.perturbationFunction 0)
    {x : Fin n → ℝ} (hx : x ∈ P.constraintSet) :
    P.perturbationFunction 0 ≤ ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) := by
  let u : Fin m → ℝ :=
    Fin.append (fun i : Fin r => P.inequalityConstraint i x)
      (fun j : Fin (m - r) => P.equalityConstraint j x) ∘
        Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount).symm
  -- Match the perturbation coordinates to the constraint values of `x`.
  have hx_perturbed : x ∈ (P.perturbedProblem u).feasibleSet := by
    refine ⟨hx, ?_, ?_⟩
    · intro i
      simp [BookOrdinaryConvexProgram.perturbedProblem,
        BookOrdinaryConvexProgram.inequalityPerturbation, u]
    · intro j
      simp [BookOrdinaryConvexProgram.perturbedProblem,
        BookOrdinaryConvexProgram.equalityPerturbation, u]
  -- Since `x` is feasible for this perturbed problem, its objective bounds the perturbation value.
  have hu_le : P.perturbationFunction u ≤ ((P.objective x : ℝ) : EReal) := by
    rw [BookOrdinaryConvexProgram.perturbationFunction, BookOrdinaryConvexProgram.optimalValue]
    exact sInf_le ⟨x, hx_perturbed, rfl⟩
  -- The pairing with the matched perturbation is exactly the correction term in the
  -- Kuhn--Tucker objective.
  have hpairing_split :
      (∑ i : Fin m, lambda i * u i) =
        (∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x) +
          ∑ j : Fin (m - r), P.equalityMultipliers lambda j * P.equalityConstraint j x := by
    simpa [u, BookOrdinaryConvexProgram.inequalityPerturbation,
      BookOrdinaryConvexProgram.equalityPerturbation, Function.comp] using
      helperForTheorem_6_28_2_pairing_split P lambda u
  have hbound_x :
      P.perturbationFunction 0 ≤
        P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) := by
    simpa using hbound u
  have hupper_x :
      P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) ≤
        (((P.objective x + ∑ i : Fin m, lambda i * u i) : ℝ) : EReal) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (show P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) ≤
          ((P.objective x : ℝ) : EReal) + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) from by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hu_le (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal))
  have hrealize :
      (((P.objective x + ∑ i : Fin m, lambda i * u i) : ℝ) : EReal) =
        ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) := by
    congr 1
    unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
    rw [hpairing_split]
    ring
  exact le_trans hbound_x (hupper_x.trans_eq hrealize)

-- Proof sketch: express the perturbation function as the value function `p` of the family of
-- perturbed programs `P_u`. One direction shows that a Kuhn--Tucker vector yields a global affine
-- lower support `u ↦ p(0) - ∑ i, λᵢ uᵢ` for this value function, while the converse recovers the
-- Kuhn--Tucker conditions from that supporting inequality at every perturbation vector.
/-- Theorem 6.28.2: Assume that the optimal value `p(0)` of `(P)` is finite, where
`p = P.perturbationFunction`. Let `lambda ∈ ℝ^m`. Then the following are equivalent:

1. `lambda` is a Kuhn--Tucker vector for `(P)`.
2. For every `u ∈ ℝ^m`, one has
   `p(u) + ∑ i, lambda i * u i ≥ p(0)`. -/
theorem isKuhnTuckerVector_iff_perturbationFunction_lower_bound
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (hp0_finite : ∃ p0 : ℝ, P.perturbationFunction 0 = (p0 : EReal)) :
    P.IsKuhnTuckerVector lambda ↔
      ∀ u : Fin m → ℝ,
        P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) ≥
          P.perturbationFunction 0 := by
  rcases hp0_finite with ⟨p0, hp0⟩
  constructor
  · intro hKT
    rcases hKT with ⟨hlambda_nonneg, v, hv, hopt⟩
    intro u
    let c : ℝ := ∑ i : Fin m, lambda i * u i
    -- Shift the real inequality before taking the infimum over the perturbed feasible set.
    have hshift : ((v - c : ℝ) : EReal) ≤ P.perturbationFunction u := by
      rw [BookOrdinaryConvexProgram.perturbationFunction, BookOrdinaryConvexProgram.optimalValue]
      refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxC : x ∈ P.constraintSet := hx.1
      have hvx : (v : EReal) ≤ ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) := by
        rw [← hv]
        exact sInf_le ⟨x, hxC, rfl⟩
      have hkuhn_le :
          ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) ≤
            (((P.objective x + ∑ i : Fin m, lambda i * u i) : ℝ) : EReal) :=
        helperForTheorem_6_28_2_kuhnTuckerObjective_le_objective_plus_pairing_of_perturbedFeasible
          P lambda hx hlambda_nonneg
      have hreal : v - c ≤ P.objective x := by
        have hreal' : v ≤ P.objective x + c := by
          exact_mod_cast (le_trans hvx hkuhn_le)
        dsimp [c] at hreal'
        linarith
      change ((v - c : ℝ) : EReal) ≤ ((P.objective x : ℝ) : EReal)
      exact_mod_cast hreal
    -- Adding the pairing back recovers the desired affine lower support inequality.
    have hv_le : (v : EReal) ≤ P.perturbationFunction u + (c : EReal) := by
      have htmp : ((v - c : ℝ) : EReal) + (c : EReal) ≤ P.perturbationFunction u + (c : EReal) := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hshift (c : EReal)
      have hleft : (((v - c : ℝ) : EReal) + (c : EReal)) = (v : EReal) := by
        exact_mod_cast sub_add_cancel v c
      rw [hleft] at htmp
      exact htmp
    calc
      P.perturbationFunction 0 = P.optimalValue :=
        helperForTheorem_6_28_2_perturbationFunction_zero_eq_optimalValue P
      _ = (v : EReal) := hopt
      _ ≤ P.perturbationFunction u + (c : EReal) := hv_le
      _ = P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) := by
        rfl
  · intro hbound
    -- Test the supporting inequality on single-coordinate relaxations to recover the sign
    -- condition on the inequality multipliers.
    have hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i := by
      intro i
      let u : Fin m → ℝ :=
        fun k => if k = Fin.castLE P.inequalityCount_le_constraintCount i then 1 else 0
      have hrelax : P.perturbationFunction u ≤ P.perturbationFunction 0 :=
        helperForTheorem_6_28_2_perturbationFunction_le_zero_of_singleInequalityRelaxation
          P i 1 (by norm_num)
      have hbound_u :
          P.perturbationFunction 0 ≤
            P.perturbationFunction u + ((P.inequalityMultipliers lambda i : ℝ) : EReal) := by
        have hsum : (∑ k : Fin m, lambda k * u k) = P.inequalityMultipliers lambda i := by
          dsimp [u]
          simpa using helperForTheorem_6_28_2_pairing_of_singleInequalityRelaxation P lambda i 1
        simpa [hsum] using hbound u
      have hupper_u :
          P.perturbationFunction u + ((P.inequalityMultipliers lambda i : ℝ) : EReal) ≤
            P.perturbationFunction 0 + ((P.inequalityMultipliers lambda i : ℝ) : EReal) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (show P.perturbationFunction u + ((P.inequalityMultipliers lambda i : ℝ) : EReal) ≤
              P.perturbationFunction 0 + ((P.inequalityMultipliers lambda i : ℝ) : EReal) from by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hrelax ((P.inequalityMultipliers lambda i : ℝ) : EReal))
      have hreal : p0 ≤ p0 + P.inequalityMultipliers lambda i := by
        have hereal : ((p0 : ℝ) : EReal) ≤ ((p0 + P.inequalityMultipliers lambda i : ℝ) : EReal) := by
          calc
            ((p0 : ℝ) : EReal) = P.perturbationFunction 0 := hp0.symm
            _ ≤ P.perturbationFunction u + ((P.inequalityMultipliers lambda i : ℝ) : EReal) :=
              hbound_u
            _ ≤ P.perturbationFunction 0 + ((P.inequalityMultipliers lambda i : ℝ) : EReal) :=
              hupper_u
            _ = ((p0 + P.inequalityMultipliers lambda i : ℝ) : EReal) := by
              rw [hp0]
              simpa using (EReal.coe_add p0 (P.inequalityMultipliers lambda i)).symm
        exact_mod_cast hereal
      linarith
    -- The global lower support now yields a lower bound on the Kuhn--Tucker objective over `C`.
    have hsinf_lower :
        P.perturbationFunction 0 ≤
          sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) := by
      refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      exact
        helperForTheorem_6_28_2_perturbationLowerBound_implies_kuhnTuckerObjective_lowerBound_on_constraintSet
          P lambda hbound hx
    -- Compare the Kuhn--Tucker infimum with the primal optimal value using feasible points.
    have hsinf_upper :
        sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) ≤
          P.optimalValue := by
      rw [BookOrdinaryConvexProgram.optimalValue]
      refine le_sInf ?_
      rintro _ ⟨x, hxFeas, rfl⟩
      have hsinf_le_x :
          sInf ((fun y => ((P.kuhnTuckerObjective lambda y : ℝ) : EReal)) '' P.constraintSet) ≤
            ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) := by
        exact sInf_le ⟨x, hxFeas.1, rfl⟩
      have hkuhn_le_obj :
          ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) ≤ ((P.objective x : ℝ) : EReal) := by
        exact_mod_cast
          helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible
            P lambda hxFeas hlambda_nonneg
      exact le_trans hsinf_le_x hkuhn_le_obj
    have hsinf_eq_p0 :
        sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) =
          (p0 : EReal) := by
      apply le_antisymm
      · calc
          sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) ≤
              P.optimalValue := hsinf_upper
          _ = P.perturbationFunction 0 :=
            (helperForTheorem_6_28_2_perturbationFunction_zero_eq_optimalValue P).symm
          _ = (p0 : EReal) := hp0
      · simpa [hp0] using hsinf_lower
    exact
      ⟨hlambda_nonneg, p0, hsinf_eq_p0,
        by
          simpa [hp0] using
            (helperForTheorem_6_28_2_perturbationFunction_zero_eq_optimalValue P).symm⟩

/-- The inequality-constraint indices for which the constraint function is not affine on the
ambient constraint set. -/
def BookOrdinaryConvexProgram.nonaffineInequalityIndices {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) : Set (Fin r) :=
  {i | ¬ IsAffineOnFiniteDimensional P.constraintSet (P.inequalityConstraint i)}

/-- A relative-interior feasible point is strict on the nonaffine inequality indices when every
inequality constraint in `P.nonaffineInequalityIndices` is satisfied with strict inequality at
that point. This is the constraint qualification used in Theorem 28.3. -/
def BookOrdinaryConvexProgram.HasStrictFeasiblePointOnNonaffineInequalityIndices
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) : Prop :=
  ∃ x : Fin n → ℝ,
    x ∈ euclideanRelativeInterior_fin n P.constraintSet ∧
      x ∈ P.feasibleSet ∧
        ∀ i ∈ P.nonaffineInequalityIndices, P.inequalityConstraint i x < 0

/-- Helper for Theorem 6.28.3: a strict feasible point makes the perturbation value at `0`
finite from above. -/
lemma helperForTheorem_6_28_3_perturbationFunction_zero_ne_top
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    P.perturbationFunction 0 ≠ (⊤ : EReal) := by
  rcases hstrict_feasible with ⟨x, _hxri, hxFeasible, _⟩
  -- A feasible point of `P` is also feasible for the zero perturbation, so `p(0)` is bounded
  -- above by a real objective value.
  have hle :
      P.perturbationFunction 0 ≤ ((P.objective x : ℝ) : EReal) := by
    rw [helperForTheorem_6_28_2_perturbationFunction_zero_eq_optimalValue P,
      BookOrdinaryConvexProgram.optimalValue]
    exact sInf_le ⟨x, hxFeasible, rfl⟩
  intro hp0_top
  rw [hp0_top] at hle
  simp at hle

/-- Helper for Theorem 6.28.3: under finite optimal value and strict feasibility on the
nonaffine inequality constraints, the perturbation value at `0` is an actual real number. -/
lemma helperForTheorem_6_28_3_exists_real_perturbationFunction_zero
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ∃ p0 : ℝ, P.perturbationFunction 0 = (p0 : EReal) := by
  have hp0_ne_top : P.perturbationFunction 0 ≠ (⊤ : EReal) :=
    helperForTheorem_6_28_3_perturbationFunction_zero_ne_top P hstrict_feasible
  have hp0_ne_bot : P.perturbationFunction 0 ≠ (⊥ : EReal) := by
    simpa [helperForTheorem_6_28_2_perturbationFunction_zero_eq_optimalValue P] using hoptimal_ne_bot
  refine ⟨(P.perturbationFunction 0).toReal, ?_⟩
  simpa using (EReal.coe_toReal (x := P.perturbationFunction 0) hp0_ne_top hp0_ne_bot).symm

/-- Helper for Theorem 6.28.3: the strict-feasible witness already separates the inequality
block into a strict nonaffine part and a weak affine part, while satisfying the equality block
exactly. -/
lemma helperForTheorem_6_28_3_exists_point_strict_on_nonaffine_and_weak_on_affine_blocks
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ∃ x : Fin n → ℝ,
      x ∈ P.constraintSet ∧
        (∀ i ∈ P.nonaffineInequalityIndices, P.inequalityConstraint i x < 0) ∧
          (∀ i : Fin r, P.inequalityConstraint i x ≤ 0) ∧
            (∀ j : Fin (m - r), P.equalityConstraint j x = 0) := by
  rcases hstrict_feasible with ⟨x, _hxri, hxFeasible, hstrict⟩
  rcases hxFeasible with ⟨hxC, hineq, heq⟩
  -- Unpack the feasible witness once so the nonaffine strictness and the weak affine data are
  -- both available in the format needed for the Chapter 21 split-block route.
  exact ⟨x, hxC, hstrict, hineq, heq⟩

/-- Helper for Theorem 6.28.3: once the optimal value is the finite real `v`, no feasible point
can have objective value strictly below `v`. -/
lemma helperForTheorem_6_28_3_not_exists_feasiblePoint_with_objective_lt_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ}
    (hoptimal : P.optimalValue = (v : EReal)) :
    ¬ ∃ x : Fin n → ℝ, x ∈ P.feasibleSet ∧ P.objective x < v := by
  intro hlt
  rcases hlt with ⟨x, hxFeasible, hxlt⟩
  -- Any feasible point contributes an upper bound to the infimum defining `P.optimalValue`.
  have hopt_le_obj :
      P.optimalValue ≤ ((P.objective x : ℝ) : EReal) := by
    rw [BookOrdinaryConvexProgram.optimalValue]
    exact sInf_le ⟨x, hxFeasible, rfl⟩
  have hv_le_obj : (v : EReal) ≤ ((P.objective x : ℝ) : EReal) := by
    simpa [hoptimal] using hopt_le_obj
  have hv_le_obj_real : v ≤ P.objective x :=
    EReal.coe_le_coe_iff.1 hv_le_obj
  linarith

/-- Helper for Theorem 6.28.3: Euclidean subgradient membership at the perturbation origin is
exactly the affine supporting inequality from Theorem 6.28.2, with sign convention `-lambda`. -/
lemma helperForTheorem_6_28_3_neg_mem_euclideanSubdifferentialAt_perturbationFunction_zero_iff
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) :
    (-lambda) ∈ euclideanSubdifferentialAt P.perturbationFunction 0 ↔
      ∀ u : Fin m → ℝ,
        P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i : ℝ)) : EReal) ≥
          P.perturbationFunction 0 := by
  constructor
  · intro hsub u
    -- Unfold the Euclidean subgradient condition into the supporting inequality at the test
    -- perturbation `u`.
    have hineq' :
        IsSubgradientAt P.perturbationFunction 0 (dotProductEquiv ℝ (Fin m) (-lambda)) := by
      simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt, subdifferentialAt] using hsub
    have hineq := hineq' u
    let a : EReal := (((∑ i : Fin m, lambda i * u i : ℝ)) : EReal)
    have hsub' : P.perturbationFunction 0 - a ≤ P.perturbationFunction u := by
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        dotProductEquiv_apply_apply, dotProduct_neg, dotProduct] using hineq
    have h1 : a ≠ (⊥ : EReal) ∨ P.perturbationFunction u ≠ ⊤ := Or.inl (by simp [a])
    have h2 : a ≠ (⊤ : EReal) ∨ P.perturbationFunction u ≠ (⊥ : EReal) := Or.inl (by simp [a])
    have hadd :
        P.perturbationFunction 0 ≤ P.perturbationFunction u + a :=
      (EReal.sub_le_iff_le_add h1 h2).1 hsub'
    simpa [a, add_assoc, add_left_comm, add_comm] using hadd
  · intro hsupport
    -- Repackage the supporting inequality back into the subgradient inequality at `0`.
    have hineq' :
        IsSubgradientAt P.perturbationFunction 0 (dotProductEquiv ℝ (Fin m) (-lambda)) := by
      intro u
      let a : EReal := (((∑ i : Fin m, lambda i * u i : ℝ)) : EReal)
      have h1 : a ≠ (⊥ : EReal) ∨ P.perturbationFunction u ≠ ⊤ := Or.inl (by simp [a])
      have h2 : a ≠ (⊤ : EReal) ∨ P.perturbationFunction u ≠ (⊥ : EReal) := Or.inl (by simp [a])
      have hsub' : P.perturbationFunction 0 - a ≤ P.perturbationFunction u :=
        (EReal.sub_le_iff_le_add h1 h2).2
          (by simpa [a, add_assoc, add_left_comm, add_comm] using hsupport u)
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        dotProductEquiv_apply_apply, dotProduct_neg, dotProduct] using hsub'
    simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt, subdifferentialAt] using hineq'

/-- Helper for Theorem 6.28.3: ordinary and Euclidean subgradient nonemptiness are equivalent at
the perturbation origin. -/
lemma helperForTheorem_6_28_3_subdifferentialAt_zero_nonempty_iff_euclideanSubdifferentialAt_zero_nonempty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    Set.Nonempty (subdifferentialAt P.perturbationFunction 0) ↔
      Set.Nonempty (euclideanSubdifferentialAt P.perturbationFunction 0) := by
  constructor
  · rintro ⟨g, hg⟩
    -- Convert the linear-functional subgradient into its Euclidean coordinate representative.
    exact ⟨(dotProductEquiv ℝ (Fin m)).symm g, by
      simpa [euclideanSubdifferentialAt] using hg⟩
  · rintro ⟨u, hu⟩
    -- Evaluate the Euclidean representative as the corresponding dot-product functional.
    exact ⟨dotProductEquiv ℝ (Fin m) u, by
      simpa [euclideanSubdifferentialAt] using hu⟩

/-- Helper for Theorem 6.28.3: once the perturbation function is convex, finite at `0`, and the
origin lies in the relative interior of its effective domain, Theorem 23.3 already forces a
Euclidean subgradient at `0`. -/
lemma helperForTheorem_6_28_3_euclideanSubdifferentialNonempty_of_convex_and_zero_mem_relativeInterior
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hpConv : ConvexFunction P.perturbationFunction)
    (hzero_ri :
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (effectiveDomain (Set.univ : Set (Fin m → ℝ)) P.perturbationFunction))
    (hpFinite : P.perturbationFunction 0 ≠ (⊤ : EReal) ∧
      P.perturbationFunction 0 ≠ (⊥ : EReal)) :
    Set.Nonempty (euclideanSubdifferentialAt P.perturbationFunction 0) := by
  let p : (Fin m → ℝ) → EReal := P.perturbationFunction
  have hsub : Set.Nonempty (subdifferentialAt p 0) := by
    by_contra hNoSub
    -- If no subgradient exists, Theorem 23.3 forces incompatible directional-derivative values
    -- at the zero direction because the base point itself lies in `ri (dom p)`.
    rcases
        (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
          p (by simpa [p] using hpConv) 0 (by simpa [p] using hpFinite)).2 hNoSub with
      ⟨_hdirWitness, hblowupOnRi⟩
    have hzero_blowup := hblowupOnRi 0 (by simpa [p] using hzero_ri)
    have hbot : upperDirectionalDerivativeAt p 0 (0 : Fin m → ℝ) = (⊥ : EReal) := by
      simpa [p] using hzero_blowup.1
    have htop : upperDirectionalDerivativeAt p 0 (0 : Fin m → ℝ) = (⊤ : EReal) := by
      simpa [p] using hzero_blowup.2
    have hbot_eq_top : (⊥ : EReal) = (⊤ : EReal) := by
      calc
        (⊥ : EReal) = upperDirectionalDerivativeAt p 0 (0 : Fin m → ℝ) := hbot.symm
        _ = (⊤ : EReal) := htop
    have hbot_ne_top : (⊥ : EReal) ≠ (⊤ : EReal) := by simp
    exact hbot_ne_top hbot_eq_top
  -- Translate the linear-functional subgradient back into Euclidean coordinates.
  exact
    (helperForTheorem_6_28_3_subdifferentialAt_zero_nonempty_iff_euclideanSubdifferentialAt_zero_nonempty
      P).1 (by simpa [p] using hsub)

/-- Helper for Theorem 6.28.3: finiteness of `p(0)` already places the origin in the effective
domain of the perturbation function. -/
lemma helperForTheorem_6_28_3_zero_mem_effectiveDomain_perturbationFunction
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hpFinite : P.perturbationFunction 0 ≠ (⊤ : EReal) ∧
      P.perturbationFunction 0 ≠ (⊥ : EReal)) :
    (0 : Fin m → ℝ) ∈
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) P.perturbationFunction := by
  -- Effective-domain membership on `Set.univ` only asks that the value at the point is not `⊤`.
  rw [effectiveDomain_eq]
  exact ⟨by simp, lt_top_iff_ne_top.mpr hpFinite.1⟩


end Section28
end Chap06
