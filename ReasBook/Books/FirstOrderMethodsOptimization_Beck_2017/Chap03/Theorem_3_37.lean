/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_36
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.37 is a `bridge/view` item in the same inequality-constrained convex-optimality
domain as Theorem 3.36. Its owner abstractions are the chapter `slaters_condition` from
Definition 3.20, the strict/weak feasible-set owners
`strict_inequality_feasible_set` and `inequality_feasible_set`, and the source-facing Fritz-John
multiplier predicate from Theorem 3.36. This file therefore keeps the textbook KKT wording only
as a thin specialization of `IsFritzJohnMultiplier f g xstar 1 lambda`, instead of
reintroducing parallel existential wrappers for strict feasibility or KKT data. -/
recall subdifferentialAt
recall strict_inequality_feasible_set
recall strict_inequality_feasible_set_subset_inequality_feasible_set
recall inequality_feasible_set
recall slaters_condition
recall IsFritzJohnMultiplier
recall exists_fritz_john_multipliers_of_isMinOn

section KKTContext

variable {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {xstar : E}

/-- A multiplier vector `lambda` satisfies the KKT conditions for the inequality-constrained
problem with objective `f`, constraints `g`, and candidate optimizer `xstar` when it is a
normalized Fritz-John multiplier, equivalently when it is componentwise nonnegative, satisfies the
subdifferential stationarity condition, and obeys complementary slackness. -/
def IsKKTMultiplier
    {m : ℕ} (f : E → ℝ) (g : Fin m → E → ℝ) (xstar : E) (lambda : Fin m → ℝ) : Prop :=
  IsFritzJohnMultiplier f g xstar 1 lambda

-- Proof sketch: in one direction, specialize the Fritz-John fields at `lambda0 = 1`, rewrite
-- `1 • subdifferentialAt f xstar` as `subdifferentialAt f xstar`, and discard the automatic
-- clauses `0 ≤ 1` and `1 ≠ 0`. In the other direction, assemble the KKT nonnegativity,
-- stationarity, and complementary-slackness data into the Fritz-John predicate at `lambda0 = 1`.
/-- Unfolding `IsKKTMultiplier` gives exactly the textbook KKT multiplier conditions:
componentwise nonnegativity, subdifferential stationarity, and complementary slackness. -/
@[simp] theorem isKKTMultiplier_iff {lambda : Fin m → ℝ} :
    IsKKTMultiplier f g xstar lambda ↔
      (∀ i : Fin m, 0 ≤ lambda i) ∧
        (0 : StrongDual ℝ E) ∈
            subdifferentialAt f xstar + ∑ i : Fin m, lambda i • subdifferentialAt (g i) xstar ∧
          ∀ i : Fin m, lambda i * g i xstar = 0 := by
  change IsFritzJohnMultiplier f g xstar 1 lambda ↔
      (∀ i : Fin m, 0 ≤ lambda i) ∧
        (0 : StrongDual ℝ E) ∈
            subdifferentialAt f xstar + ∑ i : Fin m, lambda i • subdifferentialAt (g i) xstar ∧
          ∀ i : Fin m, lambda i * g i xstar = 0
  rw [isFritzJohnMultiplier_iff]
  simp

/-- Every KKT multiplier vector is componentwise nonnegative. -/
theorem IsKKTMultiplier.nonneg
    {lambda : Fin m → ℝ} (h : IsKKTMultiplier f g xstar lambda) :
    ∀ i : Fin m, 0 ≤ lambda i :=
  (isKKTMultiplier_iff.mp h).1

/-- Every KKT multiplier vector satisfies the subdifferential stationarity condition. -/
theorem IsKKTMultiplier.stationarity
    {lambda : Fin m → ℝ} (h : IsKKTMultiplier f g xstar lambda) :
    (0 : StrongDual ℝ E) ∈
        subdifferentialAt f xstar + ∑ i : Fin m, lambda i • subdifferentialAt (g i) xstar :=
  (isKKTMultiplier_iff.mp h).2.1

/-- Every KKT multiplier vector satisfies complementary slackness. -/
theorem IsKKTMultiplier.complementary_slackness
    {lambda : Fin m → ℝ} (h : IsKKTMultiplier f g xstar lambda) :
    ∀ i : Fin m, lambda i * g i xstar = 0 :=
  (isKKTMultiplier_iff.mp h).2.2

end KKTContext

section ConvexProblemContext

variable [FiniteDimensional ℝ E]
variable {m : ℕ} (f : E → ℝ) (g : Fin m → E → ℝ) (xstar : E)

recall mem_subdifferential
recall is_subgradient_at_coe_iff
recall strongDualSubdifferential_eq_image_subdifferential

/-- Helper for Theorem 3.37: pointwise witnesses for a `Fin n`-indexed family of sets assemble
into the corresponding finite Minkowski sum. -/
private theorem mem_sum_univ_of_forall_mem
    {α : Type*} [AddCommMonoid α] {n : ℕ}
    {A : Fin n → Set α} {x : Fin n → α}
    (hx : ∀ i, x i ∈ A i) :
    (∑ i, x i) ∈ ∑ i, A i := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- Split off the last coordinate and reassemble the two summands with `Set.mem_add`.
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Set.mem_add]
      refine ⟨∑ i : Fin n, x i.castSucc, ih ?_, x (Fin.last n), hx (Fin.last n), rfl⟩
      intro i
      exact hx i.castSucc

/-- Helper for Theorem 3.37: membership in a weighted finite sum of subdifferentials can be
unpacked into explicit subgradient witnesses indexed by `Fin m`. -/
private theorem existsWeightedSubgradientFamily_of_mem_sum
    {m : ℕ} {g : Fin m → E → ℝ} {xstar : E}
    {lambda : Fin m → ℝ} {z : StrongDual ℝ E}
    (hz : z ∈ ∑ i : Fin m, lambda i • subdifferentialAt (g i) xstar) :
    ∃ phi : Fin m → StrongDual ℝ E,
      (∀ i : Fin m, phi i ∈ subdifferentialAt (g i) xstar) ∧
        ∑ i : Fin m, lambda i • phi i = z := by
  induction m generalizing z with
  | zero =>
      -- The empty Minkowski sum contains only `0`, so the witness family is empty.
      simp at hz
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simpa using hz.symm
  | succ m ih =>
      -- Peel off the last constraint term, unpack the prefix recursively, then rebuild the family.
      rw [Fin.sum_univ_castSucc, Set.mem_add] at hz
      rcases hz with ⟨zPrefix, hzPrefix, zLast, hzLast, hzEq⟩
      rcases ih hzPrefix with ⟨phiPrefix, hphiPrefix_mem, hphiPrefix_sum⟩
      rw [Set.mem_smul_set] at hzLast
      rcases hzLast with ⟨phiLast, hphiLast_mem, hzLastEq⟩
      refine ⟨fun i ↦ Fin.lastCases phiLast (fun j ↦ phiPrefix j) i, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa using hphiLast_mem
        · simpa using hphiPrefix_mem j
      · calc
          ∑ i : Fin (m + 1),
              lambda i • Fin.lastCases phiLast (fun j ↦ phiPrefix j) i
              =
                ∑ i : Fin m, lambda i.castSucc • phiPrefix i +
                  lambda (Fin.last m) • phiLast := by
                  simp [Fin.sum_univ_castSucc, Fin.lastCases]
          _ = zPrefix + zLast := by rw [hphiPrefix_sum, hzLastEq]
          _ = z := hzEq

/-- Helper for Theorem 3.37: membership in `subdifferentialAt h x` yields the usual supporting
inequality at every comparison point. -/
private theorem subgradientInequality_of_mem_subdifferentialAt
    {h : E → ℝ} {x y : E} {phi : StrongDual ℝ E}
    (hphi : phi ∈ subdifferentialAt h x) :
    h y ≥ h x + phi (y - x) := by
  -- Rewrite the strong-dual membership back to the owner subdifferential predicate.
  rw [subdifferentialAt, strongDualSubdifferential_eq_image_subdifferential] at hphi
  rcases hphi with ⟨phi', hphi', rfl⟩
  rw [mem_subdifferential, is_subgradient_at_coe_iff] at hphi'
  simpa using hphi' y

/-- Helper for Theorem 3.37: a nonzero nonnegative multiplier vector makes the weighted
constraint sum strictly negative at any strict feasible point. -/
private theorem weightedConstraintSum_lt_zero_of_strict_feasible
    {lambda : Fin m → ℝ} {x : E}
    (hx : ∀ i : Fin m, g i x < 0)
    (hlambda : ∀ i : Fin m, 0 ≤ lambda i)
    (hlambda_nonzero : ∃ i : Fin m, lambda i ≠ 0) :
    ∑ i : Fin m, lambda i * g i x < 0 := by
  rcases hlambda_nonzero with ⟨j, hj⟩
  have hj_pos : 0 < lambda j := lt_of_le_of_ne (hlambda j) (Ne.symm hj)
  have hterm_nonpos : ∀ i : Fin m, lambda i * g i x ≤ 0 := by
    intro i
    exact mul_nonpos_of_nonneg_of_nonpos (hlambda i) (le_of_lt (hx i))
  have hj_term_neg : lambda j * g j x < 0 := mul_neg_of_pos_of_neg hj_pos (hx j)
  -- Sum the coordinatewise bounds and use the strictly negative `j`-term.
  have hsum_lt : ∑ i : Fin m, lambda i * g i x < ∑ i : Fin m, (0 : ℝ) := by
    refine Finset.sum_lt_sum (fun i _ ↦ hterm_nonpos i) ?_
    exact ⟨j, by simp, hj_term_neg⟩
  simpa using hsum_lt

/-- Helper for Theorem 3.37: under Slater's condition, a Fritz-John multiplier must have
positive objective coefficient. -/
private theorem fritzJohnLambda0_ne_zero_of_slaters_condition
    {lambda0 : ℝ} {lambda : Fin m → ℝ}
    (hslater : slaters_condition g)
    (hfj : IsFritzJohnMultiplier f g xstar lambda0 lambda) :
    lambda0 ≠ 0 := by
  intro hzero
  rcases (slaters_condition_iff g).mp hslater with ⟨xbar, hxbar⟩
  have hlambda_nonzero : ∃ i : Fin m, lambda i ≠ 0 := by
    rcases hfj.not_all_zero with h0 | hlambda_nonzero
    · exact False.elim (h0 hzero)
    · exact hlambda_nonzero
  have hstrict_sum :
      ∑ i : Fin m, lambda i * g i xbar < 0 :=
    weightedConstraintSum_lt_zero_of_strict_feasible
      (g := g) hxbar hfj.nonneg hlambda_nonzero
  have hconstraint_sum_mem :
      (0 : StrongDual ℝ E) ∈ ∑ i : Fin m, lambda i • subdifferentialAt (g i) xstar := by
    have hstationarity := hfj.stationarity
    rw [Set.mem_add] at hstationarity
    rcases hstationarity with ⟨phi0Scaled, hphi0Scaled_mem, z, hz, hsum_zero⟩
    rw [Set.mem_smul_set] at hphi0Scaled_mem
    rcases hphi0Scaled_mem with ⟨phi0, hphi0_mem, hphi0Scaled_eq⟩
    have hphi0Scaled_zero : phi0Scaled = 0 := by
      simpa [hzero] using hphi0Scaled_eq.symm
    have hz_zero : z = 0 := by
      rw [hphi0Scaled_zero, zero_add] at hsum_zero
      exact hsum_zero
    simpa [hz_zero] using hz
  rcases
      existsWeightedSubgradientFamily_of_mem_sum
        (g := g) (xstar := xstar) (lambda := lambda) hconstraint_sum_mem with
    ⟨phi, hphi_mem, hphi_sum⟩
  have hweighted_support :
      ∑ i : Fin m, lambda i * (g i xstar + phi i (xbar - xstar)) ≤
        ∑ i : Fin m, lambda i * g i xbar := by
    -- Apply each subgradient inequality at the strict Slater point and sum the results.
    refine Finset.sum_le_sum ?_
    intro i hi
    exact
      mul_le_mul_of_nonneg_left
        (subgradientInequality_of_mem_subdifferentialAt
          (x := xstar) (y := xbar) (h := g i) (phi := phi i) (hphi_mem i))
        (hfj.nonneg i)
  have hconstraint_zero : ∑ i : Fin m, lambda i * g i xstar = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simpa using hfj.complementary_slackness i
  have hdual_zero :
      ∑ i : Fin m, lambda i * phi i (xbar - xstar) = 0 := by
    have hEval := congrArg (fun psi : StrongDual ℝ E ↦ psi (xbar - xstar)) hphi_sum
    simpa [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using hEval
  have hbar_nonneg : 0 ≤ ∑ i : Fin m, lambda i * g i xbar := by
    have hrewritten :
        ∑ i : Fin m, lambda i * g i xstar +
            ∑ i : Fin m, lambda i * phi i (xbar - xstar) ≤
          ∑ i : Fin m, lambda i * g i xbar := by
      simpa [mul_add, Finset.sum_add_distrib] using hweighted_support
    rw [hconstraint_zero, hdual_zero, zero_add] at hrewritten
    exact hrewritten
  linarith

-- Proof sketch: apply the Fritz-John necessary condition theorem to obtain multipliers
-- `(lambda0, lambda)`. Use the strict feasible point supplied by `hslater` and the subset
-- `strict_inequality_feasible_set g ⊆ inequality_feasible_set g` to rule out `lambda0 = 0`,
-- exactly as in the textbook contradiction argument. Normalize by dividing through by `lambda0`,
-- then package the resulting nonnegative multiplier vector as a normalized Fritz-John multiplier,
-- which is exactly the KKT condition.
/-- Theorem 3.37 (1): if `xstar` is feasible, minimizes the convex objective `f` on the
inequality-feasible set cut out by `g`, and Slater's condition holds, then there exists a KKT
multiplier vector at `xstar`. -/
theorem exists_kkt_multiplier_of_isMinOn_of_slaters_condition
    (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ i : Fin m, ConvexOn ℝ Set.univ (g i))
    (hxstar : xstar ∈ inequality_feasible_set g)
    (hmin : IsMinOn f (inequality_feasible_set g) xstar)
    (hslater : slaters_condition g) :
    ∃ lambda : Fin m → ℝ, IsKKTMultiplier f g xstar lambda := by
  rcases
      exists_fritz_john_multipliers_of_isMinOn f g xstar hf hg hxstar hmin with
    ⟨lambda0, lambda, hfj⟩
  have hlambda0_ne :
      lambda0 ≠ 0 :=
    fritzJohnLambda0_ne_zero_of_slaters_condition
      (f := f) (g := g) (xstar := xstar) hslater hfj
  let mu : Fin m → ℝ := fun i ↦ lambda0⁻¹ * lambda i
  refine ⟨mu, ?_⟩
  rw [isKKTMultiplier_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- Normalize the nonnegative Fritz-John multipliers by the positive scalar `lambda0`.
    intro i
    exact mul_nonneg (inv_nonneg.mpr hfj.lambda0_nonneg) (hfj.nonneg i)
  · -- Unpack the Fritz-John stationarity witnesses, divide the equality by `lambda0`, and
    -- reassemble the normalized KKT stationarity membership.
    have hstationarity := hfj.stationarity
    rw [Set.mem_add] at hstationarity
    rcases hstationarity with ⟨phi0Scaled, hphi0Scaled_mem, z, hz, hsum_zero⟩
    rw [Set.mem_smul_set] at hphi0Scaled_mem
    rcases hphi0Scaled_mem with ⟨phi0, hphi0_mem, hphi0Scaled_eq⟩
    rcases
        existsWeightedSubgradientFamily_of_mem_sum
          (g := g) (xstar := xstar) (lambda := lambda) hz with
      ⟨phi, hphi_mem, hphi_sum⟩
    have hfj_sum_zero :
        lambda0 • phi0 + ∑ i : Fin m, lambda i • phi i = 0 := by
      calc
        lambda0 • phi0 + ∑ i : Fin m, lambda i • phi i = phi0Scaled + z := by
          rw [hphi0Scaled_eq, hphi_sum]
        _ = 0 := hsum_zero
    have hnormalized_sum :
        phi0 + ∑ i : Fin m, mu i • phi i = 0 := by
      have hscaled :=
        congrArg (fun ψ : StrongDual ℝ E ↦ lambda0⁻¹ • ψ) hfj_sum_zero
      simpa [mu, Finset.smul_sum, smul_add, smul_smul, mul_assoc, hlambda0_ne] using hscaled
    have hphi_scaled_mem :
        ∀ i : Fin m, mu i • phi i ∈ mu i • subdifferentialAt (g i) xstar := by
      intro i
      exact Set.smul_mem_smul_set (hphi_mem i)
    have hsum_mem :
        (∑ i : Fin m, mu i • phi i) ∈
          ∑ i : Fin m, mu i • subdifferentialAt (g i) xstar :=
      mem_sum_univ_of_forall_mem (A := fun i ↦ mu i • subdifferentialAt (g i) xstar)
        (x := fun i ↦ mu i • phi i) hphi_scaled_mem
    rw [Set.mem_add]
    refine ⟨phi0, hphi0_mem, ∑ i : Fin m, mu i • phi i, hsum_mem, ?_⟩
    simpa [hnormalized_sum]
  · -- Complementary slackness survives the same normalization.
    intro i
    have hscaled :=
      congrArg (fun t : ℝ ↦ lambda0⁻¹ * t) (hfj.complementary_slackness i)
    simpa [mu, mul_assoc] using hscaled

-- Proof sketch: form the convex Lagrangian objective
-- `h x = f x + ∑ i, lambda i * g i x`. The KKT stationarity assumption says
-- `0 ∈ ∂ h(xstar)` after the finite-dimensional sum rule for subdifferentials, so Fermat's rule
-- yields that `xstar` globally minimizes `h`. For any feasible `x`, the nonnegativity of
-- `lambda` and the inequalities `g i x ≤ 0` show `h x ≤ f x`, while complementary slackness gives
-- `h xstar = f xstar`; hence `f xstar ≤ f x` on the feasible set. The separate feasibility
-- hypothesis `hxstar` records the primal-feasibility part of the KKT conclusion.
/-- Theorem 3.37 (2): a feasible point `xstar` satisfying the KKT conditions for some multiplier
vector `lambda` is an optimal solution of the convex inequality-constrained problem. -/
theorem isMinOn_of_mem_inequality_feasible_set_of_isKKTMultiplier
    (lambda : Fin m → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ i : Fin m, ConvexOn ℝ Set.univ (g i))
    (hxstar : xstar ∈ inequality_feasible_set g)
    (hlambda : IsKKTMultiplier f g xstar lambda) :
    IsMinOn f (inequality_feasible_set g) xstar := by
  rw [isMinOn_iff]
  intro x hx
  have hx_feasible : ∀ i : Fin m, g i x ≤ 0 := by
    simpa [mem_inequality_feasible_set] using hx
  have hstationarity_mem := hlambda.stationarity
  rw [Set.mem_add] at hstationarity_mem
  rcases hstationarity_mem with ⟨phi0, hphi0_mem, z, hz, hstationarity⟩
  rcases
      existsWeightedSubgradientFamily_of_mem_sum
        (g := g) (xstar := xstar) (lambda := lambda) hz with
    ⟨phi, hphi_mem, hphi_sum⟩
  have hobjective_support :
      f x ≥ f xstar + phi0 (x - xstar) :=
    subgradientInequality_of_mem_subdifferentialAt
      (x := xstar) (y := x) (h := f) (phi := phi0) hphi0_mem
  have hweighted_support :
      ∑ i : Fin m, lambda i * (g i xstar + phi i (x - xstar)) ≤
        ∑ i : Fin m, lambda i * g i x := by
    -- Sum the constraint-side subgradient inequalities after multiplying by `lambda i ≥ 0`.
    refine Finset.sum_le_sum ?_
    intro i hi
    exact
      mul_le_mul_of_nonneg_left
        (subgradientInequality_of_mem_subdifferentialAt
          (x := xstar) (y := x) (h := g i) (phi := phi i) (hphi_mem i))
        (hlambda.nonneg i)
  have hconstraint_zero : ∑ i : Fin m, lambda i * g i xstar = 0 := by
    -- Complementary slackness forces every weighted constraint term at `xstar` to vanish.
    refine Finset.sum_eq_zero ?_
    intro i hi
    simpa using hlambda.complementary_slackness i
  have hconstraint_nonpos : ∑ i : Fin m, lambda i * g i x ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hlambda.nonneg i) (hx_feasible i)
  have hdual_nonpos : ∑ i : Fin m, lambda i * phi i (x - xstar) ≤ 0 := by
    have hrewritten :
        ∑ i : Fin m, lambda i * g i xstar +
            ∑ i : Fin m, lambda i * phi i (x - xstar) ≤
          ∑ i : Fin m, lambda i * g i x := by
      simpa [mul_add, Finset.sum_add_distrib] using hweighted_support
    rw [hconstraint_zero] at hrewritten
    linarith
  have hstationarity_zero :
      phi0 (x - xstar) + ∑ i : Fin m, lambda i * phi i (x - xstar) = 0 := by
    have hsum_zero :
        phi0 + ∑ i : Fin m, lambda i • phi i = 0 := by
      calc
        phi0 + ∑ i : Fin m, lambda i • phi i = phi0 + z := by rw [hphi_sum]
        _ = 0 := hstationarity
    have hEval := congrArg (fun psi : StrongDual ℝ E ↦ psi (x - xstar)) hsum_zero
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using hEval
  have hphi0_nonneg : 0 ≤ phi0 (x - xstar) := by
    linarith
  -- Combine the objective supporting inequality with the nonnegativity forced by stationarity.
  linarith

end ConvexProblemContext

end
