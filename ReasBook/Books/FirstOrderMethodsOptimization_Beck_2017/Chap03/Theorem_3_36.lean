/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Data.Fintype.Order
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_5
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_22
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.36 is `source-facing` in the chapter's inequality-constrained convex-optimality API.
Its `core/canonical` owner notions already exist upstream:
1. `subdifferentialAt` from Theorem 3.4 for real-valued subgradients;
2. `inequality_feasible_set` from Lemma 3.5 for the feasible set;
3. `optimality_residual` from Lemma 3.5 for the canonical finite-maximum residual objective.
The primitive source-facing data here are only the scalar/vector multipliers together with the
textbook Fritz-John conditions they satisfy, so this file keeps those conditions as a plain
predicate and reuses the owner declarations directly. -/
recall subdifferentialAt
recall inequality_feasible_set
recall optimality_residual

/-- A scalar `lambda0` together with inequality multipliers `lambda` satisfies the Fritz-John
conditions for the convex problem with objective `f`, constraints `g`, and candidate optimizer
`xstar` when the multipliers are nonnegative, not all zero, satisfy the subdifferential
stationarity condition, and obey complementary slackness. -/
def IsFritzJohnMultiplier
    {m : ℕ} (f : E → ℝ) (g : Fin m → E → ℝ) (xstar : E)
    (lambda0 : ℝ) (lambda : Fin m → ℝ) : Prop :=
    0 ≤ lambda0 ∧
      (∀ i, 0 ≤ lambda i) ∧
      (lambda0 ≠ 0 ∨ ∃ i : Fin m, lambda i ≠ 0) ∧
      (0 : StrongDual ℝ E) ∈
          lambda0 • subdifferentialAt f xstar + ∑ i, lambda i • subdifferentialAt (g i) xstar ∧
        ∀ i, lambda i * g i xstar = 0

/-- Unfolding `IsFritzJohnMultiplier` gives exactly the textbook Fritz-John multiplier
conditions. -/
@[simp] theorem isFritzJohnMultiplier_iff
    {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {xstar : E}
    {lambda0 : ℝ} {lambda : Fin m → ℝ} :
    IsFritzJohnMultiplier f g xstar lambda0 lambda ↔
      0 ≤ lambda0 ∧
        (∀ i, 0 ≤ lambda i) ∧
        (lambda0 ≠ 0 ∨ ∃ i : Fin m, lambda i ≠ 0) ∧
        (0 : StrongDual ℝ E) ∈
            lambda0 • subdifferentialAt f xstar + ∑ i, lambda i • subdifferentialAt (g i) xstar ∧
          ∀ i, lambda i * g i xstar = 0 :=
  Iff.rfl

/-- Every Fritz-John multiplier has nonnegative scalar coefficient. -/
theorem IsFritzJohnMultiplier.lambda0_nonneg
    {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {xstar : E}
    {lambda0 : ℝ} {lambda : Fin m → ℝ}
    (h : IsFritzJohnMultiplier f g xstar lambda0 lambda) :
    0 ≤ lambda0 :=
  h.1

/-- Every Fritz-John multiplier vector is componentwise nonnegative. -/
theorem IsFritzJohnMultiplier.nonneg
    {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {xstar : E}
    {lambda0 : ℝ} {lambda : Fin m → ℝ}
    (h : IsFritzJohnMultiplier f g xstar lambda0 lambda) :
    ∀ i, 0 ≤ lambda i :=
  h.2.1

/-- A Fritz-John multiplier family is not identically zero. -/
theorem IsFritzJohnMultiplier.not_all_zero
    {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {xstar : E}
    {lambda0 : ℝ} {lambda : Fin m → ℝ}
    (h : IsFritzJohnMultiplier f g xstar lambda0 lambda) :
    lambda0 ≠ 0 ∨ ∃ i : Fin m, lambda i ≠ 0 :=
  h.2.2.1

/-- A Fritz-John multiplier family satisfies the subdifferential stationarity condition. -/
theorem IsFritzJohnMultiplier.stationarity
    {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {xstar : E}
    {lambda0 : ℝ} {lambda : Fin m → ℝ}
    (h : IsFritzJohnMultiplier f g xstar lambda0 lambda) :
    (0 : StrongDual ℝ E) ∈
        lambda0 • subdifferentialAt f xstar + ∑ i, lambda i • subdifferentialAt (g i) xstar :=
  h.2.2.2.1

/-- A Fritz-John multiplier family satisfies complementary slackness. -/
theorem IsFritzJohnMultiplier.complementary_slackness
    {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {xstar : E}
    {lambda0 : ℝ} {lambda : Fin m → ℝ}
    (h : IsFritzJohnMultiplier f g xstar lambda0 lambda) :
    ∀ i, lambda i * g i xstar = 0 :=
  h.2.2.2.2

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall is_convex_function_iff_convexOn_toReal
recall subdifferential
recall mem_subdifferential
recall is_subgradient_at_coe_iff
recall isMinOn_univ_iff_zero_mem_subdifferentialAt
recall isMinOn_univ_iff_zero_mem_subdifferential
recall subdifferential_pointwise_max_eq_convexHull_iUnion_active_subdifferential

/-- Helper for Theorem 3.36: subtracting a scalar constant does not change the real-valued
subdifferential at a point. -/
theorem subdifferentialAtSubConstEq
    (f : E → ℝ) (c : ℝ) (x : E) :
    subdifferentialAt (fun y ↦ f y - c) x = subdifferentialAt f x := by
  -- Rewrite both sides to the real-valued owner predicate and cancel the constant shift.
  ext φ
  change
    ((φ : Module.Dual ℝ E) ∈
        subdifferential (fun y ↦ ((f y - c : ℝ) : EReal)) x) ↔
      ((φ : Module.Dual ℝ E) ∈
        subdifferential (fun y ↦ (f y : EReal)) x)
  rw [mem_subdifferential, mem_subdifferential]
  rw [is_subgradient_at_coe_iff, is_subgradient_at_coe_iff]
  constructor
  · intro h y
    have hy := h y
    linarith
  · intro h y
    have hy := h y
    linarith

/-- Helper for Theorem 3.36: an optimal feasible point globally minimizes the residual objective
`optimality_residual f (f xstar) g`. -/
theorem isMinOnOptimalityResidualAtOptimalSolution
    {m : ℕ} (f : E → ℝ) (g : Fin m → E → ℝ) (xstar : E)
    (hxstar : xstar ∈ inequality_feasible_set g)
    (hmin : IsMinOn f (inequality_feasible_set g) xstar) :
    IsMinOn (optimality_residual f (f xstar) g) Set.univ xstar := by
  -- First package `f xstar` as the least feasible objective value.
  have hleast : IsLeast (f '' inequality_feasible_set g) (f xstar) := by
    refine ⟨⟨xstar, hxstar, rfl⟩, ?_⟩
    rw [isMinOn_iff] at hmin
    rintro _ ⟨y, hy, rfl⟩
    exact hmin y hy
  -- Then invoke the residual reformulation from Lemma 3.5.
  exact
    (isMinOn_optimality_residual_univ_iff
      (f := f) (fbar := f xstar) (g := g) hleast xstar).mp
      ⟨hxstar, hmin⟩

/-- Helper for Theorem 3.36: the coerced residual objective is the pointwise supremum of its
explicit residual-coordinate branch family. -/
theorem residualPointwiseSupEqBranchFamily
    {m : ℕ} (f : E → ℝ) (g : Fin m → E → ℝ) (xstar : E) :
    (fun y ↦ ((optimality_residual f (f xstar) g y : ℝ) : EReal)) =
      fun y ↦
        ⨆ i : Fin (m + 1),
          ((optimality_residual_coordinates f (f xstar) g y i : ℝ) : EReal) := by
  -- Compare the finite supremum with its `EReal`-coerced coordinates in both directions.
  funext y
  rw [optimality_residual, coordinatewiseMax_eq_sup']
  rw [Finset.sup'_univ_eq_ciSup]
  apply le_antisymm
  · rcases
      exists_eq_ciSup_of_finite
        (f := optimality_residual_coordinates f (f xstar) g y) with ⟨i, hi⟩
    rw [← hi]
    exact le_iSup (fun i : Fin (m + 1) ↦
      ((optimality_residual_coordinates f (f xstar) g y i : ℝ) : EReal)) i
  · refine iSup_le ?_
    intro i
    exact_mod_cast
      (Finite.le_ciSup_of_le i le_rfl :
        optimality_residual_coordinates f (f xstar) g y i ≤
          ⨆ j : Fin (m + 1), optimality_residual_coordinates f (f xstar) g y j)

/-- Helper for Theorem 3.36: at a feasible optimizer, the residual branch supremum at `xstar`
is zero. -/
theorem residualBranchSupAtOptimal_eq_zero
    {m : ℕ} (f : E → ℝ) (g : Fin m → E → ℝ) (xstar : E)
    (hxstar : xstar ∈ inequality_feasible_set g) :
    ⨆ j : Fin (m + 1),
        ((optimality_residual_coordinates f (f xstar) g xstar j : ℝ) : EReal) = 0 := by
  -- Evaluate the residual/branch-family normal form at `xstar` and then use feasibility.
  have hresidual :
      optimality_residual f (f xstar) g xstar = 0 :=
    optimality_residual_eq_zero_of_feasible_of_eq_fbar
      (f := f) (fbar := f xstar) (g := g) xstar hxstar rfl
  have hbranch :
      ((optimality_residual f (f xstar) g xstar : ℝ) : EReal) =
        ⨆ j : Fin (m + 1),
          ((optimality_residual_coordinates f (f xstar) g xstar j : ℝ) : EReal) := by
    simpa using
      congrArg (fun h : E → EReal ↦ h xstar)
        (residualPointwiseSupEqBranchFamily (f := f) (g := g) (xstar := xstar))
  simpa [hresidual] using hbranch.symm

/-- Helper for Theorem 3.36: pointwise witnesses for a `Fin n`-indexed family of sets assemble
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
      -- Split the last coordinate from the first `n` coordinates and use `Set.mem_add`.
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Set.mem_add]
      refine ⟨∑ i : Fin n, x i.castSucc, ih ?_, x (Fin.last n), hx (Fin.last n), rfl⟩
      intro i
      exact hx i.castSucc

/-- Helper for Theorem 3.36: the zero dual vector belongs to the convex hull of the active
subdifferentials of the residual branches at the optimal solution. -/
theorem zero_mem_convexHull_activeResidualSubdifferential
    {m : ℕ} (f : E → ℝ) (g : Fin m → E → ℝ) (xstar : E)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i : Fin m, ConvexOn ℝ Set.univ (g i))
    (hxstar : xstar ∈ inequality_feasible_set g)
    (hmin : IsMinOn f (inequality_feasible_set g) xstar) :
    (0 : Module.Dual ℝ E) ∈
      convexHull ℝ
        (⋃ i :
          {i : Fin (m + 1) //
            ((optimality_residual_coordinates f (f xstar) g xstar i : ℝ) : EReal) =
              ⨆ j : Fin (m + 1),
                ((optimality_residual_coordinates f (f xstar) g xstar j : ℝ) : EReal)},
          subdifferential
            (fun y ↦
              ((optimality_residual_coordinates f (f xstar) g y i : ℝ) : EReal))
            xstar) := by
  let r : Fin (m + 1) → E → EReal :=
    fun i y ↦ ((optimality_residual_coordinates f (f xstar) g y i : ℝ) : EReal)
  -- Route correction: the previous route stalled because the residual objective was still spelled
  -- as a real-valued `coordinatewiseMax`; first freeze the owner branch family `r`.
  have hresidualMin :
      IsMinOn (optimality_residual f (f xstar) g) Set.univ xstar :=
    isMinOnOptimalityResidualAtOptimalSolution f g xstar hxstar hmin
  have hresidualMinEReal :
      IsMinOn (fun y ↦ ((optimality_residual f (f xstar) g y : ℝ) : EReal)) Set.univ xstar := by
    -- Coercing a real-valued minimizer into `EReal` preserves the same global order relation.
    simpa [isMinOn_univ_iff] using hresidualMin
  have hzero_mem :
      (0 : Module.Dual ℝ E) ∈
        subdifferential (fun y ↦ ((optimality_residual f (f xstar) g y : ℝ) : EReal)) xstar := by
    -- Apply Fermat's criterion to the everywhere-finite residual objective.
    have hdom :
        (effective_domain fun y ↦
          ((optimality_residual f (f xstar) g y : ℝ) : EReal)).Nonempty := by
      refine ⟨xstar, ?_⟩
      simp [effective_domain]
    exact
      (isMinOn_univ_iff_zero_mem_subdifferential
        (f := fun y ↦ ((optimality_residual f (f xstar) g y : ℝ) : EReal)) hdom).mp
        hresidualMinEReal
  have hconvex_constraints :
      ∀ j : Fin m, is_convex_function (r j.castSucc) := by
    -- Each constraint branch is just the coercion of the convex constraint `g j`.
    intro j
    have hbranch : is_convex_function (fun y ↦ ((g j y : ℝ) : EReal)) := by
      refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
      · intro y hy
        exact EReal.coe_ne_bot _
      · simpa [effective_domain] using hg j
    simpa [r] using hbranch
  have hconvex_last : is_convex_function (r (Fin.last m)) := by
    -- The last branch is the objective gap `f - f xstar`.
    have hgap : ConvexOn ℝ Set.univ (fun y ↦ f y - f xstar) := by
      simpa [sub_eq_add_neg] using hf.add_const (-f xstar)
    have hbranch : is_convex_function (fun y ↦ ((f y : EReal) - (f xstar : EReal))) := by
      refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
      · intro y hy
        simpa [EReal.coe_sub] using (EReal.coe_ne_bot (f y - f xstar))
      · have hdomain :
            effective_domain (fun y ↦ ((f y : EReal) - (f xstar : EReal))) = Set.univ := by
          ext y
          simpa [effective_domain, EReal.coe_sub] using
            (EReal.coe_lt_top (f y - f xstar))
        rw [hdomain]
        simpa [EReal.toReal_sub, EReal.coe_ne_top, EReal.coe_ne_bot] using hgap
    simpa [r, EReal.coe_sub] using hbranch
  have hconvex_r : ∀ i : Fin (m + 1), is_convex_function (r i) := by
    -- Split the finite branch index into the constraint coordinates and the final objective one.
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with (⟨j, rfl⟩ | rfl)
    · exact hconvex_constraints j
    · exact hconvex_last
  have h_ne_bot_r : ∀ i : Fin (m + 1), ∀ y : E, r i y ≠ ⊥ := by
    -- Every branch is real-valued, so `⊥` never occurs.
    intro i y
    simp [r]
  have hxInterior : xstar ∈ ⋂ i : Fin (m + 1), interior (effective_domain (r i)) := by
    -- Real-valued branches have full effective domain.
    simp [r, effective_domain]
  have hsubEq :
      subdifferential (fun y ↦ ((optimality_residual f (f xstar) g y : ℝ) : EReal)) xstar =
        convexHull ℝ
          (⋃ i :
            {i : Fin (m + 1) //
              r i xstar = ⨆ j : Fin (m + 1), r j xstar},
            subdifferential (r i) xstar) := by
    -- Rewrite the residual objective to the frozen branch family and invoke the max rule.
    rw [residualPointwiseSupEqBranchFamily (f := f) (g := g) (xstar := xstar)]
    exact
      subdifferential_pointwise_max_eq_convexHull_iUnion_active_subdifferential
        r xstar h_ne_bot_r hconvex_r hxInterior
  -- Transport the Fermat subgradient membership through the max-rule identification.
  rw [hsubEq] at hzero_mem
  simpa [r] using hzero_mem

-- Proof sketch: set `F := optimality_residual f (f xstar) g`. By Lemma 3.5, the feasible
-- minimality of `xstar` for `f` is equivalent to global minimality of `F`, and `F xstar = 0`.
-- Apply Fermat's rule to obtain `0 ∈ ∂F(xstar)`, then use the finite max-rule for
-- subdifferentials in the owner coordinate presentation of `optimality_residual` to write `0` as
-- a convex combination of active subgradients. Separate the last coordinate, corresponding to
-- `f - f xstar`, from the constraint coordinates and extend inactive multipliers by `0` to obtain
-- the Fritz-John coefficients and complementary slackness.
/-- Theorem 3.36: Fritz-John necessary optimality conditions. If `xstar` is a feasible optimal
solution of the convex problem `min f x` subject to `g i x ≤ 0` for all `i`, then there exist
nonnegative multipliers `lambda0` and `lambda` that are not all zero and satisfy the
subdifferential stationarity condition together with complementary slackness at `xstar`. -/
theorem exists_fritz_john_multipliers_of_isMinOn
    {m : ℕ} (f : E → ℝ) (g : Fin m → E → ℝ) (xstar : E)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i : Fin m, ConvexOn ℝ Set.univ (g i))
    (hxstar : xstar ∈ inequality_feasible_set g)
    (hmin : IsMinOn f (inequality_feasible_set g) xstar) :
    ∃ (lambda0 : ℝ) (lambda : Fin m → ℝ),
      IsFritzJohnMultiplier f g xstar lambda0 lambda := by
  let r : Fin (m + 1) → E → EReal :=
    fun i y ↦ ((optimality_residual_coordinates f (f xstar) g y i : ℝ) : EReal)
  let active : Fin (m + 1) → Prop :=
    fun i => r i xstar = ⨆ j : Fin (m + 1), r j xstar
  -- Reduce the theorem to the active-branch convex-hull representation of the residual problem.
  have hactiveHull :
      (0 : Module.Dual ℝ E) ∈
        convexHull ℝ
          (⋃ i :
            {i : Fin (m + 1) // active i},
            subdifferential
              (fun y ↦
                r i y)
              xstar) :=
    by
      simpa [r, active] using
        zero_mem_convexHull_activeResidualSubdifferential
          f g xstar hf hg hxstar hmin
  have hsup_zero :
      ⨆ j : Fin (m + 1), r j xstar = 0 := by
    -- Normalize the active-value threshold to the residual value `0` at the optimizer.
    simpa [r] using residualBranchSupAtOptimal_eq_zero (f := f) (g := g) (xstar := xstar) hxstar
  -- Route correction: first flatten the active convex-hull witness into explicit sample data.
  rw [mem_convexHull_iff_exists_fintype] at hactiveHull
  rcases hactiveHull with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz_mem, hsum_zero⟩
  have hz_branch :
      ∀ a, ∃ i : Fin (m + 1), active i ∧ z a ∈ subdifferential (r i) xstar := by
    intro a
    simpa using hz_mem a
  choose k hk_active hz_sub using hz_branch
  classical
  let s : Fin (m + 1) → Finset ι := fun i ↦ Finset.univ.filter (fun a ↦ k a = i)
  let lam : Fin (m + 1) → ℝ := fun i ↦ Finset.sum (s i) fun a ↦ w a
  let uBranch : Fin (m + 1) → Module.Dual ℝ E := fun i ↦ Finset.sum (s i) fun a ↦ w a • z a
  have hlam_nonneg : ∀ i, 0 ≤ lam i := by
    -- Each branch coefficient is a sum of nonnegative convex-hull weights.
    intro i
    unfold lam s
    exact Finset.sum_nonneg fun a ha ↦ hw_nonneg a
  have hlam_sum : ∑ i : Fin (m + 1), lam i = 1 := by
    -- Reindex the sample weights by their branch label.
    have hfiber :
        ∑ i : Fin (m + 1), lam i = ∑ a : ι, w a := by
      unfold lam s
      simpa using
      (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset ι))
        (t := (Finset.univ : Finset (Fin (m + 1))))
        (g := k)
        (h := fun a ha ↦ by simp)
        (f := w))
    exact hfiber.trans hw_sum
  have huBranch_sum_zero : ∑ i : Fin (m + 1), uBranch i = 0 := by
    -- Reindex the sample subgradient sum by the same branch partition.
    have hfiber :
        ∑ i : Fin (m + 1), uBranch i = ∑ a : ι, w a • z a := by
      unfold uBranch s
      simpa using
      (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset ι))
        (t := (Finset.univ : Finset (Fin (m + 1))))
        (g := k)
        (h := fun a ha ↦ by simp)
        (f := fun a ↦ w a • z a))
    exact hfiber.trans hsum_zero
  have hlam_inactive : ∀ i, ¬ active i → lam i = 0 := by
    -- An inactive branch receives no samples from the active union witness.
    intro i hi
    unfold lam s
    refine Finset.sum_eq_zero ?_
    intro a ha
    exfalso
    exact hi <| by
      have hki : k a = i := (Finset.mem_filter.mp ha).2
      simpa [hki] using hk_active a
  have hbranch_nonempty : ∀ i : Fin (m + 1), (subdifferential (r i) xstar).Nonempty := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with (⟨j, rfl⟩ | rfl)
    · -- Constraint branches are the real-valued constraints viewed in `EReal`.
      rcases subdifferentialAt_nonempty_of_convexOn (f := g j) (hf := hg j) xstar with ⟨ξ, hξ⟩
      rw [subdifferentialAt, strongDualSubdifferential_eq_image_subdifferential] at hξ
      have himage :
          ξ ∈
            (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
              subdifferential (fun y ↦ ((g j y : ℝ) : EReal)) xstar := hξ
      rcases himage with ⟨φ, hφ, _⟩
      exact ⟨φ, by simpa [r] using hφ⟩
    · -- The last branch is the shifted objective `f - f xstar`.
      have hgap : ConvexOn ℝ Set.univ (fun y ↦ f y - f xstar) := by
        simpa [sub_eq_add_neg] using hf.add_const (-f xstar)
      rcases
          subdifferentialAt_nonempty_of_convexOn
            (f := fun y ↦ f y - f xstar) (hf := hgap) xstar with
        ⟨ξ, hξ⟩
      rw [subdifferentialAt, strongDualSubdifferential_eq_image_subdifferential] at hξ
      have himage :
          ξ ∈
            (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
              subdifferential
                (fun y ↦ (((f y - f xstar : ℝ) : ℝ) : EReal))
                xstar := hξ
      rcases himage with ⟨φ, hφ, _⟩
      exact ⟨φ, by simpa [r] using hφ⟩
  have huBranch_mem : ∀ i, uBranch i ∈ lam i • subdifferential (r i) xstar := by
    intro i
    by_cases hlam_zero : lam i = 0
    · -- If the branch total is zero, every weight on that fiber vanishes, so the branch sum is `0`.
      have hweight_zero :
          ∀ a ∈ s i, w a = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun a ha ↦ hw_nonneg a).1 <| by
          simpa [lam] using hlam_zero
      have hu_zero : uBranch i = 0 := by
        unfold uBranch
        refine Finset.sum_eq_zero ?_
        intro a ha
        rw [hweight_zero a ha, zero_smul]
      rcases hbranch_nonempty i with ⟨φ, hφ⟩
      rw [Set.mem_smul_set]
      refine ⟨φ, hφ, ?_⟩
      rw [hlam_zero, hu_zero]
      simp
    · have hlam_pos : 0 < lam i := by
        exact lt_of_le_of_ne (hlam_nonneg i) (by simpa [eq_comm] using hlam_zero)
      let ν : ι → ℝ := fun a ↦ w a / lam i
      have hν_nonneg : ∀ a ∈ s i, 0 ≤ ν a := by
        intro a ha
        exact div_nonneg (hw_nonneg a) (le_of_lt hlam_pos)
      have hν_sum : Finset.sum (s i) ν = 1 := by
        -- Normalize the positive fiber weights to a convex combination on branch `i`.
        calc
          Finset.sum (s i) ν = Finset.sum (s i) w / lam i := by
            unfold ν
            rw [Finset.sum_div]
          _ = lam i / lam i := by rw [show Finset.sum (s i) w = lam i by rfl]
          _ = 1 := div_self hlam_zero
      have havg_mem :
          Finset.sum (s i) (fun a ↦ ν a • z a) ∈ subdifferential (r i) xstar := by
        -- Average the sampled subgradients inside the convex branch subdifferential.
        refine (convex_subdifferential (r i) xstar).sum_mem (t := s i) hν_nonneg hν_sum ?_
        intro a ha
        have hki : k a = i := by
          simpa [s] using ha
        simpa [hki] using hz_sub a
      have hu_eq :
          uBranch i = lam i • Finset.sum (s i) (fun a ↦ ν a • z a) := by
        -- Pull the common branch total back out after normalizing the weights.
        unfold uBranch ν
        calc
          Finset.sum (s i) (fun a ↦ w a • z a) =
              Finset.sum (s i) (fun a ↦ lam i • ((w a / lam i) • z a)) := by
                refine Finset.sum_congr rfl ?_
                intro a ha
                have hscalar : lam i * (w a / lam i) = w a := by
                  field_simp [hlam_zero]
                rw [smul_smul, hscalar]
          _ = lam i • Finset.sum (s i) (fun a ↦ (w a / lam i) • z a) := by
            rw [Finset.smul_sum]
      rw [Set.mem_smul_set]
      exact ⟨Finset.sum (s i) (fun a ↦ ν a • z a), havg_mem, hu_eq.symm⟩
  have hu_scaled :
      ∀ i, ∃ φ : Module.Dual ℝ E, φ ∈ subdifferential (r i) xstar ∧ lam i • φ = uBranch i := by
    intro i
    simpa [Set.mem_smul_set] using huBranch_mem i
  choose φ hφ_mem hφ_eq using hu_scaled
  let φs : Fin (m + 1) → StrongDual ℝ E := fun i ↦ LinearMap.toContinuousLinearMap (φ i)
  have hφs_mem : ∀ i, φs i ∈ strongDualSubdifferential (r i) xstar := by
    intro i
    have himage :
        φs i ∈
          (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
            subdifferential (r i) xstar := by
      exact ⟨φ i, hφ_mem i, rfl⟩
    simpa [φs, strongDualSubdifferential_eq_image_subdifferential] using himage
  have hscaled_mem :
      ∀ i, lam i • φs i ∈ lam i • strongDualSubdifferential (r i) xstar := by
    intro i
    exact Set.smul_mem_smul_set (hφs_mem i)
  have hsum_owner : ∑ i : Fin (m + 1), lam i • φ i = 0 := by
    -- Replace each aggregated branch contribution by its chosen subgradient witness.
    calc
      ∑ i : Fin (m + 1), lam i • φ i = ∑ i : Fin (m + 1), uBranch i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact hφ_eq i
      _ = 0 := huBranch_sum_zero
  have hsum_strong : ∑ i : Fin (m + 1), lam i • φs i = 0 := by
    -- Transport the owner equality to the continuous-dual side in one step.
    have hmap :=
      congrArg
        (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) → StrongDual ℝ E)
        hsum_owner
    simpa [φs, map_sum, map_smul] using hmap
  have hstationarity_total :
      (0 : StrongDual ℝ E) ∈
        ∑ i : Fin (m + 1), lam i • strongDualSubdifferential (r i) xstar := by
    -- Assemble the branchwise witnesses into the full finite Minkowski sum.
    have hmem :=
      mem_sum_univ_of_forall_mem
        (A := fun i : Fin (m + 1) ↦ lam i • strongDualSubdifferential (r i) xstar)
        (x := fun i : Fin (m + 1) ↦ lam i • φs i)
        hscaled_mem
    simpa [hsum_strong] using hmem
  have hstationarity :
      (0 : StrongDual ℝ E) ∈
        lam (Fin.last m) • subdifferentialAt f xstar +
          ∑ i : Fin m, lam i.castSucc • subdifferentialAt (g i) xstar := by
    -- Split the objective branch from the constraint branches, then remove the constant shift.
    have hshifted :
        (0 : StrongDual ℝ E) ∈
          ∑ i : Fin m, lam i.castSucc • subdifferentialAt (g i) xstar +
            lam (Fin.last m) • subdifferentialAt (fun y ↦ f y - f xstar) xstar := by
      simpa [r, Fin.sum_univ_castSucc, subdifferentialAt] using hstationarity_total
    have hobjective :
        (0 : StrongDual ℝ E) ∈
          ∑ i : Fin m, lam i.castSucc • subdifferentialAt (g i) xstar +
            lam (Fin.last m) • subdifferentialAt f xstar := by
      simpa [subdifferentialAtSubConstEq] using hshifted
    simpa [add_comm] using hobjective
  have hnot_all_zero :
      lam (Fin.last m) ≠ 0 ∨ ∃ i : Fin m, lam i.castSucc ≠ 0 := by
    -- Otherwise every branch coefficient would vanish, contradicting `∑ i, λ i = 1`.
    by_contra hzero
    push Not at hzero
    have hall_zero : ∀ i : Fin (m + 1), lam i = 0 := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with (⟨j, rfl⟩ | rfl)
      · exact hzero.2 j
      · exact hzero.1
    have hsum_zero' : (∑ i : Fin (m + 1), lam i) = 0 := by
      simp [hall_zero]
    linarith [hlam_sum]
  have hcomplementary :
      ∀ i : Fin m, lam i.castSucc * g i xstar = 0 := by
    intro i
    by_cases hi : active i.castSucc
    · -- Active constraint branches have value `0` because the residual supremum is zero.
      have hgi_ereal : ((g i xstar : ℝ) : EReal) = 0 := by
        calc
          ((g i xstar : ℝ) : EReal) = r i.castSucc xstar := by simp [r]
          _ = ⨆ j : Fin (m + 1), r j xstar := hi
          _ = 0 := hsup_zero
      have hgi : g i xstar = 0 := by
        exact_mod_cast hgi_ereal
      simp [hgi]
    · -- Inactive branches already carry zero coefficient.
      simp [hlam_inactive _ hi]
  refine ⟨lam (Fin.last m), fun i ↦ lam i.castSucc, ?_⟩
  refine ⟨hlam_nonneg (Fin.last m), ?_⟩
  refine ⟨fun i ↦ hlam_nonneg i.castSucc, ?_⟩
  refine ⟨hnot_all_zero, ?_⟩
  exact ⟨hstationarity, hcomplementary⟩

end
