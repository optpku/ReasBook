/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part11

open scoped BigOperators Pointwise

section Chap06
section Section28

/-!
## Helpers for Theorem 6.28.5

We work in the dual-space subdifferential `subdifferentialAt` throughout (not the Euclideanized
variant), mirroring the proof strategy of Proposition 6.28.1 and Proposition 6.28.2.
-/

/-- Helper for Theorem 6.28.5: a convex function has a convex `0`-sublevel set. -/
lemma helperForTheorem_6_28_5_convex_sublevelSet_of_convexOn
    {n : ℕ} {constraint : (Fin n → ℝ) → ℝ}
    (hconstraint : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) constraint) :
    Convex ℝ {y : Fin n → ℝ | constraint y ≤ 0} := by
  -- We use the Jensen inequality from `ConvexOn` and close the goal by monotonicity of `≤`.
  intro x hx y hy a b ha hb hab
  have hJensen :
      constraint (a • x + b • y) ≤ a • constraint x + b • constraint y :=
    hconstraint.2 (by simp) (by simp) ha hb hab
  have hx0 : constraint x ≤ 0 := hx
  have hy0 : constraint y ≤ 0 := hy
  have hxmul : a • constraint x ≤ a • (0 : ℝ) := by
    -- Nonnegative scaling preserves `≤`.
    simpa [smul_eq_mul] using (mul_le_mul_of_nonneg_left hx0 ha)
  have hymul : b • constraint y ≤ b • (0 : ℝ) := by
    simpa [smul_eq_mul] using (mul_le_mul_of_nonneg_left hy0 hb)
  have hsumLe :
      a • constraint x + b • constraint y ≤ (0 : ℝ) := by
    -- Bound each term by `0`, then add.
    have hle : a • constraint x + b • constraint y ≤ a • (0 : ℝ) + b • (0 : ℝ) :=
      add_le_add hxmul hymul
    exact le_trans hle (by simp)
  exact le_trans hJensen hsumLe

/-- Helper for Theorem 6.28.5: Slater strict feasibility gives an `intrinsicInterior` witness for
the constraint set `{y | constraint y ≤ 0}`. -/
lemma helperForTheorem_6_28_5_slater_intrinsicInterior_witness
    {n : ℕ} {constraint : (Fin n → ℝ) → ℝ}
    (hconstraint : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) constraint)
    {xCirc : Fin n → ℝ} (hxCirc : constraint xCirc < 0) :
    xCirc ∈ intrinsicInterior ℝ {y : Fin n → ℝ | constraint y ≤ 0} := by
  -- First place `x°` in the (topological) interior using the strict inequality, then upgrade
  -- to the intrinsic interior.
  have hxInt : xCirc ∈ interior {y : Fin n → ℝ | constraint y ≤ 0} :=
    helperForProposition_6_28_2_mem_interior_sublevelSet_of_lt_zero
      (constraint := constraint) (hconstraint := hconstraint) hxCirc
  exact (interior_subset_intrinsicInterior (s := {y : Fin n → ℝ | constraint y ≤ 0})) hxInt

/-- Helper for Theorem 6.28.5: a convex real-valued function on `ℝⁿ`, coerced to `EReal`, has a
nonempty subdifferential at every point. -/
lemma helperForTheorem_6_28_5_subdifferential_coeEReal_nonempty_of_convexOn_univ
    {n : ℕ} {g : (Fin n → ℝ) → ℝ}
    (hg : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) g) (x : Fin n → ℝ) :
    Set.Nonempty (subdifferentialAt (fun y : Fin n → ℝ => ((g y : ℝ) : EReal)) x) := by
  -- Route: `g` is proper convex on `univ`, its effective domain is `univ`, hence `x` is in the
  -- relative interior of the effective domain; apply Remark 5.24.1.
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun y : Fin n → ℝ => ((g y : ℝ) : EReal)) :=
    helperForProposition_6_28_1_properConvexFunctionOn_univ_coe_of_convexOn (g := g) hg
  have hdom :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun y : Fin n → ℝ => ((g y : ℝ) : EReal)) =
        Set.univ :=
    helperForProposition_6_28_1_effectiveDomain_univ_coe_eq_univ (g := g)
  have hxInt :
      x ∈ interior
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun y : Fin n → ℝ => ((g y : ℝ) : EReal))) := by
    -- `dom = univ`, so `interior dom = univ`.
    simpa [hdom, interior_univ]
  have hxRi :
      x ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun y : Fin n → ℝ => ((g y : ℝ) : EReal))) :=
    helperForTheorem_23_4_mem_relativeInterior_of_mem_interior (n := n)
      (C :=
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun y : Fin n → ℝ => ((g y : ℝ) : EReal)))
      hxInt
  have hxSub :
      x ∈
        subdifferentialEffectiveDomain
          (fun y : Fin n → ℝ => ((g y : ℝ) : EReal)) :=
    helperForRemark_5_24_1_subdifferentiable_of_mem_relativeInterior
      (f := fun y : Fin n → ℝ => ((g y : ℝ) : EReal)) (hproper := hproper) hxRi
  exact
    (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
      (f := fun y : Fin n → ℝ => ((g y : ℝ) : EReal)) x).1 hxSub

/-- Helper for Theorem 6.28.5: if one summand in a `Fin m` Minkowski sum is empty, then the whole
sum is empty. -/
lemma helperForTheorem_6_28_5_fintype_sum_eq_empty_of_exists_eq_empty
    {α : Type*} [AddCommMonoid α] {m : ℕ} (S : Fin m → Set α) (i0 : Fin m) (hS : S i0 = ∅) :
    (∑ i : Fin m, S i) = (∅ : Set α) := by
  classical
  ext x
  constructor
  · intro hx
    rcases
        (Set.mem_fintype_sum (f := S) (a := x)).1 hx with
      ⟨parts, hparts, _hsum⟩
    have : parts i0 ∈ (∅ : Set α) := by
      simpa [hS] using hparts i0
    simpa using this
  · intro hx
    simpa using hx

/-- Helper for Theorem 6.28.5: decompose the constrained objective subdifferential into the
objective subdifferential plus the finite Minkowski sum of the indicator subdifferentials. -/
lemma helperForTheorem_6_28_5_subdifferential_indicatorReformulationObjective_eq_sum_dual
    {n m : ℕ} (f₀ : (Fin n → ℝ) → ℝ) (constraints : Fin m → (Fin n → ℝ) → ℝ)
    (hf₀ : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f₀)
    (hconstraints : ∀ i : Fin m, ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (constraints i))
    (hri :
      ∃ z : Fin n → ℝ,
        ∀ i : Fin m, z ∈ intrinsicInterior ℝ {y : Fin n → ℝ | constraints i y ≤ 0})
    (x : Fin n → ℝ) :
    subdifferentialAt (indicatorReformulationObjective f₀ constraints) x =
      (subdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x :
          Set (Module.Dual ℝ (Fin n → ℝ))) +
        ∑ i : Fin m,
          (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
            Set (Module.Dual ℝ (Fin n → ℝ))) := by
  classical
  -- Step 1: convexity of each constraint set `Cᵢ`.
  have hCconv :
      ∀ i : Fin m, Convex ℝ {y : Fin n → ℝ | constraints i y ≤ 0} := by
    intro i
    exact
      helperForTheorem_6_28_5_convex_sublevelSet_of_convexOn
        (constraint := constraints i) (hconstraint := hconstraints i)
  -- Step 2: package the objective as a `Fin (m+1)` sum so we can apply the Chapter 23 sum rule.
  let fFam : Fin (m + 1) → (Fin n → ℝ) → EReal :=
    fun j =>
      Fin.cases (motive := fun _ => (Fin n → ℝ) → EReal)
        (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal))
        (fun i : Fin m => indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) j
  have hObj :
      (fun y : Fin n → ℝ => ∑ j : Fin (m + 1), fFam j y) =
        indicatorReformulationObjective f₀ constraints := by
    -- This is the same rewrite used for Proposition 6.28.1.
    simpa [fFam] using
      (helperForProposition_6_28_1_indicatorReformulationObjective_eq_finSum
        (f₀ := f₀) (constraints := constraints))
  -- Step 3: each summand is a proper convex function on `univ`.
  have hproper : ∀ j : Fin (m + 1), ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFam j) := by
    intro j
    refine Fin.cases ?_ ?_ j
    · -- The `0`-summand is the real objective coerced to `EReal`.
      simpa [fFam] using
        (helperForProposition_6_28_1_properConvexFunctionOn_univ_coe_of_convexOn
          (g := f₀) hf₀)
    · intro i
      -- Indicator summands are proper convex thanks to convexity + nonemptiness (from `hri`).
      have hind :
          ∀ i : Fin m,
            ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
              (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) :=
        helperForProposition_6_28_1_properConvexFunctionOn_indicator_summands
          (constraints := constraints) (hconstraints := hCconv) (hri := hri)
      simpa [fFam] using hind i
  -- Step 4: build the common intrinsic-interior qualification for the effective domains.
  have hii :=
    helperForProposition_6_28_1_sumRule_qualification_for_fFam
      (f₀ := f₀) (constraints := constraints) (hri := hri)
  -- Step 5: apply the intrinsic-interior effective-domain finite-sum rule (Theorem 23.8(2)).
  have hdual :
      subdifferentialAt (fun y : Fin n → ℝ => ∑ j : Fin (m + 1), fFam j y) x =
        ∑ j : Fin (m + 1), (subdifferentialAt (fFam j) x : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    simpa using
      (subdifferential_sum_eq_sum_of_commonIntrinsicInteriorEffectiveDomain
        (f := fFam) hproper hii x)
  -- Step 6: rewrite by `hObj` and split the `Fin (m+1)` Minkowski sum into `0` plus the tail.
  have hdualObj :
      subdifferentialAt (indicatorReformulationObjective f₀ constraints) x =
        ∑ j : Fin (m + 1), (subdifferentialAt (fFam j) x : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    simpa [hObj] using hdual
  calc
    subdifferentialAt (indicatorReformulationObjective f₀ constraints) x
        = ∑ j : Fin (m + 1), (subdifferentialAt (fFam j) x : Set (Module.Dual ℝ (Fin n → ℝ))) := hdualObj
    _ = (subdifferentialAt (fFam 0) x : Set (Module.Dual ℝ (Fin n → ℝ))) +
          ∑ i : Fin m, (subdifferentialAt (fFam i.succ) x : Set (Module.Dual ℝ (Fin n → ℝ))) := by
          simpa using (Fin.sum_univ_succ (f := fun j : Fin (m + 1) =>
            (subdifferentialAt (fFam j) x : Set (Module.Dual ℝ (Fin n → ℝ)))))
    _ = (subdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x :
            Set (Module.Dual ℝ (Fin n → ℝ))) +
          ∑ i : Fin m,
            (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
              Set (Module.Dual ℝ (Fin n → ℝ))) := by
          -- Unfold `fFam` at `0` and at each `succ i`.
          simp [fFam]

-- Proof sketch: apply Proposition 6.28.1 to split the subdifferential of the indicator
-- reformulation into the subdifferential of `f₀` plus the indicator-function subdifferentials of
-- the sets `Cᵢ = {y | constraints i y ≤ 0}`. Then use Proposition 6.28.2 on each indicator term:
-- outside feasibility the active indicator subdifferential is empty, while at a feasible point
-- each indicator subdifferential is either `{0}` or a nonnegative scalar multiple of
-- `∂ constraints i (x)` according to complementary slackness. Reassembling the finite Minkowski
-- sum yields the stated union over multiplier vectors.
/-- Theorem 6.28.5: Let
`f(x) = f₀(x) + ∑ i, δ(x | Cᵢ)` with `Cᵢ = {y | constraints i y ≤ 0}`, where `f₀` and all
`constraints i` are convex on `ℝ^n`. Assume there exists a point `x°` such that
`constraints i x° < 0` for every `i`. Then for every `x`, (1) `∂f(x)` is nonempty if and only if
`x` is feasible, meaning `constraints i x ≤ 0` for all `i`; and (2) whenever `x` is feasible,
`∂f(x)` is the union over all multiplier vectors `lambda` with `lambda i ≥ 0` and
`lambda i * constraints i x = 0` of the Minkowski sums
`∂f₀(x) + lambda 1 ∂constraints 1(x) + ··· + lambda m ∂constraints m(x)`. -/
theorem subdifferential_indicatorReformulationObjective_nonempty_iff_feasible_and_eq_iUnion_multiplier_subgradient_sums
    {n m : ℕ} (f₀ : (Fin n → ℝ) → ℝ) (constraints : Fin m → (Fin n → ℝ) → ℝ)
    (hf₀ : ConvexOn ℝ Set.univ f₀)
    (hconstraints : ∀ i : Fin m, ConvexOn ℝ Set.univ (constraints i))
    (hslater : ∃ xCirc : Fin n → ℝ, ∀ i : Fin m, constraints i xCirc < 0)
    (x : Fin n → ℝ) :
    (subdifferentialAt (indicatorReformulationObjective f₀ constraints) x ≠ ∅ ↔
      ∀ i : Fin m, constraints i x ≤ 0) ∧
      ((∀ i : Fin m, constraints i x ≤ 0) →
        subdifferentialAt (indicatorReformulationObjective f₀ constraints) x =
          Set.iUnion fun lambda :
            {lambda : Fin m → ℝ // ∀ i : Fin m, 0 ≤ lambda i ∧ lambda i * constraints i x = 0} =>
              (subdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))) +
                ∑ i : Fin m,
                  (lambda.1 i) •
                    (subdifferentialAt
                      (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                        Set (Module.Dual ℝ (Fin n → ℝ)))) := by
  classical
  -- Fix a Slater witness `x°` for strict feasibility.
  rcases hslater with ⟨xCirc, hxCirc⟩

  -- Set up the constraint sets `Cᵢ = {y | constraints i y ≤ 0}` and the common intrinsic-interior point.
  have hri :
      ∃ z : Fin n → ℝ,
        ∀ i : Fin m, z ∈ intrinsicInterior ℝ {y : Fin n → ℝ | constraints i y ≤ 0} := by
    refine ⟨xCirc, ?_⟩
    intro i
    exact
      helperForTheorem_6_28_5_slater_intrinsicInterior_witness
        (constraint := constraints i) (hconstraint := hconstraints i) (hxCirc := hxCirc i)

  -- First split `∂(f₀ + ∑ δ_{Cᵢ})` into `∂ f₀` plus the finite sum of indicator subdifferentials.
  have hsplit :
      subdifferentialAt (indicatorReformulationObjective f₀ constraints) x =
        (subdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x :
            Set (Module.Dual ℝ (Fin n → ℝ))) +
          ∑ i : Fin m,
            (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
              Set (Module.Dual ℝ (Fin n → ℝ))) :=
    helperForTheorem_6_28_5_subdifferential_indicatorReformulationObjective_eq_sum_dual
      (f₀ := f₀) (constraints := constraints) (hf₀ := hf₀) (hconstraints := hconstraints) (hri := hri)
      (x := x)

  -- We will repeatedly use Proposition 6.28.2 for the individual constraints.
  have hcases :
      ∀ i : Fin m,
        subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x =
            normalConeAt {y : Fin n → ℝ | constraints i y ≤ 0} x ∧
          (constraints i x = 0 → (∃ z : Fin n → ℝ, constraints i z < 0) →
            subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x =
              Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
                a.1 •
                  subdifferentialAt (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x) ∧
          (constraints i x < 0 →
            subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x =
              ({0} : Set (Module.Dual ℝ (Fin n → ℝ)))) ∧
          (0 < constraints i x →
            subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x = ∅) := by
    intro i
    -- Nonemptiness witness for the feasible set comes from Slater.
    have hne : ∃ y : Fin n → ℝ, constraints i y ≤ 0 := ⟨xCirc, le_of_lt (hxCirc i)⟩
    exact
      subdifferential_indicator_sublevelSet_eq_normalCone_and_constraint_cases
        (constraint := constraints i) (hconstraint := hconstraints i) (hne := hne) (x := x)

  -- Part (1): `∂f(x)` is nonempty iff `x` is feasible.
  have h_nonempty_iff_feasible :
      subdifferentialAt (indicatorReformulationObjective f₀ constraints) x ≠ ∅ ↔
        ∀ i : Fin m, constraints i x ≤ 0 := by
    constructor
    · intro hnonempty i
      -- Contrapositive: if `0 < constraints i x`, then the indicator subdifferential is empty,
      -- hence the whole Minkowski sum is empty by `hsplit`.
      by_contra hle
      have hpos : 0 < constraints i x := lt_of_not_ge hle
      have hEmptyIndicator :
          subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x = ∅ :=
        (hcases i).2.2.2 hpos
      have hEmptySum :
          (∑ j : Fin m,
              (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints j y ≤ 0}) x :
                Set (Module.Dual ℝ (Fin n → ℝ)))) =
            (∅ : Set (Module.Dual ℝ (Fin n → ℝ))) :=
        helperForTheorem_6_28_5_fintype_sum_eq_empty_of_exists_eq_empty
          (S := fun j : Fin m =>
            (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints j y ≤ 0}) x :
              Set (Module.Dual ℝ (Fin n → ℝ))))
          i hEmptyIndicator
      have hEmptyTotal :
          subdifferentialAt (indicatorReformulationObjective f₀ constraints) x = ∅ := by
        -- Rewrite `∂` by `hsplit`, then simplify using `hEmptySum`.
        rw [hsplit, hEmptySum]
        simp
      exact hnonempty (by simpa [hEmptyTotal])
    · intro hfeas hEq
      -- To show nonemptiness, we explicitly build one element of the Minkowski sum given by `hsplit`.
      have hSubf0 :
          Set.Nonempty
            (subdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x) :=
        helperForTheorem_6_28_5_subdifferential_coeEReal_nonempty_of_convexOn_univ (hg := hf₀) x
      -- For each indicator summand at a feasible point, produce the element `0`.
      have hIndicatorZero :
          ∀ i : Fin m,
            (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
              subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x := by
        intro i
        have hle : constraints i x ≤ 0 := hfeas i
        rcases lt_or_eq_of_le hle with hlt | hEq0
        · -- Interior case: `constraints i x < 0` gives `∂δ_{Cᵢ}(x) = {0}`.
          have hSingleton :
              subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x =
                ({0} : Set (Module.Dual ℝ (Fin n → ℝ))) :=
            (hcases i).2.2.1 hlt
          simpa [hSingleton]
        · -- Boundary case: `constraints i x = 0` gives the conic-hull formula. Choose multiplier `0`.
          have hStrict : ∃ z : Fin n → ℝ, constraints i z < 0 := ⟨xCirc, hxCirc i⟩
          have hBoundary :
              subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x =
                Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
                  a.1 •
                    subdifferentialAt (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :=
            (hcases i).2.1 hEq0 hStrict
          -- Show `0` lies in the `t=0` summand by scaling any concrete subgradient by `0`.
          have hSubConstraint :
              Set.Nonempty
                (subdifferentialAt (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x) :=
            helperForTheorem_6_28_5_subdifferential_coeEReal_nonempty_of_convexOn_univ
              (hg := hconstraints i) x
          rcases hSubConstraint with ⟨g, hg⟩
          have hmem0 :
              (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
                (0 : ℝ) •
                  (subdifferentialAt (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                    Set (Module.Dual ℝ (Fin n → ℝ))) := by
            -- Use pointwise scalar multiplication on sets.
            have : (0 : ℝ) • g ∈ (0 : ℝ) •
                (subdifferentialAt (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))) :=
              Set.smul_mem_smul_set hg
            simpa using this
          have hmemUnion :
              (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
                Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
                  a.1 •
                    (subdifferentialAt (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                      Set (Module.Dual ℝ (Fin n → ℝ))) := by
            refine Set.mem_iUnion.2 ?_
            refine ⟨⟨0, le_rfl⟩, ?_⟩
            simpa using hmem0
          simpa [hBoundary] using hmemUnion
      -- Assemble a witness for the finite Minkowski sum of the indicator subdifferentials.
      have hIndicatorSumNonempty :
          Set.Nonempty
            (∑ i : Fin m,
              (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
                Set (Module.Dual ℝ (Fin n → ℝ)))) := by
        refine ⟨∑ i : Fin m, (0 : Module.Dual ℝ (Fin n → ℝ)), ?_⟩
        refine (Set.mem_fintype_sum
          (f := fun i : Fin m =>
            (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
              Set (Module.Dual ℝ (Fin n → ℝ))))
          (a := ∑ i : Fin m, (0 : Module.Dual ℝ (Fin n → ℝ)))).2 ?_
        refine ⟨(fun _ : Fin m => (0 : Module.Dual ℝ (Fin n → ℝ))), ?_, ?_⟩
        · intro i
          simpa using hIndicatorZero i
        · simp
      -- Now pick an element in `∂f₀(x)` and add the indicator-sum witness.
      rcases hSubf0 with ⟨g0, hg0⟩
      rcases hIndicatorSumNonempty with ⟨gInd, hgInd⟩
      have hTotalNonempty :
          Set.Nonempty (subdifferentialAt (indicatorReformulationObjective f₀ constraints) x) := by
        refine ⟨g0 + gInd, ?_⟩
        -- Use `hsplit` to reduce to membership in a Minkowski sum.
        rw [hsplit]
        refine (Set.mem_add).2 ?_
        refine ⟨g0, hg0, gInd, hgInd, rfl⟩
      exact hTotalNonempty.ne_empty hEq
  -- Part (2): at a feasible point, identify the subdifferential as a union over multipliers.
  have h_multiplier_union :
      (∀ i : Fin m, constraints i x ≤ 0) →
        subdifferentialAt (indicatorReformulationObjective f₀ constraints) x =
          Set.iUnion fun lambda :
            {lambda : Fin m → ℝ // ∀ i : Fin m, 0 ≤ lambda i ∧ lambda i * constraints i x = 0} =>
              (subdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))) +
                ∑ i : Fin m,
                  (lambda.1 i) •
                    (subdifferentialAt
                      (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                        Set (Module.Dual ℝ (Fin n → ℝ))) := by
    intro hfeas
    -- We prove set equality by membership in both directions.
    ext g
    constructor
    · intro hg
      -- Decompose `g` using `hsplit` into an objective part and indicator parts.
      have hg' :
          g ∈
            (subdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x :
                Set (Module.Dual ℝ (Fin n → ℝ))) +
              ∑ i : Fin m,
                (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))) := by
        simpa [hsplit] using hg
      rcases (Set.mem_add).1 hg' with ⟨g0, hg0, gInd, hgInd, rfl⟩
      rcases
          (Set.mem_fintype_sum
              (f := fun i : Fin m =>
                (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))))
              (a := gInd)).1 hgInd with
        ⟨partsInd, hpartsInd, hsumInd⟩
      -- For each `i`, extract a scalar multiplier `tᵢ ≥ 0` with complementary slackness and
      -- `partsInd i ∈ tᵢ • ∂(constraints i)(x)`.
      have hExists :
          ∀ i : Fin m,
            ∃ t : ℝ,
              0 ≤ t ∧ t * constraints i x = 0 ∧
                partsInd i ∈
                  t •
                    (subdifferentialAt
                        (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                      Set (Module.Dual ℝ (Fin n → ℝ))) := by
        intro i
        have hle : constraints i x ≤ 0 := hfeas i
        rcases lt_or_eq_of_le hle with hlt | hEq0
        · -- Inactive constraint: `constraints i x < 0` implies `∂δ_{Cᵢ}(x) = {0}`, so `partsInd i = 0`.
          have hSingleton :
              subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x =
                ({0} : Set (Module.Dual ℝ (Fin n → ℝ))) :=
            (hcases i).2.2.1 hlt
          have hpartEq0 : partsInd i = 0 := by
            have : partsInd i ∈ ({0} : Set (Module.Dual ℝ (Fin n → ℝ))) := by
              simpa [hSingleton] using hpartsInd i
            simpa [Set.mem_singleton_iff] using this
          -- Show `0 ∈ 0 • ∂(constraints i)(x)` using any concrete subgradient (exists by convexity).
          have hSubConstraint :
              Set.Nonempty
                (subdifferentialAt
                    (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x) :=
            helperForTheorem_6_28_5_subdifferential_coeEReal_nonempty_of_convexOn_univ
              (hg := hconstraints i) x
          rcases hSubConstraint with ⟨g', hg'⟩
          have hmem0 :
              (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
                (0 : ℝ) •
                  (subdifferentialAt
                      (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                    Set (Module.Dual ℝ (Fin n → ℝ))) := by
            have : (0 : ℝ) • g' ∈ (0 : ℝ) •
                (subdifferentialAt
                    (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))) :=
              Set.smul_mem_smul_set hg'
            simpa using this
          refine ⟨0, le_rfl, ?_, ?_⟩
          · simp
          · simpa [hpartEq0] using hmem0
        · -- Active constraint: use the boundary formula to pick `tᵢ` from the `iUnion`.
          have hStrict : ∃ z : Fin n → ℝ, constraints i z < 0 := ⟨xCirc, hxCirc i⟩
          have hBoundary :
              subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x =
                Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
                  a.1 •
                    (subdifferentialAt
                        (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                      Set (Module.Dual ℝ (Fin n → ℝ))) :=
            (hcases i).2.1 hEq0 hStrict
          have hmemUnion :
              partsInd i ∈
                Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
                  a.1 •
                    (subdifferentialAt
                        (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                      Set (Module.Dual ℝ (Fin n → ℝ))) := by
            simpa [hBoundary] using hpartsInd i
          rcases Set.mem_iUnion.1 hmemUnion with ⟨a, ha⟩
          refine ⟨a.1, a.2, ?_, ?_⟩
          · simp [hEq0]
          · exact ha
      classical
      let lambda : Fin m → ℝ := fun i => Classical.choose (hExists i)
      have hlambda :
          ∀ i : Fin m, 0 ≤ lambda i ∧ lambda i * constraints i x = 0 := by
        intro i
        exact ⟨(Classical.choose_spec (hExists i)).1, (Classical.choose_spec (hExists i)).2.1⟩
      have hpartsScaled :
          ∀ i : Fin m,
            partsInd i ∈
              (lambda i) •
                (subdifferentialAt
                    (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))) := by
        intro i
        exact (Classical.choose_spec (hExists i)).2.2
      let lambdaSub :
          {lambda : Fin m → ℝ // ∀ i : Fin m, 0 ≤ lambda i ∧ lambda i * constraints i x = 0} :=
        ⟨lambda, hlambda⟩
      have hgMul :
          gInd ∈
            ∑ i : Fin m,
              (lambda i) •
                (subdifferentialAt
                    (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))) := by
        have : (∑ i : Fin m, partsInd i) ∈
            ∑ i : Fin m,
              (lambda i) •
                (subdifferentialAt
                    (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))) := by
          refine (Set.mem_fintype_sum
            (f := fun i : Fin m =>
              (lambda i) •
                (subdifferentialAt
                    (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))))
            (a := ∑ i : Fin m, partsInd i)).2 ?_
          exact ⟨partsInd, hpartsScaled, rfl⟩
        simpa [hsumInd] using this
      have hgSum :
          g0 + gInd ∈
            (subdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x :
                Set (Module.Dual ℝ (Fin n → ℝ))) +
              ∑ i : Fin m,
                (lambdaSub.1 i) •
                  (subdifferentialAt
                      (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                    Set (Module.Dual ℝ (Fin n → ℝ))) := by
        -- `g0` is the objective component, `gInd` lies in the multiplier-scaled sum.
        refine (Set.mem_add).2 ?_
        refine ⟨g0, hg0, gInd, ?_, rfl⟩
        simpa [lambdaSub] using hgMul
      -- Finish by packaging the chosen multiplier vector into the union.
      refine Set.mem_iUnion.2 ?_
      refine ⟨lambdaSub, ?_⟩
      exact hgSum
    · intro hg
      -- Unpack the multiplier union membership and push it through `hsplit`.
      rcases Set.mem_iUnion.1 hg with ⟨lambdaSub, hgLambda⟩
      have hg' :
          g ∈
            (subdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x :
                Set (Module.Dual ℝ (Fin n → ℝ))) +
              ∑ i : Fin m,
                (lambdaSub.1 i) •
                  (subdifferentialAt
                      (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                    Set (Module.Dual ℝ (Fin n → ℝ))) := hgLambda
      rcases (Set.mem_add).1 hg' with ⟨g0, hg0, gMul, hgMul, rfl⟩
      rcases
          (Set.mem_fintype_sum
              (f := fun i : Fin m =>
                (lambdaSub.1 i) •
                  (subdifferentialAt
                      (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                    Set (Module.Dual ℝ (Fin n → ℝ))))
              (a := gMul)).1 hgMul with
        ⟨partsMul, hpartsMul, hsumMul⟩
      -- Show each scaled subgradient term lies in the corresponding indicator subdifferential.
      have hpartsIndicator :
          ∀ i : Fin m,
            partsMul i ∈
              (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
                Set (Module.Dual ℝ (Fin n → ℝ))) := by
        intro i
        have hle : constraints i x ≤ 0 := hfeas i
        rcases lt_or_eq_of_le hle with hlt | hEq0
        · -- Inactive constraint: complementarity forces `lambda i = 0`, so the scaled term is `0`,
          -- and Proposition 6.28.2 gives the singleton `{0}`.
          have hmul0 : lambdaSub.1 i * constraints i x = 0 := (lambdaSub.2 i).2
          have hxne : constraints i x ≠ 0 := ne_of_lt hlt
          have hlambda0 : lambdaSub.1 i = 0 := by
            rcases mul_eq_zero.1 hmul0 with h0 | h0
            · exact h0
            · exact (hxne h0).elim
          have hScaledZero : partsMul i = 0 := by
            -- Membership in `0 • S` forces the element to be `0`.
            have hmem0 : partsMul i ∈ (0 : ℝ) •
                (subdifferentialAt
                    (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))) := by
              simpa [hlambda0] using hpartsMul i
            rcases (Set.mem_smul_set).1 hmem0 with ⟨y, _hy, hyEq⟩
            simpa [zero_smul] using hyEq.symm
          have hSingleton :
              subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x =
                ({0} : Set (Module.Dual ℝ (Fin n → ℝ))) :=
            (hcases i).2.2.1 hlt
          simpa [hSingleton, hScaledZero]
        · -- Active constraint: use the boundary formula and pick `t = lambda i`.
          have hStrict : ∃ z : Fin n → ℝ, constraints i z < 0 := ⟨xCirc, hxCirc i⟩
          have hBoundary :
              subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x =
                Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
                  a.1 •
                    (subdifferentialAt (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                      Set (Module.Dual ℝ (Fin n → ℝ))) :=
            (hcases i).2.1 hEq0 hStrict
          have hnonneg : 0 ≤ lambdaSub.1 i := (lambdaSub.2 i).1
          have hmem :
              partsMul i ∈
                (lambdaSub.1 i) •
                  (subdifferentialAt (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                    Set (Module.Dual ℝ (Fin n → ℝ))) := hpartsMul i
          have hmemUnion :
              partsMul i ∈
                Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
                  a.1 •
                    (subdifferentialAt (fun y : Fin n → ℝ => ((constraints i y : ℝ) : EReal)) x :
                      Set (Module.Dual ℝ (Fin n → ℝ))) := by
            refine Set.mem_iUnion.2 ?_
            refine ⟨⟨lambdaSub.1 i, hnonneg⟩, ?_⟩
            simpa using hmem
          simpa [hBoundary] using hmemUnion
      -- Rebuild membership in the indicator Minkowski sum, then in the full objective subdifferential via `hsplit`.
      have hgInd :
          (∑ i : Fin m, partsMul i) ∈
            ∑ i : Fin m,
              (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
                Set (Module.Dual ℝ (Fin n → ℝ))) := by
        refine (Set.mem_fintype_sum
          (f := fun i : Fin m =>
            (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
              Set (Module.Dual ℝ (Fin n → ℝ))))
          (a := ∑ i : Fin m, partsMul i)).2 ?_
        exact ⟨partsMul, hpartsIndicator, rfl⟩
      have hgSum :
          g0 + (∑ i : Fin m, partsMul i) ∈
            (subdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x :
                Set (Module.Dual ℝ (Fin n → ℝ))) +
              ∑ i : Fin m,
                (subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
                  Set (Module.Dual ℝ (Fin n → ℝ))) := by
        refine (Set.mem_add).2 ?_
        refine ⟨g0, hg0, (∑ i : Fin m, partsMul i), hgInd, rfl⟩
      -- Finally, use `hsplit` to return to the original subdifferential.
      simpa [hsplit, hsumMul] using hgSum
  exact And.intro h_nonempty_iff_feasible h_multiplier_union

/-- The infimum of the Lagrangian of `P` over the primal variable for a fixed multiplier
vector. -/
noncomputable def BookOrdinaryConvexProgram.lagrangianPrimalInf {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ) : EReal :=
  sInf (Set.range fun x : Fin n → ℝ => P.lagrangian uStar x)

/-- The maximized primal infimum `sup_u inf_x L(u, x)` of the Lagrangian of `P`. -/
noncomputable def BookOrdinaryConvexProgram.lagrangianMaximin {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) : EReal :=
  sSup (Set.range fun u : Fin m → ℝ => P.lagrangianPrimalInf u)

/-- The minimized dual supremum `inf_x sup_u L(u, x)` of the Lagrangian of `P`. -/
noncomputable def BookOrdinaryConvexProgram.lagrangianMinimax {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) : EReal :=
  sInf (Set.range fun x : Fin n → ℝ =>
    sSup (Set.range fun u : Fin m → ℝ => P.lagrangian u x))

/-- Helper for Theorem 6.28.6: every Lagrangian value dominates the fixed-multiplier primal
infimum for the same multiplier. -/
lemma helperForTheorem_6_28_6_lagrangianPrimalInf_le_lagrangian
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (u : Fin m → ℝ) (x : Fin n → ℝ) :
    P.lagrangianPrimalInf u ≤ P.lagrangian u x := by
  -- The value at `x` belongs to the range defining `inf_x L(u, x)`.
  rw [BookOrdinaryConvexProgram.lagrangianPrimalInf]
  exact sInf_le ⟨x, rfl⟩

/-- Helper for Theorem 6.28.6: weak duality bounds every fixed-multiplier primal infimum above by
`P.optimalValue`. -/
lemma helperForTheorem_6_28_6_lagrangianPrimalInf_le_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (u : Fin m → ℝ) :
    P.lagrangianPrimalInf u ≤ P.optimalValue := by
  -- Compare `inf_x L(u, x)` against each feasible objective value and then infimize over the
  -- feasible set.
  rw [BookOrdinaryConvexProgram.optimalValue]
  refine le_sInf ?_
  rintro _ ⟨x, hxFeasible, rfl⟩
  have hLag_le : P.lagrangianPrimalInf u ≤ P.lagrangian u x :=
    helperForTheorem_6_28_6_lagrangianPrimalInf_le_lagrangian P u x
  by_cases hu : u ∈ P.lagrangeMultiplierSet
  · have hxC : x ∈ P.constraintSet := hxFeasible.1
    have hL_eq : P.lagrangian u x = (P.kuhnTuckerObjective u x : EReal) := by
      -- On the feasible branch and inside the multiplier cone, the Lagrangian is the weighted
      -- objective.
      simp [BookOrdinaryConvexProgram.lagrangian, hxC, hu]
    have hu_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers u i := by
      simpa [BookOrdinaryConvexProgram.lagrangeMultiplierSet] using hu
    have hkuhn_le_obj : P.kuhnTuckerObjective u x ≤ P.objective x :=
      helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible P u hxFeasible
        hu_nonneg
    have hL_le_obj : P.lagrangian u x ≤ ((P.objective x : ℝ) : EReal) := by
      simpa [hL_eq] using
        (show ((P.kuhnTuckerObjective u x : ℝ) : EReal) ≤ ((P.objective x : ℝ) : EReal) from
          EReal.coe_le_coe_iff.2 hkuhn_le_obj)
    exact le_trans hLag_le hL_le_obj
  · have hxC : x ∈ P.constraintSet := hxFeasible.1
    have hL_eq : P.lagrangian u x = (⊥ : EReal) := by
      -- Outside the multiplier cone, the Lagrangian collapses to `-∞` on `constraintSet`.
      simp [BookOrdinaryConvexProgram.lagrangian, hxC, hu]
    have hLag_le_bot : P.lagrangianPrimalInf u ≤ (⊥ : EReal) := by
      -- Rewrite the general bound using `P.lagrangian u x = ⊥`.
      simpa [hL_eq] using hLag_le
    have hbot_le_obj : (⊥ : EReal) ≤ ((P.objective x : ℝ) : EReal) := by
      simp
    exact le_trans hLag_le_bot hbot_le_obj

/-- Helper for Theorem 6.28.6: on a feasible point, maximizing the Lagrangian over the multiplier
variable recovers the original objective value. -/
lemma helperForTheorem_6_28_6_lagrangianDualSup_eq_objective_of_feasible
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {x : Fin n → ℝ}
    (hxFeasible : x ∈ P.feasibleSet) :
    sSup (Set.range fun u : Fin m → ℝ => P.lagrangian u x) = ((P.objective x : ℝ) : EReal) := by
  apply le_antisymm
  · -- Every multiplier gives a Lagrangian value bounded above by the feasible objective value.
    refine sSup_le ?_
    rintro _ ⟨u, rfl⟩
    by_cases hu : u ∈ P.lagrangeMultiplierSet
    · have hxC : x ∈ P.constraintSet := hxFeasible.1
      have hL_eq : P.lagrangian u x = (P.kuhnTuckerObjective u x : EReal) := by
        simp [BookOrdinaryConvexProgram.lagrangian, hxC, hu]
      have hu_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers u i := by
        simpa [BookOrdinaryConvexProgram.lagrangeMultiplierSet] using hu
      have hkuhn_le_obj : P.kuhnTuckerObjective u x ≤ P.objective x :=
        helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible P u hxFeasible
          hu_nonneg
      simpa [hL_eq] using
        (show ((P.kuhnTuckerObjective u x : ℝ) : EReal) ≤ ((P.objective x : ℝ) : EReal) from
          EReal.coe_le_coe_iff.2 hkuhn_le_obj)
    · have hxC : x ∈ P.constraintSet := hxFeasible.1
      have hL_eq : P.lagrangian u x = (⊥ : EReal) := by
        simp [BookOrdinaryConvexProgram.lagrangian, hxC, hu]
      have hbot_le_obj : (⊥ : EReal) ≤ ((P.objective x : ℝ) : EReal) := by
        simp
      simpa [hL_eq] using hbot_le_obj
  · -- The zero multiplier is admissible and attains the original objective value.
    have hzero_mem : (fun _ : Fin m => (0 : ℝ)) ∈ P.lagrangeMultiplierSet := by
      -- All inequality coordinates of the zero multiplier are nonnegative.
      intro i
      simp [BookOrdinaryConvexProgram.inequalityMultipliers]
    have hxC : x ∈ P.constraintSet := hxFeasible.1
    have hL_zero : P.lagrangian (fun _ : Fin m => (0 : ℝ)) x = ((P.objective x : ℝ) : EReal) := by
      have hkuhn_zero : P.kuhnTuckerObjective (fun _ : Fin m => (0 : ℝ)) x = P.objective x := by
        -- The multiplier terms vanish when `u = 0`.
        simp [BookOrdinaryConvexProgram.kuhnTuckerObjective,
          BookOrdinaryConvexProgram.inequalityMultipliers,
          BookOrdinaryConvexProgram.equalityMultipliers]
      have hLag_zero :
          P.lagrangian (fun _ : Fin m => (0 : ℝ)) x =
            (P.kuhnTuckerObjective (fun _ : Fin m => (0 : ℝ)) x : EReal) := by
        simp [BookOrdinaryConvexProgram.lagrangian, hxC, hzero_mem]
      -- Rewrite the Kuhn--Tucker objective at `0` to the plain objective.
      simpa [hLag_zero, hkuhn_zero]
    exact le_sSup ⟨(fun _ : Fin m => (0 : ℝ)), hL_zero⟩

/-- Helper for Theorem 6.28.6: an extended-real number that dominates every real number must be
`⊤`. -/
lemma helperForTheorem_6_28_6_ereal_eq_top_of_forall_real_le
    {a : EReal} (hreal_le : ∀ M : ℝ, ((M : ℝ) : EReal) ≤ a) :
    a = (⊤ : EReal) := by
  -- A non-`⊤` value is either `⊥` or finite; both are incompatible with domination of all reals.
  by_contra hne_top
  have hzero : ((0 : ℝ) : EReal) ≤ a := hreal_le 0
  have hne_bot : a ≠ (⊥ : EReal) := by
    intro hbot
    simpa [hbot] using hzero
  lift a to ℝ using ⟨hne_top, hne_bot⟩ with r hr
  have hlarge : ((r + 1 : ℝ) : EReal) ≤ (r : EReal) := by
    simpa [hr] using hreal_le (r + 1)
  exact
    (not_le_of_gt (by exact_mod_cast (lt_add_of_pos_right r zero_lt_one))) hlarge

/-- Helper for Theorem 6.28.6: at a nonfeasible point, the dual supremum of the Lagrangian is
`⊤`. -/
lemma helperForTheorem_6_28_6_lagrangianDualSup_eq_top_of_not_feasible
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {x : Fin n → ℝ}
    (hxNotFeasible : x ∉ P.feasibleSet) :
    sSup (Set.range fun u : Fin m → ℝ => P.lagrangian u x) = (⊤ : EReal) := by
  by_cases hxC : x ∈ P.constraintSet
  · -- Inside `constraintSet`, infeasibility means some inequality is positive or some equality is nonzero.
    by_cases hineqAll : ∀ i : Fin r, P.inequalityConstraint i x ≤ 0
    · have heqNotAll : ¬ ∀ j : Fin (m - r), P.equalityConstraint j x = 0 := by
        intro heqAll
        exact hxNotFeasible ⟨hxC, hineqAll, heqAll⟩
      push_neg at heqNotAll
      rcases heqNotAll with ⟨j, hjNe⟩
      apply helperForTheorem_6_28_6_ereal_eq_top_of_forall_real_le
      intro M
      let t : ℝ := (M - P.objective x) / P.equalityConstraint j x
      let u : Fin m → ℝ :=
        Function.update (fun _ : Fin m => (0 : ℝ))
          (Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount) (Fin.natAdd r j)) t
      have hu : u ∈ P.lagrangeMultiplierSet := by
        -- Updating an equality multiplier leaves all inequality multipliers equal to zero.
        intro i
        have hne :
            Fin.castLE P.inequalityCount_le_constraintCount i ≠
              Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount)
                (Fin.natAdd r j) := by
          intro hEq
          have hval := congr_arg Fin.val hEq
          have hi_lt :
              (Fin.castLE P.inequalityCount_le_constraintCount i : Fin m).val < r := by
            simpa using i.isLt
          have hr_le :
              r ≤
                (Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount)
                    (Fin.natAdd r j) : Fin m).val := by
            simp
          exact (Nat.not_lt_of_ge hr_le) (hval ▸ hi_lt)
        simp [u, BookOrdinaryConvexProgram.inequalityMultipliers, hne]
      have hkuhn :
          P.kuhnTuckerObjective u x =
            P.objective x + t * P.equalityConstraint j x := by
        -- Starting from the zero multiplier, the equality-update formula isolates the violated equality.
        simpa [u, t, BookOrdinaryConvexProgram.kuhnTuckerObjective,
          BookOrdinaryConvexProgram.inequalityMultipliers,
          BookOrdinaryConvexProgram.equalityMultipliers] using
          (helperForTheorem_6_28_4_kuhnTuckerObjective_update_equalityMultiplier
            P (fun _ : Fin m => (0 : ℝ)) j t x)
      have hLag :
          P.lagrangian u x =
            ((P.objective x + t * P.equalityConstraint j x : ℝ) : EReal) := by
        -- On `constraintSet` and inside the multiplier cone, the Lagrangian is finite and equals the updated objective.
        have hLag_eq : P.lagrangian u x = (P.kuhnTuckerObjective u x : EReal) := by
          simpa [helperForTheorem_6_28_4_lagrangian_simp P u x, hxC, hu] using
            (helperForTheorem_6_28_4_lagrangian_simp P u x).2.2 hxC hu
        simpa [hkuhn] using hLag_eq
      have hMul :
          t * P.equalityConstraint j x = M - P.objective x := by
        -- We choose the equality multiplier so that the corresponding Lagrangian value is exactly `M`.
        dsimp [t]
        field_simp [hjNe]
      have hValue :
          P.objective x + t * P.equalityConstraint j x = M := by
        linarith
      have hM_eq_lag : ((M : ℝ) : EReal) = P.lagrangian u x := by
        simpa [hValue] using hLag.symm
      have hM_le_lag : ((M : ℝ) : EReal) ≤ P.lagrangian u x := by
        exact le_of_eq hM_eq_lag
      calc
        ((M : ℝ) : EReal) ≤ P.lagrangian u x := hM_le_lag
        _ ≤ sSup (Set.range fun u' : Fin m → ℝ => P.lagrangian u' x) := le_sSup ⟨u, rfl⟩
    · push_neg at hineqAll
      rcases hineqAll with ⟨i, hiPos⟩
      apply helperForTheorem_6_28_6_ereal_eq_top_of_forall_real_le
      intro M
      let t : ℝ := max 0 ((M - P.objective x) / P.inequalityConstraint i x)
      let u : Fin m → ℝ :=
        Function.update (fun _ : Fin m => (0 : ℝ))
          (Fin.castLE P.inequalityCount_le_constraintCount i) t
      have hu : u ∈ P.lagrangeMultiplierSet := by
        -- Only the selected inequality multiplier changes, and it changes to a nonnegative value.
        intro j
        by_cases hj : j = i
        · subst hj
          simp [u, t, BookOrdinaryConvexProgram.inequalityMultipliers]
        · have hne :
              Fin.castLE P.inequalityCount_le_constraintCount j ≠
                Fin.castLE P.inequalityCount_le_constraintCount i := by
            intro hEq
            exact hj (Fin.castLE_injective P.inequalityCount_le_constraintCount hEq)
          simp [u, BookOrdinaryConvexProgram.inequalityMultipliers, hne]
      have hkuhn :
          P.kuhnTuckerObjective u x =
            P.objective x + t * P.inequalityConstraint i x := by
        -- Starting from the zero multiplier, the inequality-update formula isolates the violated inequality.
        simpa [u, t, BookOrdinaryConvexProgram.kuhnTuckerObjective,
          BookOrdinaryConvexProgram.inequalityMultipliers,
          BookOrdinaryConvexProgram.equalityMultipliers] using
          (helperForTheorem_6_28_4_kuhnTuckerObjective_update_inequalityMultiplier
            P (fun _ : Fin m => (0 : ℝ)) i t x)
      have hLag :
          P.lagrangian u x =
            ((P.objective x + t * P.inequalityConstraint i x : ℝ) : EReal) := by
        -- The chosen multiplier stays in the admissible cone, so the Lagrangian is the finite branch.
        have hLag_eq : P.lagrangian u x = (P.kuhnTuckerObjective u x : EReal) := by
          simpa [helperForTheorem_6_28_4_lagrangian_simp P u x, hxC, hu] using
            (helperForTheorem_6_28_4_lagrangian_simp P u x).2.2 hxC hu
        simpa [hkuhn] using hLag_eq
      have hdiv_le : (M - P.objective x) / P.inequalityConstraint i x ≤ t := by
        exact le_max_right 0 ((M - P.objective x) / P.inequalityConstraint i x)
      have hscaled :
          M - P.objective x ≤ t * P.inequalityConstraint i x := by
        have hmul :
            ((M - P.objective x) / P.inequalityConstraint i x) * P.inequalityConstraint i x ≤
              t * P.inequalityConstraint i x := by
          exact mul_le_mul_of_nonneg_right hdiv_le (le_of_lt hiPos)
        have hcancel :
            ((M - P.objective x) / P.inequalityConstraint i x) *
                P.inequalityConstraint i x =
              M - P.objective x := by
          field_simp [hiPos.ne']
        calc
          M - P.objective x =
              ((M - P.objective x) / P.inequalityConstraint i x) *
                P.inequalityConstraint i x := hcancel.symm
          _ ≤ t * P.inequalityConstraint i x := hmul
      have hValue :
          M ≤ P.objective x + t * P.inequalityConstraint i x := by
        linarith
      have hM_le_lag : ((M : ℝ) : EReal) ≤ P.lagrangian u x := by
        calc
          ((M : ℝ) : EReal) ≤
              ((P.objective x + t * P.inequalityConstraint i x : ℝ) : EReal) := by
                exact EReal.coe_le_coe_iff.2 hValue
          _ = P.lagrangian u x := hLag.symm
      calc
        ((M : ℝ) : EReal) ≤ P.lagrangian u x := hM_le_lag
        _ ≤ sSup (Set.range fun u' : Fin m → ℝ => P.lagrangian u' x) := le_sSup ⟨u, rfl⟩
  · -- Outside `constraintSet`, the Lagrangian is identically `⊤` in the multiplier variable.
    simp [BookOrdinaryConvexProgram.lagrangian, hxC]

end Section28
end Chap06
