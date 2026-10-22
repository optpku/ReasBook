/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part8

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- Helper for Theorem 6.28.4: updating one inequality multiplier changes the Kuhn--Tucker
objective by the expected scalar multiple of the corresponding inequality constraint. -/
lemma helperForTheorem_6_28_4_kuhnTuckerObjective_update_inequalityMultiplier
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (i0 : Fin r) (b : ℝ) (x : Fin n → ℝ) :
    P.kuhnTuckerObjective
        (Function.update lambda (Fin.castLE P.inequalityCount_le_constraintCount i0) b) x =
      P.kuhnTuckerObjective lambda x +
        (b - P.inequalityMultipliers lambda i0) * P.inequalityConstraint i0 x := by
  classical
  -- Expand the definition and treat the two finite sums separately.
  unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
  let k0 : Fin m := Fin.castLE P.inequalityCount_le_constraintCount i0
  -- The equality-multiplier sum is unchanged because the update index lies strictly below `r`.
  have heq_sum :
      (∑ j : Fin (m - r),
            P.equalityMultipliers (Function.update lambda k0 b) j *
              P.equalityConstraint j x) =
        ∑ j : Fin (m - r), P.equalityMultipliers lambda j * P.equalityConstraint j x := by
    -- Rewrite as a `Finset.univ.sum` and compare summands.
    change
      (Finset.univ.sum fun j : Fin (m - r) =>
          P.equalityMultipliers (Function.update lambda k0 b) j * P.equalityConstraint j x) =
        Finset.univ.sum fun j : Fin (m - r) =>
          P.equalityMultipliers lambda j * P.equalityConstraint j x
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hne :
        Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount) (Fin.natAdd r j) ≠ k0 := by
      -- Compare `val`: the left-hand side is at least `r`, while `k0.val < r`.
      intro hEq
      have hval := congr_arg Fin.val hEq
      have hr_le :
          r ≤
            (Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount) (Fin.natAdd r j) :
                Fin m).val := by
        simp
      have hk_lt : (k0 : Fin m).val < r := by
        -- `k0` is the `castLE` of an element of `Fin r`.
        simpa [k0] using i0.isLt
      exact (Nat.not_lt_of_ge hr_le) (hval ▸ hk_lt)
    simp [BookOrdinaryConvexProgram.equalityMultipliers, k0, Function.update, hne]
  -- The inequality-multiplier sum changes only at index `i0`.
  let g : Fin r → ℝ := fun i => P.inequalityMultipliers lambda i * P.inequalityConstraint i x
  have hsum_ineq :
      (∑ i : Fin r,
            P.inequalityMultipliers (Function.update lambda k0 b) i *
              P.inequalityConstraint i x) =
        (∑ i : Fin r, g i) + (b - P.inequalityMultipliers lambda i0) * P.inequalityConstraint i0 x := by
    -- Identify the updated summand function as `Function.update g i0 (b * f_i0(x))`.
    have hfun :
        (fun i : Fin r =>
              P.inequalityMultipliers (Function.update lambda k0 b) i * P.inequalityConstraint i x) =
          Function.update g i0 (b * P.inequalityConstraint i0 x) := by
      funext i
      by_cases hi : i = i0
      · subst hi
        simp [g, BookOrdinaryConvexProgram.inequalityMultipliers, k0]
      · have hcastne : Fin.castLE P.inequalityCount_le_constraintCount i ≠ k0 := by
          intro hEq
          have : i = i0 := by
            -- `castLE` is injective, and `k0 = castLE i0` by definition.
            have hEq' : Fin.castLE P.inequalityCount_le_constraintCount i =
                Fin.castLE P.inequalityCount_le_constraintCount i0 := by
              simpa [k0] using hEq
            exact (Fin.castLE_injective P.inequalityCount_le_constraintCount) hEq'
          exact hi this
        simp [g, BookOrdinaryConvexProgram.inequalityMultipliers, k0, Function.update, hi, hcastne]
    -- Rewrite both sides in `Finset` form and apply `sum_update_of_mem`.
    have hmem : i0 ∈ (Finset.univ : Finset (Fin r)) := Finset.mem_univ i0
    have hsdiff :
        (Finset.univ \ {i0} : Finset (Fin r)) = (Finset.univ.erase i0) := by
      simpa using (Finset.sdiff_singleton_eq_erase i0 (Finset.univ : Finset (Fin r)))
    have hsum_update :
        (Finset.univ.sum (Function.update g i0 (b * P.inequalityConstraint i0 x))) =
          b * P.inequalityConstraint i0 x + Finset.sum (Finset.univ.erase i0) g := by
      -- The library lemma uses `univ \ {i0}`; rewrite it as `erase`.
      have :=
        (Finset.sum_update_of_mem hmem (f := g) (b := b * P.inequalityConstraint i0 x))
      -- Turn `\ {i0}` into `erase i0`.
      simpa [hsdiff] using this
    have hsum_split :
        (Finset.univ.sum g) = g i0 + Finset.sum (Finset.univ.erase i0) g := by
      rw [add_comm]
      exact
        (Finset.sum_erase_add (s := Finset.univ) (a := i0) (f := g) (Finset.mem_univ i0)).symm
    -- Combine the update formula with the split sum and simplify the algebra.
    have :
        (Finset.univ.sum
            (fun i : Fin r =>
              P.inequalityMultipliers (Function.update lambda k0 b) i *
                P.inequalityConstraint i x)) =
          (Finset.univ.sum g) + (b - P.inequalityMultipliers lambda i0) * P.inequalityConstraint i0 x := by
      -- Rewrite the left-hand side by `hfun`, then compare `sum_update` with `sum_split`.
      have hL :
          (Finset.univ.sum fun i : Fin r =>
              P.inequalityMultipliers (Function.update lambda k0 b) i * P.inequalityConstraint i x) =
            Finset.univ.sum (Function.update g i0 (b * P.inequalityConstraint i0 x)) := by
        simpa [hfun]
      -- Use the explicit update and split formulas; only one summand changes.
      rw [hL, hsum_update, hsum_split]
      simp [g]
      ring
    -- Return from `Finset` form to the original `∑` notation.
    simpa using this
  -- Reassemble the full expression.
  rw [hsum_ineq, heq_sum]
  ring

/-- Helper for Theorem 6.28.4: updating one equality multiplier changes the Kuhn--Tucker
objective by the expected scalar multiple of the corresponding equality constraint. -/
lemma helperForTheorem_6_28_4_kuhnTuckerObjective_update_equalityMultiplier
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ)
    (j0 : Fin (m - r)) (b : ℝ) (x : Fin n → ℝ) :
    P.kuhnTuckerObjective
        (Function.update lambda
          (Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount) (Fin.natAdd r j0)) b) x =
      P.kuhnTuckerObjective lambda x +
        (b - P.equalityMultipliers lambda j0) * P.equalityConstraint j0 x := by
  classical
  -- Expand the definition and treat the two finite sums separately.
  unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
  let k0 : Fin m :=
    Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount) (Fin.natAdd r j0)
  -- The inequality-multiplier sum is unchanged because the update index lies in the equality block.
  have hineq_sum :
      (∑ i : Fin r,
            P.inequalityMultipliers (Function.update lambda k0 b) i *
              P.inequalityConstraint i x) =
        ∑ i : Fin r, P.inequalityMultipliers lambda i * P.inequalityConstraint i x := by
    change
      (Finset.univ.sum fun i : Fin r =>
          P.inequalityMultipliers (Function.update lambda k0 b) i * P.inequalityConstraint i x) =
        Finset.univ.sum fun i : Fin r =>
          P.inequalityMultipliers lambda i * P.inequalityConstraint i x
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hne : Fin.castLE P.inequalityCount_le_constraintCount i ≠ k0 := by
      intro hEq
      have hval := congr_arg Fin.val hEq
      have hi_lt :
          (Fin.castLE P.inequalityCount_le_constraintCount i : Fin m).val < r := by
        simpa using i.isLt
      have hr_le : r ≤ (k0 : Fin m).val := by
        simp [k0]
      exact (Nat.not_lt_of_ge hr_le) (hval ▸ hi_lt)
    simp [BookOrdinaryConvexProgram.inequalityMultipliers, k0, Function.update, hne]
  -- The equality-multiplier sum changes only at index `j0`.
  let g : Fin (m - r) → ℝ := fun j => P.equalityMultipliers lambda j * P.equalityConstraint j x
  have hsum_eq :
      (∑ j : Fin (m - r),
            P.equalityMultipliers (Function.update lambda k0 b) j *
              P.equalityConstraint j x) =
        (∑ j : Fin (m - r), g j) + (b - P.equalityMultipliers lambda j0) * P.equalityConstraint j0 x := by
    have hfun :
        (fun j : Fin (m - r) =>
              P.equalityMultipliers (Function.update lambda k0 b) j * P.equalityConstraint j x) =
          Function.update g j0 (b * P.equalityConstraint j0 x) := by
      funext j
      by_cases hj : j = j0
      · subst hj
        simp [g, BookOrdinaryConvexProgram.equalityMultipliers, k0]
      · have hne :
            Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount) (Fin.natAdd r j) ≠ k0 := by
          intro hEq
          have hcastinj : Fin.natAdd r j = Fin.natAdd r j0 := by
            -- The cast is injective; move the equality back before the cast.
            apply (Fin.cast_injective (Nat.add_sub_of_le P.inequalityCount_le_constraintCount))
            simpa [k0] using hEq
          exact hj ((Fin.natAdd_inj r).1 hcastinj)
        simp [g, BookOrdinaryConvexProgram.equalityMultipliers, k0, Function.update, hj, hne]
    have hmem : j0 ∈ (Finset.univ : Finset (Fin (m - r))) := Finset.mem_univ j0
    have hsdiff :
        (Finset.univ \ {j0} : Finset (Fin (m - r))) = (Finset.univ.erase j0) := by
      simpa using (Finset.sdiff_singleton_eq_erase j0 (Finset.univ : Finset (Fin (m - r))))
    have hsum_update :
        (Finset.univ.sum (Function.update g j0 (b * P.equalityConstraint j0 x))) =
          b * P.equalityConstraint j0 x + Finset.sum (Finset.univ.erase j0) g := by
      have :=
        (Finset.sum_update_of_mem hmem (f := g) (b := b * P.equalityConstraint j0 x))
      simpa [hsdiff] using this
    have hsum_split :
        (Finset.univ.sum g) = g j0 + Finset.sum (Finset.univ.erase j0) g := by
      rw [add_comm]
      exact
        (Finset.sum_erase_add (s := Finset.univ) (a := j0) (f := g) (Finset.mem_univ j0)).symm
    have :
        (Finset.univ.sum
            (fun j : Fin (m - r) =>
              P.equalityMultipliers (Function.update lambda k0 b) j * P.equalityConstraint j x)) =
          (Finset.univ.sum g) + (b - P.equalityMultipliers lambda j0) * P.equalityConstraint j0 x := by
      have hL :
          (Finset.univ.sum fun j : Fin (m - r) =>
              P.equalityMultipliers (Function.update lambda k0 b) j * P.equalityConstraint j x) =
            Finset.univ.sum (Function.update g j0 (b * P.equalityConstraint j0 x)) := by
        simpa [hfun]
      rw [hL, hsum_update, hsum_split]
      simp [g]
      ring
    simpa using this
  -- Reassemble the full expression.
  rw [hineq_sum, hsum_eq]
  ring

/-- Helper for Theorem 6.28.4: with nonempty ambient constraint set, Lagrangian saddle points are
equivalent to the explicit Kuhn--Tucker point conditions. -/
lemma helperForTheorem_6_28_4_lagrangianSaddlePoint_iff_explicitConditions
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hconstraint_nonempty : P.constraintSet.Nonempty)
    (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    P.IsLagrangianSaddlePoint uStar x ↔
      P.SatisfiesKuhnTuckerPointConditions uStar x := by
  constructor
  · intro hsaddle
    have hmax : ∀ u : Fin m → ℝ, P.lagrangian u x ≤ P.lagrangian uStar x := hsaddle.1
    have hmin : ∀ z : Fin n → ℝ, P.lagrangian uStar x ≤ P.lagrangian uStar z := hsaddle.2
    -- First show `x ∈ P.constraintSet`, using a feasible witness to contradict `⊤` at `x`.
    have hxC : x ∈ P.constraintSet := by
      by_contra hxC
      rcases hconstraint_nonempty with ⟨y, hyC⟩
      have htop_le : (⊤ : EReal) ≤ P.lagrangian uStar y := by
        -- Rewrite `P.lagrangian uStar x` to `⊤` under the hypothesis `x ∉ C`.
        simpa [BookOrdinaryConvexProgram.lagrangian, hxC] using hmin y
      -- But at a point `y ∈ C`, the Lagrangian is never `⊤`.
      have hne : P.lagrangian uStar y ≠ (⊤ : EReal) := by
        by_cases hu : uStar ∈ P.lagrangeMultiplierSet
        · -- In this branch the value is a real coercion.
          have : P.lagrangian uStar y = (P.kuhnTuckerObjective uStar y : EReal) := by
            simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar y, hyC, hu] using
              (helperForTheorem_6_28_4_lagrangian_simp P uStar y).2.2 hyC hu
          intro hEq
          have : (⊤ : EReal) = (P.kuhnTuckerObjective uStar y : EReal) := by simpa [this] using hEq
          exact (EReal.top_ne_coe (P.kuhnTuckerObjective uStar y)) this
        · -- Otherwise the value is `⊥`.
          have : P.lagrangian uStar y = (⊥ : EReal) := by
            simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar y, hyC, hu] using
              (helperForTheorem_6_28_4_lagrangian_simp P uStar y).2.1 hyC hu
          intro hEq
          simpa [this] using hEq
      exact hne (top_le_iff.mp htop_le)
    -- Next show `uStar ∈ P.lagrangeMultiplierSet` by testing against the zero multiplier.
    have huStar : uStar ∈ P.lagrangeMultiplierSet := by
      by_contra huStar
      let u0 : Fin m → ℝ := fun _ => 0
      have hu0 : u0 ∈ P.lagrangeMultiplierSet := by
        intro i
        simp [u0, BookOrdinaryConvexProgram.lagrangeMultiplierSet,
          BookOrdinaryConvexProgram.inequalityMultipliers]
      have hle : P.lagrangian u0 x ≤ P.lagrangian uStar x := hmax u0
      have hL0 : P.lagrangian u0 x = (P.kuhnTuckerObjective u0 x : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P u0 x, hxC, hu0] using
          (helperForTheorem_6_28_4_lagrangian_simp P u0 x).2.2 hxC hu0
      have hLStar : P.lagrangian uStar x = (⊥ : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x, hxC, huStar] using
          (helperForTheorem_6_28_4_lagrangian_simp P uStar x).2.1 hxC huStar
      have : P.lagrangian u0 x = (⊥ : EReal) := by
        -- Anything below `⊥` must equal `⊥`.
        have hle' : P.lagrangian u0 x ≤ (⊥ : EReal) := by
          simpa [hLStar] using hle
        exact le_bot_iff.mp hle'
      -- But `P.lagrangian u0 x` is a real coercion, contradiction.
      have : (P.kuhnTuckerObjective u0 x : EReal) = (⊥ : EReal) := by simpa [hL0] using this
      exact (EReal.coe_ne_bot (P.kuhnTuckerObjective u0 x)) this
    -- The nonnegativity conditions in the point-conditions package come directly from `huStar`.
    have huStar_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers uStar i := by
      simpa [BookOrdinaryConvexProgram.lagrangeMultiplierSet] using huStar
    -- Feasibility of each inequality constraint follows by increasing a single multiplier.
    have hineq_feas : ∀ i : Fin r, P.inequalityConstraint i x ≤ 0 := by
      intro i
      let j : Fin m := Fin.castLE P.inequalityCount_le_constraintCount i
      let uPlus : Fin m → ℝ := Function.update uStar j (uStar j + 1)
      have huPlus : uPlus ∈ P.lagrangeMultiplierSet := by
        intro k
        by_cases hk : k = i
        · -- Keep the outer index `i` in scope; use `hk` only for rewriting.
          have hone : (0 : ℝ) ≤ 1 := by norm_num
          have hnonneg : 0 ≤ uStar j + 1 := add_nonneg (huStar_nonneg i) hone
          -- The updated inequality multiplier is exactly `uStar j + 1`.
          simpa [hk, BookOrdinaryConvexProgram.inequalityMultipliers, uPlus, j, Function.update] using hnonneg
        · have hne :
              Fin.castLE P.inequalityCount_le_constraintCount k ≠ j := by
            intro hEq
            exact hk ((Fin.castLE_inj).1 hEq)
          -- All other inequality multipliers agree with `uStar`.
          simpa [BookOrdinaryConvexProgram.inequalityMultipliers, uPlus, Function.update, hne] using
            huStar_nonneg k
      have hle : P.lagrangian uPlus x ≤ P.lagrangian uStar x := hmax uPlus
      have hLPlus :
          P.lagrangian uPlus x = (P.kuhnTuckerObjective uPlus x : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P uPlus x, hxC, huPlus] using
          (helperForTheorem_6_28_4_lagrangian_simp P uPlus x).2.2 hxC huPlus
      have hLStar :
          P.lagrangian uStar x = (P.kuhnTuckerObjective uStar x : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x, hxC, huStar] using
          (helperForTheorem_6_28_4_lagrangian_simp P uStar x).2.2 hxC huStar
      have hreal_le :
          P.kuhnTuckerObjective uPlus x ≤ P.kuhnTuckerObjective uStar x := by
        -- Compare real numbers after rewriting the `EReal` inequality.
        have hle' :
            (P.kuhnTuckerObjective uPlus x : EReal) ≤ (P.kuhnTuckerObjective uStar x : EReal) := by
          simpa [hLPlus, hLStar] using hle
        exact EReal.coe_le_coe_iff.1 hle'
      -- Use the update formula with `b = uStar j + 1` to isolate `f_i(x)`.
      have hupdate :=
        helperForTheorem_6_28_4_kuhnTuckerObjective_update_inequalityMultiplier
          P uStar i (uStar j + 1) x
      -- Rearrange and finish by linear arithmetic.
      have : P.inequalityConstraint i x ≤ 0 := by
        -- `hupdate` rewrites `kuhnTuckerObjective uPlus x` as `kuhnTuckerObjective uStar x + f_i(x)`.
        -- Then `hreal_le` forces `f_i(x) ≤ 0`.
        -- (We use `j = castLE ... i` to identify the multiplier component.)
        have hmult :
            P.inequalityMultipliers uStar i = uStar j := by
          rfl
        -- Substitute the update identity and simplify.
        -- The coefficient `(uStar j + 1 - uStar j)` is `1`.
        have hreal_le' :
            P.kuhnTuckerObjective uStar x + P.inequalityConstraint i x ≤
              P.kuhnTuckerObjective uStar x := by
          -- Replace the left-hand side by `kuhnTuckerObjective uPlus x`.
          have : P.kuhnTuckerObjective uPlus x =
              P.kuhnTuckerObjective uStar x +
                ((uStar j + 1) - P.inequalityMultipliers uStar i) * P.inequalityConstraint i x := by
            simpa [uPlus, j] using hupdate
          -- Use the computed real inequality.
          -- After rewriting, it becomes a direct `linarith` goal.
          -- Route correction: `ring` handles the coefficient normalization cleanly.
          -- (No extra convexity assumptions are used here; it is pure algebra.)
          -- Convert `hreal_le` using the identity above.
          have : P.kuhnTuckerObjective uStar x +
              ((uStar j + 1) - P.inequalityMultipliers uStar i) * P.inequalityConstraint i x ≤
                P.kuhnTuckerObjective uStar x := by
            simpa [this] using hreal_le
          -- Normalize the scalar coefficient to `1`.
          simpa [hmult] using this
        linarith
      exact this
    -- Equality constraints follow by varying the unconstrained equality multipliers in both signs.
    have heq_feas : ∀ j : Fin (m - r), P.equalityConstraint j x = 0 := by
      intro j
      let k : Fin m :=
        Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount) (Fin.natAdd r j)
      let uPlus : Fin m → ℝ := Function.update uStar k (uStar k + 1)
      let uMinus : Fin m → ℝ := Function.update uStar k (uStar k - 1)
      have huPlus : uPlus ∈ P.lagrangeMultiplierSet := by
        intro i
        -- The update index lies in the equality block, so every inequality multiplier is unchanged.
        have hne :
            Fin.castLE P.inequalityCount_le_constraintCount i ≠ k := by
          intro hEq
          have hval := congr_arg Fin.val hEq
          have hi_lt :
              (Fin.castLE P.inequalityCount_le_constraintCount i : Fin m).val < r := by
            simpa using i.isLt
          have hr_le : r ≤ (k : Fin m).val := by
            simp [k]
          exact (Nat.not_lt_of_ge hr_le) (hval ▸ hi_lt)
        simpa [BookOrdinaryConvexProgram.inequalityMultipliers, uPlus, Function.update, hne] using
          huStar_nonneg i
      have huMinus : uMinus ∈ P.lagrangeMultiplierSet := by
        intro i
        have hne :
            Fin.castLE P.inequalityCount_le_constraintCount i ≠ k := by
          intro hEq
          have hval := congr_arg Fin.val hEq
          have hi_lt :
              (Fin.castLE P.inequalityCount_le_constraintCount i : Fin m).val < r := by
            simpa using i.isLt
          have hr_le : r ≤ (k : Fin m).val := by
            simp [k]
          exact (Nat.not_lt_of_ge hr_le) (hval ▸ hi_lt)
        simpa [BookOrdinaryConvexProgram.inequalityMultipliers, uMinus, Function.update, hne] using
          huStar_nonneg i
      have hlePlus : P.lagrangian uPlus x ≤ P.lagrangian uStar x := hmax uPlus
      have hleMinus : P.lagrangian uMinus x ≤ P.lagrangian uStar x := hmax uMinus
      have hLPlus :
          P.lagrangian uPlus x = (P.kuhnTuckerObjective uPlus x : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P uPlus x, hxC, huPlus] using
          (helperForTheorem_6_28_4_lagrangian_simp P uPlus x).2.2 hxC huPlus
      have hLMinus :
          P.lagrangian uMinus x = (P.kuhnTuckerObjective uMinus x : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P uMinus x, hxC, huMinus] using
          (helperForTheorem_6_28_4_lagrangian_simp P uMinus x).2.2 hxC huMinus
      have hLStar :
          P.lagrangian uStar x = (P.kuhnTuckerObjective uStar x : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x, hxC, huStar] using
          (helperForTheorem_6_28_4_lagrangian_simp P uStar x).2.2 hxC huStar
      have hreal_le_plus :
          P.kuhnTuckerObjective uPlus x ≤ P.kuhnTuckerObjective uStar x :=
        by
          have hle' :
              (P.kuhnTuckerObjective uPlus x : EReal) ≤ (P.kuhnTuckerObjective uStar x : EReal) := by
            simpa [hLPlus, hLStar] using hlePlus
          exact EReal.coe_le_coe_iff.1 hle'
      have hreal_le_minus :
          P.kuhnTuckerObjective uMinus x ≤ P.kuhnTuckerObjective uStar x :=
        by
          have hle' :
              (P.kuhnTuckerObjective uMinus x : EReal) ≤ (P.kuhnTuckerObjective uStar x : EReal) := by
            simpa [hLMinus, hLStar] using hleMinus
          exact EReal.coe_le_coe_iff.1 hle'
      -- Use update formulas to deduce both `f_j(x) ≤ 0` and `f_j(x) ≥ 0`.
      have hupdatePlus :=
        helperForTheorem_6_28_4_kuhnTuckerObjective_update_equalityMultiplier
          P uStar j (uStar k + 1) x
      have hupdateMinus :=
        helperForTheorem_6_28_4_kuhnTuckerObjective_update_equalityMultiplier
          P uStar j (uStar k - 1) x
      have hle0 : P.equalityConstraint j x ≤ 0 := by
        -- From `kuhnTuckerObjective(uStar with +1) ≤ kuhnTuckerObjective(uStar)`.
        have : (uStar k + 1 - P.equalityMultipliers uStar j) * P.equalityConstraint j x ≤ 0 := by
          have : P.kuhnTuckerObjective uStar x +
              (uStar k + 1 - P.equalityMultipliers uStar j) * P.equalityConstraint j x ≤
                P.kuhnTuckerObjective uStar x := by
            have : P.kuhnTuckerObjective uPlus x =
                P.kuhnTuckerObjective uStar x +
                  (uStar k + 1 - P.equalityMultipliers uStar j) * P.equalityConstraint j x := by
              simpa [uPlus, k] using hupdatePlus
            simpa [this] using hreal_le_plus
          linarith
        -- The scalar coefficient is `1` since `P.equalityMultipliers uStar j = uStar k`.
        have hmult : P.equalityMultipliers uStar j = uStar k := by rfl
        simpa [hmult] using this
      have hge0 : 0 ≤ P.equalityConstraint j x := by
        -- Apply the same argument to the `-1` update to get `-f_j(x) ≤ 0`.
        have : (uStar k - 1 - P.equalityMultipliers uStar j) * P.equalityConstraint j x ≤ 0 := by
          have : P.kuhnTuckerObjective uStar x +
              (uStar k - 1 - P.equalityMultipliers uStar j) * P.equalityConstraint j x ≤
                P.kuhnTuckerObjective uStar x := by
            have : P.kuhnTuckerObjective uMinus x =
                P.kuhnTuckerObjective uStar x +
                  (uStar k - 1 - P.equalityMultipliers uStar j) * P.equalityConstraint j x := by
              simpa [uMinus, k] using hupdateMinus
            simpa [this] using hreal_le_minus
          linarith
        have hmult : P.equalityMultipliers uStar j = uStar k := by rfl
        -- The coefficient now is `-1`, so the inequality becomes `0 ≤ f_j(x)`.
        have : (-1 : ℝ) * P.equalityConstraint j x ≤ 0 := by simpa [hmult] using this
        linarith
      exact le_antisymm hle0 hge0
    -- Complementary slackness comes from comparing with the update that sets a multiplier to `0`.
    have hcomp :
        ∀ i : Fin r,
          P.inequalityMultipliers uStar i * P.inequalityConstraint i x = 0 := by
      intro i
      let j : Fin m := Fin.castLE P.inequalityCount_le_constraintCount i
      let uZero : Fin m → ℝ := Function.update uStar j 0
      have huZero : uZero ∈ P.lagrangeMultiplierSet := by
        intro k
        by_cases hk : k = i
        · -- Use `hk` only to rewrite the goal; then `simp` sees the updated coordinate.
          simpa [hk, BookOrdinaryConvexProgram.inequalityMultipliers, uZero, j, Function.update]
        · have hne :
              Fin.castLE P.inequalityCount_le_constraintCount k ≠ j := by
            intro hEq
            exact hk ((Fin.castLE_inj).1 hEq)
          -- All other components agree with `uStar`.
          simpa [BookOrdinaryConvexProgram.inequalityMultipliers, uZero, Function.update, hne] using
            huStar_nonneg k
      have hle : P.lagrangian uZero x ≤ P.lagrangian uStar x := hmax uZero
      have hLZero :
          P.lagrangian uZero x = (P.kuhnTuckerObjective uZero x : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P uZero x, hxC, huZero] using
          (helperForTheorem_6_28_4_lagrangian_simp P uZero x).2.2 hxC huZero
      have hLStar :
          P.lagrangian uStar x = (P.kuhnTuckerObjective uStar x : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x, hxC, huStar] using
          (helperForTheorem_6_28_4_lagrangian_simp P uStar x).2.2 hxC huStar
      have hreal_le :
          P.kuhnTuckerObjective uZero x ≤ P.kuhnTuckerObjective uStar x :=
        by
          have hle' :
              (P.kuhnTuckerObjective uZero x : EReal) ≤ (P.kuhnTuckerObjective uStar x : EReal) := by
            simpa [hLZero, hLStar] using hle
          exact EReal.coe_le_coe_iff.1 hle'
      have hupdate :=
        helperForTheorem_6_28_4_kuhnTuckerObjective_update_inequalityMultiplier
          P uStar i 0 x
      have hmult : P.inequalityMultipliers uStar i = uStar j := by rfl
      -- The update identity gives `kuhnTuckerObjective uZero x = kuhnTuckerObjective uStar x - λ_i f_i(x)`.
      have hle0 : 0 ≤ P.inequalityMultipliers uStar i * P.inequalityConstraint i x := by
        have : P.kuhnTuckerObjective uStar x +
            (0 - P.inequalityMultipliers uStar i) * P.inequalityConstraint i x ≤
              P.kuhnTuckerObjective uStar x := by
          have : P.kuhnTuckerObjective uZero x =
              P.kuhnTuckerObjective uStar x +
                (0 - P.inequalityMultipliers uStar i) * P.inequalityConstraint i x := by
            simpa [uZero, j] using hupdate
          simpa [this] using hreal_le
        -- This inequality is exactly `-(λ_i f_i(x)) ≤ 0`.
        have : (-P.inequalityMultipliers uStar i) * P.inequalityConstraint i x ≤ 0 := by
          have htmp :
              (0 - P.inequalityMultipliers uStar i) * P.inequalityConstraint i x ≤ 0 := by
            linarith
          simpa using htmp
        linarith
      -- Combine with feasibility `f_i(x) ≤ 0` to conclude `λ_i f_i(x) = 0`.
      have hle : P.inequalityMultipliers uStar i * P.inequalityConstraint i x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (huStar_nonneg i) (hineq_feas i)
      exact le_antisymm hle hle0
    -- Stationarity follows from the primal minimization inequality rewritten for the extended objective.
    have hstationarity :
        (0 : Fin n → ℝ) ∈ P.textbookKuhnTuckerStationaritySet uStar x := by
      -- Convert the primal inequality into a pointwise lower bound for the extended objective.
      have hlower :
          ∀ z : Fin n → ℝ, P.extendedKuhnTuckerObjective uStar x ≤ P.extendedKuhnTuckerObjective uStar z := by
        intro z
        have hz : P.lagrangian uStar x ≤ P.lagrangian uStar z := hmin z
        -- Rewrite both sides using the multiplier-set assumption `huStar`.
        simpa [helperForTheorem_6_28_4_lagrangian_eq_extendedKuhnTuckerObjective_of_mem_lagrangeMultiplierSet
          P uStar huStar x,
          helperForTheorem_6_28_4_lagrangian_eq_extendedKuhnTuckerObjective_of_mem_lagrangeMultiplierSet
          P uStar huStar z] using hz
      -- Apply the zero-subgradient characterization.
      exact
        (helperForTheorem_6_28_4_zero_mem_euclideanSubdifferentialAt_iff_pointwiseLowerBound
          (f := P.extendedKuhnTuckerObjective uStar) (x := x)).2 hlower
    -- Assemble the point conditions.
    refine ⟨hxC, ?_, heq_feas, ?_⟩
    · intro i
      refine ⟨huStar_nonneg i, hineq_feas i, hcomp i⟩
    · simpa [BookOrdinaryConvexProgram.textbookKuhnTuckerStationaritySet] using hstationarity
  · intro hconditions
    rcases hconditions with ⟨hxC, hineq, heq, hstationarity⟩
    -- Extract the multiplier-set membership from the nonnegativity block.
    have huStar : uStar ∈ P.lagrangeMultiplierSet := by
      intro i
      exact (hineq i).1
    -- The saddle-point inequalities split into maximization in `u` and minimization in `x`.
    constructor
    · intro u
      by_cases hu : u ∈ P.lagrangeMultiplierSet
      · -- Inside the multiplier set the Lagrangian value is a real coercion.
        have hL_u : P.lagrangian u x = (P.kuhnTuckerObjective u x : EReal) := by
          simpa [helperForTheorem_6_28_4_lagrangian_simp P u x, hxC, hu] using
            (helperForTheorem_6_28_4_lagrangian_simp P u x).2.2 hxC hu
        have hL_star : P.lagrangian uStar x = (P.kuhnTuckerObjective uStar x : EReal) := by
          simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x, hxC, huStar] using
            (helperForTheorem_6_28_4_lagrangian_simp P uStar x).2.2 hxC huStar
        -- Show `kuhnTuckerObjective u x ≤ kuhnTuckerObjective uStar x` using feasibility and
        -- complementary slackness at `x`.
        have hxFeasible : x ∈ P.feasibleSet := by
          refine ⟨hxC, ?_, ?_⟩
          · intro i
            exact (hineq i).2.1
          · intro j
            exact heq j
        have hu_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers u i := by
          simpa [BookOrdinaryConvexProgram.lagrangeMultiplierSet] using hu
        have hkuhn_le_obj :
            P.kuhnTuckerObjective u x ≤ P.objective x :=
          helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible
            P u hxFeasible hu_nonneg
        -- Compute `kuhnTuckerObjective uStar x = objective x` from complementary slackness and `heq`.
        have hkuhn_star_eq_obj : P.kuhnTuckerObjective uStar x = P.objective x := by
          -- The inequality part is a sum of the complementary-slackness products.
          have hsum_ineq_zero :
              ∑ i : Fin r, P.inequalityMultipliers uStar i * P.inequalityConstraint i x = 0 := by
            refine Finset.sum_eq_zero ?_
            intro i hi
            simpa using (hineq i).2.2
          have hsum_eq_zero :
              ∑ j : Fin (m - r), P.equalityMultipliers uStar j * P.equalityConstraint j x = 0 := by
            refine Finset.sum_eq_zero ?_
            intro j hj
            simp [heq j]
          unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
          simp [hsum_ineq_zero, hsum_eq_zero]
        have hkuhn_le_star : P.kuhnTuckerObjective u x ≤ P.kuhnTuckerObjective uStar x := by
          calc
            P.kuhnTuckerObjective u x ≤ P.objective x := hkuhn_le_obj
            _ = P.kuhnTuckerObjective uStar x := hkuhn_star_eq_obj.symm
        have hereal :
            (P.kuhnTuckerObjective u x : EReal) ≤ (P.kuhnTuckerObjective uStar x : EReal) :=
          EReal.coe_le_coe_iff.2 hkuhn_le_star
        simpa [hL_u, hL_star] using hereal
      · -- Outside the multiplier set, the Lagrangian is `⊥` at points in `C`.
        have hL_u : P.lagrangian u x = (⊥ : EReal) := by
          simpa [helperForTheorem_6_28_4_lagrangian_simp P u x, hxC, hu] using
            (helperForTheorem_6_28_4_lagrangian_simp P u x).2.1 hxC hu
        -- Since `⊥ ≤ _` always holds, this case is immediate.
        simpa [hL_u]
    · intro z
      -- Turn the stationarity condition into a pointwise lower bound for the extended objective.
      have hstationarity' :
          (0 : Fin n → ℝ) ∈ euclideanSubdifferentialAt (P.extendedKuhnTuckerObjective uStar) x := by
        simpa [BookOrdinaryConvexProgram.textbookKuhnTuckerStationaritySet] using hstationarity
      have hlower :
          ∀ y : Fin n → ℝ,
            P.extendedKuhnTuckerObjective uStar x ≤ P.extendedKuhnTuckerObjective uStar y :=
        (helperForTheorem_6_28_4_zero_mem_euclideanSubdifferentialAt_iff_pointwiseLowerBound
          (f := P.extendedKuhnTuckerObjective uStar) (x := x)).1 hstationarity'
      have hz := hlower z
      -- Rewrite back to the Lagrangian using the multiplier-set assumption `huStar`.
      simpa
        [helperForTheorem_6_28_4_lagrangian_eq_extendedKuhnTuckerObjective_of_mem_lagrangeMultiplierSet
          P uStar huStar x,
          helperForTheorem_6_28_4_lagrangian_eq_extendedKuhnTuckerObjective_of_mem_lagrangeMultiplierSet
          P uStar huStar z] using hz

/-- Helper for Theorem 6.28.4: with nonempty ambient constraint set, the primal/dual saddle-point
condition is equivalent to "Kuhn--Tucker vector plus optimal solution". -/
lemma helperForTheorem_6_28_4_kuhnTuckerVector_and_optimalSolution_iff_lagrangianSaddlePoint
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hconstraint_nonempty : P.constraintSet.Nonempty)
    (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    (P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution x) ↔
      P.IsLagrangianSaddlePoint uStar x := by
  constructor
  · rintro ⟨hKT, hxOpt⟩
    -- From optimality, the point is feasible, hence lies in the constraint set.
    have hxC : x ∈ P.constraintSet := hxOpt.1.1
    -- The Kuhn--Tucker definition implies nonnegativity of the inequality multipliers.
    have huStar : uStar ∈ P.lagrangeMultiplierSet := by
      simpa [BookOrdinaryConvexProgram.lagrangeMultiplierSet] using hKT.1
    -- Theorem 6.28.1 already shows `h(uStar, x) = f₀(x)` at an optimal solution.
    have hkuhn_star_eq_obj : P.kuhnTuckerObjective uStar x = P.objective x :=
      helperForTheorem_6_28_1_optimal_has_kuhnTuckerObjective_eq_objective P uStar hxOpt hKT
    -- First prove the maximization inequality in the multiplier variable.
    have hmax : ∀ u : Fin m → ℝ, P.lagrangian u x ≤ P.lagrangian uStar x := by
      intro u
      by_cases hu : u ∈ P.lagrangeMultiplierSet
      · have hL_u : P.lagrangian u x = (P.kuhnTuckerObjective u x : EReal) := by
          simpa [helperForTheorem_6_28_4_lagrangian_simp P u x, hxC, hu] using
            (helperForTheorem_6_28_4_lagrangian_simp P u x).2.2 hxC hu
        have hL_star : P.lagrangian uStar x = (P.kuhnTuckerObjective uStar x : EReal) := by
          simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x, hxC, huStar] using
            (helperForTheorem_6_28_4_lagrangian_simp P uStar x).2.2 hxC huStar
        have hxFeasible : x ∈ P.feasibleSet := hxOpt.1
        have hu_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers u i := by
          simpa [BookOrdinaryConvexProgram.lagrangeMultiplierSet] using hu
        have hkuhn_le_obj :
            P.kuhnTuckerObjective u x ≤ P.objective x :=
          helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible
            P u hxFeasible hu_nonneg
        have hkuhn_le_star : P.kuhnTuckerObjective u x ≤ P.kuhnTuckerObjective uStar x := by
          calc
            P.kuhnTuckerObjective u x ≤ P.objective x := hkuhn_le_obj
            _ = P.kuhnTuckerObjective uStar x := hkuhn_star_eq_obj.symm
        have hereal :
            (P.kuhnTuckerObjective u x : EReal) ≤ (P.kuhnTuckerObjective uStar x : EReal) :=
          EReal.coe_le_coe_iff.2 hkuhn_le_star
        simpa [hL_u, hL_star] using hereal
      · -- Outside the multiplier set the Lagrangian is `⊥` at feasible points.
        have hL_u : P.lagrangian u x = (⊥ : EReal) := by
          simpa [helperForTheorem_6_28_4_lagrangian_simp P u x, hxC, hu] using
            (helperForTheorem_6_28_4_lagrangian_simp P u x).2.1 hxC hu
        simpa [hL_u]
    -- Next prove the minimization inequality in the primal variable.
    have hmin : ∀ z : Fin n → ℝ, P.lagrangian uStar x ≤ P.lagrangian uStar z := by
      intro z
      by_cases hzC : z ∈ P.constraintSet
      · rcases hKT with ⟨_, v, hvInf, hvOpt⟩
        have hoptVal : P.optimalValue = ((P.objective x : ℝ) : EReal) :=
          helperForTheorem_6_28_4_optimalValue_eq_objective_of_optimalSolution P hxOpt
        have hvx : (P.kuhnTuckerObjective uStar x : EReal) = (v : EReal) := by
          calc
            (P.kuhnTuckerObjective uStar x : EReal) = ((P.objective x : ℝ) : EReal) := by
              simpa [hkuhn_star_eq_obj]
            _ = P.optimalValue := hoptVal.symm
            _ = (v : EReal) := hvOpt
        have hvle :
            (v : EReal) ≤ ((P.kuhnTuckerObjective uStar z : ℝ) : EReal) := by
          -- `z ∈ C` gives a witness for `sInf_le`.
          rw [← hvInf]
          exact sInf_le ⟨z, hzC, rfl⟩
        have hkuhn_le :
            (P.kuhnTuckerObjective uStar x : EReal) ≤ (P.kuhnTuckerObjective uStar z : EReal) := by
          -- Use the `v` identification from the Kuhn--Tucker hypothesis.
          calc
            (P.kuhnTuckerObjective uStar x : EReal) = (v : EReal) := hvx
            _ ≤ ((P.kuhnTuckerObjective uStar z : ℝ) : EReal) := hvle
        have hL_star_x : P.lagrangian uStar x = (P.kuhnTuckerObjective uStar x : EReal) := by
          simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x, hxC, huStar] using
            (helperForTheorem_6_28_4_lagrangian_simp P uStar x).2.2 hxC huStar
        have hL_star_z : P.lagrangian uStar z = (P.kuhnTuckerObjective uStar z : EReal) := by
          simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar z, hzC, huStar] using
            (helperForTheorem_6_28_4_lagrangian_simp P uStar z).2.2 hzC huStar
        simpa [hL_star_x, hL_star_z] using hkuhn_le
      · -- Outside `C`, the Lagrangian is `⊤`, so the inequality is automatic.
        have hLz : P.lagrangian uStar z = (⊤ : EReal) :=
          (helperForTheorem_6_28_4_lagrangian_simp P uStar z).1 hzC
        simpa [hLz]
    exact ⟨hmax, hmin⟩
  · intro hsaddle
    -- Convert the saddle-point condition into explicit KKT conditions, then recover optimality and
    -- the Kuhn--Tucker vector certificate from those inequalities.
    have hconditions :
        P.SatisfiesKuhnTuckerPointConditions uStar x :=
      (helperForTheorem_6_28_4_lagrangianSaddlePoint_iff_explicitConditions
        P hconstraint_nonempty uStar x).1 hsaddle
    rcases hconditions with ⟨hxC, hineq, heq, _hstationarity⟩
    -- Feasibility is immediate from the explicit constraint conditions.
    have hxFeasible : x ∈ P.feasibleSet := by
      refine ⟨hxC, ?_, ?_⟩
      · intro i
        exact (hineq i).2.1
      · intro j
        exact heq j
    -- Prove optimality by chaining saddle inequalities against any feasible point.
    have huStar : uStar ∈ P.lagrangeMultiplierSet := by
      intro i
      exact (hineq i).1
    have hkuhn_star_eq_obj : P.kuhnTuckerObjective uStar x = P.objective x := by
      have hsum_ineq_zero :
          ∑ i : Fin r, P.inequalityMultipliers uStar i * P.inequalityConstraint i x = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        simpa using (hineq i).2.2
      have hsum_eq_zero :
          ∑ j : Fin (m - r), P.equalityMultipliers uStar j * P.equalityConstraint j x = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        simp [heq j]
      unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
      simp [hsum_ineq_zero, hsum_eq_zero]
    have hL_star_x : P.lagrangian uStar x = ((P.objective x : ℝ) : EReal) := by
      have : P.lagrangian uStar x = (P.kuhnTuckerObjective uStar x : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar x, hxC, huStar] using
          (helperForTheorem_6_28_4_lagrangian_simp P uStar x).2.2 hxC huStar
      simpa [this, hkuhn_star_eq_obj]
    have hxOptimal : ∀ y ∈ P.feasibleSet, P.objective x ≤ P.objective y := by
      intro y hyFeasible
      have hyC : y ∈ P.constraintSet := hyFeasible.1
      have hLag_le : P.lagrangian uStar x ≤ P.lagrangian uStar y := hsaddle.2 y
      have hLy : P.lagrangian uStar y = (P.kuhnTuckerObjective uStar y : EReal) := by
        simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar y, hyC, huStar] using
          (helperForTheorem_6_28_4_lagrangian_simp P uStar y).2.2 hyC huStar
      have hkuhn_le_obj :
          P.kuhnTuckerObjective uStar y ≤ P.objective y :=
        helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible
          P uStar hyFeasible (fun i => (hineq i).1)
      -- Rewrite the saddle inequality as a real inequality.
      have : ((P.objective x : ℝ) : EReal) ≤ ((P.objective y : ℝ) : EReal) := by
        calc
          ((P.objective x : ℝ) : EReal) = P.lagrangian uStar x := hL_star_x.symm
          _ ≤ P.lagrangian uStar y := hLag_le
          _ = (P.kuhnTuckerObjective uStar y : EReal) := hLy
          _ ≤ ((P.objective y : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hkuhn_le_obj
      exact EReal.coe_le_coe_iff.1 this
    have hxOpt : P.IsOptimalSolution x := ⟨hxFeasible, hxOptimal⟩
    -- Now package the Kuhn--Tucker certificate using the saddle inequalities as the infimum data.
    have hKT_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers uStar i := fun i => (hineq i).1
    have hoptVal : P.optimalValue = ((P.objective x : ℝ) : EReal) :=
      helperForTheorem_6_28_4_optimalValue_eq_objective_of_optimalSolution P hxOpt
    have hsInf_eq :
        sInf ((fun z => ((P.kuhnTuckerObjective uStar z : ℝ) : EReal)) '' P.constraintSet) =
          ((P.objective x : ℝ) : EReal) := by
      -- The saddle-point inequality gives `objective x` as a lower bound on the image set.
      have hlower :
          ((P.objective x : ℝ) : EReal) ≤
            sInf ((fun z => ((P.kuhnTuckerObjective uStar z : ℝ) : EReal)) '' P.constraintSet) := by
        refine le_sInf ?_
        rintro _ ⟨z, hzC, rfl⟩
        have hzLag : P.lagrangian uStar x ≤ P.lagrangian uStar z := hsaddle.2 z
        have hLz : P.lagrangian uStar z = (P.kuhnTuckerObjective uStar z : EReal) := by
          simpa [helperForTheorem_6_28_4_lagrangian_simp P uStar z, hzC, huStar] using
            (helperForTheorem_6_28_4_lagrangian_simp P uStar z).2.2 hzC huStar
        -- Rewrite `P.lagrangian uStar x` to `objective x`.
        simpa [hL_star_x, hLz] using hzLag
      -- The infimum is also bounded above by the value at `x` since `x ∈ C`.
      have hupper :
          sInf ((fun z => ((P.kuhnTuckerObjective uStar z : ℝ) : EReal)) '' P.constraintSet) ≤
            ((P.objective x : ℝ) : EReal) := by
        have : sInf ((fun z => ((P.kuhnTuckerObjective uStar z : ℝ) : EReal)) '' P.constraintSet) ≤
            ((P.kuhnTuckerObjective uStar x : ℝ) : EReal) :=
          sInf_le ⟨x, hxC, rfl⟩
        -- Use `kuhnTuckerObjective uStar x = objective x`.
        simpa [hkuhn_star_eq_obj] using this
      exact le_antisymm hupper hlower
    -- Extract the real witness `v = objective x` and close the definition.
    refine ⟨⟨hKT_nonneg, P.objective x, ?_, ?_⟩, hxOpt⟩
    · -- Coerce the infimum equality back to a real number.
      simpa using hsInf_eq
    · -- And match the optimal value with the same real number.
      simpa using hoptVal

-- Proof sketch: for the first equivalence, compare the definition of a Kuhn--Tucker vector with
-- the saddle inequalities for `P.lagrangian`, using that the latter encodes the admissible
-- multiplier cone and the ambient constraint set by `-∞` and `+∞`. For the second equivalence,
-- unpack the saddle inequalities into the complementary-slackness and feasibility relations, and
-- identify the minimizing condition in the primal variable with the textbook subdifferential-sum
-- stationarity condition for the indicator-extended Kuhn--Tucker objective.
/-- Theorem 6.28.4: For an ordinary convex program `P` with nonempty ambient constraint set, a
multiplier vector `uStar` and a point `x`, the following hold:

(a) `uStar` is a Kuhn--Tucker vector for `P` and `x` is an optimal solution of `P` if and only if
`(uStar, x)` is a saddle point of `P.lagrangian`.

(b) The saddle-point condition is equivalent to the explicit Kuhn--Tucker conditions consisting of
membership `x ∈ C = P.constraintSet`, the sign, feasibility, and complementary-slackness relations
for the inequality constraints, the equality constraints `f_i(x) = 0` for `i = r + 1, ..., m`,
and the stationarity condition that `0` belongs to the subdifferential of the
indicator-extended objective `δ_C + f₀ + λ₁ f₁ + ⋯ + λ_m f_m`, equivalently to the textbook
sum of subdifferentials with every zero-multiplier term omitted. -/
theorem kuhnTuckerVector_and_optimalSolution_iff_lagrangianSaddlePoint_iff_explicitConditions
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hconstraint_nonempty : P.constraintSet.Nonempty)
    (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    ((P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution x) ↔
      P.IsLagrangianSaddlePoint uStar x) ∧
      (P.IsLagrangianSaddlePoint uStar x ↔
        P.SatisfiesKuhnTuckerPointConditions uStar x) := by
  -- Route correction: as currently defined, this theorem is not provable without excluding the
  -- degenerate case `P.constraintSet = ∅`. In that case the Lagrangian is constantly `⊤` and
  -- every pair `(uStar, x)` is a saddle point, while `P.IsKuhnTuckerVector uStar` and
  -- `P.IsOptimalSolution x` both fail.
  --
  -- The helper lemma `helperForTheorem_6_28_4_not_kuhnTuckerVector_and_optimalSolution_iff_lagrangianSaddlePoint_of_constraintSet_eq_empty`
  -- records the failure of the first equivalence in that degenerate case.
  -- The helper lemma
  -- `helperForTheorem_6_28_4_not_lagrangianSaddlePoint_iff_kuhnTuckerPointConditions_of_constraintSet_eq_empty`
  -- records the corresponding failure of the second equivalence.
  --
  -- The nonemptiness hypothesis keeps the saddle inequalities from collapsing vacuously on the
  -- empty-set branch. The remaining proof is the intended textbook unpacking of the saddle
  -- inequalities into complementary slackness, equality constraints, and stationarity.
  -- First, use the saddle-point and explicit KKT-condition equivalence.
  have hsaddle_iff :
      P.IsLagrangianSaddlePoint uStar x ↔ P.SatisfiesKuhnTuckerPointConditions uStar x :=
    helperForTheorem_6_28_4_lagrangianSaddlePoint_iff_explicitConditions
      P hconstraint_nonempty uStar x
  -- Then relate saddle points back to the Kuhn--Tucker certificate and primal optimality.
  have hKT_opt_iff :
      (P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution x) ↔ P.IsLagrangianSaddlePoint uStar x :=
    helperForTheorem_6_28_4_kuhnTuckerVector_and_optimalSolution_iff_lagrangianSaddlePoint
      P hconstraint_nonempty uStar x
  exact ⟨hKT_opt_iff, hsaddle_iff⟩

-- Proof sketch: Theorem 6.28.3 gives a Kuhn--Tucker vector under the hypotheses carried here,
-- so any optimal solution admits some multiplier vector. Then Theorem 6.28.4 converts the pair
-- `(uStar, xBar)` between the formulations "optimal plus Kuhn--Tucker vector", "saddle point of
-- the Lagrangian", and "explicit Kuhn--Tucker conditions". The converse directions follow by
-- projecting the optimality statement from the corresponding equivalences in Theorem 6.28.4.
/-- Helper for Corollary 6.28.5: strict feasibility supplies a point of the ambient constraint set,
hence shows `P.constraintSet` is nonempty. -/
lemma helperForCorollary_6_28_5_constraintSet_nonempty_of_hasStrictFeasiblePoint
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    P.constraintSet.Nonempty := by
  -- Unpack the strict-feasible witness and keep only the ambient-constraint membership.
  rcases hstrict_feasible with ⟨x0, _hx0ri, hx0Feasible, _⟩
  rcases hx0Feasible with ⟨hx0C, _, _⟩
  exact ⟨x0, hx0C⟩

/-- Corollary 6.28.5 (Kuhn--Tucker theorem): Let `P` be an ordinary convex program satisfying
the hypotheses of Theorem 6.28.3, namely `P.optimalValue ≠ -∞` and the existence of a feasible
point that is strict on `P.nonaffineInequalityIndices`. Then a given vector `xBar` is an optimal
solution of `P` if and only if there exists a multiplier vector `uStar` such that `(uStar, xBar)`
is a saddle point of the Lagrangian of `P`. Equivalently, `xBar` is an optimal solution of `P`
if and only if there exists a multiplier vector `uStar` such that `uStar` and `xBar` satisfy the
explicit Kuhn--Tucker conditions for `P`. -/
theorem optimalSolution_iff_exists_lagrangianSaddlePoint_iff_exists_kuhnTuckerPointConditions
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices)
    (xBar : Fin n → ℝ) :
    (P.IsOptimalSolution xBar ↔ ∃ uStar : Fin m → ℝ, P.IsLagrangianSaddlePoint uStar xBar) ∧
      (P.IsOptimalSolution xBar ↔
        ∃ uStar : Fin m → ℝ, P.SatisfiesKuhnTuckerPointConditions uStar xBar) := by
  -- Extract the nonemptiness hypothesis required by Theorem 6.28.4 from strict feasibility.
  have hconstraint_nonempty : P.constraintSet.Nonempty :=
    helperForCorollary_6_28_5_constraintSet_nonempty_of_hasStrictFeasiblePoint
      P hstrict_feasible
  -- The goal is a conjunction of two characterizations; prove them separately.
  refine And.intro ?_ ?_
  · -- First: optimality is equivalent to existence of a Lagrangian saddle point.
    constructor
    · intro hxOpt
      -- Theorem 6.28.3 provides a Kuhn--Tucker multiplier vector `uStar` under the hypotheses.
      rcases
          exists_kuhnTuckerVector_of_optimalValue_ne_bot_and_feasiblePoint_strict_on_nonaffineIndices
            P hoptimal_ne_bot hstrict_feasible with
        ⟨uStar, huKT⟩
      -- Theorem 6.28.4(a) converts `(huKT, hxOpt)` into a Lagrangian saddle point.
      have hEquivs :=
        kuhnTuckerVector_and_optimalSolution_iff_lagrangianSaddlePoint_iff_explicitConditions
          P hconstraint_nonempty uStar xBar
      have hsaddle : P.IsLagrangianSaddlePoint uStar xBar :=
        (hEquivs.1).mp ⟨huKT, hxOpt⟩
      -- Package the saddle point as the required existential witness.
      refine ⟨uStar, hsaddle⟩
    · rintro ⟨uStar, hsaddle⟩
      -- From a saddle point, Theorem 6.28.4(a) returns primal optimality.
      have hEquivs :=
        kuhnTuckerVector_and_optimalSolution_iff_lagrangianSaddlePoint_iff_explicitConditions
          P hconstraint_nonempty uStar xBar
      have hKT_opt : P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution xBar :=
        (hEquivs.1).mpr hsaddle
      exact hKT_opt.2
  · -- Second: optimality is equivalent to existence of explicit Kuhn--Tucker point conditions.
    constructor
    · intro hxOpt
      -- Reuse Theorem 6.28.3 to obtain a Kuhn--Tucker vector.
      rcases
          exists_kuhnTuckerVector_of_optimalValue_ne_bot_and_feasiblePoint_strict_on_nonaffineIndices
            P hoptimal_ne_bot hstrict_feasible with
        ⟨uStar, huKT⟩
      -- Convert to a saddle point (Theorem 6.28.4(a)) and then to explicit conditions (6.28.4(b)).
      have hEquivs :=
        kuhnTuckerVector_and_optimalSolution_iff_lagrangianSaddlePoint_iff_explicitConditions
          P hconstraint_nonempty uStar xBar
      have hsaddle : P.IsLagrangianSaddlePoint uStar xBar :=
        (hEquivs.1).mp ⟨huKT, hxOpt⟩
      have hconds : P.SatisfiesKuhnTuckerPointConditions uStar xBar :=
        (hEquivs.2).mp hsaddle
      -- Package the conditions as the required existential witness.
      refine ⟨uStar, hconds⟩
    · rintro ⟨uStar, hconds⟩
      -- Convert explicit conditions back to a saddle point, then project optimality.
      have hEquivs :=
        kuhnTuckerVector_and_optimalSolution_iff_lagrangianSaddlePoint_iff_explicitConditions
          P hconstraint_nonempty uStar xBar
      have hsaddle : P.IsLagrangianSaddlePoint uStar xBar :=
        (hEquivs.2).mpr hconds
      have hKT_opt : P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution xBar :=
        (hEquivs.1).mpr hsaddle
      exact hKT_opt.2

/-- Definition 6.28.8 (Indicator-function reformulation): for a real-valued objective `f₀` and
real-valued constraint functions `f₁, …, f_m` on `ℝ^n`, with `Cᵢ = {x | fᵢ x ≤ 0}`, the
constrained program is represented by the extended-real-valued function
`x ↦ f₀ x + ∑ i, δ(x | Cᵢ)`. -/
noncomputable def indicatorReformulationObjective {n m : ℕ}
    (f₀ : (Fin n → ℝ) → ℝ) (constraints : Fin m → (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → EReal :=
  fun x =>
    (f₀ x : EReal) +
      ∑ i : Fin m, indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0} x

end Section28
end Chap06
