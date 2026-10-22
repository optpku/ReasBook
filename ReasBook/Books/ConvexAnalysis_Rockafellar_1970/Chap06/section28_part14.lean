/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part13

open scoped BigOperators Pointwise

section Chap06
section Section28

-- Proof sketch: Theorem 6.28.6 shows that every Kuhn--Tucker vector `u` satisfies
-- `P.lagrangianPrimalInf u = P.lagrangianMaximin`, where `P.lagrangianPrimalInf` is the book's
-- dual function `g(u) = inf_x L(u, x)`. Conversely, if some `uStar` attains this supremum and
-- there already exists a Kuhn--Tucker vector for `P`, then the supremum value is strictly above
-- `-∞`; the same theorem then yields that `uStar` is itself a Kuhn--Tucker vector.
/-- Helper for Corollary 6.28.6: the existence of one Kuhn--Tucker vector already forces the
constraint set of `P` to be nonempty. -/
lemma helperForCorollary_6_28_6_constraintSet_nonempty_of_existsKuhnTuckerVector
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (h_exists : ∃ u : Fin m → ℝ, P.IsKuhnTuckerVector u) :
    P.constraintSet.Nonempty := by
  rcases h_exists with ⟨u0, hKT0⟩
  -- Reuse the earlier corollary: any Kuhn--Tucker vector gives a feasible point.
  exact helperForCorollary_6_28_1_constraintSet_nonempty P u0 hKT0

/-- Helper for Corollary 6.28.6: if one Kuhn--Tucker vector exists and `uStar` already attains the
dual supremum value, then `uStar` also satisfies the nondegenerate minmax chain from Theorem
6.28.6. -/
lemma helperForCorollary_6_28_6_minmaxChain_of_exists_and_eq_lagrangianMaximin
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (h_exists : ∃ u : Fin m → ℝ, P.IsKuhnTuckerVector u) (uStar : Fin m → ℝ)
    (heq : P.lagrangianPrimalInf uStar = P.lagrangianMaximin) :
    (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
      P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
      P.lagrangianMaximin = P.lagrangianMinimax := by
  rcases h_exists with ⟨u0, hKT0⟩
  -- Start from an existing Kuhn--Tucker vector to recover the strict/nondegenerate chain.
  rcases helperForTheorem_6_28_6_minmax_chain_of_isKuhnTuckerVector P hKT0 with
    ⟨hbot0, hInf0Eq, hMaxEqMin⟩
  refine ⟨?_, heq, hMaxEqMin⟩
  -- Transport the strict lower bound along the common maximin value.
  calc
    (⊥ : EReal) < P.lagrangianPrimalInf u0 := hbot0
    _ = P.lagrangianMaximin := hInf0Eq
    _ = P.lagrangianPrimalInf uStar := heq.symm

/-- Helper for Corollary 6.28.6: once a Kuhn--Tucker vector exists, Theorem 6.28.6 reduces the
target statement to the middle minmax-chain equivalence on the nonempty branch. -/
lemma helperForCorollary_6_28_6_middleIff_of_exists
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (h_exists : ∃ u : Fin m → ℝ, P.IsKuhnTuckerVector u) (uStar : Fin m → ℝ) :
    P.IsKuhnTuckerVector uStar ↔
      (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
        P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
        P.lagrangianMaximin = P.lagrangianMinimax := by
  have hconstraint_nonempty :
      P.constraintSet.Nonempty :=
    helperForCorollary_6_28_6_constraintSet_nonempty_of_existsKuhnTuckerVector P h_exists
  -- Apply the middle equivalence from Theorem 6.28.6 with a dummy primal point.
  exact
    (isKuhnTuckerVector_iff_lagrangianPrimalInf_eq_maximin_eq_minimax_and_saddleValue
      P hconstraint_nonempty uStar (fun _ : Fin n => 0)).2.1

/-- Helper for Corollary 6.28.6: every Kuhn--Tucker vector already attains the dual supremum
value `P.lagrangianMaximin`. -/
lemma helperForCorollary_6_28_6_forward_eq_lagrangianMaximin_of_isKuhnTuckerVector
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
    (hKT : P.IsKuhnTuckerVector uStar) :
    P.lagrangianPrimalInf uStar = P.lagrangianMaximin := by
  -- Compare the primal infimum and the maximin value through the common optimal value.
  rcases
      helperForTheorem_6_28_6_extremalValues_eq_optimalValue_of_isKuhnTuckerVector P hKT with
    ⟨hInfEqOpt, hMaxEqOpt, _hMinEqOpt⟩
  calc
    P.lagrangianPrimalInf uStar = P.optimalValue := hInfEqOpt
    _ = P.lagrangianMaximin := hMaxEqOpt.symm

/-- Corollary 6.28.6: Let `(P)` be an ordinary convex program having at least one Kuhn--Tucker
vector. Let `g(u) = inf_x L(u, x)`, where `L = P.lagrangian`; in this file `g` is represented by
`P.lagrangianPrimalInf`, and its supremum over `ℝ^m` is `P.lagrangianMaximin`. Then a multiplier
vector `uStar` is a Kuhn--Tucker vector for `P` if and only if `g` attains its supremum at
`uStar`, equivalently if and only if
`P.lagrangianPrimalInf uStar = P.lagrangianMaximin`. -/
theorem isKuhnTuckerVector_iff_lagrangianPrimalInf_eq_lagrangianMaximin_of_exists
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (h_exists : ∃ u : Fin m → ℝ, P.IsKuhnTuckerVector u) (uStar : Fin m → ℝ) :
    P.IsKuhnTuckerVector uStar ↔ P.lagrangianPrimalInf uStar = P.lagrangianMaximin := by
  constructor
  · intro hKT
    -- The forward implication is the direct equality supplied by Theorem 6.28.6.
    exact
      helperForCorollary_6_28_6_forward_eq_lagrangianMaximin_of_isKuhnTuckerVector P uStar hKT
  · intro heq
    -- Reconstruct the minmax chain from an existing Kuhn--Tucker vector and the assumed equality.
    have hchain :
        (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
          P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
          P.lagrangianMaximin = P.lagrangianMinimax :=
      helperForCorollary_6_28_6_minmaxChain_of_exists_and_eq_lagrangianMaximin
        P h_exists uStar heq
    -- The middle equivalence from Theorem 6.28.6 now yields the converse.
    have hiff :
        P.IsKuhnTuckerVector uStar ↔
          (⊥ : EReal) < P.lagrangianPrimalInf uStar ∧
            P.lagrangianPrimalInf uStar = P.lagrangianMaximin ∧
            P.lagrangianMaximin = P.lagrangianMinimax :=
      helperForCorollary_6_28_6_middleIff_of_exists P h_exists uStar
    exact hiff.2 hchain

-- Proof sketch: fix `x`. On the admissible multiplier cone the Lagrangian is the affine map
-- `lambda ↦ f₀(x) + ∑ᵢ lambdaᵢ fᵢ(x)`, while outside that cone the present definition of
-- `P.lagrangian` takes the value `-∞`; this preserves the Jensen inequality expressing
-- concavity in the multiplier variable.
/-- Helper for Proposition 6.28.3: the Lagrangian splits into the feasible/admissible,
feasible/inadmissible, and infeasible branches dictated by Definition 6.28.6. -/
lemma helperForProposition_6_28_3_lagrangian_cases
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (u : Fin m → ℝ) (x : Fin n → ℝ) :
    (x ∉ P.constraintSet → P.lagrangian u x = (⊤ : EReal)) ∧
      (x ∈ P.constraintSet → u ∉ P.lagrangeMultiplierSet → P.lagrangian u x = (⊥ : EReal)) ∧
      (x ∈ P.constraintSet → u ∈ P.lagrangeMultiplierSet →
        P.lagrangian u x = (P.kuhnTuckerObjective u x : EReal)) := by
  constructor
  · intro hx
    -- Outside `P.constraintSet`, the outer `if` in `P.lagrangian` falls to the `⊤` branch.
    simp [BookOrdinaryConvexProgram.lagrangian, hx]
  constructor
  · intro hx hu
    -- On the feasible branch, inadmissible multipliers force the inner `if` to the `⊥` branch.
    simp [BookOrdinaryConvexProgram.lagrangian, hx, hu]
  · intro hx hu
    -- On the feasible/admissible branch, `P.lagrangian` is exactly the extended
    -- Kuhn--Tucker objective.
    simp [BookOrdinaryConvexProgram.lagrangian, hx, hu]

/-- Helper for Proposition 6.28.3: a nonnegative convex combination of admissible multipliers
stays in `P.lagrangeMultiplierSet`. -/
lemma helperForProposition_6_28_3_convexCombination_mem_lagrangeMultiplierSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (u v : Fin m → ℝ) {a b : ℝ}
    (hu : u ∈ P.lagrangeMultiplierSet) (hv : v ∈ P.lagrangeMultiplierSet)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • u + b • v ∈ P.lagrangeMultiplierSet := by
  intro i
  -- Check the inequality coordinates one by one and preserve nonnegativity under scaling/addition.
  have hu' : 0 ≤ P.inequalityMultipliers u i := by
    simpa [BookOrdinaryConvexProgram.lagrangeMultiplierSet] using hu i
  have hv' : 0 ≤ P.inequalityMultipliers v i := by
    simpa [BookOrdinaryConvexProgram.lagrangeMultiplierSet] using hv i
  simpa [BookOrdinaryConvexProgram.inequalityMultipliers, smul_eq_mul, add_mul, mul_add] using
    add_nonneg (mul_nonneg ha hu') (mul_nonneg hb hv')

/-- Helper for Proposition 6.28.3: at a fixed primal point `x`, the finite Kuhn--Tucker branch is
affine in the multiplier variable. -/
lemma helperForProposition_6_28_3_kuhnTuckerObjective_affine_in_multiplier
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (u v : Fin m → ℝ) (x : Fin n → ℝ) {a b : ℝ}
    (hab : a + b = 1) :
    P.kuhnTuckerObjective (a • u + b • v) x =
      a * P.kuhnTuckerObjective u x + b * P.kuhnTuckerObjective v x := by
  -- Expand the multiplier coordinates and collect coefficients using `a + b = 1`.
  unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
  simp [BookOrdinaryConvexProgram.inequalityMultipliers,
    BookOrdinaryConvexProgram.equalityMultipliers, smul_eq_mul,
    Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul]
  ring_nf
  have hobjective :
      P.objective x = P.objective x * a + P.objective x * b := by
    have hmul := congrArg (fun t : ℝ => P.objective x * t) hab
    simpa [mul_add, mul_one] using hmul.symm
  conv_lhs => rw [hobjective]

/-- Helper for Proposition 6.28.3: on the feasible primal branch and inside the multiplier cone,
the Lagrangian satisfies the affine Jensen identity in the multiplier variable. -/
lemma helperForProposition_6_28_3_lagrangian_affine_on_admissible_branch
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (x : Fin n → ℝ)
    (u v : Fin m → ℝ) {a b : ℝ}
    (hx : x ∈ P.constraintSet)
    (hu : u ∈ P.lagrangeMultiplierSet) (hv : v ∈ P.lagrangeMultiplierSet)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ((a : EReal) * P.lagrangian u x + (b : EReal) * P.lagrangian v x) =
      P.lagrangian (a • u + b • v) x := by
  -- First keep the convex combination inside the admissible multiplier cone.
  have hcombo : a • u + b • v ∈ P.lagrangeMultiplierSet :=
    helperForProposition_6_28_3_convexCombination_mem_lagrangeMultiplierSet P u v hu hv ha hb
  -- On the feasible/admissible branch, every Lagrangian term is just the finite Kuhn--Tucker
  -- objective.
  have huLag : P.lagrangian u x = (P.kuhnTuckerObjective u x : EReal) :=
    (helperForProposition_6_28_3_lagrangian_cases P u x).2.2 hx hu
  have hvLag : P.lagrangian v x = (P.kuhnTuckerObjective v x : EReal) :=
    (helperForProposition_6_28_3_lagrangian_cases P v x).2.2 hx hv
  have hcomboLag : P.lagrangian (a • u + b • v) x =
      (P.kuhnTuckerObjective (a • u + b • v) x : EReal) :=
    (helperForProposition_6_28_3_lagrangian_cases P (a • u + b • v) x).2.2 hx hcombo
  -- The remaining step is the affine identity for the finite branch, transported to `EReal`.
  rw [huLag, hvLag, hcomboLag,
    helperForProposition_6_28_3_kuhnTuckerObjective_affine_in_multiplier P u v x hab]
  norm_num [EReal.coe_add, EReal.coe_mul]

/-- Proposition 6.28.3: For each `x ∈ ℝ^n`, the function `u ↦ P.lagrangian u x` is concave on
`ℝ^m`, expressed here by the concavity inequality for convex combinations of multiplier vectors. -/
theorem lagrangian_concave_in_multiplier
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (x : Fin n → ℝ)
    (u v : Fin m → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ((a : EReal) * P.lagrangian u x + (b : EReal) * P.lagrangian v x) ≤
      P.lagrangian (a • u + b • v) x := by
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    -- If `a = 0`, the convex combination collapses to the `v` endpoint.
    subst ha0
    subst hb1
    simp
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    -- If `b = 0`, the convex combination collapses to the `u` endpoint.
    subst hb0
    subst ha1
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  by_cases hx : x ∈ P.constraintSet
  · by_cases hu : u ∈ P.lagrangeMultiplierSet
    · by_cases hv : v ∈ P.lagrangeMultiplierSet
      · -- On the feasible/admissible branch, the Lagrangian is exactly affine in the multiplier.
        exact le_of_eq <|
          helperForProposition_6_28_3_lagrangian_affine_on_admissible_branch
            P x u v hx hu hv ha hb hab
      · -- A positive weight on an inadmissible endpoint produces `-∞`, so the Jensen inequality
        -- is automatic.
        have hvLag : P.lagrangian v x = (⊥ : EReal) :=
          (helperForProposition_6_28_3_lagrangian_cases P v x).2.1 hx hv
        have hleft_bot :
            ((a : EReal) * P.lagrangian u x + (b : EReal) * P.lagrangian v x) = (⊥ : EReal) := by
          rw [hvLag, EReal.mul_bot_of_pos (by exact_mod_cast hb_pos)]
          exact EReal.add_bot ((a : EReal) * P.lagrangian u x)
        rw [hleft_bot]
        exact bot_le
    · -- Symmetrically, a positive weight on the inadmissible `u` endpoint forces the left-hand
      -- side to `-∞`.
      have huLag : P.lagrangian u x = (⊥ : EReal) :=
        (helperForProposition_6_28_3_lagrangian_cases P u x).2.1 hx hu
      have hleft_bot :
          ((a : EReal) * P.lagrangian u x + (b : EReal) * P.lagrangian v x) = (⊥ : EReal) := by
        rw [huLag, EReal.mul_bot_of_pos (by exact_mod_cast ha_pos)]
        exact EReal.bot_add ((b : EReal) * P.lagrangian v x)
      rw [hleft_bot]
      exact bot_le
  · -- Outside `P.constraintSet`, every Lagrangian value is `+∞`, so the right-hand side is
    -- already the top element.
    have hcomboLag : P.lagrangian (a • u + b • v) x = (⊤ : EReal) :=
      (helperForProposition_6_28_3_lagrangian_cases P (a • u + b • v) x).1 hx
    rw [hcomboLag]
    exact le_top

-- Proof sketch: for each index `i`, apply the assumed concavity inequality to `f i`. The values
-- `sInf (Set.range fun j => f j u)` and `sInf (Set.range fun j => f j v)` are lower bounds for
-- the corresponding ranges, so the left-hand side is bounded above by
-- `(a : EReal) * f i u + (b : EReal) * f i v` for every `i`. Each of these is in turn bounded
-- above by `f i (a • u + b • v)`, hence by the infimum of that range.
/-- Helper for Proposition 6.28.4: the pointwise infimum over the indexed range is below each
individual slice value. -/
lemma helperForProposition_6_28_4_sliceInfimum_le_sliceValue
    {ι : Sort*} {m : ℕ} (f : ι → (Fin m → ℝ) → EReal)
    (x : Fin m → ℝ) (i : ι) :
    sInf (Set.range fun j : ι => f j x) ≤ f i x := by
  -- The chosen slice value is one of the values whose infimum defines the left-hand side.
  exact sInf_le ⟨i, rfl⟩

/-- Helper for Proposition 6.28.4: each index `i` bounds the weighted sum of the two pointwise
infima by the concavity estimate for the `i`-th slice. -/
lemma helperForProposition_6_28_4_indexwise_bound_for_pointwise_infimum
    {ι : Sort*} {m : ℕ} (f : ι → (Fin m → ℝ) → EReal)
    (hf : ∀ i : ι,
      ∀ (u v : Fin m → ℝ) {a b : ℝ},
        0 ≤ a → 0 ≤ b → a + b = 1 →
          ((a : EReal) * f i u + (b : EReal) * f i v) ≤
            f i (a • u + b • v))
    (i : ι) (u v : Fin m → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ((a : EReal) * sInf (Set.range fun j : ι => f j u) +
        (b : EReal) * sInf (Set.range fun j : ι => f j v)) ≤
      f i (a • u + b • v) := by
  -- Bound each pointwise infimum by the chosen slice value.
  have hu :
      sInf (Set.range fun j : ι => f j u) ≤ f i u :=
    helperForProposition_6_28_4_sliceInfimum_le_sliceValue f u i
  have hv :
      sInf (Set.range fun j : ι => f j v) ≤ f i v :=
    helperForProposition_6_28_4_sliceInfimum_le_sliceValue f v i
  -- Nonnegative scaling preserves these lower bounds.
  have hau :
      (a : EReal) * sInf (Set.range fun j : ι => f j u) ≤
        (a : EReal) * f i u := by
    exact mul_le_mul_of_nonneg_left hu (by exact_mod_cast ha)
  have hbv :
      (b : EReal) * sInf (Set.range fun j : ι => f j v) ≤
        (b : EReal) * f i v := by
    exact mul_le_mul_of_nonneg_left hv (by exact_mod_cast hb)
  -- Add the two bounds and finish with the assumed concavity of the `i`-th slice.
  have hsum :
      ((a : EReal) * sInf (Set.range fun j : ι => f j u) +
          (b : EReal) * sInf (Set.range fun j : ι => f j v)) ≤
        ((a : EReal) * f i u + (b : EReal) * f i v) :=
    add_le_add hau hbv
  exact le_trans hsum (hf i u v ha hb hab)

/-- Proposition 6.28.4: The pointwise infimum of a family of concave `EReal`-valued functions on
`ℝ^m`, written as an `sInf` over the pointwise value set, is concave in the Jensen-inequality
sense. -/
theorem sInf_range_concave_of_pointwise_concave
    {ι : Sort*} {m : ℕ} (f : ι → (Fin m → ℝ) → EReal)
    (hf : ∀ i : ι,
      ∀ (u v : Fin m → ℝ) {a b : ℝ},
        0 ≤ a → 0 ≤ b → a + b = 1 →
          ((a : EReal) * f i u + (b : EReal) * f i v) ≤
            f i (a • u + b • v)) :
    ∀ (u v : Fin m → ℝ) {a b : ℝ},
      0 ≤ a → 0 ≤ b → a + b = 1 →
        ((a : EReal) * sInf (Set.range fun i : ι => f i u) +
            (b : EReal) * sInf (Set.range fun i : ι => f i v)) ≤
          sInf (Set.range fun i : ι => f i (a • u + b • v)) := by
  intro u v a b ha hb hab
  -- Show that the weighted sum of infima is a lower bound for every point in the target range.
  refine le_sInf ?_
  rintro z ⟨i, rfl⟩
  -- The helper packages the two `sInf_le` bounds and the concavity inequality for the `i`-th slice.
  exact
    helperForProposition_6_28_4_indexwise_bound_for_pointwise_infimum
      f hf i u v ha hb hab

-- Proof sketch: apply Proposition 6.28.4 to the family of functions
-- `u ↦ P.lagrangian u x`, indexed by `x : Fin n → ℝ`. Proposition 6.28.3 supplies the required
-- pointwise concavity in the multiplier variable for each fixed `x`, and the resulting `sInf`
-- over `x` is exactly `P.lagrangianPrimalInf`.
/-- Helper for Corollary 6.28.7: each fixed primal point `x` contributes a concave slice
`u ↦ P.lagrangian u x` in the multiplier variable. -/
lemma helperForCorollary_6_28_7_pointwise_concavity_family
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    ∀ x : Fin n → ℝ,
      ∀ (u v : Fin m → ℝ) {a b : ℝ},
        0 ≤ a → 0 ≤ b → a + b = 1 →
          ((a : EReal) * P.lagrangian u x + (b : EReal) * P.lagrangian v x) ≤
            P.lagrangian (a • u + b • v) x := by
  intro x u v a b ha hb hab
  -- Reuse Proposition 6.28.3 on the fixed slice indexed by `x`.
  exact lagrangian_concave_in_multiplier P x u v ha hb hab

/-- Helper for Corollary 6.28.7: Proposition 6.28.4 specializes to the family of Lagrangian
slices indexed by primal points, giving concavity of the defining pointwise infimum. -/
lemma helperForCorollary_6_28_7_sInfRange_concavity_specialization
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    ∀ (u v : Fin m → ℝ) {a b : ℝ},
      0 ≤ a → 0 ≤ b → a + b = 1 →
        ((a : EReal) * sInf (Set.range fun x : Fin n → ℝ => P.lagrangian u x) +
            (b : EReal) * sInf (Set.range fun x : Fin n → ℝ => P.lagrangian v x)) ≤
          sInf (Set.range fun x : Fin n → ℝ => P.lagrangian (a • u + b • v) x) := by
  intro u v a b ha hb hab
  -- Apply the abstract `sInf`-concavity theorem to the Lagrangian family `x ↦ P.lagrangian · x`.
  exact
    sInf_range_concave_of_pointwise_concave
      (f := fun x uStar => P.lagrangian uStar x)
      (hf := helperForCorollary_6_28_7_pointwise_concavity_family P)
      u v ha hb hab

/-- Corollary 6.28.7: The function `g(uStar) = inf_x L(uStar, x)` is concave on `ℝ^m`; in this
file, `g` is represented by `P.lagrangianPrimalInf`, and concavity is expressed by the Jensen
inequality for convex combinations of multiplier vectors. -/
theorem lagrangianPrimalInf_concave
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    ∀ (u v : Fin m → ℝ) {a b : ℝ},
      0 ≤ a → 0 ≤ b → a + b = 1 →
        ((a : EReal) * P.lagrangianPrimalInf u + (b : EReal) * P.lagrangianPrimalInf v) ≤
          P.lagrangianPrimalInf (a • u + b • v) := by
  intro u v a b ha hb hab
  -- Rewrite the dual function by the `sInf` formula and use the specialized concavity helper.
  simpa [BookOrdinaryConvexProgram.lagrangianPrimalInf] using
    (helperForCorollary_6_28_7_sInfRange_concavity_specialization P
      u v ha hb hab)

/-- Definition 6.28.9 (The functions `q_k`): a family `q = (q_k)_{k=1}^n` of proper convex
functions on `ℝ`, represented in this project on the one-dimensional space `Fin 1 → ℝ`, such
that `dom q_k ⊇ [0,1]` for every `k`. Here `[0,1]` is written as the box
`Set.Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ))`. -/
def IsProperConvexFunctionFamilyOnUnitInterval
    (n : ℕ) (q : Fin n → (Fin 1 → ℝ) → EReal) : Prop :=
  ∀ k : Fin n,
    ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (q k) ∧
      Set.Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) ⊆
        effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (q k)

/-- An optimization problem with an extended-real-valued objective and a feasible set. -/
structure ExtendedRealOptimizationProblem (α : Type*) where
  objective : α → EReal
  feasibleSet : Set α

/-- Definition 6.28.10 (The optimization problem): for a family
`q = (q_k)_{k = 1}^n` satisfying Definition 6.28.9, minimize
`q(x) = q₁(ξ₁) + ⋯ + qₙ(ξₙ)` over the vectors `x = (ξ₁, …, ξₙ)` with
nonnegative coordinates summing to `1`. Each scalar `ξ_k` is viewed as a point
of `ℝ^1` via the constant function `fun _ : Fin 1 => ξ_k`. -/
def unitSimplexSeparableOptimizationProblem
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q}) :
    ExtendedRealOptimizationProblem (Fin n → ℝ) :=
  { objective := fun x => ∑ k : Fin n, q.1 k (fun _ : Fin 1 => x k)
    feasibleSet := {x | (∀ k : Fin n, 0 ≤ x k) ∧ ∑ k : Fin n, x k = 1} }

/-- A pair of coordinate families used to rewrite a separable unit-simplex problem in ordinary
convex-program form. -/
structure SeparableUnitSimplexReformulationData (n : ℕ) where
  f0 : Fin n → (Fin 1 → ℝ) → EReal
  f1 : Fin n → (Fin 1 → ℝ) → ℝ

/-- The extended-real coordinate objective that encodes the nonnegativity constraint by assigning
`+∞` to negative inputs. -/
noncomputable def unitSimplexCoordinateObjective
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (k : Fin n) : (Fin 1 → ℝ) → EReal :=
  fun ξ => if 0 ≤ ξ 0 then q.1 k ξ else (⊤ : EReal)

/-- Restricting a proper convex coordinate objective to the nonnegative half-line by extending
it with `⊤` preserves proper convexity. -/
lemma unitSimplexCoordinateObjective_proper
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (k : Fin n) :
    ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
      (unitSimplexCoordinateObjective q k) := by
  have hqProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (q.1 k) :=
    (q.2 k).1
  have hnotbot : ∀ ξ, unitSimplexCoordinateObjective q k ξ ≠ (⊥ : EReal) := by
    intro ξ
    by_cases hξ : 0 ≤ ξ 0
    · simpa [unitSimplexCoordinateObjective, hξ] using hqProper.2.2 ξ (Set.mem_univ ξ)
    · simp [unitSimplexCoordinateObjective, hξ]
  refine ⟨?_, ?_, fun ξ _ => hnotbot ξ⟩
  · refine
      (convexFunctionOn_iff_segment_inequality
        (C := (Set.univ : Set (Fin 1 → ℝ))) (f := unitSimplexCoordinateObjective q k)
        convex_univ (fun ξ _ => hnotbot ξ)).2 ?_
    have hqSegment :=
      (convexFunctionOn_iff_segment_inequality
        (C := (Set.univ : Set (Fin 1 → ℝ))) (f := q.1 k) convex_univ hqProper.2.2).1
        hqProper.1
    intro x _ y _ t ht0 ht1
    by_cases hx : 0 ≤ x 0
    · by_cases hy : 0 ≤ y 0
      · have hcombo : 0 ≤ (1 - t) * x 0 + t * y 0 :=
          add_nonneg (mul_nonneg (sub_nonneg.mpr ht1.le) hx) (mul_nonneg ht0.le hy)
        simpa [unitSimplexCoordinateObjective, hx, hy, hcombo, smul_eq_mul] using
          hqSegment x (Set.mem_univ x) y (Set.mem_univ y) t ht0 ht1
      · have hyTop : unitSimplexCoordinateObjective q k y = (⊤ : EReal) := by
          simp [unitSimplexCoordinateObjective, hy]
        have hleftNeBot :
            (((1 - t : ℝ) : EReal) * unitSimplexCoordinateObjective q k x) ≠ (⊥ : EReal) :=
          ereal_mul_ne_bot_of_pos (sub_pos.mpr ht1) (hnotbot x)
        rw [hyTop, EReal.mul_top_of_pos (EReal.coe_pos.mpr ht0)]
        rw [EReal.add_top_of_ne_bot hleftNeBot]
        exact le_top
    · have hxTop : unitSimplexCoordinateObjective q k x = (⊤ : EReal) := by
        simp [unitSimplexCoordinateObjective, hx]
      have hrightNeBot :
          (((t : ℝ) : EReal) * unitSimplexCoordinateObjective q k y) ≠ (⊥ : EReal) :=
        ereal_mul_ne_bot_of_pos ht0 (hnotbot y)
      rw [hxTop, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ht1))]
      rw [EReal.top_add_of_ne_bot hrightNeBot]
      exact le_top
  · apply
      (nonempty_epigraph_iff_nonempty_effectiveDomain
        (Set.univ : Set (Fin 1 → ℝ)) (unitSimplexCoordinateObjective q k)).2
    have hzeroInterval :
        (0 : Fin 1 → ℝ) ∈
          Set.Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) := by
      constructor <;> intro i <;> simp
    have hzeroDom :
        (0 : Fin 1 → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (q.1 k) :=
      (q.2 k).2 hzeroInterval
    have hzeroTop : q.1 k (0 : Fin 1 → ℝ) ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top hzeroDom
    refine ⟨(0 : Fin 1 → ℝ), (q.1 k 0).toReal,
      Set.mem_univ (0 : Fin 1 → ℝ), ?_⟩
    simp only [unitSimplexCoordinateObjective, Pi.zero_apply, le_refl, if_pos]
    rw [EReal.coe_toReal hzeroTop
      (hqProper.2.2 (0 : Fin 1 → ℝ) (Set.mem_univ (0 : Fin 1 → ℝ)))]

/-- The simultaneous finite-value set of the unit-simplex coordinate objectives is convex. -/
lemma unitSimplexCoordinateFiniteSet_convex
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q}) :
    Convex ℝ
      {x : Fin n → ℝ |
        ∀ k : Fin n,
          unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) ≠ (⊤ : EReal)} := by
  intro x hx y hy a b ha hb hab
  intro k
  have hProper := unitSimplexCoordinateObjective_proper q k
  let xk : Fin 1 → ℝ := fun _ => x k
  let yk : Fin 1 → ℝ := fun _ => y k
  have hxDom :
      xk ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
        (unitSimplexCoordinateObjective q k) := by
    refine ⟨(unitSimplexCoordinateObjective q k xk).toReal, Set.mem_univ xk, ?_⟩
    rw [EReal.coe_toReal (hx k) (hProper.2.2 xk (Set.mem_univ xk))]
  have hyDom :
      yk ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
        (unitSimplexCoordinateObjective q k) := by
    refine ⟨(unitSimplexCoordinateObjective q k yk).toReal, Set.mem_univ yk, ?_⟩
    rw [EReal.coe_toReal (hy k) (hProper.2.2 yk (Set.mem_univ yk))]
  have hcombo :=
    (effectiveDomain_convex
      (S := (Set.univ : Set (Fin 1 → ℝ)))
      (f := unitSimplexCoordinateObjective q k) hProper.1) hxDom hyDom ha hb hab
  have hneTop := mem_effectiveDomain_imp_ne_top hcombo
  simpa [xk, yk, smul_eq_mul] using hneTop

/-- The sum of the real parts of the coordinate objectives is convex on their simultaneous
finite-value set. -/
lemma unitSimplexCoordinateToRealSum_convexOn
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q}) :
    ConvexOn ℝ
      {x : Fin n → ℝ |
        ∀ k : Fin n,
          unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) ≠ (⊤ : EReal)}
      (fun x =>
        ∑ k : Fin n, (unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k)).toReal) := by
  refine ⟨unitSimplexCoordinateFiniteSet_convex q, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  have hProper := unitSimplexCoordinateObjective_proper q k
  let xk : Fin 1 → ℝ := fun _ => x k
  let yk : Fin 1 → ℝ := fun _ => y k
  have hxDom :
      xk ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
        (unitSimplexCoordinateObjective q k) := by
    refine ⟨(unitSimplexCoordinateObjective q k xk).toReal, Set.mem_univ xk, ?_⟩
    rw [EReal.coe_toReal (hx k) (hProper.2.2 xk (Set.mem_univ xk))]
  have hyDom :
      yk ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
        (unitSimplexCoordinateObjective q k) := by
    refine ⟨(unitSimplexCoordinateObjective q k yk).toReal, Set.mem_univ yk, ?_⟩
    rw [EReal.coe_toReal (hy k) (hProper.2.2 yk (Set.mem_univ yk))]
  have hcoord :=
    (convexOn_toReal_effectiveDomain hProper).2 hxDom hyDom ha hb hab
  simpa [xk, yk, smul_eq_mul] using hcoord

/-- There are no inequality constraints in the unit-simplex reformulation. -/
lemma unitSimplexNoInequalityConstraints_convexOn
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q}) :
    ∀ i : Fin 0,
      ConvexOn ℝ
        {x : Fin n → ℝ |
          ∀ k : Fin n,
            unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) ≠ (⊤ : EReal)}
        (Fin.elim0 i : (Fin n → ℝ) → ℝ) := by
  intro i
  exact Fin.elim0 i

/-- The simplex sum constraint is affine on the coordinate finite-value set. -/
lemma unitSimplexSumConstraint_affineOn
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q}) :
    ∀ _i : Fin 1,
      AffineOnSet (Fin n → ℝ)
        {x : Fin n → ℝ |
          ∀ k : Fin n,
            unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) ≠ (⊤ : EReal)}
        (fun x => ∑ k : Fin n, x k - 1) := by
  intro _i
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ k : Fin n, x k
      map_add' := by
        intro x y
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp [Finset.mul_sum] }
  have hMapVadd :
      ∀ (p : Fin n → ℝ) (v : Fin n → ℝ),
        (∑ k : Fin n, (v + p) k) - 1 = L v + ((∑ k : Fin n, p k) - 1) := by
    intro p v
    simp [L, Finset.sum_add_distrib]
    ring
  let A : (Fin n → ℝ) →ᵃ[ℝ] ℝ :=
    AffineMap.mk (fun x => ∑ k : Fin n, x k - 1) L hMapVadd
  exact ⟨A, fun _x _hx => rfl⟩

/-- The zero inequality count is bounded by the single equality-constraint count. -/
lemma unitSimplexInequalityCount_le_constraintCount : 0 ≤ 1 := by
  decide

/-- The affine coordinate constraint used to encode the simplex equation
`ξ₁ + ⋯ + ξₙ = 1`, with the final coordinate shifted by `1`. -/
def unitSimplexCoordinateAffineConstraint
    {n : ℕ} (k : Fin n) : (Fin 1 → ℝ) → ℝ :=
  fun ξ => if k.1 + 1 = n then ξ 0 - 1 else ξ 0

/-- Definition 6.28.11 (The function `f0k`): to express the unit-simplex separable optimization
problem in the ordinary-convex-program form, define the coordinate families by
`f₀ₖ(ξ) = q_k(ξ)` when `ξ 0 ≥ 0` and `f₀ₖ(ξ) = +∞` when `ξ 0 < 0`, and define
`f₁ₖ(ξ) = ξ 0` for the nonfinal indices while `f₁ₖ(ξ) = ξ 0 - 1` for the final index. -/
noncomputable def unitSimplexOrdinaryConvexReformulationData
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q}) :
    SeparableUnitSimplexReformulationData n :=
  { f0 := fun k => unitSimplexCoordinateObjective q k
    f1 := unitSimplexCoordinateAffineConstraint }

/-- The ordinary convex program corresponding to the unit-simplex separable reformulation
determined by `q`. -/
noncomputable def unitSimplexSeparableOrdinaryConvexProgram
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q}) :
    BookOrdinaryConvexProgram n 1 0 :=
  { constraintSet :=
      {x | ∀ k : Fin n, unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) ≠ (⊤ : EReal)}
    objective := fun x =>
      ∑ k : Fin n, (unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k)).toReal
    inequalityConstraint := fun i => Fin.elim0 i
    equalityConstraint := fun _ x => ∑ k : Fin n, x k - 1
    inequalityCount_le_constraintCount := unitSimplexInequalityCount_le_constraintCount
    convex_constraintSet := unitSimplexCoordinateFiniteSet_convex q
    objective_convexOn := unitSimplexCoordinateToRealSum_convexOn q
    inequalityConstraint_convexOn := unitSimplexNoInequalityConstraints_convexOn q
    equalityConstraint_affineOn := unitSimplexSumConstraint_affineOn q }

/-- The Lagrangian of the unit-simplex separable reformulation with scalar multiplier `vStar`. -/
noncomputable def unitSimplexSeparableLagrangian
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (vStar : ℝ) (x : Fin n → ℝ) : EReal :=
  let data := unitSimplexOrdinaryConvexReformulationData q
  ∑ k : Fin n,
    (data.f0 k (fun _ : Fin 1 => x k) +
      ((vStar * (data.f1 k (fun _ : Fin 1 => x k)) : ℝ) : EReal))

/-- The dual function `g(vStar) = inf_x L(vStar, x)` for the unit-simplex separable
reformulation. -/
noncomputable def unitSimplexSeparableDualFunction
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (vStar : ℝ) : EReal :=
  sInf (Set.range fun x : Fin n → ℝ => unitSimplexSeparableLagrangian q vStar x)

/-- A scalar maximizes the dual function of the one-constraint unit-simplex separable
reformulation. -/
def IsUnitSimplexSeparableDualMaximizer
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (lambda1 : ℝ) : Prop :=
  unitSimplexSeparableDualFunction q lambda1 =
    sSup (Set.range fun vStar : ℝ => unitSimplexSeparableDualFunction q vStar)

/-- The explicit scalar objective `-g(vStar)` whose minimizers are exactly the maximizers of the
dual function. -/
noncomputable def unitSimplexSeparableDualPenalty
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (vStar : ℝ) : EReal :=
  ((vStar : ℝ) : EReal) +
    ∑ k : Fin n,
      fenchelConjugate 1 (unitSimplexCoordinateObjective q k) (fun _ : Fin 1 => -vStar)

/-- A scalar minimizes the explicit dual penalty when it is no larger than every competing
penalty value. -/
def IsUnitSimplexSeparableDualPenaltyMinimizer
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (vStar : ℝ) : Prop :=
  ∀ w : ℝ, unitSimplexSeparableDualPenalty q vStar ≤ unitSimplexSeparableDualPenalty q w

/-- Helper for Corollary 6.28.8: once `0 < n`, the simplex affine family contributes exactly one
`-vStar` shift and otherwise just the coordinate terms `vStar * x k`. -/
-- TODO: isolate the last index in `Fin n` and convert the affine-constraint sum into
-- `-vStar + ∑ k, vStar * x k` by an explicit `Fin.sum_univ_succ`/range-sum calculation.
lemma helperForCorollary_6_28_8_affineConstraintSum_eq_neg_vStar_add_coordinateSum
    {n : ℕ} (hn : 0 < n) (vStar : ℝ) (x : Fin n → ℝ) :
    ∑ k : Fin n, (((vStar * unitSimplexCoordinateAffineConstraint k
        (fun _ : Fin 1 => x k) : ℝ) : EReal)) =
      ((-vStar : ℝ) : EReal) + ∑ k : Fin n, ((vStar * x k : ℝ) : EReal) := by
  -- Rewrite `n` as `m + 1` so `Fin.sum_univ_succ` isolates the unique final coordinate.
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
  -- Induct on the tail length. Each step peels off the `0`-coordinate and leaves the same
  -- statement for the successor tail `fun i => x i.succ`.
  induction m with
  | zero =>
      have hreal : vStar * (x 0 - 1) = -vStar + vStar * x 0 := by
        ring
      calc
        ∑ k : Fin 1, (((vStar * unitSimplexCoordinateAffineConstraint k
            (fun _ : Fin 1 => x k) : ℝ) : EReal))
            = (((vStar * (x 0 - 1) : ℝ)) : EReal) := by
                simp [unitSimplexCoordinateAffineConstraint]
        _ = (((-vStar + vStar * x 0 : ℝ)) : EReal) := by
                rw [hreal]
        _ = ((-vStar : ℝ) : EReal) + ((vStar * x 0 : ℝ) : EReal) := by
                simp [EReal.coe_add]
        _ = ((-vStar : ℝ) : EReal) + ∑ k : Fin 1, ((vStar * x k : ℝ) : EReal) := by
                simp
  | succ m ih =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have hfirst :
          (((vStar * unitSimplexCoordinateAffineConstraint (0 : Fin (m + 2))
            (fun _ : Fin 1 => x 0) : ℝ) : EReal)) =
            ((vStar * x 0 : ℝ) : EReal) := by
        simp [unitSimplexCoordinateAffineConstraint]
      have htail :
          ∑ k : Fin (m + 1),
            (((vStar * unitSimplexCoordinateAffineConstraint k.succ
              (fun _ : Fin 1 => x k.succ) : ℝ) : EReal)) =
            ((-vStar : ℝ) : EReal) +
              ∑ k : Fin (m + 1), ((vStar * x k.succ : ℝ) : EReal) := by
        simpa [unitSimplexCoordinateAffineConstraint] using
          ih (hn := Nat.succ_pos _) (x := fun k : Fin (m + 1) => x k.succ)
      have htailExpand :
          (((vStar * unitSimplexCoordinateAffineConstraint (Fin.succ (0 : Fin (m + 1)))
              (fun _ : Fin 1 => x (Fin.succ (0 : Fin (m + 1)))) : ℝ) : EReal)) +
            ∑ i : Fin m,
              (((vStar * unitSimplexCoordinateAffineConstraint i.succ.succ
                (fun _ : Fin 1 => x i.succ.succ) : ℝ) : EReal)) =
            ∑ k : Fin (m + 1),
              (((vStar * unitSimplexCoordinateAffineConstraint k.succ
                (fun _ : Fin 1 => x k.succ) : ℝ) : EReal)) := by
        simpa using
          (Fin.sum_univ_succ (f := fun k : Fin (m + 1) =>
            (((vStar * unitSimplexCoordinateAffineConstraint k.succ
              (fun _ : Fin 1 => x k.succ) : ℝ) : EReal)))).symm
      have hsumx :
          ((vStar * x (Fin.succ (0 : Fin (m + 1))) : ℝ) : EReal) +
            ∑ i : Fin m, ((vStar * x i.succ.succ : ℝ) : EReal) =
              ∑ k : Fin (m + 1), ((vStar * x k.succ : ℝ) : EReal) := by
        simpa using
          (Fin.sum_univ_succ (f := fun k : Fin (m + 1) =>
            ((vStar * x k.succ : ℝ) : EReal))).symm
      rw [hfirst, htailExpand, htail]
      calc
        ((vStar * x 0 : ℝ) : EReal) +
            (((-vStar : ℝ) : EReal) +
              ∑ k : Fin (m + 1), ((vStar * x k.succ : ℝ) : EReal))
            = ((-vStar : ℝ) : EReal) +
                (((vStar * x 0 : ℝ) : EReal) +
                  ∑ k : Fin (m + 1), ((vStar * x k.succ : ℝ) : EReal)) := by
                abel
        _ = ((-vStar : ℝ) : EReal) +
              (((vStar * x 0 : ℝ) : EReal) +
                (((vStar * x (Fin.succ (0 : Fin (m + 1))) : ℝ) : EReal) +
                  ∑ i : Fin m, ((vStar * x i.succ.succ : ℝ) : EReal))) := by
              congr 1
              congr 1
              exact hsumx.symm
        _ = ((-vStar : ℝ) : EReal) +
              ∑ k : Fin (m + 2), ((vStar * x k : ℝ) : EReal) := by
              rw [Fin.sum_univ_succ, Fin.sum_univ_succ]

/-- Helper for Corollary 6.28.8: every unit-simplex coordinate objective is finite from below,
so it never takes the value `-∞`. -/
lemma helperForCorollary_6_28_8_coordinateObjective_ne_bot
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (k : Fin n) (ξ : Fin 1 → ℝ) :
    unitSimplexCoordinateObjective q k ξ ≠ (⊥ : EReal) := by
  by_cases hξ : 0 ≤ ξ 0
  · -- On the nonnegative branch we inherit the `≠ ⊥` property from properness of `q k`.
    simp [unitSimplexCoordinateObjective, hξ]
    have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (q.1 k) := (q.2 k).1
    rcases
        (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
          (Set.univ : Set (Fin 1 → ℝ)) (q.1 k)).1 hproper with
      ⟨_hconv, _hne, hfinite⟩
    by_cases hdom : ξ ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (q.1 k)
    · exact (hfinite ξ hdom).1
    · exact not_mem_effectiveDomain_imp_ne_bot
        (S := Set.univ) (f := q.1 k) (by trivial) hdom
  · -- On the negative branch the coordinate objective is `⊤`.
    simp [unitSimplexCoordinateObjective, hξ]

/-- Helper for Corollary 6.28.8: on the program constraint set, each coordinate objective is a
finite `EReal`, so coercing its `toReal` recovers the original value. -/
lemma helperForCorollary_6_28_8_coordinateObjective_coe_toReal_of_mem_constraintSet
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (x : Fin n → ℝ)
    (hx : x ∈ (unitSimplexSeparableOrdinaryConvexProgram q).constraintSet)
    (k : Fin n) :
    ((((unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k)).toReal : ℝ)) : EReal) =
      unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) := by
  have htop : unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) ≠ (⊤ : EReal) := hx k
  have hbot :
      unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) ≠ (⊥ : EReal) :=
    helperForCorollary_6_28_8_coordinateObjective_ne_bot q k (fun _ : Fin 1 => x k)
  simpa using (EReal.coe_toReal htop hbot)

/-- Helper for Corollary 6.28.8: coercion from `ℝ` to `EReal` commutes with finite sums. -/
lemma helperForCorollary_6_28_8_coe_finset_sum {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) :
    (((Finset.sum s f : ℝ)) : EReal) = Finset.sum s (fun i => ((f i : ℝ) : EReal)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, ih, EReal.coe_add]

/-- Helper for Corollary 6.28.8: on the feasible branch of the reformulated ordinary program, the
real-valued objective coincides with the extended-real sum of the coordinate objectives. -/
lemma helperForCorollary_6_28_8_objective_eq_coordinateSum_of_mem_constraintSet
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (x : Fin n → ℝ)
    (hx : x ∈ (unitSimplexSeparableOrdinaryConvexProgram q).constraintSet) :
    ((((unitSimplexSeparableOrdinaryConvexProgram q).objective x : ℝ)) : EReal) =
      ∑ k : Fin n, unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) := by
  -- Push the coercion through the finite real sum, then rewrite each coordinate term separately.
  change (((∑ k : Fin n, (unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k)).toReal : ℝ)) :
      EReal) =
    ∑ k : Fin n, unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k)
  classical
  let s : Finset (Fin n) := Finset.univ
  have hsum :
      (((Finset.sum s
          (fun k : Fin n => (unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k)).toReal) :
            ℝ)) : EReal) =
        Finset.sum s (fun k : Fin n => unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k)) := by
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha ih =>
        simp [ha, ih, EReal.coe_add,
          helperForCorollary_6_28_8_coordinateObjective_coe_toReal_of_mem_constraintSet q x hx a]
  simpa [s] using hsum

/-- Helper for Corollary 6.28.8: the scalar Lagrangian written directly from the separable data
agrees pointwise with the ordinary-convex-program Lagrangian of the reformulated program. -/
-- TODO: split on primal feasibility, use `helperForTheorem_6_28_4_lagrangian_simp`, and then
-- rewrite the feasible branch by the previous affine-sum lemma.
lemma helperForCorollary_6_28_8_programLagrangian_eq_unitSimplexSeparableLagrangian
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (hn : 0 < n) :
    ∀ (vStar : ℝ) (x : Fin n → ℝ),
      (unitSimplexSeparableOrdinaryConvexProgram q).lagrangian (fun _ : Fin 1 => vStar) x =
        unitSimplexSeparableLagrangian q vStar x := by
  intro vStar x
  let P := unitSimplexSeparableOrdinaryConvexProgram q
  by_cases hx : x ∈ (unitSimplexSeparableOrdinaryConvexProgram q).constraintSet
  · -- In the feasible branch the multiplier cone is automatic, since there are no inequalities.
    have hu :
        (fun _ : Fin 1 => vStar) ∈
          (unitSimplexSeparableOrdinaryConvexProgram q).lagrangeMultiplierSet := by
      intro i
      exact Fin.elim0 i
    rw [(helperForTheorem_6_28_4_lagrangian_simp (unitSimplexSeparableOrdinaryConvexProgram q)
      (fun _ : Fin 1 => vStar) x).2.2 hx hu]
    have hObjective :
        (((P.objective x : ℝ)) : EReal) =
          ∑ k : Fin n, unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) :=
      helperForCorollary_6_28_8_objective_eq_coordinateSum_of_mem_constraintSet q x hx
    have hAffine :
        (((vStar * (∑ k : Fin n, x k - 1) : ℝ) : EReal)) =
          ∑ k : Fin n, (((vStar * unitSimplexCoordinateAffineConstraint k
            (fun _ : Fin 1 => x k) : ℝ) : EReal)) := by
      have hreal :
          vStar * (∑ k : Fin n, x k - 1) = -vStar + ∑ k : Fin n, vStar * x k := by
        rw [sub_eq_add_neg, mul_add, Finset.mul_sum]
        ring_nf
      calc
        (((vStar * (∑ k : Fin n, x k - 1) : ℝ) : EReal))
            = ((-vStar : ℝ) : EReal) + ∑ k : Fin n, ((vStar * x k : ℝ) : EReal) := by
                rw [hreal]
                rw [EReal.coe_add]
                congr 1
                simpa using
                  helperForCorollary_6_28_8_coe_finset_sum (s := Finset.univ)
                    (f := fun k : Fin n => vStar * x k)
        _ = ∑ k : Fin n, (((vStar * unitSimplexCoordinateAffineConstraint k
              (fun _ : Fin 1 => x k) : ℝ) : EReal)) := by
              symm
              exact helperForCorollary_6_28_8_affineConstraintSum_eq_neg_vStar_add_coordinateSum
                hn vStar x
    -- Expand the Kuhn--Tucker objective into objective plus the single equality term.
    calc
      ((P.kuhnTuckerObjective (fun _ : Fin 1 => vStar) x : ℝ) : EReal)
          = (((P.objective x : ℝ)) : EReal) + (((vStar * (∑ k : Fin n, x k - 1) : ℝ) : EReal)) := by
              simp [P, unitSimplexSeparableOrdinaryConvexProgram,
                BookOrdinaryConvexProgram.kuhnTuckerObjective,
                BookOrdinaryConvexProgram.inequalityMultipliers,
                BookOrdinaryConvexProgram.equalityMultipliers]
      _ = (∑ k : Fin n, unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k)) +
            ∑ k : Fin n,
              (((vStar * unitSimplexCoordinateAffineConstraint k
                (fun _ : Fin 1 => x k) : ℝ) : EReal)) := by
              rw [hObjective, hAffine]
      _ = unitSimplexSeparableLagrangian q vStar x := by
              unfold unitSimplexSeparableLagrangian unitSimplexOrdinaryConvexReformulationData
              rw [← Finset.sum_add_distrib]
  · -- Outside the feasible branch both Lagrangians are `⊤`.
    rw [(helperForTheorem_6_28_4_lagrangian_simp (unitSimplexSeparableOrdinaryConvexProgram q)
      (fun _ : Fin 1 => vStar) x).1 hx]
    unfold unitSimplexSeparableLagrangian
    unfold unitSimplexOrdinaryConvexReformulationData
    have hxTop :
        ∃ k0 : Fin n, unitSimplexCoordinateObjective q k0 (fun _ : Fin 1 => x k0) = (⊤ : EReal) := by
      simpa [unitSimplexSeparableOrdinaryConvexProgram] using hx
    rcases hxTop with ⟨k0, hk0⟩
    have hTermTop :
        unitSimplexCoordinateObjective q k0 (fun _ : Fin 1 => x k0) +
          (((vStar * unitSimplexCoordinateAffineConstraint k0
            (fun _ : Fin 1 => x k0) : ℝ) : EReal)) = (⊤ : EReal) := by
      have hCoeffNeBot :
          (((vStar * unitSimplexCoordinateAffineConstraint k0
            (fun _ : Fin 1 => x k0) : ℝ) : EReal)) ≠ (⊥ : EReal) := by
        simpa using
          (EReal.coe_ne_bot
            (vStar * unitSimplexCoordinateAffineConstraint k0 (fun _ : Fin 1 => x k0)))
      calc
        unitSimplexCoordinateObjective q k0 (fun _ : Fin 1 => x k0) +
            (((vStar * unitSimplexCoordinateAffineConstraint k0
              (fun _ : Fin 1 => x k0) : ℝ) : EReal))
            = (⊤ : EReal) +
                (((vStar * unitSimplexCoordinateAffineConstraint k0
                  (fun _ : Fin 1 => x k0) : ℝ) : EReal)) := by
                  rw [hk0]
        _ = (⊤ : EReal) := by
              simpa using EReal.top_add_of_ne_bot hCoeffNeBot
    have hTermNeBot :
        ∀ j ∈ (Finset.univ : Finset (Fin n)),
          unitSimplexCoordinateObjective q j (fun _ : Fin 1 => x j) +
            (((vStar * unitSimplexCoordinateAffineConstraint j
              (fun _ : Fin 1 => x j) : ℝ) : EReal)) ≠ (⊥ : EReal) := by
      intro j hj
      have hCoordNeBot :
          unitSimplexCoordinateObjective q j (fun _ : Fin 1 => x j) ≠ (⊥ : EReal) :=
        helperForCorollary_6_28_8_coordinateObjective_ne_bot q j (fun _ : Fin 1 => x j)
      have hCoeffNeBot :
          (((vStar * unitSimplexCoordinateAffineConstraint j
            (fun _ : Fin 1 => x j) : ℝ) : EReal)) ≠ (⊥ : EReal) := by
        simpa using
          (EReal.coe_ne_bot
            (vStar * unitSimplexCoordinateAffineConstraint j (fun _ : Fin 1 => x j)))
      intro hsumBot
      rcases (EReal.add_eq_bot_iff).1 hsumBot with hLeft | hRight
      · exact hCoordNeBot hLeft
      · exact hCoeffNeBot hRight
    symm
    exact sum_eq_top_of_term_top (s := Finset.univ)
      (f := fun j : Fin n =>
        unitSimplexCoordinateObjective q j (fun _ : Fin 1 => x j) +
          (((vStar * unitSimplexCoordinateAffineConstraint j
            (fun _ : Fin 1 => x j) : ℝ) : EReal)))
      (i := k0) (by simp) hTermTop hTermNeBot

/-- Helper for Corollary 6.28.8: any `Fin 1 → ℝ`-indexed family has the same range after
scalarizing through the unique coordinate. -/
lemma helperForCorollary_6_28_8_range_fin1_eq_range_scalar {α : Type*}
    (Φ : (Fin 1 → ℝ) → α) :
    Set.range Φ = Set.range (fun t : ℝ => Φ (fun _ : Fin 1 => t)) := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    -- Collapse the vector witness to its only scalar coordinate.
    refine ⟨u 0, ?_⟩
    simpa [scalarPoint] using congrArg Φ (helperForTheorem_6_27_3_eq_scalarPoint u)
  · rintro ⟨t, rfl⟩
    -- Any scalar already defines the corresponding `Fin 1 → ℝ` witness.
    exact ⟨fun _ : Fin 1 => t, rfl⟩

/-- Helper for Corollary 6.28.8: each one-dimensional tilted coordinate infimum is the negative
Fenchel conjugate evaluated at `-vStar`. -/
-- TODO: identify the scalar variable `ξ : ℝ` with `Fin 1 → ℝ` and rewrite the resulting
-- one-dimensional supremum exactly as the Fenchel conjugate at `-vStar`.
lemma helperForCorollary_6_28_8_coordinateInf_eq_neg_fenchelConjugate
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (k : Fin n) (vStar : ℝ) :
    sInf (Set.range fun ξ : ℝ =>
      unitSimplexCoordinateObjective q k (fun _ : Fin 1 => ξ) + ((vStar * ξ : ℝ) : EReal)) =
      - fenchelConjugate 1 (unitSimplexCoordinateObjective q k) (fun _ : Fin 1 => -vStar) := by
  let p : Fin 1 → ℝ := fun _ => vStar
  let Φ : (Fin 1 → ℝ) → EReal :=
    fun u => unitSimplexCoordinateObjective q k u + (((u ⬝ᵥ p : ℝ) : EReal))
  have hRange :
      Set.range (fun ξ : ℝ =>
        unitSimplexCoordinateObjective q k (fun _ : Fin 1 => ξ) + ((vStar * ξ : ℝ) : EReal)) =
        Set.range Φ := by
    calc
      Set.range (fun ξ : ℝ =>
          unitSimplexCoordinateObjective q k (fun _ : Fin 1 => ξ) + ((vStar * ξ : ℝ) : EReal))
          = Set.range (fun t : ℝ => Φ (fun _ : Fin 1 => t)) := by
            ext z
            constructor
            · rintro ⟨ξ, rfl⟩
              refine ⟨ξ, ?_⟩
              simp [Φ, p, dotProduct, mul_comm]
            · rintro ⟨ξ, rfl⟩
              refine ⟨ξ, ?_⟩
              simp [Φ, p, dotProduct, mul_comm]
      _ = Set.range Φ :=
        (helperForCorollary_6_28_8_range_fin1_eq_range_scalar Φ).symm
  rw [hRange, sInf_range]
  have hNegInf :
      iInf Φ = - (iSup fun u : Fin 1 → ℝ => - Φ u) := by
    -- Negation turns the `iInf` into the corresponding `iSup`.
    have h := ereal_iSup_neg_eq_neg_iInf (g := Φ)
    have h' := congrArg Neg.neg h
    simpa [Φ] using h'.symm
  rw [hNegInf]
  congr 1
  rw [fenchelConjugate_eq_iSup]
  apply iSup_congr
  intro u
  -- Rewrite the negated tilted integrand into the standard Fenchel-conjugate affine form.
  have hNegAdd :
      -(unitSimplexCoordinateObjective q k u + (((u ⬝ᵥ p : ℝ) : EReal))) =
        -(unitSimplexCoordinateObjective q k u) - (((u ⬝ᵥ p : ℝ) : EReal)) := by
    exact EReal.neg_add (x := unitSimplexCoordinateObjective q k u)
      (y := (((u ⬝ᵥ p : ℝ) : EReal))) (Or.inr (by simp)) (Or.inr (by simp))
  calc
    -(unitSimplexCoordinateObjective q k u + (((u ⬝ᵥ p : ℝ) : EReal)))
        = -(unitSimplexCoordinateObjective q k u) - (((u ⬝ᵥ p : ℝ) : EReal)) := hNegAdd
    _ = -(unitSimplexCoordinateObjective q k u) + -(((u ⬝ᵥ p : ℝ) : EReal)) := by
          simp [sub_eq_add_neg]
    _ = -(((u ⬝ᵥ p : ℝ) : EReal)) + -(unitSimplexCoordinateObjective q k u) := by
          rw [add_comm]
    _ = (((u ⬝ᵥ (fun _ : Fin 1 => -vStar) : ℝ) : EReal)) +
          -(unitSimplexCoordinateObjective q k u) := by
          simp [p, dotProduct]
    _ = (((u ⬝ᵥ (fun _ : Fin 1 => -vStar) : ℝ) : EReal)) -
          unitSimplexCoordinateObjective q k u := by
          simp [sub_eq_add_neg]

-- TODO: separate the primal infimum over `x : Fin n → ℝ` into the finite sum of the coordinate
-- infima above. The remaining blocker is the independent-coordinate `sInf` decomposition in
-- `EReal` for a finite product domain, likely by induction on `n`.
/-- Helper for Corollary 6.28.8: a function on `Fin (m + 1) → ℝ` can be reindexed by its
`Fin.init` part together with its last coordinate. -/
lemma helperForCorollary_6_28_8_iInf_snoc
    {m : ℕ} (F : (Fin (m + 1) → ℝ) → EReal) :
    (⨅ x : Fin (m + 1) → ℝ, F x) =
      ⨅ y : Fin m → ℝ, ⨅ ξ : ℝ, F (@Fin.snoc _ (fun _ => ℝ) y ξ) := by
  refine le_antisymm ?_ ?_
  · -- Every pair `(y, ξ)` produces a valid point of `Fin (m + 1) → ℝ`.
    refine le_iInf ?_
    intro y
    refine le_iInf ?_
    intro ξ
    exact iInf_le F (@Fin.snoc _ (fun _ => ℝ) y ξ)
  · -- Conversely, every tuple splits as its initial segment plus its last coordinate.
    refine le_iInf ?_
    intro x
    rw [← Fin.snoc_init_self x]
    exact le_trans
      (iInf_le (fun y : Fin m → ℝ => ⨅ ξ : ℝ, F (@Fin.snoc _ (fun _ => ℝ) y ξ)) (Fin.init x))
      (iInf_le (fun ξ : ℝ => F (@Fin.snoc _ (fun _ => ℝ) (Fin.init x) ξ)) (x (Fin.last _)))

/-- Helper for Corollary 6.28.8: evaluating each tilted coordinate integrand at `ξ = 0` gives a
finite witness strictly below `⊤`. -/
lemma helperForCorollary_6_28_8_tiltedCoordinate_zero_lt_top
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (k : Fin n) (vStar : ℝ) :
    unitSimplexCoordinateObjective q k (fun _ : Fin 1 => 0) + ((vStar * 0 : ℝ) : EReal) < ⊤ := by
  have hmemDom :
      (fun _ : Fin 1 => (0 : ℝ)) ∈
        effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (q.1 k) := by
    -- The standing domain assumption places the scalar `0` inside `dom qₖ`.
    have hIcc :
        (fun _ : Fin 1 => (0 : ℝ)) ∈
          Set.Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) := by
      constructor
      · intro i
        simp
      · intro i
        simp
    exact (q.2 k).2 hIcc
  have hneTop : q.1 k (fun _ : Fin 1 => (0 : ℝ)) ≠ ⊤ := by
    exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := q.1 k) hmemDom
  have hObjNeTop :
      unitSimplexCoordinateObjective q k (fun _ : Fin 1 => 0) ≠ ⊤ := by
    -- On the nonnegative branch, `unitSimplexCoordinateObjective` is just `q k`.
    simp [unitSimplexCoordinateObjective, hneTop]
  -- The extra linear term vanishes at `ξ = 0`, so the whole value is still finite.
  simpa [unitSimplexCoordinateObjective, hneTop] using lt_of_le_of_ne le_top hObjNeTop

end Section28
end Chap06
