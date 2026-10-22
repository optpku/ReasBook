/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

section Chapter13Lemma1344

-- Source/core/bridge triage:
-- * source-facing: the split-decay summability criterion of Lemma 13.4.4;
-- * core/canonical: `Summable` on `ℕ` and on the subtype `I`;
-- * primitive data: positivity of `M` and `τ`, the decay laws on the shifted exceptional
--   indices `k + 1 ∈ I` and their complement, the lower bound `τ / M k ≤ Δ k`,
--   monotonicity of `M`, and summability of the exceptional reciprocal subseries;
-- * derived API: summability of the full reciprocal series.
--
-- Domain sampling:
-- * `Summable` in `Mathlib.Topology.Algebra.InfiniteSum.Basic`;
-- * `summable_subtype_iff_indicator` there, for the canonical subtype view of the shifted
--   exceptional subseries;
-- * `summable_nat_add_iff` in `Mathlib.Topology.Algebra.InfiniteSum.NatInt`, showing the
--   chapter's shifted sequence presentations are bridge views rather than new owner data.

/-- Helper for Chapter13 Lemma 13.4.4: `exceptionalCount I k` counts the source indices
`1, ..., k` whose shifted representatives lie in `I`. -/
def exceptionalCount (I : Set ℕ) [DecidablePred (· ∈ I)] (k : ℕ) : ℕ :=
  Nat.count (fun j : ℕ ↦ j + 1 ∈ I) k

/-- Helper for Chapter13 Lemma 13.4.4: a uniform contraction `Δ (k + 1) ≤ β Δ k` yields the
expected geometric bound on the whole sequence. -/
lemma geometric_decay_of_uniform_step_bound
    (Δ : ℕ → ℝ) (β : ℝ)
    (hβ_nonneg : 0 ≤ β)
    (hstep : ∀ k : ℕ, Δ (k + 1) ≤ β * Δ k) :
    ∀ k : ℕ, Δ k ≤ β ^ k * Δ 0 := by
  intro k
  induction k with
  | zero =>
      -- The initial index is the geometric anchor.
      simp
  | succ k ih =>
      -- One more contraction step propagates the inductive geometric estimate.
      calc
        Δ (k + 1) ≤ β * Δ k := hstep k
        _ ≤ β * (β ^ k * Δ 0) := by
          gcongr
        _ = β ^ (k + 1) * Δ 0 := by
          simp [pow_succ, mul_assoc, mul_comm]

/-- Helper for Chapter13 Lemma 13.4.4: once `Δ k` is controlled by a geometric majorant, the
lower estimate `τ / M k ≤ Δ k` turns the reciprocal series into a geometric comparison. -/
lemma summable_reciprocals_of_geometric_decay
    (Δ M : ℕ → ℝ)
    (τ β : ℝ)
    (hM_pos : ∀ k : ℕ, 0 < M k)
    (hτ : 0 < τ)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hτ_le : ∀ k : ℕ, τ / M k ≤ Δ k)
    (hΔ_bound : ∀ k : ℕ, Δ k ≤ β ^ k * Δ 0) :
    Summable (fun k : ℕ ↦ 1 / M k) := by
  have hΔ0_nonneg : 0 ≤ Δ 0 := by
    exact (lt_of_lt_of_le (div_pos hτ (hM_pos 0)) (hτ_le 0)).le
  have hmajorant : ∀ k : ℕ, 1 / M k ≤ (Δ 0 / τ) * β ^ k := by
    intro k
    -- First divide the lower estimate by the positive constant `τ`.
    have hdiv :
        1 / M k ≤ Δ k / τ := by
      simpa [div_eq_mul_inv, hτ.ne', mul_assoc, mul_left_comm, mul_comm] using
        (div_le_div_of_nonneg_right (hτ_le k) hτ.le)
    -- Then insert the geometric control of `Δ`.
    have hgeom :
        Δ k / τ ≤ (Δ 0 / τ) * β ^ k := by
      have hscaled := mul_le_mul_of_nonneg_left (hΔ_bound k) (inv_nonneg.mpr hτ.le)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact hdiv.trans hgeom
  -- Comparison with the geometric series closes the summability argument.
  refine Summable.of_nonneg_of_le
    (fun k ↦ one_div_nonneg.mpr (hM_pos k).le)
    hmajorant
    ?_
  have hgeomSummable : Summable (fun k : ℕ ↦ β ^ k) :=
    summable_geometric_of_lt_one hβ.1.le hβ.2
  have hscale_nonneg : 0 ≤ Δ 0 / τ := by
    exact div_nonneg hΔ0_nonneg hτ.le
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    hgeomSummable.mul_left (Δ 0 / τ)

/-- Helper for Chapter13 Lemma 13.4.4: the split contraction rules accumulate into a bound in
terms of the number of exceptional indices encountered so far. -/
lemma split_decay_bound_by_exceptional_count
    (Δ : ℕ → ℝ)
    (β₁ β₄ : ℝ)
    (I : Set ℕ)
    [DecidablePred (· ∈ I)]
    (hβ₁_nonneg : 0 ≤ β₁)
    (hβ₄_nonneg : 0 ≤ β₄)
    (hΔ_on : ∀ k : ℕ, k + 1 ∈ I → Δ (k + 1) ≤ β₁ * Δ k)
    (hΔ_off : ∀ k : ℕ, k + 1 ∉ I → Δ (k + 1) ≤ β₄ * Δ k) :
    ∀ k : ℕ,
      Δ k ≤ β₁ ^ exceptionalCount I k * β₄ ^ (k - exceptionalCount I k) * Δ 0 := by
  intro k
  induction k with
  | zero =>
      -- At the initial index no exceptional step has yet occurred.
      simp [exceptionalCount]
  | succ k ih =>
      have hcount_le : exceptionalCount I k ≤ k := by
        simpa [exceptionalCount] using
          (show Nat.count (fun j : ℕ ↦ j + 1 ∈ I) k ≤ k from
            Nat.count_le (p := fun j : ℕ ↦ j + 1 ∈ I))
      by_cases hk : k + 1 ∈ I
      · have hcount :
            exceptionalCount I (k + 1) = exceptionalCount I k + 1 := by
          unfold exceptionalCount
          exact Nat.count_succ_eq_succ_count hk
        -- An exceptional step adds one factor of `β₁`.
        calc
          Δ (k + 1) ≤ β₁ * Δ k := hΔ_on k hk
          _ ≤ β₁ *
              (β₁ ^ exceptionalCount I k * β₄ ^ (k - exceptionalCount I k) * Δ 0) := by
            gcongr
          _ = β₁ ^ exceptionalCount I (k + 1) *
              β₄ ^ ((k + 1) - exceptionalCount I (k + 1)) * Δ 0 := by
            rw [hcount]
            rw [Nat.succ_sub_succ_eq_sub, pow_succ]
            ac_rfl
      · have hcount :
            exceptionalCount I (k + 1) = exceptionalCount I k := by
          unfold exceptionalCount
          exact Nat.count_succ_eq_count hk
        -- A non-exceptional step contributes one factor of `β₄`.
        calc
          Δ (k + 1) ≤ β₄ * Δ k := hΔ_off k hk
          _ ≤ β₄ *
              (β₁ ^ exceptionalCount I k * β₄ ^ (k - exceptionalCount I k) * Δ 0) := by
            gcongr
          _ = β₁ ^ exceptionalCount I (k + 1) *
              β₄ ^ ((k + 1) - exceptionalCount I (k + 1)) * Δ 0 := by
            rw [hcount]
            rw [Nat.succ_sub hcount_le, pow_succ]
            ac_rfl

/-- Helper for Chapter13 Lemma 13.4.4: the blockwise majorant `q ^ (k / p)` is summable because
each nonnegative summable value is repeated across only finitely many residue classes modulo `p`. -/
lemma summable_block_repeat_of_summable
    (f : ℕ → ℝ)
    (h_nonneg : ∀ n : ℕ, 0 ≤ f n)
    (p : ℕ)
    (hp : 0 < p)
    (hf : Summable f) :
    Summable (fun k : ℕ ↦ f (k / p)) := by
  let g : ℕ × Fin p → ℝ := fun x ↦ f x.1
  have hprod : Summable g := by
    have hfiber : ∀ n : ℕ, Summable (fun r : Fin p ↦ g (n, r)) := by
      intro n
      -- Each block fiber is a finite constant sum.
      exact (hasSum_fintype (fun r : Fin p ↦ g (n, r))).summable
    have houter : Summable (fun n : ℕ ↦ ∑' r : Fin p, g (n, r)) := by
      -- The outer series is just the finite scalar multiple `p • f n`.
      simpa [g, tsum_fintype, Finset.sum_const, Fintype.card_fin, nsmul_eq_mul, mul_comm] using
        (hf.mul_left (p : ℝ))
    -- Summability on the product follows from the fiberwise criterion for nonnegative series.
    exact (summable_prod_of_nonneg (f := g) (fun x ↦ h_nonneg x.1)).2 ⟨hfiber, houter⟩
  have hp_ne : p ≠ 0 := Nat.ne_of_gt hp
  letI : NeZero p := ⟨hp_ne⟩
  let e : ℕ ≃ ℕ × Fin p := Nat.divModEquiv p
  have hcomp : Summable (fun k : ℕ ↦ g (e k)) := e.summable_iff.mpr hprod
  -- Reindexing by `Nat.divModEquiv` turns the product-series back into `f (k / p)`.
  simpa [g, e, Nat.divModEquiv] using hcomp

/-- Helper for Chapter13 Lemma 13.4.4: the blockwise geometric majorant `q ^ (k / p)` is
summable because each value `q ^ n` appears in only `p` consecutive slots. -/
lemma summable_pow_div_of_lt_one
    (p : ℕ)
    (hp : 0 < p)
    {q : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hq_lt_one : q < 1) :
    Summable (fun k : ℕ ↦ q ^ (k / p)) := by
  -- The generic block-repeat lemma turns the repeated-block sequence into a finite repetition of
  -- the ordinary geometric series.
  apply summable_block_repeat_of_summable (f := fun n : ℕ ↦ q ^ n)
  · intro n
    exact pow_nonneg hq_nonneg n
  · exact hp
  · exact summable_geometric_of_lt_one hq_nonneg hq_lt_one

/-- Helper for Chapter13 Lemma 13.4.4: the exceptional reciprocal subseries can be reindexed by
the source-faithful `Nat.nth` enumeration when the exceptional set is infinite. -/
lemma summable_nth_exceptional_reciprocals_of_infinite
    (M : ℕ → ℝ)
    (I : Set ℕ)
    [DecidablePred (· ∈ I)]
    (hIinf : {j : ℕ | j + 1 ∈ I}.Infinite)
    (hsummable_I : Summable (fun k : {k : ℕ // k + 1 ∈ I} ↦ 1 / M (k + 1))) :
    Summable (fun n : ℕ ↦ 1 / M (Nat.nth (fun j : ℕ ↦ j + 1 ∈ I) n + 1)) := by
  let P : ℕ → Prop := fun j ↦ j + 1 ∈ I
  let e : ℕ ≃ {j : ℕ // P j} :=
    (@Nat.Subtype.orderIsoOfNat (setOf P) hIinf.to_subtype).toEquiv
  have hsub : Summable (fun k : {k : ℕ // P k} ↦ 1 / M (k + 1)) := by
    -- This just repackages the given shifted exceptional subseries along the definitional alias `P`.
    simpa [P] using hsummable_I
  have hsum : Summable (fun n : ℕ ↦ (fun k : {k : ℕ // P k} ↦ 1 / M (k + 1)) (e n)) :=
    e.summable_iff.mpr hsub
  have hnth :
      ∀ n : ℕ, Nat.nth P n = ↑((@Nat.Subtype.orderIsoOfNat (setOf P) hIinf.to_subtype) n) := by
    intro n
    simpa [P] using (Nat.nth_apply_eq_orderIsoOfNat (p := P) hIinf n)
  -- Rewriting `Nat.nth` by the infinite order isomorphism produces the source enumeration.
  refine hsum.congr ?_
  intro n
  rw [hnth n]
  rfl

/-- Helper for Chapter13 Lemma 13.4.4: a dense-prefix index `k` is bounded by the reciprocal at
the `(k / p)`-th exceptional source index selected by `Nat.nth`. -/
lemma dense_prefix_reciprocal_le_nth_repeat
    (M : ℕ → ℝ)
    (I : Set ℕ)
    [DecidablePred (· ∈ I)]
    (hM_pos : ∀ k : ℕ, 0 < M k)
    (hM_mono : ∀ k : ℕ, M k ≤ M (k + 1))
    (p : ℕ)
    {k : ℕ}
    (hk : k / p < exceptionalCount I (k + 1)) :
    1 / M (k + 1) ≤ 1 / M (Nat.nth (fun j : ℕ ↦ j + 1 ∈ I) (k / p) + 1) := by
  let P : ℕ → Prop := fun j ↦ j + 1 ∈ I
  have hlt : Nat.nth P (k / p) < k + 1 := by
    -- The dense-prefix hypothesis says that the `(k / p)`-th exceptional index appears before `k + 1`.
    simpa [exceptionalCount, P] using (Nat.nth_lt_of_lt_count (p := P) hk)
  have hM_monotone : Monotone M := monotone_nat_of_le_succ hM_mono
  -- Monotonicity of `M` reverses to monotonicity of the positive reciprocals.
  exact one_div_le_one_div_of_le
    (hM_pos (Nat.nth P (k / p) + 1))
    (hM_monotone (Nat.succ_le_of_lt hlt))

/-- Helper for Chapter13 Lemma 13.4.4: if the shifted exceptional set is finite, then the dense
prefix set `J = {k | k / p < exceptionalCount I (k + 1)}` is finite as well. -/
lemma finite_dense_prefix_set_of_exceptional_finite
    (I : Set ℕ)
    [DecidablePred (· ∈ I)]
    (p : ℕ)
    (hp : 0 < p)
    (hfin : {j : ℕ | j + 1 ∈ I}.Finite) :
    {k : ℕ | k / p < exceptionalCount I (k + 1)}.Finite := by
  let C := hfin.toFinset.card
  refine (Set.finite_lt_nat (p * C)).subset ?_
  intro k hk
  have hkC : k / p < C := by
    exact lt_of_lt_of_le hk <| by
      simpa [exceptionalCount, C] using
        (Nat.count_le_card (p := fun j : ℕ ↦ j + 1 ∈ I) hfin (k + 1))
  -- Bounding `k / p` by the global exceptional count bound forces `k < p * C`.
  simpa [mul_comm] using (Nat.div_lt_iff_lt_mul hp).mp hkC

/-- Helper for Chapter13 Lemma 13.4.4: the dense-prefix contribution is summable, either by the
`Nat.nth` reindexing when the exceptional set is infinite or by finite support otherwise. -/
lemma summable_dense_prefix_indicator
    (M : ℕ → ℝ)
    (I : Set ℕ)
    [DecidablePred (· ∈ I)]
    (hM_pos : ∀ k : ℕ, 0 < M k)
    (hM_mono : ∀ k : ℕ, M k ≤ M (k + 1))
    (p : ℕ)
    (hp : 0 < p)
    (hsummable_I : Summable (fun k : {k : ℕ // k + 1 ∈ I} ↦ 1 / M (k + 1))) :
    Summable ({k : ℕ | k / p < exceptionalCount I (k + 1)}.indicator fun k ↦ 1 / M (k + 1)) := by
  let P : ℕ → Prop := fun j ↦ j + 1 ∈ I
  let J : Set ℕ := {k : ℕ | k / p < exceptionalCount I (k + 1)}
  let a : ℕ → ℝ := fun k ↦ 1 / M (k + 1)
  rcases (setOf P).finite_or_infinite with hPfin | hPinf
  · have hJfin : J.Finite := by
      simpa [J, P] using finite_dense_prefix_set_of_exceptional_finite I p hp hPfin
    letI := hJfin.fintype
    have hsub : Summable ((a ∘ Subtype.val) : J → ℝ) := by
      -- Finite support handles the source branch where only finitely many exceptional indices occur.
      exact Summable.of_finite
    simpa [J, a] using (summable_subtype_iff_indicator).1 hsub
  · have hnth :
        Summable (fun n : ℕ ↦ 1 / M (Nat.nth P n + 1)) :=
      summable_nth_exceptional_reciprocals_of_infinite M I hPinf hsummable_I
    have hrepeat :
        Summable (fun k : ℕ ↦ 1 / M (Nat.nth P (k / p) + 1)) := by
      -- The dense part repeats each `Nat.nth` exceptional reciprocal over a block of length `p`.
      refine summable_block_repeat_of_summable
        (f := fun n : ℕ ↦ 1 / M (Nat.nth P n + 1))
        (h_nonneg := fun n ↦ one_div_nonneg.mpr (hM_pos (Nat.nth P n + 1)).le)
        p hp hnth
    refine Summable.of_nonneg_of_le ?_ ?_ hrepeat
    · intro k
      by_cases hk : k ∈ J
      · simpa [J, a, hk] using one_div_nonneg.mpr (hM_pos (k + 1)).le
      · simp [J, a, hk]
    · intro k
      by_cases hk : k ∈ J
      · -- On the dense set, compare directly to the repeated `Nat.nth` exceptional reciprocal.
        simpa [J, a, hk] using
          dense_prefix_reciprocal_le_nth_repeat M I hM_pos hM_mono p hk
      · -- Outside the dense set, the indicator vanishes.
        simpa [J, a, hk] using
          (show 0 ≤ 1 / M (Nat.nth P (k / p) + 1) from
            one_div_nonneg.mpr (hM_pos (Nat.nth P (k / p) + 1)).le)

/-- Helper for Chapter13 Lemma 13.4.4: the sparse-side block count splits the exponent
`p * m - c` into `c` exceptional contributions and `m - c` full nonexceptional blocks. -/
lemma dense_prefix_block_exponent_identity
    (p m c : ℕ)
    (hp : 0 < p)
    (hc_le : c ≤ m) :
    p * m - c = (p - 1) * c + p * (m - c) := by
  rcases Nat.exists_eq_add_of_le hc_le with ⟨d, rfl⟩
  have hc_mul : c ≤ p * c := by
    simpa [one_mul] using Nat.mul_le_mul_right c hp
  -- Rewrite `m` as `c + d`, then peel the subtraction off the `p * c` block.
  rw [Nat.mul_add, Nat.add_comm (p * c), Nat.add_sub_assoc hc_mul]
  have hpc : p * c - c = (p - 1) * c := by
    calc
      p * c - c = p * c - 1 * c := by rw [one_mul]
      _ = (p - 1) * c := by rw [← Nat.mul_sub_right_distrib]
  rw [hpc]
  -- The remaining suffix block is exactly `d = (c + d) - c`.
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Helper for Chapter13 Lemma 13.4.4: after the exponent split, the mixed source factor
`β₁ ^ c * β₄ ^ (p * m - c)` factors into `q ^ c` times the repeated full-block term. -/
lemma dense_prefix_block_factorization
    (β₁ β₄ q : ℝ)
    (p m c : ℕ)
    (hq : q = β₁ * β₄ ^ (p - 1))
    (hp : 0 < p)
    (hc_le : c ≤ m) :
    β₁ ^ c * β₄ ^ (p * m - c) = q ^ c * (β₄ ^ p) ^ (m - c) := by
  -- Route correction: package the mixed Nat/Real normalization once so the sparse proof can
  -- reuse the source block factor `q` without interleaving arithmetic and power rewrites.
  rw [dense_prefix_block_exponent_identity p m c hp hc_le, pow_add, ← mul_assoc]
  rw [show β₄ ^ ((p - 1) * c) = (β₄ ^ (p - 1)) ^ c by rw [pow_mul]]
  rw [show β₄ ^ (p * (m - c)) = (β₄ ^ p) ^ (m - c) by rw [pow_mul]]
  rw [← mul_pow]
  simpa [hq]

/-- Helper for Chapter13 Lemma 13.4.4: away from the dense exceptional prefixes, the reciprocal
sequence is bounded by the blockwise geometric majorant from the source proof. -/
lemma reciprocal_bound_off_dense_prefix
    (Δ M : ℕ → ℝ)
    (τ β₁ β₄ : ℝ)
    (I : Set ℕ)
    [DecidablePred (· ∈ I)]
    (hM_pos : ∀ k : ℕ, 0 < M k)
    (hτ : 0 < τ)
    (hβ₄ : β₄ ∈ Set.Ioo (0 : ℝ) 1)
    (hβ₁_nonneg : 0 ≤ β₁)
    (hβ₄_le_β₁ : β₄ ≤ β₁)
    (hτ_le : ∀ k : ℕ, τ / M k ≤ Δ k)
    (hsplit : ∀ k : ℕ,
      Δ k ≤ β₁ ^ exceptionalCount I k * β₄ ^ (k - exceptionalCount I k) * Δ 0)
    (p : ℕ)
    (hp : 0 < p)
    {q : ℝ}
    (hq : q = β₁ * β₄ ^ (p - 1))
    {k : ℕ}
    (hk : k ∉ {k : ℕ | k / p < exceptionalCount I (k + 1)}) :
    1 / M (k + 1) ≤ (Δ 0 / τ) * q ^ (k / p) := by
  let m : ℕ := k / p
  let c : ℕ := exceptionalCount I (k + 1)
  have hc_le : c ≤ m := by
    exact not_lt.mp hk
  have hΔ0_nonneg : 0 ≤ Δ 0 := by
    exact (lt_of_lt_of_le (div_pos hτ (hM_pos 0)) (hτ_le 0)).le
  have hdiv :
      1 / M (k + 1) ≤ Δ (k + 1) / τ := by
    -- Divide the standing lower estimate by the positive constant `τ`.
    simpa [div_eq_mul_inv, hτ.ne', mul_assoc, mul_left_comm, mul_comm] using
      (div_le_div_of_nonneg_right (hτ_le (k + 1)) hτ.le)
  have hβ₄p_le_q : β₄ ^ p ≤ q := by
    -- One block of ordinary steps is dominated by one source block factor `q = β₁ * β₄^(p-1)`.
    rw [hq]
    calc
      β₄ ^ p = β₄ ^ (p - 1 + 1) := by congr; exact (Nat.sub_add_cancel hp).symm
      _ = β₄ ^ (p - 1) * β₄ := by rw [pow_add, pow_one]
      _ ≤ β₄ ^ (p - 1) * β₁ := by
        exact mul_le_mul_of_nonneg_left hβ₄_le_β₁ (pow_nonneg hβ₄.1.le _)
      _ = β₁ * β₄ ^ (p - 1) := by ring
  have hq_nonneg : 0 ≤ q := by
    rw [hq]
    exact mul_nonneg hβ₁_nonneg (pow_nonneg hβ₄.1.le _)
  have hprod :
      β₁ ^ c * β₄ ^ ((k + 1) - c) ≤ q ^ m := by
    have hpow_drop :
        β₄ ^ ((k + 1) - c) ≤ β₄ ^ (p * m - c) := by
      -- Removing the final remainder block only enlarges the power because `0 < β₄ < 1`.
      apply pow_le_pow_of_le_one hβ₄.1.le hβ₄.2.le
      exact Nat.sub_le_sub_right (Nat.le_succ_of_le (by simpa [m, mul_comm] using Nat.div_mul_le_self k p)) c
    have hpow_blocks :
        β₁ ^ c * β₄ ^ (p * m - c) =
          q ^ c * (β₄ ^ p) ^ (m - c) := by
      -- The block exponent splits into `c` exceptional factors and `m - c` full `p`-blocks.
      exact dense_prefix_block_factorization β₁ β₄ q p m c hq hp hc_le
    calc
      β₁ ^ c * β₄ ^ ((k + 1) - c) ≤ β₁ ^ c * β₄ ^ (p * m - c) := by
        gcongr
      _ = q ^ c * (β₄ ^ p) ^ (m - c) := hpow_blocks
      _ ≤ q ^ c * q ^ (m - c) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (pow_nonneg hβ₄.1.le p) hβ₄p_le_q (m - c))
          (pow_nonneg hq_nonneg _)
      _ = q ^ m := by
        rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hc_le]
  have hmajor :
      Δ (k + 1) ≤ q ^ m * Δ 0 := by
    -- The split-decay estimate now matches the blockwise geometric source majorant.
    calc
      Δ (k + 1) ≤ β₁ ^ c * β₄ ^ ((k + 1) - c) * Δ 0 := by
        simpa [c] using hsplit (k + 1)
      _ ≤ q ^ m * Δ 0 := by
        gcongr
  have hscaled :
      Δ (k + 1) / τ ≤ (Δ 0 / τ) * q ^ m := by
    -- Finally divide the geometric majorant by `τ`.
    have hscaled' := mul_le_mul_of_nonneg_left hmajor (inv_nonneg.mpr hτ.le)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled'
  exact hdiv.trans hscaled

/-- Chapter13 Lemma 13.4.4: let `Δ` and `M` be positive real sequences. Assume there are
positive constants `τ`, `β₁`, and `β₄` with `β₄ ∈ (0, 1)` and a subset `I` of indices such that
`Δ` contracts by the factor `β₁` whenever the source index `k + 1` lies in `I`, contracts by the
factor `β₄` when `k + 1 ∉ I`, `Δ k` is bounded below by `τ / M k`, `M` is nondecreasing, and
the exceptional subseries `∑_{k + 1 ∈ I} 1 / M (k + 1)` is summable. Then the full series
`∑' k, 1 / M k` is summable. The separate source assumptions `0 < β₁` and `0 < Δ k` are
redundant for this conclusion: `0 < Δ k` already follows from `hτ`, `hM_pos`, and `hτ_le`, so the
Lean API omits both while keeping the same mathematical content. This keeps the chapter's faithful
`ℕ`-encoding of the source's 1-based exceptional indices. -/
theorem summable_reciprocals_of_split_decay_and_exceptional_subseries
    (Δ M : ℕ → ℝ)
    (τ β₁ β₄ : ℝ)
    (I : Set ℕ)
    (hM_pos : ∀ k : ℕ, 0 < M k)
    (hτ : 0 < τ)
    (hβ₄ : β₄ ∈ Set.Ioo (0 : ℝ) 1)
    (hΔ_on : ∀ k : ℕ, k + 1 ∈ I → Δ (k + 1) ≤ β₁ * Δ k)
    (hΔ_off : ∀ k : ℕ, k + 1 ∉ I → Δ (k + 1) ≤ β₄ * Δ k)
    (hτ_le : ∀ k : ℕ, τ / M k ≤ Δ k)
    (hM_mono : ∀ k : ℕ, M k ≤ M (k + 1))
    (hsummable_I : Summable (fun k : {k : ℕ // k + 1 ∈ I} ↦ 1 / M (k + 1))) :
    Summable (fun k : ℕ ↦ 1 / M k) := by
  by_cases hβ₁β₄ : β₁ ≤ β₄
  · have hΔ_nonneg : ∀ k : ℕ, 0 ≤ Δ k := by
      intro k
      exact (lt_of_lt_of_le (div_pos hτ (hM_pos k)) (hτ_le k)).le
    have hstep : ∀ k : ℕ, Δ (k + 1) ≤ β₄ * Δ k := by
      intro k
      by_cases hk : k + 1 ∈ I
      · -- In the easy branch, even the exceptional steps contract by at most `β₄`.
        exact (hΔ_on k hk).trans <| mul_le_mul_of_nonneg_right hβ₁β₄ (hΔ_nonneg k)
      · exact hΔ_off k hk
    have hgeom : ∀ k : ℕ, Δ k ≤ β₄ ^ k * Δ 0 :=
      geometric_decay_of_uniform_step_bound Δ β₄ hβ₄.1.le hstep
    -- The easy branch closes by a direct geometric comparison.
    exact summable_reciprocals_of_geometric_decay Δ M τ β₄ hM_pos hτ hβ₄ hτ_le hgeom
  · have hβ₄_lt_β₁ : β₄ < β₁ := lt_of_not_ge hβ₁β₄
    have hβ₁_nonneg : 0 ≤ β₁ := hβ₄.1.le.trans hβ₄_lt_β₁.le
    classical
    have hsplit :
        ∀ k : ℕ,
          Δ k ≤ β₁ ^ exceptionalCount I k * β₄ ^ (k - exceptionalCount I k) * Δ 0 :=
      split_decay_bound_by_exceptional_count
        Δ β₁ β₄ I hβ₁_nonneg hβ₄.1.le hΔ_on hΔ_off
    have hβ₁_pos : 0 < β₁ := lt_of_lt_of_le hβ₄.1 hβ₄_lt_β₁.le
    obtain ⟨n, hn⟩ : ∃ n : ℕ, β₄ ^ n < 1 / β₁ :=
      exists_pow_lt_of_lt_one (one_div_pos.mpr hβ₁_pos) hβ₄.2
    let p : ℕ := n + 1
    let q : ℝ := β₁ * β₄ ^ (p - 1)
    have hp : 0 < p := by
      simp [p]
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      exact mul_nonneg hβ₁_nonneg (pow_nonneg hβ₄.1.le _)
    have hΔ0_nonneg : 0 ≤ Δ 0 := by
      exact (lt_of_lt_of_le (div_pos hτ (hM_pos 0)) (hτ_le 0)).le
    have hq_lt_one : q < 1 := by
      have hmul : β₁ * β₄ ^ n < β₁ * (1 / β₁) :=
        mul_lt_mul_of_pos_left hn hβ₁_pos
      have hcancel : β₁ * (1 / β₁) = 1 := by
        field_simp [hβ₁_pos.ne']
      have hq_lt : β₁ * β₄ ^ (p - 1) < β₁ * (1 / β₁) := by
        simpa [p] using hmul
      exact hq_lt.trans_eq hcancel
    let J : Set ℕ := {k : ℕ | k / p < exceptionalCount I (k + 1)}
    let a : ℕ → ℝ := fun k ↦ 1 / M (k + 1)
    have hdense :
        Summable (J.indicator a) := by
      -- Route correction: the dense part now follows the source split exactly, via `Nat.nth`
      -- on the infinite exceptional branch and finite support on the finite branch.
      simpa [J, a, p] using
        summable_dense_prefix_indicator M I hM_pos hM_mono p hp hsummable_I
    have hsparse_majorant :
        ∀ k : ℕ, Jᶜ.indicator a k ≤ (Δ 0 / τ) * q ^ (k / p) := by
      intro k
      by_cases hk : k ∈ J
      · -- On the dense set the complement indicator vanishes.
        simpa [J, a, hk] using
          (show 0 ≤ (Δ 0 / τ) * q ^ (k / p) from
            mul_nonneg (div_nonneg hΔ0_nonneg hτ.le) (pow_nonneg hq_nonneg _))
      · -- Off the dense set, use the source geometric majorant from the split-decay estimate.
        simpa [J, a, hk] using
          reciprocal_bound_off_dense_prefix
            Δ M τ β₁ β₄ I hM_pos hτ hβ₄ hβ₁_nonneg hβ₄_lt_β₁.le hτ_le
            hsplit p hp rfl hk
    have hsparse :
        Summable (Jᶜ.indicator a) := by
      refine Summable.of_nonneg_of_le ?_ hsparse_majorant ?_
      · intro k
        by_cases hk : k ∈ J
        · simp [J, a, hk]
        · simpa [J, a, hk] using one_div_nonneg.mpr (hM_pos (k + 1)).le
      · simpa [a, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          (summable_pow_div_of_lt_one p hp hq_nonneg hq_lt_one).mul_left (Δ 0 / τ)
    have hshifted : Summable a := by
      -- Recombining the dense and sparse pieces recovers the shifted reciprocal series.
      convert hdense.add hsparse using 1
      funext k
      by_cases hk : k ∈ J <;> simp [J, a, hk]
    exact (summable_nat_add_iff 1).1 <| by
      simpa [a] using hshifted

/-- The shifted exceptional subseries `∑_{k + 1 ∈ I} 1 / M (k + 1)` is canonically the
indicator-restricted series on `ℕ`. This companion bridge lets downstream results switch between
the source-facing subtype formulation and the standard ambient `ℕ`-indexed view. -/
theorem summable_exceptional_reciprocals_iff_indicator
    (M : ℕ → ℝ) (I : Set ℕ) :
    Summable (fun k : {k : ℕ // k + 1 ∈ I} ↦ 1 / M (k + 1)) ↔
      Summable (({k : ℕ | k + 1 ∈ I}).indicator fun k ↦ 1 / M (k + 1)) := by
  constructor
  · intro h
    let J : Set ℕ := {k : ℕ | k + 1 ∈ I}
    change Summable (((fun k : ℕ ↦ 1 / M (k + 1)) ∘ Subtype.val) : J → ℝ) at h
    have h'' : Summable (J.indicator fun k ↦ 1 / M (k + 1)) :=
      (summable_subtype_iff_indicator).1 h
    simpa [J] using h''
  · intro h
    let J : Set ℕ := {k : ℕ | k + 1 ∈ I}
    have h' : Summable (J.indicator fun k ↦ 1 / M (k + 1)) := by
      simpa [J] using h
    have h'' : Summable (((fun k : ℕ ↦ 1 / M (k + 1)) ∘ Subtype.val) : J → ℝ) :=
      (summable_subtype_iff_indicator).2 h'
    change Summable (((fun k : ℕ ↦ 1 / M (k + 1)) ∘ Subtype.val) : J → ℝ)
    exact h''

/-- The nondecreasing-sequence hypothesis in Lemma 13.4.4 can be supplied canonically as
`Monotone M`; on `ℕ`, this implies the stepwise bound `M k ≤ M (k + 1)` used in the source
statement. -/
theorem summable_reciprocals_of_split_decay_and_exceptional_subseries_of_monotone
    (Δ M : ℕ → ℝ)
    (τ β₁ β₄ : ℝ)
    (I : Set ℕ)
    (hM_pos : ∀ k : ℕ, 0 < M k)
    (hτ : 0 < τ)
    (hβ₄ : β₄ ∈ Set.Ioo (0 : ℝ) 1)
    (hΔ_on : ∀ k : ℕ, k + 1 ∈ I → Δ (k + 1) ≤ β₁ * Δ k)
    (hΔ_off : ∀ k : ℕ, k + 1 ∉ I → Δ (k + 1) ≤ β₄ * Δ k)
    (hτ_le : ∀ k : ℕ, τ / M k ≤ Δ k)
    (hM_mono : Monotone M)
    (hsummable_I : Summable (fun k : {k : ℕ // k + 1 ∈ I} ↦ 1 / M (k + 1))) :
    Summable (fun k : ℕ ↦ 1 / M k) := by
  exact summable_reciprocals_of_split_decay_and_exceptional_subseries
    Δ M τ β₁ β₄ I hM_pos hτ hβ₄ hΔ_on hΔ_off hτ_le
    (fun k ↦ hM_mono (Nat.le_succ k)) hsummable_I

end Chapter13Lemma1344
