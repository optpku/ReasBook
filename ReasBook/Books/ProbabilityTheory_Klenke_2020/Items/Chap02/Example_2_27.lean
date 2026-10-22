/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_26

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set

universe u

/-- Helper for Example 2.27: distinct adjacent two-point blocks of indices are disjoint. -/
private lemma adjacentTwoPointBlocksPairwiseDisjoint :
    Pairwise fun m n ↦
      Disjoint ({2 * m + 1, 2 * m + 2} : Set ℕ) ({2 * n + 1, 2 * n + 2} : Set ℕ) := by
  intro m n hmn
  -- Two different adjacent blocks cannot share either their odd or even endpoint.
  refine Set.disjoint_left.mpr ?_
  intro k hk hm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk hm
  rcases hk with hk | hk <;> rcases hm with hm | hm <;> omega

/-- Helper for Example 2.27: the even endpoint belongs to its adjacent two-point block. -/
private lemma mem_adjacentTwoPointBlock_even (n : ℕ) :
    2 * n + 2 ∈ ({2 * n + 1, 2 * n + 2} : Set ℕ) := by
  -- The block is exactly the two-element set containing the even endpoint.
  simp

/-- Helper for Example 2.27: the odd endpoint belongs to its adjacent two-point block. -/
private lemma mem_adjacentTwoPointBlock_odd (n : ℕ) :
    2 * n + 1 ∈ ({2 * n + 1, 2 * n + 2} : Set ℕ) := by
  -- The block is exactly the two-element set containing the odd endpoint.
  simp

/-- Helper for Example 2.27: the canonical ordered pair extracted from one adjacent two-point
block-valued function. -/
private def adjacentBlockToPair (n : ℕ) :
    ({j // j ∈ ({2 * n + 1, 2 * n + 2} : Set ℕ)} → ℝ) → ℝ × ℝ :=
  fun f ↦
    (f ⟨2 * n + 2, mem_adjacentTwoPointBlock_even n⟩,
      f ⟨2 * n + 1, mem_adjacentTwoPointBlock_odd n⟩)

/-- Helper for Example 2.27: reading the even and odd coordinates from a two-point block-valued
random element is measurable. -/
private lemma measurableAdjacentBlockToPair (n : ℕ) :
    Measurable (adjacentBlockToPair n) := by
  -- Each coordinate is just evaluation at one distinguished point of the two-point block.
  exact Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)

/-- Helper for Example 2.27: subtraction on pairs of real numbers is measurable. -/
private lemma measurableRealPairSub : Measurable (fun p : ℝ × ℝ ↦ p.1 - p.2) := by
  -- This is the standard measurability of subtraction composed with the coordinate projections.
  exact measurable_fst.sub measurable_snd

/-- Helper for Example 2.27: the process of adjacent coordinate pairs extracted from an
independent real-valued sequence is itself independent. -/
private theorem iIndepFun_adjacent_pairs_of_iIndepFun
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n)) (hX_indep : iIndepFun X μ) :
    iIndepFun (fun n ω ↦ (X (2 * n + 2) ω, X (2 * n + 1) ω)) μ := by
  let I : ℕ → Set ℕ := fun n ↦ ({2 * n + 1, 2 * n + 2} : Set ℕ)
  have h_disjoint : Pairwise fun m n ↦ Disjoint (I m) (I n) := by
    -- The concrete block family is exactly the disjoint adjacent two-point family.
    simpa [I] using adjacentTwoPointBlocksPairwiseDisjoint
  have h_blocks :
      iIndepFun (fun n ω (j : I n) ↦ X j ω) μ :=
    iIndepFun_block_of_pairwise_disjoint_blocks μ X I h_disjoint hX_indep hX_meas
  -- We turn each block-valued random element into the ordered pair `(X (2n + 2), X (2n + 1))`.
  simpa [I, Function.comp] using
    h_blocks.comp
      (fun n ↦ adjacentBlockToPair n)
      measurableAdjacentBlockToPair

-- Proof sketch: first use `iIndepFun_adjacent_pairs_of_iIndepFun` to obtain independence of the
-- pair process `n ↦ (X (2 * n + 2), X (2 * n + 1))`, then postcompose each pair with the
-- measurable subtraction map `(x, y) ↦ x - y` via `ProbabilityTheory.iIndepFun.comp`.
/-- Example 2.27: with Lean's `0`-based indexing, the textbook family
`(X_{2n} - X_{2n-1})_{n ∈ ℕ}` is rendered as
`(X (2 * n + 2) - X (2 * n + 1))_{n ∈ ℕ}`; this adjacent-pair difference family is independent
whenever `X` is an independent family of real random variables. -/
theorem iIndepFun_adjacent_pair_differences_of_iIndepFun
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n)) (hX_indep : iIndepFun X μ) :
    iIndepFun (fun n ω ↦ X (2 * n + 2) ω - X (2 * n + 1) ω) μ := by
  have h_pairs :
      iIndepFun (fun n ω ↦ (X (2 * n + 2) ω, X (2 * n + 1) ω)) μ :=
    iIndepFun_adjacent_pairs_of_iIndepFun hX_meas hX_indep
  -- Postcomposing each independent pair with subtraction gives the desired differences.
  simpa [Function.comp] using
    h_pairs.comp (fun _ ↦ fun p : ℝ × ℝ ↦ p.1 - p.2) (fun _ ↦ measurableRealPairSub)
