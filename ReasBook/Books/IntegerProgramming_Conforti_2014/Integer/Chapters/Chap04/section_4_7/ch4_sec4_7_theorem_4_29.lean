/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_remark_3_10
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_6.ch4_sec4_6_theorem_4_26
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_7.ch4_sec4_7_remark_4_7_extra_2

open scoped BigOperators Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: subset-incidence matrix presentations of submodular polyhedra and their
--   Chapter 4.6 total-dual-integrality bridge
-- * sampled owner declarations: Chapter 2 `matrixOfRowSupports`/`rowOfSupport`, Chapter 4.1
--   `rational_matrix_polyhedron`, and Chapter 4.6 `totally_dual_integral`
-- * owner abstraction: the canonical subset-family incidence owner is `matrixOfRowSupports`; this
--   file should only add the Section 4.7 bridge from the all-subsets family to the Chapter 4.6
--   `Fin`-indexed TDI owner
-- * source/core/bridge triage: the subset-inequality system is source-facing, the TDI predicate is
--   core/canonical, and the reindexed `matrixOfRowSupports` presentation is the bridge/view
-- * primitive data: the family of all subsets of `α` and the right-hand side `f : Finset α → ℤ`
-- * derived API: the reindexed rational matrix system and the induced integrality statement

-- This file keeps the Section 4.7 subset-indexed inequality system as the source-facing owner
-- and presents its Chapter 4.6 `Fin`-indexed matrix view as a thin bridge.

section Theorem429

section BridgeData

variable (α : Type)

section SystemData

variable [Fintype α]

/-- The Chapter 4.6 right-hand side bridge for the subset-indexed submodular system. -/
private noncomputable abbrev submodularSystemRhs (f : Finset α → ℤ) :
    Fin (Fintype.card (Finset α)) → ℚ :=
  fun i ↦ f ((Fintype.equivFin (Finset α)).symm i)

end SystemData

section TdiSystem

variable [Fintype α]

/-- The Chapter 4.6 matrix bridge for the subset-indexed submodular system, obtained by canonical
reindexing to `Fin`. -/
private noncomputable abbrev submodularSystemMatrix :
    Matrix (Fin (Fintype.card (Finset α))) (Fin (Fintype.card α)) ℚ :=
  let _ : DecidableEq α := Classical.decEq α
  let eRows :
      (Finset.univ : Finset (Finset α)) ≃ Fin (Fintype.card (Finset α)) :=
    (Equiv.subtypeUnivEquiv fun _ ↦ Finset.mem_univ _).trans (Fintype.equivFin (Finset α))
  Matrix.reindex eRows (Fintype.equivFin α)
    ((matrixOfRowSupports (Finset.univ : Finset (Finset α)) :
      Matrix (Finset.univ : Finset (Finset α)) α ℤ).map (Int.castRingHom ℚ))

end TdiSystem

end BridgeData

section TDIBridge

variable (α : Type) [Fintype α] [DecidableEq α]

/-- Helper for Theorem 4.29: relabel a finite subset along an equivalence. -/
private def relabelFinset {γ β : Type*} [DecidableEq β] (e : γ ≃ β) (S : Finset γ) : Finset β :=
  S.map e.toEmbedding

@[simp] private theorem mem_relabelFinset {γ β : Type*} [DecidableEq β]
    (e : γ ≃ β) (S : Finset γ) (b : β) :
    b ∈ relabelFinset e S ↔ e.symm b ∈ S := by
  simp [relabelFinset]

@[simp] private theorem relabelFinset_empty {γ β : Type*} [DecidableEq β] (e : γ ≃ β) :
    relabelFinset e (∅ : Finset γ) = ∅ := by
  simp [relabelFinset]

@[simp] private theorem relabelFinset_inter {γ β : Type*} [DecidableEq γ] [DecidableEq β]
    (e : γ ≃ β) (S T : Finset γ) :
    relabelFinset e (S ∩ T) = relabelFinset e S ∩ relabelFinset e T := by
  ext b
  simp

@[simp] private theorem relabelFinset_union {γ β : Type*} [DecidableEq γ] [DecidableEq β]
    (e : γ ≃ β) (S T : Finset γ) :
    relabelFinset e (S ∪ T) = relabelFinset e S ∪ relabelFinset e T := by
  ext b
  simp

@[simp] private theorem relabelFinset_relabelFinset {γ β : Type*} [DecidableEq γ] [DecidableEq β]
    (e : γ ≃ β) (S : Finset γ) :
    relabelFinset e.symm (relabelFinset e S) = S := by
  ext a
  simp

/-- Helper for Theorem 4.29: relabeling along a composed equivalence is the same as relabeling in
stages. -/
@[simp] private theorem relabelFinset_trans {γ β δ : Type*}
    [DecidableEq β] [DecidableEq δ]
    (e₁ : γ ≃ β) (e₂ : β ≃ δ) (S : Finset γ) :
    relabelFinset (e₁.trans e₂) S = relabelFinset e₂ (relabelFinset e₁ S) := by
  ext d
  simp [mem_relabelFinset]

/-- Helper for Theorem 4.29: relabeling finite subsets is itself an equivalence. -/
private def relabelFinsetEquiv {γ β : Type*} [DecidableEq γ] [DecidableEq β] (e : γ ≃ β) :
    Finset γ ≃ Finset β where
  toFun := relabelFinset e
  invFun := relabelFinset e.symm
  left_inv := relabelFinset_relabelFinset e
  right_inv := relabelFinset_relabelFinset e.symm

/-- Helper for Theorem 4.29: the submodular right-hand side can be viewed as a `Fin`-indexed set
function on `Fin (card α)`. -/
private noncomputable abbrev submodularFinFunction (f : Finset α → ℤ) :
    Finset (Fin (Fintype.card α)) → ℤ :=
  fun S ↦ f (relabelFinset (Fintype.equivFin α).symm S)

/-- Helper for Theorem 4.29: relabeling the ground set preserves submodularity. -/
private theorem submodularFinFunction_submodular
    (f : Finset α → ℤ)
    (h_submodular : Submodular f) :
    Submodular (submodularFinFunction α f) := by
  -- Reindex the meet-join inequality through the finite-set equivalence.
  intro S T
  simpa [submodularFinFunction] using
    h_submodular
      (relabelFinset (Fintype.equivFin α).symm S)
      (relabelFinset (Fintype.equivFin α).symm T)

/-- Helper for Theorem 4.29: relabeling the ground set preserves submodularity for integer-valued
set functions. -/
private theorem submodular_relabelFinset_int {γ β : Type*} [DecidableEq γ] [DecidableEq β]
    (e : γ ≃ β) (f : Finset γ → ℤ) (hf : Submodular f) :
    Submodular (fun S : Finset β ↦ f (relabelFinset e.symm S)) := by
  -- The submodular inequality is invariant under the finite-set equivalence.
  intro S T
  simpa using hf (relabelFinset e.symm S) (relabelFinset e.symm T)

/-- Helper for Theorem 4.29: the working integer normalization changes only the empty-set value. -/
private def normalizeEmptyInt {γ : Type*} [DecidableEq γ] (f : Finset γ → ℤ) :
    Finset γ → ℤ :=
  fun S ↦ if S = ∅ then 0 else f S

/-- Helper for Theorem 4.29: the integer normalization sends the empty set to `0`. -/
@[simp] private theorem normalizeEmptyInt_empty {γ : Type*} [DecidableEq γ]
    (f : Finset γ → ℤ) :
    normalizeEmptyInt f ∅ = 0 := by
  simp [normalizeEmptyInt]

/-- Helper for Theorem 4.29: the integer normalization agrees with the original function on
nonempty subsets. -/
private theorem normalizeEmptyInt_of_ne_empty {γ : Type*} [DecidableEq γ]
    (f : Finset γ → ℤ) {S : Finset γ} (hS : S ≠ ∅) :
    normalizeEmptyInt f S = f S := by
  simp [normalizeEmptyInt, hS]

/-- Helper for Theorem 4.29: if `f ∅` is nonnegative, changing only the empty-set value preserves
submodularity. -/
private theorem submodularNormalizeEmptyInt {γ : Type*} [DecidableEq γ]
    (f : Finset γ → ℤ) (hf : Submodular f) (hEmptyNonneg : 0 ≤ f ∅) :
    Submodular (normalizeEmptyInt f) := by
  -- Handle the empty-set cases explicitly, then reuse the original submodularity inequality.
  intro S T
  by_cases hS : S = ∅
  · subst hS
    simp [normalizeEmptyInt]
  by_cases hT : T = ∅
  · subst hT
    simp [normalizeEmptyInt]
  by_cases hI : S ∩ T = ∅
  · have hsub : f (S ∩ T) + f (S ∪ T) ≤ f S + f T := hf S T
    have hzero : 0 ≤ f (S ∩ T) := by
      simpa [hI] using hEmptyNonneg
    have hmain : f (S ∪ T) ≤ f S + f T := by
      linarith
    simpa [normalizeEmptyInt, hS, hT, hI] using hmain
  · simpa [normalizeEmptyInt, hS, hT, hI] using hf S T

/-- Helper for Theorem 4.29: if `f ∅` is nonnegative, changing only the empty-set value does not
change the submodular polyhedron after casting to `ℝ`. -/
private theorem mem_submodularPolyhedron_normalizeEmptyInt_iff
    (f : Finset α → ℤ) (hEmptyNonneg : 0 ≤ f ∅) {x : α → ℝ} :
    x ∈ submodularPolyhedron (fun S ↦ (normalizeEmptyInt f S : ℝ)) ↔
      x ∈ submodularPolyhedron (fun S ↦ (f S : ℝ)) := by
  rw [mem_submodularPolyhedron_iff, mem_submodularPolyhedron_iff]
  constructor
  · intro hx S
    by_cases hS : S = ∅
    · subst hS
      have hCast : (0 : ℝ) ≤ (f ∅ : ℝ) := by
        exact_mod_cast hEmptyNonneg
      simpa using hCast
    · simpa [normalizeEmptyInt, hS] using hx S
  · intro hx S
    by_cases hS : S = ∅
    · subst hS
      simp [normalizeEmptyInt]
    · simpa [normalizeEmptyInt, hS] using hx S

/-- Helper for Theorem 4.29: summing over a relabeled finite set is the same as composing the
summand with the relabeling equivalence. -/
private theorem sum_relabelFinset {γ β : Type*} [DecidableEq β]
    (e : γ ≃ β) (x : β → ℝ) (S : Finset γ) :
    Finset.sum (relabelFinset e S) x = Finset.sum S (fun a ↦ x (e a)) := by
  simpa [relabelFinset] using Finset.sum_map (f := x) e.toEmbedding S

/-- Helper for Theorem 4.29: the nonempty greedy prefixes on `Fin n` are indexed injectively by
their length. -/
private theorem submodularGreedyPrefix_succ_injective (n : ℕ) :
    Function.Injective (fun k : Fin n ↦ submodularGreedyPrefix n (k.1 + 1)) := by
  intro i j hij
  -- Compare membership of each index in the equal prefixes to recover both inequalities.
  have hi_mem : i ∈ submodularGreedyPrefix n (i.1 + 1) := by
    simpa using (mem_submodularGreedyPrefix_iff n (i.1 + 1) i).2 (Nat.lt_succ_self _)
  have hj_mem : j ∈ submodularGreedyPrefix n (j.1 + 1) := by
    simpa using (mem_submodularGreedyPrefix_iff n (j.1 + 1) j).2 (Nat.lt_succ_self _)
  have hij_le : i.1 ≤ j.1 := by
    have hi_mem' : i ∈ submodularGreedyPrefix n (j.1 + 1) := by simpa [hij] using hi_mem
    exact Nat.lt_succ_iff.mp ((mem_submodularGreedyPrefix_iff n (j.1 + 1) i).1 hi_mem')
  have hji_le : j.1 ≤ i.1 := by
    have hj_mem' : j ∈ submodularGreedyPrefix n (i.1 + 1) := by simpa [hij] using hj_mem
    exact Nat.lt_succ_iff.mp ((mem_submodularGreedyPrefix_iff n (i.1 + 1) j).1 hj_mem')
  exact Fin.ext (Nat.le_antisymm hij_le hji_le)

/-- Helper for Theorem 4.29: the sorted dual certificate uses consecutive coefficient gaps, with
zero appended after the last coefficient. -/
private def sortedPrefixGap {n : ℕ} (c : Fin n → ℤ) (k : Fin n) : ℤ :=
  c k - if hk : k.1 + 1 < n then c ⟨k.1 + 1, hk⟩ else 0

/-- Helper for Theorem 4.29: the subset-side dual certificate is supported on the greedy prefix
chain. -/
private def sortedPrefixDualVector {n : ℕ} (c : Fin n → ℤ) (S : Finset (Fin n)) : ℝ :=
  ∑ k : Fin n,
    if S = submodularGreedyPrefix n (k.1 + 1) then (sortedPrefixGap c k : ℝ) else 0

/-- Helper for Theorem 4.29: each prefix set carries exactly its own coefficient gap. -/
private theorem sortedPrefixDualVector_apply_prefix {n : ℕ} (c : Fin n → ℤ) (k : Fin n) :
    sortedPrefixDualVector c (submodularGreedyPrefix n (k.1 + 1)) = (sortedPrefixGap c k : ℝ) := by
  -- Isolate the unique nonzero summand coming from the matching prefix index `k`.
  unfold sortedPrefixDualVector
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
  · simp
  · intro j _ hj
    have hprefix :
        submodularGreedyPrefix n (k.1 + 1) ≠ submodularGreedyPrefix n (j.1 + 1) := by
      intro hEq
      exact hj ((submodularGreedyPrefix_succ_injective n) hEq.symm)
    simp [hprefix]

/-- Helper for Theorem 4.29: the prefix-chain certificate vanishes away from the greedy chain. -/
private theorem sortedPrefixDualVector_eq_zero_of_not_prefix {n : ℕ} (c : Fin n → ℤ)
    {S : Finset (Fin n)}
    (hS : ∀ k : Fin n, S ≠ submodularGreedyPrefix n (k.1 + 1)) :
    sortedPrefixDualVector c S = 0 := by
  -- Every support test in the defining sum fails, so all summands vanish.
  unfold sortedPrefixDualVector
  refine Finset.sum_eq_zero ?_
  intro k hk
  simp [hS k]

/-- Helper for Theorem 4.29: the empty set receives zero weight in the prefix-chain certificate. -/
private theorem sortedPrefixDualVector_empty {n : ℕ} (c : Fin n → ℤ) :
    sortedPrefixDualVector c (∅ : Finset (Fin n)) = 0 := by
  -- Every nonempty prefix contains its endpoint `k`, so the empty set is outside the support.
  refine sortedPrefixDualVector_eq_zero_of_not_prefix c ?_
  intro k hEq
  have hk_mem : k ∈ submodularGreedyPrefix n (k.1 + 1) := by
    simpa using (mem_submodularGreedyPrefix_iff n (k.1 + 1) k).2 (Nat.lt_succ_self _)
  have : k ∈ (∅ : Finset (Fin n)) := by simpa [hEq] using hk_mem
  simpa using this

/-- Helper for Theorem 4.29: summing the prefix-chain certificate against any test function
collapses to the greedy prefix support. -/
private theorem sortedPrefixDualVector_sum_over_prefixes {n : ℕ}
    (c : Fin n → ℤ) (φ : Finset (Fin n) → ℝ) :
    ∑ S : Finset (Fin n), sortedPrefixDualVector c S * φ S =
      ∑ k : Fin n, (sortedPrefixGap c k : ℝ) * φ (submodularGreedyPrefix n (k.1 + 1)) := by
  classical
  -- Expand the supported certificate and swap the two finite sums before isolating each prefix.
  unfold sortedPrefixDualVector
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Finset.sum_eq_single_of_mem (submodularGreedyPrefix n (k.1 + 1)) (Finset.mem_univ _)]
  · simp
  · intro S _ hS
    simp [hS]

/-- Helper for Theorem 4.29: every zero-tail coefficient gap is nonnegative for an antitone
nonnegative objective sequence. -/
private theorem sortedPrefixGap_nonneg {n : ℕ} (c : Fin n → ℤ)
    (hAntitone : Antitone c) (hNonneg : ∀ i, 0 ≤ c i) (k : Fin n) :
    0 ≤ sortedPrefixGap c k := by
  by_cases hk : k.1 + 1 < n
  · -- On a genuine successor step, the gap is nonnegative by antitonicity.
    let kSucc : Fin n := ⟨k.1 + 1, hk⟩
    have hstep : c kSucc ≤ c k := by
      exact hAntitone (Fin.le_iff_val_le_val.mpr (Nat.le_succ _))
    simpa [sortedPrefixGap, hk, kSucc] using sub_nonneg.mpr hstep
  · -- At the last index, the zero-tail convention leaves the final coefficient itself.
    simpa [sortedPrefixGap, hk] using hNonneg k

/-- Helper for Theorem 4.29: the prefix-chain certificate is pointwise nonnegative once the sorted
objective coefficients are antitone and nonnegative. -/
private theorem sortedPrefixDualVector_nonneg {n : ℕ} (c : Fin n → ℤ)
    (hAntitone : Antitone c) (hNonneg : ∀ i, 0 ≤ c i) (S : Finset (Fin n)) :
    0 ≤ sortedPrefixDualVector c S := by
  classical
  -- Either `S` is one of the supported prefixes, or the certificate vanishes there.
  by_cases hS : ∃ k : Fin n, S = submodularGreedyPrefix n (k.1 + 1)
  · rcases hS with ⟨k, rfl⟩
    simpa [sortedPrefixDualVector_apply_prefix] using
      (sortedPrefixGap_nonneg c hAntitone hNonneg k)
  · have hS' : ∀ k : Fin n, S ≠ submodularGreedyPrefix n (k.1 + 1) := by
      intro k hEq
      exact hS ⟨k, hEq⟩
    simp [sortedPrefixDualVector_eq_zero_of_not_prefix, hS']

/-- Helper for Theorem 4.29: every coordinate of the prefix-chain certificate is an integer. -/
private theorem sortedPrefixDualVector_integer {n : ℕ} (c : Fin n → ℤ) (S : Finset (Fin n)) :
    sortedPrefixDualVector c S ∈ Set.range (Int.cast : ℤ → ℝ) := by
  -- The certificate is either one explicit prefix gap or the zero value off the prefix chain.
  by_cases hS : ∃ k : Fin n, S = submodularGreedyPrefix n (k.1 + 1)
  · rcases hS with ⟨k, rfl⟩
    exact ⟨sortedPrefixGap c k, by simpa [sortedPrefixDualVector_apply_prefix]⟩
  · have hS' : ∀ k : Fin n, S ≠ submodularGreedyPrefix n (k.1 + 1) := by
      intro k hEq
      exact hS ⟨k, hEq⟩
    exact ⟨0, by simpa [sortedPrefixDualVector_eq_zero_of_not_prefix, hS']⟩

/-- Helper for Theorem 4.29: the zero-tail gaps telescope along the prefix chain to recover each
sorted objective coefficient. -/
private theorem sortedPrefixGap_tailSum {n : ℕ} (c : Fin n → ℤ) (i : Fin n) :
    (∑ k : Fin n, if i.1 < k.1 + 1 then (sortedPrefixGap c k : ℝ) else 0) = (c i : ℝ) := by
  let a : ℕ → ℝ := fun m ↦ if hm : m < n then (c ⟨m, hm⟩ : ℝ) else 0
  let gapNat : ℕ → ℝ := fun k ↦ if hk : k < n then (sortedPrefixGap c ⟨k, hk⟩ : ℝ) else 0
  have hgap : ∀ k : Fin n, (sortedPrefixGap c k : ℝ) = a k.1 - a (k.1 + 1) := by
    intro k
    -- Rewrite each coefficient gap against the zero-tail extension `a`.
    by_cases hk : k.1 + 1 < n
    · simp [sortedPrefixGap, a, hk]
    · simp [sortedPrefixGap, a, hk]
  have hfilter :
      (Finset.range n).filter (fun k : ℕ => i.1 < k + 1) = Finset.Ico i.1 n := by
    -- The tail condition `i < k + 1` is exactly the interval condition `i ≤ k < n`.
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Nat.lt_succ_iff]
    constructor
    · intro hk
      exact ⟨hk.2, hk.1⟩
    · intro hk
      exact ⟨hk.2, hk.1⟩
  have htail :
      (∑ k : Fin n, if i.1 < k.1 + 1 then (sortedPrefixGap c k : ℝ) else 0) =
        Finset.sum (Finset.Ico i.1 n) (fun k ↦ a k - a (k + 1)) := by
    have hrange :
        (∑ k : Fin n, if i.1 < k.1 + 1 then (sortedPrefixGap c k : ℝ) else 0) =
          Finset.sum (Finset.range n) (fun k ↦ if i.1 < k + 1 then gapNat k else 0) := by
      simpa [gapNat] using
        (Fin.sum_univ_eq_sum_range
          (fun k : ℕ ↦ if i.1 < k + 1 then gapNat k else 0) n)
    rw [hrange]
    rw [← Finset.sum_filter]
    rw [hfilter]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_lt : k < n := (Finset.mem_Ico.mp hk).2
    simp [gapNat, hk_lt, hgap ⟨k, hk_lt⟩]
  have htel :
      Finset.sum (Finset.Ico i.1 n) (fun k ↦ a k - a (k + 1)) = a i.1 - a n := by
    have hrange :
        ∀ m : ℕ, Finset.sum (Finset.range m) (fun k ↦ a k - a (k + 1)) = a 0 - a m := by
      intro m
      induction m with
      | zero =>
          simp
      | succ m hm =>
          rw [Finset.sum_range_succ, hm]
          ring
    -- Rewrite the interval sum as a difference of two telescoping range sums.
    calc
      Finset.sum (Finset.Ico i.1 n) (fun k ↦ a k - a (k + 1))
        = Finset.sum (Finset.range n) (fun k ↦ a k - a (k + 1)) -
            Finset.sum (Finset.range i.1) (fun k ↦ a k - a (k + 1)) := by
              simpa using
                (Finset.sum_Ico_eq_sub (fun k ↦ a k - a (k + 1)) (Nat.le_of_lt i.isLt))
      _ = (a 0 - a n) - (a 0 - a i.1) := by rw [hrange, hrange]
      _ = a i.1 - a n := by ring
  calc
    (∑ k : Fin n, if i.1 < k.1 + 1 then (sortedPrefixGap c k : ℝ) else 0)
      = Finset.sum (Finset.Ico i.1 n) (fun k ↦ a k - a (k + 1)) := htail
    _ = a i.1 - a n := htel
    _ = (c i : ℝ) := by
          simp [a, i.isLt]

/-- Helper for Theorem 4.29: summing the prefix-chain dual certificate over all sets containing a
given element recovers the corresponding sorted objective coefficient. -/
private theorem sortedPrefixDualVector_coordinate {n : ℕ} (c : Fin n → ℤ) (i : Fin n) :
    (∑ S : Finset (Fin n), (if i ∈ S then sortedPrefixDualVector c S else (0 : ℝ))) = (c i : ℝ) := by
  -- Collapse the supported subset sum to the prefix chain and then telescope the tail gaps.
  calc
    ∑ S : Finset (Fin n), (if i ∈ S then sortedPrefixDualVector c S else (0 : ℝ))
      = ∑ S : Finset (Fin n),
          sortedPrefixDualVector c S * (if i ∈ S then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            by_cases hiS : i ∈ S <;> simp [hiS]
    _ = ∑ k : Fin n,
          (sortedPrefixGap c k : ℝ) *
            (if i ∈ submodularGreedyPrefix n (k.1 + 1) then (1 : ℝ) else 0) := by
          simpa using
            sortedPrefixDualVector_sum_over_prefixes c
              (fun S : Finset (Fin n) ↦ if i ∈ S then (1 : ℝ) else 0)
    _ = ∑ k : Fin n, if i.1 < k.1 + 1 then (sortedPrefixGap c k : ℝ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          by_cases hik : i.1 < k.1 + 1
          · simp [mem_submodularGreedyPrefix_iff, hik]
          · simp [mem_submodularGreedyPrefix_iff, hik]
    _ = (c i : ℝ) := sortedPrefixGap_tailSum c i

/-- Helper for Theorem 4.29: Abel summation on nat ranges converts the prefix-gap expression into
the greedy objective expression once the tail and initial terms vanish. -/
private theorem prefixGapObjective_rangeByParts
    (a G : ℕ → ℝ) (n : ℕ) (haTail : a n = 0) (hGZero : G 0 = 0) :
    Finset.sum (Finset.range n) (fun k ↦ G (k + 1) * (a k - a (k + 1))) =
      Finset.sum (Finset.range n) (fun k ↦ a k * (G (k + 1) - G k)) := by
  -- Apply Abel summation to the difference sequence `G (k + 1) - G k`.
  have hparts :
      Finset.sum (Finset.range (n + 1)) (fun k ↦ a k * (G (k + 1) - G k)) =
        a n * Finset.sum (Finset.range (n + 1)) (fun k ↦ (G (k + 1) - G k)) -
          Finset.sum (Finset.range n)
            (fun k ↦ (a (k + 1) - a k) *
              Finset.sum (Finset.range (k + 1)) (fun j ↦ (G (j + 1) - G j))) := by
    simpa [smul_eq_mul] using
      (Finset.sum_range_by_parts a (fun k ↦ G (k + 1) - G k) (n + 1))
  have hpartial :
      ∀ k : ℕ,
        Finset.sum (Finset.range (k + 1)) (fun j ↦ (G (j + 1) - G j)) = G (k + 1) - G 0 := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k hk =>
        rw [Finset.sum_range_succ, hk]
        ring
  have hleft :
      Finset.sum (Finset.range (n + 1)) (fun k ↦ a k * (G (k + 1) - G k)) =
        Finset.sum (Finset.range n) (fun k ↦ a k * (G (k + 1) - G k)) := by
    rw [Finset.sum_range_succ]
    simp [haTail]
  have hpartials :
      Finset.sum (Finset.range n)
          (fun k ↦ (a (k + 1) - a k) *
            Finset.sum (Finset.range (k + 1)) (fun j ↦ (G (j + 1) - G j))) =
        Finset.sum (Finset.range n) (fun k ↦ (a (k + 1) - a k) * G (k + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [hpartial, hGZero]
    ring_nf
  have hmain :
      Finset.sum (Finset.range n) (fun k ↦ a k * (G (k + 1) - G k)) =
        Finset.sum (Finset.range n) (fun k ↦ G (k + 1) * (a k - a (k + 1))) := by
    calc
      Finset.sum (Finset.range n) (fun k ↦ a k * (G (k + 1) - G k))
        = Finset.sum (Finset.range (n + 1)) (fun k ↦ a k * (G (k + 1) - G k)) := hleft.symm
      _ = a n * Finset.sum (Finset.range (n + 1)) (fun k ↦ (G (k + 1) - G k)) -
            Finset.sum (Finset.range n)
              (fun k ↦ (a (k + 1) - a k) *
                Finset.sum (Finset.range (k + 1)) (fun j ↦ (G (j + 1) - G j))) := hparts
      _ = -Finset.sum (Finset.range n) (fun k ↦ (a (k + 1) - a k) * G (k + 1)) := by
            rw [hpartials]
            simp [haTail]
      _ = Finset.sum (Finset.range n) (fun k ↦ G (k + 1) * (a k - a (k + 1))) := by
            have hneg :
                -Finset.sum (Finset.range n) (fun k ↦ (a (k + 1) - a k) * G (k + 1)) =
                  Finset.sum (Finset.range n)
                    (fun k ↦ -((a (k + 1) - a k) * G (k + 1))) := by
              simpa using
                (Finset.sum_neg_distrib
                  (s := Finset.range n)
                  (f := fun k ↦ (a (k + 1) - a k) * G (k + 1))).symm
            rw [hneg]
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
  exact hmain.symm

/-- Helper for Theorem 4.29: Abel summation turns the prefix-gap dual objective into the greedy
primal objective. -/
private theorem sortedPrefixDualObjective_eq_greedyObjective {n : ℕ}
    (g : Finset (Fin n) → ℤ) (c : Fin n → ℤ) (hgEmpty : g ∅ = 0) :
    ∑ S : Finset (Fin n), sortedPrefixDualVector c S * (g S : ℝ) =
      ∑ i : Fin n, (c i : ℝ) * submodularGreedySolution g i := by
  let a : ℕ → ℝ := fun k ↦ if hk : k < n then (c ⟨k, hk⟩ : ℝ) else 0
  let G : ℕ → ℝ := fun k ↦ (g (submodularGreedyPrefix n k) : ℝ)
  have hLeft :
      ∑ S : Finset (Fin n), sortedPrefixDualVector c S * (g S : ℝ) =
        Finset.sum (Finset.range n) (fun k ↦ G (k + 1) * (a k - a (k + 1))) := by
    calc
      ∑ S : Finset (Fin n), sortedPrefixDualVector c S * (g S : ℝ)
        = ∑ k : Fin n,
            (sortedPrefixGap c k : ℝ) *
              (g (submodularGreedyPrefix n (k.1 + 1)) : ℝ) := by
              simpa using sortedPrefixDualVector_sum_over_prefixes c (fun S ↦ (g S : ℝ))
      _ = Finset.sum (Finset.range n) (fun k ↦ G (k + 1) * (a k - a (k + 1))) := by
            have hrange :
                (∑ k : Fin n,
                    (sortedPrefixGap c k : ℝ) *
                      (g (submodularGreedyPrefix n (k.1 + 1)) : ℝ)) =
                  Finset.sum (Finset.range n)
                    (fun k ↦
                      if hk : k < n then
                        (sortedPrefixGap c ⟨k, hk⟩ : ℝ) *
                          (g (submodularGreedyPrefix n (k + 1)) : ℝ)
                      else 0) := by
              simpa using
                (Fin.sum_univ_eq_sum_range
                  (fun k : ℕ ↦
                    if hk : k < n then
                      (sortedPrefixGap c ⟨k, hk⟩ : ℝ) *
                        (g (submodularGreedyPrefix n (k + 1)) : ℝ)
                    else 0) n)
            rw [hrange]
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hklt : k < n := Finset.mem_range.mp hk
            by_cases hk' : k + 1 < n
            · simp [G, a, sortedPrefixGap, hklt, hk']; ring_nf
            · simp [G, a, sortedPrefixGap, hklt, hk']; ring_nf
  have hRight :
      ∑ i : Fin n, (c i : ℝ) * submodularGreedySolution g i =
        Finset.sum (Finset.range n) (fun k ↦ a k * (G (k + 1) - G k)) := by
    have hrange :
        (∑ i : Fin n, (c i : ℝ) * submodularGreedySolution g i) =
          Finset.sum (Finset.range n)
            (fun k ↦ if hk : k < n then (c ⟨k, hk⟩ : ℝ) * submodularGreedySolution g ⟨k, hk⟩ else 0) := by
      simpa using
        (Fin.sum_univ_eq_sum_range
          (fun k : ℕ ↦ if hk : k < n then (c ⟨k, hk⟩ : ℝ) * submodularGreedySolution g ⟨k, hk⟩ else 0)
          n)
    rw [hrange]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [a, G, submodularGreedySolution, submodularGreedySolutionInt, hk]
  have hGZero : G 0 = 0 := by
    simp [G, hgEmpty, submodularGreedyPrefix]
  have haTail : a n = 0 := by
    simp [a]
  calc
    ∑ S : Finset (Fin n), sortedPrefixDualVector c S * (g S : ℝ)
      = Finset.sum (Finset.range n) (fun k ↦ G (k + 1) * (a k - a (k + 1))) := hLeft
    _ = Finset.sum (Finset.range n) (fun k ↦ a k * (G (k + 1) - G k)) := by
          exact prefixGapObjective_rangeByParts a G n haTail hGZero
    _ = ∑ i : Fin n, (c i : ℝ) * submodularGreedySolution g i := hRight.symm

end TDIBridge

section IntegralBridge

variable (α : Type) [Fintype α]

@[simp] private theorem submodularCoordinateReindex_apply
    (y : Fin (Fintype.card α) → ℝ) (a : α) :
    LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α) y a = y ((Fintype.equivFin α) a) := by
  simp

@[simp] private theorem submodularCoordinateReindex_symm_apply
    (x : α → ℝ) (j : Fin (Fintype.card α)) :
    (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α)).symm x j =
      x ((Fintype.equivFin α).symm j) := by
  simp

section MatrixTransport

variable [DecidableEq α]

omit [DecidableEq α] in
private theorem submodularSystemMatrix_mulVec_apply
    (y : Fin (Fintype.card α) → ℝ) (i : Fin (Fintype.card (Finset α))) :
    (((submodularSystemMatrix α).map (Rat.castHom ℝ)) *ᵥ y) i =
      ((Fintype.equivFin (Finset α)).symm i).sum (fun a ↦ y ((Fintype.equivFin α) a)) := by
  classical
  let eCols : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let eRows :
      (Finset.univ : Finset (Finset α)) ≃ Fin (Fintype.card (Finset α)) :=
    (Equiv.subtypeUnivEquiv fun _ ↦ Finset.mem_univ _).trans (Fintype.equivFin (Finset α))
  let M : Matrix (Finset.univ : Finset (Finset α)) α ℝ :=
    ((matrixOfRowSupports (Finset.univ : Finset (Finset α)) :
      Matrix (Finset.univ : Finset (Finset α)) α ℤ).map (Int.castRingHom ℝ))
  have hmatrix :
      ((submodularSystemMatrix α).map (Rat.castHom ℝ)) = Matrix.reindex eRows eCols M := by
    ext r c
    simp [submodularSystemMatrix, M, eRows, eCols, Equiv.subtypeUnivEquiv_symm_apply]
  have hreindex :
      Matrix.reindex eRows eCols M *ᵥ y =
        fun j ↦ (M *ᵥ LinearEquiv.funCongrLeft ℝ ℝ eCols y) (eRows.symm j) := by
    simpa [Matrix.reindex, eCols] using
      (Matrix.submatrix_mulVec_equiv M y eRows.symm eCols.symm)
  calc
    (((submodularSystemMatrix α).map (Rat.castHom ℝ)) *ᵥ y) i
      = (Matrix.reindex eRows eCols M *ᵥ y) i := by rw [hmatrix]
    _ = (fun j ↦ (M *ᵥ LinearEquiv.funCongrLeft ℝ ℝ eCols y) (eRows.symm j)) i := by
          rw [hreindex]
    _ = (M *ᵥ LinearEquiv.funCongrLeft ℝ ℝ eCols y) (eRows.symm i) := rfl
    _ = ((eRows.symm i : Finset α)).sum (LinearEquiv.funCongrLeft ℝ ℝ eCols y) := by
          simpa [M] using
            matrixOfRowSupports_mulVec_apply (Finset.univ : Finset (Finset α))
              (LinearEquiv.funCongrLeft ℝ ℝ eCols y) (eRows.symm i)
    _ = ((Fintype.equivFin (Finset α)).symm i).sum (fun a ↦ y (eCols a)) := by
          simp [eRows, eCols, Equiv.subtypeUnivEquiv_symm_apply]

/-- Helper for Theorem 4.29: evaluating the matrix dual equality at a ground element is exactly the
subset-indexed row sum over all sets containing that element. -/
private theorem submodularSystemMatrix_vecMul_apply
    (y : Fin (Fintype.card (Finset α)) → ℝ) (a : α) :
    (y ᵥ* ((submodularSystemMatrix α).map (Rat.castHom ℝ))) ((Fintype.equivFin α) a) =
      ∑ S : Finset α, if a ∈ S then y ((Fintype.equivFin (Finset α)) S) else 0 := by
  classical
  -- Expand the column evaluation and then reindex the finite sum back to actual subsets.
  calc
    (y ᵥ* ((submodularSystemMatrix α).map (Rat.castHom ℝ))) ((Fintype.equivFin α) a)
      = ∑ i : Fin (Fintype.card (Finset α)),
          y i *
            (((submodularSystemMatrix α).map (Rat.castHom ℝ)) i ((Fintype.equivFin α) a)) := by
          simp [Matrix.vecMul, dotProduct]
    _ = ∑ i : Fin (Fintype.card (Finset α)),
          if a ∈ ((Fintype.equivFin (Finset α)).symm i) then y i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hmem : a ∈ ((Fintype.equivFin (Finset α)).symm i)
          · simp [submodularSystemMatrix, matrixOfRowSupports, rowOfSupport,
              Equiv.subtypeUnivEquiv_symm_apply, hmem]
          · simp [submodularSystemMatrix, matrixOfRowSupports, rowOfSupport,
              Equiv.subtypeUnivEquiv_symm_apply, hmem]
    _ = ∑ S : Finset α, if a ∈ S then y ((Fintype.equivFin (Finset α)) S) else 0 := by
          symm
          exact Fintype.sum_equiv (Fintype.equivFin (Finset α)) _ _ fun i ↦ by
            simp

/-- Helper for Theorem 4.29: reindexing coordinates along `Fintype.equivFin α` preserves the primal
linear objective. -/
private theorem submodular_primal_objective_reindex
    (c : α → ℤ) (x : Fin (Fintype.card α) → ℝ) :
    (fun j ↦ (c ((Fintype.equivFin α).symm j) : ℝ)) ⬝ᵥ x =
      ∑ a, (c a : ℝ) * (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α) x) a := by
  classical
  -- Reindex the `Fin`-sum back to the original ground set.
  symm
  exact Fintype.sum_equiv (Fintype.equivFin α) _ _ fun j ↦ by
    simp [submodularCoordinateReindex_apply]

/-- Helper for Theorem 4.29: reindexing subset rows along `Fintype.equivFin (Finset α)` preserves
the dual objective. -/
private theorem submodular_dual_objective_reindex
    (f : Finset α → ℤ) (y : Fin (Fintype.card (Finset α)) → ℝ) :
    y ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) =
      ∑ S : Finset α, y ((Fintype.equivFin (Finset α)) S) * (f S : ℝ) := by
  classical
  -- Reindex the finite row sum from `Fin` back to actual subsets.
  symm
  exact Fintype.sum_equiv (Fintype.equivFin (Finset α)) _ _ fun i ↦ by
    simp [submodularSystemRhs]

omit [Fintype α] [DecidableEq α] in
private theorem funCongrLeft_symm_image_integerPoints
    {β : Type*} (e : α ≃ β) :
    (LinearEquiv.funCongrLeft ℝ ℝ e.symm) ''
        Set.range (fun z : α → ℤ ↦ Int.cast ∘ z) =
      Set.range (fun z : β → ℤ ↦ Int.cast ∘ z) := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    refine ⟨z ∘ e.symm, ?_⟩
    funext b
    simp
  · rintro ⟨z, rfl⟩
    refine ⟨Int.cast ∘ z ∘ e, ?_, ?_⟩
    · exact ⟨z ∘ e, rfl⟩
    · funext b
      simp

omit [Fintype α] [DecidableEq α] in
private theorem funCongrLeft_symm_image_inter
    {β : Type*} (e : α ≃ β)
    (P Q : Set (α → ℝ)) :
    (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' (P ∩ Q) =
      (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P ∩
        (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' Q := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxP, hxQ⟩, rfl⟩
    exact ⟨⟨x, hxP, rfl⟩, ⟨x, hxQ, rfl⟩⟩
  · rintro ⟨⟨x, hxP, rfl⟩, ⟨x', hxQ, hImage⟩⟩
    have hxx' : x = x' := by
      apply (LinearEquiv.funCongrLeft ℝ ℝ e.symm).injective
      simpa using hImage.symm
    exact ⟨x, ⟨hxP, hxx' ▸ hxQ⟩, rfl⟩

omit [Fintype α] [DecidableEq α] in
private theorem is_integral_funCongrLeft_symm_image
    {β : Type*} [Finite α] [Finite β] (e : α ≃ β)
    {P : Set (α → ℝ)} (hP : is_integral P) :
    is_integral ((LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P) := by
  rw [is_integral_iff] at hP ⊢
  calc
    (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P
      = (LinearEquiv.funCongrLeft ℝ ℝ e.symm) ''
          convexHull ℝ
            (P ∩ Set.range (fun z : α → ℤ ↦ Int.cast ∘ z)) := by
          exact congrArg (Set.image (LinearEquiv.funCongrLeft ℝ ℝ e.symm)) hP
    _ = convexHull ℝ
          ((LinearEquiv.funCongrLeft ℝ ℝ e.symm) ''
            (P ∩ Set.range (fun z : α → ℤ ↦ Int.cast ∘ z))) := by
          simpa using
            (LinearEquiv.funCongrLeft ℝ ℝ e.symm).toLinearMap.image_convexHull
              (P ∩ Set.range (fun z : α → ℤ ↦ Int.cast ∘ z))
    _ = convexHull ℝ
          ((LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P ∩
            Set.range (fun z : β → ℤ ↦ Int.cast ∘ z)) := by
          rw [funCongrLeft_symm_image_inter, funCongrLeft_symm_image_integerPoints]

/- Internal bridge: the submodular polyhedron is the image of its Chapter 4.1 rational matrix
presentation under the canonical coordinate reindexing by `Fintype.equivFin α`. -/
omit [DecidableEq α] in
private theorem submodularPolyhedron_eq_reindexed_rational_matrix_polyhedron
    (f : Finset α → ℤ) :
    submodularPolyhedron (fun S ↦ (f S : ℝ)) =
      LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α) ''
        rational_matrix_polyhedron (submodularSystemMatrix α) (submodularSystemRhs α f) := by
  classical
  ext x
  constructor
  · intro hx
    refine ⟨(LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α)).symm x, ?_, ?_⟩
    · rw [mem_rational_matrix_polyhedron]
      intro i
      rw [submodularSystemMatrix_mulVec_apply]
      simpa [submodularCoordinateReindex_symm_apply]
        using hx ((Fintype.equivFin (Finset α)).symm i)
    · ext a
      simp
  · rintro ⟨y, hy, rfl⟩
    rw [mem_rational_matrix_polyhedron] at hy
    rw [mem_submodularPolyhedron_iff]
    intro S
    obtain ⟨i, rfl⟩ := (Fintype.equivFin (Finset α)).symm.surjective S
    have hi :
        (((submodularSystemMatrix α).map (Rat.castHom ℝ)) *ᵥ y) i ≤
          (submodularSystemRhs α f i : ℝ) := by
      simpa [submodularSystemMatrix, submodularSystemRhs] using hy i
    calc
      ∑ x ∈ (Fintype.equivFin (Finset α)).symm i,
          (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α) y) x
        = ∑ x ∈ (Fintype.equivFin (Finset α)).symm i, y ((Fintype.equivFin α) x) := by
            simp
      _
        = (((submodularSystemMatrix α).map (Rat.castHom ℝ)) *ᵥ y) i := by
            symm
            exact submodularSystemMatrix_mulVec_apply α y i
      _ ≤ (submodularSystemRhs α f i : ℝ) := hi
      _ = ↑(f ((Fintype.equivFin (Finset α)).symm i)) := by
            rfl

end MatrixTransport

section TdiMatrixProof

variable (α : Type) [Fintype α] [DecidableEq α]

/-- Helper for Theorem 4.29: the negative basis direction decreases every subset-row sum. -/
private theorem submodularSystemMatrix_negBasis_mulVec_nonpos
    (j : Fin (Fintype.card α)) :
    (((submodularSystemMatrix α).map (Rat.castHom ℝ)) *ᵥ
      (fun k : Fin (Fintype.card α) ↦ if k = j then (-1 : ℝ) else 0)) ≤ 0 := by
  intro i
  let S : Finset α := (Fintype.equivFin (Finset α)).symm i
  let T : Finset (Fin (Fintype.card α)) := relabelFinset (Fintype.equivFin α) S
  have hsum :
      Finset.sum T (fun k ↦ if k = j then (-1 : ℝ) else 0) =
        Finset.sum S (fun a ↦ if (Fintype.equivFin α) a = j then (-1 : ℝ) else 0) := by
    simpa [S, T] using
      (sum_relabelFinset (Fintype.equivFin α)
        (fun k : Fin (Fintype.card α) ↦ if k = j then (-1 : ℝ) else 0) S)
  -- Reindex the row support to `Fin`, where the direction is the single-coordinate vector `-e_j`.
  calc
    (((submodularSystemMatrix α).map (Rat.castHom ℝ)) *ᵥ
        (fun k : Fin (Fintype.card α) ↦ if k = j then (-1 : ℝ) else 0)) i
      = Finset.sum S (fun a ↦ if (Fintype.equivFin α) a = j then (-1 : ℝ) else 0) := by
          simpa [S] using
            (submodularSystemMatrix_mulVec_apply α
              (fun k : Fin (Fintype.card α) ↦ if k = j then (-1 : ℝ) else 0) i)
    _ = Finset.sum T (fun k ↦ if k = j then (-1 : ℝ) else 0) := hsum.symm
    _ ≤ 0 := by
          by_cases hj : j ∈ T
          · rw [Finset.sum_eq_single_of_mem j hj]
            · norm_num
            · intro k hk hkj
              simp [hkj]
          · simp [hj]

/-- Helper for Theorem 4.29: a finite optimum for the subset system forces every objective
coefficient to be nonnegative. -/
private theorem finiteOptimumForcesNonnegativeObjective
    (f : Finset α → ℤ) {c : Fin (Fintype.card α) → ℤ}
    (hFinite :
      rational_primal_has_finite_optimum
        (submodularSystemMatrix α) (submodularSystemRhs α f) c) :
    ∀ j, 0 ≤ c j := by
  intro j
  by_contra hj
  have hjlt : c j < 0 := lt_of_not_ge hj
  rw [rational_primal_has_finite_optimum_iff] at hFinite
  rcases hFinite with ⟨xStar, hxStar, hxGreatest⟩
  let A : Matrix (Fin (Fintype.card (Finset α))) (Fin (Fintype.card α)) ℝ :=
    (submodularSystemMatrix α).map (Rat.castHom ℝ)
  let b : Fin (Fintype.card (Finset α)) → ℝ := fun i ↦ (submodularSystemRhs α f i : ℝ)
  let cReal : Fin (Fintype.card α) → ℝ := fun i ↦ (c i : ℝ)
  let d : Fin (Fintype.card α) → ℝ := fun k ↦ if k = j then (-1 : ℝ) else 0
  have hP : Set.Nonempty (primal_feasible_region A b) := by
    refine ⟨xStar, ?_⟩
    simpa [A, b, primal_feasible_region, rational_matrix_polyhedron] using hxStar
  have hdA : A *ᵥ d ≤ 0 := by
    simpa [A, d] using submodularSystemMatrix_negBasis_mulVec_nonpos α j
  have hdc : 0 < cReal ⬝ᵥ d := by
    have hjCast : ((c j : ℝ)) < 0 := by
      exact_mod_cast hjlt
    -- The objective slope along `-e_j` is exactly `-c_j`, which is positive when `c_j < 0`.
    calc
      0 < -((c j : ℝ)) := by
            simpa using neg_pos.mpr hjCast
      _ = cReal ⬝ᵥ d := by
            simp [cReal, d, dotProduct]
  have hBdd : BddAbove (primal_objective_values A b cReal) := by
    refine ⟨cReal ⬝ᵥ xStar, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact hxGreatest.2
      ⟨x, by simpa [A, b, primal_feasible_region, rational_matrix_polyhedron] using hx, rfl⟩
  exact (primal_objective_values_not_bddAbove_of_improving_direction A b cReal hP hdA hdc) hBdd

/-- Theorem 4.29: reindexing the subset-inequality system to the Chapter 4.6 `Fin`-indexed matrix
presentation preserves total dual integrality. -/
private theorem submodular_system_tdi_matrix
    (f : Finset α → ℤ)
    (h_submodular : Submodular f) :
    totally_dual_integral (submodularSystemMatrix α) (submodularSystemRhs α f) := by
  -- Route correction: the sorted greedy construction stays entirely in the normalized `Fin` world,
  -- and only the final dual witness is transported back to subset rows of the Chapter 4.6 matrix.
  intro c hFinite
  classical
  have hFiniteOrig := hFinite
  rw [rational_dual_has_integral_optimal_solution_iff]
  rw [rational_primal_has_finite_optimum_iff] at hFinite
  rcases hFinite with ⟨xStar, hxStar, hxGreatest⟩
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let xOrig : α → ℝ := LinearEquiv.funCongrLeft ℝ ℝ e xStar
  have hxOrig_mem :
      xOrig ∈ submodularPolyhedron (fun S ↦ (f S : ℝ)) := by
    -- Transport the maximizing matrix point once back to the subset-indexed polyhedron.
    have hxImage :
        xOrig ∈
          LinearEquiv.funCongrLeft ℝ ℝ e ''
            rational_matrix_polyhedron (submodularSystemMatrix α) (submodularSystemRhs α f) :=
      ⟨xStar, hxStar, rfl⟩
    simpa [submodularPolyhedron_eq_reindexed_rational_matrix_polyhedron α f, xOrig, e] using
      hxImage
  have hEmptyNonneg : 0 ≤ f ∅ := by
    -- The empty-set inequality forces the normalization side condition needed by the greedy route.
    have hEmpty : (0 : ℝ) ≤ (f ∅ : ℝ) := by
      simpa using hxOrig_mem ∅
    exact_mod_cast hEmpty
  have hNonneg : ∀ j, 0 ≤ c j :=
    finiteOptimumForcesNonnegativeObjective α f hFiniteOrig
  let n : ℕ := Fintype.card α
  let fFin : Finset (Fin n) → ℤ := submodularFinFunction α f
  let f0 : Finset (Fin n) → ℤ := normalizeEmptyInt fFin
  have hf0_sub : Submodular f0 := by
    -- Normalizing only the empty-set value preserves submodularity once `f ∅ ≥ 0`.
    refine submodularNormalizeEmptyInt fFin ?_ ?_
    · simpa [fFin] using submodularFinFunction_submodular α f h_submodular
    · simpa [fFin] using hEmptyNonneg
  have hxFin_mem :
      xStar ∈ submodularPolyhedron (fun S ↦ (fFin S : ℝ)) := by
    rw [mem_submodularPolyhedron_iff]
    intro S
    -- Reindex each subset inequality from the original ground set to `Fin`.
    simpa [xOrig, fFin, e, sum_relabelFinset] using
      hxOrig_mem (relabelFinset e.symm S)
  have hxFin0_mem :
      xStar ∈ submodularPolyhedron (fun S ↦ (f0 S : ℝ)) := by
    -- The matrix point remains feasible after the empty-set normalization.
    refine (mem_submodularPolyhedron_normalizeEmptyInt_iff
      (α := Fin n) fFin (by simpa [fFin] using hEmptyNonneg)).2 hxFin_mem
  let σ : Equiv.Perm (Fin n) := Tuple.sort (fun j ↦ OrderDual.toDual (c j))
  let cSorted : Fin n → ℤ := fun j ↦ c (σ j)
  have hSorted : Antitone cSorted := by
    -- Sorting the integral objective is the single order-normalization needed by the greedy proof.
    simpa [cSorted, σ] using Tuple.monotone_sort (fun j ↦ OrderDual.toDual (c j))
  have hSorted_nonneg : ∀ j, 0 ≤ cSorted j := by
    intro j
    simpa [cSorted] using hNonneg (σ j)
  let gSorted : Finset (Fin n) → ℤ := fun S ↦ f0 (relabelFinset σ S)
  have hgSorted_sub : Submodular gSorted := by
    -- Apply the sorting permutation to the normalized set function once.
    simpa [gSorted] using submodular_relabelFinset_int σ.symm f0 hf0_sub
  have hgSorted_empty : gSorted ∅ = 0 := by
    -- The normalized empty set stays empty under the sorting permutation.
    simp [gSorted, f0]
  rcases submodularGreedySolution_optimal gSorted cSorted hgSorted_sub hgSorted_empty
      hSorted hSorted_nonneg with ⟨hxGreedySorted_mem, hxGreedySorted_opt⟩
  let rowToSorted : Finset α ≃ Finset (Fin n) :=
    { toFun := fun S ↦ relabelFinset σ.symm (relabelFinset e S)
      invFun := fun T ↦ relabelFinset e.symm (relabelFinset σ T)
      left_inv := by
        intro S
        ext a
        simp [e]
      right_inv := by
        intro T
        ext j
        simp [e] }
  let yRow : Fin (Fintype.card (Finset α)) → ℝ := fun i ↦
    sortedPrefixDualVector cSorted (rowToSorted ((Fintype.equivFin (Finset α)).symm i))
  have hyRow_feasible :
      yRow ∈ rational_dual_feasible_region (submodularSystemMatrix α) c := by
    refine (mem_rational_dual_feasible_region_iff).2 ?_
    refine ⟨?_, ?_⟩
    · ext j
      let a : α := e.symm j
      -- Evaluate the matrix dual equation as a subset sum and then reindex to the sorted world.
      calc
        (yRow ᵥ* ((submodularSystemMatrix α).map (Rat.castHom ℝ))) j
          = ∑ S : Finset α, if a ∈ S then yRow ((Fintype.equivFin (Finset α)) S) else 0 := by
              simpa [a, e] using submodularSystemMatrix_vecMul_apply α yRow a
        _ = ∑ T : Finset (Fin n),
              if σ.symm j ∈ T then sortedPrefixDualVector cSorted T else 0 := by
              exact Fintype.sum_equiv rowToSorted
                (fun S : Finset α ↦
                  if a ∈ S then yRow ((Fintype.equivFin (Finset α)) S) else 0)
                (fun T : Finset (Fin n) ↦
                  if σ.symm j ∈ T then sortedPrefixDualVector cSorted T else 0)
                (fun S ↦ by
                  have ha :
                      a ∈ S ↔ σ.symm j ∈ rowToSorted S := by
                    simp [rowToSorted, a, e]
                  by_cases hS : a ∈ S
                  · simp [yRow, rowToSorted, a, e, hS, ha.mp hS]
                  · simp [yRow, rowToSorted, a, e, hS, ha.not.mp hS])
        _ = (cSorted (σ.symm j) : ℝ) := sortedPrefixDualVector_coordinate cSorted (σ.symm j)
        _ = (c j : ℝ) := by
              simp [cSorted]
    · intro i
      -- The transported prefix-gap weights stay nonnegative rowwise.
      simpa [yRow] using
        sortedPrefixDualVector_nonneg cSorted hSorted hSorted_nonneg
          (rowToSorted ((Fintype.equivFin (Finset α)).symm i))
  have hyRow_integer :
      yRow ∈ integerVectors (Fintype.card (Finset α)) := by
    rw [mem_integerVectors_iff_forall]
    intro i
    -- Each row weight is one of the integral prefix gaps or zero.
    simpa [yRow] using
      sortedPrefixDualVector_integer cSorted
        (rowToSorted ((Fintype.equivFin (Finset α)).symm i))
  have hyRow_value :
      yRow ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) =
        ∑ j : Fin n, (cSorted j : ℝ) * submodularGreedySolution gSorted j := by
    -- Reindex the subset-row objective to the sorted `Fin` subsets, then invoke the Abel identity.
    calc
      yRow ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ))
        = ∑ S : Finset α, yRow ((Fintype.equivFin (Finset α)) S) * (f S : ℝ) := by
            simpa [yRow] using submodular_dual_objective_reindex α f yRow
      _ = ∑ T : Finset (Fin n),
            sortedPrefixDualVector cSorted T * (f (rowToSorted.symm T) : ℝ) := by
            exact Fintype.sum_equiv rowToSorted
              (fun S : Finset α ↦ yRow ((Fintype.equivFin (Finset α)) S) * (f S : ℝ))
              (fun T : Finset (Fin n) ↦
                sortedPrefixDualVector cSorted T * (f (rowToSorted.symm T) : ℝ))
              (fun S ↦ by simp [yRow])
      _ = ∑ T : Finset (Fin n), sortedPrefixDualVector cSorted T * (gSorted T : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro T hT
            by_cases hEmptyT : T = ∅
            · subst hEmptyT
              simp [sortedPrefixDualVector_empty, hgSorted_empty]
            · have hRow :
                rowToSorted.symm T = relabelFinset e.symm (relabelFinset σ T) := by
                  rfl
              have hSortedNonempty : relabelFinset σ T ≠ ∅ := by
                intro hZero
                apply hEmptyT
                have hBack := congrArg (relabelFinset σ.symm) hZero
                simpa using hBack
              rw [hRow]
              change sortedPrefixDualVector cSorted T *
                  (fFin (relabelFinset σ T) : ℝ) =
                sortedPrefixDualVector cSorted T * (gSorted T : ℝ)
              have hgValue : (gSorted T : ℝ) = (fFin (relabelFinset σ T) : ℝ) := by
                simp [gSorted, f0, normalizeEmptyInt, hSortedNonempty]
              rw [hgValue]
      _ = ∑ j : Fin n, (cSorted j : ℝ) * submodularGreedySolution gSorted j := by
            exact sortedPrefixDualObjective_eq_greedyObjective gSorted cSorted hgSorted_empty
  let xSorted : Fin n → ℝ := fun j ↦ xStar (σ j)
  have hxSorted_mem :
      xSorted ∈ submodularPolyhedron (fun S ↦ (gSorted S : ℝ)) := by
    rw [mem_submodularPolyhedron_iff]
    intro S
    have hsum :
        Finset.sum (relabelFinset σ S) xStar = Finset.sum S xSorted := by
      simpa [xSorted, Function.comp] using sum_relabelFinset σ xStar S
    -- Sorting the coordinates once transports feasibility to the greedy world.
    calc
      Finset.sum S xSorted = Finset.sum (relabelFinset σ S) xStar := hsum.symm
      _ ≤ (f0 (relabelFinset σ S) : ℝ) := hxFin0_mem (relabelFinset σ S)
      _ = (gSorted S : ℝ) := rfl
  let xGreedyFin : Fin n → ℝ := fun j ↦ submodularGreedySolution gSorted (σ.symm j)
  have hxGreedyFin0_mem :
      xGreedyFin ∈ submodularPolyhedron (fun S ↦ (f0 S : ℝ)) := by
    rw [mem_submodularPolyhedron_iff]
    intro S
    have hsum :
        Finset.sum (relabelFinset σ.symm S) (submodularGreedySolution gSorted) =
          Finset.sum S xGreedyFin := by
      simpa [xGreedyFin, Function.comp] using
        sum_relabelFinset σ.symm (submodularGreedySolution gSorted) S
    -- Undo the sorting permutation once to return to the unsorted normalized system.
    calc
      Finset.sum S xGreedyFin =
          Finset.sum (relabelFinset σ.symm S) (submodularGreedySolution gSorted) := hsum.symm
      _ ≤ (gSorted (relabelFinset σ.symm S) : ℝ) :=
          hxGreedySorted_mem (relabelFinset σ.symm S)
      _ = (f0 S : ℝ) := by
            simpa [gSorted] using congrArg f0 (relabelFinset_relabelFinset σ.symm S)
  let xGreedyOrig : α → ℝ := LinearEquiv.funCongrLeft ℝ ℝ e xGreedyFin
  have hxGreedyOrig_f0 :
      xGreedyOrig ∈ submodularPolyhedron
        (fun S ↦ (normalizeEmptyInt f S : ℝ)) := by
    rw [mem_submodularPolyhedron_iff]
    intro S
    have hsum :
        Finset.sum (relabelFinset e S) xGreedyFin = Finset.sum S xGreedyOrig := by
      simpa [xGreedyOrig, e] using sum_relabelFinset e xGreedyFin S
    -- Undo the original ground-set reindexing to return from `Fin` to `α`.
    calc
      Finset.sum S xGreedyOrig = Finset.sum (relabelFinset e S) xGreedyFin := hsum.symm
      _ ≤ (f0 (relabelFinset e S) : ℝ) := hxGreedyFin0_mem (relabelFinset e S)
      _ = (normalizeEmptyInt f S : ℝ) := by
            by_cases hS : S = ∅
            · subst hS
              simp [f0, fFin, e]
            · have hRelabelNonempty : relabelFinset e S ≠ ∅ := by
                intro hZero
                apply hS
                have hBack := congrArg (relabelFinset e.symm) hZero
                simpa [e] using hBack
              have hFinEval : submodularFinFunction α f (relabelFinset e S) = f S := by
                simp [submodularFinFunction, e]
              have hfFinEval : fFin (relabelFinset e S) = f S := by
                simpa [fFin] using hFinEval
              have hf0Eval : (f0 (relabelFinset e S) : ℝ) = (f S : ℝ) := by
                simp [f0, normalizeEmptyInt, hRelabelNonempty, hfFinEval]
              simpa [normalizeEmptyInt, hS] using hf0Eval
  have hxGreedyOrig_mem :
      xGreedyOrig ∈ submodularPolyhedron (fun S ↦ (f S : ℝ)) := by
    exact (mem_submodularPolyhedron_normalizeEmptyInt_iff
      (α := α) f hEmptyNonneg).1 hxGreedyOrig_f0
  have hxGreedyFin_mem :
      xGreedyFin ∈ rational_matrix_polyhedron (submodularSystemMatrix α) (submodularSystemRhs α f) := by
    -- The unsorted greedy point is feasible for the original matrix presentation.
    have hxGreedyImage :
        xGreedyOrig ∈
          LinearEquiv.funCongrLeft ℝ ℝ e ''
            rational_matrix_polyhedron (submodularSystemMatrix α) (submodularSystemRhs α f) := by
      simpa [submodularPolyhedron_eq_reindexed_rational_matrix_polyhedron α f, xGreedyOrig, e] using
        hxGreedyOrig_mem
    rcases hxGreedyImage with ⟨y, hy, hyEq⟩
    have hyx : y = xGreedyFin := by
      apply (LinearEquiv.funCongrLeft ℝ ℝ e).injective
      simpa [xGreedyOrig] using hyEq
    simpa [hyx] using hy
  have hxStar_value :
      (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar =
        ∑ j : Fin n, (cSorted j : ℝ) * xSorted j := by
    -- Reindex the primal objective into sorted coordinates once.
    calc
      (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar = ∑ j : Fin n, (c j : ℝ) * xStar j := by
        simpa [n, dotProduct]
      _ = ∑ j : Fin n, (c (σ j) : ℝ) * xStar (σ j) := by
            symm
            simpa using
              (Equiv.sum_comp (e := σ) (g := fun j : Fin n ↦ (c j : ℝ) * xStar j))
      _ = ∑ j : Fin n, (cSorted j : ℝ) * xSorted j := by
            simp [cSorted, xSorted]
  have hxGreedyFin_value :
      (fun j ↦ (c j : ℝ)) ⬝ᵥ xGreedyFin =
        ∑ j : Fin n, (cSorted j : ℝ) * submodularGreedySolution gSorted j := by
    -- The same reindexing identifies the unsorted greedy point with its sorted coordinates.
    calc
      (fun j ↦ (c j : ℝ)) ⬝ᵥ xGreedyFin = ∑ j : Fin n, (c j : ℝ) * xGreedyFin j := by
        simpa [n, dotProduct]
      _ = ∑ j : Fin n, (c (σ j) : ℝ) * xGreedyFin (σ j) := by
            symm
            simpa using
              (Equiv.sum_comp (e := σ) (g := fun j : Fin n ↦ (c j : ℝ) * xGreedyFin j))
      _ = ∑ j : Fin n, (cSorted j : ℝ) * submodularGreedySolution gSorted j := by
            simp [cSorted, xGreedyFin]
  have hxStar_le_yRow :
      (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar ≤
        yRow ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) := by
    -- Greedy optimality in sorted coordinates bounds the primal optimum by the dual candidate.
    calc
      (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar
        = ∑ j : Fin n, (cSorted j : ℝ) * xSorted j := hxStar_value
      _ ≤ ∑ j : Fin n, (cSorted j : ℝ) * submodularGreedySolution gSorted j :=
          hxGreedySorted_opt xSorted hxSorted_mem
      _ = yRow ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) := hyRow_value.symm
  have hyRow_le_xStar :
      yRow ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) ≤
        (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar := by
    -- Maximality of `xStar` bounds the greedy primal point from above in the original matrix LP.
    calc
      yRow ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ))
        = (fun j ↦ (c j : ℝ)) ⬝ᵥ xGreedyFin := by rw [hxGreedyFin_value, hyRow_value]
      _ ≤ (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar := hxGreatest.2 ⟨xGreedyFin, hxGreedyFin_mem, rfl⟩
  have hyRow_eq_primal :
      yRow ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) =
        (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar := by
    exact le_antisymm hyRow_le_xStar hxStar_le_yRow
  refine ⟨yRow, hyRow_feasible, hyRow_integer, ?_⟩
  refine ⟨⟨yRow, hyRow_feasible, rfl⟩, ?_⟩
  intro r hr
  rcases hr with ⟨y, hy, rfl⟩
  rcases (mem_rational_dual_feasible_region_iff.mp hy) with ⟨hyEq, hyNonneg⟩
  have hxStar_feasible :
      ((submodularSystemMatrix α).map (Rat.castHom ℝ)) *ᵥ xStar ≤
        fun i ↦ (submodularSystemRhs α f i : ℝ) := by
    simpa [rational_matrix_polyhedron] using hxStar
  have hxStar_le_y :
      (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar ≤
        y ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) := by
    -- A direct weak-duality calculation gives the lower bound for every feasible dual point.
    calc
      (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar
        = (y ᵥ* ((submodularSystemMatrix α).map (Rat.castHom ℝ))) ⬝ᵥ xStar := by
            rw [hyEq]
      _ = y ⬝ᵥ ((((submodularSystemMatrix α).map (Rat.castHom ℝ)) *ᵥ xStar)) := by
            rw [Matrix.dotProduct_mulVec]
      _ ≤ y ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) := by
            exact dotProduct_le_dotProduct_of_nonneg_left hxStar_feasible hyNonneg
  calc
    yRow ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ))
      = (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar := hyRow_eq_primal
    _ ≤ y ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) := hxStar_le_y

end TdiMatrixProof

end IntegralBridge

section TDITheorem

variable (α : Type) [Fintype α] [DecidableEq α]

/-- Source-facing consequence of Theorem 4.29 (2): every integral objective with a finite maximum
on the subset-inequality system `∑ j in S, x j ≤ f S` has an integral optimal dual solution. -/
theorem submodular_system_tdi
    (f : Finset α → ℤ)
    (h_submodular : Submodular f) :
    ∀ c : α → ℤ,
      (∃ xStar ∈ submodularPolyhedron (fun S ↦ (f S : ℝ)),
        IsGreatest
          ((fun x : α → ℝ ↦ ∑ j, (c j : ℝ) * x j) ''
            submodularPolyhedron (fun S ↦ (f S : ℝ)))
          (∑ j, (c j : ℝ) * xStar j)) →
      ∃ yStar : Finset α → ℝ,
        (∀ j, (∑ S, if j ∈ S then yStar S else 0) = (c j : ℝ)) ∧
        0 ≤ yStar ∧
        yStar ∈ Set.range (fun z : Finset α → ℤ ↦ Int.cast ∘ z) ∧
        IsLeast
          ((fun y : Finset α → ℝ ↦ ∑ S, y S * (f S : ℝ)) ''
            {y | (∀ j, (∑ S, if j ∈ S then y S else 0) = (c j : ℝ)) ∧ 0 ≤ y})
          (∑ S, yStar S * (f S : ℝ)) := by
  classical
  intro c hOpt
  let cFin : Fin (Fintype.card α) → ℤ := fun j ↦ c ((Fintype.equivFin α).symm j)
  have hTDI :
      totally_dual_integral (submodularSystemMatrix α) (submodularSystemRhs α f) :=
    submodular_system_tdi_matrix α f h_submodular
  rcases hOpt with ⟨xStar, hxStar, hxGreatest⟩
  let xFin : Fin (Fintype.card α) → ℝ :=
    (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α)).symm xStar
  have hxFin_mem :
      xFin ∈ rational_matrix_polyhedron (submodularSystemMatrix α) (submodularSystemRhs α f) := by
    -- The feasible point is transported through the reindexed polyhedron equivalence.
    have hxImage :
        xStar ∈
          LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α) ''
            rational_matrix_polyhedron (submodularSystemMatrix α) (submodularSystemRhs α f) := by
      simpa [submodularPolyhedron_eq_reindexed_rational_matrix_polyhedron α f] using hxStar
    rcases hxImage with ⟨y, hy, hyEq⟩
    have hyx : y = xFin := by
      apply (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α)).injective
      calc
        LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α) y = xStar := hyEq
        _ = LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α) xFin := by
              simpa [xFin] using
                (LinearEquiv.apply_symm_apply
                  (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α)) xStar).symm
    simpa [hyx] using hy
  have hxFin_value :
      (fun j ↦ (cFin j : ℝ)) ⬝ᵥ xFin = ∑ j, (c j : ℝ) * xStar j := by
    -- The objective is unchanged by the coordinate reindexing.
    simpa [cFin, xFin] using submodular_primal_objective_reindex α c xFin
  have hPrimalFinite :
      rational_primal_has_finite_optimum
        (submodularSystemMatrix α) (submodularSystemRhs α f) cFin := by
    rw [rational_primal_has_finite_optimum_iff]
    refine ⟨xFin, hxFin_mem, ?_⟩
    refine ⟨?_, ?_⟩
    · exact ⟨xFin, hxFin_mem, rfl⟩
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      let xSrc : α → ℝ := LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α) x
      have hxSrc :
          xSrc ∈ submodularPolyhedron (fun S ↦ (f S : ℝ)) := by
        have hxImage :
            xSrc ∈
              LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α) ''
                rational_matrix_polyhedron (submodularSystemMatrix α) (submodularSystemRhs α f) :=
          ⟨x, hx, rfl⟩
        simpa [submodularPolyhedron_eq_reindexed_rational_matrix_polyhedron α f, xSrc] using hxImage
      have hx_value :
          (fun j ↦ (cFin j : ℝ)) ⬝ᵥ x = ∑ j, (c j : ℝ) * xSrc j := by
        -- Every feasible `Fin`-indexed point has the same objective after reindexing.
        simpa [cFin, xSrc] using submodular_primal_objective_reindex α c x
      have hUpper :
          (∑ j, (c j : ℝ) * xSrc j) ≤ ∑ j, (c j : ℝ) * xStar j :=
        hxGreatest.right ⟨xSrc, hxSrc, rfl⟩
      simpa [hx_value, hxFin_value] using hUpper
  have hDual :
      rational_dual_has_integral_optimal_solution
        (submodularSystemMatrix α) (submodularSystemRhs α f) cFin :=
    hTDI cFin hPrimalFinite
  rw [rational_dual_has_integral_optimal_solution_iff] at hDual
  rcases hDual with ⟨yFin, hyFin, hyInt, hyLeast⟩
  rw [mem_rational_dual_feasible_region_iff] at hyFin
  rcases hyFin with ⟨hyEq, hyNonneg⟩
  let yStar : Finset α → ℝ := fun S ↦ yFin ((Fintype.equivFin (Finset α)) S)
  have hyStar_eq : ∀ j, (∑ S, if j ∈ S then yStar S else 0) = (c j : ℝ) := by
    intro j
    -- Evaluate the matrix dual equality in the column corresponding to `j`.
    have hcoord := congrArg (fun v ↦ v ((Fintype.equivFin α) j)) hyEq
    calc
      ∑ S : Finset α, (if j ∈ S then yStar S else (0 : ℝ))
        = (yFin ᵥ* ((submodularSystemMatrix α).map (Rat.castHom ℝ))) ((Fintype.equivFin α) j) := by
            symm
            simpa [yStar] using submodularSystemMatrix_vecMul_apply α yFin j
      _ = (cFin ((Fintype.equivFin α) j) : ℝ) := hcoord
      _ = (c j : ℝ) := by
            simp [cFin]
  have hyStar_nonneg : 0 ≤ yStar := by
    -- Nonnegativity is preserved by the row reindexing.
    intro S
    exact hyNonneg ((Fintype.equivFin (Finset α)) S)
  have hyStar_integer :
      yStar ∈ Set.range (fun z : Finset α → ℤ ↦ Int.cast ∘ z) := by
    -- Pull back the integral `Fin`-indexed witness to an integral subset-indexed function.
    rcases (mem_integerVectors_iff.mp hyInt) with ⟨zFin, hzFin⟩
    refine ⟨zFin ∘ (Fintype.equivFin (Finset α)), ?_⟩
    funext S
    simp [yStar, hzFin]
  have hyStar_value :
      yFin ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) =
        ∑ S, yStar S * (f S : ℝ) := by
    -- The dual objective is also unchanged by the row reindexing.
    simpa [yStar] using submodular_dual_objective_reindex α f yFin
  refine ⟨yStar, hyStar_eq, hyStar_nonneg, hyStar_integer, ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨yStar, ⟨hyStar_eq, hyStar_nonneg⟩, rfl⟩
  · intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    let yFin' : Fin (Fintype.card (Finset α)) → ℝ :=
      fun i ↦ y ((Fintype.equivFin (Finset α)).symm i)
    have hyFin'_feasible :
        yFin' ∈ rational_dual_feasible_region (submodularSystemMatrix α) cFin := by
      rw [mem_rational_dual_feasible_region_iff]
      refine ⟨?_, ?_⟩
      · ext j
        -- The subset-indexed equalities become the Chapter 4.6 matrix equalities after reindexing.
        calc
          (yFin' ᵥ* ((submodularSystemMatrix α).map (Rat.castHom ℝ))) j
            = ∑ S : Finset α,
                if (Fintype.equivFin α).symm j ∈ S then yFin' ((Fintype.equivFin (Finset α)) S)
                  else 0 := by
                simpa using
                  submodularSystemMatrix_vecMul_apply α yFin' ((Fintype.equivFin α).symm j)
          _ = ∑ S : Finset α, if (Fintype.equivFin α).symm j ∈ S then y S else 0 := by
                simp [yFin']
          _ = (c ((Fintype.equivFin α).symm j) : ℝ) := hy.1 ((Fintype.equivFin α).symm j)
          _ = (cFin j : ℝ) := by
                simp [cFin]
      · intro i
        simpa [yFin'] using hy.2 ((Fintype.equivFin (Finset α)).symm i)
    have hyFin'_value :
        yFin' ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) = ∑ S, y S * (f S : ℝ) := by
      -- The reindexed subset-indexed candidate has the same dual objective value.
      simpa [yFin'] using submodular_dual_objective_reindex α f yFin'
    have hLower :
        yFin ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) ≤
          yFin' ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) :=
      hyLeast.right ⟨yFin', hyFin'_feasible, rfl⟩
    calc
      ∑ S, yStar S * (f S : ℝ)
        = yFin ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) := hyStar_value.symm
      _ ≤ yFin' ⬝ᵥ (fun i ↦ (submodularSystemRhs α f i : ℝ)) := hLower
      _ = ∑ S, y S * (f S : ℝ) := hyFin'_value

end TDITheorem

section IntegralTheorem

variable (α : Type) [Finite α] [DecidableEq α]

/-- Integrality consequence of Theorem 4.29 (1): the submodular polyhedron defined by the
inequalities `∑ j in S, x j ≤ f S` is integral. -/
theorem submodular_polyhedron_integral
    (f : Finset α → ℤ)
    (h_submodular : Submodular f) :
    is_integral (submodularPolyhedron (fun S ↦ (f S : ℝ))) := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  have hTDI :
      totally_dual_integral (submodularSystemMatrix α) (submodularSystemRhs α f) :=
    submodular_system_tdi_matrix α f h_submodular
  let b : Fin (Fintype.card (Finset α)) → ℤ :=
    fun i ↦ f ((Fintype.equivFin (Finset α)).symm i)
  have hIntegral :
      is_integral
        (rational_matrix_polyhedron (submodularSystemMatrix α) (Int.cast ∘ b)) :=
    totally_dual_integral_rational_matrix_polyhedron_is_integral
      (submodularSystemMatrix α) b (by
        simpa [b, submodularSystemRhs] using hTDI)
  have hReindexed :
      is_integral
        ((LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin α)) ''
          rational_matrix_polyhedron (submodularSystemMatrix α) (submodularSystemRhs α f)) :=
    by
      simpa using
        (is_integral_funCongrLeft_symm_image (Fin (Fintype.card α))
          (Fintype.equivFin α).symm
          (by simpa [b, submodularSystemRhs] using hIntegral))
  simpa [submodularPolyhedron_eq_reindexed_rational_matrix_polyhedron α f]
    using hReindexed

end IntegralTheorem

end Theorem429
