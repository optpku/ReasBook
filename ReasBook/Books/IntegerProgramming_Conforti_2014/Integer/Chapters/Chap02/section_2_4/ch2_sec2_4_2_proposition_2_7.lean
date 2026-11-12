/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Real.Basic

public section

open scoped BigOperators

universe u

namespace SimpleGraph

/-- Helper for Proposition 2.7: the real cast of the predecessor of a natural number greater
than one is positive. -/
private lemma castPred_pos (n : ℕ) (hn : 1 < n) : (0 : ℝ) < (n - 1 : ℕ) := by
  -- Cast the positive natural predecessor into the ordered field of real weights.
  exact Nat.cast_pos.mpr (Nat.sub_pos_of_lt hn)

/-- Helper for Proposition 2.7: the reciprocal of the predecessor of a natural number greater
than one lies in `[0, 1]`. -/
private lemma oneDivCastPred_mem_Icc (n : ℕ) (hn : 1 < n) :
    1 / ((n - 1 : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Positivity of the natural predecessor supplies the denominator side condition.
  have hpredPosNat : 0 < n - 1 := Nat.sub_pos_of_lt hn
  have hpredPos : (0 : ℝ) < (n - 1 : ℕ) := castPred_pos n hn
  constructor
  · exact (one_div_pos.mpr hpredPos).le
  · rw [div_le_one hpredPos]
    exact_mod_cast hpredPosNat

/-- Helper for Proposition 2.7: a natural number greater than one divided by its predecessor is
strictly greater than one over the reals. -/
private lemma oneLtCastDivCastPred (n : ℕ) (hn : 1 < n) :
    (1 : ℝ) < n / ((n - 1 : ℕ) : ℝ) := by
  -- Positivity of the predecessor reduces the quotient comparison to the natural inequality.
  have hpredPos : (0 : ℝ) < (n - 1 : ℕ) := castPred_pos n hn
  rw [one_lt_div hpredPos]
  exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt hn) Nat.one_pos

/-- Helper for Proposition 2.7: selecting either an admissible weight or zero preserves the unit
interval bounds. -/
private lemma ite_mem_Icc_zero_one (p : Prop) [Decidable p] {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) : (if p then c else 0) ∈ Set.Icc (0 : ℝ) 1 := by
  -- In either branch, the selected value is already known to lie in the unit interval.
  by_cases hp : p
  · simpa only [hp, if_pos] using hc
  · simp only [hp, if_false, Set.mem_Icc, le_refl, zero_le_one, and_self]

open scoped Classical in
/-- Helper for Proposition 2.7: summing a constant on a finite support counts the intersection
with that support. -/
private lemma sumIteMem_eq_card_nsmul {α M : Type*} [AddCommMonoid M]
    (s t : Finset α) (c : M) :
    s.sum (fun a ↦ if a ∈ t then c else 0) = (s ∩ t).card • c := by
  -- Restrict the sum to the supported intersection, where every summand is constant.
  simp only [Finset.sum_ite_mem, Finset.sum_const]

open scoped Classical in
/-- Helper for Proposition 2.7: a maximal clique is not contained in a distinct clique. -/
private lemma notSubsetOfNeMaximalClique {V : Type u} {G : SimpleGraph V}
    {K L : Finset V} (hK : Maximal G.IsClique K) (hL : G.IsClique L)
    (hne : L ≠ K) : ¬ K ⊆ L := by
  -- Any such containment would force equality by maximality, contradicting distinctness.
  intro hKL
  exact hne (Finset.coe_injective (hK.eq_of_le hL hKL).symm)

open scoped Classical in
/-- Helper for Proposition 2.7: a clique distinct from a maximal clique meets it in at most one
fewer vertex. -/
private lemma interCard_le_pred_of_maximalClique {V : Type u} {G : SimpleGraph V}
    {K L : Finset V} (hK : Maximal G.IsClique K) (hL : G.IsClique L)
    (hne : L ≠ K) : (L ∩ K).card ≤ K.card - 1 := by
  classical
  -- Equality of the intersection with `K` would make `K` a subset of `L`.
  have hinterNe : L ∩ K ≠ K := by
    intro hinterEq
    have hKL : K ⊆ L := by
      rw [← hinterEq]
      exact Finset.inter_subset_left
    exact notSubsetOfNeMaximalClique hK hL hne hKL
  -- Thus the intersection is a strict subset, so its cardinal is strictly smaller.
  have hinterStrict : L ∩ K ⊂ K :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, hinterNe⟩
  exact Nat.le_sub_one_of_lt (Finset.card_lt_card hinterStrict)

open scoped Classical in
/-- Helper for Proposition 2.7: the constant weight supported on a maximal clique satisfies every
distinct clique inequality. -/
private lemma cliqueSupportWeightSum_le_one {V : Type u} {G : SimpleGraph V}
    {K L : Finset V} (hK : Maximal G.IsClique K) (hKcard : 1 < K.card)
    (hne : L ≠ K) (hL : G.IsClique L) :
    L.sum (fun v ↦ if v ∈ K then 1 / ((K.card - 1 : ℕ) : ℝ) else 0) ≤ 1 := by
  classical
  -- Normalize the supported sum to the intersection cardinal divided by the denominator.
  have hdenPos : (0 : ℝ) < (K.card - 1 : ℕ) := castPred_pos K.card hKcard
  have hinterCard : ((L ∩ K).card : ℝ) ≤ (K.card - 1 : ℕ) :=
    Nat.cast_le.mpr (interCard_le_pred_of_maximalClique hK hL hne)
  rw [sumIteMem_eq_card_nsmul, nsmul_eq_mul, ← div_eq_mul_one_div,
    div_le_one hdenPos]
  exact hinterCard

open scoped Classical in
/-- Helper for Proposition 2.7: the supported weight sum on its defining clique is strictly
greater than one. -/
private lemma cliqueSupportWeightSum_gt_one {V : Type u} {K : Finset V} (hKcard : 1 < K.card) :
    1 < K.sum (fun v ↦ if v ∈ K then 1 / ((K.card - 1 : ℕ) : ℝ) else 0) := by
  -- The defining clique contributes one copy of the reciprocal predecessor per vertex.
  rw [sumIteMem_eq_card_nsmul, Finset.inter_self, nsmul_eq_mul,
    ← div_eq_mul_one_div]
  exact oneLtCastDivCastPred K.card hKcard

/--
remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_2_proposition_2_7.lean <!-- http -->

Proposition 2.7 (Nonredundancy of maximal clique inequalities). If `K` is a maximal clique of `G`
with `1 < K.card`, then there exists `x : V → ℝ` satisfying the bounds `0 ≤ x v ≤ 1` and every
clique inequality for cliques `K' ≠ K`, while violating the clique inequality of `K`. -/
theorem maximalCliqueNonredundancy {V : Type u} (G : SimpleGraph V) {K : Finset V}
    (hK : Maximal G.IsClique K) (hKcard : 1 < K.card) :
    ∃ x : V → ℝ,
      (∀ v, x v ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ K' : Finset V, K' ≠ K → G.IsClique K' → K'.sum x ≤ 1) ∧
      1 < K.sum x := by
  classical
  -- Give each vertex of `K` the reciprocal predecessor weight and every other vertex zero.
  use fun v ↦ if v ∈ K then 1 / ((K.card - 1 : ℕ) : ℝ) else 0
  constructor
  · intro v
    -- The indicator-form witness stays bounded because both its supported value and zero do.
    exact ite_mem_Icc_zero_one (v ∈ K) (oneDivCastPred_mem_Icc K.card hKcard)
  -- The intersection-cardinality invariant certifies all omitted clique inequalities.
  constructor
  · intro K' hne hK'
    exact cliqueSupportWeightSum_le_one hK hKcard hne hK'
  · exact cliqueSupportWeightSum_gt_one hKcard

end SimpleGraph

end

#print axioms SimpleGraph.maximalCliqueNonredundancy
