module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_1_definition_2_12.IntersectionGraph
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_definition_2_9.Optimization
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Combinatorics.SimpleGraph.Clique

open scoped BigOperators

public section

namespace Matrix

section SetPacking

variable {m n : ℕ}

/-- The family of row supports of a `0/1` matrix `A`, indexed by its rows. -/
def rowSupportFamily (A : Matrix (Fin m) (Fin n) Bool) : Fin m → Finset (Fin n) :=
  fun i ↦ Finset.univ.filter fun j ↦ A i j = true

/-- A column lies in `rowSupportFamily A i` exactly when row `i` contains `true` in that column. -/
theorem mem_rowSupportFamily_iff
    {A : Matrix (Fin m) (Fin n) Bool} {i : Fin m} {j : Fin n} :
    j ∈ A.rowSupportFamily i ↔ A i j = true := by
  simp [rowSupportFamily]

/-- The source-facing set packing family `S^P(A)` attached to a `0/1` matrix `A`. -/
abbrev setPackingFamily (A : Matrix (Fin m) (Fin n) Bool) : Set (Fin n → ℤ) :=
  SetFamilyOptimization.packingFeasibleSet A.rowSupportFamily

/-- Membership in `S^P(A)` is exactly the binary condition together with the row-support packing
inequalities `∑ j in rowSupportFamily A i, x j ≤ 1`. -/
theorem mem_setPackingFamily_iff
    {A : Matrix (Fin m) (Fin n) Bool} {x : Fin n → ℤ} :
    x ∈ A.setPackingFamily ↔
      (∀ j, x j = 0 ∨ x j = 1) ∧
        ∀ i, (A.rowSupportFamily i).sum x ≤ 1 := by
  exact SetFamilyOptimization.mem_packingFeasibleSet_iff

end SetPacking

end Matrix

namespace SimpleGraph

section StableSetFamily

variable {V : Type*}

/-- The source-facing family `stab(G)` of binary integer vectors whose support is a stable set
of `G`. -/
def stableSetFamily (G : SimpleGraph V) : Set (V → ℤ) :=
  {x | (∀ v, x v = 0 ∨ x v = 1) ∧ G.IsIndepSet (Function.support x)}

/-- Membership in `stab(G)` is exactly the binary condition together with support independence. -/
theorem mem_stableSetFamily_iff
    {G : SimpleGraph V} {x : V → ℤ} :
    x ∈ G.stableSetFamily ↔
      (∀ v, x v = 0 ∨ x v = 1) ∧ G.IsIndepSet (Function.support x) := Iff.rfl

end StableSetFamily

end SimpleGraph

namespace Matrix

section SetPacking

variable {m n : ℕ}

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_1_proposition_2_5/SetPacking.lean:
a binary integer-valued function sums to the cardinality of its one-valued coordinates on any
finite set. -/
lemma binarySum_eq_cardFilterEqOne
    {α : Type*} [DecidableEq α] (s : Finset α) (x : α → ℤ)
    (hx01 : ∀ a, x a = 0 ∨ x a = 1) :
    s.sum x = ((s.filter fun a ↦ x a = 1).card : ℤ) := by
  -- Replace each binary summand by the indicator of the equation `x a = 1`.
  calc
    s.sum x = ∑ a ∈ s, if x a = 1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rcases hx01 a with hzero | hone
      · simp [hzero]
      · simp [hone]
    _ = ((s.filter fun a ↦ x a = 1).card : ℤ) := by
      simp

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_1_proposition_2_5/SetPacking.lean:
Membership in `S^P(A)` is equivalent to membership in the stable-set family of
`Matrix.intersectionGraph A`. -/
theorem mem_setPackingFamily_iff_mem_stableSetFamily
    {A : Matrix (Fin m) (Fin n) Bool} {x : Fin n → ℤ} :
    x ∈ A.setPackingFamily ↔ x ∈ (Matrix.intersectionGraph A).stableSetFamily := by
  rw [mem_setPackingFamily_iff, SimpleGraph.mem_stableSetFamily_iff]
  constructor
  · rintro ⟨hbin, hrows⟩
    refine ⟨hbin, ?_⟩
    rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv huv hAdj
    have huOne : x u = 1 := (hbin u).resolve_left hu
    have hvOne : x v = 1 := (hbin v).resolve_left hv
    rcases (intersectionGraph_adj_iff A).mp hAdj with ⟨_, i, hiu, hiv⟩
    have huRow : u ∈ A.rowSupportFamily i := mem_rowSupportFamily_iff.mpr hiu
    have hvRow : v ∈ A.rowSupportFamily i := mem_rowSupportFamily_iff.mpr hiv
    have hPairSubset : {u, v} ⊆ A.rowSupportFamily i := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hwu | hwv
      · rwa [hwu]
      · rwa [hwv]
    have hNonnegative :
        ∀ w ∈ A.rowSupportFamily i, w ∉ ({u, v} : Finset (Fin n)) → 0 ≤ x w := by
      intro w _ _
      rcases hbin w with hwZero | hwOne
      · omega
      · omega
    -- The adjacent support coordinates contribute two in their common row.
    have hPairLeRow : ({u, v} : Finset (Fin n)).sum x ≤ (A.rowSupportFamily i).sum x :=
      Finset.sum_le_sum_of_subset_of_nonneg hPairSubset hNonnegative
    have hRowBound := hrows i
    simp [huv, huOne, hvOne] at hPairLeRow
    omega
  · rintro ⟨hbin, hIndep⟩
    refine ⟨hbin, ?_⟩
    intro i
    have hcard :
        (A.rowSupportFamily i |>.filter fun j ↦ x j = 1).card ≤ 1 := by
      refine Finset.card_le_one_iff.mpr ?_
      intro u v hu hv
      rcases Finset.mem_filter.mp hu with ⟨huRow, huOne⟩
      rcases Finset.mem_filter.mp hv with ⟨hvRow, hvOne⟩
      by_contra huv
      have huSupport : u ∈ Function.support x :=
        Function.mem_support.mpr (huOne.trans_ne one_ne_zero)
      have hvSupport : v ∈ Function.support x :=
        Function.mem_support.mpr (hvOne.trans_ne one_ne_zero)
      have hiu : A i u = true := mem_rowSupportFamily_iff.mp huRow
      have hiv : A i v = true := mem_rowSupportFamily_iff.mp hvRow
      have hAdj : (intersectionGraph A).Adj u v :=
        (intersectionGraph_adj_iff A).mpr ⟨huv, i, hiu, hiv⟩
      -- Independence rules out two active columns in the same matrix row.
      exact (hIndep huSupport hvSupport huv hAdj).elim
    rw [binarySum_eq_cardFilterEqOne (A.rowSupportFamily i) x hbin]
    exact_mod_cast hcard

end SetPacking

end Matrix

#print axioms Matrix.mem_setPackingFamily_iff_mem_stableSetFamily
