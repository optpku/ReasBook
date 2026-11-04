/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_1_proposition_2_5.SetPacking

public section

namespace Matrix

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_1_proposition_2_5.lean`: a binary
sum is at most one when no two distinct summands are simultaneously nonzero. -/
private lemma sum_le_one_of_binary_of_pairwise_zero
    {α : Type*} (s : Finset α) (x : α → ℤ)
    (hbin : ∀ a, x a = 0 ∨ x a = 1)
    (hpair : ∀ ⦃u v⦄, u ∈ s → v ∈ s → u ≠ v → x u = 0 ∨ x v = 0) :
    s.sum x ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      -- Separate the new binary coordinate from the previously controlled sum.
      rcases hbin a with haZero | haOne
      · rw [Finset.sum_insert ha, haZero, zero_add]
        apply ih
        intro u v hu hv huv
        exact hpair (Finset.mem_insert_of_mem hu) (Finset.mem_insert_of_mem hv) huv
      · have hsZero : ∀ b ∈ s, x b = 0 := by
          -- Pair the new one-valued coordinate with each old coordinate.
          intro b hb
          have hab : a ≠ b := by
            -- Distinctness follows because `a` was freshly inserted.
            intro hab
            subst b
            exact ha hb
          rcases hpair (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb) hab with
            haZero | hbZero
          · omega
          · exact hbZero
        -- If the new coordinate is one, pairwise exclusion makes every old coordinate zero.
        have hsumZero : s.sum x = 0 := Finset.sum_eq_zero hsZero
        rw [Finset.sum_insert ha, haOne, hsumZero]
        norm_num

/--
remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_1_proposition_2_5.lean

Proposition 2.5. For a `0/1` matrix `A`, the set packing family `S^P(A)` is exactly the
stable-set family `stab(Matrix.intersectionGraph A)`. -/
theorem setPackingFamily_eq_stableSetFamily
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) :
    A.setPackingFamily = (Matrix.intersectionGraph A).stableSetFamily := by
  -- Route correction: the supplied closure plan did not match this matrix-family target.
  ext x
  constructor
  · intro hx
    rw [SetFamilyOptimization.mem_packingFeasibleSet_iff] at hx
    rw [SimpleGraph.mem_stableSetFamily_iff]
    rcases hx with ⟨hbin, hrows⟩
    refine ⟨hbin, ?_⟩
    rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv huv hAdj
    have huOne : x u = 1 := (hbin u).resolve_left hu
    have hvOne : x v = 1 := (hbin v).resolve_left hv
    rcases (intersectionGraph_adj_iff A).mp hAdj with ⟨_, i, hiu, hiv⟩
    have huRow : u ∈ A.rowSupportFamily i := mem_rowSupportFamily_iff.mpr hiu
    have hvRow : v ∈ A.rowSupportFamily i := mem_rowSupportFamily_iff.mpr hiv
    have hPairSubset : {u, v} ⊆ A.rowSupportFamily i := by
      -- Both endpoints belong to the support of their common row.
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hwu | hwv
      · rwa [hwu]
      · rwa [hwv]
    have hNonnegative :
        ∀ w ∈ A.rowSupportFamily i, w ∉ ({u, v} : Finset (Fin n)) → 0 ≤ x w := by
      -- Every binary coordinate is nonnegative.
      intro w _ _
      rcases hbin w with hwZero | hwOne
      · omega
      · omega
    -- The two selected columns force a contribution of two in their common row.
    have hPairLeRow : ({u, v} : Finset (Fin n)).sum x ≤ (A.rowSupportFamily i).sum x :=
      Finset.sum_le_sum_of_subset_of_nonneg hPairSubset hNonnegative
    have hRowBound := hrows i
    simp [huv, huOne, hvOne] at hPairLeRow
    omega
  · intro hx
    rw [SimpleGraph.mem_stableSetFamily_iff] at hx
    rw [SetFamilyOptimization.mem_packingFeasibleSet_iff]
    rcases hx with ⟨hbin, hIndep⟩
    refine ⟨hbin, ?_⟩
    intro i
    apply sum_le_one_of_binary_of_pairwise_zero (A.rowSupportFamily i) x hbin
    intro u v hu hv huv
    rcases hbin u with huZero | huOne
    · exact Or.inl huZero
    rcases hbin v with hvZero | hvOne
    · exact Or.inr hvZero
    · have huSupport : u ∈ Function.support x :=
        Function.mem_support.mpr (huOne.trans_ne one_ne_zero)
      have hvSupport : v ∈ Function.support x :=
        Function.mem_support.mpr (hvOne.trans_ne one_ne_zero)
      have hiu : A i u = true := mem_rowSupportFamily_iff.mp hu
      have hiv : A i v = true := mem_rowSupportFamily_iff.mp hv
      have hAdj : (intersectionGraph A).Adj u v :=
        (intersectionGraph_adj_iff A).mpr ⟨huv, i, hiu, hiv⟩
      -- Independence contradicts the edge supplied by the common matrix row.
      exact (hIndep huSupport hvSupport huv hAdj).elim

end Matrix

#print axioms Matrix.setPackingFamily_eq_stableSetFamily
