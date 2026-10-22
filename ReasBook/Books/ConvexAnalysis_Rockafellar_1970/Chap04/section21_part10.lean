/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part9

section Chap04
section Section21

/-- Helper for Corollary 21.6.2: if a selected mixed subfamily of the Theorem 21.2
constraints is already infeasible on `C`, then Theorem 21.2 yields a dual certificate
supported on that mixed subfamily alone. -/
lemma helperForCorollary_21_6_2_sparse_dual_for_selected_theorem21_2_subfamily
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (hfStrict : ∀ i : Fin k,
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStrict i))
    (hdomStrict :
      ∀ i : Fin k,
        euclideanRelativeInterior_fin n C ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fStrict i))
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hAffine : ∀ j : Fin l, ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, fAffine j = g)
    (hFeasRi :
      ∃ x, x ∈ euclideanRelativeInterior_fin n C ∧
        ∀ j : Fin l, fAffine j x ≤ 0)
    (s : Finset (Fin k ⊕ Fin l))
    (hsCard : s.card ≤ n + 1)
    (hNotPrimal :
      ¬ ∃ x : Fin n → ℝ, x ∈ C ∧
        (∀ i : Fin k, Sum.inl i ∈ s → fStrict i x < (0 : EReal)) ∧
          (∀ j : Fin l, Sum.inr j ∈ s → fAffine j x ≤ 0)) :
    ∃ lamStrict : Fin k → ℝ, ∃ lamAffine : Fin l → ℝ,
      (∀ i : Fin k, 0 ≤ lamStrict i) ∧
        (∀ j : Fin l, 0 ≤ lamAffine j) ∧
          (∃ i : Fin k, lamStrict i ≠ 0) ∧
            Fintype.card {i : Fin k // lamStrict i ≠ 0} +
                Fintype.card {j : Fin l // lamAffine j ≠ 0} ≤
              s.card ∧
              (∀ x, x ∈ C →
                (0 : EReal) ≤
                  (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
                    ∑ j : Fin l,
                      ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) := by
  classical
  -- Route correction: split the mixed selected subsystem into strict and affine subtype
  -- blocks first, then reindex those blocks by `Fin` before zero-extending the coefficients.
  let JStrict : Type := {i : Fin k // Sum.inl i ∈ s}
  let JAffine : Type := {j : Fin l // Sum.inr j ∈ s}
  have eSelected : s ≃ JStrict ⊕ JAffine := by
    refine
      { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
    · intro t
      cases h : t.1 with
      | inl i =>
          exact Sum.inl ⟨i, by simpa [h] using t.2⟩
      | inr j =>
          exact Sum.inr ⟨j, by simpa [h] using t.2⟩
    · intro u
      cases u with
      | inl i => exact ⟨Sum.inl i.1, i.2⟩
      | inr j => exact ⟨Sum.inr j.1, j.2⟩
    · intro t
      cases t with
      | mk t ht =>
          cases t with
          | inl i => rfl
          | inr j => rfl
    · intro u
      cases u with
      | inl i => rfl
      | inr j => rfl
  have hsCardSplit :
      Fintype.card JStrict + Fintype.card JAffine = s.card := by
    -- The selected mixed subtype is exactly the disjoint sum of the left and right blocks.
    calc
      Fintype.card JStrict + Fintype.card JAffine = Fintype.card (JStrict ⊕ JAffine) := by
        symm
        exact Fintype.card_sum
      _ = Fintype.card s := by
        symm
        exact Fintype.card_congr eSelected
      _ = s.card := by
        exact Fintype.card_coe s
  let p : ℕ := Fintype.card JStrict
  let q : ℕ := Fintype.card JAffine
  let eStrict : JStrict ≃ Fin p := Fintype.equivFin JStrict
  let eAffine : JAffine ≃ Fin q := Fintype.equivFin JAffine
  let gStrict : Fin p → (Fin n → ℝ) → EReal := fun i => fStrict (eStrict.symm i).1
  let gAffine : Fin q → (Fin n → ℝ) → ℝ := fun j => fAffine (eAffine.symm j).1
  have hgStrict :
      ∀ i : Fin p,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (gStrict i) := by
    intro i
    exact hfStrict (eStrict.symm i).1
  have hdom_gStrict :
      ∀ i : Fin p,
        euclideanRelativeInterior_fin n C ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (gStrict i) := by
    intro i
    simpa [gStrict] using hdomStrict (eStrict.symm i).1
  have hgAffine :
      ∀ j : Fin q, ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, gAffine j = g := by
    intro j
    rcases hAffine (eAffine.symm j).1 with ⟨g, hg⟩
    exact ⟨g, by simpa [gAffine] using hg⟩
  have hFeasRiSelected :
      ∃ x, x ∈ euclideanRelativeInterior_fin n C ∧
        ∀ j : Fin q, gAffine j x ≤ 0 := by
    rcases hFeasRi with ⟨x, hxRi, hxAffine⟩
    refine ⟨x, hxRi, ?_⟩
    intro j
    simpa [gAffine] using hxAffine (eAffine.symm j).1
  have hNotPrimalSelected :
      ¬ ∃ x : Fin n → ℝ, x ∈ C ∧
        (∀ i : Fin p, gStrict i x < (0 : EReal)) ∧
          (∀ j : Fin q, gAffine j x ≤ 0) := by
    intro hSelected
    apply hNotPrimal
    rcases hSelected with ⟨x, hxC, hxStrict, hxAffine⟩
    refine ⟨x, hxC, ?_, ?_⟩
    · intro i hi
      let iSel : JStrict := ⟨i, hi⟩
      have hiStrict : gStrict (eStrict iSel) x < (0 : EReal) := hxStrict (eStrict iSel)
      simpa [gStrict, iSel] using hiStrict
    · intro j hj
      let jSel : JAffine := ⟨j, hj⟩
      have hjAffine : gAffine (eAffine jSel) x ≤ 0 := hxAffine (eAffine jSel)
      simpa [gAffine, jSel] using hjAffine
  have hAlt :=
    theorem21_mixed_convex_affine_alternative
      C hC gStrict hgStrict hdom_gStrict gAffine hgAffine hFeasRiSelected
  rw [xor_def] at hAlt
  rcases hAlt with hSelectedPrimal | hSelectedDual
  · exact False.elim (hNotPrimalSelected hSelectedPrimal.1)
  · rcases hSelectedDual.1 with
      ⟨μStrict, μAffine, hμStrictNonneg, hμAffineNonneg, hμStrictNonzero, hμMargin⟩
    let lamStrict : Fin k → ℝ := fun i =>
      if hi : Sum.inl i ∈ s then μStrict (eStrict ⟨i, hi⟩) else 0
    let lamAffine : Fin l → ℝ := fun j =>
      if hj : Sum.inr j ∈ s then μAffine (eAffine ⟨j, hj⟩) else 0
    refine ⟨lamStrict, lamAffine, ?_, ?_, ?_, ?_⟩
    · intro i
      -- Zero extension preserves nonnegativity on the strict block.
      by_cases hi : Sum.inl i ∈ s
      · simp [lamStrict, hi, hμStrictNonneg]
      · simp [lamStrict, hi]
    · intro j
      -- Zero extension preserves nonnegativity on the affine block.
      by_cases hj : Sum.inr j ∈ s
      · simp [lamAffine, hj, hμAffineNonneg]
      · simp [lamAffine, hj]
    · rcases hμStrictNonzero with ⟨i0, hi0⟩
      refine ⟨(eStrict.symm i0).1, ?_⟩
      have hi0Sel : Sum.inl (eStrict.symm i0).1 ∈ s := (eStrict.symm i0).2
      simp [lamStrict, hi0Sel, hi0]
    · refine ⟨?_, ?_⟩
      · have hStrictSupportLe :
            Fintype.card {i : Fin k // lamStrict i ≠ 0} ≤ Fintype.card JStrict := by
          refine Fintype.card_le_of_injective
            (f := fun i : {i : Fin k // lamStrict i ≠ 0} =>
              show JStrict from
                ⟨i.1, by
                  by_contra hiNot
                  have : lamStrict i.1 = 0 := by
                    simp [lamStrict, hiNot]
                  exact i.2 this⟩) ?_
          intro a b hab
          exact Subtype.ext (by simpa using congrArg Subtype.val hab)
        have hAffineSupportLe :
            Fintype.card {j : Fin l // lamAffine j ≠ 0} ≤ Fintype.card JAffine := by
          refine Fintype.card_le_of_injective
            (f := fun j : {j : Fin l // lamAffine j ≠ 0} =>
              show JAffine from
                ⟨j.1, by
                  by_contra hjNot
                  have : lamAffine j.1 = 0 := by
                    simp [lamAffine, hjNot]
                  exact j.2 this⟩) ?_
          intro a b hab
          exact Subtype.ext (by simpa using congrArg Subtype.val hab)
        calc
          Fintype.card {i : Fin k // lamStrict i ≠ 0} +
              Fintype.card {j : Fin l // lamAffine j ≠ 0}
              ≤ Fintype.card JStrict + Fintype.card JAffine := by
                  exact Nat.add_le_add hStrictSupportLe hAffineSupportLe
          _ = s.card := hsCardSplit
      · intro x hxC
        have hStrictReindexed :
            (∑ i : Fin p, ((μStrict i : ℝ) : EReal) * gStrict i x) =
              ∑ i : JStrict, ((lamStrict i.1 : ℝ) : EReal) * fStrict i.1 x := by
          -- Reindex the strict selected subsystem from `Fin p` back to the strict subtype block.
          refine Fintype.sum_equiv eStrict.symm
            (fun i : Fin p => ((μStrict i : ℝ) : EReal) * gStrict i x)
            (fun i : JStrict => ((lamStrict i.1 : ℝ) : EReal) * fStrict i.1 x) ?_
          intro i
          have hiSel : Sum.inl (eStrict.symm i).1 ∈ s := (eStrict.symm i).2
          simp [gStrict, lamStrict, hiSel]
        have hAffineReindexed :
            (∑ j : Fin q, ((μAffine j : ℝ) : EReal) * ((gAffine j x : ℝ) : EReal)) =
              ∑ j : JAffine, ((lamAffine j.1 : ℝ) : EReal) * ((fAffine j.1 x : ℝ) : EReal) := by
          -- Do the same reindexing for the affine selected subsystem.
          refine Fintype.sum_equiv eAffine.symm
            (fun j : Fin q => ((μAffine j : ℝ) : EReal) * ((gAffine j x : ℝ) : EReal))
            (fun j : JAffine =>
              ((lamAffine j.1 : ℝ) : EReal) * ((fAffine j.1 x : ℝ) : EReal)) ?_
          intro j
          have hjSel : Sum.inr (eAffine.symm j).1 ∈ s := (eAffine.symm j).2
          simp [gAffine, lamAffine, hjSel]
        have hStrictSubtypeToAmbient :
            (∑ i : JStrict, ((lamStrict i.1 : ℝ) : EReal) * fStrict i.1 x) =
              ∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x := by
          let strictSelected : Finset (Fin k) := Finset.univ.filter fun i => Sum.inl i ∈ s
          let eStrictSelected : JStrict ≃ strictSelected :=
            { toFun := fun i => ⟨i.1, by simp [strictSelected, i.2]⟩
              invFun := fun i => ⟨i.1, (Finset.mem_filter.1 i.2).2⟩
              left_inv := by
                intro i
                cases i
                rfl
              right_inv := by
                intro i
                cases i
                rfl }
          have hSubtypeToFinset :
              (∑ i : JStrict, ((lamStrict i.1 : ℝ) : EReal) * fStrict i.1 x) =
                Finset.sum strictSelected
                  (fun i => ((lamStrict i : ℝ) : EReal) * fStrict i x) := by
            calc
              (∑ i : JStrict, ((lamStrict i.1 : ℝ) : EReal) * fStrict i.1 x)
                  = ∑ i : strictSelected, ((lamStrict i.1 : ℝ) : EReal) * fStrict i.1 x := by
                      exact Fintype.sum_equiv eStrictSelected
                        (fun i : JStrict => ((lamStrict i.1 : ℝ) : EReal) * fStrict i.1 x)
                        (fun i : strictSelected =>
                          ((lamStrict i.1 : ℝ) : EReal) * fStrict i.1 x)
                        (fun _ => rfl)
              _ = Finset.sum strictSelected
                    (fun i => ((lamStrict i : ℝ) : EReal) * fStrict i x) := by
                    exact Finset.sum_attach strictSelected
                      (fun i => ((lamStrict i : ℝ) : EReal) * fStrict i x)
          have hFinsetToAmbient :
              Finset.sum strictSelected
                  (fun i => ((lamStrict i : ℝ) : EReal) * fStrict i x) =
                ∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x := by
            refine Finset.sum_subset ?_ ?_
            · intro i hi
              simp
            · intro i hiUniv hiNotSel
              have hiNot : ¬ Sum.inl i ∈ s := by
                simpa [strictSelected, Finset.mem_filter] using hiNotSel
              simp [lamStrict, hiNot]
          exact hSubtypeToFinset.trans hFinsetToAmbient
        have hAffineSubtypeToAmbient :
            (∑ j : JAffine, ((lamAffine j.1 : ℝ) : EReal) * ((fAffine j.1 x : ℝ) : EReal)) =
              ∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal) := by
          let affineSelected : Finset (Fin l) := Finset.univ.filter fun j => Sum.inr j ∈ s
          let eAffineSelected : JAffine ≃ affineSelected :=
            { toFun := fun j => ⟨j.1, by simp [affineSelected, j.2]⟩
              invFun := fun j => ⟨j.1, (Finset.mem_filter.1 j.2).2⟩
              left_inv := by
                intro j
                cases j
                rfl
              right_inv := by
                intro j
                cases j
                rfl }
          have hSubtypeToFinset :
              (∑ j : JAffine, ((lamAffine j.1 : ℝ) : EReal) * ((fAffine j.1 x : ℝ) : EReal)) =
                Finset.sum affineSelected
                  (fun j => ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) := by
            calc
              (∑ j : JAffine, ((lamAffine j.1 : ℝ) : EReal) * ((fAffine j.1 x : ℝ) : EReal))
                  = ∑ j : affineSelected,
                      ((lamAffine j.1 : ℝ) : EReal) * ((fAffine j.1 x : ℝ) : EReal) := by
                        exact Fintype.sum_equiv eAffineSelected
                          (fun j : JAffine =>
                            ((lamAffine j.1 : ℝ) : EReal) * ((fAffine j.1 x : ℝ) : EReal))
                          (fun j : affineSelected =>
                            ((lamAffine j.1 : ℝ) : EReal) * ((fAffine j.1 x : ℝ) : EReal))
                          (fun _ => rfl)
              _ = Finset.sum affineSelected
                    (fun j => ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) := by
                    exact Finset.sum_attach affineSelected
                      (fun j => ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal))
          have hFinsetToAmbient :
              Finset.sum affineSelected
                  (fun j => ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) =
                ∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal) := by
            refine Finset.sum_subset ?_ ?_
            · intro j hj
              simp
            · intro j hjUniv hjNotSel
              have hjNot : ¬ Sum.inr j ∈ s := by
                simpa [affineSelected, Finset.mem_filter] using hjNotSel
              simp [lamAffine, hjNot]
          exact hSubtypeToFinset.trans hFinsetToAmbient
        calc
          (0 : EReal) ≤
              (∑ i : Fin p, ((μStrict i : ℝ) : EReal) * gStrict i x) +
                ∑ j : Fin q, ((μAffine j : ℝ) : EReal) * ((gAffine j x : ℝ) : EReal) :=
            hμMargin x hxC
          _ =
              (∑ i : JStrict, ((lamStrict i.1 : ℝ) : EReal) * fStrict i.1 x) +
                ∑ j : JAffine,
                  ((lamAffine j.1 : ℝ) : EReal) * ((fAffine j.1 x : ℝ) : EReal) := by
                rw [hStrictReindexed, hAffineReindexed]
          _ =
              (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
                ∑ j : JAffine,
                  ((lamAffine j.1 : ℝ) : EReal) * ((fAffine j.1 x : ℝ) : EReal) := by
                rw [hStrictSubtypeToAmbient]
          _ =
              (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
                ∑ j : Fin l,
                  ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal) := by
                rw [hAffineSubtypeToAmbient]

/-- Corollary 21.6.2: if alternative (b) holds in Theorem 21.1 or Theorem 21.2, the
corresponding multipliers can be chosen so that at most `n + 1` of them are nonzero. -/
theorem corollary21_6_2_sparse_dual_multipliers_for_theorems_21_1_and_21_2 :
    (∀ {n m : ℕ}
      (C : Set (Fin n → ℝ))
      (hC : Convex ℝ C)
      (hm : 0 < m)
      (f : Fin m → (Fin n → ℝ) → EReal)
      (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
      (hdom_ri :
        ∀ i, euclideanRelativeInterior_fin n C ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)),
        (∃ l : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ l i) ∧
            (∃ i : Fin m, l i ≠ 0) ∧
              (∀ x, x ∈ C →
                (0 : EReal) ≤ ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x)) →
        ∃ l : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ l i) ∧
            (∃ i : Fin m, l i ≠ 0) ∧
              ((Finset.univ : Finset (Fin m)).filter fun i => l i ≠ 0).card ≤ n + 1 ∧
                (∀ x, x ∈ C →
                  (0 : EReal) ≤ ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x)) ∧
      (∀ {n k l : ℕ}
        (C : Set (Fin n → ℝ))
        (hC : Convex ℝ C)
        (fStrict : Fin k → (Fin n → ℝ) → EReal)
        (hfStrict : ∀ i : Fin k,
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStrict i))
        (hdomStrict :
          ∀ i : Fin k,
            euclideanRelativeInterior_fin n C ⊆
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fStrict i))
        (fAffine : Fin l → (Fin n → ℝ) → ℝ)
        (hAffine : ∀ j : Fin l, ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, fAffine j = g)
        (hFeasRi :
          ∃ x, x ∈ euclideanRelativeInterior_fin n C ∧
            ∀ j : Fin l, fAffine j x ≤ 0),
          (∃ lamStrict : Fin k → ℝ, ∃ lamAffine : Fin l → ℝ,
            (∀ i : Fin k, 0 ≤ lamStrict i) ∧
              (∀ j : Fin l, 0 ≤ lamAffine j) ∧
                (∃ i : Fin k, lamStrict i ≠ 0) ∧
                  (∀ x, x ∈ C →
                    (0 : EReal) ≤
                      (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
                        ∑ j : Fin l,
                          ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal))) →
          ∃ lamStrict : Fin k → ℝ, ∃ lamAffine : Fin l → ℝ,
            (∀ i : Fin k, 0 ≤ lamStrict i) ∧
              (∀ j : Fin l, 0 ≤ lamAffine j) ∧
                (∃ i : Fin k, lamStrict i ≠ 0) ∧
                  Fintype.card {i : Fin k // lamStrict i ≠ 0} +
                      Fintype.card {j : Fin l // lamAffine j ≠ 0} ≤
                    n + 1 ∧
                    (∀ x, x ∈ C →
                    (0 : EReal) ≤
                      (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
                          ∑ j : Fin l,
                            ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal))) :=
  by
    constructor
    · intro n m C hC hm f hf hdom_ri hDual
      let A : Fin m → Set (Fin n → ℝ) := fun i => C ∩ {x : Fin n → ℝ | f i x < (0 : EReal)}
      have hAConvex : ∀ i : Fin m, Convex ℝ (A i) := by
        intro i
        have hfiConvex : ConvexFunction (f i) := by
          simpa [ConvexFunction] using (hf i).1
        simpa [A] using hC.inter
          (convex_sublevel_lt_real_of_convexFunction (f := f i) hfiConvex 0)
      have hNotStrict :
          ¬ ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : Fin m, f i x < (0 : EReal) :=
        helperForTheorem_21_1_certificate_implies_not_strict C f hDual
      have hAEmpty : ¬ (⋂ i : Fin m, A i).Nonempty := by
        intro hNonempty
        rcases hNonempty with ⟨x, hxAll⟩
        let i0 : Fin m := ⟨0, hm⟩
        have hx0 : x ∈ A i0 := Set.mem_iInter.1 hxAll i0
        have hxC : x ∈ C := by
          have hxSet : x ∈ C ∩ {x : Fin n → ℝ | f i0 x < (0 : EReal)} := by
            simpa [A] using hx0
          exact hxSet.1
        have hxStrict : ∀ i : Fin m, f i x < (0 : EReal) := by
          intro i
          have hxi : x ∈ A i := Set.mem_iInter.1 hxAll i
          have hxSet : x ∈ C ∩ {x : Fin n → ℝ | f i x < (0 : EReal)} := by
            simpa [A] using hxi
          exact hxSet.2
        exact hNotStrict ⟨x, hxC, hxStrict⟩
      rcases
          helperForCorollary_21_6_2_small_infeasible_subfamily_of_empty_finite_convex_intersection
            A hAConvex hAEmpty with
        ⟨s, hsPos, hsCard, hsEmpty⟩
      have hNotStrictOnS :
          ¬ ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : Fin m, i ∈ s → f i x < (0 : EReal) := by
        intro hSelected
        apply hsEmpty
        rcases hSelected with ⟨x, hxC, hxSelected⟩
        refine ⟨x, Set.mem_iInter₂.mpr ?_⟩
        intro i hi
        have hxAi : x ∈ C ∩ {x : Fin n → ℝ | f i x < (0 : EReal)} := ⟨hxC, hxSelected i hi⟩
        simpa [A] using hxAi
      rcases
          helperForCorollary_21_6_2_sparse_dual_for_selected_theorem21_1_subfamily
            C hC f hf hdom_ri s hsPos hsCard hNotStrictOnS with
        ⟨l, hlNonneg, hlNonzero, hlCard, hlGlobal⟩
      exact ⟨l, hlNonneg, hlNonzero, le_trans hlCard hsCard, hlGlobal⟩
    · intro n k l C hC fStrict hfStrict hdomStrict fAffine hAffine hFeasRi hDual
      let A : Fin k ⊕ Fin l → Set (Fin n → ℝ) := fun
        | Sum.inl i => C ∩ {x : Fin n → ℝ | fStrict i x < (0 : EReal)}
        | Sum.inr j => C ∩ {x : Fin n → ℝ | fAffine j x ≤ 0}
      have hAConvex : ∀ t : Fin k ⊕ Fin l, Convex ℝ (A t) := by
        intro t
        cases t with
        | inl i =>
            have hfiConvex : ConvexFunction (fStrict i) := by
              simpa [ConvexFunction] using (hfStrict i).1
            simpa [A] using hC.inter
              (convex_sublevel_lt_real_of_convexFunction (f := fStrict i) hfiConvex 0)
        | inr j =>
            rcases hAffine j with ⟨g, hg⟩
            have hAffineConvex : Convex ℝ {x : Fin n → ℝ | fAffine j x ≤ 0} := by
              intro x hx y hy a b ha hb hab
              have hx' : g x ≤ 0 := by
                simpa [hg] using hx
              have hy' : g y ≤ 0 := by
                simpa [hg] using hy
              have hcombo :
                  g (a • x + b • y) = a * g x + b * g y := by
                simpa [smul_eq_mul] using
                  (Convex.combo_affine_apply (x := x) (y := y) (a := a) (b := b) (f := g) hab)
              change fAffine j (a • x + b • y) ≤ 0
              rw [hg, hcombo]
              nlinarith
            simpa [A] using hC.inter hAffineConvex
      have hNotPrimal :
          ¬ ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧
            (∀ j : Fin l, fAffine j x ≤ 0) := by
        intro hPrimal
        exact helperForTheorem_21_2_primal_dual_mutual_exclusion C fStrict fAffine hPrimal hDual
      have hAEmpty : ¬ (⋂ t : Fin k ⊕ Fin l, A t).Nonempty := by
        intro hNonempty
        rcases hNonempty with ⟨x, hxAll⟩
        rcases hDual with
          ⟨lamStrict, lamAffine, hlamStrictNonneg, hlamAffineNonneg, hStrictNonzero, hglobal⟩
        rcases hStrictNonzero with ⟨i0, hi0⟩
        have hx0 : x ∈ A (Sum.inl i0) := Set.mem_iInter.1 hxAll (Sum.inl i0)
        have hxC : x ∈ C := by
          have hxSet : x ∈ C ∩ {x : Fin n → ℝ | fStrict i0 x < (0 : EReal)} := by
            simpa [A] using hx0
          exact hxSet.1
        have hxStrict : ∀ i : Fin k, fStrict i x < (0 : EReal) := by
          intro i
          have hxi : x ∈ A (Sum.inl i) := Set.mem_iInter.1 hxAll (Sum.inl i)
          have hxSet : x ∈ C ∩ {x : Fin n → ℝ | fStrict i x < (0 : EReal)} := by
            simpa [A] using hxi
          exact hxSet.2
        have hxAffine : ∀ j : Fin l, fAffine j x ≤ 0 := by
          intro j
          have hxj : x ∈ A (Sum.inr j) := Set.mem_iInter.1 hxAll (Sum.inr j)
          have hxSet : x ∈ C ∩ {x : Fin n → ℝ | fAffine j x ≤ 0} := by
            simpa [A] using hxj
          exact hxSet.2
        exact hNotPrimal ⟨x, hxC, hxStrict, hxAffine⟩
      rcases
          helperForCorollary_21_6_2_small_infeasible_subfamily_of_empty_finite_convex_intersection
            A hAConvex hAEmpty with
        ⟨s, hsPos, hsCard, hsEmpty⟩
      have hNotPrimalOnS :
          ¬ ∃ x : Fin n → ℝ, x ∈ C ∧
            (∀ i : Fin k, Sum.inl i ∈ s → fStrict i x < (0 : EReal)) ∧
              (∀ j : Fin l, Sum.inr j ∈ s → fAffine j x ≤ 0) := by
        intro hSelected
        apply hsEmpty
        rcases hSelected with ⟨x, hxC, hxStrict, hxAffine⟩
        refine ⟨x, Set.mem_iInter₂.mpr ?_⟩
        intro t ht
        cases t with
        | inl i =>
            have hxAi : x ∈ C ∩ {x : Fin n → ℝ | fStrict i x < (0 : EReal)} := by
              exact ⟨hxC, hxStrict i (by simpa using ht)⟩
            simpa [A] using hxAi
        | inr j =>
            have hxAj : x ∈ C ∩ {x : Fin n → ℝ | fAffine j x ≤ 0} := by
              exact ⟨hxC, hxAffine j (by simpa using ht)⟩
            simpa [A] using hxAj
      rcases
          helperForCorollary_21_6_2_sparse_dual_for_selected_theorem21_2_subfamily
            C hC fStrict hfStrict hdomStrict fAffine hAffine hFeasRi s hsCard hNotPrimalOnS with
        ⟨lamStrict, lamAffine, hlamStrictNonneg, hlamAffineNonneg, hStrictNonzero,
          hSupportCard, hglobal⟩
      exact ⟨lamStrict, lamAffine, hlamStrictNonneg, hlamAffineNonneg, hStrictNonzero,
        le_trans hSupportCard hsCard, hglobal⟩

end Section21
end Chap04
