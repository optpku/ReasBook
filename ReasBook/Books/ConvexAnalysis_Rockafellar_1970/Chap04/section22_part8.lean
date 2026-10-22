/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section22_part7

section Chap04
section Section22

/-- Helper for Theorem 22.6: multiplying by a nonzero scalar does not change the support. -/
lemma helperForTheorem_22_6_vectorSupport_smul_eq'
    {N : ℕ} {z : Fin N → ℝ} {c : ℝ} (hc : c ≠ 0) :
    vectorSupport (c • z) = vectorSupport z := by
  ext i
  simp [vectorSupport, Pi.smul_apply, hc]

/-- Helper for Theorem 22.6: elementary vectors stay elementary under negation. -/
lemma helperForTheorem_22_6_elementaryVector_neg
    {N : ℕ} {L : Submodule ℝ (Fin N → ℝ)} {z : Fin N → ℝ}
    (hz : IsElementaryVector L z) :
    IsElementaryVector L (-z) := by
  rcases hz with ⟨hzNe, hzL, hzMin⟩
  refine ⟨neg_ne_zero.mpr hzNe, L.neg_mem hzL, ?_⟩
  intro hSmall
  rcases hSmall with ⟨y, hyNe, hyL, hySupport⟩
  refine hzMin ⟨-y, neg_ne_zero.mpr hyNe, L.neg_mem hyL, ?_⟩
  simpa [vectorSupport] using hySupport

/-- Helper for Theorem 22.6: elementary vectors stay elementary under multiplication by a
nonzero scalar. -/
lemma helperForTheorem_22_6_elementaryVector_smul
    {N : ℕ} {L : Submodule ℝ (Fin N → ℝ)} {z : Fin N → ℝ} {c : ℝ}
    (hc : c ≠ 0) (hz : IsElementaryVector L z) :
    IsElementaryVector L (c • z) := by
  rcases hz with ⟨hzNe, hzL, hzMin⟩
  refine ⟨smul_ne_zero hc hzNe, L.smul_mem c hzL, ?_⟩
  intro hSmall
  rcases hSmall with ⟨y, hyNe, hyL, hySupport⟩
  refine hzMin ⟨c⁻¹ • y, smul_ne_zero (inv_ne_zero hc) hyNe,
    L.smul_mem c⁻¹ hyL, ?_⟩
  simpa [helperForTheorem_22_6_vectorSupport_smul_eq' hc,
    helperForTheorem_22_6_vectorSupport_smul_eq' (inv_ne_zero hc)] using hySupport

/-- Helper for Theorem 22.6: for a finite family of real intervals indexed by any finite type,
pairwise intersection implies total intersection. -/
lemma helperForTheorem_22_6_pairwiseIntersecting_realIntervals_nonempty_iInter_of_finite
    {ι : Type*} [Finite ι] (J : ι → Set ℝ)
    (hJ : ∀ i, Set.OrdConnected (J i))
    (hpair : ∀ i j : ι, (J i ∩ J j).Nonempty) :
    (⋂ i, J i).Nonempty := by
  classical
  let _ := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hFin :
      (⋂ i : Fin (Fintype.card ι), J (e.symm i)).Nonempty :=
    pairwiseIntersecting_realIntervals_nonempty_iInter
      (J := fun i => J (e.symm i))
      (hJ := by
        intro i
        exact hJ (e.symm i))
      (hpair := by
        intro i j
        simpa using hpair (e.symm i) (e.symm j))
  rcases hFin with ⟨x, hx⟩
  have hxFin : ∀ i : Fin (Fintype.card ι), x ∈ J (e.symm i) := by
    simpa [Set.mem_iInter] using hx
  refine ⟨x, ?_⟩
  simpa [Set.mem_iInter] using (fun i : ι => hxFin (e i))

/-- Helper for Theorem 22.6: if a vector annihilates every elementary vector in `Lᗮ`, then it
already belongs to `L`. -/
lemma helperForTheorem_22_6_annihilates_all_elementaryVectors_iff_mem_subspace
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) (x : Fin N → ℝ)
    (hx :
      ∀ y : Fin N → ℝ,
        IsElementaryVector (dotProductOrthogonalComplement L) y →
          dotProduct y x = 0) :
    x ∈ L := by
  have hSpanZero :
      ∀ y : Fin N → ℝ,
        y ∈ Submodule.span ℝ
          {w : Fin N → ℝ | IsElementaryVector (dotProductOrthogonalComplement L) w} →
          dotProduct y x = 0 := by
    intro y hy
    refine Submodule.span_induction
      (p := fun y _ => dotProduct y x = 0) ?_ ?_ ?_ ?_ hy
    · intro w hw
      exact hx w hw
    · simp [dotProduct]
    · intro u v hu hv
      intro hu0 hv0
      simpa [dotProduct_add, hu0, hv0]
    · intro a w hw
      intro hw0
      simp [dotProduct_smul, hw0, smul_eq_mul]
  have hxOrth :
      x ∈ LinearMap.BilinForm.orthogonal
        (dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N))
        (dotProductOrthogonalComplement L) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hSpanZero y (mem_span_elementaryVectors (L := dotProductOrthogonalComplement L) hy)
  have hDouble :
      x ∈ LinearMap.BilinForm.orthogonal
        (dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N))
        (LinearMap.BilinForm.orthogonal
          (dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N)) L) := by
    simpa [helperForTheorem_22_6_dotProductOrthogonalComplement_eq_bilinOrthogonal L] using
      hxOrth
  have hEq :=
    LinearMap.BilinForm.orthogonal_orthogonal
      (V := Fin N → ℝ) (K := ℝ)
      (B := dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N))
      (helperForTheorem_22_6_dotProductBilin_nondegenerate (N := N))
      (helperForTheorem_22_6_dotProductBilin_isRefl (N := N)) L
  simpa [hEq] using hDouble

/-- Helper for Theorem 22.6: count the coordinates whose intervals are genuinely nontrivial in
the sense of the book, i.e. neither singleton nor all of `ℝ`. -/
noncomputable def helperForTheorem_22_6_nontrivialCoordCount {N : ℕ}
    (I : Fin N → Set ℝ) : ℕ :=
  (@Finset.filter (Fin N)
      (fun j => ¬ Set.Subsingleton (I j) ∧ I j ≠ Set.univ)
      (Classical.decPred _) Finset.univ).card

/-- Helper for Theorem 22.6: if the book-count of nontrivial intervals is zero, every coordinate
interval is either a singleton or all of `ℝ`. -/
lemma helperForTheorem_22_6_subsingleton_or_univ_of_nontrivialCoordCount_eq_zero
    {N : ℕ} (I : Fin N → Set ℝ)
    (hCount : helperForTheorem_22_6_nontrivialCoordCount I = 0)
    (j : Fin N) :
    Set.Subsingleton (I j) ∨ I j = Set.univ := by
  classical
  by_contra hTrivial
  have hNotSub : ¬ Set.Subsingleton (I j) := by
    intro hSub
    exact hTrivial (Or.inl hSub)
  have hNotUniv : I j ≠ Set.univ := by
    intro hUniv
    exact hTrivial (Or.inr hUniv)
  have hj :
      j ∈ (Finset.univ.filter fun k =>
        ¬ Set.Subsingleton (I k) ∧ I k ≠ Set.univ) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact ⟨hNotSub, hNotUniv⟩
  have hPos :
      0 < helperForTheorem_22_6_nontrivialCoordCount I := by
    simpa [helperForTheorem_22_6_nontrivialCoordCount] using
      Finset.card_pos.mpr ⟨j, hj⟩
  linarith

/-- Helper for Theorem 22.6: if the book-count of nontrivial intervals is positive, one can pick
such a coordinate. -/
lemma helperForTheorem_22_6_exists_nontrivial_coord
    {N : ℕ} (I : Fin N → Set ℝ)
    (hPos : 0 < helperForTheorem_22_6_nontrivialCoordCount I) :
    ∃ j : Fin N, ¬ Set.Subsingleton (I j) ∧ I j ≠ Set.univ := by
  classical
  have hCardPos :
      0 < (Finset.univ.filter fun j =>
        ¬ Set.Subsingleton (I j) ∧ I j ≠ Set.univ).card := by
    simpa [helperForTheorem_22_6_nontrivialCoordCount] using hPos
  rcases Finset.card_pos.mp hCardPos with ⟨j, hj⟩
  exact ⟨j, (Finset.mem_filter.mp hj).2⟩

/-- Helper for Theorem 22.6: replacing a genuinely nontrivial coordinate interval by `ℝ`
strictly decreases the book-count. -/
lemma helperForTheorem_22_6_nontrivialCoordCount_update_univ_lt
    {N : ℕ} (I : Fin N → Set ℝ) {j : Fin N}
    (hj : ¬ Set.Subsingleton (I j) ∧ I j ≠ Set.univ) :
    helperForTheorem_22_6_nontrivialCoordCount (Function.update I j Set.univ) <
      helperForTheorem_22_6_nontrivialCoordCount I := by
  classical
  let s : Finset (Fin N) :=
    Finset.univ.filter fun k => ¬ Set.Subsingleton (I k) ∧ I k ≠ Set.univ
  let s' : Finset (Fin N) :=
    Finset.univ.filter fun k =>
      ¬ Set.Subsingleton (Function.update I j Set.univ k) ∧
        Function.update I j Set.univ k ≠ Set.univ
  have hs'subset : s' ⊆ s := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    by_cases hkj : k = j
    · have : Function.update I j Set.univ k = Set.univ := by
        simp [Function.update, hkj]
      exact False.elim (hk'.2 this)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [Function.update, hkj] using hk'⟩
  have hjmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hjnotmem : j ∉ s' := by
    intro hj'
    have hj'' := (Finset.mem_filter.mp hj').2
    have : Function.update I j Set.univ j = Set.univ := by simp
    exact hj''.2 this
  have hcardLe : s'.card ≤ s.card := Finset.card_le_card hs'subset
  have hcardNe : s'.card ≠ s.card := by
    intro hEqCard
    have hsEq : s' = s := Finset.eq_of_subset_of_card_le hs'subset (by simpa [hEqCard])
    exact hjnotmem (hsEq ▸ hjmem)
  simpa [helperForTheorem_22_6_nontrivialCoordCount, s, s'] using
    Nat.lt_of_le_of_ne hcardLe hcardNe

/-- Helper for Theorem 22.6: replacing a genuinely nontrivial coordinate interval by a singleton
strictly decreases the book-count. -/
lemma helperForTheorem_22_6_nontrivialCoordCount_update_singleton_lt
    {N : ℕ} (I : Fin N → Set ℝ) {j : Fin N} {α : ℝ}
    (hj : ¬ Set.Subsingleton (I j) ∧ I j ≠ Set.univ) :
    helperForTheorem_22_6_nontrivialCoordCount (Function.update I j ({α} : Set ℝ)) <
      helperForTheorem_22_6_nontrivialCoordCount I := by
  classical
  let s : Finset (Fin N) :=
    Finset.univ.filter fun k => ¬ Set.Subsingleton (I k) ∧ I k ≠ Set.univ
  let s' : Finset (Fin N) :=
    Finset.univ.filter fun k =>
      ¬ Set.Subsingleton (Function.update I j ({α} : Set ℝ) k) ∧
        Function.update I j ({α} : Set ℝ) k ≠ Set.univ
  have hs'subset : s' ⊆ s := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    by_cases hkj : k = j
    · have : Set.Subsingleton ({α} : Set ℝ) := Set.subsingleton_singleton
      have hUpdateSub :
          Set.Subsingleton (Function.update I j ({α} : Set ℝ) k) := by
        simpa [Function.update, hkj] using this
      exact False.elim (hk'.1 hUpdateSub)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [Function.update, hkj] using hk'⟩
  have hjmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hjnotmem : j ∉ s' := by
    intro hj'
    have hj'' := (Finset.mem_filter.mp hj').2
    have hUpdateSub :
        Set.Subsingleton (Function.update I j ({α} : Set ℝ) j) := by
      simpa using (Set.subsingleton_singleton : Set.Subsingleton ({α} : Set ℝ))
    exact hj''.1 hUpdateSub
  have hcardLe : s'.card ≤ s.card := Finset.card_le_card hs'subset
  have hcardNe : s'.card ≠ s.card := by
    intro hEqCard
    have hsEq : s' = s := Finset.eq_of_subset_of_card_le hs'subset (by simpa [hEqCard])
    exact hjnotmem (hsEq ▸ hjmem)
  simpa [helperForTheorem_22_6_nontrivialCoordCount, s, s'] using
    Nat.lt_of_le_of_ne hcardLe hcardNe

/-- Helper for Theorem 22.6: if neither a vector nor its negative positively separates the box,
then some box point lies on the corresponding zero level set. -/
lemma helperForTheorem_22_6_zeroWitness_of_not_positive_of_not_positive_neg
    {N : ℕ} (I : Fin N → Set ℝ)
    (hI_interval : ∀ j, Set.OrdConnected (I j))
    (hI_nonempty : ∀ j, (I j).Nonempty)
    {zStar : Fin N → ℝ}
    (hNotPos : ¬ PositivelySeparatesIntervalFamily I zStar)
    (hNotNegPos : ¬ PositivelySeparatesIntervalFamily I (-zStar)) :
    ∃ z : Fin N → ℝ, (∀ j, z j ∈ I j) ∧ dotProduct zStar z = 0 := by
  rcases helperForTheorem_22_6_intervalBox_convex_nonempty I hI_interval hI_nonempty with
    ⟨hBoxNonempty, hBoxConvex⟩
  have hNotPos' :
      ∃ z : Fin N → ℝ, (∀ j, z j ∈ I j) ∧ dotProduct zStar z ≤ 0 := by
    simpa [PositivelySeparatesIntervalFamily, not_lt] using hNotPos
  have hNotNegPos' :
      ∃ z : Fin N → ℝ, (∀ j, z j ∈ I j) ∧ 0 ≤ dotProduct zStar z := by
    simpa [PositivelySeparatesIntervalFamily, dotProduct_neg, not_lt] using hNotNegPos
  rcases hNotPos' with ⟨z0, hz0I, hz0Nonpos⟩
  rcases hNotNegPos' with ⟨z1, hz1I, hz1Nonneg⟩
  by_cases hz0Zero : dotProduct zStar z0 = 0
  · exact ⟨z0, hz0I, hz0Zero⟩
  by_cases hz1Zero : dotProduct zStar z1 = 0
  · exact ⟨z1, hz1I, hz1Zero⟩
  have hz0Neg : dotProduct zStar z0 < 0 := lt_of_le_of_ne hz0Nonpos hz0Zero
  have hz1Pos : 0 < dotProduct zStar z1 := lt_of_le_of_ne hz1Nonneg (Ne.symm hz1Zero)
  let t : ℝ := dotProduct zStar z1 / (dotProduct zStar z1 - dotProduct zStar z0)
  have hDenPos : 0 < dotProduct zStar z1 - dotProduct zStar z0 := by
    linarith
  have htNonneg : 0 ≤ t := by
    exact le_of_lt (div_pos hz1Pos hDenPos)
  have htLe : t ≤ 1 := by
    have hDenNe : dotProduct zStar z1 - dotProduct zStar z0 ≠ 0 := by linarith
    rw [show (1 : ℝ) = (dotProduct zStar z1 - dotProduct zStar z0) /
        (dotProduct zStar z1 - dotProduct zStar z0) by
          field_simp [hDenNe]]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hDenPos)
  let z : Fin N → ℝ := t • z0 + (1 - t) • z1
  have hzI : ∀ j, z j ∈ I j := by
    have hz0Mem : z0 ∈ {w : Fin N → ℝ | ∀ j, w j ∈ I j} := hz0I
    have hz1Mem : z1 ∈ {w : Fin N → ℝ | ∀ j, w j ∈ I j} := hz1I
    have hzMem :
        z ∈ {w : Fin N → ℝ | ∀ j, w j ∈ I j} := by
      have htOneNonneg : 0 ≤ 1 - t := sub_nonneg.mpr htLe
      have htSum : t + (1 - t) = 1 := by ring
      exact hBoxConvex hz0Mem hz1Mem htNonneg htOneNonneg htSum
    exact hzMem
  have hzDotZero : dotProduct zStar z = 0 := by
    have hDenNe : dotProduct zStar z1 - dotProduct zStar z0 ≠ 0 := by linarith
    calc
      dotProduct zStar z
          = t * dotProduct zStar z0 + (1 - t) * dotProduct zStar z1 := by
              simp [z, dotProduct_add, dotProduct_smul, smul_eq_mul, mul_comm, mul_left_comm,
                mul_assoc]
      _ = t * dotProduct zStar z0 - t * dotProduct zStar z1 + dotProduct zStar z1 := by
            ring
      _ = 0 := by
            have htMul :
                t * (dotProduct zStar z1 - dotProduct zStar z0) = dotProduct zStar z1 := by
              dsimp [t]
              field_simp [hDenNe]
            nlinarith
  exact ⟨z, hzI, hzDotZero⟩

/-- Helper for Theorem 22.6: for a fixed coordinate `j`, the book's interval
`ζ₁⋆ I₁ + ··· + ζ_N⋆ I_N` specialized to `ζⱼ⋆ = -1` is represented by the set of values that can
be assigned to the `j`-th coordinate while solving the zero-pairing equation. -/
def helperForTheorem_22_6_coordinateReductionInterval
    {N : ℕ} (I : Fin N → Set ℝ) (j : Fin N) (zStar : Fin N → ℝ) : Set ℝ :=
  {α : ℝ |
    ∃ z : Fin N → ℝ,
      z j = α ∧
        (∀ k, k ≠ j → z k ∈ I k) ∧
        dotProduct zStar z = 0}

/-- Helper for Theorem 22.6: the coordinate-reduction set attached to a normalized elementary
separator is again a real interval. -/
lemma helperForTheorem_22_6_coordinateReductionInterval_ordConnected
    {N : ℕ} (I : Fin N → Set ℝ) (j : Fin N) (zStar : Fin N → ℝ)
    (hI_interval : ∀ k, Set.OrdConnected (I k)) :
    Set.OrdConnected
      (helperForTheorem_22_6_coordinateReductionInterval I j zStar) := by
  have hConvex :
      Convex ℝ (helperForTheorem_22_6_coordinateReductionInterval I j zStar) := by
    intro α0 hα0 α1 hα1 a b ha hb hab
    rcases hα0 with ⟨x0, hx0j, hx0I, hx0Zero⟩
    rcases hα1 with ⟨x1, hx1j, hx1I, hx1Zero⟩
    refine ⟨a • x0 + b • x1, ?_, ?_, ?_⟩
    · simp [hx0j, hx1j, smul_eq_mul, left_distrib, right_distrib, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    · intro k hk
      exact (hI_interval k).convex (hx0I k hk) (hx1I k hk) ha hb hab
    · simp [dotProduct_add, dotProduct_smul, hx0Zero, hx1Zero, smul_eq_mul]
  exact hConvex.ordConnected

/-- Helper for Theorem 22.6: the base case of the book's induction, where every coordinate
interval is either a singleton or all of `ℝ`. -/
lemma helperForTheorem_22_6_primal_of_no_elementary_separator_base
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) (I : Fin N → Set ℝ)
    (hI_interval : ∀ j, Set.OrdConnected (I j))
    (hI_nonempty : ∀ j, (I j).Nonempty)
    (hCount : helperForTheorem_22_6_nontrivialCoordCount I = 0)
    (hNoElemSep :
      ∀ zStar : Fin N → ℝ,
        zStar ∈ dotProductOrthogonalComplement L →
        IsElementaryVector (dotProductOrthogonalComplement L) zStar →
        ¬ PositivelySeparatesIntervalFamily I zStar) :
    ∃ z : Fin N → ℝ, z ∈ L ∧ ∀ j, z j ∈ I j := by
  classical
  let a : Fin N → ℝ := fun j => Classical.choose (hI_nonempty j)
  let U : Submodule ℝ (Fin N → ℝ) :=
    { carrier := {u : Fin N → ℝ | ∀ j, I j ≠ Set.univ → u j = 0}
      zero_mem' := by
        intro j hj
        simp
      add_mem' := by
        intro u v hu hv j hj
        simp [hu j hj, hv j hj]
      smul_mem' := by
        intro c u hu j hj
        simp [hu j hj] }
  let L0 : Submodule ℝ (Fin N → ℝ) := L + U
  have hLiftElementary :
      ∀ y : Fin N → ℝ,
        IsElementaryVector (dotProductOrthogonalComplement L0) y →
          IsElementaryVector (dotProductOrthogonalComplement L) y := by
    intro y hyElem
    have hyOrthL0 : y ∈ dotProductOrthogonalComplement L0 := hyElem.2.1
    have hyOrthL : y ∈ dotProductOrthogonalComplement L := by
      rw [dotProductOrthogonalComplement, Submodule.mem_iInf] at hyOrthL0 ⊢
      intro z
      have hzL0 : (z : Fin N → ℝ) ∈ L0 := by
        exact Submodule.mem_sup.mpr ⟨(z : Fin N → ℝ), z.2, 0, U.zero_mem, by simp⟩
      simpa [LinearMap.mem_ker] using hyOrthL0 ⟨(z : Fin N → ℝ), hzL0⟩
    have hyFreeZero : ∀ j : Fin N, I j = Set.univ → y j = 0 := by
      intro j hjUniv
      let ej : Fin N → ℝ := fun k => if k = j then 1 else 0
      have hejU : ej ∈ U := by
        intro k hk
        by_cases hkj : k = j
        · subst hkj
          exact False.elim (hk hjUniv)
        · simp [ej, hkj]
      have hejL0 : ej ∈ L0 := by
        exact Submodule.mem_sup.mpr ⟨0, L.zero_mem, ej, hejU, by simp⟩
      have hejKer := by
        rw [dotProductOrthogonalComplement, Submodule.mem_iInf] at hyOrthL0
        exact hyOrthL0 ⟨ej, hejL0⟩
      have hdot : dotProduct ej y = 0 := by
        simpa [LinearMap.mem_ker] using hejKer
      simpa [ej, dotProduct] using hdot
    refine ⟨hyElem.1, hyOrthL, ?_⟩
    intro hSmall
    rcases hSmall with ⟨w, hwNe, hwOrthL, hwSupport⟩
    have hwFreeZero : ∀ j : Fin N, I j = Set.univ → w j = 0 := by
      intro j hjUniv
      by_contra hwjNe
      have hwj : j ∈ vectorSupport w := by
        simpa [vectorSupport] using hwjNe
      have hyj : j ∈ vectorSupport y := hwSupport.1 hwj
      have hyjNe : y j ≠ 0 := by
        simpa [vectorSupport] using hyj
      exact hyjNe (hyFreeZero j hjUniv)
    have hwOrthL0 : w ∈ dotProductOrthogonalComplement L0 := by
      rw [dotProductOrthogonalComplement, Submodule.mem_iInf]
      intro z
      rw [LinearMap.mem_ker]
      rcases Submodule.mem_sup.mp z.2 with ⟨l, hlL, u, huU, hzEq⟩
      have hdotL : dotProduct l w = 0 := by
        rw [dotProductOrthogonalComplement, Submodule.mem_iInf] at hwOrthL
        simpa [LinearMap.mem_ker] using hwOrthL ⟨l, hlL⟩
      have hdotU : dotProduct u w = 0 := by
        rw [dotProduct]
        refine Finset.sum_eq_zero ?_
        intro k hk
        by_cases hkUniv : I k = Set.univ
        · have hwk : w k = 0 := hwFreeZero k hkUniv
          simp [hwk]
        · have huk : u k = 0 := huU k hkUniv
          simp [huk]
      have hdotLU : dotProduct (l + u) w = 0 := by
        simp [dotProduct_add, hdotL, hdotU]
      simpa [hzEq] using hdotLU
    exact hyElem.2.2 ⟨w, hwNe, hwOrthL0, hwSupport⟩
  have haL0 : a ∈ L0 := by
    apply helperForTheorem_22_6_annihilates_all_elementaryVectors_iff_mem_subspace (L := L0)
    intro y hyElem
    have hyElemL : IsElementaryVector (dotProductOrthogonalComplement L) y :=
      hLiftElementary y hyElem
    have hyOrthL : y ∈ dotProductOrthogonalComplement L := hyElemL.2.1
    have hNotPos : ¬ PositivelySeparatesIntervalFamily I y :=
      hNoElemSep y hyOrthL hyElemL
    have hNotNegPos : ¬ PositivelySeparatesIntervalFamily I (-y) := by
      exact hNoElemSep (-y) ((dotProductOrthogonalComplement L).neg_mem hyOrthL)
        (helperForTheorem_22_6_elementaryVector_neg hyElemL)
    rcases helperForTheorem_22_6_zeroWitness_of_not_positive_of_not_positive_neg
        (I := I) hI_interval hI_nonempty hNotPos hNotNegPos with
      ⟨z, hzI, hzZero⟩
    have hyFreeZero : ∀ j : Fin N, I j = Set.univ → y j = 0 := by
      intro j hjUniv
      have hyOrthL0 : y ∈ dotProductOrthogonalComplement L0 := hyElem.2.1
      let ej : Fin N → ℝ := fun k => if k = j then 1 else 0
      have hejU : ej ∈ U := by
        intro k hk
        by_cases hkj : k = j
        · subst hkj
          exact False.elim (hk hjUniv)
        · simp [ej, hkj]
      have hdot : dotProduct ej y = 0 := by
        have hejL0 : ej ∈ L0 := by
          exact Submodule.mem_sup.mpr ⟨0, L.zero_mem, ej, hejU, by simp⟩
        have hyOrthL0' : y ∈ dotProductOrthogonalComplement L0 := hyElem.2.1
        rw [dotProductOrthogonalComplement, Submodule.mem_iInf] at hyOrthL0'
        have hejKer :
            y ∈ LinearMap.ker
              ((dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N)) ej) :=
          hyOrthL0' ⟨ej, hejL0⟩
        simpa [LinearMap.mem_ker] using hejKer
      simpa [ej, dotProduct] using hdot
    have hDotEq : dotProduct y a = dotProduct y z := by
      rw [dotProduct, dotProduct]
      refine Finset.sum_congr rfl ?_
      intro j hj
      by_cases hjUniv : I j = Set.univ
      · have hyj : y j = 0 := hyFreeZero j hjUniv
        simp [hyj]
      · have hSingle : Set.Subsingleton (I j) := by
          exact
            (helperForTheorem_22_6_subsingleton_or_univ_of_nontrivialCoordCount_eq_zero
              I hCount j).resolve_right hjUniv
        have hzEq : z j = a j := hSingle (hzI j) (Classical.choose_spec (hI_nonempty j))
        simp [hzEq]
    simpa [hDotEq] using hzZero
  rcases Submodule.mem_sup.mp haL0 with ⟨z, hzL, u, huU, hEq⟩
  refine ⟨z, hzL, ?_⟩
  intro j
  by_cases hjUniv : I j = Set.univ
  · simpa [hjUniv]
  · have huj : u j = 0 := huU j hjUniv
    have hzEq : z j = a j := by
      have hCoord : z j + u j = a j := by
        simpa using congrArg (fun w => w j) hEq
      simpa [huj] using hCoord
    simpa [a, hzEq] using Classical.choose_spec (hI_nonempty j)

/-- Helper for Theorem 22.6: the original book proof proceeds by induction on the number of
coordinate intervals that are neither singletons nor all of `ℝ`. -/
lemma helperForTheorem_22_6_primal_of_no_elementary_separator_aux
    {N : ℕ} (n : ℕ) :
    ∀ (L : Submodule ℝ (Fin N → ℝ)) (I : Fin N → Set ℝ),
      helperForTheorem_22_6_nontrivialCoordCount I ≤ n →
      (∀ j, Set.OrdConnected (I j)) →
      (∀ j, (I j).Nonempty) →
      (∀ zStar : Fin N → ℝ,
        zStar ∈ dotProductOrthogonalComplement L →
        IsElementaryVector (dotProductOrthogonalComplement L) zStar →
        ¬ PositivelySeparatesIntervalFamily I zStar) →
      ∃ z : Fin N → ℝ, z ∈ L ∧ ∀ j, z j ∈ I j := by
  induction' n with n ih
  · intro L I hCount hI_interval hI_nonempty hNoElemSep
    exact
      helperForTheorem_22_6_primal_of_no_elementary_separator_base
        L I hI_interval hI_nonempty (Nat.le_zero.mp hCount) hNoElemSep
  · intro L I hCount hI_interval hI_nonempty hNoElemSep
    by_cases hCountZero : helperForTheorem_22_6_nontrivialCoordCount I = 0
    · exact
        helperForTheorem_22_6_primal_of_no_elementary_separator_base
          L I hI_interval hI_nonempty hCountZero hNoElemSep
    · have hCountPos : 0 < helperForTheorem_22_6_nontrivialCoordCount I :=
        Nat.pos_of_ne_zero hCountZero
      rcases helperForTheorem_22_6_exists_nontrivial_coord I hCountPos with
        ⟨j0, hj0NonSub, hj0NotUniv⟩
      let Iuniv : Fin N → Set ℝ := Function.update I j0 Set.univ
      have hIuniv_interval : ∀ j, Set.OrdConnected (Iuniv j) := by
        intro j
        by_cases hj : j = j0
        · subst hj
          simpa [Iuniv] using (Set.ordConnected_univ : Set.OrdConnected (Set.univ : Set ℝ))
        · simpa [Iuniv, Function.update, hj] using hI_interval j
      have hIuniv_nonempty : ∀ j, (Iuniv j).Nonempty := by
        intro j
        by_cases hj : j = j0
        · subst hj
          simp [Iuniv]
        · simpa [Iuniv, Function.update, hj] using hI_nonempty j
      have hCountUnivLe :
          helperForTheorem_22_6_nontrivialCoordCount Iuniv ≤ n := by
        exact Nat.lt_succ_iff.mp <|
          lt_of_lt_of_le
            (helperForTheorem_22_6_nontrivialCoordCount_update_univ_lt
              (I := I) (j := j0) ⟨hj0NonSub, hj0NotUniv⟩)
            hCount
      have hNoElemSepUniv :
          ∀ zStar : Fin N → ℝ,
            zStar ∈ dotProductOrthogonalComplement L →
            IsElementaryVector (dotProductOrthogonalComplement L) zStar →
            ¬ PositivelySeparatesIntervalFamily Iuniv zStar := by
        intro zStar hzStarOrth hzStarElem hPosUniv
        apply hNoElemSep zStar hzStarOrth hzStarElem
        intro z hzI
        exact hPosUniv z (by
          intro j
          by_cases hj : j = j0
          · subst hj
            simp [Iuniv]
          · simpa [Iuniv, Function.update, hj] using hzI j)
      rcases ih L Iuniv hCountUnivLe hIuniv_interval hIuniv_nonempty hNoElemSepUniv with
        ⟨zUniv, hzUnivL, hzUnivI⟩
      rcases elementaryVector_finite_upToScalarMultiples
          (L := dotProductOrthogonalComplement L) with
        ⟨S, hSfin, hSelem, hScover⟩
      let τ := {y : Fin N → ℝ // y ∈ S ∧ y j0 ≠ 0}
      let _ : Fintype τ := (hSfin.subset (by
        intro y hy
        exact hy.1)).fintype
      let eNorm : τ → Fin N → ℝ := fun t => (-1 / t.1 j0) • t.1
      have heNormOrth :
          ∀ t : τ, eNorm t ∈ dotProductOrthogonalComplement L := by
        intro t
        exact (dotProductOrthogonalComplement L).smul_mem _
          ((hSelem t.1 t.2.1).2.1)
      have heNormElem :
          ∀ t : τ, IsElementaryVector (dotProductOrthogonalComplement L) (eNorm t) := by
        intro t
        exact
          helperForTheorem_22_6_elementaryVector_smul
            (div_ne_zero (by norm_num) t.2.2) (hSelem t.1 t.2.1)
      have hIIntersectReduction :
          ∀ t : τ,
            (I j0 ∩ helperForTheorem_22_6_coordinateReductionInterval I j0 (eNorm t)).Nonempty := by
        intro t
        have hNotPos :
            ¬ PositivelySeparatesIntervalFamily I (eNorm t) :=
          hNoElemSep (eNorm t) (heNormOrth t) (heNormElem t)
        have hNotNegPos :
            ¬ PositivelySeparatesIntervalFamily I (-eNorm t) :=
          hNoElemSep (-eNorm t)
            ((dotProductOrthogonalComplement L).neg_mem (heNormOrth t))
            (helperForTheorem_22_6_elementaryVector_neg (heNormElem t))
        rcases helperForTheorem_22_6_zeroWitness_of_not_positive_of_not_positive_neg
            (I := I) hI_interval hI_nonempty hNotPos hNotNegPos with
          ⟨z, hzI, hzZero⟩
        refine ⟨z j0, hzI j0, ?_⟩
        exact ⟨z, rfl, (by
          intro k hk
          exact hzI k), hzZero⟩
      have hReductionPair :
          ∀ t1 t2 : τ,
            (helperForTheorem_22_6_coordinateReductionInterval I j0 (eNorm t1) ∩
                helperForTheorem_22_6_coordinateReductionInterval I j0 (eNorm t2)).Nonempty := by
        intro t1 t2
        refine ⟨zUniv j0, ?_, ?_⟩
        · refine ⟨zUniv, rfl, ?_, ?_⟩
          · intro k hk
            simpa [Iuniv, Function.update, hk] using hzUnivI k
          · have hdot : dotProduct zUniv (eNorm t1) = 0 := by
              have hOrth := heNormOrth t1
              rw [dotProductOrthogonalComplement, Submodule.mem_iInf] at hOrth
              simpa [LinearMap.mem_ker, dotProduct_comm] using hOrth ⟨zUniv, hzUnivL⟩
            simpa [dotProduct_comm] using hdot
        · refine ⟨zUniv, rfl, ?_, ?_⟩
          · intro k hk
            simpa [Iuniv, Function.update, hk] using hzUnivI k
          · have hdot : dotProduct zUniv (eNorm t2) = 0 := by
              have hOrth := heNormOrth t2
              rw [dotProductOrthogonalComplement, Submodule.mem_iInf] at hOrth
              simpa [LinearMap.mem_ker, dotProduct_comm] using hOrth ⟨zUniv, hzUnivL⟩
            simpa [dotProduct_comm] using hdot
      let K : Option τ → Set ℝ
        | none => I j0
        | some t => helperForTheorem_22_6_coordinateReductionInterval I j0 (eNorm t)
      have hKnonempty :
          (⋂ o : Option τ, K o).Nonempty := by
        apply
          helperForTheorem_22_6_pairwiseIntersecting_realIntervals_nonempty_iInter_of_finite
            (J := K)
        · intro o
          cases o with
          | none =>
              exact hI_interval j0
          | some t =>
              exact
                helperForTheorem_22_6_coordinateReductionInterval_ordConnected
                  I j0 (eNorm t) hI_interval
        · intro o1 o2
          cases o1 with
          | none =>
              cases o2 with
              | none =>
                  simpa [K, Set.inter_self] using (hI_nonempty j0)
              | some t =>
                  simpa [K] using hIIntersectReduction t
          | some t1 =>
              cases o2 with
              | none =>
                  simpa [K, Set.inter_comm] using hIIntersectReduction t1
              | some t2 =>
                  simpa [K] using hReductionPair t1 t2
      rcases hKnonempty with ⟨α, hαK⟩
      have hαKall : ∀ o : Option τ, α ∈ K o := by
        simpa [Set.mem_iInter] using hαK
      have hαI : α ∈ I j0 := by
        simpa [K] using hαKall none
      have hαReduction :
          ∀ t : τ,
            α ∈ helperForTheorem_22_6_coordinateReductionInterval I j0 (eNorm t) := by
        intro t
        simpa [K] using hαKall (some t)
      let Ising : Fin N → Set ℝ := Function.update I j0 ({α} : Set ℝ)
      have hIsing_interval : ∀ j, Set.OrdConnected (Ising j) := by
        intro j
        by_cases hj : j = j0
        · subst hj
          simpa [Ising] using (Set.ordConnected_singleton (a := α))
        · simpa [Ising, Function.update, hj] using hI_interval j
      have hIsing_nonempty : ∀ j, (Ising j).Nonempty := by
        intro j
        by_cases hj : j = j0
        · subst hj
          simp [Ising]
        · simpa [Ising, Function.update, hj] using hI_nonempty j
      have hCountSingLe :
          helperForTheorem_22_6_nontrivialCoordCount Ising ≤ n := by
        exact Nat.lt_succ_iff.mp <|
          lt_of_lt_of_le
            (helperForTheorem_22_6_nontrivialCoordCount_update_singleton_lt
              (I := I) (j := j0) (α := α) ⟨hj0NonSub, hj0NotUniv⟩)
            hCount
      have hNoElemSepSing :
          ∀ zStar : Fin N → ℝ,
            zStar ∈ dotProductOrthogonalComplement L →
            IsElementaryVector (dotProductOrthogonalComplement L) zStar →
            ¬ PositivelySeparatesIntervalFamily Ising zStar := by
        intro zStar hzStarOrth hzStarElem hPosSing
        by_cases hzj0 : zStar j0 = 0
        · have hPosUniv :
            PositivelySeparatesIntervalFamily Iuniv zStar := by
            intro z hzIuniv
            let z' : Fin N → ℝ := Function.update z j0 α
            have hz'I :
                ∀ j, z' j ∈ Ising j := by
              intro j
              by_cases hj : j = j0
              · subst hj
                simp [z', Ising]
              · simpa [z', Ising, Iuniv, Function.update, hj] using hzIuniv j
            have hDotEq : dotProduct zStar z' = dotProduct zStar z := by
              rw [dotProduct, dotProduct]
              refine Finset.sum_congr rfl ?_
              intro j hj
              by_cases hji : j = j0
              · subst hji
                simp [z', hzj0]
              · simp [z', Function.update, hji]
            have hPos := hPosSing z' hz'I
            simpa [hDotEq] using hPos
          exact hNoElemSepUniv zStar hzStarOrth hzStarElem hPosUniv
        · rcases hScover zStar hzStarElem with ⟨yRep, hyRepS, c, hc, hzEq⟩
          have hyRepj0 : yRep j0 ≠ 0 := by
            intro hyZero
            have hCoord : zStar j0 = c * yRep j0 := by
              simpa [Pi.smul_apply, smul_eq_mul] using congrArg (fun w => w j0) hzEq
            exact hzj0 (by simpa [hyZero] using hCoord)
          let t : τ := ⟨yRep, ⟨hyRepS, hyRepj0⟩⟩
          rcases hαReduction t with ⟨z, hzj0Alpha, hzRestI, hzZero⟩
          have hzI :
              ∀ j, z j ∈ Ising j := by
            intro j
            by_cases hj : j = j0
            · subst hj
              simpa [Ising, hzj0Alpha]
            · simpa [Ising, Function.update, hj] using hzRestI j hj
          have hyRepEq : yRep = (-(yRep j0)) • eNorm t := by
            ext k
            dsimp [eNorm, t]
            simp [Pi.smul_apply, smul_eq_mul]
            field_simp [hyRepj0]
          have hyRepZero : dotProduct yRep z = 0 := by
            have hEqDot :
                dotProduct yRep z = dotProduct ((-(yRep j0)) • eNorm t) z := by
              exact congrArg (fun w => dotProduct w z) hyRepEq
            calc
              dotProduct yRep z = dotProduct ((-(yRep j0)) • eNorm t) z := hEqDot
              _ = (-(yRep j0)) * dotProduct (eNorm t) z := by
                    simp [smul_eq_mul]
              _ = 0 := by simp [hzZero]
          have hzStarZero : dotProduct zStar z = 0 := by
            calc
              dotProduct zStar z = dotProduct (c • yRep) z := by rw [hzEq]
              _ = c * dotProduct yRep z := by simp [dotProduct_smul, smul_eq_mul]
              _ = 0 := by simp [hyRepZero]
          have hPos := hPosSing z hzI
          have : (0 : ℝ) < 0 := by simpa [hzStarZero] using hPos
          exact (lt_irrefl (0 : ℝ)) this
      rcases ih L Ising hCountSingLe hIsing_interval hIsing_nonempty hNoElemSepSing with
        ⟨z, hzL, hzIsing⟩
      refine ⟨z, hzL, ?_⟩
      intro j
      by_cases hj : j = j0
      · have hzAlpha : z j = α := by
          simpa [Ising, Function.update, hj] using hzIsing j
        have hαIj : α ∈ I j := by
          simpa [hj] using hαI
        exact hzAlpha ▸ hαIj
      · simpa [Ising, Function.update, hj] using hzIsing j

/-- Helper for Theorem 22.6: if no elementary vector of `Lᗮ` positively separates the interval
family, then the primal alternative holds. -/
lemma helperForTheorem_22_6_primal_of_no_elementary_separator
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) (I : Fin N → Set ℝ)
    (hI_interval : ∀ j, Set.OrdConnected (I j))
    (hI_nonempty : ∀ j, (I j).Nonempty)
    (hNoElemSep :
      ∀ zStar : Fin N → ℝ,
        zStar ∈ dotProductOrthogonalComplement L →
        IsElementaryVector (dotProductOrthogonalComplement L) zStar →
        ¬ PositivelySeparatesIntervalFamily I zStar) :
    ∃ z : Fin N → ℝ, z ∈ L ∧ ∀ j, z j ∈ I j := by
  exact
    helperForTheorem_22_6_primal_of_no_elementary_separator_aux
      (n := helperForTheorem_22_6_nontrivialCoordCount I)
      L I (le_rfl : helperForTheorem_22_6_nontrivialCoordCount I ≤
        helperForTheorem_22_6_nontrivialCoordCount I)
      hI_interval hI_nonempty hNoElemSep

-- Proof sketch: interpret alternative (a) as the existence of a point of `L` inside the product
-- of the intervals, and alternative (b) as a strictly positive functional coming from `Lᗮ` on
-- that product. Orthogonality rules out simultaneous occurrence, while the interval-separation
-- argument gives existence of one alternative. If a separator exists, Lemma 22.5 lets one reduce
-- to an elementary vector in `Lᗮ` that still defines the same positive separating ray.

end Section22
end Chap04
