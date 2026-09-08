module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Operations
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Ext

public section

namespace FiniteTaylorJet

universe u v w x

variable {𝕜 : Type u} {E : Type v} {F : Type w} {G : Type x}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/- The degree-zero composition identity is useful independently of the positive-order
   top-coefficient estimates below. -/

/-- Helper for Infrastructure I.16a: composing finite Taylor jets preserves the constant
coefficient of the outer jet. -/
theorem constantCoeff_comp {m : ℕ} (Q : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) :
    (FiniteTaylorJet.comp Q P).constantCoeff = Q.constantCoeff := by
  rw [constantCoeff_eq_coeff_zero, constantCoeff_eq_coeff_zero, coeff_comp]
  have hzero := FormalMultilinearSeries.comp_coeff_zero Q.toFormalMultilinearSeries
    P.toFormalMultilinearSeries (fun _ : Fin 0 ↦ (0 : E)) (fun _ : Fin 0 ↦ (0 : F))
  rw [toFormalMultilinearSeries_coeff_of_le Q (Nat.zero_le m)] at hzero
  exact hzero

/-- Helper for Infrastructure I.16a: the top coefficient of a finite jet composition is the
finite sum of its formal-series composition branches. -/
theorem comp_topCoeff_branch_sum
    {m : ℕ} (Q : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ =
      ∑ c : Composition m,
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries c := by
  rw [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp]

/-- Helper for Infrastructure I.16a: if every outer coefficient of a finite
    Taylor jet vanishes, every coefficient of its composition vanishes. -/
theorem comp_coeff_eq_zero_of_outer_coeff_eq_zero
    {m : ℕ} (Q : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) (n : Fin (m + 1))
    (hQ : ∀ k : Fin (m + 1), Q.coeff k = 0) :
    (FiniteTaylorJet.comp Q P).coeff n = 0 := by
  rw [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp]
  apply Finset.sum_eq_zero
  intro c hc
  have hlengthBound : c.length ≤ (n : ℕ) := c.length_le
  have hlengthOrder : c.length ≤ m :=
    hlengthBound.trans (Nat.le_of_lt_succ n.isLt)
  ext z
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q hlengthOrder,
    hQ ⟨c.length, hlengthBound.trans_lt n.isLt⟩]
  simp

/- Vanishing only through the requested order is the form needed when a finite
   composition is truncated before its ambient top degree. -/

/-- Helper for Infrastructure I.16a: vanishing outer coefficients through a target order
    forces the corresponding composition coefficient to vanish. -/
theorem comp_coeff_eq_zero_of_outer_coeff_eq_zero_below
    {m : ℕ} (Q : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) (n : Fin (m + 1))
    (hQ : ∀ k : Fin (m + 1), (k : ℕ) ≤ (n : ℕ) → Q.coeff k = 0) :
    (FiniteTaylorJet.comp Q P).coeff n = 0 := by
  rw [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp]
  apply Finset.sum_eq_zero
  intro c _
  have hlengthBound : c.length ≤ (n : ℕ) := c.length_le
  have hlengthOrder : c.length ≤ m :=
    hlengthBound.trans (Nat.le_of_lt_succ n.isLt)
  ext z
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q hlengthOrder,
    hQ ⟨c.length, hlengthBound.trans_lt n.isLt⟩ hlengthBound]
  simp

/- Vanishing positive inner coefficients is the dual support form of the
   outer-coefficient zero criterion above. -/

/-- Helper for Infrastructure I.16a: if every positive inner coefficient through a retained
    order vanishes, the corresponding coefficient of any finite-jet composition vanishes. -/
theorem comp_coeff_eq_zero_of_inner_coeff_eq_zero
    {m : ℕ} (Q : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m)
    (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (hP : ∀ k : Fin (m + 1), 0 < (k : ℕ) →
      (k : ℕ) ≤ (n : ℕ) → P.coeff k = 0) :
    (FiniteTaylorJet.comp Q P).coeff n = 0 := by
  rw [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp]
  apply Finset.sum_eq_zero
  intro c _hc
  have hlength_pos : 0 < c.length := c.length_pos_of_pos hn
  let i : Fin c.length := ⟨0, hlength_pos⟩
  have hblock_pos : 0 < c.blocksFun i :=
    lt_of_lt_of_le Nat.zero_lt_one (c.one_le_blocksFun i)
  have hblock_le_n : c.blocksFun i ≤ (n : ℕ) := c.blocksFun_le i
  have hblock_le_m : c.blocksFun i ≤ m :=
    hblock_le_n.trans (Nat.le_of_lt_succ n.isLt)
  have hblock_zero :
      P.toFormalMultilinearSeries (c.blocksFun i) = 0 := by
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P hblock_le_m]
    exact hP ⟨c.blocksFun i, hblock_le_m.trans_lt (Nat.lt_succ_self m)⟩
      hblock_pos hblock_le_n
  ext v
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  apply ContinuousMultilinearMap.map_coord_zero _ i
  dsimp [FormalMultilinearSeries.applyComposition]
  rw [hblock_zero, _root_.zero_apply]

/-- Helper for Infrastructure I.16a: the top coefficient branch sum splits into a chosen
    composition branch and the finite sum of all remaining branches. -/
theorem comp_topCoeff_branch_split
    {m : ℕ} (Q : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ =
      Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) +
        ∑ c : Composition m, if c = Composition.ones m then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c := by
  classical
  rw [comp_topCoeff_branch_sum]
  have hsingle :
      (∑ c : Composition m, if c = Composition.ones m then
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c else 0) =
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) := by
    rw [Finset.sum_ite_eq']
    simp
  calc
    (∑ c : Composition m,
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries c) =
        ∑ c : Composition m,
          ((if c = Composition.ones m then
              Q.toFormalMultilinearSeries.compAlongComposition
                P.toFormalMultilinearSeries c else 0) +
            (if c = Composition.ones m then 0 else
              Q.toFormalMultilinearSeries.compAlongComposition
                P.toFormalMultilinearSeries c)) := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases h : c = Composition.ones m
      · simp [h]
      · simp [h]
    _ = (∑ c : Composition m, if c = Composition.ones m then
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c else 0) +
        ∑ c : Composition m, if c = Composition.ones m then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c := by
      rw [Finset.sum_add_distrib]
    _ = Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) +
        ∑ c : Composition m, if c = Composition.ones m then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c := by
      rw [hsingle]

/- The same branch decomposition is useful at an arbitrary retained coefficient,
   where the selected composition need not be the all-ones branch. -/

/-- Helper for Infrastructure I.16a: a finite-jet composition coefficient splits into a chosen
    composition branch and the finite sum of all remaining branches. -/
theorem comp_coeff_branch_split
    {m : ℕ} (Q : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) (n : Fin (m + 1))
    (distinguished : Composition (n : ℕ)) :
    (FiniteTaylorJet.comp Q P).coeff n =
      Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries distinguished +
        ∑ c : Composition (n : ℕ), if c = distinguished then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c := by
  classical
  rw [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp]
  have hsingle :
      (∑ c : Composition (n : ℕ), if c = distinguished then
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c else 0) =
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries distinguished := by
    rw [Finset.sum_ite_eq']
    simp
  calc
    (∑ c : Composition (n : ℕ),
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries c) =
        ∑ c : Composition (n : ℕ),
          ((if c = distinguished then
              Q.toFormalMultilinearSeries.compAlongComposition
                P.toFormalMultilinearSeries c else 0) +
            (if c = distinguished then 0 else
              Q.toFormalMultilinearSeries.compAlongComposition
                P.toFormalMultilinearSeries c)) := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases h : c = distinguished
      · simp [h]
      · simp [h]
    _ = (∑ c : Composition (n : ℕ), if c = distinguished then
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c else 0) +
        ∑ c : Composition (n : ℕ), if c = distinguished then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c := by
      rw [Finset.sum_add_distrib]
    _ = Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries distinguished +
        ∑ c : Composition (n : ℕ), if c = distinguished then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c := by
      rw [hsingle]

/-- Helper for Infrastructure I.16a: a finite-jet composition coefficient is unchanged when
the outer coefficients and positive inner coefficients agree through that order. -/
theorem comp_coeff_eq_of_eq_below
    {m : ℕ} (Q R : FiniteTaylorJet 𝕜 F G m)
    (P S : FiniteTaylorJet 𝕜 E F m) (n : Fin (m + 1))
    (hQR : ∀ k : Fin (m + 1), (k : ℕ) ≤ (n : ℕ) → Q.coeff k = R.coeff k)
    (hPS : ∀ k : Fin (m + 1), 0 < (k : ℕ) → (k : ℕ) ≤ (n : ℕ) →
      P.coeff k = S.coeff k) :
    (FiniteTaylorJet.comp Q P).coeff n =
      (FiniteTaylorJet.comp R S).coeff n := by
  classical
  rw [FiniteTaylorJet.coeff_comp, FiniteTaylorJet.coeff_comp,
    FormalMultilinearSeries.comp, FormalMultilinearSeries.comp]
  apply Finset.sum_congr rfl
  intro c _
  ext z
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  have hlengthBound : c.length ≤ (n : ℕ) := c.length_le
  have hlengthOrder : c.length ≤ m :=
    hlengthBound.trans (Nat.le_of_lt_succ n.isLt)
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q hlengthOrder,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R hlengthOrder,
    hQR ⟨c.length, hlengthBound.trans_lt n.isLt⟩ hlengthBound]
  congr 1
  funext i
  dsimp only [FormalMultilinearSeries.applyComposition]
  have hblockBound : c.blocksFun i ≤ (n : ℕ) := c.blocksFun_le i
  have hblockOrder : c.blocksFun i ≤ m :=
    hblockBound.trans (Nat.le_of_lt_succ n.isLt)
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P hblockOrder,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le S hblockOrder,
    hPS ⟨c.blocksFun i, hblockBound.trans_lt n.isLt⟩
      (c.one_le_blocksFun i) hblockBound]

/-- Helper for Infrastructure I.16a: if two inner jets agree below a positive top order,
the top coefficient of their common outer composition is the outer linear map
applied to the difference of their top coefficients. -/
theorem comp_topCoeff_sub_eq_inner
    {m : ℕ} (hm : 0 < m) (Q : FiniteTaylorJet 𝕜 F G m)
    (P R : FiniteTaylorJet 𝕜 E F m)
    (hPR : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = R.coeff k) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩ =
      (continuousMultilinearCurryFin1 𝕜 F G
        (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
          (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩) := by
  classical
  rw [FiniteTaylorJet.coeff_comp, FiniteTaylorJet.coeff_comp,
    FormalMultilinearSeries.comp, FormalMultilinearSeries.comp,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (Composition.single m hm)]
  · ext z
    change
      Q.toFormalMultilinearSeries.compAlongComposition P.toFormalMultilinearSeries
          (Composition.single m hm) z -
        Q.toFormalMultilinearSeries.compAlongComposition R.toFormalMultilinearSeries
          (Composition.single m hm) z = _
    rw [FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.applyComposition_single,
      FormalMultilinearSeries.applyComposition_single,
      Composition.single_length,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)),
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P le_rfl,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R le_rfl,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      continuousMultilinearCurryFin1_apply]
    have hPvector : (fun _ : Fin 1 ↦ P.coeff ⟨m, Nat.lt_succ_self m⟩ z) =
        Fin.snoc 0 (P.coeff ⟨m, Nat.lt_succ_self m⟩ z) := by
      funext i
      exact Fin.eq_zero i ▸ rfl
    have hRvector : (fun _ : Fin 1 ↦ R.coeff ⟨m, Nat.lt_succ_self m⟩ z) =
        Fin.snoc 0 (R.coeff ⟨m, Nat.lt_succ_self m⟩ z) := by
      funext i
      exact Fin.eq_zero i ▸ rfl
    rw [hPvector, hRvector, ← continuousMultilinearCurryFin1_apply,
      ← continuousMultilinearCurryFin1_apply, ← map_sub]
    rw [continuousMultilinearCurryFin1_apply]
    rfl
  · intro c _ hc
    rw [sub_eq_zero]
    ext z
    simp only [FormalMultilinearSeries.compAlongComposition_apply]
    congr 1
    funext i
    dsimp only [FormalMultilinearSeries.applyComposition]
    have hblock : c.blocksFun i < m := (Composition.ne_single_iff hm).mp hc i
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P
        ((c.blocksFun_le i).trans (Nat.le_of_lt_succ (Nat.lt_succ_self m))),
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R
        ((c.blocksFun_le i).trans (Nat.le_of_lt_succ (Nat.lt_succ_self m))),
      hPR ⟨c.blocksFun i, hblock.trans (Nat.lt_succ_self m)⟩ hblock]
  · intro hsingle
    exact (hsingle (Finset.mem_univ _)).elim

/- The same one-block isolation works at every positive retained coefficient,
   not only at the ambient top order. -/

/-- Helper for Infrastructure I.16a: at a positive retained order, agreement of two inner jets
    below that order leaves only the one-block composition branch. -/
theorem comp_coeff_sub_eq_inner
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q : FiniteTaylorJet 𝕜 F G m)
    (P R : FiniteTaylorJet 𝕜 E F m)
    (hPR : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → P.coeff k = R.coeff k) :
    (FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp Q R).coeff n =
      (continuousMultilinearCurryFin1 𝕜 F G
        (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
          (P.coeff n - R.coeff n) := by
  classical
  have hn_le : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have hm : 0 < m := lt_of_lt_of_le hn hn_le
  have hone_le : 1 ≤ m := Nat.succ_le_iff.mpr hm
  rw [FiniteTaylorJet.coeff_comp, FiniteTaylorJet.coeff_comp,
    FormalMultilinearSeries.comp, FormalMultilinearSeries.comp,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (Composition.single (n : ℕ) hn)]
  · ext z
    change
      Q.toFormalMultilinearSeries.compAlongComposition P.toFormalMultilinearSeries
          (Composition.single (n : ℕ) hn) z -
        Q.toFormalMultilinearSeries.compAlongComposition R.toFormalMultilinearSeries
          (Composition.single (n : ℕ) hn) z = _
    rw [FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.applyComposition_single,
      FormalMultilinearSeries.applyComposition_single,
      Composition.single_length,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q hone_le,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P hn_le,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R hn_le,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      continuousMultilinearCurryFin1_apply]
    have hPvector : (fun _ : Fin 1 ↦ P.coeff n z) =
        Fin.snoc 0 (P.coeff n z) := by
      funext i
      exact Fin.eq_zero i ▸ rfl
    have hRvector : (fun _ : Fin 1 ↦ R.coeff n z) =
        Fin.snoc 0 (R.coeff n z) := by
      funext i
      exact Fin.eq_zero i ▸ rfl
    rw [hPvector, hRvector, ← continuousMultilinearCurryFin1_apply,
      ← continuousMultilinearCurryFin1_apply, ← map_sub]
    rw [continuousMultilinearCurryFin1_apply]
    rfl
  · intro c _ hc
    rw [sub_eq_zero]
    ext z
    simp only [FormalMultilinearSeries.compAlongComposition_apply]
    congr 1
    funext i
    dsimp only [FormalMultilinearSeries.applyComposition]
    have hlengthBound : c.length ≤ (n : ℕ) := c.length_le
    have hlengthOrder : c.length ≤ m := hlengthBound.trans hn_le
    have hblock : c.blocksFun i < (n : ℕ) :=
      (Composition.ne_single_iff hn).mp hc i
    have hblockBound : c.blocksFun i ≤ m :=
      (c.blocksFun_le i).trans hn_le
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P hblockBound,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R hblockBound,
      hPR ⟨c.blocksFun i, hblock.trans n.isLt⟩ hblock]
  · intro hsingle
    exact (hsingle (Finset.mem_univ _)).elim

/- The projected-inner form retains a lower-order agreement certificate while
   replacing only the inner top coefficient by a second endpoint. -/

/-- Helper for Infrastructure I.16a: replacing an inner jet by a projected jet
    isolates the outer linear top-order term and the remaining projected composition. -/
theorem comp_topCoeff_sub_eq_inner_through_topProjection
    {m : ℕ} (hm : 0 < m) (Q : FiniteTaylorJet 𝕜 F G m)
    (P R Psharp : FiniteTaylorJet 𝕜 E F m)
    (hP : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = Psharp.coeff k)
    (hTop : Psharp.coeff ⟨m, Nat.lt_succ_self m⟩ =
      R.coeff ⟨m, Nat.lt_succ_self m⟩) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩ =
      (continuousMultilinearCurryFin1 𝕜 F G
        (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
          (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩) := by
  have hinner := comp_topCoeff_sub_eq_inner hm Q P Psharp hP
  calc
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩ =
      ((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      abel
    _ = (continuousMultilinearCurryFin1 𝕜 F G
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
            (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              Psharp.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      rw [hinner]
    _ = (continuousMultilinearCurryFin1 𝕜 F G
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
            (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              R.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      rw [hTop]

/- The projected identity is also useful after evaluating all arguments on one direction. -/

/-- Helper for Infrastructure I.16a: evaluating the projected top-coefficient identity on a
    repeated direction preserves the outer linear term and the projected residual term. -/
theorem comp_topCoeff_sub_apply_eq_inner_through_topProjection
    {m : ℕ} (hm : 0 < m) (Q : FiniteTaylorJet 𝕜 F G m)
    (P R Psharp : FiniteTaylorJet 𝕜 E F m)
    (hP : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = Psharp.coeff k)
    (hTop : Psharp.coeff ⟨m, Nat.lt_succ_self m⟩ =
      R.coeff ⟨m, Nat.lt_succ_self m⟩)
    (x : E) :
    ((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩)
        (fun _ : Fin m ↦ x) =
      ((continuousMultilinearCurryFin1 𝕜 F G
        (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
          (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩)) (fun _ : Fin m ↦ x) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩)
          (fun _ : Fin m ↦ x) := by
  have hidentity := comp_topCoeff_sub_eq_inner_through_topProjection
    hm Q P R Psharp hP hTop
  have hvalue := congrArg
    (fun A : E [×m]→L[𝕜] G => A (fun _ : Fin m ↦ x)) hidentity
  simpa only [add_apply] using hvalue

/-- Helper for Infrastructure I.16a: the projected-inner top-coefficient identity
    gives a norm estimate with the outer linear coefficient and projected remainder. -/
theorem norm_comp_topCoeff_sub_le_inner_through_topProjection
    {m : ℕ} (hm : 0 < m) (Q : FiniteTaylorJet 𝕜 F G m)
    (P R Psharp : FiniteTaylorJet 𝕜 E F m)
    (hP : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = Psharp.coeff k)
    (hTop : Psharp.coeff ⟨m, Nat.lt_succ_self m⟩ =
      R.coeff ⟨m, Nat.lt_succ_self m⟩) :
    ‖(FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩‖ ≤
      ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ +
        ‖(FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
  rw [comp_topCoeff_sub_eq_inner_through_topProjection hm Q P R Psharp hP hTop]
  calc
    ‖(continuousMultilinearCurryFin1 𝕜 F G
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
            (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              R.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩)‖ ≤
      ‖(continuousMultilinearCurryFin1 𝕜 F G
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
            (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              R.coeff ⟨m, Nat.lt_succ_self m⟩)‖ +
        ‖(FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩‖ :=
      norm_add_le _ _
    _ ≤ ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ +
          ‖(FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
      have hlinear :
          ‖(continuousMultilinearCurryFin1 𝕜 F G
              (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
                (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
                  R.coeff ⟨m, Nat.lt_succ_self m⟩)‖ ≤
            ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
              ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
                R.coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
        apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans_eq
        rw [LinearIsometryEquiv.norm_map]
      exact add_le_add hlinear le_rfl

/-- Helper for Infrastructure I.16a: the inner top-coefficient variation is bounded by
the norm of the outer linear coefficient times the inner top-coefficient gap. -/
theorem norm_comp_topCoeff_sub_le_inner
    {m : ℕ} (hm : 0 < m) (Q : FiniteTaylorJet 𝕜 F G m)
    (P R : FiniteTaylorJet 𝕜 E F m)
    (hPR : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = R.coeff k) :
    ‖(FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩‖ ≤
      ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
        ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
  rw [comp_topCoeff_sub_eq_inner hm Q P R hPR]
  apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans_eq
  rw [LinearIsometryEquiv.norm_map]

/-- Helper for Infrastructure I.16a: a top-coefficient secant of two finite
compositions splits through the mixed composition obtained by changing the
inner jet first and the outer jet second. -/
theorem comp_topCoeff_sub_decompose
    {m : ℕ} (Q R : FiniteTaylorJet 𝕜 F G m)
    (P S : FiniteTaylorJet 𝕜 E F m) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩ =
      ((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩) := by
  abel

/-- Helper for Infrastructure I.16a: if two outer jets agree below the top order, the top
coefficient of their common inner composition is exactly the all-ones branch
of the outer formal-series difference. -/
theorem comp_topCoeff_sub_eq_outer
    {m : ℕ} (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m)
    (hQR : ∀ k : Fin (m + 1), (k : ℕ) < m → Q.coeff k = R.coeff k) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩ =
      (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m) := by
  classical
  rw [FiniteTaylorJet.coeff_comp, FiniteTaylorJet.coeff_comp,
    FormalMultilinearSeries.comp, FormalMultilinearSeries.comp,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (Composition.ones m)]
  · rfl
  · intro c _ hc
    rw [sub_eq_zero]
    have hlength_ne : c.length ≠ m := by
      intro hlength
      exact hc (Composition.eq_ones_iff_length.mpr hlength)
    have hlength : c.length < m := lt_of_le_of_ne c.length_le hlength_ne
    have hcoeff : Q.toFormalMultilinearSeries c.length =
        R.toFormalMultilinearSeries c.length := by
        rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q
          (c.length_le.trans (Nat.le_of_lt_succ (Nat.lt_succ_self m))),
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R
          (c.length_le.trans (Nat.le_of_lt_succ (Nat.lt_succ_self m))),
        hQR ⟨c.length, hlength.trans (Nat.lt_succ_self m)⟩ hlength]
    rw [FormalMultilinearSeries.compAlongComposition]
    exact congrArg (fun q ↦ q.compAlongComposition P.toFormalMultilinearSeries c) hcoeff
  · intro hsingle
    exact (hsingle (Finset.mem_univ _)).elim

/- The same outer all-ones projection is available at every positive retained
   coefficient, which is useful when a composition is truncated below its ambient order. -/

/-- Helper for Infrastructure I.16a: at a positive retained order, agreement of two outer jets
    below that order leaves only the all-ones composition branch. -/
theorem comp_coeff_sub_eq_outer
    {m : ℕ} (n : Fin (m + 1))
    (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m)
    (hQR : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → Q.coeff k = R.coeff k) :
    (FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp R P).coeff n =
      (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones (n : ℕ)) := by
  classical
  have hn_le : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  rw [FiniteTaylorJet.coeff_comp, FiniteTaylorJet.coeff_comp,
    FormalMultilinearSeries.comp, FormalMultilinearSeries.comp,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (Composition.ones (n : ℕ))]
  · rfl
  · intro c _ hc
    rw [sub_eq_zero]
    have hlength_ne : c.length ≠ (n : ℕ) := by
      intro hlength
      exact hc (Composition.eq_ones_iff_length.mpr hlength)
    have hlength : c.length < (n : ℕ) := lt_of_le_of_ne c.length_le hlength_ne
    have hcoeff : Q.toFormalMultilinearSeries c.length =
        R.toFormalMultilinearSeries c.length := by
      rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q
          (c.length_le.trans hn_le),
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R
          (c.length_le.trans hn_le),
        hQR ⟨c.length, hlength.trans n.isLt⟩ hlength]
    rw [FormalMultilinearSeries.compAlongComposition]
    exact congrArg (fun q ↦ q.compAlongComposition P.toFormalMultilinearSeries c) hcoeff
  · intro hsingle
    exact (hsingle (Finset.mem_univ _)).elim

/- The outer top-coefficient route also needs a stable projection interface:
   the distinguished branch depends only on the top outer coefficient. -/

/-- Helper for Infrastructure I.16a: the all-ones outer branch vanishes when two
outer finite jets have the same top coefficient. -/
theorem comp_topCoeff_outer_ones_eq_zero_of_topCoeff_eq
    {m : ℕ} (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m)
    (hTop : Q.coeff ⟨m, Nat.lt_succ_self m⟩ = R.coeff ⟨m, Nat.lt_succ_self m⟩) :
    (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m) = 0 := by
  ext z
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  have hcoeff :
      (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
          (Composition.ones m).length = 0 := by
    rw [Composition.ones_length]
    change Q.toFormalMultilinearSeries m - R.toFormalMultilinearSeries m = 0
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q le_rfl,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R le_rfl, hTop,
      sub_self]
  simp only [hcoeff, zero_apply]

/-- Helper for Infrastructure I.16a: evaluating the all-ones outer branch on a
constant direction exposes the outer coefficient at the branch length and the
repeated inner linear coefficient. -/
theorem comp_topCoeff_outer_ones_apply
    {m : ℕ} (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) (x : E) :
    ((Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m)) (fun _ : Fin m ↦ x) =
      (Q.toFormalMultilinearSeries (Composition.ones m).length -
        R.toFormalMultilinearSeries (Composition.ones m).length)
        (fun _ : Fin (Composition.ones m).length ↦
          P.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ x)) := by
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  rw [FormalMultilinearSeries.applyComposition_ones]
  rfl

/- The same evaluation identity is independent of the ambient truncation order. -/

/-- Helper for Infrastructure I.16a: evaluating an all-ones outer branch at an arbitrary
retained coefficient exposes the outer coefficient at that branch length and the repeated
inner linear coefficient. -/
theorem comp_coeff_outer_ones_apply
    {m : ℕ} (n : Fin (m + 1))
    (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) (x : E) :
    ((Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones (n : ℕ)))
        (fun _ : Fin (n : ℕ) ↦ x) =
      (Q.toFormalMultilinearSeries (Composition.ones (n : ℕ)).length -
        R.toFormalMultilinearSeries (Composition.ones (n : ℕ)).length)
        (fun _ : Fin (Composition.ones (n : ℕ)).length ↦
          P.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ x)) := by
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  rw [FormalMultilinearSeries.applyComposition_ones]
  rfl

/- The coefficient-level form removes the formal-series wrappers from the same branch. -/

/-- Helper for Infrastructure I.16a: an arbitrary all-ones branch evaluated on a repeated input
is exactly the outer coefficient gap applied to repeated inner linear coefficients. -/
theorem comp_coeff_outer_ones_apply_eq_coeff
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) (x : E) :
    ((Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones (n : ℕ)))
        (fun _ : Fin (n : ℕ) ↦ x) =
      (Q.coeff n - R.coeff n)
        (fun _ : Fin (n : ℕ) ↦
          P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
            (Nat.le_of_lt_succ n.isLt))⟩
            (fun _ : Fin 1 ↦ x)) := by
  have hn_le : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have hm : 0 < m := lt_of_lt_of_le hn hn_le
  have hone : 1 ≤ m := Nat.succ_le_iff.mpr hm
  rw [comp_coeff_outer_ones_apply n Q R P x, Composition.ones_length]
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q hn_le,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R hn_le]
  congr 1
  funext i
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P hone]

/- The corresponding arbitrary-order branch estimate keeps the retained degree explicit. -/

/-- Helper for Infrastructure I.16a: the all-ones blocks at an arbitrary retained degree select
the inner linear coefficient, so their norms multiply to the retained-degree power. -/
theorem norm_formal_onesProduct_general
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (P : FiniteTaylorJet 𝕜 E F m) :
    ∏ i, ‖P.toFormalMultilinearSeries
        ((Composition.ones (n : ℕ)).blocksFun i)‖ =
      ‖P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
        (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) := by
  have hn_le : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have hm : 0 < m := lt_of_lt_of_le hn hn_le
  calc
    ∏ i, ‖P.toFormalMultilinearSeries
        ((Composition.ones (n : ℕ)).blocksFun i)‖ =
        ∏ _i : Fin (Composition.ones (n : ℕ)).length,
          ‖P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn hn_le)⟩‖ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Composition.ones_blocksFun,
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))]
    _ = ‖P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn hn_le)⟩‖ ^ (n : ℕ) := by
      simp only [Finset.prod_const, Finset.card_fin, Composition.ones_length]

/-- Helper for Infrastructure I.16a: the norm of an arbitrary retained all-ones branch is bounded
by the outer coefficient gap times the corresponding power of the inner linear coefficient. -/
theorem norm_comp_coeff_outer_ones_le
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) :
    ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones (n : ℕ))‖ ≤
      ‖Q.coeff n - R.coeff n‖ *
        ‖P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
          (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) := by
  have hn_le : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have hm : 0 < m := lt_of_lt_of_le hn hn_le
  have hone_le : 1 ≤ m := Nat.succ_le_iff.mpr hm
  have houter :
      ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
          (Composition.ones (n : ℕ)).length‖ = ‖Q.coeff n - R.coeff n‖ := by
    rw [Composition.ones_length]
    change ‖Q.toFormalMultilinearSeries (n : ℕ) -
      R.toFormalMultilinearSeries (n : ℕ)‖ = _
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q hn_le,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R hn_le]
  have hproduct :
      ∏ i, ‖P.toFormalMultilinearSeries
          ((Composition.ones (n : ℕ)).blocksFun i)‖ =
        ‖P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn hn_le)⟩‖ ^ (n : ℕ) := by
    apply (norm_formal_onesProduct_general n hn P)
  calc
    ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ))‖ ≤
        ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
            (Composition.ones (n : ℕ)).length‖ *
          ∏ i, ‖P.toFormalMultilinearSeries
            ((Composition.ones (n : ℕ)).blocksFun i)‖ :=
      FormalMultilinearSeries.compAlongComposition_norm _ _ _
    _ = ‖Q.coeff n - R.coeff n‖ *
        ‖P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn hn_le)⟩‖ ^ (n : ℕ) := by
      rw [houter, hproduct]

/- Product-valued inner jets can be threaded through both projections at any retained order. -/

/-- Helper for Infrastructure I.16a: a lower-equal product-valued inner variation passes through
an outer jet and a scalar reindexing jet at an arbitrary positive retained coefficient. -/
theorem comp_prod_comp_coeff_sub_eq_inner_of_lower
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q : FiniteTaylorJet 𝕜 (𝕜 × X) Y m)
    (C : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (P R : FiniteTaylorJet 𝕜 𝕜 X m)
    (I : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (hPR : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → P.coeff k = R.coeff k) :
    (((FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) I).coeff n -
        (FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)) I).coeff n)
      (fun _ : Fin (n : ℕ) ↦ 1)) =
      ((I.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ 1)) ^ (n : ℕ)) •
        (continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
          (Q.toFormalMultilinearSeries 1))
          (0, (P.coeff n - R.coeff n) (fun _ : Fin (n : ℕ) ↦ 1)) := by
  classical
  have hn_le : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have hm : 0 < m := lt_of_lt_of_le hn hn_le
  have hprod_lower (k : Fin (m + 1)) (hk : (k : ℕ) < (n : ℕ)) :
      (FiniteTaylorJet.prod C P).coeff k =
        (FiniteTaylorJet.prod C R).coeff k := by
    rw [FiniteTaylorJet.coeff_prod, FiniteTaylorJet.coeff_prod, hPR k hk]
  have hinner := comp_coeff_sub_eq_inner n hn Q
    (FiniteTaylorJet.prod C P) (FiniteTaylorJet.prod C R) hprod_lower
  have hinner_lower (k : Fin (m + 1)) (hk : (k : ℕ) < (n : ℕ)) :
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)).coeff k =
        (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)).coeff k := by
    apply comp_coeff_eq_of_eq_below
    · intro j _hj
      rfl
    · intro j _hj_pos hj_le
      exact hprod_lower j (hj_le.trans_lt hk)
  have houter := comp_coeff_sub_eq_outer
    n (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P))
    (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)) I hinner_lower
  rw [houter, comp_coeff_outer_ones_apply, Composition.ones_length]
  have hone_le : 1 ≤ m := Nat.succ_le_iff.mpr hm
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) hn_le,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)) hn_le,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le I hone_le,
    hinner, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  simp only [FiniteTaylorJet.coeff_prod, ContinuousMultilinearMap.prod_apply,
    sub_apply]
  have hscale :=
    ((FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)).coeff n -
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)).coeff n).map_smul_univ
      (fun _ : Fin (n : ℕ) ↦
        I.coeff ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ 1))
      (fun _ : Fin (n : ℕ) ↦ (1 : 𝕜))
  rw [hinner, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply] at hscale
  simp only [FiniteTaylorJet.coeff_prod, ContinuousMultilinearMap.prod_apply,
    sub_apply] at hscale
  simp at hscale ⊢
  simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin,
    continuousMultilinearCurryFin1_apply] using hscale

/-- Helper for Infrastructure I.16a: the arbitrary-order product-composition projection has a
repeated-input norm bound separating the scalar reindexing factor, the outer linear coefficient,
and the retained inner coefficient gap. -/
theorem norm_comp_prod_comp_coeff_sub_apply_le_inner_of_lower
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q : FiniteTaylorJet 𝕜 (𝕜 × X) Y m)
    (C : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (P R : FiniteTaylorJet 𝕜 𝕜 X m)
    (I : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (hPR : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → P.coeff k = R.coeff k) :
    ‖(((FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) I).coeff n -
        (FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)) I).coeff n)
      (fun _ : Fin (n : ℕ) ↦ 1))‖ ≤
      ‖I.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ 1)‖ ^ (n : ℕ) *
        ‖Q.toFormalMultilinearSeries 1‖ *
          ‖(P.coeff n - R.coeff n) (fun _ : Fin (n : ℕ) ↦ 1)‖ := by
  rw [comp_prod_comp_coeff_sub_eq_inner_of_lower n hn Q C P R I hPR]
  rw [norm_smul, norm_pow]
  let hdiff := (P.coeff n - R.coeff n) (fun _ : Fin (n : ℕ) ↦ 1)
  have hlinear :
      ‖(continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
          (Q.toFormalMultilinearSeries 1)) (0, hdiff)‖ ≤
        ‖Q.toFormalMultilinearSeries 1‖ * ‖hdiff‖ := by
    calc
      ‖(continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
            (Q.toFormalMultilinearSeries 1)) (0, hdiff)‖ ≤
          ‖continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
              (Q.toFormalMultilinearSeries 1)‖ * ‖(0, hdiff)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖Q.toFormalMultilinearSeries 1‖ * ‖hdiff‖ := by
        rw [LinearIsometryEquiv.norm_map]
        simp only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
  calc
    ‖I.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ 1)‖ ^ (n : ℕ) *
          ‖(continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
            (Q.toFormalMultilinearSeries 1))
            (0, hdiff)‖ ≤
        ‖I.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ 1)‖ ^ (n : ℕ) *
          (‖Q.toFormalMultilinearSeries 1‖ *
            ‖hdiff‖) :=
      mul_le_mul_of_nonneg_left hlinear
        (pow_nonneg (norm_nonneg _) _)
    _ = ‖I.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ 1)‖ ^ (n : ℕ) *
          ‖Q.toFormalMultilinearSeries 1‖ *
          ‖hdiff‖ := by
      ring

/-- Helper for Infrastructure I.16a: replacing an outer jet through an arbitrary retained
coefficient isolates its all-ones branch from the residual with the projected outer jet. -/
theorem comp_coeff_sub_eq_outer_through_topProjection
    {m : ℕ} (n : Fin (m + 1))
    (Q R Q' : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m)
    (hQ'lower : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → Q'.coeff k = Q.coeff k)
    (hQ'n : Q'.coeff n = R.coeff n) :
    (FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp R P).coeff n =
      (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ)) +
        ((FiniteTaylorJet.comp Q' P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n) := by
  have houter :
      (FiniteTaylorJet.comp Q P).coeff n -
          (FiniteTaylorJet.comp Q' P).coeff n =
        (Q.toFormalMultilinearSeries - Q'.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ)) :=
    comp_coeff_sub_eq_outer n Q Q' P
      (fun k hk ↦ (hQ'lower k hk).symm)
  have hn_le : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have hbranch :
      (Q.toFormalMultilinearSeries - Q'.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ)) =
        (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ)) := by
    ext z
    rw [FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.compAlongComposition_apply]
    have hcoeff :
        (Q.toFormalMultilinearSeries - Q'.toFormalMultilinearSeries)
            (Composition.ones (n : ℕ)).length =
          (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
            (Composition.ones (n : ℕ)).length := by
      rw [Composition.ones_length]
      change Q.toFormalMultilinearSeries (n : ℕ) - Q'.toFormalMultilinearSeries (n : ℕ) =
        Q.toFormalMultilinearSeries (n : ℕ) - R.toFormalMultilinearSeries (n : ℕ)
      rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q hn_le,
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q' hn_le,
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R hn_le, hQ'n]
    exact congrArg
      (fun A : F [×(Composition.ones (n : ℕ)).length]→L[𝕜] G ↦
        A (P.toFormalMultilinearSeries.applyComposition
          (Composition.ones (n : ℕ)) z)) hcoeff
  calc
    (FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp R P).coeff n =
      ((FiniteTaylorJet.comp Q P).coeff n -
          (FiniteTaylorJet.comp Q' P).coeff n) +
        ((FiniteTaylorJet.comp Q' P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n) := by
      abel
    _ = (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ)) +
        ((FiniteTaylorJet.comp Q' P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n) := by
      rw [houter, hbranch]

/-- Helper for Infrastructure I.16a: the arbitrary-order outer projection decomposition has a norm
bound given by the all-ones coefficient gap and the projected composition residual. -/
theorem norm_comp_coeff_sub_le_outer_through_topProjection
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q R Q' : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m)
    (hQ'lower : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → Q'.coeff k = Q.coeff k)
    (hQ'n : Q'.coeff n = R.coeff n) :
    ‖(FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp R P).coeff n‖ ≤
      ‖Q.coeff n - R.coeff n‖ *
          ‖P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
            (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) +
        ‖(FiniteTaylorJet.comp Q' P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n‖ := by
  rw [comp_coeff_sub_eq_outer_through_topProjection n Q R Q' P hQ'lower hQ'n]
  calc
    ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ)) +
        ((FiniteTaylorJet.comp Q' P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n)‖ ≤
      ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ))‖ +
        ‖(FiniteTaylorJet.comp Q' P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n‖ :=
      norm_add_le _ _
    _ ≤ ‖Q.coeff n - R.coeff n‖ *
          ‖P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
            (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) +
        ‖(FiniteTaylorJet.comp Q' P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n‖ := by
      exact add_le_add (norm_comp_coeff_outer_ones_le n hn Q R P) le_rfl

/-- Helper for Infrastructure I.16a: evaluating the arbitrary-order outer projection estimate on a
repeated input contributes exactly the retained-degree power of the input norm. -/
theorem norm_comp_coeff_sub_apply_le_outer_through_topProjection
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q R Q' : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m)
    (hQ'lower : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → Q'.coeff k = Q.coeff k)
    (hQ'n : Q'.coeff n = R.coeff n) (x : E) :
    ‖((FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp R P).coeff n) (fun _ : Fin (n : ℕ) ↦ x)‖ ≤
      (‖Q.coeff n - R.coeff n‖ *
          ‖P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
            (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) +
        ‖(FiniteTaylorJet.comp Q' P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n‖) *
        ‖x‖ ^ (n : ℕ) := by
  have hoperator := norm_comp_coeff_sub_le_outer_through_topProjection
    n hn Q R Q' P hQ'lower hQ'n
  have hproduct_nonneg : 0 ≤ ∏ _ : Fin (n : ℕ), ‖x‖ := by
    exact Finset.prod_nonneg (fun _ _ ↦ norm_nonneg x)
  calc
    ‖((FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp R P).coeff n) (fun _ : Fin (n : ℕ) ↦ x)‖ ≤
      ‖(FiniteTaylorJet.comp Q P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n‖ *
        ∏ _ : Fin (n : ℕ), ‖x‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ ≤
      (‖Q.coeff n - R.coeff n‖ *
          ‖P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
            (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) +
        ‖(FiniteTaylorJet.comp Q' P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n‖) *
        ∏ _ : Fin (n : ℕ), ‖x‖ := by
      exact mul_le_mul_of_nonneg_right hoperator hproduct_nonneg
    _ =
      (‖Q.coeff n - R.coeff n‖ *
          ‖P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
            (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) +
        ‖(FiniteTaylorJet.comp Q' P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n‖) *
        ‖x‖ ^ (n : ℕ) := by
      simp

/- A scalar reindexing jet can be placed outside an outer variation whose
   lower coefficients already agree. -/

/-- Helper for Infrastructure I.16a: positivity of a retained coefficient implies positivity
of the ambient finite-jet order. -/
theorem ambientOrder_pos_of_index_pos
    {m : ℕ} {n : Fin (m + 1)} (hn : 0 < (n : ℕ)) : 0 < m := by
  exact lt_of_lt_of_le hn (Nat.le_of_lt_succ n.isLt)

/- A scalar reindexing jet can be evaluated after the inner all-ones branch. -/

/-- Helper for Infrastructure I.16a: a nested scalar composition evaluates the outer
coefficient gap on the inner linear coefficient after the scalar reindexing linear coefficient. -/
theorem comp_comp_coeff_sub_apply_eq_outer_of_lower
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 𝕜 F m)
    (I : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (hQR : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → Q.coeff k = R.coeff k)
    (x : 𝕜) :
    (((FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q P) I).coeff n -
        (FiniteTaylorJet.comp
          (FiniteTaylorJet.comp R P) I).coeff n)
      (fun _ : Fin (n : ℕ) ↦ x)) =
      (Q.coeff n - R.coeff n)
        (fun _ : Fin (n : ℕ) ↦
          P.coeff ⟨1, Nat.succ_lt_succ
            (ambientOrder_pos_of_index_pos (m := m) (n := n) hn)⟩
            (fun _ : Fin 1 ↦
              I.coeff ⟨1, Nat.succ_lt_succ
                (ambientOrder_pos_of_index_pos (m := m) (n := n) hn)⟩
                (fun _ : Fin 1 ↦ x))) := by
  let y : 𝕜 := I.coeff ⟨1, Nat.succ_lt_succ
      (ambientOrder_pos_of_index_pos (m := m) (n := n) hn)⟩
      (fun _ : Fin 1 ↦ x)
  have hinner_lower (k : Fin (m + 1)) (hk : (k : ℕ) < (n : ℕ)) :
      (FiniteTaylorJet.comp Q P).coeff k =
        (FiniteTaylorJet.comp R P).coeff k := by
    apply comp_coeff_eq_of_eq_below
    · intro j hj
      exact hQR j (lt_of_le_of_lt hj hk)
    · intro j _hj_pos _hj_le
      rfl
  have houter := comp_coeff_sub_eq_outer n
    (FiniteTaylorJet.comp Q P) (FiniteTaylorJet.comp R P) I hinner_lower
  have houter_eval := congrArg
    (fun A ↦ A (fun _ : Fin (n : ℕ) ↦ x)) houter
  have houter_branch := comp_coeff_outer_ones_apply_eq_coeff n hn
    (FiniteTaylorJet.comp Q P) (FiniteTaylorJet.comp R P) I x
  have hinner := comp_coeff_sub_eq_outer n Q R P hQR
  have hinner_eval := congrArg
    (fun A ↦ A (fun _ : Fin (n : ℕ) ↦ y)) hinner
  have hbranch := comp_coeff_outer_ones_apply_eq_coeff n hn Q R P y
  calc
    (((FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q P) I).coeff n -
        (FiniteTaylorJet.comp
          (FiniteTaylorJet.comp R P) I).coeff n)
      (fun _ : Fin (n : ℕ) ↦ x)) =
        (((FiniteTaylorJet.comp Q P).toFormalMultilinearSeries -
          (FiniteTaylorJet.comp R P).toFormalMultilinearSeries).compAlongComposition
          I.toFormalMultilinearSeries (Composition.ones (n : ℕ)))
          (fun _ : Fin (n : ℕ) ↦ x) := by
      simpa using houter_eval
    _ = ((FiniteTaylorJet.comp Q P).coeff n -
          (FiniteTaylorJet.comp R P).coeff n)
          (fun _ : Fin (n : ℕ) ↦ y) := by
      simpa [y] using houter_branch
    _ = ((Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ)))
          (fun _ : Fin (n : ℕ) ↦ y) := by
      simpa using hinner_eval
    _ = (Q.coeff n - R.coeff n)
          (fun _ : Fin (n : ℕ) ↦
            P.coeff ⟨1, Nat.succ_lt_succ
              (ambientOrder_pos_of_index_pos (m := m) (n := n) hn)⟩
              (fun _ : Fin 1 ↦ y)) := by
      simpa using hbranch
    _ = (Q.coeff n - R.coeff n)
          (fun _ : Fin (n : ℕ) ↦
            P.coeff ⟨1, Nat.succ_lt_succ
              (ambientOrder_pos_of_index_pos (m := m) (n := n) hn)⟩
              (fun _ : Fin 1 ↦
                I.coeff ⟨1, Nat.succ_lt_succ
                  (ambientOrder_pos_of_index_pos (m := m) (n := n) hn)⟩
                  (fun _ : Fin 1 ↦ x))) := by
      rfl

/-- Helper for Infrastructure I.16a: a nested scalar composition transports a lower-equal
outer top-coefficient bound to repeated inputs with explicit inner and reindexing factors. -/
theorem norm_comp_comp_coeff_sub_apply_le_outer_of_lower
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 𝕜 F m)
    (I : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (hQR : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → Q.coeff k = R.coeff k)
    (x : 𝕜) :
    ‖(((FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q P) I).coeff n -
        (FiniteTaylorJet.comp
          (FiniteTaylorJet.comp R P) I).coeff n)
      (fun _ : Fin (n : ℕ) ↦ x))‖ ≤
      ‖Q.coeff n - R.coeff n‖ *
        ‖P.coeff ⟨1, Nat.succ_lt_succ
          (ambientOrder_pos_of_index_pos (m := m) (n := n) hn)⟩‖ ^ (n : ℕ) *
        ‖I.coeff ⟨1, Nat.succ_lt_succ
          (ambientOrder_pos_of_index_pos (m := m) (n := n) hn)⟩
          (fun _ : Fin 1 ↦ x)‖ ^ (n : ℕ) := by
  have hinner_lower (k : Fin (m + 1)) (hk : (k : ℕ) < (n : ℕ)) :
      (FiniteTaylorJet.comp Q P).coeff k =
        (FiniteTaylorJet.comp R P).coeff k := by
    apply comp_coeff_eq_of_eq_below
    · intro j hj
      exact hQR j (lt_of_le_of_lt hj hk)
    · intro j _hj_pos _hj_le
      rfl
  have houter := comp_coeff_sub_eq_outer n
    (FiniteTaylorJet.comp Q P) (FiniteTaylorJet.comp R P) I hinner_lower
  have hinner_bound := norm_comp_coeff_sub_apply_le_outer_through_topProjection
    (m := m) n hn Q R R P (fun k hk ↦ (hQR k hk).symm) rfl
    (I.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
      (Nat.le_of_lt_succ n.isLt))⟩ (fun _ : Fin 1 ↦ x))
  rw [houter, comp_coeff_outer_ones_apply_eq_coeff n hn]
  simpa [sub_self, add_zero, mul_assoc] using hinner_bound

/-- Helper for Infrastructure I.16a: simultaneous inner and outer coefficient changes split into
the inner one-block term, the projected inner residual, the outer all-ones branch, and the
projected outer residual at any positive retained order. -/
theorem comp_coeff_sub_decompose_through_projections
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q R Qsharp : FiniteTaylorJet 𝕜 F G m)
    (P S Psharp : FiniteTaylorJet 𝕜 E F m)
    (hP : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → P.coeff k = Psharp.coeff k)
    (hPtop : Psharp.coeff n = S.coeff n)
    (hQ : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → Qsharp.coeff k = Q.coeff k)
    (hQtop : Qsharp.coeff n = R.coeff n) :
    (FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp R S).coeff n =
      (continuousMultilinearCurryFin1 𝕜 F G
        (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
          (P.coeff n - S.coeff n) +
        ((FiniteTaylorJet.comp Q Psharp).coeff n -
          (FiniteTaylorJet.comp Q S).coeff n) +
        (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones (n : ℕ)) +
        ((FiniteTaylorJet.comp Qsharp S).coeff n -
          (FiniteTaylorJet.comp R S).coeff n) := by
  have hinner := comp_coeff_sub_eq_inner n hn Q P Psharp hP
  have hinner' :
      (FiniteTaylorJet.comp Q P).coeff n -
          (FiniteTaylorJet.comp Q Psharp).coeff n =
        (continuousMultilinearCurryFin1 𝕜 F G
          (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
            (P.coeff n - S.coeff n) := by
    rw [hinner, hPtop]
  have houter := comp_coeff_sub_eq_outer_through_topProjection
    n Q R Qsharp S hQ hQtop
  calc
    (FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp R S).coeff n =
      ((FiniteTaylorJet.comp Q P).coeff n -
          (FiniteTaylorJet.comp Q Psharp).coeff n) +
        ((FiniteTaylorJet.comp Q Psharp).coeff n -
          (FiniteTaylorJet.comp Q S).coeff n) +
        ((FiniteTaylorJet.comp Q S).coeff n -
          (FiniteTaylorJet.comp R S).coeff n) := by
      abel
    _ =
      (((continuousMultilinearCurryFin1 𝕜 F G
        (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
          (P.coeff n - S.coeff n)) +
        ((FiniteTaylorJet.comp Q Psharp).coeff n -
          (FiniteTaylorJet.comp Q S).coeff n)) +
        ((Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones (n : ℕ)) +
        ((FiniteTaylorJet.comp Qsharp S).coeff n -
          (FiniteTaylorJet.comp R S).coeff n)) := by
      rw [hinner', houter]
    _ =
      (continuousMultilinearCurryFin1 𝕜 F G
        (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
          (P.coeff n - S.coeff n) +
        ((FiniteTaylorJet.comp Q Psharp).coeff n -
          (FiniteTaylorJet.comp Q S).coeff n) +
        (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones (n : ℕ)) +
        ((FiniteTaylorJet.comp Qsharp S).coeff n -
          (FiniteTaylorJet.comp R S).coeff n) := by
      abel

/-- Helper for Infrastructure I.16a: the simultaneous arbitrary-order projection decomposition has
a four-term norm estimate, with the two distinguished branches isolated explicitly. -/
theorem norm_comp_coeff_sub_le_decompose_through_projections
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q R Qsharp : FiniteTaylorJet 𝕜 F G m)
    (P S Psharp : FiniteTaylorJet 𝕜 E F m)
    (hP : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → P.coeff k = Psharp.coeff k)
    (hPtop : Psharp.coeff n = S.coeff n)
    (hQ : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → Qsharp.coeff k = Q.coeff k)
    (hQtop : Qsharp.coeff n = R.coeff n) :
    ‖(FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp R S).coeff n‖ ≤
      ‖Q.toFormalMultilinearSeries 1‖ * ‖P.coeff n - S.coeff n‖ +
        ‖(FiniteTaylorJet.comp Q Psharp).coeff n -
          (FiniteTaylorJet.comp Q S).coeff n‖ +
        ‖Q.coeff n - R.coeff n‖ *
          ‖S.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
            (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) +
        ‖(FiniteTaylorJet.comp Qsharp S).coeff n -
          (FiniteTaylorJet.comp R S).coeff n‖ := by
  have hdecomp := comp_coeff_sub_decompose_through_projections
    n hn Q R Qsharp P S Psharp hP hPtop hQ hQtop
  rw [hdecomp]
  have hinner :
      ‖(continuousMultilinearCurryFin1 𝕜 F G
          (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
        (P.coeff n - S.coeff n)‖ ≤
        ‖Q.toFormalMultilinearSeries 1‖ * ‖P.coeff n - S.coeff n‖ := by
    apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans_eq
    rw [LinearIsometryEquiv.norm_map]
  have hbranch := norm_comp_coeff_outer_ones_le n hn Q R S
  calc
    ‖(continuousMultilinearCurryFin1 𝕜 F G
          (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
        (P.coeff n - S.coeff n) +
        ((FiniteTaylorJet.comp Q Psharp).coeff n -
          (FiniteTaylorJet.comp Q S).coeff n) +
        (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones (n : ℕ)) +
        ((FiniteTaylorJet.comp Qsharp S).coeff n -
          (FiniteTaylorJet.comp R S).coeff n)‖ ≤
      ‖(continuousMultilinearCurryFin1 𝕜 F G
          (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
        (P.coeff n - S.coeff n)‖ +
        ‖(FiniteTaylorJet.comp Q Psharp).coeff n -
          (FiniteTaylorJet.comp Q S).coeff n‖ +
        ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones (n : ℕ))‖ +
        ‖(FiniteTaylorJet.comp Qsharp S).coeff n -
          (FiniteTaylorJet.comp R S).coeff n‖ := by
      calc
        _ ≤ ‖(continuousMultilinearCurryFin1 𝕜 F G
              (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
            (P.coeff n - S.coeff n) +
              ((FiniteTaylorJet.comp Q Psharp).coeff n -
                (FiniteTaylorJet.comp Q S).coeff n) +
            (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
              S.toFormalMultilinearSeries (Composition.ones (n : ℕ))‖ +
            ‖(FiniteTaylorJet.comp Qsharp S).coeff n -
              (FiniteTaylorJet.comp R S).coeff n‖ := norm_add_le _ _
        _ ≤
            (‖(continuousMultilinearCurryFin1 𝕜 F G
                (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
              (P.coeff n - S.coeff n) +
              ((FiniteTaylorJet.comp Q Psharp).coeff n -
                (FiniteTaylorJet.comp Q S).coeff n)‖) +
            ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
              S.toFormalMultilinearSeries (Composition.ones (n : ℕ))‖ +
            ‖(FiniteTaylorJet.comp Qsharp S).coeff n -
              (FiniteTaylorJet.comp R S).coeff n‖ := by
          apply add_le_add_left
          exact norm_add_le
            ((continuousMultilinearCurryFin1 𝕜 F G
                (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
              (P.coeff n - S.coeff n) +
              ((FiniteTaylorJet.comp Q Psharp).coeff n -
                (FiniteTaylorJet.comp Q S).coeff n))
            ((Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
              S.toFormalMultilinearSeries (Composition.ones (n : ℕ)))
        _ ≤
            (‖(continuousMultilinearCurryFin1 𝕜 F G
                (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
              (P.coeff n - S.coeff n)‖ +
              ‖(FiniteTaylorJet.comp Q Psharp).coeff n -
                (FiniteTaylorJet.comp Q S).coeff n‖) +
            ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
              S.toFormalMultilinearSeries (Composition.ones (n : ℕ))‖ +
            ‖(FiniteTaylorJet.comp Qsharp S).coeff n -
              (FiniteTaylorJet.comp R S).coeff n‖ := by
          apply add_le_add_left
          exact add_le_add_left
            (norm_add_le
              ((continuousMultilinearCurryFin1 𝕜 F G
                  (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
                (P.coeff n - S.coeff n))
              ((FiniteTaylorJet.comp Q Psharp).coeff n -
                (FiniteTaylorJet.comp Q S).coeff n)) _
        _ =
            ‖(continuousMultilinearCurryFin1 𝕜 F G
                (Q.toFormalMultilinearSeries 1)).compContinuousMultilinearMap
              (P.coeff n - S.coeff n)‖ +
              ‖(FiniteTaylorJet.comp Q Psharp).coeff n -
                (FiniteTaylorJet.comp Q S).coeff n‖ +
            ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
              S.toFormalMultilinearSeries (Composition.ones (n : ℕ))‖ +
            ‖(FiniteTaylorJet.comp Qsharp S).coeff n -
              (FiniteTaylorJet.comp R S).coeff n‖ := by
          ring
    _ ≤
        ‖Q.toFormalMultilinearSeries 1‖ * ‖P.coeff n - S.coeff n‖ +
          ‖(FiniteTaylorJet.comp Q Psharp).coeff n -
            (FiniteTaylorJet.comp Q S).coeff n‖ +
          ‖Q.coeff n - R.coeff n‖ *
            ‖S.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
              (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) +
          ‖(FiniteTaylorJet.comp Qsharp S).coeff n -
            (FiniteTaylorJet.comp R S).coeff n‖ := by
      exact add_le_add (add_le_add (add_le_add hinner le_rfl) hbranch) le_rfl

/- The four-term operator estimate is often consumed on a repeated direction,
   as in an all-ones composition branch. -/

/-- Helper for Infrastructure I.16a: evaluating the simultaneous projection estimate on a
repeated direction multiplies the four coefficient bounds by the corresponding direction power. -/
theorem norm_comp_coeff_sub_apply_le_decompose_through_projections
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q R Qsharp : FiniteTaylorJet 𝕜 F G m)
    (P S Psharp : FiniteTaylorJet 𝕜 E F m)
    (hP : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → P.coeff k = Psharp.coeff k)
    (hPtop : Psharp.coeff n = S.coeff n)
    (hQ : ∀ k : Fin (m + 1), (k : ℕ) < (n : ℕ) → Qsharp.coeff k = Q.coeff k)
    (hQtop : Qsharp.coeff n = R.coeff n)
    (x : E) :
    ‖((FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp R S).coeff n)
        (fun _ : Fin (n : ℕ) ↦ x)‖ ≤
      (‖Q.toFormalMultilinearSeries 1‖ * ‖P.coeff n - S.coeff n‖ +
        ‖(FiniteTaylorJet.comp Q Psharp).coeff n -
          (FiniteTaylorJet.comp Q S).coeff n‖ +
        ‖Q.coeff n - R.coeff n‖ *
          ‖S.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
            (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) +
        ‖(FiniteTaylorJet.comp Qsharp S).coeff n -
          (FiniteTaylorJet.comp R S).coeff n‖) *
        ‖x‖ ^ (n : ℕ) := by
  have hoperator := norm_comp_coeff_sub_le_decompose_through_projections
    n hn Q R Qsharp P S Psharp hP hPtop hQ hQtop
  have hproduct_nonneg : 0 ≤ ∏ _ : Fin (n : ℕ), ‖x‖ := by
    exact Finset.prod_nonneg (fun _ _ ↦ norm_nonneg x)
  calc
    ‖((FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp R S).coeff n)
        (fun _ : Fin (n : ℕ) ↦ x)‖ ≤
        ‖(FiniteTaylorJet.comp Q P).coeff n -
          (FiniteTaylorJet.comp R S).coeff n‖ *
          ∏ _ : Fin (n : ℕ), ‖x‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ ≤
        (‖Q.toFormalMultilinearSeries 1‖ * ‖P.coeff n - S.coeff n‖ +
          ‖(FiniteTaylorJet.comp Q Psharp).coeff n -
            (FiniteTaylorJet.comp Q S).coeff n‖ +
          ‖Q.coeff n - R.coeff n‖ *
          ‖S.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
              (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) +
          ‖(FiniteTaylorJet.comp Qsharp S).coeff n -
            (FiniteTaylorJet.comp R S).coeff n‖) *
          ∏ _ : Fin (n : ℕ), ‖x‖ := by
      exact mul_le_mul_of_nonneg_right hoperator hproduct_nonneg
    _ =
        (‖Q.toFormalMultilinearSeries 1‖ * ‖P.coeff n - S.coeff n‖ +
          ‖(FiniteTaylorJet.comp Q Psharp).coeff n -
            (FiniteTaylorJet.comp Q S).coeff n‖ +
          ‖Q.coeff n - R.coeff n‖ *
          ‖S.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
              (Nat.le_of_lt_succ n.isLt))⟩‖ ^ (n : ℕ) +
          ‖(FiniteTaylorJet.comp Qsharp S).coeff n -
            (FiniteTaylorJet.comp R S).coeff n‖) *
          ‖x‖ ^ (n : ℕ) := by
      simp

/- A common inner linear coefficient cancels the distinguished branch at every positive
   retained coefficient, not only at the ambient top degree. -/

/-- Helper for Infrastructure I.16a: when two inner jets have the same linear coefficient, an
arbitrary positive composition coefficient difference is exactly the sum of its non-all-ones
branches. -/
theorem comp_coeff_sub_eq_nonOnes_of_inner_linear_eq
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q : FiniteTaylorJet 𝕜 F G m)
    (P S : FiniteTaylorJet 𝕜 E F m)
    (hlinear :
      P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
        (Nat.le_of_lt_succ n.isLt))⟩ =
        S.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
          (Nat.le_of_lt_succ n.isLt))⟩) :
    (FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp Q S).coeff n =
      ∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) := by
  have hn_le : (n : ℕ) ≤ m := Nat.le_of_lt_succ n.isLt
  have hm : 0 < m := lt_of_lt_of_le hn hn_le
  have hone : 1 ≤ m := Nat.succ_le_iff.mpr hm
  have hones :
      Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ)) =
        Q.toFormalMultilinearSeries.compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones (n : ℕ)) := by
    ext z
    simp only [FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.applyComposition_ones]
    congr 1
    funext i
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P hone,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le S hone, hlinear]
  have hsplitP := comp_coeff_branch_split Q P n (Composition.ones (n : ℕ))
  have hsplitS := comp_coeff_branch_split Q S n (Composition.ones (n : ℕ))
  rw [hsplitP, hsplitS]
  calc
    (Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ)) +
        ∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c) -
        (Q.toFormalMultilinearSeries.compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones (n : ℕ)) +
        ∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) =
      (Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones (n : ℕ)) -
        Q.toFormalMultilinearSeries.compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones (n : ℕ))) +
        ((∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
            Q.toFormalMultilinearSeries.compAlongComposition
              P.toFormalMultilinearSeries c) -
          ∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
            Q.toFormalMultilinearSeries.compAlongComposition
              S.toFormalMultilinearSeries c) := by
      abel
    _ =
      (∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c) -
        ∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c := by
      rw [hones, sub_self, zero_add]
    _ = ∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hones' : c = Composition.ones (n : ℕ)
      · simp [hones']
      · simp only [if_neg hones']

/-- Helper for Infrastructure I.16a: evaluating the arbitrary positive non-all-ones
composition difference on a repeated input commutes with the finite branch sum. -/
theorem comp_coeff_sub_eq_nonOnes_of_inner_linear_eq_apply
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q : FiniteTaylorJet 𝕜 F G m)
    (P S : FiniteTaylorJet 𝕜 E F m)
    (hlinear :
      P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
        (Nat.le_of_lt_succ n.isLt))⟩ =
        S.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
          (Nat.le_of_lt_succ n.isLt))⟩)
    (x : E) :
    ((FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp Q S).coeff n)
        (fun _ : Fin (n : ℕ) ↦ x) =
      ∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) (fun _ : Fin (n : ℕ) ↦ x) := by
  have hsplit := comp_coeff_sub_eq_nonOnes_of_inner_linear_eq
    n hn Q P S hlinear
  have hvalue := congrArg
    (fun A : E [×(n : ℕ)]→L[𝕜] G ↦ A (fun _ : Fin (n : ℕ) ↦ x)) hsplit
  calc
    ((FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp Q S).coeff n)
        (fun _ : Fin (n : ℕ) ↦ x) =
      (∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c))
        (fun _ : Fin (n : ℕ) ↦ x) := hvalue
    _ = ∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) (fun _ : Fin (n : ℕ) ↦ x) := by
      rw [_root_.sum_apply]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hones' : c = Composition.ones (n : ℕ)
      · simp [hones']
      · simp only [if_neg hones', sub_apply]

/-- Helper for Infrastructure I.16a: branchwise bounds on arbitrary retained non-all-ones
composition terms give a direct norm bound for the coefficient difference. -/
theorem norm_comp_coeff_sub_eq_nonOnes_of_inner_linear_eq_apply_le
    {m : ℕ} (n : Fin (m + 1)) (hn : 0 < (n : ℕ))
    (Q : FiniteTaylorJet 𝕜 F G m)
    (P S : FiniteTaylorJet 𝕜 E F m)
    (hlinear :
      P.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
        (Nat.le_of_lt_succ n.isLt))⟩ =
        S.coeff ⟨1, Nat.succ_lt_succ (lt_of_lt_of_le hn
          (Nat.le_of_lt_succ n.isLt))⟩)
    (x : E) (C : Composition (n : ℕ) → ℝ)
    (hbranch :
      ∀ c : Composition (n : ℕ), c ≠ Composition.ones (n : ℕ) →
        ‖(Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) (fun _ : Fin (n : ℕ) ↦ x)‖ ≤ C c) :
    ‖((FiniteTaylorJet.comp Q P).coeff n -
        (FiniteTaylorJet.comp Q S).coeff n)
        (fun _ : Fin (n : ℕ) ↦ x)‖ ≤
      ∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else C c := by
  rw [comp_coeff_sub_eq_nonOnes_of_inner_linear_eq_apply n hn Q P S hlinear x]
  calc
    ‖∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) (fun _ : Fin (n : ℕ) ↦ x)‖ ≤
      ∑ c : Composition (n : ℕ), ‖if c = Composition.ones (n : ℕ) then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) (fun _ : Fin (n : ℕ) ↦ x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : Composition (n : ℕ), if c = Composition.ones (n : ℕ) then 0 else C c := by
      apply Finset.sum_le_sum
      intro c hc
      by_cases hones' : c = Composition.ones (n : ℕ)
      · simp [hones']
      · simp only [if_neg hones']
        exact hbranch c hones'

/-- Helper for Infrastructure I.16a: replacing only the top outer coefficient
isolates the all-ones branch from the remaining equal-top composition residual. -/
theorem comp_topCoeff_sub_eq_outer_through_topProjection
    {m : ℕ}
    (Q R Q' : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m)
    (hQ'lower : ∀ k : Fin (m + 1), (k : ℕ) < m → Q'.coeff k = Q.coeff k)
    (hQ'top : Q'.coeff ⟨m, Nat.lt_succ_self m⟩ = R.coeff ⟨m, Nat.lt_succ_self m⟩) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩ =
      (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m) +
        ((FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩) := by
  have houter :
      (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ =
        (Q.toFormalMultilinearSeries - Q'.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) :=
    comp_topCoeff_sub_eq_outer Q Q' P
      (fun k hk ↦ (hQ'lower k hk).symm)
  have hbranch :
      (Q.toFormalMultilinearSeries - Q'.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) =
        (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) := by
    ext z
    rw [FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.compAlongComposition_apply]
    have hcoeff :
        (Q.toFormalMultilinearSeries - Q'.toFormalMultilinearSeries)
            (Composition.ones m).length =
          (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
            (Composition.ones m).length := by
      rw [Composition.ones_length]
      change Q.toFormalMultilinearSeries m - Q'.toFormalMultilinearSeries m =
        Q.toFormalMultilinearSeries m - R.toFormalMultilinearSeries m
      rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q le_rfl,
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q' le_rfl,
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R le_rfl,
        hQ'top]
    exact congrArg
      (fun A : F [×(Composition.ones m).length]→L[𝕜] G ↦
        A (P.toFormalMultilinearSeries.applyComposition (Composition.ones m) z)) hcoeff
  calc
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩ =
      ((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      abel
    _ = (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) +
        ((FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      rw [houter, hbranch]

/- The two projection routes combine into a single four-endpoint normal form. -/

/-- Helper for Infrastructure I.16a: a two-sided top-coefficient secant splits into
    the inner linear term, the projected inner residual, the outer all-ones term,
    and the projected outer residual. -/
theorem comp_topCoeff_sub_decompose_through_projections
    {m : ℕ} (hm : 0 < m)
    (Q R Qsharp : FiniteTaylorJet 𝕜 F G m)
    (P S Psharp : FiniteTaylorJet 𝕜 E F m)
    (hP : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = Psharp.coeff k)
    (hPtop : Psharp.coeff ⟨m, Nat.lt_succ_self m⟩ =
      S.coeff ⟨m, Nat.lt_succ_self m⟩)
    (hQ : ∀ k : Fin (m + 1), (k : ℕ) < m → Qsharp.coeff k = Q.coeff k)
    (hQtop : Qsharp.coeff ⟨m, Nat.lt_succ_self m⟩ =
      R.coeff ⟨m, Nat.lt_succ_self m⟩) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩ =
      (continuousMultilinearCurryFin1 𝕜 F G
        (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
          (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            S.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩) +
        (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones m) +
        ((FiniteTaylorJet.comp Qsharp S).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩) := by
  have hinner := comp_topCoeff_sub_eq_inner_through_topProjection
    hm Q P S Psharp hP hPtop
  have houter := comp_topCoeff_sub_eq_outer_through_topProjection
    Q R Qsharp S hQ hQtop
  calc
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩ =
      ((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      abel
    _ = ((continuousMultilinearCurryFin1 𝕜 F G
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
            (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              S.coeff ⟨m, Nat.lt_succ_self m⟩) +
          ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
            (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩)) +
        ((Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
            S.toFormalMultilinearSeries (Composition.ones m) +
          ((FiniteTaylorJet.comp Qsharp S).coeff ⟨m, Nat.lt_succ_self m⟩ -
            (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩)) := by
      rw [hinner, houter]
    _ = (continuousMultilinearCurryFin1 𝕜 F G
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
            (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              S.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩) +
        (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones m) +
        ((FiniteTaylorJet.comp Qsharp S).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩) := by
      abel

/-- Helper for Infrastructure I.16a: the four projected top-coefficient branches
    have a norm estimate in which the inner and outer one-block terms are
    controlled by their respective coefficient gaps. -/
theorem norm_comp_topCoeff_sub_le_decompose_through_projections
    {m : ℕ} (hm : 0 < m)
    (Q R Qsharp : FiniteTaylorJet 𝕜 F G m)
    (P S Psharp : FiniteTaylorJet 𝕜 E F m)
    (hP : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = Psharp.coeff k)
    (hPtop : Psharp.coeff ⟨m, Nat.lt_succ_self m⟩ =
      S.coeff ⟨m, Nat.lt_succ_self m⟩)
    (hQ : ∀ k : Fin (m + 1), (k : ℕ) < m → Qsharp.coeff k = Q.coeff k)
    (hQtop : Qsharp.coeff ⟨m, Nat.lt_succ_self m⟩ =
      R.coeff ⟨m, Nat.lt_succ_self m⟩) :
    ‖(FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩‖ ≤
      ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            S.coeff ⟨m, Nat.lt_succ_self m⟩‖ +
        ‖(FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩‖ +
        ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
          ‖S.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m +
        ‖(FiniteTaylorJet.comp Qsharp S).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
  have hdecomp := comp_topCoeff_sub_decompose_through_projections
    hm Q R Qsharp P S Psharp hP hPtop hQ hQtop
  have hinner := norm_comp_topCoeff_sub_le_inner_through_topProjection
    hm Q P S Psharp hP hPtop
  have hinnerAB :
      ‖(continuousMultilinearCurryFin1 𝕜 F G
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
            (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              S.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩)‖ ≤
        ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
            ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              S.coeff ⟨m, Nat.lt_succ_self m⟩‖ +
          ‖(FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
            (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
    rw [← comp_topCoeff_sub_eq_inner_through_topProjection hm Q P S Psharp hP hPtop]
    exact hinner
  have houter :
      ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones m)‖ ≤
        ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
          ‖S.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
    have hformal :
        ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
            (Composition.ones m).length‖ =
          ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
      rw [Composition.ones_length]
      change ‖Q.toFormalMultilinearSeries m - R.toFormalMultilinearSeries m‖ = _
      rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q le_rfl,
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R le_rfl]
    have hproduct :
        ∏ i, ‖S.toFormalMultilinearSeries
            ((Composition.ones m).blocksFun i)‖ =
          ‖S.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
      calc
        ∏ i, ‖S.toFormalMultilinearSeries
              ((Composition.ones m).blocksFun i)‖ =
            ∏ _i : Fin (Composition.ones m).length,
              ‖S.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ := by
          apply Finset.prod_congr rfl
          intro i _
          rw [Composition.ones_blocksFun,
            FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le S
              (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))]
        _ = ‖S.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
          simp only [Finset.prod_const, Finset.card_fin, Composition.ones_length]
    calc
      ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
            S.toFormalMultilinearSeries (Composition.ones m)‖ ≤
          ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
              (Composition.ones m).length‖ *
            ∏ i, ‖S.toFormalMultilinearSeries
              ((Composition.ones m).blocksFun i)‖ :=
        FormalMultilinearSeries.compAlongComposition_norm _ _ _
      _ = ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
          ‖S.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
        rw [hformal, hproduct]
  rw [hdecomp]
  calc
    ‖(continuousMultilinearCurryFin1 𝕜 F G
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
            (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              S.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩) +
        (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones m) +
        ((FiniteTaylorJet.comp Qsharp S).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩)‖ ≤
      ‖(continuousMultilinearCurryFin1 𝕜 F G
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
            (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              S.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩)‖ +
        ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones m)‖ +
        ‖(FiniteTaylorJet.comp Qsharp S).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            S.coeff ⟨m, Nat.lt_succ_self m⟩‖ +
        ‖(FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩‖) +
        (‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
          ‖S.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m) +
        ‖(FiniteTaylorJet.comp Qsharp S).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
      exact add_le_add (add_le_add hinnerAB houter) le_rfl
    _ = ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            S.coeff ⟨m, Nat.lt_succ_self m⟩‖ +
        ‖(FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩‖ +
        ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
          ‖S.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m +
        ‖(FiniteTaylorJet.comp Qsharp S).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R S).coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
      ring

/-- Helper for Infrastructure I.16a: the all-ones composition selects the top finite-jet
coefficient of a formal-series difference after taking norms. -/
theorem norm_formalSub_onesLength
    {m : ℕ} (Q R : FiniteTaylorJet 𝕜 E F m) :
    ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
        (Composition.ones m).length‖ =
      ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
        R.coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
  rw [Composition.ones_length]
  change
    ‖Q.toFormalMultilinearSeries m - R.toFormalMultilinearSeries m‖ = _
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q le_rfl,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R le_rfl]

/-- Helper for Infrastructure I.16a: the norms of the inner factors selected by an
all-ones composition multiply to the power of the inner linear coefficient. -/
theorem norm_formal_onesProduct
    {m : ℕ} (hm : 0 < m) (P : FiniteTaylorJet 𝕜 E F m) :
    ∏ i, ‖P.toFormalMultilinearSeries
        ((Composition.ones m).blocksFun i)‖ =
      ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
  classical
  calc
    ∏ i, ‖P.toFormalMultilinearSeries
        ((Composition.ones m).blocksFun i)‖ =
        ∏ _i : Fin (Composition.ones m).length,
          ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Composition.ones_blocksFun,
        FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))]
    _ = ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
      simp only [Finset.prod_const, Finset.card_fin, Composition.ones_length]

/- The operator-norm estimate above is often consumed after evaluating the
   distinguished branch on a repeated input.  The following pointwise form
   keeps that evaluation and its input scale visible. -/

/-- Helper for Infrastructure I.16a: evaluating the all-ones composition branch on a repeated
input is bounded by the outer top-coefficient gap and the scaled inner linear coefficient. -/
theorem norm_comp_topCoeff_outer_ones_apply_le
    {m : ℕ} (hm : 0 < m)
    (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) (x : E) :
    ‖((Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m)) (fun _ : Fin m ↦ x)‖ ≤
      ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
        (‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ * ‖x‖) ^ m := by
  rw [comp_topCoeff_outer_ones_apply Q R P x, Composition.ones_length]
  have hinner :
      ‖P.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ x)‖ ≤
        ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ * ‖x‖ := by
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P hm]
    calc
      ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ x)‖ ≤
          ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
            ∏ _ : Fin 1, ‖x‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ * ‖x‖ := by
        simp
  have hproduct :
      (∏ _ : Fin m, ‖P.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ x)‖) ≤
        (‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ * ‖x‖) ^ m := by
    calc
      ∏ _ : Fin m, ‖P.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ x)‖ ≤
          ∏ _ : Fin m, (‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ * ‖x‖) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact norm_nonneg _
        · intro i hi
          exact hinner
      _ = (‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ * ‖x‖) ^ m := by
        simp only [Finset.prod_const, Finset.card_fin]
  have houter :
      ‖Q.toFormalMultilinearSeries m - R.toFormalMultilinearSeries m‖ =
        ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q le_rfl,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le R le_rfl]
  calc
    ‖(Q.toFormalMultilinearSeries m - R.toFormalMultilinearSeries m)
        (fun _ : Fin m ↦ P.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ x))‖ ≤
        ‖Q.toFormalMultilinearSeries m - R.toFormalMultilinearSeries m‖ *
          ∏ _ : Fin m, ‖P.toFormalMultilinearSeries 1 (fun _ : Fin 1 ↦ x)‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ ‖Q.toFormalMultilinearSeries m - R.toFormalMultilinearSeries m‖ *
          (‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ * ‖x‖) ^ m := by
      exact mul_le_mul_of_nonneg_left hproduct (norm_nonneg _)
    _ = ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
        (‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ * ‖x‖) ^ m := by
      rw [houter]

/-- Helper for Infrastructure I.16a: the outer projected top-coefficient identity
    admits a norm bound by the outer top gap and the projected residual. -/
theorem norm_comp_topCoeff_sub_le_outer_through_topProjection
    {m : ℕ} (hm : 0 < m)
    (Q R Q' : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m)
    (hQ'lower : ∀ k : Fin (m + 1), (k : ℕ) < m → Q'.coeff k = Q.coeff k)
    (hQ'top : Q'.coeff ⟨m, Nat.lt_succ_self m⟩ = R.coeff ⟨m, Nat.lt_succ_self m⟩) :
    ‖(FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖ ≤
      ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
        ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m +
        ‖(FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
  rw [comp_topCoeff_sub_eq_outer_through_topProjection
    Q R Q' P hQ'lower hQ'top]
  calc
    ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) +
        ((FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩)‖ ≤
      ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m)‖ +
        ‖(FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖ :=
      norm_add_le _ _
    _ ≤ ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
          (Composition.ones m).length‖ *
          ∏ i, ‖P.toFormalMultilinearSeries
            ((Composition.ones m).blocksFun i)‖ +
        ‖(FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
      exact add_le_add (FormalMultilinearSeries.compAlongComposition_norm _ _ _) le_rfl
    _ = ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
        ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m +
        ‖(FiniteTaylorJet.comp Q' P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
      rw [norm_formalSub_onesLength Q R, norm_formal_onesProduct hm P]

/- The operator-norm projection estimate is often consumed on the repeated
   input supplied by an all-ones composition branch. -/

/-- Helper for Infrastructure I.16a: the projected inner top-coefficient estimate remains valid
    after evaluation on a repeated input, with the expected power of its norm. -/
theorem norm_comp_topCoeff_sub_apply_le_inner_through_topProjection
    {m : ℕ} (hm : 0 < m) (Q : FiniteTaylorJet 𝕜 F G m)
    (P R Psharp : FiniteTaylorJet 𝕜 E F m)
    (hP : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = Psharp.coeff k)
    (hTop : Psharp.coeff ⟨m, Nat.lt_succ_self m⟩ =
      R.coeff ⟨m, Nat.lt_succ_self m⟩)
    (x : E) :
    ‖((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩)
        (fun _ : Fin m ↦ x)‖ ≤
      (‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ +
        ‖(FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩‖) *
        ‖x‖ ^ m := by
  have hoperator := norm_comp_topCoeff_sub_le_inner_through_topProjection
    hm Q P R Psharp hP hTop
  have hproduct_nonneg : 0 ≤ ∏ _ : Fin m, ‖x‖ := by
    exact Finset.prod_nonneg (fun _ _ ↦ norm_nonneg x)
  calc
    ‖((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩)
        (fun _ : Fin m ↦ x)‖ ≤
        ‖(FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩‖ *
          ∏ _ : Fin m, ‖x‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ ≤
        (‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
            ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              R.coeff ⟨m, Nat.lt_succ_self m⟩‖ +
          ‖(FiniteTaylorJet.comp Q Psharp).coeff
              ⟨m, Nat.lt_succ_self m⟩ -
            (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩‖) *
          ∏ _ : Fin m, ‖x‖ := by
      exact mul_le_mul_of_nonneg_right hoperator hproduct_nonneg
    _ =
        (‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
            ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              R.coeff ⟨m, Nat.lt_succ_self m⟩‖ +
          ‖(FiniteTaylorJet.comp Q Psharp).coeff
              ⟨m, Nat.lt_succ_self m⟩ -
            (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩‖) *
          ‖x‖ ^ m := by
      simp

/- The same evaluation bridge applies to the outer projection route. -/

/-- Helper for Infrastructure I.16a: the projected outer top-coefficient estimate remains valid
    after evaluation on a repeated input, with the expected power of its norm. -/
theorem norm_comp_topCoeff_sub_apply_le_outer_through_topProjection
    {m : ℕ} (hm : 0 < m)
    (Q R Qsharp : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m)
    (hQ : ∀ k : Fin (m + 1), (k : ℕ) < m → Qsharp.coeff k = Q.coeff k)
    (hQtop : Qsharp.coeff ⟨m, Nat.lt_succ_self m⟩ =
      R.coeff ⟨m, Nat.lt_succ_self m⟩)
    (x : E) :
    ‖((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩)
        (fun _ : Fin m ↦ x)‖ ≤
      (‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
          ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m +
        ‖(FiniteTaylorJet.comp Qsharp P).coeff
            ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖) *
        ‖x‖ ^ m := by
  have hoperator := norm_comp_topCoeff_sub_le_outer_through_topProjection
    hm Q R Qsharp P hQ hQtop
  have hproduct_nonneg : 0 ≤ ∏ _ : Fin m, ‖x‖ := by
    exact Finset.prod_nonneg (fun _ _ ↦ norm_nonneg x)
  calc
    ‖((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩)
        (fun _ : Fin m ↦ x)‖ ≤
        ‖(FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖ *
          ∏ _ : Fin m, ‖x‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ ≤
        (‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
            ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m +
          ‖(FiniteTaylorJet.comp Qsharp P).coeff
              ⟨m, Nat.lt_succ_self m⟩ -
            (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖) *
          ∏ _ : Fin m, ‖x‖ := by
      exact mul_le_mul_of_nonneg_right hoperator hproduct_nonneg
    _ =
        (‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
            ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m +
          ‖(FiniteTaylorJet.comp Qsharp P).coeff
              ⟨m, Nat.lt_succ_self m⟩ -
            (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖) *
          ‖x‖ ^ m := by
      simp

/-- Helper for Infrastructure I.16a: with a fixed inner jet, the top-coefficient variation
is bounded by the outer top-coefficient gap times the `m`-th power of the
inner linear coefficient norm. -/
theorem norm_comp_topCoeff_sub_le_outer
    {m : ℕ} (hm : 0 < m) (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m)
    (hQR : ∀ k : Fin (m + 1), (k : ℕ) < m → Q.coeff k = R.coeff k) :
    ‖(FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖ ≤
      ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
        ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
  rw [comp_topCoeff_sub_eq_outer Q R P hQR]
  calc
    ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m)‖ ≤
        ‖(Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries)
            (Composition.ones m).length‖ *
          ∏ i, ‖P.toFormalMultilinearSeries
            ((Composition.ones m).blocksFun i)‖ :=
      FormalMultilinearSeries.compAlongComposition_norm _ _ _
    _ = ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
        ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m := by
      rw [norm_formalSub_onesLength Q R, norm_formal_onesProduct hm P]

/- A top-coefficient replacement is the canonical way to choose the projected
   inner jet used by the mixed composition identities above. -/

/-- Helper for Infrastructure I.16a: replace one finite jet's top coefficient
    while retaining all lower coefficients. -/
noncomputable def replaceTopCoeff
    {m : ℕ} (P : FiniteTaylorJet 𝕜 E F m)
    (a : E [×m]→L[𝕜] F) : FiniteTaylorJet 𝕜 E F m :=
  { coeff := Function.update P.coeff ⟨m, Nat.lt_succ_self m⟩ a }

/-- Helper for Infrastructure I.16a: the replacement jet agrees with the source
    jet at every degree strictly below the top order. -/
theorem replaceTopCoeff_coeff_of_lt
    {m : ℕ} (P : FiniteTaylorJet 𝕜 E F m)
    (a : E [×m]→L[𝕜] F) (n : Fin (m + 1)) (hn : (n : ℕ) < m) :
    (replaceTopCoeff P a).coeff n = P.coeff n := by
  dsimp only [replaceTopCoeff]
  have hne : n ≠ ⟨m, Nat.lt_succ_self m⟩ := by
    intro htop
    exact (Nat.ne_of_lt hn) (congrArg Fin.val htop)
  rw [Function.update_of_ne hne]

/-- Helper for Infrastructure I.16a: the replacement jet has exactly the
    requested coefficient at its top order. -/
theorem replaceTopCoeff_coeff_top
    {m : ℕ} (P : FiniteTaylorJet 𝕜 E F m)
    (a : E [×m]→L[𝕜] F) :
    (replaceTopCoeff P a).coeff ⟨m, Nat.lt_succ_self m⟩ = a := by
  dsimp only [replaceTopCoeff]
  rw [Function.update_self]

/-- Helper for Infrastructure I.16a: a jet with the prescribed lower
    coefficients and top coefficient is the corresponding top replacement. -/
theorem eq_replaceTopCoeff_of_coeff_eq
    {m : ℕ} (P Q : FiniteTaylorJet 𝕜 E F m)
    (a : E [×m]→L[𝕜] F)
    (hbelow : ∀ n : Fin (m + 1), (n : ℕ) < m → Q.coeff n = P.coeff n)
    (htop : Q.coeff ⟨m, Nat.lt_succ_self m⟩ = a) :
    Q = replaceTopCoeff P a := by
  apply FiniteTaylorJet.ext_coeff
  intro n
  refine Fin.lastCases ?_ (fun i => ?_) n
  · exact htop.trans (replaceTopCoeff_coeff_top P a).symm
  · exact (hbelow i.castSucc i.isLt).trans
      (replaceTopCoeff_coeff_of_lt P a i.castSucc i.isLt).symm

/-- Helper for Infrastructure I.16a: the top-coefficient secant identity can
    use the canonical jet obtained by replacing the source top coefficient. -/
theorem comp_topCoeff_sub_eq_inner_through_replacedTopCoeff
    {m : ℕ} (hm : 0 < m) (Q : FiniteTaylorJet 𝕜 F G m)
    (P R : FiniteTaylorJet 𝕜 E F m) :
    let Psharp := replaceTopCoeff P
      (R.coeff ⟨m, Nat.lt_succ_self m⟩)
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩ =
      (continuousMultilinearCurryFin1 𝕜 F G
        (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)).compContinuousMultilinearMap
          (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩) +
        ((FiniteTaylorJet.comp Q Psharp).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩) := by
  dsimp only
  apply comp_topCoeff_sub_eq_inner_through_topProjection hm Q P R
    (replaceTopCoeff P (R.coeff ⟨m, Nat.lt_succ_self m⟩))
  · intro k hk
    exact (replaceTopCoeff_coeff_of_lt P _ k hk).symm
  · exact replaceTopCoeff_coeff_top P _

/-- Helper for Infrastructure I.16a: the canonical inner top-coefficient replacement gives
    the projected secant estimate after evaluation on a repeated input. -/
theorem norm_comp_topCoeff_sub_apply_le_inner_through_replacedTopCoeff
    {m : ℕ} (hm : 0 < m) (Q : FiniteTaylorJet 𝕜 F G m)
    (P R : FiniteTaylorJet 𝕜 E F m) (x : E) :
    let Psharp := replaceTopCoeff P
      (R.coeff ⟨m, Nat.lt_succ_self m⟩)
    ‖((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩)
        (fun _ : Fin m ↦ x)‖ ≤
      (‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩‖ +
        ‖(FiniteTaylorJet.comp Q Psharp).coeff
            ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp Q R).coeff ⟨m, Nat.lt_succ_self m⟩‖) *
        ‖x‖ ^ m := by
  dsimp only
  apply norm_comp_topCoeff_sub_apply_le_inner_through_topProjection
    hm Q P R (replaceTopCoeff P (R.coeff ⟨m, Nat.lt_succ_self m⟩))
  · intro k hk
    exact (replaceTopCoeff_coeff_of_lt P _ k hk).symm
  · exact replaceTopCoeff_coeff_top P _

/-- Helper for Infrastructure I.16a: the outer top-coefficient secant identity
    uses the canonical jet obtained by replacing the outer source top coefficient. -/
theorem comp_topCoeff_sub_eq_outer_through_replacedTopCoeff
    {m : ℕ} (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) :
    let Qsharp := replaceTopCoeff Q
      (R.coeff ⟨m, Nat.lt_succ_self m⟩)
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩ =
      (Q.toFormalMultilinearSeries - R.toFormalMultilinearSeries).compAlongComposition
        P.toFormalMultilinearSeries (Composition.ones m) +
        ((FiniteTaylorJet.comp Qsharp P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩) := by
  dsimp only
  apply comp_topCoeff_sub_eq_outer_through_topProjection Q R
    (replaceTopCoeff Q (R.coeff ⟨m, Nat.lt_succ_self m⟩)) P
  · intro k hk
    exact replaceTopCoeff_coeff_of_lt Q _ k hk
  · exact replaceTopCoeff_coeff_top Q _

/-- Helper for Infrastructure I.16a: the canonical outer replacement gives the
    outer one-block norm bound together with its projected composition residual. -/
theorem norm_comp_topCoeff_sub_le_outer_through_replacedTopCoeff
    {m : ℕ} (hm : 0 < m) (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) :
    let Qsharp := replaceTopCoeff Q
      (R.coeff ⟨m, Nat.lt_succ_self m⟩)
    ‖(FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖ ≤
      ‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
        ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m +
        ‖(FiniteTaylorJet.comp Qsharp P).coeff ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖ := by
  dsimp only
  apply norm_comp_topCoeff_sub_le_outer_through_topProjection hm Q R
    (replaceTopCoeff Q (R.coeff ⟨m, Nat.lt_succ_self m⟩)) P
  · intro k hk
    exact replaceTopCoeff_coeff_of_lt Q _ k hk
  · exact replaceTopCoeff_coeff_top Q _

/-- Helper for Infrastructure I.16a: the canonical outer top-coefficient replacement gives
    the outer secant estimate after evaluation on a repeated input. -/
theorem norm_comp_topCoeff_sub_apply_le_outer_through_replacedTopCoeff
    {m : ℕ} (hm : 0 < m) (Q R : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) (x : E) :
    let Qsharp := replaceTopCoeff Q
      (R.coeff ⟨m, Nat.lt_succ_self m⟩)
    ‖((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩)
        (fun _ : Fin m ↦ x)‖ ≤
      (‖Q.coeff ⟨m, Nat.lt_succ_self m⟩ -
          R.coeff ⟨m, Nat.lt_succ_self m⟩‖ *
          ‖P.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ ^ m +
        ‖(FiniteTaylorJet.comp Qsharp P).coeff
            ⟨m, Nat.lt_succ_self m⟩ -
          (FiniteTaylorJet.comp R P).coeff ⟨m, Nat.lt_succ_self m⟩‖) *
        ‖x‖ ^ m := by
  dsimp only
  apply norm_comp_topCoeff_sub_apply_le_outer_through_topProjection
    hm Q R (replaceTopCoeff Q (R.coeff ⟨m, Nat.lt_succ_self m⟩)) P
  · intro k hk
    exact replaceTopCoeff_coeff_of_lt Q _ k hk
  · exact replaceTopCoeff_coeff_top Q _

/- A product-valued inner jet is the common source of the affine top-coefficient
   term in the graph-transform construction.  The following specialization keeps
   that source-facing shape while leaving the projected jet explicit. -/

/- The same calculation is useful before the fiber top coefficient is normalized to
   zero, so expose the lower-coefficient version separately. -/

/-- Helper for Infrastructure I.16a: a lower-equal fiber-jet variation passes
   through a product-valued inner jet and a scalar reindexing jet at the repeated-one
   top coefficient. -/
theorem comp_prod_comp_topCoeff_sub_eq_inner_of_lower
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {m : ℕ} (hm : 0 < m)
    (Q : FiniteTaylorJet 𝕜 (𝕜 × X) Y m)
    (C : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (P R : FiniteTaylorJet 𝕜 𝕜 X m)
    (I : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (hPR : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = R.coeff k) :
    let top : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    let oneM : Fin m → 𝕜 := fun _ ↦ 1
    let oneI : Fin 1 → 𝕜 := fun _ ↦ 1
    (((FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) I).coeff top -
        (FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)) I).coeff top)
      oneM) =
      ((I.coeff ⟨1, Nat.succ_lt_succ hm⟩ oneI) ^ m) •
        (continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩))
          (0, (P.coeff top - R.coeff top) oneM) := by
  classical
  have hprod_lower (k : Fin (m + 1)) (hk : (k : ℕ) < m) :
      (FiniteTaylorJet.prod C P).coeff k =
        (FiniteTaylorJet.prod C R).coeff k := by
    rw [FiniteTaylorJet.coeff_prod, FiniteTaylorJet.coeff_prod, hPR k hk]
  have hinner := comp_topCoeff_sub_eq_inner hm Q
    (FiniteTaylorJet.prod C P) (FiniteTaylorJet.prod C R) hprod_lower
  have hinner_lower (k : Fin (m + 1)) (hk : (k : ℕ) < m) :
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)).coeff k =
        (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)).coeff k := by
    apply comp_coeff_eq_of_eq_below
    · intro j _hj
      rfl
    · intro j _hj_pos hj_le
      exact hprod_lower j (hj_le.trans_lt hk)
  have houter := comp_topCoeff_sub_eq_outer
    (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P))
    (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)) I hinner_lower
  dsimp only
  rw [houter, comp_topCoeff_outer_ones_apply, Composition.ones_length]
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) le_rfl,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)) le_rfl,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le I
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)), hinner,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  simp only [FiniteTaylorJet.coeff_prod, ContinuousMultilinearMap.prod_apply,
    sub_apply]
  have hscale :=
    ((FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)).coeff
        ⟨m, Nat.lt_succ_self m⟩ -
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)).coeff
        ⟨m, Nat.lt_succ_self m⟩).map_smul_univ
      (fun _ : Fin m ↦ I.coeff ⟨1, Nat.succ_lt_succ hm⟩ (fun _ ↦ 1))
      (fun _ : Fin m ↦ (1 : 𝕜))
  rw [hinner, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply] at hscale
  simp only [FiniteTaylorJet.coeff_prod, ContinuousMultilinearMap.prod_apply,
    sub_apply] at hscale
  simp at hscale ⊢
  simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin,
    continuousMultilinearCurryFin1_apply] using hscale

/-- Helper for Infrastructure I.16a: a one-variable curry of a multilinear map
    is bounded on a pair with zero first component by the map norm times the
    second-component norm. -/
theorem norm_continuousMultilinearCurryFin1_apply_zero_pair_le
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : (𝕜 × X) [×1]→L[𝕜] Y) (x : X) :
    ‖(continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y f) (0, x)‖ ≤
      ‖f‖ * ‖x‖ := by
  calc
    ‖(continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y f) (0, x)‖ ≤
        ‖continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y f‖ * ‖(0, x)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖f‖ * ‖x‖ := by
      rw [LinearIsometryEquiv.norm_map]
      simp only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]

/-- Helper for Infrastructure I.16a: the lower-equal product-composition
    identity has a repeated-input norm bound separating the reindexing factor,
    the inner linear coefficient, and the fiber top-coefficient gap. -/
theorem norm_comp_prod_comp_topCoeff_sub_apply_le_inner_of_lower
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {m : ℕ} (hm : 0 < m)
    (Q : FiniteTaylorJet 𝕜 (𝕜 × X) Y m)
    (C : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (P R : FiniteTaylorJet 𝕜 𝕜 X m)
    (I : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (hPR : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = R.coeff k) :
    let top : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    let oneM : Fin m → 𝕜 := fun _ ↦ 1
    let oneI : Fin 1 → 𝕜 := fun _ ↦ 1
    ‖(((FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) I).coeff top -
        (FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C R)) I).coeff top)
      oneM)‖ ≤
      ‖I.coeff ⟨1, Nat.succ_lt_succ hm⟩ oneI‖ ^ m *
        ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖(P.coeff top - R.coeff top) oneM‖ := by
  dsimp only
  rw [comp_prod_comp_topCoeff_sub_eq_inner_of_lower hm Q C P R I hPR]
  rw [norm_smul, norm_pow]
  have hlinear :
      ‖(continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩))
          (0, (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩) (fun _ : Fin m ↦ 1))‖ ≤
        ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖(P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            R.coeff ⟨m, Nat.lt_succ_self m⟩) (fun _ : Fin m ↦ 1)‖ := by
    exact norm_continuousMultilinearCurryFin1_apply_zero_pair_le
      (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)
      ((P.coeff ⟨m, Nat.lt_succ_self m⟩ -
        R.coeff ⟨m, Nat.lt_succ_self m⟩) (fun _ : Fin m ↦ 1))
  calc
    ‖I.coeff ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ 1)‖ ^ m *
          ‖(continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
            (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩))
            (0, (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              R.coeff ⟨m, Nat.lt_succ_self m⟩) (fun _ : Fin m ↦ 1))‖ ≤
        ‖I.coeff ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ 1)‖ ^ m *
          (‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
            ‖(P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              R.coeff ⟨m, Nat.lt_succ_self m⟩) (fun _ : Fin m ↦ 1)‖) :=
      mul_le_mul_of_nonneg_left hlinear
        (pow_nonneg (norm_nonneg _) m)
    _ = ‖I.coeff ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ 1)‖ ^ m *
          ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
            ‖(P.coeff ⟨m, Nat.lt_succ_self m⟩ -
              R.coeff ⟨m, Nat.lt_succ_self m⟩) (fun _ : Fin m ↦ 1)‖ := by
      ring

/-- Helper for Infrastructure I.16a: a product inner jet with a zero-top projection
isolates the fiber top coefficient through two nested finite-jet compositions. -/
theorem comp_prod_comp_topCoeff_sub_eq_inner_of_zeroTop
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {m : ℕ} (hm : 0 < m)
    (Q : FiniteTaylorJet 𝕜 (𝕜 × X) Y m)
    (C : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (P Pflat : FiniteTaylorJet 𝕜 𝕜 X m)
    (I : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (hP : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = Pflat.coeff k)
    (hPflat : Pflat.coeff ⟨m, Nat.lt_succ_self m⟩ = 0) :
    let top : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    let oneM : Fin m → 𝕜 := fun _ ↦ 1
    let oneI : Fin 1 → 𝕜 := fun _ ↦ 1
    (((FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) I).coeff top -
        (FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C Pflat)) I).coeff top)
      oneM) =
      ((I.coeff ⟨1, Nat.succ_lt_succ hm⟩ oneI) ^ m) •
        (continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩))
          (0, P.coeff top oneM) := by
  classical
  have hprod_lower (k : Fin (m + 1)) (hk : (k : ℕ) < m) :
      (FiniteTaylorJet.prod C P).coeff k =
        (FiniteTaylorJet.prod C Pflat).coeff k := by
    rw [FiniteTaylorJet.coeff_prod, FiniteTaylorJet.coeff_prod, hP k hk]
  have hfirst_top := comp_topCoeff_sub_eq_inner hm Q
    (FiniteTaylorJet.prod C P) (FiniteTaylorJet.prod C Pflat) hprod_lower
  have hfirst_lower (k : Fin (m + 1)) (hk : (k : ℕ) < m) :
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)).coeff k =
        (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C Pflat)).coeff k := by
    apply comp_coeff_eq_of_eq_below
    · intro j _hj
      rfl
    · intro j _hj_pos hj_le
      exact hprod_lower j (hj_le.trans_lt hk)
  have hsecond_top := comp_topCoeff_sub_eq_outer
    (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P))
    (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C Pflat)) I hfirst_lower
  dsimp only
  rw [hsecond_top, comp_topCoeff_outer_ones_apply]
  rw [Composition.ones_length]
  rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) le_rfl,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C Pflat)) le_rfl,
    FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le I
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))]
  rw [hfirst_top,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  simp only [FiniteTaylorJet.coeff_prod, ContinuousMultilinearMap.prod_apply,
    sub_apply]
  rw [hPflat]
  have hscale :=
    ((FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)).coeff
        ⟨m, Nat.lt_succ_self m⟩ -
      (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C Pflat)).coeff
        ⟨m, Nat.lt_succ_self m⟩).map_smul_univ
      (fun _ : Fin m ↦ I.coeff ⟨1, Nat.succ_lt_succ hm⟩ (fun _ ↦ 1))
      (fun _ : Fin m ↦ (1 : 𝕜))
  rw [hfirst_top, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply] at hscale
  simp only [FiniteTaylorJet.coeff_prod, ContinuousMultilinearMap.prod_apply,
    sub_apply] at hscale
  rw [hPflat] at hscale
  simp at hscale ⊢
  simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin,
    continuousMultilinearCurryFin1_apply] using hscale

/- The zero-top identity also has a direct operator-norm estimate, which is the
   form used when the projected residual is inserted into a compact bound. -/

/-- Helper for Infrastructure I.16a: the zero-top projected nested composition is bounded
    by the repeated scalar coefficient, the outer linear coefficient, and the fiber top gap. -/
theorem norm_comp_prod_comp_topCoeff_sub_apply_le_inner_of_zeroTop
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {m : ℕ} (hm : 0 < m)
    (Q : FiniteTaylorJet 𝕜 (𝕜 × X) Y m)
    (C : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (P Pflat : FiniteTaylorJet 𝕜 𝕜 X m)
    (I : FiniteTaylorJet 𝕜 𝕜 𝕜 m)
    (hP : ∀ k : Fin (m + 1), (k : ℕ) < m → P.coeff k = Pflat.coeff k)
    (hPflat : Pflat.coeff ⟨m, Nat.lt_succ_self m⟩ = 0) :
    let top : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    let oneM : Fin m → 𝕜 := fun _ ↦ 1
    let oneI : Fin 1 → 𝕜 := fun _ ↦ 1
    ‖(((FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C P)) I).coeff top -
        (FiniteTaylorJet.comp
          (FiniteTaylorJet.comp Q (FiniteTaylorJet.prod C Pflat)) I).coeff top)
      oneM)‖ ≤
      ‖I.coeff ⟨1, Nat.succ_lt_succ hm⟩ oneI‖ ^ m *
        ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖P.coeff top oneM‖ := by
  dsimp only
  rw [comp_prod_comp_topCoeff_sub_eq_inner_of_zeroTop hm Q C P Pflat I hP hPflat]
  rw [norm_smul, norm_pow]
  have hlinear :
      ‖(continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩))
          (0, (P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            Pflat.coeff ⟨m, Nat.lt_succ_self m⟩) (fun _ : Fin m ↦ 1))‖ ≤
        ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖(P.coeff ⟨m, Nat.lt_succ_self m⟩ -
            Pflat.coeff ⟨m, Nat.lt_succ_self m⟩) (fun _ : Fin m ↦ 1)‖ := by
    exact norm_continuousMultilinearCurryFin1_apply_zero_pair_le
      (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩)
      ((P.coeff ⟨m, Nat.lt_succ_self m⟩ -
        Pflat.coeff ⟨m, Nat.lt_succ_self m⟩) (fun _ : Fin m ↦ 1))
  have hlinear' :
      ‖(continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
          (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩))
          (0, P.coeff ⟨m, Nat.lt_succ_self m⟩ (fun _ : Fin m ↦ 1))‖ ≤
        ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
          ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ (fun _ : Fin m ↦ 1)‖ := by
    simpa only [hPflat, sub_zero] using hlinear
  calc
    ‖I.coeff ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ 1)‖ ^ m *
          ‖(continuousMultilinearCurryFin1 𝕜 (𝕜 × X) Y
            (Q.coeff ⟨1, Nat.succ_lt_succ hm⟩))
            (0, P.coeff ⟨m, Nat.lt_succ_self m⟩ (fun _ : Fin m ↦ 1))‖ ≤
        ‖I.coeff ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ 1)‖ ^ m *
          (‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
            ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ (fun _ : Fin m ↦ 1)‖) :=
      mul_le_mul_of_nonneg_left hlinear'
        (pow_nonneg (norm_nonneg _) m)
    _ = ‖I.coeff ⟨1, Nat.succ_lt_succ hm⟩ (fun _ : Fin 1 ↦ 1)‖ ^ m *
          ‖Q.coeff ⟨1, Nat.succ_lt_succ hm⟩‖ *
            ‖P.coeff ⟨m, Nat.lt_succ_self m⟩ (fun _ : Fin m ↦ 1)‖ := by
      ring

/- A zeroed outer top coefficient removes exactly the distinguished all-ones
   branch from a finite-jet top coefficient. -/

/-- Helper for Infrastructure I.16a: replacing an outer jet's top coefficient by zero
isolates the non-all-ones branches of its top composition coefficient. -/
theorem comp_topCoeff_nonOnes_eq_zeroTopReplacement
    {m : ℕ} (Q : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) :
    (FiniteTaylorJet.comp (replaceTopCoeff Q 0) P).coeff
        ⟨m, Nat.lt_succ_self m⟩ =
      ∑ c : Composition m, if c = Composition.ones m then 0 else
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries c := by
  classical
  rw [comp_topCoeff_branch_sum]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hones : c = Composition.ones m
  · subst c
    simp only [if_pos]
    ext z
    simp only [FormalMultilinearSeries.compAlongComposition_apply]
    have htop :
        (replaceTopCoeff Q 0).toFormalMultilinearSeries
            (Composition.ones m).length = 0 := by
      rw [Composition.ones_length]
      rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
        (replaceTopCoeff Q 0) le_rfl]
      rw [replaceTopCoeff_coeff_top]
    rw [htop]
    simp
  · simp only [if_neg hones]
    ext z
    simp only [FormalMultilinearSeries.compAlongComposition_apply]
    have hlength_ne : c.length ≠ m := by
      intro hlength
      exact hones (Composition.eq_ones_iff_length.mpr hlength)
    have hlen : c.length < m := lt_of_le_of_ne c.length_le hlength_ne
    have hbound : c.length ≤ m := hlen.le
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le
      (replaceTopCoeff Q 0) hbound,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le Q hbound]
    congr 1
    dsimp only [replaceTopCoeff]
    rw [Function.update_of_ne]
    intro htop
    exact (Nat.ne_of_lt hlen) (congrArg Fin.val htop)

/- A common inner linear coefficient makes the distinguished all-ones branch
   cancel in a top-coefficient difference. -/

/-- Helper for Infrastructure I.16a: when two inner jets have the same linear
    coefficient, their top-composition difference is exactly the sum of the
    non-all-ones branch differences. -/
theorem comp_topCoeff_sub_eq_nonOnes_of_inner_linear_eq
    {m : ℕ} (hm : 0 < m)
    (Q : FiniteTaylorJet 𝕜 F G m)
    (P S : FiniteTaylorJet 𝕜 E F m)
    (hlinear :
      P.coeff ⟨1, Nat.succ_lt_succ hm⟩ =
        S.coeff ⟨1, Nat.succ_lt_succ hm⟩) :
    (FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩ =
      ∑ c : Composition m, if c = Composition.ones m then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) := by
  classical
  have hones :
      Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries (Composition.ones m) =
        Q.toFormalMultilinearSeries.compAlongComposition
          S.toFormalMultilinearSeries (Composition.ones m) := by
    ext z
    simp only [FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.applyComposition_ones]
    congr 1
    funext i
    rw [FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le P hm,
      FiniteTaylorJet.toFormalMultilinearSeries_coeff_of_le S hm, hlinear]
  rw [comp_topCoeff_branch_sum, comp_topCoeff_branch_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hones' : c = Composition.ones m
  · subst c
    simp only [if_pos]
    exact sub_eq_zero.mpr hones
  · simp only [if_neg hones']

/- The pointwise form is the one used by endpoint estimates, where the top
   coefficient is evaluated on a repeated direction. -/

/-- Helper for Infrastructure I.16a: evaluating the all-ones-cancelled top
    coefficient difference on a repeated input commutes with the non-ones sum. -/
theorem comp_topCoeff_sub_eq_nonOnes_of_inner_linear_eq_apply
    {m : ℕ} (hm : 0 < m)
    (Q : FiniteTaylorJet 𝕜 F G m)
    (P S : FiniteTaylorJet 𝕜 E F m)
    (hlinear :
      P.coeff ⟨1, Nat.succ_lt_succ hm⟩ =
        S.coeff ⟨1, Nat.succ_lt_succ hm⟩)
    (x : E) :
    ((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩)
        (fun _ : Fin m ↦ x) =
      ∑ c : Composition m, if c = Composition.ones m then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) (fun _ : Fin m ↦ x) := by
  have hsplit :=
    comp_topCoeff_sub_eq_nonOnes_of_inner_linear_eq hm Q P S hlinear
  have hvalue := congrArg
    (fun A : E [×m]→L[𝕜] G => A (fun _ : Fin m ↦ x)) hsplit
  calc
    ((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩)
        (fun _ : Fin m ↦ x) =
      (∑ c : Composition m, if c = Composition.ones m then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c)) (fun _ : Fin m ↦ x) := hvalue
    _ = ∑ c : Composition m, if c = Composition.ones m then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) (fun _ : Fin m ↦ x) := by
      rw [_root_.sum_apply]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hones' : c = Composition.ones m
      · simp [hones']
      · simp only [if_neg hones', sub_apply]

/- The norm form packages the pointwise cancellation with independent branchwise bounds. -/

/-- Helper for Infrastructure I.16a: a branchwise norm bound for the repeated-input
    top-coefficient difference after the all-ones branch has been cancelled. -/
theorem norm_comp_topCoeff_sub_eq_nonOnes_of_inner_linear_eq_apply_le
    {m : ℕ} (hm : 0 < m)
    (Q : FiniteTaylorJet 𝕜 F G m)
    (P S : FiniteTaylorJet 𝕜 E F m)
    (hlinear :
      P.coeff ⟨1, Nat.succ_lt_succ hm⟩ =
        S.coeff ⟨1, Nat.succ_lt_succ hm⟩)
    (x : E)
    (C : Composition m → ℝ)
    (hbranch :
      ∀ c : Composition m, c ≠ Composition.ones m →
        ‖(Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) (fun _ : Fin m ↦ x)‖ ≤ C c) :
    ‖((FiniteTaylorJet.comp Q P).coeff ⟨m, Nat.lt_succ_self m⟩ -
        (FiniteTaylorJet.comp Q S).coeff ⟨m, Nat.lt_succ_self m⟩)
        (fun _ : Fin m ↦ x)‖ ≤
      ∑ c : Composition m, if c = Composition.ones m then 0 else C c := by
  rw [comp_topCoeff_sub_eq_nonOnes_of_inner_linear_eq_apply hm Q P S hlinear x]
  calc
    ‖∑ c : Composition m, if c = Composition.ones m then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) (fun _ : Fin m ↦ x)‖ ≤
      ∑ c : Composition m, ‖if c = Composition.ones m then 0 else
        (Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c -
          Q.toFormalMultilinearSeries.compAlongComposition
            S.toFormalMultilinearSeries c) (fun _ : Fin m ↦ x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : Composition m, if c = Composition.ones m then 0 else C c := by
      apply Finset.sum_le_sum
      intro c hc
      by_cases hones' : c = Composition.ones m
      · simp [hones']
      · simp only [if_neg hones']
        exact hbranch c hones'

end FiniteTaylorJet
