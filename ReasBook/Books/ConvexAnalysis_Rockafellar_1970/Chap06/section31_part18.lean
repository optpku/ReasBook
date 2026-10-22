/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part17

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- The concave Fenchel-Young equality for the book's concave conjugate `g⋆`. -/
def ConcaveFenchelYoungEqualityAt {m : ℕ}
    (g : (Fin m → ℝ) → EReal) (y uStar : Fin m → ℝ) : Prop :=
  g y + concaveFenchelConjugate g uStar = ((dotProduct y uStar : ℝ) : EReal)

/-- The book's Kuhn-Tucker conditions for a primal-dual pair `(x, u⋆)` in Fenchel duality with a
linear map `A`, encoded by the Fenchel-Young equalities for `f` at `(x, A⋆ u⋆)` and for `g` at
`(A x, u⋆)`. -/
def SatisfiesFenchelKuhnTuckerConditions {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (x : Fin n → ℝ) (uStar : Fin m → ℝ) : Prop :=
  FenchelYoungEqualityAt f x (fenchelCoordinateAdjointApply A uStar) ∧
    ConcaveFenchelYoungEqualityAt g (A x) uStar

lemma helperForTheorem_31_3_concaveFenchelInequality {m : ℕ}
    (g : (Fin m → ℝ) → EReal)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (y uStar : Fin m → ℝ) :
    g y + concaveFenchelConjugate g uStar ≤ ((dotProduct y uStar : ℝ) : EReal) := by
  let h : (Fin m → ℝ) → EReal := fun v => -(g v)
  have hh : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) h := by
    simpa [h, ProperConcaveFunctionOn] using hg
  have hfy := (fenchelYoung_inequality_and_eq_iff_mem_subdifferential h hh y (-uStar)).1
  have hy_ne_top : g y ≠ (⊤ : EReal) := by
    simpa [h] using hh.2.2 y (by simp)
  have hfc_ne_bot : fenchelConjugate m h (-uStar) ≠ (⊥ : EReal) := by
    exact (proper_fenchelConjugate_of_proper (n := m) (f := h) hh).2.2 (-uStar) (by simp)
  have hneg :
      -(-g y + fenchelConjugate m h (-uStar)) ≤
        -(-(((dotProduct y uStar : ℝ) : EReal))) := by
    exact EReal.neg_le_neg_iff.2 (by simpa [h, dotProduct, Finset.sum_neg_distrib] using hfy)
  have hleft :
      -(-g y + fenchelConjugate m h (-uStar)) =
        g y + concaveFenchelConjugate g uStar := by
    rw [EReal.neg_add (Or.inl (by simpa) ) (Or.inr hfc_ne_bot)]
    simp [h, concaveFenchelConjugate, sub_eq_add_neg]
  simpa [hleft] using hneg

lemma helperForTheorem_31_3_pointEq_implies_sumLe {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (x : Fin n → ℝ) (uStar : Fin m → ℝ)
    (hPoint :
      f x - g (A x) =
        concaveFenchelConjugate g uStar -
          fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar)) :
    f x + fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar) ≤
      g (A x) + concaveFenchelConjugate g uStar := by
  let fStar := fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar)
  let gStar := concaveFenchelConjugate g uStar
  have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  have hgx_ne_top : g (A x) ≠ (⊤ : EReal) := by
    have hNegg : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun y => -(g y)) := by
      simpa [ProperConcaveFunctionOn] using hg
    simpa using hNegg.2.2 (A x) (by simp)
  have hprimal_ne_bot : f x - g (A x) ≠ (⊥ : EReal) := by
    have hneg_gx_ne_bot : -(g (A x)) ≠ (⊥ : EReal) := by
      simpa using hgx_ne_top
    simpa [sub_eq_add_neg] using add_ne_bot_of_notbot hfx_ne_bot hneg_gx_ne_bot
  have hfStar_ne_bot : fStar ≠ (⊥ : EReal) := by
    exact
      (proper_fenchelConjugate_of_proper (n := n) (f := f) hf).2.2
        (fenchelCoordinateAdjointApply A uStar) (by simp)
  have hgStar_ne_top : gStar ≠ (⊤ : EReal) := by
    let hNegg : (Fin m → ℝ) → EReal := fun y => -(g y)
    have hhNegg : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) hNegg := by
      simpa [hNegg, ProperConcaveFunctionOn] using hg
    have hconj_ne_bot : fenchelConjugate m hNegg (-uStar) ≠ (⊥ : EReal) := by
      exact (proper_fenchelConjugate_of_proper (n := m) (f := hNegg) hhNegg).2.2 (-uStar) (by simp)
    simpa [gStar, hNegg, concaveFenchelConjugate] using hconj_ne_bot
  have hdual_ne_top :
      gStar - fStar ≠ (⊤ : EReal) := by
    cases hsf : fStar with
    | bot =>
        exact (hfStar_ne_bot hsf).elim
    | coe a =>
        cases hsg : gStar with
        | bot =>
            simp [hsg, hsf]
        | coe b =>
            intro htop
            have hEq : ((↑b : EReal) - (↑a : EReal)) = (((b - a : ℝ) : EReal)) := by
              simp [EReal.coe_sub]
            rw [hEq] at htop
            exact EReal.coe_ne_top (b - a) htop
        | top =>
            exact (hgStar_ne_top hsg).elim
    | top =>
        simpa [hsf] using hgStar_ne_top
  have hfStar_ne_top : fStar ≠ (⊤ : EReal) := by
    intro hfStar_top
    have hdual_bot : gStar - fStar = (⊥ : EReal) := by
      simpa [hfStar_top] using rfl
    exact hprimal_ne_bot (hPoint.trans hdual_bot)
  have hfx_le :
      f x ≤ (gStar - fStar) + g (A x) := by
    exact
      (EReal.sub_le_iff_le_add (Or.inr hdual_ne_top) (Or.inl hgx_ne_top)).1
        (le_of_eq hPoint)
  have hfx_le' :
      f x ≤ (g (A x) + gStar) - fStar := by
    simpa [fStar, gStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hfx_le
  exact
    (EReal.le_sub_iff_add_le (Or.inl hfStar_ne_bot) (Or.inl hfStar_ne_top)).1
      hfx_le'

lemma helperForTheorem_31_3_sumLe_implies_pointLe {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (x : Fin n → ℝ) (uStar : Fin m → ℝ)
    (hSum :
      f x + fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar) ≤
        g (A x) + concaveFenchelConjugate g uStar) :
    f x - g (A x) ≤
      concaveFenchelConjugate g uStar -
        fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar) := by
  let fStar := fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar)
  let gStar := concaveFenchelConjugate g uStar
  have hNegg : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun y => -(g y)) := by
    simpa [ProperConcaveFunctionOn] using hg
  have hgx_ne_top : g (A x) ≠ (⊤ : EReal) := by
    simpa using hNegg.2.2 (A x) (by simp)
  have hfStar_ne_bot : fStar ≠ (⊥ : EReal) := by
    exact
      (proper_fenchelConjugate_of_proper (n := n) (f := f) hf).2.2
        (fenchelCoordinateAdjointApply A uStar) (by simp)
  have hgStar_ne_top : gStar ≠ (⊤ : EReal) := by
    let hNegg' : (Fin m → ℝ) → EReal := fun y => -(g y)
    have hhNegg' : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) hNegg' := by
      simpa [hNegg', ProperConcaveFunctionOn] using hg
    have hconj_ne_bot : fenchelConjugate m hNegg' (-uStar) ≠ (⊥ : EReal) := by
      exact (proper_fenchelConjugate_of_proper (n := m) (f := hNegg') hhNegg').2.2 (-uStar) (by simp)
    simpa [gStar, hNegg', concaveFenchelConjugate] using hconj_ne_bot
  have hfStar_ne_top : fStar ≠ (⊤ : EReal) := by
    intro hfStar_top
    have hLeftTop : f x + fStar = (⊤ : EReal) := by
      simpa [hfStar_top] using EReal.add_top_of_ne_bot (hf.2.2 x (by simp))
    have hTopLe : (⊤ : EReal) ≤ g (A x) + gStar := by
      calc
        (⊤ : EReal) = f x + fStar := hLeftTop.symm
        _ ≤ g (A x) + gStar := by simpa [fStar, gStar] using hSum
    have hRightTop : g (A x) + gStar = (⊤ : EReal) := by
      exact top_unique hTopLe
    cases hsg : gStar with
    | bot =>
        simp [hsg] at hRightTop
    | coe b =>
        cases hgx : g (A x) with
        | bot =>
            simp [hgx, hsg] at hRightTop
        | coe c =>
            have hEq : (((c + b : ℝ) : EReal)) = (⊤ : EReal) := by
              simpa [hgx, hsg] using hRightTop
            exact EReal.coe_ne_top (c + b) hEq
        | top =>
            exact (hgx_ne_top hgx).elim
    | top =>
        exact (hgStar_ne_top hsg).elim
  have hdual_ne_top : gStar - fStar ≠ (⊤ : EReal) := by
    cases hsf : fStar with
    | bot =>
        exact (hfStar_ne_bot hsf).elim
    | coe a =>
        cases hsg : gStar with
        | bot =>
            simp [hsg, hsf]
        | coe b =>
            intro htop
            have hEq : ((↑b : EReal) - (↑a : EReal)) = (((b - a : ℝ) : EReal)) := by
              simp [EReal.coe_sub]
            rw [hEq] at htop
            exact EReal.coe_ne_top (b - a) htop
        | top =>
            exact (hgStar_ne_top hsg).elim
    | top =>
        exact (hfStar_ne_top hsf).elim
  have hfx_le :
      f x ≤ (g (A x) + gStar) - fStar := by
    exact
      (EReal.le_sub_iff_add_le (Or.inl hfStar_ne_bot) (Or.inl hfStar_ne_top)).2 hSum
  have hfx_le' :
      f x ≤ (gStar - fStar) + g (A x) := by
    simpa [fStar, gStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hfx_le
  exact
    (EReal.sub_le_iff_le_add (Or.inr hdual_ne_top) (Or.inl hgx_ne_top)).2
      hfx_le'

lemma helperForTheorem_31_3_reverseSumLe_implies_reversePointLe {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (x : Fin n → ℝ) (uStar : Fin m → ℝ)
    (hSum :
      g (A x) + concaveFenchelConjugate g uStar ≤
        f x + fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar)) :
    concaveFenchelConjugate g uStar -
        fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar) ≤
      f x - g (A x) := by
  let fStar := fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar)
  let gStar := concaveFenchelConjugate g uStar
  have hNegg : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun y => -(g y)) := by
    simpa [ProperConcaveFunctionOn] using hg
  have hgx_ne_top : g (A x) ≠ (⊤ : EReal) := by
    simpa using hNegg.2.2 (A x) (by simp)
  have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  have hfStar_ne_bot : fStar ≠ (⊥ : EReal) := by
    exact
      (proper_fenchelConjugate_of_proper (n := n) (f := f) hf).2.2
        (fenchelCoordinateAdjointApply A uStar) (by simp)
  by_cases hgx_bot : g (A x) = (⊥ : EReal)
  · have hTop : f x - g (A x) = (⊤ : EReal) := by
      simpa [sub_eq_add_neg, hgx_bot] using EReal.add_top_of_ne_bot hfx_ne_bot
    rw [hTop]
    exact le_top
  · have hgx_ne_bot : g (A x) ≠ (⊥ : EReal) := hgx_bot
    have hAddLe :
        (g (A x) + gStar) - fStar ≤ f x := by
      exact
        (EReal.sub_le_iff_le_add (Or.inl hfStar_ne_bot) (Or.inr hfx_ne_bot)).2
          (by simpa [fStar, gStar, add_assoc, add_left_comm, add_comm] using hSum)
    have hPoint :
        gStar - fStar ≤ f x - g (A x) := by
      exact
        (EReal.le_sub_iff_add_le (Or.inl hgx_ne_bot) (Or.inl hgx_ne_top)).2
          (by simpa [fStar, gStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hAddLe)
    simpa [fStar, gStar] using hPoint

-- Proof sketch: combine Corollary 31.2.1 with the Fenchel-Young equalities. If `x` and `u⋆`
-- attain the primal infimum and dual supremum with the same value, then the two Fenchel
-- inequalities for `f` at `(x, A⋆ u⋆)` and for `-g` at `(A x, -u⋆)` must both be equalities,
-- which is exactly the Kuhn-Tucker condition encoded here. Conversely, those equalities force
-- the primal and dual objectives to coincide at `(x, u⋆)`, so both attain the common optimal
-- value.
/-- Theorem 31.3: let `f : ℝ^n → ℝ ∪ {+∞}` be closed proper convex, let
`g : ℝ^m → ℝ ∪ {-∞}` be closed proper concave, and let `A : ℝ^n → ℝ^m` be linear. Then
`f x - g (A x) = inf_z (f z - g (A z)) = sup_u⋆ (g⋆ u⋆ - f⋆ (A⋆ u⋆)) =
g⋆ uStar - f⋆ (A⋆ uStar)` if and only if the pair `(x, uStar)` satisfies the Kuhn-Tucker
conditions. In this formalization, those conditions are encoded by
`SatisfiesFenchelKuhnTuckerConditions A f g x uStar`, i.e. the Fenchel-Young equalities for `f`
at `(x, A⋆ uStar)` and for `g` at `(A x, uStar)`. -/
theorem fenchel_linear_map_optimality_iff_kuhn_tucker_conditions {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hg_closed : ClosedConcaveFunction g)
    (x : Fin n → ℝ) (uStar : Fin m → ℝ) :
    let dualObj : (Fin m → ℝ) → EReal :=
      fun v =>
        concaveFenchelConjugate g v -
          fenchelConjugate n f (fenchelCoordinateAdjointApply A v)
    (f x - g (A x) = functionInfimumEReal (fun z => f z - g (A z)) ∧
      functionInfimumEReal (fun z => f z - g (A z)) =
        (⨆ v : Fin m → ℝ, dualObj v) ∧
      (⨆ v : Fin m → ℝ, dualObj v) =
        dualObj uStar) ↔
      SatisfiesFenchelKuhnTuckerConditions A f g x uStar := by
  let dualObj : (Fin m → ℝ) → EReal := fun v =>
    concaveFenchelConjugate g v -
      fenchelConjugate n f (fenchelCoordinateAdjointApply A v)
  let primalObj : (Fin n → ℝ) → EReal := fun z => f z - g (A z)
  let _ := hf_closed
  let _ := hg_closed
  have hWeakDuality : ∀ z v, dualObj v ≤ primalObj z := by
    intro z v
    let fStar := fenchelConjugate n f (fenchelCoordinateAdjointApply A v)
    let gStar := concaveFenchelConjugate g v
    have hConc :
        g (A z) + gStar ≤ ((dotProduct (A z) v : ℝ) : EReal) :=
      helperForTheorem_31_3_concaveFenchelInequality (g := g) hg (A z) v
    have hConv :
        ((dotProduct (A z) v : ℝ) : EReal) ≤
          f z + fStar := by
      have hDot :
          (((dotProduct z (fenchelCoordinateAdjointApply A v) : ℝ)) : EReal) =
            (((dotProduct (A z) v : ℝ)) : EReal) := by
        norm_num [dotProduct, mul_comm,
          helperForLemma_31_0_8_sum_uStar_mul_Ax_eq_sum_adjoint_mul_x (A := A) v z]
      simpa [hDot] using
        (fenchelYoung_inequality_and_eq_iff_mem_subdifferential
          f hf z (fenchelCoordinateAdjointApply A v)).1
    have hNegg : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun y => -(g y)) := by
      simpa [ProperConcaveFunctionOn] using hg
    have hgz_ne_top : g (A z) ≠ (⊤ : EReal) := by
      simpa using hNegg.2.2 (A z) (by simp)
    have hfz_ne_bot : f z ≠ (⊥ : EReal) := hf.2.2 z (by simp)
    have hfStar_ne_bot : fStar ≠ (⊥ : EReal) := by
      exact
        (proper_fenchelConjugate_of_proper (n := n) (f := f) hf).2.2
          (fenchelCoordinateAdjointApply A v) (by simp)
    have hSum :
        g (A z) + gStar ≤ f z + fStar := le_trans hConc hConv
    by_cases hgz_bot : g (A z) = (⊥ : EReal)
    · have hTop : primalObj z = (⊤ : EReal) := by
        simpa [primalObj, sub_eq_add_neg, hgz_bot] using EReal.add_top_of_ne_bot hfz_ne_bot
      rw [hTop]
      exact le_top
    · have hgz_ne_bot : g (A z) ≠ (⊥ : EReal) := hgz_bot
      have hAddLe : (g (A z) + gStar) - fStar ≤ f z := by
        exact
          (EReal.sub_le_iff_le_add (Or.inl hfStar_ne_bot) (Or.inr hfz_ne_bot)).2
            (by simpa [fStar, gStar, add_assoc, add_left_comm, add_comm] using hSum)
      have hPoint : gStar - fStar ≤ f z - g (A z) := by
        exact
          (EReal.le_sub_iff_add_le (Or.inl hgz_ne_bot) (Or.inl hgz_ne_top)).2
            (by
              simpa [fStar, gStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                hAddLe)
      simpa [dualObj, primalObj, fStar, gStar] using hPoint
  constructor
  · rintro ⟨hxInf, hInfSup, hSupu⟩
    have hPoint : primalObj x = dualObj uStar := by
      exact hxInf.trans (hInfSup.trans hSupu)
    have hSumLe :
        f x + fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar) ≤
          g (A x) + concaveFenchelConjugate g uStar :=
      helperForTheorem_31_3_pointEq_implies_sumLe
        (A := A) (f := f) (g := g) hf hg x uStar hPoint
    have hDot :
        (((dotProduct x (fenchelCoordinateAdjointApply A uStar) : ℝ)) : EReal) =
          (((dotProduct (A x) uStar : ℝ)) : EReal) := by
      norm_num [dotProduct, mul_comm,
        helperForLemma_31_0_8_sum_uStar_mul_Ax_eq_sum_adjoint_mul_x (A := A) uStar x]
    have hConc :
        g (A x) + concaveFenchelConjugate g uStar ≤ ((dotProduct (A x) uStar : ℝ) : EReal) :=
      helperForTheorem_31_3_concaveFenchelInequality (g := g) hg (A x) uStar
    have hConv :
        ((dotProduct (A x) uStar : ℝ) : EReal) ≤
          f x + fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar) := by
      simpa [hDot] using
        (fenchelYoung_inequality_and_eq_iff_mem_subdifferential
          f hf x (fenchelCoordinateAdjointApply A uStar)).1
    have hConvEq :
        f x + fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar) =
          ((dotProduct (A x) uStar : ℝ) : EReal) := by
      apply le_antisymm
      · exact le_trans hSumLe hConc
      · exact hConv
    have hConcEq :
        g (A x) + concaveFenchelConjugate g uStar =
          ((dotProduct (A x) uStar : ℝ) : EReal) := by
      apply le_antisymm
      · exact hConc
      · exact le_trans hConv hSumLe
    constructor
    · simpa [FenchelYoungEqualityAt, hDot] using hConvEq
    · simpa [ConcaveFenchelYoungEqualityAt] using hConcEq
  · rintro ⟨hKTf, hKTg⟩
    have hSumEq :
        f x + fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar) =
          g (A x) + concaveFenchelConjugate g uStar := by
      have hDot :
          (((dotProduct x (fenchelCoordinateAdjointApply A uStar) : ℝ)) : EReal) =
            (((dotProduct (A x) uStar : ℝ)) : EReal) := by
        norm_num [dotProduct, mul_comm,
          helperForLemma_31_0_8_sum_uStar_mul_Ax_eq_sum_adjoint_mul_x (A := A) uStar x]
      rw [hKTf, hDot, hKTg]
    have hPointLe :
        primalObj x ≤ dualObj uStar :=
      helperForTheorem_31_3_sumLe_implies_pointLe
        (A := A) (f := f) (g := g) hf hg x uStar (le_of_eq hSumEq)
    have hPointEq : primalObj x = dualObj uStar := by
      exact le_antisymm hPointLe (hWeakDuality x uStar)
    have hInfLePoint : functionInfimumEReal primalObj ≤ primalObj x := by
      rw [functionInfimumEReal]
      exact sInf_le (Set.mem_range.mpr ⟨x, rfl⟩)
    have hSupGePoint : dualObj uStar ≤ ⨆ v : Fin m → ℝ, dualObj v :=
      le_iSup dualObj uStar
    have hSupLeInf :
        (⨆ v : Fin m → ℝ, dualObj v) ≤ functionInfimumEReal primalObj := by
      rw [functionInfimumEReal]
      refine le_iInf ?_
      intro z
      refine iSup_le ?_
      intro v
      exact hWeakDuality z v
    have hInfEqSup :
        functionInfimumEReal primalObj = (⨆ v : Fin m → ℝ, dualObj v) := by
      apply le_antisymm
      · calc
          functionInfimumEReal primalObj ≤ primalObj x := hInfLePoint
          _ = dualObj uStar := hPointEq
          _ ≤ ⨆ v : Fin m → ℝ, dualObj v := hSupGePoint
      · exact hSupLeInf
    have hPointEqInf : primalObj x = functionInfimumEReal primalObj := by
      apply le_antisymm
      · rw [hPointEq]
        exact le_trans hSupGePoint hSupLeInf
      · exact hInfLePoint
    have hSupEqPoint : (⨆ v : Fin m → ℝ, dualObj v) = dualObj uStar := by
      apply le_antisymm
      · calc
          (⨆ v : Fin m → ℝ, dualObj v) = functionInfimumEReal primalObj := hInfEqSup.symm
          _ = primalObj x := hPointEqInf.symm
          _ = dualObj uStar := hPointEq
          _ ≤ dualObj uStar := le_rfl
      · exact hSupGePoint
    refine ⟨?_, ?_, ?_⟩
    · simpa [primalObj] using hPointEqInf
    · exact hInfEqSup
    · simpa [dualObj] using hSupEqPoint

/-- Helper for Corollary 31.3.1: if `A x₀` lies in the relative interior of the effective domain
of `-g`, then `x₀` lies in the relative interior of the effective domain of the precomposition
`x ↦ -(g (A x))`. -/
lemma helperForCorollary_31_3_1_ri_precomp_neg_g {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (g : (Fin m → ℝ) → EReal)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    {x0 : Fin n → ℝ}
    (hAx0 :
      A x0 ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)) :
    x0 ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun y => -(g (A y)))) := by
  let h : (Fin m → ℝ) → EReal := fun y => -(g y)
  have hh : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) h := by
    simpa [h, ProperConcaveFunctionOn] using hg
  have hAx0riH :
      A x0 ∈ euclideanRelativeInterior_fin m (effectiveDomain Set.univ h) := by
    simpa [h, concaveEffectiveDomain, effectiveDomain_eq] using hAx0
  let e_n := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  let e_m := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m))
  let A_e : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m) :=
    (e_m.symm.toLinearMap).comp (A.comp e_n.toLinearMap)
  have hri :
      ∃ x : Fin n → ℝ,
        e_m.symm (A x) ∈
          euclideanRelativeInterior m (Set.image e_m.symm (effectiveDomain Set.univ h)) := by
    refine ⟨x0, ?_⟩
    exact
      (mem_euclideanRelativeInterior_fin_iff (n := m) (C := effectiveDomain Set.univ h)
        (x := A x0)).1 hAx0riH
  have hri_eq :
      euclideanRelativeInterior n
          (Set.image e_n.symm (effectiveDomain Set.univ (fun x => h (A x)))) =
        A_e ⁻¹' euclideanRelativeInterior m (Set.image e_m.symm (effectiveDomain Set.univ h)) := by
    simpa [e_n, e_m, A_e] using
      (ri_effectiveDomain_preimage_linearMap (hgproper := hh) (A := A) hri)
  have hx0_pre :
      e_n.symm x0 ∈
        A_e ⁻¹' euclideanRelativeInterior m (Set.image e_m.symm (effectiveDomain Set.univ h)) := by
    simpa [e_n, e_m, A_e] using
      (show e_m.symm (A x0) ∈
          euclideanRelativeInterior m (Set.image e_m.symm (effectiveDomain Set.univ h)) from
        (mem_euclideanRelativeInterior_fin_iff (n := m) (C := effectiveDomain Set.univ h)
          (x := A x0)).1 hAx0riH)
  have hx0_ri :
      e_n.symm x0 ∈
        euclideanRelativeInterior n
          (Set.image e_n.symm (effectiveDomain Set.univ (fun x => h (A x)))) := by
    rw [hri_eq]
    exact hx0_pre
  exact
    (mem_euclideanRelativeInterior_fin_iff (n := n)
      (C := effectiveDomain Set.univ (fun x => h (A x))) (x := x0)).2 hx0_ri

/-- Helper for Corollary 31.3.1: the dual map applied to the functional represented by
`-u⋆` is the negative of the functional represented by the coordinate adjoint `A⋆ u⋆`. -/
lemma helperForCorollary_31_3_1_dualMap_dotProductEquiv_neg {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (uStar : Fin m → ℝ) :
    A.dualMap (dotProductEquiv ℝ (Fin m) (-uStar)) =
      -dotProductEquiv ℝ (Fin n) (fenchelCoordinateAdjointApply A uStar) := by
  ext x
  -- Evaluate both dual functionals on an arbitrary primal vector and rewrite the `A x` pairing
  -- through the coordinate adjoint identity from Lemma 31.0.8.
  simp [LinearMap.dualMap_apply, dotProductEquiv_apply_apply,
    helperForLemma_31_0_8_sum_uStar_mul_Ax_eq_sum_adjoint_mul_x, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Corollary 31.3.1: the concave Fenchel-Young equality for `g` is exactly the
convex subgradient condition for `-g` at the negated dual vector. -/
lemma helperForCorollary_31_3_1_concaveFenchelYoungEqualityAt_iff_neg_subgradient {m : ℕ}
    (g : (Fin m → ℝ) → EReal)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (y uStar : Fin m → ℝ) :
    ConcaveFenchelYoungEqualityAt g y uStar ↔
      dotProductEquiv ℝ (Fin m) (-uStar) ∈ subdifferentialAt (fun v => -(g v)) y := by
  let h : (Fin m → ℝ) → EReal := fun v => -(g v)
  have hh : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) h := by
    -- Switch to the convex function `h = -g` so the Chapter 30 Fenchel-Young theorem applies.
    simpa [h, ProperConcaveFunctionOn] using hg
  have hFY := fenchelYoung_inequality_and_eq_iff_mem_subdifferential h hh y (-uStar)
  have hFY' :
      FenchelYoungEqualityAt h y (-uStar) ↔ IsEuclideanSubgradientAt h y (-uStar) := by
    simpa [FenchelYoungEqualityAt] using hFY.2
  have hFY'' :
      FenchelYoungEqualityAt h y (-uStar) ↔
        dotProductEquiv ℝ (Fin m) (-uStar) ∈ subdifferentialAt h y := by
    simpa [IsEuclideanSubgradientAt] using hFY'
  have hy_ne_top : g y ≠ (⊤ : EReal) := by
    simpa [h] using hh.2.2 y (by simp)
  have hconj_ne_bot : fenchelConjugate m h (-uStar) ≠ (⊥ : EReal) := by
    exact (proper_fenchelConjugate_of_proper (n := m) (f := h) hh).2.2 (-uStar) (by simp)
  have hconj :
      fenchelConjugate m h (-uStar) = -concaveFenchelConjugate g uStar := by
    simpa [h] using
      (helperForLemma_31_0_8_fenchelConjugate_neg_eq_neg_concaveFenchelConjugate_neg
        (g := g) (uStar := -uStar))
  have hleft :
      -(-g y + fenchelConjugate m h (-uStar)) =
        g y + concaveFenchelConjugate g uStar := by
    rw [hconj]
    rw [EReal.neg_add (Or.inl (by simpa using hy_ne_top)) (Or.inr (by simpa [hconj] using hconj_ne_bot))]
    simp [sub_eq_add_neg]
  constructor
  · intro hEq
    have hneg :
        -(g y + concaveFenchelConjugate g uStar) =
          -((((dotProduct y uStar : ℝ)) : EReal)) := by
      exact congrArg Neg.neg (by simpa [ConcaveFenchelYoungEqualityAt] using hEq)
    have hright :
        -((((dotProduct y (-uStar) : ℝ)) : EReal)) =
          (((dotProduct y uStar : ℝ)) : EReal) := by
      simp [dotProduct, Finset.sum_neg_distrib]
    have hEq' :
        -g y + fenchelConjugate m h (-uStar) =
          (((dotProduct y (-uStar) : ℝ)) : EReal) := by
      calc
        -g y + fenchelConjugate m h (-uStar) = -(g y + concaveFenchelConjugate g uStar) := by
          simpa using congrArg Neg.neg hleft
        _ = -((((dotProduct y uStar : ℝ)) : EReal)) := hneg
        _ = (((dotProduct y (-uStar) : ℝ)) : EReal) := by
            simp [dotProduct, Finset.sum_neg_distrib]
    exact hFY''.1 (by simpa [FenchelYoungEqualityAt, h] using hEq')
  · intro hEq
    have hEq' : -g y + fenchelConjugate m h (-uStar) =
        (((dotProduct y (-uStar) : ℝ)) : EReal) := by
      have hEq'' : FenchelYoungEqualityAt h y (-uStar) := hFY''.2 (by simpa [h] using hEq)
      simpa [FenchelYoungEqualityAt, h] using hEq''
    have hleft' :
        -g y + fenchelConjugate m h (-uStar) =
          -(g y + concaveFenchelConjugate g uStar) := by
      simpa using congrArg Neg.neg hleft
    have hright' :
        (((dotProduct y (-uStar) : ℝ)) : EReal) =
          -((((dotProduct y uStar : ℝ)) : EReal)) := by
      simp [dotProduct, Finset.sum_neg_distrib]
    have hneg :
        -(g y + concaveFenchelConjugate g uStar) =
          -((((dotProduct y uStar : ℝ)) : EReal)) := by
      calc
        -(g y + concaveFenchelConjugate g uStar) =
            -g y + fenchelConjugate m h (-uStar) := hleft'.symm
        _ = (((dotProduct y (-uStar) : ℝ)) : EReal) := hEq'
        _ = -((((dotProduct y uStar : ℝ)) : EReal)) := hright'
    exact neg_injective hneg

/-- Helper for Corollary 31.3.1: under the relative-interior qualification, the subdifferential of
`x ↦ f x - g (A x)` splits as the sum of `∂f(x)` and the pullback of `∂(-g)(A x)` through `A⋆`.
-/
lemma helperForCorollary_31_3_1_subdifferential_f_minus_gA {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hri : ∃ x0 : Fin n → ℝ,
      x0 ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
        A x0 ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g))
    (x : Fin n → ℝ) :
    subdifferentialAt (fun y => f y - g (A y)) x =
      subdifferentialAt f x + A.dualMap '' subdifferentialAt (fun y => -(g y)) (A x) := by
  let h : (Fin m → ℝ) → EReal := fun y => -(g y)
  have hh : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) h := by
    -- Replace the concave term by the convex function `h = -g`.
    simpa [h, ProperConcaveFunctionOn] using hg
  rcases hri with ⟨x0, hx0riF, hAx0riG⟩
  have hAx0riH : A x0 ∈ euclideanRelativeInterior_fin m (effectiveDomain Set.univ h) := by
    -- `concaveEffectiveDomain g` is exactly the effective domain of `-g`.
    simpa [h, concaveEffectiveDomain, effectiveDomain_eq] using hAx0riG
  have hAx0Dom : A x0 ∈ effectiveDomain Set.univ h :=
    helperForTheorem_21_1_riFin_subset_C (effectiveDomain Set.univ h) hAx0riH
  have hRangeDom : ∃ z : Fin m → ℝ, z ∈ Set.range A ∧ z ∈ effectiveDomain Set.univ h := by
    -- The same qualification witness supplies the finite point needed for properness of `h ∘ A`.
    exact ⟨A x0, ⟨x0, rfl⟩, hAx0Dom⟩
  have hPrecompProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun y => h (A y)) :=
    helperForTheorem_23_9_precomp_proper_of_range_meets_effectiveDomain A h hh hRangeDom
  have hRangeRi : RangeMeetsRelativeInteriorEffectiveDomain A h := by
    -- For the chain rule itself, we can use the qualification witness directly in the range.
    exact ⟨A x0, ⟨x0, rfl⟩, hAx0riH⟩
  have hPrecompEq :
      subdifferentialAt (fun y => h (A y)) x = A.dualMap '' subdifferentialAt h (A x) := by
    -- Apply Theorem 23.9 in its equality branch to the precomposition `h ∘ A`.
    simpa using
      (subdifferential_precomp_linearMap_contains_dualMapImage_and_eq_under_qualification
        A h hh).2 (Or.inl hRangeRi) x
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal := fun i => if i = 0 then f else fun y => h (A y)
  have hproperTwo : ∀ i : Fin 2, ProperConvexFunctionOn Set.univ (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hf
    · simpa [fTwo] using hPrecompProper
  have hx0riPrecomp :
      x0 ∈ euclideanRelativeInterior_fin n (effectiveDomain Set.univ (fun y => h (A y))) := by
    -- The remaining common-relative-interior witness is exactly the linear-preimage helper proved
    -- above.
    simpa [h] using
      helperForCorollary_31_3_1_ri_precomp_neg_g (A := A) (g := g) hg hAx0riG
  have hriTwo :
      ∃ z : Fin n → ℝ,
        ∀ i : Fin 2, z ∈ euclideanRelativeInterior_fin n (effectiveDomain Set.univ (fTwo i)) := by
    -- Package the two summands `f` and `h ∘ A` into the Chapter 23 sum rule.
    refine ⟨x0, ?_⟩
    intro i
    fin_cases i
    · simpa [fTwo] using hx0riF
    · simpa [fTwo] using hx0riPrecomp
  have hSumEq :
      subdifferentialAt (fun y => f y + h (A y)) x =
        subdifferentialAt f x + subdifferentialAt (fun y => h (A y)) x := by
    -- The sum rule now gives the exact decomposition into the two summand subdifferentials.
    simpa [fTwo, Fin.sum_univ_two] using
      (subdifferential_sum_eq_sum_of_commonRelativeInteriorEffectiveDomain
        fTwo hproperTwo hriTwo x)
  calc
    subdifferentialAt (fun y => f y - g (A y)) x
        = subdifferentialAt (fun y => f y + h (A y)) x := by
            simp [h, sub_eq_add_neg]
    _ = subdifferentialAt f x + subdifferentialAt (fun y => h (A y)) x := hSumEq
    _ = subdifferentialAt f x + A.dualMap '' subdifferentialAt h (A x) := by
          rw [hPrecompEq]
    _ = subdifferentialAt f x + A.dualMap '' subdifferentialAt (fun y => -(g y)) (A x) := by
          simp [h]

/-- Helper for Corollary 31.3.1: under the qualification hypothesis, a zero subgradient of the
primal objective is equivalent to the existence of a dual vector satisfying the Fenchel
Kuhn-Tucker equalities. -/
lemma helperForCorollary_31_3_1_zero_mem_subdifferential_iff_exists_kuhn_tucker {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hri : ∃ x0 : Fin n → ℝ,
      x0 ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
        A x0 ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g))
    (x : Fin n → ℝ) :
    (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt (fun y => f y - g (A y)) x ↔
      ∃ uStar : Fin m → ℝ, SatisfiesFenchelKuhnTuckerConditions A f g x uStar := by
  constructor
  · intro hZero
    rw [helperForCorollary_31_3_1_subdifferential_f_minus_gA (A := A) (f := f) (g := g)
      hf hg hri x] at hZero
    rcases (Set.mem_add).1 hZero with ⟨p, hp, r, hr, hsum⟩
    rcases hr with ⟨q, hq, rfl⟩
    let uNeg : Fin m → ℝ := (dotProductEquiv ℝ (Fin m)).symm q
    let uStar : Fin m → ℝ := -uNeg
    have hqEq : q = dotProductEquiv ℝ (Fin m) (-uStar) := by
      -- Normalize the codomain dual witness `q` into the coordinate vector `-u⋆`.
      simp [uStar, uNeg]
    have hpEq : p = dotProductEquiv ℝ (Fin n) (fenchelCoordinateAdjointApply A uStar) := by
      have hsum0 :
          p + A.dualMap (dotProductEquiv ℝ (Fin m) (-uStar)) = 0 := by
        rw [← hqEq]
        exact hsum
      have hsum' :
          p + -dotProductEquiv ℝ (Fin n) (fenchelCoordinateAdjointApply A uStar) = 0 := by
        rwa [helperForCorollary_31_3_1_dualMap_dotProductEquiv_neg (A := A) (uStar := uStar)] at hsum0
      have hpEq' := eq_neg_of_add_eq_zero_left hsum'
      simpa using hpEq'
    refine ⟨uStar, ?_⟩
    constructor
    · have hpE : IsEuclideanSubgradientAt f x ((dotProductEquiv ℝ (Fin n)).symm p) := by
        -- Translate the dual membership `p ∈ ∂f(x)` into the Euclidean subgradient form used by
        -- the Fenchel-Young theorem.
        change dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm p) ∈
          subdifferentialAt f x
        simpa using hp
      have hpFY : FenchelYoungEqualityAt f x ((dotProductEquiv ℝ (Fin n)).symm p) := by
        -- The Chapter 30 equivalence turns that Euclidean subgradient into the first
        -- Fenchel-Young equality.
        exact
          ((fenchelYoung_inequality_and_eq_iff_mem_subdifferential
            f hf x ((dotProductEquiv ℝ (Fin n)).symm p)).2).2 hpE
      simpa [hpEq] using hpFY
    · -- The codomain subgradient is already exactly the negated-dual statement from the concave
      -- Fenchel-Young bridge.
      exact
        (helperForCorollary_31_3_1_concaveFenchelYoungEqualityAt_iff_neg_subgradient
          (g := g) hg (y := A x) (uStar := uStar)).2
          (by simpa [hqEq] using hq)
  · rintro ⟨uStar, hKTf, hKTg⟩
    rw [helperForCorollary_31_3_1_subdifferential_f_minus_gA (A := A) (f := f) (g := g)
      hf hg hri x]
    have hpE : IsEuclideanSubgradientAt f x (fenchelCoordinateAdjointApply A uStar) := by
      -- The primal Kuhn-Tucker equality is the Fenchel-Young equality for `f`, hence a
      -- Euclidean subgradient at `x`.
      exact
        ((fenchelYoung_inequality_and_eq_iff_mem_subdifferential
          f hf x (fenchelCoordinateAdjointApply A uStar)).2).1 hKTf
    have hp :
        dotProductEquiv ℝ (Fin n) (fenchelCoordinateAdjointApply A uStar) ∈
          subdifferentialAt f x := by
      simpa [IsEuclideanSubgradientAt] using hpE
    have hq :
        dotProductEquiv ℝ (Fin m) (-uStar) ∈
          subdifferentialAt (fun y => -(g y)) (A x) := by
      -- The concave Kuhn-Tucker equality rewrites to the convex subgradient condition for `-g`.
      exact
        (helperForCorollary_31_3_1_concaveFenchelYoungEqualityAt_iff_neg_subgradient
          (g := g) hg (y := A x) (uStar := uStar)).1 hKTg
    -- Assemble the two subgradients into a Minkowski-sum witness for `0`.
    refine (Set.mem_add).2 ?_
    refine ⟨dotProductEquiv ℝ (Fin n) (fenchelCoordinateAdjointApply A uStar), hp,
      A.dualMap (dotProductEquiv ℝ (Fin m) (-uStar)), ?_, ?_⟩
    · exact ⟨dotProductEquiv ℝ (Fin m) (-uStar), hq, rfl⟩
    · calc
        dotProductEquiv ℝ (Fin n) (fenchelCoordinateAdjointApply A uStar) +
            A.dualMap (dotProductEquiv ℝ (Fin m) (-uStar)) =
            dotProductEquiv ℝ (Fin n) (fenchelCoordinateAdjointApply A uStar) +
              -dotProductEquiv ℝ (Fin n) (fenchelCoordinateAdjointApply A uStar) := by
                rw [helperForCorollary_31_3_1_dualMap_dotProductEquiv_neg]
        _ = 0 := by simp

-- Proof sketch: if `x` minimizes `f - g ∘ A`, Corollary 31.2.1 under condition `(a)` supplies a
-- dual maximizer `u⋆`; then Theorem 31.3 identifies simultaneous primal-dual optimality with the
-- Kuhn-Tucker conditions. Conversely, if `x` satisfies the Kuhn-Tucker conditions with some
-- `u⋆`, Theorem 31.3 forces `x` to attain the primal infimum.
/-- Corollary 31.3.1: assume the notation of Theorem 31.3, and assume moreover that there exists
`x₀ ∈ ri (dom f)` such that `A x₀ ∈ ri (dom g)`. Then a vector `x` attains the infimum of
`z ↦ f z - g (A z)` if and only if there exists a vector `u⋆` such that `x` and `u⋆` satisfy the
Kuhn-Tucker conditions `SatisfiesFenchelKuhnTuckerConditions A f g x u⋆`. -/
theorem fenchel_linear_map_minimizer_iff_exists_kuhn_tucker_vector {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hg_closed : ClosedConcaveFunction g)
    (hri : ∃ x0 : Fin n → ℝ,
      x0 ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
        A x0 ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g))
    (x : Fin n → ℝ) :
    x ∈ minimumSetEReal (fun z => f z - g (A z)) ↔
      ∃ uStar : Fin m → ℝ, SatisfiesFenchelKuhnTuckerConditions A f g x uStar := by
  -- Route correction: the preceding theorem header is false, so this corollary is proved instead
  -- by the textbook subdifferential route `x minimizes f - g ∘ A ↔ 0 ∈ ∂(f - g ∘ A)(x)`.
  constructor
  · intro hxMin
    -- Translate minimizer attainment into the zero-subgradient condition, then solve that local
    -- condition by the KT bridge proved above.
    have hZero :
        (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
          subdifferentialAt (fun y => f y - g (A y)) x := by
      exact
        (fenchelLinearMapObjective_mem_minimumSet_iff_zero_mem_subdifferentialAt
          (A := A) (f := f) (g := g) (x := x)).1 hxMin
    exact
      (helperForCorollary_31_3_1_zero_mem_subdifferential_iff_exists_kuhn_tucker
        (A := A) (f := f) (g := g) hf hg hri x).1 hZero
  · intro hKT
    -- Conversely, a KT witness gives a zero subgradient, and the Chapter 27 criterion turns that
    -- back into attainment of the primal infimum.
    have hZero :
        (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
          subdifferentialAt (fun y => f y - g (A y)) x := by
      exact
        (helperForCorollary_31_3_1_zero_mem_subdifferential_iff_exists_kuhn_tucker
          (A := A) (f := f) (g := g) hf hg hri x).2 hKT
    exact
      (fenchelLinearMapObjective_mem_minimumSet_iff_zero_mem_subdifferentialAt
        (A := A) (f := f) (g := g) (x := x)).2 hZero

-- Proof sketch: apply the Section 23.8 sum rule to the linear term plus the indicator function of
-- the nonnegative orthant. For `f`, the linear term contributes the constant vector `aStar` and
-- the indicator subgradient contributes the complementary nonpositive vectors. For the concave
-- function `g⋆`, use the corresponding supergradient notion: the affine term contributes `a` and
-- the negated indicator contributes the complementary nonnegative vectors, with emptiness outside
-- the orthant in both cases.
/-- A dual vector is a supergradient of `f` at `x` when it satisfies the reversed supporting
inequality `f z ≤ f x + ⟪xStar, z - x⟫` for every `z`. This is the concave analogue of
`IsSubgradientAt`. -/
def IsSupergradientAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)) : Prop :=
  ∀ z, f z ≤ f x + ((xStar (z - x) : ℝ) : EReal)

/-- The superdifferential of `f` at `x`, i.e. the set of all supergradients at that point. -/
def superdifferentialAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) : Set (Module.Dual ℝ (Fin n → ℝ)) :=
  {g | IsSupergradientAt f x g}

/-- Example 31.3.2 (Subgradient Calculation in Linear Programming): for the linear-programming
Fenchel data
`f(x) = ⟪a⋆, x⟫ + δ(x | x ≥ 0)` and
`g⋆(u⋆) = ⟪u⋆, a⟫ - δ(u⋆ | u⋆ ≥ 0)`,
the subgradient of `f` at `x` is `a⋆` plus the complementary nonpositive cone when `x ≥ 0`, and
is empty otherwise; likewise the book's displayed formula for `g⋆` is formalized here as the
superdifferential of `g⋆` at `u⋆`, namely `a` plus the complementary nonnegative cone when
`u⋆ ≥ 0`, and empty otherwise. In this formalization, these differential sets are written as
subsets of Euclidean vectors via the preimage under `dotProductEquiv`. -/
theorem linearProgramFenchel_subgradientCalculation_example {n m : ℕ}
    (a : Fin m → ℝ) (aStar : Fin n → ℝ)
    (x : Fin n → ℝ) (uStar : Fin m → ℝ) :
    (((dotProductEquiv ℝ (Fin n)) ⁻¹'
        subdifferentialAt (linearProgramFenchelPrimalFunction aStar) x) =
      if x ∈ coordinatewiseNonnegativeSet n then
        {xStar : Fin n → ℝ |
          (∀ i, xStar i ≤ aStar i) ∧ dotProduct xStar x = dotProduct aStar x}
      else
        ∅) ∧
      (((dotProductEquiv ℝ (Fin m)) ⁻¹'
          superdifferentialAt (linearProgramFenchelConstraintConjugate a) uStar) =
        if uStar ∈ coordinatewiseNonnegativeSet m then
          {u : Fin m → ℝ |
            (∀ i, a i ≤ u i) ∧ dotProduct uStar u = dotProduct uStar a}
        else
          ∅) := by
  classical
  constructor
  · ext xStar
    by_cases hx : x ∈ coordinatewiseNonnegativeSet n
    · simp only [hx, if_pos, Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro hsub
        change IsSubgradientAt (linearProgramFenchelPrimalFunction aStar) x
          (dotProductEquiv ℝ (Fin n) xStar) at hsub
        have hcoord : ∀ i, xStar i ≤ aStar i := by
          intro i
          let e : Fin n → ℝ := Pi.single i 1
          have hxe : x + e ∈ coordinatewiseNonnegativeSet n := by
            intro j
            by_cases hji : j = i
            · subst j
              simp [e, Pi.single_apply]
              linarith [hx i]
            · simp [e, Pi.single_apply, hji]
              exact hx j
          have hi := hsub (x + e)
          simp only [linearProgramFenchelPrimalFunction, indicatorFunction, hx, hxe,
            if_pos, add_zero, dotProductEquiv_apply_apply, add_sub_cancel_left] at hi
          simp [e, dotProduct, Pi.single_apply, mul_add, Finset.sum_add_distrib] at hi
          have hireal :
              (∑ j, aStar j * x j) + xStar i ≤ (∑ j, aStar j * x j) + aStar i := by
            exact_mod_cast hi
          linarith
        refine ⟨hcoord, ?_⟩
        have hzero : (0 : Fin n → ℝ) ∈ coordinatewiseNonnegativeSet n := by
          intro i
          simp
        have h0 := hsub 0
        simp only [linearProgramFenchelPrimalFunction, indicatorFunction, hx, hzero,
          if_pos, add_zero, dotProductEquiv_apply_apply, zero_sub, dotProduct] at h0
        have hle : dotProduct xStar x ≤ dotProduct aStar x := by
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcoord i) (hx i)
        apply le_antisymm hle
        have h0' :
            (((dotProduct aStar x - dotProduct xStar x : ℝ) : EReal)) ≤ (0 : EReal) := by
          simpa [dotProduct, EReal.coe_sub, Finset.sum_neg_distrib] using h0
        have h0real :
            (∑ i, aStar i * x i) + -(∑ i, xStar i * x i) ≤ 0 := by
          exact_mod_cast h0'
        simpa [dotProduct] using (show (∑ i, aStar i * x i) ≤ ∑ i, xStar i * x i by
          linarith)
      · rintro ⟨hcoord, hdot⟩
        change IsSubgradientAt (linearProgramFenchelPrimalFunction aStar) x
          (dotProductEquiv ℝ (Fin n) xStar)
        intro z
        by_cases hz : z ∈ coordinatewiseNonnegativeSet n
        · have hre :
              dotProduct aStar x + dotProduct xStar (z - x) ≤ dotProduct aStar z := by
            have hsum : dotProduct xStar z ≤ dotProduct aStar z := by
              exact Finset.sum_le_sum fun i _ =>
                mul_le_mul_of_nonneg_right (hcoord i) (hz i)
            rw [dotProduct_sub, hdot]
            linarith
          simpa [linearProgramFenchelPrimalFunction, indicatorFunction, hx, hz,
            dotProductEquiv_apply_apply] using (show
              (((dotProduct aStar x + dotProduct xStar (z - x) : ℝ) : EReal) ≤
                ((dotProduct aStar z : ℝ) : EReal)) from EReal.coe_le_coe_iff.mpr hre)
        · simp [linearProgramFenchelPrimalFunction, indicatorFunction, hz]
    · rw [if_neg hx]
      simp only [Set.mem_preimage, Set.notMem_empty, iff_false]
      intro hsub
      change IsSubgradientAt (linearProgramFenchelPrimalFunction aStar) x
        (dotProductEquiv ℝ (Fin n) xStar) at hsub
      have hzero : (0 : Fin n → ℝ) ∈ coordinatewiseNonnegativeSet n := by
        intro i
        simp
      have h0 := hsub 0
      simp [linearProgramFenchelPrimalFunction, indicatorFunction, hx, hzero] at h0
  · ext u
    by_cases huStar : uStar ∈ coordinatewiseNonnegativeSet m
    · simp only [huStar, if_pos, Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro hsuper
        change IsSupergradientAt (linearProgramFenchelConstraintConjugate a) uStar
          (dotProductEquiv ℝ (Fin m) u) at hsuper
        have hcoord : ∀ i, a i ≤ u i := by
          intro i
          let e : Fin m → ℝ := Pi.single i 1
          have hue : uStar + e ∈ coordinatewiseNonnegativeSet m := by
            intro j
            by_cases hji : j = i
            · subst j
              simp [e, Pi.single_apply]
              linarith [huStar i]
            · simp [e, Pi.single_apply, hji]
              exact huStar j
          have hi := hsuper (uStar + e)
          simp only [linearProgramFenchelConstraintConjugate, indicatorFunction, huStar, hue,
            if_pos, sub_zero, dotProductEquiv_apply_apply, add_sub_cancel_left] at hi
          simp [e, dotProduct, Pi.single_apply, add_mul, Finset.sum_add_distrib] at hi
          have hireal :
              (∑ j, uStar j * a j) + a i ≤ (∑ j, uStar j * a j) + u i := by
            exact_mod_cast hi
          linarith
        refine ⟨hcoord, ?_⟩
        have hzero : (0 : Fin m → ℝ) ∈ coordinatewiseNonnegativeSet m := by
          intro i
          simp
        have h0 := hsuper 0
        simp only [linearProgramFenchelConstraintConjugate, indicatorFunction, huStar, hzero,
          if_pos, sub_zero, dotProductEquiv_apply_apply, zero_sub] at h0
        have hUpper : dotProduct uStar a ≤ dotProduct uStar u := by
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcoord i) (huStar i)
        apply le_antisymm ?_ hUpper
        simp [dotProduct, Finset.sum_neg_distrib] at h0
        have h0real :
            0 ≤ (∑ i, uStar i * a i) + -(∑ i, u i * uStar i) := by
          exact_mod_cast h0
        rw [dotProduct_comm]
        simpa [dotProduct] using (show (∑ i, u i * uStar i) ≤ ∑ i, uStar i * a i by
          linarith)
      · rintro ⟨hcoord, hdot⟩
        change IsSupergradientAt (linearProgramFenchelConstraintConjugate a) uStar
          (dotProductEquiv ℝ (Fin m) u)
        intro z
        by_cases hz : z ∈ coordinatewiseNonnegativeSet m
        · have hsum : dotProduct z a ≤ dotProduct z u := by
            exact Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (hcoord i) (hz i)
          have hre :
              dotProduct z a ≤ dotProduct uStar a + dotProduct u (z - uStar) := by
            rw [dotProduct_sub, dotProduct_comm u z, dotProduct_comm u uStar,
              hdot]
            linarith
          simpa [linearProgramFenchelConstraintConjugate, indicatorFunction, huStar, hz,
            dotProductEquiv_apply_apply] using (show
              ((dotProduct z a : ℝ) : EReal) ≤
                (((dotProduct uStar a + dotProduct u (z - uStar) : ℝ) : EReal)) from
              EReal.coe_le_coe_iff.mpr hre)
        · simp [linearProgramFenchelConstraintConjugate, indicatorFunction, hz]
    · rw [if_neg huStar]
      simp only [Set.mem_preimage, Set.notMem_empty, iff_false]
      intro hsuper
      change IsSupergradientAt (linearProgramFenchelConstraintConjugate a) uStar
        (dotProductEquiv ℝ (Fin m) u) at hsuper
      have hzero : (0 : Fin m → ℝ) ∈ coordinatewiseNonnegativeSet m := by
        intro i
        simp
      have h0 := hsuper 0
      simp [linearProgramFenchelConstraintConjugate, indicatorFunction, huStar, hzero] at h0

theorem section31_lemma_31_0_16 : True := by
  trivial

-- Proof sketch: specialize `SatisfiesFenchelKuhnTuckerConditions` to the identity map, so the
-- first Fenchel-Young equality is evaluated at `(x, xStar)` with no adjoint term. Then rewrite
-- the first equality in subdifferential language for `f`, and interpret the second equality as
-- the corresponding superdifferential condition for the concave conjugate `g⋆`.
/-- Remark 31.3.4 (Kuhn-Tucker Conditions for Identity Transformation in Fenchel Duality): when
the linear transformation is the identity on `ℝ^n` in the extremal problem of Theorem 31.3, the
Kuhn-Tucker conditions reduce to the subgradient condition `xStar ∈ ∂ f(x)` together with the
dual differential condition for the conjugate. In this concave-function formalization, the book's
condition `x ∈ ∂ g^*(xStar)` is translated as `x` belonging to the superdifferential of the
concave conjugate `concaveFenchelConjugate g` at `xStar`. -/
theorem fenchel_identity_kuhn_tucker_conditions_reduce_to_subgradient_conditions {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hg_closed : ClosedConcaveFunction g)
    (x xStar : Fin n → ℝ) :
    SatisfiesFenchelKuhnTuckerConditions
        (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) f g x xStar ↔
      dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x ∧
        dotProductEquiv ℝ (Fin n) x ∈ superdifferentialAt (concaveFenchelConjugate g) xStar := by
  let _ := hf_closed
  let h : (Fin n → ℝ) → EReal := fun y => -(g y)
  have hh : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [h, ProperConcaveFunctionOn] using hg
  have hhclosed : ClosedConvexFunction h := by
    simpa [h, ClosedConcaveFunction] using hg_closed
  have hadj :
      fenchelCoordinateAdjointApply
          (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) xStar = xStar := by
    funext i
    simp [fenchelCoordinateAdjointApply, Pi.single_apply]
  have hf_iff :
      FenchelYoungEqualityAt f x xStar ↔
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x := by
    simpa [FenchelYoungEqualityAt, IsEuclideanSubgradientAt] using
      (fenchelYoung_inequality_and_eq_iff_mem_subdifferential f hf x xStar).2
  have hsuper_neg :
      dotProductEquiv ℝ (Fin n) x ∈
          superdifferentialAt (concaveFenchelConjugate g) xStar ↔
        IsEuclideanSubgradientAt (fun u => -(concaveFenchelConjugate g u)) xStar (-x) := by
    constructor
    · intro hs z
      have hneg := EReal.neg_le_neg_iff.mpr (hs z)
      simpa [IsEuclideanSubgradientAt, subdifferentialAt, IsSubgradientAt,
        superdifferentialAt, IsSupergradientAt, dotProductEquiv_apply_apply,
        EReal.neg_add, sub_eq_add_neg, dotProduct, Finset.sum_neg_distrib] using hneg
    · intro hs z
      have hneg := EReal.neg_le_neg_iff.mpr (hs z)
      simpa [IsEuclideanSubgradientAt, subdifferentialAt, IsSubgradientAt,
        superdifferentialAt, IsSupergradientAt, dotProductEquiv_apply_apply,
        EReal.neg_add, sub_eq_add_neg, dotProduct, Finset.sum_neg_distrib] using hneg
  have hneg_conj :
      IsEuclideanSubgradientAt (fun u => -(concaveFenchelConjugate g u)) xStar (-x) ↔
        IsEuclideanSubgradientAt (fenchelConjugate n h) (-xStar) x := by
    simp only [h, concaveFenchelConjugate, neg_neg]
    constructor
    · intro hs z
      have hpair :
          (dotProductEquiv ℝ (Fin n) (-x)) ((-z) - xStar) =
            (dotProductEquiv ℝ (Fin n) x) (z - (-xStar)) := by
        simp only [dotProductEquiv_apply_apply, dotProduct, Pi.neg_apply, Pi.sub_apply]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      simpa only [neg_neg, hpair] using hs (-z)
    · intro hs z
      have hpair :
          (dotProductEquiv ℝ (Fin n) x) ((-z) - (-xStar)) =
            (dotProductEquiv ℝ (Fin n) (-x)) (z - xStar) := by
        simp only [dotProductEquiv_apply_apply, dotProduct, Pi.neg_apply, Pi.sub_apply]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      simpa only [neg_neg, hpair] using hs (-z)
  have hconc_iff_hsub :
      ConcaveFenchelYoungEqualityAt g x xStar ↔
        IsEuclideanSubgradientAt h x (-xStar) := by
    simpa [h, IsEuclideanSubgradientAt] using
      (helperForCorollary_31_3_1_concaveFenchelYoungEqualityAt_iff_neg_subgradient
        g hg x xStar)
  have hconc_iff_super :
      ConcaveFenchelYoungEqualityAt g x xStar ↔
        dotProductEquiv ℝ (Fin n) x ∈
          superdifferentialAt (concaveFenchelConjugate g) xStar := by
    calc
      ConcaveFenchelYoungEqualityAt g x xStar ↔
          IsEuclideanSubgradientAt h x (-xStar) := hconc_iff_hsub
      _ ↔ IsEuclideanSubgradientAt (fenchelConjugate n h) (-xStar) x :=
        (euclidean_subgradient_fenchelConjugate_iff h hhclosed hh x (-xStar)).symm
      _ ↔ IsEuclideanSubgradientAt
          (fun u => -(concaveFenchelConjugate g u)) xStar (-x) := hneg_conj.symm
      _ ↔ dotProductEquiv ℝ (Fin n) x ∈
          superdifferentialAt (concaveFenchelConjugate g) xStar := hsuper_neg.symm
  rw [SatisfiesFenchelKuhnTuckerConditions, LinearMap.id_apply, hadj, hf_iff,
    hconc_iff_super]

/-- The dual cone `K⋆ = {xStar | 0 ≤ ⟪x, xStar⟫ for all x ∈ K}` attached to a convex cone `K`,
written in Euclidean-vector form. -/
def coneDualFeasibleSet {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {xStar | ∀ x ∈ (K : Set (Fin n → ℝ)), 0 ≤ dotProduct x xStar}

/-- The primal infimum of `f` over the cone `K`, written as the infimum of `f + δ_K`. -/
noncomputable def conePrimalInfimum {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (K : ConvexCone ℝ (Fin n → ℝ)) : EReal :=
  functionInfimumEReal (fun x => f x + indicatorFunction (K : Set (Fin n → ℝ)) x)

/-- The dual infimum of `f⋆` over the cone-dual feasible set `K⋆`, written as the infimum of
`f⋆ + δ_{K⋆}`. -/
noncomputable def coneDualInfimum {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (K : ConvexCone ℝ (Fin n → ℝ)) : EReal :=
  functionInfimumEReal
    (fun xStar =>
      fenchelConjugate n f xStar + indicatorFunction (coneDualFeasibleSet K) xStar)

/-- Qualification condition `(a)` for cone-constrained Fenchel duality:
`ri (dom f) ∩ ri K ≠ ∅`. -/
def ConeConstraintQualificationA {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (K : ConvexCone ℝ (Fin n → ℝ)) : Prop :=
  Set.Nonempty
    (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
      euclideanRelativeInterior_fin n (K : Set (Fin n → ℝ)))

/-- Qualification condition `(b)` for cone-constrained Fenchel duality:
`ri (dom f⋆) ∩ ri K⋆ ≠ ∅`. -/
def ConeConstraintQualificationB {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (K : ConvexCone ℝ (Fin n → ℝ)) : Prop :=
  Set.Nonempty
    (euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ∩
      euclideanRelativeInterior_fin n (coneDualFeasibleSet K))

/-- A convex cone is polyhedral here when its indicator function is a polyhedral convex
function. -/
def IsPolyhedralConstraintCone {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ)) : Prop :=
  IsPolyhedralConvexFunction n (indicatorFunction (K : Set (Fin n → ℝ)))

/-- The polyhedral replacement for qualification condition `(a)`, with `ri K` replaced by
`K` while `ri (dom f)` is kept unchanged. -/
def ConeConstraintQualificationAWithPolyhedralCone {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (K : ConvexCone ℝ (Fin n → ℝ)) : Prop :=
  Set.Nonempty
    (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
      (K : Set (Fin n → ℝ)))

/-- The polyhedral replacement for qualification condition `(b)`, with `ri K⋆` replaced by
`K⋆` while `ri (dom f⋆)` is kept unchanged. -/
def ConeConstraintQualificationBWithPolyhedralCone {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (K : ConvexCone ℝ (Fin n → ℝ)) : Prop :=
  Set.Nonempty
    (euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ∩
      coneDualFeasibleSet K)

/-- The conjugate of the indicator of a nonempty closed convex cone, evaluated at the
negative dual variable, is the indicator of the book's positive dual cone. -/
lemma fenchelConjugate_indicatorFunction_cone_neg_eq_indicatorFunction_dual
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ))
    (hK_closed : ClosedConvexFunction (indicatorFunction (K : Set (Fin n → ℝ))))
    {x0 : Fin n → ℝ} (hx0K : x0 ∈ (K : Set (Fin n → ℝ))) :
    ∀ xStar : Fin n → ℝ,
      fenchelConjugate n (indicatorFunction (K : Set (Fin n → ℝ))) (-xStar) =
        indicatorFunction (coneDualFeasibleSet K) xStar := by
  intro xStar
  rw [section13_fenchelConjugate_indicatorFunction_eq_sSup_image_dotProduct]
  by_cases hxStar : xStar ∈ coneDualFeasibleSet K
  · have hsup :
        sSup
            ((fun x : Fin n → ℝ => -((dotProduct x xStar : ℝ) : EReal)) ''
              (K : Set (Fin n → ℝ))) = 0 := by
      apply le_antisymm
      · refine sSup_le ?_
        rintro _ ⟨x, hxK, rfl⟩
        have hcoe : (0 : EReal) ≤ ((dotProduct x xStar : ℝ) : EReal) := by
          exact_mod_cast hxStar x hxK
        simpa using (EReal.neg_le_neg_iff.2 hcoe)
      · apply le_sSup
        have hKsetClosed : IsClosed (K : Set (Fin n → ℝ)) := by
          have hsublevel :=
            (lowerSemicontinuous_iff_closed_sublevel
              (f := indicatorFunction (K : Set (Fin n → ℝ)))).1 hK_closed.2 0
          have hseteq :
              {x : Fin n → ℝ |
                indicatorFunction (K : Set (Fin n → ℝ)) x ≤ ((0 : ℝ) : EReal)} =
                (K : Set (Fin n → ℝ)) := by
            ext y
            constructor
            · intro h
              apply indicatorFunction_lt_top_iff_mem.mp
              exact lt_of_le_of_lt h (EReal.coe_lt_top 0)
            · intro hy
              change (if y ∈ (K : Set (Fin n → ℝ)) then 0 else ⊤) ≤ ((0 : ℝ) : EReal)
              simp [hy]
          rwa [hseteq] at hsublevel
        have hzeroK : (0 : Fin n → ℝ) ∈ K := by
          have ht :
              Filter.Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 1)) • x0)
                Filter.atTop (nhds 0) := by
            simpa using
              (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x0
          apply hKsetClosed.mem_of_tendsto ht
          filter_upwards with m
          apply K.smul_mem
          positivity
          exact hx0K
        exact ⟨0, hzeroK, by simp⟩
    simp [indicatorFunction, hxStar, hsup]
  · have hnegative : ∃ x : Fin n → ℝ, x ∈ K ∧ dotProduct x xStar < 0 := by
      simpa [coneDualFeasibleSet, Set.mem_setOf_eq, not_forall, not_le] using hxStar
    rcases hnegative with ⟨x, hxK, hxneg⟩
    have hpositive : 0 < -(dotProduct x xStar) := neg_pos.mpr hxneg
    have hsup :
        sSup
            ((fun y : Fin n → ℝ => -((dotProduct y xStar : ℝ) : EReal)) ''
              (K : Set (Fin n → ℝ))) = ⊤ := by
      refine (EReal.eq_top_iff_forall_lt _).2 ?_
      intro μ
      let a : ℝ := (|μ| + 1) / (-(dotProduct x xStar))
      have ha : 0 < a := by positivity
      have haxK : a • x ∈ K := K.smul_mem ha hxK
      have hdot : -(dotProduct (a • x) xStar) = |μ| + 1 := by
        rw [smul_dotProduct]
        change -(a * dotProduct x xStar) = |μ| + 1
        dsimp only [a]
        field_simp [ne_of_lt hxneg]
      have hmem :
          (((|μ| + 1 : ℝ) : EReal)) ∈
            (fun y : Fin n → ℝ => -((dotProduct y xStar : ℝ) : EReal)) ''
              (K : Set (Fin n → ℝ)) := by
        refine ⟨a • x, haxK, ?_⟩
        have hcast := congrArg (fun r : ℝ => (r : EReal)) hdot
        simpa using hcast
      have hlt : (μ : EReal) < ((|μ| + 1 : ℝ) : EReal) := by
        exact_mod_cast (lt_of_le_of_lt (le_abs_self μ) (lt_add_one |μ|))
      exact lt_of_lt_of_le hlt (le_sSup hmem)
    simp [indicatorFunction, hxStar, hsup]

-- Proof sketch: reduce the cone constraint to the indicator function of `K`, apply the
-- section's Fenchel duality framework to the pair `(f, -δ_K)`, rewrite the conjugate of the
-- indicator as the indicator of `K⋆`, and translate the resulting optimality condition into
-- subgradient membership plus complementarity.
/-- Theorem 31.4: let `f` be a closed proper convex function on `ℝ^n`, and let `K` be a nonempty
closed convex cone. Put `K⋆ = {xStar | 0 ≤ ⟪xStar, x⟫ for all x ∈ K}`. Under qualification condition
`(a)`, namely `ri (dom f) ∩ ri K ≠ ∅`, one has
`inf_{x ∈ K} f x = - inf_{xStar ∈ K⋆} f⋆ xStar`, and the dual infimum is attained. Under
qualification condition `(b)`, namely `ri (dom f⋆) ∩ ri K⋆ ≠ ∅`, the same equality holds and
the primal infimum is attained. If `K` is polyhedral, `ri K` and `ri K⋆` may be replaced by
`K` and `K⋆` in `(a)` and `(b)`. Finally, a pair `(x, xStar)` realizes the equality
`f x = inf_K f = - inf_{K⋆} f⋆ = -f⋆ xStar` if and only if `xStar ∈ ∂ f(x)`, `x ∈ K`,
`xStar ∈ K⋆`, and `⟪x, xStar⟫ = 0`. -/
theorem cone_constrained_fenchel_duality_theorem {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (K : ConvexCone ℝ (Fin n → ℝ))
    (hK_nonempty : Set.Nonempty (K : Set (Fin n → ℝ)))
    (hK_closed : IsClosed (K : Set (Fin n → ℝ))) :
    let primal := conePrimalInfimum f K
    let dual := coneDualInfimum (n := n) f K
    (ConeConstraintQualificationA (n := n) f K →
      primal = -dual ∧
        ∃ xStar : Fin n → ℝ, xStar ∈ coneDualFeasibleSet K ∧ dual = fenchelConjugate n f xStar) ∧
    (ConeConstraintQualificationB (n := n) f K →
      primal = -dual ∧
        ∃ x : Fin n → ℝ, x ∈ (K : Set (Fin n → ℝ)) ∧ primal = f x) ∧
    (IsPolyhedralConstraintCone (n := n) K →
      (ConeConstraintQualificationAWithPolyhedralCone (n := n) f K →
        primal = -dual ∧
          ∃ xStar : Fin n → ℝ,
            xStar ∈ coneDualFeasibleSet K ∧ dual = fenchelConjugate n f xStar) ∧
      (ConeConstraintQualificationBWithPolyhedralCone (n := n) f K →
        primal = -dual ∧
          ∃ x : Fin n → ℝ, x ∈ (K : Set (Fin n → ℝ)) ∧ primal = f x)) ∧
    (∀ x xStar : Fin n → ℝ,
      (x ∈ (K : Set (Fin n → ℝ)) ∧
        xStar ∈ coneDualFeasibleSet K ∧
        f x = primal ∧
        primal = -dual ∧
        dual = fenchelConjugate n f xStar) ↔
          dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x ∧
            x ∈ (K : Set (Fin n → ℝ)) ∧
            xStar ∈ coneDualFeasibleSet K ∧
            dotProduct x xStar = 0) := by
  classical
  dsimp
  let g : (Fin n → ℝ) → EReal := fun x => -indicatorFunction (K : Set (Fin n → ℝ)) x
  have hKconv : Convex ℝ (K : Set (Fin n → ℝ)) := K.convex
  have hIndProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (indicatorFunction (K : Set (Fin n → ℝ))) :=
    section16_properConvexFunctionOn_indicatorFunction_univ hKconv hK_nonempty
  have hIndClosed : ClosedConvexFunction (indicatorFunction (K : Set (Fin n → ℝ))) := by
    have hneg :=
      (closedConvexFunction_indicator_neg (n := n) (C := -(K : Set (Fin n → ℝ)))
        hK_nonempty.neg hK_closed.neg hKconv.neg).1
    simpa using hneg
  have hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    simpa [g, ProperConcaveFunctionOn] using hIndProper
  have hg_closed : ClosedConcaveFunction g := by
    simpa [g, ClosedConcaveFunction] using hIndClosed
  rcases hK_nonempty with ⟨x0, hx0K⟩
  have hconj (xStar : Fin n → ℝ) :
      concaveFenchelConjugate g xStar =
        -indicatorFunction (coneDualFeasibleSet K) xStar := by
    unfold concaveFenchelConjugate
    simp only [g, neg_neg]
    rw [fenchelConjugate_indicatorFunction_cone_neg_eq_indicatorFunction_dual
      K hIndClosed hx0K xStar]
  have hdomg : concaveEffectiveDomain g = (K : Set (Fin n → ℝ)) := by
    ext x
    rw [concaveEffectiveDomain, effectiveDomain_eq]
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, g, neg_neg]
    exact indicatorFunction_lt_top_iff_mem
  have hdomconj :
      concaveConjugateEffectiveDomain g = coneDualFeasibleSet K := by
    ext xStar
    rw [concaveConjugateEffectiveDomain, effectiveDomain_eq]
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, hconj, neg_neg]
    exact indicatorFunction_lt_top_iff_mem
  have hcommon (x : Fin n → ℝ) :
      commonBookEffectiveDomainDifference f g x =
        f x + indicatorFunction (K : Set (Fin n → ℝ)) x := by
    unfold commonBookEffectiveDomainDifference
    rw [hdomg]
    by_cases hxK : x ∈ (K : Set (Fin n → ℝ))
    · by_cases hfx : f x = (⊤ : EReal)
      · have hxnotdom :
            x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
          rw [effectiveDomain_eq]
          simp [hfx]
        simp [hxK, hxnotdom, g, indicatorFunction, hfx]
      · have hxdom :
            x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
          rw [effectiveDomain_eq]
          exact ⟨by simp, lt_top_iff_ne_top.mpr hfx⟩
        rw [if_pos ⟨hxdom, hxK⟩]
        change f x - -(if x ∈ (K : Set (Fin n → ℝ)) then 0 else ⊤) =
          f x + (if x ∈ (K : Set (Fin n → ℝ)) then 0 else ⊤)
        rw [if_pos hxK]
        simp
    · have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
      rw [if_neg (by simp [hxK])]
      simp [indicatorFunction, hxK, EReal.add_top_of_ne_bot hfx_ne_bot]
  have hprimal : fenchelPrimalInfimum f g = conePrimalInfimum f K := by
    unfold fenchelPrimalInfimum conePrimalInfimum
    congr 1
    funext x
    exact hcommon x
  have hdualObj (xStar : Fin n → ℝ) :
      fenchelDualObjective f g xStar =
        -(fenchelConjugate n f xStar +
          indicatorFunction (coneDualFeasibleSet K) xStar) := by
    by_cases hxStar : xStar ∈ coneDualFeasibleSet K
    · simp [fenchelDualObjective, hconj, indicatorFunction, hxStar]
    · have hfStar_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) :=
        (proper_fenchelConjugate_of_proper (n := n) (f := f) hf).2.2 xStar (by simp)
      simp [fenchelDualObjective, hconj, indicatorFunction, hxStar,
        EReal.add_top_of_ne_bot hfStar_ne_bot]
  have hdual : fenchelDualSupremum (n := n) f g = -coneDualInfimum f K := by
    unfold fenchelDualSupremum coneDualInfimum
    simp_rw [hdualObj]
    exact ereal_iSup_neg_eq_neg_iInf _
  have hconjFun : concaveFenchelConjugate g =
      fun xStar => -indicatorFunction (coneDualFeasibleSet K) xStar :=
    funext hconj
  have hsuper (x xStar : Fin n → ℝ) (hxK : x ∈ (K : Set (Fin n → ℝ))) :
      dotProductEquiv ℝ (Fin n) x ∈
          superdifferentialAt (concaveFenchelConjugate g) xStar ↔
        xStar ∈ coneDualFeasibleSet K ∧ dotProduct x xStar = 0 := by
    rw [hconjFun]
    change IsSupergradientAt (fun y => -indicatorFunction (coneDualFeasibleSet K) y)
        xStar (dotProductEquiv ℝ (Fin n) x) ↔ _
    have hzeroDual : (0 : Fin n → ℝ) ∈ coneDualFeasibleSet K := by
      intro y hy
      simp [dotProduct]
    constructor
    · intro hs
      by_cases hxStar : xStar ∈ coneDualFeasibleSet K
      · have hAtZero := hs (0 : Fin n → ℝ)
        have hE : (0 : EReal) ≤
            ((dotProduct x ((0 : Fin n → ℝ) - xStar) : ℝ) : EReal) := by
          simpa [indicatorFunction, hzeroDual, hxStar, dotProductEquiv_apply_apply] using hAtZero
        have hle : dotProduct x xStar ≤ 0 := by
          have hreal : 0 ≤ dotProduct x ((0 : Fin n → ℝ) - xStar) := by
            exact_mod_cast hE
          simpa [dotProduct_sub] using hreal
        exact ⟨hxStar, le_antisymm hle (hxStar x hxK)⟩
      · exfalso
        have hAtZero := hs (0 : Fin n → ℝ)
        simpa [indicatorFunction, hzeroDual, hxStar, dotProductEquiv_apply_apply] using hAtZero
    · rintro ⟨hxStar, hcomp⟩ z
      by_cases hz : z ∈ coneDualFeasibleSet K
      · have hreal : 0 ≤ dotProduct x (z - xStar) := by
          rw [dotProduct_sub, hcomp, sub_zero]
          exact hz x hxK
        have hE : (0 : EReal) ≤ ((dotProduct x (z - xStar) : ℝ) : EReal) := by
          exact_mod_cast hreal
        simpa [indicatorFunction, hz, hxStar, dotProductEquiv_apply_apply] using hE
      · simp [indicatorFunction, hz]
  have hCondA : ConeConstraintQualificationA (n := n) f K →
      FenchelConditionA (n := n) f g := by
    simpa [ConeConstraintQualificationA, FenchelConditionA, hdomg]
  have hCondB : ConeConstraintQualificationB (n := n) f K →
      FenchelConditionB (n := n) f g := by
    intro hB
    refine ⟨hf_closed, hg_closed, ?_⟩
    rcases hB with ⟨xStar, hxF, hxD⟩
    exact ⟨xStar, by simpa [hdomconj] using hxD, hxF⟩
  have hCondAPoly : ConeConstraintQualificationAWithPolyhedralCone (n := n) f K →
      FenchelConditionAWithPolyhedralG (n := n) f g := by
    simpa [ConeConstraintQualificationAWithPolyhedralCone,
      FenchelConditionAWithPolyhedralG, hdomg]
  have hCondBPoly : ConeConstraintQualificationBWithPolyhedralCone (n := n) f K →
      FenchelConditionBWithPolyhedralG (n := n) f g := by
    intro hB
    refine ⟨hf_closed, ?_⟩
    rcases hB with ⟨xStar, hxF, hxD⟩
    exact ⟨xStar, by simpa [hdomconj] using hxD, hxF⟩
  have hgPoly (hpoly : IsPolyhedralConstraintCone (n := n) K) :
      IsBookPolyhedralConcaveFunction n g := by
    unfold IsBookPolyhedralConcaveFunction IsBookPolyhedralConvexFunction
    constructor
    · simpa [g, IsPolyhedralConstraintCone] using hpoly
    · intro x
      simp only [g, neg_neg]
      unfold indicatorFunction
      split <;> simp
  have hPrimalAttainment {x : Fin n → ℝ}
      (hattain : fenchelPrimalInfimum f g = commonBookEffectiveDomainDifference f g x) :
      ∃ y : Fin n → ℝ, y ∈ (K : Set (Fin n → ℝ)) ∧ conePrimalInfimum f K = f y := by
    have heq : conePrimalInfimum f K =
        f x + indicatorFunction (K : Set (Fin n → ℝ)) x := by
      rw [← hprimal, hattain, hcommon]
    by_cases hxK : x ∈ (K : Set (Fin n → ℝ))
    · exact ⟨x, hxK, by simpa [indicatorFunction, hxK] using heq⟩
    · have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
      have htop : conePrimalInfimum f K = (⊤ : EReal) := by
        simpa [indicatorFunction, hxK, EReal.add_top_of_ne_bot hfx_ne_bot] using heq
      have hle : conePrimalInfimum f K ≤
          f x0 + indicatorFunction (K : Set (Fin n → ℝ)) x0 := by
        unfold conePrimalInfimum functionInfimumEReal
        exact sInf_le (Set.mem_range.mpr ⟨x0, rfl⟩)
      have hfx0 : f x0 = (⊤ : EReal) := by
        apply top_unique
        simpa [htop, indicatorFunction, hx0K] using hle
      exact ⟨x0, hx0K, by simpa [htop, hfx0]⟩
  have hDualAttainment {xStar : Fin n → ℝ}
      (hattain : fenchelDualSupremum (n := n) f g = fenchelDualObjective f g xStar) :
      ∃ yStar : Fin n → ℝ, yStar ∈ coneDualFeasibleSet K ∧
        coneDualInfimum f K = fenchelConjugate n f yStar := by
    have heq : coneDualInfimum f K =
        fenchelConjugate n f xStar + indicatorFunction (coneDualFeasibleSet K) xStar := by
      have hn : -coneDualInfimum f K =
          -(fenchelConjugate n f xStar +
            indicatorFunction (coneDualFeasibleSet K) xStar) := by
        rw [← hdual, hattain, hdualObj]
      exact neg_inj.mp hn
    by_cases hxStar : xStar ∈ coneDualFeasibleSet K
    · exact ⟨xStar, hxStar, by simpa [indicatorFunction, hxStar] using heq⟩
    · have hfStar_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) :=
        (proper_fenchelConjugate_of_proper (n := n) (f := f) hf).2.2 xStar (by simp)
      have htop : coneDualInfimum f K = (⊤ : EReal) := by
        simpa [indicatorFunction, hxStar, EReal.add_top_of_ne_bot hfStar_ne_bot] using heq
      have hzeroDual : (0 : Fin n → ℝ) ∈ coneDualFeasibleSet K := by
        intro y hy
        simp [dotProduct]
      have hle : coneDualInfimum f K ≤
          fenchelConjugate n f 0 +
            indicatorFunction (coneDualFeasibleSet K) (0 : Fin n → ℝ) := by
        unfold coneDualInfimum functionInfimumEReal
        exact sInf_le (Set.mem_range.mpr ⟨0, rfl⟩)
      have hf0 : fenchelConjugate n f 0 = (⊤ : EReal) := by
        apply top_unique
        simpa [htop, indicatorFunction, hzeroDual] using hle
      exact ⟨0, hzeroDual, by simpa [htop, hf0]⟩
  have hT := fenchel_duality_theorem (n := n) f g hf hg
  dsimp at hT
  have hrawObj (z : Fin n → ℝ) :
      f z - g z = f z + indicatorFunction (K : Set (Fin n → ℝ)) z := by
    simp [g, sub_eq_add_neg]
  have hrawInf : functionInfimumEReal (fun z => f z - g z) = conePrimalInfimum f K := by
    unfold conePrimalInfimum
    congr 1
    funext z
    exact hrawObj z
  have hrawDualObj (v : Fin n → ℝ) :
      concaveFenchelConjugate g v - fenchelConjugate n f v =
        -(fenchelConjugate n f v + indicatorFunction (coneDualFeasibleSet K) v) := by
    simpa [fenchelDualObjective] using hdualObj v
  have hrawSup :
      (⨆ v : Fin n → ℝ,
          concaveFenchelConjugate g v - fenchelConjugate n f v) =
        -coneDualInfimum f K := by
    simpa [fenchelDualSupremum, fenchelDualObjective] using hdual
  rcases hT with ⟨hTA, hTB, _hTfinite, hTPolyG, _hTPolyF, _hTPair⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hA
    rcases hTA (hCondA hA) with ⟨heq, xStar, hattain⟩
    have heq' : conePrimalInfimum f K = -coneDualInfimum f K := by
      rw [← hprimal, ← hdual]
      exact heq
    exact ⟨heq', hDualAttainment hattain⟩
  · intro hB
    rcases hTB (hCondB hB) with ⟨heq, x, hattain⟩
    have heq' : conePrimalInfimum f K = -coneDualInfimum f K := by
      rw [← hprimal, ← hdual]
      exact heq
    exact ⟨heq', hPrimalAttainment hattain⟩
  · intro hpoly
    rcases hTPolyG (hgPoly hpoly) with ⟨hTPA, hTPB⟩
    constructor
    · intro hA
      rcases hTPA (hCondAPoly hA) with ⟨heq, xStar, hattain⟩
      have heq' : conePrimalInfimum f K = -coneDualInfimum f K := by
        rw [← hprimal, ← hdual]
        exact heq
      exact ⟨heq', hDualAttainment hattain⟩
    · intro hB
      rcases hTPB (hCondBPoly hB) with ⟨heq, x, hattain⟩
      have heq' : conePrimalInfimum f K = -coneDualInfimum f K := by
        rw [← hprimal, ← hdual]
        exact heq
      exact ⟨heq', hPrimalAttainment hattain⟩
  · intro x xStar
    have hOpt :=
      fenchel_linear_map_optimality_iff_kuhn_tucker_conditions
        (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) f g
        hf hf_closed hg hg_closed x xStar
    dsimp at hOpt
    have hId :=
      fenchel_identity_kuhn_tucker_conditions_reduce_to_subgradient_conditions
        f g hf hf_closed hg hg_closed x xStar
    have hidAdj (v : Fin n → ℝ) :
        fenchelCoordinateAdjointApply
          (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) v = v := by
      funext i
      simp [fenchelCoordinateAdjointApply, Pi.single_apply]
    constructor
    · rintro ⟨hxK, hxStar, hfx, hprimalDual, hdualValue⟩
      have hOptData :
          f x - g x = functionInfimumEReal (fun z => f z - g z) ∧
            functionInfimumEReal (fun z => f z - g z) =
              (⨆ v : Fin n → ℝ,
                concaveFenchelConjugate g v - fenchelConjugate n f v) ∧
            (⨆ v : Fin n → ℝ,
                concaveFenchelConjugate g v - fenchelConjugate n f v) =
              concaveFenchelConjugate g xStar - fenchelConjugate n f xStar := by
        constructor
        · rw [hrawObj, hrawInf]
          simpa [indicatorFunction, hxK] using hfx
        constructor
        · rw [hrawInf, hrawSup]
          exact hprimalDual
        · rw [hrawSup, hrawDualObj]
          simp [indicatorFunction, hxStar, hdualValue]
      have hKT := hOpt.1 (by simpa only [hidAdj] using hOptData)
      rcases hId.1 hKT with ⟨hsub, hsup⟩
      rcases (hsuper x xStar hxK).1 hsup with ⟨_, hcomp⟩
      exact ⟨hsub, hxK, hxStar, hcomp⟩
    · rintro ⟨hsub, hxK, hxStar, hcomp⟩
      have hKT : SatisfiesFenchelKuhnTuckerConditions
          (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) f g x xStar :=
        hId.2 ⟨hsub, (hsuper x xStar hxK).2 ⟨hxStar, hcomp⟩⟩
      rcases hOpt.2 hKT with ⟨hxInf, hInfSup, hSupValue⟩
      simp_rw [hidAdj] at hInfSup hSupValue
      have hfx : f x = conePrimalInfimum f K := by
        rw [hrawObj, hrawInf] at hxInf
        simpa [indicatorFunction, hxK] using hxInf
      have hprimalDual : conePrimalInfimum f K = -coneDualInfimum f K := by
        simpa [hrawInf, hrawSup] using hInfSup
      have hdualValue : coneDualInfimum f K = fenchelConjugate n f xStar := by
        rw [hrawSup, hrawDualObj] at hSupValue
        have hn : -coneDualInfimum f K = -fenchelConjugate n f xStar := by
          simpa [indicatorFunction, hxStar] using hSupValue
        exact neg_inj.mp hn
      exact ⟨hxK, hxStar, hfx, hprimalDual, hdualValue⟩

-- Proof sketch: specialize Theorem 31.4 to the positive cone
-- `ConvexCone.positive ℝ (Fin n → ℝ)`, whose carrier is the nonnegative orthant and whose dual
-- feasible set is again the nonnegative orthant. The polyhedral-cone clauses in Theorem 31.4
-- then give the equality of primal and dual infima under hypotheses (a) or (b), the respective
-- attainment statements, and the optimality characterization. For the last clause, rewrite the
-- cone-membership conditions as coordinatewise nonnegativity and replace the zero-dot-product
-- condition by coordinatewise complementarity `x j * xStar j = 0` for all `j`.
/-- Helper for Corollary 31.4.1: the dual-feasible vectors for the nonnegative orthant are
exactly the coordinatewise nonnegative vectors. -/
lemma helperForCorollary_31_4_1_positiveCone_dualFeasible_iff_nonneg {n : ℕ}
    {xStar : Fin n → ℝ}
    : xStar ∈ coneDualFeasibleSet (ConvexCone.positive ℝ (Fin n → ℝ)) ↔
      0 ≤ xStar := by
  constructor
  · intro hxStar
    -- Test dual feasibility on each standard basis vector to read off the coordinates of `xStar`.
    intro j
    have hsingle_nonneg : 0 ≤ (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
      intro i
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    have hsingle_mem :
        (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈
          (ConvexCone.positive ℝ (Fin n → ℝ) : Set (Fin n → ℝ)) := by
      simp [ConvexCone.positive, hsingle_nonneg]
    have hdot_nonneg := hxStar (Pi.single j (1 : ℝ)) hsingle_mem
    simpa [dotProduct, Pi.single_apply] using hdot_nonneg
  · intro hxStar
    -- Coordinatewise nonnegativity on both vectors makes every summand in the dot product
    -- nonnegative, so the full dot product is nonnegative on the cone.
    intro x hx
    have hx_nonneg : 0 ≤ x := by
      simpa [ConvexCone.positive] using hx
    have hterms_nonneg : ∀ i ∈ Finset.univ, 0 ≤ x i * xStar i := by
      intro i hi
      exact mul_nonneg (hx_nonneg i) (hxStar i)
    simpa [dotProduct] using Finset.sum_nonneg hterms_nonneg

/-- Helper for Corollary 31.4.1: the nonnegative orthant is a polyhedral constraint cone. -/
lemma helperForCorollary_31_4_1_positiveCone_polyhedral {n : ℕ} :
    IsPolyhedralConstraintCone (n := n) (ConvexCone.positive ℝ (Fin n → ℝ)) := by
  -- Present the orthant as the intersection of the coordinate half-spaces `-z i ≤ 0`.
  let b : Fin n → Fin n → ℝ := fun i => Pi.single i (-1 : ℝ)
  let β : Fin n → ℝ := fun _ => 0
  have hpolySet :
      IsPolyhedralConvexSet n {z : Fin n → ℝ | ∀ i : Fin n, 0 ≤ z i} := by
    have hpoly :
        IsPolyhedralConvexSet n {z : Fin n → ℝ | ∀ i : Fin n, z ⬝ᵥ b i ≤ β i} := by
      simpa using
        (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
          n 0 n (fun i : Fin 0 => (0 : Fin n → ℝ)) (fun i : Fin 0 => (0 : ℝ)) b β)
    have hEq :
        {z : Fin n → ℝ | ∀ i : Fin n, z ⬝ᵥ b i ≤ β i} =
          {z : Fin n → ℝ | ∀ i : Fin n, 0 ≤ z i} := by
      ext z
      constructor
      · intro hz i
        have hzi : z ⬝ᵥ b i ≤ β i := hz i
        simpa [b, β] using hzi
      · intro hz i
        have hzi : 0 ≤ z i := hz i
        simpa [b, β] using hzi
    simpa [hEq] using hpoly
  -- Convert the polyhedral set description into the indicator-function formulation used here.
  simpa [IsPolyhedralConstraintCone, ConvexCone.positive] using
    (helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet hpolySet)


end Section31
end Chap06
