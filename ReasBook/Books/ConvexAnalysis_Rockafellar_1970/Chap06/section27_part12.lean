/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part11

section Chap06
section Section27

/-- The feasible set cut out by the convex inequality system `fᵢ(x) ≤ 0` for all indices `i`. -/
def convexInequalityFeasibleSet {n : ℕ} {ι : Type*}
    (fi : ι → (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | ∀ i : ι, fi i x ≤ (0 : EReal)}

/-- The objective `f₀` and the entire constraint family `fᵢ` have no common recession direction
when every vector that is a recession direction of `f₀` and of every `fᵢ` is zero. -/
def HasNoCommonRecessionDirectionsWithConstraintFamily {n : ℕ} {ι : Type*}
    (f₀ : (Fin n → ℝ) → EReal) (fi : ι → (Fin n → ℝ) → EReal) : Prop :=
  ∀ y : Fin n → ℝ, IsRecessionDirection f₀ y → (∀ i : ι, IsRecessionDirection (fi i) y) → y = 0

/-- A finite polyhedral subfamily controls common recession directions when there is a finite
index subset `I₀` such that each `fᵢ` with `i ∈ I₀` is polyhedral convex, and every direction
common to `f₀` and all constraint functions `fᵢ` is a direction of constancy of `f₀` and of
every remaining constraint function `fᵢ` with `i ∉ I₀`. -/
def FinitePolyhedralSubfamilyControlsCommonRecessionDirections {n : ℕ} {ι : Type*}
    (f₀ : (Fin n → ℝ) → EReal) (fi : ι → (Fin n → ℝ) → EReal) : Prop :=
  ∃ I₀ : Set ι, I₀.Finite ∧
    (∀ i : ι, i ∈ I₀ → IsPolyhedralConvexFunction n (fi i)) ∧
    ∀ y : Fin n → ℝ, IsRecessionDirection f₀ y →
      (∀ i : ι, IsRecessionDirection (fi i) y) →
      IsDirectionOfConstancy f₀ y ∧
        ∀ i : ι, i ∉ I₀ → IsDirectionOfConstancy (fi i) y

/-- Helper for Corollary 6.27.5: the feasible set of the inequality system is exactly the
intersection of the zero-sublevels, so it is closed and convex. -/
lemma helperForCorollary_6_27_5_feasibleSet_iInter_closedConvex
    {n : ℕ} {ι : Type*}
    (fi : ι → (Fin n → ℝ) → EReal)
    (hfi_closed : ∀ i : ι, ClosedConvexFunction (fi i)) :
    convexInequalityFeasibleSet fi = ⋂ i : ι, sublevelSetEReal (fi i) 0 ∧
      IsClosed (convexInequalityFeasibleSet fi) ∧
      Convex ℝ (convexInequalityFeasibleSet fi) := by
  have hCeq : convexInequalityFeasibleSet fi = ⋂ i : ι, sublevelSetEReal (fi i) 0 := by
    -- Unpack the feasible inequalities into membership in each zero-sublevel.
    ext x
    simp [convexInequalityFeasibleSet, sublevelSetEReal]
  constructor
  · exact hCeq
  · constructor
    · -- Closedness is inherited from the closed zero-sublevels by intersection.
      have hclosed_each : ∀ i : ι, IsClosed (sublevelSetEReal (fi i) 0) := by
        intro i
        exact
          (lowerSemicontinuous_iff_closed_sublevel (f := fi i)).1
            (hfi_closed i).2 0
      rw [hCeq]
      exact isClosed_iInter hclosed_each
    · -- Convexity is inherited from the convex zero-sublevels by intersection.
      have hconv_each : ∀ i : ι, Convex ℝ (sublevelSetEReal (fi i) 0) := by
        intro i
        simpa [sublevelSetEReal] using
          (convexFunction_level_sets_convex
            (f := fi i) (hfi_closed i).1 (α := (0 : EReal))).2
      rw [hCeq]
      exact convex_iInter hconv_each

/-- Helper for Corollary 6.27.5: the recession cone of the feasible set is the intersection of
the recession cones of the zero-sublevel constraints. -/
lemma helperForCorollary_6_27_5_feasibleSet_recessionCone_iInter
    {n : ℕ} {ι : Type*}
    (fi : ι → (Fin n → ℝ) → EReal)
    (hfi_closed : ∀ i : ι, ClosedConvexFunction (fi i))
    (hconsistent : Set.Nonempty (convexInequalityFeasibleSet fi)) :
    Set.recessionCone (convexInequalityFeasibleSet fi) =
      ⋂ i : ι, Set.recessionCone (sublevelSetEReal (fi i) 0) := by
  rcases
      helperForCorollary_6_27_5_feasibleSet_iInter_closedConvex
        (fi := fi) hfi_closed with
    ⟨hCeq, hCclosed, hCconvex⟩
  have hclosed_each : ∀ i : ι, IsClosed (sublevelSetEReal (fi i) 0) := by
    intro i
    exact
      (lowerSemicontinuous_iff_closed_sublevel (f := fi i)).1
        (hfi_closed i).2 0
  have hconv_each : ∀ i : ι, Convex ℝ (sublevelSetEReal (fi i) 0) := by
    intro i
    simpa [sublevelSetEReal] using
      (convexFunction_level_sets_convex
        (f := fi i) (hfi_closed i).1 (α := (0 : EReal))).2
  have hne_inter : Set.Nonempty (⋂ i : ι, sublevelSetEReal (fi i) 0) := by
    rcases hconsistent with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [hCeq] using hx
  -- Rewrite the feasible set as an intersection and apply the general recession-cone theorem.
  calc
    Set.recessionCone (convexInequalityFeasibleSet fi) =
        Set.recessionCone (⋂ i : ι, sublevelSetEReal (fi i) 0) := by
          rw [hCeq]
    _ = ⋂ i : ι, Set.recessionCone (sublevelSetEReal (fi i) 0) :=
      helperForTheorem_21_3_recessionCone_iInter_eq_iInter_fin
        (C := fun i : ι => sublevelSetEReal (fi i) 0) hclosed_each hconv_each hne_inter

/-- Helper for Corollary 6.27.5: a recession direction of a nonempty zero-sublevel of a closed
proper convex function is a recession direction of the function itself. -/
lemma helperForCorollary_6_27_5_zeroSublevel_recession_implies_functionRecession
    {n : ℕ} (g : (Fin n → ℝ) → EReal)
    (hg_closed : ClosedConvexFunction g)
    (hg_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hzero_nonempty : (sublevelSetEReal g 0).Nonempty)
    {y : Fin n → ℝ}
    (hy : y ∈ Set.recessionCone (sublevelSetEReal g 0)) :
    IsRecessionDirection g y := by
  rcases closedProperConvexFunction_minimum_characterizations g hg_closed hg_proper with
    ⟨_hA, _hB, _hC, _hD, _hE, hF, _hG, _hH, _hI⟩
  rcases hF with ⟨_hSublevelEq, hFrest⟩
  rcases hFrest with ⟨_hMinBridge, hFrest'⟩
  rcases hFrest' with ⟨hSublevelRec, _hPolar⟩
  -- Transport the set-level recession hypothesis through the shared recession-cone description.
  have hyE : y ∈ recessionConeEReal (F := Fin n → ℝ) g := by
    rw [hSublevelRec 0 hzero_nonempty] at hy
    exact hy
  simpa [recessionConeEReal, IsRecessionDirection, recessionFunctionEReal,
    recessionFunction, erealDom, effectiveDomain_eq] using hyE

/-- Helper for Corollary 6.27.5: the mixed Helly family combines the zero-sublevels of the
constraint functions with the real sublevels of the objective. -/
def helperForCorollary_6_27_5_mixedLevelFamily
    {n : ℕ} {ι : Type*}
    (f₀ : (Fin n → ℝ) → EReal)
    (fi : ι → (Fin n → ℝ) → EReal)
    (β : ℕ → ℝ) :
    Sum ι ℕ → Set (Fin n → ℝ)
  | Sum.inl i => sublevelSetEReal (fi i) 0
  | Sum.inr k => sublevelSetEReal f₀ (β k)

/-- Helper for Corollary 6.27.5: the recession cone of any nonempty real sublevel of a closed
proper convex function agrees with the recession cone of the function. -/
lemma helperForCorollary_6_27_5_sublevel_recession_iff_functionRecession
    {n : ℕ} (g : (Fin n → ℝ) → EReal)
    (hg_closed : ClosedConvexFunction g)
    (hg_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    {α : ℝ}
    (hα_nonempty : (sublevelSetEReal g α).Nonempty)
    {y : Fin n → ℝ} :
    y ∈ Set.recessionCone (sublevelSetEReal g α) ↔ IsRecessionDirection g y := by
  rcases closedProperConvexFunction_minimum_characterizations g hg_closed hg_proper with
    ⟨_hA, _hB, _hC, _hD, _hE, hF, _hG, _hH, _hI⟩
  rcases hF with ⟨_hSublevelEq, hFrest⟩
  rcases hFrest with ⟨_hMinBridge, hFrest'⟩
  rcases hFrest' with ⟨hSublevelRec, _hPolar⟩
  constructor
  · intro hy
    -- Transport the set-level recession statement through the shared sublevel description.
    have hyE : y ∈ recessionConeEReal (F := Fin n → ℝ) g := by
      rw [hSublevelRec α hα_nonempty] at hy
      exact hy
    simpa [recessionConeEReal, IsRecessionDirection, recessionFunctionEReal,
      recessionFunction, erealDom, effectiveDomain_eq] using hyE
  · intro hy
    -- The converse direction reads the function-level recession statement back on the sublevel.
    have hyE : y ∈ recessionConeEReal (F := Fin n → ℝ) g := by
      simpa [recessionConeEReal, IsRecessionDirection, recessionFunctionEReal,
        recessionFunction, erealDom, effectiveDomain_eq] using hy
    rw [hSublevelRec α hα_nonempty]
    exact hyE

/-- Helper for Corollary 6.27.5: a direction of constancy of a closed proper convex function lies
in the lineality space of every nonempty real sublevel. -/
lemma helperForCorollary_6_27_5_constancy_lineality_of_nonempty_sublevel
    {n : ℕ} (g : (Fin n → ℝ) → EReal)
    (hg_closed : ClosedConvexFunction g)
    (hg_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    {α : ℝ}
    (hα_nonempty : (sublevelSetEReal g α).Nonempty)
    {y : Fin n → ℝ}
    (hy_const : IsDirectionOfConstancy g y) :
    y ∈ (-Set.recessionCone (sublevelSetEReal g α)) ∩
      Set.recessionCone (sublevelSetEReal g α) := by
  -- Convert the two constancy directions into the corresponding two recession directions.
  have hy_pos : IsRecessionDirection g y := by
    simpa [IsRecessionDirection, hy_const.1]
  have hy_neg : IsRecessionDirection g (-y) := by
    simpa [IsRecessionDirection, hy_const.2]
  have hy_mem :
      y ∈ Set.recessionCone (sublevelSetEReal g α) :=
    (helperForCorollary_6_27_5_sublevel_recession_iff_functionRecession
      (g := g) hg_closed hg_proper hα_nonempty).2 hy_pos
  have hneg_mem :
      -y ∈ Set.recessionCone (sublevelSetEReal g α) :=
    (helperForCorollary_6_27_5_sublevel_recession_iff_functionRecession
      (g := g) hg_closed hg_proper hα_nonempty).2 hy_neg
  exact ⟨by simpa [Set.mem_neg] using hneg_mem, hy_mem⟩

/-- Helper for Corollary 6.27.5: the zero-sublevel of a proper polyhedral convex function is a
polyhedral convex set. -/
lemma helperForCorollary_6_27_5_zeroSublevel_polyhedral_of_polyhedralConstraint
    {n : ℕ} (g : (Fin n → ℝ) → EReal)
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    IsPolyhedralConvexSet n (sublevelSetEReal g 0) := by
  have hnonbot : ∀ x : Fin n → ℝ, g x ≠ (⊥ : EReal) := by
    intro x
    exact hg_proper.2.2 x (by simp)
  rcases
      (polyhedral_convex_function_iff_max_affine_plus_indicator
        (n := n) (f := g)).1 ⟨hg_poly, hnonbot⟩ with
    ⟨k, m, b, β, hk, hrepr⟩
  refine (isPolyhedralConvexSet_iff_exists_finite_halfspaces n (sublevelSetEReal g 0)).2 ?_
  refine ⟨m, b, β, ?_⟩
  ext x
  let Sx : Set ℝ :=
    {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i}
  let D : Set (Fin n → ℝ) :=
    {y | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
  constructor
  · intro hx
    have hxle : g x ≤ (0 : EReal) := by
      simpa [sublevelSetEReal] using hx
    have hxrepr :
        (((sSup Sx : ℝ)) : EReal) + indicatorFunction (C := D) x ≤ (0 : EReal) := by
      simpa [hrepr, Sx, D] using hxle
    have hxD : x ∈ D := by
      by_contra hxD
      simp [indicatorFunction, hxD] at hxrepr
    refine Set.mem_iInter.mpr ?_
    intro i
    by_cases hi : (i : ℕ) < k
    · have hSxFinite : Set.Finite Sx := by
        let T : Finset ℝ := Finset.univ.image (fun i : Fin m => (∑ j, x j * b i j) - β i)
        refine T.finite_toSet.subset ?_
        intro r hr
        rcases hr with ⟨j, _hj, hrfl⟩
        exact by
          simp [T]
          exact ⟨j, by simpa [hrfl]⟩
      have hSupLeEReal : (((sSup Sx : ℝ)) : EReal) ≤ (0 : EReal) := by
        simpa [indicatorFunction, hxD] using hxrepr
      have hSupLe : sSup Sx ≤ 0 := EReal.coe_le_coe_iff.mp hSupLeEReal
      have hiLeSup : (∑ j, x j * b i j) - β i ≤ sSup Sx := by
        exact le_csSup hSxFinite.bddAbove ⟨i, hi, rfl⟩
      have hiLe : (∑ j, x j * b i j) ≤ β i := by
        linarith
      simpa [closedHalfSpaceLE, dotProduct] using hiLe
    · have hiLe : (∑ j, x j * b i j) ≤ β i := hxD i (le_of_not_gt hi)
      simpa [closedHalfSpaceLE, dotProduct] using hiLe
  · intro hx
    have hxAll : ∀ i : Fin m, (∑ j, x j * b i j) ≤ β i := by
      intro i
      have hmem : x ∈ closedHalfSpaceLE n (b i) (β i) := Set.mem_iInter.mp hx i
      simpa [closedHalfSpaceLE, dotProduct] using hmem
    have hxD : x ∈ D := by
      intro i hi
      exact hxAll i
    have hSxFinite : Set.Finite Sx := by
      let T : Finset ℝ := Finset.univ.image (fun i : Fin m => (∑ j, x j * b i j) - β i)
      refine T.finite_toSet.subset ?_
      intro r hr
      rcases hr with ⟨j, _hj, hrfl⟩
      exact by
        simp [T]
        exact ⟨j, by simpa [hrfl]⟩
    have hSupLe : sSup Sx ≤ 0 := by
      by_cases hSx : Sx.Nonempty
      · refine csSup_le hSx ?_
        intro r hr
        rcases hr with ⟨i, hi, rfl⟩
        have hiLe : (∑ j, x j * b i j) ≤ β i := hxAll i
        linarith
      · have hSxEmpty : Sx = ∅ := Set.not_nonempty_iff_eq_empty.mp hSx
        simp [hSxEmpty]
    have hxle : g x ≤ (0 : EReal) := by
      have hSupLeEReal : (((sSup Sx : ℝ)) : EReal) + indicatorFunction (C := D) x ≤ (0 : EReal) := by
        have hSupLeEReal' : (((sSup Sx : ℝ)) : EReal) ≤ (0 : EReal) := by
          exact_mod_cast hSupLe
        simpa [indicatorFunction, hxD] using hSupLeEReal'
      simpa [hrepr, Sx, D] using hSupLeEReal
    simpa [sublevelSetEReal] using hxle

/-- Helper for Corollary 6.27.5: the mixed family has the same memberwise closedness, convexity,
nonemptiness, and finite-intersection witness package as in the `Option ℕ` proof of
Theorem 6.27.4. -/
lemma helperForCorollary_6_27_5_mixedLevelFamily_finiteIntersection_packages
    {n : ℕ} {ι : Type*} (f₀ : (Fin n → ℝ) → EReal)
    (fi : ι → (Fin n → ℝ) → EReal)
    (hf₀_closed : ClosedConvexFunction f₀)
    (hfi_closed : ∀ i : ι, ClosedConvexFunction (fi i))
    (hconsistent : Set.Nonempty (convexInequalityFeasibleSet fi))
    (β : ℕ → ℝ)
    (hβmono : ∀ {k l : ℕ}, k ≤ l → (β l : EReal) ≤ (β k : EReal))
    (hβpts :
      ∀ k : ℕ,
        ∃ x : Fin n → ℝ, x ∈ convexInequalityFeasibleSet fi ∧ f₀ x ≤ (β k : EReal)) :
    let Aβ := helperForCorollary_6_27_5_mixedLevelFamily f₀ fi β
    (∀ j : Sum ι ℕ, (Aβ j).Nonempty) ∧
      (∀ j : Sum ι ℕ, IsClosed (Aβ j)) ∧
      (∀ j : Sum ι ℕ, Convex ℝ (Aβ j)) ∧
      (∀ s : Finset (Sum ι ℕ), s.card ≤ n + 1 →
        ∃ x : Fin n → ℝ, ∀ j ∈ s, x ∈ Aβ j) := by
  classical
  let Aβ := helperForCorollary_6_27_5_mixedLevelFamily f₀ fi β
  have hNonempty : ∀ j : Sum ι ℕ, (Aβ j).Nonempty := by
    intro j
    cases j with
    | inl i =>
        rcases hconsistent with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        simpa [Aβ, helperForCorollary_6_27_5_mixedLevelFamily, sublevelSetEReal,
          convexInequalityFeasibleSet] using hx i
    | inr k =>
        rcases hβpts k with ⟨x, _hxC, hxLe⟩
        exact ⟨x, by
          simpa [Aβ, helperForCorollary_6_27_5_mixedLevelFamily, sublevelSetEReal] using hxLe⟩
  have hClosed : ∀ j : Sum ι ℕ, IsClosed (Aβ j) := by
    intro j
    cases j with
    | inl i =>
        simpa [Aβ, helperForCorollary_6_27_5_mixedLevelFamily] using
          (lowerSemicontinuous_iff_closed_sublevel (f := fi i)).1 (hfi_closed i).2 0
    | inr k =>
        simpa [Aβ, helperForCorollary_6_27_5_mixedLevelFamily] using
          (lowerSemicontinuous_iff_closed_sublevel (f := f₀)).1 hf₀_closed.2 (β k)
  have hConvex : ∀ j : Sum ι ℕ, Convex ℝ (Aβ j) := by
    intro j
    cases j with
    | inl i =>
        simpa [Aβ, helperForCorollary_6_27_5_mixedLevelFamily, sublevelSetEReal] using
          (convexFunction_level_sets_convex
            (f := fi i) (hfi_closed i).1 (α := (0 : EReal))).2
    | inr k =>
        simpa [Aβ, helperForCorollary_6_27_5_mixedLevelFamily, sublevelSetEReal] using
          (convexFunction_level_sets_convex
            (f := f₀) hf₀_closed.1 (α := ((β k : ℝ) : EReal))).2
  have hFiniteIntersection :
      ∀ s : Finset (Sum ι ℕ), s.card ≤ n + 1 →
        ∃ x : Fin n → ℝ, ∀ j ∈ s, x ∈ Aβ j := by
    intro s _hs
    let γ : Sum ι ℕ → ℕ := fun j =>
      match j with
      | Sum.inl _ => 0
      | Sum.inr k => k + 1
    let K : ℕ := s.sup γ
    by_cases hK : K = 0
    · rcases hconsistent with ⟨x, hxC⟩
      refine ⟨x, ?_⟩
      intro j hj
      cases j with
      | inl i =>
          simpa [Aβ, helperForCorollary_6_27_5_mixedLevelFamily, sublevelSetEReal,
            convexInequalityFeasibleSet] using hxC i
      | inr k =>
          have hkLe : k + 1 ≤ K := by
            simpa [γ, K] using (Finset.le_sup hj : γ (Sum.inr k) ≤ s.sup γ)
          exact False.elim (by omega)
    · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
      let kMax : ℕ := K - 1
      rcases hβpts kMax with ⟨x, hxC, hxLeMax⟩
      refine ⟨x, ?_⟩
      intro j hj
      cases j with
      | inl i =>
          simpa [Aβ, helperForCorollary_6_27_5_mixedLevelFamily, sublevelSetEReal,
            convexInequalityFeasibleSet] using hxC i
      | inr k =>
          have hkSuccLe : k + 1 ≤ K := by
            simpa [γ, K] using (Finset.le_sup hj : γ (Sum.inr k) ≤ s.sup γ)
          have hkLeMax : k ≤ kMax := by
            dsimp [kMax]
            exact Nat.le_pred_of_lt (Nat.succ_le_iff.mp hkSuccLe)
          have hxLek : f₀ x ≤ (β k : EReal) := le_trans hxLeMax (hβmono hkLeMax)
          simpa [Aβ, helperForCorollary_6_27_5_mixedLevelFamily, sublevelSetEReal] using hxLek
  exact ⟨hNonempty, hClosed, hConvex, hFiniteIntersection⟩

/-- Helper for Corollary 6.27.5: the mixed Helly family satisfies the weaker recession package
coming from the finite distinguished polyhedral subfamily and the constancy conclusion outside it. -/
lemma helperForCorollary_6_27_5_mixedLevelFamily_weakRecessionPackage
    {n : ℕ} {ι : Type*} (f₀ : (Fin n → ℝ) → EReal)
    (fi : ι → (Fin n → ℝ) → EReal)
    (hf₀_closed : ClosedConvexFunction f₀)
    (hf₀_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₀)
    (hfi_closed : ∀ i : ι, ClosedConvexFunction (fi i))
    (hfi_proper : ∀ i : ι, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fi i))
    (hconsistent : Set.Nonempty (convexInequalityFeasibleSet fi))
    (β : ℕ → ℝ)
    (hβpts :
      ∀ k : ℕ,
        ∃ x : Fin n → ℝ, x ∈ convexInequalityFeasibleSet fi ∧ f₀ x ≤ (β k : EReal))
    (hcontrol : FinitePolyhedralSubfamilyControlsCommonRecessionDirections f₀ fi) :
    HasHellyWeakRecessionHypothesis (n := n)
      (helperForCorollary_6_27_5_mixedLevelFamily f₀ fi β) := by
  classical
  rcases hcontrol with ⟨I₀, hI₀finite, hI₀poly, hConstCommon⟩
  let I₀fin : Finset ι := hI₀finite.toFinset
  have hzero_nonempty : ∀ i : ι, (sublevelSetEReal (fi i) 0).Nonempty := by
    rcases hconsistent with ⟨x, hx⟩
    intro i
    refine ⟨x, ?_⟩
    simpa [sublevelSetEReal, convexInequalityFeasibleSet] using hx i
  have hObjectiveRec :
      ∀ {d : Fin n → ℝ},
        d ∈ Set.recessionCone
            (helperForCorollary_6_27_5_mixedLevelFamily f₀ fi β (Sum.inr 0)) →
          IsRecessionDirection f₀ d := by
    intro d hd
    rcases hβpts 0 with ⟨x0, _hx0C, hx0Le⟩
    have hβ0nonempty : (sublevelSetEReal f₀ (β 0)).Nonempty := by
      exact ⟨x0, by simpa [sublevelSetEReal] using hx0Le⟩
    exact
      (helperForCorollary_6_27_5_sublevel_recession_iff_functionRecession
        (g := f₀) hf₀_closed hf₀_proper hβ0nonempty).1
        (by simpa [helperForCorollary_6_27_5_mixedLevelFamily] using hd)
  have hConstraintRec :
      ∀ {d : Fin n → ℝ}, (∀ i : ι,
        d ∈ Set.recessionCone
          (helperForCorollary_6_27_5_mixedLevelFamily f₀ fi β (Sum.inl i))) →
          ∀ i : ι, IsRecessionDirection (fi i) d := by
    intro d hdAll i
    exact
      helperForCorollary_6_27_5_zeroSublevel_recession_implies_functionRecession
        (g := fi i) (hg_closed := hfi_closed i) (hg_proper := hfi_proper i)
        (hzero_nonempty := hzero_nonempty i)
        (by simpa [helperForCorollary_6_27_5_mixedLevelFamily] using hdAll i)
  let J₀ : Finset (Sum ι ℕ) := I₀fin.image (fun x : ι => (Sum.inl x : Sum ι ℕ))
  refine ⟨J₀, ?_, ?_⟩
  · intro j hj
    have hj' : j ∈ I₀fin.image (fun x : ι => (Sum.inl x : Sum ι ℕ)) := by
      simpa [J₀] using hj
    rcases Finset.mem_image.mp hj' with
      ⟨i, hi, rfl⟩
    have hiI₀ : i ∈ I₀ := by
      simpa [I₀fin] using hi
    exact
      helperForCorollary_6_27_5_zeroSublevel_polyhedral_of_polyhedralConstraint
        (g := fi i) (hg_poly := hI₀poly i hiI₀) (hg_proper := hfi_proper i)
  · intro d hdAll j hj
    have hdRec₀ : IsRecessionDirection f₀ d := hObjectiveRec (hdAll (Sum.inr 0))
    have hdRecFi : ∀ i : ι, IsRecessionDirection (fi i) d := by
      intro i
      exact hConstraintRec (fun i' => hdAll (Sum.inl i')) i
    have hConst := hConstCommon d hdRec₀ hdRecFi
    cases j with
    | inl i =>
        have hiNotI₀ : i ∉ I₀ := by
          intro hiI₀
          have hiMem : i ∈ I₀fin := by
            simpa [I₀fin] using hiI₀
          have : Sum.inl i ∈ J₀ := by
            simpa [J₀] using (Finset.mem_image.mpr ⟨i, hiMem, rfl⟩ :
              Sum.inl i ∈ I₀fin.image (fun x : ι => (Sum.inl x : Sum ι ℕ)))
          exact hj this
        have hiConst : IsDirectionOfConstancy (fi i) d := hConst.2 i hiNotI₀
        simpa [helperForCorollary_6_27_5_mixedLevelFamily] using
          helperForCorollary_6_27_5_constancy_lineality_of_nonempty_sublevel
            (g := fi i) (hg_closed := hfi_closed i) (hg_proper := hfi_proper i)
            (hα_nonempty := hzero_nonempty i) hiConst
    | inr k =>
        rcases hβpts k with ⟨xk, _hxkC, hxkLe⟩
        have hβknonempty : (sublevelSetEReal f₀ (β k)).Nonempty := by
          exact ⟨xk, by simpa [sublevelSetEReal] using hxkLe⟩
        simpa [helperForCorollary_6_27_5_mixedLevelFamily] using
          helperForCorollary_6_27_5_constancy_lineality_of_nonempty_sublevel
            (g := f₀) (hg_closed := hf₀_closed) (hg_proper := hf₀_proper)
            (hα_nonempty := hβknonempty) hConst.1

/-- Helper for Corollary 6.27.5: the finite-polyhedral-subfamily branch must be handled by the
mixed `Sum ι ℕ` Helly family described in the book proof and in Agent C's plan. -/
lemma helperForCorollary_6_27_5_finitePolyhedralSubfamily_branch
    {n : ℕ} {ι : Type*} (f₀ : (Fin n → ℝ) → EReal)
    (fi : ι → (Fin n → ℝ) → EReal)
    (hf₀_closed : ClosedConvexFunction f₀)
    (hf₀_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₀)
    (hfi_closed : ∀ i : ι, ClosedConvexFunction (fi i))
    (hfi_proper : ∀ i : ι, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fi i))
    (hconsistent : Set.Nonempty (convexInequalityFeasibleSet fi))
    (hcontrol : FinitePolyhedralSubfamilyControlsCommonRecessionDirections f₀ fi) :
    AttainsInfimumOn f₀ (convexInequalityFeasibleSet fi) := by
  classical
  let C : Set (Fin n → ℝ) := convexInequalityFeasibleSet fi
  by_cases hallTop : ∀ x : Fin n → ℝ, x ∈ C → f₀ x = (⊤ : EReal)
  · -- If every feasible objective value is `⊤`, the constrained infimum is attained trivially.
    exact
      helperForTheorem_6_27_4_trivial_attainment_of_all_top_on_C
        (h := f₀) (C := C) hconsistent hallTop
  · have hnotbot : ∀ x : Fin n → ℝ, f₀ x ≠ (⊥ : EReal) := by
      intro x
      exact hf₀_proper.2.2 x (by simp)
    have hfinitePoint : ∃ x0 : Fin n → ℝ, x0 ∈ C ∧ f₀ x0 < (⊤ : EReal) := by
      by_contra hNoFinite
      push_neg at hNoFinite
      apply hallTop
      intro x hxC
      by_contra hxneTop
      exact
        (not_le_of_gt (lt_top_iff_ne_top.mpr hxneTop))
          (hNoFinite x hxC)
    rcases hfinitePoint with ⟨x0, hx0C, hx0Top⟩
    have hBelowEveryLevel_of_not_lower :
        (¬ ∃ m : ℝ, ∀ x : Fin n → ℝ, x ∈ C → (m : EReal) ≤ f₀ x) →
          ∀ m : ℝ, ∃ x : Fin n → ℝ, x ∈ C ∧ f₀ x < (m : EReal) := by
      intro hNoLower m
      by_contra hNoPoint
      push_neg at hNoPoint
      exact hNoLower ⟨m, by
        intro x hxC
        exact hNoPoint x hxC⟩
    have hLowerBound : ∃ m : ℝ, ∀ x : Fin n → ℝ, x ∈ C → (m : EReal) ≤ f₀ x := by
      by_contra hNoLower
      have hBelowEveryLevel := hBelowEveryLevel_of_not_lower hNoLower
      let βLower : ℕ → ℝ := fun k => -(k : ℝ)
      have hβLowerMono :
          ∀ {k l : ℕ}, k ≤ l → (βLower l : EReal) ≤ (βLower k : EReal) := by
        intro k l hkl
        simpa [βLower] using
          (show ((-(l : ℝ)) : EReal) ≤ ((-(k : ℝ)) : EReal) by
            exact_mod_cast
              (neg_le_neg (show (k : ℝ) ≤ l by exact_mod_cast hkl)))
      have hβLowerPts :
          ∀ k : ℕ, ∃ x : Fin n → ℝ, x ∈ C ∧ f₀ x ≤ (βLower k : EReal) := by
        intro k
        rcases hBelowEveryLevel (βLower k) with ⟨x, hxC, hxLt⟩
        exact ⟨x, hxC, le_of_lt hxLt⟩
      rcases
          helperForCorollary_6_27_5_mixedLevelFamily_finiteIntersection_packages
            (f₀ := f₀) (fi := fi) hf₀_closed hfi_closed hconsistent βLower
            hβLowerMono hβLowerPts with
        ⟨hNonempty, hClosed, hConvex, hFiniteIntersection⟩
      obtain ⟨xBad, hxBadAll⟩ :=
        theorem21_5_helly_theorem_under_weaker_recession_hypothesis
          (C := helperForCorollary_6_27_5_mixedLevelFamily f₀ fi βLower)
          (hCnonempty := hNonempty)
          (hCclosed := hClosed)
          (hCconvex := hConvex)
          (hWeakerRecession :=
            helperForCorollary_6_27_5_mixedLevelFamily_weakRecessionPackage
              (f₀ := f₀) (fi := fi) hf₀_closed hf₀_proper hfi_closed hfi_proper
              hconsistent βLower hβLowerPts hcontrol)
          (hFiniteIntersectionNonempty := hFiniteIntersection)
      have hxBadAtZero : f₀ xBad ≤ (0 : EReal) := by
        simpa [helperForCorollary_6_27_5_mixedLevelFamily, sublevelSetEReal, βLower] using
          hxBadAll (Sum.inr 0)
      have hxBadTop : f₀ xBad ≠ (⊤ : EReal) := by
        intro hxTop
        have : (⊤ : EReal) ≤ (0 : EReal) := by
          simpa [hxTop] using hxBadAtZero
        exact (not_top_le_coe 0) this
      let a : ℝ := (f₀ xBad).toReal
      let k : ℕ := Nat.ceil (-a) + 1
      have hkNot : ¬ f₀ xBad ≤ ((-(k : ℝ)) : EReal) := by
        have hacoe : (((a : ℝ) : EReal)) = f₀ xBad := by
          simpa [a] using EReal.coe_toReal (x := f₀ xBad) hxBadTop (hnotbot xBad)
        have hkReal : -a < (k : ℝ) := by
          have : -a < ((Nat.ceil (-a) : ℕ) + 1 : ℕ) := by
            have hceil : -a ≤ Nat.ceil (-a) := Nat.le_ceil (-a)
            have : -a < (Nat.ceil (-a) : ℝ) + 1 := by
              linarith
            exact_mod_cast this
          simpa [k] using this
        have hkReal' : (-(k : ℝ)) < a := by
          linarith
        have hkLt : ((-(k : ℝ)) : EReal) < f₀ xBad := by
          rw [← hacoe]
          exact_mod_cast hkReal'
        exact not_le_of_gt hkLt
      have hxBadAtK : f₀ xBad ≤ (βLower k : EReal) := by
        simpa [helperForCorollary_6_27_5_mixedLevelFamily, sublevelSetEReal] using
          hxBadAll (Sum.inr k)
      exact hkNot (by simpa [βLower] using hxBadAtK)
    let infC : EReal := ⨅ y : C, f₀ y
    have hInfFinite : IsFiniteEReal infC := by
      constructor
      · have hUpper : infC ≤ f₀ x0 := by
          simpa [infC] using (iInf_le (fun y : C => f₀ y) ⟨x0, hx0C⟩)
        exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hUpper hx0Top)
      · rcases hLowerBound with ⟨m, hm⟩
        have hLower : (m : EReal) ≤ infC := by
          refine le_iInf ?_
          intro y
          exact hm y y.property
        exact ne_of_gt (lt_of_lt_of_le (by simp) hLower)
    let βApprox : ℕ → ℝ := fun k => infC.toReal + 1 / (k + 1 : ℝ)
    have hβApproxMono :
        ∀ {k l : ℕ}, k ≤ l → (βApprox l : EReal) ≤ (βApprox k : EReal) := by
      intro k l hkl
      have hkpos : (0 : ℝ) < k + 1 := by positivity
      have hkle : (k + 1 : ℝ) ≤ l + 1 := by
        exact_mod_cast Nat.succ_le_succ hkl
      have hdiv : 1 / (l + 1 : ℝ) ≤ 1 / (k + 1 : ℝ) := by
        exact one_div_le_one_div_of_le hkpos hkle
      exact_mod_cast (show βApprox l ≤ βApprox k by
        dsimp [βApprox]
        linarith)
    have hβApproxPts :
        ∀ k : ℕ, ∃ x : Fin n → ℝ, x ∈ C ∧ f₀ x ≤ (βApprox k : EReal) := by
      intro k
      refine
        helperForTheorem_6_27_4_exists_point_of_restrictedInf_lt_level
          (h := f₀) (C := C) (βApprox k) ?_
      have hInfCoe : (((infC.toReal : ℝ)) : EReal) = infC := by
        simpa [infC] using EReal.coe_toReal (x := infC) hInfFinite.1 hInfFinite.2
      have hRealLt : infC.toReal < βApprox k := by
        dsimp [βApprox]
        have hpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
        linarith
      have hERealLt : (((infC.toReal : ℝ)) : EReal) < (βApprox k : EReal) := by
        exact_mod_cast hRealLt
      calc
        infC = (((infC.toReal : ℝ)) : EReal) := hInfCoe.symm
        _ < (βApprox k : EReal) := hERealLt
    rcases
        helperForCorollary_6_27_5_mixedLevelFamily_finiteIntersection_packages
          (f₀ := f₀) (fi := fi) hf₀_closed hfi_closed hconsistent βApprox
          hβApproxMono hβApproxPts with
      ⟨hNonempty, hClosed, hConvex, hFiniteIntersection⟩
    obtain ⟨xBar, hxBarAll⟩ :=
      theorem21_5_helly_theorem_under_weaker_recession_hypothesis
        (C := helperForCorollary_6_27_5_mixedLevelFamily f₀ fi βApprox)
        (hCnonempty := hNonempty)
        (hCclosed := hClosed)
        (hCconvex := hConvex)
        (hWeakerRecession :=
          helperForCorollary_6_27_5_mixedLevelFamily_weakRecessionPackage
            (f₀ := f₀) (fi := fi) hf₀_closed hf₀_proper hfi_closed hfi_proper
            hconsistent βApprox hβApproxPts hcontrol)
        (hFiniteIntersectionNonempty := hFiniteIntersection)
    have hxBarC : xBar ∈ C := by
      intro i
      simpa [C, convexInequalityFeasibleSet, helperForCorollary_6_27_5_mixedLevelFamily,
        sublevelSetEReal] using hxBarAll (Sum.inl i)
    have hxBarApprox :
        ∀ k : ℕ, f₀ xBar ≤ (βApprox k : EReal) := by
      intro k
      simpa [helperForCorollary_6_27_5_mixedLevelFamily, sublevelSetEReal] using
        hxBarAll (Sum.inr k)
    have hxBarEq :
        f₀ xBar = infC :=
      helperForTheorem_6_27_4_eq_restrictedInf_of_mem_all_approximateSublevels
        (h := f₀) (C := C) xBar hxBarC hInfFinite hxBarApprox (hnotbot xBar)
    exact ⟨⟨xBar, hxBarC⟩, by simpa [C, infC] using hxBarEq⟩

-- Proof sketch: encode the constraint system by the feasible set
-- `C = {x | ∀ i, fᵢ x ≤ 0}` and apply Theorem 6.27.4 to the constrained minimization of `f₀`
-- over `C`. Any recession direction common to `f₀` and all constraints lies in the recession
-- cone of `C`, so the no-common-recession hypothesis gives attainment. The more general clause
-- is recorded by the finite-subfamily control predicate, which packages the existence of a
-- finite polyhedral subfamily such that any direction common to `f₀` and all constraints
-- forces constancy on `f₀` and on the remaining non-polyhedral constraints, and hence still
-- yields attainment.
/-- Corollary 6.27.5: this is Corollary 27.3.3 in the book's chapter-section numbering. Let `f₀`
and `fᵢ` be closed proper convex functions on `ℝ^n`, where the
index type `ι` may be finite or infinite, and assume that the constraint system
`fᵢ(x) ≤ 0` is consistent. Then the infimum of `f₀` over the feasible set
`{x | ∀ i, fᵢ x ≤ 0}` is attained if `f₀` and all the `fᵢ` have no common recession direction.
More generally, attainment also holds when there exists a finite subset `I₀ ⊆ I` consisting of
polyhedral constraints such that every direction common to `f₀` and all the `fᵢ` is a direction
of constancy of `f₀` and of every `fᵢ` with `i ∉ I₀`; this is encoded by
`FinitePolyhedralSubfamilyControlsCommonRecessionDirections f₀ fi`. -/
theorem attainsInfimumOn_convexInequalitySystem_of_commonRecessionHypotheses
    {n : ℕ} {ι : Type*} (f₀ : (Fin n → ℝ) → EReal)
    (fi : ι → (Fin n → ℝ) → EReal)
    (hf₀_closed : ClosedConvexFunction f₀)
    (hf₀_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₀)
    (hfi_closed : ∀ i : ι, ClosedConvexFunction (fi i))
    (hfi_proper : ∀ i : ι, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fi i))
    (hconsistent : Set.Nonempty (convexInequalityFeasibleSet fi))
    (hcommon :
      HasNoCommonRecessionDirectionsWithConstraintFamily f₀ fi ∨
        FinitePolyhedralSubfamilyControlsCommonRecessionDirections f₀ fi) :
    AttainsInfimumOn f₀ (convexInequalityFeasibleSet fi) := by
  classical
  rcases
      helperForCorollary_6_27_5_feasibleSet_iInter_closedConvex
        (fi := fi) hfi_closed with
    ⟨_hCeq, hCclosed, hCconvex⟩
  have hCrec :
      Set.recessionCone (convexInequalityFeasibleSet fi) =
        ⋂ i : ι, Set.recessionCone (sublevelSetEReal (fi i) 0) :=
    helperForCorollary_6_27_5_feasibleSet_recessionCone_iInter
      (fi := fi) hfi_closed hconsistent
  have hzero_nonempty : ∀ i : ι, (sublevelSetEReal (fi i) 0).Nonempty := by
    rcases hconsistent with ⟨x, hx⟩
    intro i
    refine ⟨x, ?_⟩
    simpa [convexInequalityFeasibleSet, sublevelSetEReal] using hx i
  have hAttainsBase :
      (HasNoCommonRecessionDirections f₀ (convexInequalityFeasibleSet fi) →
        AttainsInfimumOn f₀ (convexInequalityFeasibleSet fi)) ∧
        (IsPolyhedralConvexSet n (convexInequalityFeasibleSet fi) →
          CommonRecessionDirectionsAreDirectionsOfConstancy f₀
            (convexInequalityFeasibleSet fi) →
          AttainsInfimumOn f₀ (convexInequalityFeasibleSet fi)) :=
    attainsInfimumOn_closedConvexSet_of_commonRecessionHypotheses
      (h := f₀) (C := convexInequalityFeasibleSet fi)
      hf₀_closed hf₀_proper hconsistent hCclosed hCconvex
  rcases hcommon with hnoCommon | hcontrol
  · -- The direct branch transports recession information from the feasible set back to each
    -- constraint zero-sublevel and then to each constraint function.
    apply hAttainsBase.1
    intro y hy₀ hyC
    have hyAllSets :
        y ∈ ⋂ i : ι, Set.recessionCone (sublevelSetEReal (fi i) 0) := by
      simpa [hCrec] using hyC
    have hyAllFunctions : ∀ i : ι, IsRecessionDirection (fi i) y := by
      intro i
      have hyi :
          y ∈ Set.recessionCone (sublevelSetEReal (fi i) 0) :=
        Set.mem_iInter.mp hyAllSets i
      exact
        helperForCorollary_6_27_5_zeroSublevel_recession_implies_functionRecession
          (g := fi i) (hg_closed := hfi_closed i) (hg_proper := hfi_proper i)
          (hzero_nonempty := hzero_nonempty i) hyi
    exact hnoCommon y hy₀ hyAllFunctions
  · -- The finite-polyhedral-subfamily branch requires the mixed-family Helly argument.
    exact
      helperForCorollary_6_27_5_finitePolyhedralSubfamily_branch
        (f₀ := f₀) (fi := fi) hf₀_closed hf₀_proper hfi_closed hfi_proper
        hconsistent hcontrol

end Section27
end Chap06
