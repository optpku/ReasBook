/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section11_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part7

section Chap05
section Section23

open scoped ConvexAnalysis Pointwise

/-- Helper for Theorem 23.8: an attained conjugate split at a full Fenchel-Young equality forces
Fenchel-Young equality for each summand. -/
lemma helperForTheorem_23_8_summandFenchelYoung_of_fullEquality_and_attainedSplit
    {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn Set.univ (f i))
    (hsumProper : ProperConvexFunctionOn Set.univ (fun y => ∑ i, f i y))
    (x xStarE : Fin n → ℝ) (parts : Fin m → Fin n → ℝ)
    (hfullFY : FenchelYoungEqualityAt (fun y => ∑ i, f i y) x xStarE)
    (hsum : ∑ i, parts i = xStarE)
    (hatt : fenchelConjugate n (fun y => ∑ i, f i y) xStarE =
      ∑ i, fenchelConjugate n (f i) (parts i)) :
    ∀ i : Fin m, FenchelYoungEqualityAt (f i) x (parts i) := by
  -- Compare the full Fenchel-Young equality with the summed Fenchel inequalities and show that
  -- every nonnegative real gap must vanish.
  have hsumFinite :=
    helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality
      (f := fun y => ∑ i, f i y) hsumProper x xStarE (le_of_eq hfullFY)
  have hconjSum_ne_top :
      fenchelConjugate n (fun y => ∑ i, f i y) xStarE ≠ (⊤ : EReal) :=
    helperForTheorem_23_8_fullConjugate_ne_top_of_fullFenchelYoung
      f hsumProper x xStarE hfullFY
  have hsumConj_ne_top :
      (∑ i, fenchelConjugate n (f i) (parts i)) ≠ (⊤ : EReal) := by
    simpa [hatt] using hconjSum_ne_top
  have hfi_ne_bot : ∀ i : Fin m, f i x ≠ (⊥ : EReal) := by
    intro i
    exact (hproper i).2.2 x (by simp)
  have hconj_ne_bot :
      ∀ i : Fin m, fenchelConjugate n (f i) (parts i) ≠ (⊥ : EReal) := by
    intro i
    obtain ⟨z0, r0, hz0⟩ :=
      properConvexFunctionOn_exists_finite_point (n := n) (f := f i) (hproper i)
    have hExists : ∃ z : Fin n → ℝ, f i z ≠ (⊤ : EReal) := by
      refine ⟨z0, ?_⟩
      rw [hz0]
      simp
    exact fenchelConjugate_ne_bot_of_exists_ne_top (n := n) (f := f i) hExists (parts i)
  have hconj_ne_top :
      ∀ i : Fin m, fenchelConjugate n (f i) (parts i) ≠ (⊤ : EReal) := by
    intro i
    intro htop
    exact hsumConj_ne_top
      (sum_eq_top_of_term_top
        (s := (Finset.univ : Finset (Fin m)))
        (f := fun j : Fin m => fenchelConjugate n (f j) (parts j))
        (i := i) (by simp) htop
        (by
          intro j hj
          exact hconj_ne_bot j))
  have hfi_ne_top : ∀ i : Fin m, f i x ≠ (⊤ : EReal) := by
    have hsumx_ne_top : (∑ i, f i x) ≠ (⊤ : EReal) := hsumFinite.1
    intro i
    intro htop
    exact hsumx_ne_top
      (sum_eq_top_of_term_top
        (s := (Finset.univ : Finset (Fin m)))
        (f := fun j : Fin m => f j x)
        (i := i) (by simp) htop
        (by
          intro j hj
          exact hfi_ne_bot j))
  have hgap_nonneg :
      ∀ i : Fin m,
        0 ≤
          (f i x).toReal + (fenchelConjugate n (f i) (parts i)).toReal -
            dotProduct x (parts i) := by
    intro i
    have hfenchel := fenchel_inequality n (f i) (hproper i) x (parts i)
    have hreal_le :
        dotProduct x (parts i) ≤
          (f i x + fenchelConjugate n (f i) (parts i)).toReal := by
      simpa using
        EReal.toReal_le_toReal hfenchel (EReal.coe_ne_bot _)
          (EReal.add_ne_top (hfi_ne_top i) (hconj_ne_top i))
    have hadd_toReal :
        (f i x + fenchelConjugate n (f i) (parts i)).toReal =
          (f i x).toReal + (fenchelConjugate n (f i) (parts i)).toReal :=
      EReal.toReal_add (hfi_ne_top i) (hfi_ne_bot i) (hconj_ne_top i) (hconj_ne_bot i)
    linarith [hreal_le]
  have hsum_fx_real :
      (∑ i, f i x) = ((((∑ i, (f i x).toReal) : ℝ)) : EReal) := by
    calc
      (∑ i, f i x) = ∑ i, (((f i x).toReal : ℝ) : EReal) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
          (hTop := hfi_ne_top i) (hBot := hfi_ne_bot i)
      _ = ((((∑ i, (f i x).toReal) : ℝ)) : EReal) := by
        symm
        exact section16_coe_finset_sum (s := Finset.univ) (b := fun i : Fin m => (f i x).toReal)
  have hsum_conj_real :
      (∑ i, fenchelConjugate n (f i) (parts i)) =
        ((((∑ i, (fenchelConjugate n (f i) (parts i)).toReal) : ℝ)) : EReal) := by
    calc
      (∑ i, fenchelConjugate n (f i) (parts i)) =
          ∑ i, ((((fenchelConjugate n (f i) (parts i)).toReal : ℝ)) : EReal) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
          (hTop := hconj_ne_top i) (hBot := hconj_ne_bot i)
      _ = ((((∑ i, (fenchelConjugate n (f i) (parts i)).toReal) : ℝ)) : EReal) := by
        symm
        exact section16_coe_finset_sum (s := Finset.univ)
          (b := fun i : Fin m => (fenchelConjugate n (f i) (parts i)).toReal)
  have hsum_eq_dot :
      (∑ i, (f i x).toReal) + (∑ i, (fenchelConjugate n (f i) (parts i)).toReal) =
        ∑ i, dotProduct x (parts i) := by
    have hsumEqEReal :
        ((((∑ i, (f i x).toReal) + ∑ i, (fenchelConjugate n (f i) (parts i)).toReal : ℝ))
            : EReal) =
          ((((∑ i, dotProduct x (parts i) : ℝ)) : ℝ) : EReal) := by
      calc
        ((((∑ i, (f i x).toReal) + ∑ i, (fenchelConjugate n (f i) (parts i)).toReal : ℝ))
            : EReal) =
            (∑ i, f i x) + (∑ i, fenchelConjugate n (f i) (parts i)) := by
              rw [hsum_fx_real, hsum_conj_real]
              simp [EReal.coe_add]
        _ = (fun y => ∑ i, f i y) x + fenchelConjugate n (fun y => ∑ i, f i y) xStarE := by
              simp [hatt]
        _ = ((dotProduct x xStarE : ℝ) : EReal) := by
              simpa [FenchelYoungEqualityAt] using hfullFY
        _ = ((((∑ i, dotProduct x (parts i) : ℝ)) : ℝ) : EReal) := by
              have hdot :
                  dotProduct x xStarE = ∑ i, dotProduct x (parts i) := by
                calc
                  dotProduct x xStarE = dotProduct x (∑ i, parts i) := by
                    simpa [hsum]
                  _ = ∑ i, dotProduct x (parts i) := by
                        simpa using
                          (dotProduct_sum (u := x) (s := (Finset.univ : Finset (Fin m)))
                            (v := fun i : Fin m => parts i))
              simp [hdot]
    exact_mod_cast hsumEqEReal
  have hgap_sum_zero :
      ∑ i, ((f i x).toReal + (fenchelConjugate n (f i) (parts i)).toReal -
        dotProduct x (parts i)) = 0 := by
    calc
      ∑ i,
          ((f i x).toReal + (fenchelConjugate n (f i) (parts i)).toReal -
            dotProduct x (parts i)) =
          (∑ i, (f i x).toReal) + (∑ i, (fenchelConjugate n (f i) (parts i)).toReal) -
            ∑ i, dotProduct x (parts i) := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = 0 := by
            linarith [hsum_eq_dot]
  have hgap_zero :
      ∀ i ∈ (Finset.univ : Finset (Fin m)),
        (f i x).toReal + (fenchelConjugate n (f i) (parts i)).toReal -
          dotProduct x (parts i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ)
      (f := fun i : Fin m =>
        (f i x).toReal + (fenchelConjugate n (f i) (parts i)).toReal -
          dotProduct x (parts i))
      (by intro i hi; exact hgap_nonneg i)).1 hgap_sum_zero
  intro i
  have hrealEq :
      (f i x).toReal + (fenchelConjugate n (f i) (parts i)).toReal =
        dotProduct x (parts i) := by
    linarith [hgap_zero i (by simp)]
  have hEqEReal :
      f i x + fenchelConjugate n (f i) (parts i) =
        ((dotProduct x (parts i) : ℝ) : EReal) := by
    calc
      f i x + fenchelConjugate n (f i) (parts i) =
          ((((f i x).toReal + (fenchelConjugate n (f i) (parts i)).toReal : ℝ)) : EReal) := by
            rw [helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
                  (hTop := hfi_ne_top i) (hBot := hfi_ne_bot i)]
            rw [helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
                  (hTop := hconj_ne_top i) (hBot := hconj_ne_bot i)]
            simp [EReal.coe_add]
      _ = ((dotProduct x (parts i) : ℝ) : EReal) := by
            exact_mod_cast hrealEq
  simpa [FenchelYoungEqualityAt] using hEqEReal

/-- Helper for Theorem 23.8: under the qualification hypothesis, a subgradient of the full sum
should decompose into summand subgradients. The remaining work is the Chapter 4 exact-conjugate
argument that splits a Fenchel-Young equality into summand equalities. -/
lemma helperForTheorem_23_8_reverse_decomposition_under_qualification {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn Set.univ (f i)) (Ipoly : Set (Fin m))
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hqual : SubdifferentialSumQualification f Ipoly) :
    ∀ (x : Fin n → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)),
      xStar ∈ subdifferentialAt (fun y => ∑ i, f i y) x →
        IsSubdifferentialSumDecompositionAt f x xStar := by
  intro x xStar hxStar
  -- First record the properness of the full sum and the corresponding full Fenchel-Young
  -- equality at `(x, x⋆)`. These two reductions are now stable and can be reused by the remaining
  -- attained-split argument.
  have hsumProper :
      ProperConvexFunctionOn Set.univ (fun y => ∑ i, f i y) :=
    helperForTheorem_23_8_sum_proper_of_qualification f hproper Ipoly hqual
  have hfullFY :
      FenchelYoungEqualityAt (fun y => ∑ i, f i y) x ((dotProductEquiv ℝ (Fin n)).symm xStar) :=
    helperForTheorem_23_8_fullFenchelYoung_of_sumSubgradient f hsumProper x xStar hxStar
  let xStarE : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xStar
  -- TODO: produce `parts : Fin m → Fin n → ℝ` with
  -- `∑ i, parts i = xStarE` and
  -- `fenchelConjugate n (fun y => ∑ i, f i y) xStarE =
  --    ∑ i, fenchelConjugate n (f i) (parts i)`
  -- from the Chapter 4 attained-split theorem under `hqual`; then combine that witness with
  -- `hfullFY` and `helperForTheorem_23_8_dualDecomposition_of_summandFenchelYoung`.
  have _hxStarE : xStarE = (dotProductEquiv ℝ (Fin n)).symm xStar := rfl
  have _hfullFY_use :
      FenchelYoungEqualityAt (fun y => ∑ i, f i y) x xStarE := by
    simpa [xStarE] using hfullFY
  by_cases hm0 : m = 0
  · -- The empty-family case has only the zero decomposition, which is already forced by the
    -- empty subgradient relation on the summed zero function.
    subst hm0
    have hxStar_zero : xStar = 0 := by
      ext v
      let e : Fin n → ℝ := Pi.single v 1
      have hle :
          ((xStar e : ℝ) : EReal) ≤ 0 := by
        simpa [e] using hxStar (x + e)
      have hneg :
          ((xStar (-e) : ℝ) : EReal) ≤ 0 := by
        simpa [e, sub_eq_add_neg, add_assoc] using hxStar (x - e)
      have hneg' : (((-xStar e : ℝ)) : EReal) ≤ 0 := by
        simpa [LinearMap.map_neg] using hneg
      have hreal_le : xStar e ≤ 0 := by
        exact_mod_cast hle
      have hreal_ge : 0 ≤ xStar e := by
        have : -xStar e ≤ 0 := by exact_mod_cast hneg'
        linarith
      simpa [e] using le_antisymm hreal_le hreal_ge
    refine ⟨fun i => False.elim (Fin.elim0 i), ?_, ?_⟩
    · simp
    · simpa [hxStar_zero]
  · have hmPos : 0 < m := Nat.pos_of_ne_zero hm0
    classical
    -- Route correction: instead of forcing a direct arbitrary-`Ipoly` attainment theorem, first
    -- build an attained conjugate split from the qualification branch and then transport the full
    -- Fenchel-Young equality to each summand.
    have hattained :
        ∃ parts : Fin m → Fin n → ℝ,
          (∑ i, parts i) = xStarE ∧
            fenchelConjugate n (fun y => ∑ i, f i y) xStarE =
              ∑ i, fenchelConjugate n (f i) (parts i) := by
      rcases hqual with hallri | hmixed
      · exact
          helperForTheorem_23_8_attainedFenchelSplit_of_allRiQualification
            f hmPos hproper hsumProper x xStarE hallri _hfullFY_use
      · exact
          helperForTheorem_23_8_attainedFenchelSplit_of_mixedQualification_via_filteredBinaryBridge
            f hmPos hproper hsumProper Ipoly hpoly hmixed x xStarE _hfullFY_use
    rcases hattained with ⟨parts, hsumParts, hattParts⟩
    have hfyParts :
        ∀ i : Fin m, FenchelYoungEqualityAt (f i) x (parts i) :=
      helperForTheorem_23_8_summandFenchelYoung_of_fullEquality_and_attainedSplit
        f hproper hsumProper x xStarE parts _hfullFY_use hsumParts hattParts
    simpa [xStarE] using
      helperForTheorem_23_8_dualDecomposition_of_summandFenchelYoung
        f hproper x xStarE parts hsumParts hfyParts

/-- Theorem 23.8: Let `f₁, …, fₘ` be proper convex functions on `ℝⁿ`, and let
`f = f₁ + ··· + fₘ`. Then every finite sum of subgradients `x₁⋆ + ··· + xₘ⋆` with
`xᵢ⋆ ∈ ∂ fᵢ(x)` belongs to `∂ f(x)`. If the relative interiors `ri (dom fᵢ)` have a common
point, then every `x⋆ ∈ ∂ f(x)` decomposes in this way. More generally, if a distinguished
subfamily consists of polyhedral convex functions, the same equality holds under the weaker
qualification that requires a common point of `dom fᵢ` for the polyhedral indices and
`ri (dom fᵢ)` for the remaining indices. -/
theorem subdifferential_sum_contains_sum_and_eq_under_qualification {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn Set.univ (f i)) (Ipoly : Set (Fin m))
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i)) :
    (∀ (x : Fin n → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)),
      IsSubdifferentialSumDecompositionAt f x xStar →
        xStar ∈ subdifferentialAt (fun y => ∑ i, f i y) x) ∧
    (SubdifferentialSumQualification f Ipoly →
      ∀ (x : Fin n → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)),
        xStar ∈ subdifferentialAt (fun y => ∑ i, f i y) x ↔
          IsSubdifferentialSumDecompositionAt f x xStar) := by
  constructor
  · -- The forward inclusion is the elementary sum of the defining subgradient inequalities.
    intro x xStar hxdecomp
    exact helperForTheorem_23_8_subgradient_of_sum_of_decomposition f x xStar hxdecomp
  · intro hqual x xStar
    constructor
    · -- Route correction: the reverse inclusion is not another pointwise inequality argument.
      -- It must pass through Fenchel-Young equality plus the qualified exact conjugate-sum split.
      intro hxStar
      exact
        helperForTheorem_23_8_reverse_decomposition_under_qualification
          f hproper Ipoly hpoly hqual x xStar hxStar
    · -- The converse direction in the qualified equality is again the elementary inclusion.
      intro hxdecomp
      exact helperForTheorem_23_8_subgradient_of_sum_of_decomposition f x xStar hxdecomp

/-- Theorem 23.8(2), common-relative-interior form:
if the relative interiors `ri (dom fᵢ)` have a common point, then the subdifferential of the sum
is exactly the Minkowski sum of the summand subdifferentials. -/
lemma subdifferential_sum_eq_sum_of_commonRelativeInteriorEffectiveDomain {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn Set.univ (f i))
    (hri :
      ∃ z : Fin n → ℝ,
        ∀ i : Fin m, z ∈ euclideanRelativeInterior_fin n (effectiveDomain Set.univ (f i)))
    (x : Fin n → ℝ) :
    ∂ (fun y => ∑ i, f i y) (x) =
      ∑ i, (∂ (f i) (x) : Set (Module.Dual ℝ (Fin n → ℝ))) := by
  let Ipoly : Set (Fin m) := {i | IsPolyhedralConvexFunction n (f i)}
  have hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i) := by
    intro i
    simp [Ipoly]
  have hqual : SubdifferentialSumQualification f Ipoly := Or.inl hri
  ext xStar
  constructor
  · intro hxStar
    have hdecomp : IsSubdifferentialSumDecompositionAt f x xStar :=
      ((subdifferential_sum_contains_sum_and_eq_under_qualification f hproper Ipoly hpoly).2
        hqual x xStar).1 hxStar
    rcases hdecomp with ⟨parts, hparts, hsum⟩
    refine (Set.mem_fintype_sum
      (f := fun i : Fin m => (∂ (f i) (x) : Set (Module.Dual ℝ (Fin n → ℝ))))
      (a := xStar)).2 ?_
    exact ⟨parts, hparts, by simpa [hsum]⟩
  · intro hxStar
    rcases
        (Set.mem_fintype_sum
          (f := fun i : Fin m => (∂ (f i) (x) : Set (Module.Dual ℝ (Fin n → ℝ))))
          (a := xStar)).1 hxStar with
      ⟨parts, hparts, hsum⟩
    have hmem : (∑ i, parts i) ∈ ∂ (fun y => ∑ i, f i y) (x) :=
      subgradient_sum_mem_subdifferential_sum f x parts hparts
    simpa [hsum] using hmem

/-- Theorem 23.8(2), mathlib `intrinsicInterior` form:
if the intrinsic interiors of the effective domains have a common point, then the subdifferential
of the sum is exactly the Minkowski sum of the summand subdifferentials. -/
lemma subdifferential_sum_eq_sum_of_commonIntrinsicInteriorEffectiveDomain {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) (hproper : ∀ i, ProperConvexFunctionOn Set.univ (f i))
    (hii : ∃ z, ∀ i, z ∈ intrinsicInterior ℝ (effectiveDomain Set.univ (f i)))
    (x : Fin n → ℝ) : ∂ (∑ i, f i ·) (x) = ∑ i, ∂ (f i) (x) := by
  rcases hii with ⟨z, hz⟩
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hri :
      ∃ z : Fin n → ℝ,
        ∀ i : Fin m, z ∈ euclideanRelativeInterior_fin n (effectiveDomain Set.univ (f i)) := by
    refine ⟨z, ?_⟩
    intro i
    have hz' :
        z ∈ e '' intrinsicInterior Real (e.symm '' effectiveDomain Set.univ (f i)) := by
      have himage :
          e '' intrinsicInterior Real (e.symm '' effectiveDomain Set.univ (f i)) =
            intrinsicInterior Real (effectiveDomain Set.univ (f i)) := by
        simpa [e] using
          (ContinuousLinearEquiv.image_intrinsicInterior (e := e)
            (s := e.symm '' effectiveDomain Set.univ (f i))).symm
      rw [himage]
      exact hz i
    have hz'' :
        z ∈ e '' euclideanRelativeInterior n (e.symm '' effectiveDomain Set.univ (f i)) := by
      rw [← intrinsicInterior_eq_euclideanRelativeInterior (n := n)
        (C := e.symm '' effectiveDomain Set.univ (f i))]
      exact hz'
    simpa [euclideanRelativeInterior_fin, e] using hz''
  exact
    subdifferential_sum_eq_sum_of_commonRelativeInteriorEffectiveDomain
      f hproper hri x

/-- Helper for Corollary 23.8.1: the set-qualification hypothesis yields a single point lying in
every set of the family. -/
lemma helperForCorollary_23_8_1_commonPoint_of_setQualification
    {m n : ℕ} (C : Fin m → Set (Fin n → ℝ)) (Ipoly : Set (Fin m)) :
    ((∃ z : Fin n → ℝ, ∀ i : Fin m, z ∈ euclideanRelativeInterior_fin n (C i)) ∨
      ∃ z : Fin n → ℝ, (∀ i ∈ Ipoly, z ∈ C i) ∧
        ∀ i ∉ Ipoly, z ∈ euclideanRelativeInterior_fin n (C i)) →
      ∃ z : Fin n → ℝ, ∀ i : Fin m, z ∈ C i := by
  intro hqual
  rcases hqual with hallri | hmixed
  · -- Turn each relative-interior membership into ordinary set membership.
    rcases hallri with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    intro i
    exact helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin (hz i)
  · -- In the mixed case, only the nonpolyhedral indices need the relative-interior reduction.
    rcases hmixed with ⟨z, hzpoly, hzri⟩
    refine ⟨z, ?_⟩
    intro i
    by_cases hi : i ∈ Ipoly
    · exact hzpoly i hi
    · exact helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin (hzri i hi)

/-- Helper for Corollary 23.8.1: after rewriting indicator effective domains back to the
underlying sets, the corollary hypothesis is exactly the qualification needed in Theorem 23.8. -/
lemma helperForCorollary_23_8_1_indicatorQualification
    {m n : ℕ} (C : Fin m → Set (Fin n → ℝ)) (Ipoly : Set (Fin m))
    (hqual :
      (∃ z : Fin n → ℝ, ∀ i : Fin m, z ∈ euclideanRelativeInterior_fin n (C i)) ∨
        ∃ z : Fin n → ℝ, (∀ i ∈ Ipoly, z ∈ C i) ∧
          ∀ i ∉ Ipoly, z ∈ euclideanRelativeInterior_fin n (C i)) :
    SubdifferentialSumQualification (fun i => indicatorFunction (C i)) Ipoly := by
  -- The indicator of `C i` has effective domain exactly `C i`.
  simpa [SubdifferentialSumQualification, effectiveDomain_indicatorFunction_eq] using hqual

/-- Helper for Corollary 23.8.1: a common point makes every indicator in the family proper convex,
so the sum rule from Theorem 23.8 is applicable. -/
lemma helperForCorollary_23_8_1_indicatorFamilyProper
    {m n : ℕ} (C : Fin m → Set (Fin n → ℝ)) (hconv : ∀ i : Fin m, Convex ℝ (C i))
    {z : Fin n → ℝ} (hz : ∀ i : Fin m, z ∈ C i) :
    ∀ i : Fin m, ProperConvexFunctionOn Set.univ (indicatorFunction (C i)) := by
  intro i
  -- The common point witnesses nonemptiness of each set.
  have hCne : (C i).Nonempty := ⟨z, hz i⟩
  exact properConvexFunctionOn_indicator_of_convex_of_nonempty (hconv i) hCne

/-- Helper for Corollary 23.8.1: for a nonempty set, the subdifferential of its indicator is
exactly the normal cone at every point. -/
lemma helperForCorollary_23_8_1_subdifferential_indicator_eq_normalCone_of_nonempty
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCne : C.Nonempty) :
    ∀ x : Fin n → ℝ, subdifferentialAt (indicatorFunction C) x = normalConeAt C x := by
  intro x
  ext xStar
  by_cases hx : x ∈ C
  · constructor
    · intro hxStar
      -- Inside the set, the subgradient inequality against indicator values is exactly the
      -- supporting inequality that defines the normal cone.
      refine (mem_normalConeAt_iff).2 ⟨hx, ?_⟩
      intro z hz
      have hineq :
          indicatorFunction C z ≥
            indicatorFunction C x + (((xStar (z - x) : ℝ) : EReal)) :=
        hxStar z
      have hineq' : (((xStar (z - x) : ℝ) : EReal)) ≤ (0 : EReal) := by
        simpa [indicatorFunction, hx, hz] using hineq
      exact_mod_cast hineq'
    · intro hxStar
      -- Conversely, normal-cone membership supplies the only nontrivial branch of the
      -- subgradient inequality; outside the set the indicator is already `⊤`.
      intro z
      by_cases hz : z ∈ C
      · have hzle : xStar (z - x) ≤ 0 := (mem_normalConeAt_iff.1 hxStar).2 z hz
        have hzle' : (((xStar (z - x) : ℝ) : EReal)) ≤ (0 : EReal) := by
          exact_mod_cast hzle
        calc
          indicatorFunction C z = (0 : EReal) := by simp [indicatorFunction, hz]
          _ ≥ (((xStar (z - x) : ℝ) : EReal)) := hzle'
          _ = indicatorFunction C x + (((xStar (z - x) : ℝ) : EReal)) := by
            simp [indicatorFunction, hx]
      · simp [indicatorFunction, hz]
  · constructor
    · intro hxStar
      -- Outside the set, a nonempty indicator cannot admit any subgradient because the
      -- inequality at an interior witness would force `⊤ ≤ 0`.
      rcases hCne with ⟨z0, hz0⟩
      have hineq :
          indicatorFunction C z0 ≥
            indicatorFunction C x + (((xStar (z0 - x) : ℝ) : EReal)) :=
        hxStar z0
      have hbad' : (⊤ : EReal) + (((xStar (z0 - x) : ℝ) : EReal)) ≤ (0 : EReal) := by
        simpa [indicatorFunction, hx, hz0] using hineq
      have hbad : (⊤ : EReal) ≤ (0 : EReal) := by
        calc
          (⊤ : EReal) = (⊤ : EReal) + (((xStar (z0 - x) : ℝ) : EReal)) := by
            symm
            exact EReal.top_add_coe (xStar (z0 - x))
          _ ≤ (0 : EReal) := hbad'
      have : ¬ ((⊤ : EReal) ≤ (0 : EReal)) := by
        simp
      exact False.elim (this hbad)
    · intro hxStar
      -- The normal cone is also empty outside the set because membership already demands `x ∈ C`.
      have hxmem : x ∈ C := (mem_normalConeAt_iff.1 hxStar).1
      exact (hx hxmem).elim

/-- Corollary 23.8.1: Let `C₁, …, Cₘ` be convex sets in `ℝⁿ`. If their relative interiors have a
common point, then the normal cone of `C₁ ∩ ··· ∩ Cₘ` at `x` consists exactly of sums
`x₁⋆ + ··· + xₘ⋆` with `xᵢ⋆ ∈ N_{Cᵢ}(x)`. If a distinguished subfamily is polyhedral, the same
equality holds under the weaker qualification that uses `Cᵢ` itself for the polyhedral indices and
`ri Cᵢ` for the remaining ones. -/
theorem normalCone_intersection_eq_sum_under_qualification {m n : ℕ}
    (C : Fin m → Set (Fin n → ℝ)) (hconv : ∀ i : Fin m, Convex ℝ (C i)) (Ipoly : Set (Fin m))
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (indicatorFunction (C i))) :
    ((∃ z : Fin n → ℝ, ∀ i : Fin m, z ∈ euclideanRelativeInterior_fin n (C i)) ∨
      ∃ z : Fin n → ℝ, (∀ i ∈ Ipoly, z ∈ C i) ∧
        ∀ i ∉ Ipoly, z ∈ euclideanRelativeInterior_fin n (C i)) →
    ∀ x : Fin n → ℝ,
      normalConeAt (⋂ i, C i) x =
        {xStar | ∃ parts : Fin m → Module.Dual ℝ (Fin n → ℝ),
          (∀ i : Fin m, parts i ∈ normalConeAt (C i) x) ∧ xStar = ∑ i, parts i} := by
  intro hqual x
  -- First extract a common point so every indicator is proper and the intersection is nonempty.
  rcases helperForCorollary_23_8_1_commonPoint_of_setQualification C Ipoly hqual with ⟨z, hz⟩
  have hproper :
      ∀ i : Fin m, ProperConvexFunctionOn Set.univ (indicatorFunction (C i)) :=
    helperForCorollary_23_8_1_indicatorFamilyProper C hconv hz
  have hqualIndicator :
      SubdifferentialSumQualification (fun i => indicatorFunction (C i)) Ipoly :=
    helperForCorollary_23_8_1_indicatorQualification C Ipoly hqual
  have hInterNonempty : (⋂ i, C i).Nonempty := by
    refine ⟨z, ?_⟩
    simpa [Set.mem_iInter] using hz
  have hsumRule :=
    subdifferential_sum_contains_sum_and_eq_under_qualification
      (f := fun i => indicatorFunction (C i)) hproper Ipoly hpoly
  ext xStar
  constructor
  · intro hxStar
    -- Rewrite the normal-cone condition as a subgradient statement for the indicator of the
    -- intersection, then apply the qualified sum rule.
    have hxInterSub : xStar ∈ subdifferentialAt (indicatorFunction (⋂ i, C i)) x := by
      simpa
        [helperForCorollary_23_8_1_subdifferential_indicator_eq_normalCone_of_nonempty
          hInterNonempty x] using hxStar
    have hxSumSub : xStar ∈ subdifferentialAt (fun y => ∑ i, indicatorFunction (C i) y) x := by
      simpa [section16_sum_indicatorFunction_eq_indicatorFunction_iInter (C := C)] using hxInterSub
    have hxDecomp :
        IsSubdifferentialSumDecompositionAt (fun i => indicatorFunction (C i)) x xStar :=
      ((hsumRule.2 hqualIndicator x xStar).1 hxSumSub)
    rcases hxDecomp with ⟨parts, hparts, hsum⟩
    refine ⟨parts, ?_, hsum⟩
    -- Translate each indicator-function subgradient back into a normal-cone membership.
    intro i
    simpa
      [helperForCorollary_23_8_1_subdifferential_indicator_eq_normalCone_of_nonempty
        ⟨z, hz i⟩ x] using hparts i
  · rintro ⟨parts, hparts, hsum⟩
    -- Start from a normal-cone decomposition, rewrite it as a decomposition by indicator
    -- subgradients, and push it through the forward implication of Theorem 23.8.
    have hxDecomp :
        IsSubdifferentialSumDecompositionAt (fun i => indicatorFunction (C i)) x xStar := by
      refine ⟨parts, ?_, hsum⟩
      intro i
      simpa
        [helperForCorollary_23_8_1_subdifferential_indicator_eq_normalCone_of_nonempty
          ⟨z, hz i⟩ x] using hparts i
    have hxSumSub : xStar ∈ subdifferentialAt (fun y => ∑ i, indicatorFunction (C i) y) x :=
      hsumRule.1 x xStar hxDecomp
    have hxInterSub : xStar ∈ subdifferentialAt (indicatorFunction (⋂ i, C i)) x := by
      simpa [section16_sum_indicatorFunction_eq_indicatorFunction_iInter (C := C)] using hxSumSub
    simpa
      [helperForCorollary_23_8_1_subdifferential_indicator_eq_normalCone_of_nonempty
        hInterNonempty x] using hxInterSub

-- Helper declarations for Theorem 23.9.
/-- Helper for Theorem 23.9: lift a linear map on coordinate spaces to the Euclidean-space
presentation used by the Chapter 3 adjoint-image theorems. -/
noncomputable def helperForTheorem_23_9_euclideanLinearLift {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  ((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin m → ℝ)).symm.toLinearMap).comp
    (A.comp (WithLp.linearEquiv (2 : ENNReal) ℝ (Fin n → ℝ)).toLinearMap)

/-- Helper for Theorem 23.9: an adjoint-fiber equality in Euclidean coordinates becomes the
expected `A.dualMap` equality on subgradients. -/
lemma helperForTheorem_23_9_dualMap_eq_of_adjoint_eq {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (xStarE : Fin n → ℝ) (yStarE : Fin m → ℝ)
    (hAadj :
      (LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A)) (WithLp.toLp 2 yStarE) =
        WithLp.toLp 2 xStarE) :
    A.dualMap (dotProductEquiv ℝ (Fin m) yStarE) = dotProductEquiv ℝ (Fin n) xStarE := by
  -- Compare the two dual vectors coordinate-by-coordinate by evaluating them on the basis vector
  -- `e_u`.
  ext u
  have hdot :=
    section16_dotProduct_map_eq_dotProduct_adjoint
      (A := helperForTheorem_23_9_euclideanLinearLift A) (x := Pi.single u 1) (yStar := yStarE)
  have hdot' :
      yStarE ⬝ᵥ A (Pi.single u 1) =
        (((LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A))
            (WithLp.toLp 2 yStarE)) : Fin n → ℝ) u := by
    simpa [helperForTheorem_23_9_euclideanLinearLift, dotProduct_comm] using hdot
  have hcoord :
      (((LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A))
          (WithLp.toLp 2 yStarE)) : Fin n → ℝ) u = xStarE u := by
    have hAadj' :
        (((LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A))
            (WithLp.toLp 2 yStarE)) : Fin n → ℝ) = xStarE := by
      simpa [WithLp.ofLp_toLp] using
        congrArg (fun v : EuclideanSpace ℝ (Fin n) => (v : Fin n → ℝ)) hAadj
    exact congrArg (fun f : Fin n → ℝ => f u) hAadj'
  simpa [LinearMap.dualMap_apply, dotProductEquiv_apply_apply] using hdot'.trans hcoord

/-- Helper for Theorem 23.9: a finite point of `h` lying in the range of `A` makes the
precomposition `h ∘ A` proper convex. -/
lemma helperForTheorem_23_9_precomp_proper_of_range_meets_effectiveDomain {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (h : (Fin m → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ h)
    (hw : ∃ z : Fin m → ℝ, z ∈ Set.range A ∧ z ∈ effectiveDomain Set.univ h) :
    ProperConvexFunctionOn Set.univ (fun y => h (A y)) := by
  refine ⟨convexFunctionOn_precomp_linearMap (A := A) (g := h) hproper.1, ?_, ?_⟩
  · -- Pull the finite value of `h` back along the range witness to produce a finite epigraph
    -- point for `h ∘ A`.
    rcases hw with ⟨z, ⟨x, rfl⟩, hz⟩
    refine ⟨(x, (h (A x)).toReal), ?_⟩
    refine (mem_epigraph_univ_iff (f := fun y => h (A y))).2 ?_
    have htop : h (A x) ≠ ⊤ := mem_effectiveDomain_imp_ne_top (S := Set.univ) (f := h) hz
    have hbot : h (A x) ≠ ⊥ := hproper.2.2 (A x) (by simp)
    exact le_of_eq
      (helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot (hTop := htop) (hBot := hbot))
  · -- Properness of `h` still rules out `⊥` after precomposition.
    intro y hy
    exact hproper.2.2 (A y) (by simp)

/-- Helper for Theorem 23.9: every subgradient of `h` at `A x` pushes forward to a subgradient of
`h ∘ A` at `x`. -/
lemma helperForTheorem_23_9_dualMapImage_mem_subdifferential_precomp {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (h : (Fin m → ℝ) → EReal)
    (x : Fin n → ℝ)
    (yStar : Module.Dual ℝ (Fin m → ℝ))
    (hyStar : yStar ∈ subdifferentialAt h (A x)) :
    A.dualMap yStar ∈ subdifferentialAt (fun y => h (A y)) x := by
  -- Evaluate the subgradient inequality for `h` at the point `A z`, then rewrite the linear term
  -- through `A.dualMap`.
  intro z
  have hy := hyStar (A z)
  simpa [LinearMap.dualMap_apply, LinearMap.map_sub] using hy

/-- Helper for Theorem 23.9: once a codomain dual vector lies over `xStar` and attains the same
Fenchel-conjugate value, it is a genuine subgradient of `h` at `A x`. -/
lemma helperForTheorem_23_9_subgradient_of_h_of_attained_dualFiber {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (h : (Fin m → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ h)
    (hAproper : ProperConvexFunctionOn Set.univ (fun y => h (A y)))
    (x : Fin n → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ))
    (yStar : Module.Dual ℝ (Fin m → ℝ))
    (hxStar : xStar ∈ subdifferentialAt (fun y => h (A y)) x)
    (hdual : A.dualMap yStar = xStar)
    (hconj : fenchelConjugate m h ((dotProductEquiv ℝ (Fin m)).symm yStar) =
      fenchelConjugate n (fun y => h (A y)) ((dotProductEquiv ℝ (Fin n)).symm xStar)) :
    yStar ∈ subdifferentialAt h (A x) := by
  -- Route correction: rather than forcing a raw inequality proof on the fiber witness, translate
  -- both subgradient conditions through the Fenchel-Young equivalence from Theorem 23.5.
  have hxStarE :
      IsEuclideanSubgradientAt (fun y => h (A y)) x ((dotProductEquiv ℝ (Fin n)).symm xStar) := by
    change dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm xStar) ∈
      subdifferentialAt (fun y => h (A y)) x
    simpa using hxStar
  have hfy_precomp :
      FenchelYoungEqualityAt (fun y => h (A y)) x ((dotProductEquiv ℝ (Fin n)).symm xStar) := by
    exact
      ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        (fun y => h (A y)) hAproper x ((dotProductEquiv ℝ (Fin n)).symm xStar)).1.out 0 3).1
        hxStarE
  have hdot :
      dotProduct (A x) ((dotProductEquiv ℝ (Fin m)).symm yStar) =
        dotProduct x ((dotProductEquiv ℝ (Fin n)).symm xStar) := by
    have hdual_apply : yStar (A x) = xStar x := congrArg (fun f => f x) hdual
    have hyEval :
        yStar (A x) = dotProduct ((dotProductEquiv ℝ (Fin m)).symm yStar) (A x) := by
      simpa using
        (dotProductEquiv_apply_apply ℝ (Fin m) ((dotProductEquiv ℝ (Fin m)).symm yStar) (A x))
    have hxEval :
        xStar x = dotProduct ((dotProductEquiv ℝ (Fin n)).symm xStar) x := by
      simpa using
        (dotProductEquiv_apply_apply ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm xStar) x)
    calc
      dotProduct (A x) ((dotProductEquiv ℝ (Fin m)).symm yStar)
          = yStar (A x) := by simpa [dotProduct_comm] using hyEval.symm
      _ = xStar x := hdual_apply
      _ = dotProduct ((dotProductEquiv ℝ (Fin n)).symm xStar) x := hxEval
      _ = dotProduct x ((dotProductEquiv ℝ (Fin n)).symm xStar) := by simp [dotProduct_comm]
  have hfy_h : FenchelYoungEqualityAt h (A x) ((dotProductEquiv ℝ (Fin m)).symm yStar) := by
    rw [FenchelYoungEqualityAt] at hfy_precomp ⊢
    simpa [hconj, hdot] using hfy_precomp
  have hyStarE :
      IsEuclideanSubgradientAt h (A x) ((dotProductEquiv ℝ (Fin m)).symm yStar) :=
    ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
      h hproper (A x) ((dotProductEquiv ℝ (Fin m)).symm yStar)).1.out 3 0).1 hfy_h
  simpa [IsEuclideanSubgradientAt] using hyStarE

/-- Helper for Theorem 23.9: under the relative-interior qualification, every subgradient of
`h ∘ A` comes from a subgradient of `h` lying over the same dual fiber. -/
lemma helperForTheorem_23_9_mem_image_subdifferential_of_relativeInteriorQualification {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (h : (Fin m → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ h)
    (hri : RangeMeetsRelativeInteriorEffectiveDomain A h)
    (x : Fin n → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ))
    (hxStar : xStar ∈ subdifferentialAt (fun y => h (A y)) x) :
    xStar ∈ A.dualMap '' subdifferentialAt h (A x) := by
  have hconv : ConvexFunction h := by
    simpa [ConvexFunction] using hproper.1
  rcases hri with ⟨z, hzRange, hzri⟩
  rcases hzRange with ⟨x0, rfl⟩
  -- The qualification point lies in `dom h`, so `h ∘ A` is proper and Theorem 23.5 applies.
  have hzDom : A x0 ∈ effectiveDomain Set.univ h :=
    helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin hzri
  have hAproper :=
    helperForTheorem_23_9_precomp_proper_of_range_meets_effectiveDomain A h hproper
      ⟨A x0, ⟨x0, rfl⟩, hzDom⟩
  have hriEuclid :
      ∃ x0e : EuclideanSpace ℝ (Fin n),
        helperForTheorem_23_9_euclideanLinearLift A x0e ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain Set.univ h) := by
    refine ⟨WithLp.toLp 2 x0, ?_⟩
    have hzri' :
        (EuclideanSpace.equiv (Fin m) ℝ).symm (A x0) ∈
          euclideanRelativeInterior m
            ((EuclideanSpace.equiv (Fin m) ℝ).symm '' effectiveDomain Set.univ h) :=
      (mem_euclideanRelativeInterior_fin_iff
        (n := m) (C := effectiveDomain Set.univ h) (x := A x0)).1 hzri
    simpa [helperForTheorem_23_9_euclideanLinearLift,
      helperForTheorem_23_4_preimage_eq_symmImage] using hzri'
  have hsec16 :=
    section16_fenchelConjugate_precomp_eq_adjoint_image_of_exists_mem_ri_effectiveDomain
      (A := helperForTheorem_23_9_euclideanLinearLift A) (g := h) hconv hriEuclid
  let xStarE : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xStar
  have hxStarE : IsEuclideanSubgradientAt (fun y => h (A y)) x xStarE := by
    change dotProductEquiv ℝ (Fin n) xStarE ∈ subdifferentialAt (fun y => h (A y)) x
    simpa [xStarE] using hxStar
  have hfy_precomp : FenchelYoungEqualityAt (fun y => h (A y)) x xStarE := by
    exact
      ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        (fun y => h (A y)) hAproper x xStarE).1.out 0 3).1 hxStarE
  have hconj_ne_top : fenchelConjugate n (fun y => h (A y)) xStarE ≠ (⊤ : EReal) := by
    have hfinite :=
      helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality
        (f := fun y => h (A y)) hAproper x xStarE (le_of_eq hfy_precomp)
    intro htop
    rw [FenchelYoungEqualityAt] at hfy_precomp
    have hleft_top :
        (fun y => h (A y)) x + fenchelConjugate n (fun y => h (A y)) xStarE = (⊤ : EReal) := by
      simpa [htop] using (EReal.add_top_of_ne_bot hfinite.2)
    exact EReal.coe_ne_top (dotProduct x xStarE) (hfy_precomp.symm.trans hleft_top)
  have hEq_x :
      fenchelConjugate n (fun y => h (A y)) xStarE =
        sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) => fenchelConjugate m h (yStar : Fin m → ℝ)) ''
            {yStar |
              (LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A)) yStar =
                WithLp.toLp 2 xStarE}) := by
    simpa [helperForTheorem_23_9_euclideanLinearLift, xStarE] using
      congrArg (fun f => f xStarE) hsec16.1
  have hFiber_ne_top :
      sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) => fenchelConjugate m h (yStar : Fin m → ℝ)) ''
            {yStar |
              (LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A)) yStar =
                WithLp.toLp 2 xStarE}) ≠ (⊤ : EReal) := by
    simpa [hEq_x] using hconj_ne_top
  rcases hsec16.2 xStarE with htop | ⟨yStarEuc, hyFiber, hyAtt⟩
  · exact False.elim (hFiber_ne_top htop)
  · -- The attained fiber value provides the codomain dual vector we need in the image set.
    let yStar : Module.Dual ℝ (Fin m → ℝ) := dotProductEquiv ℝ (Fin m) (yStarEuc : Fin m → ℝ)
    have hdual : A.dualMap yStar = xStar := by
      simpa [xStarE, yStar] using
        helperForTheorem_23_9_dualMap_eq_of_adjoint_eq A xStarE (yStarEuc : Fin m → ℝ) hyFiber
    have hconj :
        fenchelConjugate m h ((dotProductEquiv ℝ (Fin m)).symm yStar) =
          fenchelConjugate n (fun y => h (A y)) ((dotProductEquiv ℝ (Fin n)).symm xStar) := by
      simpa [xStarE, yStar, hEq_x] using hyAtt
    have hySub : yStar ∈ subdifferentialAt h (A x) :=
      helperForTheorem_23_9_subgradient_of_h_of_attained_dualFiber
        A h hproper hAproper x xStar yStar hxStar hdual hconj
    exact ⟨yStar, hySub, hdual⟩

/-- Helper for Theorem 23.9: convert the Euclidean adjoint of the lifted map back to a linear map
between coordinate spaces. -/
noncomputable def helperForTheorem_23_9_coordinateAdjointMap {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  (WithLp.linearEquiv (2 : ENNReal) ℝ (Fin n → ℝ)).toLinearMap.comp
    ((LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A)).comp
      ((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin m → ℝ)).symm.toLinearMap))

/-- Helper for Theorem 23.9: the Section 16 adjoint-fiber infimum is exactly the
`imageUnderLinearMap` of `h*` under the coordinate adjoint map. -/
lemma helperForTheorem_23_9_rawAdjointImage_eq_imageUnderCoordinateAdjoint {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (h : (Fin m → ℝ) → EReal) :
    (fun xStar : Fin n → ℝ =>
      sInf
        ((fun yStar : EuclideanSpace ℝ (Fin m) =>
            fenchelConjugate m h (yStar : Fin m → ℝ)) ''
          {yStar |
            (LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A)) yStar =
              WithLp.toLp 2 xStar})) =
      imageUnderLinearMap
        (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h) := by
  -- Rewrite both fibers by explicit witness conversion, so the result is stable under the
  -- `WithLp` coercions used by Section 16.
  ext xStar
  apply congrArg sInf
  ext z
  constructor
  · rintro ⟨yStar, hyStar, rfl⟩
    refine ⟨(yStar : Fin m → ℝ), ?_, rfl⟩
    have hyStar' :
        (((LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A)) yStar) : Fin n → ℝ) =
          xStar := by
      simpa using congrArg (fun v : EuclideanSpace ℝ (Fin n) => (v : Fin n → ℝ)) hyStar
    simpa [helperForTheorem_23_9_coordinateAdjointMap] using hyStar'
  · rintro ⟨yStarE, hyStarE, rfl⟩
    refine ⟨(WithLp.toLp 2 yStarE : EuclideanSpace ℝ (Fin m)), ?_, rfl⟩
    have hyStarE' :
        (((LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A))
            (WithLp.toLp 2 yStarE)) : Fin n → ℝ) = xStar := by
      simpa [helperForTheorem_23_9_coordinateAdjointMap] using hyStarE
    ext i
    simpa using congrArg (fun f : Fin n → ℝ => f i) hyStarE'

/-- Helper for Theorem 23.9: once the range of `A` meets `dom h`, the coordinate adjoint image of
`h*` is proper convex in the target coordinates. -/
lemma helperForTheorem_23_9_coordinateAdjointImage_proper_of_polyhedral {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (h : (Fin m → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ h)
    (hpoly : IsPolyhedralConvexFunction m h)
    (hw : ∃ z : Fin m → ℝ, z ∈ Set.range A ∧ z ∈ effectiveDomain Set.univ h) :
    ProperConvexFunctionOn Set.univ
      (imageUnderLinearMap
        (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h)) := by
  have hconv : ConvexFunction h := by
    simpa [ConvexFunction] using hproper.1
  have hAproper :=
    helperForTheorem_23_9_precomp_proper_of_range_meets_effectiveDomain A h hproper hw
  have hsec16 :=
    section16_fenchelConjugate_precomp_convexFunctionClosure_eq_convexFunctionClosure_adjoint_image
      (A := helperForTheorem_23_9_euclideanLinearLift A) (g := h) hconv
  have hhClosure :=
    helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_polyhedral_proper
      (g := h) hpoly hproper
  have hstarProper : ProperConvexFunctionOn Set.univ (fenchelConjugate m h) :=
    proper_fenchelConjugate_of_proper (n := m) (f := h) hproper
  have hstarPoly : IsPolyhedralConvexFunction m (fenchelConjugate m h) :=
    polyhedralConvexFunction_fenchelConjugate m h hpoly
  have hImagePoly :
      IsPolyhedralConvexFunction n
        (imageUnderLinearMap
          (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h)) :=
    ((polyhedralConvexFunction_image_preimage_linear m n
        (helperForTheorem_23_9_coordinateAdjointMap A)).1
      (fenchelConjugate m h) hstarPoly).1
  refine ⟨hImagePoly.1, ?_, ?_⟩
  · -- Push a finite point of `h*` through the coordinate adjoint map to get a finite epigraph
    -- point of the image function.
    obtain ⟨y0, r0, hy0⟩ :=
      properConvexFunctionOn_exists_finite_point (n := m) (f := fenchelConjugate m h) hstarProper
    refine ⟨(helperForTheorem_23_9_coordinateAdjointMap A y0, r0), ?_⟩
    refine
      (mem_epigraph_univ_iff
        (f := imageUnderLinearMap
          (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h))).2 ?_
    have hsInf_le :
        imageUnderLinearMap
            (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h)
            (helperForTheorem_23_9_coordinateAdjointMap A y0) ≤
          fenchelConjugate m h y0 := by
      have hyMem :
          fenchelConjugate m h y0 ∈
            {z : EReal |
              ∃ x : Fin m → ℝ,
                helperForTheorem_23_9_coordinateAdjointMap A x =
                    helperForTheorem_23_9_coordinateAdjointMap A y0 ∧
                  z = fenchelConjugate m h x} := by
        exact ⟨y0, rfl, rfl⟩
      simpa [imageUnderLinearMap] using (sInf_le hyMem)
    simpa [hy0] using hsInf_le
  · -- Route correction: instead of proving `⊥`-avoidance directly on the infimum fiber, transport
    -- the claim through the Section 16 closure identity and the properness of `(h ∘ A)*`.
    intro xStar _ hbot
    have hprecompStarProper :
        ProperConvexFunctionOn Set.univ (fenchelConjugate n (fun y => h (A y))) :=
      proper_fenchelConjugate_of_proper (n := n) (f := fun y => h (A y)) hAproper
    have hEqClosure :
        fenchelConjugate n (fun y => h (A y)) =
          convexFunctionClosure
            (imageUnderLinearMap
              (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h)) := by
      calc
        fenchelConjugate n (fun y => h (A y)) =
            fenchelConjugate n (fun y => convexFunctionClosure h (A y)) := by
              congr 1
              ext y
              rw [hhClosure]
        _ = convexFunctionClosure
              (fun xStar : Fin n → ℝ =>
                sInf
                  ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                      fenchelConjugate m h (yStar : Fin m → ℝ)) ''
                    {yStar |
                      (LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A)) yStar =
                        WithLp.toLp 2 xStar})) := hsec16
        _ = convexFunctionClosure
              (imageUnderLinearMap
                (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h)) := by
              rw [helperForTheorem_23_9_rawAdjointImage_eq_imageUnderCoordinateAdjoint A h]
    have hcl_bot :
        convexFunctionClosure
            (imageUnderLinearMap
              (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h)) xStar =
          ⊥ := by
      have hcl_le :=
        (convexFunctionClosure_le_self
          (f := imageUnderLinearMap
            (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h))) xStar
      exact le_antisymm (hcl_le.trans_eq hbot) bot_le
    have hleft_bot : fenchelConjugate n (fun y => h (A y)) xStar = ⊥ := by
      simpa [hEqClosure] using hcl_bot
    exact hprecompStarProper.2.2 xStar (by simp) hleft_bot

end Section23
end Chap05
