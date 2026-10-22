/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part12

open scoped Pointwise

section Chap08
section Section38

attribute [local instance] instTopologicalSpace_moduleDual_weak_part3

/-- Helper for Theorem 38.5: the textbook three-variable objective
`h(u, x, y) = F u x + G x y`. -/
noncomputable def helperForTheorem_38_5_threeVariableObjective
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (u : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin p → ℝ) : EReal :=
  F.toFun u x + G.toFun x y

/-- Helper for Theorem 38.5: the same textbook objective packed onto `ℝ^(n + (m + p))` so the
middle block `x` can be eliminated by Theorem 5.7. -/
noncomputable def helperForTheorem_38_5_packedTripleObjective
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p) :
    (Fin (n + (m + p)) → ℝ) → EReal :=
  fun w =>
    helperForTheorem_38_5_threeVariableObjective F G
      (projXLinearMap (n := m) (m := p)
        (projLamLinearMap (n := n) (m := m + p) w))
      (projXLinearMap (n := n) (m := m + p) w)
      (projLamLinearMap (n := m) (m := p)
        (projLamLinearMap (n := n) (m := m + p) w))

/-- Helper for Theorem 38.5: the textbook function
`f(x) = inf_u {⟨u, u*⟩ - (F_* x)(u)}`. -/
noncomputable def helperForTheorem_38_5_textbookPrimalMiddleFunction
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (uStar : Module.Dual ℝ (Fin m → ℝ)) : (Fin n → ℝ) → EReal :=
  fun x => ⨅ u : Fin m → ℝ, ((uStar u : ℝ) : EReal) + F.toFun u x

/-- Helper for Theorem 38.5: the textbook function
`g(x) = sup_y {⟨y, y*⟩ - G x y}`. -/
noncomputable def helperForTheorem_38_5_textbookDualMiddleFunction
    {n p : Nat} (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ)) : (Fin n → ℝ) → EReal :=
  fun x => ⨆ y : Fin p → ℝ, ((yStar y : ℝ) : EReal) + (-G.toFun x y)

/-- Helper for Theorem 38.5: any real-valued linear functional, viewed as an `EReal`-valued
function on `ℝ^m`, is proper convex on all of `ℝ^m`. -/
lemma helperForTheorem_38_5_dualLinearFunctional_properConvexFunctionOn_univ
    {m : Nat} (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ))
      (fun u : Fin m → ℝ => ((uStar u : ℝ) : EReal)) := by
  have hconvOn :
      ConvexFunctionOn (Set.univ : Set (Fin m → ℝ))
        (fun u : Fin m → ℝ => ((uStar u : ℝ) : EReal)) := by
    refine
      (convexFunctionOn_univ_iff_jensen_inequality
        (f := fun u : Fin m → ℝ => ((uStar u : ℝ) : EReal))
        (hnotbot := by
          intro u
          exact EReal.coe_ne_bot (uStar u))).2 ?_
    intro k w x hw hsum
    have hlin :
        uStar (∑ i : Fin k, w i • x i) = ∑ i : Fin k, w i * uStar (x i) := by
      simp [map_sum]
    have hsumCoe :
        (((∑ i : Fin k, w i * uStar (x i) : ℝ)) : EReal) =
          ∑ i : Fin k, (((w i * uStar (x i) : ℝ)) : EReal) := by
      classical
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty =>
          simp
      | @insert i s hi ih =>
          simp [Finset.sum_insert, hi, ih, EReal.coe_add]
    exact le_of_eq <| calc
      (((uStar (∑ i : Fin k, w i • x i) : ℝ)) : EReal)
          = (((∑ i : Fin k, w i * uStar (x i) : ℝ)) : EReal) := by rw [hlin]
      _ = ∑ i : Fin k, (((w i * uStar (x i) : ℝ)) : EReal) := hsumCoe
      _ = ∑ i : Fin k, ((w i : ℝ) : EReal) * (((uStar (x i) : ℝ) : EReal)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [EReal.coe_mul]
  refine ⟨hconvOn, ?_, ?_⟩
  · refine ⟨((0 : Fin m → ℝ), 0), ?_⟩
    exact
      (mem_epigraph_univ_iff
        (f := fun u : Fin m → ℝ => ((uStar u : ℝ) : EReal))).2
        (by simp)
  · intro u _
    exact EReal.coe_ne_bot (uStar u)

/-- Helper for Theorem 38.5: the textbook middle function
`x ↦ inf_u {⟨u, u*⟩ - (F_* x)(u)}` is convex. -/
lemma helperForTheorem_38_5_textbookPrimalMiddleFunction_convexOn
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hF_properConvex : ProperConvexBifunction F.toFun) :
    ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (helperForTheorem_38_5_textbookPrimalMiddleFunction F uStar) := by
  let packedGraphMap : (Fin (n + m) → ℝ) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
    { toFun := fun z =>
        Fin.append
          (projLamLinearMap (n := n) (m := m) z)
          (projXLinearMap (n := n) (m := m) z)
      map_add' := by
        intro z₁ z₂
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_left, Pi.add_apply]
        | right i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_right, Pi.add_apply]
      map_smul' := by
        intro a z
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_left, Pi.smul_apply]
        | right i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_right, Pi.smul_apply] }
  let objective : (Fin (n + m) → ℝ) → EReal :=
    fun z =>
      ((uStar (projLamLinearMap (n := n) (m := m) z) : ℝ) : EReal) +
        bifunctionGraphFunction F.toFun (packedGraphMap z)
  have hProjLam_surj : Function.Surjective (projLamLinearMap (n := n) (m := m)) := by
    intro u
    refine ⟨Fin.append (0 : Fin n → ℝ) u, ?_⟩
    ext i
    simp [projLamLinearMap, Fin.append_right]
  have hPackedGraphMap_surj : Function.Surjective packedGraphMap := by
    intro z
    refine ⟨Fin.append
      (fun j : Fin n => z (Fin.natAdd m j))
      (fun i : Fin m => z (Fin.castAdd n i)), ?_⟩
    ext i
    cases i using Fin.addCases with
    | left i =>
        simp [packedGraphMap, projLamLinearMap, projXLinearMap, Fin.append_left]
    | right i =>
        simp [packedGraphMap, projLamLinearMap, projXLinearMap, Fin.append_right]
  have hLinearProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
        (fun z : Fin (n + m) → ℝ =>
          ((uStar (projLamLinearMap (n := n) (m := m) z) : ℝ) : EReal)) := by
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := projLamLinearMap (n := n) (m := m)) hProjLam_surj
      (helperForTheorem_38_5_dualLinearFunctional_properConvexFunctionOn_univ uStar)
  have hGraphProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (bifunctionGraphFunction F.toFun) := by
    exact
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := bifunctionGraphFunction F.toFun) hF_properConvex.2
  have hPackedGraphProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
        (fun z : Fin (n + m) → ℝ => bifunctionGraphFunction F.toFun (packedGraphMap z)) := by
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := packedGraphMap) hPackedGraphMap_surj hGraphProper
  have hObjectiveConv :
      ConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ)) objective := by
    simpa [objective] using
      (convexFunctionOn_add_of_proper
        (n := n + m) hLinearProper hPackedGraphProper)
  have hFiberConv :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x : Fin n → ℝ =>
          sInf {r : EReal |
            ∃ z : Fin (n + m) → ℝ,
              projXLinearMap (n := n) (m := m) z = x ∧ r = objective z}) := by
    simpa using
      (convexFunctionOn_inf_fiber_linearMap
        (A := projXLinearMap (n := n) (m := m))
        (h := objective) hObjectiveConv)
  have hEq :
      (fun x : Fin n → ℝ =>
        sInf {r : EReal |
          ∃ z : Fin (n + m) → ℝ,
            projXLinearMap (n := n) (m := m) z = x ∧ r = objective z}) =
        helperForTheorem_38_5_textbookPrimalMiddleFunction F uStar := by
    funext x
    have hset :
        {r : EReal |
            ∃ z : Fin (n + m) → ℝ,
              projXLinearMap (n := n) (m := m) z = x ∧ r = objective z} =
          Set.range (fun u : Fin m → ℝ => ((uStar u : ℝ) : EReal) + F.toFun u x) := by
      ext r
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨projLamLinearMap (n := n) (m := m) z, ?_⟩
        simp [objective, bifunctionGraphFunction, packedGraphMap, hz]
      · rintro ⟨u, rfl⟩
        refine ⟨Fin.append x u, ?_, ?_⟩
        · ext i
          simp [projXLinearMap, Fin.append_left]
        · simp [objective, packedGraphMap, bifunctionGraphFunction, projLamLinearMap,
            projXLinearMap]
    rw [hset, sInf_range, helperForTheorem_38_5_textbookPrimalMiddleFunction]
  simpa [hEq] using hFiberConv

/-- Helper for Theorem 38.5: rewrite the textbook `f(x)` through the inverse bifunction notation
`F_*`. -/
lemma helperForTheorem_38_5_textbookPrimalMiddleFunction_eq_iInf_inverse
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (uStar : Module.Dual ℝ (Fin m → ℝ)) (x : Fin n → ℝ) :
    helperForTheorem_38_5_textbookPrimalMiddleFunction F uStar x =
      ⨅ u : Fin m → ℝ, ((uStar u : ℝ) : EReal) + (-bifunctionInverse F.toFun x u) := by
  simp [helperForTheorem_38_5_textbookPrimalMiddleFunction, bifunctionInverse]

/-- Helper for Theorem 38.5: the `u`-slice appearing in the fixed-`x` reduced problem is the
primal middle function evaluated at `-uStar`. -/
lemma helperForTheorem_38_5_textbookPrimalMiddleFunction_negDual
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (uStar : Module.Dual ℝ (Fin m → ℝ)) (x : Fin n → ℝ) :
    helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x =
      ⨅ u : Fin m → ℝ, (-((uStar u : ℝ) : EReal)) + F.toFun u x := by
  simp [helperForTheorem_38_5_textbookPrimalMiddleFunction]

/-- Helper for Theorem 38.5: rewrite the textbook `g(x)` in the explicit
`sup_y {⟨y, y*⟩ - G x y}` form used in the original proof. -/
lemma helperForTheorem_38_5_textbookDualMiddleFunction_eq_iSup
    {n p : Nat} (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ)) (x : Fin n → ℝ) :
    helperForTheorem_38_5_textbookDualMiddleFunction G yStar x =
      ⨆ y : Fin p → ℝ, (((yStar y : ℝ) : EReal) - G.toFun x y) := by
  simp [helperForTheorem_38_5_textbookDualMiddleFunction, sub_eq_add_neg]

/-- Helper for Theorem 38.5: negating the dual middle function at `-yStar` produces the `y`-side
infimum `inf_y {⟨y, y*⟩ + G x y}` that occurs in the current sign convention for the adjoint. -/
lemma helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_eq_iInf
    {n p : Nat} (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ)) (x : Fin n → ℝ) :
    -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x) =
      ⨅ y : Fin p → ℝ, ((yStar y : ℝ) : EReal) + G.toFun x y := by
  have hRewrite :
      helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x =
        ⨆ y : Fin p → ℝ, -((((yStar y : ℝ) : EReal) + G.toFun x y)) := by
    rw [helperForTheorem_38_5_textbookDualMiddleFunction]
    refine iSup_congr ?_
    intro y
    have hy_ne_bot : (((yStar y : ℝ) : EReal)) ≠ ⊥ := EReal.coe_ne_bot (yStar y)
    have hG_ne_bot : G.toFun x y ≠ ⊥ := G.proper.1 x y
    calc
      ((((-yStar) y : ℝ) : EReal) + (-G.toFun x y))
          = (-(((yStar y : ℝ) : EReal))) + (-G.toFun x y) := by simp
      _ = -((((yStar y : ℝ) : EReal) + G.toFun x y)) := by
          simpa [add_comm] using
            (helperForProposition_38_4_2_neg_add_of_neBot hy_ne_bot hG_ne_bot).symm
  have hNegInf :=
    ereal_iSup_neg_eq_neg_iInf
      (g := fun y : Fin p → ℝ => (((yStar y : ℝ) : EReal) + G.toFun x y))
  calc
    -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x) =
        -(⨆ y : Fin p → ℝ, -((((yStar y : ℝ) : EReal) + G.toFun x y))) := by
          rw [hRewrite]
    _ = ⨅ y : Fin p → ℝ, ((yStar y : ℝ) : EReal) + G.toFun x y := by
          simpa using congrArg Neg.neg hNegInf

/-- Helper for Theorem 38.5: the fixed-middle-variable reduced objective obtained after moving the
outer minimization to the middle variable `x`. -/
noncomputable def helperForTheorem_38_5_middleReducedObjective
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) : (Fin n → ℝ) → EReal :=
  fun x =>
    ⨅ u : Fin m → ℝ, ⨅ y : Fin p → ℝ,
      ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
        (F.toFun u x + G.toFun x y)

/-- Helper for Theorem 38.5: the original-text second-shift perturbation written as a partial
infimum over the auxiliary primal/dual variables `(u, y)`. This is the corrected object behind
the guarded value function `z ↦ inf_x (f x - g (x + z))`. -/
noncomputable def helperForTheorem_38_5_secondShiftMiddleReducedObjective
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) : (Fin n → ℝ) → (Fin n → ℝ) → EReal :=
  fun z x =>
    ⨅ u : Fin m → ℝ, ⨅ y : Fin p → ℝ,
      ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
        (F.toFun u x + G.toFun (x + z) y)

/-- Helper for Theorem 38.5: when the fixed-`x` primal and dual slices each admit one finite
witness, the reduced middle-variable objective splits into the textbook `f(x) - g(x)` form. -/
lemma helperForTheorem_38_5_middleReducedObjective_eq_textbookPieces
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) (x : Fin n → ℝ)
    (hPrimalFinite : ∃ u : Fin m → ℝ, (-((uStar u : ℝ) : EReal)) + F.toFun u x < ⊤)
    (hDualFinite : ∃ y : Fin p → ℝ, ((yStar y : ℝ) : EReal) + G.toFun x y < ⊤) :
    helperForTheorem_38_5_middleReducedObjective F G yStar uStar x =
      helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x +
        -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x) := by
  let A : (Fin m → ℝ) → EReal := fun u =>
    (-((uStar u : ℝ) : EReal)) + F.toFun u x
  let B : (Fin p → ℝ) → EReal := fun y =>
    ((yStar y : ℝ) : EReal) + G.toFun x y
  have hNested :
      helperForTheorem_38_5_middleReducedObjective F G yStar uStar x =
        (⨅ q : (Fin m → ℝ) × (Fin p → ℝ), A q.1 + B q.2) := by
    rw [helperForTheorem_38_5_middleReducedObjective]
    have hReassoc :
        (⨅ u : Fin m → ℝ, ⨅ y : Fin p → ℝ,
            ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
              (F.toFun u x + G.toFun x y)) =
          (⨅ u : Fin m → ℝ, ⨅ y : Fin p → ℝ, A u + B y) := by
      refine iInf_congr ?_
      intro u
      refine iInf_congr ?_
      intro y
      simp [A, B, add_assoc, add_left_comm, add_comm]
    rw [hReassoc]
    rw [← helperForTheorem_6_30_22_iInf_prod_eq_nested (H := fun u y => A u + B y)]
  rw [hNested]
  rw [helperForTheorem_6_30_22_twoFactor_iInf_eq_iInf_add_iInf
    (F := A) (G := B) hPrimalFinite hDualFinite]
  have hA :
      (⨅ u : Fin m → ℝ, A u) =
        helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x := by
    symm
    exact helperForTheorem_38_5_textbookPrimalMiddleFunction_negDual F uStar x
  have hB :
      (⨅ y : Fin p → ℝ, B y) =
        -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x) := by
    symm
    exact helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_eq_iInf G yStar x
  rw [hA, hB]

/-- Helper for Theorem 38.5: for fixed `z`, the corrected second-shift reduced objective splits as
`f(x) - g(x + z)` once the primal slice at `x` and the dual slice at `x + z` both have a finite
witness. -/
lemma helperForTheorem_38_5_secondShiftMiddleReducedObjective_eq_textbookPieces
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (z x : Fin n → ℝ)
    (hPrimalFinite : ∃ u : Fin m → ℝ, (-((uStar u : ℝ) : EReal)) + F.toFun u x < ⊤)
    (hDualFinite : ∃ y : Fin p → ℝ, ((yStar y : ℝ) : EReal) + G.toFun (x + z) y < ⊤) :
    helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar z x =
      helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x +
        -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) (x + z)) := by
  let A : (Fin m → ℝ) → EReal := fun u =>
    (-((uStar u : ℝ) : EReal)) + F.toFun u x
  let B : (Fin p → ℝ) → EReal := fun y =>
    ((yStar y : ℝ) : EReal) + G.toFun (x + z) y
  have hNested :
      helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar z x =
        (⨅ q : (Fin m → ℝ) × (Fin p → ℝ), A q.1 + B q.2) := by
    rw [helperForTheorem_38_5_secondShiftMiddleReducedObjective]
    have hReassoc :
        (⨅ u : Fin m → ℝ, ⨅ y : Fin p → ℝ,
            ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
              (F.toFun u x + G.toFun (x + z) y)) =
          (⨅ u : Fin m → ℝ, ⨅ y : Fin p → ℝ, A u + B y) := by
      refine iInf_congr ?_
      intro u
      refine iInf_congr ?_
      intro y
      simp [A, B, add_assoc, add_left_comm, add_comm]
    rw [hReassoc]
    rw [← helperForTheorem_6_30_22_iInf_prod_eq_nested (H := fun u y => A u + B y)]
  rw [hNested]
  rw [helperForTheorem_6_30_22_twoFactor_iInf_eq_iInf_add_iInf
    (F := A) (G := B) hPrimalFinite hDualFinite]
  have hA :
      (⨅ u : Fin m → ℝ, A u) =
        helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x := by
    symm
    exact helperForTheorem_38_5_textbookPrimalMiddleFunction_negDual F uStar x
  have hB :
      (⨅ y : Fin p → ℝ, B y) =
        -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) (x + z)) := by
    symm
    exact helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_eq_iInf G yStar (x + z)
  rw [hA, hB]

/-- Helper for Theorem 38.5: the convex function underlying the textbook
`g(x) = sup_y {⟨y, y*⟩ - G x y}` is the negated slice at `-yStar`. -/
lemma helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_convexOn
    {n p : Nat} (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x : Fin n → ℝ => -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x)) := by
  let objective : (Fin (n + p) → ℝ) → EReal :=
    fun z =>
      ((yStar (projLamLinearMap (n := n) (m := p) z) : ℝ) : EReal) +
        bifunctionGraphFunction G.toFun z
  have hProjLam_surj : Function.Surjective (projLamLinearMap (n := n) (m := p)) := by
    intro y
    refine ⟨Fin.append (0 : Fin n → ℝ) y, ?_⟩
    ext i
    simp [projLamLinearMap, Fin.append_right]
  have hLinearProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + p) → ℝ))
        (fun z : Fin (n + p) → ℝ =>
          ((yStar (projLamLinearMap (n := n) (m := p) z) : ℝ) : EReal)) := by
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := projLamLinearMap (n := n) (m := p)) hProjLam_surj
      (helperForTheorem_38_5_dualLinearFunctional_properConvexFunctionOn_univ yStar)
  have hGraphProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + p) → ℝ))
        (bifunctionGraphFunction G.toFun) := by
    exact
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := bifunctionGraphFunction G.toFun) hG_properConvex.2
  have hObjectiveConv :
      ConvexFunctionOn (Set.univ : Set (Fin (n + p) → ℝ)) objective := by
    simpa [objective] using
      (convexFunctionOn_add_of_proper
        (n := n + p) hLinearProper hGraphProper)
  have hFiberConv :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x : Fin n → ℝ =>
          sInf {r : EReal |
            ∃ z : Fin (n + p) → ℝ,
              projXLinearMap (n := n) (m := p) z = x ∧ r = objective z}) := by
    simpa using
      (convexFunctionOn_inf_fiber_linearMap
        (A := projXLinearMap (n := n) (m := p))
        (h := objective) hObjectiveConv)
  have hEq :
      (fun x : Fin n → ℝ =>
        sInf {r : EReal |
          ∃ z : Fin (n + p) → ℝ,
            projXLinearMap (n := n) (m := p) z = x ∧ r = objective z}) =
        (fun x : Fin n → ℝ => -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x)) := by
    funext x
    have hset :
        {r : EReal |
            ∃ z : Fin (n + p) → ℝ,
              projXLinearMap (n := n) (m := p) z = x ∧ r = objective z} =
          Set.range (fun y : Fin p → ℝ => ((yStar y : ℝ) : EReal) + G.toFun x y) := by
      ext r
      constructor
      · rintro ⟨z, hz, rfl⟩
        subst x
        refine ⟨projLamLinearMap (n := n) (m := p) z, ?_⟩
        change
          ((yStar (projLamLinearMap (n := n) (m := p) z) : ℝ) : EReal) +
              G.toFun (fun i => z (Fin.castAdd p i)) (fun j => z (Fin.natAdd n j)) =
            objective z
        rfl
      · rintro ⟨y, rfl⟩
        refine ⟨Fin.append x y, ?_, ?_⟩
        · ext i
          simp [projXLinearMap, Fin.append_left]
        · simp [objective, bifunctionGraphFunction, projLamLinearMap]
    rw [hset, sInf_range]
    simpa using
      (helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_eq_iInf
        (G := G) (yStar := yStar) (x := x)).symm
  simpa [hEq] using hFiberConv

/-- Helper for Theorem 38.5: after identifying the middle dual variable with its Euclidean vector
via `dotProductEquiv`, the left adjoint term `F^*(x*, u*)` is the negative Fenchel conjugate of
the textbook primal middle function `x ↦ inf_u {⟨u, -u*⟩ + F u x}`. -/
lemma helperForTheorem_38_5_adjoint_firstFactor_eq_neg_fenchelConjugate_textbookPrimal
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (xStar : Module.Dual ℝ (Fin n → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionAdjoint F.toFun xStar uStar =
      -fenchelConjugate n
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (-((dotProductEquiv ℝ (Fin n)).symm xStar)) := by
  let xVec : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xStar
  have hSlice :
      bifunctionAdjoint F.toFun xStar uStar =
        ⨅ x : Fin n → ℝ,
          (((xVec ⬝ᵥ x : ℝ) : EReal) +
            helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x) := by
    rw [bifunctionAdjoint, iInf_comm]
    refine iInf_congr ?_
    intro x
    have hpair : (xVec ⬝ᵥ x) = xStar x := by
      simpa [xVec] using
        (dotProductEquiv_apply_apply ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm xStar) x).symm
    have hRewrite :
        (⨅ u : Fin m → ℝ, ((xStar x : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) + F.toFun u x) =
          (((xStar x : ℝ) : EReal) +
            ⨅ u : Fin m → ℝ, (-((uStar u : ℝ) : EReal)) + F.toFun u x) := by
      have hPointwise :
          (⨅ u : Fin m → ℝ, ((xStar x : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) + F.toFun u x) =
            (⨅ u : Fin m → ℝ, ((xStar x : ℝ) : EReal) +
              ((-((uStar u : ℝ) : EReal)) + F.toFun u x)) := by
        refine iInf_congr ?_
        intro u
        simp [add_assoc, add_comm]
      rw [hPointwise]
      symm
      exact
        helperForTheorem_6_30_15_real_add_iInf (xStar x)
          (fun u : Fin m → ℝ => (-((uStar u : ℝ) : EReal)) + F.toFun u x)
    rw [hRewrite]
    have hpairE :
        ((xStar x : ℝ) : EReal) = (((xVec ⬝ᵥ x : ℝ) : EReal)) := by
      exact_mod_cast hpair.symm
    rw [hpairE]
    simp [helperForTheorem_38_5_textbookPrimalMiddleFunction]
  have hFenchelAsInf :
      -fenchelConjugate n
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) (-xVec) =
          ⨅ x : Fin n → ℝ,
            -((((x ⬝ᵥ (-xVec) : ℝ) : EReal) -
                helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x)) := by
    have hSup :
        fenchelConjugate n
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) (-xVec) =
            -(⨅ x : Fin n → ℝ,
                -((((x ⬝ᵥ (-xVec) : ℝ) : EReal) -
                    helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x))) := by
      rw [fenchelConjugate_eq_iSup]
      simpa using
        (helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
          (φ := fun x : Fin n → ℝ =>
            -((((x ⬝ᵥ (-xVec) : ℝ) : EReal) -
                helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x)))).symm
    simpa using congrArg Neg.neg hSup
  calc
    bifunctionAdjoint F.toFun xStar uStar
        = (⨅ x : Fin n → ℝ,
            -((((x ⬝ᵥ (-xVec) : ℝ) : EReal) -
                helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x))) := by
            rw [hSlice]
            refine iInf_congr ?_
            intro x
            have hComm : (xVec ⬝ᵥ x) = (x ⬝ᵥ xVec) := by
              simpa using (dotProduct_comm xVec x)
            have hdot : (x ⬝ᵥ (-xVec) : ℝ) = -(xVec ⬝ᵥ x) := by
              rw [dotProduct_comm]
              simp [hComm]
            rw [hdot]
            have hnegSub :
                -((((-(xVec ⬝ᵥ x) : ℝ) : EReal) -
                    helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x)) =
                  (-(((-(xVec ⬝ᵥ x) : ℝ) : EReal))) +
                    helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x := by
              have h1 :
                  (((-(xVec ⬝ᵥ x) : ℝ) : EReal)) ≠ (⊥ : EReal) ∨
                    helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x ≠ (⊥ : EReal) :=
                Or.inl (EReal.coe_ne_bot _)
              have h2 :
                  (((-(xVec ⬝ᵥ x) : ℝ) : EReal)) ≠ (⊤ : EReal) ∨
                    helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x ≠ (⊤ : EReal) :=
                Or.inl (EReal.coe_ne_top _)
              simpa using EReal.neg_sub
                (x := (((-(xVec ⬝ᵥ x) : ℝ) : EReal)))
                (y := helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x)
                h1 h2
            rw [hnegSub]
            simp [add_comm]
    _ = -fenchelConjugate n
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) (-xVec) := by
          rw [hFenchelAsInf]

/-- Helper for Theorem 38.5: under the same Euclidean identification of the middle dual space,
the right adjoint term `G^*(y*, x*)` is the concave Fenchel conjugate of the textbook dual middle
function `x ↦ sup_y {⟨y, -y*⟩ - G x y}`. -/
lemma helperForTheorem_38_5_adjoint_secondFactor_eq_concaveFenchelConjugate_textbookDual
    {n p : Nat} (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (xStar : Module.Dual ℝ (Fin n → ℝ)) :
    bifunctionAdjoint G.toFun yStar xStar =
      concaveFenchelConjugate
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
        (-((dotProductEquiv ℝ (Fin n)).symm xStar)) := by
  let xVec : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xStar
  calc
    bifunctionAdjoint G.toFun yStar xStar
        = ⨅ x : Fin n → ℝ,
            ((((-xVec) ⬝ᵥ x : ℝ) : EReal) -
              helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x) := by
            rw [bifunctionAdjoint]
            refine iInf_congr ?_
            intro x
            have hpair : (xVec ⬝ᵥ x) = xStar x := by
              simpa [xVec] using
                (dotProductEquiv_apply_apply ℝ (Fin n)
                  ((dotProductEquiv ℝ (Fin n)).symm xStar) x).symm
            have hpairNeg :
                (((-xVec) ⬝ᵥ x : ℝ)) = -(xStar x) := by
              calc
                (((-xVec) ⬝ᵥ x : ℝ)) = -(xVec ⬝ᵥ x) := by
                    simp [dotProduct]
                _ = -(xStar x) := by rw [hpair]
            have hRewrite :
                (⨅ y : Fin p → ℝ,
                    ((yStar y : ℝ) : EReal) + (-((xStar x : ℝ) : EReal)) + G.toFun x y) =
                  ((-((xStar x : ℝ) : EReal)) +
                    ⨅ y : Fin p → ℝ, ((yStar y : ℝ) : EReal) + G.toFun x y) := by
              have hPointwise :
                  (⨅ y : Fin p → ℝ,
                      ((yStar y : ℝ) : EReal) + (-((xStar x : ℝ) : EReal)) + G.toFun x y) =
                    (⨅ y : Fin p → ℝ,
                      (-((xStar x : ℝ) : EReal)) +
                        (((yStar y : ℝ) : EReal) + G.toFun x y)) := by
                refine iInf_congr ?_
                intro y
                simp [add_left_comm, add_comm]
              rw [hPointwise]
              symm
              exact
                helperForTheorem_6_30_15_real_add_iInf (-(xStar x))
                  (fun y : Fin p → ℝ => ((yStar y : ℝ) : EReal) + G.toFun x y)
            rw [hRewrite, ← helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_eq_iInf]
            have hpairNegE :
                (((-xVec) ⬝ᵥ x : ℝ) : EReal) = (-((xStar x : ℝ) : EReal)) := by
              exact_mod_cast hpairNeg
            rw [← hpairNegE]
            simp [sub_eq_add_neg]
    _ = concaveFenchelConjugate
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) (-xVec) := by
          rw [helperForLemma_31_0_11_concaveFenchelConjugate_eq_iInf]
          refine iInf_congr ?_
          intro x
          simp [dotProduct_comm]

/-- Helper for Theorem 38.5: after rewriting both adjoint factors through the textbook middle
functions, the supremum composition `F^* G^*` becomes the Fenchel dual supremum of that pair,
still indexed by middle dual vectors via `dotProductEquiv`. -/
lemma helperForTheorem_38_5_composeSupGeneric_eq_iSup_fenchelDualObjective
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        yStar uStar =
      ⨆ xStar : Module.Dual ℝ (Fin n → ℝ),
        fenchelDualObjective
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          (-((dotProductEquiv ℝ (Fin n)).symm xStar)) := by
  rw [bifunctionComposeSupGeneric]
  refine iSup_congr ?_
  intro xStar
  rw [helperForTheorem_38_5_adjoint_secondFactor_eq_concaveFenchelConjugate_textbookDual,
    helperForTheorem_38_5_adjoint_firstFactor_eq_neg_fenchelConjugate_textbookPrimal]
  simp [fenchelDualObjective, sub_eq_add_neg]

/-- Helper for Theorem 38.5: the textbook primal middle function has exactly the domain
`dom F_*`, i.e. those `x` for which some `u` makes `F u x` different from `⊤`. -/
lemma helperForTheorem_38_5_textbookPrimalMiddleFunction_effectiveDomain
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F uStar) =
      bifunctionDomBot (bifunctionInverse F.toFun) := by
  ext x
  constructor
  · intro hx
    rw [effectiveDomain_eq] at hx
    by_contra hxDom
    have hAllTop : ∀ u : Fin m → ℝ, F.toFun u x = (⊤ : EReal) := by
      intro u
      by_contra hu
      apply hxDom
      refine ⟨u, ?_⟩
      simpa [bifunctionInverse] using hu
    have : helperForTheorem_38_5_textbookPrimalMiddleFunction F uStar x = (⊤ : EReal) := by
      rw [helperForTheorem_38_5_textbookPrimalMiddleFunction]
      simp [hAllTop]
    exact (lt_irrefl (⊤ : EReal)) (this ▸ hx.2)
  · intro hx
    simp [bifunctionDomBot, bifunctionInverse] at hx
    rcases hx with ⟨u, hu⟩
    rw [effectiveDomain_eq]
    refine ⟨by simp, ?_⟩
    have hTerm_ne_top :
        ((uStar u : ℝ) : EReal) + F.toFun u x ≠ (⊤ : EReal) := by
      exact EReal.add_ne_top (EReal.coe_ne_top _) hu
    have hlt_top :
        ((uStar u : ℝ) : EReal) + F.toFun u x < (⊤ : EReal) :=
      lt_top_iff_ne_top.mpr hTerm_ne_top
    have hle :
        helperForTheorem_38_5_textbookPrimalMiddleFunction F uStar x ≤
          ((uStar u : ℝ) : EReal) + F.toFun u x := by
      rw [helperForTheorem_38_5_textbookPrimalMiddleFunction]
      exact iInf_le _ u
    exact lt_of_le_of_lt hle hlt_top

/-- Helper for Theorem 38.5: the textbook dual middle function has book concave effective domain
exactly `dom G`. Equivalently, `-g(x)` is finite from above exactly when some `y` makes `G x y`
different from `⊤`. -/
lemma helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain
    {n p : Nat} (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ)) :
    concaveEffectiveDomain (helperForTheorem_38_5_textbookDualMiddleFunction G yStar) =
      bifunctionDom G.toFun := by
  ext x
  constructor
  · intro hx
    simp [concaveEffectiveDomain, effectiveDomain_eq] at hx
    by_contra hxDom
    have hAllTop : ∀ y : Fin p → ℝ, G.toFun x y = (⊤ : EReal) := by
      intro y
      by_contra hy
      apply hxDom
      exact ⟨y, hy⟩
    have : helperForTheorem_38_5_textbookDualMiddleFunction G yStar x = (⊥ : EReal) := by
      have hneg := helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_eq_iInf
        (G := G) (yStar := -yStar) (x := x)
      have htopInf : (⨅ y : Fin p → ℝ, ((((-yStar) y : ℝ) : EReal) + G.toFun x y)) = (⊤ : EReal) := by
        simp [hAllTop]
      have htop : -(helperForTheorem_38_5_textbookDualMiddleFunction G yStar x) = (⊤ : EReal) := by
        simpa using hneg.trans htopInf
      simpa using congrArg Neg.neg htop
    have hnegTop : -(helperForTheorem_38_5_textbookDualMiddleFunction G yStar x) = (⊤ : EReal) := by
      simpa using congrArg Neg.neg this
    exact (lt_irrefl (⊤ : EReal)) (hnegTop ▸ hx)
  · intro hx
    simp [bifunctionDom] at hx
    rcases hx with ⟨y, hy⟩
    simp [concaveEffectiveDomain, effectiveDomain_eq]
    have hneg :
        -(helperForTheorem_38_5_textbookDualMiddleFunction G yStar x) =
          ⨅ y' : Fin p → ℝ, ((((-yStar) y' : ℝ) : EReal) + G.toFun x y') := by
      simpa using
        (helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_eq_iInf
          (G := G) (yStar := -yStar) (x := x))
    rw [hneg]
    have hTerm_ne_top :
        ((((-yStar) y : ℝ) : EReal) + G.toFun x y) ≠ (⊤ : EReal) := by
      exact EReal.add_ne_top (EReal.coe_ne_top _) hy
    have hlt_top :
        ((((-yStar) y : ℝ) : EReal) + G.toFun x y) < (⊤ : EReal) :=
      lt_top_iff_ne_top.mpr hTerm_ne_top
    have hle :
        (⨅ y' : Fin p → ℝ, ((((-yStar) y' : ℝ) : EReal) + G.toFun x y')) ≤
          ((((-yStar) y : ℝ) : EReal) + G.toFun x y) := by
      exact iInf_le _ y
    exact lt_of_le_of_lt hle hlt_top

/-- Helper for Theorem 38.5: the qualification hypothesis stated with intrinsic interiors of
`dom F_*` and `dom G` is exactly Fenchel's condition `(a)` for the textbook middle functions. -/
lemma helperForTheorem_38_5_hri_implies_fenchelConditionA
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    FenchelConditionA (n := n)
      (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
      (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
  rcases hri with ⟨x0, hx0F, hx0G⟩
  let domF :=
    effectiveDomain (Set.univ : Set (Fin n → ℝ))
      (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
  let domG :=
    concaveEffectiveDomain (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
  have hdomF : domF = bifunctionDomBot (bifunctionInverse F.toFun) := by
    simp [domF, helperForTheorem_38_5_textbookPrimalMiddleFunction_effectiveDomain]
  have hdomG : domG = bifunctionDom G.toFun := by
    simp [domG, helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain]
  refine ⟨x0, ?_, ?_⟩
  · rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    have hx0F' : x0 ∈ intrinsicInterior ℝ domF := by
      rw [hdomF]
      exact hx0F
    exact hx0F'
  · rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    have hx0G' : x0 ∈ intrinsicInterior ℝ domG := by
      rw [hdomG]
      exact hx0G
    exact hx0G'

/-- Helper for Theorem 38.5: the reduced middle-variable objective is exactly the Chapter 31
primal objective `commonBookEffectiveDomainDifference f g` built from the textbook middle
functions `f(x) = inf_u {⟨u, -u*⟩ + F u x}` and `g(x) = sup_y {⟨y, -y*⟩ - G x y}`. -/
lemma helperForTheorem_38_5_middleReducedObjective_eq_commonBookEffectiveDomainDifference
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) (x : Fin n → ℝ) :
    helperForTheorem_38_5_middleReducedObjective F G yStar uStar x =
      commonBookEffectiveDomainDifference
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) x := by
  let f : (Fin n → ℝ) → EReal :=
    helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)
  let g : (Fin n → ℝ) → EReal :=
    helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)
  by_cases hx :
      x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩ concaveEffectiveDomain g
  · have hxF : x ∈ bifunctionDomBot (bifunctionInverse F.toFun) := by
      simpa [f, helperForTheorem_38_5_textbookPrimalMiddleFunction_effectiveDomain] using hx.1
    have hxG : x ∈ bifunctionDom G.toFun := by
      simpa [g, helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain] using
        hx.2
    have hPrimalFinite : ∃ u : Fin m → ℝ, (-((uStar u : ℝ) : EReal)) + F.toFun u x < ⊤ := by
      simp [bifunctionDomBot, bifunctionInverse] at hxF
      rcases hxF with ⟨u, hu⟩
      refine ⟨u, lt_top_iff_ne_top.mpr ?_⟩
      exact EReal.add_ne_top (EReal.coe_ne_top _) hu
    have hDualFinite : ∃ y : Fin p → ℝ, ((yStar y : ℝ) : EReal) + G.toFun x y < ⊤ := by
      simp [bifunctionDom] at hxG
      rcases hxG with ⟨y, hy⟩
      refine ⟨y, lt_top_iff_ne_top.mpr ?_⟩
      exact EReal.add_ne_top (EReal.coe_ne_top _) hy
    rw [commonBookEffectiveDomainDifference, if_pos hx]
    simpa [f, g, sub_eq_add_neg] using
      helperForTheorem_38_5_middleReducedObjective_eq_textbookPieces
        (F := F) (G := G) (yStar := yStar) (uStar := uStar) (x := x) hPrimalFinite hDualFinite
  · have hx' :
        x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∨ x ∉ concaveEffectiveDomain g := by
      exact not_and_or.mp hx
    rw [commonBookEffectiveDomainDifference, if_neg hx]
    rcases hx' with hxF | hxG
    · have hAllTopF : ∀ u : Fin m → ℝ, F.toFun u x = (⊤ : EReal) := by
        intro u
        by_contra hu
        apply hxF
        rw [effectiveDomain_eq]
        refine ⟨by simp, ?_⟩
        have hTerm_ne_top :
            (-((uStar u : ℝ) : EReal)) + F.toFun u x ≠ (⊤ : EReal) := by
          exact EReal.add_ne_top (EReal.coe_ne_top _) hu
        have hlt_top :
            (-((uStar u : ℝ) : EReal)) + F.toFun u x < (⊤ : EReal) :=
          lt_top_iff_ne_top.mpr hTerm_ne_top
        have hle :
            f x ≤ (-((uStar u : ℝ) : EReal)) + F.toFun u x := by
          simpa [f, helperForTheorem_38_5_textbookPrimalMiddleFunction] using
            (iInf_le (fun u' : Fin m → ℝ => (-((uStar u' : ℝ) : EReal)) + F.toFun u' x) u)
        exact lt_of_le_of_lt hle hlt_top
      rw [helperForTheorem_38_5_middleReducedObjective]
      apply le_antisymm le_top
      refine le_iInf ?_
      intro u
      refine le_iInf ?_
      intro y
      have hG_ne_bot : G.toFun x y ≠ (⊥ : EReal) := G.proper.1 x y
      have hTopInner : F.toFun u x + G.toFun x y = (⊤ : EReal) := by
        simpa [hAllTopF u] using EReal.top_add_of_ne_bot hG_ne_bot
      have hCoeff_ne_bot :
          (((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal))) ≠ (⊥ : EReal) := by
        exact add_ne_bot_of_notbot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _)
      have hTerm :
          ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
              (F.toFun u x + G.toFun x y) =
            (⊤ : EReal) := by
        simp [hTopInner, EReal.add_top_of_ne_bot hCoeff_ne_bot]
      rw [hTerm]
    · have hAllTopG : ∀ y : Fin p → ℝ, G.toFun x y = (⊤ : EReal) := by
        intro y
        by_contra hy
        apply hxG
        rw [concaveEffectiveDomain, effectiveDomain_eq]
        refine ⟨by simp, ?_⟩
        have hTerm_ne_bot :
            ((((-yStar) y : ℝ) : EReal) + (-G.toFun x y)) ≠ (⊥ : EReal) := by
          exact add_ne_bot_of_notbot (EReal.coe_ne_bot _) (by simpa using hy)
        have hle :
            ((((-yStar) y : ℝ) : EReal) + (-G.toFun x y)) ≤ g x := by
          simpa [g, helperForTheorem_38_5_textbookDualMiddleFunction] using
            (le_iSup (fun y' : Fin p → ℝ => ((((-yStar) y' : ℝ) : EReal) + (-G.toFun x y'))) y)
        have hgx_ne_bot : g x ≠ (⊥ : EReal) := by
          intro hgx_bot
          exact (not_le_of_gt (bot_lt_iff_ne_bot.mpr hTerm_ne_bot))
            (by simpa [hgx_bot] using hle)
        exact lt_top_iff_ne_top.mpr (by
          intro hneg_top
          apply hgx_ne_bot
          simpa using hneg_top)
      rw [helperForTheorem_38_5_middleReducedObjective]
      apply le_antisymm le_top
      refine le_iInf ?_
      intro u
      refine le_iInf ?_
      intro y
      have hF_ne_bot : F.toFun u x ≠ (⊥ : EReal) := F.proper.1 u x
      have hTopInner : F.toFun u x + G.toFun x y = (⊤ : EReal) := by
        simpa [hAllTopG y] using EReal.add_top_of_ne_bot hF_ne_bot
      have hCoeff_ne_bot :
          (((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal))) ≠ (⊥ : EReal) := by
        exact add_ne_bot_of_notbot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _)
      have hTerm :
          ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
              (F.toFun u x + G.toFun x y) =
            (⊤ : EReal) := by
        simp [hTopInner, EReal.add_top_of_ne_bot hCoeff_ne_bot]
      rw [hTerm]


end Section38
end Chap08
