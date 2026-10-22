/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part12

open scoped Pointwise

section Chap08
section Section38

attribute [local instance] instTopologicalSpace_moduleDual_weak_part3

/-- Helper for Theorem 38.5: the reduced middle-variable objective is convex on `ℝ^n`.
This is the Section 29/Theorem 5.7 packaging of the three-variable objective
`(x, u, y) ↦ ⟨y, y*⟩ - ⟨u, u*⟩ + F(u, x) + G(x, y)` after partial infimum over `(u, y)`. -/
lemma helperForTheorem_38_5_middleReducedObjective_convexOn
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (helperForTheorem_38_5_middleReducedObjective F G yStar uStar) := by
  let projTailMap :
      (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin (m + p) → ℝ) :=
    projLamLinearMap (n := n) (m := m + p)
  let projXMap :
      (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    projXLinearMap (n := n) (m := m + p)
  let projUMap :
      (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    (projXLinearMap (n := m) (m := p)).comp projTailMap
  let projYMap :
      (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin p → ℝ) :=
    (projLamLinearMap (n := m) (m := p)).comp projTailMap
  let packedFMap :
      (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
    { toFun := fun w => Fin.append (projUMap w) (projXMap w)
      map_add' := by
        intro w₁ w₂
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projUMap, projTailMap, projXMap, Fin.append_left, Pi.add_apply]
        | right i =>
            simp [projUMap, projTailMap, projXMap, Fin.append_right, Pi.add_apply]
      map_smul' := by
        intro a w
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projUMap, projTailMap, projXMap, Fin.append_left, Pi.smul_apply]
        | right i =>
            simp [projUMap, projTailMap, projXMap, Fin.append_right, Pi.smul_apply] }
  let packedGMap :
      (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin (n + p) → ℝ) :=
    { toFun := fun w => Fin.append (projXMap w) (projYMap w)
      map_add' := by
        intro w₁ w₂
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projYMap, projTailMap, projXMap, Fin.append_left, Pi.add_apply]
        | right i =>
            simp [projYMap, projTailMap, projXMap, Fin.append_right, Pi.add_apply]
      map_smul' := by
        intro a w
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projYMap, projTailMap, projXMap, Fin.append_left, Pi.smul_apply]
        | right i =>
            simp [projYMap, projTailMap, projXMap, Fin.append_right, Pi.smul_apply] }
  let leftObjective : (Fin (n + (m + p)) → ℝ) → EReal :=
    fun w =>
      ((((-uStar) (projUMap w) : ℝ) : EReal)) +
        bifunctionGraphFunction F.toFun (packedFMap w)
  let rightObjective : (Fin (n + (m + p)) → ℝ) → EReal :=
    fun w =>
      ((yStar (projYMap w) : ℝ) : EReal) +
        bifunctionGraphFunction G.toFun (packedGMap w)
  let objective : (Fin (n + (m + p)) → ℝ) → EReal :=
    fun w => rightObjective w + leftObjective w
  have hProjY_surj : Function.Surjective projYMap := by
    intro y
    refine ⟨Fin.append (0 : Fin n → ℝ) (Fin.append (0 : Fin m → ℝ) y), ?_⟩
    ext i
    simp [projYMap, projTailMap, projLamLinearMap, Fin.append_right]
  have hProjU_surj : Function.Surjective projUMap := by
    intro u
    refine ⟨Fin.append (0 : Fin n → ℝ) (Fin.append u (0 : Fin p → ℝ)), ?_⟩
    ext i
    simpa [projUMap, projTailMap, projLamLinearMap, projXLinearMap,
      Fin.append_left, Fin.append_right]
  have hPackedF_surj : Function.Surjective packedFMap := by
    intro z
    refine ⟨Fin.append (fun i : Fin n => z (Fin.natAdd m i))
      (Fin.append (fun i : Fin m => z (Fin.castAdd n i)) (0 : Fin p → ℝ)), ?_⟩
    ext i
    cases i using Fin.addCases with
    | left i =>
        simpa [packedFMap, projUMap, projTailMap, projLamLinearMap, projXLinearMap,
          Fin.append_left, Fin.append_right]
    | right i =>
        simpa [packedFMap, projXMap, projXLinearMap, Fin.append_left] using
          (Fin.append_right
            (u := (fun j : Fin n => z (Fin.natAdd m j)))
            (v := (0 : Fin p → ℝ))
            (i := i))
  have hPackedG_surj : Function.Surjective packedGMap := by
    intro z
    refine ⟨Fin.append (fun i : Fin n => z (Fin.castAdd p i))
      (Fin.append (0 : Fin m → ℝ) (fun j : Fin p => z (Fin.natAdd n j))), ?_⟩
    ext i
    cases i using Fin.addCases with
    | left i =>
        simpa [packedGMap, projXMap, projXLinearMap, Fin.append_left, Fin.append_right]
          using (Fin.append_left
            (u := (fun j : Fin n => z (Fin.castAdd p j)))
            (v := (fun j : Fin p => z (Fin.natAdd n j)))
            (i := i))
    | right i =>
        simpa [packedGMap, projYMap, projTailMap, projLamLinearMap, projXLinearMap,
          Fin.append_left, Fin.append_right] using
          (Fin.append_right
            (u := (0 : Fin m → ℝ))
            (v := (fun j : Fin p => z (Fin.natAdd n j)))
            (i := i))
  have hLinearYProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ))
        (fun w : Fin (n + (m + p)) → ℝ => ((yStar (projYMap w) : ℝ) : EReal)) := by
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := projYMap) hProjY_surj
      (helperForTheorem_38_5_dualLinearFunctional_properConvexFunctionOn_univ yStar)
  have hLinearUProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ))
        (fun w : Fin (n + (m + p)) → ℝ => ((((-uStar) (projUMap w) : ℝ) : EReal))) := by
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := projUMap) hProjU_surj
      (helperForTheorem_38_5_dualLinearFunctional_properConvexFunctionOn_univ (-uStar))
  have hFGraphProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (bifunctionGraphFunction F.toFun) := by
    exact
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := bifunctionGraphFunction F.toFun) hF_properConvex.2
  have hGGraphProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + p) → ℝ))
        (bifunctionGraphFunction G.toFun) := by
    exact
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := bifunctionGraphFunction G.toFun) hG_properConvex.2
  have hFProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ))
        (fun w : Fin (n + (m + p)) → ℝ => bifunctionGraphFunction F.toFun (packedFMap w)) := by
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := packedFMap) hPackedF_surj hFGraphProper
  have hGProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ))
        (fun w : Fin (n + (m + p)) → ℝ => bifunctionGraphFunction G.toFun (packedGMap w)) := by
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := packedGMap) hPackedG_surj hGGraphProper
  have hLeftProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ)) leftObjective := by
    rw [properConvexFunctionOn_iff_effectiveDomain_nonempty_finite]
    refine ⟨?_, ?_, ?_⟩
    · simpa [leftObjective] using convexFunctionOn_add_of_proper hLinearUProper hFProper
    · have hFProper' :=
          (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
            (S := (Set.univ : Set (Fin (n + (m + p)) → ℝ)))
            (f := fun w : Fin (n + (m + p)) → ℝ => bifunctionGraphFunction F.toFun (packedFMap w))).1 hFProper
      rcases hFProper'.2.1 with ⟨w, hw⟩
      refine ⟨w, ?_⟩
      rw [effectiveDomain_eq]
      refine ⟨by simp, ?_⟩
      have hwFinite := hFProper'.2.2 w hw
      have hCoeff_ne_top : ((((-uStar) (projUMap w) : ℝ) : EReal)) ≠ (⊤ : EReal) := by simp
      have hGraph_lt_top : bifunctionGraphFunction F.toFun (packedFMap w) < (⊤ : EReal) :=
        lt_top_iff_ne_top.mpr hwFinite.2
      exact EReal.add_lt_top hCoeff_ne_top (ne_of_lt hGraph_lt_top)
    · intro w hw
      rw [effectiveDomain_eq] at hw
      have hCoeff_ne_bot : ((((-uStar) (projUMap w) : ℝ) : EReal)) ≠ (⊥ : EReal) := by simp
      have hGraph_ne_bot : bifunctionGraphFunction F.toFun (packedFMap w) ≠ (⊥ : EReal) :=
        hFProper.2.2 w (by simp)
      have hSum_ne_top : leftObjective w ≠ (⊤ : EReal) :=
        (lt_top_iff_ne_top.mp hw.2)
      exact ⟨add_ne_bot_of_notbot hCoeff_ne_bot hGraph_ne_bot, hSum_ne_top⟩
  have hRightProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ)) rightObjective := by
    rw [properConvexFunctionOn_iff_effectiveDomain_nonempty_finite]
    refine ⟨?_, ?_, ?_⟩
    · simpa [rightObjective] using convexFunctionOn_add_of_proper hLinearYProper hGProper
    · have hGProper' :=
          (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
            (S := (Set.univ : Set (Fin (n + (m + p)) → ℝ)))
            (f := fun w : Fin (n + (m + p)) → ℝ => bifunctionGraphFunction G.toFun (packedGMap w))).1 hGProper
      rcases hGProper'.2.1 with ⟨w, hw⟩
      refine ⟨w, ?_⟩
      rw [effectiveDomain_eq]
      refine ⟨by simp, ?_⟩
      have hwFinite := hGProper'.2.2 w hw
      have hCoeff_ne_top : (((yStar (projYMap w) : ℝ) : EReal)) ≠ (⊤ : EReal) := by simp
      have hGraph_lt_top : bifunctionGraphFunction G.toFun (packedGMap w) < (⊤ : EReal) :=
        lt_top_iff_ne_top.mpr hwFinite.2
      exact EReal.add_lt_top hCoeff_ne_top (ne_of_lt hGraph_lt_top)
    · intro w hw
      rw [effectiveDomain_eq] at hw
      have hCoeff_ne_bot : (((yStar (projYMap w) : ℝ) : EReal)) ≠ (⊥ : EReal) := by simp
      have hGraph_ne_bot : bifunctionGraphFunction G.toFun (packedGMap w) ≠ (⊥ : EReal) :=
        hGProper.2.2 w (by simp)
      have hSum_ne_top : rightObjective w ≠ (⊤ : EReal) :=
        (lt_top_iff_ne_top.mp hw.2)
      exact ⟨add_ne_bot_of_notbot hCoeff_ne_bot hGraph_ne_bot, hSum_ne_top⟩
  have hObjectiveConv :
      ConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ)) objective := by
    exact convexFunctionOn_add_of_proper hRightProper hLeftProper
  have hFiberConv :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x : Fin n → ℝ =>
          sInf {r : EReal |
            ∃ w : Fin (n + (m + p)) → ℝ, projXMap w = x ∧ r = objective w}) := by
    simpa using
      (convexFunctionOn_inf_fiber_linearMap (A := projXMap) (h := objective) hObjectiveConv)
  have hEq :
      (fun x : Fin n → ℝ =>
        sInf {r : EReal |
          ∃ w : Fin (n + (m + p)) → ℝ, projXMap w = x ∧ r = objective w}) =
        helperForTheorem_38_5_middleReducedObjective F G yStar uStar := by
    let H : (Fin n → ℝ) → (Fin (m + p) → ℝ) → EReal :=
      fun x q =>
        ((yStar (projLamLinearMap (n := m) (m := p) q) : ℝ) : EReal) +
          (-((uStar (projXLinearMap (n := m) (m := p) q) : ℝ) : EReal)) +
            (F.toFun (projXLinearMap (n := m) (m := p) q) x +
              G.toFun x (projLamLinearMap (n := m) (m := p) q))
    have hproj : projectionLinearMap (Nat.le_add_right n (m + p)) = projXMap := by
      ext w i
      rfl
    have hobj : bifunctionGraphFunction H = objective := by
      funext w
      have hU :
          projXLinearMap (n := m) (m := p) (projLamLinearMap (n := n) (m := m + p) w) =
            projUMap w := by
        rfl
      have hY :
          projLamLinearMap (n := m) (m := p) (projLamLinearMap (n := n) (m := m + p) w) =
            projYMap w := by
        rfl
      have hFGraph :
          bifunctionGraphFunction F.toFun (packedFMap w) =
            F.toFun (projUMap w) (projXMap w) := by
        simp [packedFMap, bifunctionGraphFunction]
      have hGGraph :
          bifunctionGraphFunction G.toFun (packedGMap w) =
            G.toFun (projXMap w) (projYMap w) := by
        simp [packedGMap, bifunctionGraphFunction]
      calc
        bifunctionGraphFunction H w
            = ((yStar (projYMap w) : ℝ) : EReal) + (-((uStar (projUMap w) : ℝ) : EReal)) +
                (F.toFun (projUMap w) (projXMap w) + G.toFun (projXMap w) (projYMap w)) := by
                  change
                    ((yStar (projLamLinearMap (n := m) (m := p) (projLamLinearMap (n := n) (m := m + p) w)) : ℝ) : EReal) +
                      (-((uStar (projXLinearMap (n := m) (m := p) (projLamLinearMap (n := n) (m := m + p) w)) : ℝ) : EReal)) +
                        (F.toFun (projXLinearMap (n := m) (m := p) (projLamLinearMap (n := n) (m := m + p) w))
                          (projXLinearMap (n := n) (m := m + p) w) +
                          G.toFun (projXLinearMap (n := n) (m := m + p) w)
                            (projLamLinearMap (n := m) (m := p) (projLamLinearMap (n := n) (m := m + p) w))) = _
                  rw [hU, hY]
        _ = objective w := by
              have hReassoc :
                  ((yStar (projYMap w) : ℝ) : EReal) + (-((uStar (projUMap w) : ℝ) : EReal)) +
                    (F.toFun (projUMap w) (projXMap w) + G.toFun (projXMap w) (projYMap w)) =
                  (((yStar (projYMap w) : ℝ) : EReal) + G.toFun (projXMap w) (projYMap w)) +
                    (((-((uStar (projUMap w) : ℝ) : EReal))) + F.toFun (projUMap w) (projXMap w)) := by
                let a : EReal := ((yStar (projYMap w) : ℝ) : EReal)
                let b : EReal := -((uStar (projUMap w) : ℝ) : EReal)
                let c : EReal := F.toFun (projUMap w) (projXMap w)
                let d : EReal := G.toFun (projXMap w) (projYMap w)
                have hTail : b + (c + d) = d + (b + c) := by
                  rw [← add_assoc, add_comm (b + c) d]
                simpa [a, b, c, d, add_assoc] using congrArg (fun t : EReal => a + t) hTail
              simpa [objective, rightObjective, leftObjective, hFGraph, hGGraph] using hReassoc
    funext x
    calc
      sInf {r : EReal | ∃ w : Fin (n + (m + p)) → ℝ, projXMap w = x ∧ r = objective w}
          = sInf {r : EReal | ∃ w : Fin (n + (m + p)) → ℝ,
              projectionLinearMap (Nat.le_add_right n (m + p)) w = x ∧
                r = bifunctionGraphFunction H w} := by
            congr
            ext r
            constructor
            · rintro ⟨w, hw, hr⟩
              exact ⟨w, by simpa [hproj] using hw, by simpa [hobj] using hr⟩
            · rintro ⟨w, hw, hr⟩
              exact ⟨w, by simpa [hproj] using hw, by simpa [hobj] using hr⟩
      _ = sInf (Set.range (fun q : Fin (m + p) → ℝ => H x q)) := by
            rw [helperForTheorem_6_30_15_projectionFiber_eq_sliceRange H x]
      _ = (⨅ q : Fin (m + p) → ℝ, H x q) := by rw [sInf_range]
      _ = (⨅ u : Fin m → ℝ, ⨅ y : Fin p → ℝ, H x (Fin.append u y)) := by
            refine le_antisymm ?_ ?_
            · refine le_iInf ?_
              intro u
              refine le_iInf ?_
              intro y
              exact iInf_le (fun q : Fin (m + p) → ℝ => H x q) (Fin.append u y)
            · refine le_iInf ?_
              intro q
              exact le_trans
                (iInf_le (fun u : Fin m → ℝ => ⨅ y : Fin p → ℝ, H x (Fin.append u y))
                  (projXLinearMap (n := m) (m := p) q))
                (by
                  refine le_trans
                    (iInf_le (fun y : Fin p → ℝ =>
                      H x (Fin.append (projXLinearMap (n := m) (m := p) q) y))
                      (projLamLinearMap (n := m) (m := p) q)) ?_
                  simp [H, projXLinearMap, projLamLinearMap])
      _ = helperForTheorem_38_5_middleReducedObjective F G yStar uStar x := by
            rw [helperForTheorem_38_5_middleReducedObjective]
            refine iInf_congr ?_
            intro u
            refine iInf_congr ?_
            intro y
            change
              ((yStar (projLamLinearMap (n := m) (m := p) (Fin.append u y)) : ℝ) : EReal) +
                (-((uStar (projXLinearMap (n := m) (m := p) (Fin.append u y)) : ℝ) : EReal)) +
                  (F.toFun (projXLinearMap (n := m) (m := p) (Fin.append u y)) x +
                    G.toFun x (projLamLinearMap (n := m) (m := p) (Fin.append u y))) =
              ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) + (F.toFun u x + G.toFun x y)
            simp [projXLinearMap, projLamLinearMap]
  simpa [hEq] using hFiberConv

/-- Helper for Theorem 38.5: the packed version of the corrected second-shift reduced objective,
with the first `n` coordinates interpreted as `z` and the second `n` coordinates as `x`. -/
noncomputable def helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) : (Fin (n + n) → ℝ) → EReal :=
  fun zx =>
    helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar
      (projXLinearMap (n := n) (m := n) zx)
      (projLamLinearMap (n := n) (m := n) zx)

/-- Helper for Theorem 38.5: unpacking the packed second-shift reduced objective at
`Fin.append z x` recovers the original bifunction value. -/
lemma helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective_append
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (z x : Fin n → ℝ) :
    helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective F G yStar uStar
        (Fin.append z x) =
      helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar z x := by
  rw [helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective,
    helperForTheorem_38_5_secondShiftMiddleReducedObjective]
  simp [projXLinearMap, Fin.append_left]
  refine iInf_congr ?_
  intro u
  refine iInf_congr ?_
  intro y
  have hxEq : (fun i : Fin n => Fin.append z x (i.addNat n)) = x := by
    funext i
    simpa using (Fin.append_right (u := z) (v := x) (i := i))
  have hzxEq : (fun i : Fin n => z i) + (fun i : Fin n => Fin.append z x (i.addNat n)) = z + x := by
    ext i
    simp [hxEq]
  simpa [projLamLinearMap, hxEq, hzxEq, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 38.5: the remaining convexity work for the corrected perturbation is
equivalent to convexity of its packed product-space representative. -/
lemma helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective_convexOn
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    ConvexFunctionOn (Set.univ : Set (Fin (n + n) → ℝ))
      (helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective F G yStar uStar) := by
  let xProj : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    projLamLinearMap (n := n) (m := n)
  let shiftZX : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun zx i => zx (Fin.castAdd n i) + zx (Fin.natAdd n i)
      map_add' := by
        intro z1 z2
        ext i
        simp [Pi.add_apply, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a z
        ext i
        simp [Pi.smul_apply, mul_add] }
  let Fpacked : FiberwiseProperConvexBifunction m (n + n) :=
    { toFun := fun u zx => F.toFun u (xProj zx)
      proper := by
        constructor
        · intro u zx
          exact F.proper.1 u (xProj zx)
        · rcases F.proper.2 with ⟨u, x, hx⟩
          refine ⟨u, Fin.append (0 : Fin n → ℝ) x, ?_⟩
          have hxProj : xProj (Fin.append (0 : Fin n → ℝ) x) = x := by
            ext i
            simpa [xProj, projLamLinearMap] using
              (Fin.append_right (u := (0 : Fin n → ℝ)) (v := x) (i := i))
          simpa [hxProj] using hx
      convex := by
        intro u
        simpa [xProj] using
          helperForTheorem_38_4_isERealConvex_precomp_linearMap xProj (F.convex u) }
  let Gpacked : FiberwiseProperConvexBifunction (n + n) p :=
    { toFun := fun zx y => G.toFun (shiftZX zx) y
      proper := by
        constructor
        · intro zx y
          exact G.proper.1 (shiftZX zx) y
        · rcases G.proper.2 with ⟨x, y, hy⟩
          refine ⟨Fin.append (0 : Fin n → ℝ) x, y, ?_⟩
          have hShift : shiftZX (Fin.append (0 : Fin n → ℝ) x) = x := by
            ext i
            simp [shiftZX, Fin.append_left]
            simpa using (Fin.append_right (u := (0 : Fin n → ℝ)) (v := x) (i := i))
          simpa [hShift] using hy
      convex := by
        intro zx
        exact G.convex (shiftZX zx) }
  have hFpacked_properConvex : ProperConvexBifunction Fpacked.toFun := by
    let graphMap : (Fin (m + (n + n)) → ℝ) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
      { toFun := fun w =>
          Fin.append
            (projXLinearMap (n := m) (m := n + n) w)
            (xProj (projLamLinearMap (n := m) (m := n + n) w))
        map_add' := by
          intro w₁ w₂
          ext i
          cases i using Fin.addCases with
          | left i =>
              simp [xProj, projXLinearMap, projLamLinearMap, Fin.append_left, Pi.add_apply]
          | right i =>
              simp [xProj, projXLinearMap, projLamLinearMap, Fin.append_right, Pi.add_apply]
        map_smul' := by
          intro a w
          ext i
          cases i using Fin.addCases with
          | left i =>
              simp [xProj, projXLinearMap, projLamLinearMap, Fin.append_left, Pi.smul_apply]
          | right i =>
              simp [xProj, projXLinearMap, projLamLinearMap, Fin.append_right, Pi.smul_apply] }
    have hGraphMap_surj : Function.Surjective graphMap := by
      intro z
      refine ⟨Fin.append (projXLinearMap (n := m) (m := n) z)
        (Fin.append (0 : Fin n → ℝ) (projLamLinearMap (n := m) (m := n) z)), ?_⟩
      ext i
      cases i using Fin.addCases with
      | left i =>
          simp [graphMap, xProj, projXLinearMap, projLamLinearMap, Fin.append_left]
      | right i =>
          simpa [graphMap, xProj, projXLinearMap, projLamLinearMap, Fin.append_left] using
            (Fin.append_right
              (u := (0 : Fin n → ℝ))
              (v := (fun j : Fin n => z (Fin.natAdd m j)))
              (i := i))
    have hBase :
        ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
          (bifunctionGraphFunction F.toFun) :=
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := bifunctionGraphFunction F.toFun) hF_properConvex.2
    have hGraphProperOn :
        ProperConvexFunctionOn (Set.univ : Set (Fin (m + (n + n)) → ℝ))
          (bifunctionGraphFunction Fpacked.toFun) := by
      simpa [graphMap, xProj, bifunctionGraphFunction] using
        properConvexFunctionOn_precomp_linearMap_surjective (A := graphMap) hGraphMap_surj hBase
    refine ⟨?_, helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ _ hGraphProperOn⟩
    simpa [ConvexBifunction, ConvexFunction] using hGraphProperOn.1
  have hGpacked_properConvex : ProperConvexBifunction Gpacked.toFun := by
    let graphMap : (Fin ((n + n) + p) → ℝ) →ₗ[ℝ] (Fin (n + p) → ℝ) :=
      { toFun := fun w =>
          Fin.append
            (shiftZX (projXLinearMap (n := n + n) (m := p) w))
            (projLamLinearMap (n := n + n) (m := p) w)
        map_add' := by
          intro w₁ w₂
          ext i
          cases i using Fin.addCases with
          | left i =>
              simp [shiftZX, projXLinearMap, projLamLinearMap, Fin.append_left, Pi.add_apply,
                add_assoc, add_left_comm, add_comm]
          | right i =>
              simp [shiftZX, projXLinearMap, projLamLinearMap, Fin.append_right, Pi.add_apply]
        map_smul' := by
          intro a w
          ext i
          cases i using Fin.addCases with
          | left i =>
              simp [shiftZX, projXLinearMap, projLamLinearMap, Fin.append_left, Pi.smul_apply,
                mul_add]
          | right i =>
              simp [shiftZX, projXLinearMap, projLamLinearMap, Fin.append_right, Pi.smul_apply] }
    have hGraphMap_surj : Function.Surjective graphMap := by
      intro z
      refine ⟨Fin.append
        (Fin.append (0 : Fin n → ℝ) (projXLinearMap (n := n) (m := p) z))
        (projLamLinearMap (n := n) (m := p) z), ?_⟩
      ext i
      cases i using Fin.addCases with
      | left i =>
          simpa [graphMap, shiftZX, projXLinearMap, projLamLinearMap, Fin.append_left] using
            (Fin.append_right
              (u := (0 : Fin n → ℝ))
              (v := (fun j : Fin n => z (Fin.castAdd p j)))
              (i := i))
      | right i =>
          simp [graphMap, shiftZX, projXLinearMap, projLamLinearMap, Fin.append_left,
            Fin.append_right]
    have hBase :
        ProperConvexFunctionOn (Set.univ : Set (Fin (n + p) → ℝ))
          (bifunctionGraphFunction G.toFun) :=
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := bifunctionGraphFunction G.toFun) hG_properConvex.2
    have hGraphProperOn :
        ProperConvexFunctionOn (Set.univ : Set (Fin ((n + n) + p) → ℝ))
          (bifunctionGraphFunction Gpacked.toFun) := by
      change ProperConvexFunctionOn Set.univ
        (fun x => G.toFun (shiftZX (projXLinearMap (n := n + n) (m := p) x))
          (projLamLinearMap (n := n + n) (m := p) x))
      simpa [graphMap, bifunctionGraphFunction] using
        properConvexFunctionOn_precomp_linearMap_surjective (A := graphMap) hGraphMap_surj hBase
    refine ⟨?_, helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ _ hGraphProperOn⟩
    simpa [ConvexBifunction, ConvexFunction] using hGraphProperOn.1
  have hEqPacked :
      helperForTheorem_38_5_middleReducedObjective Fpacked Gpacked yStar uStar =
        helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective F G yStar uStar := by
    funext zx
    rw [helperForTheorem_38_5_middleReducedObjective,
      helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective,
      helperForTheorem_38_5_secondShiftMiddleReducedObjective]
    refine iInf_congr ?_
    intro u
    refine iInf_congr ?_
    intro y
    have hShiftEq :
        shiftZX zx =
          projLamLinearMap (n := n) (m := n) zx + projXLinearMap (n := n) (m := n) zx := by
      ext i
      simp [shiftZX, projLamLinearMap, projXLinearMap, Pi.add_apply, add_comm]
    simp [Fpacked, Gpacked, xProj, projXLinearMap, projLamLinearMap, hShiftEq, add_comm,
      add_left_comm, add_assoc]
  simpa [← hEqPacked] using
    (helperForTheorem_38_5_middleReducedObjective_convexOn
      (F := Fpacked) (G := Gpacked) (yStar := yStar) (uStar := uStar)
      hFpacked_properConvex hGpacked_properConvex)

/-- Helper for Theorem 38.5: after the preceding rewrites, the right-hand side `F^* G^*` is the
Fenchel dual supremum of the textbook middle-function pair. -/
lemma helperForTheorem_38_5_composeSupGeneric_eq_fenchelDualSupremum
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        yStar uStar =
      fenchelDualSupremum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
  rw [fenchelDualSupremum]
  calc
    bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        yStar uStar =
      ⨆ xStar : Module.Dual ℝ (Fin n → ℝ),
        fenchelDualObjective
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          (-((dotProductEquiv ℝ (Fin n)).symm xStar)) := by
            exact helperForTheorem_38_5_composeSupGeneric_eq_iSup_fenchelDualObjective
              (F := F) (G := G) (yStar := yStar) (uStar := uStar)
    _ = ⨆ xStar : Fin n → ℝ,
          fenchelDualObjective
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
            xStar := by
          refine le_antisymm ?_ ?_
          · refine iSup_le ?_
            intro xStar
            exact le_iSup
              (fun z : Fin n → ℝ =>
                fenchelDualObjective
                  (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
                  (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
                  z)
              (-((dotProductEquiv ℝ (Fin n)).symm xStar))
          · refine iSup_le ?_
            intro xStar
            simpa using (le_iSup
              (fun z : Module.Dual ℝ (Fin n → ℝ) =>
                fenchelDualObjective
                  (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
                  (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
                  (-((dotProductEquiv ℝ (Fin n)).symm z)))
              (dotProductEquiv ℝ (Fin n) (-xStar)))

/-- Helper for Theorem 38.5: the graph function of `bifunctionCompose G F` is the fiber infimum
of the triple objective `(x, u, y) ↦ F u x + G x y` over the eliminated middle variable `x`. -/
lemma helperForTheorem_38_5_graphFunction_compose_eq_infFiber
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p) :
    (fun z : Fin (m + p) → ℝ =>
        sInf {r : EReal |
          ∃ w : Fin (n + (m + p)) → ℝ,
            projLamLinearMap (n := n) (m := m + p) w = z ∧
              r = helperForTheorem_38_5_packedTripleObjective F G w}) =
      bifunctionGraphFunction (bifunctionCompose G F) := by
  funext z
  have hset :
      {r : EReal |
          ∃ w : Fin (n + (m + p)) → ℝ,
            projLamLinearMap (n := n) (m := m + p) w = z ∧
              r = helperForTheorem_38_5_packedTripleObjective F G w} =
        Set.range (fun x : Fin n → ℝ =>
          F.toFun (projXLinearMap (n := m) (m := p) z) x +
            G.toFun x (projLamLinearMap (n := m) (m := p) z)) := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨projXLinearMap (n := n) (m := m + p) w, ?_⟩
      simp [helperForTheorem_38_5_packedTripleObjective,
        helperForTheorem_38_5_threeVariableObjective, hw]
    · rintro ⟨x, rfl⟩
      refine ⟨Fin.append x z, ?_, ?_⟩
      · ext i
        simp [projLamLinearMap]
      · simp [helperForTheorem_38_5_packedTripleObjective,
          helperForTheorem_38_5_threeVariableObjective, projXLinearMap, projLamLinearMap]
  rw [hset, sInf_range, bifunctionGraphFunction, bifunctionCompose]
  simp [projXLinearMap, projLamLinearMap]

/-- Helper for Theorem 38.5: product-space proper convexity of the graph functions of `F` and `G`
implies convexity of the graph function of the composition `bifunctionCompose G F`. -/
lemma helperForTheorem_38_5_compose_convexBifunction
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    ConvexBifunction (bifunctionCompose G F) := by
  let tripleObjective : (Fin (n + (m + p)) → ℝ) → EReal :=
    helperForTheorem_38_5_packedTripleObjective F G
  let packedFMap : (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
    { toFun := fun w =>
        Fin.append
          (projXLinearMap (n := m) (m := p)
            (projLamLinearMap (n := n) (m := m + p) w))
          (projXLinearMap (n := n) (m := m + p) w)
      map_add' := by
        intro w₁ w₂
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_left, Pi.add_apply]
        | right i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_right, Pi.add_apply]
      map_smul' := by
        intro a w
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_left, Pi.smul_apply]
        | right i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_right, Pi.smul_apply] }
  let packedGMap : (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin (n + p) → ℝ) :=
    { toFun := fun w =>
        Fin.append
          (projXLinearMap (n := n) (m := m + p) w)
          (projLamLinearMap (n := m) (m := p)
            (projLamLinearMap (n := n) (m := m + p) w))
      map_add' := by
        intro w₁ w₂
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_left, Pi.add_apply]
        | right i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_right, Pi.add_apply]
      map_smul' := by
        intro a w
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_left, Pi.smul_apply]
        | right i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_right, Pi.smul_apply] }
  have hPackedF_surj : Function.Surjective packedFMap := by
    intro z
    refine ⟨Fin.append (fun j : Fin n => z (Fin.natAdd m j))
      (Fin.append (fun i : Fin m => z (Fin.castAdd n i)) (0 : Fin p → ℝ)), ?_⟩
    ext i
    cases i using Fin.addCases with
    | left i =>
        simp [packedFMap, projLamLinearMap, projXLinearMap, Fin.append_left]
    | right i =>
        simp [packedFMap, projLamLinearMap, projXLinearMap, Fin.append_right]
  have hPackedG_surj : Function.Surjective packedGMap := by
    intro z
    refine ⟨Fin.append (fun i : Fin n => z (Fin.castAdd p i))
      (Fin.append (0 : Fin m → ℝ) (fun j : Fin p => z (Fin.natAdd n j))), ?_⟩
    ext i
    cases i using Fin.addCases with
    | left i =>
        simp [packedGMap, projLamLinearMap, projXLinearMap, Fin.append_left]
    | right i =>
        simp [packedGMap, projLamLinearMap, projXLinearMap, Fin.append_right]
  have hFGraphProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (bifunctionGraphFunction F.toFun) := by
    exact
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := bifunctionGraphFunction F.toFun) hF_properConvex.2
  have hGGraphProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + p) → ℝ))
        (bifunctionGraphFunction G.toFun) := by
    exact
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := bifunctionGraphFunction G.toFun) hG_properConvex.2
  have hLiftedFProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ))
        (fun w => bifunctionGraphFunction F.toFun (packedFMap w)) := by
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := packedFMap) hPackedF_surj hFGraphProper
  have hLiftedGProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ))
        (fun w => bifunctionGraphFunction G.toFun (packedGMap w)) := by
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := packedGMap) hPackedG_surj hGGraphProper
  have hTripleConv :
      ConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ)) tripleObjective := by
    simpa [tripleObjective, packedFMap, packedGMap, bifunctionGraphFunction] using
      (convexFunctionOn_add_of_proper
        (n := n + (m + p)) hLiftedFProper hLiftedGProper)
  have hFiberConv :
      ConvexFunctionOn (Set.univ : Set (Fin (m + p) → ℝ))
        (fun z : Fin (m + p) → ℝ =>
          sInf {r : EReal |
            ∃ w : Fin (n + (m + p)) → ℝ,
              projLamLinearMap (n := n) (m := m + p) w = z ∧ r = tripleObjective w}) := by
    simpa using
      (convexFunctionOn_inf_fiber_linearMap (A := projLamLinearMap (n := n) (m := m + p))
        (h := tripleObjective) hTripleConv)
  have hGraphEq :
      (fun z : Fin (m + p) → ℝ =>
        sInf {r : EReal |
          ∃ w : Fin (n + (m + p)) → ℝ,
            projLamLinearMap (n := n) (m := m + p) w = z ∧ r = tripleObjective w}) =
        bifunctionGraphFunction (bifunctionCompose G F) := by
    simpa [tripleObjective] using helperForTheorem_38_5_graphFunction_compose_eq_infFiber F G
  have hGraphConv :
      ConvexFunctionOn (Set.univ : Set (Fin (m + p) → ℝ))
        (bifunctionGraphFunction (bifunctionCompose G F)) := by
    simpa [hGraphEq] using hFiberConv
  simpa [ConvexBifunction, ConvexFunction] using hGraphConv

/-- Helper for Theorem 38.5: the explicit actual-hypotheses counterexample still satisfies the
weaker Chapter 30 graph-convex conclusion delivered by the composition argument via Theorem 5.7. -/
lemma helperForTheorem_38_5_actualCounterexample_compose_convexBifunction :
    ConvexBifunction
      (bifunctionCompose helperForTheorem_38_5_actualCounterexampleSecondBifunction
        helperForTheorem_38_5_actualCounterexampleFirstBifunction) := by
  -- Reuse the dependency-closed graph-convex composition lemma on the explicit counterexample.
  exact
    helperForTheorem_38_5_compose_convexBifunction
      helperForTheorem_38_5_actualCounterexampleFirstBifunction
      helperForTheorem_38_5_actualCounterexampleSecondBifunction
      helperForTheorem_38_5_actualCounterexampleFirst_properConvex
      helperForTheorem_38_5_actualCounterexampleSecond_properConvex

/-- Helper for Theorem 38.5: the explicit actual-hypotheses counterexample separates the weaker
graph-convex predicate from the stronger Chapter 29 predicate `IsConvexBifunction`. -/
lemma helperForTheorem_38_5_actualCounterexample_separates_convexPredicates :
    ConvexBifunction
        (bifunctionCompose helperForTheorem_38_5_actualCounterexampleSecondBifunction
          helperForTheorem_38_5_actualCounterexampleFirstBifunction) ∧
      ¬ IsConvexBifunction
        (bifunctionCompose helperForTheorem_38_5_actualCounterexampleSecondBifunction
          helperForTheorem_38_5_actualCounterexampleFirstBifunction) := by
  constructor
  · -- The Chapter 30 graph-convex route remains valid on the explicit counterexample.
    exact helperForTheorem_38_5_actualCounterexample_compose_convexBifunction
  · -- The midpoint calculation already witnesses failure of the stronger Chapter 29 predicate.
    exact helperForTheorem_38_5_actualCounterexample_compose_not_IsConvexBifunction

/-- Helper for Theorem 38.5: no theorem-local bridge can upgrade graph-convexity of compositions
to `IsConvexBifunction` under the current hypotheses, because the explicit actual-hypotheses
counterexample already satisfies the properness assumptions while refuting the stronger conclusion.
-/
lemma helperForTheorem_38_5_noGenericBridgeFromConvexBifunctionToIsConvexBifunction :
    ¬ ∀ {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
        (G : FiberwiseProperConvexBifunction n p),
      ProperConvexBifunction F.toFun →
      ProperConvexBifunction G.toFun →
      ConvexBifunction (bifunctionCompose G F) →
      IsConvexBifunction (bifunctionCompose G F) := by
  intro hBridge
  rcases helperForTheorem_38_5_actualCounterexample_separates_convexPredicates with
    ⟨hConvex, hNotIsConvex⟩
  -- Specialize the hypothetical bridge to the explicit actual-hypotheses counterexample.
  have hIsConvex :
      IsConvexBifunction
        (bifunctionCompose helperForTheorem_38_5_actualCounterexampleSecondBifunction
          helperForTheorem_38_5_actualCounterexampleFirstBifunction) :=
    hBridge helperForTheorem_38_5_actualCounterexampleFirstBifunction
      helperForTheorem_38_5_actualCounterexampleSecondBifunction
      helperForTheorem_38_5_actualCounterexampleFirst_properConvex
      helperForTheorem_38_5_actualCounterexampleSecond_properConvex
      hConvex
  -- This contradicts the already-proved failure of `IsConvexBifunction` on the same example.
  exact hNotIsConvex hIsConvex

/-- Helper for Theorem 38.5: the dual functional `u ↦ -u₁` used to show that the textbook middle
function need not be proper, even under the theorem's current bifunction hypotheses. -/
def helperForTheorem_38_5_actualCounterexampleNegativeFirstCoordinateDual :
    Module.Dual ℝ (Fin 1 → ℝ) where
  toFun := fun u => -(u 0)
  map_add' := by
    intro u v
    simp [add_comm]
  map_smul' := by
    intro a u
    simp

/-- Helper for Theorem 38.5: on the explicit actual-hypotheses counterexample, choosing the dual
functional `u ↦ -u₁` makes the textbook primal middle function identically `⊥`. -/
lemma helperForTheorem_38_5_actualCounterexample_textbookPrimalMiddle_eq_bot
    (x : Fin 1 → ℝ) :
    helperForTheorem_38_5_textbookPrimalMiddleFunction
        helperForTheorem_38_5_actualCounterexampleFirstBifunction
        helperForTheorem_38_5_actualCounterexampleNegativeFirstCoordinateDual x =
      ⊥ := by
  rw [helperForTheorem_38_5_textbookPrimalMiddleFunction, iInf_eq_bot]
  intro b hb
  rcases EReal.lt_iff_exists_rat_btwn.mp hb with ⟨q, -, hq⟩
  let u : Fin 1 → ℝ := fun _ => |(q : ℝ)| + 1
  have hu_pos : 0 < u 0 := by
    have habs : 0 ≤ |(q : ℝ)| := abs_nonneg (q : ℝ)
    dsimp [u]
    linarith
  have hq' : ((((q : ℚ) : ℝ) : EReal) < b) := by
    simpa using hq
  have hnegAbsLe : -|(q : ℝ)| ≤ (q : ℝ) := by
    exact neg_abs_le (q : ℝ)
  have hltReal : -( |(q : ℝ)| + 1) < (q : ℝ) := by
    linarith
  refine ⟨u, ?_⟩
  have hltEReal : (((-( |(q : ℝ)| + 1) : ℝ)) : EReal) < b := by
    exact lt_trans (by exact_mod_cast hltReal) hq'
  simpa [u, helperForTheorem_38_5_actualCounterexampleNegativeFirstCoordinateDual,
    helperForTheorem_38_5_actualCounterexampleFirstBifunction,
    helperForTheorem_38_5_actualCounterexampleFirstRaw, hu_pos] using hltEReal

/-- Helper for Theorem 38.5: therefore no generic argument can package all textbook primal middle
functions into `ProperConvexFunctionOn`; the current theorem hypotheses already admit an explicit
counterexample where the middle function is `⊥` everywhere. -/
lemma helperForTheorem_38_5_actualCounterexample_textbookPrimalMiddle_not_properConvexFunctionOn :
    ¬ ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
      (helperForTheorem_38_5_textbookPrimalMiddleFunction
        helperForTheorem_38_5_actualCounterexampleFirstBifunction
        helperForTheorem_38_5_actualCounterexampleNegativeFirstCoordinateDual) := by
  intro hProper
  have hNoBot :=
    hProper.2.2 helperForTheorem_38_5_zeroVec (by simp)
  exact hNoBot
    (helperForTheorem_38_5_actualCounterexample_textbookPrimalMiddle_eq_bot
      helperForTheorem_38_5_zeroVec)

/-- Helper for Theorem 38.5: there is no theorem-local bridge that upgrades the current bifunction
hypotheses to `ProperConvexFunctionOn` for every textbook primal middle function. The explicit
actual-hypotheses counterexample already violates that conclusion. -/
lemma helperForTheorem_38_5_noGenericPropernessPackageForTextbookPrimalMiddle :
    ¬ ∀ {m n : Nat} (F : FiberwiseProperConvexBifunction m n),
        ProperConvexBifunction F.toFun →
        ∀ uStar : Module.Dual ℝ (Fin m → ℝ),
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F uStar) := by
  intro hPackage
  have hProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction
          helperForTheorem_38_5_actualCounterexampleFirstBifunction
          helperForTheorem_38_5_actualCounterexampleNegativeFirstCoordinateDual) :=
    hPackage helperForTheorem_38_5_actualCounterexampleFirstBifunction
      helperForTheorem_38_5_actualCounterexampleFirst_properConvex
      helperForTheorem_38_5_actualCounterexampleNegativeFirstCoordinateDual
  exact
    helperForTheorem_38_5_actualCounterexample_textbookPrimalMiddle_not_properConvexFunctionOn
      hProper

/-- Helper for Theorem 38.5: the nonzero dual functional `y ↦ y₁` used to show that the textbook
dual middle function need not be proper concave under the theorem's current hypotheses. -/
def helperForTheorem_38_5_actualCounterexamplePositiveFirstCoordinateDual :
    Module.Dual ℝ (Fin 1 → ℝ) where
  toFun := fun y => y 0
  map_add' := by
    intro y z
    simp
  map_smul' := by
    intro a y
    simp

/-- Helper for Theorem 38.5: on the explicit actual-hypotheses counterexample, choosing the dual
functional `y ↦ y₁` makes the textbook dual middle function identically `⊤`. -/
lemma helperForTheorem_38_5_actualCounterexample_textbookDualMiddle_eq_top
    (x : Fin 1 → ℝ) :
    helperForTheorem_38_5_textbookDualMiddleFunction
        helperForTheorem_38_5_actualCounterexampleSecondBifunction
        helperForTheorem_38_5_actualCounterexamplePositiveFirstCoordinateDual x =
      ⊤ := by
  rw [helperForTheorem_38_5_textbookDualMiddleFunction, iSup_eq_top]
  intro b hb
  rcases EReal.lt_iff_exists_rat_btwn.mp hb with ⟨q, hq, -⟩
  let y : Fin 1 → ℝ := fun _ => x 0 + q + 1
  refine ⟨y, ?_⟩
  have hltReal : (q : ℝ) < y 0 - x 0 := by
    dsimp [y]
    linarith
  have hltEReal : (((q : ℚ) : ℝ) : EReal) <
      (((helperForTheorem_38_5_actualCounterexamplePositiveFirstCoordinateDual y : ℝ)) : EReal) +
        (-helperForTheorem_38_5_actualCounterexampleSecondBifunction.toFun x y) := by
    simpa [y, helperForTheorem_38_5_actualCounterexamplePositiveFirstCoordinateDual,
      helperForTheorem_38_5_actualCounterexampleSecondBifunction,
      helperForTheorem_38_5_actualCounterexampleSecondRaw, sub_eq_add_neg] using
      (by exact_mod_cast hltReal :
        (((q : ℚ) : ℝ) : EReal) < (((y 0 - x 0 : ℝ)) : EReal))
  exact lt_trans hq hltEReal

/-- Helper for Theorem 38.5: therefore no generic argument can package all textbook dual middle
functions into `ProperConcaveFunctionOn`; the current theorem hypotheses already admit an explicit
counterexample where the dual middle function is `⊤` everywhere. -/
lemma helperForTheorem_38_5_actualCounterexample_textbookDualMiddle_not_properConcaveFunctionOn :
    ¬ ProperConcaveFunctionOn (Set.univ : Set (Fin 1 → ℝ))
      (helperForTheorem_38_5_textbookDualMiddleFunction
        helperForTheorem_38_5_actualCounterexampleSecondBifunction
        helperForTheorem_38_5_actualCounterexamplePositiveFirstCoordinateDual) := by
  intro hProper
  have hProperNeg :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun x : Fin 1 → ℝ =>
          -(helperForTheorem_38_5_textbookDualMiddleFunction
            helperForTheorem_38_5_actualCounterexampleSecondBifunction
            helperForTheorem_38_5_actualCounterexamplePositiveFirstCoordinateDual x)) := by
    simpa [ProperConcaveFunctionOn] using hProper
  have hNoBot := hProperNeg.2.2 helperForTheorem_38_5_zeroVec (by simp)
  have hTop :
      helperForTheorem_38_5_textbookDualMiddleFunction
          helperForTheorem_38_5_actualCounterexampleSecondBifunction
          helperForTheorem_38_5_actualCounterexamplePositiveFirstCoordinateDual
          helperForTheorem_38_5_zeroVec = ⊤ :=
    helperForTheorem_38_5_actualCounterexample_textbookDualMiddle_eq_top
      helperForTheorem_38_5_zeroVec
  have hBot :
      -(helperForTheorem_38_5_textbookDualMiddleFunction
          helperForTheorem_38_5_actualCounterexampleSecondBifunction
          helperForTheorem_38_5_actualCounterexamplePositiveFirstCoordinateDual
          helperForTheorem_38_5_zeroVec) = ⊥ := by
    simp [hTop]
  exact hNoBot hBot

/-- Helper for Theorem 38.5: there is no theorem-local bridge that upgrades the current bifunction
hypotheses to `ProperConcaveFunctionOn` for every textbook dual middle function. The explicit
actual-hypotheses counterexample already violates that conclusion. -/
lemma helperForTheorem_38_5_noGenericPropernessPackageForTextbookDualMiddle :
    ¬ ∀ {n p : Nat} (G : FiberwiseProperConvexBifunction n p),
        ProperConvexBifunction G.toFun →
        ∀ yStar : Module.Dual ℝ (Fin p → ℝ),
          ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ))
            (helperForTheorem_38_5_textbookDualMiddleFunction G yStar) := by
  intro hPackage
  have hProper :
      ProperConcaveFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (helperForTheorem_38_5_textbookDualMiddleFunction
          helperForTheorem_38_5_actualCounterexampleSecondBifunction
          helperForTheorem_38_5_actualCounterexamplePositiveFirstCoordinateDual) :=
    hPackage helperForTheorem_38_5_actualCounterexampleSecondBifunction
      helperForTheorem_38_5_actualCounterexampleSecond_properConvex
      helperForTheorem_38_5_actualCounterexamplePositiveFirstCoordinateDual
  exact
    helperForTheorem_38_5_actualCounterexample_textbookDualMiddle_not_properConcaveFunctionOn
      hProper


end Section38
end Chap08
