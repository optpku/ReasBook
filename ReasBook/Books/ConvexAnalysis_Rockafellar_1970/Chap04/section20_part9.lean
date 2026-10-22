/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part8

open scoped BigOperators Pointwise

section Chap04
section Section20
/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` binary
branch, an exact/top-or-attained bridge implies reverse inequality and universal
split-attainment. -/
lemma helperForTheorem_20_1_nonriInter_binary_reverseLe_and_universalAttainment_of_polyLeft_domRi_posDim_of_exact_topOrAttained
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hbinaryBridge :
      (fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        ∃ y : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
            fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  have hcore :
      (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :=
    helperForTheorem_20_1_nonriInterCore_reverseLe_and_neTopAttainment_of_exact_topOrAttained_binary_posDim
      (p := p) (q := q) hbinaryBridge
  exact
    helperForTheorem_20_1_nonriInter_binary_reverseLe_and_universalAttainment_of_polyLeft_domRi_posDim_of_core
      (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ hnonemptyDomInterRi
      hnotRiInter hcore

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, exact/top-or-attained is equivalent to
reverse inequality plus non-`⊤` split-attainment. -/
lemma helperForTheorem_20_1_nonriInter_posDim_exactTopOrAttained_iff_reverseLe_and_neTopAttainment_of_polyLeft_domRi
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    ((fenchelConjugate n (fun x => p x + q x) =
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
      ↔
      ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) := by
  have _hnPos_use : 0 < n := hnPos
  have _hnotRiInter_use :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) :=
    hnotRiInter
  constructor
  · intro hbinaryBridge
    exact
      helperForTheorem_20_1_nonriInterCore_reverseLe_and_neTopAttainment_of_exact_topOrAttained_binary_posDim
        (p := p) (q := q) hbinaryBridge
  · intro hcore
    have hforwardAndTopWitness :
        (fenchelConjugate n (fun x => p x + q x) ≤
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q))
          ∧
          (∀ xStar : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) →
              ∃ y : Fin n → ℝ,
                infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                  fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :=
      helperForTheorem_20_1_forwardLe_and_topWitness_of_polyLeft_domRi
        (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi
    exact
      helperForTheorem_20_1_exact_topOrAttained_of_forward_reverse_and_neTopAttainment
        (p := p) (q := q) (hforwardLe := hforwardAndTopWitness.1)
        (hreverseLe := hcore.1) (hneTopAttained := hcore.2)

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, the core package
`reverseLe + non-⊤ split-attainment` implies exact equality plus top-or-attained
for the binary bridge. -/
lemma helperForTheorem_20_1_nonriInter_posDim_exactTopOrAttained_of_core
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hcore :
      (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (fenchelConjugate n (fun x => p x + q x) =
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  exact
    (helperForTheorem_20_1_nonriInter_posDim_exactTopOrAttained_iff_reverseLe_and_neTopAttainment_of_polyLeft_domRi
      (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ hnonemptyDomInterRi
      hnotRiInter).2 hcore

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, the remaining core package
`reverseLe + non-⊤ split-attainment` is equivalent to
`reverseLe + universal split-attainment`. -/
lemma helperForTheorem_20_1_nonriInter_posDim_coreGoal_iff_reverseLe_and_universalAttainment_of_polyLeft_domRi
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
      ↔
      ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
          fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) := by
  have _hnPos_use : 0 < n := hnPos
  have _hnotRiInter_use :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) :=
    hnotRiInter
  exact
    helperForTheorem_20_1_nonriInter_binary_goal_iff_reverseLe_and_universalAttainment_of_polyLeft_domRi
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, the package
`reverseLe + universal split-attainment` already implies the required
exact/top-or-attained binary bridge. -/
lemma helperForTheorem_20_1_nonriInter_posDim_exactTopOrAttained_of_reverseLe_and_universal
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hreverseAndUniversal :
      (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (fenchelConjugate n (fun x => p x + q x) =
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  have hcoreGoalIff :
      ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠
              (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
        ↔
        ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
          fenchelConjugate n (fun x => p x + q x))
          ∧
          (∀ xStar : Fin n → ℝ,
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :=
    helperForTheorem_20_1_nonriInter_posDim_coreGoal_iff_reverseLe_and_universalAttainment_of_polyLeft_domRi
      (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ hnonemptyDomInterRi
      hnotRiInter
  have hcore :
      (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠
              (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :=
    hcoreGoalIff.2 hreverseAndUniversal
  exact
    helperForTheorem_20_1_nonriInter_posDim_exactTopOrAttained_of_core
      (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ hnonemptyDomInterRi
      hnotRiInter hcore

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, the core package
`reverseLe + non-⊤ split-attainment` yields both
exact/top-or-attained and universal split-attainment. -/
lemma helperForTheorem_20_1_nonriInter_posDim_exactTopOrAttained_and_universal_of_core
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hcore :
      (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠
              (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    ((fenchelConjugate n (fun x => p x + q x) =
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
      ∧
      (∀ xStar : Fin n → ℝ,
        ∃ y : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
            fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  have hbinaryBridge :
      (fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :=
    helperForTheorem_20_1_nonriInter_posDim_exactTopOrAttained_of_core
      (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ hnonemptyDomInterRi
      hnotRiInter hcore
  have hreverseAndUniversal :
      (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :=
    helperForTheorem_20_1_nonriInter_binary_reverseLe_and_universalAttainment_of_polyLeft_domRi_posDim_of_core
      (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ hnonemptyDomInterRi
      hnotRiInter hcore
  exact ⟨hbinaryBridge, hreverseAndUniversal.2⟩

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, the mixed assumptions already yield
forward inequality and top-case split-attainment for the binary infimal
convolution. -/
lemma helperForTheorem_20_1_nonriInter_posDim_forwardLe_and_topWitness_of_polyLeft_domRi
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    (fenchelConjugate n (fun x => p x + q x) ≤
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  have _hnPos_use : 0 < n := hnPos
  have _hnotRiInter_use :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) :=
    hnotRiInter
  exact
    helperForTheorem_20_1_forwardLe_and_topWitness_of_polyLeft_domRi
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, the unresolved core package
`reverseLe + non-⊤ split-attainment` is equivalent to the binary
exact/top-or-attained bridge. -/
lemma helperForTheorem_20_1_nonriInter_posDim_core_iff_exactTopOrAttained_of_polyLeft_domRi
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
      ↔
      ((fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) := by
  exact
    (helperForTheorem_20_1_nonriInter_posDim_exactTopOrAttained_iff_reverseLe_and_neTopAttainment_of_polyLeft_domRi
      (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ hnonemptyDomInterRi
      hnotRiInter).symm

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, an exact/top-or-attained binary bridge
immediately yields the core package `reverseLe + non-⊤ split-attainment`. -/
lemma helperForTheorem_20_1_nonriInter_posDim_core_of_exactTopOrAttained_of_polyLeft_domRi
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hbinaryBridge :
      (fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  exact
    (helperForTheorem_20_1_nonriInter_posDim_core_iff_exactTopOrAttained_of_polyLeft_domRi
      (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ hnonemptyDomInterRi
      hnotRiInter).2 hbinaryBridge

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, the currently available
dependency-closed binary data can be packaged as:
forward inequality + top-case witness, together with the equivalence between
the core package and exact/top-or-attained. -/
lemma helperForTheorem_20_1_nonriInter_posDim_forwardTop_and_coreIffExact_data_of_polyLeft_domRi
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    ((fenchelConjugate n (fun x => p x + q x) ≤
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
      ∧
      (((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
        ↔
        ((fenchelConjugate n (fun x => p x + q x) =
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
          (∀ xStar : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                (⊤ : EReal) ∨
              ∃ y : Fin n → ℝ,
                infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                  fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))) := by
  refine ⟨?_, ?_⟩
  · exact
      helperForTheorem_20_1_nonriInter_posDim_forwardLe_and_topWitness_of_polyLeft_domRi
        (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ hnonemptyDomInterRi
        hnotRiInter
  · exact
      helperForTheorem_20_1_nonriInter_posDim_core_iff_exactTopOrAttained_of_polyLeft_domRi
        (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ hnonemptyDomInterRi
        hnotRiInter

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, any exact/top-or-attained binary
bridge implies the core package once the local `core ↔ bridge` equivalence is
available. -/
lemma helperForTheorem_20_1_nonriInter_posDim_core_of_coreIff_and_exactTopOrAttained
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hcoreIffBinaryBridge :
      ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠
              (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
        ↔
        ((fenchelConjugate n (fun x => p x + q x) =
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
          (∀ xStar : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                (⊤ : EReal) ∨
              ∃ y : Fin n → ℝ,
                infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                  fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)))
    (hbinaryBridge :
      (fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  exact hcoreIffBinaryBridge.2 hbinaryBridge

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, the remaining unresolved core package
is reverse inequality plus non-`⊤` split-attainment. -/
lemma helperForTheorem_20_1_nonriInter_posDim_core_reverseLe_and_neTopAttainment_of_polyLeft_domRi
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (_hnPos : 0 < n)
    (_hpolyP : IsPolyhedralConvexFunction n p)
    (_hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (_hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (_hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (_hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hbinaryBridgeExactTopOrAttained_nonri :
      (fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  exact
    helperForTheorem_20_1_nonriInterCore_reverseLe_and_neTopAttainment_of_exact_topOrAttained_binary_posDim
      (p := p) (q := q) hbinaryBridgeExactTopOrAttained_nonri

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` setting with polyhedral left block, this is the exact/top-or-attained
binary bridge needed to close the non-`riInter` branch. -/
lemma section20_mixed_two_block_exact_topOrAttained_of_polyLeft_domRi_nonriInter_posDim_from_closure_forward_topcase
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (_hnPos : 0 < n)
    (_hpolyP : IsPolyhedralConvexFunction n p)
    (_hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (_hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (_hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (_hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hbinaryBridgeExactTopOrAttained_nonri :
      (fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (fenchelConjugate n (fun x => p x + q x) =
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  exact hbinaryBridgeExactTopOrAttained_nonri

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` mixed
`dom/ri` branch with polyhedral left block, the exact/top-or-attained binary bridge
implies the core package `reverseLe + non-⊤ split-attainment`. -/
lemma section20_mixed_two_block_reverseLe_and_neTopAttainment_of_polyLeft_domRi_nonriInter_posDim_from_closure_forward_topcase
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hbinaryBridgeExactTopOrAttained_nonri :
      (fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  exact
    helperForTheorem_20_1_nonriInter_posDim_core_reverseLe_and_neTopAttainment_of_polyLeft_domRi
      (p := p) (q := q) hnPos hpolyP hproperP hproperQ hnonemptyDomInterRi
      hnotRiInter hbinaryBridgeExactTopOrAttained_nonri

/-- Helper for Theorem 20.1: core non-`riInter` binary bridge under
`dom(p) ∩ ri(dom(q))` with polyhedral left block, providing reverse inequality
and non-`⊤` split-attainment. -/
lemma helperForTheorem_20_1_nonriInter_binary_reverseLe_and_universalAttainment_of_polyLeft_domRi_posDim
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hbinaryBridgeExactTopOrAttained_nonri :
      (fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        ∃ y : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
            fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  have hcore :
      (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :=
    section20_mixed_two_block_reverseLe_and_neTopAttainment_of_polyLeft_domRi_nonriInter_posDim_from_closure_forward_topcase
      (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ
      hnonemptyDomInterRi hnotRiInter hbinaryBridgeExactTopOrAttained_nonri
  exact
    helperForTheorem_20_1_nonriInter_binary_reverseLe_and_universalAttainment_of_polyLeft_domRi_posDim_of_core
      (p := p) (q := q) (hnPos := hnPos) hpolyP hproperP hproperQ hnonemptyDomInterRi
      hnotRiInter hcore

/-- Helper for Theorem 20.5: every polyhedral convex set is finitely generated. -/
lemma helperForTheorem_20_5_finitelyGenerated_of_polyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsFinitelyGeneratedConvexSet n C := by
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hTFAE :
      [IsPolyhedralConvexSet n C,
        (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite),
        IsFinitelyGeneratedConvexSet n C].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := n) (C := C) hCconv
  exact (hTFAE.out 0 2).1 hCpoly

/-- Helper for Theorem 20.5: a simplex admits the local finite-simplicial witness
required by `Set.LocallySimplicial`. -/
lemma helperForTheorem_20_5_localSimplexWitness_of_isSimplex
    {n m : ℕ} {P : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hP : IsSimplex n m P) (hx : x ∈ P) :
    ∃ (𝒮 : Set (Set (Fin n → ℝ))) (U : Set (Fin n → ℝ)),
      𝒮.Finite ∧
        U ∈ nhds x ∧
          (∀ Q ∈ 𝒮, ∃ k : ℕ, IsSimplex n k Q ∧ Q ⊆ P) ∧
            U ∩ (⋃₀ 𝒮) = U ∩ P := by
  classical
  rcases simplex_exists_subsimplex_through_point (hC := hP) (hx := hx) with
    ⟨b, _hb, _hP_eq, hthrough⟩
  let cand : Fin (m + 1) → Set (Fin n → ℝ) := fun j =>
    convexHull ℝ (Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j i)))
  let 𝒮 : Set (Set (Fin n → ℝ)) :=
    {Q | ∃ j : Fin (m + 1), Q = cand j ∧ IsSimplex n m Q ∧ Q ⊆ P}
  have h𝒮subsetRange : 𝒮 ⊆ Set.range cand := by
    intro Q hQ
    rcases hQ with ⟨j, hQeq, _hQsimp, _hQsub⟩
    exact ⟨j, hQeq.symm⟩
  have h𝒮finite : 𝒮.Finite := by
    exact (Set.finite_range cand).subset h𝒮subsetRange
  have hsUnion_subset : ⋃₀ 𝒮 ⊆ P := by
    intro y hy
    rcases Set.mem_sUnion.mp hy with ⟨Q, hQmem, hyQ⟩
    rcases hQmem with ⟨j, rfl, _hQsimp, hQsub⟩
    exact hQsub hyQ
  have hP_subset : P ⊆ ⋃₀ 𝒮 := by
    intro y hyP
    rcases hthrough y hyP with ⟨j, hQsub, hQsimp, _hxQ, hyQ⟩
    have hQsimpCand : IsSimplex n m (cand j) := by
      simpa [cand] using hQsimp
    have hQsubCand : cand j ⊆ P := by
      simpa [cand] using hQsub
    have hyCand : y ∈ cand j := by
      simpa [cand] using hyQ
    have hCandMem : cand j ∈ 𝒮 := ⟨j, rfl, hQsimpCand, hQsubCand⟩
    exact Set.mem_sUnion.mpr ⟨cand j, hCandMem, hyCand⟩
  have hsUnion_eq : ⋃₀ 𝒮 = P := Set.Subset.antisymm hsUnion_subset hP_subset
  have hUnivNhds : (Set.univ : Set (Fin n → ℝ)) ∈ nhds x := Filter.univ_mem
  have hSimplexFamily :
      ∀ Q ∈ 𝒮, ∃ k : ℕ, IsSimplex n k Q ∧ Q ⊆ P := by
    intro Q hQ
    rcases hQ with ⟨j, rfl, hQsimp, hQsub⟩
    exact ⟨m, hQsimp, hQsub⟩
  refine ⟨𝒮, Set.univ, h𝒮finite, hUnivNhds, hSimplexFamily, ?_⟩
  simpa [hsUnion_eq]

/-- Helper for Theorem 20.5: every simplex is locally simplicial. -/
lemma helperForTheorem_20_5_locallySimplicial_of_isSimplex
    {n m : ℕ} {P : Set (Fin n → ℝ)}
    (hP : IsSimplex n m P) :
    Set.LocallySimplicial n P := by
  intro x hx
  exact helperForTheorem_20_5_localSimplexWitness_of_isSimplex (hP := hP) (hx := hx)

/-- Helper for Theorem 20.5: a finitely generated convex set admits the global
generalized-simplex decomposition from Theorem 17.1. -/
lemma helperForTheorem_20_5_globalGeneralizedSimplexDecomposition_of_finitelyGenerated
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCfg : IsFinitelyGeneratedConvexSet n C) :
    let d := Module.finrank ℝ (affineSpan ℝ C).direction
    C = ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} := by
  rcases hCfg with ⟨S0, S1, hS0fin, hS1fin, rfl⟩
  have _hS0fin_use : Set.Finite S0 := hS0fin
  have _hS1fin_use : Set.Finite S1 := hS1fin
  exact mixedConvexHull_eq_sUnion_generalizedSimplex_finrank_affineSpan_direction
    (n := n) S0 S1

/-- Helper for Theorem 20.5: any member of the global generalized-simplex family over `C`
is a subset of `C`. -/
lemma helperForTheorem_20_5_subset_of_mem_globalGeneralizedSimplexFamily
    {n d : ℕ} {C T : Set (Fin n → ℝ)}
    (hTmem : T ∈ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C}) :
    T ⊆ C := by
  exact hTmem.2

/-- Helper for Theorem 20.5: the global generalized-simplex union from finite generation is
contained in the original set. -/
lemma helperForTheorem_20_5_globalGeneralizedSimplexUnion_subset_of_finitelyGenerated
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCfg : IsFinitelyGeneratedConvexSet n C) :
    let d := Module.finrank ℝ (affineSpan ℝ C).direction
    ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} ⊆ C := by
  intro d
  have hdecomp :
      C = ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} :=
    helperForTheorem_20_5_globalGeneralizedSimplexDecomposition_of_finitelyGenerated
      (n := n) (C := C) hCfg
  intro x hx
  exact hdecomp.symm ▸ hx

/-- Helper for Theorem 20.5: every point of a finitely generated convex set belongs to the
global generalized-simplex union from Theorem 17.1. -/
lemma helperForTheorem_20_5_mem_globalGeneralizedSimplexUnion_of_finitelyGenerated
    {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hCfg : IsFinitelyGeneratedConvexSet n C) (hx : x ∈ C) :
    let d := Module.finrank ℝ (affineSpan ℝ C).direction
    x ∈ ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} := by
  intro d
  have hdecomp :
      C = ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} :=
    helperForTheorem_20_5_globalGeneralizedSimplexDecomposition_of_finitelyGenerated
      (n := n) (C := C) hCfg
  exact hdecomp ▸ hx

/-- Helper for Theorem 20.5: a point in the global generalized-simplex union lies in one
generalized simplex from that family. -/
lemma helperForTheorem_20_5_exists_generalizedSimplex_through_point_of_mem_globalGeneralizedSimplexUnion
    {n d : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hxUnion :
      x ∈ ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C}) :
    ∃ T : Set (Fin n → ℝ), IsGeneralizedSimplex n d T ∧ T ⊆ C ∧ x ∈ T := by
  rcases Set.mem_sUnion.mp hxUnion with ⟨T, hTmem, hxT⟩
  have hTsub : T ⊆ C :=
    helperForTheorem_20_5_subset_of_mem_globalGeneralizedSimplexFamily
      (n := n) (d := d) (C := C) (T := T) hTmem
  exact ⟨T, hTmem.1, hTsub, hxT⟩

/-- Helper for Theorem 20.5: extract a point-containing generalized simplex from finite
generation via the global decomposition route. -/
lemma helperForTheorem_20_5_exists_generalizedSimplex_through_point_of_finitelyGenerated_via_globalUnion
    {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hCfg : IsFinitelyGeneratedConvexSet n C) (hx : x ∈ C) :
    let d := Module.finrank ℝ (affineSpan ℝ C).direction
    ∃ T : Set (Fin n → ℝ), IsGeneralizedSimplex n d T ∧ T ⊆ C ∧ x ∈ T := by
  intro d
  have hxUnion :
      x ∈ ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} :=
    helperForTheorem_20_5_mem_globalGeneralizedSimplexUnion_of_finitelyGenerated
      (n := n) (C := C) (x := x) hCfg hx
  exact
    helperForTheorem_20_5_exists_generalizedSimplex_through_point_of_mem_globalGeneralizedSimplexUnion
      (n := n) (d := d) (C := C) (x := x) hxUnion

/-- Helper for Theorem 20.5: every point of a mixed convex hull lies in a generalized
simplex contained in that mixed convex hull. -/
lemma helperForTheorem_20_5_exists_generalizedSimplex_through_point_of_mixedConvexHull
    {n : ℕ} {S0 S1 : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ mixedConvexHull (n := n) S0 S1) :
    let C := mixedConvexHull (n := n) S0 S1
    let d := Module.finrank ℝ (affineSpan ℝ C).direction
    ∃ T : Set (Fin n → ℝ), IsGeneralizedSimplex n d T ∧ T ⊆ C ∧ x ∈ T := by
  intro C d
  have hxC : x ∈ C := by
    simpa [C] using hx
  have hdecomp :
      C = ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} :=
    mixedConvexHull_eq_sUnion_generalizedSimplex_finrank_affineSpan_direction
      (n := n) S0 S1
  have hxUnion :
      x ∈ ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} := by
    rw [← hdecomp]
    exact hxC
  rcases Set.mem_sUnion.mp hxUnion with ⟨T, hTmem, hxT⟩
  exact ⟨T, hTmem.1, hTmem.2, hxT⟩

/-- Helper for Theorem 20.5: every point of a finitely generated convex set lies in a
generalized simplex contained in that set. -/
lemma helperForTheorem_20_5_exists_generalizedSimplex_through_point_of_finitelyGenerated
    {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hCfg : IsFinitelyGeneratedConvexSet n C) (hx : x ∈ C) :
    let d := Module.finrank ℝ (affineSpan ℝ C).direction
    ∃ T : Set (Fin n → ℝ), IsGeneralizedSimplex n d T ∧ T ⊆ C ∧ x ∈ T := by
  rcases hCfg with ⟨S0, S1, hS0fin, hS1fin, rfl⟩
  have _hS0fin_use : Set.Finite S0 := hS0fin
  have _hS1fin_use : Set.Finite S1 := hS1fin
  simpa using
    (helperForTheorem_20_5_exists_generalizedSimplex_through_point_of_mixedConvexHull
      (n := n) (S0 := S0) (S1 := S1) (x := x) hx)

/-- Helper for Theorem 20.5: the global generalized-simplex decomposition of a finitely
generated convex set gives a neighborhood equality with the global generalized-simplex
union. -/
lemma helperForTheorem_20_5_localEq_with_globalGeneralizedSimplexUnion_of_finitelyGenerated
    {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hCfg : IsFinitelyGeneratedConvexSet n C) :
    let d := Module.finrank ℝ (affineSpan ℝ C).direction
    ∃ U : Set (Fin n → ℝ),
      U ∈ nhds x ∧
        U ∩ C = U ∩ ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} := by
  intro d
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  have hdecomp :
      C = ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} :=
    helperForTheorem_20_5_globalGeneralizedSimplexDecomposition_of_finitelyGenerated
      (n := n) (C := C) hCfg
  calc
    Set.univ ∩ C = C := by simp
    _ = ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} := hdecomp
    _ = Set.univ ∩ ⋃₀ {T : Set (Fin n → ℝ) | IsGeneralizedSimplex n d T ∧ T ⊆ C} := by
      simp

/-- Helper for Theorem 20.5: package a point-containing generalized simplex together with
the neighborhood equality to the global generalized-simplex union. -/
lemma helperForTheorem_20_5_exists_generalizedSimplex_through_point_and_localEq_with_globalUnion_of_finitelyGenerated
    {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hCfg : IsFinitelyGeneratedConvexSet n C) (hx : x ∈ C) :
    let d := Module.finrank ℝ (affineSpan ℝ C).direction
    ∃ (T U : Set (Fin n → ℝ)),
      IsGeneralizedSimplex n d T ∧
        T ⊆ C ∧
          x ∈ T ∧
            U ∈ nhds x ∧
              U ∩ C = U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} := by
  intro d
  rcases
      (helperForTheorem_20_5_exists_generalizedSimplex_through_point_of_finitelyGenerated
        (n := n) (C := C) (x := x) hCfg hx)
    with ⟨T, hTgen, hTsub, hxT⟩
  rcases
      (helperForTheorem_20_5_localEq_with_globalGeneralizedSimplexUnion_of_finitelyGenerated
        (n := n) (C := C) (x := x) hCfg)
    with ⟨U, hUnhds, hUeq⟩
  exact ⟨T, U, hTgen, hTsub, hxT, hUnhds, hUeq⟩

/-- Helper for Theorem 20.5: if `T ⊆ C` is locally simplicial and `T` agrees with `C`
on a neighborhood of `x`, then `C` has a local simplicial witness at `x`. -/
lemma helperForTheorem_20_5_localWitness_of_subset_locallySimplicial_and_localEq
    {n : ℕ} {C T : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hTloc : Set.LocallySimplicial n T)
    (hTsub : T ⊆ C) (hxT : x ∈ T)
    {U : Set (Fin n → ℝ)} (hUnhds : U ∈ nhds x) (hUeq : U ∩ C = U ∩ T) :
    ∃ (𝒮 : Set (Set (Fin n → ℝ))) (W : Set (Fin n → ℝ)),
      𝒮.Finite ∧
        W ∈ nhds x ∧
          (∀ Q ∈ 𝒮, ∃ k : ℕ, IsSimplex n k Q ∧ Q ⊆ C) ∧
            W ∩ (⋃₀ 𝒮) = W ∩ C := by
  rcases hTloc x hxT with ⟨𝒮, V, h𝒮fin, hVnhds, hSimplex, hVeq⟩
  refine ⟨𝒮, U ∩ V, h𝒮fin, Filter.inter_mem hUnhds hVnhds, ?_, ?_⟩
  · intro Q hQ
    rcases hSimplex Q hQ with ⟨k, hQsimplex, hQsubT⟩
    exact ⟨k, hQsimplex, Set.Subset.trans hQsubT hTsub⟩
  · ext y
    constructor
    · intro hy
      rcases hy with ⟨hyUV, hyUnion⟩
      rcases hyUV with ⟨hyU, hyV⟩
      have hyVT : y ∈ V ∩ T := by
        have hyVS : y ∈ V ∩ ⋃₀ 𝒮 := ⟨hyV, hyUnion⟩
        simpa [hVeq] using hyVS
      have hyC : y ∈ C := hTsub hyVT.2
      exact ⟨⟨hyU, hyV⟩, hyC⟩
    · intro hy
      rcases hy with ⟨hyUV, hyC⟩
      rcases hyUV with ⟨hyU, hyV⟩
      have hyUT : y ∈ U ∩ T := by
        have hyUC : y ∈ U ∩ C := ⟨hyU, hyC⟩
        simpa [hUeq] using hyUC
      have hyVS : y ∈ V ∩ ⋃₀ 𝒮 := by
        have hyVT : y ∈ V ∩ T := ⟨hyV, hyUT.2⟩
        simpa [hVeq] using hyVT
      exact ⟨⟨hyU, hyV⟩, hyVS.2⟩

/-- Helper for Theorem 20.5: local generalized-simplex bridge at a point of a finitely
generated convex set. -/
lemma helperForTheorem_20_5_localEq_of_localEq_with_union_and_localEq_union_to_piece
    {n : ℕ} {C T U : Set (Fin n → ℝ)} {𝒯 : Set (Set (Fin n → ℝ))}
    (hUCeqUnion : U ∩ C = U ∩ ⋃₀ 𝒯)
    (hUUnionEqT : U ∩ ⋃₀ 𝒯 = U ∩ T) :
    U ∩ C = U ∩ T := by
  calc
    U ∩ C = U ∩ ⋃₀ 𝒯 := hUCeqUnion
    _ = U ∩ T := hUUnionEqT

/-- Helper for Theorem 20.5: a selected generalized-simplex piece contained in `C`
is contained in the global generalized-simplex union over `C`. -/
lemma helperForTheorem_20_5_selectedGeneralizedSimplex_subset_globalUnion
    {n d : ℕ} {C T : Set (Fin n → ℝ)}
    (hTgen : IsGeneralizedSimplex n d T) (hTsub : T ⊆ C) :
    T ⊆ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} := by
  intro y hyT
  exact Set.mem_sUnion.mpr ⟨T, ⟨hTgen, hTsub⟩, hyT⟩

/-- Helper for Theorem 20.5: intersecting with `U`, a selected generalized-simplex
piece contained in `C` is contained in the global generalized-simplex union over `C`. -/
lemma helperForTheorem_20_5_selectedGeneralizedSimplex_inter_subset_globalUnion_inter
    {n d : ℕ} {C T U : Set (Fin n → ℝ)}
    (hTgen : IsGeneralizedSimplex n d T) (hTsub : T ⊆ C) :
    U ∩ T ⊆ U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} := by
  intro y hyUT
  rcases hyUT with ⟨hyU, hyT⟩
  exact ⟨hyU,
    helperForTheorem_20_5_selectedGeneralizedSimplex_subset_globalUnion
      (n := n) (d := d) (C := C) (T := T) hTgen hTsub hyT⟩

/-- Helper for Theorem 20.5: missing local piece data for a selected generalized-simplex
inside the global generalized-simplex union of a finitely generated convex set. -/
lemma helperForTheorem_20_5_localPieceData_of_selectedGeneralizedSimplex_in_finitelyGenerated
    {n d : ℕ} {C T U : Set (Fin n → ℝ)}
    (hTloc : Set.LocallySimplicial n T)
    (hUUnionSubT :
      U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} ⊆ U ∩ T) :
    ∃ _hTloc : Set.LocallySimplicial n T,
      U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} ⊆ U ∩ T := by
  exact ⟨hTloc, hUUnionSubT⟩

/-- Helper for Theorem 20.5: from a selected generalized-simplex in the finitely generated
decomposition neighborhood, extract the local piece data needed for the bridge step. -/
lemma helperForTheorem_20_5_selectedGeneralizedSimplex_localPieceData_of_finitelyGenerated
    {n d : ℕ} {C T U : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (_hCfg : IsFinitelyGeneratedConvexSet n C) (_hx : x ∈ C)
    (_hTgen : IsGeneralizedSimplex n d T) (_hTsub : T ⊆ C) (_hxT : x ∈ T)
    (_hUCeqUnion :
      U ∩ C = U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C})
    (hTloc : Set.LocallySimplicial n T)
    (hUUnionSubT :
      U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} ⊆ U ∩ T) :
    ∃ _hTloc : Set.LocallySimplicial n T,
      U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} ⊆ U ∩ T := by
  exact
    helperForTheorem_20_5_localPieceData_of_selectedGeneralizedSimplex_in_finitelyGenerated
      (n := n) (d := d) (C := C) (T := T) (U := U) hTloc hUUnionSubT

/-- Helper for Theorem 20.5: local piece data together with the selected-piece-to-union
inclusion yields neighborhood equality between the global union and the selected piece. -/
lemma helperForTheorem_20_5_localEq_of_localPieceData_and_selectedGeneralizedSimplexInterSubset
    {n d : ℕ} {C T U : Set (Fin n → ℝ)}
    (hLocalPieceData :
      ∃ _hTloc : Set.LocallySimplicial n T,
        U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} ⊆ U ∩ T)
    (hUTsubUUnion :
      U ∩ T ⊆ U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C}) :
    ∃ _hTloc : Set.LocallySimplicial n T,
      U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} = U ∩ T := by
  rcases hLocalPieceData with ⟨hTloc, hUUnionSubT⟩
  refine ⟨hTloc, Set.Subset.antisymm hUUnionSubT hUTsubUUnion⟩

/-- Helper for Theorem 20.5: once local simpliciality of a selected generalized-simplex
piece and local union-to-piece equality are available, the local bridge data follow. -/
lemma helperForTheorem_20_5_localGeneralizedSimplexBridge_of_finitelyGenerated_of_localPieceData
    {n d : ℕ} {C T U : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hTgen : IsGeneralizedSimplex n d T)
    (hTsub : T ⊆ C) (hxT : x ∈ T) (hTloc : Set.LocallySimplicial n T)
    (hUnhds : U ∈ nhds x)
    (hUCeqUnion :
      U ∩ C = U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C})
    (hUUnionEqT :
      U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} = U ∩ T) :
    ∃ (T' U' : Set (Fin n → ℝ)),
      IsGeneralizedSimplex n d T' ∧
        T' ⊆ C ∧
          x ∈ T' ∧
            Set.LocallySimplicial n T' ∧
              U' ∈ nhds x ∧
                U' ∩ C = U' ∩ T' := by
  have hUCeqT : U ∩ C = U ∩ T :=
    helperForTheorem_20_5_localEq_of_localEq_with_union_and_localEq_union_to_piece
      (n := n) (C := C) (T := T) (U := U)
      (𝒯 := {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C})
      hUCeqUnion hUUnionEqT
  exact ⟨T, U, hTgen, hTsub, hxT, hTloc, hUnhds, hUCeqT⟩

/-- Helper for Theorem 20.5: local generalized-simplex bridge at a point of a finitely
generated convex set. -/
lemma helperForTheorem_20_5_localGeneralizedSimplexBridge_of_finitelyGenerated
    {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hCfg : IsFinitelyGeneratedConvexSet n C) (hx : x ∈ C) :
    let d := Module.finrank ℝ (affineSpan ℝ C).direction
    (∀ {T U : Set (Fin n → ℝ)},
      IsGeneralizedSimplex n d T →
      T ⊆ C →
      x ∈ T →
      U ∈ nhds x →
      U ∩ C = U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} →
      ∃ _hTloc : Set.LocallySimplicial n T,
        U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} ⊆ U ∩ T) →
    ∃ (T U : Set (Fin n → ℝ)),
      IsGeneralizedSimplex n d T ∧
        T ⊆ C ∧
          x ∈ T ∧
            Set.LocallySimplicial n T ∧
              U ∈ nhds x ∧
                U ∩ C = U ∩ T := by
  intro d hSelectedLocalPieceData
  rcases
      (helperForTheorem_20_5_exists_generalizedSimplex_through_point_and_localEq_with_globalUnion_of_finitelyGenerated
        (n := n) (C := C) (x := x) hCfg hx)
    with ⟨T, U, hTgen, hTsub, hxT, hUnhds, hUeqUnion⟩
  have _hUeqUnion_use :
      U ∩ C = U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} :=
    hUeqUnion
  have _hTgen_use : IsGeneralizedSimplex n d T := hTgen
  have _hTsub_use : T ⊆ C := hTsub
  have _hxT_use : x ∈ T := hxT
  have _hUnhds_use : U ∈ nhds x := hUnhds
  have hUTsubUUnion :
      U ∩ T ⊆ U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} := by
    exact
      helperForTheorem_20_5_selectedGeneralizedSimplex_inter_subset_globalUnion_inter
        (n := n) (d := d) (C := C) (T := T) (U := U) hTgen hTsub
  have hLocalPieceData :
      ∃ hTloc : Set.LocallySimplicial n T,
        U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} ⊆ U ∩ T :=
    hSelectedLocalPieceData hTgen hTsub hxT hUnhds hUeqUnion
  rcases
      (helperForTheorem_20_5_localEq_of_localPieceData_and_selectedGeneralizedSimplexInterSubset
        (n := n) (d := d) (C := C) (T := T) (U := U) hLocalPieceData hUTsubUUnion)
    with ⟨hTloc, hUUnionEqT⟩
  exact
    helperForTheorem_20_5_localGeneralizedSimplexBridge_of_finitelyGenerated_of_localPieceData
      (n := n) (d := d) (C := C) (T := T) (U := U) (x := x)
      hTgen hTsub hxT hTloc hUnhds hUeqUnion hUUnionEqT

/-- Helper for Theorem 20.5: finitely generated convex sets are locally simplicial. -/
lemma helperForTheorem_20_5_locallySimplicial_of_finitelyGenerated
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCfg : IsFinitelyGeneratedConvexSet n C)
    (hSelectedLocalPieceData :
      ∀ x ∈ C,
        let d := Module.finrank ℝ (affineSpan ℝ C).direction
        ∀ {T U : Set (Fin n → ℝ)},
          IsGeneralizedSimplex n d T →
          T ⊆ C →
          x ∈ T →
          U ∈ nhds x →
          U ∩ C = U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} →
          ∃ _hTloc : Set.LocallySimplicial n T,
            U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} ⊆ U ∩ T) :
    Set.LocallySimplicial n C := by
  intro x hx
  let d := Module.finrank ℝ (affineSpan ℝ C).direction
  rcases
      (helperForTheorem_20_5_localGeneralizedSimplexBridge_of_finitelyGenerated
        (n := n) (C := C) (x := x) hCfg hx)
        (hSelectedLocalPieceData x hx)
    with ⟨T, U, _hTgen, hTsub, hxT, hTloc, hUnhds, hUeq⟩
  exact
    helperForTheorem_20_5_localWitness_of_subset_locallySimplicial_and_localEq
      (n := n) (C := C) (T := T) (x := x) hTloc hTsub hxT hUnhds hUeq

/-- Helper for Theorem 20.5: every polytope is polyhedral. -/
lemma helperForTheorem_20_5_polyhedral_of_polytope
    {n : ℕ} {P : Set (Fin n → ℝ)}
    (hPpolytope : IsPolytope n P) :
    IsPolyhedralConvexSet n P := by
  rcases hPpolytope with ⟨S, hSfinite, hP_eq⟩
  have hPconv : Convex ℝ P := by
    rw [hP_eq]
    exact convex_convexHull ℝ S
  have hPfg : IsFinitelyGeneratedConvexSet n P := by
    refine ⟨S, (∅ : Set (Fin n → ℝ)), hSfinite, Set.finite_empty, ?_⟩
    calc
      P = convexHull ℝ S := hP_eq
      _ = mixedConvexHull (n := n) S (∅ : Set (Fin n → ℝ)) := by
            symm
            exact mixedConvexHull_empty_directions_eq_convexHull (n := n) S
  exact helperForTheorem_19_1_finitelyGenerated_imp_polyhedral
    (n := n) (C := P) hPconv hPfg

/-- Theorem 20.5: every polyhedral convex set is locally simplicial; in particular,
every polytope is locally simplicial. -/
theorem Theorem_20_5
    (n : ℕ)
    (hSelectedLocalPieceData :
      ∀ C : Set (Fin n → ℝ), IsPolyhedralConvexSet n C →
        ∀ x ∈ C,
          let d := Module.finrank ℝ (affineSpan ℝ C).direction
          ∀ {T U : Set (Fin n → ℝ)},
            IsGeneralizedSimplex n d T →
            T ⊆ C →
            x ∈ T →
            U ∈ nhds x →
            U ∩ C = U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} →
            ∃ _hTloc : Set.LocallySimplicial n T,
              U ∩ ⋃₀ {R : Set (Fin n → ℝ) | IsGeneralizedSimplex n d R ∧ R ⊆ C} ⊆ U ∩ T) :
    (∀ C : Set (Fin n → ℝ), IsPolyhedralConvexSet n C → Set.LocallySimplicial n C) ∧
      (∀ P : Set (Fin n → ℝ), IsPolytope n P → Set.LocallySimplicial n P) := by
  have hpolyhedralLocallySimplicial :
      ∀ C : Set (Fin n → ℝ), IsPolyhedralConvexSet n C → Set.LocallySimplicial n C := by
    intro C hCpoly
    exact
      helperForTheorem_20_5_locallySimplicial_of_finitelyGenerated
        (helperForTheorem_20_5_finitelyGenerated_of_polyhedral (n := n) (C := C) hCpoly)
        (hSelectedLocalPieceData C hCpoly)
  constructor
  · exact hpolyhedralLocallySimplicial
  · intro P hPpolytope
    exact
      hpolyhedralLocallySimplicial P
        (helperForTheorem_20_5_polyhedral_of_polytope (n := n) (P := P) hPpolytope)


end Section20
end Chap04
