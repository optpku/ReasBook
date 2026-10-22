/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part12

open scoped Pointwise

section Chap08
section Section38

attribute [local instance] instTopologicalSpace_moduleDual_weak_part3

/-- Helper for Theorem 38.5: the supremum-side dual composition is always bounded above by the
adjoint of the primal composition. -/
lemma helperForTheorem_38_5_composeSupGeneric_le_adjoint_compose
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun) yStar uStar ≤
      bifunctionAdjoint (bifunctionCompose G F) yStar uStar := by
  rw [bifunctionComposeSupGeneric, bifunctionAdjoint]
  refine iSup_le ?_
  intro xStar
  refine le_iInf ?_
  intro u
  refine le_iInf ?_
  intro y
  let c : ℝ := yStar y - uStar u
  have hPointwise :
      bifunctionAdjoint F.toFun xStar uStar + bifunctionAdjoint G.toFun yStar xStar ≤
        ⨅ x : Fin n → ℝ, ((c : EReal) + (F.toFun u x + G.toFun x y)) := by
    -- Compare both adjoint terms against the same primal triple `(u, x, y)`.
    refine le_iInf ?_
    intro x
    have hFterm :
        bifunctionAdjoint F.toFun xStar uStar ≤
          ((xStar x : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) + F.toFun u x := by
      rw [bifunctionAdjoint]
      refine iInf_le_of_le u ?_
      exact iInf_le_of_le x le_rfl
    have hGterm :
        bifunctionAdjoint G.toFun yStar xStar ≤
          ((yStar y : ℝ) : EReal) + (-((xStar x : ℝ) : EReal)) + G.toFun x y := by
      rw [bifunctionAdjoint]
      refine iInf_le_of_le x ?_
      exact iInf_le_of_le y le_rfl
    have hSum :
        bifunctionAdjoint F.toFun xStar uStar + bifunctionAdjoint G.toFun yStar xStar ≤
          (((xStar x : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) + F.toFun u x) +
            (((yStar y : ℝ) : EReal) + (-((xStar x : ℝ) : EReal)) + G.toFun x y) :=
      add_le_add hFterm hGterm
    refine hSum.trans ?_
    have hReassoc :
        (((xStar x : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) + F.toFun u x) +
            (((yStar y : ℝ) : EReal) + (-((xStar x : ℝ) : EReal)) + G.toFun x y) =
          ((((xStar x : ℝ) : EReal) + (-((xStar x : ℝ) : EReal))) +
              (((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)))) +
            (F.toFun u x + G.toFun x y) := by
      simp [add_assoc, add_left_comm, add_comm]
    have hCancel :
        ((xStar x : ℝ) : EReal) + (-((xStar x : ℝ) : EReal) + ((yStar y : ℝ) : EReal)) =
          ((yStar y : ℝ) : EReal) := by
      change (((xStar x : ℝ) + (-(xStar x) + yStar y) : ℝ) : EReal) = ((yStar y : ℝ) : EReal)
      ring_nf
    have hCancel' :
        ((xStar x : ℝ) : EReal) + (-((xStar x : ℝ) : EReal)) + ((yStar y : ℝ) : EReal) =
          ((yStar y : ℝ) : EReal) := by
      change (((xStar x : ℝ) + (-(xStar x)) + yStar y : ℝ) : EReal) = ((yStar y : ℝ) : EReal)
      ring_nf
    rw [hReassoc]
    simp [hCancel', c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hRewrite :
      (⨅ x : Fin n → ℝ, ((c : EReal) + (F.toFun u x + G.toFun x y))) =
        ((c : EReal) + ⨅ x : Fin n → ℝ, (F.toFun u x + G.toFun x y)) := by
    -- Pull the finite real constant out of the infimum over the eliminated middle variable.
    symm
    exact
      helperForTheorem_6_30_15_real_add_iInf c
        (fun x : Fin n → ℝ => F.toFun u x + G.toFun x y)
  simpa [c, bifunctionCompose, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    hPointwise.trans_eq hRewrite

/-- Helper for Theorem 38.5: unfold the adjoint of the composition into the explicit three-fold
infimum over `(u, y, x)` appearing in the textbook proof. -/
lemma helperForTheorem_38_5_adjoint_compose_eq_iInf_triple
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionAdjoint (bifunctionCompose G F) yStar uStar =
      ⨅ u : Fin m → ℝ, ⨅ y : Fin p → ℝ, ⨅ x : Fin n → ℝ,
        ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
          (F.toFun u x + G.toFun x y) := by
  simp [bifunctionAdjoint, bifunctionCompose]
  refine iInf_congr ?_
  intro u
  refine iInf_congr ?_
  intro y
  let c : ℝ := yStar y - uStar u
  calc
    (((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
        ⨅ x : Fin n → ℝ, (F.toFun u x + G.toFun x y)) =
      ((c : EReal) + ⨅ x : Fin n → ℝ, (F.toFun u x + G.toFun x y)) := by
        simp [c, sub_eq_add_neg, add_left_comm, add_comm]
    _ = ⨅ x : Fin n → ℝ, ((c : EReal) + (F.toFun u x + G.toFun x y)) := by
          exact
            helperForTheorem_6_30_15_real_add_iInf c
              (fun x : Fin n → ℝ => F.toFun u x + G.toFun x y)
    _ = ⨅ x : Fin n → ℝ,
          ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
            (F.toFun u x + G.toFun x y) := by
          refine iInf_congr ?_
          intro x
          simp [c, sub_eq_add_neg, add_assoc, add_comm]

/-- Helper for Theorem 38.5: commute the three indexed infima so the eliminated middle variable
`x` becomes the outer index, matching the textbook minimization over the middle variable. -/
lemma helperForTheorem_38_5_adjoint_compose_eq_iInf_middleFirst
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionAdjoint (bifunctionCompose G F) yStar uStar =
      ⨅ x : Fin n → ℝ, ⨅ u : Fin m → ℝ, ⨅ y : Fin p → ℝ,
        ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
          (F.toFun u x + G.toFun x y) := by
  calc
    bifunctionAdjoint (bifunctionCompose G F) yStar uStar =
        ⨅ u : Fin m → ℝ, ⨅ y : Fin p → ℝ, ⨅ x : Fin n → ℝ,
          ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
            (F.toFun u x + G.toFun x y) :=
      helperForTheorem_38_5_adjoint_compose_eq_iInf_triple F G yStar uStar
    _ = ⨅ u : Fin m → ℝ, ⨅ x : Fin n → ℝ, ⨅ y : Fin p → ℝ,
          ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
            (F.toFun u x + G.toFun x y) := by
          refine iInf_congr ?_
          intro u
          rw [iInf_comm]
    _ = ⨅ x : Fin n → ℝ, ⨅ u : Fin m → ℝ, ⨅ y : Fin p → ℝ,
          ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
            (F.toFun u x + G.toFun x y) := by
          rw [iInf_comm]

/-- Helper for Theorem 38.5: package the rewritten adjoint of the composition as the infimum of
the reduced middle-variable objective. -/
lemma helperForTheorem_38_5_adjoint_compose_eq_iInf_middleReducedObjective
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionAdjoint (bifunctionCompose G F) yStar uStar =
      ⨅ x : Fin n → ℝ, helperForTheorem_38_5_middleReducedObjective F G yStar uStar x := by
  simpa [helperForTheorem_38_5_middleReducedObjective] using
    helperForTheorem_38_5_adjoint_compose_eq_iInf_middleFirst F G yStar uStar

/-- Helper for Theorem 38.5: after the middle-objective rewrite, the adjoint of the composition is
the Fenchel primal infimum for the textbook middle-function pair. -/
lemma helperForTheorem_38_5_adjoint_compose_eq_fenchelPrimalInfimum
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionAdjoint (bifunctionCompose G F) yStar uStar =
      fenchelPrimalInfimum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
  rw [helperForTheorem_38_5_adjoint_compose_eq_iInf_middleReducedObjective, fenchelPrimalInfimum,
    functionInfimumEReal]
  refine iInf_congr ?_
  intro x
  exact helperForTheorem_38_5_middleReducedObjective_eq_commonBookEffectiveDomainDifference
    (F := F) (G := G) (yStar := yStar) (uStar := uStar) (x := x)

/-- Helper for Theorem 38.5: the remaining pointwise strong-duality statement for the textbook
middle-function pair. This is the exact Chapter 31-style subgoal left after the bifunction-side
rewrites are in place. -/
abbrev helperForTheorem_38_5_textbookSpecialPairStrongDuality
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) : Prop :=
  fenchelPrimalInfimum
      (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
      (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) =
    fenchelDualSupremum
      (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
      (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) ∧
    ∃ xStarVec : Fin n → ℝ,
      fenchelDualSupremum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) =
        fenchelDualObjective
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          xStarVec

/-- Helper for Theorem 38.5: a legacy common-shift surrogate
`z ↦ inf_x (f(x + z) - g(x + z))` for the middle-function pair. It keeps the book-effective-domain
guard inside a single function of `x + z`, so it is convenient for some Section 29 packaging, but
it is not the literal Chapter 31 perturbation used in the original text, where only the concave
term is translated. The corrected second-shift object is introduced just below. -/
noncomputable abbrev helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) : (Fin n → ℝ) → EReal :=
  fun z =>
    functionInfimumEReal
      (fun x : Fin n → ℝ =>
        commonBookEffectiveDomainDifference
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          (x + z))

/-- Helper for Theorem 38.5: the original-text translated perturbation for the textbook middle
pair. Unlike the legacy common-shift surrogate above, this is the genuine Chapter 31 pattern
`(z, x) ↦ f x - g (x + z)`, guarded so that the convex term is finite at `x` and the concave term
is finite at `x + z`. -/
noncomputable def helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    (Fin n → ℝ) → (Fin n → ℝ) → EReal :=
  by
    classical
    exact fun z x =>
      if hx :
          x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∧
            (x + z) ∈
              concaveEffectiveDomain
                (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) then
        helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x -
          helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) (x + z)
      else
        (⊤ : EReal)

/-- Helper for Theorem 38.5: the genuine Chapter 31 translated-value datum for the textbook
middle pair in the present guarded improper setting. -/
noncomputable abbrev helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) : (Fin n → ℝ) → EReal :=
  fun z =>
    functionInfimumEReal
      (helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
        F G yStar uStar z)

/-- Helper for Theorem 38.5: at `z = 0`, the corrected second-shift guarded perturbation reduces
pointwise to the guarded primal objective `commonBookEffectiveDomainDifference f g`. -/
lemma helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw_zero
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (x : Fin n → ℝ) :
    helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar 0 x =
      commonBookEffectiveDomainDifference
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
        x := by
  by_cases hx :
      x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∩
        concaveEffectiveDomain
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
  · have hx' :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∧
          (x + (0 : Fin n → ℝ)) ∈
            concaveEffectiveDomain
              (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
      simpa using hx
    have hzero : x + (0 : Fin n → ℝ) = x := by
      ext i
      simp
    have hx'' :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∧
          x ∈ concaveEffectiveDomain
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
      simpa [hzero] using hx'
    simp [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, hx'', hx, hzero,
      commonBookEffectiveDomainDifference]
  · have hx' :
        ¬ (x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∧
            (x + (0 : Fin n → ℝ)) ∈
              concaveEffectiveDomain
                (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))) := by
      simpa using hx
    have hzero : x + (0 : Fin n → ℝ) = x := by
      ext i
      simp
    have hx'' :
        ¬ (x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∧
            x ∈ concaveEffectiveDomain
              (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))) := by
      simpa [hzero] using hx'
    simp [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, hx'', hx, hzero,
      commonBookEffectiveDomainDifference]

/-- Helper for Theorem 38.5: the corrected second-shift guarded translated value recovers the
Fenchel primal infimum at `z = 0`, exactly as in the original text. -/
lemma helperForTheorem_38_5_textbookSecondShiftGuardedValueAtZero_eq_fenchelPrimalInfimum
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar 0 =
      fenchelPrimalInfimum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
  rw [helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction, fenchelPrimalInfimum,
    functionInfimumEReal]
  refine iInf_congr ?_
  intro x
  exact
    helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw_zero
      (F := F) (G := G) (yStar := yStar) (uStar := uStar) x

/-- Helper for Theorem 38.5: the qualification hypothesis gives an actual finite section witness
for the corrected second-shift perturbation at `z = 0`. This is the theorem-local "consistency at
the origin" datum that the original Chapter 31 perturbation route needs. -/
lemma helperForTheorem_38_5_textbookSecondShiftGuardedOriginConsistent_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    ∃ x0 : Fin n → ℝ,
      helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
          F G yStar uStar 0 x0 < ⊤ := by
  have hFenchelA :
      FenchelConditionA (n := n)
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
    exact
      helperForTheorem_38_5_hri_implies_fenchelConditionA
        (F := F) (G := G) (yStar := yStar) (uStar := uStar) hri
  rcases hFenchelA with ⟨x0, hx0riF, hx0riG⟩
  have hx0F :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) :=
    helperForTheorem_21_1_riFin_subset_C (n := n)
      (effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))) hx0riF
  have hx0G :
      x0 ∈ concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) :=
    helperForTheorem_21_1_riFin_subset_C (n := n)
      (concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))) hx0riG
  have hx0Common :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∩
        concaveEffectiveDomain
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) :=
    ⟨hx0F, hx0G⟩
  have hneTop :
      helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
          F G yStar uStar 0 x0 ≠ (⊤ : EReal) := by
    rw [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw_zero
      (F := F) (G := G) (yStar := yStar) (uStar := uStar) (x := x0)]
    have hmid_ne_top :
        helperForTheorem_38_5_middleReducedObjective F G yStar uStar x0 ≠ (⊤ : EReal) :=
      by
        have hfx_ne_top :
            helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x0 ≠ (⊤ : EReal) :=
          mem_effectiveDomain_imp_ne_top
            (S := (Set.univ : Set (Fin n → ℝ)))
            (f := helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) hx0Common.1
        have hgx_ne_bot :
            helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0 ≠ (⊥ : EReal) := by
          intro hgx_bot
          have hxG' :
              x0 ∈ (Set.univ : Set (Fin n → ℝ)) ∧
                (-(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0)) <
                  (⊤ : EReal) := by
            simpa [concaveEffectiveDomain, effectiveDomain_eq] using hx0Common.2
          have :
              -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0) =
                (⊤ : EReal) := by
            simpa [hgx_bot] using
              (show -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0) =
                  (-(⊥ : EReal)) from rfl)
          exact (lt_top_iff_ne_top).1 hxG'.2 (by simpa [this])
        have hSample_ne_top :
            commonBookEffectiveDomainDifference
                (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
                (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
                x0 ≠ (⊤ : EReal) := by
          rw [commonBookEffectiveDomainDifference, if_pos hx0Common]
          cases hfx :
              helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x0 with
          | top =>
              exact (hfx_ne_top hfx).elim
          | bot =>
              cases hgx :
                  helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0 with
              | bot =>
                  exact (hgx_ne_bot hgx).elim
              | top =>
                  simp
              | coe s =>
                  simp
          | coe r =>
              cases hgx :
                  helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0 with
              | bot =>
                  exact (hgx_ne_bot hgx).elim
              | top =>
                  simp
              | coe s =>
                  simpa [hfx, hgx, EReal.coe_sub] using (EReal.coe_ne_top (r - s))
        have hEq :=
          helperForTheorem_38_5_middleReducedObjective_eq_commonBookEffectiveDomainDifference
            (F := F) (G := G) (yStar := yStar) (uStar := uStar) (x := x0)
        intro htop
        exact hSample_ne_top (by simpa [hEq] using htop)
    exact
      hmid_ne_top ∘
        (by
          intro h
          simpa [helperForTheorem_38_5_middleReducedObjective_eq_commonBookEffectiveDomainDifference
            (F := F) (G := G) (yStar := yStar) (uStar := uStar) (x := x0)] using h)
  exact ⟨x0, lt_top_iff_ne_top.mpr hneTop⟩

/-- Helper for Theorem 38.5: under the qualification hypothesis, the corrected second-shift
translated value at the origin is not `⊤`. This is the precise origin-consistency bridge needed
for the finite branch of the original-text perturbation route. -/
lemma helperForTheorem_38_5_textbookSecondShiftGuardedValueAtZero_ne_top_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar 0 ≠
      (⊤ : EReal) := by
  rcases
      helperForTheorem_38_5_textbookSecondShiftGuardedOriginConsistent_of_hri
        (F := F) (G := G) (yStar := yStar) (uStar := uStar) hri with
    ⟨x0, hx0lt⟩
  have hLe :
      helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar 0 ≤
        helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
          F G yStar uStar 0 x0 := by
    rw [helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction, functionInfimumEReal]
    exact
      iInf_le
        (helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
          F G yStar uStar 0) x0
  exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hLe hx0lt)

/-- Helper for Theorem 38.5: the corrected guarded perturbation is exactly the second-shift
middle reduced objective, i.e. the partial infimum over `(u, y)` with the `G` term evaluated at
`x + z`. This isolates the remaining convexity work from the `if ... then ... else ⊤` wrapper. -/
lemma helperForTheorem_38_5_secondShiftMiddleReducedObjective_eq_textbookSecondShiftGuardedPerturbationRaw
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (z x : Fin n → ℝ) :
    helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar z x =
      helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar z x := by
  let f : (Fin n → ℝ) → EReal :=
    helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)
  let g : (Fin n → ℝ) → EReal :=
    helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)
  by_cases hx :
      x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
        (x + z) ∈ concaveEffectiveDomain g
  · have hxF : x ∈ bifunctionDomBot (bifunctionInverse F.toFun) := by
      simpa [f, helperForTheorem_38_5_textbookPrimalMiddleFunction_effectiveDomain] using hx.1
    have hxG : x + z ∈ bifunctionDom G.toFun := by
      simpa [g, helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain] using
        hx.2
    have hPrimalFinite : ∃ u : Fin m → ℝ, (-((uStar u : ℝ) : EReal)) + F.toFun u x < ⊤ := by
      simp [bifunctionDomBot, bifunctionInverse] at hxF
      rcases hxF with ⟨u, hu⟩
      refine ⟨u, lt_top_iff_ne_top.mpr ?_⟩
      exact EReal.add_ne_top (EReal.coe_ne_top _) hu
    have hDualFinite : ∃ y : Fin p → ℝ, ((yStar y : ℝ) : EReal) + G.toFun (x + z) y < ⊤ := by
      simp [bifunctionDom] at hxG
      rcases hxG with ⟨y, hy⟩
      refine ⟨y, lt_top_iff_ne_top.mpr ?_⟩
      exact EReal.add_ne_top (EReal.coe_ne_top _) hy
    simp [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, f, g, hx]
    simpa [f, g, sub_eq_add_neg] using
      helperForTheorem_38_5_secondShiftMiddleReducedObjective_eq_textbookPieces
        (F := F) (G := G) (yStar := yStar) (uStar := uStar) (z := z) (x := x)
        hPrimalFinite hDualFinite
  · have hx' :
        x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∨
          (x + z) ∉ concaveEffectiveDomain g := by
      exact not_and_or.mp hx
    simp [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, f, g, hx]
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
      rw [helperForTheorem_38_5_secondShiftMiddleReducedObjective]
      apply le_antisymm le_top
      refine le_iInf ?_
      intro u
      refine le_iInf ?_
      intro y
      have hG_ne_bot : G.toFun (x + z) y ≠ (⊥ : EReal) := G.proper.1 (x + z) y
      have hTopInner : F.toFun u x + G.toFun (x + z) y = (⊤ : EReal) := by
        simpa [hAllTopF u] using EReal.top_add_of_ne_bot hG_ne_bot
      have hCoeff_ne_bot :
          (((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal))) ≠ (⊥ : EReal) := by
        exact add_ne_bot_of_notbot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _)
      have hTerm :
          ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
              (F.toFun u x + G.toFun (x + z) y) =
            (⊤ : EReal) := by
        simp [hTopInner, EReal.add_top_of_ne_bot hCoeff_ne_bot]
      rw [hTerm]
    · have hxDom : x + z ∉ bifunctionDom G.toFun := by
        simpa [g, helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain] using
          hxG
      have hAllTopG : ∀ y : Fin p → ℝ, G.toFun (x + z) y = (⊤ : EReal) := by
        intro y
        by_contra hy
        exact hxDom ⟨y, hy⟩
      rw [helperForTheorem_38_5_secondShiftMiddleReducedObjective]
      apply le_antisymm le_top
      refine le_iInf ?_
      intro u
      refine le_iInf ?_
      intro y
      have hF_ne_bot : F.toFun u x ≠ (⊥ : EReal) := F.proper.1 u x
      have hTopInner : F.toFun u x + G.toFun (x + z) y = (⊤ : EReal) := by
        simpa [hAllTopG y] using EReal.add_top_of_ne_bot hF_ne_bot
      have hCoeff_ne_bot :
          (((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal))) ≠ (⊥ : EReal) := by
        exact add_ne_bot_of_notbot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _)
      have hTerm :
          ((yStar y : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
              (F.toFun u x + G.toFun (x + z) y) =
            (⊤ : EReal) := by
        simp [hTopInner, EReal.add_top_of_ne_bot hCoeff_ne_bot]
      rw [hTerm]

/-- Helper for Theorem 38.5: if the endpoint guards hold for the corrected second-shift
perturbation, then the same guard holds at their convex combination. -/
lemma helperForTheorem_38_5_secondShiftGuard_convexCombination
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    {z₁ z₂ x₁ x₂ : Fin n → ℝ} {a b : ℝ}
    (hx₁ :
      x₁ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)))
    (hx₂ :
      x₂ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)))
    (hxz₁ :
      x₁ + z₁ ∈ concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)))
    (hxz₂ :
      x₂ + z₂ ∈ concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x₁ + b • x₂ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∧
      (a • x₁ + b • x₂) + (a • z₁ + b • z₂) ∈
        concaveEffectiveDomain
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
  -- The first guard component is the convex effective domain of the primal middle function.
  have hConvF :
      Convex ℝ
        (effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))) := by
    have hconv :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) :=
      helperForTheorem_38_5_textbookPrimalMiddleFunction_convexOn
        (F := F) (uStar := -uStar) hF_properConvex
    exact
      effectiveDomain_convex
        (S := (Set.univ : Set (Fin n → ℝ)))
        (f := helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) hconv
  -- The second guard component is the convex domain of the shifted concave middle function.
  have hConvG :
      Convex ℝ
        (concaveEffectiveDomain
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))) := by
    have hconv :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (fun x : Fin n → ℝ =>
            -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x)) :=
      helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_convexOn
        (G := G) (yStar := yStar) hG_properConvex
    simpa [concaveEffectiveDomain] using
      effectiveDomain_convex
        (S := (Set.univ : Set (Fin n → ℝ)))
        (f := fun x : Fin n → ℝ =>
          -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x)) hconv
  refine ⟨?_, ?_⟩
  · -- Convexity of `dom f` keeps the `x`-component admissible.
    exact hConvF hx₁ hx₂ ha hb hab
  · -- Rewrite the shifted point as the convex combination of the shifted endpoints.
    have hShift :
        (a • x₁ + b • x₂) + (a • z₁ + b • z₂) =
          a • (x₁ + z₁) + b • (x₂ + z₂) := by
      ext i
      simp
      ring
    rw [hShift]
    exact hConvG hxz₁ hxz₂ ha hb hab

/-- Helper for Theorem 38.5: on the guarded finite branch, the corrected second-shift
perturbation satisfies the textbook Jensen inequality obtained by adding the convex Jensen
inequalities for the primal middle function and the negated dual middle function. -/
lemma helperForTheorem_38_5_secondShiftGuarded_nonexceptional_jensen
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    {z₁ z₂ x₁ x₂ : Fin n → ℝ} {a b : ℝ}
    (hx₁ :
      x₁ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)))
    (hx₂ :
      x₂ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)))
    (hxz₁ :
      x₁ + z₁ ∈ concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)))
    (hxz₂ :
      x₂ + z₂ ∈ concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)))
    (haPos : 0 < a) (hbPos : 0 < b) (hab : a + b = 1)
    (hx₁_ne_bot :
      helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x₁ ≠ ⊥)
    (hx₂_ne_bot :
      helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x₂ ≠ ⊥)
    (hxz₁_ne_top :
      helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) (x₁ + z₁) ≠ ⊤)
    (hxz₂_ne_top :
      helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) (x₂ + z₂) ≠ ⊤) :
    helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
        F G yStar uStar (a • z₁ + b • z₂) (a • x₁ + b • x₂) ≤
      ((a : ℝ) : EReal) *
          helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
            F G yStar uStar z₁ x₁ +
        ((b : ℝ) : EReal) *
          helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
            F G yStar uStar z₂ x₂ := by
  let f : (Fin n → ℝ) → EReal :=
    helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)
  let h : (Fin n → ℝ) → EReal :=
    fun x => -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x)
  have ha : 0 ≤ a := le_of_lt haPos
  have hb : 0 ≤ b := le_of_lt hbPos
  have hGuardMid :=
    helperForTheorem_38_5_secondShiftGuard_convexCombination
      (F := F) (G := G) (yStar := yStar) (uStar := uStar)
      hF_properConvex hG_properConvex hx₁ hx₂ hxz₁ hxz₂ ha hb hab
  have hConvF : Convex ℝ (epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
    -- The primal middle function is convex on all of `ℝ^n`, so its epigraph is convex.
    simpa [ConvexFunctionOn, f] using
      helperForTheorem_38_5_textbookPrimalMiddleFunction_convexOn
        (F := F) (uStar := -uStar) hF_properConvex
  have hConvH : Convex ℝ (epigraph (Set.univ : Set (Fin n → ℝ)) h) := by
    -- The negated dual middle function is the second convex summand in the textbook formula.
    simpa [ConvexFunctionOn, h] using
      helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_convexOn
        (G := G) (yStar := yStar) hG_properConvex
  have ha_eq : a = 1 - b := by linarith
  have hb_le_one : b ≤ 1 := by linarith
  have hf₁_ne_top : f x₁ ≠ ⊤ := by
    rw [effectiveDomain_eq] at hx₁
    exact lt_top_iff_ne_top.mp hx₁.2
  have hf₂_ne_top : f x₂ ≠ ⊤ := by
    rw [effectiveDomain_eq] at hx₂
    exact lt_top_iff_ne_top.mp hx₂.2
  have hxz₁_lt : h (x₁ + z₁) < ⊤ := by
    simpa [h, concaveEffectiveDomain, effectiveDomain_eq] using hxz₁
  have hxz₂_lt : h (x₂ + z₂) < ⊤ := by
    simpa [h, concaveEffectiveDomain, effectiveDomain_eq] using hxz₂
  have hh₁_ne_top : h (x₁ + z₁) ≠ ⊤ := by
    exact lt_top_iff_ne_top.mp hxz₁_lt
  have hh₂_ne_top : h (x₂ + z₂) ≠ ⊤ := by
    exact lt_top_iff_ne_top.mp hxz₂_lt
  have hh₁_ne_bot : h (x₁ + z₁) ≠ ⊥ := by
    simpa [h] using hxz₁_ne_top
  have hh₂_ne_bot : h (x₂ + z₂) ≠ ⊥ := by
    simpa [h] using hxz₂_ne_top
  let rf₁ : ℝ := (f x₁).toReal
  let rf₂ : ℝ := (f x₂).toReal
  let rh₁ : ℝ := (h (x₁ + z₁)).toReal
  let rh₂ : ℝ := (h (x₂ + z₂)).toReal
  have hrh₁ : ((rh₁ : ℝ) : EReal) = h (x₁ + z₁) := by
    simp [rh₁, EReal.coe_toReal hh₁_ne_top hh₁_ne_bot]
  have hrh₂ : ((rh₂ : ℝ) : EReal) = h (x₂ + z₂) := by
    simp [rh₂, EReal.coe_toReal hh₂_ne_top hh₂_ne_bot]
  have hfJensen :
      f (a • x₁ + b • x₂) ≤
        ((a : ℝ) : EReal) * f x₁ + ((b : ℝ) : EReal) * f x₂ := by
    -- Compare `f` with the real epigraph heights obtained from the finite endpoint values.
    have hbase :=
      epigraph_combo_ineq_aux (S := (Set.univ : Set (Fin n → ℝ))) (f := f)
        (x := x₁) (y := x₂) (μ := rf₁) (v := rf₂) (t := b)
        hConvF (by simp) (by simp)
        (by
          simpa [rf₁, f] using
            (EReal.le_coe_toReal hf₁_ne_top))
        (by
          simpa [rf₂, f] using
            (EReal.le_coe_toReal hf₂_ne_top))
        hb hb_le_one
    calc
      f (a • x₁ + b • x₂) = f ((1 - b) • x₁ + b • x₂) := by simp [ha_eq]
      _ ≤ (((1 - b) * rf₁ + b * rf₂ : ℝ) : EReal) := hbase
      _ = ((a : ℝ) : EReal) * f x₁ + ((b : ℝ) : EReal) * f x₂ := by
        rw [ha_eq]
        simp [rf₁, rf₂, f, EReal.coe_toReal hf₁_ne_top hx₁_ne_bot,
          EReal.coe_toReal hf₂_ne_top hx₂_ne_bot, EReal.coe_add, EReal.coe_mul]
  have hShift :
      a • (x₁ + z₁) + b • (x₂ + z₂) =
        (a • x₁ + b • x₂) + (a • z₁ + b • z₂) := by
    -- The shifted middle variable is the convex combination of the shifted endpoints.
    ext i
    simp [smul_add]
    ring
  have hhJensen :
      h ((a • x₁ + b • x₂) + (a • z₁ + b • z₂)) ≤
        ((a : ℝ) : EReal) * h (x₁ + z₁) + ((b : ℝ) : EReal) * h (x₂ + z₂) := by
    -- Apply the same epigraph argument to `-g`.
    have hbase :=
      epigraph_combo_ineq_aux (S := (Set.univ : Set (Fin n → ℝ))) (f := h)
        (x := x₁ + z₁) (y := x₂ + z₂) (μ := rh₁) (v := rh₂) (t := b)
        hConvH (by simp) (by simp)
        (by
          simpa [rh₁, h] using
            (EReal.le_coe_toReal hh₁_ne_top))
        (by
          simpa [rh₂, h] using
            (EReal.le_coe_toReal hh₂_ne_top))
        hb hb_le_one
    calc
      h ((a • x₁ + b • x₂) + (a • z₁ + b • z₂)) =
          h (a • (x₁ + z₁) + b • (x₂ + z₂)) := by rw [← hShift]
      _ = h ((1 - b) • (x₁ + z₁) + b • (x₂ + z₂)) := by simp [ha_eq]
      _ ≤ (((1 - b) * rh₁ + b * rh₂ : ℝ) : EReal) := hbase
      _ = ((a : ℝ) : EReal) * h (x₁ + z₁) + ((b : ℝ) : EReal) * h (x₂ + z₂) := by
        rw [ha_eq]
        simp [hrh₁, hrh₂, EReal.coe_add, EReal.coe_mul]
  have hSum :
      f (a • x₁ + b • x₂) + h ((a • x₁ + b • x₂) + (a • z₁ + b • z₂)) ≤
        (((a : ℝ) : EReal) * f x₁ + ((b : ℝ) : EReal) * f x₂) +
          (((a : ℝ) : EReal) * h (x₁ + z₁) + ((b : ℝ) : EReal) * h (x₂ + z₂)) := by
    -- Add the two one-variable Jensen inequalities to recover the bifunction estimate.
    exact add_le_add hfJensen hhJensen
  have hDistrib₁ :
      ((a : ℝ) : EReal) *
          helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar z₁ x₁ =
        ((a : ℝ) : EReal) * f x₁ + ((a : ℝ) : EReal) * h (x₁ + z₁) := by
    -- On the guarded finite branch, the endpoint value is exactly `f + (-g)`.
    have hx₁_guard :
        x₁ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
          (x₁ + z₁) ∈ concaveEffectiveDomain
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
      simpa [f] using And.intro hx₁ hxz₁
    calc
      ((a : ℝ) : EReal) *
          helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar z₁ x₁ =
          ((a : ℝ) : EReal) * (f x₁ + h (x₁ + z₁)) := by
            simp [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, hx₁_guard,
              f, h, sub_eq_add_neg]
      _ = ((a : ℝ) : EReal) * f x₁ + ((a : ℝ) : EReal) * h (x₁ + z₁) := by
            simpa using
              (EReal.left_distrib_of_nonneg_of_ne_top
                (by exact_mod_cast ha)
                (EReal.coe_ne_top a)
                (f x₁) (h (x₁ + z₁)))
  have hDistrib₂ :
      ((b : ℝ) : EReal) *
          helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar z₂ x₂ =
        ((b : ℝ) : EReal) * f x₂ + ((b : ℝ) : EReal) * h (x₂ + z₂) := by
    -- The same scalar distribution handles the second endpoint.
    have hx₂_guard :
        x₂ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
          (x₂ + z₂) ∈ concaveEffectiveDomain
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
      simpa [f] using And.intro hx₂ hxz₂
    calc
      ((b : ℝ) : EReal) *
          helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar z₂ x₂ =
          ((b : ℝ) : EReal) * (f x₂ + h (x₂ + z₂)) := by
            simp [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, hx₂_guard,
              f, h, sub_eq_add_neg]
      _ = ((b : ℝ) : EReal) * f x₂ + ((b : ℝ) : EReal) * h (x₂ + z₂) := by
            simpa using
              (EReal.left_distrib_of_nonneg_of_ne_top
                (by exact_mod_cast hb)
                (EReal.coe_ne_top b)
                (f x₂) (h (x₂ + z₂)))
  have hGuardMid' :
      (a • x₁ + b • x₂) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
        ((a • x₁ + b • x₂) + (a • z₁ + b • z₂)) ∈
          concaveEffectiveDomain
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
    simpa [f] using hGuardMid
  calc
    helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
        F G yStar uStar (a • z₁ + b • z₂) (a • x₁ + b • x₂) =
        f (a • x₁ + b • x₂) +
          h ((a • x₁ + b • x₂) + (a • z₁ + b • z₂)) := by
            simp [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, hGuardMid',
              f, h, sub_eq_add_neg]
    _ ≤ (((a : ℝ) : EReal) * f x₁ + ((b : ℝ) : EReal) * f x₂) +
          (((a : ℝ) : EReal) * h (x₁ + z₁) + ((b : ℝ) : EReal) * h (x₂ + z₂)) := hSum
    _ = ((a : ℝ) : EReal) *
          helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
            F G yStar uStar z₁ x₁ +
        ((b : ℝ) : EReal) *
          helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
            F G yStar uStar z₂ x₂ := by
          rw [hDistrib₁, hDistrib₂]
          simp [add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 38.5: if the first guarded endpoint already has primal value `⊥`, then
convexity of the primal middle function forces the guarded midpoint value to collapse to `⊥`. -/
lemma helperForTheorem_38_5_secondShiftGuarded_primalBot_collapse
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    {z₁ z₂ x₁ x₂ : Fin n → ℝ} {a b : ℝ}
    (hx₁ :
      x₁ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)))
    (hx₂ :
      x₂ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)))
    (hxz₁ :
      x₁ + z₁ ∈ concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)))
    (hxz₂ :
      x₂ + z₂ ∈ concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)))
    (haPos : 0 < a) (hbPos : 0 < b) (hab : a + b = 1)
    (hx₁_bot :
      helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x₁ = ⊥) :
    helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
        F G yStar uStar (a • z₁ + b • z₂) (a • x₁ + b • x₂) = ⊥ := by
  let f : (Fin n → ℝ) → EReal :=
    helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)
  have hGuardMid :=
    helperForTheorem_38_5_secondShiftGuard_convexCombination
      (F := F) (G := G) (yStar := yStar) (uStar := uStar)
      hF_properConvex hG_properConvex hx₁ hx₂ hxz₁ hxz₂ (le_of_lt haPos) (le_of_lt hbPos) hab
  have hConvFun : ConvexFunction f := by
    -- Repackage convexity on `Set.univ` as a global convex function statement.
    simpa [ConvexFunction, f] using
      helperForTheorem_38_5_textbookPrimalMiddleFunction_convexOn
        (F := F) (uStar := -uStar) hF_properConvex
  have hf₂_ne_top : f x₂ ≠ ⊤ := by
    rw [effectiveDomain_eq] at hx₂
    exact lt_top_iff_ne_top.mp hx₂.2
  have hMidBot :
      f (a • x₁ + b • x₂) = ⊥ := by
    -- A positive weight on a `⊥` endpoint forces every strict convex combination back to `⊥`.
    exact helperForLemma33_0_5_convexFunction_leftBot_rightNotTop_forces_comboBot
      (g := f) hConvFun (le_of_lt haPos) (le_of_lt hbPos) hab haPos
      (by simpa [f] using hx₁_bot) hf₂_ne_top
  have hGuardMid' :
      (a • x₁ + b • x₂) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
        ((a • x₁ + b • x₂) + (a • z₁ + b • z₂)) ∈
          concaveEffectiveDomain
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
    simpa [f] using hGuardMid
  -- Once the midpoint primal term is `⊥`, the guarded perturbation value is automatically `⊥`.
  simp [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, hGuardMid',
    hMidBot, f, sub_eq_add_neg]

/-- Helper for Theorem 38.5: if the shifted dual value at the first guarded endpoint is `⊤`,
then convexity of the negated dual middle function forces the guarded midpoint value to collapse
to `⊥`. -/
lemma helperForTheorem_38_5_secondShiftGuarded_shiftedDualTop_collapse
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    {z₁ z₂ x₁ x₂ : Fin n → ℝ} {a b : ℝ}
    (hx₁ :
      x₁ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)))
    (hx₂ :
      x₂ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)))
    (hxz₁ :
      x₁ + z₁ ∈ concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)))
    (hxz₂ :
      x₂ + z₂ ∈ concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)))
    (haPos : 0 < a) (hbPos : 0 < b) (hab : a + b = 1)
    (hxz₁_top :
      helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) (x₁ + z₁) = ⊤) :
    helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
        F G yStar uStar (a • z₁ + b • z₂) (a • x₁ + b • x₂) = ⊥ := by
  let f : (Fin n → ℝ) → EReal :=
    helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)
  let h : (Fin n → ℝ) → EReal :=
    fun x => -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x)
  have hGuardMid :=
    helperForTheorem_38_5_secondShiftGuard_convexCombination
      (F := F) (G := G) (yStar := yStar) (uStar := uStar)
      hF_properConvex hG_properConvex hx₁ hx₂ hxz₁ hxz₂ (le_of_lt haPos) (le_of_lt hbPos) hab
  have hConvFun : ConvexFunction h := by
    -- The shifted dual contribution enters through the convex function `x ↦ -g(x)`.
    simpa [ConvexFunction, h] using
      helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_convexOn
        (G := G) (yStar := yStar) hG_properConvex
  have hh₂_ne_top : h (x₂ + z₂) ≠ ⊤ := by
    simp [h, concaveEffectiveDomain, effectiveDomain_eq] at hxz₂
    simpa [h] using (lt_top_iff_ne_top.mp hxz₂)
  have hh₁_bot : h (x₁ + z₁) = ⊥ := by
    simpa [h] using hxz₁_top
  have hShift :
      a • (x₁ + z₁) + b • (x₂ + z₂) =
        (a • x₁ + b • x₂) + (a • z₁ + b • z₂) := by
    -- The shifted point is exactly the convex combination of the shifted endpoints.
    ext i
    simp [smul_add]
    ring
  have hMidBot :
      h ((a • x₁ + b • x₂) + (a • z₁ + b • z₂)) = ⊥ := by
    have hRawBot :
        h (a • (x₁ + z₁) + b • (x₂ + z₂)) = ⊥ := by
      exact helperForLemma33_0_5_convexFunction_leftBot_rightNotTop_forces_comboBot
        (g := h) hConvFun (le_of_lt haPos) (le_of_lt hbPos) hab haPos hh₁_bot hh₂_ne_top
    rw [hShift] at hRawBot
    exact hRawBot
  have hxzMid_top :
      helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)
          ((a • x₁ + b • x₂) + (a • z₁ + b • z₂)) = ⊤ := by
    -- Undo the negation to recover the original dual top value at the midpoint.
    have := congrArg Neg.neg hMidBot
    simpa [h] using this
  have hGuardMid' :
      (a • x₁ + b • x₂) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
        ((a • x₁ + b • x₂) + (a • z₁ + b • z₂)) ∈
          concaveEffectiveDomain
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
    simpa [f] using hGuardMid
  -- Once the midpoint dual term is `⊤`, the guarded perturbation value is again `⊥`.
  simp [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, hGuardMid',
    hxzMid_top, f, sub_eq_add_neg]


end Section38
end Chap08
