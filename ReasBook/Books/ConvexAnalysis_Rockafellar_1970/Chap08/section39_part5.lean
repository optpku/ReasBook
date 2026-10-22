/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part4

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

section Chap08
section Section39

namespace ConvexProcess

/-- The oriented bracket of a set `S ⊆ ℝ^n` against a vector `x* ∈ ℝ^n`, using `sup` for supremum
orientation and `inf` for infimum orientation:
`⟪S, x*⟫ = sup { finDot x x* | x ∈ S }` or `inf { finDot x x* | x ∈ S }`. -/
noncomputable def setBracketVec {n : ℕ} (o : ConvexSetOrientation) (S : Set (Fin n → ℝ))
    (xStar : Fin n → ℝ) : EReal :=
  match o with
  | .supremum => sSup ((fun x => ((finDot x xStar : ℝ) : EReal)) '' S)
  | .infimum => sInf ((fun x => ((finDot x xStar : ℝ) : EReal)) '' S)

/-- The oriented Fenchel-style bracket of an `EReal`-valued function `f : ℝ^n → EReal` against
`x* ∈ ℝ^n`, defined as `sup_x (finDot x x* - f x)` in supremum orientation and
`inf_x (finDot x x* - f x)` in infimum orientation. -/
noncomputable def eRealFunctionBracketVec {n : ℕ} (o : ConvexSetOrientation)
    (f : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) : EReal :=
  match o with
  | .supremum => sSup ((fun x => ((finDot x xStar : ℝ) : EReal) - f x) '' (Set.univ : Set (Fin n → ℝ)))
  | .infimum => sInf ((fun x => ((finDot x xStar : ℝ) : EReal) - f x) '' (Set.univ : Set (Fin n → ℝ)))

/-- The oriented bracket of an `EReal`-valued bifunction `F : ℝ^m → ℝ^n → EReal` against `x* ∈ ℝ^n`,
evaluated at a fixed `u`. -/
noncomputable def eRealBifunctionBracketVec {m n : ℕ} (o : ConvexSetOrientation)
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (u : Fin m → ℝ) (xStar : Fin n → ℝ) : EReal :=
  eRealFunctionBracketVec o (F u) xStar

-- Proof sketch: The `A** = cl A` identity is the corresponding component of Theorem 39.2.
-- For the bracket identity, unfold the two bracket definitions and the oriented indicator
-- bifunction; then use that the Fenchel bracket of an indicator function (resp. negative indicator)
-- is the support (resp. inf-support) function of the underlying set.
/-- Definition 39.2.1: The infimum-oriented case is analogous. One has `A** = cl A`, which can be
derived from the corresponding biconjugacy/closure identity for the (oriented) indicator
bifunction. Moreover, if an oriented convex process `A` has oriented indicator bifunction `F`, then
`⟪A u, x*⟫ = ⟪F u, x*⟫` for all `u` and `x*`. -/
theorem doubleAdjoint_eq_closure_and_bracket_eq_indicator {m n : ℕ} (o : ConvexSetOrientation)
    (A : ConvexProcess m n) :
    doubleAdjointVecSetValuedOriented o A = (A.cl).toSetValued ∧
      ∀ u xStar,
        setBracketVec o (A.toSetValued u) xStar =
          eRealBifunctionBracketVec o (indicatorBifunctionOriented o A) u xStar := by
  constructor
  · exact
      (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint o A).2.2.2.1
  · intro u xStar
    cases o
    · unfold setBracketVec eRealBifunctionBracketVec eRealFunctionBracketVec indicatorBifunctionOriented
      let φ : (Fin n → ℝ) → EReal :=
        fun x => (((finDot x xStar : ℝ) : EReal)) - indicatorEReal (A.toSetValued u) x
      apply le_antisymm
      · refine sSup_le ?_
        rintro r ⟨x, hx, rfl⟩
        by_cases hmem : x ∈ A.toSetValued u
        · have hsup :
              (((finDot x xStar : ℝ) : EReal)) ≤
                sSup (φ '' (Set.univ : Set (Fin n → ℝ))) := by
            have hφ : φ x ≤ sSup (φ '' (Set.univ : Set (Fin n → ℝ))) :=
              le_sSup ⟨x, by simp, rfl⟩
            simpa [φ, indicatorEReal, hmem] using hφ
          simpa using hsup
        · exact (hmem hx).elim
      · refine sSup_le ?_
        rintro r ⟨x, hx, rfl⟩
        by_cases hmem : x ∈ A.toSetValued u
        · have hsup :
              (((finDot x xStar : ℝ) : EReal)) ≤
                sSup ((fun x : Fin n → ℝ => (((finDot x xStar : ℝ) : EReal))) '' (A.toSetValued u)) :=
              le_sSup ⟨x, hmem, rfl⟩
          simpa [φ, ConvexProcess.indicatorBifunction, indicatorEReal, hmem] using hsup
        · simp [φ, ConvexProcess.indicatorBifunction, indicatorEReal, hmem]
    · unfold setBracketVec eRealBifunctionBracketVec eRealFunctionBracketVec indicatorBifunctionOriented
      let φ : (Fin n → ℝ) → EReal :=
        fun x => (((finDot x xStar : ℝ) : EReal)) - negIndicatorEReal (A.toSetValued u) x
      apply le_antisymm
      · refine le_sInf ?_
        rintro r ⟨x, -, rfl⟩
        by_cases hmem : x ∈ A.toSetValued u
        · have hinf :
              sInf ((fun x : Fin n → ℝ => (((finDot x xStar : ℝ) : EReal))) '' (A.toSetValued u)) ≤
                (((finDot x xStar : ℝ) : EReal)) :=
              sInf_le ⟨x, hmem, rfl⟩
          simpa [φ, ConvexProcess.negIndicatorBifunction, negIndicatorEReal, hmem] using hinf
        · simp [φ, ConvexProcess.negIndicatorBifunction, negIndicatorEReal, hmem]
      · refine le_sInf ?_
        rintro r ⟨x, hx, rfl⟩
        have hφ : sInf (φ '' (Set.univ : Set (Fin n → ℝ))) ≤ φ x :=
          sInf_le ⟨x, by simp, rfl⟩
        simpa [φ, ConvexProcess.negIndicatorBifunction, negIndicatorEReal, hx] using hφ

/-- The hypograph of an `EReal`-valued function `f : X → EReal`, as a subset of `X × ℝ`. -/
def eRealHypograph {X : Type*} (f : X → EReal) : Set (X × ℝ) :=
  { p | (p.2 : EReal) ≤ f p.1 }

/-- Concavity of an `EReal`-valued function, defined as convexity of its hypograph. -/
def IsConcaveEReal {X : Type*} [AddCommGroup X] [Module ℝ X] (f : X → EReal) : Prop :=
  Convex ℝ (eRealHypograph f)

/-- Upper closedness of an `EReal`-valued function, defined as topological closedness of its
hypograph in `X × ℝ`. -/
def IsUpperClosedEReal {X : Type*} [TopologicalSpace X] (f : X → EReal) : Prop :=
  _root_.IsClosed (eRealHypograph f)

/-- Positive homogeneity for `EReal`-valued functions with respect to scaling by strictly positive
real scalars. -/
def IsPosHomogeneousEReal {X : Type*} [SMul ℝ X] (f : X → EReal) : Prop :=
  ∀ x (t : ℝ), 0 < t → f (t • x) = (t : EReal) * f x

/-- Helper for Theorem 39.3: scaling the covector by a positive real scalar scales the oriented
set bracket by the same factor. -/
lemma helperForTheorem_39_3_bracket_covector_smul_pos {n : ℕ}
    (o : ConvexSetOrientation) (S : Set (Fin n → ℝ)) (xStar : Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) :
    setBracketVec o S (t • xStar) = (t : EReal) * setBracketVec o S xStar := by
  -- Step 1: rewrite the dot-product image under the positive scaling map on the covector.
  cases o
  · unfold setBracketVec
    have hImg :
        ((fun x => ((finDot x (t • xStar) : ℝ) : EReal)) '' S) =
          ((fun z : EReal => (t : EReal) * z) ''
            ((fun x => ((finDot x xStar : ℝ) : EReal)) '' S)) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨((finDot x xStar : ℝ) : EReal), ⟨x, hx, rfl⟩, ?_⟩
        simp [finDot, dotProduct_smul, EReal.coe_mul, mul_comm]
      · rintro ⟨z', hz', hz⟩
        rcases hz' with ⟨x, hx, rfl⟩
        refine ⟨x, hx, ?_⟩
        simp [finDot, dotProduct_smul, EReal.coe_mul] at hz ⊢
        exact hz
    rw [hImg]
    have hMonotone : Monotone (fun z : EReal => (t : EReal) * z) := by
      intro a b hab
      exact mul_le_mul_of_nonneg_left hab (by exact_mod_cast (le_of_lt ht))
    have hContinuous :
        ContinuousAt (fun z : EReal => (t : EReal) * z)
          (sSup (((fun x => ((finDot x xStar : ℝ) : EReal)) '' S))) := by
      exact
        (EReal.continuousAt_mul
          (p := ((t : EReal),
            sSup (((fun x => ((finDot x xStar : ℝ) : EReal)) '' S))))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt ht)))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt ht)))
          (Or.inl (by simp))
          (Or.inl (by simp))).comp
          (continuousAt_const.prodMk continuousAt_id)
    have hBot : (t : EReal) * (⊥ : EReal) = ⊥ := by
      simpa using (EReal.coe_mul_bot_of_pos ht)
    simpa using (hMonotone.map_sSup_of_continuousAt hContinuous hBot).symm
  · unfold setBracketVec
    have hImg :
        ((fun x => ((finDot x (t • xStar) : ℝ) : EReal)) '' S) =
          ((fun z : EReal => (t : EReal) * z) ''
            ((fun x => ((finDot x xStar : ℝ) : EReal)) '' S)) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨((finDot x xStar : ℝ) : EReal), ⟨x, hx, rfl⟩, ?_⟩
        simp [finDot, dotProduct_smul, EReal.coe_mul, mul_comm]
      · rintro ⟨z', hz', hz⟩
        rcases hz' with ⟨x, hx, rfl⟩
        refine ⟨x, hx, ?_⟩
        simp [finDot, dotProduct_smul, EReal.coe_mul] at hz ⊢
        exact hz
    rw [hImg]
    have hMonotone : Monotone (fun z : EReal => (t : EReal) * z) := by
      intro a b hab
      exact mul_le_mul_of_nonneg_left hab (by exact_mod_cast (le_of_lt ht))
    have hContinuous :
        ContinuousAt (fun z : EReal => (t : EReal) * z)
          (sInf (((fun x => ((finDot x xStar : ℝ) : EReal)) '' S))) := by
      exact
        (EReal.continuousAt_mul
          (p := ((t : EReal),
            sInf (((fun x => ((finDot x xStar : ℝ) : EReal)) '' S))))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt ht)))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt ht)))
          (Or.inl (by simp))
          (Or.inl (by simp))).comp
          (continuousAt_const.prodMk continuousAt_id)
    have hTop : (t : EReal) * (⊤ : EReal) = ⊤ := by
      simpa using (EReal.coe_mul_top_of_pos ht)
    simpa using (hMonotone.map_sInf_of_continuousAt hContinuous hTop).symm

/-- Helper for Theorem 39.3: scaling the parameter by a positive real scalar scales the oriented
fiber bracket by the same factor. -/
lemma helperForTheorem_39_3_parameterSection_posHomogeneous {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n) (xStar : Fin n → ℝ) :
    IsPosHomogeneousEReal (fun u => setBracketVec o (A.toSetValued u) xStar) := by
  intro u t ht
  -- Step 1: positive homogeneity of the convex process identifies the scaled fiber exactly.
  have hFiber : A.toSetValued (t • u) = t • A.toSetValued u :=
    A.map_smul_pos u t ht
  cases o
  · unfold setBracketVec
    change sSup ((fun x => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued (t • u)) =
      (t : EReal) * sSup ((fun x => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued u)
    rw [hFiber]
    have hImg :
        ((fun x => ((finDot x xStar : ℝ) : EReal)) '' (t • A.toSetValued u)) =
          ((fun z : EReal => (t : EReal) * z) ''
            ((fun x => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued u)) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
        refine ⟨((finDot y xStar : ℝ) : EReal), ?_, ?_⟩
        · exact ⟨y, hy, rfl⟩
        · simp [finDot, dotProduct_smul, EReal.coe_mul, mul_comm]
      · rintro ⟨z', hz', hz⟩
        rcases hz' with ⟨y, hy, rfl⟩
        refine ⟨t • y, ?_, ?_⟩
        · exact Set.mem_smul_set.mpr ⟨y, hy, rfl⟩
        · simp [finDot, smul_dotProduct, EReal.coe_mul, mul_comm] at hz ⊢
          exact hz
    rw [hImg]
    have hMonotone : Monotone (fun z : EReal => (t : EReal) * z) := by
      intro a b hab
      exact mul_le_mul_of_nonneg_left hab (by exact_mod_cast (le_of_lt ht))
    have hContinuous :
        ContinuousAt (fun z : EReal => (t : EReal) * z)
          (sSup (((fun x => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued u))) := by
      exact
        (EReal.continuousAt_mul
          (p := ((t : EReal),
            sSup (((fun x => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued u))))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt ht)))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt ht)))
          (Or.inl (by simp))
          (Or.inl (by simp))).comp
          (continuousAt_const.prodMk continuousAt_id)
    have hBot : (t : EReal) * (⊥ : EReal) = ⊥ := by
      simpa using (EReal.coe_mul_bot_of_pos ht)
    simpa using (hMonotone.map_sSup_of_continuousAt hContinuous hBot).symm
  · unfold setBracketVec
    change sInf ((fun x => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued (t • u)) =
      (t : EReal) * sInf ((fun x => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued u)
    rw [hFiber]
    have hImg :
        ((fun x => ((finDot x xStar : ℝ) : EReal)) '' (t • A.toSetValued u)) =
          ((fun z : EReal => (t : EReal) * z) ''
            ((fun x => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued u)) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
        refine ⟨((finDot y xStar : ℝ) : EReal), ?_, ?_⟩
        · exact ⟨y, hy, rfl⟩
        · simp [finDot, dotProduct_smul, EReal.coe_mul, mul_comm]
      · rintro ⟨z', hz', hz⟩
        rcases hz' with ⟨y, hy, rfl⟩
        refine ⟨t • y, ?_, ?_⟩
        · exact Set.mem_smul_set.mpr ⟨y, hy, rfl⟩
        · simp [finDot, smul_dotProduct, EReal.coe_mul, mul_comm] at hz ⊢
          exact hz
    rw [hImg]
    have hMonotone : Monotone (fun z : EReal => (t : EReal) * z) := by
      intro a b hab
      exact mul_le_mul_of_nonneg_left hab (by exact_mod_cast (le_of_lt ht))
    have hContinuous :
        ContinuousAt (fun z : EReal => (t : EReal) * z)
          (sInf (((fun x => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued u))) := by
      exact
        (EReal.continuousAt_mul
          (p := ((t : EReal),
            sInf (((fun x => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued u))))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt ht)))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt ht)))
          (Or.inl (by simp))
          (Or.inl (by simp))).comp
          (continuousAt_const.prodMk continuousAt_id)
    have hTop : (t : EReal) * (⊤ : EReal) = ⊤ := by
      simpa using (EReal.coe_mul_top_of_pos ht)
    simpa using (hMonotone.map_sInf_of_continuousAt hContinuous hTop).symm

/-- Helper for Theorem 39.3: a Jensen-concave `EReal` function on all of `ℝ^n` has convex
hypograph in the local notation of this file. -/
lemma helperForTheorem_39_3_isERealConcaveOn_univ_to_IsConcaveEReal {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hConc : IsERealConcaveOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsConcaveEReal f := by
  -- Step 1: unfold the local hypograph definition and apply Jensen directly to the function
  -- values while keeping track of the real heights separately.
  rw [IsConcaveEReal, eRealHypograph]
  intro p hp q hq a b ha hb hab
  have hp' : (p.2 : EReal) ≤ f p.1 := by
    simpa [eRealHypograph] using hp
  have hq' : (q.2 : EReal) ≤ f q.1 := by
    simpa [eRealHypograph] using hq
  have hJensen :
      (a : EReal) * f p.1 + (b : EReal) * f q.1 ≤
        f (a • p.1 + b • q.1) :=
    hConc (by simp) (by simp) ha hb hab (by simp)
  have hHeights :
      (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) ≤
        (a : EReal) * f p.1 + (b : EReal) * f q.1 := by
    gcongr
  calc
    ((a * p.2 + b * q.2 : ℝ) : EReal) =
        (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) := by
      rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    _ ≤ (a : EReal) * f p.1 + (b : EReal) * f q.1 := hHeights
    _ ≤ f (a • p.1 + b • q.1) := hJensen

/-- The lower (epigraph) closure `cl f` of an `EReal`-valued function `f`, defined by closing its
epigraph and taking the infimum of the fiber. -/
noncomputable def eRealLowerClosure {X : Type*} [TopologicalSpace X] (f : X → EReal) : X → EReal :=
  fun x =>
    sInf ((fun r : ℝ => (r : EReal)) '' { r : ℝ | (x, r) ∈ closure (eRealEpigraph f) })

/-- The upper (hypograph) closure `cl f` of an `EReal`-valued function `f`, defined by closing its
hypograph and taking the supremum of the fiber. -/
noncomputable def eRealUpperClosure {X : Type*} [TopologicalSpace X] (f : X → EReal) : X → EReal :=
  fun x =>
    sSup ((fun r : ℝ => (r : EReal)) '' { r : ℝ | (x, r) ∈ closure (eRealHypograph f) })

/-- The oriented closure operation on `EReal`-valued functions: in supremum orientation this is
epigraph closure (closed convex convention), and in infimum orientation this is hypograph closure
(closed concave convention). -/
noncomputable def eRealClosureOriented {X : Type*} [TopologicalSpace X] (o : ConvexSetOrientation)
    (f : X → EReal) : X → EReal :=
  match o with
  | .supremum => eRealLowerClosure f
  | .infimum => eRealUpperClosure f

/-- Relative interior (`ri`) of a set in a real topological vector space, formalized as the
intrinsic interior. -/
def ri {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V] (S : Set V) : Set V :=
  intrinsicInterior ℝ S

/-- Helper for Theorem 39.3: the oriented set bracket of a fiber of `A` is exactly the matching
Section 33 pairing of the oriented indicator bifunction. -/
lemma helperForTheorem_39_3_bracket_eq_orientedPairing {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    setBracketVec o (A.toSetValued u) xStar =
      match o with
      | .supremum => convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u xStar
      | .infimum => concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar := by
  cases o
  · change setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar =
      convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u xStar
    have hBracketSupport :
        setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar =
          supportFunctionEReal (A.toSetValued u) xStar := by
      -- Step 1: both expressions are the same supremum once the image-set presentations are
      -- aligned.
      unfold setBracketVec supportFunctionEReal
      have hSet :
          ((fun x => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued u) =
            {z : EReal | ∃ x ∈ A.toSetValued u, z = ((dotProduct x xStar : ℝ) : EReal)} := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, by simp [finDot]⟩
        · rintro ⟨x, hx, hz⟩
          refine ⟨x, hx, ?_⟩
          simpa [finDot] using hz.symm
      rw [hSet]
    have hIndicatorEq :
        indicatorFunction (A.toSetValued u) =
          ConvexProcess.indicatorBifunction A u := by
      funext x
      -- Step 2: the local Chapter 3 indicator and the process indicator agree pointwise on the
      -- frozen fiber `A u`.
      simp [indicatorFunction, ConvexProcess.indicatorBifunction, indicatorEReal]
    calc
      setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar =
          supportFunctionEReal (A.toSetValued u) xStar := hBracketSupport
      _ =
          fenchelConjugate n (indicatorFunction (A.toSetValued u)) xStar := by
            symm
            exact congrFun
              (section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal
                (C := A.toSetValued u))
              xStar
      _ =
          convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u xStar := by
            rw [convexBifunctionPairing, helperForLemma33_0_14_convexConjugate_eq_fenchelConjugate,
              hIndicatorEq]
  · change setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar =
      concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar
    have hNegIndicatorEq :
        (fun x : Fin n → ℝ => -indicatorFunction (A.toSetValued u) x) =
          ConvexProcess.negIndicatorBifunction A u := by
      funext x
      -- Step 1: the negative indicator is the pointwise negation of the ordinary indicator on the
      -- frozen fiber.
      by_cases hx : x ∈ A.toSetValued u <;>
        simp [indicatorFunction, ConvexProcess.negIndicatorBifunction, negIndicatorEReal, hx]
    calc
      setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar =
          -supportFunctionEReal (((fun x : Fin n → ℝ => -x) '' A.toSetValued u)) xStar := by
            have hSupportNeg :
                supportFunctionEReal (((fun x : Fin n → ℝ => -x) '' A.toSetValued u)) xStar =
                  supportFunctionEReal (A.toSetValued u) (-xStar) := by
              -- Step 2: transport support-function witnesses through the involution `x ↦ -x`.
              unfold supportFunctionEReal
              refine le_antisymm ?_ ?_
              · refine sSup_le ?_
                intro r hr
                rcases hr with ⟨x, hx, rfl⟩
                refine le_sSup ?_
                refine ⟨-x, by simpa using hx, ?_⟩
                simp [dotProduct_neg]
              · refine sSup_le ?_
                intro r hr
                rcases hr with ⟨x, hx, rfl⟩
                refine le_sSup ?_
                refine ⟨-x, by simpa using hx, ?_⟩
                simp [dotProduct_neg]
            rw [hSupportNeg]
            rw [helperForCorollary_6_29_4_supportFunction_neg_eq_neg_sInf_pairings
              (U := A.toSetValued u) (u := xStar)]
            have hSet :
                ((fun a => (((a ⬝ᵥ xStar : ℝ) : EReal))) '' A.toSetValued u) =
                  ((fun r : ℝ => (r : EReal)) '' ((fun uStar => uStar ⬝ᵥ xStar) '' A.toSetValued u)) := by
              ext z
              constructor
              · rintro ⟨x, hx, rfl⟩
                exact ⟨x ⬝ᵥ xStar, ⟨x, hx, rfl⟩, rfl⟩
              · rintro ⟨r, ⟨x, hx, hr⟩, hz⟩
                subst hr
                subst hz
                exact ⟨x, hx, rfl⟩
            simp [setBracketVec, finDot, hSet]
      _ = -supportFunctionEReal (A.toSetValued u) (-xStar) := by
            rw [helperForCorollary_6_29_4_supportFunction_negImage_eq_supportFunction_neg
              (A.toSetValued u) xStar]
      _ = concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar := by
            calc
              -supportFunctionEReal (A.toSetValued u) (-xStar) =
                  -fenchelConjugate n (indicatorFunction (A.toSetValued u)) (-xStar) := by
                    rw [section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal
                      (C := A.toSetValued u)]
              _ =
                  concaveConjugate
                    (fun x : Fin n → ℝ => -indicatorFunction (A.toSetValued u) x) xStar := by
                    symm
                    simpa using
                      helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
                        (g := fun x : Fin n → ℝ => -indicatorFunction (A.toSetValued u) x)
                        (xStar := xStar)
              _ = concaveConjugate (ConvexProcess.negIndicatorBifunction A u) xStar := by
                    rw [hNegIndicatorEq]
              _ = concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar := by
                    rfl

/-- Helper for Theorem 39.3: every fiber of a convex process is convex, so its indicator section is
convex in the Section 33 sense. -/
lemma helperForTheorem_39_3_indicator_sections_convex {m n : ℕ}
    (A : ConvexProcess m n) :
    IsRockafellarSectionwiseConvexBifunction (ConvexProcess.indicatorBifunction A) := by
  intro u x y hx hy a b ha hb hab hxy
  -- Step 1: the fixed fiber `A u` is convex by Proposition 39.0.2.
  have hConv : Convex ℝ (A.toSetValued u) := (convexProcess_prop_39_0_2 A).1 u
  -- Step 2: split on endpoint membership in the fiber and simplify the indicator values in each
  -- Jensen branch.
  by_cases hxmem : x ∈ A.toSetValued u
  · by_cases hymem : y ∈ A.toSetValued u
    · -- If both endpoints lie in the fiber, convexity keeps the combination in the fiber.
      have hxyMem : a • x + b • y ∈ A.toSetValued u :=
        hConv hxmem hymem ha hb hab
      simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxmem, hymem, hxyMem]
    · -- If the second endpoint is off the fiber, the right-hand side is already forced large
      -- enough, so only the combination value needs case analysis.
      by_cases hxyMem : a • x + b • y ∈ A.toSetValued u
      · by_cases hZero : b = 0
        · have haOne : a = 1 := by linarith
          simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxmem, hymem, hxyMem, hZero, haOne]
        · have hbPos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hZero)
          simpa [ConvexProcess.indicatorBifunction, indicatorEReal, hxmem, hymem, hxyMem,
            EReal.coe_mul_top_of_pos hbPos]
      · by_cases hZero : b = 0
        · have haOne : a = 1 := by linarith
          have : a • x + b • y ∈ A.toSetValued u := by simpa [hZero, haOne] using hxmem
          exact (hxyMem this).elim
        · have hbPos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hZero)
          simpa [ConvexProcess.indicatorBifunction, indicatorEReal, hxmem, hymem, hxyMem,
            EReal.coe_mul_top_of_pos hbPos]
  · by_cases hymem : y ∈ A.toSetValued u
    · -- This is the symmetric branch where only the first endpoint is off the fiber.
      by_cases hxyMem : a • x + b • y ∈ A.toSetValued u
      · by_cases hZero : a = 0
        · have hbOne : b = 1 := by linarith
          simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxmem, hymem, hxyMem, hZero, hbOne]
        · have haPos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZero)
          simpa [ConvexProcess.indicatorBifunction, indicatorEReal, hxmem, hymem, hxyMem,
            EReal.coe_mul_top_of_pos haPos]
      · by_cases hZero : a = 0
        · have hbOne : b = 1 := by linarith
          have : a • x + b • y ∈ A.toSetValued u := by simpa [hZero, hbOne] using hymem
          exact (hxyMem this).elim
        · have haPos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZero)
          simpa [ConvexProcess.indicatorBifunction, indicatorEReal, hxmem, hymem, hxyMem,
            EReal.coe_mul_top_of_pos haPos]
    · -- If both endpoints are off the fiber, the Jensen inequality is immediate after
      -- simplifying the indicator values.
      by_cases hxyMem : a • x + b • y ∈ A.toSetValued u
      · by_cases hZero : a = 0
        · have hbOne : b = 1 := by linarith
          simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxmem, hymem, hxyMem, hZero, hbOne]
        · have haPos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZero)
          have hLe : (0 : EReal) ≤ ((⊤ : EReal) + (b : EReal) * ⊤) := by
            have hEq : ((⊤ : EReal) + (b : EReal) * ⊤) = (⊤ : EReal) := by
              have hMulNeBot : ((b : EReal) * ⊤) ≠ (⊥ : EReal) := by
                by_cases hbZero : b = 0
                · simp [hbZero]
                · have hbPos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hbZero)
                  rw [EReal.coe_mul_top_of_pos hbPos]
                  simp
              exact EReal.top_add_of_ne_bot hMulNeBot
            rw [hEq]
            simp
          simpa [ConvexProcess.indicatorBifunction, indicatorEReal, hxmem, hymem, hxyMem,
            EReal.coe_mul_top_of_pos haPos] using hLe
      · by_cases hZero : a = 0
        · have hbOne : b = 1 := by linarith
          simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxmem, hymem, hxyMem, hZero, hbOne]
        · have haPos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZero)
          have hEq : ((⊤ : EReal) + (b : EReal) * ⊤) = (⊤ : EReal) := by
            have hMulNeBot : ((b : EReal) * ⊤) ≠ (⊥ : EReal) := by
              by_cases hbZero : b = 0
              · simp [hbZero]
              · have hbPos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hbZero)
                rw [EReal.coe_mul_top_of_pos hbPos]
                simp
            exact EReal.top_add_of_ne_bot hMulNeBot
          simpa [ConvexProcess.indicatorBifunction, indicatorEReal, hxmem, hymem, hxyMem,
            EReal.coe_mul_top_of_pos haPos] using hEq

/-- Helper for Theorem 39.3: every fiber of a convex process is convex, so the negative indicator
sections are concave in the Section 33 sense. -/
lemma helperForTheorem_39_3_negIndicator_sections_concave {m n : ℕ}
    (A : ConvexProcess m n) :
    IsConcaveBifunction (ConvexProcess.negIndicatorBifunction A) := by
  exact helperForTheorem_39_2_negIndicatorConcave A

/-- Helper for Theorem 39.3: the supremum-oriented indicator bifunction never takes the value
`⊥`, which is the one-sided extended-real hypothesis needed in the convex Section 33 branch. -/
lemma indicatorBifunction_hasNoBotValues {m n : ℕ}
    (A : ConvexProcess m n) :
    HasNoBotValuesBifunction (ConvexProcess.indicatorBifunction A) := by
  intro u x
  by_cases hx : x ∈ A.toSetValued u
  · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hx]
  · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hx]

/-- Helper for Theorem 39.3: the infimum-oriented negative indicator bifunction never takes the
value `⊤`, which is the one-sided extended-real hypothesis needed in the concave Section 33
branch. -/
lemma helperForTheorem_39_3_negIndicator_hasNoTopValues {m n : ℕ}
    (A : ConvexProcess m n) :
    HasNoTopValuesBifunction (ConvexProcess.negIndicatorBifunction A) := by
  intro u x
  by_cases hx : x ∈ A.toSetValued u
  · simp [ConvexProcess.negIndicatorBifunction, negIndicatorEReal, hx]
  · simp [ConvexProcess.negIndicatorBifunction, negIndicatorEReal, hx]

/-- Helper for Theorem 39.3: negating the negative indicator bifunction recovers the ordinary
indicator bifunction pointwise. -/
lemma helperForTheorem_39_3_neg_negIndicatorBifunction_eq_indicator {m n : ℕ}
    (A : ConvexProcess m n) :
    (fun u x => -(ConvexProcess.negIndicatorBifunction A u x)) =
      ConvexProcess.indicatorBifunction A := by
  funext u x
  -- Step 1: both bifunctions only distinguish whether `x` belongs to the fiber `A u`.
  by_cases hx : x ∈ A.toSetValued u
  · simp [ConvexProcess.negIndicatorBifunction, ConvexProcess.indicatorBifunction,
      negIndicatorEReal, indicatorEReal, hx]
  · simp [ConvexProcess.negIndicatorBifunction, ConvexProcess.indicatorBifunction,
      negIndicatorEReal, indicatorEReal, hx]

/-- Helper for Theorem 39.3: a `ConvexFunction` on all of `ℝ^n` is exactly an `IsConvexEReal`
section in the local epigraph notation of this file. -/
lemma helperForTheorem_39_3_convexFunction_to_IsConvexEReal {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hConv : ConvexFunction f) :
    IsConvexEReal f := by
  -- Step 1: both predicates are the same full-space epigraph convexity statement, only written
  -- with different local names.
  have hEpigraph :
      epigraph (Set.univ : Set (Fin n → ℝ)) f = eRealEpigraph f := by
    ext p
    constructor
    · intro hp
      exact hp.2
    · intro hp
      exact ⟨by trivial, hp⟩
  simpa [IsConvexEReal, ConvexFunction, ConvexFunctionOn, hEpigraph] using hConv

/-- Helper for Theorem 39.3: Jensen convexity on all of `ℝ^n` upgrades directly to the local
epigraph-convexity predicate `IsConvexEReal`. -/
lemma helperForTheorem_39_3_isERealConvexOn_univ_to_IsConvexEReal {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsConvexEReal f := by
  -- Step 1: first upgrade the Jensen form to the standard full-space convex-function package.
  have hConvFn : ConvexFunction f :=
    helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hConv
  -- Step 2: the local `IsConvexEReal` predicate is just the same epigraph convexity statement.
  exact helperForTheorem_39_3_convexFunction_to_IsConvexEReal hConvFn

/-- Helper for Theorem 39.3: lower semicontinuity of a section yields closedness of its local
epigraph in the `IsClosedEReal` sense used here. -/
lemma isClosedEReal_of_lowerSemicontinuous {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hf : LowerSemicontinuous f) :
    IsClosedEReal f := by
  -- Step 1: work with the standard full-space epigraph on `ℝ^n`.
  have hClosedSublevel :
      ∀ α : ℝ, _root_.IsClosed {x : Fin n → ℝ | f x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := f)).1.mp hf
  have hClosedEpigraph :
      _root_.IsClosed (epigraph (Set.univ : Set (Fin n → ℝ)) f) :=
    (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := f)).2.mp
      hClosedSublevel
  -- Step 2: rewrite the standard epigraph back to the local `eRealEpigraph`.
  have hEpigraph :
      epigraph (Set.univ : Set (Fin n → ℝ)) f = eRealEpigraph f := by
    ext p
    constructor
    · intro hp
      exact hp.2
    · intro hp
      exact ⟨by trivial, hp⟩
  simpa [IsClosedEReal, hEpigraph] using hClosedEpigraph

/-- Closedness of an `EReal` function in the local epigraph sense implies ordinary lower
semicontinuity. -/
lemma lowerSemicontinuous_of_IsClosedEReal {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (hf : IsClosedEReal f) :
    LowerSemicontinuous f := by
  have hEpigraph :
      epigraph (Set.univ : Set (Fin n → ℝ)) f = eRealEpigraph f := by
    ext p
    constructor
    · intro hp
      exact hp.2
    · intro hp
      exact ⟨by trivial, hp⟩
  have hClosedEpigraph :
      _root_.IsClosed (epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
    simpa [IsClosedEReal, hEpigraph] using hf
  have hClosedSublevel :
      ∀ α : ℝ, _root_.IsClosed {x : Fin n → ℝ | f x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := f)).2.mpr hClosedEpigraph
  exact
    (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := f)).1.mpr hClosedSublevel

/-- Helper for Theorem 39.3: a closed convex function is a closed `EReal` section in the local
notation of this file. -/
lemma isClosedEReal_of_closedConvexFunction {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexFunction f) :
    IsClosedEReal f := by
  -- Step 1: only the lower-semicontinuity field is needed for the epigraph-closedness claim.
  exact isClosedEReal_of_lowerSemicontinuous hClosed.2

/-- Helper for Theorem 39.3: on a fixed fiber, the supremum-oriented bracket is the `EReal`
support function of that fiber. -/
lemma helperForTheorem_39_3_supremumBracket_eq_supportFunctionEReal {n : ℕ}
    (S : Set (Fin n → ℝ)) :
    setBracketVec ConvexSetOrientation.supremum S = supportFunctionEReal S := by
  -- Step 1: unfold both definitions and identify the image-set description with the existential
  -- set used by `supportFunctionEReal`.
  funext xStar
  unfold setBracketVec supportFunctionEReal
  have hSet :
      ((fun x => ((finDot x xStar : ℝ) : EReal)) '' S) =
        {z : EReal | ∃ x ∈ S, z = ((dotProduct x xStar : ℝ) : EReal)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp [finDot]⟩
    · rintro ⟨x, hx, hz⟩
      refine ⟨x, hx, ?_⟩
      simpa [finDot] using hz.symm
  rw [hSet]

/-- Helper for Theorem 39.3: on a fixed fiber, the infimum-oriented bracket is the negative of the
support function of the negated fiber. -/
lemma helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber {n : ℕ}
    (S : Set (Fin n → ℝ)) :
    setBracketVec ConvexSetOrientation.infimum S =
      fun xStar => -supportFunctionEReal (Neg.neg ⁻¹' S) xStar := by
  funext xStar
  have hSupportNeg :
      supportFunctionEReal (Neg.neg ⁻¹' S) xStar = supportFunctionEReal S (-xStar) := by
    -- Step 1: transport support-function witnesses through the involution `x ↦ -x`.
    unfold supportFunctionEReal
    refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      refine le_sSup ?_
      refine ⟨-x, by simpa using hx, ?_⟩
      simp [dotProduct_neg]
    · refine sSup_le ?_
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      refine le_sSup ?_
      refine ⟨-x, by simpa using hx, ?_⟩
      simp [dotProduct_neg]
  -- Step 2: convert the support value at `-xStar` into the negative infimum pairing formula.
  rw [hSupportNeg]
  rw [helperForCorollary_6_29_4_supportFunction_neg_eq_neg_sInf_pairings (U := S) (u := xStar)]
  have hSet :
      ((fun a => (((a ⬝ᵥ xStar : ℝ) : EReal))) '' S) =
        ((fun r : ℝ => (r : EReal)) '' ((fun uStar => uStar ⬝ᵥ xStar) '' S)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x ⬝ᵥ xStar, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨x, hx, hr⟩, hz⟩
      subst hr
      subst hz
      exact ⟨x, hx, rfl⟩
  simp [setBracketVec, finDot, hSet]

/-- Helper for Theorem 39.3: if a fiber is empty, its supremum-oriented bracket section is the
constant bottom function, hence positively homogeneous, closed, and convex. -/
lemma helperForTheorem_39_3_emptyFiber_supremumSection {n : ℕ}
    {S : Set (Fin n → ℝ)}
    (hS : S = ∅) :
    IsPosHomogeneousEReal (fun xStar => setBracketVec ConvexSetOrientation.supremum S xStar) ∧
      IsClosedEReal (fun xStar => setBracketVec ConvexSetOrientation.supremum S xStar) ∧
      IsConvexEReal (fun xStar => setBracketVec ConvexSetOrientation.supremum S xStar) := by
  -- Step 1: after rewriting the empty fiber, the section is literally the constant `⊥` function.
  have hEq :
      (fun xStar => setBracketVec ConvexSetOrientation.supremum S xStar) =
        fun _ : Fin n → ℝ => (⊥ : EReal) := by
    funext xStar
    simp [setBracketVec, hS]
  refine ⟨?_, ?_, ?_⟩
  · -- Positive homogeneity is immediate because positive scaling fixes the constant `⊥` section.
    intro xStar t ht
    simpa [hEq] using (EReal.coe_mul_bot_of_pos ht).symm
  · -- The epigraph of the constant `⊥` function is all of `ℝ^n × ℝ`.
    rw [hEq]
    simpa [IsClosedEReal, eRealEpigraph]
      using (isClosed_univ : IsClosed (Set.univ : Set ((Fin n → ℝ) × ℝ)))
  · -- The same whole-space epigraph is convex.
    rw [hEq]
    simpa [IsConvexEReal, eRealEpigraph]
      using (convex_univ : Convex ℝ (Set.univ : Set ((Fin n → ℝ) × ℝ)))

/-- Helper for Theorem 39.3: every supremum-oriented fiber section is the support function of a
convex set, so it is positively homogeneous, closed, and convex. -/
lemma helperForTheorem_39_3_supremumSection_properties {m n : ℕ}
    (A : ConvexProcess m n) (u : Fin m → ℝ) :
    IsPosHomogeneousEReal
        (fun xStar => setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar) ∧
      IsClosedEReal
        (fun xStar => setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar) ∧
      IsConvexEReal
        (fun xStar => setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar) := by
  -- Step 1: split off the empty-fiber degenerate case, where the bracket is the constant `⊥`.
  by_cases hEmpty : A.toSetValued u = ∅
  · exact helperForTheorem_39_3_emptyFiber_supremumSection hEmpty
  · have hNonempty : Set.Nonempty (A.toSetValued u) := by
      exact Set.nonempty_iff_ne_empty.mpr hEmpty
    have hConvFiber : Convex ℝ (A.toSetValued u) :=
      (convexProcess_prop_39_0_2 A).1 u
    have hSupport :
        ClosedConvexFunction (supportFunctionEReal (A.toSetValued u)) ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
            (supportFunctionEReal (A.toSetValued u)) ∧
          PositivelyHomogeneous (supportFunctionEReal (A.toSetValued u)) :=
      (exists_supportFunctionEReal_iff_closedProperConvex_posHom
        (f := supportFunctionEReal (A.toSetValued u))).1
        ⟨A.toSetValued u, hNonempty, hConvFiber, rfl⟩
    have hEq :
        (fun xStar =>
          setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar) =
          supportFunctionEReal (A.toSetValued u) :=
      helperForTheorem_39_3_supremumBracket_eq_supportFunctionEReal (A.toSetValued u)
    refine ⟨?_, ?_, ?_⟩
    · -- Step 2: transfer positive homogeneity across the support-function identification.
      simpa [IsPosHomogeneousEReal, hEq] using hSupport.2.2
    · -- Step 3: transfer lower-semicontinuity/closedness across the same identification.
      simpa [hEq] using
        isClosedEReal_of_closedConvexFunction hSupport.1
    · -- Step 4: the support function is convex as a closed convex function.
      simpa [hEq] using
        helperForTheorem_39_3_convexFunction_to_IsConvexEReal hSupport.1.1

/-- Helper for Theorem 39.3: negating a closed convex `EReal` function turns its epigraph into the
hypograph of a closed concave function. -/
lemma helperForTheorem_39_3_neg_of_closedConvex_is_upperClosedConcave {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hClosed : IsClosedEReal f) (hConv : IsConvexEReal f) :
    IsUpperClosedEReal (fun x => -f x) ∧ IsConcaveEReal (fun x => -f x) := by
  let flipHeight : (Fin n → ℝ) × ℝ → (Fin n → ℝ) × ℝ := fun p => (p.1, -p.2)
  have hPre :
      eRealHypograph (fun x => -f x) = flipHeight ⁻¹' eRealEpigraph f := by
    -- Step 1: membership in the hypograph of `-f` is exactly membership in the epigraph of `f`
    -- after flipping the real-height coordinate.
    ext p
    constructor
    · intro hp
      change ((p.2 : EReal) ≤ -f p.1) at hp
      change f p.1 ≤ ((-p.2 : ℝ) : EReal)
      exact (EReal.le_neg.mp hp)
    · intro hp
      change f p.1 ≤ ((-p.2 : ℝ) : EReal) at hp
      change ((p.2 : EReal) ≤ -f p.1)
      exact (EReal.le_neg.mp hp)
  refine ⟨?_, ?_⟩
  · -- Step 2: closed epigraphs stay closed under the continuous height-flip map.
    rw [IsUpperClosedEReal, hPre]
    exact hClosed.preimage (by
      change Continuous fun p : (Fin n → ℝ) × ℝ => (p.1, -p.2)
      continuity)
  · -- Step 3: the same linear height-flip transports convexity of the epigraph to convexity of
    -- the hypograph, i.e. concavity of the negated function.
    have hFlipConv : Convex ℝ (flipHeight ⁻¹' eRealEpigraph f) := by
      intro p hp q hq a b ha hb hab
      have hMap :
          flipHeight (a • p + b • q) = a • flipHeight p + b • flipHeight q := by
        ext <;> simp [flipHeight, mul_add, add_mul, add_comm, add_left_comm, add_assoc]
      have hCombo :
          a • flipHeight p + b • flipHeight q ∈ eRealEpigraph f :=
        hConv hp hq ha hb hab
      simpa [hMap] using hCombo
    simpa [IsConcaveEReal, hPre] using hFlipConv

/-- Helper for Theorem 39.3: if a fiber is empty, its infimum-oriented bracket section is the
constant top function, hence positively homogeneous, upper closed, and concave. -/
lemma helperForTheorem_39_3_emptyFiber_infimumSection {n : ℕ}
    {S : Set (Fin n → ℝ)}
    (hS : S = ∅) :
    IsPosHomogeneousEReal (fun xStar => setBracketVec ConvexSetOrientation.infimum S xStar) ∧
      IsUpperClosedEReal (fun xStar => setBracketVec ConvexSetOrientation.infimum S xStar) ∧
      IsConcaveEReal (fun xStar => setBracketVec ConvexSetOrientation.infimum S xStar) := by
  -- Step 1: after rewriting the empty fiber, the section is literally the constant `⊤` function.
  have hEq :
      (fun xStar => setBracketVec ConvexSetOrientation.infimum S xStar) =
        fun _ : Fin n → ℝ => (⊤ : EReal) := by
    funext xStar
    simp [setBracketVec, hS]
  refine ⟨?_, ?_, ?_⟩
  · -- Positive homogeneity is immediate because positive scaling fixes the constant `⊤` section.
    intro xStar t ht
    simpa [hEq] using (EReal.coe_mul_top_of_pos ht).symm
  · -- The hypograph of the constant `⊤` function is all of `ℝ^n × ℝ`.
    rw [hEq]
    simpa [IsUpperClosedEReal, eRealHypograph]
      using (isClosed_univ : IsClosed (Set.univ : Set ((Fin n → ℝ) × ℝ)))
  · -- The same whole-space hypograph is convex.
    rw [hEq]
    simpa [IsConcaveEReal, eRealHypograph]
      using (convex_univ : Convex ℝ (Set.univ : Set ((Fin n → ℝ) × ℝ)))

/-- Helper for Theorem 39.3: every infimum-oriented fiber section is the negative of a support
function, so it is positively homogeneous, upper closed, and concave. -/
lemma helperForTheorem_39_3_infimumSection_properties {m n : ℕ}
    (A : ConvexProcess m n) (u : Fin m → ℝ) :
    IsPosHomogeneousEReal
        (fun xStar => setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar) ∧
      IsUpperClosedEReal
        (fun xStar => setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar) ∧
      IsConcaveEReal
        (fun xStar => setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar) := by
  -- Step 1: split off the empty-fiber degenerate case, where the bracket is the constant `⊤`.
  by_cases hEmpty : A.toSetValued u = ∅
  · exact helperForTheorem_39_3_emptyFiber_infimumSection hEmpty
  · have hNonempty : Set.Nonempty (A.toSetValued u) := by
      exact Set.nonempty_iff_ne_empty.mpr hEmpty
    have hConvFiber : Convex ℝ (A.toSetValued u) :=
      (convexProcess_prop_39_0_2 A).1 u
    have hNegFiberNonempty : Set.Nonempty (Neg.neg ⁻¹' A.toSetValued u) := by
      rcases hNonempty with ⟨x, hx⟩
      exact ⟨-x, by simpa using hx⟩
    have hNegFiberConv : Convex ℝ (Neg.neg ⁻¹' A.toSetValued u) := by
      simpa using hConvFiber.neg
    have hSupport :
        ClosedConvexFunction (supportFunctionEReal (Neg.neg ⁻¹' A.toSetValued u)) ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
            (supportFunctionEReal (Neg.neg ⁻¹' A.toSetValued u)) ∧
          PositivelyHomogeneous (supportFunctionEReal (Neg.neg ⁻¹' A.toSetValued u)) :=
      (exists_supportFunctionEReal_iff_closedProperConvex_posHom
        (f := supportFunctionEReal (Neg.neg ⁻¹' A.toSetValued u))).1
        ⟨Neg.neg ⁻¹' A.toSetValued u, hNegFiberNonempty, hNegFiberConv, rfl⟩
    have hEq :
        (fun xStar =>
          setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar) =
          fun xStar => -supportFunctionEReal (Neg.neg ⁻¹' A.toSetValued u) xStar :=
      helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber (A.toSetValued u)
    have hNegClosedConc :
        IsUpperClosedEReal
            (fun xStar => -supportFunctionEReal (Neg.neg ⁻¹' A.toSetValued u) xStar) ∧
          IsConcaveEReal
            (fun xStar => -supportFunctionEReal (Neg.neg ⁻¹' A.toSetValued u) xStar) :=
      helperForTheorem_39_3_neg_of_closedConvex_is_upperClosedConcave
        (isClosedEReal_of_closedConvexFunction hSupport.1)
        (helperForTheorem_39_3_convexFunction_to_IsConvexEReal hSupport.1.1)
    refine ⟨?_, ?_, ?_⟩
    · -- Step 2: positive homogeneity survives after negating the support function.
      intro xStar t ht
      rw [hEq]
      have hPos :=
        hSupport.2.2 xStar t ht
      simpa [hPos] using congrArg Neg.neg hPos
    · -- Step 3: transport upper closedness across the bracket/support identification.
      simpa [hEq] using hNegClosedConc.1
    · -- Step 4: the same identification transports concavity.
      simpa [hEq] using hNegClosedConc.2

/-- Helper for Theorem 39.3: the supremum-oriented indicator bifunction already satisfies the
Rockafellar convexity and no-`⊥` package from Section 33, and closedness of the process upgrades
its graph function to a fixed point of the convex closure. -/
lemma indicatorBifunction_rockafellarPackage {m n : ℕ}
    (A : ConvexProcess m n) :
    IsRockafellarConvexBifunction (ConvexProcess.indicatorBifunction A) ∧
      HasNoBotValuesBifunction (ConvexProcess.indicatorBifunction A) ∧
      (A.IsClosed →
        IsFunctionConvexClosed
          (graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A))) := by
  let graphSet : Set (Fin (m + n) → ℝ) :=
    {z | (fun j => z (Fin.natAdd m j)) ∈ A.toSetValued (fun i => z (Fin.castAdd n i))}
  have hGraphSetConvex : Convex ℝ graphSet := by
    have hGraphConv : Convex ℝ (setValuedGraph A.toSetValued) :=
      (helperForProposition_39_0_1_graphConvexCone_ofConvexProcess A).convex
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    have hz₁' :
        ((fun i => z₁ (Fin.castAdd n i)), (fun j => z₁ (Fin.natAdd m j))) ∈
          setValuedGraph A.toSetValued := by
      simpa [graphSet, setValuedGraph] using hz₁
    have hz₂' :
        ((fun i => z₂ (Fin.castAdd n i)), (fun j => z₂ (Fin.natAdd m j))) ∈
          setValuedGraph A.toSetValued := by
      simpa [graphSet, setValuedGraph] using hz₂
    have hCombo :
        a • ((fun i => z₁ (Fin.castAdd n i)), (fun j => z₁ (Fin.natAdd m j))) +
            b • ((fun i => z₂ (Fin.castAdd n i)), (fun j => z₂ (Fin.natAdd m j))) ∈
          setValuedGraph A.toSetValued :=
      hGraphConv hz₁' hz₂' ha hb hab
    simpa [graphSet, setValuedGraph, Pi.add_apply, Pi.smul_apply] using hCombo
  have hIndicatorConvex :
      ConvexFunction (indicatorFunction graphSet) :=
    convexFunction_indicator_of_convex (C := graphSet) hGraphSetConvex
  have hIndicatorNoBot :
      ∀ z : Fin (m + n) → ℝ, indicatorFunction graphSet z ≠ (⊥ : EReal) := by
    -- The ordinary indicator only takes the values `0` and `⊤`.
    intro z
    by_cases hz : z ∈ graphSet
    · simp [indicatorFunction, hz]
    · simp [indicatorFunction, hz]
  have hGraphConvex :
      IsGraphConvexBifunction (ConvexProcess.indicatorBifunction A) := by
    -- Rewrite the uncurried graph function as the graph indicator and transfer convexity.
    have hGraphIndicatorConvex :
        IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
          (indicatorFunction graphSet) :=
      helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ
        (f := indicatorFunction graphSet) hIndicatorConvex hIndicatorNoBot
    have hGraphEq :
        graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A) =
          indicatorFunction graphSet := by
      funext z
      by_cases hz : z ∈ graphSet
      · have hz' :
            (fun j => z (Fin.natAdd m j)) ∈
              A.toSetValued (fun i => z (Fin.castAdd n i)) := by
          simpa [graphSet] using hz
        simp [graphFunctionOfBifunction, ConvexProcess.indicatorBifunction, indicatorEReal,
          indicatorFunction, graphSet, hz, hz']
      · have hz' :
            (fun j => z (Fin.natAdd m j)) ∉
              A.toSetValued (fun i => z (Fin.castAdd n i)) := by
          simpa [graphSet] using hz
        simp [graphFunctionOfBifunction, ConvexProcess.indicatorBifunction, indicatorEReal,
          indicatorFunction, graphSet, hz, hz']
    simpa [IsGraphConvexBifunction, hGraphEq] using hGraphIndicatorConvex
  refine ⟨?_, indicatorBifunction_hasNoBotValues A, ?_⟩
  · -- Graph convexity is exactly the Section 33 entry point for Rockafellar convexity.
    exact helperForLemma33_0_22_graphConvex_gives_rockafellarConvex
      (F := ConvexProcess.indicatorBifunction A) hGraphConvex
  · intro hAClosed
    have hGraphEq :
        graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A) =
          indicatorFunction graphSet := by
      funext z
      by_cases hz : z ∈ graphSet
      · have hz' :
            (fun j => z (Fin.natAdd m j)) ∈
              A.toSetValued (fun i => z (Fin.castAdd n i)) := by
          simpa [graphSet] using hz
        simp [graphFunctionOfBifunction, ConvexProcess.indicatorBifunction, indicatorEReal,
          indicatorFunction, graphSet, hz, hz']
      · have hz' :
            (fun j => z (Fin.natAdd m j)) ∉
              A.toSetValued (fun i => z (Fin.castAdd n i)) := by
          simpa [graphSet] using hz
        simp [graphFunctionOfBifunction, ConvexProcess.indicatorBifunction, indicatorEReal,
          indicatorFunction, graphSet, hz, hz']
    have hGraphSetClosed : _root_.IsClosed graphSet := by
      let split :
          (Fin (m + n) → ℝ) → (Fin m → ℝ) × (Fin n → ℝ) :=
        fun z => ((fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j)))
      have hSplitCont : Continuous split := by
        continuity
      have hSplitPreimage :
          split ⁻¹' setValuedGraph A.toSetValued = graphSet := by
        ext z
        rfl
      have hClosedGraph :
          _root_.IsClosed (setValuedGraph A.toSetValued) :=
        (helperForProposition_39_0_13_graphClosed_iff_processClosed A).2 hAClosed
      rw [← hSplitPreimage]
      exact hClosedGraph.preimage hSplitCont
    have hNegGraphSetClosed : _root_.IsClosed (-graphSet) := by
      -- Closedness is preserved by the continuous negation map.
      have hcont : Continuous fun z : Fin (m + n) → ℝ => -z := by
        continuity
      have hpre :
          _root_.IsClosed ((fun z : Fin (m + n) → ℝ => -z) ⁻¹' graphSet) :=
        hGraphSetClosed.preimage hcont
      simpa [Set.preimage, Set.neg] using hpre
    have hNegGraphSetNonempty : Set.Nonempty (-graphSet) := by
      -- The origin belongs to the graph of every convex process, so it also belongs to `-graphSet`.
      refine ⟨0, ?_⟩
      have hZero : (0 : Fin (m + n) → ℝ) ∈ graphSet := by
        simpa [graphSet] using A.zero_mem
      change -(0 : Fin (m + n) → ℝ) ∈ graphSet
      simpa using hZero
    have hClosedIndicator :
        ClosedConvexFunction (indicatorFunction graphSet) := by
      -- Closedness of the graph upgrades its indicator to a closed convex function.
      have hNegNeg :
          -(-graphSet) = graphSet := by
        ext z
        change -(-z) ∈ graphSet ↔ z ∈ graphSet
        simp
      rw [← hNegNeg]
      exact
        (closedConvexFunction_indicator_neg
          (C := -graphSet) hNegGraphSetNonempty hNegGraphSetClosed hGraphSetConvex.neg).1
    have hGraphClosed :
        ClosedConvexFunction
          (graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A)) := by
      simpa [hGraphEq] using hClosedIndicator
    -- A closed graph function is already fixed by the raw Section 33 convex closure.
    exact
      helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
        (f := graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A))
        hGraphClosed.2


end ConvexProcess
end Section39
end Chap08
