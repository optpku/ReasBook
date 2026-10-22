/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section04_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part1

section Chap08
section Section38

/-- Helper for Proposition 38.0.3: the advertised theorem schema is already refuted by its
one-dimensional identity specialization. -/
lemma helperForProposition_38_0_3_existsCounterexample :
    ∃ (m n : Nat) (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)),
      ¬ (bifunctionInverse (convexIndicatorBifunction A.toLinearMap) =
            concaveIndicatorBifunctionLinear A.symm.toLinearMap ∧
          bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
            convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) := by
  -- The one-dimensional identity map is an explicit counterexample to the theorem schema.
  refine ⟨1, 1, LinearEquiv.refl ℝ (Fin 1 → ℝ), ?_⟩
  exact helperForProposition_38_0_3_identityOneDim_targetFalse

/-- Helper for Proposition 38.0.3: the advertised theorem schema is already refuted by its
one-dimensional identity specialization. -/
lemma helperForProposition_38_0_3_universalClaimFalse :
    ¬ (∀ {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)),
        bifunctionInverse (convexIndicatorBifunction A.toLinearMap) =
            concaveIndicatorBifunctionLinear A.symm.toLinearMap ∧
          bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
            convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) := by
  intro hUniversal
  -- Extract the explicit counterexample and contradict the putative universal theorem schema.
  rcases helperForProposition_38_0_3_existsCounterexample with ⟨m, n, A, hCounterexample⟩
  exact hCounterexample (hUniversal A)

/-- Helper for Proposition 38.0.3: when both primal spaces are subsingletons, the current
`iInf`-adjoint of a concave indicator bifunction collapses to the matching convex indicator of the
dual map because every graph condition is automatic and every infimum is taken over a singleton. -/
lemma helperForProposition_38_0_3_adjoint_concaveIndicator_eq_convexIndicator_of_subsingleton
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    [Subsingleton U] [Subsingleton X]
    (A : X →ₗ[ℝ] U) :
    bifunctionAdjoint (concaveIndicatorBifunctionLinear A) =
      convexIndicatorBifunctionLinear A.dualMap := by
  funext uStar xStar
  have hUStar : uStar = 0 := by
    -- A linear functional on a subsingleton space is forced to be the zero functional.
    ext u
    have hu : u = 0 := Subsingleton.elim _ _
    rw [hu]
    simp
  have hXStar : xStar = 0 := by
    -- The same collapse holds for functionals on the second subsingleton space.
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    simp
  subst hUStar
  subst hXStar
  have hAdjointZero :
      bifunctionAdjoint (concaveIndicatorBifunctionLinear A)
          (0 : Module.Dual ℝ U) (0 : Module.Dual ℝ X) = 0 := by
    apply le_antisymm
    · -- The unique primal pair `(0, 0)` realizes the value `0`.
      refine le_trans (iInf_le _ (0 : X)) ?_
      refine le_trans (iInf_le _ (0 : U)) ?_
      simp [concaveIndicatorBifunctionLinear]
    · -- Every summand uses the same on-graph primal pair, so the infimum cannot drop below `0`.
      rw [bifunctionAdjoint]
      refine le_iInf ?_
      intro x
      refine le_iInf ?_
      intro u
      have hu : u = A x := Subsingleton.elim _ _
      rw [concaveIndicatorBifunctionLinear, if_pos hu]
      simp
  have hConvexZero :
      convexIndicatorBifunctionLinear A.dualMap
          (0 : Module.Dual ℝ U) (0 : Module.Dual ℝ X) = 0 := by
    -- The unique dual pair automatically lies on the graph of `A*`.
    simp [convexIndicatorBifunctionLinear]
  -- After collapsing the dual variables, both sides equal `0`.
  rw [hAdjointZero, hConvexZero]

/-- Helper for Proposition 38.0.3: when `m = 0`, the second conjunct actually holds, because the
inverse graph and its dual graph are both singletons and the generic subsingleton-collapse lemma
applies. -/
lemma helperForProposition_38_0_3_secondConjunct_of_zeroDimension
    {n : Nat} (A : (Fin 0 → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
      convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap) := by
  -- Rewrite the inverse term to the concave indicator of `A⁻¹`.
  rw [helperForProposition_38_0_3_inverse_eq_concaveIndicator A]
  have hSubDom : Subsingleton (Fin 0 → ℝ) := inferInstance
  have hSubCod : Subsingleton (Fin n → ℝ) := by
    -- Transport the zero-dimensional collapse across the linear equivalence `A`.
    refine ⟨?_⟩
    intro x y
    apply A.symm.injective
    exact Subsingleton.elim _ _
  letI : Subsingleton (Fin 0 → ℝ) := hSubDom
  letI : Subsingleton (Fin n → ℝ) := hSubCod
  -- With both primal spaces collapsed, the generic singleton computation finishes the proof.
  exact
    helperForProposition_38_0_3_adjoint_concaveIndicator_eq_convexIndicator_of_subsingleton
      A.symm.toLinearMap

/-- Helper for Proposition 38.0.3: in every positive-dimensional successor case, the advertised
second conjunct is already refuted once the inverse formula is rewritten explicitly. -/
lemma helperForProposition_38_0_3_secondConjunctFalse_of_succDimension
    {m n : Nat} (A : (Fin (Nat.succ m) → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) ≠
      convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap) := by
  -- Reuse the general positive-dimensional obstruction together with the proved inverse formula.
  exact
    helperForProposition_38_0_3_secondConjunctFalse_of_positiveDimension_given_inverse
      A (Nat.succ_pos m) (helperForProposition_38_0_3_inverse_eq_concaveIndicator A)

/-- Helper for Proposition 38.0.3: in every positive-dimensional successor case, the full target
conjunction is impossible under the current `iInf`-based adjoint formalization. -/
lemma helperForProposition_38_0_3_targetFalse_of_succDimension
    {m n : Nat} (A : (Fin (Nat.succ m) → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    ¬ (bifunctionInverse (convexIndicatorBifunction A.toLinearMap) =
          concaveIndicatorBifunctionLinear A.symm.toLinearMap ∧
        bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
          convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) := by
  intro hTarget
  -- The successor-case obstruction already rules out the second conjunct of the conjunction.
  exact (helperForProposition_38_0_3_secondConjunctFalse_of_succDimension A) hTarget.2

/-- Helper for Proposition 38.0.3: the textbook concave adjoint of the inverse convex indicator
is the convex indicator bifunction of the coordinate adjoint graph of `A⁻¹`. -/
lemma helperForProposition_38_0_3_inverseTextbookAdjoint_eq_convexIndicator
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    bifunctionInverseTextbookAdjoint A =
      convexIndicatorBifunctionLinear (coordinateAdjointLinearMap A.symm.toLinearMap) := by
  -- Route correction: the old `iInf`-based `bifunctionAdjoint` obstruction analyzed the wrong
  -- adjoint notion. The textbook object here is the Chapter 6 concave adjoint of the inverse
  -- graph indicator, so the generic graph-indicator adjoint formula applies directly.
  unfold bifunctionInverseTextbookAdjoint
  simpa using
    helperForProposition_38_0_3_textbookAdjoint_eq_convexIndicator A.symm.toLinearMap

/-- Helper for Proposition 38.0.3: pointwise, the inverse of the convex indicator of `A` takes
the value `0` on the inverse graph `u = A⁻¹ x` and `⊥` off that graph. -/
lemma helperForProposition_38_0_3_inverse_apply
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (x : Fin n → ℝ) (u : Fin m → ℝ) :
    bifunctionInverse (convexIndicatorBifunction A.toLinearMap) x u =
      if u = A.symm x then 0 else ⊥ := by
  -- Evaluate the inverse via the previously established identification with the concave graph
  -- indicator of `A⁻¹`.
  have hEq :
      bifunctionInverse (convexIndicatorBifunction A.toLinearMap) x u =
        concaveIndicatorBifunctionLinear A.symm.toLinearMap x u := by
    exact
      congrArg (fun F => F x u)
        (helperForProposition_38_0_3_inverse_eq_concaveIndicator A)
  -- The concave indicator is exactly the `0/-∞` indicator of the inverse graph condition.
  by_cases hu : u = A.symm x
  · simpa [concaveIndicatorBifunctionLinear, hu] using hEq
  · simpa [concaveIndicatorBifunctionLinear, hu] using hEq

/-- Helper for Proposition 38.0.3: pointwise, the textbook adjoint `F_*^*` takes the value `0`
on the coordinate-adjoint graph `xStar = (A⁻¹)^* uStar` and `⊤` off that graph. -/
lemma helperForProposition_38_0_3_inverseTextbookAdjoint_apply
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (uStar : Fin m → ℝ) (xStar : Fin n → ℝ) :
    bifunctionInverseTextbookAdjoint A uStar xStar =
      if xStar = coordinateAdjointLinearMap A.symm.toLinearMap uStar then 0 else ⊤ := by
  -- Rewrite the textbook adjoint as the convex indicator of the coordinate adjoint graph.
  have hEq :
      bifunctionInverseTextbookAdjoint A uStar xStar =
        convexIndicatorBifunctionLinear (coordinateAdjointLinearMap A.symm.toLinearMap)
          uStar xStar := by
    exact
      congrArg (fun F => F uStar xStar)
        (helperForProposition_38_0_3_inverseTextbookAdjoint_eq_convexIndicator A)
  -- The convex indicator is exactly the `0/+∞` indicator of membership in that dual graph.
  by_cases hx : xStar = coordinateAdjointLinearMap A.symm.toLinearMap uStar
  · simpa [convexIndicatorBifunctionLinear, hx] using hEq
  · simpa [convexIndicatorBifunctionLinear, hx] using hEq

/-- Helper for Proposition 38.0.3: bundling the inverse-graph identification and the textbook
adjoint-graph identification yields the full proposition as a conjunction. -/
lemma helperForProposition_38_0_3_inverse_and_textbookAdjoint_eq_indicators
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    bifunctionInverse (convexIndicatorBifunction A.toLinearMap) =
        concaveIndicatorBifunctionLinear A.symm.toLinearMap ∧
      bifunctionInverseTextbookAdjoint A =
        convexIndicatorBifunctionLinear (coordinateAdjointLinearMap A.symm.toLinearMap) := by
  -- Package the two previously established indicator identifications into the final conjunction.
  constructor
  · exact helperForProposition_38_0_3_inverse_eq_concaveIndicator A
  · exact helperForProposition_38_0_3_inverseTextbookAdjoint_eq_convexIndicator A

/-- Proposition 38.0.3: Let `A : ℝ^m → ℝ^n` be a nonsingular linear transformation, and let `F`
be the convex indicator bifunction of `A`. Then the inverse `F_*` of `F` is the concave indicator
bifunction of `A⁻¹`, and the textbook concave adjoint `F_*^*` is the convex indicator bifunction
of `(A^*)⁻¹ = (A⁻¹)^*` (here modeled in coordinates by `coordinateAdjointLinearMap`). -/
theorem bifunctionInverse_convexIndicatorBifunction {m n : Nat}
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    bifunctionInverse (convexIndicatorBifunction A.toLinearMap) =
        concaveIndicatorBifunctionLinear A.symm.toLinearMap ∧
      bifunctionInverseTextbookAdjoint A =
        convexIndicatorBifunctionLinear (coordinateAdjointLinearMap A.symm.toLinearMap) :=
  by
    -- Reuse the dedicated bundled helper so the theorem statement stays aligned with the textbook.
    exact helperForProposition_38_0_3_inverse_and_textbookAdjoint_eq_indicators A

/-- The epigraph of an `EReal`-valued function `f : X → EReal`, viewed as a subset of `X × ℝ`:
`(x, r)` lies in the epigraph when `f x ≤ r` (with `r` coerced to `EReal`). -/
def ERealEpigraph {X : Type*} (f : X → EReal) : Set (X × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

/-- A book-style convexity predicate for an `EReal`-valued function: `f` is convex when its
epigraph is a convex set in `X × ℝ`. This matches the standard notion for extended-real-valued
convex functions. -/
def IsERealConvex {X : Type*} [AddCommMonoid X] [Module ℝ X] (f : X → EReal) : Prop :=
  Convex ℝ (ERealEpigraph f)

/-- A book-style properness predicate for an `EReal`-valued function: `f` never takes the value
`-∞` and is not identically `+∞`. This models functions into `ℝ ∪ {+∞}` by ruling out `-∞`. -/
def IsProperEReal {X : Type*} (f : X → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, f x ≠ ⊤

/-- A bifunction `F : ℝ^m → ℝ^n → EReal` equipped with the hypotheses used in the text:
`F` is proper as an extended-real-valued function on the product (it never takes the value `-∞`
and is not identically `+∞`), and for each fixed `u`, the slice `x ↦ F u x` is convex (via convex
epigraph).  This allows the `u`-domain `dom F` to be a proper subset, as in the book. -/
structure FiberwiseProperConvexBifunction (m n : Nat) : Type where
  /-- The underlying `EReal`-valued bifunction. -/
  toFun : (Fin m → ℝ) → (Fin n → ℝ) → EReal
  /-- Global properness: `F` never takes the value `-∞` and is not identically `+∞`. -/
  proper : (∀ u x, toFun u x ≠ ⊥) ∧ ∃ u x, toFun u x ≠ ⊤
  /-- Convexity in the `x`-variable for each fixed `u`. -/
  convex : ∀ u, IsERealConvex (toFun u)

/-- Definition 38.0.4: Given proper convex bifunctions `F₁` and `F₂` from `ℝ^m` to `ℝ^n` (modeled
as `FiberwiseProperConvexBifunction m n`, i.e. `EReal`-valued and globally proper, with convexity in the
second variable), their infimal
convolution `F = F₁ □ F₂` is the bifunction defined pointwise in `u` by

`F u x = inf_{y : ℝ^n} (F₁ u (x - y) + F₂ u y)`. -/
noncomputable def bifunctionInfimalConvolution {m n : Nat}
    (F₁ F₂ : FiberwiseProperConvexBifunction m n) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x => ⨅ y : (Fin n → ℝ), F₁.toFun u (x - y) + F₂.toFun u y

/-- The domain (in the `u`-variable) of a bifunction `F : U → X → EReal`: those `u` for which the
function `x ↦ F u x` is not identically `+∞` (equivalently, there exists `x` with `F u x ≠ +∞`). -/
def bifunctionDom {U X : Type*} (F : U → X → EReal) : Set U :=
  {u | ∃ x : X, F u x ≠ ⊤}

/-- The `-∞`-effective domain (in the first variable) of a bifunction `F : U → X → EReal`:
those `u` for which there exists `x` with `F u x ≠ -∞`. This is used for concave/negated
bifunctions such as `F_*`. -/
def bifunctionDomBot {U X : Type*} (F : U → X → EReal) : Set U :=
  {u | ∃ x : X, F u x ≠ ⊥}

/-- A book-style convexity predicate for a bifunction in its second variable. -/
def IsFiberwiseConvexBifunction {U X : Type*} [AddCommMonoid X] [Module ℝ X] (F : U → X → EReal) : Prop :=
  ∀ u, IsERealConvex (F u)

/-- Helper for Theorem 38.1: the first one-dimensional test bifunction is fiberwise proper convex,
but outside the single allowed `u`-slice it is identically `⊤`. -/
noncomputable def helperForTheorem_38_1_counterexampleFirstBifunction :
    FiberwiseProperConvexBifunction 1 1 where
  toFun := fun u _x => if u 0 = 0 then (0 : EReal) else ⊤
  proper := by
    constructor
    · -- The construction only takes the values `0` and `⊤`, so `⊥` never appears.
      intro u x
      by_cases hu : u 0 = 0 <;> simp [hu]
    · -- The slice at `u = 0` is the finite constant zero function, so the global bifunction is proper.
      refine ⟨0, 0, ?_⟩
      simp
  convex := by
    intro u
    by_cases hu : u 0 = 0
    · -- On the distinguished slice the function is constant zero, whose epigraph is convex.
      have hconv0 :
          ConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (0 : EReal)) :=
        (properConvexFunctionOn_const (n := 1) (c := (0 : ℝ))).1
      have hEq :
          ERealEpigraph (fun _x : Fin 1 → ℝ => if u 0 = 0 then (0 : EReal) else ⊤) =
            epigraph (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (0 : EReal)) := by
        ext p
        constructor
        · intro hp
          change (if u 0 = 0 then (0 : EReal) else ⊤) ≤ (p.2 : EReal) at hp
          exact ⟨by trivial, by simpa [hu] using hp⟩
        · intro hp
          have hp' : (0 : EReal) ≤ (p.2 : EReal) := hp.2
          simpa [ERealEpigraph, hu] using hp'
      simpa [IsERealConvex, ConvexFunctionOn, hEq] using hconv0
    · -- Off that slice the function is constant `⊤`, whose epigraph is empty and hence convex.
      have hconvTop :
          ConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (⊤ : EReal)) :=
        convexFunctionOn_const_top (C := (Set.univ : Set (Fin 1 → ℝ)))
      have hEq :
          ERealEpigraph (fun _x : Fin 1 → ℝ => if u 0 = 0 then (0 : EReal) else ⊤) =
            epigraph (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (⊤ : EReal)) := by
        ext p
        simp [ERealEpigraph, epigraph, hu]
      simpa [IsERealConvex, ConvexFunctionOn, hEq] using hconvTop

/-- Helper for Theorem 38.1: the second one-dimensional test bifunction is the constant zero
bifunction, hence fiberwise proper convex. -/
noncomputable def helperForTheorem_38_1_counterexampleSecondBifunction :
    FiberwiseProperConvexBifunction 1 1 where
  toFun := fun _u _x => (0 : EReal)
  proper := by
    constructor
    · -- The constant zero bifunction never hits `⊥`.
      intro u x
      simp
    · -- Any point witnesses that the bifunction is not identically `⊤`.
      refine ⟨0, 0, by simp⟩
  convex := by
    intro u
    -- Every slice is the constant zero function, so its epigraph is convex.
    have hconv0 :
        ConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (0 : EReal)) :=
      (properConvexFunctionOn_const (n := 1) (c := (0 : ℝ))).1
    have hEq :
        ERealEpigraph (fun _x : Fin 1 → ℝ => (0 : EReal)) =
          epigraph (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (0 : EReal)) := by
      ext p
      constructor
      · intro hp
        change (0 : EReal) ≤ (p.2 : EReal) at hp
        exact ⟨by trivial, hp⟩
      · intro hp
        have hp' : (0 : EReal) ≤ (p.2 : EReal) := hp.2
        simpa [ERealEpigraph] using hp'
    simpa [IsERealConvex, ConvexFunctionOn, hEq] using hconv0

/-- Helper for Theorem 38.1: the offending slice where the first bifunction loses its domain. -/
def helperForTheorem_38_1_counterexampleU : Fin 1 → ℝ := fun _ => 1

/-- Helper for Theorem 38.1: the nonzero dual functional used to force the second left pairing to
be `⊥`. -/
noncomputable def helperForTheorem_38_1_counterexampleXStar :
    Module.Dual ℝ (Fin 1 → ℝ) :=
  LinearMap.proj 0

/-- Helper for Theorem 38.1: for the constant zero bifunction, the `iInf`-based left pairing at a
nonzero functional is `⊥`. -/
lemma helperForTheorem_38_1_counterexampleSecond_leftPairing_eq_bot :
    bifunctionLeftPairing helperForTheorem_38_1_counterexampleSecondBifunction.toFun
        helperForTheorem_38_1_counterexampleU
        helperForTheorem_38_1_counterexampleXStar = (⊥ : EReal) := by
  rw [bifunctionLeftPairing]
  rw [iInf_eq_bot]
  intro b hb
  rcases EReal.lt_iff_exists_rat_btwn.mp hb with ⟨q, -, hq⟩
  refine ⟨fun _ => q - 1, ?_⟩
  -- Evaluating at a sufficiently negative point pushes the linear term below any prescribed bound.
  have hlt : ((((q - 1 : ℚ) : ℝ) : EReal) < (b : EReal)) := by
    have hq' : ((((q - 1 : ℚ) : ℝ) : EReal) < (((q : ℚ) : ℝ) : EReal)) := by
      exact_mod_cast (show (q - 1 : ℚ) < q by linarith)
    exact lt_trans hq' hq
  simpa [helperForTheorem_38_1_counterexampleSecondBifunction,
    helperForTheorem_38_1_counterexampleU, helperForTheorem_38_1_counterexampleXStar] using hlt

/-- Helper for Theorem 38.1: the advertised pairing identity fails for the explicit
one-dimensional counterexample under the current `iInf`-based `bifunctionLeftPairing`. -/
lemma helperForTheorem_38_1_counterexample_pairing_failure :
    bifunctionLeftPairing
        (bifunctionInfimalConvolution
          helperForTheorem_38_1_counterexampleFirstBifunction
          helperForTheorem_38_1_counterexampleSecondBifunction)
        helperForTheorem_38_1_counterexampleU
        helperForTheorem_38_1_counterexampleXStar ≠
      bifunctionLeftPairing
          helperForTheorem_38_1_counterexampleFirstBifunction.toFun
          helperForTheorem_38_1_counterexampleU
          helperForTheorem_38_1_counterexampleXStar +
        bifunctionLeftPairing
          helperForTheorem_38_1_counterexampleSecondBifunction.toFun
          helperForTheorem_38_1_counterexampleU
          helperForTheorem_38_1_counterexampleXStar := by
  -- The infimal convolution and the first left pairing are both `⊤` on the bad slice.
  -- The second left pairing is `⊥`, so the right-hand side collapses to `⊤ + ⊥ = ⊥`.
  rw [helperForTheorem_38_1_counterexampleSecond_leftPairing_eq_bot]
  simp [bifunctionLeftPairing, bifunctionInfimalConvolution,
    helperForTheorem_38_1_counterexampleFirstBifunction,
    helperForTheorem_38_1_counterexampleSecondBifunction,
    helperForTheorem_38_1_counterexampleU, helperForTheorem_38_1_counterexampleXStar]

-- Proof sketch: Apply the single-variable infimal convolution results (cf. Theorem 16.4 in the
-- text) pointwise in `u` to the functions `x ↦ F₁.toFun u x` and `x ↦ F₂.toFun u x`, and then
-- unfold `bifunctionInfimalConvolution`, `bifunctionDom`, and `bifunctionLeftPairing`. The book’s
-- convention about `∞ - ∞` is handled by `EReal`’s totalized arithmetic (notably `⊥ + ⊤ = ⊥`).
/-- The textbook pairing `⟨F u, x*⟩` for a convex slice `x ↦ F u x`, interpreted as the Fenchel
conjugate value `sup_x (⟨x, x*⟩ - F u x)`. This is the object used in Theorem 38.1 via Theorem
16.4, unlike the earlier `iInf`-based bracket used for indicator-bifunction identities. -/
noncomputable def bifunctionConvexSlicePairing
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (F : U → X → EReal) (u : U) (xStar : Module.Dual ℝ X) : EReal :=
  ⨆ x : X, ((xStar x : ℝ) : EReal) - F u x

/-- Helper for Theorem 38.1: on `Set.univ`, the local epigraph predicate `ERealEpigraph`
coincides with the standard `epigraph` used by `ConvexFunctionOn`. -/
lemma helperForTheorem_38_1_epigraph_eq_univ {n : Nat} (f : (Fin n → ℝ) → EReal) :
    ERealEpigraph f = epigraph (Set.univ : Set (Fin n → ℝ)) f := by
  -- Both predicates say exactly that the function value is bounded above by the real height.
  ext p
  constructor
  · intro hp
    exact ⟨by trivial, hp⟩
  · intro hp
    exact hp.2

/-- Helper for Theorem 38.1: the textbook slice pairing is exactly the Fenchel conjugate of the
corresponding slice after identifying dual covectors with coordinate vectors. -/
lemma helperForTheorem_38_1_slicePairing_eq_fenchelConjugate (n : Nat)
    {U : Type*} [AddCommMonoid U] [Module ℝ U]
    (F : U → (Fin n → ℝ) → EReal)
    (u : U) (xStar : Module.Dual ℝ (Fin n → ℝ)) :
    bifunctionConvexSlicePairing F u xStar =
      fenchelConjugate n (F u) ((dotProductEquiv ℝ (Fin n)).symm xStar) := by
  -- Rewrite the conjugate as a supremum over points and identify the dual evaluation with the
  -- corresponding dot product.
  rw [bifunctionConvexSlicePairing, fenchelConjugate_eq_iSup]
  refine iSup_congr ?_
  intro x
  have hpair : (((dotProductEquiv ℝ (Fin n)).symm xStar) ⬝ᵥ x) = xStar x := by
    simpa using
      (dotProductEquiv_apply_apply ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm xStar) x).symm
  have hpairE :
      ((xStar x : ℝ) : EReal) =
        ((((dotProductEquiv ℝ (Fin n)).symm xStar) ⬝ᵥ x : ℝ) : EReal) := by
    exact_mod_cast hpair.symm
  rw [hpairE]
  simp [dotProduct_comm]

/-- Helper for Theorem 38.1: the slice of the bifunction infimal convolution agrees with the
ordinary infimal convolution of the two slices. -/
lemma helperForTheorem_38_1_slice_infimalConvolution_eq {m n : Nat}
    (F₁ F₂ : FiberwiseProperConvexBifunction m n) (u : Fin m → ℝ) :
    bifunctionInfimalConvolution F₁ F₂ u = infimalConvolution (F₁.toFun u) (F₂.toFun u) := by
  -- Reindex the slice infimum by the Chapter 1 parameterization of infimal convolution.
  funext x
  change (⨅ y : Fin n → ℝ, F₁.toFun u (x - y) + F₂.toFun u y) =
    infimalConvolution (F₁.toFun u) (F₂.toFun u) x
  rw [← sInf_range]
  have hrange :
      Set.range (fun y : Fin n → ℝ => F₂.toFun u y + F₁.toFun u (x - y)) =
        {r : EReal | ∃ z : Fin n → ℝ, r = F₂.toFun u z + F₁.toFun u (x - z)} := by
    ext r
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  have hrangeSwap :
      Set.range (fun y : Fin n → ℝ => F₁.toFun u (x - y) + F₂.toFun u y) =
        Set.range (fun y : Fin n → ℝ => F₂.toFun u y + F₁.toFun u (x - y)) := by
    ext r
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      simp [add_comm]
    · rintro ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      simp [add_comm]
  rw [hrangeSwap]
  rw [hrange]
  simpa [add_comm] using
    (infimalConvolution_eq_sInf_param (f := F₁.toFun u) (g := F₂.toFun u) x).symm

/-- Helper for Theorem 38.1: `u ∈ dom F` is equivalent to the corresponding slice having
nonempty ordinary effective domain. -/
lemma helperForTheorem_38_1_mem_dom_iff_sliceEffectiveDomain_nonempty {m n : Nat}
    (F : FiberwiseProperConvexBifunction m n) (u : Fin m → ℝ) :
    u ∈ bifunctionDom F.toFun ↔
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F.toFun u)).Nonempty := by
  constructor
  · intro hu
    rcases hu with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hlt : F.toFun u x < (⊤ : EReal) := (lt_top_iff_ne_top).2 hx
    have hxUniv : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    simpa [effectiveDomain_eq] using And.intro hxUniv hlt
  · intro hu
    rcases hu with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hlt : F.toFun u x < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hx
    exact (lt_top_iff_ne_top).1 hlt

/-- Helper for Theorem 38.1: a slice that lies in the `u`-domain is an ordinary proper convex
function on `Set.univ`. -/
lemma helperForTheorem_38_1_sliceProperConvex_of_mem_dom {m n : Nat}
    (F : FiberwiseProperConvexBifunction m n) (u : Fin m → ℝ)
    (hu : u ∈ bifunctionDom F.toFun) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (F.toFun u) := by
  rcases hu with ⟨x0, hx0⟩
  -- Convert the book-style convexity of the slice into the Chapter 1 `ConvexFunctionOn` predicate.
  have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (F.toFun u) := by
    simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ] using F.convex u
  -- A domain witness produces a point of the epigraph, which supplies the properness witness.
  have hne : Set.Nonempty (epigraph (Set.univ : Set (Fin n → ℝ)) (F.toFun u)) := by
    refine ⟨(x0, (F.toFun u x0).toReal), ?_⟩
    constructor
    · trivial
    · simpa using (EReal.le_coe_toReal (x := F.toFun u x0) hx0)
  -- Global properness of the bifunction rules out `-∞` on every slice.
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), F.toFun u x ≠ (⊥ : EReal) := by
    intro x hx
    exact F.proper.1 u x
  exact ⟨hconv, hne, hnotbot⟩

/-- Helper for Theorem 38.1: if a slice is outside `dom F`, then it is identically `⊤`. -/
lemma helperForTheorem_38_1_slice_eq_top_of_not_mem_dom {m n : Nat}
    (F : FiberwiseProperConvexBifunction m n) (u : Fin m → ℝ)
    (hu : u ∉ bifunctionDom F.toFun) :
    F.toFun u = fun _ : Fin n → ℝ => (⊤ : EReal) := by
  -- Outside the domain there is no point with finite value, so every value must be `⊤`.
  funext x
  by_contra hxtop
  exact hu ⟨x, hxtop⟩

/-- Helper for Theorem 38.1: the `u`-domain of the bifunction infimal convolution is exactly the
intersection of the two input `u`-domains. -/
lemma helperForTheorem_38_1_mem_dom_infimalConvolution_iff {m n : Nat}
    (F₁ F₂ : FiberwiseProperConvexBifunction m n) (u : Fin m → ℝ) :
    u ∈ bifunctionDom (bifunctionInfimalConvolution F₁ F₂) ↔
      u ∈ bifunctionDom F₁.toFun ∧ u ∈ bifunctionDom F₂.toFun := by
  constructor
  · intro hu
    -- Convert domain membership of the slice convolution into nonemptiness of its effective domain.
    have hDomNonempty :
        (effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (infimalConvolution (F₁.toFun u) (F₂.toFun u))).Nonempty := by
      rcases hu with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hx' : infimalConvolution (F₁.toFun u) (F₂.toFun u) x ≠ (⊤ : EReal) := by
        simpa [helperForTheorem_38_1_slice_infimalConvolution_eq] using hx
      have hlt : infimalConvolution (F₁.toFun u) (F₂.toFun u) x < (⊤ : EReal) :=
        (lt_top_iff_ne_top).2 hx'
      have hxUniv : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
        simp
      simpa [effectiveDomain_eq] using And.intro hxUniv hlt
    -- The Chapter 1 domain formula splits the slice domain into the Minkowski sum of the two
    -- effective domains, so a witness on the sum yields witnesses on both factors.
    have hEqDom :
        effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (infimalConvolution (F₁.toFun u) (F₂.toFun u)) =
          Set.image2 (fun x y => x + y)
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F₁.toFun u))
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F₂.toFun u)) :=
      effectiveDomain_infimalConvolution_eq_sum
        (f := F₁.toFun u) (g := F₂.toFun u) (hf := F₁.proper.1 u) (hg := F₂.proper.1 u)
    rw [hEqDom] at hDomNonempty
    rcases hDomNonempty with ⟨w, hw⟩
    rcases hw with ⟨x, hx, y, hy, rfl⟩
    constructor
    · refine ⟨x, ?_⟩
      have hlt : F₁.toFun u x < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using hx
      exact (lt_top_iff_ne_top).1 hlt
    · refine ⟨y, ?_⟩
      have hlt : F₂.toFun u y < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using hy
      exact (lt_top_iff_ne_top).1 hlt
  · intro hu
    rcases hu with ⟨hu1, hu2⟩
    rcases hu1 with ⟨x1, hx1⟩
    rcases hu2 with ⟨x2, hx2⟩
    -- Finite witnesses for the two input slices combine to a finite witness for the slice
    -- infimal convolution via the effective-domain sum formula.
    have hx1eff : x1 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F₁.toFun u) := by
      have hlt : F₁.toFun u x1 < (⊤ : EReal) := (lt_top_iff_ne_top).2 hx1
      have hx1Univ : x1 ∈ (Set.univ : Set (Fin n → ℝ)) := by
        simp
      simpa [effectiveDomain_eq] using And.intro hx1Univ hlt
    have hx2eff : x2 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F₂.toFun u) := by
      have hlt : F₂.toFun u x2 < (⊤ : EReal) := (lt_top_iff_ne_top).2 hx2
      have hx2Univ : x2 ∈ (Set.univ : Set (Fin n → ℝ)) := by
        simp
      simpa [effectiveDomain_eq] using And.intro hx2Univ hlt
    have hsumeff :
        x1 + x2 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (infimalConvolution (F₁.toFun u) (F₂.toFun u)) := by
      rw [effectiveDomain_infimalConvolution_eq_sum
        (f := F₁.toFun u) (g := F₂.toFun u) (hf := F₁.proper.1 u) (hg := F₂.proper.1 u)]
      exact ⟨x1, hx1eff, x2, hx2eff, rfl⟩
    refine ⟨x1 + x2, ?_⟩
    have hlt : infimalConvolution (F₁.toFun u) (F₂.toFun u) (x1 + x2) < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hsumeff
    simpa [helperForTheorem_38_1_slice_infimalConvolution_eq] using
      ((lt_top_iff_ne_top).1 hlt)

/-- Helper for Theorem 38.1: if one slice is missing from the domain, then the corresponding slice
of the bifunction infimal convolution is identically `⊤`. -/
lemma helperForTheorem_38_1_infimalConvolution_slice_eq_top_of_missing_dom {m n : Nat}
    (F₁ F₂ : FiberwiseProperConvexBifunction m n) (u : Fin m → ℝ)
    (hMissing : u ∉ bifunctionDom F₁.toFun ∨ u ∉ bifunctionDom F₂.toFun) :
    bifunctionInfimalConvolution F₁ F₂ u = fun _ : Fin n → ℝ => (⊤ : EReal) := by
  -- Collapse the missing slice to the constant `⊤` function and then simplify the ordinary
  -- infimal convolution formula.
  rw [helperForTheorem_38_1_slice_infimalConvolution_eq]
  funext x
  rcases hMissing with hMissing | hMissing
  · rw [helperForTheorem_38_1_slice_eq_top_of_not_mem_dom F₁ u hMissing]
    rw [infimalConvolution_eq_sInf_param]
    simp [F₂.proper.1]
  · rw [infimalConvolution_eq_sInf_param]
    rw [helperForTheorem_38_1_slice_eq_top_of_not_mem_dom F₂ u hMissing]
    simp [F₁.proper.1]

/-- Theorem 38.1: If `F₁` and `F₂` are proper convex bifunctions from `ℝⁿ` to `ℝⁿ`, then their
infimal convolution `F₁ □ F₂` is a convex bifunction, and

`dom (F₁ □ F₂) = dom F₁ ∩ dom F₂`.

Furthermore, for all `u` and all `x*` (modeled as an element of the dual space), one has

`⟨(F₁ □ F₂) u, x*⟩ = ⟨F₁ u, x*⟩ + ⟨F₂ u, x*⟩`,

with the text’s convention about `∞ - ∞`. -/

theorem bifunctionInfimalConvolution_convex_dom_eq_inter_leftPairing {m n : Nat}
    (F₁ F₂ : FiberwiseProperConvexBifunction m n) :
    IsFiberwiseConvexBifunction (bifunctionInfimalConvolution F₁ F₂) ∧
      bifunctionDom (bifunctionInfimalConvolution F₁ F₂) =
        bifunctionDom F₁.toFun ∩ bifunctionDom F₂.toFun ∧
      (∀ (u : Fin m → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)),
        bifunctionConvexSlicePairing (bifunctionInfimalConvolution F₁ F₂) u xStar =
          bifunctionConvexSlicePairing F₁.toFun u xStar +
            bifunctionConvexSlicePairing F₂.toFun u xStar) :=
  by
    constructor
    · intro u
      by_cases hu : u ∈ bifunctionDom F₁.toFun ∧ u ∈ bifunctionDom F₂.toFun
      · -- On a slice that lies in both domains, Chapter 1 gives convexity of the ordinary
        -- infimal convolution of the two proper convex slices.
        have hconv :
            ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
              (infimalConvolution (F₁.toFun u) (F₂.toFun u)) :=
          convexFunctionOn_infimalConvolution_of_proper
            (helperForTheorem_38_1_sliceProperConvex_of_mem_dom F₁ u hu.1)
            (helperForTheorem_38_1_sliceProperConvex_of_mem_dom F₂ u hu.2)
        simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ,
          helperForTheorem_38_1_slice_infimalConvolution_eq] using hconv
      · -- If one slice is missing from the domain, the slice infimal convolution is the constant
        -- `⊤` function, whose epigraph is empty and hence convex.
        have hMissing : u ∉ bifunctionDom F₁.toFun ∨ u ∉ bifunctionDom F₂.toFun := by
          by_cases hu1 : u ∈ bifunctionDom F₁.toFun
          · right
            intro hu2
            exact hu ⟨hu1, hu2⟩
          · exact Or.inl hu1
        have hconvTop :
            ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun _ => (⊤ : EReal)) :=
          convexFunctionOn_const_top (C := (Set.univ : Set (Fin n → ℝ)))
        simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ,
          helperForTheorem_38_1_infimalConvolution_slice_eq_top_of_missing_dom F₁ F₂ u hMissing] using
          hconvTop
    constructor
    · -- The `u`-domain identity is the slice-wise domain identity from Chapter 1, translated back
      -- through the local bifunction-domain definition.
      ext u
      simpa [Set.mem_inter_iff] using
        (helperForTheorem_38_1_mem_dom_infimalConvolution_iff F₁ F₂ u)
    · intro u xStar
      by_cases hu : u ∈ bifunctionDom F₁.toFun ∧ u ∈ bifunctionDom F₂.toFun
      · -- Route correction: the old `iInf`-based pairing route was the wrong object here. On a
        -- proper slice, rewrite the textbook bracket as a Fenchel conjugate and then apply Theorem
        -- 16.4 to the two-function family.
        have hproper :
            ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
              ((fun i : Fin 2 => if i = 0 then F₁.toFun u else F₂.toFun u) i) := by
          intro i
          fin_cases i
          · simpa using helperForTheorem_38_1_sliceProperConvex_of_mem_dom F₁ u hu.1
          · simpa using helperForTheorem_38_1_sliceProperConvex_of_mem_dom F₂ u hu.2
        have hfen :
            fenchelConjugate n
                (infimalConvolutionFamily (fun i : Fin 2 => if i = 0 then F₁.toFun u else F₂.toFun u)) =
              fun xStarVec =>
                ∑ i, fenchelConjugate n ((fun i : Fin 2 => if i = 0 then F₁.toFun u else F₂.toFun u) i)
                  xStarVec :=
          section16_fenchelConjugate_infimalConvolutionFamily
            (f := fun i : Fin 2 => if i = 0 then F₁.toFun u else F₂.toFun u) hproper
        rw [helperForTheorem_38_1_slicePairing_eq_fenchelConjugate,
          helperForTheorem_38_1_slicePairing_eq_fenchelConjugate,
          helperForTheorem_38_1_slicePairing_eq_fenchelConjugate]
        simpa [helperForTheorem_38_1_slice_infimalConvolution_eq,
          infimalConvolution_eq_infimalConvolutionFamily_two, Fin.sum_univ_two] using
          congrFun hfen ((dotProductEquiv ℝ (Fin n)).symm xStar)
      · -- If one slice is missing, all three pairings reduce to the conjugate of the constant
        -- `⊤` function, hence to `⊥`, and the identity is immediate.
        have hMissing : u ∉ bifunctionDom F₁.toFun ∨ u ∉ bifunctionDom F₂.toFun := by
          by_cases hu1 : u ∈ bifunctionDom F₁.toFun
          · right
            intro hu2
            exact hu ⟨hu1, hu2⟩
          · exact Or.inl hu1
        have htopInf :
            bifunctionInfimalConvolution F₁ F₂ u = fun _ : Fin n → ℝ => (⊤ : EReal) :=
          helperForTheorem_38_1_infimalConvolution_slice_eq_top_of_missing_dom F₁ F₂ u hMissing
        rcases hMissing with hMissing | hMissing
        · rw [helperForTheorem_38_1_slicePairing_eq_fenchelConjugate,
            helperForTheorem_38_1_slicePairing_eq_fenchelConjugate,
            helperForTheorem_38_1_slicePairing_eq_fenchelConjugate]
          simp [htopInf, helperForTheorem_38_1_slice_eq_top_of_not_mem_dom F₁ u hMissing,
            fenchelConjugate_eq_iSup]
        · rw [helperForTheorem_38_1_slicePairing_eq_fenchelConjugate,
            helperForTheorem_38_1_slicePairing_eq_fenchelConjugate,
            helperForTheorem_38_1_slicePairing_eq_fenchelConjugate]
          simp [htopInf, helperForTheorem_38_1_slice_eq_top_of_not_mem_dom F₂ u hMissing,
            fenchelConjugate_eq_iSup]

/-- Infimal convolution of two `EReal`-valued bifunctions in the second variable:
`(F₁ □ F₂) u x = inf_y (F₁ u (x - y) + F₂ u y)`. This is the same operation as
`bifunctionInfimalConvolution`, but for raw bifunctions on arbitrary modules (e.g. on dual spaces). -/
noncomputable def bifunctionInfimalConvolutionInSecond
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
    (F₁ F₂ : U → X → EReal) : U → X → EReal :=
  fun u x => ⨅ y : X, F₁ u (x - y) + F₂ u y

/-- Helper for Theorem 38.2: the first Section 38.1 counterexample bifunction is finite exactly
on the zero slice in the `u`-variable. -/
lemma helperForTheorem_38_2_counterexample_firstDom :
    bifunctionDom helperForTheorem_38_1_counterexampleFirstBifunction.toFun =
      {u : Fin 1 → ℝ | u 0 = 0} := by
  ext u
  constructor
  · intro hu
    rcases hu with ⟨x, hx⟩
    by_cases hu0 : u 0 = 0
    · -- On the admissible slice the domain condition is immediate.
      exact hu0
    · -- Off that slice the bifunction is identically `⊤`, contradicting domain membership.
      simp [helperForTheorem_38_1_counterexampleFirstBifunction, hu0] at hx
  · intro hu0
    -- The zero `x`-value witnesses that this slice is in the domain.
    have hu0' : u 0 = 0 := by
      simpa using hu0
    refine ⟨0, ?_⟩
    simp [helperForTheorem_38_1_counterexampleFirstBifunction, hu0']

/-- Helper for Theorem 38.2: in one dimension, the zero slice `u 0 = 0` is exactly the zero
submodule. -/
lemma helperForTheorem_38_2_counterexample_zeroSlice_eq_bot :
    ({u : Fin 1 → ℝ | u 0 = 0} : Set (Fin 1 → ℝ)) =
      ((⊥ : Submodule ℝ (Fin 1 → ℝ)) : Set (Fin 1 → ℝ)) := by
  ext u
  constructor
  · intro hu0
    -- A one-dimensional vector with vanishing only coordinate must be the zero vector.
    change u = 0
    ext i
    fin_cases i
    simpa using hu0
  · intro hu
    -- Membership in the zero submodule rewrites exactly to the vanishing coordinate equation.
    change u = 0 at hu
    simp [hu]

/-- Helper for Theorem 38.2: the second Section 38.1 counterexample bifunction has full
`u`-domain. -/
lemma helperForTheorem_38_2_counterexample_secondDom :
    bifunctionDom helperForTheorem_38_1_counterexampleSecondBifunction.toFun =
      (Set.univ : Set (Fin 1 → ℝ)) := by
  ext u
  constructor
  · intro _
    -- Every `u` belongs to the domain because the bifunction is identically zero.
    simp
  · intro _
    -- The zero `x`-value witnesses finiteness on every slice.
    refine ⟨0, ?_⟩
    simp [helperForTheorem_38_1_counterexampleSecondBifunction]

/-- Helper for Theorem 38.2: the Section 38.1 counterexample pair satisfies the relative-interior
qualification hypothesis appearing in the theorem statement. -/
lemma helperForTheorem_38_2_counterexample_hri :
    (intrinsicInterior ℝ (bifunctionDom helperForTheorem_38_1_counterexampleFirstBifunction.toFun) ∩
        intrinsicInterior ℝ
          (bifunctionDom helperForTheorem_38_1_counterexampleSecondBifunction.toFun)).Nonempty := by
  refine ⟨0, ?_⟩
  constructor
  · -- The first domain is the zero submodule, whose intrinsic interior is itself.
    rw [helperForTheorem_38_2_counterexample_firstDom,
      helperForTheorem_38_2_counterexample_zeroSlice_eq_bot]
    simp
  · -- The second domain is all of space, so its interior point is automatically intrinsic.
    rw [helperForTheorem_38_2_counterexample_secondDom]
    exact
      interior_subset_intrinsicInterior
        (by simp : (0 : Fin 1 → ℝ) ∈ interior (Set.univ : Set (Fin 1 → ℝ)))

/-- Helper for Theorem 38.2: at the offending dual point, the adjoint of the infimal convolution
evaluates to `0`. -/
lemma helperForTheorem_38_2_counterexample_leftValue :
    bifunctionAdjoint
        (bifunctionInfimalConvolution
          helperForTheorem_38_1_counterexampleFirstBifunction
          helperForTheorem_38_1_counterexampleSecondBifunction)
        (0 : Module.Dual ℝ (Fin 1 → ℝ))
        helperForTheorem_38_1_counterexampleXStar = 0 := by
  -- Evaluate the infimum at `(u, x) = (0, 0)` for the upper bound, then show every summand is
  -- bounded below by `0`.
  rw [bifunctionAdjoint]
  apply le_antisymm
  · refine le_trans (iInf_le _ (0 : Fin 1 → ℝ)) ?_
    refine le_trans (iInf_le _ (0 : Fin 1 → ℝ)) ?_
    simp [bifunctionInfimalConvolution, helperForTheorem_38_1_counterexampleFirstBifunction,
      helperForTheorem_38_1_counterexampleSecondBifunction,
      helperForTheorem_38_1_counterexampleXStar]
  · refine le_iInf ?_
    intro u
    refine le_iInf ?_
    intro x
    by_cases hu : u 0 = 0
    · simp [bifunctionInfimalConvolution, helperForTheorem_38_1_counterexampleFirstBifunction,
        helperForTheorem_38_1_counterexampleSecondBifunction,
        helperForTheorem_38_1_counterexampleXStar, hu]
    · simp [bifunctionInfimalConvolution, helperForTheorem_38_1_counterexampleFirstBifunction,
        helperForTheorem_38_1_counterexampleSecondBifunction,
        helperForTheorem_38_1_counterexampleXStar, hu]

/-- Helper for Theorem 38.2: the first counterexample bifunction has adjoint value `0` at the
dual origin. -/
lemma helperForTheorem_38_2_counterexample_firstAdjointZero :
    bifunctionAdjoint helperForTheorem_38_1_counterexampleFirstBifunction.toFun
      (0 : Module.Dual ℝ (Fin 1 → ℝ)) (0 : Module.Dual ℝ (Fin 1 → ℝ)) = 0 := by
  -- The zero primal pair realizes the value `0`, and every other summand is at least `0`.
  rw [bifunctionAdjoint]
  apply le_antisymm
  · refine le_trans (iInf_le _ (0 : Fin 1 → ℝ)) ?_
    refine le_trans (iInf_le _ (0 : Fin 1 → ℝ)) ?_
    simp [helperForTheorem_38_1_counterexampleFirstBifunction]
  · refine le_iInf ?_
    intro u
    refine le_iInf ?_
    intro x
    by_cases hu : u 0 = 0
    · simp [helperForTheorem_38_1_counterexampleFirstBifunction, hu]
    · simp [helperForTheorem_38_1_counterexampleFirstBifunction, hu]

/-- Helper for Theorem 38.2: the second counterexample bifunction has adjoint value `⊥` at the
offending dual witness. -/
lemma helperForTheorem_38_2_counterexample_secondAdjointBot :
    bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun
      (0 : Module.Dual ℝ (Fin 1 → ℝ)) helperForTheorem_38_1_counterexampleXStar = (⊥ : EReal) := by
  -- Evaluating at a sufficiently large positive primal point drives the linear term to `-∞`.
  rw [bifunctionAdjoint, iInf_eq_bot]
  intro b hb
  rcases EReal.lt_iff_exists_rat_btwn.mp hb with ⟨q, -, hq⟩
  refine ⟨fun _ => (1 : ℝ) - q, ?_⟩
  refine lt_of_le_of_lt (iInf_le _ (0 : Fin 1 → ℝ)) ?_
  have hqminus : (-((((1 : ℝ) - q) : ℝ) : EReal) < (b : EReal)) := by
    have hq' : (-((((1 : ℝ) - q) : ℝ) : EReal) < (((q : ℚ) : ℝ) : EReal)) := by
      exact_mod_cast (show -((1 : ℝ) - q) < (q : ℝ) by linarith)
    exact lt_trans hq' hq
  simpa [helperForTheorem_38_1_counterexampleSecondBifunction,
    helperForTheorem_38_1_counterexampleXStar, sub_eq_add_neg]
    using hqminus

/-- Helper for Theorem 38.2: at the same dual point, the infimal convolution of the adjoints
evaluates to `⊥`. -/
lemma helperForTheorem_38_2_counterexample_rightValue :
    bifunctionInfimalConvolutionInSecond
        (bifunctionAdjoint helperForTheorem_38_1_counterexampleFirstBifunction.toFun)
        (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun)
        (0 : Module.Dual ℝ (Fin 1 → ℝ))
        helperForTheorem_38_1_counterexampleXStar = (⊥ : EReal) := by
  -- Choosing the outer witness `y = helperForTheorem_38_1_counterexampleXStar` produces the value
  -- `⊥`, and `⊥` is the global lower bound in `EReal`.
  apply le_antisymm
  · refine le_trans (iInf_le _ helperForTheorem_38_1_counterexampleXStar) ?_
    have hFirst :
        bifunctionAdjoint helperForTheorem_38_1_counterexampleFirstBifunction.toFun
          (0 : Module.Dual ℝ (Fin 1 → ℝ))
          (helperForTheorem_38_1_counterexampleXStar -
            helperForTheorem_38_1_counterexampleXStar) = 0 := by
      simpa using helperForTheorem_38_2_counterexample_firstAdjointZero
    rw [hFirst, helperForTheorem_38_2_counterexample_secondAdjointBot]
    simp
  · exact bot_le

/-- Helper for Theorem 38.2: the advertised equality already fails pointwise at the explicit dual
witness from Section 38.1. -/
lemma helperForTheorem_38_2_counterexample_pointwiseMismatch :
    bifunctionAdjoint
        (bifunctionInfimalConvolution
          helperForTheorem_38_1_counterexampleFirstBifunction
          helperForTheorem_38_1_counterexampleSecondBifunction)
        (0 : Module.Dual ℝ (Fin 1 → ℝ))
        helperForTheorem_38_1_counterexampleXStar ≠
      bifunctionInfimalConvolutionInSecond
        (bifunctionAdjoint helperForTheorem_38_1_counterexampleFirstBifunction.toFun)
        (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun)
        (0 : Module.Dual ℝ (Fin 1 → ℝ))
        helperForTheorem_38_1_counterexampleXStar := by
  -- Compare the two sides at the explicit witness using the already computed values `0` and `⊥`.
  rw [helperForTheorem_38_2_counterexample_leftValue,
    helperForTheorem_38_2_counterexample_rightValue]
  exact EReal.zero_ne_bot

/-- Helper for Theorem 38.2: the Section 38.1 counterexample bifunctions violate the advertised
adjoint identity under the current local definitions. -/
lemma helperForTheorem_38_2_counterexample_adjoint_failure :
    bifunctionAdjoint
        (bifunctionInfimalConvolution
          helperForTheorem_38_1_counterexampleFirstBifunction
          helperForTheorem_38_1_counterexampleSecondBifunction) ≠
      bifunctionInfimalConvolutionInSecond
        (bifunctionAdjoint helperForTheorem_38_1_counterexampleFirstBifunction.toFun)
        (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun) := by
  intro hEq
  -- Evaluate the putative function equality at the explicit dual witness from Section 38.1.
  exact helperForTheorem_38_2_counterexample_pointwiseMismatch
    (congrFun (congrFun hEq (0 : Module.Dual ℝ (Fin 1 → ℝ)))
      helperForTheorem_38_1_counterexampleXStar)

/-- Helper for Theorem 38.2: the current theorem schema has an explicit one-dimensional
counterexample satisfying the relative-interior qualification hypothesis. -/
lemma helperForTheorem_38_2_existsCounterexample :
    ∃ (F₁ F₂ : FiberwiseProperConvexBifunction 1 1),
      (intrinsicInterior ℝ (bifunctionDom F₁.toFun) ∩
          intrinsicInterior ℝ (bifunctionDom F₂.toFun)).Nonempty ∧
        bifunctionAdjoint (bifunctionInfimalConvolution F₁ F₂) ≠
          bifunctionInfimalConvolutionInSecond (bifunctionAdjoint F₁.toFun)
            (bifunctionAdjoint F₂.toFun) := by
  -- Package the Section 38.1 witness together with the proved qualification and failure lemmas.
  refine ⟨helperForTheorem_38_1_counterexampleFirstBifunction,
    helperForTheorem_38_1_counterexampleSecondBifunction, ?_⟩
  constructor
  · exact helperForTheorem_38_2_counterexample_hri
  · exact helperForTheorem_38_2_counterexample_adjoint_failure

/-- Helper for Theorem 38.2: after specializing the theorem statement to the Section 38.1 witness
pair, even the resulting single implication is already false. -/
lemma helperForTheorem_38_2_specializedImplicationFalse :
    ¬ ((intrinsicInterior ℝ
            (bifunctionDom helperForTheorem_38_1_counterexampleFirstBifunction.toFun) ∩
          intrinsicInterior ℝ
            (bifunctionDom helperForTheorem_38_1_counterexampleSecondBifunction.toFun)).Nonempty →
        bifunctionAdjoint
            (bifunctionInfimalConvolution
              helperForTheorem_38_1_counterexampleFirstBifunction
              helperForTheorem_38_1_counterexampleSecondBifunction) =
          bifunctionInfimalConvolutionInSecond
            (bifunctionAdjoint helperForTheorem_38_1_counterexampleFirstBifunction.toFun)
            (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun)) := by
  intro hSpecialized
  -- Feed the established relative-interior witness into the specialized theorem implication.
  exact helperForTheorem_38_2_counterexample_adjoint_failure
    (hSpecialized helperForTheorem_38_2_counterexample_hri)

/-- Helper for Theorem 38.2: the universal theorem schema is already false under the current
`iInf`-based bifunction adjoint formalization. -/
lemma helperForTheorem_38_2_universalClaimFalse :
    ¬ (∀ {m n : Nat} (F₁ F₂ : FiberwiseProperConvexBifunction m n)
          (_hri :
            (intrinsicInterior ℝ (bifunctionDom F₁.toFun) ∩
                intrinsicInterior ℝ (bifunctionDom F₂.toFun)).Nonempty),
          bifunctionAdjoint (bifunctionInfimalConvolution F₁ F₂) =
            bifunctionInfimalConvolutionInSecond (bifunctionAdjoint F₁.toFun)
              (bifunctionAdjoint F₂.toFun)) := by
  intro hUniversal
  -- Specialize the putative universal theorem to the explicit Section 38.1 witness pair.
  exact helperForTheorem_38_2_specializedImplicationFalse (fun hri =>
    hUniversal (m := 1) (n := 1)
      helperForTheorem_38_1_counterexampleFirstBifunction
      helperForTheorem_38_1_counterexampleSecondBifunction hri)

/-! The following operators implement the conventions in Chapter 30 and §38.2. They coexist
with the legacy operators above precisely so that the proved counterexample continues to document
why the old statement was false. -/

/-- The textbook adjoint of a convex bifunction:
`F* x* u* = inf_{u,x} (F u x - ⟨x,x*⟩ + ⟨u,u*⟩)`. -/
noncomputable def textbookBifunctionAdjoint
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun xStar uStar =>
    ⨅ (u : Fin m → ℝ) (x : Fin n → ℝ),
      F u x - ((x ⬝ᵥ xStar : ℝ) : EReal) + ((u ⬝ᵥ uStar : ℝ) : EReal)

/-- Addition with the concave extended-real convention: `+∞` is absorbing; away from
`+∞` ordinary `EReal` addition has the required `-∞` behavior. -/
noncomputable def erealAddConcaveBook (a b : EReal) : EReal :=
  -((-a) + (-b))

/-- The concave analogue of infimal convolution used on adjoints in Theorem 38.2. -/
noncomputable def concaveBifunctionInfimalConvolutionInSecond
    {m n : Nat} (G₁ G₂ : (Fin n → ℝ) → (Fin m → ℝ) → EReal) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun xStar uStar =>
    ⨆ vStar : Fin m → ℝ,
      erealAddConcaveBook (G₁ xStar (uStar - vStar)) (G₂ xStar vStar)

lemma neg_fenchelConjugate_eq_iInf_tilted
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    -fenchelConjugate n (F u) xStar =
      ⨅ x : Fin n → ℝ, F u x - (((x ⬝ᵥ xStar : ℝ)) : EReal) := by
  rw [fenchelConjugate_eq_iSup]
  have hneg :=
    congrArg Neg.neg
      (helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
        (fun x : Fin n → ℝ =>
          -(((((xStar ⬝ᵥ x : ℝ)) : EReal) - F u x))))
  have hterm : ∀ x : Fin n → ℝ,
      -((((dotProduct xStar x : ℝ) : EReal) - F u x)) =
        F u x - (((dotProduct xStar x : ℝ) : EReal)) := by
    intro x
    calc
      -((((dotProduct xStar x : ℝ) : EReal) - F u x)) =
          -(((dotProduct xStar x : ℝ) : EReal)) + F u x := by
            exact EReal.neg_sub
              (x := (((dotProduct xStar x : ℝ) : EReal))) (y := F u x)
              (Or.inl (by simp)) (Or.inl (by simp))
      _ = F u x - (((dotProduct xStar x : ℝ) : EReal)) := by
            simp [sub_eq_add_neg, add_comm]
  have hterm' : ∀ x : Fin n → ℝ,
      -(F u x - ((dotProduct xStar x : ℝ) : EReal)) =
        ((dotProduct xStar x : ℝ) : EReal) - F u x := by
    intro x
    calc
      -(F u x - ((dotProduct xStar x : ℝ) : EReal)) =
          -F u x + ((dotProduct xStar x : ℝ) : EReal) := by
            exact EReal.neg_sub
              (x := F u x) (y := ((dotProduct xStar x : ℝ) : EReal))
              (Or.inr (by simp)) (Or.inr (by simp))
      _ = ((dotProduct xStar x : ℝ) : EReal) - F u x := by
            simp [sub_eq_add_neg, add_comm]
  simpa only [hterm, hterm', neg_neg, dotProduct_comm] using hneg.symm

lemma textbookBifunctionAdjoint_eq_concaveConjugate_pairing
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    textbookBifunctionAdjoint F xStar uStar =
      concaveConjugate (fun u => fenchelConjugate n (F u) xStar) uStar := by
  rw [textbookBifunctionAdjoint, helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
  congr with u
  rw [neg_fenchelConjugate_eq_iInf_tilted]
  simpa [add_comm, add_left_comm, add_assoc] using
    (helperForTheorem_6_30_15_real_add_iInf (c := (u ⬝ᵥ uStar : ℝ))
      (f := fun x : Fin n → ℝ => F u x - (((x ⬝ᵥ xStar : ℝ)) : EReal))).symm

lemma effectiveDomain_neg_fenchelConjugate_slice_eq_bifunctionDom
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n) (xStar : Fin n → ℝ) :
    effectiveDomain (Set.univ : Set (Fin m → ℝ))
        (fun u => -fenchelConjugate n (F.toFun u) xStar) =
      bifunctionDom F.toFun := by
  ext u
  simp only [effectiveDomain_eq, Set.mem_setOf_eq, Set.mem_univ, true_and,
    lt_top_iff_ne_top, bifunctionDom]
  constructor
  · intro hnegTop
    rw [fenchelConjugate_eq_iSup] at hnegTop
    have hsupBot :
        (⨆ x : Fin n → ℝ,
          (((dotProduct x xStar : ℝ) : EReal) - F.toFun u x)) ≠ (⊥ : EReal) := by
      intro hbot
      exact hnegTop ((EReal.neg_eq_top_iff).2 hbot)
    by_contra hdom
    push_neg at hdom
    apply hsupBot
    rw [iSup_eq_bot]
    intro x
    simp [hdom x]
  · rintro ⟨x, hx⟩
    rw [fenchelConjugate_eq_iSup]
    intro hnegTop
    have hsupBot :
        (⨆ y : Fin n → ℝ,
          (((dotProduct y xStar : ℝ) : EReal) - F.toFun u y)) = (⊥ : EReal) :=
      (EReal.neg_eq_top_iff).1 hnegTop
    have hxBot :
        (((dotProduct x xStar : ℝ) : EReal) - F.toFun u x) = (⊥ : EReal) :=
      (iSup_eq_bot.mp hsupBot) x
    cases hval : F.toFun u x with
    | bot => exact (F.proper.1 u x hval).elim
    | top => exact (hx hval).elim
    | coe r =>
        have hcoe :
            (((dotProduct x xStar - r : ℝ) : EReal)) = (⊥ : EReal) := by
          simpa [hval] using hxBot
        exact EReal.coe_ne_bot _ hcoe

/-- For a jointly convex bifunction, the negative of a frozen slice conjugate is convex in the
parameter variable. -/
lemma neg_fenchelConjugate_slice_convexFunction
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (hconv : ConvexBifunction F.toFun) (xStar : Fin n → ℝ) :
    ConvexFunction (fun u : Fin m → ℝ => -fenchelConjugate n (F.toFun u) xStar) := by
  have hGraph : IsGraphConvexBifunction F.toFun := by
    have hNoBot :
        ∀ z : Fin (m + n) → ℝ, bifunctionGraphFunction F.toFun z ≠ (⊥ : EReal) := by
      intro z
      exact F.proper.1 _ _
    have hJensen :=
      helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ hconv hNoBot
    simpa [IsGraphConvexBifunction, bifunctionGraphFunction,
      graphFunctionOfBifunction] using hJensen
  have hProjection :=
    helperForLemma33_0_22_tiltedProjection_isConvexFunction
      (F := F.toFun) hGraph xStar
  rw [helperForLemma33_0_22_swappedNegatedAdjointSection_eq_projectionImage_tiltedGraph
    (F := F.toFun) xStar] at hProjection
  simpa [convexBifunctionAdjoint, convexBifunctionPairing, convexConjugate] using hProjection

/-- A convex frozen slice-conjugate is proper as soon as it has no `-∞` values. -/
lemma neg_fenchelConjugate_slice_properConvex_of_ne_bot
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (hconv : ConvexBifunction F.toFun) (xStar : Fin n → ℝ)
    (hneBot : ∀ u : Fin m → ℝ, -fenchelConjugate n (F.toFun u) xStar ≠ (⊥ : EReal)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ))
      (fun u => -fenchelConjugate n (F.toFun u) xStar) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [ConvexFunction] using neg_fenchelConjugate_slice_convexFunction F hconv xStar
  · obtain ⟨u, x, hx⟩ := F.proper.2
    have huDom : u ∈ bifunctionDom F.toFun := ⟨x, hx⟩
    have huEff :
        u ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (fun v => -fenchelConjugate n (F.toFun v) xStar) := by
      rw [effectiveDomain_neg_fenchelConjugate_slice_eq_bifunctionDom F xStar]
      exact huDom
    exact (nonempty_epigraph_iff_nonempty_effectiveDomain
      (S := (Set.univ : Set (Fin m → ℝ)))
      (f := fun v => -fenchelConjugate n (F.toFun v) xStar)).2 ⟨u, huEff⟩
  · intro u _
    exact hneBot u

/-- The frozen slice conjugate of a bifunction infimal convolution is the sum of the two frozen
slice conjugates. -/
lemma fenchelConjugate_bifunctionInfimalConvolution_eq_add
    {m n : Nat} (F₁ F₂ : FiberwiseProperConvexBifunction m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    fenchelConjugate n (bifunctionInfimalConvolution F₁ F₂ u) xStar =
      fenchelConjugate n (F₁.toFun u) xStar + fenchelConjugate n (F₂.toFun u) xStar := by
  let xDual : Module.Dual ℝ (Fin n → ℝ) := (dotProductEquiv ℝ (Fin n)) xStar
  have hpair :=
    (bifunctionInfimalConvolution_convex_dom_eq_inter_leftPairing F₁ F₂).2.2 u xDual
  simpa [xDual, helperForTheorem_38_1_slicePairing_eq_fenchelConjugate] using hpair

/-- If the negative of a concave function takes the value `-∞`, its concave conjugate is
identically `-∞`. -/
lemma concaveConjugate_eq_bot_of_neg_value_eq_bot
    {m : Nat} (g : (Fin m → ℝ) → EReal) (u₀ : Fin m → ℝ)
    (hbot : -g u₀ = (⊥ : EReal)) (uStar : Fin m → ℝ) :
    concaveConjugate g uStar = (⊥ : EReal) := by
  rw [helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
  apply le_antisymm
  · refine le_trans (iInf_le _ u₀) ?_
    simp [hbot]
  · exact bot_le

/-- A concave conjugate is not `+∞` if the primal concave function is not `-∞` at one
point. -/
lemma concaveConjugate_ne_top_of_value_ne_bot
    {m : Nat} (g : (Fin m → ℝ) → EReal) (u₀ : Fin m → ℝ)
    (hne : g u₀ ≠ (⊥ : EReal)) (uStar : Fin m → ℝ) :
    concaveConjugate g uStar ≠ (⊤ : EReal) := by
  rw [helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
  intro htop
  have hle := iInf_le
    (fun u : Fin m → ℝ => (((dotProduct u uStar : ℝ) : EReal) + -g u)) u₀
  rw [htop] at hle
  have htermTop :
      (((dotProduct u₀ uStar : ℝ) : EReal) + -g u₀) = (⊤ : EReal) :=
    top_unique hle
  cases hg : g u₀ with
  | bot => exact (hne hg).elim
  | top => simp [hg] at htermTop
  | coe r =>
      have hcoe :
          (((dotProduct u₀ uStar - r : ℝ) : EReal)) = (⊤ : EReal) := by
        simpa [hg] using htermTop
      exact EReal.coe_ne_top _ hcoe

/-- Concave extended-real addition with a left `-∞` input is `-∞` provided the other input
is not `+∞`. -/
lemma erealAddConcaveBook_bot_left_of_ne_top (b : EReal) (hb : b ≠ (⊤ : EReal)) :
    erealAddConcaveBook (⊥ : EReal) b = (⊥ : EReal) := by
  cases hb' : b with
  | bot => simp [erealAddConcaveBook, hb']
  | top => exact (hb hb').elim
  | coe r => simp [erealAddConcaveBook, hb']

/-- The symmetric right-absorbing form of concave extended-real addition. -/
lemma erealAddConcaveBook_bot_right_of_ne_top (a : EReal) (ha : a ≠ (⊤ : EReal)) :
    erealAddConcaveBook a (⊥ : EReal) = (⊥ : EReal) := by
  simpa [erealAddConcaveBook, add_comm] using
    erealAddConcaveBook_bot_left_of_ne_top a ha

/-- The relative-interior qualification for two functions, converted to the Euclidean-space
family form used by Theorem 16.4. -/
lemma section16_hri_two_of_intrinsic
    {m : Nat} (f₁ f₂ : (Fin m → ℝ) → EReal)
    (hri :
      (intrinsicInterior ℝ (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f₁) ∩
        intrinsicInterior ℝ
          (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f₂)).Nonempty) :
    Set.Nonempty
      (⋂ i : Fin 2,
        euclideanRelativeInterior m
          ((fun x : EuclideanSpace ℝ (Fin m) => (x : Fin m → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → ℝ))
              (if i = 0 then f₁ else f₂))) := by
  rcases hri with ⟨u₀, hu₁, hu₂⟩
  have hu₁' :
      u₀ ∈ euclideanRelativeInterior_fin m
        (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f₁) := by
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    exact hu₁
  have hu₂' :
      u₀ ∈ euclideanRelativeInterior_fin m
        (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f₂) := by
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    exact hu₂
  let e := EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  let y₀ : EuclideanSpace ℝ (Fin m) := e.symm u₀
  have hPreimage (C : Set (Fin m → ℝ)) :
      ((fun x : EuclideanSpace ℝ (Fin m) => (x : Fin m → ℝ)) ⁻¹' C) = e.symm '' C := by
    ext y
    constructor
    · intro hy
      exact ⟨e y, hy, by simp [e]⟩
    · rintro ⟨x, hx, rfl⟩
      simpa [e] using hx
  refine ⟨y₀, Set.mem_iInter.2 ?_⟩
  intro i
  fin_cases i
  · have hy :=
      (mem_euclideanRelativeInterior_fin_iff
        (n := m) (C := effectiveDomain (Set.univ : Set (Fin m → ℝ)) f₁)
        (x := u₀)).1 hu₁'
    simpa [y₀, e, hPreimage] using hy
  · have hy :=
      (mem_euclideanRelativeInterior_fin_iff
        (n := m) (C := effectiveDomain (Set.univ : Set (Fin m → ℝ)) f₂)
        (x := u₀)).1 hu₂'
    simpa [y₀, e, hPreimage] using hy

/-- Binary infimal convolution written as an indexed infimum over its second summand. -/
lemma infimalConvolution_eq_iInf_second {m : Nat}
    (f g : (Fin m → ℝ) → EReal) (x : Fin m → ℝ) :
    infimalConvolution f g x = ⨅ z : Fin m → ℝ, g z + f (x - z) := by
  rw [infimalConvolution_eq_sInf_param]
  have hset :
      {r : EReal | ∃ z : Fin m → ℝ, r = g z + f (x - z)} =
        Set.range (fun z : Fin m → ℝ => g z + f (x - z)) := by
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  rw [hset, sInf_range]

/-- An improper convex function is `-∞` at every intrinsic-relative-interior point of its
effective domain, in `Fin` coordinates. -/
lemma improperConvexFunctionOn_eq_bot_on_intrinsicInterior_fin
    {m : Nat} {f : (Fin m → ℝ) → EReal}
    (himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ
      (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f)) :
    f u = (⊥ : EReal) := by
  have huFin :
      u ∈ euclideanRelativeInterior_fin m
        (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) := by
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    exact hu
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  have hPreimage :
      ((fun x : EuclideanSpace ℝ (Fin m) => (x : Fin m → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) =
        e.symm '' effectiveDomain (Set.univ : Set (Fin m → ℝ)) f := by
    ext y
    constructor
    · intro hy
      exact ⟨e y, hy, by simp [e]⟩
    · rintro ⟨x, hx, rfl⟩
      simpa [e] using hx
  have huE :
      e.symm u ∈ euclideanRelativeInterior m
        ((fun x : EuclideanSpace ℝ (Fin m) => (x : Fin m → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) := by
    have huImage :=
      (mem_euclideanRelativeInterior_fin_iff
        (n := m) (C := effectiveDomain (Set.univ : Set (Fin m → ℝ)) f)
        (x := u)).1 huFin
    simpa [e, hPreimage] using huImage
  simpa [e] using
    improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain
      (f := f) himproper (e.symm u) huE

/-- The concave conjugate of a sum is the concave sup-convolution of the conjugates under the
usual relative-interior qualification. -/
lemma concaveConjugate_add_eq_supConvolution
    {m : Nat} (g₁ g₂ : (Fin m → ℝ) → EReal)
    (hf₁ : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun u => -g₁ u))
    (hf₂ : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun u => -g₂ u))
    (hri :
      (intrinsicInterior ℝ
          (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun u => -g₁ u)) ∩
        intrinsicInterior ℝ
          (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun u => -g₂ u))).Nonempty)
    (uStar : Fin m → ℝ) :
    concaveConjugate (fun u => g₁ u + g₂ u) uStar =
      ⨆ v : Fin m → ℝ,
        erealAddConcaveBook (concaveConjugate g₁ (uStar - v))
          (concaveConjugate g₂ v) := by
  let fTwo : Fin 2 → (Fin m → ℝ) → EReal :=
    fun i => if i = 0 then (fun u => -g₁ u) else (fun u => -g₂ u)
  have hfTwo :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hf₁
    · simpa [fTwo] using hf₂
  have hriTwo :=
    section16_hri_two_of_intrinsic (fun u => -g₁ u) (fun u => -g₂ u) hri
  have hSec :=
    section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
      fTwo hfTwo hriTwo
  have hFen :
      fenchelConjugate m (fun u => -g₁ u + -g₂ u) =
        infimalConvolution (fenchelConjugate m (fun u => -g₁ u))
          (fenchelConjugate m (fun u => -g₂ u)) := by
    simpa [fTwo, Fin.sum_univ_two, infimalConvolution_eq_infimalConvolutionFamily_two] using hSec.1
  have hg₁Top : ∀ u, g₁ u ≠ (⊤ : EReal) := by
    intro u htop
    exact hf₁.2.2 u (by simp) (by simp [htop])
  have hg₂Top : ∀ u, g₂ u ≠ (⊤ : EReal) := by
    intro u htop
    exact hf₂.2.2 u (by simp) (by simp [htop])
  have hnegAdd :
      (fun u => -(g₁ u + g₂ u)) = (fun u => -g₁ u + -g₂ u) := by
    funext u
    exact EReal.neg_add (Or.inr (hg₂Top u)) (Or.inl (hg₁Top u))
  rw [helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted,
    hnegAdd, hFen]
  rw [infimalConvolution_eq_iInf_second]
  have hNegInf :=
    helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
      (fun z : Fin m → ℝ =>
        fenchelConjugate m (fun u => -g₂ u) z +
          fenchelConjugate m (fun u => -g₁ u) (-uStar - z))
  rw [hNegInf]
  rw [show
      (⨆ z : Fin m → ℝ,
        -(fenchelConjugate m (fun u => -g₂ u) z +
          fenchelConjugate m (fun u => -g₁ u) (-uStar - z))) =
        ⨆ v : Fin m → ℝ,
          -(fenchelConjugate m (fun u => -g₂ u) (-v) +
            fenchelConjugate m (fun u => -g₁ u) (-uStar - (-v))) by
      exact (Equiv.iSup_congr (Equiv.neg (Fin m → ℝ)) (fun _ => rfl)).symm]
  refine iSup_congr ?_
  intro v
  rw [helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted,
    helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted]
  simp [erealAddConcaveBook, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Theorem 38.2: Let `F₁` and `F₂` be proper convex bifunctions from `ℝ^m` to `ℝ^n`. If
`ri (dom F₁)` and `ri (dom F₂)` have a point in common, then the adjoint (conjugate) of their
infimal convolution equals the infimal convolution of their adjoints:

`(F₁ □ F₂)^* = F₁^* □ F₂^*`. -/
theorem bifunctionAdjoint_infimalConvolution_eq_infimalConvolution_adjoint {m n : Nat}
    (F₁ F₂ : FiberwiseProperConvexBifunction m n)
    (hconv₁ : ConvexBifunction F₁.toFun)
    (hconv₂ : ConvexBifunction F₂.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDom F₁.toFun) ∩
          intrinsicInterior ℝ (bifunctionDom F₂.toFun)).Nonempty) :
    textbookBifunctionAdjoint (bifunctionInfimalConvolution F₁ F₂) =
      concaveBifunctionInfimalConvolutionInSecond
        (textbookBifunctionAdjoint F₁.toFun) (textbookBifunctionAdjoint F₂.toFun) :=
  by
    funext xStar uStar
    let g₁ : (Fin m → ℝ) → EReal := fun u => fenchelConjugate n (F₁.toFun u) xStar
    let g₂ : (Fin m → ℝ) → EReal := fun u => fenchelConjugate n (F₂.toFun u) xStar
    have hSlice :
        (fun u => fenchelConjugate n (bifunctionInfimalConvolution F₁ F₂ u) xStar) =
          (fun u => g₁ u + g₂ u) := by
      funext u
      exact fenchelConjugate_bifunctionInfimalConvolution_eq_add F₁ F₂ u xStar
    rw [textbookBifunctionAdjoint_eq_concaveConjugate_pairing, hSlice]
    change concaveConjugate (fun u => g₁ u + g₂ u) uStar =
      ⨆ v : Fin m → ℝ,
        erealAddConcaveBook (textbookBifunctionAdjoint F₁.toFun xStar (uStar - v))
          (textbookBifunctionAdjoint F₂.toFun xStar v)
    simp_rw [textbookBifunctionAdjoint_eq_concaveConjugate_pairing]
    change concaveConjugate (fun u => g₁ u + g₂ u) uStar =
      ⨆ v : Fin m → ℝ,
        erealAddConcaveBook (concaveConjugate g₁ (uStar - v)) (concaveConjugate g₂ v)
    have hconvF₁ : ConvexFunction (fun u : Fin m → ℝ => -g₁ u) := by
      simpa [g₁] using neg_fenchelConjugate_slice_convexFunction F₁ hconv₁ xStar
    have hconvF₂ : ConvexFunction (fun u : Fin m → ℝ => -g₂ u) := by
      simpa [g₂] using neg_fenchelConjugate_slice_convexFunction F₂ hconv₂ xStar
    have hri' :
        (intrinsicInterior ℝ
            (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun u => -g₁ u)) ∩
          intrinsicInterior ℝ
            (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun u => -g₂ u))).Nonempty := by
      simpa [g₁, g₂, effectiveDomain_neg_fenchelConjugate_slice_eq_bifunctionDom]
        using hri
    by_cases hne₁ : ∀ u : Fin m → ℝ, -g₁ u ≠ (⊥ : EReal)
    · have hf₁ :
          ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun u => -g₁ u) := by
        simpa [g₁] using
          neg_fenchelConjugate_slice_properConvex_of_ne_bot F₁ hconv₁ xStar
            (by simpa [g₁] using hne₁)
      by_cases hne₂ : ∀ u : Fin m → ℝ, -g₂ u ≠ (⊥ : EReal)
      · have hf₂ :
            ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun u => -g₂ u) := by
          simpa [g₂] using
            neg_fenchelConjugate_slice_properConvex_of_ne_bot F₂ hconv₂ xStar
              (by simpa [g₂] using hne₂)
        exact concaveConjugate_add_eq_supConvolution g₁ g₂ hf₁ hf₂ hri' uStar
      · push_neg at hne₂
        rcases hri' with ⟨u₀, hu₁, hu₂⟩
        have himproper₂ :
            ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun u => -g₂ u) := by
          refine ⟨by simpa [ConvexFunction] using hconvF₂, ?_⟩
          intro hp
          rcases hne₂ with ⟨u, hu⟩
          exact hp.2.2 u (by simp) hu
        have hu₂ri :
            u₀ ∈ euclideanRelativeInterior_fin m
              (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun u => -g₂ u)) := by
          rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
          exact hu₂
        have hbot₂ : -g₂ u₀ = (⊥ : EReal) :=
          improperConvexFunctionOn_eq_bot_on_intrinsicInterior_fin himproper₂ hu₂
        have hg₂Top : g₂ u₀ = (⊤ : EReal) := (EReal.neg_eq_bot_iff).1 hbot₂
        have hg₁NeBot : g₁ u₀ ≠ (⊥ : EReal) := by
          have huEff :
              u₀ ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun u => -g₁ u) :=
            intrinsicInterior_subset hu₁
          intro hg₁Bot
          have : -g₁ u₀ = (⊤ : EReal) := by simp [hg₁Bot]
          exact (lt_top_iff_ne_top.1 (by simpa [effectiveDomain_eq] using huEff)) this
        have hsumTop : g₁ u₀ + g₂ u₀ = (⊤ : EReal) := by
          rw [hg₂Top]
          exact EReal.add_top_of_ne_bot hg₁NeBot
        rw [concaveConjugate_eq_bot_of_neg_value_eq_bot
          (fun u => g₁ u + g₂ u) u₀ (by simp [hsumTop]) uStar]
        symm
        rw [iSup_eq_bot]
        intro v
        have hrightBot : concaveConjugate g₂ v = (⊥ : EReal) :=
          concaveConjugate_eq_bot_of_neg_value_eq_bot g₂ u₀ hbot₂ v
        have hleftNeTop : concaveConjugate g₁ (uStar - v) ≠ (⊤ : EReal) :=
          concaveConjugate_ne_top_of_value_ne_bot g₁ u₀ hg₁NeBot (uStar - v)
        rw [hrightBot]
        exact erealAddConcaveBook_bot_right_of_ne_top _ hleftNeTop
    · push_neg at hne₁
      rcases hri' with ⟨u₀, hu₁, hu₂⟩
      have himproper₁ :
          ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun u => -g₁ u) := by
        refine ⟨by simpa [ConvexFunction] using hconvF₁, ?_⟩
        intro hp
        rcases hne₁ with ⟨u, hu⟩
        exact hp.2.2 u (by simp) hu
      have hu₁ri :
          u₀ ∈ euclideanRelativeInterior_fin m
            (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun u => -g₁ u)) := by
        rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
        exact hu₁
      have hbot₁ : -g₁ u₀ = (⊥ : EReal) :=
        improperConvexFunctionOn_eq_bot_on_intrinsicInterior_fin himproper₁ hu₁
      have hg₁Top : g₁ u₀ = (⊤ : EReal) := (EReal.neg_eq_bot_iff).1 hbot₁
      have hg₂NeBot : g₂ u₀ ≠ (⊥ : EReal) := by
        have huEff :
            u₀ ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun u => -g₂ u) :=
          intrinsicInterior_subset hu₂
        intro hg₂Bot
        have : -g₂ u₀ = (⊤ : EReal) := by simp [hg₂Bot]
        exact (lt_top_iff_ne_top.1 (by simpa [effectiveDomain_eq] using huEff)) this
      have hsumTop : g₁ u₀ + g₂ u₀ = (⊤ : EReal) := by
        rw [hg₁Top]
        exact EReal.top_add_of_ne_bot hg₂NeBot
      rw [concaveConjugate_eq_bot_of_neg_value_eq_bot
        (fun u => g₁ u + g₂ u) u₀ (by simp [hsumTop]) uStar]
      symm
      rw [iSup_eq_bot]
      intro v
      have hleftBot : concaveConjugate g₁ (uStar - v) = (⊥ : EReal) :=
        concaveConjugate_eq_bot_of_neg_value_eq_bot g₁ u₀ hbot₁ (uStar - v)
      have hrightNeTop : concaveConjugate g₂ v ≠ (⊤ : EReal) :=
        concaveConjugate_ne_top_of_value_ne_bot g₂ u₀ hg₂NeBot v
      rw [hleftBot]
      exact erealAddConcaveBook_bot_left_of_ne_top _ hrightNeTop

end Section38
end Chap08
