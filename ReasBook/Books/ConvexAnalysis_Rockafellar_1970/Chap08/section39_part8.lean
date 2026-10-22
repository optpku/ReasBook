/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part19

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

section Chap08
section Section39

namespace ConvexProcess

/-- Theorem 39.3: If `A` is an oriented convex process from `ℝ^m` to `ℝ^n`, then the bracket
`x* ↦ ⟪A u, x*⟫` is positively homogeneous and closed, and it is convex in supremum orientation and
concave in infimum orientation. Dually, for fixed `x*` the function `u ↦ ⟪A u, x*⟫` is positively
homogeneous and is concave in supremum orientation (convex in infimum orientation).

In either orientation one has the closure identity
`⟪u, A* x*⟫ = cl_u ⟪A u, x*⟫`. If `A` is closed, then also
`⟪A u, x*⟫ = cl_{x*} ⟪u, A* x*⟫`, and in fact `⟪A u, x*⟫ = ⟪u, A* x*⟫` whenever
`u ∈ ri (dom A)` or `x* ∈ ri (dom A*)`. -/
theorem theorem_39_3 {m n : ℕ} (o : ConvexSetOrientation) (A : ConvexProcess m n)
    (hQualification : Section39Theorem39_3Qualification) :
    (∀ u,
        IsPosHomogeneousEReal (fun xStar => setBracketVec o (A.toSetValued u) xStar) ∧
          (match o with
            | .supremum =>
                IsClosedEReal (fun xStar => setBracketVec o (A.toSetValued u) xStar) ∧
                  IsConvexEReal (fun xStar => setBracketVec o (A.toSetValued u) xStar)
            | .infimum =>
                IsUpperClosedEReal (fun xStar => setBracketVec o (A.toSetValued u) xStar) ∧
                  IsConcaveEReal (fun xStar => setBracketVec o (A.toSetValued u) xStar))) ∧
      (∀ xStar,
        IsPosHomogeneousEReal (fun u => setBracketVec o (A.toSetValued u) xStar) ∧
          (match o with
            | .supremum => IsConcaveEReal (fun u => setBracketVec o (A.toSetValued u) xStar)
            | .infimum => IsConvexEReal (fun u => setBracketVec o (A.toSetValued u) xStar))) ∧
      (∀ u xStar,
        setBracketVec o.opposite ((adjointVecOriented o A).toSetValued xStar) u =
          eRealClosureOriented o.opposite (fun u => setBracketVec o (A.toSetValued u) xStar) u) ∧
      (A.IsClosed →
        (∀ u xStar,
          setBracketVec o (A.toSetValued u) xStar =
            match o with
            | .supremum =>
                convexFunctionClosure
                  (fun xStar =>
                    setBracketVec o.opposite
                      ((adjointVecOriented o A).toSetValued xStar) u) xStar
            | .infimum =>
                concaveClosure
                  (fun xStar =>
                    setBracketVec o.opposite
                      ((adjointVecOriented o A).toSetValued xStar) u) xStar)) ∧
      (A.IsClosed →
        (∀ u xStar,
          u ∈ ri A.dom →
            setBracketVec o (A.toSetValued u) xStar =
            setBracketVec o.opposite ((adjointVecOriented o A).toSetValued xStar) u)) :=
  by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u
    cases o
    · -- Step 1: in the supremum branch, each fixed fiber is a support function section.
      rcases helperForTheorem_39_3_supremumSection_properties A u with
        ⟨hPos, hClosed, hConv⟩
      exact ⟨hPos, hClosed, hConv⟩
    · -- Step 2: the infimum branch should be discharged from the concave pairing
      -- correspondence for `ConvexProcess.negIndicatorBifunction A`, together with the positive
      -- homogeneity of inf-support functions. For the fixed-fiber branch we can already bypass
      -- the missing parameter-convexity package by rewriting the infimum bracket as the negative
      -- of a support function of the negated fiber.
      rcases helperForTheorem_39_3_infimumSection_properties A u with
        ⟨hPos, hUpperClosed, hConc⟩
      exact ⟨hPos, hUpperClosed, hConc⟩
  · intro xStar
    -- Step 1: rewrite the parameter section `u ↦ ⟪A u, x*⟫` into the corresponding Section 33
    -- pairing section.
    cases o
    · -- Step 2: the supremum branch gets positive homogeneity from the process axiom and
      -- concavity from the Section 33 convex pairing correspondence.
      have hPos :
          IsPosHomogeneousEReal
            (fun u =>
              setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar) :=
        helperForTheorem_39_3_parameterSection_posHomogeneous
          ConvexSetOrientation.supremum A xStar
      have hRock : IsRockafellarConvexBifunction (ConvexProcess.indicatorBifunction A) :=
        (indicatorBifunction_rockafellarPackage A).1
      have hNoBot : HasNoBotValuesBifunction (ConvexProcess.indicatorBifunction A) :=
        (indicatorBifunction_rockafellarPackage A).2.1
      rcases
          (convexBifunction_pairing_correspondence (m := m) (n := n)).1
            (ConvexProcess.indicatorBifunction A) hRock hNoBot with
        ⟨hConcConv, _, _⟩
      have hPairConc :
          IsERealConcaveOn (Set.univ : Set (Fin m → ℝ))
            (fun u =>
              convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u xStar) :=
        hConcConv.1 xStar (by simp)
      have hEq :
          (fun u =>
            setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar) =
            fun u =>
              convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u xStar := by
        funext u
        simpa using
          helperForTheorem_39_3_bracket_eq_orientedPairing
            ConvexSetOrientation.supremum A u xStar
      refine ⟨hPos, ?_⟩
      rw [hEq]
      exact
        helperForTheorem_39_3_isERealConcaveOn_univ_to_IsConcaveEReal hPairConc
    · -- Step 3: the infimum branch is the dual Section 33 package for the negative indicator.
      have hPos :
          IsPosHomogeneousEReal
            (fun u =>
              setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar) :=
        helperForTheorem_39_3_parameterSection_posHomogeneous
          ConvexSetOrientation.infimum A xStar
      have hRock : IsRockafellarConcaveBifunction (ConvexProcess.negIndicatorBifunction A) :=
        (helperForTheorem_39_3_indicator_infimum_package A).1 (by
          intro u' xStar'
          have hBracketEq :=
            helperForTheorem_39_3_bracket_eq_orientedPairing
              ConvexSetOrientation.supremum A u' xStar'
          intro hTop
          apply hQualification.parameterFinite ConvexSetOrientation.supremum A xStar' u'
          calc
            setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar' =
                convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u' xStar' := by
                  simpa using hBracketEq
            _ = ⊤ := hTop)
      have hNoTop : HasNoTopValuesBifunction (ConvexProcess.negIndicatorBifunction A) :=
        (helperForTheorem_39_3_indicator_infimum_package A).2.1
      rcases
          (concaveBifunction_pairing_correspondence (m := m) (n := n)).1
            (ConvexProcess.negIndicatorBifunction A) hRock hNoTop with
        ⟨hConvConc, _, _⟩
      have hPairConv :
          IsERealConvexOn (Set.univ : Set (Fin m → ℝ))
            (fun u =>
              concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar) :=
        hConvConc.1 xStar (by simp)
      have hEq :
          (fun u =>
            setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar) =
            fun u =>
              concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar := by
        funext u
        simpa using
          helperForTheorem_39_3_bracket_eq_orientedPairing
            ConvexSetOrientation.infimum A u xStar
      refine ⟨hPos, ?_⟩
      rw [hEq]
      -- Step 4: the Jensen-convex parameter section becomes convex in the local epigraph notation.
      exact helperForTheorem_39_3_isERealConvexOn_univ_to_IsConvexEReal hPairConv
  · intro u xStar
    -- Route correction: this is the first genuinely structural bridge. After rewriting
    -- `⟪A u, x*⟫` to the Section 33 pairing by
    -- `helperForTheorem_39_3_bracket_eq_orientedPairing`, the remaining missing input is the
    -- dual rewrite from the oriented adjoint fiber
    -- `setBracketVec o.opposite ((adjointVecOriented o A).toSetValued xStar) u`
    -- to the corresponding Section 33 adjoint-pairing object.
    cases o
    · -- Step 2: in the supremum branch the direct adjoint-fiber closure lemma is exactly the
      -- desired conclusion.
      simpa using
        helperForTheorem_39_3_parameterClosure_eq_adjointBracket_direct
          ConvexSetOrientation.supremum A hQualification u xStar
    · -- Step 3: the infimum branch is the same direct closure identity with the opposite
      -- orientation.
      simpa using
        helperForTheorem_39_3_parameterClosure_eq_adjointBracket_direct
          ConvexSetOrientation.infimum A hQualification u xStar
  · intro hAClosed u xStar
    -- Step 1: this is the closed-process companion to the previous closure identity, now using
    -- the second half of Theorem 33.2 together with the closed-graph fixed-point lemmas from
    -- Corollary 33.2.1.
    cases o
    · have hGraph : IsGraphConvexBifunction (ConvexProcess.indicatorBifunction A) :=
        helperForTheorem_39_3_indicatorBifunction_graphConvex A
      have hNoBot : HasNoBotValuesBifunction (ConvexProcess.indicatorBifunction A) :=
        (indicatorBifunction_rockafellarPackage A).2.1
      have hGraphClosed :
          IsFunctionConvexClosed
            (graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A)) :=
        (indicatorBifunction_rockafellarPackage A).2.2 hAClosed
      rcases
          (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).1
            (ConvexProcess.indicatorBifunction A) ⟨hGraph, hNoBot⟩ with
        ⟨_hFirst, hSecond⟩
      have hDualEq :
          (fun xStar' : Fin n → ℝ =>
            convexBifunctionCanonicalAdjointPairing
              (ConvexProcess.indicatorBifunction A) xStar' u) =
            fun xStar' : Fin n → ℝ =>
              setBracketVec ConvexSetOrientation.infimum
                ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar') u := by
        funext xStar'
        symm
        simpa using
          helperForTheorem_39_3_adjointBracket_eq_orientedAdjointPairing
            ConvexSetOrientation.supremum A hQualification xStar' u
      calc
        setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar =
            convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u xStar := by
              simpa using
                helperForTheorem_39_3_bracket_eq_orientedPairing
                  ConvexSetOrientation.supremum A u xStar
        _ =
            convexBifunctionPairing (convexBifunctionClosure
              (ConvexProcess.indicatorBifunction A)) u xStar := by
              symm
              exact
                helperForCorollary33_2_1_convexClosure_pairing_eq_self_of_closed
                  (F := ConvexProcess.indicatorBifunction A) hGraph hNoBot hGraphClosed u xStar
        _ =
            convexFunctionClosure
              (fun xStar' : Fin n → ℝ =>
                convexBifunctionCanonicalAdjointPairing
                  (ConvexProcess.indicatorBifunction A) xStar' u)
              xStar := by
              symm
              exact hSecond u xStar
        _ =
            convexFunctionClosure
              (fun xStar' : Fin n → ℝ =>
                setBracketVec ConvexSetOrientation.supremum.opposite
                  ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar') u)
              xStar := by
              rw [hDualEq]
              rfl
    · have hGraph : IsGraphConcaveBifunction (ConvexProcess.negIndicatorBifunction A) :=
        helperForTheorem_39_3_negIndicatorBifunction_graphConcave A
      have hNoTop : HasNoTopValuesBifunction (ConvexProcess.negIndicatorBifunction A) :=
        (helperForTheorem_39_3_indicator_infimum_package A).2.1
      have hGraphClosed :
          IsFunctionConcaveClosed
            (graphFunctionOfBifunction (ConvexProcess.negIndicatorBifunction A)) :=
        (helperForTheorem_39_3_indicator_infimum_package A).2.2 hAClosed
      rcases
          (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).2
            (ConvexProcess.negIndicatorBifunction A) ⟨hGraph, hNoTop⟩ with
        ⟨_hFirst, hSecond⟩
      have hDualEq :
          (fun xStar' : Fin n → ℝ =>
            concaveBifunctionCanonicalAdjointPairing
              (ConvexProcess.negIndicatorBifunction A) xStar' u) =
            fun xStar' : Fin n → ℝ =>
              setBracketVec ConvexSetOrientation.supremum
                ((adjointVecOriented ConvexSetOrientation.infimum A).toSetValued xStar') u := by
        funext xStar'
        symm
        simpa using
          helperForTheorem_39_3_adjointBracket_eq_orientedAdjointPairing
            ConvexSetOrientation.infimum A hQualification xStar' u
      calc
        setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar =
            concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar := by
              simpa using
                helperForTheorem_39_3_bracket_eq_orientedPairing
                  ConvexSetOrientation.infimum A u xStar
        _ =
            concaveBifunctionPairing (concaveBifunctionClosure
              (ConvexProcess.negIndicatorBifunction A)) u xStar := by
              symm
              exact
                helperForCorollary33_2_1_concaveClosure_pairing_eq_self_of_closed
                  (F := ConvexProcess.negIndicatorBifunction A) hGraph hNoTop hGraphClosed u xStar
        _ =
            concaveClosure
              (fun xStar' : Fin n → ℝ =>
                concaveBifunctionCanonicalAdjointPairing
                  (ConvexProcess.negIndicatorBifunction A) xStar' u) xStar := by
              symm
              exact hSecond u xStar
        _ =
            concaveClosure
              (fun xStar' : Fin n → ℝ =>
                setBracketVec ConvexSetOrientation.infimum.opposite
                  ((adjointVecOriented ConvexSetOrientation.infimum A).toSetValued xStar') u)
              xStar := by
              rw [hDualEq]
              rfl
  · intro hAClosed u xStar hri
    let _ := hAClosed
    cases o
    · calc
            setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar =
                convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u xStar := by
                  simpa using
                    helperForTheorem_39_3_bracket_eq_orientedPairing
                      ConvexSetOrientation.supremum A u xStar
            _ =
                convexBifunctionCanonicalAdjointPairing
                  (ConvexProcess.indicatorBifunction A) xStar u := by
                  exact
                    ((adjoint_pairing_eq_on_relativeInterior_domains (m := m) (n := n)).1
                      (F := ConvexProcess.indicatorBifunction A)
                      ⟨helperForTheorem_39_3_indicatorBifunction_graphConvex A,
                        (indicatorBifunction_rockafellarPackage A).2.1⟩).1
                      (by
                        rw [helperForTheorem_39_3_indicator_parameterDomain_eq_dom A]
                        exact hri) xStar
            _ =
                setBracketVec ConvexSetOrientation.supremum.opposite
                  ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar) u := by
                  symm
                  simpa using
                    helperForTheorem_39_3_adjointBracket_eq_orientedAdjointPairing
                      ConvexSetOrientation.supremum A hQualification xStar u
    · calc
            setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar =
                concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar := by
                  simpa using
                    helperForTheorem_39_3_bracket_eq_orientedPairing
                      ConvexSetOrientation.infimum A u xStar
            _ =
                concaveBifunctionCanonicalAdjointPairing
                  (ConvexProcess.negIndicatorBifunction A) xStar u := by
                  exact
                    ((adjoint_pairing_eq_on_relativeInterior_domains (m := m) (n := n)).2
                      (F := ConvexProcess.negIndicatorBifunction A)
                      ⟨helperForTheorem_39_3_negIndicatorBifunction_graphConcave A,
                        (helperForTheorem_39_3_indicator_infimum_package A).2.1⟩).1
                      (by
                        rw [helperForTheorem_39_3_negIndicator_parameterDomain_eq_dom A]
                        exact hri) xStar
            _ =
                setBracketVec ConvexSetOrientation.infimum.opposite
                  ((adjointVecOriented ConvexSetOrientation.infimum A).toSetValued xStar) u := by
                  symm
                  simpa using
                    helperForTheorem_39_3_adjointBracket_eq_orientedAdjointPairing
                      ConvexSetOrientation.infimum A hQualification xStar u

/-- The weak lower-closed concave-convex package used for the unconditional direction of
Theorem 39.4: concave-convexity together with closedness of the convex second-variable sections.
Endpoint exclusions needed by the reverse Section 33 realization are recorded separately in the
working qualification below. -/
def IsLowerClosedConcaveConvexBifunction {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
    IsConvexClosedInSecond K

/-- The additional normalization and positive-homogeneity hypotheses on a bifunction `K` appearing
in Theorem 39.4: `K(0,0)=0` and for every `r>0`,
`K(r • u, x*) = r K(u, x*) = K(u, r • x*)`. -/
def IsNormalizedBihomogeneousERealBifunction {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  K 0 0 = 0 ∧
    ∀ (r : ℝ), 0 < r → ∀ u xStar,
      (K (r • u) xStar = (r : EReal) * K u xStar) ∧
        (K u (r • xStar) = (r : EReal) * K u xStar)

/-- The class of bifunctions `K` in the statement of Theorem 39.4: lower closed concave-convex,
normalized by `K(0,0)=0`, and positively homogeneous in each variable (with a common scaling
factor). -/
def IsLowerClosedConcaveConvexPosHomBifunction {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsLowerClosedConcaveConvexBifunction (m := m) (n := n) K ∧
    IsNormalizedBihomogeneousERealBifunction (m := m) (n := n) K

/-- A stronger working kernel package for Theorem 39.4.

Besides the textbook lower-closed concave-convex and bihomogeneous hypotheses, this records the
two extra facts currently needed by the reverse map `K ↦ A_K` in the local formalization:

* the origin section is pointwise nonnegative, so `0 ∈ A_K 0`;
* each parameter section `u ↦ K(u, x*)` is upper closed, so the reconstructed graph is closed.

The long-term goal is to derive these facts from the textbook notion of lower closedness, but for
now this predicate isolates the exact missing interface. -/
def IsWorkingLowerClosedConcaveConvexPosHomBifunction {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) K ∧
    HasNoTopOrBotValuesBifunction K ∧
      (∀ xStar : Fin n → ℝ, (0 : EReal) ≤ K (0 : Fin m → ℝ) xStar) ∧
        (∀ xStar : Fin n → ℝ, IsUpperClosedEReal (fun u : Fin m → ℝ => K u xStar))

/-- The bifunction associated to a convex process `A` by the supremum-oriented bracket:
`K_A(u, x*) = ⟪A u, x*⟫`. -/
noncomputable def bracketBifunctionOfProcess {m n : ℕ} (A : ConvexProcess m n) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u xStar => setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar

/-- The set-valued mapping associated to a bifunction `K` by the half-space intersection formula:
`A_K u = {x | ⟪x, x*⟫ ≤ K(u, x*), ∀ x*}` (using the Euclidean pairing `finDot`). -/
def processMapOfBifunction {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → Set (Fin n → ℝ) :=
  fun u => { x | ∀ xStar, ((finDot x xStar : ℝ) : EReal) ≤ K u xStar }

/-- The subtype of lower closed concave-convex bifunctions `K` satisfying the normalization and
positive-homogeneity hypotheses of Theorem 39.4. -/
abbrev LowerClosedConcaveConvexPosHomBifunction (m n : ℕ) : Type :=
  { K : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsLowerClosedConcaveConvexPosHomBifunction K }

/-- The stronger working subtype for Theorem 39.4, adding exactly the origin-section and
parameter-upper-closedness data currently needed by the reverse construction
`K ↦ processMapOfBifunction K`. -/
abbrev WorkingLowerClosedConcaveConvexPosHomBifunction (m n : ℕ) : Type :=
  { K : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsWorkingLowerClosedConcaveConvexPosHomBifunction K }

/-- Explicit endpoint and realization data needed only by the reverse construction in Theorem
39.4.  The underlying bifunction subtype remains the weak, unconditional closed-section package. -/
structure Section39Theorem39_4GlobalQualification (m n : ℕ) : Prop where
  kernelNoTopOrBot : ∀ K : LowerClosedConcaveConvexPosHomBifunction m n,
    HasNoTopOrBotValuesBifunction K.1
  conjugateGraphClosed : ∀ K : LowerClosedConcaveConvexPosHomBifunction m n,
    IsFunctionConvexClosed
      (graphFunctionOfBifunction (fun u x => convexConjugate (K.1 u) x))

/-- The subtype of closed convex processes `A` (in the sense `cl A = A`). -/
abbrev ClosedConvexProcess (m n : ℕ) : Type :=
  { A : ConvexProcess m n // A.IsClosed }

/-- Helper for Theorem 39.4: the bracket bifunction of a closed convex process already satisfies
the lower-closed concave-convex and bihomogeneous hypotheses needed for the forward map
`A ↦ K_A`. -/
lemma helperForTheorem_39_4_bracketBifunctionOfClosedProcess_memSubtype {m n : ℕ}
    (A : ClosedConvexProcess m n) :
    IsLowerClosedConcaveConvexPosHomBifunction
      (bracketBifunctionOfProcess (m := m) (n := n) A.1) := by
  -- Step 1: the weak, endpoint-independent part of Theorem 39.3 supplies the two positive
  -- homogeneity facts needed here; no canonical-closure qualification is required.
  have hFiberSections := helperForTheorem_39_3_supremumSection_properties A.1
  have hRock : IsRockafellarConvexBifunction (ConvexProcess.indicatorBifunction A.1) :=
    (indicatorBifunction_rockafellarPackage A.1).1
  have hNoBot : HasNoBotValuesBifunction (ConvexProcess.indicatorBifunction A.1) :=
    (indicatorBifunction_rockafellarPackage A.1).2.1
  have hGraphClosed :
      IsFunctionConvexClosed
        (graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A.1)) :=
    (indicatorBifunction_rockafellarPackage A.1).2.2 A.2
  have hImageClosed :
      IsImageClosedConvexBifunction (ConvexProcess.indicatorBifunction A.1) := by
    refine ⟨hRock, hNoBot, ?_⟩
    exact helperForLemma33_0_22_section_isFunctionConvexClosed hGraphClosed
  have hPairingBase :=
    (closedSaddleFunctions_imageClosedBifunctions_correspondence
      (m := m) (n := n)).1 (ConvexProcess.indicatorBifunction A.1) hImageClosed
  have hEq :
      bracketBifunctionOfProcess (m := m) (n := n) A.1 =
        convexBifunctionPairing (ConvexProcess.indicatorBifunction A.1) := by
    funext u xStar
    simpa [bracketBifunctionOfProcess] using
      helperForTheorem_39_3_bracket_eq_orientedPairing
        ConvexSetOrientation.supremum A.1 u xStar
  refine ⟨?_, ?_⟩
  · -- Step 2: rewrite the strong Section 33 lower-closed package along the bracket/pairing
    -- identification.
    refine ⟨?_, ?_⟩
    · simpa [hEq] using hPairingBase.1
    · simpa [hEq] using hPairingBase.2.1
  · -- Step 3: normalization and positive homogeneity come from the same theorem plus the zero
    -- witness in the origin fiber.
    constructor
    · -- The zero covector evaluates every point of `A 0` to `0`, so the support value is `0`.
      unfold bracketBifunctionOfProcess setBracketVec
      apply le_antisymm
      · refine sSup_le ?_
        rintro r ⟨x, hx, rfl⟩
        simp [finDot]
      · exact le_sSup ⟨0, A.1.zero_mem, by simp [finDot]⟩
    · intro r hr u xStar
      rcases hFiberSections u with ⟨hPosFiber, _hClosedFiber, _hConvFiber⟩
      have hPosParam :=
        helperForTheorem_39_3_parameterSection_posHomogeneous
          ConvexSetOrientation.supremum A.1 xStar
      constructor
      · -- Scaling the parameter `u` uses positive homogeneity of the `u`-section.
        simpa [bracketBifunctionOfProcess] using hPosParam u r hr
      · -- Scaling the covector `x*` uses positive homogeneity of the `x*`-section.
        simpa [bracketBifunctionOfProcess] using hPosFiber xStar r hr

/-- Helper for Theorem 39.4: each fixed fiber of `processMapOfBifunction K` is an intersection of
closed convex affine half-spaces, hence is itself closed and convex. -/
lemma helperForTheorem_39_4_processMapOfBifunction_fiber_closed_convex {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (u : Fin m → ℝ) :
    _root_.IsClosed (processMapOfBifunction (m := m) (n := n) K u) ∧
      Convex ℝ (processMapOfBifunction (m := m) (n := n) K u) := by
  have hSlice :
      ∀ xStar : Fin n → ℝ,
        _root_.IsClosed {x : Fin n → ℝ | (((finDot x xStar : ℝ) : EReal) ≤ K u xStar)} ∧
          Convex ℝ {x : Fin n → ℝ | (((finDot x xStar : ℝ) : EReal) ≤ K u xStar)} := by
    intro xStar
    by_cases hTop : K u xStar = (⊤ : EReal)
    · -- If the bound is `⊤`, the slice is the whole space.
      constructor
      · simp [hTop]
      · simpa [hTop] using (convex_univ : Convex ℝ (Set.univ : Set (Fin n → ℝ)))
    by_cases hBot : K u xStar = (⊥ : EReal)
    · -- If the bound is `⊥`, the slice is empty because a real dot product is always finite.
      constructor
      · simp [hBot]
      · simpa [hBot] using (convex_empty : Convex ℝ (∅ : Set (Fin n → ℝ)))
    · -- In the finite case, rewrite the slice as an ordinary real affine half-space.
      let β : ℝ := (K u xStar).toReal
      have hβ :
          ((β : ℝ) : EReal) = K u xStar := by
        exact EReal.coe_toReal hTop hBot
      have hSetEq :
          {x : Fin n → ℝ | (((finDot x xStar : ℝ) : EReal) ≤ K u xStar)} =
            {x : Fin n → ℝ | finDot x xStar ≤ β} := by
        ext x
        rw [← hβ]
        exact EReal.coe_le_coe_iff
      rcases
          isClosed_and_convex_setOf_dotProduct_le n Unit
            (fun _ => xStar) (fun _ => β) with
        ⟨hClosed, hConv⟩
      constructor
      · rw [hSetEq]
        simpa [β, finDot] using hClosed
      · rw [hSetEq]
        simpa [β, finDot] using hConv
  have hProcessEq :
      processMapOfBifunction (m := m) (n := n) K u =
        ⋂ xStar : Fin n → ℝ, {x : Fin n → ℝ | (((finDot x xStar : ℝ) : EReal) ≤ K u xStar)} := by
    ext x
    simp [processMapOfBifunction]
  constructor
  · -- Step 1: closedness is preserved under arbitrary intersections of the half-space slices.
    rw [hProcessEq]
    exact isClosed_iInter fun xStar : Fin n → ℝ => (hSlice xStar).1
  · -- Step 2: convexity is preserved under arbitrary intersections of the same slices.
    rw [hProcessEq]
    exact convex_iInter fun xStar : Fin n → ℝ => (hSlice xStar).2

/-- Helper for Theorem 39.4: the origin belongs to a reconstructed fiber exactly when the
corresponding section is pointwise nonnegative, because every pairing `⟪0,x*⟫` is `0`. -/
lemma helperForTheorem_39_4_zero_mem_processMapOfBifunction_iff_nonnegSection {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (u : Fin m → ℝ) :
    (0 : Fin n → ℝ) ∈ processMapOfBifunction (m := m) (n := n) K u ↔
      ∀ xStar : Fin n → ℝ, (0 : EReal) ≤ K u xStar := by
  constructor
  · intro hZero xStar
    -- Step 1: unpack the defining inequality at the zero vector in the reconstructed fiber.
    have hZero' :
        ∀ yStar : Fin n → ℝ,
          (((finDot (0 : Fin n → ℝ) yStar : ℝ) : EReal)) ≤ K u yStar := by
      simpa [processMapOfBifunction] using hZero
    simpa [finDot] using hZero' xStar
  · intro hNonneg
    -- Step 2: conversely, the zero vector satisfies every defining half-space inequality.
    have hZero' :
        ∀ xStar : Fin n → ℝ,
          (((finDot (0 : Fin n → ℝ) xStar : ℝ) : EReal)) ≤ K u xStar := by
      intro xStar
      simpa [finDot] using hNonneg xStar
    simpa [processMapOfBifunction] using hZero'

/-- Helper for Theorem 39.4: the admissibility condition `∀ x*, 0 ≤ K(u,x*)` is already enough
to put the origin into the reconstructed fiber over `u`. -/
lemma helperForTheorem_39_4_zero_mem_processMapOfBifunction_of_nonnegSection {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (u : Fin m → ℝ)
    (hNonneg : ∀ xStar : Fin n → ℝ, (0 : EReal) ≤ K u xStar) :
    (0 : Fin n → ℝ) ∈ processMapOfBifunction (m := m) (n := n) K u := by
  -- Step 1: reuse the exact origin-membership criterion just proved above.
  exact
    (helperForTheorem_39_4_zero_mem_processMapOfBifunction_iff_nonnegSection
      (m := m) (n := n) K u).2 hNonneg

/-- Helper for Theorem 39.4: a single `⊥` value in a fixed section forces the entire reconstructed
fiber to be empty, because finite dot products can never satisfy `≤ ⊥`. -/
lemma helperForTheorem_39_4_processMapOfBifunction_eq_empty_of_botSection {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (u : Fin m → ℝ) {xStar : Fin n → ℝ}
    (hBot : K u xStar = (⊥ : EReal)) :
    processMapOfBifunction (m := m) (n := n) K u = ∅ := by
  ext x
  constructor
  · intro hx
    -- Step 1: the offending covector section gives an impossible inequality for any candidate `x`.
    have hx' :
        ∀ yStar : Fin n → ℝ,
          (((finDot x yStar : ℝ) : EReal)) ≤ K u yStar := by
      simpa [processMapOfBifunction] using hx
    have hImpossible : (((finDot x xStar : ℝ) : EReal)) ≤ (⊥ : EReal) := by
      simpa [hBot] using hx' xStar
    have hNoLeBot :
        ¬ (((finDot x xStar : ℝ) : EReal)) ≤ (⊥ : EReal) := by
      simp
    exact False.elim (hNoLeBot hImpossible)
  · intro hx
    exfalso
    simp at hx

/-- Helper for Theorem 39.4: if every fixed covector section `u ↦ K(u,x*)` is upper closed, then
the graph of the half-space reconstruction `u ↦ processMapOfBifunction K u` is closed because it
is an intersection of continuous preimages of the corresponding hypographs. -/
lemma helperForTheorem_39_4_processMapOfBifunction_graphClosed_of_upperClosedSections {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hUpper : ∀ xStar : Fin n → ℝ, IsUpperClosedEReal (fun u : Fin m → ℝ => K u xStar)) :
    _root_.IsClosed (setValuedGraph (processMapOfBifunction (m := m) (n := n) K)) := by
  have hSlice :
      ∀ xStar : Fin n → ℝ,
        _root_.IsClosed
          {p : (Fin m → ℝ) × (Fin n → ℝ) |
            (((finDot p.2 xStar : ℝ) : EReal) ≤ K p.1 xStar)} := by
    intro xStar
    let evaluateSlice : (Fin m → ℝ) × (Fin n → ℝ) → (Fin m → ℝ) × ℝ :=
      fun p => (p.1, finDot p.2 xStar)
    have hPreimage :
        evaluateSlice ⁻¹' eRealHypograph (fun u : Fin m → ℝ => K u xStar) =
          {p : (Fin m → ℝ) × (Fin n → ℝ) |
            (((finDot p.2 xStar : ℝ) : EReal) ≤ K p.1 xStar)} := by
      -- Step 1: freezing `x*` identifies the slice with the hypograph pullback of the
      -- corresponding first-variable section.
      ext p
      simp [evaluateSlice, eRealHypograph]
    -- Step 2: closed hypographs stay closed under the continuous evaluation map
    -- `(u,x) ↦ (u, ⟪x,x*⟫)`.
    rw [← hPreimage]
    have hContinuousFinDot : Continuous fun x : Fin n → ℝ => finDot x xStar := by
      -- `finDot` is the usual Euclidean dot product, hence continuous in the variable `x`.
      have hContinuousDot : Continuous fun x : Fin n → ℝ => dotProduct xStar x := by
        simpa using (continuous_dotProduct_const (x := xStar))
      simpa [finDot, dotProduct_comm] using hContinuousDot
    exact (hUpper xStar).preimage
      (show Continuous fun p : (Fin m → ℝ) × (Fin n → ℝ) => (p.1, finDot p.2 xStar) by
        exact Continuous.prodMk continuous_fst (hContinuousFinDot.comp continuous_snd))
  have hGraphEq :
      setValuedGraph (processMapOfBifunction (m := m) (n := n) K) =
        ⋂ xStar : Fin n → ℝ,
          {p : (Fin m → ℝ) × (Fin n → ℝ) |
            (((finDot p.2 xStar : ℝ) : EReal) ≤ K p.1 xStar)} := by
    -- Step 3: graph membership is exactly the family of half-space inequalities defining the
    -- reconstructed fiber.
    ext p
    rcases p with ⟨u, x⟩
    simp [setValuedGraph, processMapOfBifunction]
  -- Step 4: intersect the closed slices over all covectors.
  rw [hGraphEq]
  exact isClosed_iInter hSlice

/-- Helper for Theorem 39.4: any reverse map whose fibers are prescribed by
`processMapOfBifunction` forces every admissible kernel to have a pointwise nonnegative origin
section, because the output process must satisfy the `zero_mem` axiom. -/
lemma helperForTheorem_39_4_nonneg_originSection_of_reverseMap {m n : ℕ}
    (toProcess : LowerClosedConcaveConvexPosHomBifunction m n → ClosedConvexProcess m n)
    (hToProcess :
      ∀ K : LowerClosedConcaveConvexPosHomBifunction m n,
        (toProcess K).1.toSetValued = processMapOfBifunction (m := m) (n := n) K.1)
    (K : LowerClosedConcaveConvexPosHomBifunction m n) :
    ∀ xStar : Fin n → ℝ, (0 : EReal) ≤ K.1 (0 : Fin m → ℝ) xStar := by
  intro xStar
  -- Step 1: every convex process contains the origin in its origin fiber.
  have hZeroMem : (0 : Fin n → ℝ) ∈ (toProcess K).1.toSetValued (0 : Fin m → ℝ) :=
    (toProcess K).1.zero_mem
  -- Step 2: after rewriting the reconstructed fiber, the zero-membership criterion yields the
  -- claimed pointwise nonnegativity.
  rw [hToProcess K] at hZeroMem
  exact
    (helperForTheorem_39_4_zero_mem_processMapOfBifunction_iff_nonnegSection
      (m := m) (n := n) K.1 (0 : Fin m → ℝ)).1 hZeroMem xStar

/-- Helper for Theorem 39.4: any reverse map whose fibers are prescribed by
`processMapOfBifunction` also forces the reconstructed graph to be closed, because its values lie
in the subtype of closed convex processes. -/
lemma helperForTheorem_39_4_graphClosed_of_reverseMap {m n : ℕ}
    (toProcess : LowerClosedConcaveConvexPosHomBifunction m n → ClosedConvexProcess m n)
    (hToProcess :
      ∀ K : LowerClosedConcaveConvexPosHomBifunction m n,
        (toProcess K).1.toSetValued = processMapOfBifunction (m := m) (n := n) K.1)
    (K : LowerClosedConcaveConvexPosHomBifunction m n) :
    _root_.IsClosed (setValuedGraph (processMapOfBifunction (m := m) (n := n) K.1)) := by
  -- Step 1: the codomain of `toProcess` packages closed convex processes, so its graph is closed.
  have hClosedProcess : (toProcess K).1.IsClosed := (toProcess K).2
  have hGraphClosed :
      _root_.IsClosed (setValuedGraph (toProcess K).1.toSetValued) :=
    (helperForProposition_39_0_13_graphClosed_iff_processClosed ((toProcess K).1)).2
      hClosedProcess
  -- Step 2: rewrite the graph along the prescribed half-space reconstruction identity.
  rw [hToProcess K] at hGraphClosed
  simpa using hGraphClosed

/-- Helper for Theorem 39.4: package the current Section 33 reverse bridge into the canonical
convex witness `F(u,x) = (K(u,·))^*(x)`. Chapter 8 only needs this local wrapper, so the single
remaining dependency on the old Section 33 reverse theorem stays isolated here. -/
lemma helperForTheorem_39_4_reverseConvexWitness_of_lowerClosed {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsLowerClosedConcaveConvexBifunction (m := m) (n := n) K)
    (hNoTopBot : HasNoTopOrBotValuesBifunction K) :
    let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => convexConjugate (K u) x
    IsImageClosedConvexBifunction F ∧
      (∀ (u : Fin m → ℝ) (x : Fin n → ℝ), F u x = convexConjugate (K u) x) ∧
        ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
          convexBifunctionPairing F u xStar = K u xStar := by
  rcases hK with ⟨hConcConv, hSecondClosed⟩
  let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => convexConjugate (K u) x
  simpa [F] using
    (lowerClosedConcaveConvex_and_upperClosedConvexConcave_pairing_correspondence
      (m := m) (n := n)).2.1 K hConcConv hSecondClosed hNoTopBot

/-- Helper for Theorem 39.4: the strong Section 33 lower-closed hypothesis already forces every
fixed covector section `u ↦ K(u, x*)` to be concave-closed, hence upper closed in the local
`EReal` notation of Section 39. -/
lemma helperForTheorem_39_4_upperClosedSections_of_lowerClosed {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsLowerClosedConcaveConvexBifunction (m := m) (n := n) K)
    (hNoTopBot : HasNoTopOrBotValuesBifunction K)
    (hFClosed : IsFunctionConvexClosed
      (graphFunctionOfBifunction (fun u x => convexConjugate (K u) x))) :
    ∀ xStar : Fin n → ℝ, IsUpperClosedEReal (fun u : Fin m → ℝ => K u xStar) := by
  have hBase := hK
  have hNoBotK : HasNoBotValuesBifunction K := hNoTopBot.1
  let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => convexConjugate (K u) x
  have hReverse :=
    helperForTheorem_39_4_reverseConvexWitness_of_lowerClosed
      (m := m) (n := n) (K := K) hBase hNoTopBot
  have hF_convex : IsRockafellarConvexBifunction F := hReverse.1.1
  have hF_noBot : HasNoBotValuesBifunction F := hReverse.1.2.1
  have hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F) := by
    simpa [F] using hFClosed
  have hF_graphConvex : IsGraphConvexBifunction F :=
    helperForTheorem33_0_39_graphConvex_of_graphFunctionClosed
      (F := F) hF_convex hF_noBot hF_closed
  have hPair : ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ), convexBifunctionPairing F u xStar = K u xStar :=
    hReverse.2.2
  have hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤ := by
    intro u
    by_contra hu
    have huOutside : u ∉ convexBifunctionParameterDomain F := by
      simpa [convexBifunctionParameterDomain] using hu
    have hPairBot : convexBifunctionPairing F u (0 : Fin n → ℝ) = ⊥ :=
      helperForCorollary33_2_2_convex_pairing_eq_bot_of_off_parameterDomain
        (G := F) huOutside (0 : Fin n → ℝ)
    have hKNoBotAtZero : K u (0 : Fin n → ℝ) ≠ (⊥ : EReal) := hNoBotK u 0
    exact hKNoBotAtZero (by simpa [hPair u (0 : Fin n → ℝ)] using hPairBot)
  intro xStar
  have hClosedSection :
      IsFunctionConcaveClosed (fun u : Fin m → ℝ => convexBifunctionPairing F u xStar) :=
    helperForLemma33_0_22_pairingSection_isFunctionConcaveClosed
      (F := F) (hF_convex := hF_graphConvex) (hF_closed := hF_closed)
      (hF_noBot := hF_noBot) (hF_notTop := hF_notTop) xStar
  have hEq :
      (fun u : Fin m → ℝ => convexBifunctionPairing F u xStar) =
        fun u : Fin m → ℝ => K u xStar := by
    funext u
    exact hPair u xStar
  have hClosedKSection : IsFunctionConcaveClosed (fun u : Fin m → ℝ => K u xStar) := by
    simpa [hEq] using hClosedSection
  exact
    helperForTheorem_39_3_functionConcaveClosed_to_IsUpperClosedEReal
      hClosedKSection

/-- Helper for Theorem 39.4: the upgraded Section 33 lower-closed kernel class, together with the
bihomogeneous scaling law, already forces the origin section to be pointwise nonnegative. -/
lemma helperForTheorem_39_4_nonneg_originSection_of_lowerClosedPosHom {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) K)
    (hNoBotK : HasNoBotValuesBifunction K) :
    ∀ xStar : Fin n → ℝ, (0 : EReal) ≤ K (0 : Fin m → ℝ) xStar := by
  rcases hK with ⟨_hBase, hNormHom⟩
  intro xStar
  by_cases hTop : K (0 : Fin m → ℝ) xStar = (⊤ : EReal)
  · simp [hTop]
  · have hBot : K (0 : Fin m → ℝ) xStar ≠ (⊥ : EReal) := hNoBotK 0 xStar
    let a : ℝ := (K (0 : Fin m → ℝ) xStar).toReal
    have hFinite : ((a : ℝ) : EReal) = K (0 : Fin m → ℝ) xStar := by
      exact EReal.coe_toReal hTop hBot
    have hScale :
        K (0 : Fin m → ℝ) xStar = ((2 : ℝ) : EReal) * K (0 : Fin m → ℝ) xStar := by
      simpa using (hNormHom.2 2 zero_lt_two (0 : Fin m → ℝ) xStar).1
    have hScaleReal :
        ((a : ℝ) : EReal) = (((2 : ℝ) * a : ℝ) : EReal) := by
      calc
        ((a : ℝ) : EReal) = K (0 : Fin m → ℝ) xStar := hFinite
        _ = ((2 : ℝ) : EReal) * K (0 : Fin m → ℝ) xStar := hScale
        _ = ((2 : ℝ) : EReal) * ((a : ℝ) : EReal) := by rw [← hFinite]
        _ = (((2 : ℝ) * a : ℝ) : EReal) := by rw [EReal.coe_mul]
    have haEq : a = 2 * a := by
      exact_mod_cast hScaleReal
    have ha : a = 0 := by
      linarith
    have hZero : K (0 : Fin m → ℝ) xStar = (0 : EReal) := by
      calc
        K (0 : Fin m → ℝ) xStar = ((a : ℝ) : EReal) := by symm; exact hFinite
        _ = 0 := by simp [ha]
    simp [hZero]

/-- Helper for Theorem 39.4: once "lower closed" is upgraded to the strong Section 33 notion,
the two extra working assumptions on the reverse map are derivable instead of being postulated. -/
lemma helperForTheorem_39_4_workingKernel_of_lowerClosedPosHom {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) K)
    (hNoTopBot : HasNoTopOrBotValuesBifunction K)
    (hFClosed : IsFunctionConvexClosed
      (graphFunctionOfBifunction (fun u x => convexConjugate (K u) x))) :
    IsWorkingLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) K := by
  refine ⟨hK, hNoTopBot, ?_, ?_⟩
  · exact
      helperForTheorem_39_4_nonneg_originSection_of_lowerClosedPosHom
        (m := m) (n := n) hK hNoTopBot.1
  · exact
      helperForTheorem_39_4_upperClosedSections_of_lowerClosed
        (m := m) (n := n) hK.1 hNoTopBot hFClosed

/-- Helper for Theorem 39.4: a working kernel has a nonempty reconstructed origin fiber and a
closed reconstructed graph, exactly the two structural properties missing from the weaker local
kernel class. -/
lemma helperForTheorem_39_4_processMap_origin_mem_and_graphClosed_of_workingKernel {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsWorkingLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) K) :
    (0 : Fin n → ℝ) ∈ processMapOfBifunction (m := m) (n := n) K (0 : Fin m → ℝ) ∧
      _root_.IsClosed (setValuedGraph (processMapOfBifunction (m := m) (n := n) K)) := by
  rcases hK with ⟨_hBase, _hNoTopBot, hOriginNonneg, hUpper⟩
  constructor
  · exact
      helperForTheorem_39_4_zero_mem_processMapOfBifunction_of_nonnegSection
        (m := m) (n := n) K (0 : Fin m → ℝ) hOriginNonneg
  · exact
      helperForTheorem_39_4_processMapOfBifunction_graphClosed_of_upperClosedSections
        (m := m) (n := n) K hUpper

/-- Helper for Theorem 39.4: scaling the input parameter of the half-space reconstruction by a
positive scalar scales the output fiber by the same factor, provided `K` is bihomogeneous in the
parameter variable. -/
lemma helperForTheorem_39_4_processMapOfBifunction_map_smul_pos {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hHom : IsNormalizedBihomogeneousERealBifunction (m := m) (n := n) K) :
    ∀ u (r : ℝ), 0 < r →
      processMapOfBifunction (m := m) (n := n) K (r • u) =
        r • processMapOfBifunction (m := m) (n := n) K u := by
  intro u r hr
  ext x
  constructor
  · intro hx
    refine Set.mem_smul_set.2 ?_
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · intro xStar
      have hx' :
          (((finDot x xStar : ℝ) : EReal)) ≤ K (r • u) xStar := by
        simpa [processMapOfBifunction] using hx xStar
      have hxScaled :
          ((r⁻¹ : ℝ) : EReal) * (((finDot x xStar : ℝ) : EReal)) ≤
            ((r⁻¹ : ℝ) : EReal) * K (r • u) xStar := by
        gcongr
      have hParamScale :
          K (r • u) xStar = ((r : ℝ) : EReal) * K u xStar := by
        simpa using (hHom.2 r hr u xStar).1
      have hInvMul : (r⁻¹ * r : ℝ) = 1 := by
        field_simp [hr.ne']
      calc
        (((finDot (r⁻¹ • x) xStar : ℝ) : EReal))
            = ((r⁻¹ : ℝ) : EReal) * (((finDot x xStar : ℝ) : EReal)) := by
                simp [finDot, smul_eq_mul, EReal.coe_mul, mul_comm]
        _ ≤ ((r⁻¹ : ℝ) : EReal) * K (r • u) xStar := hxScaled
        _ = ((r⁻¹ : ℝ) : EReal) * (((r : ℝ) : EReal) * K u xStar) := by
              rw [hParamScale]
        _ = (((r⁻¹ * r : ℝ) : EReal) * K u xStar) := by
              rw [← mul_assoc, EReal.coe_mul]
        _ = K u xStar := by
              simp [hInvMul]
    · ext i
      change r * (r⁻¹ * x i) = x i
      field_simp [hr.ne']
  · intro hx
    rcases Set.mem_smul_set.1 hx with ⟨y, hy, rfl⟩
    intro xStar
    have hy' :
        (((finDot y xStar : ℝ) : EReal)) ≤ K u xStar := by
      simpa [processMapOfBifunction] using hy xStar
    have hyScaled :
        ((r : ℝ) : EReal) * (((finDot y xStar : ℝ) : EReal)) ≤
          ((r : ℝ) : EReal) * K u xStar := by
      gcongr
    have hParamScale :
        K (r • u) xStar = ((r : ℝ) : EReal) * K u xStar := by
      simpa using (hHom.2 r hr u xStar).1
    calc
      (((finDot (r • y) xStar : ℝ) : EReal))
          = ((r : ℝ) : EReal) * (((finDot y xStar : ℝ) : EReal)) := by
              simp [finDot, smul_eq_mul, EReal.coe_mul]
      _ ≤ ((r : ℝ) : EReal) * K u xStar := hyScaled
      _ = K (r • u) xStar := by rw [hParamScale]
end ConvexProcess
end Section39
end Chap08
