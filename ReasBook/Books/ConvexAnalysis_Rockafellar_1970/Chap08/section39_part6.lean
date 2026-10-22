/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part5

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

section Chap08
section Section39

namespace ConvexProcess

/-- Helper for Theorem 39.3: a function that is concave-closed in the Section 33 sense has a
closed hypograph in the local `EReal` notation used for the infimum-oriented branch. -/
lemma helperForTheorem_39_3_functionConcaveClosed_to_IsUpperClosedEReal {n : ℕ}
    {g : (Fin n → ℝ) → EReal}
    (hClosed : IsFunctionConcaveClosed g) :
    IsUpperClosedEReal g := by
  have hNegClosed : IsFunctionConvexClosed (fun x => -g x) :=
    (helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed
      (g := g)).mp hClosed
  have hNegLsc : LowerSemicontinuous (fun x => -g x) := by
    -- The raw convex closure is always lower semicontinuous, and a convex-closed function agrees
    -- with that closure.
    have hClosureLsc :
        LowerSemicontinuous (functionConvexClosure (fun x => -g x)) :=
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
        (f := fun x => -g x)
    exact hNegClosed ▸ hClosureLsc
  have hUpperSc : UpperSemicontinuous g :=
    (helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg
      (g := g)).2 hNegLsc
  have hClosedHypographEReal :
      _root_.IsClosed {p : (Fin n → ℝ) × EReal | p.2 ≤ g p.1} :=
    hUpperSc.IsClosed_hypograph
  let realToERealHeight : (Fin n → ℝ) × ℝ → (Fin n → ℝ) × EReal :=
    fun p => (p.1, (p.2 : EReal))
  have hRealToERealHeightCont : Continuous realToERealHeight := by
    -- Compare the real-height hypograph with the standard `EReal` hypograph through coercion.
    simpa [realToERealHeight] using
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  have hPreimage :
      realToERealHeight ⁻¹' {p : (Fin n → ℝ) × EReal | p.2 ≤ g p.1} =
        eRealHypograph g := by
    ext p
    simp [realToERealHeight, eRealHypograph]
  -- Pull the closed `EReal`-hypograph back to the real-height hypograph used locally.
  unfold IsUpperClosedEReal
  rw [← hPreimage]
  exact hClosedHypographEReal.preimage hRealToERealHeightCont

/-- Helper for Theorem 39.3: negating a concave section that avoids `⊤` turns it into a convex
section. -/
lemma helperForTheorem_39_3_concaveNegation_isConvex_of_noTop {k : ℕ}
    {f : (Fin k → ℝ) → EReal}
    (hConc : IsERealConcaveOn (Set.univ : Set (Fin k → ℝ)) f)
    (hNoTop : ∀ x, f x ≠ ⊤) :
    IsERealConvexOn (Set.univ : Set (Fin k → ℝ)) (fun x => -f x) := by
  -- Step 1: start from the Jensen inequality for the original concave section.
  intro x y hx hy a b ha hb hab hxy
  have hJensen :
      (a : EReal) * f x + (b : EReal) * f y ≤ f (a • x + b • y) :=
    hConc (x := x) (y := y) hx hy ha hb hab hxy
  have hTerm1_ne_top : (a : EReal) * f x ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inl ?_, Or.inl (EReal.coe_ne_top a), ?_⟩
    · exact_mod_cast ha
    · by_cases hZero : a = 0
      · left
        simp [hZero]
      · right
        exact hNoTop x
  have hTerm2_ne_top : (b : EReal) * f y ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot b), Or.inl ?_, Or.inl (EReal.coe_ne_top b), ?_⟩
    · exact_mod_cast hb
    · by_cases hZero : b = 0
      · left
        simp [hZero]
      · right
        exact hNoTop y
  -- Step 2: after ruling out the `⊤` branches, negation distributes across the weighted sum.
  have hNegJensen :
      -f (a • x + b • y) ≤ -((a : EReal) * f x + (b : EReal) * f y) := by
    simpa using hJensen
  have hNegWeighted :
      -((a : EReal) * f x + (b : EReal) * f y) =
        (a : EReal) * (-f x) + (b : EReal) * (-f y) := by
    have hNegAdd :=
      EReal.neg_add (x := (a : EReal) * f x) (y := (b : EReal) * f y)
        (Or.inr hTerm2_ne_top) (Or.inl hTerm1_ne_top)
    simpa [sub_eq_add_neg, mul_neg, neg_mul, add_comm] using hNegAdd
  calc
    -f (a • x + b • y) ≤ -((a : EReal) * f x + (b : EReal) * f y) := hNegJensen
    _ = (a : EReal) * (-f x) + (b : EReal) * (-f y) := hNegWeighted

/-- Helper for Theorem 39.3: the infimum-oriented negative indicator bifunction satisfies the
Section 33 concave package, and graph closedness follows from the closed graph of the process
after a global sign flip. -/
lemma helperForTheorem_39_3_indicator_infimum_package {m n : ℕ}
    (A : ConvexProcess m n) :
    (HasNoTopValuesBifunction
        (convexBifunctionPairing (ConvexProcess.indicatorBifunction A)) →
      IsRockafellarConcaveBifunction (ConvexProcess.negIndicatorBifunction A)) ∧
      HasNoTopValuesBifunction (ConvexProcess.negIndicatorBifunction A) ∧
      (A.IsClosed →
        IsFunctionConcaveClosed
          (graphFunctionOfBifunction (ConvexProcess.negIndicatorBifunction A))) := by
  refine ⟨?_, helperForTheorem_39_3_negIndicator_hasNoTopValues A, ?_⟩
  · intro hPairNoTop
    refine ⟨helperForTheorem_39_2_negIndicatorConcave A, ?_⟩
    intro xStar
    -- Step 1: invoke the Section 33 negation bridge on the ordinary indicator package.
    have hRock : IsRockafellarConvexBifunction (ConvexProcess.indicatorBifunction A) :=
      (indicatorBifunction_rockafellarPackage A).1
    have hNoBot : HasNoBotValuesBifunction (ConvexProcess.indicatorBifunction A) :=
      (indicatorBifunction_rockafellarPackage A).2.1
    have hPairConv :
        IsERealConvexOn (Set.univ : Set (Fin m → ℝ))
          (fun u => -convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u (-xStar)) :=
      helperForCorollary33_2_1_negConvexPairingSection_isERealConvexOn
        (F := ConvexProcess.indicatorBifunction A) hRock hNoBot (-xStar)
        (fun u => hPairNoTop u (-xStar))
    convert hPairConv using 1
    funext u
    calc
      concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar =
          -convexBifunctionPairing
            (fun u' x => -(ConvexProcess.negIndicatorBifunction A u' x)) u (-xStar) := by
              simpa using
                helperForCorollary33_2_1_concavePairing_eq_neg_convexPairing_of_neg
                  (F := ConvexProcess.negIndicatorBifunction A) u xStar
      _ = -convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u (-xStar) := by
            rw [helperForTheorem_39_3_neg_negIndicatorBifunction_eq_indicator A]
  · intro hAClosed
    -- Step 3: the negated graph function of the negative indicator is exactly the ordinary graph
    -- indicator, so the convex closedness package transfers across negation.
    have hClosedConv :
        IsFunctionConvexClosed
          (graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A)) :=
      (indicatorBifunction_rockafellarPackage A).2.2 hAClosed
    have hEq :
        (fun z : Fin (m + n) → ℝ =>
          -graphFunctionOfBifunction (ConvexProcess.negIndicatorBifunction A) z) =
          graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A) := by
      funext z
      by_cases hz :
          (fun j => z (Fin.natAdd m j)) ∈ A.toSetValued (fun i => z (Fin.castAdd n i))
      · simp [graphFunctionOfBifunction, ConvexProcess.negIndicatorBifunction,
          ConvexProcess.indicatorBifunction, negIndicatorEReal, indicatorEReal, hz]
      · simp [graphFunctionOfBifunction, ConvexProcess.negIndicatorBifunction,
          ConvexProcess.indicatorBifunction, negIndicatorEReal, indicatorEReal, hz]
    exact
      (helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed
        (g := graphFunctionOfBifunction (ConvexProcess.negIndicatorBifunction A))).2
        (by simpa [hEq] using hClosedConv)

/-- Helper for Theorem 39.3: in the supremum-oriented Section 33 package, the parameter domain
`{u | ∃ x, F u x < ⊤}` of the indicator bifunction is exactly `dom A`. -/
lemma helperForTheorem_39_3_indicator_parameterDomain_eq_dom {m n : ℕ}
    (A : ConvexProcess m n) :
    {u : Fin m → ℝ | ∃ x : Fin n → ℝ, ConvexProcess.indicatorBifunction A u x < ⊤} = A.dom := by
  ext u
  -- Step 1: the indicator value is strictly below `⊤` exactly on members of the fiber `A u`.
  constructor
  · rintro ⟨x, hxFinite⟩
    have hxMem : x ∈ A.toSetValued u := by
      by_cases hx : x ∈ A.toSetValued u
      · exact hx
      · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hx] at hxFinite
    simpa [ConvexProcess.dom, setValuedDom, Set.nonempty_def] using ⟨x, hxMem⟩
  · intro huMem
    rcases huMem with ⟨x, hxMem⟩
    refine ⟨x, ?_⟩
    simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxMem]

/-- Helper for Theorem 39.3: in the infimum-oriented Section 33 package, the parameter domain
`{u | ∃ x, -δ(x | A u) ≠ ⊥}` of the negative indicator bifunction is exactly `dom A`. -/
lemma helperForTheorem_39_3_negIndicator_parameterDomain_eq_dom {m n : ℕ}
    (A : ConvexProcess m n) :
    {u : Fin m → ℝ | ∃ x : Fin n → ℝ, ConvexProcess.negIndicatorBifunction A u x ≠ ⊥} = A.dom := by
  ext u
  -- Step 1: the negative indicator avoids `⊥` exactly on points lying in the fiber `A u`.
  simp [ConvexProcess.negIndicatorBifunction, ConvexProcess.dom, negIndicatorEReal, setValuedDom,
    Set.nonempty_def]

/-- Helper for Theorem 39.3: if `u ∈ ri (dom A)`, then in the supremum-oriented Section 33
package the primal pairing already equals the adjoint pairing for every `x*`. -/
lemma helperForTheorem_39_3_supremum_pairing_eq_on_ri_dom {m n : ℕ}
    (A : ConvexProcess m n)
    (hGraph : IsGraphConvexBifunction (ConvexProcess.indicatorBifunction A))
    {u : Fin m → ℝ} (hu : u ∈ intrinsicInterior ℝ A.dom) :
    ∀ xStar : Fin n → ℝ,
      convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u xStar =
        convexBifunctionCanonicalAdjointPairing
          (ConvexProcess.indicatorBifunction A) xStar u := by
  -- Step 1: package the Section 33 convex hypotheses for the indicator bifunction.
  have hNoBot : HasNoBotValuesBifunction (ConvexProcess.indicatorBifunction A) :=
    (indicatorBifunction_rockafellarPackage A).2.1
  have huSection33 :
      u ∈ intrinsicInterior ℝ
        {u' : Fin m → ℝ | ∃ x : Fin n → ℝ, ConvexProcess.indicatorBifunction A u' x < ⊤} := by
    -- Step 2: rewrite the Section 33 parameter domain back to `dom A` before invoking the
    -- relative-interior theorem.
    have hu' := hu
    rw [← helperForTheorem_39_3_indicator_parameterDomain_eq_dom A] at hu'
    exact hu'
  -- Step 3: apply the relative-interior equality theorem on the convex branch.
  intro xStar
  exact
    ((adjoint_pairing_eq_on_relativeInterior_domains (m := m) (n := n)).1
      (F := ConvexProcess.indicatorBifunction A) ⟨hGraph, hNoBot⟩).1 huSection33 xStar

/-- Helper for Theorem 39.3: if `u ∈ ri (dom A)`, then in the infimum-oriented Section 33
package the primal pairing already equals the adjoint pairing for every `x*`. -/
lemma helperForTheorem_39_3_infimum_pairing_eq_on_ri_dom {m n : ℕ}
    (A : ConvexProcess m n)
    (hGraph : IsGraphConcaveBifunction (ConvexProcess.negIndicatorBifunction A))
    {u : Fin m → ℝ} (hu : u ∈ intrinsicInterior ℝ A.dom) :
    ∀ xStar : Fin n → ℝ,
      concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar =
        concaveBifunctionCanonicalAdjointPairing
          (ConvexProcess.negIndicatorBifunction A) xStar u := by
  -- Step 1: package the Section 33 concave hypotheses for the negative indicator bifunction.
  have hNoTop : HasNoTopValuesBifunction (ConvexProcess.negIndicatorBifunction A) :=
    (helperForTheorem_39_3_indicator_infimum_package A).2.1
  have huSection33 :
      u ∈ intrinsicInterior ℝ
        {u' : Fin m → ℝ | ∃ x : Fin n → ℝ, ConvexProcess.negIndicatorBifunction A u' x ≠ ⊥} := by
    -- Step 2: rewrite the Section 33 parameter domain back to `dom A` before invoking the
    -- relative-interior theorem.
    have hu' := hu
    rw [← helperForTheorem_39_3_negIndicator_parameterDomain_eq_dom A] at hu'
    exact hu'
  -- Step 3: apply the relative-interior equality theorem on the concave branch.
  intro xStar
  exact
    ((adjoint_pairing_eq_on_relativeInterior_domains (m := m) (n := n)).2
      (F := ConvexProcess.negIndicatorBifunction A) ⟨hGraph, hNoTop⟩).1 huSection33 xStar

/-- Helper for Theorem 39.3: the genuine Section 33 adjoint effective domain in the supremum
branch is all of `ℝ^n`, because the origin fiber contributes the finite value `0`. -/
lemma helperForTheorem_39_3_supremum_adjSectionDomain_univ {m n : ℕ}
    (A : ConvexProcess m n) :
    {xStar : Fin n → ℝ |
        ∃ u : Fin m → ℝ,
          convexBifunctionAdjoint (ConvexProcess.indicatorBifunction A) xStar u ≠ ⊥} =
      Set.univ := by
  ext xStar
  constructor
  · intro _hxStar
    simp
  · intro _hxStar
    refine ⟨0, ?_⟩
    -- Step 1: the origin belongs to `A 0`, so the frozen support section at `u = 0` is at least
    -- `0` and therefore cannot be `⊥`.
    have hZeroLePair :
        (0 : EReal) ≤
          convexBifunctionPairing (ConvexProcess.indicatorBifunction A) (0 : Fin m → ℝ) xStar := by
      have hBracketEq :
          setBracketVec ConvexSetOrientation.supremum (A.toSetValued (0 : Fin m → ℝ)) xStar =
            convexBifunctionPairing (ConvexProcess.indicatorBifunction A) (0 : Fin m → ℝ) xStar := by
        simpa using
          helperForTheorem_39_3_bracket_eq_orientedPairing
            ConvexSetOrientation.supremum A (0 : Fin m → ℝ) xStar
      rw [← hBracketEq]
      unfold setBracketVec
      apply le_sSup
      refine ⟨0, A.zero_mem, ?_⟩
      simp [finDot]
    have hZeroLe :
        (0 : EReal) ≤
          convexBifunctionAdjoint (ConvexProcess.indicatorBifunction A) xStar (0 : Fin m → ℝ) := by
      simpa [convexBifunctionAdjoint] using hZeroLePair
    intro hBot
    have : (0 : EReal) ≤ (⊥ : EReal) := by
      simpa [hBot] using hZeroLe
    simpa using this

/-- Helper for Theorem 39.3: every point in `dom A*` for the infimum-oriented adjoint already lies
in the Section 33 adjoint effective domain of the negative indicator package. -/
lemma helperForTheorem_39_3_infimum_domAstar_subset_concaveAdjointDomain {m n : ℕ}
    (A : ConvexProcess m n) :
    setValuedDom (adjointVecOriented ConvexSetOrientation.infimum A).toSetValued ⊆
      {xStar : Fin n → ℝ |
        ∃ u : Fin m → ℝ,
          concaveBifunctionAdjoint (ConvexProcess.negIndicatorBifunction A) xStar u ≠ ⊥} := by
  intro xStar hxStar
  rcases hxStar with ⟨u, hu⟩
  change u ∈ setValuedAdjointVecInf A.toSetValued xStar at hu
  refine ⟨u, ?_⟩
  change concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar ≠ ⊥
  -- Step 1: the adjoint-fiber witness bounds every primal pairing from below by `⟪u, u⟫`,
  -- preventing the infimum bracket from dropping to `⊥`.
  have hLowerBound :
      (((finDot u u : ℝ) : EReal)) ≤
        setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar := by
    unfold setBracketVec
    apply le_sInf
    rintro r ⟨x, hx, rfl⟩
    have hIneq : finDot u u ≤ finDot x xStar := hu u x hx
    exact
      (show (((finDot u u : ℝ) : EReal)) ≤ (((finDot x xStar : ℝ) : EReal)) from by
        exact_mod_cast hIneq)
  have hBracketEq :
      setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar =
        concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar :=
    helperForTheorem_39_3_bracket_eq_orientedPairing
      ConvexSetOrientation.infimum A u xStar
  intro hBot
  have hBot' :
      setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar = ⊥ := by
    simpa [hBracketEq] using hBot
  have : (((finDot u u : ℝ) : EReal)) ≤ (⊥ : EReal) := by
    simpa [hBot'] using hLowerBound
  simpa using this

/-- Helper for Theorem 39.3: in the infimum-oriented branch, the Section 33 adjoint effective
domain of the negative indicator package is exactly the set of dual vectors for which some primal
parameter bracket is not `⊥`. -/
lemma helperForTheorem_39_3_infimum_adjSectionDomain_eq_parameterBracketDomain {m n : ℕ}
    (A : ConvexProcess m n) :
    {xStar : Fin n → ℝ |
        ∃ u : Fin m → ℝ,
          concaveBifunctionAdjoint (ConvexProcess.negIndicatorBifunction A) xStar u ≠ ⊥} =
      {xStar : Fin n → ℝ |
        ∃ u : Fin m → ℝ,
          setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar ≠ ⊥} := by
  ext xStar
  constructor
  · intro hxStar
    rcases hxStar with ⟨u, hu⟩
    have hBracketEq :
        setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar =
          concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar :=
      helperForTheorem_39_3_bracket_eq_orientedPairing
        ConvexSetOrientation.infimum A u xStar
    refine ⟨u, ?_⟩
    -- Step 1: rewrite the Section 33 adjoint section back to the local infimum bracket.
    intro hBot
    apply hu
    simpa [concaveBifunctionAdjoint, hBracketEq] using hBot
  · intro hxStar
    rcases hxStar with ⟨u, hu⟩
    have hBracketEq :
        setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar =
          concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u xStar :=
      helperForTheorem_39_3_bracket_eq_orientedPairing
        ConvexSetOrientation.infimum A u xStar
    refine ⟨u, ?_⟩
    -- Step 2: convert the local bracket witness to the matching Section 33 pairing witness.
    intro hBot
    apply hu
    simpa [concaveBifunctionAdjoint, hBracketEq] using hBot

/-- Helper for Theorem 39.3: in the supremum-oriented branch, membership in the adjoint fiber is
exactly the statement that the parameter section `u ↦ ⟪A u, x*⟫` admits `uStar` as a global linear
majorant. -/
lemma helperForTheorem_39_3_supremum_adjointFiber_mem_iff_parameter_majorant {m n : ℕ}
    (A : ConvexProcess m n) (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    uStar ∈ setValuedAdjointVec A.toSetValued xStar ↔
      ∀ u : Fin m → ℝ,
        setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar ≤
          (((finDot u uStar : ℝ) : EReal)) := by
  constructor
  · intro huStar u
    -- Step 1: every point of the fiber contributes a dot product bounded by the adjoint witness.
    unfold setBracketVec
    refine sSup_le ?_
    rintro r ⟨x, hx, rfl⟩
    exact
      (show (((finDot x xStar : ℝ) : EReal)) ≤ (((finDot u uStar : ℝ) : EReal)) from by
        exact_mod_cast huStar u x hx)
  · intro hMajorant u x hx
    -- Step 2: recover the defining adjoint inequality by testing the majorant on the witness `x`.
    have hxLeBracket :
        (((finDot x xStar : ℝ) : EReal)) ≤
          setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar := by
      unfold setBracketVec
      refine le_sSup ?_
      exact ⟨x, hx, rfl⟩
    have hxLeDot :
        (((finDot x xStar : ℝ) : EReal)) ≤ (((finDot u uStar : ℝ) : EReal)) :=
      le_trans hxLeBracket (hMajorant u)
    exact_mod_cast hxLeDot

/-- Helper for Theorem 39.3: in the infimum-oriented branch, membership in the adjoint fiber is
exactly the statement that the parameter section `u ↦ ⟪A u, x*⟫` dominates the linear form
`u ↦ ⟪u, u*⟫` pointwise. -/
lemma helperForTheorem_39_3_infimum_adjointFiber_mem_iff_parameter_minorant {m n : ℕ}
    (A : ConvexProcess m n) (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    uStar ∈ setValuedAdjointVecInf A.toSetValued xStar ↔
      ∀ u : Fin m → ℝ,
        (((finDot u uStar : ℝ) : EReal)) ≤
          setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar := by
  constructor
  · intro huStar u
    -- Step 1: every point of the fiber contributes an upper bound for the infimum bracket.
    unfold setBracketVec
    refine le_sInf ?_
    rintro r ⟨x, hx, rfl⟩
    exact
      (show (((finDot u uStar : ℝ) : EReal)) ≤ (((finDot x xStar : ℝ) : EReal)) from by
        exact_mod_cast huStar u x hx)
  · intro hMinorant u x hx
    -- Step 2: recover the defining adjoint inequality by comparing with the witness `x`.
    have hBracketLeX :
        setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar ≤
          (((finDot x xStar : ℝ) : EReal)) := by
      unfold setBracketVec
      refine sInf_le ?_
      exact ⟨x, hx, rfl⟩
    have hDotLeX :
        (((finDot u uStar : ℝ) : EReal)) ≤ (((finDot x xStar : ℝ) : EReal)) :=
      le_trans (hMinorant u) hBracketLeX
    exact_mod_cast hDotLeX

/-- Helper for Theorem 39.3: convexity of the height-flipped epigraph is exactly Chapter 6
concavity of the original function. -/
lemma helperForTheorem_39_3_isConcaveEReal_to_ConcaveFunction {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hConc : IsConcaveEReal f) :
    ConcaveFunction f := by
  let flipHeight : ((Fin n → ℝ) × ℝ) → ((Fin n → ℝ) × ℝ) := fun p => (p.1, -p.2)
  have hPre :
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) (fun x => -f x) =
        flipHeight ⁻¹' eRealHypograph f := by
    -- Step 1: the epigraph of `-f` is the height-flipped preimage of the hypograph of `f`.
    ext p
    constructor
    · intro hp
      rcases hp with ⟨_hpUniv, hpHeight⟩
      change (((-p.2 : ℝ) : EReal)) ≤ f p.1
      have : -((p.2 : ℝ) : EReal) ≤ -(-f p.1) := (EReal.neg_le_neg_iff).2 hpHeight
      simpa using this
    · intro hp
      refine ⟨by trivial, ?_⟩
      change (((-p.2 : ℝ) : EReal)) ≤ f p.1 at hp
      have : -f p.1 ≤ ((p.2 : ℝ) : EReal) := by
        have hp' : (((-p.2 : ℝ) : EReal)) ≤ -(-f p.1) := by
          simpa using hp
        exact (EReal.neg_le_neg_iff).1 hp'
      exact this
  -- Step 2: after rewriting the epigraph, the Chapter 6 concavity predicate is the same convex
  -- hypograph statement already packaged by `IsConcaveEReal`.
  rw [ConcaveFunction, ConvexFunction, ConvexFunctionOn, hPre]
  rw [IsConcaveEReal] at hConc
  intro p hp q hq a b ha hb hab
  have hMap :
      flipHeight (a • p + b • q) = a • flipHeight p + b • flipHeight q := by
    ext <;> simp [flipHeight, mul_add, add_mul, add_comm, add_left_comm, add_assoc]
  have hCombo : a • flipHeight p + b • flipHeight q ∈ eRealHypograph f :=
    hConc hp hq ha hb hab
  simpa [hMap] using hCombo

/-- Helper for Theorem 39.3: in the supremum-oriented branch, the first conjugate of the parameter
section is exactly the negative indicator of the actual adjoint fiber. -/
lemma helperForTheorem_39_3_supremum_parameterConjugate_eq_adjointFiberIndicator {m n : ℕ}
    (A : ConvexProcess m n) (xStar : Fin n → ℝ) :
    concaveConjugate
        (fun u : Fin m → ℝ =>
          setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar) =
      fun uStar : Fin m → ℝ =>
        negIndicatorEReal (setValuedAdjointVec A.toSetValued xStar) uStar := by
  funext uStar
  let g : (Fin m → ℝ) → EReal :=
    fun u : Fin m → ℝ =>
      setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar
  -- Step 1: unfold the concave conjugate to the raw infimum of affine offsets.
  rw [helperForTheorem_6_30_4_concaveConjugate_eq_iInf (g := g) (xStar := uStar)]
  let φ : (Fin m → ℝ) → EReal :=
    fun u : Fin m → ℝ => (((finDot u uStar : ℝ) : EReal)) + (-g u)
  change iInf φ = negIndicatorEReal (setValuedAdjointVec A.toSetValued xStar) uStar
  by_cases hu : uStar ∈ setValuedAdjointVec A.toSetValued xStar
  · -- Step 2: on the adjoint fiber, every affine offset is nonnegative and the origin attains `0`.
    have hMajorant :
        ∀ u : Fin m → ℝ, g u ≤ (((finDot u uStar : ℝ) : EReal)) := by
      simpa [g] using
        (helperForTheorem_39_3_supremum_adjointFiber_mem_iff_parameter_majorant A xStar uStar).1 hu
    have hPhiNonneg : ∀ u : Fin m → ℝ, (0 : EReal) ≤ φ u := by
      intro u
      have hSub :
          (0 : EReal) ≤ (((finDot u uStar : ℝ) : EReal)) - g u :=
        (EReal.sub_nonneg
          (Or.inl (by simp))
          (Or.inl (by simp))).2 (hMajorant u)
      simpa [φ, sub_eq_add_neg] using hSub
    have hSectionZero : g 0 = 0 := by
      have hUpper : g 0 ≤ 0 := by
        simpa [g, finDot] using hMajorant (0 : Fin m → ℝ)
      have hLower : (0 : EReal) ≤ g 0 := by
        unfold g setBracketVec
        exact le_sSup ⟨0, A.zero_mem, by simp [finDot]⟩
      exact le_antisymm hUpper hLower
    have hInfNonneg : (0 : EReal) ≤ iInf φ := by
      exact le_iInf hPhiNonneg
    have hInfLeZero : iInf φ ≤ 0 := by
      have hEval : iInf φ ≤ φ 0 := iInf_le φ 0
      simpa [φ, hSectionZero, finDot] using hEval
    have hInfEq : iInf φ = 0 := le_antisymm hInfLeZero hInfNonneg
    simp [negIndicatorEReal, hu, hInfEq]
  · -- Step 3: off the adjoint fiber, a violating direction drives the infimum to `⊥`.
    have hNotMajorant :
        ¬ ∀ u : Fin m → ℝ, g u ≤ (((finDot u uStar : ℝ) : EReal)) := by
      intro hMajorant
      exact hu <|
        (helperForTheorem_39_3_supremum_adjointFiber_mem_iff_parameter_majorant A xStar uStar).2
          (by simpa [g] using hMajorant)
    push_neg at hNotMajorant
    rcases hNotMajorant with ⟨u0, hNotLe⟩
    have hViol : (((finDot u0 uStar : ℝ) : EReal)) < g u0 := hNotLe
    have hInfBot : iInf φ = ⊥ := by
      apply (EReal.eq_bot_iff_forall_lt (x := iInf φ)).2
      intro μ
      by_cases hTop : g u0 = ⊤
      · have hLe : iInf φ ≤ φ u0 := iInf_le φ u0
        have hTermBot : φ u0 = ⊥ := by
          simp [φ, hTop]
        have hBotLt : (⊥ : EReal) < (μ : EReal) := by simp
        exact lt_of_le_of_lt (by simpa [hTermBot] using hLe) hBotLt
      · have hNotBot : g u0 ≠ ⊥ := by
          intro hBot
          have : (((finDot u0 uStar : ℝ) : EReal)) < (⊥ : EReal) := by
            simpa [hBot] using hViol
          simpa using this
        let r : ℝ := (g u0).toReal
        have hgEq : g u0 = (r : EReal) := by
          have hcoe : (((g u0).toReal : ℝ) : EReal) = g u0 :=
            EReal.coe_toReal hTop hNotBot
          simpa [r] using hcoe.symm
        have hViolReal : finDot u0 uStar < r := by
          have : (((finDot u0 uStar : ℝ) : EReal)) < ((r : ℝ) : EReal) := by
            simpa [hgEq] using hViol
          exact_mod_cast this
        let c : ℝ := finDot u0 uStar - r
        have hcNeg : c < 0 := by
          dsimp [c]
          linarith
        let t : ℝ := |μ| / (-c) + 1
        have ht : 0 < t := by
          have hden : 0 < -c := by linarith
          have hdiv : 0 ≤ |μ| / (-c) := by
            exact div_nonneg (abs_nonneg μ) (le_of_lt hden)
          dsimp [t]
          linarith
        have hScale :
            φ (t • u0) = (((t * c : ℝ) : EReal)) := by
          have hSectionScale :
              g (t • u0) = (t : EReal) * g u0 :=
            helperForTheorem_39_3_parameterSection_posHomogeneous
              ConvexSetOrientation.supremum A xStar u0 t ht
          have hDotScale :
              (((finDot (t • u0) uStar : ℝ) : EReal)) =
                (((t * finDot u0 uStar : ℝ) : EReal)) := by
            simp [finDot, smul_dotProduct, mul_comm]
          simp [φ, hDotScale, hSectionScale, hgEq, c, sub_eq_add_neg, mul_add, add_mul, mul_assoc,
            mul_comm, mul_left_comm]
        have htc : t * c < μ := by
          have hcNe : c ≠ 0 := by linarith
          have hcalc : t * c = -|μ| + c := by
            calc
              t * c = (|μ| / (-c) + 1) * c := by rfl
              _ = |μ| / (-c) * c + c := by ring
              _ = -|μ| + c := by
                    field_simp [hcNe]
          have hltNegAbs : -|μ| + c < -|μ| := by linarith
          have hnegAbsLe : -|μ| ≤ μ := neg_abs_le μ
          rw [hcalc]
          exact lt_of_lt_of_le hltNegAbs hnegAbsLe
        have hltEval : φ (t • u0) < (μ : EReal) := by
          rw [hScale]
          exact_mod_cast htc
        exact lt_of_le_of_lt (iInf_le φ (t • u0)) hltEval
    simp [negIndicatorEReal, hu, hInfBot]

/-- Helper for Theorem 39.3: in the infimum-oriented branch, the first conjugate of the parameter
section is exactly the indicator of the actual adjoint fiber. -/
lemma helperForTheorem_39_3_infimum_parameterConjugate_eq_adjointFiberIndicator {m n : ℕ}
    (A : ConvexProcess m n) (xStar : Fin n → ℝ) :
    convexConjugate
        (fun u : Fin m → ℝ =>
          setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar) =
      fun uStar : Fin m → ℝ =>
        indicatorEReal (setValuedAdjointVecInf A.toSetValued xStar) uStar := by
  funext uStar
  let g : (Fin m → ℝ) → EReal :=
    fun u : Fin m → ℝ =>
      setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar
  -- Step 1: unfold the convex conjugate to the raw supremum of affine offsets.
  rw [convexConjugate, fenchelConjugate_eq_iSup]
  let φ : (Fin m → ℝ) → EReal :=
    fun u : Fin m → ℝ => (((finDot u uStar : ℝ) : EReal)) + (-g u)
  change iSup φ = indicatorEReal (setValuedAdjointVecInf A.toSetValued xStar) uStar
  by_cases hu : uStar ∈ setValuedAdjointVecInf A.toSetValued xStar
  · -- Step 2: on the adjoint fiber, every affine offset is nonpositive and the origin attains `0`.
    have hMinorant :
        ∀ u : Fin m → ℝ, (((finDot u uStar : ℝ) : EReal)) ≤ g u := by
      simpa [g] using
        (helperForTheorem_39_3_infimum_adjointFiber_mem_iff_parameter_minorant A xStar uStar).1 hu
    have hPhiNonpos : ∀ u : Fin m → ℝ, φ u ≤ (0 : EReal) := by
      intro u
      have hSub :
          (((finDot u uStar : ℝ) : EReal)) - g u ≤ (0 : EReal) :=
        EReal.sub_nonpos.2 (hMinorant u)
      simpa [φ, sub_eq_add_neg] using hSub
    have hSectionZero : g 0 = 0 := by
      have hLower : (0 : EReal) ≤ g 0 := by
        simpa [g, finDot] using hMinorant (0 : Fin m → ℝ)
      have hUpper : g 0 ≤ 0 := by
        unfold g setBracketVec
        exact sInf_le ⟨0, A.zero_mem, by simp [finDot]⟩
      exact le_antisymm hUpper hLower
    have hZeroLeSup : (0 : EReal) ≤ iSup φ := by
      have hEval : (0 : EReal) ≤ φ 0 := by
        simp [φ, hSectionZero, finDot]
      exact le_trans hEval (le_iSup φ 0)
    have hSupLeZero : iSup φ ≤ 0 := by
      exact iSup_le hPhiNonpos
    have hSupEq : iSup φ = 0 := le_antisymm hSupLeZero hZeroLeSup
    simp [indicatorEReal, hu, hSupEq]
  · -- Step 3: off the adjoint fiber, a violating direction drives the supremum to `⊤`.
    have hNotMinorant :
        ¬ ∀ u : Fin m → ℝ, (((finDot u uStar : ℝ) : EReal)) ≤ g u := by
      intro hMinorant
      exact hu <|
        (helperForTheorem_39_3_infimum_adjointFiber_mem_iff_parameter_minorant A xStar uStar).2
          (by simpa [g] using hMinorant)
    push_neg at hNotMinorant
    rcases hNotMinorant with ⟨u0, hNotLe⟩
    have hViol : g u0 < (((finDot u0 uStar : ℝ) : EReal)) := hNotLe
    have hSupTop : iSup φ = ⊤ := by
      apply (EReal.eq_top_iff_forall_lt (iSup φ)).2
      intro μ
      by_cases hBot : g u0 = ⊥
      · have hEval : φ u0 = ⊤ := by
          simp [φ, hBot]
        have hTop : (μ : EReal) < φ u0 := by simpa [hEval]
        exact lt_of_lt_of_le hTop (le_iSup φ u0)
      · have hNotTop : g u0 ≠ ⊤ := by
          intro hTop
          have : (⊤ : EReal) < (((finDot u0 uStar : ℝ) : EReal)) := by
            simpa [hTop] using hViol
          simpa using this
        let r : ℝ := (g u0).toReal
        have hgEq : g u0 = (r : EReal) := by
          have hcoe : (((g u0).toReal : ℝ) : EReal) = g u0 :=
            EReal.coe_toReal hNotTop hBot
          simpa [r] using hcoe.symm
        have hViolReal : r < finDot u0 uStar := by
          have : ((r : ℝ) : EReal) < (((finDot u0 uStar : ℝ) : EReal)) := by
            simpa [hgEq] using hViol
          exact_mod_cast this
        let c : ℝ := finDot u0 uStar - r
        have hcPos : 0 < c := by
          dsimp [c]
          linarith
        let t : ℝ := |μ| / c + 1
        have ht : 0 < t := by
          have hdiv : 0 ≤ |μ| / c := by
            exact div_nonneg (abs_nonneg μ) (le_of_lt hcPos)
          dsimp [t]
          linarith
        have hScale :
            φ (t • u0) = (((t * c : ℝ) : EReal)) := by
          have hSectionScale :
              g (t • u0) = (t : EReal) * g u0 :=
            helperForTheorem_39_3_parameterSection_posHomogeneous
              ConvexSetOrientation.infimum A xStar u0 t ht
          have hDotScale :
              (((finDot (t • u0) uStar : ℝ) : EReal)) =
                (((t * finDot u0 uStar : ℝ) : EReal)) := by
            simp [finDot, smul_dotProduct, mul_comm]
          simp [φ, hDotScale, hSectionScale, hgEq, c, sub_eq_add_neg, mul_add, add_mul, mul_assoc,
            mul_comm, mul_left_comm]
        have htc : μ < t * c := by
          have hcNe : c ≠ 0 := by linarith
          have hcalc : t * c = |μ| + c := by
            calc
              t * c = (|μ| / c + 1) * c := by rfl
              _ = |μ| / c * c + c := by ring
              _ = |μ| + c := by
                    field_simp [hcNe]
          have hμLeAbs : μ ≤ |μ| := le_abs_self μ
          rw [hcalc]
          linarith
        have hltEval : (μ : EReal) < φ (t • u0) := by
          rw [hScale]
          exact_mod_cast htc
        exact lt_of_lt_of_le hltEval (le_iSup φ (t • u0))
    simp [indicatorEReal, hu, hSupTop]

/-- Helper for Theorem 39.3: the infimum-oriented bracket of a set is the concave conjugate of
its negative indicator. -/
lemma helperForTheorem_39_3_infimumBracket_eq_concaveConjugate_negIndicator {k : ℕ}
    (S : Set (Fin k → ℝ)) (u : Fin k → ℝ) :
    setBracketVec ConvexSetOrientation.infimum S u =
      concaveConjugate (fun uStar => negIndicatorEReal S uStar) u := by
  -- Step 1: unfold the concave conjugate to the indexed infimum over all candidate covectors.
  rw [helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
  unfold setBracketVec
  let φ : (Fin k → ℝ) → EReal :=
    fun v => (((finDot v u : ℝ) : EReal)) + (-negIndicatorEReal S v)
  -- Step 2: compare the indexed infimum with the set infimum by separating the `uStar ∈ S`
  -- and `uStar ∉ S` branches of the negative indicator.
  apply le_antisymm
  · refine le_iInf ?_
    intro v
    by_cases hv : v ∈ S
    · have hEval :
          sInf ((fun x : Fin k → ℝ => (((finDot x u : ℝ) : EReal))) '' S) ≤
            (((finDot v u : ℝ) : EReal)) := by
        exact sInf_le ⟨v, hv, rfl⟩
      simpa [φ, negIndicatorEReal, hv] using hEval
    · simp [φ, negIndicatorEReal, hv]
  · refine le_sInf ?_
    rintro r ⟨v, hv, rfl⟩
    have hEval : iInf φ ≤ φ v := iInf_le φ v
    simpa [φ, negIndicatorEReal, hv] using hEval

/-- Helper for Theorem 39.3: the supremum-oriented bracket of a set is the convex conjugate of
its indicator. -/
lemma helperForTheorem_39_3_supremumBracket_eq_convexConjugate_indicator {k : ℕ}
    (S : Set (Fin k → ℝ)) (u : Fin k → ℝ) :
    setBracketVec ConvexSetOrientation.supremum S u =
      convexConjugate (fun uStar => indicatorEReal S uStar) u := by
  -- Step 1: unfold the convex conjugate to the indexed supremum over all candidate covectors.
  rw [convexConjugate, fenchelConjugate_eq_iSup]
  unfold setBracketVec
  let φ : (Fin k → ℝ) → EReal :=
    fun v => (((finDot v u : ℝ) : EReal)) + (-indicatorEReal S v)
  -- Step 2: points outside `S` contribute `⊥`, so the indexed supremum reduces to the genuine
  -- support supremum over `S`.
  apply le_antisymm
  · refine sSup_le ?_
    rintro r ⟨v, hv, rfl⟩
    have hEval : φ v ≤ iSup φ := le_iSup φ v
    simpa [φ, indicatorEReal, hv] using hEval
  · refine iSup_le ?_
    intro v
    by_cases hv : v ∈ S
    · have hEval :
          (((finDot v u : ℝ) : EReal)) ≤
            sSup ((fun x : Fin k → ℝ => (((finDot x u : ℝ) : EReal))) '' S) := by
        exact le_sSup ⟨v, hv, rfl⟩
      simpa [φ, indicatorEReal, hv] using hEval
    · simp [φ, indicatorEReal, hv]

/-- Helper for Theorem 39.3: the genuine adjoint-fiber bracket is exactly the second conjugate of
the primal parameter section. This is the Chapter 30 normalization step behind the closure
identity. -/
lemma helperForTheorem_39_3_actualAdjointBracket_eq_parameterBiconjugate {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    setBracketVec o.opposite ((adjointVecOriented o A).toSetValued xStar) u =
      match o with
      | .supremum =>
          concaveConjugate
            (concaveConjugate
              (fun u' : Fin m → ℝ =>
                setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar)) u
      | .infimum =>
          convexConjugate
            (convexConjugate
              (fun u' : Fin m → ℝ =>
                setBracketVec ConvexSetOrientation.infimum (A.toSetValued u') xStar)) u := by
  -- Step 1: normalize the actual adjoint-fiber bracket to the conjugate of the corresponding
  -- adjoint-fiber indicator, then rewrite that indicator by the already-proved parameter
  -- conjugacy formulas.
  cases o
  · calc
      setBracketVec ConvexSetOrientation.infimum (setValuedAdjointVec A.toSetValued xStar) u =
          concaveConjugate
            (fun uStar : Fin m → ℝ =>
              negIndicatorEReal (setValuedAdjointVec A.toSetValued xStar) uStar) u :=
            helperForTheorem_39_3_infimumBracket_eq_concaveConjugate_negIndicator
              (S := setValuedAdjointVec A.toSetValued xStar) u
      _ =
          concaveConjugate
            (concaveConjugate
              (fun u' : Fin m → ℝ =>
                setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar)) u := by
            rw [← helperForTheorem_39_3_supremum_parameterConjugate_eq_adjointFiberIndicator
              (A := A) (xStar := xStar)]
  · calc
      setBracketVec ConvexSetOrientation.supremum (setValuedAdjointVecInf A.toSetValued xStar) u =
          convexConjugate
            (fun uStar : Fin m → ℝ =>
              indicatorEReal (setValuedAdjointVecInf A.toSetValued xStar) uStar) u :=
            helperForTheorem_39_3_supremumBracket_eq_convexConjugate_indicator
              (S := setValuedAdjointVecInf A.toSetValued xStar) u
      _ =
          convexConjugate
            (convexConjugate
              (fun u' : Fin m → ℝ =>
                setBracketVec ConvexSetOrientation.infimum (A.toSetValued u') xStar)) u := by
            rw [← helperForTheorem_39_3_infimum_parameterConjugate_eq_adjointFiberIndicator
              (A := A) (xStar := xStar)]

/-- Helper for Theorem 39.3: the Section 33 raw convex closure is exactly the local epigraph
closure operator used for Theorem 39.3. -/
lemma helperForTheorem_39_3_functionConvexClosure_eq_eRealLowerClosure {k : ℕ}
    (f : (Fin k → ℝ) → EReal) :
    functionConvexClosure f = eRealLowerClosure f := by
  -- Step 1: identify the Section 33 ball formula with the ordinary lower semicontinuous hull.
  have hHullSpec := Classical.choose_spec (exists_lowerSemicontinuousHull (n := k) f)
  have hHullLsc : LowerSemicontinuous (lowerSemicontinuousHull f) := by
    simpa [lowerSemicontinuousHull] using hHullSpec.1
  have hHullLe : lowerSemicontinuousHull f ≤ f := by
    simpa [lowerSemicontinuousHull] using hHullSpec.2.1
  have hRawEqHull : functionConvexClosure f = lowerSemicontinuousHull f := by
    apply le_antisymm
    · intro x
      have hRawLsc : LowerSemicontinuous (functionConvexClosure f) := by
        simpa [functionConvexClosure] using
          helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := f)
      have hRawLe : functionConvexClosure f ≤ f := by
        intro y
        exact helperForLemma33_0_5_functionConvexClosure_raw_le_self (f := f) y
      exact
        (show functionConvexClosure f x ≤ lowerSemicontinuousHull f x from by
          simpa [lowerSemicontinuousHull] using
            hHullSpec.2.2 (functionConvexClosure f) hRawLsc hRawLe x)
    · intro x
      exact
        helperForTheorem33_1_lowerSemicontinuous_le_functionConvexClosure
          (f := f) (h := lowerSemicontinuousHull f) hHullLsc hHullLe x
  -- Step 2: rewrite the local epigraph closure as Chapter 2's `epigraphClosureInf`.
  have hEpigraphEq :
      epigraph (S := (Set.univ : Set (Fin k → ℝ))) f = eRealEpigraph f := by
    ext p
    constructor
    · intro hp
      exact hp.2
    · intro hp
      exact ⟨by trivial, hp⟩
  have hEpiInfEq : epigraphClosureInf f = eRealLowerClosure f := by
    funext x
    simp [epigraphClosureInf, eRealLowerClosure, hEpigraphEq]
  -- Step 3: the Chapter 2 epigraph hull is also characterized as the lower semicontinuous hull.
  have hEpiClosure :
      epigraph (S := (Set.univ : Set (Fin k → ℝ))) (epigraphClosureInf f) =
        closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) f) := by
    simpa using (closure_epigraph_eq_epigraph_sInf (f := f))
  have hEpiLsc : LowerSemicontinuous (epigraphClosureInf f) := by
    -- Closedness of the epigraph is exactly lower semicontinuity.
    have hClosedEpigraph :
        _root_.IsClosed (epigraph (S := (Set.univ : Set (Fin k → ℝ))) (epigraphClosureInf f)) := by
      simpa [hEpiClosure] using isClosed_closure
    have hClosedSublevel :
        ∀ α : ℝ, _root_.IsClosed {x | epigraphClosureInf f x ≤ (α : EReal)} :=
      closed_sublevel_of_closed_epigraph (f := epigraphClosureInf f) hClosedEpigraph
    exact (lowerSemicontinuous_iff_closed_sublevel (f := epigraphClosureInf f)).2 hClosedSublevel
  have hEpiLe : epigraphClosureInf f ≤ f := by
    intro x
    by_cases htop : f x = (⊤ : EReal)
    · simp [epigraphClosureInf, htop]
    by_cases hbot : f x = (⊥ : EReal)
    · have hHullBot : epigraphClosureInf f x = (⊥ : EReal) := by
        apply (EReal.eq_bot_iff_forall_lt (x := epigraphClosureInf f x)).2
        intro μ
        have hleAll : ∀ r : ℝ, epigraphClosureInf f x ≤ (r : EReal) := by
          intro r
          have hxEpigraph :
              (x, r) ∈ epigraph (S := (Set.univ : Set (Fin k → ℝ))) f := by
            exact (mem_epigraph_univ_iff (f := f)).2 (by simp [hbot])
          have hxMem :
              (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) f) :=
            subset_closure hxEpigraph
          have hmem :
              ((r : ℝ) : EReal) ∈
                (fun t : ℝ => (t : EReal)) '' {t : ℝ |
                  (x, t) ∈ closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) f)} :=
            ⟨r, hxMem, rfl⟩
          exact sInf_le hmem
        have hlt : (((μ - 1 : ℝ)) : EReal) < (μ : EReal) := by
          exact_mod_cast (show μ - 1 < μ by linarith)
        exact lt_of_le_of_lt (hleAll (μ - 1)) hlt
      simp [hbot, hHullBot]
    · have hxMem :
        (x, (f x).toReal) ∈
          closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) f) := by
        have hleToReal : f x ≤ (f x).toReal := EReal.le_coe_toReal htop
        have hxEpigraph :
            (x, (f x).toReal) ∈ epigraph (S := (Set.univ : Set (Fin k → ℝ))) f :=
          (mem_epigraph_univ_iff (f := f)).2 hleToReal
        exact subset_closure hxEpigraph
      have hleToReal :
          epigraphClosureInf f x ≤ (f x).toReal := by
        have hmem :
            (((f x).toReal : ℝ) : EReal) ∈
              (fun t : ℝ => (t : EReal)) '' {t : ℝ |
                (x, t) ∈ closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) f)} :=
          ⟨(f x).toReal, hxMem, rfl⟩
        exact sInf_le hmem
      have hcoe : (((f x).toReal : ℝ) : EReal) = f x := EReal.coe_toReal htop hbot
      simpa [hcoe] using hleToReal
  have hEpiEqHull : epigraphClosureInf f = lowerSemicontinuousHull f := by
    apply le_antisymm
    · intro x
      exact
        (show epigraphClosureInf f x ≤ lowerSemicontinuousHull f x from by
          simpa [lowerSemicontinuousHull] using
            hHullSpec.2.2 (epigraphClosureInf f) hEpiLsc hEpiLe x)
    · have hClosureSubset :
          closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) f) ⊆
            epigraph (S := (Set.univ : Set (Fin k → ℝ))) (lowerSemicontinuousHull f) :=
        closure_epigraph_subset_epigraph_of_lsc_le
          (f := f) (g := lowerSemicontinuousHull f) hHullLsc hHullLe
      have hSubset :
          epigraph (S := (Set.univ : Set (Fin k → ℝ))) (epigraphClosureInf f) ⊆
            epigraph (S := (Set.univ : Set (Fin k → ℝ))) (lowerSemicontinuousHull f) := by
        simpa [hEpiClosure] using hClosureSubset
      intro x
      by_cases htop : epigraphClosureInf f x = (⊤ : EReal)
      · simp [htop]
      by_cases hbot : epigraphClosureInf f x = (⊥ : EReal)
      · have hforall : ∀ μ : ℝ, lowerSemicontinuousHull f x ≤ (μ : EReal) := by
          intro μ
          have hxEpigraph :
              (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin k → ℝ))) (epigraphClosureInf f) := by
            exact (mem_epigraph_univ_iff (f := epigraphClosureInf f)).2 (by simp [hbot])
          exact (mem_epigraph_univ_iff (f := lowerSemicontinuousHull f)).1 (hSubset hxEpigraph)
        have hbot' : lowerSemicontinuousHull f x = (⊥ : EReal) := by
          apply (EReal.eq_bot_iff_forall_lt (x := lowerSemicontinuousHull f x)).2
          intro μ
          have hlt : (((μ - 1 : ℝ)) : EReal) < (μ : EReal) := by
            exact_mod_cast (show μ - 1 < μ by linarith)
          exact lt_of_le_of_lt (hforall (μ - 1)) hlt
        simp [hbot, hbot']
      · have hxEpigraph :
          (x, (epigraphClosureInf f x).toReal) ∈
            epigraph (S := (Set.univ : Set (Fin k → ℝ))) (epigraphClosureInf f) := by
          exact
            (mem_epigraph_univ_iff (f := epigraphClosureInf f)).2
              (EReal.le_coe_toReal htop)
        have hleToReal :
            lowerSemicontinuousHull f x ≤ (epigraphClosureInf f x).toReal := by
          exact (mem_epigraph_univ_iff (f := lowerSemicontinuousHull f)).1 (hSubset hxEpigraph)
        have hcoe :
            (((epigraphClosureInf f x).toReal : ℝ) : EReal) = epigraphClosureInf f x :=
          EReal.coe_toReal htop hbot
        simpa [lowerSemicontinuousHull, hcoe] using hleToReal
  calc
    functionConvexClosure f = lowerSemicontinuousHull f := hRawEqHull
    _ = epigraphClosureInf f := hEpiEqHull.symm
    _ = eRealLowerClosure f := hEpiInfEq


end ConvexProcess
end Section39
end Chap08
