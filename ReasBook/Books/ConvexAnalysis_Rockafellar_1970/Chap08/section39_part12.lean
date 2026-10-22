/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part11

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Chap08
section Section39

namespace ConvexProcess

/-- Helper for Theorem 39.5: the infimum-oriented bracket of a Minkowski sum also splits into the
sum of the two infimum-oriented brackets once the pointwise extended-real sum avoids the
indeterminate `⊤ + ⊥` case. -/
lemma helperForTheorem_39_5_infimumBracket_add {n : ℕ}
    (S T : Set (Fin n → ℝ))
    (hNoIndet :
      ∀ xStar,
        (¬ (setBracketVec ConvexSetOrientation.infimum S xStar = ⊤ ∧
            setBracketVec ConvexSetOrientation.infimum T xStar = ⊥)) ∧
        (¬ (setBracketVec ConvexSetOrientation.infimum S xStar = ⊥ ∧
            setBracketVec ConvexSetOrientation.infimum T xStar = ⊤))) :
    setBracketVec ConvexSetOrientation.infimum (S + T) =
      fun xStar => setBracketVec ConvexSetOrientation.infimum S xStar +
        setBracketVec ConvexSetOrientation.infimum T xStar := by
  funext xStar
  -- Step 1: convert each infimum bracket into the negative support function of the negated fiber.
  rw [helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber,
    helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber,
    helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber]
  have hNegPreimageAdd :
      (Neg.neg ⁻¹' (S + T)) = (Neg.neg ⁻¹' S) + (Neg.neg ⁻¹' T) := by
    -- Step 2: negation transports the Minkowski sum fiberwise.
    ext x
    constructor
    · intro hx
      have hx' : -x ∈ S + T := hx
      rcases Set.mem_add.1 hx' with ⟨s, hs, t, ht, hst⟩
      have hsNeg : -s ∈ Neg.neg ⁻¹' S := by
        simpa
      have htNeg : -t ∈ Neg.neg ⁻¹' T := by
        simpa
      refine Set.mem_add.2 ⟨-s, hsNeg, -t, htNeg, ?_⟩
      simpa [neg_add, add_comm, add_left_comm, add_assoc] using congrArg Neg.neg hst
    · intro hx
      rcases Set.mem_add.1 hx with ⟨s, hs, t, ht, hst⟩
      have hs' : -s ∈ S := by
        simpa using hs
      have ht' : -t ∈ T := by
        simpa using ht
      have hsum : (-s) + (-t) = -x := by
        simpa [neg_add, add_comm, add_left_comm, add_assoc] using congrArg Neg.neg hst
      exact Set.mem_add.2 ⟨-s, hs', -t, ht', hsum⟩
  -- Step 3: apply the already-proved support-function splitting to the negated fibers.
  rw [hNegPreimageAdd, helperForTheorem_39_5_supportFunctionEReal_add]
  have hLeft :
      supportFunctionEReal (-S) xStar ≠ ⊥ ∨ supportFunctionEReal (-T) xStar ≠ ⊤ := by
    -- Step 4: exclude the first exceptional support-function configuration by translating it back
    -- to the bracket values ruled out by hypothesis.
    by_cases hSbot : supportFunctionEReal (-S) xStar = ⊥
    · right
      intro hTtop
      have hBracketS : setBracketVec ConvexSetOrientation.infimum S xStar = ⊤ := by
        rw [helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber]
        simp [hSbot]
      have hBracketT : setBracketVec ConvexSetOrientation.infimum T xStar = ⊥ := by
        rw [helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber]
        simp [hTtop]
      exact (hNoIndet xStar).1 ⟨hBracketS, hBracketT⟩
    · exact Or.inl hSbot
  have hRight :
      supportFunctionEReal (-S) xStar ≠ ⊤ ∨ supportFunctionEReal (-T) xStar ≠ ⊥ := by
    -- Step 5: exclude the second exceptional support-function configuration in the same way.
    by_cases hStop : supportFunctionEReal (-S) xStar = ⊤
    · right
      intro hTbot
      have hBracketS : setBracketVec ConvexSetOrientation.infimum S xStar = ⊥ := by
        rw [helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber]
        simp [hStop]
      have hBracketT : setBracketVec ConvexSetOrientation.infimum T xStar = ⊤ := by
        rw [helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber]
        simp [hTbot]
      exact (hNoIndet xStar).2 ⟨hBracketS, hBracketT⟩
    · exact Or.inl hStop
  -- Step 6: with the exceptional cases ruled out, `EReal` negation distributes over the sum.
  simpa [sub_eq_add_neg] using EReal.neg_add hLeft hRight

/-- Helper for Theorem 39.5: every fiber bracket of `A₁ + A₂` is the sum of the corresponding
fiber brackets of `A₁` and `A₂`, provided the infimum branch avoids indeterminate `EReal`
sums. -/
lemma helperForTheorem_39_5_bracket_addProcess_eq_sum {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n) (u : Fin m → ℝ)
    (hNoIndet :
      ∀ xStar,
        (¬ (setBracketVec ConvexSetOrientation.infimum (A₁.toSetValued u) xStar = ⊤ ∧
            setBracketVec ConvexSetOrientation.infimum (A₂.toSetValued u) xStar = ⊥)) ∧
        (¬ (setBracketVec ConvexSetOrientation.infimum (A₁.toSetValued u) xStar = ⊥ ∧
            setBracketVec ConvexSetOrientation.infimum (A₂.toSetValued u) xStar = ⊤))) :
    setBracketVec o ((addProcess A₁ A₂).toSetValued u) =
      fun xStar =>
        setBracketVec o (A₁.toSetValued u) xStar + setBracketVec o (A₂.toSetValued u) xStar := by
  have hAddProcess :
      (addProcess A₁ A₂).toSetValued = addSetValued A₁ A₂ :=
    helperForTheorem_39_5_addProcess_toSetValued A₁ A₂
  -- Step 1: after rewriting the chosen sum process to the actual Minkowski sum, split the two
  -- orientations into the corresponding support/inf-support identities.
  cases o
  · simpa [hAddProcess, addSetValued, helperForTheorem_39_3_supremumBracket_eq_supportFunctionEReal]
      using
      helperForTheorem_39_5_supportFunctionEReal_add (A₁.toSetValued u) (A₂.toSetValued u)
  · simpa [hAddProcess, addSetValued] using
      helperForTheorem_39_5_infimumBracket_add (A₁.toSetValued u) (A₂.toSetValued u) hNoIndet

/-- Helper for Theorem 39.5: once the appropriate oriented bracket agrees on each dual fiber, the
target adjoint fiber is exactly the closure of the raw Minkowski-sum fiber. -/
lemma helperForTheorem_39_5_pointwiseFiberClosure_of_orientedAdjointBracketEq {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n)
    (hBracketEq :
      ∀ xStar,
        setBracketVec o.opposite
          (((adjointVecOriented o A₁).toSetValued xStar) +
            ((adjointVecOriented o A₂).toSetValued xStar)) =
          setBracketVec o.opposite
            ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued xStar)) :
    ∀ xStar,
      closure
        (((adjointVecOriented o A₁).toSetValued xStar) +
          ((adjointVecOriented o A₂).toSetValued xStar)) =
        (adjointVecOriented o (addProcess A₁ A₂)).toSetValued xStar := by
  intro xStar
  let S :
      Set (Fin m → ℝ) :=
    ((adjointVecOriented o A₁).toSetValued xStar) +
      ((adjointVecOriented o A₂).toSetValued xStar)
  let T :
      Set (Fin m → ℝ) :=
    (adjointVecOriented o (addProcess A₁ A₂)).toSetValued xStar
  have hFiberA₁ :
      _root_.IsClosed ((adjointVecOriented o A₁).toSetValued xStar) ∧
        Convex ℝ ((adjointVecOriented o A₁).toSetValued xStar) :=
    helperForTheorem_39_5_adjointVecOriented_fiber_closed_convex o A₁ xStar
  have hFiberA₂ :
      _root_.IsClosed ((adjointVecOriented o A₂).toSetValued xStar) ∧
        Convex ℝ ((adjointVecOriented o A₂).toSetValued xStar) :=
    helperForTheorem_39_5_adjointVecOriented_fiber_closed_convex o A₂ xStar
  have hTClosedConv :
      _root_.IsClosed T ∧ Convex ℝ T := by
    simpa [T] using
      helperForTheorem_39_5_adjointVecOriented_fiber_closed_convex
        o (addProcess A₁ A₂) xStar
  have hSConv : Convex ℝ S := by
    -- Step 1: convexity of the raw fiber sum comes from convexity of the two adjoint fibers.
    simpa [S] using hFiberA₁.2.add hFiberA₂.2
  cases o
  · -- Step 2: in the supremum branch the opposite bracket is the infimum bracket, so the
    -- pointwise closed-convex reconstruction lemma applies directly.
    simpa [S, T] using
      helperForTheorem_39_5_closure_eq_of_infimumBracketEq
        S T hSConv hTClosedConv.1 hTClosedConv.2 (hBracketEq xStar)
  · -- Step 3: in the infimum branch the opposite bracket is the support function, so rewrite to
    -- support-function equality before invoking the same reconstruction principle.
    have hSupportEq : supportFunctionEReal S = supportFunctionEReal T := by
      simpa [S, T, ConvexSetOrientation.opposite,
        helperForTheorem_39_3_supremumBracket_eq_supportFunctionEReal] using
        hBracketEq xStar
    exact
      helperForTheorem_39_5_closure_eq_of_supportFunctionEq
        S T hSConv hTClosedConv.1 hTClosedConv.2 hSupportEq

/-- Helper for Theorem 39.5: the graph-closure formula follows once the oriented adjoint brackets
agree fiberwise, because the previous lemma identifies every target fiber with the closure of the
raw Minkowski-sum fiber. -/
lemma helperForTheorem_39_5_graphClosure_eq_of_orientedAdjointBracketEq {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n)
    (hBracketEq :
      ∀ xStar,
        setBracketVec o.opposite
          (((adjointVecOriented o A₁).toSetValued xStar) +
            ((adjointVecOriented o A₂).toSetValued xStar)) =
          setBracketVec o.opposite
            ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued xStar)) :
    setValuedGraph ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued) =
      closure
        (setValuedGraph fun xStar =>
          (adjointVecOriented o A₁).toSetValued xStar +
            (adjointVecOriented o A₂).toSetValued xStar) := by
  have hGraphClosed :
      _root_.IsClosed
        (setValuedGraph' ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued)) := by
    -- Step 1: the target adjoint graph is already known to be closed.
    simpa [setValuedGraph', setValuedGraph] using
      helperForTheorem_39_5_adjointAddProcess_graphClosed o A₁ A₂
  -- Step 2: combine graph closedness with the new pointwise fiber-closure reconstruction.
  simpa [setValuedGraph', setValuedGraph] using
    helperForTheorem_39_5_setValuedGraph_eq_closure_of_pointwiseFiberClosure
      (A := fun xStar =>
        (adjointVecOriented o A₁).toSetValued xStar +
          (adjointVecOriented o A₂).toSetValued xStar)
      (B := (adjointVecOriented o (addProcess A₁ A₂)).toSetValued)
      hGraphClosed
      (helperForTheorem_39_5_pointwiseFiberClosure_of_orientedAdjointBracketEq
        o A₁ A₂ hBracketEq)

/-- Helper for Theorem 39.5: once the supremum-oriented exact adjoint-sum formula is known, the
infimum-oriented formula follows by negating both dual variables. -/
lemma helperForTheorem_39_5_infimum_exact_processMap_identification_of_supremum {m n : ℕ}
    (A₁ A₂ : ConvexProcess m n)
    (hSup :
      (adjointVecOriented ConvexSetOrientation.supremum (addProcess A₁ A₂)).toSetValued =
        fun xStar =>
          (adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar +
            (adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar) :
    (adjointVecOriented ConvexSetOrientation.infimum (addProcess A₁ A₂)).toSetValued =
      fun xStar =>
        (adjointVecOriented ConvexSetOrientation.infimum A₁).toSetValued xStar +
          (adjointVecOriented ConvexSetOrientation.infimum A₂).toSetValued xStar := by
  funext xStar
  apply Set.Subset.antisymm
  · intro uStar huStar
    -- Step 1: negate the infimum membership and invoke the known supremum formula at `-xStar`.
    have hNeg :
        -uStar ∈
          (adjointVecOriented ConvexSetOrientation.supremum
            (addProcess A₁ A₂)).toSetValued (-xStar) :=
      (helperForTheorem_39_5_infimumMembership_iff_supremumMembership_neg
        (addProcess A₁ A₂) xStar uStar).1 huStar
    have hSupNeg :
        (adjointVecOriented ConvexSetOrientation.supremum
          (addProcess A₁ A₂)).toSetValued (-xStar) =
          (adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued (-xStar) +
            (adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued (-xStar) :=
      congrFun hSup (-xStar)
    rw [hSupNeg] at hNeg
    rcases Set.mem_add.1 hNeg with ⟨uStar₁, huStar₁, uStar₂, huStar₂, hSum⟩
    have huStar₁Inf :
        -uStar₁ ∈ (adjointVecOriented ConvexSetOrientation.infimum A₁).toSetValued xStar :=
      (helperForTheorem_39_5_infimumMembership_iff_supremumMembership_neg
        A₁ xStar (-uStar₁)).2 (by simpa using huStar₁)
    have huStar₂Inf :
        -uStar₂ ∈ (adjointVecOriented ConvexSetOrientation.infimum A₂).toSetValued xStar :=
      (helperForTheorem_39_5_infimumMembership_iff_supremumMembership_neg
        A₂ xStar (-uStar₂)).2 (by simpa using huStar₂)
    have hSumInf : (-uStar₁) + (-uStar₂) = uStar := by
      simpa [add_comm, add_left_comm, add_assoc] using congrArg Neg.neg hSum
    exact Set.mem_add.2 ⟨-uStar₁, huStar₁Inf, -uStar₂, huStar₂Inf, hSumInf⟩
  · intro uStar huStar
    rcases Set.mem_add.1 huStar with ⟨uStar₁, huStar₁, uStar₂, huStar₂, hSum⟩
    -- Step 2: negate a Minkowski decomposition in the infimum fibers and transport it back to
    -- the supremum branch at `-xStar`.
    have huStar₁Sup :
        -uStar₁ ∈ (adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued (-xStar) :=
      (helperForTheorem_39_5_infimumMembership_iff_supremumMembership_neg
        A₁ xStar uStar₁).1 huStar₁
    have huStar₂Sup :
        -uStar₂ ∈ (adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued (-xStar) :=
      (helperForTheorem_39_5_infimumMembership_iff_supremumMembership_neg
        A₂ xStar uStar₂).1 huStar₂
    have hSumSup : (-uStar₁) + (-uStar₂) = -uStar := by
      simpa [add_comm, add_left_comm, add_assoc] using congrArg Neg.neg hSum
    have hNeg :
        -uStar ∈
          (adjointVecOriented ConvexSetOrientation.supremum
            (addProcess A₁ A₂)).toSetValued (-xStar) := by
      rw [hSup]
      exact Set.mem_add.2 ⟨-uStar₁, huStar₁Sup, -uStar₂, huStar₂Sup, hSumSup⟩
    exact
      (helperForTheorem_39_5_infimumMembership_iff_supremumMembership_neg
        (addProcess A₁ A₂) xStar uStar).2 hNeg

/-- Helper for Theorem 39.5: if each raw supremum-adjoint fiber sum is already closed and has the
same infimum-oriented bracket as the target fiber, then the exact supremum-oriented adjoint-sum
formula follows fiberwise. -/
lemma helperForTheorem_39_5_supremum_exact_processMap_identification_of_fiberClosed_and_infimumBracketEq
    {m n : ℕ} (A₁ A₂ : ConvexProcess m n)
    (hFiberClosed :
      ∀ xStar,
        _root_.IsClosed
          (((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar) +
            ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar)))
    (hBracketEq :
      ∀ xStar,
        setBracketVec ConvexSetOrientation.infimum
          (((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar) +
            ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar)) =
          setBracketVec ConvexSetOrientation.infimum
            ((adjointVecOriented ConvexSetOrientation.supremum
              (addProcess A₁ A₂)).toSetValued xStar)) :
    (adjointVecOriented ConvexSetOrientation.supremum (addProcess A₁ A₂)).toSetValued =
      fun xStar =>
        (adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar +
          (adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar := by
  funext xStar
  let S :
      Set (Fin m → ℝ) :=
    ((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar) +
      ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar)
  let T :
      Set (Fin m → ℝ) :=
    (adjointVecOriented ConvexSetOrientation.supremum (addProcess A₁ A₂)).toSetValued xStar
  have hFiberA₁ :
      _root_.IsClosed ((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar) ∧
        Convex ℝ ((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar) :=
    helperForTheorem_39_5_adjointVecOriented_fiber_closed_convex
      ConvexSetOrientation.supremum A₁ xStar
  have hFiberA₂ :
      _root_.IsClosed ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar) ∧
        Convex ℝ ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar) :=
    helperForTheorem_39_5_adjointVecOriented_fiber_closed_convex
      ConvexSetOrientation.supremum A₂ xStar
  have hTClosedConv :
      _root_.IsClosed T ∧ Convex ℝ T := by
    simpa [T] using
      helperForTheorem_39_5_adjointVecOriented_fiber_closed_convex
        ConvexSetOrientation.supremum (addProcess A₁ A₂) xStar
  have hSConv : Convex ℝ S := by
    -- Step 1: convexity of the raw fiber sum comes from convexity of the two summand fibers.
    simpa [S] using hFiberA₁.2.add hFiberA₂.2
  have hEq : S = T := by
    -- Step 2: once both sides are closed and convex, equality of infimum brackets fixes the fiber.
    exact
      helperForTheorem_39_5_fiber_eq_of_infimumBracketEq
        S T (hFiberClosed xStar) hSConv hTClosedConv.1 hTClosedConv.2 (hBracketEq xStar)
  -- Step 3: rewrite the named fibers back to the original pointwise adjoint formula.
  simpa [S, T] using hEq.symm

/-- Helper for Theorem 39.5: the only remaining local input for the supremum branch is the
fiberwise package consisting of closedness of the raw adjoint-fiber sum together with equality of
its infimum-oriented bracket to the target fiber bracket. -/
abbrev helperForTheorem_39_5_supremumFiberTransportData {m n : ℕ}
    (A₁ A₂ : ConvexProcess m n) : Prop :=
  ∀ xStar,
    _root_.IsClosed
        (((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar) +
          ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar)) ∧
      setBracketVec ConvexSetOrientation.infimum
        (((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar) +
          ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar)) =
        setBracketVec ConvexSetOrientation.infimum
          ((adjointVecOriented ConvexSetOrientation.supremum
            (addProcess A₁ A₂)).toSetValued xStar)

/-- Helper for Theorem 39.5: the supremum-oriented exact adjoint-sum formula is equivalent to the
fiberwise closedness-plus-bracket transport package isolated above. -/
lemma helperForTheorem_39_5_supremum_exact_processMap_identification_iff_transportData
    {m n : ℕ} (A₁ A₂ : ConvexProcess m n) :
    ((adjointVecOriented ConvexSetOrientation.supremum (addProcess A₁ A₂)).toSetValued =
        fun xStar =>
          (adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar +
            (adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar) ↔
      helperForTheorem_39_5_supremumFiberTransportData A₁ A₂ := by
  constructor
  · intro hExact xStar
    let S :
        Set (Fin m → ℝ) :=
      ((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar) +
        ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar)
    let T :
        Set (Fin m → ℝ) :=
      (adjointVecOriented ConvexSetOrientation.supremum (addProcess A₁ A₂)).toSetValued xStar
    have hFiberEq : T = S := congrFun hExact xStar
    have hTClosed :
        _root_.IsClosed T := by
      -- Step 1: the target adjoint fiber is always closed by the Theorem 39.2 package.
      simpa [T] using
        (helperForTheorem_39_5_adjointVecOriented_fiber_closed_convex
          ConvexSetOrientation.supremum (addProcess A₁ A₂) xStar).1
    have hSClosed :
        _root_.IsClosed S := by
      -- Step 2: transport closedness across the exact fiber identification.
      exact hFiberEq ▸ hTClosed
    have hBracketEq :
        setBracketVec ConvexSetOrientation.infimum S =
          setBracketVec ConvexSetOrientation.infimum T := by
      -- Step 3: the infimum-oriented bracket agrees after rewriting by the same fiber identity.
      simpa [S, T] using
        congrArg (setBracketVec ConvexSetOrientation.infimum) hFiberEq.symm
    exact ⟨hSClosed, hBracketEq⟩
  · intro hTransport
    -- Step 4: the previously proved reconstruction lemma turns this package back into exact
    -- supremum-oriented fiber equality.
    exact
      helperForTheorem_39_5_supremum_exact_processMap_identification_of_fiberClosed_and_infimumBracketEq
        A₁ A₂
        (fun xStar => (hTransport xStar).1)
        (fun xStar => (hTransport xStar).2)

/-- Helper for Theorem 39.5: a point lying in `T` must also lie in `S` whenever the negative
indicator of `T` is bounded above by the negative indicator of `S` at that same point. -/
lemma helperForTheorem_39_5_mem_of_negIndicatorEReal_le {n : ℕ}
    {S T : Set (Fin n → ℝ)} {u : Fin n → ℝ}
    (huT : u ∈ T) (hLe : negIndicatorEReal T u ≤ negIndicatorEReal S u) :
    u ∈ S := by
  -- Step 1: split on whether the desired source-set membership already holds.
  by_cases huS : u ∈ S
  · exact huS
  · -- Step 2: if `u ∉ S` while `u ∈ T`, the two negative indicators collapse to `0 ≤ -∞`,
    -- contradicting the assumed order comparison.
    exfalso
    simp [negIndicatorEReal, huT, huS] at hLe

/-- The corrected vector-valued textbook adjoint specializes to the negative indicator of the
supremum-oriented adjoint fiber. -/
lemma helperForTheorem_39_5_textbookAdjoint_indicator_eq_negIndicator_supremumAdjointFiber
    {m n : ℕ} (A : ConvexProcess m n) (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction A) xStar uStar =
      negIndicatorEReal
        ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar) uStar := by
  simpa [textbookBifunctionAdjoint, bifunctionAdjoint, dotProductEquiv_apply_apply,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm, finDot, dotProduct_comm] using
      helperForTheorem_39_5_bifunctionAdjoint_indicator_eq_negIndicator_supremumAdjointFiber
        A xStar uStar

/-- Helper for Theorem 39.5: once the Chapter 38 indicator-adjoint identity has been rewritten as
negative-indicator data, every point of the supremum-oriented adjoint fiber of `A₁ + A₂` already
lies in the raw Minkowski sum of the two supremum adjoint fibers. -/
lemma helperForTheorem_39_5_adjointAddProcess_subset_adjointSum_supremum {m n : ℕ}
    (A₁ A₂ : ConvexProcess m n)
    (hIndicatorAdjoint :
      textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction (addProcess A₁ A₂)) =
        concaveBifunctionInfimalConvolutionInSecond
          (textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction A₁))
          (textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction A₂))) :
    ∀ xStar uStar,
      uStar ∈ (adjointVecOriented ConvexSetOrientation.supremum (addProcess A₁ A₂)).toSetValued xStar →
        uStar ∈
          ((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar) +
            ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar) := by
  intro xStar uStar huStar
  have hPoint := congrFun (congrFun hIndicatorAdjoint xStar) uStar
  have hRightZero :
      concaveBifunctionInfimalConvolutionInSecond
          (textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction A₁))
          (textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction A₂))
          xStar uStar = 0 := by
    rw [← hPoint,
      helperForTheorem_39_5_textbookAdjoint_indicator_eq_negIndicator_supremumAdjointFiber]
    simp [negIndicatorEReal, huStar]
  by_contra hNotMem
  have hAllBot : ∀ v : Fin m → ℝ,
      erealAddConcaveBook
          (textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction A₁)
            xStar (uStar - v))
          (textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction A₂) xStar v) = ⊥ := by
    intro v
    by_cases h₁ :
        (uStar - v) ∈
          (adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar
    · have h₂ :
          v ∉ (adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar := by
        intro hv
        exact hNotMem
          (Set.mem_add.2 ⟨uStar - v, h₁, v, hv, sub_add_cancel uStar v⟩)
      rw [helperForTheorem_39_5_textbookAdjoint_indicator_eq_negIndicator_supremumAdjointFiber,
        helperForTheorem_39_5_textbookAdjoint_indicator_eq_negIndicator_supremumAdjointFiber]
      simp [negIndicatorEReal, h₁, h₂, erealAddConcaveBook]
    · rw [helperForTheorem_39_5_textbookAdjoint_indicator_eq_negIndicator_supremumAdjointFiber,
        helperForTheorem_39_5_textbookAdjoint_indicator_eq_negIndicator_supremumAdjointFiber]
      by_cases h₂ :
          v ∈ (adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar
      · simp [negIndicatorEReal, h₁, h₂, erealAddConcaveBook]
      · simp [negIndicatorEReal, h₁, h₂, erealAddConcaveBook]
  rw [concaveBifunctionInfimalConvolutionInSecond] at hRightZero
  simp only [hAllBot, iSup_const] at hRightZero
  simp at hRightZero

/-- Helper for Theorem 39.5: the remaining exact reconstruction blocker is already concentrated in
the supremum-oriented branch. -/
lemma helperForTheorem_39_5_supremum_exact_processMap_identification {m n : ℕ}
    (A₁ A₂ : ConvexProcess m n)
    (hri : Set.Nonempty (ri A₁.dom ∩ ri A₂.dom)) :
    (adjointVecOriented ConvexSetOrientation.supremum (addProcess A₁ A₂)).toSetValued =
      fun xStar =>
    (adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar +
          (adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar := by
  have hIndicatorAdjoint :
      textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction (addProcess A₁ A₂)) =
        concaveBifunctionInfimalConvolutionInSecond
          (textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction A₁))
          (textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction A₂)) :=
    helperForTheorem_39_5_indicatorAdjoint_eq_infimalConvolutionInSecond_adjoint A₁ A₂ hri
  -- Step 1: combine the dedicated reverse-inclusion helper with the earlier forward inclusion
  -- lemma to obtain fiberwise equality.
  funext xStar
  ext uStar
  constructor
  · intro huStar
    exact
      helperForTheorem_39_5_adjointAddProcess_subset_adjointSum_supremum
        A₁ A₂ hIndicatorAdjoint xStar uStar huStar
  · -- Step 2: the forward inclusion is the direct Minkowski-sum inclusion already proved above.
    intro huSum
    exact
      helperForTheorem_39_5_adjointSum_subset_adjointAddProcess
        ConvexSetOrientation.supremum A₁ A₂ xStar huSum

/-- Helper for Theorem 39.5: exact branch packaged as a single reconstruction target for the
proof pipeline. -/
lemma helperForTheorem_39_5_infimum_exact_processMap_identification {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n)
    (hri : Set.Nonempty (ri A₁.dom ∩ ri A₂.dom)) :
    (adjointVecOriented o (addProcess A₁ A₂)).toSetValued =
      fun xStar =>
        (adjointVecOriented o A₁).toSetValued xStar + (adjointVecOriented o A₂).toSetValued xStar := by
  cases o
  · -- Step 1: the real blocker is now isolated to the supremum-oriented reconstruction.
    exact helperForTheorem_39_5_supremum_exact_processMap_identification A₁ A₂ hri
  · -- Step 2: the infimum-oriented formula is a formal negation transport of the supremum one.
    exact
      helperForTheorem_39_5_infimum_exact_processMap_identification_of_supremum A₁ A₂
        (helperForTheorem_39_5_supremum_exact_processMap_identification A₁ A₂ hri)

/-- Helper for Theorem 39.5: closed branch packaged as a single reconstructed-graph target for
the proof pipeline. -/
lemma helperForTheorem_39_5_closed_reconstructed_graph_of_processClosed_and_orientedAdjointBracketEq
    {m n : ℕ} (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n)
    (hAddClosed : (addProcess A₁ A₂).IsClosed)
    (hBracketEq :
      ∀ xStar,
        setBracketVec o.opposite
          (((adjointVecOriented o A₁).toSetValued xStar) +
            ((adjointVecOriented o A₂).toSetValued xStar)) =
          setBracketVec o.opposite
            ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued xStar)) :
    (addProcess A₁ A₂).IsClosed ∧
      setValuedGraph ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued) =
        closure
          (setValuedGraph fun xStar =>
            (adjointVecOriented o A₁).toSetValued xStar +
              (adjointVecOriented o A₂).toSetValued xStar) := by
  constructor
  · -- Step 1: keep the separately supplied closedness conclusion for the summed process.
    exact hAddClosed
  · -- Step 2: the graph component is exactly the already-proved bracket-reconstruction lemma.
    exact
      helperForTheorem_39_5_graphClosure_eq_of_orientedAdjointBracketEq
        o A₁ A₂ hBracketEq

/-- Helper for Theorem 39.5: package the oriented adjoint fibers of `A` as the auxiliary convex
process used in the closed-branch dualization argument. -/
def helperForTheorem_39_5_orientedAdjointProcess {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n) : ConvexProcess n m :=
  { toSetValued := (adjointVecOriented o A).toSetValued
    map_add_superset :=
      (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint o A).1.1
    map_smul_pos :=
      (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint o A).1.2.1
    zero_mem :=
      (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint o A).1.2.2 }

/-- Helper for Theorem 39.5: if `A` is closed, then taking the opposite-oriented adjoint of the
auxiliary adjoint process recovers the original set-valued map. -/
lemma helperForTheorem_39_5_doubleAdjoint_orientedAdjointProcess_toSetValued_eq_self
    {m n : ℕ} (o : ConvexSetOrientation) (A : ConvexProcess m n) (hA : A.IsClosed) :
    (adjointVecOriented o.opposite
      (helperForTheorem_39_5_orientedAdjointProcess o A)).toSetValued = A.toSetValued := by
  have hClosedToSetValued : (A.cl).toSetValued = A.toSetValued := by
    -- Step 1: a closed process agrees with its closure at the level of set-valued maps.
    exact congrArg ConvexProcess.toSetValued hA
  -- Step 2: the opposite-oriented adjoint of the auxiliary adjoint process is exactly the
  -- oriented double adjoint, which Theorem 39.2 identifies with the closure.
  calc
    (adjointVecOriented o.opposite
        (helperForTheorem_39_5_orientedAdjointProcess o A)).toSetValued =
        doubleAdjointVecSetValuedOriented o A := by
          cases o <;> rfl
    _ = (A.cl).toSetValued :=
      (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint o A).2.2.2.1
    _ = A.toSetValued := hClosedToSetValued

/-- Helper for Theorem 39.5: the Minkowski sum of the two auxiliary adjoint processes has
underlying set-valued map equal to the pointwise sum of the two oriented adjoint fibers. -/
lemma helperForTheorem_39_5_addProcess_orientedAdjointProcess_toSetValued
    {m n : ℕ} (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n) :
    (addProcess (helperForTheorem_39_5_orientedAdjointProcess o A₁)
      (helperForTheorem_39_5_orientedAdjointProcess o A₂)).toSetValued =
        fun xStar =>
          (adjointVecOriented o A₁).toSetValued xStar +
            (adjointVecOriented o A₂).toSetValued xStar := by
  funext xStar
  -- Step 1: expand the auxiliary-process definition and rewrite `addProcess` as the pointwise
  -- Minkowski sum of the two adjoint fibers.
  simpa [helperForTheorem_39_5_orientedAdjointProcess, addSetValued] using
    congrFun
      (helperForTheorem_39_5_addProcess_toSetValued
        (helperForTheorem_39_5_orientedAdjointProcess o A₁)
        (helperForTheorem_39_5_orientedAdjointProcess o A₂))
      xStar

/-- Helper for Theorem 39.5: under the dual relative-interior qualification, the opposite-oriented
adjoint of the auxiliary adjoint-process sum identifies with the original Minkowski sum. -/
lemma helperForTheorem_39_5_auxiliaryDualSum_toSetValued_eq_addProcess
    {m n : ℕ} (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n)
    (hA₁ : A₁.IsClosed) (hA₂ : A₂.IsClosed)
    (hriAdj :
      Set.Nonempty
        (ri (setValuedDom (adjointVecOriented o A₁).toSetValued) ∩
          ri (setValuedDom (adjointVecOriented o A₂).toSetValued))) :
    (adjointVecOriented o.opposite
      (addProcess (helperForTheorem_39_5_orientedAdjointProcess o A₁)
        (helperForTheorem_39_5_orientedAdjointProcess o A₂))).toSetValued =
      (addProcess A₁ A₂).toSetValued := by
  let B₁ : ConvexProcess n m := helperForTheorem_39_5_orientedAdjointProcess o A₁
  let B₂ : ConvexProcess n m := helperForTheorem_39_5_orientedAdjointProcess o A₂
  have hriDual : Set.Nonempty (ri B₁.dom ∩ ri B₂.dom) := by
    -- Step 1: rewrite the dual-domain hypothesis as the domain qualification for the auxiliary
    -- adjoint processes.
    simpa [B₁, B₂, helperForTheorem_39_5_orientedAdjointProcess] using hriAdj
  have hDualExact :
      (adjointVecOriented o.opposite (addProcess B₁ B₂)).toSetValued =
        fun x =>
          (adjointVecOriented o.opposite B₁).toSetValued x +
            (adjointVecOriented o.opposite B₂).toSetValued x :=
    helperForTheorem_39_5_infimum_exact_processMap_identification o.opposite B₁ B₂ hriDual
  have hB₁Double :
      (adjointVecOriented o.opposite B₁).toSetValued = A₁.toSetValued := by
    -- Step 2: closedness lets the first auxiliary adjoint process dualize back to `A₁`.
    simpa [B₁] using
      helperForTheorem_39_5_doubleAdjoint_orientedAdjointProcess_toSetValued_eq_self
        o A₁ hA₁
  have hB₂Double :
      (adjointVecOriented o.opposite B₂).toSetValued = A₂.toSetValued := by
    -- Step 3: the same double-adjoint recovery works for `A₂`.
    simpa [B₂] using
      helperForTheorem_39_5_doubleAdjoint_orientedAdjointProcess_toSetValued_eq_self
        o A₂ hA₂
  have hAuxiliary :
      (adjointVecOriented o.opposite (addProcess B₁ B₂)).toSetValued =
        (addProcess A₁ A₂).toSetValued := by
    -- Step 4: evaluate the dual exact sum formula fiberwise and rewrite both auxiliary double
    -- adjoints back to the original processes.
    funext u
    calc
      (adjointVecOriented o.opposite (addProcess B₁ B₂)).toSetValued u =
          ((adjointVecOriented o.opposite B₁).toSetValued u) +
            ((adjointVecOriented o.opposite B₂).toSetValued u) := by
              simpa using congrFun hDualExact u
      _ = A₁.toSetValued u + A₂.toSetValued u := by rw [hB₁Double, hB₂Double]
      _ = (addProcess A₁ A₂).toSetValued u := by
            simpa [addSetValued] using
              (congrFun (helperForTheorem_39_5_addProcess_toSetValued A₁ A₂) u).symm
  simpa [B₁, B₂] using hAuxiliary

/-- Helper for Theorem 39.5: the dual exact identification forces the original Minkowski sum
process to be closed. -/
lemma helperForTheorem_39_5_addProcessClosed_of_dualQualification
    {m n : ℕ} (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n)
    (hA₁ : A₁.IsClosed) (hA₂ : A₂.IsClosed)
    (hriAdj :
      Set.Nonempty
        (ri (setValuedDom (adjointVecOriented o A₁).toSetValued) ∩
          ri (setValuedDom (adjointVecOriented o A₂).toSetValued))) :
    (addProcess A₁ A₂).IsClosed := by
  let B₁ : ConvexProcess n m := helperForTheorem_39_5_orientedAdjointProcess o A₁
  let B₂ : ConvexProcess n m := helperForTheorem_39_5_orientedAdjointProcess o A₂
  have hDualExactToAddProcess :
      (adjointVecOriented o.opposite (addProcess B₁ B₂)).toSetValued =
        (addProcess A₁ A₂).toSetValued := by
    -- Step 1: identify the auxiliary dual sum with the original process sum.
    simpa [B₁, B₂] using
      helperForTheorem_39_5_auxiliaryDualSum_toSetValued_eq_addProcess
        o A₁ A₂ hA₁ hA₂ hriAdj
  have hAddGraphClosed :
      _root_.IsClosed (setValuedGraph (addProcess A₁ A₂).toSetValued) := by
    -- Step 2: the graph of the auxiliary double adjoint is closed, and the previous
    -- identification transports that closedness to `A₁ + A₂`.
    simpa [IsClosedSetValuedMap, setValuedGraph', setValuedGraph, hDualExactToAddProcess] using
      (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint
        o.opposite (addProcess B₁ B₂)).2.1
  -- Step 3: convert graph closedness back into closedness of the convex process itself.
  exact
    (helperForProposition_39_0_13_graphClosed_iff_processClosed (addProcess A₁ A₂)).1
      hAddGraphClosed

/-- Helper for Theorem 39.5: after dualizing the closed branch to the auxiliary adjoint
processes, the adjoint of `A₁ + A₂` is the closure of that auxiliary sum process. -/
lemma helperForTheorem_39_5_adjointAddProcess_toSetValued_eq_cl_auxiliarySum
    {m n : ℕ} (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n)
    (hA₁ : A₁.IsClosed) (hA₂ : A₂.IsClosed)
    (hriAdj :
      Set.Nonempty
        (ri (setValuedDom (adjointVecOriented o A₁).toSetValued) ∩
          ri (setValuedDom (adjointVecOriented o A₂).toSetValued))) :
    (adjointVecOriented o (addProcess A₁ A₂)).toSetValued =
      ((addProcess (helperForTheorem_39_5_orientedAdjointProcess o A₁)
        (helperForTheorem_39_5_orientedAdjointProcess o A₂)).cl).toSetValued := by
  let B₁ : ConvexProcess n m := helperForTheorem_39_5_orientedAdjointProcess o A₁
  let B₂ : ConvexProcess n m := helperForTheorem_39_5_orientedAdjointProcess o A₂
  have hDualExactToAddProcess :
      (adjointVecOriented o.opposite (addProcess B₁ B₂)).toSetValued =
        (addProcess A₁ A₂).toSetValued := by
    -- Step 1: reuse the auxiliary exact-sum identification from the dual branch.
    simpa [B₁, B₂] using
      helperForTheorem_39_5_auxiliaryDualSum_toSetValued_eq_addProcess
        o A₁ A₂ hA₁ hA₂ hriAdj
  have hClosureTransport :
      (adjointVecOriented o (addProcess A₁ A₂)).toSetValued =
        ((addProcess B₁ B₂).cl).toSetValued := by
    -- Step 2: replace `A₁ + A₂` by the opposite-oriented adjoint of the auxiliary sum, then apply
    -- the double-adjoint-equals-closure package to that auxiliary sum process.
    calc
      (adjointVecOriented o (addProcess A₁ A₂)).toSetValued =
          (adjointVecOrientedSetValued o
            ((adjointVecOriented o.opposite (addProcess B₁ B₂)).toSetValued)).toSetValued := by
              change
                (adjointVecOrientedSetValued o (addProcess A₁ A₂).toSetValued).toSetValued =
                  (adjointVecOrientedSetValued o
                    ((adjointVecOriented o.opposite (addProcess B₁ B₂)).toSetValued)).toSetValued
              rw [hDualExactToAddProcess.symm]
      _ = doubleAdjointVecSetValuedOriented o.opposite (addProcess B₁ B₂) := by
            cases o <;> rfl
      _ = ((addProcess B₁ B₂).cl).toSetValued :=
        (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint
          o.opposite (addProcess B₁ B₂)).2.2.2.1
  simpa [B₁, B₂] using hClosureTransport

/-- Helper for Theorem 39.5: closed branch packaged as a single reconstructed-graph target for
the proof pipeline. -/
lemma helperForTheorem_39_5_closed_reconstructed_graph {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n)
    (hA₁ : A₁.IsClosed) (hA₂ : A₂.IsClosed)
    (hriAdj :
    Set.Nonempty
        (ri (setValuedDom (adjointVecOriented o A₁).toSetValued) ∩
          ri (setValuedDom (adjointVecOriented o A₂).toSetValued))) :
    (addProcess A₁ A₂).IsClosed ∧
      setValuedGraph ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued) =
        closure
          (setValuedGraph fun xStar =>
            (adjointVecOriented o A₁).toSetValued xStar +
              (adjointVecOriented o A₂).toSetValued xStar) := by
  let B₁ : ConvexProcess n m := helperForTheorem_39_5_orientedAdjointProcess o A₁
  let B₂ : ConvexProcess n m := helperForTheorem_39_5_orientedAdjointProcess o A₂
  have hBsumToSetValued :
      (addProcess B₁ B₂).toSetValued =
        fun xStar =>
          (adjointVecOriented o A₁).toSetValued xStar +
            (adjointVecOriented o A₂).toSetValued xStar := by
    -- Step 1: the raw dual Minkowski sum is literally the sum of the two adjoint fibers.
    simpa [B₁, B₂] using
      helperForTheorem_39_5_addProcess_orientedAdjointProcess_toSetValued o A₁ A₂
  have hAddClosed : (addProcess A₁ A₂).IsClosed :=
    -- Step 2: closedness of the primal sum is now packaged as a dedicated dual-qualification
    -- consequence.
    helperForTheorem_39_5_addProcessClosed_of_dualQualification o A₁ A₂ hA₁ hA₂ hriAdj
  have hAdjointEqClosure :
      (adjointVecOriented o (addProcess A₁ A₂)).toSetValued =
        ((addProcess B₁ B₂).cl).toSetValued := by
    -- Step 3: the remaining adjoint-as-closure identification is also packaged separately.
    simpa [B₁, B₂] using
      helperForTheorem_39_5_adjointAddProcess_toSetValued_eq_cl_auxiliarySum
        o A₁ A₂ hA₁ hA₂ hriAdj
  constructor
  · exact hAddClosed
  · calc
      setValuedGraph ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued) =
          setValuedGraph ((addProcess B₁ B₂).cl).toSetValued := by
            rw [hAdjointEqClosure]
      _ = closure (setValuedGraph (addProcess B₁ B₂).toSetValued) :=
        helperForProposition_39_0_6_cl_graph (addProcess B₁ B₂)
      _ = closure
            (setValuedGraph fun xStar =>
              (adjointVecOriented o A₁).toSetValued xStar +
                (adjointVecOriented o A₂).toSetValued xStar) := by
            rw [hBsumToSetValued]

-- Proof sketch: Combine the graph/polar-cone description of adjoints (Theorem 39.2) with the
-- convex-analytic sum rule for support/indicator conjugates (Theorem 38.2 and Corollary 38.2.1),
-- using the relative-interior intersection hypotheses to ensure exactness (no closure) in the
-- first part; in the second part, closedness hypotheses yield closedness of `A₁ + A₂` and identify
-- the adjoint of the sum with the closure of the Minkowski sum of adjoints.
/-- Helper for Theorem 39.5: isolate the exact adjoint-sum branch as a standalone implication
from the primal relative-interior hypothesis. -/
lemma helperForTheorem_39_5_exact_branch {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n) :
    Set.Nonempty (ri A₁.dom ∩ ri A₂.dom) →
      (adjointVecOriented o (addProcess A₁ A₂)).toSetValued =
        fun xStar =>
          (adjointVecOriented o A₁).toSetValued xStar +
            (adjointVecOriented o A₂).toSetValued xStar := by
  intro hri
  -- Step 1: feed the primal relative-interior hypothesis into the already-established exact
  -- oriented adjoint-sum identification.
  exact helperForTheorem_39_5_infimum_exact_processMap_identification o A₁ A₂ hri

/-- Helper for Theorem 39.5: isolate the closed-graph branch as a standalone implication from the
closedness assumptions and the dual relative-interior hypothesis. -/
lemma helperForTheorem_39_5_closed_branch {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n) :
    A₁.IsClosed →
      A₂.IsClosed →
        Set.Nonempty
            (ri (setValuedDom (adjointVecOriented o A₁).toSetValued) ∩
              ri (setValuedDom (adjointVecOriented o A₂).toSetValued)) →
          (addProcess A₁ A₂).IsClosed ∧
            setValuedGraph ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued) =
              closure
                (setValuedGraph fun xStar =>
                  (adjointVecOriented o A₁).toSetValued xStar +
                    (adjointVecOriented o A₂).toSetValued xStar) := by
  intro hA₁ hA₂ hriAdj
  -- Step 1: pass the closedness and dual relative-interior data into the reconstructed-graph
  -- package already proved above.
  exact helperForTheorem_39_5_closed_reconstructed_graph o A₁ A₂ hA₁ hA₂ hriAdj

/-- Theorem 39.5: Let `A₁` and `A₂` be convex processes from `ℝ^m` to `ℝ^n`, viewed in the same
orientation convention `o : ConvexSetOrientation`.

If `ri (dom A₁)` and `ri (dom A₂)` have a point in common, then the (oriented) adjoint of the
Minkowski sum satisfies `(A₁ + A₂)^* = A₁^* + A₂^*` as set-valued mappings.

If `A₁` and `A₂` are closed and `ri (dom A₁^*)` and `ri (dom A₂^*)` have a point in common, then
`A₁ + A₂` is closed and `(A₁ + A₂)^*` is the closure (graph-closure) of `A₁^* + A₂^*`. -/
theorem theorem_39_5 {m n : ℕ} (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n) :
    (Set.Nonempty (ri A₁.dom ∩ ri A₂.dom) →
        (adjointVecOriented o (addProcess A₁ A₂)).toSetValued =
          fun xStar =>
            (adjointVecOriented o A₁).toSetValued xStar + (adjointVecOriented o A₂).toSetValued xStar) ∧
      (A₁.IsClosed →
          A₂.IsClosed →
            Set.Nonempty
                (ri (setValuedDom (adjointVecOriented o A₁).toSetValued) ∩
                  ri (setValuedDom (adjointVecOriented o A₂).toSetValued)) →
              (addProcess A₁ A₂).IsClosed ∧
                setValuedGraph ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued) =
                  closure
                    (setValuedGraph fun xStar =>
                      (adjointVecOriented o A₁).toSetValued xStar +
                        (adjointVecOriented o A₂).toSetValued xStar)) :=
  by
  constructor
  · -- Step 1: the first theorem branch is exactly the dedicated exact-sum wrapper.
    exact helperForTheorem_39_5_exact_branch o A₁ A₂
  · -- Step 2: the second theorem branch is exactly the dedicated closed-graph wrapper.
    exact helperForTheorem_39_5_closed_branch o A₁ A₂

-- Proof sketch: Unfold the definition of the oriented adjoint `adjointVecOriented`. For `r > 0`,
-- membership `uStar ∈ (r • A)^* xStar` is the inequality `finDot u uStar ≥ finDot x xStar` for all
-- `u` and all `x ∈ r • A u`, i.e. `x = r • x₀` with `x₀ ∈ A u`. Rewrite the inequality as
-- `finDot u (r⁻¹ • uStar) ≥ finDot x₀ xStar` to identify `r⁻¹ • uStar ∈ A^* xStar`, which is
-- equivalent to `uStar ∈ r • (A^* xStar)`.
/-- Helper for Theorem 39.6: the chosen scaled convex process has exactly the expected underlying
set-valued map. -/
lemma helperForTheorem_39_6_smulProcess_toSetValued {m n : ℕ}
    (A : ConvexProcess m n) (r : ℝ) :
    (smulProcess r A).toSetValued = smulSetValued r A := by
  -- Step 1: unpack the witness chosen in the definition of `smulProcess`.
  exact Classical.choose_spec ((prop_39_0_7 (A := A) (B := A) (r := r)).1)

/-- Helper for Theorem 39.6: a point lies in the positively scaled fiber `r • A u` exactly when
descaling it by `r⁻¹` lands back in the original fiber. -/
lemma helperForTheorem_39_6_mem_smulSetValued_iff {m n : ℕ}
    (A : ConvexProcess m n) (r : ℝ) (hr : 0 < r)
    (u : Fin m → ℝ) (x : Fin n → ℝ) :
    x ∈ smulSetValued r A u ↔ r⁻¹ • x ∈ A.toSetValued u := by
  constructor
  · intro hx
    rcases Set.mem_smul_set.1 hx with ⟨x0, hx0, rfl⟩
    -- Step 1: descaling a point of the scaled fiber recovers a point of the original fiber.
    simpa [smul_smul, hr.ne'] using hx0
  · intro hx
    -- Step 2: rescaling the descaled point returns the original point in the scaled fiber.
    refine Set.mem_smul_set.2 ?_
    refine ⟨r⁻¹ • x, hx, ?_⟩
    simp [smul_smul, hr.ne']

/-- Helper for Theorem 39.6: dividing a positive scalar out of the second dual variable turns the
scaled supremum-branch inequality back into the original one. -/
lemma helperForTheorem_39_6_descale_supremumInequality {m n : ℕ}
    (u : Fin m → ℝ) (x : Fin n → ℝ) (uStar : Fin m → ℝ) (xStar : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r)
    (h : finDot (r • x) xStar ≤ finDot u uStar) :
    finDot x xStar ≤ finDot u (r⁻¹ • uStar) := by
  -- Step 1: multiply the whole inequality by `r⁻¹`, which is nonnegative because `r > 0`.
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.2 hr))
  -- Step 2: simplify the two scaled dot products to recover the descaled comparison.
  simpa [finDot, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, hr.ne'] using hmul

/-- Helper for Theorem 39.6: dividing a positive scalar out of the second dual variable also
transports the infimum-branch inequality back to the original fiber. -/
lemma helperForTheorem_39_6_descale_infimumInequality {m n : ℕ}
    (u : Fin m → ℝ) (x : Fin n → ℝ) (uStar : Fin m → ℝ) (xStar : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r)
    (h : finDot u uStar ≤ finDot (r • x) xStar) :
    finDot u (r⁻¹ • uStar) ≤ finDot x xStar := by
  -- Step 1: multiply the whole inequality by `r⁻¹`, again preserving order by positivity.
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.2 hr))
  -- Step 2: simplify the scaled dot products to identify the unscaled adjoint inequality.
  simpa [finDot, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, hr.ne'] using hmul

/-- Helper for Theorem 39.6: multiplying a supremum-branch inequality by a positive scalar yields
the corresponding inequality for the scaled process fiber. -/
lemma helperForTheorem_39_6_scale_supremumInequality {m n : ℕ}
    (u : Fin m → ℝ) (x : Fin n → ℝ) (v : Fin m → ℝ) (xStar : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r)
    (h : finDot x xStar ≤ finDot u v) :
    finDot (r • x) xStar ≤ finDot u (r • v) := by
  -- Step 1: multiply the base inequality by the positive scalar `r`.
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hr)
  -- Step 2: rewrite the products as dot products against the scaled vectors.
  simpa [finDot, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Theorem 39.6: multiplying an infimum-branch inequality by a positive scalar yields
the corresponding inequality for the scaled process fiber. -/
lemma helperForTheorem_39_6_scale_infimumInequality {m n : ℕ}
    (u : Fin m → ℝ) (x : Fin n → ℝ) (v : Fin m → ℝ) (xStar : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r)
    (h : finDot u v ≤ finDot x xStar) :
    finDot u (r • v) ≤ finDot (r • x) xStar := by
  -- Step 1: multiply the base inequality by the positive scalar `r`.
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hr)
  -- Step 2: rewrite the products as dot products against the scaled vectors.
  simpa [finDot, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Theorem 39.6: every covector in the adjoint fiber of the positively scaled process
comes from scaling a covector in the original adjoint fiber by the same positive scalar.

Helper for Theorem 39.6: this is the forward inclusion `(rA)^* x* ⊆ r • (A^* x*)`. -/
lemma helperForTheorem_39_6_forwardMembership {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n) (r : ℝ) (hr : 0 < r)
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (huStar : uStar ∈ (adjointVecOriented o (smulProcess r A)).toSetValued xStar) :
    uStar ∈ r • (adjointVecOriented o A).toSetValued xStar := by
  cases o
  · change uStar ∈ setValuedAdjointVec (smulProcess r A).toSetValued xStar at huStar
    refine Set.mem_smul_set.2 ?_
    refine ⟨r⁻¹ • uStar, ?_, ?_⟩
    · change r⁻¹ • uStar ∈ setValuedAdjointVec A.toSetValued xStar
      -- Step 1: test the scaled adjoint inequality on points of the form `r • x`.
      intro u x hx
      have hxScaled : r • x ∈ smulSetValued r A u := Set.mem_smul_set.2 ⟨x, hx, rfl⟩
      have huStar' :
          ∀ u x, x ∈ smulSetValued r A u → finDot u uStar ≥ finDot x xStar := by
        simpa [helperForTheorem_39_6_smulProcess_toSetValued, smulSetValued] using huStar
      have hScaledIneq : finDot u uStar ≥ finDot (r • x) xStar := huStar' u (r • x) hxScaled
      have hScaledIneq' : finDot (r • x) xStar ≤ finDot u uStar := hScaledIneq
      -- Step 2: divide the inequality by the positive scalar to recover the original adjoint fiber.
      have hDescaled :
          finDot x xStar ≤ finDot u (r⁻¹ • uStar) :=
        helperForTheorem_39_6_descale_supremumInequality u x uStar xStar hr hScaledIneq'
      exact hDescaled
    · -- Step 3: the witness scales back to the original covector.
      simp [smul_smul, hr.ne']
  · change uStar ∈ setValuedAdjointVecInf (smulProcess r A).toSetValued xStar at huStar
    refine Set.mem_smul_set.2 ?_
    refine ⟨r⁻¹ • uStar, ?_, ?_⟩
    · change r⁻¹ • uStar ∈ setValuedAdjointVecInf A.toSetValued xStar
      -- Step 1: test the scaled adjoint inequality on points of the form `r • x`.
      intro u x hx
      have hxScaled : r • x ∈ smulSetValued r A u := Set.mem_smul_set.2 ⟨x, hx, rfl⟩
      have huStar' :
          ∀ u x, x ∈ smulSetValued r A u → finDot u uStar ≤ finDot x xStar := by
        simpa [helperForTheorem_39_6_smulProcess_toSetValued, smulSetValued] using huStar
      have hScaledIneq : finDot u uStar ≤ finDot (r • x) xStar := huStar' u (r • x) hxScaled
      -- Step 2: divide the inequality by the positive scalar to recover the original adjoint fiber.
      have hDescaled :
          finDot u (r⁻¹ • uStar) ≤ finDot x xStar :=
        helperForTheorem_39_6_descale_infimumInequality u x uStar xStar hr hScaledIneq
      exact hDescaled
    · -- Step 3: the witness scales back to the original covector.
      simp [smul_smul, hr.ne']

/-- Helper for Theorem 39.6: every scaled covector in `r • (A^* x*)` belongs to the adjoint fiber
of the positively scaled process.

Helper for Theorem 39.6: this is the reverse inclusion `r • (A^* x*) ⊆ (rA)^* x*`. -/
lemma helperForTheorem_39_6_backwardMembership {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n) (r : ℝ) (hr : 0 < r)
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (huStar : uStar ∈ r • (adjointVecOriented o A).toSetValued xStar) :
    uStar ∈ (adjointVecOriented o (smulProcess r A)).toSetValued xStar := by
  cases o
  · change uStar ∈ r • setValuedAdjointVec A.toSetValued xStar at huStar
    rcases Set.mem_smul_set.1 huStar with ⟨v, hv, rfl⟩
    change r • v ∈ setValuedAdjointVec (smulProcess r A).toSetValued xStar
    -- Step 1: rewrite the scaled-process fiber as the actual scaled set `r • A u`.
    rw [helperForTheorem_39_6_smulProcess_toSetValued]
    intro u x hx
    have hx0 : r⁻¹ • x ∈ A.toSetValued u :=
      (helperForTheorem_39_6_mem_smulSetValued_iff A r hr u x).1 hx
    have hvIneq : finDot u v ≥ finDot (r⁻¹ • x) xStar := hv u (r⁻¹ • x) hx0
    have hvIneq' : finDot (r⁻¹ • x) xStar ≤ finDot u v := hvIneq
    -- Step 2: multiply the original adjoint inequality by the positive scalar `r`.
    have hScaled :
        finDot (r • (r⁻¹ • x)) xStar ≤ finDot u (r • v) :=
      helperForTheorem_39_6_scale_supremumInequality u (r⁻¹ • x) v xStar hr hvIneq'
    -- Step 3: simplify the rescaled point back to the original test vector `x`.
    simpa [smul_smul, hr.ne'] using hScaled
  · change uStar ∈ r • setValuedAdjointVecInf A.toSetValued xStar at huStar
    rcases Set.mem_smul_set.1 huStar with ⟨v, hv, rfl⟩
    change r • v ∈ setValuedAdjointVecInf (smulProcess r A).toSetValued xStar
    -- Step 1: rewrite the scaled-process fiber as the actual scaled set `r • A u`.
    rw [helperForTheorem_39_6_smulProcess_toSetValued]
    intro u x hx
    have hx0 : r⁻¹ • x ∈ A.toSetValued u :=
      (helperForTheorem_39_6_mem_smulSetValued_iff A r hr u x).1 hx
    have hvIneq : finDot u v ≤ finDot (r⁻¹ • x) xStar := hv u (r⁻¹ • x) hx0
    -- Step 2: multiply the original adjoint inequality by the positive scalar `r`.
    have hScaled :
        finDot u (r • v) ≤ finDot (r • (r⁻¹ • x)) xStar :=
      helperForTheorem_39_6_scale_infimumInequality u (r⁻¹ • x) v xStar hr hvIneq
    -- Step 3: simplify the rescaled point back to the original test vector `x`.
    simpa [smul_smul, hr.ne'] using hScaled

/-- Helper for Theorem 39.6: membership in the adjoint fiber of the positively scaled process is
equivalent to membership in the corresponding positive scaling of the original adjoint fiber. -/
lemma helperForTheorem_39_6_membership_iff {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n) (r : ℝ) (hr : 0 < r)
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    uStar ∈ (adjointVecOriented o (smulProcess r A)).toSetValued xStar ↔
      uStar ∈ r • (adjointVecOriented o A).toSetValued xStar := by
  constructor
  · -- Step 1: the forward implication is exactly the descaling membership lemma.
    intro huStar
    exact helperForTheorem_39_6_forwardMembership o A r hr xStar uStar huStar
  · -- Step 2: the reverse implication is the scaling membership lemma.
    intro huStar
    exact helperForTheorem_39_6_backwardMembership o A r hr xStar uStar huStar

/-- Helper for Theorem 39.6: on each fixed dual fiber `xStar`, the adjoint of the positively
scaled process is exactly the positive scalar multiple of the original adjoint fiber. -/
lemma helperForTheorem_39_6_pointwiseFiberEquality {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n) (r : ℝ) (hr : 0 < r)
    (xStar : Fin n → ℝ) :
    (adjointVecOriented o (smulProcess r A)).toSetValued xStar =
      r • (adjointVecOriented o A).toSetValued xStar := by
  ext uStar
  -- Step 1: reduce the fiber equality to the dedicated pointwise membership equivalence.
  exact helperForTheorem_39_6_membership_iff o A r hr xStar uStar

/-- Helper for Theorem 39.6: once every dual fiber is identified, the whole oriented adjoint map
of the scaled process agrees with the corresponding positive scalar multiple of the original
adjoint map. -/
lemma helperForTheorem_39_6_toSetValuedEquality {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n) (r : ℝ) (hr : 0 < r) :
    (adjointVecOriented o (smulProcess r A)).toSetValued =
      fun xStar => r • (adjointVecOriented o A).toSetValued xStar := by
  -- Step 1: identify the two set-valued maps by checking equality on each dual fiber.
  funext xStar
  -- Step 2: invoke the dedicated pointwise fiber computation.
  exact helperForTheorem_39_6_pointwiseFiberEquality o A r hr xStar

/-- Theorem 39.6: For any oriented convex process `A`, one has `(λ A)^* = λ A^*` for every `λ > 0`.

Here `λ A` is the scalar-multiple convex process `smulProcess λ A`, and `A^*` is the oriented
Euclidean adjoint `adjointVecOriented`. -/
theorem theorem_39_6 {m n : ℕ} (o : ConvexSetOrientation) (A : ConvexProcess m n) (r : ℝ)
    (hr : 0 < r) :
    (adjointVecOriented o (smulProcess r A)).toSetValued =
      fun xStar => r • (adjointVecOriented o A).toSetValued xStar :=
  by
  -- Step 1: defer the global set-valued-map equality to the dedicated map-level helper.
  exact helperForTheorem_39_6_toSetValuedEquality o A r hr

/-- The effective domain `dom f` of an `EReal`-valued function `f`, defined as the set of points
where `f` is finite (i.e. not `+∞`). -/
def eRealFunctionDom {X : Type*} (f : X → EReal) : Set X :=
  { x | f x ≠ ⊤ }

/-- The convex-process infimal pushforward `(A f)` of an `EReal`-valued function `f` along a convex
process `A : ℝ^m ⇉ ℝ^n`, defined by

`(A f)(x) = inf { f u | u ∈ A⁻¹ x }`. -/
noncomputable def infPreimageEReal {m n : ℕ} (A : ConvexProcess m n)
    (f : (Fin m → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun x => sInf (f '' A.inverseMap x)

/-- The process image `A f` is the Chapter 38 image under the indicator bifunction of `A`, provided
`f` never takes the value `⊥` (as in the proper-function hypotheses of Theorem 39.7). -/
lemma infPreimageEReal_eq_bifunctionImageRaw_indicator_of_noBot {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal) (hf : ∀ u, f u ≠ ⊥) :
    infPreimageEReal A f = bifunctionImageRaw (ConvexProcess.indicatorBifunction A) f := by
  funext x
  have hset :
      f '' A.inverseMap x = Set.range (fun u : {u // u ∈ A.inverseMap x} => f u.1) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u.1, u.2, rfl⟩
  rw [infPreimageEReal, hset, sInf_range, bifunctionImageRaw]
  calc
    (⨅ u : {u // u ∈ A.inverseMap x}, f u.1)
        = ⨅ u, ⨅ (_ : x ∈ A.toSetValued u), f u := by
            simp [ConvexProcess.inverseMap, setValuedInverse, iInf_subtype]
    _ = ⨅ u, if x ∈ A.toSetValued u then f u else ⊤ := by
          refine iInf_congr ?_
          intro u
          by_cases hx : x ∈ A.toSetValued u
          · simp [hx]
          · simp [hx]
    _ = ⨅ u, f u + if x ∈ A.toSetValued u then 0 else ⊤ := by
          refine iInf_congr ?_
          intro u
          by_cases hx : x ∈ A.toSetValued u
          · simp [hx]
          · simp [hx, hf u, EReal.add_top_of_ne_bot]

/-- Specialization of the previous bridge under the `IsProperEReal` hypothesis used in
Theorem 39.7. -/
lemma infPreimageEReal_eq_bifunctionImageRaw_indicator_of_proper {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal) (hf : IsProperEReal f) :
    infPreimageEReal A f = bifunctionImageRaw (ConvexProcess.indicatorBifunction A) f :=
  infPreimageEReal_eq_bifunctionImageRaw_indicator_of_noBot A f hf.1

/-- The indicator bifunction of a convex process has parameter domain exactly `dom A`, so the
Theorem 39.7 qualification `ri (dom f) ∩ ri (dom A)` matches the Chapter 38 qualification for
`F := indicatorBifunction A`. -/
lemma bifunctionDom_indicatorBifunction_eq_dom {m n : ℕ} (A : ConvexProcess m n) :
    bifunctionDom (ConvexProcess.indicatorBifunction A) = A.dom := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    by_cases hxMem : x ∈ A.toSetValued u
    · exact ⟨x, hxMem⟩
    · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxMem] at hx
  · rintro ⟨x, hxMem⟩
    refine ⟨x, ?_⟩
    simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxMem]

/-- The product-side indicator bifunction of a convex process is proper in the Chapter 38 sense:
it never takes the value `⊥`, and the origin graph point witnesses that it is not identically
`⊤`. -/
lemma indicatorBifunction_isProperEReal {m n : ℕ} (A : ConvexProcess m n) :
    IsProperEReal
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => ConvexProcess.indicatorBifunction A p.1 p.2) := by
  constructor
  · intro p
    by_cases hp : p.2 ∈ A.toSetValued p.1
    · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hp]
    · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hp]
  · refine ⟨(0, 0), ?_⟩
    simp [ConvexProcess.indicatorBifunction, indicatorEReal, A.zero_mem]

/-- The product-space indicator bifunction of a convex process is convex in the Chapter 38 sense,
because its epigraph is the product of the convex graph cone with the half-line `r ≥ 0`. -/
lemma indicatorBifunction_isERealConvex {m n : ℕ} (A : ConvexProcess m n) :
    IsERealConvex
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => ConvexProcess.indicatorBifunction A p.1 p.2) := by
  rw [IsERealConvex, ERealEpigraph]
  let graphSet : Set ((Fin m → ℝ) × (Fin n → ℝ)) := setValuedGraph A.toSetValued
  have hGraphConv : Convex ℝ graphSet :=
    (helperForProposition_39_0_1_graphConvexCone_ofConvexProcess A).convex
  intro p hp q hq a b ha hb hab
  have hpGraph : p.1 ∈ graphSet := by
    by_cases hpMem : p.1.2 ∈ A.toSetValued p.1.1
    · simp [graphSet, setValuedGraph, hpMem]
    · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hpMem] at hp
  have hqGraph : q.1 ∈ graphSet := by
    by_cases hqMem : q.1.2 ∈ A.toSetValued q.1.1
    · simp [graphSet, setValuedGraph, hqMem]
    · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hqMem] at hq
  have hpHeight : 0 ≤ p.2 := by
    have hpMem : p.1.2 ∈ A.toSetValued p.1.1 := by simpa [graphSet, setValuedGraph] using hpGraph
    simpa [ERealEpigraph, ConvexProcess.indicatorBifunction, indicatorEReal, hpMem] using hp
  have hqHeight : 0 ≤ q.2 := by
    have hqMem : q.1.2 ∈ A.toSetValued q.1.1 := by simpa [graphSet, setValuedGraph] using hqGraph
    simpa [ERealEpigraph, ConvexProcess.indicatorBifunction, indicatorEReal, hqMem] using hq
  have hComboGraph : a • p.1 + b • q.1 ∈ graphSet :=
    hGraphConv hpGraph hqGraph ha hb hab
  have hComboHeight : 0 ≤ a * p.2 + b * q.2 := by
    nlinarith
  have hComboMem :
      (a • p.1.1 + b • q.1.1, a • p.1.2 + b • q.1.2) ∈ graphSet := by
    simpa [Prod.smul_mk, Prod.mk_add_mk] using hComboGraph
  have hComboFiber : a • p.1.2 + b • q.1.2 ∈ A.toSetValued (a • p.1.1 + b • q.1.1) := by
    simpa [graphSet, setValuedGraph] using hComboMem
  have hComboHeightEReal :
      (0 : EReal) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal) := by
    exact_mod_cast hComboHeight
  simpa [ConvexProcess.indicatorBifunction, indicatorEReal, hComboFiber] using hComboHeightEReal

/-- If a convex process is closed, then its indicator bifunction is lower semicontinuous on the
product, so it satisfies the closedness hypothesis used in Corollary 38.4.1. -/
lemma indicatorBifunction_isProductLowerSemicontinuous_of_closed {m n : ℕ}
    (A : ConvexProcess m n) (hAClosed : A.IsClosed) :
    IsProductLowerSemicontinuousBifunction (ConvexProcess.indicatorBifunction A) := by
  rw [IsProductLowerSemicontinuousBifunction]
  let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal := ConvexProcess.indicatorBifunction A
  have hGraphClosed :
      IsFunctionConvexClosed (graphFunctionOfBifunction F) :=
    (indicatorBifunction_rockafellarPackage A).2.2 hAClosed
  have hGraphLsc : LowerSemicontinuous (graphFunctionOfBifunction F) := by
    have hClosureLsc :
        LowerSemicontinuous (functionConvexClosure (graphFunctionOfBifunction F)) :=
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
        (f := graphFunctionOfBifunction F)
    exact hGraphClosed ▸ hClosureLsc
  have hPackCont : Continuous (fun p : (Fin m → ℝ) × (Fin n → ℝ) => Fin.append p.1 p.2) := by
    simpa using
      (continuous_pi fun i => by
        by_cases hi : i.1 < m
        · simpa [Fin.append, Fin.addCases, hi] using
            ((continuous_apply (i := (⟨i.1, hi⟩ : Fin m))).comp continuous_fst)
        · let j : Fin n := ⟨i.1 - m, by omega⟩
          have hjCont : Continuous fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.2 j :=
            (continuous_apply (i := j)).comp continuous_snd
          simpa [Fin.append, Fin.addCases, hi, j] using hjCont)
  simpa [F, graphFunctionOfBifunction] using hGraphLsc.comp_continuous hPackCont

/-- The Chapter 38 inverse bifunction `F_*` attached to the indicator of a convex process is
exactly the negative indicator bifunction of the inverse process. This is the textbook
identification `F_*(x,u) = -δ(u | A⁻¹ x)`. -/
lemma bifunctionInverse_indicatorBifunction_eq_negIndicatorBifunction_inverse {m n : ℕ}
    (A : ConvexProcess m n) :
    bifunctionInverse (ConvexProcess.indicatorBifunction A) =
      ConvexProcess.negIndicatorBifunction A.inverse := by
  funext x u
  by_cases hx : x ∈ A.toSetValued u
  · simp [bifunctionInverse, ConvexProcess.indicatorBifunction,
      ConvexProcess.negIndicatorBifunction, helperForProposition_39_0_6_inverse_toSetValued,
      ConvexProcess.inverseMap, setValuedInverse, negIndicatorEReal, indicatorEReal, hx]
  · simp [bifunctionInverse, ConvexProcess.indicatorBifunction,
      ConvexProcess.negIndicatorBifunction, helperForProposition_39_0_6_inverse_toSetValued,
      ConvexProcess.inverseMap, setValuedInverse, negIndicatorEReal, indicatorEReal, hx]

/-- The dual image `x* ↦ inf_{u* ∈ A* x*} g(u*)` is the Chapter 38 image under the indicator
bifunction of `setValuedInverse (adjointVec A).toSetValued`, provided `g` never takes `⊥`. -/
lemma sInf_image_adjointVec_eq_bifunctionImageRaw_indicator_of_noBot {m n : ℕ}
    (A : ConvexProcess m n) (g : (Fin m → ℝ) → EReal) (hg : ∀ uStar, g uStar ≠ ⊥) :
    (fun xStar => sInf (g '' (adjointVec A).toSetValued xStar)) =
      bifunctionImageRaw
        (indicatorBifunctionSetValued (setValuedInverse (adjointVec A).toSetValued))
        g := by
  funext xStar
  have hset :
      g '' (adjointVec A).toSetValued xStar =
        Set.range (fun uStar : {uStar // uStar ∈ (adjointVec A).toSetValued xStar} => g uStar.1) := by
    ext y
    constructor
    · rintro ⟨uStar, huStar, rfl⟩
      exact ⟨⟨uStar, huStar⟩, rfl⟩
    · rintro ⟨uStar, rfl⟩
      exact ⟨uStar.1, uStar.2, rfl⟩
  rw [hset, sInf_range, bifunctionImageRaw]
  calc
    (⨅ uStar : {uStar // uStar ∈ (adjointVec A).toSetValued xStar}, g uStar.1)
        = ⨅ uStar, ⨅ (_ : uStar ∈ (adjointVec A).toSetValued xStar), g uStar := by
            simp [iInf_subtype]
    _ = ⨅ uStar, if uStar ∈ (adjointVec A).toSetValued xStar then g uStar else ⊤ := by
          refine iInf_congr ?_
          intro uStar
          by_cases hu : uStar ∈ (adjointVec A).toSetValued xStar
          · simp [hu]
          · simp [hu]
    _ = ⨅ uStar, g uStar + if uStar ∈ (adjointVec A).toSetValued xStar then 0 else ⊤ := by
          refine iInf_congr ?_
          intro uStar
          by_cases hu : uStar ∈ (adjointVec A).toSetValued xStar
          · simp [hu]
          · simp [hu, hg uStar, EReal.add_top_of_ne_bot]
    _ = bifunctionImageRaw
          (indicatorBifunctionSetValued (setValuedInverse (adjointVec A).toSetValued)) g xStar := by
          simp [bifunctionImageRaw, indicatorBifunctionSetValued, adjointVec, setValuedInverse,
            indicatorEReal]

end ConvexProcess

end Section39
end Chap08
