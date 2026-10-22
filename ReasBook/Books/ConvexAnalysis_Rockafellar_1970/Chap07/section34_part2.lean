/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part1

section Chap07
section Section34

open Set

/-- Predicates on coordinate spaces in this section are treated classically when needed in
piecewise definitions. -/
noncomputable local instance classicalDecidablePredPart2 {α : Type*} (p : α → Prop) :
    DecidablePred p :=
  Classical.decPred p

section SaddleAmbient

variable {m n : ℕ}

/-- Helper for Text 34.1.4: the canonical upper partner of `underline(K)` is unique without
invoking the upstream Corollary 33.3.2 shim, because its defining equality already pins down
the witness. -/
lemma helperForText_34_1_4_lowerClosure_uniqueUpperClosedPartner
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    ∃! U' : SaddleFunction m n,
      IsConcaveConvex U' ∧
        IsUpperClosedSaddleFunction U' ∧
        U' = partialClosure₁ (lowerClosureConcaveConvex K h) ∧
        partialClosure₂ U' = lowerClosureConcaveConvex K h := by
  -- Route correction: this uniqueness statement does not need the global Section 33
  -- correspondence, because the witness equation already determines the partner exactly.
  exact helperForText_34_1_4_existsUniqueCanonicalUpperPartner K h hNoBot

/-- Helper for Text 34.1.4: Corollary 33.3.2 makes `cl₂ overline(K)` the unique lower-closed
partner attached to the mixed upper closure. -/
lemma helperForText_34_1_4_existsUniqueCanonicalLowerPartner
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    ∃! L' : SaddleFunction m n,
      IsConcaveConvex L' ∧
        IsLowerClosedSaddleFunction L' ∧
        upperClosureConcaveConvex K h = partialClosure₁ L' ∧
        partialClosure₂ (upperClosureConcaveConvex K h) = L' := by
  -- The canonical lower partner is already `cl₂ overline(K)`, so existence again comes from
  -- the closure data already established locally.
  refine ⟨partialClosure₂ (upperClosureConcaveConvex K h), ?_, ?_⟩
  · -- Reuse the canonical-partner package proved just above.
    exact helperForText_34_1_4_secondClosureOfUpper_isCanonicalLowerPartner K h hNoBot
  · intro L' hL'
    -- Uniqueness is definitional: the data already records `cl₂ overline(K) = L'`.
    exact hL'.2.2.2.symm

/-- Helper for Text 34.1.4: the canonical lower partner of `overline(K)` is unique without
invoking the upstream Corollary 33.3.2 shim, because the recovery equality already determines
the witness. -/
lemma helperForText_34_1_4_upperClosure_uniqueLowerClosedPartner
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    ∃! L' : SaddleFunction m n,
      IsConcaveConvex L' ∧
        IsLowerClosedSaddleFunction L' ∧
        upperClosureConcaveConvex K h = partialClosure₁ L' ∧
        partialClosure₂ (upperClosureConcaveConvex K h) = L' := by
  -- Route correction: this uniqueness statement also does not need the global Section 33
  -- correspondence, because the witness equation already determines the partner exactly.
  exact helperForText_34_1_4_existsUniqueCanonicalLowerPartner K h hNoBot

/-- Helper for Text 34.1.4: the second partial closure of the mixed upper closure already lies
below the mixed lower closure. -/
lemma helperForText_34_1_4_secondClosureOfUpper_le_lowerClosure
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    partialClosure₂ (upperClosureConcaveConvex K h) ≤ lowerClosureConcaveConvex K h := by
  -- Compare the mixed upper closure with `cl₁ K`, then apply `cl₂` and rewrite the result.
  rcases helperForText_34_0_1_mixedClosure_formulas K h with ⟨hLowerFormula, -⟩
  have hUpper_le_cl₁K : upperClosureConcaveConvex K h ≤ partialClosure₁ K := by
    rcases helperForText_34_0_1_mixedClosure_formulas K h with ⟨-, hUpperFormula⟩
    calc
      upperClosureConcaveConvex K h = partialClosure₁ (partialClosure₂ K) := hUpperFormula
      _ ≤ partialClosure₁ K :=
        helperForText_34_0_1_partialClosure₁_mono
          (helperForText_34_0_1_partialClosure₂_le K)
  calc
    partialClosure₂ (upperClosureConcaveConvex K h) ≤ partialClosure₂ (partialClosure₁ K) :=
      helperForText_34_0_1_partialClosure₂_mono hUpper_le_cl₁K
    _ = lowerClosureConcaveConvex K h := by
      rw [← hLowerFormula]

/-- Helper for Text 34.1.4: the canonical lower partner `cl₂ overline(K)` also lies below
`overline(K)` itself by the Section 33 closure-pair order theorem. -/
lemma helperForText_34_1_4_secondClosureOfUpper_le_upperClosure
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    partialClosure₂ (upperClosureConcaveConvex K h) ≤ upperClosureConcaveConvex K h := by
  let L' := partialClosure₂ (upperClosureConcaveConvex K h)
  let U := upperClosureConcaveConvex K h
  have hUOrient : IsConcaveConvex U := by
    -- The mixed upper closure stays in the concave-convex orientation of `K`.
    simpa [U] using
      (helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBot).2.1
  have hL'Orient : IsConcaveConvex L' := by
    -- The canonical lower partner `cl₂ overline(K)` is still concave-convex.
    simpa [L', U] using
      (helperForText_34_1_4_secondClosureOfUpper_isCanonicalLowerPartner K h hNoBot).1
  have hPair :
      U = partialClosure₁ L' ∧ partialClosure₂ U = L' := by
    -- Package the canonical lower partner in the exact closure-pair form used by
    -- Corollary 33.3.1.
    simpa [L', U] using
      (helperForText_34_1_4_secondClosureOfUpper_isCanonicalLowerPartner K h hNoBot).2.2
  -- Corollary 33.3.1 now gives the pointwise order for this exact lower/upper partner pair.
  simpa [L', U] using
    (helperForCorollary33_3_1_coordinatewise_closure_pair_implies_closedness_and_order
      (K := L') (Kbar := U)
      (by simpa [IsConcaveConvex] using hL'Orient)
      (by simpa [IsConcaveConvex] using hUOrient)
      hPair).2.2

/-- Helper for Text 34.1.4: once the exact recovery `cl₂ overline(K) = underline(K)` is known,
the mixed-order inequality follows immediately from the Section 33 uniqueness package. -/
lemma helperForText_34_1_4_mixedClosure_order_of_secondClosure_eq_lower
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K)
    (hRecover :
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h) :
    lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h := by
  -- Corollary 33.3.2 identifies the actual mixed upper closure with the canonical partner
  -- `cl₁ underline(K)` once its second closure is known to recover `underline(K)` exactly.
  rcases helperForText_34_1_4_upperClosure_uniqueLowerClosedPartner K h hNoBot with
    ⟨L', hL', -⟩
  have hUpperEqCanonical :
      upperClosureConcaveConvex K h = partialClosure₁ (lowerClosureConcaveConvex K h) := by
    have hL'eq : L' = lowerClosureConcaveConvex K h := by
      calc
        L' = partialClosure₂ (upperClosureConcaveConvex K h) := by
          symm
          exact hL'.2.2.2
        _ = lowerClosureConcaveConvex K h := hRecover
    calc
      upperClosureConcaveConvex K h = partialClosure₁ L' := hL'.2.2.1
      _ = partialClosure₁ (lowerClosureConcaveConvex K h) := by
            rw [hL'eq]
  -- The canonical Section 33 partner already dominates the lower closure pointwise.
  calc
    lowerClosureConcaveConvex K h ≤ partialClosure₁ (lowerClosureConcaveConvex K h) :=
      helperForText_34_1_4_lowerClosure_below_canonicalUpperPartner K h
    _ = upperClosureConcaveConvex K h := hUpperEqCanonical.symm

/-- Helper for Text 34.1.4: on fixed first- and second-variable neighborhoods, the trivial
minimax inequality places the local maximin value below the local minimax value. -/
lemma helperForText_34_1_4_fixedNeighborhood_maximin_le_minimax
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)
      ≤
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1) := by
  -- This is the generic complete-lattice minimax inequality applied to the two neighborhood
  -- index sets.
  simpa using
    (iSup_iInf_le_iInf_iSup
      (f := fun w : {w : Fin m → ℝ // ‖w - u‖ < ε.1} =>
        fun z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1} => K w.1 z.1))

/-- Helper for Text 34.1.4: on fixed neighborhood balls, reverse minimax together with the
trivial forward inequality yields equality of the local minimax and maximin values. -/
lemma helperForText_34_1_4_fixedNeighborhood_minimax_eq_maximin_of_reverseMinimax
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ})
    (hReverse :
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
        ≤
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)) :
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
      =
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
  -- Combine the assumed reverse inequality with the generic forward minimax inequality.
  apply le_antisymm
  · exact hReverse
  · -- The forward direction is the trivial minimax inequality (maximin ≤ minimax).
    exact
      helperForText_34_1_4_fixedNeighborhood_maximin_le_minimax
        (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)

/-- Helper for Text 34.1.4: pointwise, the lower mixed closure is the supremum over
second-variable neighborhoods of the infimum over first-variable neighborhoods of the local
minimax values. -/
lemma helperForText_34_1_4_lowerMixedClosure_pointwise_as_supInf_localBallMinimax
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    partialClosure₂ (partialClosure₁ K) u xStar =
      ⨆ (δ : {δ : ℝ // 0 < δ}),
        ⨅ (ε : {ε : ℝ // 0 < ε}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
            ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1 := by
  -- Unfold the two coordinatewise closures and commute the two infima so the outer radii
  -- appear in the order needed for the remaining lattice comparison.
  calc
    partialClosure₂ (partialClosure₁ K) u xStar
        = ⨆ (δ : {δ : ℝ // 0 < δ}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
              ⨅ (ε : {ε : ℝ // 0 < ε}),
                ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1 := by
            rfl
    _ = ⨆ (δ : {δ : ℝ // 0 < δ}),
          ⨅ (ε : {ε : ℝ // 0 < ε}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
              ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1 := by
          refine iSup_congr ?_
          intro δ
          rw [iInf_comm]

/-- Helper for Text 34.1.4: pointwise, the upper mixed closure is the infimum over
first-variable neighborhoods of the supremum over second-variable neighborhoods of the local
maximin values. -/
lemma helperForText_34_1_4_upperMixedClosure_pointwise_as_infSup_localBallMaximin
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    partialClosure₁ (partialClosure₂ K) u xStar =
      ⨅ (ε : {ε : ℝ // 0 < ε}),
        ⨆ (δ : {δ : ℝ // 0 < δ}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1 := by
  -- Unfold the two coordinatewise closures and commute the two suprema so the neighborhood
  -- game values line up with the fixed-ball minimax statement.
  calc
    partialClosure₁ (partialClosure₂ K) u xStar
        = ⨅ (ε : {ε : ℝ // 0 < ε}),
            ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
              ⨆ (δ : {δ : ℝ // 0 < δ}),
                ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1 := by
            rfl
    _ = ⨅ (ε : {ε : ℝ // 0 < ε}),
          ⨆ (δ : {δ : ℝ // 0 < δ}),
            ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
              ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1 := by
          refine iInf_congr ?_
          intro ε
          rw [iSup_comm]

/-- Helper for Text 34.1.4: enlarging the first-variable neighborhood can only increase the
local minimax value. -/
lemma helperForText_34_1_4_fixedNeighborhood_minimax_mono_firstRadius
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    {ε ε' : {ε : ℝ // 0 < ε}} (hε : ε.1 ≤ ε'.1)
    (δ : {δ : ℝ // 0 < δ}) :
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
      ≤
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε'.1}), K w.1 z.1) := by
  -- Reindex each first-variable point from the smaller ball into the larger ball.
  refine iInf_mono ?_
  intro z
  refine iSup_le ?_
  intro w
  exact le_iSup_of_le ⟨w.1, lt_of_lt_of_le w.2 hε⟩ le_rfl

/-- Helper for Text 34.1.4: enlarging the second-variable neighborhood can only decrease the
local minimax value. -/
lemma helperForText_34_1_4_fixedNeighborhood_minimax_antitone_secondRadius
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε})
    {δ δ' : {δ : ℝ // 0 < δ}} (hδ : δ.1 ≤ δ'.1) :
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ'.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
      ≤
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1) := by
  -- Shrinking the infimum index set can only raise the neighborhood game value.
  refine le_iInf ?_
  intro z
  exact iInf_le_of_le ⟨z.1, lt_of_lt_of_le z.2 hδ⟩ le_rfl

/-- Helper for Text 34.1.4: enlarging the first-variable neighborhood can only increase the
local maximin value. -/
lemma helperForText_34_1_4_fixedNeighborhood_maximin_mono_firstRadius
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    {ε ε' : {ε : ℝ // 0 < ε}} (hε : ε.1 ≤ ε'.1)
    (δ : {δ : ℝ // 0 < δ}) :
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)
      ≤
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε'.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
  -- Reindex each first-variable point from the smaller ball into the larger ball.
  refine iSup_le ?_
  intro w
  exact le_iSup_of_le ⟨w.1, lt_of_lt_of_le w.2 hε⟩ le_rfl

/-- Helper for Text 34.1.4: enlarging the second-variable neighborhood can only decrease the
local maximin value. -/
lemma helperForText_34_1_4_fixedNeighborhood_maximin_antitone_secondRadius
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε})
    {δ δ' : {δ : ℝ // 0 < δ}} (hδ : δ.1 ≤ δ'.1) :
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ'.1}), K w.1 z.1)
      ≤
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
  -- Shrinking the infimum index set raises each local response value, hence also the outer
  -- supremum.
  refine iSup_le ?_
  intro w
  refine le_trans ?_ (le_iSup_of_le ⟨w.1, w.2⟩ le_rfl)
  refine le_iInf ?_
  intro z
  exact iInf_le_of_le ⟨z.1, lt_of_lt_of_le z.2 hδ⟩ le_rfl

/-- Helper for Text 34.1.4: once the mixed lower closure lies below the mixed upper closure,
the second cross-closure identity follows by squeezing `cl₂ overline(K)` between them. -/
lemma helperForText_34_1_4_secondClosureOfUpper_eq_lower_of_mixedClosure_order
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h) :
    partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  -- The upper mixed closure already gives the upper bound `cl₂ overline(K) ≤ underline(K)`.
  -- The mixed-order hypothesis gives the reverse bound by second-variable closedness of
  -- `underline(K)`, so antisymmetry yields the exact recovery.
  have hReverse :
      lowerClosureConcaveConvex K h ≤ partialClosure₂ (upperClosureConcaveConvex K h) := by
    rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBot with
      ⟨-, -, hLowerClosed, -⟩
    exact
      helperForText_34_0_1_le_partialClosure₂_of_convexClosedInSecond_of_le
        hLowerClosed hOrder
  exact le_antisymm
    (helperForText_34_1_4_secondClosureOfUpper_le_lowerClosure K h)
    hReverse

/-- Helper for Text 34.1.4: the remaining order comparison is definitionally the raw mixed
closure inequality `cl₂ (cl₁ K) ≤ cl₁ (cl₂ K)`. -/
lemma helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h ↔
      partialClosure₂ (partialClosure₁ K) ≤ partialClosure₁ (partialClosure₂ K) := by
  -- Rewrite both mixed closures to the explicit iterated coordinatewise closures from
  -- Defn. 34.1 so that the target comparison is expressed on the raw operators.
  rcases helperForText_34_0_1_mixedClosure_formulas K h with ⟨hLowerFormula, hUpperFormula⟩
  constructor
  · intro hOrder
    -- The forward direction is just the defining rewrite of `underline(K)` and `overline(K)`.
    simpa [hLowerFormula, hUpperFormula] using hOrder
  · intro hOrder
    -- The reverse direction packages the raw mixed-order theorem back into the textbook form.
    simpa [hLowerFormula, hUpperFormula] using hOrder

/-- Helper for Text 34.1.4: a reverse minimax inequality on every pair of first- and
second-variable neighborhoods already forces the raw mixed-closure order
`cl₂ (cl₁ K) ≤ cl₁ (cl₂ K)`. -/
lemma helperForText_34_1_4_rawMixedClosureOrder_of_fixedNeighborhood_reverseMinimax
    (K : SaddleFunction m n)
    (hReverse :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ)
        (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}),
        (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
          ≤
        (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)) :
    partialClosure₂ (partialClosure₁ K) ≤ partialClosure₁ (partialClosure₂ K) := by
  intro u xStar
  -- Rewrite the mixed closures to the nested neighborhood minimax/maximin expressions from the
  -- previous two helpers.
  rw [helperForText_34_1_4_lowerMixedClosure_pointwise_as_supInf_localBallMinimax]
  rw [helperForText_34_1_4_upperMixedClosure_pointwise_as_infSup_localBallMaximin]
  -- First replace each fixed-ball minimax value by the reverse-minimax upper bound.
  have hLocalToLocal :
      (⨆ (δ : {δ : ℝ // 0 < δ}),
        ⨅ (ε : {ε : ℝ // 0 < ε}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
            ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
        ≤
      (⨆ (δ : {δ : ℝ // 0 < δ}),
        ⨅ (ε : {ε : ℝ // 0 < ε}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
    refine iSup_mono ?_
    intro δ
    refine iInf_mono ?_
    intro ε
    exact hReverse u xStar ε δ
  have hOuterMinimax :
      (⨆ (δ : {δ : ℝ // 0 < δ}),
        ⨅ (ε : {ε : ℝ // 0 < ε}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)
        ≤
      (⨅ (ε : {ε : ℝ // 0 < ε}),
        ⨆ (δ : {δ : ℝ // 0 < δ}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
    -- Then the generic complete-lattice minimax inequality compares the outer `sup-inf` and
    -- `inf-sup` envelopes of the resulting local maximin family.
    simpa using
      (iSup_iInf_le_iInf_iSup
        (f := fun δ : {δ : ℝ // 0 < δ} =>
          fun ε : {ε : ℝ // 0 < ε} =>
            (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
              ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)))
  exact le_trans hLocalToLocal hOuterMinimax

/-- Helper for Text 34.1.4: once the fixed-neighborhood reverse minimax theorem is available,
the textbook mixed-closure order `underline(K) ≤ overline(K)` follows immediately. -/
lemma helperForText_34_1_4_mixedClosure_order_of_fixedNeighborhood_reverseMinimax
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hReverse :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ)
        (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}),
        (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
          ≤
        (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)) :
    lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h := by
  -- First normalize the neighborhood hypothesis to the raw operator inequality
  -- `cl₂ (cl₁ K) ≤ cl₁ (cl₂ K)`.
  have hRawOrder :
      partialClosure₂ (partialClosure₁ K) ≤ partialClosure₁ (partialClosure₂ K) :=
    helperForText_34_1_4_rawMixedClosureOrder_of_fixedNeighborhood_reverseMinimax K hReverse
  -- Then rewrite the raw operator inequality back to the textbook lower/upper closures.
  exact
    (helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder K h).2 hRawOrder

/-- Helper for Text 34.1.4: a fixed-neighborhood reverse minimax theorem upgrades the mixed-order
comparison to the exact recovery identity `cl₂ overline(K) = underline(K)`. -/
lemma helperForText_34_1_4_secondClosureOfUpper_eq_lower_of_fixedNeighborhood_reverseMinimax
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K)
    (hReverse :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ)
        (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}),
        (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
          ≤
        (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)) :
    partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  -- First obtain `underline(K) ≤ overline(K)` from the reverse-minimax hypothesis.
  have hOrder :
      lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h :=
    helperForText_34_1_4_mixedClosure_order_of_fixedNeighborhood_reverseMinimax K h hReverse
  -- Then squeeze `cl₂ overline(K)` between `underline(K)` and itself to recover equality.
  exact helperForText_34_1_4_secondClosureOfUpper_eq_lower_of_mixedClosure_order
    K h hNoBot hOrder

/-- Helper for Text 34.1.4: the textbook mixed-order comparison is equivalent to the exact
recovery `cl₂ overline(K) = underline(K)`. -/
lemma helperForText_34_1_4_mixedClosure_order_iff_secondClosureOfUpper_eq_lower
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h ↔
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  constructor
  · intro hOrder
    -- The forward direction is exactly the squeezing argument already isolated from the
    -- remaining blocker.
    exact helperForText_34_1_4_secondClosureOfUpper_eq_lower_of_mixedClosure_order
      K h hNoBot hOrder
  · intro hRecover
    -- Conversely, once `cl₂ overline(K)` recovers `underline(K)` exactly, the Section 33
    -- uniqueness package upgrades it to the mixed-order inequality immediately.
    exact helperForText_34_1_4_mixedClosure_order_of_secondClosure_eq_lower
      K h hNoBot hRecover

/-- Helper for Text 34.1.4: a saddle point on two open balls forces the reverse minimax
inequality.

This packages the standard saddle-point implication: if `(w₀, z₀)` satisfies
`K w z₀ ≤ K w₀ z` for all `w` and `z` in the respective balls, then the local minimax and
maximin values coincide with the saddle value `K w₀ z₀`. -/
lemma helperForText_34_1_4_fixedNeighborhood_reverseMinimax_of_saddlePointOn
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ})
    (w0 : Fin m → ℝ) (hw0 : ‖w0 - u‖ < ε.1)
    (z0 : Fin n → ℝ) (hz0 : ‖z0 - xStar‖ < δ.1)
    (hS : IsSaddlePointOn
      (X := {z : Fin n → ℝ | ‖z - xStar‖ < δ.1})
      (Y := {w : Fin m → ℝ | ‖w - u‖ < ε.1})
      (f := fun z w => K w z) z0 w0) :
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
      ≤
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
  -- Extract the set-indexed minimax equalities pinned down by the saddle point.
  have hValue :=
    isSaddlePointOn_value
      (X := {z : Fin n → ℝ | ‖z - xStar‖ < δ.1})
      (Y := {w : Fin m → ℝ | ‖w - u‖ < ε.1})
      (f := fun z w => K w z) hz0 hw0 hS
  -- Rewrite the subtype-indexed lattice expressions as the corresponding set-indexed ones.
  have hMinimaxEq :
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
        =
      (⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ < δ.1),
        ⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ < ε.1), K w z) := by
    simp [iInf_subtype, iSup_subtype]
  have hMaximinEq :
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)
        =
      (⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ < ε.1),
        ⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ < δ.1), K w z) := by
    simp [iInf_subtype, iSup_subtype]
  -- Both the set-indexed minimax and maximin values are exactly the saddle value `K w₀ z₀`.
  have hMinimaxSet :
      (⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ < δ.1),
        ⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ < ε.1), K w z)
        = K w0 z0 := by
    simpa using hValue.1
  have hMaximinSet :
      (⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ < ε.1),
        ⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ < δ.1), K w z)
        = K w0 z0 := by
    simpa using hValue.2
  -- Conclude by rewriting both sides to the same saddle value, hence obtaining `≤`.
  have hEq :
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
        =
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
    calc
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
          =
        (⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ < δ.1),
          ⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ < ε.1), K w z) := hMinimaxEq
      _ = K w0 z0 := hMinimaxSet
      _ =
        (⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ < ε.1),
          ⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ < δ.1), K w z) := hMaximinSet.symm
      _ =
        (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := hMaximinEq.symm
  exact le_of_eq hEq

/-- Helper for Text 34.1.4: a saddle point on two closed balls forces the reverse minimax
inequality.

This is the closed-ball analogue of
`helperForText_34_1_4_fixedNeighborhood_reverseMinimax_of_saddlePointOn`. -/
lemma helperForText_34_1_4_fixedNeighborhood_reverseMinimax_closedBall_of_saddlePointOn
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ρw ρz : ℝ)
    (w0 : Fin m → ℝ) (hw0 : ‖w0 - u‖ ≤ ρw)
    (z0 : Fin n → ℝ) (hz0 : ‖z0 - xStar‖ ≤ ρz)
    (hS : IsSaddlePointOn
      (X := {z : Fin n → ℝ | ‖z - xStar‖ ≤ ρz})
      (Y := {w : Fin m → ℝ | ‖w - u‖ ≤ ρw})
      (f := fun z w => K w z) z0 w0) :
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw}), K w.1 z.1)
      ≤
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz}), K w.1 z.1) := by
  -- Extract the set-indexed minimax equalities pinned down by the saddle point.
  have hValue :=
    isSaddlePointOn_value
      (X := {z : Fin n → ℝ | ‖z - xStar‖ ≤ ρz})
      (Y := {w : Fin m → ℝ | ‖w - u‖ ≤ ρw})
      (f := fun z w => K w z) hz0 hw0 hS
  -- Rewrite the subtype-indexed lattice expressions as the corresponding set-indexed ones.
  have hMinimaxEq :
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw}), K w.1 z.1)
        =
      (⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ ≤ ρz),
        ⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ ≤ ρw), K w z) := by
    simp [iInf_subtype, iSup_subtype]
  have hMaximinEq :
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz}), K w.1 z.1)
        =
      (⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ ≤ ρw),
        ⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ ≤ ρz), K w z) := by
    simp [iInf_subtype, iSup_subtype]
  -- Both the set-indexed minimax and maximin values are exactly the saddle value `K w₀ z₀`.
  have hMinimaxSet :
      (⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ ≤ ρz),
        ⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ ≤ ρw), K w z)
        = K w0 z0 := by
    simpa using hValue.1
  have hMaximinSet :
      (⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ ≤ ρw),
        ⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ ≤ ρz), K w z)
        = K w0 z0 := by
    simpa using hValue.2
  -- Conclude by rewriting both sides to the same saddle value, hence obtaining `≤`.
  have hEq :
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw}), K w.1 z.1)
        =
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz}), K w.1 z.1) := by
    calc
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw}), K w.1 z.1)
          =
        (⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ ≤ ρz),
          ⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ ≤ ρw), K w z) := hMinimaxEq
      _ = K w0 z0 := hMinimaxSet
      _ =
        (⨆ (w : Fin m → ℝ), ⨆ (hw : ‖w - u‖ ≤ ρw),
          ⨅ (z : Fin n → ℝ), ⨅ (hz : ‖z - xStar‖ ≤ ρz), K w z) := hMaximinSet.symm
      _ =
        (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz}), K w.1 z.1) := hMaximinEq.symm
  exact le_of_eq hEq

/-- Helper for Text 34.1.4: global concave-convexity on `ℝ^m × ℝ^n` restricts to any pair of
first- and second-variable open balls. -/
lemma helperForText_34_1_4_fixedNeighborhood_concaveConvexOn_of_global
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ)
      (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}),
      IsConcaveConvexOn
        ({w : Fin m → ℝ | ‖w - u‖ < ε.1})
        ({z : Fin n → ℝ | ‖z - xStar‖ < δ.1}) K := by
  intro u xStar ε δ
  rcases h with ⟨hConcaveInFirst, hConvexInSecond⟩
  constructor
  · intro z hz
    -- Restrict first-variable concavity from `univ` to the chosen first-variable ball.
    have hConcaveGlobal :
        IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun w => K w z) :=
      hConcaveInFirst z (by simp)
    intro w1 w2 hw1 hw2 a b ha hb hab hcomb
    exact hConcaveGlobal (x := w1) (y := w2) (by simp) (by simp) ha hb hab (by simp)
  · intro w hw
    -- Restrict second-variable convexity from `univ` to the chosen second-variable ball.
    have hConvexGlobal :
        IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun z => K w z) :=
      hConvexInSecond w (by simp)
    intro z1 z2 hz1 hz2 a b ha hb hab hcomb
    exact hConvexGlobal (x := z1) (y := z2) (by simp) (by simp) ha hb hab (by simp)

/-- Helper for Text 34.1.4: restricting the first- and second-variable domains preserves
`IsConcaveConvexOn`. -/
lemma helperForText_34_1_4_IsConcaveConvexOn_mono
    {C C' : Set (Fin m → ℝ)} {D D' : Set (Fin n → ℝ)}
    {K : SaddleFunction m n}
    (hC : C' ⊆ C) (hD : D' ⊆ D)
    (h : IsConcaveConvexOn C D K) :
    IsConcaveConvexOn C' D' K := by
  rcases h with ⟨hConcave, hConvex⟩
  constructor
  · intro z hz
    -- Restrict the first-variable concavity proof along the smaller second-variable domain.
    have hConcaveOnC : IsERealConcaveOn C (fun w => K w z) := hConcave z (hD hz)
    intro w1 w2 hw1 hw2 a b ha hb hab hcomb
    exact hConcaveOnC (x := w1) (y := w2) (hC hw1) (hC hw2) ha hb hab (hC hcomb)
  · intro w hw
    -- Restrict the second-variable convexity proof along the smaller first-variable domain.
    have hConvexOnD : IsERealConvexOn D (fun z => K w z) := hConvex w (hC hw)
    intro z1 z2 hz1 hz2 a b ha hb hab hcomb
    exact hConvexOnD (x := z1) (y := z2) (hD hz1) (hD hz2) ha hb hab (hD hcomb)

/-- Helper for Text 34.1.4: local concave-convexity on open balls restricts to every pair of
strictly smaller closed balls. -/
lemma helperForText_34_1_4_fixedNeighborhood_concaveConvexOn_closedBalls_of_local
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ})
    (hLocal :
      IsConcaveConvexOn
        ({w : Fin m → ℝ | ‖w - u‖ < ε.1})
        ({z : Fin n → ℝ | ‖z - xStar‖ < δ.1}) K) :
    ∀ (ρw : {ρ : ℝ // ρ < ε.1}) (ρz : {ρ : ℝ // ρ < δ.1}),
      IsConcaveConvexOn
        ({w : Fin m → ℝ | ‖w - u‖ ≤ ρw.1})
        ({z : Fin n → ℝ | ‖z - xStar‖ ≤ ρz.1}) K := by
  intro ρw ρz
  -- Each closed ball of strictly smaller radius lies inside the corresponding open ball.
  refine helperForText_34_1_4_IsConcaveConvexOn_mono ?_ ?_ hLocal
  · intro w hw
    have hwClosed : w ∈ Metric.closedBall u ρw.1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hwOpen : w ∈ Metric.ball u ε.1 :=
      Metric.closedBall_subset_ball ρw.2 hwClosed
    simpa [Metric.mem_ball, dist_eq_norm] using hwOpen
  · intro z hz
    have hzClosed : z ∈ Metric.closedBall xStar ρz.1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzOpen : z ∈ Metric.ball xStar δ.1 :=
      Metric.closedBall_subset_ball ρz.2 hzClosed
    simpa [Metric.mem_ball, dist_eq_norm] using hzOpen

/-- Helper for Text 34.1.4: an open-ball `iInf` can be rewritten as an `iInf` over all smaller
closed-ball radii, followed by the corresponding closed-ball `iInf`. -/
lemma helperForText_34_1_4_openBall_iInf_as_iInf_closedBallRadii
    {k : ℕ} (u : Fin k → ℝ) (ε : ℝ) (f : (Fin k → ℝ) → EReal) :
    (⨅ (w : {w : Fin k → ℝ // ‖w - u‖ < ε}), f w.1)
      =
    (⨅ (ρ : {ρ : ℝ // ρ < ε}),
      ⨅ (w : {w : Fin k → ℝ // ‖w - u‖ ≤ ρ.1}), f w.1) := by
  -- Rewrite the open ball as the union of all strictly smaller closed balls.
  have hUnionMetric :
      Metric.ball u ε =
        ⋃ (ρ : {ρ : ℝ // ρ < ε}), Metric.closedBall u ρ.1 := by
    calc
      Metric.ball u ε = ⋃ (r : ℝ) (hr : r < ε), Metric.closedBall u r := by
            simpa using (Metric.biUnion_lt_closedBall u ε).symm
      _ = ⋃ (ρ : {ρ : ℝ // ρ < ε}), Metric.closedBall u ρ.1 := by
            simp [iUnion_subtype]
  have hUnionNorm :
      {w : Fin k → ℝ | ‖w - u‖ < ε}
        =
      ⋃ (ρ : {ρ : ℝ // ρ < ε}), {w : Fin k → ℝ | ‖w - u‖ ≤ ρ.1} := by
    simpa [Metric.ball, Metric.closedBall, dist_eq_norm] using hUnionMetric
  -- Transport the indexed infimum through this union decomposition.
  calc
    (⨅ (w : {w : Fin k → ℝ // ‖w - u‖ < ε}), f w.1)
        = (⨅ w ∈ {w : Fin k → ℝ | ‖w - u‖ < ε}, f w) := by
            simp [iInf_subtype]
    _ = (⨅ w ∈ ⋃ (ρ : {ρ : ℝ // ρ < ε}), {w : Fin k → ℝ | ‖w - u‖ ≤ ρ.1}, f w) := by
          rw [hUnionNorm]
    _ = (⨅ (ρ : {ρ : ℝ // ρ < ε}), ⨅ w ∈ {w : Fin k → ℝ | ‖w - u‖ ≤ ρ.1}, f w) := by
          rw [iInf_iUnion]
    _ = (⨅ (ρ : {ρ : ℝ // ρ < ε}),
          ⨅ (w : {w : Fin k → ℝ // ‖w - u‖ ≤ ρ.1}), f w.1) := by
          simp [iInf_subtype]

/-- Helper for Text 34.1.4: an open-ball `iSup` can be rewritten as an `iSup` over all smaller
closed-ball radii, followed by the corresponding closed-ball `iSup`. -/
lemma helperForText_34_1_4_openBall_iSup_as_iSup_closedBallRadii
    {k : ℕ} (u : Fin k → ℝ) (ε : ℝ) (f : (Fin k → ℝ) → EReal) :
    (⨆ (w : {w : Fin k → ℝ // ‖w - u‖ < ε}), f w.1)
      =
    (⨆ (ρ : {ρ : ℝ // ρ < ε}),
      ⨆ (w : {w : Fin k → ℝ // ‖w - u‖ ≤ ρ.1}), f w.1) := by
  -- Rewrite the open ball as the union of all strictly smaller closed balls.
  have hUnionMetric :
      Metric.ball u ε =
        ⋃ (ρ : {ρ : ℝ // ρ < ε}), Metric.closedBall u ρ.1 := by
    calc
      Metric.ball u ε = ⋃ (r : ℝ) (hr : r < ε), Metric.closedBall u r := by
            simpa using (Metric.biUnion_lt_closedBall u ε).symm
      _ = ⋃ (ρ : {ρ : ℝ // ρ < ε}), Metric.closedBall u ρ.1 := by
            simp [iUnion_subtype]
  have hUnionNorm :
      {w : Fin k → ℝ | ‖w - u‖ < ε}
        =
      ⋃ (ρ : {ρ : ℝ // ρ < ε}), {w : Fin k → ℝ | ‖w - u‖ ≤ ρ.1} := by
    simpa [Metric.ball, Metric.closedBall, dist_eq_norm] using hUnionMetric
  -- Transport the indexed supremum through this union decomposition.
  calc
    (⨆ (w : {w : Fin k → ℝ // ‖w - u‖ < ε}), f w.1)
        = (⨆ w ∈ {w : Fin k → ℝ | ‖w - u‖ < ε}, f w) := by
            simp [iSup_subtype]
    _ = (⨆ w ∈ ⋃ (ρ : {ρ : ℝ // ρ < ε}), {w : Fin k → ℝ | ‖w - u‖ ≤ ρ.1}, f w) := by
          rw [hUnionNorm]
    _ = (⨆ (ρ : {ρ : ℝ // ρ < ε}), ⨆ w ∈ {w : Fin k → ℝ | ‖w - u‖ ≤ ρ.1}, f w) := by
          rw [iSup_iUnion]
    _ = (⨆ (ρ : {ρ : ℝ // ρ < ε}),
          ⨆ (w : {w : Fin k → ℝ // ‖w - u‖ ≤ ρ.1}), f w.1) := by
          simp [iSup_subtype]

/-- Helper for Text 34.1.4: the fixed-neighborhood minimax expression on open balls can be
expanded into nested inf/sup over smaller closed-ball radii. -/
lemma helperForText_34_1_4_fixedNeighborhood_minimax_openBall_as_closedBallRadii
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
      =
    (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
        ⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1) := by
  -- First decompose the outer open-ball infimum in the second variable.
  calc
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
        =
      (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1) := by
            simpa using
              (helperForText_34_1_4_openBall_iInf_as_iInf_closedBallRadii
                (u := xStar) (ε := δ.1)
                (f := fun z =>
                  ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z))
    -- Then decompose each inner open-ball supremum in the first variable.
    _ = (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
            ⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
              ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1) := by
          refine iInf_congr ?_
          intro ρz
          refine iInf_congr ?_
          intro z
          simpa using
            (helperForText_34_1_4_openBall_iSup_as_iSup_closedBallRadii
              (u := u) (ε := ε.1) (f := fun w => K w z.1))

/-- Helper for Text 34.1.4: the fixed-neighborhood maximin expression on open balls can be
expanded into nested sup/inf over smaller closed-ball radii. -/
lemma helperForText_34_1_4_fixedNeighborhood_maximin_openBall_as_closedBallRadii
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)
      =
    (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
        ⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1) := by
  -- First decompose the outer open-ball supremum in the first variable.
  calc
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)
        =
      (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
            simpa using
              (helperForText_34_1_4_openBall_iSup_as_iSup_closedBallRadii
                (u := u) (ε := ε.1)
                (f := fun w =>
                  ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w z.1))
    -- Then decompose each inner open-ball infimum in the second variable.
    _ = (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
            ⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
              ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1) := by
          refine iSup_congr ?_
          intro ρw
          refine iSup_congr ?_
          intro w
          simpa using
            (helperForText_34_1_4_openBall_iInf_as_iInf_closedBallRadii
              (u := xStar) (ε := δ.1) (f := fun z => K w.1 z))

/-- Helper for Text 34.1.4: to prove reverse minimax on open balls, it is enough to prove the
corresponding inequality on the closed-ball-radius envelope form. -/
lemma helperForText_34_1_4_fixedNeighborhood_reverseMinimax_of_closedBallRadiusEnvelope
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ})
    (hEnvelope :
      (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
          ⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
            ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1)
        ≤
      (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
          ⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1)) :
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
      ≤
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
  -- Rewrite the open-ball minimax side into the closed-ball-radius envelope.
  rw [helperForText_34_1_4_fixedNeighborhood_minimax_openBall_as_closedBallRadii
    (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)]
  -- Rewrite the open-ball maximin side into the closed-ball-radius envelope.
  rw [helperForText_34_1_4_fixedNeighborhood_maximin_openBall_as_closedBallRadii
    (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)]
  -- After normalization, the claim is exactly the assumed envelope inequality.
  exact hEnvelope

/-- Helper for Text 34.1.4: the reverse-minimax inequality on open balls is equivalent to the
closed-ball-radius envelope inequality used to isolate the upstream minimax blocker. -/
lemma helperForText_34_1_4_fixedNeighborhood_reverseMinimax_iff_closedBallRadiusEnvelope
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    ((⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
        ≤
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)) ↔
      (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
          ⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
            ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1)
        ≤
      (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
          ⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1) := by
  constructor
  · intro hReverse
    -- Rewrite the envelope goal back to the original open-ball inequality.
    rw [← helperForText_34_1_4_fixedNeighborhood_minimax_openBall_as_closedBallRadii
      (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)]
    rw [← helperForText_34_1_4_fixedNeighborhood_maximin_openBall_as_closedBallRadii
      (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)]
    exact hReverse
  · intro hEnvelope
    -- Convert the envelope inequality back to the open-ball reverse-minimax inequality via the
    -- deterministic reduction lemma.
    exact
      helperForText_34_1_4_fixedNeighborhood_reverseMinimax_of_closedBallRadiusEnvelope
        (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ) hEnvelope

/-- Helper for Text 34.1.4: a saddle point on the open-ball neighborhoods implies the
closed-ball-radius envelope reverse-minimax inequality.

This repackages
`helperForText_34_1_4_fixedNeighborhood_reverseMinimax_of_saddlePointOn` using the equivalence
`helperForText_34_1_4_fixedNeighborhood_reverseMinimax_iff_closedBallRadiusEnvelope`. -/
lemma helperForText_34_1_4_reverseMinimax_closedBallRadiusEnvelope_of_saddlePointOn
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ})
    (w0 : Fin m → ℝ) (hw0 : ‖w0 - u‖ < ε.1)
    (z0 : Fin n → ℝ) (hz0 : ‖z0 - xStar‖ < δ.1)
    (hS : IsSaddlePointOn
      (X := {z : Fin n → ℝ | ‖z - xStar‖ < δ.1})
      (Y := {w : Fin m → ℝ | ‖w - u‖ < ε.1})
      (f := fun z w => K w z) z0 w0) :
    (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
        ⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1)
      ≤
    (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
        ⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1) := by
  -- First obtain reverse-minimax on open balls from the saddle point.
  have hReverse :
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
        ≤
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) :=
    helperForText_34_1_4_fixedNeighborhood_reverseMinimax_of_saddlePointOn
      (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)
      (w0 := w0) (hw0 := hw0) (z0 := z0) (hz0 := hz0) hS
  -- Then translate to the closed-ball-radius envelope form via the established equivalence.
  exact
    (helperForText_34_1_4_fixedNeighborhood_reverseMinimax_iff_closedBallRadiusEnvelope
      (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)).1 hReverse

end SaddleAmbient

end Section34
end Chap07
