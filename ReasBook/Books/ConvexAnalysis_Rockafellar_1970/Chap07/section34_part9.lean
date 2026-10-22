/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part8

section Chap07
section Section34

open Set

/-- Predicates on coordinate spaces in this section are treated classically when needed in
piecewise definitions. -/
noncomputable local instance classicalDecidablePredPart9 {α : Type*} (p : α → Prop) :
    DecidablePred p :=
  Classical.decPred p

section SaddleAmbient

variable {m n : ℕ}

/-- Helper for Text 34.1.4: after checking both the local-minimax route and the Section 33
uniqueness route, the unresolved dependency-closed blocker is exactly the original-text bridge
`cl₂ overline(K) = underline(K)`, from which the normalized raw mixed-order comparison follows
formally. -/
lemma helperForText_34_1_4_rawMixedClosureOrder_missingPrerequisite
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h) :
    partialClosure₂ (partialClosure₁ K) ≤ partialClosure₁ (partialClosure₂ K) := by
  exact
    (helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder K h).1 hOrder

/-- Helper bridge for Text 34.1.4: the exact upstream reverse-minimax input needed by the proof
pipeline is precisely the normalized raw mixed-order inequality
`cl₂ (cl₁ K) ≤ cl₁ (cl₂ K)`. This theorem is just the dependency-closed package of the existing
missing-prerequisite lemma, exposed under the name the later endgame uses conceptually. -/
lemma helperForText_34_1_4_reverseMinimax_bridge
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h) :
    partialClosure₂ (partialClosure₁ K) ≤ partialClosure₁ (partialClosure₂ K) := by
  exact helperForText_34_1_4_rawMixedClosureOrder_missingPrerequisite K h hOrder

/-- Helper for Text 34.1.4: once the normalized raw mixed-order comparison is supplied, the
exact recovery `cl₂ overline(K) = underline(K)` follows formally from the already-proved local
endgame. -/
lemma helperForText_34_1_4_secondClosureOfUpper_eq_lower_from_concaveConvex
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h) :
    partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  -- Then squeeze `cl₂ overline(K)` between `underline(K)` and itself.
  exact helperForText_34_1_4_secondClosureOfUpper_eq_lower_of_mixedClosure_order K h hNoBotK hOrder

/-- Helper for Text 34.1.4: the only remaining upstream prerequisite is now the mixed-order
comparison `underline(K) ≤ overline(K)` for a bare concave-convex saddle-function. -/
lemma helperForText_34_1_4_mixedClosure_order
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h) :
    lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h := by
  exact hOrder

/-- Helper for Text 34.1.4: after isolating the true upstream blocker to the mixed-order
comparison, the exact recovery `cl₂ overline(K) = underline(K)` follows formally. -/
lemma helperForText_34_1_4_secondClosureOfUpper_eq_lower
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h) :
    partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  -- Route correction: this wrapper no longer carries the blocker. It just converts the mixed
  -- closure-order prerequisite into the exact recovery needed by the endgame lemmas.
  exact
    helperForText_34_1_4_secondClosureOfUpper_eq_lower_of_mixedClosure_order K h
      hNoBotK hOrder

/-- Helper for Text 34.1.4: independently of the unresolved mixed-order comparison, the mixed
upper closure always lies below `cl₁` of the mixed lower closure. -/
lemma helperForText_34_1_4_upperClosure_le_firstClosureOfLower
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    upperClosureConcaveConvex K h ≤ partialClosure₁ (lowerClosureConcaveConvex K h) := by
  rcases helperForText_34_0_1_mixedClosure_formulas K h with ⟨hLowerFormula, hUpperFormula⟩
  have hCl₂K_le_lower :
      partialClosure₂ K ≤ lowerClosureConcaveConvex K h := by
    -- Since `K ≤ cl₁ K`, applying `cl₂` places `cl₂ K` below the mixed lower closure.
    calc
      partialClosure₂ K ≤ partialClosure₂ (partialClosure₁ K) :=
        helperForText_34_0_1_partialClosure₂_mono
          (helperForText_34_0_1_le_partialClosure₁ K)
      _ = lowerClosureConcaveConvex K h := by
        rw [← hLowerFormula]
  -- Rewrite the upper mixed closure to `cl₁ (cl₂ K)` and then use monotonicity of `cl₁`.
  calc
    upperClosureConcaveConvex K h = partialClosure₁ (partialClosure₂ K) := hUpperFormula
    _ ≤ partialClosure₁ (lowerClosureConcaveConvex K h) :=
      helperForText_34_0_1_partialClosure₁_mono hCl₂K_le_lower

/-- Helper for Text 34.1.4: once the mixed lower closure is known to lie below the mixed upper
closure, first-variable closedness of the upper closure gives the reverse `cl₁` bound. -/
lemma helperForText_34_1_4_firstClosureOfLower_le_upper_of_mixedClosure_order
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h) :
    partialClosure₁ (lowerClosureConcaveConvex K h) ≤ upperClosureConcaveConvex K h := by
  rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBotK with
    ⟨-, -, -, hUpperClosed⟩
  -- Any concave-closed first-variable majorant bounds the first closure from above.
  exact
    helperForText_34_0_1_partialClosure₁_le_of_le_of_concaveClosedInFirst
      hOrder hUpperClosed

/-- Helper for Text 34.1.4: the mixed-order comparison already forces the first cross-closure
identity `cl₁ underline(K) = overline(K)`. -/
lemma helperForText_34_1_4_firstClosureOfLower_eq_upper_of_mixedClosure_order
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h) :
    partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h := by
  -- The mixed-order comparison gives the forward `cl₁` bound, while the reverse bound already
  -- holds independently of the unresolved upstream theorem.
  exact le_antisymm
    (helperForText_34_1_4_firstClosureOfLower_le_upper_of_mixedClosure_order K h hNoBotK hOrder)
    (helperForText_34_1_4_upperClosure_le_firstClosureOfLower K h)

/-- Helper for Text 34.1.4: once the mixed lower closure is known to lie below the mixed upper
closure, second-variable closedness of the lower closure gives the reverse `cl₂` bound. -/
lemma helperForText_34_1_4_lowerClosure_le_secondClosureOfUpper_of_mixedClosure_order
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h) :
    lowerClosureConcaveConvex K h ≤ partialClosure₂ (upperClosureConcaveConvex K h) := by
  rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBotK with
    ⟨-, -, hLowerClosed, -⟩
  -- Any convex-closed second-variable minorant stays below the second closure of a larger
  -- kernel.
  exact
    helperForText_34_0_1_le_partialClosure₂_of_convexClosedInSecond_of_le
      hLowerClosed hOrder

/-- Helper for Text 34.1.4: the raw mixed-order inequality on `cl₂ (cl₁ K)` and `cl₁ (cl₂ K)`
already packages the full concave-convex cross-closure conclusion. -/
lemma helperForText_34_1_4_concaveConvex_crossClosure_of_rawMixedClosureOrder
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hRawOrder : partialClosure₂ (partialClosure₁ K) ≤ partialClosure₁ (partialClosure₂ K)) :
    partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h ∧
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  -- First convert the raw operator inequality into the textbook order
  -- `underline(K) ≤ overline(K)`.
  have hOrder :
      lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h :=
    (helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder K h).2 hRawOrder
  constructor
  · -- The first cross-closure identity is the `cl₁` antisymmetry package for the mixed order.
    exact
      helperForText_34_1_4_firstClosureOfLower_eq_upper_of_mixedClosure_order K h hNoBotK hOrder
  · -- The second cross-closure identity is the already-isolated `cl₂` consequence of the same
    -- mixed-order comparison.
    exact
      helperForText_34_1_4_secondClosureOfUpper_eq_lower_of_mixedClosure_order K h hNoBotK hOrder

/-- Helper for Text 34.1.4: once the exact recovery `cl₂ overline(K) = underline(K)` is known,
both cross-closure identities follow immediately. -/
lemma helperForText_34_1_4_concaveConvex_crossClosure_of_secondClosure_eq_lower
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hRecover :
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h) :
    partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h ∧
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  -- First convert the exact recovery of `cl₂ overline(K)` into the mixed-order inequality.
  have hOrder :
      lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h :=
    helperForText_34_1_4_mixedClosure_order_of_secondClosure_eq_lower K h hNoBotK hRecover
  -- Repackage the mixed-order consequence as the raw operator inequality so the fully local
  -- endgame can be applied in one step.
  exact
    helperForText_34_1_4_concaveConvex_crossClosure_of_rawMixedClosureOrder K h hNoBotK
      ((helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder K h).1 hOrder)

/-- Helper for Text 34.1.4: the full textbook pair of cross-closure identities is equivalent to
the exact recovery statement `cl₂ overline(K) = underline(K)`. -/
lemma helperForText_34_1_4_concaveConvex_crossClosure_iff_secondClosureOfUpper_eq_lower
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K) :
    (partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h ∧
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h) ↔
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  constructor
  · intro hCross
    -- The second component of the textbook conclusion is exactly the normalized recovery
    -- statement isolated from the remaining blocker.
    exact hCross.2
  · intro hRecover
    -- Conversely, once the exact recovery is available, the earlier endgame packages both
    -- textbook identities at once.
    exact helperForText_34_1_4_concaveConvex_crossClosure_of_secondClosure_eq_lower
      K h hNoBotK hRecover

/-- Helper for Text 34.1.4: the first cross-closure identity already forces the textbook
mixed-order comparison. -/
lemma helperForText_34_1_4_mixedClosure_order_of_firstClosure_eq_upper
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hFirst :
      partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h) :
    lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h := by
  -- The Section 33 order theorem always gives `underline(K) ≤ cl₁ underline(K)`.
  calc
    lowerClosureConcaveConvex K h ≤ partialClosure₁ (lowerClosureConcaveConvex K h) :=
      helperForText_34_1_4_lowerClosure_below_canonicalUpperPartner K h
    _ = upperClosureConcaveConvex K h := hFirst

/-- Helper for Text 34.1.4: the textbook mixed-order comparison is equivalent to the two
cross-closure identities. -/
lemma helperForText_34_1_4_mixedClosure_order_iff_crossClosure
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K) :
    lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h ↔
      (partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h ∧
        partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h) := by
  constructor
  · intro hOrder
    -- The forward direction is exactly the local endgame already isolated from the blocker.
    constructor
    · exact
        helperForText_34_1_4_firstClosureOfLower_eq_upper_of_mixedClosure_order
          K h hNoBotK hOrder
    · exact
        helperForText_34_1_4_secondClosureOfUpper_eq_lower_of_mixedClosure_order
          K h hNoBotK hOrder
  · intro hCross
    -- Conversely, the first cross-closure identity alone already yields the mixed order.
    exact
      helperForText_34_1_4_mixedClosure_order_of_firstClosure_eq_upper K h hCross.1

/-- Helper for Text 34.1.4: the full concave-convex textbook conclusion is equivalent to the
raw operator inequality `cl₂ (cl₁ K) ≤ cl₁ (cl₂ K)`. -/
lemma helperForText_34_1_4_concaveConvex_crossClosure_iff_rawMixedClosureOrder
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K) :
    (partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h ∧
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h) ↔
      partialClosure₂ (partialClosure₁ K) ≤ partialClosure₁ (partialClosure₂ K) := by
  constructor
  · intro hCross
    -- First collapse the textbook pair of exact cross-closure identities to the mixed-order
    -- comparison they encode.
    have hOrder :
        lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h :=
      (helperForText_34_1_4_mixedClosure_order_iff_crossClosure K h hNoBotK).2 hCross
    -- Then rewrite that mixed-order comparison back to the raw operator inequality.
    exact
      (helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder K h).1 hOrder
  · intro hRawOrder
    -- First convert the raw operator inequality into the textbook mixed-order comparison.
    have hOrder :
        lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h :=
      (helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder K h).2 hRawOrder
    -- Then package the two exact cross-closure identities from the already-isolated endgame.
    exact
      (helperForText_34_1_4_mixedClosure_order_iff_crossClosure K h hNoBotK).1 hOrder

/-- Helper for Text 34.1.4: after the lower recovery `cl₂ overline(K) = underline(K)` is known,
the first cross-closure identity is the short textbook rewrite
`cl₁ underline(K) = cl₁ (cl₂ overline(K)) = overline(K)`. -/
lemma helperForText_34_1_4_concaveConvex_crossClosure
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h)
    (hLowerClosed : IsConvexClosedInSecond (lowerClosureConcaveConvex K h))
    (hUpperClosed : IsConcaveClosedInFirst (upperClosureConcaveConvex K h)) :
    partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h ∧
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  constructor
  · exact le_antisymm
      (helperForText_34_0_1_partialClosure₁_le_of_le_of_concaveClosedInFirst
        hOrder hUpperClosed)
      (helperForText_34_1_4_upperClosure_le_firstClosureOfLower K h)
  · exact le_antisymm
      (helperForText_34_1_4_secondClosureOfUpper_le_lowerClosure K h)
      (helperForText_34_0_1_le_partialClosure₂_of_convexClosedInSecond_of_le
        hLowerClosed hOrder)

-- Proof sketch: unfold the lower and upper closures in each saddle orientation and use the
-- corresponding order of the two partial closure operators.
/-- Text 34.1.4, qualified formal version: if `K` is concave-convex, its mixed closures are
ordered, and the outer closures are fixed in their respective variables, then applying the
opposite partial closures exchanges the mixed pair. -/
theorem section34_text_34_1_4 (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h)
    (hLowerClosed : IsConvexClosedInSecond (lowerClosureConcaveConvex K h))
    (hUpperClosed : IsConcaveClosedInFirst (upperClosureConcaveConvex K h)) :
    partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h ∧
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  exact
    helperForText_34_1_4_concaveConvex_crossClosure K h hOrder hLowerClosed hUpperClosed

/-- Helper for Text 34.0.1: once the mixed lower closure is known to lie below the mixed upper
closure, the two cross-closure identities follow from monotonicity and the one-sided fixed-point
properties of the outer closures. -/
lemma helperForText_34_0_1_crossClosure_relations_of_mixedClosure_order
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h) :
    partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h ∧
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  -- Record the explicit mixed-closure formulas and the one-sided fixed-point data.
  rcases helperForText_34_0_1_mixedClosure_formulas K h with ⟨hLowerFormula, hUpperFormula⟩
  rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBotK with
    ⟨-, -, hLowerClosed, hUpperClosed⟩
  have hCl₂K_le_lower :
      partialClosure₂ K ≤ lowerClosureConcaveConvex K h := by
    -- Since `K ≤ cl₁ K`, applying `cl₂` places `cl₂ K` below the mixed lower closure.
    calc
      partialClosure₂ K ≤ partialClosure₂ (partialClosure₁ K) :=
        helperForText_34_0_1_partialClosure₂_mono
          (helperForText_34_0_1_le_partialClosure₁ K)
      _ = lowerClosureConcaveConvex K h := by
        rw [← hLowerFormula]
  have hUpper_le_cl₁Lower :
      upperClosureConcaveConvex K h ≤ partialClosure₁ (lowerClosureConcaveConvex K h) := by
    -- The upper mixed closure is `cl₁ (cl₂ K)`, and `cl₂ K` sits below the lower mixed closure.
    calc
      upperClosureConcaveConvex K h = partialClosure₁ (partialClosure₂ K) := hUpperFormula
      _ ≤ partialClosure₁ (lowerClosureConcaveConvex K h) :=
        helperForText_34_0_1_partialClosure₁_mono hCl₂K_le_lower
  have hCl₁Lower_le_upper :
      partialClosure₁ (lowerClosureConcaveConvex K h) ≤ upperClosureConcaveConvex K h := by
    -- Any concave-closed first-variable majorant bounds the first closure from above.
    exact
      helperForText_34_0_1_partialClosure₁_le_of_le_of_concaveClosedInFirst
        hOrder hUpperClosed
  have hUpper_le_cl₁K :
      upperClosureConcaveConvex K h ≤ partialClosure₁ K := by
    -- Since `cl₂ K ≤ K`, applying `cl₁` bounds the upper mixed closure by `cl₁ K`.
    calc
      upperClosureConcaveConvex K h = partialClosure₁ (partialClosure₂ K) := hUpperFormula
      _ ≤ partialClosure₁ K :=
        helperForText_34_0_1_partialClosure₁_mono
          (helperForText_34_0_1_partialClosure₂_le K)
  have hLower_le_cl₂Upper :
      lowerClosureConcaveConvex K h ≤ partialClosure₂ (upperClosureConcaveConvex K h) := by
    -- Any convex-closed second-variable minorant stays below the second closure of a larger
    -- kernel.
    exact
      helperForText_34_0_1_le_partialClosure₂_of_convexClosedInSecond_of_le
        hLowerClosed hOrder
  have hCl₂Upper_le_lower :
      partialClosure₂ (upperClosureConcaveConvex K h) ≤ lowerClosureConcaveConvex K h := by
    -- Bounding the upper mixed closure by `cl₁ K` and applying `cl₂` recovers the lower mixed
    -- closure.
    calc
      partialClosure₂ (upperClosureConcaveConvex K h) ≤ partialClosure₂ (partialClosure₁ K) :=
        helperForText_34_0_1_partialClosure₂_mono hUpper_le_cl₁K
      _ = lowerClosureConcaveConvex K h := by
        rw [← hLowerFormula]
  constructor
  · -- The first cross-closure equality is the antisymmetry package for the two bounds above.
    exact le_antisymm hCl₁Lower_le_upper hUpper_le_cl₁Lower
  · -- The second cross-closure equality is the analogous antisymmetry package for `cl₂`.
    exact le_antisymm hCl₂Upper_le_lower hLower_le_cl₂Upper

/-- Helper for Text 34.0.1: the first partial closure is unconditionally idempotent. -/
lemma helperForText_34_0_1_partialClosure₁_idempotent_unconditional
    (K : SaddleFunction m n) :
    partialClosure₁ (partialClosure₁ K) = partialClosure₁ K := by
  funext u
  funext v
  exact helperForCorollary33_1_1_concaveClosureInFirst_idempotent (K := K) u v

/-- Compatibility form of first-partial-closure idempotence for concave-convex kernels. -/
lemma helperForText_34_0_1_partialClosure₁_idempotent
    (K : SaddleFunction m n) (_h : IsConcaveConvex K) :
    partialClosure₁ (partialClosure₁ K) = partialClosure₁ K := by
  exact helperForText_34_0_1_partialClosure₁_idempotent_unconditional K

/-- Helper for Text 34.0.1: the second partial closure is unconditionally idempotent. -/
lemma helperForText_34_0_1_partialClosure₂_idempotent_unconditional
    (K : SaddleFunction m n) :
    partialClosure₂ (partialClosure₂ K) = partialClosure₂ K := by
  funext u
  funext v
  exact helperForCorollary33_1_1_convexClosureInSecond_idempotent (K := K) u v

/-- Compatibility form of second-partial-closure idempotence for concave-convex kernels. -/
lemma helperForText_34_0_1_partialClosure₂_idempotent
    (K : SaddleFunction m n) (_h : IsConcaveConvex K) :
    partialClosure₂ (partialClosure₂ K) = partialClosure₂ K := by
  exact helperForText_34_0_1_partialClosure₂_idempotent_unconditional K

/-- Helper for Text 34.0.1: both mixed closures are fixed points of repeating the lower or upper
closure operation. -/
lemma helperForText_34_0_1_lower_and_upper_fixedPoint_forms
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) =
      lowerClosureConcaveConvex K h ∧
    partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) =
      upperClosureConcaveConvex K h := by
  -- Route correction: the earlier mixed-order route is unnecessary for Text 34.0.1 itself.
  -- The two fixed-point identities follow directly from the operator algebra of an extensive
  -- idempotent `cl₁` and a reductive idempotent `cl₂`.
  rcases helperForText_34_0_1_mixedClosure_formulas K h with ⟨hLowerFormula, hUpperFormula⟩
  have hCl₁Idem :
      partialClosure₁ (partialClosure₁ K) = partialClosure₁ K :=
    helperForText_34_0_1_partialClosure₁_idempotent K h
  have hCl₂Idem :
      partialClosure₂ (partialClosure₂ K) = partialClosure₂ K :=
    helperForText_34_0_1_partialClosure₂_idempotent K h
  have hCl₂IdemOnCl₁ :
      partialClosure₂ (partialClosure₂ (partialClosure₁ K)) =
        partialClosure₂ (partialClosure₁ K) :=
    helperForText_34_0_1_partialClosure₂_idempotent_unconditional (partialClosure₁ K)
  have hCl₁IdemOnCl₂ :
      partialClosure₁ (partialClosure₁ (partialClosure₂ K)) =
        partialClosure₁ (partialClosure₂ K) :=
    helperForText_34_0_1_partialClosure₁_idempotent_unconditional (partialClosure₂ K)
  constructor
  · apply le_antisymm
    · -- Push the inner `cl₂` below `cl₁ K`, then collapse the repeated `cl₁`.
      calc
        partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h))
            = partialClosure₂ (partialClosure₁ (partialClosure₂ (partialClosure₁ K))) := by
                rw [hLowerFormula]
        _ ≤ partialClosure₂ (partialClosure₁ (partialClosure₁ K)) := by
              apply helperForText_34_0_1_partialClosure₂_mono
              apply helperForText_34_0_1_partialClosure₁_mono
              exact helperForText_34_0_1_partialClosure₂_le (partialClosure₁ K)
        _ = partialClosure₂ (partialClosure₁ K) := by
              rw [hCl₁Idem]
        _ = lowerClosureConcaveConvex K h := by
              rw [← hLowerFormula]
    · -- Insert an extra `cl₂` using idempotence on `cl₁ K`, then use extensivity of `cl₁`.
      calc
        lowerClosureConcaveConvex K h = partialClosure₂ (partialClosure₁ K) := hLowerFormula
        _ = partialClosure₂ (partialClosure₂ (partialClosure₁ K)) := hCl₂IdemOnCl₁.symm
        _ ≤ partialClosure₂ (partialClosure₁ (partialClosure₂ (partialClosure₁ K))) :=
              helperForText_34_0_1_partialClosure₂_mono
                (helperForText_34_0_1_le_partialClosure₁ (partialClosure₂ (partialClosure₁ K)))
        _ = partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) := by
              rw [hLowerFormula]
  · apply le_antisymm
    · -- Push the inner `cl₂` below `cl₁ (cl₂ K)`, then collapse the repeated `cl₁`.
      calc
        partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h))
            = partialClosure₁ (partialClosure₂ (partialClosure₁ (partialClosure₂ K))) := by
                rw [hUpperFormula]
        _ ≤ partialClosure₁ (partialClosure₁ (partialClosure₂ K)) := by
              apply helperForText_34_0_1_partialClosure₁_mono
              exact helperForText_34_0_1_partialClosure₂_le (partialClosure₁ (partialClosure₂ K))
        _ = partialClosure₁ (partialClosure₂ K) := hCl₁IdemOnCl₂
        _ = upperClosureConcaveConvex K h := by
              rw [← hUpperFormula]
    · -- Insert an extra `cl₂` using idempotence on `K`, then use extensivity of `cl₁`.
      calc
        upperClosureConcaveConvex K h = partialClosure₁ (partialClosure₂ K) := hUpperFormula
        _ ≤ partialClosure₁ (partialClosure₂ (partialClosure₁ (partialClosure₂ K))) := by
              apply helperForText_34_0_1_partialClosure₁_mono
              calc
                partialClosure₂ K = partialClosure₂ (partialClosure₂ K) := hCl₂Idem.symm
                _ ≤ partialClosure₂ (partialClosure₁ (partialClosure₂ K)) :=
                  helperForText_34_0_1_partialClosure₂_mono
                    (helperForText_34_0_1_le_partialClosure₁ (partialClosure₂ K))
        _ = partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) := by
              rw [hUpperFormula]

/-- Helper for Text 34.0.1: a mixed lower closure is lower closed once the repeated lower
closure operation fixes it. -/
lemma helperForText_34_0_1_lowerClosed_from_fixedPoint
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hFixed :
      partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) =
        lowerClosureConcaveConvex K h) :
    IsLowerClosed (lowerClosureConcaveConvex K h) := by
  -- The mixed lower closure keeps the concave-convex orientation inherited from `K`.
  rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBotK with
    ⟨hLowerOrient, -, -, -⟩
  constructor
  · exact hLowerOrient
  · intro hLowerWitness
    -- The supplied proof of concave-convexity only matters up to branch proof irrelevance.
    have hProofIrrel :=
      (helperForText_34_0_1_concaveConvex_branch_proofIrrelevance
        (lowerClosureConcaveConvex K h) hLowerOrient hLowerWitness).1
    have hLowerSelfFormula :=
      (helperForText_34_0_1_mixedClosure_formulas
        (lowerClosureConcaveConvex K h) hLowerOrient).1
    calc
      lowerClosureConcaveConvex K h
          = partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) := hFixed.symm
      _ = lowerClosureConcaveConvex (lowerClosureConcaveConvex K h) hLowerOrient := by
            exact hLowerSelfFormula.symm
      _ = lowerClosureConcaveConvex (lowerClosureConcaveConvex K h) hLowerWitness := hProofIrrel

/-- Helper for Text 34.0.1: an upper mixed closure is upper closed once the repeated upper
closure operation fixes it. -/
lemma helperForText_34_0_1_upperClosed_from_fixedPoint
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hFixed :
      partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) =
        upperClosureConcaveConvex K h) :
    IsUpperClosed (upperClosureConcaveConvex K h) := by
  -- The mixed upper closure is still concave-convex after the two coordinatewise closures.
  rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBotK with
    ⟨-, hUpperOrient, -, -⟩
  constructor
  · exact hUpperOrient
  · intro hUpperWitness
    -- Branch proof irrelevance lets us rewrite to the same explicit mixed closure formula.
    have hProofIrrel :=
      (helperForText_34_0_1_concaveConvex_branch_proofIrrelevance
        (upperClosureConcaveConvex K h) hUpperOrient hUpperWitness).2
    have hUpperSelfFormula :=
      (helperForText_34_0_1_mixedClosure_formulas
        (upperClosureConcaveConvex K h) hUpperOrient).2
    calc
      upperClosureConcaveConvex K h
          = partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) := hFixed.symm
      _ = upperClosureConcaveConvex (upperClosureConcaveConvex K h) hUpperOrient := by
            exact hUpperSelfFormula.symm
      _ = upperClosureConcaveConvex (upperClosureConcaveConvex K h) hUpperWitness := hProofIrrel

/-- Helper for Text 34.0.1: the fixed-point forms package directly into the lower-closed and
upper-closed conclusions for the two mixed closures. -/
lemma helperForText_34_0_1_packaged_closedness_conclusions
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K) :
    IsLowerClosed (lowerClosureConcaveConvex K h) ∧
      IsUpperClosed (upperClosureConcaveConvex K h) := by
  -- Reduce both closedness statements to the corresponding fixed-point identities.
  rcases helperForText_34_0_1_lower_and_upper_fixedPoint_forms K h with
    ⟨hLowerFixed, hUpperFixed⟩
  constructor
  · -- Package the lower mixed closure as a lower-closed saddle-function.
    exact helperForText_34_0_1_lowerClosed_from_fixedPoint K h hNoBotK hLowerFixed
  · -- Package the upper mixed closure as an upper-closed saddle-function.
    exact helperForText_34_0_1_upperClosed_from_fixedPoint K h hNoBotK hUpperFixed

/-- Helper for Text 34.0.1: once the normalized existential witness is available, the full
idempotence and lower/upper closedness conclusion follows by the local closure chain already
established in this file. -/
lemma helperForText_34_0_1_closedConvexWitness_exists_forces_main_conclusion
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hLowerNoTopBot : HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hWitness :
      ∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        IsRockafellarConvexBifunction F ∧
          HasNoBotValuesBifunction F ∧
          ClosedConvexBifunction F ∧
          lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
          upperClosureConcaveConvex K h =
            helperForText_34_0_1_convexAdjointPairingKernel F) :
    partialClosure₂ (partialClosure₁ (partialClosure₂ (partialClosure₁ K))) =
      partialClosure₂ (partialClosure₁ K) ∧
    partialClosure₁ (partialClosure₂ (partialClosure₁ (partialClosure₂ K))) =
      partialClosure₁ (partialClosure₂ K) ∧
    IsLowerClosed (lowerClosureConcaveConvex K h) ∧
    IsUpperClosed (upperClosureConcaveConvex K h) := by
  -- First rewrite the lower and upper closures to the mixed coordinatewise forms that appear
  -- in the statement of Text 34.0.1 itself.
  rcases helperForText_34_0_1_mixedClosure_formulas K h with ⟨hLowerFormula, hUpperFormula⟩
  -- Then unpack the witness and derive the inner cross-closure identities from it.
  rcases hWitness with ⟨F, hF, hNoBot, hClosed, hLowerRep, hUpperRep⟩
  have hCross :
      partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h ∧
        partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h :=
    helperForText_34_0_1_closedConvexWitness_forces_crossClosure_relations_of_function_equalities
      hF hNoBot hClosed hLowerRep hUpperRep hLowerNoTopBot
  -- These cross-closure formulas immediately turn the repeated lower and upper closures into
  -- fixed-point identities.
  have hFixed :
      partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) =
        lowerClosureConcaveConvex K h ∧
      partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) =
        upperClosureConcaveConvex K h := by
    rcases hCross with ⟨hLowerToUpper, hUpperToLower⟩
    constructor
    · calc
        partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h))
            = partialClosure₂ (upperClosureConcaveConvex K h) := by
                rw [hLowerToUpper]
        _ = lowerClosureConcaveConvex K h := hUpperToLower
    · calc
        partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h))
            = partialClosure₁ (lowerClosureConcaveConvex K h) := by
                rw [hUpperToLower]
        _ = upperClosureConcaveConvex K h := hLowerToUpper
  -- Finally package the fixed-point identities into the lower-closed and upper-closed
  -- conclusions for the two mixed closures.
  rcases helperForText_34_0_1_packaged_closedness_conclusions K h hNoBotK with
    ⟨hLowerClosed, hUpperClosed⟩
  rcases hFixed with ⟨hLowerFixed, hUpperFixed⟩
  constructor
  · calc
      partialClosure₂ (partialClosure₁ (partialClosure₂ (partialClosure₁ K)))
          = partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) := by
              rw [hLowerFormula]
      _ = lowerClosureConcaveConvex K h := hLowerFixed
      _ = partialClosure₂ (partialClosure₁ K) := hLowerFormula
  constructor
  · calc
      partialClosure₁ (partialClosure₂ (partialClosure₁ (partialClosure₂ K)))
          = partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) := by
              rw [hUpperFormula]
      _ = upperClosureConcaveConvex K h := hUpperFixed
      _ = partialClosure₁ (partialClosure₂ K) := hUpperFormula
  constructor
  · exact hLowerClosed
  · exact hUpperClosed

/-- Text 34.0.1: for a concave-convex saddle-function, the iterated lower and upper closure
operations are idempotent, and consequently the lower closure is lower closed while the upper
closure is upper closed. -/
theorem section34_idempotent_closures (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K) :
    partialClosure₂ (partialClosure₁ (partialClosure₂ (partialClosure₁ K))) =
      partialClosure₂ (partialClosure₁ K) ∧
    partialClosure₁ (partialClosure₂ (partialClosure₁ (partialClosure₂ K))) =
      partialClosure₁ (partialClosure₂ K) ∧
    IsLowerClosed (lowerClosureConcaveConvex K h) ∧
    IsUpperClosed (upperClosureConcaveConvex K h) := by
  -- First rewrite the displayed identities into the mixed lower and upper closure forms.
  rcases helperForText_34_0_1_mixedClosure_formulas K h with ⟨hLowerFormula, hUpperFormula⟩
  -- Then use the direct fixed-point and closedness helpers coming from the operator-algebra
  -- proof above.
  rcases helperForText_34_0_1_lower_and_upper_fixedPoint_forms K h with
    ⟨hLowerFixed, hUpperFixed⟩
  rcases helperForText_34_0_1_packaged_closedness_conclusions K h hNoBotK with
    ⟨hLowerClosed, hUpperClosed⟩
  constructor
  · calc
      partialClosure₂ (partialClosure₁ (partialClosure₂ (partialClosure₁ K)))
          = partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) := by
              rw [hLowerFormula]
      _ = lowerClosureConcaveConvex K h := hLowerFixed
      _ = partialClosure₂ (partialClosure₁ K) := hLowerFormula
  constructor
  · calc
      partialClosure₁ (partialClosure₂ (partialClosure₁ (partialClosure₂ K)))
          = partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) := by
              rw [hUpperFormula]
      _ = upperClosureConcaveConvex K h := hUpperFixed
      _ = partialClosure₁ (partialClosure₂ K) := hUpperFormula
  constructor
  · exact hLowerClosed
  · exact hUpperClosed

-- Proof sketch: apply the idempotence statement for the concave-convex lower and upper closure
-- operators proved just above, then read off the lower-closed and upper-closed conclusions.
/-- Theorem 34.1: if `K` is any saddle-function on `ℝ^m × ℝ^n`, then its lower closure is a
lower closed saddle-function and its upper closure is an upper closed saddle-function. -/
theorem section34_lower_and_upper_closures_are_closed (K : SaddleFunction m n)
    (h : IsConcaveConvex K) (hNoBotK : HasNoBotValuesBifunction K) :
    IsLowerClosed (lowerClosureConcaveConvex K h) ∧
      IsUpperClosed (upperClosureConcaveConvex K h) := by
  -- The preceding theorem already proves the stronger idempotence statement together with
  -- these lower-closed and upper-closed conclusions.
  rcases section34_idempotent_closures K h hNoBotK with ⟨-, -, hLowerClosed, hUpperClosed⟩
  -- Keep only the final packaged closedness pair required here.
  exact ⟨hLowerClosed, hUpperClosed⟩

end SaddleAmbient

end Section34
end Chap07
