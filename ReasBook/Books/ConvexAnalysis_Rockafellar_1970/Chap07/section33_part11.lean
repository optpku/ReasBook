/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part10

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

-- Route correction: Lemma33.0.35 itself is declared later in `section33_part18.lean`, so in
-- the supplied `section33_part11.lean` we stage only the dependency-closed zero-section
-- rewrites that the later proof uses when reducing the translated program to the zero case.
/-- Helper for Lemma33.0.35: evaluating the raw translated-and-tilted bifunction at the zero
primal displacement recovers the tilted primal objective from the textbook statement. -/
lemma helperForLemma33_0_35_rawTranslatedTiltedZeroSection_eq_tiltedObjective
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    (fun y : Fin n → ℝ =>
      (fun v : Fin m → ℝ => fun y : Fin n → ℝ =>
        F (u + v) y - ((dotProduct y xStar : ℝ) : EReal))
        (0 : Fin m → ℝ) y) =
      fun y : Fin n → ℝ => F u y - ((dotProduct y xStar : ℝ) : EReal) := by
  -- Step 1: compare the two frozen-section formulas pointwise.
  funext y
  -- Step 2: the translated parameter collapses because `u + 0 = u`.
  simp

/-- Helper for Lemma33.0.35: the value set of the zero section of the raw translated-and-tilted
bifunction is exactly the tilted primal objective range appearing in the textbook formula. -/
lemma helperForLemma33_0_35_zeroSectionRange_eq_tiltedObjectiveRange
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    Set.range
        (fun y : Fin n → ℝ =>
          (fun v : Fin m → ℝ => fun y : Fin n → ℝ =>
            F (u + v) y - ((dotProduct y xStar : ℝ) : EReal))
            (0 : Fin m → ℝ) y) =
      Set.range (fun y : Fin n → ℝ => F u y - ((dotProduct y xStar : ℝ) : EReal)) := by
  -- Step 1: rewrite the zero section pointwise using the previous helper.
  ext z
  constructor
  · intro hz
    rcases hz with ⟨y, rfl⟩
    -- Step 2: the same witness `y` already lies in the textbook tilted range.
    refine ⟨y, ?_⟩
    simp
  · intro hz
    rcases hz with ⟨y, rfl⟩
    -- Step 3: conversely, the tilted objective value comes from the zero translated section.
    refine ⟨y, ?_⟩
    simp

/-- Helper for Lemma33.0.35: the infimum over the zero section of the raw translated-and-tilted
bifunction is the infimum over the tilted primal objective itself. -/
lemma helperForLemma33_0_35_zeroSection_sInf_eq_tiltedObjective_sInf
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    sInf
        (Set.range
          (fun y : Fin n → ℝ =>
            (fun v : Fin m → ℝ => fun y : Fin n → ℝ =>
              F (u + v) y - ((dotProduct y xStar : ℝ) : EReal))
              (0 : Fin m → ℝ) y)) =
      sInf (Set.range (fun y : Fin n → ℝ => F u y - ((dotProduct y xStar : ℝ) : EReal))) := by
  -- Step 1: first identify the two displayed value sets.
  have hRange :
      Set.range
          (fun y : Fin n → ℝ =>
            (fun v : Fin m → ℝ => fun y : Fin n → ℝ =>
              F (u + v) y - ((dotProduct y xStar : ℝ) : EReal))
              (0 : Fin m → ℝ) y) =
        Set.range (fun y : Fin n → ℝ => F u y - ((dotProduct y xStar : ℝ) : EReal)) :=
    helperForLemma33_0_35_zeroSectionRange_eq_tiltedObjectiveRange
      (F := F) u xStar
  -- Step 2: apply `sInf` to that set equality.
  exact congrArg sInf hRange

/-- Helper for Lemma33.0.36: if two statements are each equivalent to the same criterion,
then they are equivalent to each other. -/
lemma helperForLemma33_0_36_equivalent_of_sharedCriterion
    {P Q R : Prop}
    (hPR : P ↔ R)
    (hQR : Q ↔ R) :
    P ↔ Q := by
  constructor
  · intro hP
    -- Step 1: pass from `P` to the shared criterion `R`.
    have hR : R := hPR.mp hP
    -- Step 2: use the shared criterion to recover `Q`.
    exact hQR.mpr hR
  · intro hQ
    -- Step 3: run the same argument in the opposite direction.
    have hR : R := hQR.mp hQ
    exact hPR.mpr hR

/-- Helper for Lemma33.0.36: pointwise equivalence to a shared criterion identifies the two
binary predicates themselves. -/
lemma helperForLemma33_0_36_predicateEquality_of_sharedCriterion
    {α : Sort*} {β : Sort*}
    {P Q R : α → β → Prop}
    (hPR : ∀ a b, P a b ↔ R a b)
    (hQR : ∀ a b, Q a b ↔ R a b) :
    P = Q := by
  -- Step 1: use function extensionality to reduce predicate equality to pointwise
  -- propositional equality.
  funext a b
  -- Step 2: at each parameter pair, the two propositions are equivalent through the same
  -- shared criterion.
  apply propext
  exact helperForLemma33_0_36_equivalent_of_sharedCriterion (hPR a b) (hQR a b)

/-- Helper for Lemma33.0.36: pointwise equivalences to a shared criterion compose into a
pointwise equivalence. -/
lemma helperForLemma33_0_36_pointwiseEquivalent_of_sharedCriterion
    {α : Sort*} {β : Sort*}
    {P Q R : α → β → Prop}
    (hPR : ∀ a b, P a b ↔ R a b)
    (hQR : ∀ a b, Q a b ↔ R a b) :
    ∀ a b, P a b ↔ Q a b := by
  -- Route correction: the main declaration for Lemma33.0.36 is split into `section33_part18`,
  -- so this earlier part packages the dependency-closed logical composition step that the later
  -- theorem will reuse pointwise in `(u, xStar)`.
  -- Step 1: upgrade the two pointwise shared-criterion equivalences to extensional equality
  -- of the binary predicates.
  have hPQ : P = Q :=
    helperForLemma33_0_36_predicateEquality_of_sharedCriterion hPR hQR
  -- Step 2: rewrite the goal along that predicate equality at the chosen parameters.
  intro a b
  simp [hPQ]

end Section33
end Chap07
