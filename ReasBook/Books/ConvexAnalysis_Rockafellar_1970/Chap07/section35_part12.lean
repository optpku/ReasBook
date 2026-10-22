/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part11

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

-- Proof sketch: apply Theorem 23.4 to the proper convex slice `u₁ ↦ -K u₁ v` at the finite
-- point `u`. The directional derivative of this slice in direction `u'` is
-- `-K'(u, v; u', 0)`, while its subdifferential identifies with the negatives of the first
-- partial subgradients of `K` at `(u, v)`. Rewriting the support-function formula from Theorem
-- 23.4 for this negated slice gives the desired infimum formula.
-- Route correction: the textbook all-finite-points statement is false on the branch
-- `partialSubdifferentialInFirstVariable K u v = ∅`, because the zero-direction derivative
-- infimum is `0` while the pairing infimum is `sInf ∅ = ⊤`. The formalized theorem therefore
-- records the valid nonempty-bounded branch isolated by Theorem 23.4.
/-- Helper for Text 35.6.10: at a finite base point, the zero-direction saddle difference
quotient is constantly `0`, so the corresponding first-variable directional derivative value is
`0`. -/
lemma helperForText_35_6_10_zeroDirectionDerivative_eq_zero
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) :
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 0 L} = 0 := by
  let S : Set EReal := {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 0 L}
  have hQuotEq :
      saddleDirectionalDifferenceQuotientAt K u v 0 0 = fun _ : ℝ => (0 : EReal) := by
    funext t
    -- Zero directions freeze both coordinates, so the quotient reduces to `0 / t`.
    simp [saddleDirectionalDifferenceQuotientAt, EReal.sub_self hFinite.1 hFinite.2]
  have hZeroTendsto :
      Filter.Tendsto
        (saddleDirectionalDifferenceQuotientAt K u v 0 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (0 : EReal)) := by
    -- After the quotient is identified with the constant-zero map, the limit is immediate.
    rw [hQuotEq]
    simp
  have hZeroMem : (0 : EReal) ∈ S := by
    -- The constant-zero quotient gives an actual derivative witness with value `0`.
    exact ⟨hFinite.1, hFinite.2, hZeroTendsto⟩
  have hUnique : ∀ L ∈ S, L = 0 := by
    intro L hL
    rcases hL with ⟨_, _, hLlim⟩
    -- Limits of the same quotient family are unique, so every admissible value is `0`.
    exact tendsto_nhds_unique hLlim hZeroTendsto
  have hS_nonempty : S.Nonempty := ⟨0, hZeroMem⟩
  -- The derivative-value set is a singleton up to equality, so its infimum is `0`.
  refine le_antisymm ?_ ?_
  · exact sInf_le hZeroMem
  · exact le_csInf hS_nonempty (by intro L hL; rw [hUnique L hL])

/-- Helper for Text 35.6.10: if the first partial subdifferential is empty, then the infimum of
its first-variable pairing image is `⊤` because the image set itself is empty. -/
lemma helperForText_35_6_10_pairingInf_eq_top_of_empty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (u' : Fin m → ℝ)
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    sInf
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v) = ⊤ := by
  -- Once the partial subdifferential is empty, the pairing image is empty as well.
  simp [hpartialEmpty]

/-- Helper for Text 35.6.10: if the first partial subdifferential is nonempty, then the
pairing-infimum cannot be `⊤` because the image set contains a genuine real value. -/
lemma helperForText_35_6_10_pairingInf_ne_top_of_nonempty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (u' : Fin m → ℝ)
    (hpartial : Set.Nonempty (partialSubdifferentialInFirstVariable K u v)) :
    sInf
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v) ≠ (⊤ : EReal) := by
  rcases hpartial with ⟨uStar, huStar⟩
  have hmem :
      (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal) ∈
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v) := by
    -- `uStar` itself witnesses membership in the image set.
    refine ⟨uStar, huStar, rfl⟩
  intro hInfTop
  have hle :
      (⊤ : EReal) ≤ (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal) := by
    -- The infimum is always below every element of the set; rewriting with `hInfTop` forces
    -- the top element to be below this real value.
    simpa [hInfTop] using (sInf_le hmem)
  have hEqTop :
      (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal) = (⊤ : EReal) :=
    top_le_iff.1 hle
  -- Coercions from `ℝ` never land in `⊤`.
  have hNeTop :
      (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal) ≠ (⊤ : EReal) := by
    simp
  exact hNeTop hEqTop

/-- Helper for Text 35.6.10: the pairing-infimum equals `⊤` if and only if the first partial
subdifferential is empty, matching the textbook convention `inf ∅ = +∞`. -/
lemma helperForText_35_6_10_pairingInf_eq_top_iff_partialFirst_empty
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (u' : Fin m → ℝ) :
    (sInf
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v) = (⊤ : EReal)) ↔
      partialSubdifferentialInFirstVariable K u v = ∅ := by
  constructor
  · intro hInfTop
    -- If the infimum is `⊤`, the image set cannot contain any real point, hence must be empty.
    by_contra hne
    have hpartial :
        Set.Nonempty (partialSubdifferentialInFirstVariable K u v) :=
      Set.nonempty_iff_ne_empty.2 hne
    exact
      helperForText_35_6_10_pairingInf_ne_top_of_nonempty_partialFirst
        (K := K) (u := u) (v := v) u' hpartial hInfTop
  · intro hEmpty
    -- Conversely, if the partial subdifferential is empty, the pairing image is empty and its
    -- infimum is `⊤ = sInf ∅`.
    exact
      helperForText_35_6_10_pairingInf_eq_top_of_empty_partialFirst
        (K := K) (u := u) (v := v) u' hEmpty

/-- Helper for Text 35.6.10: on the empty-first-partial branch, the zero-direction derivative
infimum is `0` while the corresponding pairing infimum is `⊤`. -/
lemma helperForText_35_6_10_zeroDirectionValues_of_empty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 0 L} = 0 ∧
      sInf
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * (0 : Fin m → ℝ) i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v) = ⊤ := by
  constructor
  · -- The zero-direction quotient is constant, so its derivative infimum is exactly `0`.
    exact
      helperForText_35_6_10_zeroDirectionDerivative_eq_zero
        (K := K) (u := u) (v := v) hFinite
  · -- Emptiness of `∂₁ K(u, v)` forces the zero-direction pairing image to be empty as well.
    exact
      helperForText_35_6_10_pairingInf_eq_top_of_empty_partialFirst
        (K := K) (u := u) (v := v) (u' := 0) hpartialEmpty

/-- Helper for Text 35.6.10: the claimed infimum formula already fails in the zero direction on
the branch where the first partial subdifferential is empty. -/
lemma helperForText_35_6_10_zeroDirection_formula_false_of_empty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 0 L} ≠
      sInf
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * (0 : Fin m → ℝ) i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v) := by
  rcases
      helperForText_35_6_10_zeroDirectionValues_of_empty_partialFirst
        (K := K) (u := u) (v := v) hFinite hpartialEmpty with
    ⟨hLeft, hRight⟩
  -- The empty-partial obstruction is the explicit mismatch `0 ≠ ⊤` in the zero direction.
  rw [hLeft, hRight]
  simp

/-- Helper for Text 35.6.10: if the zero-direction infimum identity held at a finite base point,
then the first partial subdifferential could not be empty. -/
lemma helperForText_35_6_10_zeroDirectionFormula_forces_nonempty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFormula :
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 0 L} =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * (0 : Fin m → ℝ) i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v)) :
    Set.Nonempty (partialSubdifferentialInFirstVariable K u v) := by
  by_contra hPartialNonempty
  -- Convert the negated nonemptiness statement into the empty-set branch of the counterexample.
  rw [Set.not_nonempty_iff_eq_empty] at hPartialNonempty
  -- The earlier zero-direction obstruction now contradicts the asserted formula.
  exact
    (helperForText_35_6_10_zeroDirection_formula_false_of_empty_partialFirst
      (K := K) (u := u) (v := v) hFinite hPartialNonempty) hFormula

/-- Helper for Text 35.6.10: at a finite base point, the zero-direction infimum formula holds
exactly when the first partial subdifferential is nonempty. -/
lemma helperForText_35_6_10_zeroDirectionFormula_iff_nonempty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) :
    (sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 0 L} =
      sInf
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * (0 : Fin m → ℝ) i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v)) ↔
      Set.Nonempty (partialSubdifferentialInFirstVariable K u v) := by
  constructor
  · intro hFormula
    -- The previously isolated counterexample already proves the forward implication.
    exact
      helperForText_35_6_10_zeroDirectionFormula_forces_nonempty_partialFirst
        (K := K) (u := u) (v := v) hFinite hFormula
  · rintro ⟨uStar0, huStar0⟩
    -- The left-hand side is the zero directional derivative value.
    rw [helperForText_35_6_10_zeroDirectionDerivative_eq_zero
      (K := K) (u := u) (v := v) hFinite]
    have hPairingImage :
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * (0 : Fin m → ℝ) i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v) = ({0} : Set EReal) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨uStar, huStar, rfl⟩
        -- Pairing any first subgradient with the zero direction gives `0`.
        simp
      · intro hz
        have hz0 : z = 0 := by
          simpa using hz
        -- Nonemptiness supplies a witness whose zero pairing realizes the singleton image.
        refine ⟨uStar0, huStar0, ?_⟩
        rw [hz0]
        simp
    -- The right-hand side is the infimum of the singleton `{0}`.
    rw [hPairingImage]
    simp

/-- Helper for Text 35.6.10: on the branch where `∂₁ K(u, v)` is not simultaneously nonempty and
bounded, the zero-direction identity survives exactly in the nonempty-unbounded case. -/
lemma helperForText_35_6_10_zeroDirectionFormula_on_badBranch_iff_nonempty_unbounded_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hBad :
      ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v))) :
    (sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 0 L} =
      sInf
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * (0 : Fin m → ℝ) i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v)) ↔
      Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
        ¬ Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v) := by
  constructor
  · intro hFormula
    -- The zero-direction identity still forces nonemptiness of `∂₁ K(u, v)`.
    have hNonempty :
        Set.Nonempty (partialSubdifferentialInFirstVariable K u v) :=
      helperForText_35_6_10_zeroDirectionFormula_forces_nonempty_partialFirst
        (K := K) (u := u) (v := v) hFinite hFormula
    refine ⟨hNonempty, ?_⟩
    -- Since the branch hypothesis forbids the good case, boundedness is the only remaining
    -- property that can fail once nonemptiness has been recovered.
    intro hBounded
    exact hBad ⟨hNonempty, hBounded⟩
  · rintro ⟨hNonempty, _⟩
    -- Conversely, the zero-direction formula depends only on nonemptiness, not on boundedness.
    exact
      (helperForText_35_6_10_zeroDirectionFormula_iff_nonempty_partialFirst
        (K := K) (u := u) (v := v) hFinite).2 hNonempty

/-- Helper for Text 35.6.10: if the good nonempty-bounded branch fails, then the only remaining
possibilities are the empty branch and the nonempty-unbounded branch. -/
lemma helperForText_35_6_10_badBranch_cases
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hBad :
      ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v))) :
    partialSubdifferentialInFirstVariable K u v = ∅ ∨
      (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
        ¬ Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)) := by
  by_cases hNonempty : Set.Nonempty (partialSubdifferentialInFirstVariable K u v)
  · right
    -- Once nonemptiness holds on the bad branch, boundedness is exactly the remaining failure.
    refine ⟨hNonempty, ?_⟩
    intro hBounded
    exact hBad ⟨hNonempty, hBounded⟩
  · left
    -- Negating nonemptiness identifies the empty branch.
    exact Set.not_nonempty_iff_eq_empty.mp hNonempty

/-- Helper for Text 35.6.10: on the bad branch, either the zero direction already contradicts the
textbook formula or one is forced into the remaining nonempty-unbounded case. -/
lemma helperForText_35_6_10_zeroDirection_failure_or_nonempty_unbounded_of_badBranch
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hBad :
      ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v))) :
    (sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 0 L} ≠
      sInf
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * (0 : Fin m → ℝ) i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v)) ∨
      (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
        ¬ Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)) := by
  rcases helperForText_35_6_10_badBranch_cases (K := K) (u := u) (v := v) hBad with
    hEmpty | hRemaining
  · left
    -- In the empty branch, the zero-direction contradiction has already been isolated earlier.
    exact
      helperForText_35_6_10_zeroDirection_formula_false_of_empty_partialFirst
        (K := K) (u := u) (v := v) hFinite hEmpty
  · right
    -- Otherwise the bad branch has been reduced to the nonempty-unbounded remainder.
    exact hRemaining

/-- Helper for Text 35.6.10: if `∂₁ K(u, v)` is empty, then the failure of the textbook formula
is witnessed by the concrete first direction `u' = 0`. -/
lemma helperForText_35_6_10_counterexampleDirection_of_empty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    ∃ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} ≠
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v) := by
  -- The zero direction already realizes the contradiction isolated in the previous helper.
  refine ⟨0, ?_⟩
  simpa using
    helperForText_35_6_10_zeroDirection_formula_false_of_empty_partialFirst
      (K := K) (u := u) (v := v) hFinite hpartialEmpty

/-- Helper for Text 35.6.10: if `∂₁ K(u, v)` is empty, then the full textbook formula cannot hold
for every first direction, because the zero direction already contradicts it. -/
lemma helperForText_35_6_10_not_allDirectionsFormula_of_empty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    ¬ ∀ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v) := by
  rcases
      helperForText_35_6_10_counterexampleDirection_of_empty_partialFirst
        (K := K) (u := u) (v := v) hFinite hpartialEmpty with
    ⟨u', hu'⟩
  intro hFormula
  -- The explicit counterexample direction contradicts the asserted all-directions identity.
  exact hu' (hFormula u')

/-- Helper for Text 35.6.10: if `∂₁ K(u, v)` is empty, then the reflected convex slice has a pair
of opposite first directions whose directional-derivative infima are `⊥` and `⊤`. -/
lemma helperForText_35_6_10_exists_bot_and_top_direction_of_empty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    ∃ w : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v w 0 L} = (⊥ : EReal) ∧
        sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v (-w) 0 L} = (⊤ : EReal) := by
  let g : (Fin m → ℝ) → EReal := fun x => -K (-x) v
  have hg : ConvexFunction g := by
    -- The empty-partial obstruction is analyzed on the reflected convex slice from Text 35.6.6.
    simpa [g] using helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hSaddle v
  have hgu : g (-u) ≠ (⊤ : EReal) ∧ g (-u) ≠ (⊥ : EReal) := by
    -- The reflected base point is finite because it still evaluates to `-K u v`.
    simpa [g] using
      helperForText_35_6_6_reflectedFirstSlice_finiteAtBase
        (K := K) (u := u) (v := v) hFinite
  have hsliceNotNonempty : ¬ Set.Nonempty (subdifferentialAt g (-u)) := by
    intro hsliceNonempty
    have hpartialNonempty :
        Set.Nonempty (partialSubdifferentialInFirstVariable K u v) :=
      (helperForText_35_6_6_partialFirst_nonempty_iff_sliceSubdifferential_nonempty
        (K := K) (u := u) (v := v)).2 hsliceNonempty
    -- Empty textbook first partial subdifferential forbids any reflected-slice subgradient.
    rw [hpartialEmpty] at hpartialNonempty
    simp at hpartialNonempty
  rcases
      (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
        g hg (-u) hgu).2 hsliceNotNonempty with
    ⟨⟨w, hwBot, hwTop⟩, _⟩
  have hphiEq :
      firstVariableDirectionalDerivativeFunction K u v =
        upperDirectionalDerivativeAt g (-u) := by
    -- Transport the Chapter 23 directional derivatives back to the textbook first-variable
    -- derivative function.
    simpa [g] using
      helperForText_35_6_6_firstVariableDirectionalDerivative_eq_upperDirectionalDerivative
        (K := K) hSaddle (u := u) (v := v) hFinite
  have hwBot' : firstVariableDirectionalDerivativeFunction K u v w = (⊥ : EReal) := by
    -- Rewrite the reflected-slice `⊥` derivative back to the textbook first-variable notation.
    rw [hphiEq]
    exact hwBot
  have hwTop' : firstVariableDirectionalDerivativeFunction K u v (-w) = (⊤ : EReal) := by
    -- The opposite reflected-slice direction becomes the textbook `⊤` derivative witness.
    rw [hphiEq]
    exact hwTop
  refine ⟨w, ?_, ?_⟩
  · have hEq :
        -sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v (-(-w)) 0 L} = (⊤ : EReal) := by
      -- The `⊤` value of the textbook `φ(-w)` means the raw derivative infimum at `w` is `⊥`.
      simpa [firstVariableDirectionalDerivativeFunction] using hwTop'
    simpa using hEq
  · have hEq :
        -sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v (-w) 0 L} = (⊥ : EReal) := by
      -- Likewise, the `⊥` value of `φ(w)` means the opposite raw infimum is `⊤`.
      simpa [firstVariableDirectionalDerivativeFunction] using hwBot'
    simpa using hEq

/-- Helper for Text 35.6.10: if `∂₁ K(u, v)` is empty, then some first direction has
directional-derivative infimum `⊥` while the pairing infimum over `∂₁ K(u, v)` is `⊤`. -/
lemma helperForText_35_6_10_exists_direction_with_botDerivative_and_topPairing_of_empty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    ∃ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} = (⊥ : EReal) ∧
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v) = (⊤ : EReal) := by
  rcases
      helperForText_35_6_10_exists_bot_and_top_direction_of_empty_partialFirst
        (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty with
    ⟨u', hu'bot, _⟩
  refine ⟨u', hu'bot, ?_⟩
  -- Emptiness of `∂₁ K(u, v)` makes the corresponding pairing image empty in every direction.
  exact
    helperForText_35_6_10_pairingInf_eq_top_of_empty_partialFirst
      (K := K) (u := u) (v := v) (u' := u') hpartialEmpty

/-- Helper for Text 35.6.10: if `∂₁ K(u, v)` is empty, then the textbook formula fails in a first
direction where the directional-derivative infimum is `⊥` while the pairing infimum is still `⊤`.
-/
lemma helperForText_35_6_10_counterexampleDirection_of_empty_partialFirst_via_infiniteDerivative
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    ∃ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} ≠
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v) := by
  rcases
      helperForText_35_6_10_exists_direction_with_botDerivative_and_topPairing_of_empty_partialFirst
        (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty with
    ⟨u', hu'bot, hu'top⟩
  refine ⟨u', ?_⟩
  -- The explicit `⊥` versus `⊤` witness packages the failure of the textbook identity.
  rw [hu'bot, hu'top]
  simp

/-- Helper for Text 35.6.10: if the textbook formula held for every first direction at a finite
base point, then the first partial subdifferential would have to be nonempty. -/
lemma helperForText_35_6_10_allDirectionsFormula_forces_nonempty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFormula : ∀ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v)) :
    Set.Nonempty (partialSubdifferentialInFirstVariable K u v) := by
  by_contra hPartialNonempty
  -- Contrapositively, emptiness of `∂₁ K(u, v)` already kills the full all-directions formula.
  rw [Set.not_nonempty_iff_eq_empty] at hPartialNonempty
  exact
    helperForText_35_6_10_not_allDirectionsFormula_of_empty_partialFirst
      (K := K) (u := u) (v := v) hFinite hPartialNonempty hFormula

/-- Helper for Text 35.6.10: once the remaining nonempty-unbounded branch is excluded, any
all-directions instance of the textbook formula already forces the corrected nonempty-bounded
branch hypothesis. -/
lemma helperForText_35_6_10_allDirectionsFormula_forces_goodBranch_of_no_nonempty_unbounded
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hNoNonemptyUnbounded :
      ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          ¬ Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)))
    (hFormula : ∀ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v)) :
    Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
      Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v) := by
  have hNonempty :
      Set.Nonempty (partialSubdifferentialInFirstVariable K u v) :=
    -- The empty branch is already impossible once the textbook identity is assumed in all
    -- directions.
    helperForText_35_6_10_allDirectionsFormula_forces_nonempty_partialFirst
      (K := K) (u := u) (v := v) hFinite hFormula
  by_cases hBounded : Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)
  · -- If the partial subdifferential is bounded, we are already in the corrected good branch.
    exact ⟨hNonempty, hBounded⟩
  · -- Otherwise we would land in the excluded nonempty-unbounded remainder.
    exact False.elim (hNoNonemptyUnbounded ⟨hNonempty, hBounded⟩)

/-- Helper for Text 35.6.10: on the bad branch, if the remaining nonempty-unbounded alternative
is also excluded, then the full all-directions formula already fails. -/
lemma helperForText_35_6_10_badBranch_without_nonempty_unbounded_forces_formula_failure
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hBad :
      ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)))
    (hNoRemaining :
      ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          ¬ Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v))) :
    ¬ ∀ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v) := by
  rcases helperForText_35_6_10_badBranch_cases (K := K) (u := u) (v := v) hBad with
    hEmpty | hRemaining
  · -- If the bad branch is actually the empty branch, the zero direction already refutes the
    -- all-directions formula.
    exact
      helperForText_35_6_10_not_allDirectionsFormula_of_empty_partialFirst
        (K := K) (u := u) (v := v) hFinite hEmpty
  · -- Otherwise we have reached exactly the nonempty-unbounded alternative that was excluded.
    exact False.elim (hNoRemaining hRemaining)

/-- Helper for Text 35.6.10: if the full all-directions formula held on the bad branch, the bad
branch would necessarily collapse to the nonempty-unbounded alternative. -/
lemma helperForText_35_6_10_badBranch_allDirectionsFormula_forces_nonempty_unbounded
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hBad :
      ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)))
    (hFormula : ∀ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v)) :
    Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
      ¬ Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v) := by
  by_contra hNoRemaining
  -- Excluding the nonempty-unbounded alternative leaves only the empty branch, which the
  -- previous helper already shows is incompatible with the asserted all-directions formula.
  exact
    (helperForText_35_6_10_badBranch_without_nonempty_unbounded_forces_formula_failure
      (K := K) (u := u) (v := v) hFinite hBad hNoRemaining) hFormula

/-- Helper for Text 35.6.10: on the bad branch, either the empty-partial obstruction already
produces a concrete counterexample direction to the textbook formula, or the only remaining case
is the nonempty-unbounded branch. -/
lemma helperForText_35_6_10_badBranch_counterexampleDirection_or_nonempty_unbounded
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hBad :
      ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v))) :
    (∃ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} ≠
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v)) ∨
      (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
        ¬ Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)) := by
  rcases helperForText_35_6_10_badBranch_cases (K := K) (u := u) (v := v) hBad with
    hEmpty | hRemaining
  · left
    -- On the empty branch, the stronger reflected-slice obstruction gives an explicit witness
    -- direction where the derivative infimum and pairing infimum disagree.
    exact
      helperForText_35_6_10_counterexampleDirection_of_empty_partialFirst_via_infiniteDerivative
        (K := K) hSaddle (u := u) (v := v) hFinite hEmpty
  · right
    -- Otherwise the bad branch has already been reduced to the nonempty-unbounded remainder.
    exact hRemaining




end Section35
end Chap07
