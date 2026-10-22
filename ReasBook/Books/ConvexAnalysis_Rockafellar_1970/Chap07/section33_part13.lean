/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part12

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-- Helper for Lemma33.0.32: evaluating the Section 33 convex pairing at the zero dual vector
recovers the negative of the frozen primal-section infimum. -/
lemma helperForLemma33_0_32_pairingAtZero_eq_neg_sectionInfimum
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) :
    convexBifunctionPairing F u (0 : Fin n → ℝ) =
      -(iInf fun x : Fin n → ℝ => F u x) := by
  -- Step 1: rewrite the Section 33 pairing as the ordinary Fenchel conjugate of the frozen
  -- primal section.
  rw [convexBifunctionPairing, helperForLemma33_0_14_convexConjugate_eq_fenchelConjugate]
  -- Step 2: evaluating the Fenchel conjugate at `0` removes the affine term and leaves the
  -- negative of the section infimum.
  simpa using fenchelConjugate_zero_eq_neg_iInf (n := n) (f := F u)

/-- Helper for Lemma33.0.32: negating the zero-pairing identity gives the primal-section
infimum as the negative of the zero pairing. -/
lemma helperForLemma33_0_32_neg_pairingAtZero_eq_sectionInfimum
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) :
    -convexBifunctionPairing F u (0 : Fin n → ℝ) =
      iInf fun x : Fin n → ℝ => F u x := by
  -- Step 1: start from the zero-pairing formula proved just above.
  have hPairing :
      convexBifunctionPairing F u (0 : Fin n → ℝ) =
        -(iInf fun x : Fin n → ℝ => F u x) :=
    helperForLemma33_0_32_pairingAtZero_eq_neg_sectionInfimum (F := F) u
  -- Step 2: negate both sides so the displayed textbook infimum identity is explicit.
  simpa using congrArg Neg.neg hPairing

/-- Helper for Lemma33.0.32: evaluating the dual Section 33 slice at the zero primal vector
rewrites its supremum as the negative of the corresponding concave conjugate. -/
lemma helperForLemma33_0_32_dualSectionSupremum_eq_neg_concaveConjugateAtZero
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ) :
    sSup (Set.range fun uStar : Fin m → ℝ => convexBifunctionAdjoint F xStar uStar) =
      -concaveConjugate (convexBifunctionAdjoint F xStar) (0 : Fin m → ℝ) := by
  -- Step 1: rewrite the displayed supremum as an indexed supremum over the dual parameter.
  calc
    sSup (Set.range fun uStar : Fin m → ℝ => convexBifunctionAdjoint F xStar uStar)
        = iSup (fun uStar : Fin m → ℝ => convexBifunctionAdjoint F xStar uStar) := by
          rw [sSup_range]
    -- Step 2: convert the indexed supremum to the negative of the corresponding indexed
    -- infimum, matching the zero-value formula for the concave conjugate.
    _ =
        -(iInf fun uStar : Fin m → ℝ =>
            (((uStar ⬝ᵥ (0 : Fin m → ℝ) : ℝ) : EReal) +
              (-convexBifunctionAdjoint F xStar uStar))) := by
          calc
            iSup (fun uStar : Fin m → ℝ => convexBifunctionAdjoint F xStar uStar)
                =
                  iSup (fun uStar : Fin m → ℝ =>
                    -((((uStar ⬝ᵥ (0 : Fin m → ℝ) : ℝ) : EReal) +
                      (-convexBifunctionAdjoint F xStar uStar)))) := by
                    congr with uStar
                    simp
            _ =
                -(iInf fun uStar : Fin m → ℝ =>
                    (((uStar ⬝ᵥ (0 : Fin m → ℝ) : ℝ) : EReal) +
                      (-convexBifunctionAdjoint F xStar uStar))) := by
                    symm
                    exact helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
                      (φ := fun uStar : Fin m → ℝ =>
                        (((uStar ⬝ᵥ (0 : Fin m → ℝ) : ℝ) : EReal) +
                          (-convexBifunctionAdjoint F xStar uStar)))
    -- Step 3: identify that infimum with the Chapter 6 formula for the concave conjugate at
    -- the origin.
    _ = -concaveConjugate (convexBifunctionAdjoint F xStar) (0 : Fin m → ℝ) := by
          rw [← helperForTheorem_6_30_4_concaveConjugate_eq_iInf
            (g := convexBifunctionAdjoint F xStar) (xStar := (0 : Fin m → ℝ))]

/-- Helper for Lemma33.0.32: the primal program value is the negative of the zero pairing with
the frozen primal section. -/
lemma helperForLemma33_0_32_primalValue_eq_neg_pairingAtZero
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) :
    convexProgramAssociatedWith F u =
      -convexBifunctionPairing F u (0 : Fin n → ℝ) := by
  -- Step 1: unfold the primal program value into the infimum of the frozen primal section.
  calc
    convexProgramAssociatedWith F u
        = sInf (Set.range fun x : Fin n → ℝ => F u x) := by
          rfl
    _ = iInf (fun x : Fin n → ℝ => F u x) := by
          rw [sInf_range]
    -- Step 2: substitute the zero-pairing identity proved just above.
    _ = -convexBifunctionPairing F u (0 : Fin n → ℝ) := by
          rw [← helperForLemma33_0_32_neg_pairingAtZero_eq_sectionInfimum (F := F) u]

/-- Helper for Lemma33.0.32: equality of the primal and dual values at the origin is
equivalent to equality of the corresponding zero pairings. -/
lemma helperForLemma33_0_32_zeroValueEquality_iff_zeroPairingEquality
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    convexProgramAssociatedWith F (0 : Fin m → ℝ) =
        sSup (Set.range fun uStar : Fin m → ℝ =>
          convexBifunctionAdjoint F (0 : Fin n → ℝ) uStar) ↔
      convexBifunctionPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
        concaveConjugate (convexBifunctionAdjoint F (0 : Fin n → ℝ)) (0 : Fin m → ℝ) := by
  constructor
  · intro hValue
    -- Step 1: rewrite the value equality using the primal and dual zero identities.
    have hNeg :
        -convexBifunctionPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
          -concaveConjugate (convexBifunctionAdjoint F (0 : Fin n → ℝ)) (0 : Fin m → ℝ) := by
      simpa [
        helperForLemma33_0_32_primalValue_eq_neg_pairingAtZero (F := F) (u := (0 : Fin m → ℝ)),
        helperForLemma33_0_32_dualSectionSupremum_eq_neg_concaveConjugateAtZero
          (F := F) (xStar := (0 : Fin n → ℝ))
      ] using hValue
    -- Step 2: cancel the common negation to recover the pairing equality.
    simpa using congrArg Neg.neg hNeg
  · intro hPairing
    -- Step 1: negate the pairing equality so it matches the value identities at zero.
    have hNeg :
        -convexBifunctionPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
          -concaveConjugate (convexBifunctionAdjoint F (0 : Fin n → ℝ)) (0 : Fin m → ℝ) := by
      exact congrArg Neg.neg hPairing
    -- Step 2: rewrite back to the equality of the primal and dual optimal values.
    simpa [
      helperForLemma33_0_32_primalValue_eq_neg_pairingAtZero (F := F) (u := (0 : Fin m → ℝ)),
      helperForLemma33_0_32_dualSectionSupremum_eq_neg_concaveConjugateAtZero
        (F := F) (xStar := (0 : Fin n → ℝ))
    ] using hNeg

/-- Lemma33.0.32 (Optimal value equality at `0` and pairing equality): the primal value is the
negative of the zero pairing, the dual value is the negative of the zero concave conjugate,
and equality of the two values at the origin is equivalent to equality of those pairings. -/
theorem optimalValueEqualityAtZero_and_pairingEquality
    {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (∀ u : Fin m → ℝ,
        convexProgramAssociatedWith F u =
          -convexBifunctionPairing F u (0 : Fin n → ℝ)) ∧
      (∀ xStar : Fin n → ℝ,
        sSup (Set.range fun uStar : Fin m → ℝ => convexBifunctionAdjoint F xStar uStar) =
          -concaveConjugate (convexBifunctionAdjoint F xStar) (0 : Fin m → ℝ)) ∧
      (convexProgramAssociatedWith F (0 : Fin m → ℝ) =
          sSup (Set.range fun uStar : Fin m → ℝ =>
            convexBifunctionAdjoint F (0 : Fin n → ℝ) uStar) ↔
        convexBifunctionPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
          concaveConjugate (convexBifunctionAdjoint F (0 : Fin n → ℝ)) (0 : Fin m → ℝ)) := by
  constructor
  · intro u
    -- Step 1: this is exactly the primal zero-value identity established just above.
    exact helperForLemma33_0_32_primalValue_eq_neg_pairingAtZero (F := F) u
  constructor
  · intro xStar
    -- Step 2: the dual zero-value identity is the corresponding concave-conjugate formula.
    exact helperForLemma33_0_32_dualSectionSupremum_eq_neg_concaveConjugateAtZero
      (F := F) xStar
  · -- Step 3: specialize both pointwise identities at `0` to obtain the textbook equivalence.
    exact helperForLemma33_0_32_zeroValueEquality_iff_zeroPairingEquality (F := F)

end Section33
end Chap07
