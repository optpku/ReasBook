/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part20
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part11

open scoped Topology

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

-- Proof sketch: rewrite both textbook sides into the same separated split-infimum expression.
-- The dual objective `g⋆ - f⋆` becomes one `g`-infimum plus one `f`-infimum, while the
-- concave conjugate of `-p` becomes the same expression after unfolding
-- `translatedDifferenceValueFunction`, pushing the affine term through the inner infimum, and
-- reindexing by `v = x + u`.

/-- Helper for Lemma 31.0.11: the `g`-part of the separated infimum is exactly the concave
Fenchel conjugate. -/
lemma helperForLemma_31_0_11_concaveFenchelConjugate_eq_iInf {n : ℕ}
    (g : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    concaveFenchelConjugate g xStar =
      (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) := by
  -- Rewrite the outer negated `iSup` as an `iInf`, then simplify the sign change pointwise.
  calc
    concaveFenchelConjugate g xStar
        = -fenchelConjugate n (fun v => -(g v)) (-xStar) := by
            simp [concaveFenchelConjugate]
    _ = -iSup (fun v : Fin n → ℝ => (((v ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun y => -(g y)) v)) := by
          rw [fenchelConjugate_eq_iSup]
    _ = iInf (fun v : Fin n → ℝ => -((((v ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun y => -(g y)) v))) := by
          have hsup :
              iSup (fun v : Fin n → ℝ => (((v ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun y => -(g y)) v)) =
                -iInf (fun v : Fin n → ℝ => -((((v ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun y => -(g y)) v))) := by
            simpa using
              (ereal_iSup_neg_eq_neg_iInf
                (g := fun v : Fin n → ℝ =>
                  -((((v ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun y => -(g y)) v))))
          simpa using congrArg Neg.neg hsup
    _ = (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) := by
          refine iInf_congr ?_
          intro v
          calc
            -((((v ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun y => -(g y)) v))
                = -(g v + -(((v ⬝ᵥ xStar : ℝ) : EReal))) := by
                    simp [sub_eq_add_neg, dotProduct_neg, add_comm]
            _ = -g v + (((v ⬝ᵥ xStar : ℝ) : EReal)) := by
                  calc
                    -(g v + -(((v ⬝ᵥ xStar : ℝ) : EReal)))
                        = -g v - (-(((v ⬝ᵥ xStar : ℝ) : EReal))) := by
                            exact EReal.neg_add (Or.inr (by simp)) (Or.inr (by simp))
                    _ = -g v + (((v ⬝ᵥ xStar : ℝ) : EReal)) := by
                          simp [sub_eq_add_neg]
            _ = (((v ⬝ᵥ xStar : ℝ) : EReal) - g v) := by
                  simp [sub_eq_add_neg, add_comm]

/-- Helper for Lemma 31.0.11: the `f`-part of the separated infimum is exactly minus the Fenchel
conjugate. -/
lemma helperForLemma_31_0_11_neg_fenchelConjugate_eq_iInf {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    -fenchelConjugate n f xStar =
      (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) := by
  -- Rewrite the negative of the defining `iSup` as the corresponding indexed infimum.
  calc
    -fenchelConjugate n f xStar
        = -iSup (fun x : Fin n → ℝ => (((x ⬝ᵥ xStar : ℝ) : EReal) - f x)) := by
            rw [fenchelConjugate_eq_iSup]
    _ = iInf (fun x : Fin n → ℝ => -((((x ⬝ᵥ xStar : ℝ) : EReal) - f x))) := by
          have hsup :
              iSup (fun x : Fin n → ℝ => (((x ⬝ᵥ xStar : ℝ) : EReal) - f x)) =
                -iInf (fun x : Fin n → ℝ => -((((x ⬝ᵥ xStar : ℝ) : EReal) - f x))) := by
            simpa using
              (ereal_iSup_neg_eq_neg_iInf
                (g := fun x : Fin n → ℝ => -((((x ⬝ᵥ xStar : ℝ) : EReal) - f x))))
          simpa using congrArg Neg.neg hsup
    _ = (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) := by
          refine iInf_congr ?_
          intro x
          calc
            -((((x ⬝ᵥ xStar : ℝ) : EReal) - f x))
                = -(-f x + (((x ⬝ᵥ xStar : ℝ) : EReal))) := by
                    simp [sub_eq_add_neg, add_comm]
            _ = f x + -(((x ⬝ᵥ xStar : ℝ) : EReal)) := by
                  calc
                    -(-f x + (((x ⬝ᵥ xStar : ℝ) : EReal)))
                        = -(-f x) - (((x ⬝ᵥ xStar : ℝ) : EReal)) := by
                            exact EReal.neg_add (Or.inr (by simp)) (Or.inr (by simp))
                    _ = f x + -(((x ⬝ᵥ xStar : ℝ) : EReal)) := by
                          simp [sub_eq_add_neg]
            _ = f x - (((x ⬝ᵥ xStar : ℝ) : EReal)) := by
                  simp [sub_eq_add_neg]

/-- Helper for Lemma 31.0.11: unfolding the concave conjugate of the negated translated value
function yields the nested infimum over translations and primal variables. -/
lemma helperForLemma_31_0_11_rhs_eq_iInf_u_iInf_x {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    concaveFenchelConjugate (fun u => -(translatedDifferenceValueFunction f g u)) xStar =
      (⨅ u : Fin n → ℝ, ⨅ x : Fin n → ℝ,
        ((((u ⬝ᵥ xStar : ℝ) : EReal)) + (f x - g (x + u)))) := by
  -- Unfold `(-p)^*`, convert the resulting `iSup` to an `iInf`, and then push the finite affine
  -- term through the inner infimum over `x`.
  calc
    concaveFenchelConjugate (fun u => -(translatedDifferenceValueFunction f g u)) xStar
        = -fenchelConjugate n (fun u => translatedDifferenceValueFunction f g u) (-xStar) := by
            simp [concaveFenchelConjugate]
    _ = -iSup (fun u : Fin n → ℝ =>
          (((u ⬝ᵥ (-xStar) : ℝ) : EReal) - translatedDifferenceValueFunction f g u)) := by
          rw [fenchelConjugate_eq_iSup]
    _ = iInf (fun u : Fin n → ℝ =>
          -((((u ⬝ᵥ (-xStar) : ℝ) : EReal) - translatedDifferenceValueFunction f g u))) := by
          have hsup :
              iSup (fun u : Fin n → ℝ =>
                (((u ⬝ᵥ (-xStar) : ℝ) : EReal) - translatedDifferenceValueFunction f g u)) =
                -iInf (fun u : Fin n → ℝ =>
                  -((((u ⬝ᵥ (-xStar) : ℝ) : EReal) - translatedDifferenceValueFunction f g u))) := by
            simpa using
              (ereal_iSup_neg_eq_neg_iInf
                (g := fun u : Fin n → ℝ =>
                  -((((u ⬝ᵥ (-xStar) : ℝ) : EReal) - translatedDifferenceValueFunction f g u))))
          simpa using congrArg Neg.neg hsup
    _ = iInf (fun u : Fin n → ℝ =>
          (((u ⬝ᵥ xStar : ℝ) : EReal) + translatedDifferenceValueFunction f g u)) := by
          refine iInf_congr ?_
          intro u
          calc
            -((((u ⬝ᵥ (-xStar) : ℝ) : EReal) - translatedDifferenceValueFunction f g u))
                = -(-translatedDifferenceValueFunction f g u + -(((u ⬝ᵥ xStar : ℝ) : EReal))) := by
                    simp [sub_eq_add_neg, dotProduct_neg, add_comm]
            _ = translatedDifferenceValueFunction f g u + (((u ⬝ᵥ xStar : ℝ) : EReal)) := by
                  calc
                    -(-translatedDifferenceValueFunction f g u + -(((u ⬝ᵥ xStar : ℝ) : EReal)))
                        = -(-translatedDifferenceValueFunction f g u) -
                            (-(((u ⬝ᵥ xStar : ℝ) : EReal))) := by
                              exact EReal.neg_add (Or.inr (by simp)) (Or.inr (by simp))
                    _ = translatedDifferenceValueFunction f g u + (((u ⬝ᵥ xStar : ℝ) : EReal)) := by
                          simp [sub_eq_add_neg]
            _ = (((u ⬝ᵥ xStar : ℝ) : EReal) + translatedDifferenceValueFunction f g u) := by
                  simp [add_comm]
    _ = iInf (fun u : Fin n → ℝ =>
          (((u ⬝ᵥ xStar : ℝ) : EReal) + iInf (fun x : Fin n → ℝ => f x - g (x + u)))) := by
          simp [translatedDifferenceValueFunction, functionInfimumEReal]
    _ = (⨅ u : Fin n → ℝ, ⨅ x : Fin n → ℝ,
          ((((u ⬝ᵥ xStar : ℝ) : EReal)) + (f x - g (x + u)))) := by
          refine iInf_congr ?_
          intro u
          simpa using
            (helperForTheorem_6_30_15_real_add_iInf
              (c := (u ⬝ᵥ xStar : ℝ))
              (f := fun x : Fin n → ℝ => f x - g (x + u)))

/-- Helper for Lemma 31.0.11: the translated pairing `(v - x) · x⋆` separates into the `v`
term and the negated `x`-term. -/
lemma helperForLemma_31_0_11_sub_dot_eq_add_negDot {n : ℕ}
    (xStar v x : Fin n → ℝ) :
    ((v - x) ⬝ᵥ xStar : ℝ) = (v ⬝ᵥ xStar : ℝ) + (x ⬝ᵥ (-xStar) : ℝ) := by
  -- Expand the subtraction inside the dot product and rewrite the second summand with `-x⋆`.
  simp [dotProduct_neg, sub_eq_add_neg]

/-- Helper for Lemma 31.0.11: after the substitution `v = x + u`, the translated integrand
splits into the `v`-term and the `x`-term used in the separated infimum formula. -/
lemma helperForLemma_31_0_11_changeVariables_integrand_eq_split {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (xStar v x : Fin n → ℝ) :
    ((((v - x) ⬝ᵥ xStar : ℝ) : EReal) + (f x - g v)) =
      ((((v ⬝ᵥ xStar : ℝ) : EReal) - g v) + (f x - (((x ⬝ᵥ xStar : ℝ) : EReal)))) := by
  -- First split the translated pairing into the same two affine blocks used by the textbook.
  rw [helperForLemma_31_0_11_sub_dot_eq_add_negDot xStar v x]
  -- Reassociate the extended-real sum into the same `g`-block plus `f`-block used later.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 31.0.11: the substitution `(u, x) ↦ (x + u, x)` reindexes the translated
infimum into the `(v - x, x)` form used in the split-infimum argument. -/
lemma helperForLemma_31_0_11_reindexTranslatedInfimum {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    (⨅ u : Fin n → ℝ, ⨅ x : Fin n → ℝ,
      ((((u ⬝ᵥ xStar : ℝ) : EReal)) + (f x - g (x + u)))) =
      (⨅ q : (Fin n → ℝ) × (Fin n → ℝ),
        ((((q.1 - q.2) ⬝ᵥ xStar : ℝ) : EReal) + (f q.2 - g q.1))) := by
  let e : ((Fin n → ℝ) × (Fin n → ℝ)) ≃ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    { toFun := fun p => (p.2 + p.1, p.2)
      invFun := fun q => (q.1 - q.2, q.2)
      left_inv := by
        intro p
        ext i <;> simp [sub_eq_add_neg]
      right_inv := by
        intro q
        ext i <;> simp [sub_eq_add_neg] }
  -- First bundle the iterated infimum into a product-indexed infimum.
  calc
    (⨅ u : Fin n → ℝ, ⨅ x : Fin n → ℝ,
        ((((u ⬝ᵥ xStar : ℝ) : EReal)) + (f x - g (x + u))))
        = (⨅ p : (Fin n → ℝ) × (Fin n → ℝ),
            ((((p.1 ⬝ᵥ xStar : ℝ) : EReal)) + (f p.2 - g (p.2 + p.1)))) := by
              rw [iInf_prod']
    _ = (⨅ q : (Fin n → ℝ) × (Fin n → ℝ),
          ((((q.1 - q.2) ⬝ᵥ xStar : ℝ) : EReal) + (f q.2 - g q.1))) := by
          -- Then reindex by the explicit equivalence implementing `v = x + u`.
          refine Equiv.iInf_congr e ?_
          intro p
          simp [e, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 31.0.11: changing variables from `(u, x)` to `(v, x)` separates the two
independent infimum factors. -/
lemma helperForLemma_31_0_11_changeVariables_split_iInf {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (xStar : Fin n → ℝ) :
    (⨅ u : Fin n → ℝ, ⨅ x : Fin n → ℝ,
      ((((u ⬝ᵥ xStar : ℝ) : EReal)) + (f x - g (x + u)))) =
      (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) +
        (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) := by
  let F : (Fin n → ℝ) → EReal := fun v => (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)
  let G : (Fin n → ℝ) → EReal := fun x => f x - (((x ⬝ᵥ xStar : ℝ) : EReal))
  have hF : ∃ x0 : Fin n → ℝ, G x0 < ⊤ := by
    -- Properness of `f` supplies one point with finite value, and subtracting a real keeps the
    -- result finite.
    rcases hf.2.1 with ⟨⟨x0, μ⟩, hx0μ⟩
    have hfx_le : f x0 ≤ (μ : EReal) := (mem_epigraph_univ_iff).1 hx0μ
    have hfx_lt_top : f x0 < (⊤ : EReal) := lt_of_le_of_lt hfx_le (by simp)
    refine ⟨x0, ?_⟩
    have hfinite : -((((x0 ⬝ᵥ xStar : ℝ) : EReal))) < (⊤ : EReal) := by
      exact lt_of_le_of_ne le_top (by simp)
    simpa [G, sub_eq_add_neg] using
      (EReal.add_lt_top (ne_of_lt hfx_lt_top) (ne_of_lt hfinite))
  have hG : ∃ v0 : Fin n → ℝ, F v0 < ⊤ := by
    -- Properness of `-g` gives one point where the `g`-term is finite from above.
    rcases hg.2.1 with ⟨⟨v0, μ⟩, hv0μ⟩
    have hnegG_le : -(g v0) ≤ (μ : EReal) := (mem_epigraph_univ_iff).1 hv0μ
    have hnegG_lt_top : -(g v0) < (⊤ : EReal) := lt_of_le_of_lt hnegG_le (by simp)
    refine ⟨v0, ?_⟩
    simpa [F, sub_eq_add_neg, add_comm] using
      (EReal.add_lt_top (EReal.coe_ne_top _) (ne_of_lt hnegG_lt_top))
  -- Reindex by `v = x + u`, rewrite the integrand as a separable sum, and invoke the Section 30
  -- product-infimum splitting lemma.
  calc
    (⨅ u : Fin n → ℝ, ⨅ x : Fin n → ℝ,
        ((((u ⬝ᵥ xStar : ℝ) : EReal)) + (f x - g (x + u))))
        = (⨅ q : (Fin n → ℝ) × (Fin n → ℝ),
          ((((q.1 - q.2) ⬝ᵥ xStar : ℝ) : EReal) + (f q.2 - g q.1))) := by
          exact helperForLemma_31_0_11_reindexTranslatedInfimum f g xStar
    _ = (⨅ q : (Fin n → ℝ) × (Fin n → ℝ), F q.1 + G q.2) := by
          refine iInf_congr ?_
          intro q
          -- The reindexed integrand is exactly the separated `g`-block plus `f`-block.
          simpa [F, G] using
            helperForLemma_31_0_11_changeVariables_integrand_eq_split f g xStar q.1 q.2
    _ = (⨅ v : Fin n → ℝ, F v) + (⨅ x : Fin n → ℝ, G x) := by
          rw [helperForTheorem_6_30_22_twoFactor_iInf_eq_iInf_add_iInf F G hG hF]
    _ = (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) +
          (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) := by
          simp [F, G, add_comm]

/-- Helper for Lemma 31.0.11: the dual objective itself already matches the separated
`f`-infimum plus `g`-infimum form used in the textbook computation. -/
lemma helperForLemma_31_0_11_dualObjective_eq_split_iInf {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    fenchelDualObjective f g xStar =
      (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) +
        (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) := by
  -- Rewrite `g⋆ - f⋆` as `g⋆ + (-f⋆)` so each summand can be converted to the indexed infimum
  -- that appears in the textbook change-of-variables argument.
  calc
    fenchelDualObjective f g xStar
        = concaveFenchelConjugate g xStar + (-fenchelConjugate n f xStar) := by
            simp [fenchelDualObjective, sub_eq_add_neg]
    _ = (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) +
          (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) := by
            rw [helperForLemma_31_0_11_concaveFenchelConjugate_eq_iInf,
              helperForLemma_31_0_11_neg_fenchelConjugate_eq_iInf]
    _ = (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) +
          (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) := by
            rw [add_comm]

/-- Helper for Lemma 31.0.11: the concave conjugate of the negated translated value function
reduces to the same separated `f`- and `g`-infima as the dual objective. -/
lemma helperForLemma_31_0_11_concaveConjugate_negTranslatedDifference_eq_split_iInf {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (xStar : Fin n → ℝ) :
    concaveFenchelConjugate (fun u => -(translatedDifferenceValueFunction f g u)) xStar =
      (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) +
        (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) := by
  -- First expand `(-p)^*` into the nested infimum over translations and primal variables.
  calc
    concaveFenchelConjugate (fun u => -(translatedDifferenceValueFunction f g u)) xStar
        = (⨅ u : Fin n → ℝ, ⨅ x : Fin n → ℝ,
            ((((u ⬝ᵥ xStar : ℝ) : EReal)) + (f x - g (x + u)))) := by
            exact helperForLemma_31_0_11_rhs_eq_iInf_u_iInf_x f g xStar
    _ = (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) +
          (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) := by
            exact helperForLemma_31_0_11_changeVariables_split_iInf f g hf hg xStar

/-- Helper for Lemma 31.0.11: both textbook sides are identified with the same separated
split-infimum expression. -/
lemma helperForLemma_31_0_11_dualObjective_and_negTranslatedDifference_share_split_iInf
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (xStar : Fin n → ℝ) :
    fenchelDualObjective f g xStar =
        (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) +
          (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) ∧
      concaveFenchelConjugate (fun u => -(translatedDifferenceValueFunction f g u)) xStar =
        (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) +
          (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) := by
  constructor
  · -- The dual objective is already the separated `f`-block plus `g`-block expression.
    exact helperForLemma_31_0_11_dualObjective_eq_split_iInf f g xStar
  · -- The concave conjugate of `-p` reduces to the same separated split-infimum formula.
    exact helperForLemma_31_0_11_concaveConjugate_negTranslatedDifference_eq_split_iInf
      f g hf hg xStar

/-- Helper for Lemma 31.0.11: once both sides are rewritten into the same separated
split-infimum expression, the target identity follows by transitivity. -/
lemma helperForLemma_31_0_11_dualObjective_eq_negTranslatedDifference_conjugate
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (xStar : Fin n → ℝ) :
    fenchelDualObjective f g xStar =
      concaveFenchelConjugate (fun u => -(translatedDifferenceValueFunction f g u)) xStar := by
  -- Read off the two split-infimum descriptions proved just above.
  rcases
      helperForLemma_31_0_11_dualObjective_and_negTranslatedDifference_share_split_iInf
        f g hf hg xStar with ⟨hDual, hConj⟩
  -- Route correction: finish through the shared separated expression rather than reopen the
  -- conjugate definitions.
  calc
    fenchelDualObjective f g xStar
        = (⨅ x : Fin n → ℝ, f x - (((x ⬝ᵥ xStar : ℝ) : EReal))) +
            (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - g v)) := hDual
    _ = concaveFenchelConjugate (fun u => -(translatedDifferenceValueFunction f g u)) xStar := by
          symm
          exact hConj

/-- Lemma 31.0.11 (Dual Objective as the Concave Conjugate of `-p`): in the same Fenchel-duality
setup as Lemma 31.0.10, let `f : ℝ^n → ℝ ∪ {+∞}` be proper convex and let
`g : ℝ^n → ℝ ∪ {-∞}` be proper concave; in this formalization, these hypotheses are recorded by
`hf : ProperConvexFunctionOn Set.univ f` and `hg : ProperConcaveFunctionOn Set.univ g`. Define
`p(u) = inf_x (f x - g (x + u))`, represented here by `translatedDifferenceValueFunction f g`.
Then the dual objective
`xStar ↦ concaveFenchelConjugate g xStar - fenchelConjugate n f xStar`
is the concave conjugate of `-p`; that is, for every `xStar`,
`fenchelDualObjective f g xStar =
  concaveFenchelConjugate (fun u => -(translatedDifferenceValueFunction f g u)) xStar`. -/
lemma fenchelDualObjective_eq_concaveConjugate_neg_translatedDifferenceValueFunction {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    ∀ xStar : Fin n → ℝ,
      fenchelDualObjective f g xStar =
        concaveFenchelConjugate (fun u => -(translatedDifferenceValueFunction f g u)) xStar := by
  intro xStar
  -- Invoke the dedicated final-step helper so the main theorem stays focused on the book's
  -- statement rather than on the shared split-infimum bookkeeping.
  exact helperForLemma_31_0_11_dualObjective_eq_negTranslatedDifference_conjugate
    f g hf hg xStar

-- Proof sketch: treat this as a separate convex/convex translated-value statement rather than as
-- part of the earlier convex/concave perturbation setup. Use the ordinary convex Fenchel
-- conjugates `f⋆` and `g⋆`, identify `sup_{xStar} (g⋆ xStar - f⋆ xStar)` with the dual value
-- attached to the translated function `p(u) = inf_x (f x - g (x + u))`, then use closedness of
-- `f` and `g`, together with the book-level codomain restriction `∀ x, g x ≠ -∞`, and the
-- stated domain qualification to relate that value to
-- `liminf_{u → 0} p(u)`, bound the liminf by `p(0)`, and evaluate `p(0)` as
-- `inf_x (f x - g x)`.
end Section31
end Chap06
