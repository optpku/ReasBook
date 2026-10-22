/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part16

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- Helper for Theorem 6.28.8: the infimum of the block-separable affine perturbation over the
full block vector splits into the finite sum of one-block infima. -/
lemma helperForTheorem_6_28_8_blockAffine_iInf_eq_sum_iInf
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : ∀ k : Fin s, (Fin (n k) → ℝ) → ℝ)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (uStar : Fin m → ℝ) :
    (⨅ x : DecompositionBlockVector s n,
      ∑ k : Fin s,
        ((((f0 k (x k) + dotProduct (x k) ((A k).transpose.mulVec uStar)) : ℝ) : EReal))) =
      ∑ k : Fin s,
        ⨅ xk : Fin (n k) → ℝ,
          ((((f0 k xk + dotProduct xk ((A k).transpose.mulVec uStar)) : ℝ) : EReal)) := by
  classical
  induction s with
  | zero =>
      -- With no blocks there is only one block vector, so both sides are the empty sum.
      simp
  | succ t ih =>
      -- Split a dependent block vector into its tail and last block.
      rw [helperForTheorem_6_28_8_blockVector_iInf_lastCases]
      have hRewrite :
          (⨅ y : DecompositionBlockVector t (fun k => n (Fin.castSucc k)),
            ⨅ ξ : Fin (n (Fin.last t)) → ℝ,
              ∑ k : Fin (t + 1),
                ((((f0 k
                    ((helperForTheorem_6_28_8_lastCasesBlockVector n y ξ) k) +
                    dotProduct
                      ((helperForTheorem_6_28_8_lastCasesBlockVector n y ξ) k)
                      ((A k).transpose.mulVec uStar)) : ℝ) : EReal))) =
            (⨅ y : DecompositionBlockVector t (fun k => n (Fin.castSucc k)),
              ⨅ ξ : Fin (n (Fin.last t)) → ℝ,
                (∑ k : Fin t,
                  ((((f0 (Fin.castSucc k) (y k) +
                      dotProduct (y k) ((A (Fin.castSucc k)).transpose.mulVec uStar)) : ℝ) :
                      EReal))) +
                  ((((f0 (Fin.last t) ξ +
                      dotProduct ξ ((A (Fin.last t)).transpose.mulVec uStar)) : ℝ) :
                      EReal))) := by
        -- Rewrite the `Fin (t + 1)` sum as the tail sum plus the last block.
        apply iInf_congr
        intro y
        apply iInf_congr
        intro ξ
        rw [Fin.sum_univ_castSucc]
        simp [helperForTheorem_6_28_8_lastCasesBlockVector]
      rw [hRewrite]
      have hProd :
          (⨅ y : DecompositionBlockVector t (fun k => n (Fin.castSucc k)),
            ⨅ ξ : Fin (n (Fin.last t)) → ℝ,
              (∑ k : Fin t,
                ((((f0 (Fin.castSucc k) (y k) +
                    dotProduct (y k) ((A (Fin.castSucc k)).transpose.mulVec uStar)) : ℝ) :
                    EReal))) +
                ((((f0 (Fin.last t) ξ +
                    dotProduct ξ ((A (Fin.last t)).transpose.mulVec uStar)) : ℝ) :
                    EReal))) =
            (⨅ p :
              DecompositionBlockVector t (fun k => n (Fin.castSucc k)) ×
                (Fin (n (Fin.last t)) → ℝ),
              (∑ k : Fin t,
                ((((f0 (Fin.castSucc k) (p.1 k) +
                    dotProduct (p.1 k) ((A (Fin.castSucc k)).transpose.mulVec uStar)) : ℝ) :
                    EReal))) +
                ((((f0 (Fin.last t) p.2 +
                    dotProduct p.2 ((A (Fin.last t)).transpose.mulVec uStar)) : ℝ) :
                    EReal))) := by
        -- Repackage the iterated infimum as an infimum over the product type.
        simpa using
          (iInf_prod
            (f := fun p :
              DecompositionBlockVector t (fun k => n (Fin.castSucc k)) ×
                (Fin (n (Fin.last t)) → ℝ) =>
              (∑ k : Fin t,
                ((((f0 (Fin.castSucc k) (p.1 k) +
                    dotProduct (p.1 k) ((A (Fin.castSucc k)).transpose.mulVec uStar)) : ℝ) :
                    EReal))) +
                ((((f0 (Fin.last t) p.2 +
                    dotProduct p.2 ((A (Fin.last t)).transpose.mulVec uStar)) : ℝ) :
                    EReal)))).symm
      rw [hProd]
      have hTailWitness :
          ∃ y : DecompositionBlockVector t (fun k => n (Fin.castSucc k)),
            (∑ k : Fin t,
              ((((f0 (Fin.castSucc k) (y k) +
                  dotProduct (y k) ((A (Fin.castSucc k)).transpose.mulVec uStar)) : ℝ) :
                  EReal))) < ⊤ := by
        -- The zero tail provides a finite witness because every summand is real-valued.
        refine ⟨fun _ _ => 0, ?_⟩
        rw [show
          (∑ k : Fin t,
            ((((f0 (Fin.castSucc k) (fun _ : Fin (n (Fin.castSucc k)) => 0) +
                dotProduct (fun _ : Fin (n (Fin.castSucc k)) => 0)
                  ((A (Fin.castSucc k)).transpose.mulVec uStar)) : ℝ) : EReal))) =
            (((∑ k : Fin t,
              (f0 (Fin.castSucc k) (fun _ : Fin (n (Fin.castSucc k)) => 0) +
                dotProduct (fun _ : Fin (n (Fin.castSucc k)) => 0)
                  ((A (Fin.castSucc k)).transpose.mulVec uStar)) : ℝ)) : EReal) by
          simpa using
            (helperForCorollary_6_28_8_coe_finset_sum (s := Finset.univ)
              (f := fun k : Fin t =>
                f0 (Fin.castSucc k) (fun _ : Fin (n (Fin.castSucc k)) => 0) +
                  dotProduct (fun _ : Fin (n (Fin.castSucc k)) => 0)
                    ((A (Fin.castSucc k)).transpose.mulVec uStar))).symm]
        simp
      have hLastWitness :
          ∃ ξ : Fin (n (Fin.last t)) → ℝ,
            ((((f0 (Fin.last t) ξ +
                dotProduct ξ ((A (Fin.last t)).transpose.mulVec uStar)) : ℝ) : EReal)) < ⊤ := by
        -- The zero last block is again a finite witness.
        refine ⟨fun _ => 0, ?_⟩
        simp
      rw [helperForCorollary_6_28_8_twoFactor_iInf_eq_iInf_add_iInf
        (F := fun y : DecompositionBlockVector t (fun k => n (Fin.castSucc k)) =>
          ∑ k : Fin t,
            ((((f0 (Fin.castSucc k) (y k) +
                dotProduct (y k) ((A (Fin.castSucc k)).transpose.mulVec uStar)) : ℝ) :
                EReal)))
        (G := fun ξ : Fin (n (Fin.last t)) → ℝ =>
          ((((f0 (Fin.last t) ξ +
              dotProduct ξ ((A (Fin.last t)).transpose.mulVec uStar)) : ℝ) : EReal)))
        hTailWitness hLastWitness]
      -- Apply the induction hypothesis to the tail family and rebuild the full finite sum.
      rw [show
          (⨅ y : DecompositionBlockVector t (fun k => n (Fin.castSucc k)),
            ∑ k : Fin t,
              ((((f0 (Fin.castSucc k) (y k) +
                  dotProduct (y k) ((A (Fin.castSucc k)).transpose.mulVec uStar)) : ℝ) :
                  EReal))) =
            ∑ k : Fin t,
              ⨅ xk : Fin (n (Fin.castSucc k)) → ℝ,
                ((((f0 (Fin.castSucc k) xk +
                    dotProduct xk ((A (Fin.castSucc k)).transpose.mulVec uStar)) : ℝ) :
                    EReal)) by
          simpa using
            ih (n := fun k => n (Fin.castSucc k))
              (f0 := fun k => f0 (Fin.castSucc k))
              (A := fun k => A (Fin.castSucc k))]
      simp [Fin.sum_univ_castSucc]

/-- Helper for Theorem 6.28.8: the one-block infimum of `f₀ₖ + ⟪xₖ, Aₖᵀ uStar⟫` is the
negative conjugate value `-f₀ₖ^*(-Aₖᵀ uStar)`. -/
lemma helperForTheorem_6_28_8_blockInf_eq_neg_convexConjugate
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : ∀ k : Fin s, (Fin (n k) → ℝ) → ℝ)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (k : Fin s) (uStar : Fin m → ℝ) :
    sInf (Set.range fun xk : Fin (n k) → ℝ =>
      ((((f0 k xk + dotProduct xk ((A k).transpose.mulVec uStar)) : ℝ) : EReal))) =
      - convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
          (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) := by
  -- Rewrite the block infimum as a negated supremum and recognize the Fenchel integrand.
  rw [sInf_range]
  have hNeg :
      -((⨅ xk : Fin (n k) → ℝ,
          ((((f0 k xk + dotProduct xk ((A k).transpose.mulVec uStar)) : ℝ) : EReal)))) =
        iSup (fun xk : Fin (n k) → ℝ =>
          -(((((f0 k xk + dotProduct xk ((A k).transpose.mulVec uStar)) : ℝ) : EReal)))) := by
    simpa using
      (ereal_iSup_neg_eq_neg_iInf
        (g := fun xk : Fin (n k) → ℝ =>
          ((((f0 k xk + dotProduct xk ((A k).transpose.mulVec uStar)) : ℝ) : EReal)))).symm
  have hIntegrand :
      (fun xk : Fin (n k) → ℝ =>
        -(((((f0 k xk + dotProduct xk ((A k).transpose.mulVec uStar)) : ℝ) : EReal)))) =
        fun xk : Fin (n k) → ℝ =>
          (((xk ⬝ᵥ (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) : ℝ) : EReal)) -
            (f0 k xk : EReal) := by
    funext xk
    have hReal :
        -(f0 k xk + dotProduct xk ((A k).transpose.mulVec uStar)) =
          dotProduct xk (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) - f0 k xk := by
      simp [dotProduct, sub_eq_add_neg]
    have hNegAdd :
        -((((f0 k xk : ℝ) : EReal)) +
            (((dotProduct xk ((A k).transpose.mulVec uStar) : ℝ) : EReal))) =
          -(((dotProduct xk ((A k).transpose.mulVec uStar) : ℝ) : EReal)) +
            -((f0 k xk : EReal)) := by
      calc
        -((((f0 k xk : ℝ) : EReal)) +
            (((dotProduct xk ((A k).transpose.mulVec uStar) : ℝ) : EReal)))
            = -((f0 k xk : EReal)) +
                -(((dotProduct xk ((A k).transpose.mulVec uStar) : ℝ) : EReal)) := by
                  exact
                    EReal.neg_add
                      (x := (f0 k xk : EReal))
                      (y := ((dotProduct xk ((A k).transpose.mulVec uStar) : ℝ) : EReal))
                      (Or.inl (by simp)) (Or.inl (by simp))
        _ = -(((dotProduct xk ((A k).transpose.mulVec uStar) : ℝ) : EReal)) +
              -((f0 k xk : EReal)) := by
              rw [add_comm]
    -- The negated affine perturbation is exactly the Fenchel-conjugate slice at slope `-AₖᵀuStar`.
    calc
      -(((((f0 k xk + dotProduct xk ((A k).transpose.mulVec uStar)) : ℝ) : EReal)))
          = -((((f0 k xk : ℝ) : EReal)) +
              (((dotProduct xk ((A k).transpose.mulVec uStar) : ℝ) : EReal))) := by
                simp [EReal.coe_add]
      _ = -(((dotProduct xk ((A k).transpose.mulVec uStar) : ℝ) : EReal)) +
            -((f0 k xk : EReal)) := hNegAdd
      _ = (((-(f0 k xk + dotProduct xk ((A k).transpose.mulVec uStar)) : ℝ) : EReal)) := by
            simp [EReal.coe_add, add_comm]
      _ = ((((dotProduct xk (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) -
              f0 k xk) : ℝ) : EReal)) := by
            exact congrArg (fun r : ℝ => ((r : ℝ) : EReal)) hReal
      _ = (((xk ⬝ᵥ (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) : ℝ) : EReal)) -
            (f0 k xk : EReal) := by
            simp
  have hSup :
      -((⨅ xk : Fin (n k) → ℝ,
          ((((f0 k xk + dotProduct xk ((A k).transpose.mulVec uStar)) : ℝ) : EReal)))) =
        convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
          (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) := by
    rw [hNeg, convexConjugate, hIntegrand, fenchelConjugate_eq_iSup]
  simpa using congrArg Neg.neg hSup

/-- Helper for Theorem 6.28.8: once the product infimum is separated, the displayed dual-function
formula follows by rewriting every one-block infimum as a conjugate term. -/
lemma helperForTheorem_6_28_8_dualFunction_eq_neg_dotProduct_sub_sumConjugates
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : ∀ k : Fin s, (Fin (n k) → ℝ) → ℝ)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : Fin m → ℝ) :
    ∀ uStar : Fin m → ℝ,
      decompositionDualFunction n f0 A a uStar =
        ((-(dotProduct a uStar) : ℝ) : EReal) -
          ∑ k : Fin s,
            convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
              (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) := by
  intro uStar
  -- Expand the Lagrangian, pull out the finite constant `-⟪a,uStar⟫`, then rewrite each block infimum.
  unfold decompositionDualFunction
  rw [sInf_range]
  have hExpand :
      (⨅ x : DecompositionBlockVector s n, (decompositionLagrangian n f0 A a uStar x : EReal)) =
        (⨅ x : DecompositionBlockVector s n,
          (((-(dotProduct a uStar) : ℝ) : EReal) +
            ∑ k : Fin s,
              ((((f0 k (x k) + dotProduct (x k) ((A k).transpose.mulVec uStar)) : ℝ) :
                EReal)))) := by
    apply iInf_congr
    intro x
    calc
      (decompositionLagrangian n f0 A a uStar x : EReal)
          = (((-(dotProduct a uStar) +
              ∑ k : Fin s,
                (f0 k (x k) + dotProduct (x k) ((A k).transpose.mulVec uStar))) : ℝ) : EReal) := by
                exact_mod_cast
                  helperForTheorem_6_28_8_lagrangian_eq_neg_dotProduct_add_sum_blockDotProducts
                    n f0 A a uStar x
      _ = (((-(dotProduct a uStar) : ℝ) : EReal) +
            ∑ k : Fin s,
              ((((f0 k (x k) + dotProduct (x k) ((A k).transpose.mulVec uStar)) : ℝ) :
                EReal))) := by
              rw [EReal.coe_add,
                helperForCorollary_6_28_8_coe_finset_sum (s := Finset.univ)
                  (f := fun k : Fin s =>
                    f0 k (x k) + dotProduct (x k) ((A k).transpose.mulVec uStar))]
  rw [hExpand]
  rw [helperForCorollary_6_28_8_finiteConstant_add_iInf
    (-(dotProduct a uStar))
    (fun x : DecompositionBlockVector s n =>
      ∑ k : Fin s,
        ((((f0 k (x k) + dotProduct (x k) ((A k).transpose.mulVec uStar)) : ℝ) : EReal)))]
  rw [helperForTheorem_6_28_8_blockAffine_iInf_eq_sum_iInf n f0 A uStar]
  have hRewrite :
      ∑ k : Fin s,
        (⨅ xk : Fin (n k) → ℝ,
          ((((f0 k xk + dotProduct xk ((A k).transpose.mulVec uStar)) : ℝ) : EReal))) =
        ∑ k : Fin s,
          -convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
            (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) := by
    apply Finset.sum_congr rfl
    intro k hk
    simpa [sInf_range] using
      helperForTheorem_6_28_8_blockInf_eq_neg_convexConjugate n f0 A k uStar
  rw [hRewrite]
  have hFenchelNeBot :
      ∀ k : Fin s,
        convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
          (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) ≠ (⊥ : EReal) := by
    intro k
    intro hBot
    let zeroVec : Fin (n k) → ℝ := fun _ => 0
    have hTermLe :
        (((zeroVec ⬝ᵥ (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) : ℝ) : EReal) -
            (f0 k zeroVec : EReal)) ≤
          convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
            (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) := by
      rw [convexConjugate, fenchelConjugate_eq_iSup]
      exact le_iSup_of_le zeroVec le_rfl
    have hTermNeBot :
        (((zeroVec ⬝ᵥ (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) : ℝ) : EReal) -
            (f0 k zeroVec : EReal)) ≠ (⊥ : EReal) := by
      simp [zeroVec, dotProduct]
    have hTermEqBot :
        (((zeroVec ⬝ᵥ (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)) : ℝ) : EReal) -
            (f0 k zeroVec : EReal)) = (⊥ : EReal) := by
      exact le_antisymm (by simpa [hBot] using hTermLe) bot_le
    exact hTermNeBot hTermEqBot
  rw [helperForCorollary_6_28_8_neg_sum_of_ne_bot
    (f := fun k : Fin s =>
      convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
        (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)))
    hFenchelNeBot]
  simp [sub_eq_add_neg]

/-- Helper for Theorem 6.28.8: the explicit penalty is the pointwise negative of the dual
function once the conjugate formula has been established. -/
lemma helperForTheorem_6_28_8_dualPenalty_eq_neg_dualFunction
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : ∀ k : Fin s, (Fin (n k) → ℝ) → ℝ)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : Fin m → ℝ) :
    ∀ uStar : Fin m → ℝ,
      decompositionDualPenalty n f0 A a uStar =
        - decompositionDualFunction n f0 A a uStar := by
  intro uStar
  -- Substitute the explicit conjugate formula for `g` and negate it.
  calc
    decompositionDualPenalty n f0 A a uStar
        = (((dotProduct a uStar : ℝ) : EReal) +
            ∑ k : Fin s,
              convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
                (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j))) := rfl
    _ = -((((-(dotProduct a uStar) : ℝ) : EReal) -
          ∑ k : Fin s,
            convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
              (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)))) := by
            rw [sub_eq_add_neg]
            have hneg :
                -((((-(dotProduct a uStar) : ℝ) : EReal)) +
                    -(∑ k : Fin s,
                      convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
                        (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)))) =
                  -((((-(dotProduct a uStar) : ℝ) : EReal)) : EReal) -
                    (-(∑ k : Fin s,
                      convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
                        (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j)))) := by
              exact EReal.neg_add (x := (((-(dotProduct a uStar) : ℝ) : EReal)))
                (y := -(∑ k : Fin s,
                  convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
                    (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j))))
                (Or.inl (by simp)) (Or.inl (by simp))
            rw [hneg]
            simp [sub_eq_add_neg]
    _ = - decompositionDualFunction n f0 A a uStar := by
          rw [helperForTheorem_6_28_8_dualFunction_eq_neg_dotProduct_sub_sumConjugates
            n f0 A a uStar]

/-- Helper for Theorem 6.28.8: the zero block vector gives a finite witness for the Lagrangian,
so the dual infimum can never equal `⊤`. -/
lemma helperForTheorem_6_28_8_dualFunction_ne_top
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : ∀ k : Fin s, (Fin (n k) → ℝ) → ℝ)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : Fin m → ℝ) (uStar : Fin m → ℝ) :
    decompositionDualFunction n f0 A a uStar ≠ ⊤ := by
  -- The zero block vector gives a finite Lagrangian value, so the infimum cannot be `⊤`.
  let zeroVec : DecompositionBlockVector s n := fun _ _ => 0
  have hle :
      decompositionDualFunction n f0 A a uStar ≤
        (decompositionLagrangian n f0 A a uStar zeroVec : EReal) := by
    unfold decompositionDualFunction
    exact sInf_le ⟨zeroVec, rfl⟩
  have hfinite : (decompositionLagrangian n f0 A a uStar zeroVec : EReal) < ⊤ := by
    simp [zeroVec]
  intro hTop
  have : (⊤ : EReal) ≤ (decompositionLagrangian n f0 A a uStar zeroVec : EReal) := by
    simpa [hTop] using hle
  exact (not_lt_of_ge this) hfinite

/-- Helper for Theorem 6.28.8: every primal block vector bounds the dual function above through
the extended primal objective, which is the weak-duality inequality in this decomposition setup. -/
lemma helperForTheorem_6_28_8_dualFunction_le_extendedPrimalObjective
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : ∀ k : Fin s, (Fin (n k) → ℝ) → ℝ)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : Fin m → ℝ)
    (uStar : Fin m → ℝ) (x : DecompositionBlockVector s n) :
    decompositionDualFunction n f0 A a uStar ≤
      decompositionExtendedPrimalObjective n f0 A a x := by
  -- Compare the dual infimum to the particular primal slice at `x`.
  calc
    decompositionDualFunction n f0 A a uStar
        ≤ (decompositionLagrangian n f0 A a uStar x : EReal) := by
            unfold decompositionDualFunction
            exact sInf_le ⟨x, rfl⟩
    _ ≤ decompositionExtendedPrimalObjective n f0 A a x := by
          by_cases hx : decompositionConstraintValue n A x = a
          · -- On feasible points the Lagrangian equals the primal objective.
            rw [helperForTheorem_6_28_7_lagrangian_eq_primalObjective_of_feasible
              n f0 A a uStar hx]
            simp [decompositionExtendedPrimalObjective, hx]
          · -- On infeasible points the extended objective is `⊤`.
            simp [decompositionExtendedPrimalObjective, hx]

/-- Helper for Theorem 6.28.8: minimizing the explicit penalty is equivalent to maximizing the
dual function, because the penalty is pointwise `-g`. -/
lemma helperForTheorem_6_28_8_dualPenaltyMinimizer_iff_dualFunctionMaximizer
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : ∀ k : Fin s, (Fin (n k) → ℝ) → ℝ)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : Fin m → ℝ) (uStar : Fin m → ℝ) :
    IsDecompositionDualPenaltyMinimizer n f0 A a uStar ↔
      decompositionDualFunction n f0 A a uStar =
        sSup (Set.range fun vStar : Fin m → ℝ =>
          decompositionDualFunction n f0 A a vStar) := by
  constructor
  · intro hMin
    -- A minimizer of `w = -g` makes every competing dual value lie below `g(uStar)`.
    apply le_antisymm
    · exact le_sSup ⟨uStar, rfl⟩
    · refine sSup_le ?_
      rintro _ ⟨vStar, rfl⟩
      have hv := hMin vStar
      rw [helperForTheorem_6_28_8_dualPenalty_eq_neg_dualFunction n f0 A a uStar,
        helperForTheorem_6_28_8_dualPenalty_eq_neg_dualFunction n f0 A a vStar] at hv
      exact EReal.neg_le_neg_iff.mp hv
  · intro hSup vStar
    -- Conversely, a maximizer of `g` minimizes the negated objective.
    rw [helperForTheorem_6_28_8_dualPenalty_eq_neg_dualFunction n f0 A a uStar,
      helperForTheorem_6_28_8_dualPenalty_eq_neg_dualFunction n f0 A a vStar]
    refine EReal.neg_le_neg_iff.mpr ?_
    calc
      decompositionDualFunction n f0 A a vStar
          ≤ sSup (Set.range fun wStar : Fin m → ℝ =>
              decompositionDualFunction n f0 A a wStar) := le_sSup ⟨vStar, rfl⟩
      _ = decompositionDualFunction n f0 A a uStar := hSup.symm

/-- Helper for Theorem 6.28.8: once one Kuhn--Tucker vector exists, the same weak-duality value
identifies Kuhn--Tucker vectors exactly with the dual maximizers. -/
lemma helperForTheorem_6_28_8_isKuhnTuckerVector_iff_dualFunctionMaximizer_of_exists
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : ∀ k : Fin s, (Fin (n k) → ℝ) → ℝ)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : Fin m → ℝ)
    (h_exists : ∃ u : Fin m → ℝ, IsDecompositionKuhnTuckerVector n f0 A a u)
    (uStar : Fin m → ℝ) :
    IsDecompositionKuhnTuckerVector n f0 A a uStar ↔
      decompositionDualFunction n f0 A a uStar =
        sSup (Set.range fun vStar : Fin m → ℝ =>
          decompositionDualFunction n f0 A a vStar) := by
  constructor
  · intro hKT
    rcases h_exists with ⟨u0, hKT0⟩
    rcases hKT with ⟨v, hvDual, hvPrimal⟩
    rcases hKT0 with ⟨v0, hv0Dual, hv0Primal⟩
    have hWeakLower :
        ∀ w : Fin m → ℝ,
          decompositionDualFunction n f0 A a w ≤ (v0 : EReal) := by
      intro w
      calc
        decompositionDualFunction n f0 A a w
            ≤ sInf (Set.range fun x => decompositionExtendedPrimalObjective n f0 A a x) := by
                refine le_sInf ?_
                rintro _ ⟨x, rfl⟩
                exact
                  helperForTheorem_6_28_8_dualFunction_le_extendedPrimalObjective
                    n f0 A a w x
        _ = (v0 : EReal) := hv0Primal
    have hDualEq :
        decompositionDualFunction n f0 A a uStar = (v0 : EReal) := by
      calc
        decompositionDualFunction n f0 A a uStar = (v : EReal) := hvDual
        _ = sInf (Set.range fun x => decompositionExtendedPrimalObjective n f0 A a x) :=
              hvPrimal.symm
        _ = (v0 : EReal) := hv0Primal
    have hSupLe :
        sSup (Set.range fun vStar : Fin m → ℝ => decompositionDualFunction n f0 A a vStar) ≤
          (v0 : EReal) := by
      refine sSup_le ?_
      rintro _ ⟨w, rfl⟩
      exact hWeakLower w
    apply le_antisymm
    · exact le_sSup ⟨uStar, rfl⟩
    · calc
        sSup (Set.range fun vStar : Fin m → ℝ => decompositionDualFunction n f0 A a vStar)
            ≤ (v0 : EReal) := hSupLe
        _ = decompositionDualFunction n f0 A a uStar := hDualEq.symm
  · intro hSup
    rcases h_exists with ⟨u0, hKT0⟩
    rcases hKT0 with ⟨v0, hv0Dual, hv0Primal⟩
    have hWeakLower :
        ∀ w : Fin m → ℝ,
          decompositionDualFunction n f0 A a w ≤ (v0 : EReal) := by
      intro w
      calc
        decompositionDualFunction n f0 A a w
            ≤ sInf (Set.range fun x => decompositionExtendedPrimalObjective n f0 A a x) := by
                refine le_sInf ?_
                rintro _ ⟨x, rfl⟩
                exact
                  helperForTheorem_6_28_8_dualFunction_le_extendedPrimalObjective
                    n f0 A a w x
        _ = (v0 : EReal) := hv0Primal
    have hSupEq :
        sSup (Set.range fun vStar : Fin m → ℝ => decompositionDualFunction n f0 A a vStar) =
          (v0 : EReal) := by
      apply le_antisymm
      · refine sSup_le ?_
        rintro _ ⟨w, rfl⟩
        exact hWeakLower w
      · calc
          (v0 : EReal) = decompositionDualFunction n f0 A a u0 := hv0Dual.symm
          _ ≤ sSup (Set.range fun vStar : Fin m → ℝ =>
                decompositionDualFunction n f0 A a vStar) := le_sSup ⟨u0, rfl⟩
    refine ⟨v0, ?_, hv0Primal⟩
    calc
      decompositionDualFunction n f0 A a uStar =
          sSup (Set.range fun vStar : Fin m → ℝ =>
            decompositionDualFunction n f0 A a vStar) := hSup
      _ = (v0 : EReal) := hSupEq

/-- Helper for Theorem 6.28.8: once the explicit penalty is written as a sum of conjugate terms,
its convexity reduces to Jensen's inequality for each conjugate precomposed with the linear map
`uStar ↦ -AₖᵀuStar`. -/
lemma helperForTheorem_6_28_8_dualPenalty_convexJensen
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : ∀ k : Fin s, (Fin (n k) → ℝ) → ℝ)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : Fin m → ℝ) :
    (∀ k : Fin s, ConvexOn ℝ Set.univ (f0 k)) →
      (∀ (u v : Fin m → ℝ) {α β : ℝ},
        0 ≤ α → 0 ≤ β → α + β = 1 →
          decompositionDualPenalty n f0 A a (α • u + β • v) ≤
            (α : EReal) * decompositionDualPenalty n f0 A a u +
              (β : EReal) * decompositionDualPenalty n f0 A a v) := by
  intro hconvex u v α β hα hβ hαβ
  -- Route correction: instead of summing Jensen inequalities term-by-term in `EReal`, first
  -- obtain Jensen inequalities for each precomposed conjugate term from `ConvexFunctionOn`,
  -- and only then sum those inequalities together with the affine dot-product identity.
  let blockTerm : Fin s → (Fin m → ℝ) → EReal :=
    fun k uStar =>
      convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
        (-Matrix.vecMul uStar (A k))
  have hblock_not_bot :
      ∀ k : Fin s, ∀ uStar : Fin m → ℝ, blockTerm k uStar ≠ (⊥ : EReal) := by
    intro k uStar hBot
    let zeroVec : Fin (n k) → ℝ := fun _ => 0
    have hTermLe :
        (((zeroVec ⬝ᵥ (-Matrix.vecMul uStar (A k)) : ℝ) : EReal) -
            (f0 k zeroVec : EReal)) ≤
          blockTerm k uStar := by
      simpa [blockTerm, convexConjugate, fenchelConjugate_eq_iSup] using
        (le_iSup_of_le zeroVec le_rfl :
          (((zeroVec ⬝ᵥ (-Matrix.vecMul uStar (A k)) : ℝ) : EReal) -
              (f0 k zeroVec : EReal)) ≤
            iSup (fun xk : Fin (n k) → ℝ =>
              (((xk ⬝ᵥ (-Matrix.vecMul uStar (A k)) : ℝ) : EReal)) -
                (f0 k xk : EReal)))
    have hTermNeBot :
        (((zeroVec ⬝ᵥ (-Matrix.vecMul uStar (A k)) : ℝ) : EReal) -
            (f0 k zeroVec : EReal)) ≠ (⊥ : EReal) := by
      simp [zeroVec, dotProduct]
    exact hTermNeBot (le_antisymm (by simpa [hBot] using hTermLe) bot_le)
  have hblock_jensen :
      ∀ k : Fin s,
        blockTerm k (α • u + β • v) ≤
          (α : EReal) * blockTerm k u + (β : EReal) * blockTerm k v := by
    intro k
    have hFenchel :
        ConvexFunctionOn (Set.univ : Set (Fin (n k) → ℝ))
          (convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))) := by
      simpa [ConvexFunction, convexConjugate] using
        (fenchelConjugate_closedConvex (n := n k)
          (f := fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))).2
    have hPrecomp :
        ConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (blockTerm k) := by
      simpa [blockTerm, Function.comp, Matrix.mulVecLin_apply, Pi.smul_apply] using
        convexFunctionOn_precomp_linearMap
          (A := ((-1 : ℝ) • (A k).transpose.mulVecLin))
          (g := convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))) hFenchel
    let w : Fin 2 → ℝ := fun i => if i = 0 then α else β
    let z : Fin 2 → (Fin m → ℝ) := fun i => if i = 0 then u else v
    have hw : ∀ i, 0 ≤ w i := by
      intro i
      fin_cases i <;> simp [w, hα, hβ]
    have hsum : (∑ i : Fin 2, w i) = 1 := by
      simp [w, Fin.sum_univ_two, hαβ]
    have hjensen :=
      (convexFunctionOn_univ_iff_jensen_inequality (f := blockTerm k)
        (hnotbot := hblock_not_bot k)).1 hPrecomp
    have hTwoPoint := hjensen 2 w z hw (by simpa using hsum)
    simpa [blockTerm, w, z, Fin.sum_univ_two] using hTwoPoint
  have hscale_sum :
      ∀ (t : ℝ) (ht : 0 ≤ t) (x : Fin m → ℝ),
        (t : EReal) * ∑ k : Fin s, blockTerm k x =
          ∑ k : Fin s, (t : EReal) * blockTerm k x := by
    intro t ht x
    by_cases ht_zero : t = 0
    · simp [ht_zero]
    · have ht_pos : 0 < t := lt_of_le_of_ne ht (by simpa [eq_comm] using ht_zero)
      refine Finset.induction_on (Finset.univ : Finset (Fin s)) ?_ ?_
      · simp
      · intro a s ha hs
        have hnotbot_a : blockTerm a x ≠ (⊥ : EReal) := hblock_not_bot a x
        have hsum_notbot : s.sum (fun k => blockTerm k x) ≠ (⊥ : EReal) := by
          refine sum_ne_bot_of_ne_bot (s := s) (f := fun k => blockTerm k x) ?_
          intro i hi
          exact hblock_not_bot i x
        have hnotbot_a' : ((t : EReal) * blockTerm a x) ≠ (⊥ : EReal) :=
          ereal_mul_ne_bot_of_pos ht_pos hnotbot_a
        have hnotbot_s' : ((t : EReal) * s.sum (fun k => blockTerm k x)) ≠ (⊥ : EReal) :=
          ereal_mul_ne_bot_of_pos ht_pos hsum_notbot
        have hforb :
            ¬ ERealForbiddenSum ((t : EReal) * blockTerm a x)
              ((t : EReal) * s.sum (fun k => blockTerm k x)) := by
          intro hforb
          rcases hforb with hforb | hforb
          · exact hnotbot_s' hforb.2
          · exact hnotbot_a' hforb.1
        have hdistrib :
            (t : EReal) * (blockTerm a x + s.sum (fun k => blockTerm k x)) =
              (t : EReal) * blockTerm a x + (t : EReal) * s.sum (fun k => blockTerm k x) :=
          ereal_mul_add_of_no_forbidden
            (α := (t : EReal)) (x1 := blockTerm a x)
            (x2 := s.sum (fun k => blockTerm k x)) hforb
        simp [Finset.sum_insert, ha, hs, hdistrib]
  have hsum_jensen :
      ∑ k : Fin s, blockTerm k (α • u + β • v) ≤
        (α : EReal) * ∑ k : Fin s, blockTerm k u +
          (β : EReal) * ∑ k : Fin s, blockTerm k v := by
    -- Summing the blockwise Jensen inequalities yields the Jensen inequality for the block sum.
    calc
      ∑ k : Fin s, blockTerm k (α • u + β • v)
          ≤ ∑ k : Fin s, ((α : EReal) * blockTerm k u + (β : EReal) * blockTerm k v) := by
              refine Finset.sum_le_sum ?_
              intro k hk
              exact hblock_jensen k
      _ = (α : EReal) * ∑ k : Fin s, blockTerm k u +
            (β : EReal) * ∑ k : Fin s, blockTerm k v := by
              rw [Finset.sum_add_distrib, hscale_sum α hα u, hscale_sum β hβ v]
  have hAffineEq :
      (((dotProduct a (α • u + β • v) : ℝ) : EReal)) =
        (α : EReal) * ((dotProduct a u : ℝ) : EReal) +
          (β : EReal) * ((dotProduct a v : ℝ) : EReal) := by
    -- The dot-product contribution is affine, so the two-point inequality is an equality here.
    calc
      (((dotProduct a (α • u + β • v) : ℝ) : EReal))
          = (((α * dotProduct a u + β * dotProduct a v : ℝ) : EReal)) := by
              congr 1
              simp [dotProduct_add, dotProduct_smul]
      _ = (α : EReal) * ((dotProduct a u : ℝ) : EReal) +
            (β : EReal) * ((dotProduct a v : ℝ) : EReal) := by
              simp [EReal.coe_add, EReal.coe_mul]
  have hPenalty_combo :
      decompositionDualPenalty n f0 A a (α • u + β • v) =
        (((dotProduct a (α • u + β • v) : ℝ) : EReal) +
          ∑ k : Fin s, blockTerm k (α • u + β • v)) := by
    unfold decompositionDualPenalty
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k hk
    congr 1
    funext j
    simpa [Matrix.mulVec_transpose]
  have hPenalty_u :
      decompositionDualPenalty n f0 A a u =
        (((dotProduct a u : ℝ) : EReal) + ∑ k : Fin s, blockTerm k u) := by
    unfold decompositionDualPenalty
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k hk
    congr 1
    funext j
    simpa [Matrix.mulVec_transpose]
  have hPenalty_v :
      decompositionDualPenalty n f0 A a v =
        (((dotProduct a v : ℝ) : EReal) + ∑ k : Fin s, blockTerm k v) := by
    unfold decompositionDualPenalty
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k hk
    congr 1
    funext j
    simpa [Matrix.mulVec_transpose]
  -- Combine the affine identity with the blockwise Jensen inequality and fold back to `w`.
  calc
    decompositionDualPenalty n f0 A a (α • u + β • v)
        = (((dotProduct a (α • u + β • v) : ℝ) : EReal) +
            ∑ k : Fin s, blockTerm k (α • u + β • v)) := hPenalty_combo
    _ ≤ ((α : EReal) * ((dotProduct a u : ℝ) : EReal) +
          (β : EReal) * ((dotProduct a v : ℝ) : EReal)) +
            ((α : EReal) * ∑ k : Fin s, blockTerm k u +
              (β : EReal) * ∑ k : Fin s, blockTerm k v) := by
                exact add_le_add (le_of_eq hAffineEq) hsum_jensen
    _ = (α : EReal) * decompositionDualPenalty n f0 A a u +
          (β : EReal) * decompositionDualPenalty n f0 A a v := by
            rw [hPenalty_u, hPenalty_v]
            have hαE : (0 : EReal) ≤ (α : EReal) := by
              exact (EReal.coe_nonneg).2 hα
            have hβE : (0 : EReal) ≤ (β : EReal) := by
              exact (EReal.coe_nonneg).2 hβ
            have hαdist :
                (α : EReal) * (((dotProduct a u : ℝ) : EReal) + ∑ k : Fin s, blockTerm k u) =
                  (α : EReal) * ((dotProduct a u : ℝ) : EReal) +
                    (α : EReal) * ∑ k : Fin s, blockTerm k u := by
              simpa using
                (EReal.left_distrib_of_nonneg_of_ne_top hαE (EReal.coe_ne_top α)
                  (((dotProduct a u : ℝ) : EReal)) (∑ k : Fin s, blockTerm k u))
            have hβdist :
                (β : EReal) * (((dotProduct a v : ℝ) : EReal) + ∑ k : Fin s, blockTerm k v) =
                  (β : EReal) * ((dotProduct a v : ℝ) : EReal) +
                    (β : EReal) * ∑ k : Fin s, blockTerm k v := by
              simpa using
                (EReal.left_distrib_of_nonneg_of_ne_top hβE (EReal.coe_ne_top β)
                  (((dotProduct a v : ℝ) : EReal)) (∑ k : Fin s, blockTerm k v))
            rw [hαdist, hβdist]
            simpa [add_assoc, add_left_comm, add_comm]

-- Proof sketch: expand the separable Lagrangian as the constant term `-⟪a, uStar⟫` plus the sum
-- of blockwise affine perturbations `f₀ₖ(xₖ) + ⟪xₖ, Aₖᵀ uStar⟫`. Taking the infimum over all block
-- vectors separates into a sum of one-block infima, and each such infimum is the negative of the
-- Fenchel conjugate evaluated at `-Aₖᵀ uStar`. When the block objectives are convex, the explicit
-- penalty `w = -g` is convex on `ℝ^m`; if a Kuhn--Tucker vector exists, Corollary 6.28.6 then
-- identifies Kuhn--Tucker vectors exactly with the maximizers of the dual function, hence with
-- the minimizers of `w`.
/-- Theorem 6.28.8: For the separable equality-constrained decomposition problem with block
objectives `f₀ₖ : ℝ^{nₖ} → ℝ`, matrices `Aₖ : ℝ^{nₖ} → ℝ^m`, and right-hand side `a ∈ ℝ^m`, the
Lagrangian satisfies
`L(uStar, x) = -⟪a, uStar⟫ + ∑ₖ (f₀ₖ(xₖ) + ⟪xₖ, Aₖᵀ uStar⟫)`. Consequently the dual function
`g(uStar) = inf_x L(uStar, x)`, represented here by `decompositionDualFunction n f0 A a uStar`,
is
`g(uStar) = -⟪a, uStar⟫ - ∑ₖ f₀ₖ^*(-Aₖᵀ uStar)`. If each `f₀ₖ` is convex on `ℝ^{nₖ}`, then the
explicit dual penalty
`w(uStar) = ⟪a, uStar⟫ + ∑ₖ f₀ₖ^*(-Aₖᵀ uStar)`, represented here by
`decompositionDualPenalty n f0 A a uStar`, is convex on `ℝ^m`, expressed here by the Jensen
inequality for convex combinations of multiplier vectors; if the problem has at least one
Kuhn--Tucker vector, then the Kuhn--Tucker vectors are exactly the minimizers of this convex
function. -/
theorem decomposition_lagrangian_dualFunction_and_dualPenalty_formula
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : ∀ k : Fin s, (Fin (n k) → ℝ) → ℝ)
    (A : ∀ k : Fin s, Matrix (Fin m) (Fin (n k)) ℝ)
    (a : Fin m → ℝ) :
    (∀ (uStar : Fin m → ℝ) (x : DecompositionBlockVector s n),
      decompositionLagrangian n f0 A a uStar x =
        -dotProduct a uStar +
          ∑ k : Fin s,
            (f0 k (x k) + dotProduct (x k) ((A k).transpose.mulVec uStar))) ∧
      (∀ uStar : Fin m → ℝ,
        decompositionDualFunction n f0 A a uStar =
          ((-(dotProduct a uStar) : ℝ) : EReal) -
            ∑ k : Fin s,
              convexConjugate (fun xk : Fin (n k) → ℝ => (f0 k xk : EReal))
                (fun j : Fin (n k) => -((A k).transpose.mulVec uStar j))) ∧
      ((∀ k : Fin s, ConvexOn ℝ Set.univ (f0 k)) →
        (∀ (u v : Fin m → ℝ) {α β : ℝ},
          0 ≤ α → 0 ≤ β → α + β = 1 →
            decompositionDualPenalty n f0 A a (α • u + β • v) ≤
              (α : EReal) * decompositionDualPenalty n f0 A a u +
                (β : EReal) * decompositionDualPenalty n f0 A a v) ∧
          ((∃ u : Fin m → ℝ, IsDecompositionKuhnTuckerVector n f0 A a u) →
            ∀ uStar : Fin m → ℝ,
              IsDecompositionKuhnTuckerVector n f0 A a uStar ↔
                IsDecompositionDualPenaltyMinimizer n f0 A a uStar)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro uStar x
    -- Reuse the previously established expansion of the decomposition Lagrangian.
    exact helperForTheorem_6_28_8_lagrangian_eq_neg_dotProduct_add_sum_blockDotProducts
      n f0 A a uStar x
  · intro uStar
    -- The displayed dual formula is the dedicated helper proved above.
    exact helperForTheorem_6_28_8_dualFunction_eq_neg_dotProduct_sub_sumConjugates
      n f0 A a uStar
  · intro hconvex
    refine ⟨?_, ?_⟩
    · -- The only remaining structural gap is the Jensen inequality for the explicit dual penalty.
      exact helperForTheorem_6_28_8_dualPenalty_convexJensen n f0 A a hconvex
    · intro h_exists uStar
      -- Compose the dual-maximizer characterization with `w = -g`.
      exact
        (helperForTheorem_6_28_8_isKuhnTuckerVector_iff_dualFunctionMaximizer_of_exists
          n f0 A a h_exists uStar).trans
          (helperForTheorem_6_28_8_dualPenaltyMinimizer_iff_dualFunctionMaximizer
            n f0 A a uStar).symm

end Section28
end Chap06
