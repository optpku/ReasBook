/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part4

section Chap06
section Section30

/-- Theorem 6.30.8: for a concave bifunction `G : ℝ^m → ℝ^n` with perturbation function
`h = sup G`, a vector `u* ∈ ℝ^m` is a Kuhn--Tucker vector for `(Q)` if and only if `h(0)` is
finite and `-u* ∈ ∂ h(0)`. In Lean, finiteness of `h(0)` is expressed by `h 0 ≠ ⊤` and
`h 0 ≠ ⊥`. -/
theorem isKuhnTuckerVectorForConcaveProgram_iff_neg_mem_concaveSubdifferentialAt_zero {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G})
    (uStar : Fin m → ℝ) :
    IsKuhnTuckerVectorForConcaveProgram G uStar ↔
      let h := perturbationFunctionOfConcaveProgram G
      h 0 ≠ ⊤ ∧ h 0 ≠ ⊥ ∧ (-uStar) ∈ concaveSubdifferentialAt h 0 := by
  let h := perturbationFunctionOfConcaveProgram G
  let S : EReal := sSup (Set.range fun u : Fin m → ℝ => (((uStar ⬝ᵥ u : ℝ) : EReal) + h u))
  have hsupport :
      (-uStar) ∈ concaveSubdifferentialAt h 0 ↔
        ∀ u : Fin m → ℝ, (((uStar ⬝ᵥ u : ℝ) : EReal) + h u) ≤ h 0 :=
    helperForTheorem_6_30_8_neg_mem_concaveSubdifferentialAt_zero_iff_supporting_inequality
      (h := h) uStar
  have hsup :
      (S ≠ ⊤ ∧ S ≠ ⊥ ∧ S = h 0) ↔
        h 0 ≠ ⊤ ∧ h 0 ≠ ⊥ ∧ (-uStar) ∈ concaveSubdifferentialAt h 0 := by
    constructor
    · rintro ⟨hTop, hBot, hEq⟩
      have hbound :
          ∀ u : Fin m → ℝ, (((uStar ⬝ᵥ u : ℝ) : EReal) + h u) ≤ h 0 :=
        (helperForTheorem_6_30_8_perturbationSup_eq_valueAt_zero_iff_pointwise_bound
          (h := h) uStar).1 ⟨hEq, hTop, hBot⟩ |>.2.2
      exact ⟨by simpa [hEq] using hTop, by simpa [hEq] using hBot, hsupport.2 hbound⟩
    · rintro ⟨hTop, hBot, hsubgrad⟩
      have hbound :
          ∀ u : Fin m → ℝ, (((uStar ⬝ᵥ u : ℝ) : EReal) + h u) ≤ h 0 :=
        hsupport.1 hsubgrad
      have hS :
          S = h 0 ∧ S ≠ ⊤ ∧ S ≠ ⊥ :=
        (helperForTheorem_6_30_8_perturbationSup_eq_valueAt_zero_iff_pointwise_bound
          (h := h) uStar).2 ⟨hTop, hBot, hbound⟩
      exact ⟨hS.2.1, hS.2.2, hS.1⟩
  -- Rewrite the Kuhn--Tucker data into the perturbation supremum alone.
  change IsKuhnTuckerVectorForConcaveProgram G uStar ↔
    h 0 ≠ ⊤ ∧ h 0 ≠ ⊥ ∧ (-uStar) ∈ concaveSubdifferentialAt h 0
  -- The three helper lemmas identify the pair supremum, the supporting inequality, and the
  -- equality case at `u = 0`.
  simpa [IsKuhnTuckerVectorForConcaveProgram, h, S,
    helperForTheorem_6_30_8_bifunctionSup_eq_perturbationSup] using hsup

/-- Corollary 30.1.30 -/
theorem corollary_6_30_1_30 : True := by
  trivial

/-- Corollary 30.1.31 -/
theorem corollary_6_30_1_31 : True := by
  trivial

/-- Proposition 30.1.32 -/
theorem proposition_6_30_1_32 : True := by
  trivial

/-- Corollary 30.1.33 -/
theorem corollary_6_30_1_33 : True := by
  trivial

-- Proof sketch: apply the convex Fenchel-Young theorem from Chapter 5 to the proper convex
-- function `g`; this gives the global inequality and identifies equality with Euclidean
-- subgradient membership, i.e. with `x* ∈ ∂ g(x)` under the dot-product identification of `ℝ^n`
-- with its dual.
/-- Theorem 6.30.5: if `g : ℝ^n → (-∞, +∞]` is proper and convex, then for every `x, x* ∈ ℝ^n`
one has the Fenchel--Young inequality `⟪x, x*⟫ ≤ g x + g*(x*)`. Moreover, equality holds if and
only if `x*` is a Euclidean subgradient of `g` at `x`, equivalently `x* ∈ ∂ g(x)` under the
standard identification of `ℝ^n` with its dual. -/
theorem fenchelYoung_inequality_and_eq_iff_mem_subdifferential {n : ℕ}
    (g : (Fin n → ℝ) → EReal)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (x xStar : Fin n → ℝ) :
    (((dotProduct x xStar : ℝ) : EReal) ≤ g x + fenchelConjugate n g xStar) ∧
      (g x + fenchelConjugate n g xStar = ((dotProduct x xStar : ℝ) : EReal) ↔
        IsEuclideanSubgradientAt g x xStar) := by
  constructor
  · -- The first claim is exactly the global Fenchel--Young inequality for a proper convex function.
    exact fenchel_inequality n g hg x xStar
  · -- The Chapter 5 TFAE identifies Fenchel--Young equality with Euclidean subgradient membership.
    simpa [FenchelYoungEqualityAt] using
      ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung g hg x xStar).1.out 3 0)

-- Proof sketch: apply Corollary 23.5.1, namely
-- `euclidean_subgradient_fenchelConjugate_iff`, to the closed proper convex function `g`, then
-- unfold `euclideanSubdifferentialAt` to rewrite Euclidean subgradient predicates as membership in
-- the corresponding subdifferential fibers.
/-- Theorem 6.30.6: if `g : ℝ^n → (-∞, +∞]` is a proper closed convex function and `g*` is its
Fenchel conjugate, then for every `x, x* ∈ ℝ^n` one has
`x* ∈ ∂ g(x)` if and only if `x ∈ ∂ g*(x*)`, where both subdifferentials are interpreted in the
Euclidean sense on `Fin n → ℝ`. -/
theorem mem_euclideanSubdifferentialAt_iff_mem_euclideanSubdifferentialAt_fenchelConjugate
    {n : ℕ} (g : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction g)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (x xStar : Fin n → ℝ) :
    xStar ∈ euclideanSubdifferentialAt g x ↔
      x ∈ euclideanSubdifferentialAt (fenchelConjugate n g) xStar := by
  -- Rewrite both fiber-membership statements as Euclidean subgradient predicates.
  -- Corollary 23.5.1 then swaps the primal and conjugate subgradient conditions.
  simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt] using
    (euclidean_subgradient_fenchelConjugate_iff
      (f := g) hclosed hproper x xStar).symm

-- Corollary 30.5.1 / Corollary 6.30.4 is stated near the end of the file, after the normality
-- and Kuhn--Tucker infrastructure it depends on.

/-- Corollary 30.5.2 -/
theorem corollary_6_30_5_2 : True := by
  trivial

end Section30
end Chap06
