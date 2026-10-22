/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib

section Chap06

/-- A real-valued function is affine on a set if it agrees there with an affine map. -/
def AffineOnSet
    (X : Type*) [AddCommGroup X] [Module ℝ X]
    (C : Set X) (f : X → ℝ) : Prop :=
  ∃ a : X →ᵃ[ℝ] ℝ, Set.EqOn f a C

/-- A minimal core definition of an ordinary convex program over a real vector space: a convex
ambient set `C`, a convex objective `f₀` on `C`, convex inequality constraints `gᵢ` on `C`, and
affine equality constraints `hⱼ` on `C`. -/
structure OrdinaryConvexProgram
    (X : Type*) (ι κ : Type*)
    [AddCommGroup X] [Module ℝ X] where
  C : Set X
  f0 : X → ℝ
  g : ι → X → ℝ
  h : κ → X → ℝ
  C_convex : Convex ℝ C
  f0_convexOn : ConvexOn ℝ C f0
  g_convexOn : ∀ i, ConvexOn ℝ C (g i)
  h_affineOn : ∀ j, AffineOnSet X C (h j)

/-- The book's coordinate presentation of an ordinary convex program on `ℝⁿ`, with `r`
inequality constraints and `m-r` equality constraints. This wrapper keeps the textbook indexing
convention while the canonical semantic core is `OrdinaryConvexProgram`. -/
structure BookOrdinaryConvexProgram (n m r : ℕ) where
  constraintSet : Set (Fin n → ℝ)
  objective : (Fin n → ℝ) → ℝ
  inequalityConstraint : Fin r → (Fin n → ℝ) → ℝ
  equalityConstraint : Fin (m - r) → (Fin n → ℝ) → ℝ
  inequalityCount_le_constraintCount : r ≤ m
  convex_constraintSet : Convex ℝ constraintSet
  objective_convexOn : ConvexOn ℝ constraintSet objective
  inequalityConstraint_convexOn :
    ∀ i : Fin r, ConvexOn ℝ constraintSet (inequalityConstraint i)
  equalityConstraint_affineOn :
    ∀ i : Fin (m - r), AffineOnSet (Fin n → ℝ) constraintSet (equalityConstraint i)

/-- The canonical ordinary-convex-program core attached to the book's coordinate presentation. -/
def BookOrdinaryConvexProgram.asOrdinaryConvexProgram {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) :
    OrdinaryConvexProgram (Fin n → ℝ) (Fin r) (Fin (m - r)) where
  C := P.constraintSet
  f0 := P.objective
  g := P.inequalityConstraint
  h := P.equalityConstraint
  C_convex := P.convex_constraintSet
  f0_convexOn := P.objective_convexOn
  g_convexOn := P.inequalityConstraint_convexOn
  h_affineOn := P.equalityConstraint_affineOn

end Chap06
