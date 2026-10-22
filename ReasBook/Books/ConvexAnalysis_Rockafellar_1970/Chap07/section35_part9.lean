/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part8

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

/-- Helper for Text 35.6.6: the textbook hull/support identity is correct on the honest branch
where the first partial subdifferential is nonempty. -/
lemma helperForText_35_6_6_saddleLowerHull_eq_firstPartialSupport_of_nonempty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartial : Set.Nonempty (partialSubdifferentialInFirstVariable K u v)) :
    saddleLowerSemicontinuousHull (firstVariableDirectionalDerivativeFunction K u v) =
      supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) := by
  let g : (Fin m → ℝ) → EReal := fun x => -K (-x) v
  have hg : ConvexFunction g := by
    -- Reuse the same reflected-slice convexity helper used in the closure computation.
    simpa [g] using helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hSaddle v
  have hgu : g (-u) ≠ (⊤ : EReal) ∧ g (-u) ≠ (⊥ : EReal) := by
    -- Recentring preserves the finiteness of the base value via the same dedicated helper.
    simpa [g] using
      helperForText_35_6_6_reflectedFirstSlice_finiteAtBase (K := K) (u := u) (v := v) hFinite
  let D : (Fin m → ℝ) → EReal := upperDirectionalDerivativeAt g (-u)
  have hphiEq :
      firstVariableDirectionalDerivativeFunction K u v = D := by
    -- The reflected-slice equality now comes from the whole-function recentering helper.
    simpa [D, g] using
      helperForText_35_6_6_firstVariableDirectionalDerivative_eq_upperDirectionalDerivative
        (K := K) hSaddle (u := u) (v := v) hFinite
  have hsliceNonempty : Set.Nonempty (subdifferentialAt g (-u)) :=
    (helperForText_35_6_6_partialFirst_nonempty_iff_sliceSubdifferential_nonempty
      (K := K) (u := u) (v := v)).1 hpartial
  calc
    saddleLowerSemicontinuousHull (firstVariableDirectionalDerivativeFunction K u v) =
        epigraphClosureInf D := by
      rw [hphiEq]
      rw [helperForText_35_6_6_saddleLowerHull_eq_epigraphClosureInf (φ := D)]
    _ = subdifferentialSupportAt g (-u) := by
      -- On the nonempty branch, Chapter 23 and Chapter 2 agree on the directional-derivative
      -- hull.
      exact
        helperForText_35_6_6_epigraphClosureInf_eq_sliceSupport_of_nonempty_sliceSubdifferential
          (g := g) (x := -u) hg hgu hsliceNonempty
    _ = supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) := by
      -- Translate the slice support back to the textbook first partial subdifferential.
      simpa [g] using
        helperForText_35_6_6_sliceSupport_eq_firstPartialSupport
          (K := K) (u := u) (v := v)

/-- Helper for Text 35.6.6: the mathematically correct Chapter 23 closure statement identifies the
convex closure of the first directional-derivative slice with the support function of `∂₁ K(u,v)`.
-/
lemma helperForText_35_6_6_saddleLowerHull_eq_firstPartialSupport
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) :
    convexFunctionClosure (firstVariableDirectionalDerivativeFunction K u v) =
      supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) := by
  exact
    helperForText_35_6_6_convexFunctionClosure_eq_firstPartialSupport
      (K := K) hSaddle (u := u) (v := v) hFinite

-- Proof sketch: apply the one-variable convex analysis result for the convex function
-- `u' ↦ -K u' v` at the finite point `u`. Its directional derivative in direction `-u'` is
-- exactly `-K'(u, v; -u', 0)`, which is convex in `u'`; then Theorem 23.2 identifies the
-- convex closure of this directional-derivative function with the support function of
-- the first partial subdifferential `∂₁ K(u, v)`.
/-- Text 35.6.6: let `K` be a saddle function on `ℝ^m × ℝ^n`, and let `(u, v)` be a point with
finite value `K u v`. Define `φ(u') = -K'(u, v; -u', 0)`. Then `φ` is a convex function on
`ℝ^m`, and the convex closure of `φ` coincides with the support function of the closed
convex set `∂₁ K(u, v)`. -/
theorem section35_text35_6_6
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) :
    ConvexFunction (firstVariableDirectionalDerivativeFunction K u v) ∧
      ∀ u' : Fin m → ℝ,
        convexFunctionClosure (firstVariableDirectionalDerivativeFunction K u v) u' =
          supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) u' := by
  let g : (Fin m → ℝ) → EReal := fun x => -K (-x) v
  have hg : ConvexFunction g := by
    -- Reuse the reflected-slice convexity helper so the theorem follows the textbook route
    -- without re-deriving the slice geometry.
    simpa [g] using helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hSaddle v
  have hgu : g (-u) ≠ (⊤ : EReal) ∧ g (-u) ≠ (⊥ : EReal) := by
    -- At the reflected base point the slice still has the finite value `-K u v`.
    simpa [g] using
      helperForText_35_6_6_reflectedFirstSlice_finiteAtBase (K := K) (u := u) (v := v) hFinite
  have hphiEq :
      firstVariableDirectionalDerivativeFunction K u v =
        upperDirectionalDerivativeAt g (-u) := by
    -- The textbook `φ` is exactly the Chapter 23 directional derivative of the recentered slice.
    simpa [g] using
      helperForText_35_6_6_firstVariableDirectionalDerivative_eq_upperDirectionalDerivative
        (K := K) hSaddle (u := u) (v := v) hFinite
  have hphiConv : ConvexFunction (firstVariableDirectionalDerivativeFunction K u v) := by
    -- Directional derivatives of convex functions are convex, and `φ` is one of those.
    have hdirConv : ConvexFunction (upperDirectionalDerivativeAt g (-u)) :=
      (convex_directionalDerivative_monotone_exists_and_sublinear g hg (-u) hgu).2.2.1
    simpa [hphiEq] using hdirConv
  refine ⟨hphiConv, ?_⟩
  intro u'
  -- Rewrite the local hull directly to the textbook support function.
  calc
    convexFunctionClosure (firstVariableDirectionalDerivativeFunction K u v) u' =
        supportFunctionOfSet (partialSubdifferentialInFirstVariable K u v) u' := by
      rw [helperForText_35_6_6_saddleLowerHull_eq_firstPartialSupport
        (K := K) hSaddle (u := u) (v := v) hFinite]

end Section35
end Chap07
