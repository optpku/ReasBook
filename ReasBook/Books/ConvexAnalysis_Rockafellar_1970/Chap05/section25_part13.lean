/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part5

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-- Helper for Corollary 25.7.1: Theorem 25.3 gives continuity and monotonicity of the derivative
on every compact subinterval once differentiability is known on the whole open interval. -/
lemma helperForCorollary_25_7_1_deriv_continuousOn_Icc_and_monotoneOn
    {I : Set ℝ} (hIopen : IsOpen I) (hIconv : Convex ℝ I) {g : ℝ → ℝ}
    (hgconv : ConvexOn ℝ I g) (hgdiff : DifferentiableOn ℝ g I)
    {a b : ℝ} (_hab : a ≤ b) (hIcc : Set.Icc a b ⊆ I) :
    ContinuousOn (deriv g) (Set.Icc a b) ∧ MonotoneOn (deriv g) (Set.Icc a b) := by
  let D : Set ℝ := {x | x ∈ I ∧ HasDerivAt g (deriv g x) x}
  have hTheorem25_3 :=
    convexOn_openInterval_countable_nondifferentiabilitySet_dense_and_deriv_continuousOn_monotoneOn
      (I := I) hIopen hIconv hgconv
  rcases hTheorem25_3 with ⟨_hcount, _hclosure, hcontD, hmonoD⟩
  have hDI : D = I := by
    -- Differentiability on the open interval identifies the set `D` from Theorem 25.3 with `I`.
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      exact (hgdiff x hx).differentiableAt (hIopen.mem_nhds hx) |>.hasDerivAt
  constructor
  · intro x hx
    -- Restrict the continuity statement from `D = I` down to the compact interval.
    have hxI : x ∈ I := hIcc hx
    have hxD : x ∈ D := by
      rw [hDI]
      exact hxI
    have hcontDx : ContinuousWithinAt (deriv g) D x := hcontD x hxD
    have hIccSubsetD : Set.Icc a b ⊆ D := by
      intro y hy
      rw [hDI]
      exact hIcc hy
    exact hcontDx.mono hIccSubsetD
  · intro x hx y hy hxy
    -- The same restriction argument transports monotonicity to `Set.Icc a b`.
    have hxD : x ∈ D := by
      rw [hDI]
      exact hIcc hx
    have hyD : y ∈ D := by
      rw [hDI]
      exact hIcc hy
    simpa [hDI] using hmonoD hxD hyD hxy

end Section25
end Chap05
