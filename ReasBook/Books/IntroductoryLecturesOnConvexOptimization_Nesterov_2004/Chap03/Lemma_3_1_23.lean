/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {U : Type v} {α : Type*} [AddCommGroup α] [Preorder α]
  [AddLeftMono α] [AddRightMono α]

/- Lemma 3.1.23 lies in the chapter's primal-dual gap domain.

Primary domain:
- one-step primal-dual gap estimates in an ordered additive value type under primal lower bounds,
  dual upper bounds, and weak duality

Sampled owner-style declarations:
- `Set.Icc` / `Set.mem_Icc` in mathlib, the canonical closed-interval owner for the target bound
- `sub_nonneg` and `sub_nonpos` in mathlib, the canonical ordered-additive owners for the two
  primitive gap comparisons
- `primal_dual_decomposition_mem_Icc_and_gap_le_of_averaged_affine_lower_model` in
  `Chap03/Lemma_3_23`
- `primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta` in `Chap03/Lemma_3_1_24`

Best owner abstraction:
- this theorem itself is the source-facing owner for the generic one-step decomposition interval;
  its primitive inputs are the local primal and dual comparison inequalities at the chosen pair,
  and later Chapter 3 results derive those inequalities from concrete lower-value and certificate
  constructions

Primitive data:
- the functions `f`, `φ`
- the points `xN`, `uHat`
- the comparison values `fStar`, `φStar`, `rN`
- the local comparison bounds `fStar ≤ f xN` and `φ uHat ≤ φStar`

Derived API:
- weak duality `φStar ≤ fStar`
- the residual estimate `f xN - φ uHat ≤ rN`
- any set-based or optimal-value owners used later only to derive the two local comparison bounds

Source/core/bridge triage:
- source-facing: the textbook interval estimate for the decomposition at a residual-controlled pair
- core/canonical: the order/arithmetic comparison between the decomposition and the raw
  primal-dual gap under local primal and dual comparison bounds together with weak duality
- bridge/view: the Chapter 3 certificate and affine-lower-model specializations in
  `Lemma_3_1_24` and `Lemma_3_23`

There is no stricter upstream theorem with the same generic interface. This file therefore keeps
the generic source-facing owner itself, but reduces its public inputs to the primitive local
inequalities actually used by the arithmetic instead of carrying ambient sets and global
lower/upper-bound hypotheses that direct downstream files immediately specialize back to the chosen
pair `(xN, uHat)`.
-/

/-- Lemma 3.1.23: if `x_N` satisfies the residual estimate `(3.1.85)`, written here as
`f(x_N) - φ(\hat u_N) ≤ r_N`, then the decomposition
`(f(x_N) - f^*) + (φ^* - φ(\hat u_N))` lies between `0` and the primal-dual gap
`f(x_N) - φ(\hat u_N)`, and that gap is itself bounded above by `r_N`. -/
-- Proof sketch: the local primal and dual comparison bounds give
-- `0 ≤ f(x_N) - f^*` and `0 ≤ φ^* - φ(\hat u_N)`, so the decomposition is nonnegative. The
-- difference between the primal-dual gap and the decomposition is `f^* - φ^*`, which is
-- nonnegative by weak duality. The final upper bound is exactly the assumed residual estimate
-- `(3.1.85)`.
theorem primal_dual_decomposition_mem_Icc_of_gap_le
    {f : E → α} {φ : U → α} {xN : E} {uHat : U} {fStar φStar rN : α}
    (h_primal : fStar ≤ f xN) (h_dual : φ uHat ≤ φStar)
    (h_weak_duality : φStar ≤ fStar)
    (h_gap : f xN - φ uHat ≤ rN) :
    (f xN - fStar) + (φStar - φ uHat) ∈ Set.Icc 0 (f xN - φ uHat) ∧
      f xN - φ uHat ≤ rN := by
  have h_primal_gap : 0 ≤ f xN - fStar := sub_nonneg.mpr h_primal
  have h_dual_gap : 0 ≤ φStar - φ uHat := sub_nonneg.mpr h_dual
  have h_nonneg : 0 ≤ (f xN - fStar) + (φStar - φ uHat) :=
    add_nonneg h_primal_gap h_dual_gap
  have h_le_gap : (f xN - fStar) + (φStar - φ uHat) ≤ f xN - φ uHat := by
    calc
      (f xN - fStar) + (φStar - φ uHat) = (f xN - φ uHat) + (φStar - fStar) := by
        abel
      _ ≤ (f xN - φ uHat) + 0 := by
        exact add_le_add_right (sub_nonpos.mpr h_weak_duality) (f xN - φ uHat)
      _ = f xN - φ uHat := by simp
  refine ⟨?_, h_gap⟩
  rw [Set.mem_Icc]
  exact ⟨h_nonneg, h_le_gap⟩

end
