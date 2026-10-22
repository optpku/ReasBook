/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_49
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section Ambient

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 3.52 lies in the cutting-plane localization-recursion domain.

Relevant owner-style declarations sampled before refinement:
- `cuttingHalfspace` in `Definition_3_49`, the chapter owner for the retained one-step affine cut;
- `localizationSet` in `Theorem_3_2_9`, the closed-form stage set cut out by the first `k + 1`
  inequalities;
- `mem_localizationSet_iff` in `Theorem_3_2_9`, the canonical membership expansion of that
  closed-form stage set;
- `GeneralCuttingPlaneScheme.localizer` in `Algorithm_3_6`, a downstream owner that consumes this
  recursive localization family.

Best owner abstraction:
- source-facing: the recursive localization family `localizationSets`;
- core/canonical: the retained half-space cut `cuttingHalfspace`;
- bridge/view: the earlier closed-form stage description `localizationSet`.

Primitive data:
- the initial feasible region `Q`;
- the query sequence `xSeq`;
- the cutting-vector sequence `gSeq`.

Derived API:
- the recursive zero and successor equations for `localizationSets`;
- the identification of `localizationSets Q xSeq gSeq (k + 1)` with the earlier closed-form owner
  `localizationSet Q xSeq gSeq k`.

Accordingly, this file keeps the source-facing recursive object public, reuses the canonical
half-space owner for the successor step, and treats the earlier closed-form stage set only as a
bridge/view of the same recursion. -/

/-- Definition 3.52: given an initial set `Q`, a sequence `X = (x_k)`, and associated vectors
`g_k`, the localization sets are defined recursively by `S₀(X) = Q` and
`S_{k+1}(X) = {x ∈ S_k(X) | ⟪g_k, x_k - x⟫ ≥ 0}`. In the textbook this is specialized to
`Q ⊆ ℝⁿ`. -/
def localizationSets (Q : Set E) (xSeq gSeq : ℕ → E) : ℕ → Set E
  | 0 => Q
  | k + 1 => localizationSets Q xSeq gSeq k ∩ cuttingHalfspace (xSeq k) (gSeq k)

/-- The zeroth localization set is the initial set `Q`. -/
-- Proof sketch: unfold `localizationSets`; the zero case of the recursive definition is exactly
-- `Q`.
@[simp]
theorem localizationSets_zero (Q : Set E) (xSeq gSeq : ℕ → E) :
    localizationSets Q xSeq gSeq 0 = Q :=
  rfl

/-- The recursive step intersects the previous localization set with the half-space cut determined
by `x_k` and `g_k`. -/
-- Proof sketch: unfold `localizationSets`; the successor equation of the recursive definition is
-- precisely the displayed set equality.
@[simp]
theorem localizationSets_succ (Q : Set E) (xSeq gSeq : ℕ → E) (k : ℕ) :
    localizationSets Q xSeq gSeq (k + 1) =
      localizationSets Q xSeq gSeq k ∩ cuttingHalfspace (xSeq k) (gSeq k) :=
  rfl

end Ambient

section Bridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The recursive localization set at stage `k + 1` agrees with the earlier closed-form
localization-set owner determined by the first `k + 1` cuts. -/
@[simp]
theorem localizationSets_succ_eq_localizationSet
    (Q : Set E) (xSeq gSeq : ℕ → E) (k : ℕ) :
    localizationSets Q xSeq gSeq (k + 1) = localizationSet Q xSeq gSeq k := by
  induction k with
  | zero =>
      ext x
      simp [localizationSet, mem_cuttingHalfspace_iff]
  | succ k hk =>
      ext x
      rw [localizationSets_succ, hk]
      simp [localizationSet, mem_cuttingHalfspace_iff, Fin.forall_iff_castSucc, and_left_comm,
        and_comm]

end Bridge

end
