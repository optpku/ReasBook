/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section

/- Chapter 5 repeatedly uses the raw product types `(ℝ × ℝ)` and `((ℝ × ℝ) × ℝ)` as concrete
coordinate models for planar and lifted power-cone slices, but the self-concordance owners act in
the Euclidean `L²` ambient structure. Mathlib provides that ambient structure on
`WithLp 2 (E × F)`, while these source-facing files keep the raw product types. This helper owns
the reusable local-instance bridge from the raw products to the corresponding `WithLp 2` `L²`
structures, so neighboring theorem files can activate one shared setup instead of repeating
ad hoc instance blocks. -/

namespace Chap05RealProdL2

noncomputable local instance instSeminormedAddCommGroupRealProd :
    SeminormedAddCommGroup (ℝ × ℝ) :=
  WithLp.seminormedAddCommGroupToProd 2 ℝ ℝ

noncomputable local instance instNormedAddCommGroupRealProd : NormedAddCommGroup (ℝ × ℝ) :=
  WithLp.normedAddCommGroupToProd 2 ℝ ℝ

noncomputable local instance instNormedSpaceRealProd : NormedSpace ℝ (ℝ × ℝ) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 ℝ ℝ

noncomputable local instance instInnerProductSpaceRealProd : InnerProductSpace ℝ (ℝ × ℝ) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 ℝ ℝ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instCompleteSpaceRealProd : CompleteSpace (ℝ × ℝ) := inferInstance

noncomputable local instance instSeminormedAddCommGroupRealProdProd :
    SeminormedAddCommGroup ((ℝ × ℝ) × ℝ) :=
  WithLp.seminormedAddCommGroupToProd 2 (ℝ × ℝ) ℝ

noncomputable local instance instNormedAddCommGroupRealProdProd :
    NormedAddCommGroup ((ℝ × ℝ) × ℝ) :=
  WithLp.normedAddCommGroupToProd 2 (ℝ × ℝ) ℝ

noncomputable local instance instNormedSpaceRealProdProd : NormedSpace ℝ ((ℝ × ℝ) × ℝ) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 (ℝ × ℝ) ℝ

noncomputable local instance instInnerProductSpaceRealProdProd :
    InnerProductSpace ℝ ((ℝ × ℝ) × ℝ) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 (ℝ × ℝ) ℝ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instCompleteSpaceRealProdProd :
    CompleteSpace ((ℝ × ℝ) × ℝ) := inferInstance

end Chap05RealProdL2
